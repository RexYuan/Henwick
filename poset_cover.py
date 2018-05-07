import graphviz as gz
import networkx as nx

from z3 import *

import logging

from functools import reduce
from itertools import permutations
from math import factorial
from time import time

TAUTO = BoolVal(True)
CONTRA = BoolVal(False)

logger = logging.getLogger(__name__)
logger.addHandler(logging.NullHandler())
'''
logger.setLevel(logging.DEBUG)
status_sh = logging.StreamHandler()
status_sh.setLevel(logging.DEBUG)
status_formatter = logging.Formatter('[%(levelname)s] %(asctime)s : %(name)s : %(message)s')
status_sh.setFormatter(status_formatter)
logger.addHandler(status_sh)
'''

def is_swap(s1, s2):
    '''
    return if s1 and s2 are off by one swap
    s1, s2 : string | tuple
    '''
    pair = False
    i = 0
    while i < len(s1):
        if s1[i] != s2[i]:
            if i == len(s1)-1:
                return False
            if (s1[i] == s2[i+1] and s1[i+1] == s2[i]):
                if pair:
                    return False
                pair = True
                i += 1
            else:
                return False
        i += 1
    return pair

def trans_closure(ss):
    '''
    ss : list
    '''
    s = set(map((lambda s : tuple(s.split('<'))), ss))
    t = set()
    while True:
        tmp = set()
        changed = False
        for x in s:
            for y in s:
                if x[1] == y[0] and x[0]+'<'+y[1] not in t:
                    tmp.add((x[0], y[1]))
                    t.add(x[0]+'<'+y[1])
                    changed = True
        s = s | tmp
        if not changed:
            break
    return set(map('<'.join, s)) | t

def rm_trans_closure(uni, rs):
    crels = set()
    for x,y in rs:
        cover = True
        for z in uni:
            if (x,z) in rs and (z,y) in rs:
                cover = False
        if cover:
            crels.add( (x,y) )
    return crels

def poset_axioms(universe, name, total=False):
    '''
    build poset axioms on iterable universe
    '''
    def rel(x, y):
        return Bool('P'+name+'_'+x+'<'+y)
    constraints = TAUTO
    omega = set(universe)

    for x in omega:
        for y in omega-{x}:
            # forall x!=y, -(x<y & y<x)
            constraints = simplify(And( constraints , Not( And(rel(x,y),rel(y,x)) ) ))

            if total:
                # forall x!=y, (x<y | y<x)
                constraints = simplify(And( constraints , Or( rel(x,y),rel(y,x) ) ))

            for z in omega-{x,y}:
                # forall x!=y!=z, (x<y & y<z) => x<z
                constraints = simplify(And( constraints , Implies( And(rel(x,y),rel(y,z)) , rel(x,z) ) ))
    return constraints

def le_constraints(universe, name, lin):
    '''
    linear extension constraints : <lin> (string) extends poset <name>

    given P2,
    P2 extends P1 : forall r, r in P1 => r in P2
                  = forall r, r not in P2 => r not in P1
    '''
    def rel(x, y):
        return Bool('P'+name+'_'+x+'<'+y)
    constraints = TAUTO
    omega = set(universe)

    ords = set()
    # cartesian set
    for x in omega:
        for y in omega-{x}:
            ords.add( (x,y) )

    # set difference the relations from lin
    # NOTE: this is WRONG. this only works with |uni| < 10 because an element
    # may not be a single character!!!
    # TODO: replace this with some method using tuples as I did in the angluin
    # code where a symbol may also not be a single character!!!
    for i,x in enumerate(lin):
        for y in lin[i+1:]:
            try:
                ords.remove( (x,y) )
            except:
                #print((x,y), 'not in ords')
                pass

    # build constraints on name : forall r not in <lin>, r not in <name>
    for r in ords:
        constraints = simplify(And( constraints , Not(rel(*r)) ))
    return constraints

def connected_poset_cover(lins=None, comp=None, getall=False, timeout=None, runaway_timeout=False):
    '''
    Return minimal poset cover for connected linearizations

    return type : a set of frozensets of 2-tuples ; as a poset is expressed as
    a set of 2-tuples. if getall is set the return type is a set of frozensets
    of frozensets of 2-tuples ; as a cover is expressed as a set of posets

    lins : linearizations as collection of strings ; if set will override comp
    comp : a networkx induced connected component subgraph
    getall : if set will return all possible solutions
    timeout : timeout for each z3 query
    runaway_timeout : if set will return None on z3 timeout
    '''

    lins = lins if lins else list(comp.nodes)
    omega = set(lins[0])
    s = Solver()

    logger.info("Solving connected component: |S| = %s ; |Y| = %s", len(omega), len(lins))
    logger.debug("Lins: %s", lins)

    if timeout:
        s.set('timeout', timeout)
        logger.info("Timeout = %s", timeout)

    start_time = time()

    # use the naive method if insulation takes more time
    naive_method = len(lins) * (len(omega)-1) > factorial(len(omega))
    logger.debug("Revert to naive method: %s", naive_method)

    # to make relation
    def rel(name, x, y):
        return Bool('P'+name+'_'+x+'<'+y)

    # to generate swaps
    def get_swap(s):
        if type(s) == str:
            for i in range(len(s)-1):
                yield s[:i]+s[i+1]+s[i]+s[i+2:]
        else:
            for i in range(len(s)-1):
                yield s[:i]+(s[i+1],)+(s[i],)+s[i+2:]

    # non-extended linearizations
    if naive_method:
        # all the absent permutations
        bar = {''.join(p) for p in permutations(omega)} - set(lins)
    else:
        # the insulating barrier
        bar = list(filter( lambda l : l not in lins ,
                   reduce( lambda x,y : x|y ,
                   map( lambda l : set(get_swap(l)) , lins ) ) ))

    # make k posets ; worst case is size of lins
    for k in range(1, len(lins)+1):
        s.reset()

        logger.debug("Trying with %s posets!", k)

        # TODO: OPTIMIZE
        logger.debug("Encoding poset axioms..."); time1=time()
        # poset axioms : basic poset contraints
        for i in range(k):
            s.add( poset_axioms(omega , str(i)) )
        logger.debug("Done. Time = %s", round(time()-time1,4))

        # TODO: OPTIMIZE
        logger.debug("Encoding extension constraints..."); time1=time()
        # extension constraints : forall l, exists p, p covers l
        for l in lins:
            tmp = CONTRA
            for i in range(k):
                tmp = Or( tmp , le_constraints(omega , str(i) , l) )
            s.add( tmp )
        logger.debug("Done. Time = %s", round(time()-time1,4))

        # TODO: OPTIMIZE
        logger.debug("Encoding non-extension constraints..."); time1=time()
        # non-extension constraints : forall not l, forall p, p does not cover l
        for l in bar:
            for i in range(k):
                s.add( Not(le_constraints(omega , str(i) , l)) )
        logger.debug("Done. Time = %s", round(time()-time1,4))

        '''
        if log and tau:
            print('tau...', end=' ', flush=True); time1=time()
        if tau:
            # tau dist
            # TODO: all paths
            for i in range(f, f+k):
                for off, pi in enumerate(lins):
                    for tau in lins[off+1:]:
                        poles = And(le_constraints(omega , str(i) , pi), le_constraints(omega , str(i) , tau))
                        tmp = TAUTO
                        musts = set()
                        #for l in kendall[pi][tau][1:-1]:
                        for path in nx.all_shortest_paths(g, source=pi, target=tau):
                            for l in path[1:-1]:
                                musts.add( l )
                        for l in musts:
                            tmp = And(tmp, le_constraints(omega , str(i) , l) )
                        s.add( Implies(poles, tmp) )
        if log and tau:
            print('taued...', end=' ', flush=True); time2=time(); print(time2-time1, flush=True)
        '''

        # for tossing away duplicates
        covers = set()
        cover = set()
        poset = set()

        # check if size k works
        logger.debug("Checking..."); time1=time()
        result = s.check()
        logger.debug("Done. Time = %s", round(time()-time1,4))

        # cover found
        if result == sat:
            logger.info("%s works!", k)

            # get all covers NOTE: factorial time
            if getall:
                logger.debug("Finding all answers..."); time1=time()
                while result == sat:
                    m = s.model()
                    counter = TAUTO

                    # collect example
                    for i in range(k):
                        for x in omega:
                            for y in omega-{x}:
                                if m[ rel(str(i), x, y) ]:
                                    poset.add( (x,y) )
                                    counter = And( counter , rel(str(i), x, y) )
                                else:
                                    counter = And( counter , Not(rel(str(i), x, y)) )
                        cover.add(frozenset(poset))
                        poset = set()
                    covers.add(frozenset(cover))
                    cover = set()

                    # force this example to false
                    s.add( simplify(Not(counter)) )
                    result = s.check()
                logger.debug("Done. Time = %s", round(time()-time1,4))
            # get one cover
            else:
                m = s.model()

                # collect example
                for i in range(k):
                    for x in omega:
                        for y in omega-{x}:
                            if m[ rel(str(i), x, y) ]:
                                poset.add( (x,y) )
                    cover.add(frozenset(poset))
                    poset = set()

            break
        # k doesn't work meh
        else:
            if timeout and result == unknown:
                logger.info("%s timed out :/", k)
                # data collection
                logger.warning("(%s, %s, %s, %s, %s),", len(lins), len(omega), k, nx.diameter(comp), nx.radius(comp))
                # yeah you better run
                if runaway_timeout:
                    logger.info("Runaway set. I quit.")
                    return None
            else:
                logger.info("%s failed :(", k)

    # return cover(s)
    if getall:
        logger.debug("All solutions: %s", covers)
        logger.info("Component done. Time = %s", round(time()-start_time,4))
        return covers
    else:
        logger.debug("Solution: %s", cover)
        logger.info("Component done. Time = %s", round(time()-start_time,4))
        return cover

def poset_cover(lins, getall=False, timeout=None, runaway_timeout=False, render=False, dir='graphs'):
    '''
    Find the minimal poset cover for arbitrary linearizations
    '''
    omega = set(lins[0])

    logger.info("Input: |S| = %s ; |Y| = %s", len(omega), len(lins))
    logger.debug("Lins: %s", lins)
    start_time = time()

    # generate swap graph from lins
    swap_graph = nx.Graph()
    swap_graph.add_nodes_from(lins)
    for i,l1 in enumerate(lins):
        for l2 in lins[i+1:]:
            if is_swap(l1, l2):
                swap_graph.add_edge(l1, l2)

    # render swap graph
    if render:
        g = gz.Graph('G', filename=dir+'/swap_graph', format='jpg')
        if type(lins[0]) == str:
            g.attr(label='[ '+' '.join(lins)+' ]')
        else:
            g.attr(label='[ '+' '.join(map(lambda t : '-'.join(t) , lins))+' ]')
        # render components as clusters
        for i, comp in enumerate(nx.connected_components(swap_graph)):
            comp = swap_graph.subgraph(comp)
            nodes, edges = list(comp.nodes), list(comp.edges)
            if type(nodes[0]) != str:
                nodes = list(map(lambda t : '-'.join(t), nodes))
                edges = list(map(lambda p : ('-'.join(p[0]), '-'.join(p[1])), edges))
            # copy information from networkx to graphviz
            with g.subgraph(name='cluster_'+str(i+1)) as c:
                c.attr(label='Component '+str(i+1))
                for n in nodes:
                    c.node(n)
                c.edges(edges)
        g.render()
        logger.info("rendered ./%s/swap_graph.jpg", dir)

    # divide & conquer on connected components
    component_covers = []
    for i, comp in enumerate(nx.connected_components(swap_graph)):
        comp = swap_graph.subgraph(comp)
        lins = list(comp.nodes)

        # find poset cover(s) for each and every components
        covers = connected_poset_cover(comp=comp, getall=getall, timeout=timeout, runaway_timeout=runaway_timeout)

        # well shit
        if covers == None:
            continue
        else:
            component_covers.append( (lins, covers) )

        # render cover
        if render:
            for j, cover in enumerate(covers if getall else [covers]):
                g = gz.Digraph('G', filename=dir+'/comp_'+str(i+1)+'_cover_'+str(j+1), format='jpg')
                g.attr(label='Cover '+str(j+1)+' for component '+str(i+1))
                # render posets as clusters
                for k, poset in enumerate(cover):
                    with g.subgraph(name='cluster_'+str(k+1)) as c:
                        c.attr(label='Poset '+str(k+1))
                        for x,y in rm_trans_closure(omega, poset):
                            c.node('P'+str(k+1)+'_'+x, x)
                            c.node('P'+str(k+1)+'_'+y, y)
                            c.edge('P'+str(k+1)+'_'+x,'P'+str(k+1)+'_'+y)
                g.render()
                logger.info("rendered ./%s/comp_%s_cover_%s.jpg", dir, str(i+1), str(j+1))

    if covers:
        logger.debug("Solution found: %s", component_covers)
        logger.info("All done! Total time = %s", round(time()-start_time,4))
    else:
        logger.info("Failed, sorry! Total time = %s", round(time()-start_time,4))

    return covers
'''
if __name__ == '__main__':
    from exp import get_rand_lins
    from itertools import islice
    lins = list(islice(get_rand_lins(20, 20),1))[0]
    poset_cover(list(lins), render=False, timeout=300000, runaway_timeout=True, getall=False)
'''
