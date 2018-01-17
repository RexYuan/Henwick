import graphviz as gz
import networkx as nx

from z3 import *
from functools import reduce
from itertools import permutations
from graphviz import Digraph
from math import factorial
from time import time

TAUTO = BoolVal(True)
CONTRA = BoolVal(False)

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
    for i,x in enumerate(lin):
        for y in lin[i+1:]:
            ords.remove( (x,y) )

    # build constraints on name : forall r not in <lin>, r not in <name>
    for r in ords:
        constraints = simplify(And( constraints , Not(rel(*r)) ))
    return constraints

def connected_poset_cover(lins, f=1, get_constraint=False, getall=False, g=None, tau=False, log=False, breakaway_v=None, breakaway_p=None, timeout=None):
    '''
    minimal poset cover for connected lins
    '''
    omega = set(lins[0])
    s = Solver()
    constraints = TAUTO

    if timeout:
        s.set('timeout', timeout)

    if log:
        print('=> solving:', lins, flush=True)
        print('|S| =',len(omega),'|Y| =', len(lins), flush=True)
        if timeout:
            print('timeout =',timeout, flush=True)
        stime = time()

    # use the naive method if insulation takes more time
    naive_method = len(lins) * (len(omega)-1) > factorial(len(omega))

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
        if breakaway_p and k > breakaway_p:
            if log:
                print('breaking p', flush=True)
            return False
        if breakaway_v and k * len(omega)**2 > breakaway_v:
            if log:
                print('breaking v', flush=True)
            return False

        if log:
            print('>','trying',k, flush=True)
        s.reset()
        constraints = TAUTO

        if log:
            print('axm...', end=' ', flush=True); time1=time()
        # TODO: OPTIMIZE
        # poset axioms : basic poset contraints
        for i in range(f, f+k):
            s.add( simplify(poset_axioms(omega , str(i))) )
            constraints = simplify(And( constraints , simplify(poset_axioms(omega , str(i))) ))
        if log:
            print('axmed...', end=' ', flush=True); time2=time(); print(time2-time1, flush=True)

        if log:
            print('ext...', end=' ', flush=True); time1=time()
        # TODO: OPTIMIZE
        # extension constraints : forall l, exists p, p covers l
        for l in lins:
            tmp = CONTRA
            for i in range(f, f+k):
                tmp = Or( tmp , le_constraints(omega , str(i) , l) )
            s.add( simplify(tmp) )
            constraints = simplify(And( constraints , simplify(tmp) ))
        if log:
            print('exted...', end=' ', flush=True); time2=time(); print(time2-time1, flush=True)

        if log:
            print('next...', end=' ', flush=True); time1=time()
        # TODO: OPTIMIZE
        # non-extension constraints : forall not l, forall p, p does not cover l
        for l in bar:
            for i in range(f, f+k):
                s.add( simplify(Not(le_constraints(omega , str(i) , l))) )
                constraints = simplify(And( constraints , simplify(Not(le_constraints(omega , str(i) , l))) ))
        if log:
            print('nexted...', end=' ', flush=True); time2=time(); print(time2-time1, flush=True)

        if log and tau:
            print('tau...', end=' ', flush=True); time1=time()
        if tau:
            # tau dist
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

        # for tossing away duplicates
        covers = set()
        cover = set()
        poset = set()

        # check if size k works
        done = False
        if log:
            print('checking...', end=' ', flush=True); time1=time()
        result = s.check()
        if log:
            print('checked...', end=' ', flush=True); time2=time(); print(time2-time1, flush=True)

        # cover found
        if result == sat:
            if log and getall:
                print('all...', end=' ', flush=True); time1=time()

            # return constraint
            if get_constraint:
                return constraints

            # get one cover
            if not getall:
                m = s.model()

                # collect example
                for i in range(f, f+k):
                    for x in omega:
                        for y in omega-{x}:
                            if m[ rel(str(i), x, y) ]:
                                poset.add( (x,y) )
                    cover.add(frozenset(poset))
                    poset = set()

            # get all covers NOTE: factorial time
            else:
                while result == sat:
                    done = True
                    m = s.model()
                    counter = TAUTO

                    # collect example
                    for i in range(f, f+k):
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

            # found
            if log:
                if getall:
                    print('alled...', end=' ', flush=True); time2=time(); print(time2-time1, flush=True)
                print('>',k,'found', flush=True)
            break
        # add more poset
        else:
            if log:
                if timeout and result == unknown:
                    print('>',k,'timeout', flush=True)
                    with open('../timeout_table.txt','a') as fp:
                        fp.write("({}, {}, {}, {}, {}),\n".format(len(lins), len(omega), k, nx.diameter(g), nx.radius(g)))
                else:
                    print('>',k,'failed', flush=True)

    # return cover(s)
    if log:
        etime = time()
        print('time =', etime-stime, flush=True)
        if getall:
            print(covers)
        else:
            print(cover)
        print('=> done', flush=True)
    if getall:
        return covers
    else:
        return cover

def poset_cover(lins, render=False, getall=False, log=True, tau=True, dir='graphs', breakaway_p=None, breakaway_v=None, timeout=None):
    '''
    minimal poset cover for arbitrary lins
    '''
    omega = set(lins[0])
    s = Solver()
    constraints = TAUTO

    if log:
        print('==> lins:', lins, flush=True)
        pstime = time()

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
        print('rendered ./'+dir+'/swap_graph.jpg', flush=True)

    # divide & conquer on connected components
    for i, comp in enumerate(nx.connected_components(swap_graph)):
        comp = swap_graph.subgraph(comp)
        ls = list(comp.nodes)

        # find poset cover(s) for each and every components
        covers = connected_poset_cover(ls, getall=getall, g=comp, tau=tau, log=log, breakaway_p=breakaway_p, breakaway_v=breakaway_v, timeout=timeout)

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
                print('rendered ./'+dir+'/comp_'+str(i+1)+'_cover_'+str(j+1)+'.jpg', flush=True)

    if log:
        petime = time()
        print('all time:',petime-pstime, flush=True)
        print('==> all done\n', flush=True)

    return covers
