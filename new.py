import graphviz as gz
import networkx as nx

from z3 import *
from functools import reduce
from itertools import permutations
from graphviz import Digraph

TAUTO = BoolVal(True)
CONTRA = BoolVal(False)

def order_graph(rs):
    g = nx.Graph()
    g.add_edges_from(rs)
    return g

def render_order(ng):
    g = gz.Graph('G', filename='graphs/order_graph', format='jpg')
    for n in ng.nodes:
        g.node(n)
    g.edges(ng.edges)
    g.view()

def render_graph(ng):
    g = gz.Graph('G', filename='graphs/swap_graph', format='jpg')
    for n in ng.nodes:
        g.node(n)
    g.edges(ng.edges)
    #g.render()
    #print('rendered ./graphs/swap_graph.jpg')
    g.view()

def trans_closure(ss):
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

def connected_poset_cover(lins, f=1, get_constraint=False):
    '''
    minimal poset cover for connected lins
    '''
    omega = set(lins[0])
    s = Solver()
    constraints = TAUTO

    # to make relation
    def rel(name, x, y):
        return Bool('P'+name+'_'+x+'<'+y)

    # to generate swaps
    def get_swap(s):
        for i in range(len(s)-1):
            yield s[:i]+s[i+1]+s[i]+s[i+2:]

    # find the insulating barrier
    bar = list(filter( lambda l : l not in lins ,
               reduce( lambda x,y : x|y ,
               map( lambda l : set(get_swap(l)) , lins ) ) ))

    # make k posets ; worst case is size of lins
    for k in range(1, len(lins)+1):
        s.reset()
        constraints = TAUTO

        # poset axioms : basic poset contraints
        for i in range(f, f+k):
            s.add( simplify(poset_axioms(omega , str(i))) )
            constraints = simplify(And( constraints , simplify(poset_axioms(omega , str(i))) ))

        # extension constraints : forall l, exists p, p covers l
        for l in lins:
            tmp = CONTRA
            for i in range(f, f+k):
                tmp = Or( tmp , le_constraints(omega , str(i) , l) )
            s.add( simplify(tmp) )
            constraints = simplify(And( constraints , simplify(tmp) ))

        # non-extension constraints : forall not l, forall p, p does not cover l
        for l in bar:
            for i in range(f, f+k):
                s.add( simplify(Not(le_constraints(omega , str(i) , l))) )
                constraints = simplify(And( constraints , simplify(Not(le_constraints(omega , str(i) , l))) ))

        # for tossing away duplicates
        covers = set()
        cover = set()
        poset = set()

        # check if size k works
        done = False
        result = s.check()

        # return constraint with satisfying number of posets
        if get_constraint and result == sat:
            return constraints

        # get all covers
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

        # return all covers if found
        if covers:
            return covers
        else:
            print(k,'failed')

def poset_cover(lins):
    '''
    minimal poset cover for arbitrary lins
    '''
    omega = set(lins[0])
    s = Solver()
    constraints = TAUTO

    # if s1 s2 are off by one swap
    def is_swap(s1, s2):
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

    # generate swap graph from lins
    swap_graph = nx.Graph()
    swap_graph.add_nodes_from(lins)
    for i,l1 in enumerate(lins):
        for l2 in lins[i+1:]:
            if is_swap(l1, l2):
                swap_graph.add_edge(l1, l2)

    # divide & conquer on connected components
    for comp in nx.connected_components(swap_graph):
        comp = swap_graph.subgraph(comp)
        lins = comp.nodes

        # find poset cover for each and every components
        covers = connected_poset_cover(lins)



        '''
        g = gz.Graph('G', filename='graphs/swap_graph', format='jpg')
        for n in swap_graph.nodes:
            g.node(n)
        g.edges(swap_graph.edges)
        g.render()

        done = False
        for i, cover in enumerate(covers):
            done = True
            g = Digraph('G', filename='graphs/cover_'+str(i), format='jpg')
            g.attr(label='Cover '+str(i))
            for j, poset in enumerate(cover):
                with g.subgraph(name='cluster_'+str(j)) as c:
                    c.attr(color='black')
                    c.attr(label='Poset '+str(j))
                    c.node_attr.update(style='filled', color='white')
                    for x,y in poset:
                        c.edge('P'+str(j)+'_'+x,'P'+str(j)+'_'+y)
            g.render()
            print('rendered ./graphs/cover_'+str(i)+'.jpg')
        '''
