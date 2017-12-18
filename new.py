import graphviz as gz
import networkx as nx

from z3 import *
from functools import reduce
from itertools import permutations
from graphviz import Digraph

TAUTO = BoolVal(True)
CONTRA = BoolVal(False)

def get_order(s):
    t = set()
    for i in range(len(s)):
        for j in range(i+1, len(s)):
            t.add((s[i],s[j]))
    return t

def order_n_intersect(ss):
    rs = get_order(ss[0])
    for s in ss:
        rs = rs & get_order(s)
    return rs

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

def swap_graph(ss):
    g = nx.Graph()
    g.add_nodes_from(ss)
    for i in range(len(ss)):
        for j in range(i+1, len(ss)):
            if is_swap(ss[i], ss[j]):
                g.add_edge(ss[i], ss[j])
    return g

def render_graph(ng):
    g = gz.Graph('G', filename='graphs/swap_graph', format='jpg')
    for n in ng.nodes:
        g.node(n)
    g.edges(ng.edges)
    #g.render()
    #print('rendered ./graphs/swap_graph.jpg')
    g.view()

def add_l(ng, l):
    ng.add_node(l)
    for s in ng.nodes:
        if is_swap(s, l):
            ng.add_edge(s, l)
    return ng

def components(ng):
    for g in nx.connected_components(ng):
        yield ng.subgraph(g)

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
        return Bool(name+'_'+x+'<'+y)
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
        return Bool(name+'_'+x+'<'+y)
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

def get_all_posets(universe, name, constraints):
    def rel(x, y):
        return Bool(name+'_'+x+'<'+y)
    omega = set(universe)
    s = Solver()

    s.add(constraints)
    while s.check() == sat:
        ords = set()
        counter = TAUTO

        m = s.model()
        for x in omega:
            for y in omega-{x}:
                if m[ rel(x,y) ]:
                    ords.add( (x,y) )
                    counter = simplify(And( counter , rel(x,y) ))
                else:
                    counter = simplify(And( counter , Not(rel(x,y)) ))
        yield ords

        s.add( Not(counter) )

def connected_poset_cover(lins):
    '''
    minimal poset cover for connected lins
    '''
    omega = set(lins[0])
    s = Solver()
    constraints = TAUTO

    # to generate swaps
    def get_swap(s):
        for i in range(len(s)-1):
            yield s[:i]+s[i+1]+s[i]+s[i+2:]

    # find the insulating barrier
    bar = filter( lambda l : l not in lins ,
                  reduce( lambda x,y : x|y ,
                          map( lambda l : set(get_swap(l)) , lins ) ) )

    # worst case is size of lins
    for k in range(2, len(lins)+1):
        s.reset()

        # make k posets
        for i in range(1, k+1):
            # poset axioms : basic poset contraints
            s.add( simplify(poset_axioms(omega , 'P'+str(i))) )
            constraints = simplify(And( constraints , simplify(poset_axioms(omega , 'P'+str(i))) ))

        # extension constraints : forall l, exists p, p covers l
        for l in lins:
            tmp = CONTRA
            for i in range(1, k+1):
                tmp = Or( tmp , le_constraints(omega , 'P'+str(i) , l) )
            s.add( simplify(tmp) )
            constraints = simplify(And( constraints , simplify(tmp) ))

        # non-extension constraints : forall not l, forall p, p does not cover l
        for l in bar:
            for i in range(1, k+1):
                s.add( simplify(Not(le_constraints(omega , 'P'+str(i) , l))) )
                #pA = CONTRA
                #for i in range(len(l)):
                #    for j in range(i+1,len(l)):
                #        pA = Or(pA , Bool('P'+str(i)+'_'+l[j]+'<'+l[i]))
                #s.add(pA)
                constraints = simplify(And( constraints , simplify(Not(le_constraints(omega , 'P'+str(i) , l))) ))

        # check if size k works
        done = False
        while s.check() == sat:
            done = True
            m = s.model()
            counter = TAUTO
            for i in range(1, k+1):
                for x in omega:
                    for y in omega-{x}:
                        if m[ Bool('P'+str(i)+'_'+x+'<'+y) ]:
                            print('P'+str(i)+'_'+x+'<'+y,' ',end='')
                            counter = And(counter, Bool('P'+str(i)+'_'+x+'<'+y))
                        else:
                            counter = And(counter, Not(Bool('P'+str(i)+'_'+x+'<'+y)))

            s.add(Not(simplify(counter)))
            #print(simplify(counter))
            print()
        if done:
            break



def poset_cover(k, lins):
    omega = set(lins[0])
    s = Solver()

    # helper function : generate adjacent transposed linearizations
    def get_swap(s):
        for i in range(len(s)-1):
            yield s[:i]+s[i+1]+s[i]+s[i+2:]

    # helper function : if s1 s2 are adjacent transposed
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

    # poset axioms : basic poset contraints
    for i in range(k):
        s.add( poset_axioms(omega , 'P'+str(i+1)) )

    # extension constraints : forall l, exists p, p covers l
    for l in lins:
        tmp = CONTRA
        for i in range(k):
            tmp = simplify(Or( tmp , le_constraints(omega , 'P'+str(i+1) , l) ))
        s.add( tmp )

    # find poset cover for each and every components
    bar = set()
    for comp in nx.connected_components(swap_graph):
        comp = swap_graph.subgraph(comp)

        # find the insulating barrier
        for l in comp.nodes:
            for f in get_swap(l):
                if f not in comp.nodes:
                    bar.add(f)

    # non-extension constraints
    # l not generated by any p : (absent)
    # forall p, exists l_x<y, p_y<x
    for pname, p in ps.items():
        for w in bar:
            pA = F
            for i in range(len(w)):
                for j in range(i+1,len(w)):
                    pA = Or(pA , v(p.name+w[j]+'<'+w[i]))
            c_s.add(pA)
            constraints = simplify(And(constraints , pA))

    if solve:
        covers = set()
        cover = set()
        poset = set()

        result = c_s.check()
        i = 1
        print('---cover for : [ ', ' '.join(lins), ' ]---')
        if result == sat:
            m = c_s.model()
            print('cover',i,' : ',end='')
            counter = T
            for pname, p in ps.items():
                for x in universe:
                    for y in universe-{x}:
                        if m[v(p.name+x+'{'+y)]:
                            poset.add((x,y))
                            print(p.name+x+'{'+y,' ',end='')
                        if m[v(p.name+x+'<'+y)]:
                            print(p.name+x+'<'+y,' ',end='')
                            counter = And(counter, v(p.name+x+'<'+y))
                        else:
                            counter = And(counter, Not(v(p.name+x+'<'+y)))
                cover.add(frozenset(poset))
                poset = set()
            #print('\n',simplify(counter))
            c_s.add(Not(simplify(counter)))
            result = c_s.check()
            i = i+1
            print()

            covers.add(frozenset(cover))
            cover = set()
        print('---end---\n')

        # render
        done = True if covers else False
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

    return done
