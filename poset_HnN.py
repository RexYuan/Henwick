import graphviz as gz
import networkx as nx

from random import choice

from poset_partial import get_linearizations

def is_swap(s1, s2, get_pair=False):
    the_pair = None
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
                the_pair = frozenset({s1[i], s1[i+1]})
                i += 1
            else:
                return False
        i += 1
    return pair if not get_pair else the_pair

def trans_closure(ss):
    '''
    ss : set of tuples
    '''
    t = set(ss)
    while True:
        changed = False
        for x in ss:
            for y in ss:
                if x[1] == y[0] and (x[0],y[1]) not in t:
                    t.add( (x[0],y[1]) )
                    changed = True
        if not changed:
            break
    return t

def lin_trans_closure(s):
    '''
    s : string
    '''
    t = set()
    for i, x in enumerate(s):
        for y in s[i+1:]:
            t.add( (x,y) )
    return t

def Trim(A, UpsilonPrime, Delta):
    '''
    Ensure that UpsilonPrime is in L(min A)
    and that A contains all order relation implied by Delta and UpsilonPrime
    '''
    # done <- FALSE
    done = False

    # while NOT done
    while not done:
        # do done <- TRUE
        done = True
        # for L in Delta
        for L in Delta:
            # do for i <- 1 to n-1
            for i in range(len(L)-1):
                # do LPrime <- Swap[L;i]
                LPrime = L[:i]+L[i+1]+L[i]+L[i+2:]
                # if LPrime not in UpsilonPrime
                if LPrime not in UpsilonPrime:
                    # then A <- A union { (L[i], L[i+1]) }
                    A = A | { (L[i], L[i+1]) }

        removes = set()
        # for L in UpsilonPrime
        for L in UpsilonPrime:
            # do if L not in L(min A)
            if not all(e in lin_trans_closure(L) for e in trans_closure(A)):
                # then UpsilonPrime <- UpsilonPrime \ {L}
                removes.add(L)
                # done <- False
                done = False
        # dirty fix since set size can't change during iteration
        UpsilonPrime = UpsilonPrime - removes

    # return (A, UpsilonPrime)
    return (A, UpsilonPrime)

def partial_cover(Upsilon, L):
    '''

    '''
    assert(L in Upsilon)

    # Delta <- {L}
    Delta = {L}

    # Set UpsilonPrime to the set of linear orders in the connected component of G(Y) that contains L
    swap_graph = nx.Graph()
    swap_graph.add_nodes_from(Upsilon)
    for i,l1 in enumerate(Upsilon):
        for l2 in Upsilon[i+1:]:
            if is_swap(l1, l2):
                swap_graph.add_edge(l1, l2)
    for i, comp in enumerate(nx.connected_components(swap_graph)):
        comp = swap_graph.subgraph(comp)
        if L in comp.nodes:
            UpsilonPrime = set(comp.nodes)
            break

    # A <- empty set
    A = set()
    #B <- empty set
    B = set()

    # (A, UpsilonPrime) <- Trim(A, UpsilonPrime, Delta)
    A, UpsilonPrime = Trim(A, UpsilonPrime, Delta)

    # Set UpsilonPrime to the set of linear orders in the connected component of G(Y) that contains L
    swap_graph = nx.Graph()
    swap_graph.add_nodes_from(Upsilon)
    for i,l1 in enumerate(Upsilon):
        for l2 in Upsilon[i+1:]:
            if is_swap(l1, l2):
                swap_graph.add_edge(l1, l2)
    for i, comp in enumerate(nx.connected_components(swap_graph)):
        comp = swap_graph.subgraph(comp)
        if L in comp.nodes:
            UpsilonPrime = set(comp.nodes)
            break

    # while UpsilonPrime =/= Delta
    while UpsilonPrime != Delta:
        # NOTE: i figured it out! this is the problem! should be select L1,L2 scuh that...
        #       if you select L1 first then you may not be able to find a L2
        #       but there is always a pair of L1,L2 as long as Y' != D (proof?)
        # NOTE: thus the bug of infinite loop is resolved
        # do Select L1 in Delta and L2 in UpsilonPrime\Delta such that L1 <-> L2
        L1 = choice(tuple(Delta))
        L2 = choice(tuple(UpsilonPrime - Delta))
        while not is_swap(L1 , L2):
            L1 = choice(tuple(Delta))
            L2 = choice(tuple(UpsilonPrime - Delta))

        # Delta <- Delta U {L2}
        Delta = Delta | {L2}
        # B <- B U {SwapPair(L1,L2)}
        B = B | {is_swap(L1,L2,get_pair=True)}
        # (A, UpsilonPrime) <- Trim(A, UpsilonPrime, Delta)
        A, UpsilonPrime = Trim(A, UpsilonPrime, Delta)
        # again <- True
        again = True
        # while again
        while again:
            # do again <- False
            again = False
            # for L3 in UpsilonPrime
            for L3 in UpsilonPrime:
                # do for {a,b} in B
                for a,b in B:
                    # do if a {L3 b or b {L3 a
                    if a+b in L3 or b+a in L3:
                        mid,rev = (a+b,b+a) if a+b in L3 else (b+a,a+b)
                        # then L4 <- Swap[L3;{a,b}]
                        L4 = L3.replace(mid,rev)
                        # if L4 not in UpsilonPrime then UpsilonPrime <- UpsilonPrime \ {L3}
                        if L4 not in UpsilonPrime:
                            UpsilonPrime = UpsilonPrime - {L3}
                            # (A, UpsilonPrime) <- Trim(A, UpsilonPrime, Delta)
                            A, UpsilonPrime = Trim(A, UpsilonPrime, Delta)
                            # again <- True
                            again = True
        # Set UpsilonPrime to the set of linear orders in the connected component of G(Y') that contains L
        swap_graph = nx.Graph()
        swap_graph.add_nodes_from(UpsilonPrime)
        UP = list(UpsilonPrime)
        for i,l1 in enumerate(UP):
            for l2 in UP[i+1:]:
                if is_swap(l1, l2):
                    swap_graph.add_edge(l1, l2)
        for i, comp in enumerate(nx.connected_components(swap_graph)):
            comp = swap_graph.subgraph(comp)
            if L in comp.nodes:
                UpsilonPrime = set(comp.nodes)
                break
    # return (A,B,Delta)
    return (A, B, Delta)

'''
lins1 = [
'afbced',
'afbecd',
'abfecd',
'bfaced',
'bafced',
'abfced',
'bacfed',
'abcfed',
'bacefd',
'abcefd'
]
for _ in range(100):
    print(partial_cover(lins1, 'abfced')[2])
'''
