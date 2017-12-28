import graphviz as gz
import networkx as nx

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

def lin_trans_closure(s):
    '''
    ss : string
    '''
    t = set()
    for i, x in enumerate(s):
        for y in s[i+1:]:
            t.add(x+'<'+y)
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
        for L in Delta::
            # do for i <- 1 to n-1
            for i in range(1, n):
                # do LPrime <- Swap[L;i]
                LPrime = L[:i]+L[i+1]+L[i]+L[i+2:]
                    # if LPrime not in UpsilonPrime
                    if LPrime not in UpsilonPrime:
                        # then A <- A union { (L[i], L[i+1]) }
                        A = A | { (L[i], L[i+1]) }

        # for L in UpsilonPrime
        for L in UpsilonPrime:
            # do if L not in L(min A)
            if not all(e in lin_trans_closure(L) for e in trans_closure(A)):
                # then UpsilonPrime <- UpsilonPrime \ {L}
                UpsilonPrime.remove(L)
                # done <- False
                done = False

    # return (A, UpsilonPrime)


def partial_cover(lins, l):
    '''
    find the poset with the most linearizations within lins that also
    blanket l
    '''
    assert(l in lins)

    # delta <- L
    Delta = set(l)

    # Set Upsilon' to the set of linear orders in the connected
    # component of G(Y) that contains L
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

    swap_graph = nx.Graph()
    swap_graph.add_nodes_from(lins)
    for i,l1 in enumerate(lins):
        for l2 in lins[i+1:]:
            if is_swap(l1, l2):
                swap_graph.add_edge(l1, l2)

    for i, comp in enumerate(nx.connected_components(swap_graph)):
        comp = swap_graph.subgraph(comp)
        if l in comp.nodes:
            UpsilonPrime = comp
            break

    # A <- empty set; B <- empty set
    A = set()
    B = set()

    # (A, UpsilonPrime) <- TRIM(A, UpsilonPrime, Delta)
