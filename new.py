import graphviz as gz
import networkx as nx

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
