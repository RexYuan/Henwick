import graphviz as gz

# a poset described by its cover relation

def nbit_order(bit):
    def flip(bits, i):
        return bits[:i]+'1'+bits[i+1:]
    top = '0' * bit
    bot = '1' * bit
    rel = []
    seen = {top}

    def recurse(parent):
        if parent == bot:
            return
        for i in range(bit):
            flipped = flip(parent,i)
            if parent[i] == '0':
                rel.append( (parent, flipped) )
                if flipped not in seen:
                    seen.add(flipped)
                    recurse(flipped)
    recurse(top)
    return rel

def visualize(rel,f=None,bits=None,filename='tmp'):
    g = gz.Digraph('G', filename=filename, format='jpg')
    if f:
        for i in range(2**bits):
            bs = "{:0>{w}b}".format(i, w=bits)
            if f(bs):
                g.attr('node', shape='box')
            else:
                g.attr('node', shape='ellipse')
            g.node(bs)
    g.edges(rel)
    g.view(cleanup=True)

def xor_transform(rel, a):
    def sxor(a,b):
        tab = {('0','0'): '0', ('0','1'): '1', ('1','0'): '1', ('1','1'): '0'}
        return tab[a,b]
    def strxor(x,y):
        s = ''
        for i in range(len(x)):
            s+=sxor(x[i],y[i])
        return s
    rel = list(rel)
    for i in range(len(rel)):
        t,h = rel[i]
        rel[i] = (strxor(t,a),strxor(h,a))
    return rel
