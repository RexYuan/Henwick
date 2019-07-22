
def tabulate(f, bits):
    for i in range(2**bits):
        bs = "{:0>{w}b}".format(i, w=bits)
        print(bs, '1' if f(bs) else '0')

def sxor(a,b):
    tab = {('0','0'): '0', ('0','1'): '1', ('1','0'): '1', ('1','1'): '0'}
    return tab[a,b]
def strxor(x,y):
    s = ''
    for i in range(len(x)):
        s+=sxor(x[i],y[i])
    return s

def target(s):
    # a xor c
    return s in {'100','110','001','011'}

def eqi(f1, f2, bits):
    for i in range(2**bits):
        bs = "{:0>{w}b}".format(i, w=bits)
        if f1(bs) != f2(bs):
            print('counter-example:',bs)
            return bs
    return True

def mem_oracle(s):
    return target(s)

def eqi_oracle(h):
    return eqi(h, target, 3)

def walk(v, a, f, bits):
    def flip(s, i):
        return s[:i]+('0' if s[i] == '1' else '1')+s[i+1:]
    more = True
    while more:
        more = False
        for i in range(bits):
            if v[i] != a[i] and f(flip(v, i)):
                v = flip(v, i)
                more = True
                break
    return v

def M_term(s):
    # represented as a list of indices
    tmp = []
    for i,b in enumerate(s):
        if b == '1':
            tmp.append(i)
    return tmp

def M_dnf(ss):
    #represented as a list of M-terms
    return list(map(M_term, ss))

def make_H(md, a):
    def h(s):
        s = strxor(s,a)
        ms = M_term(s)
        for mt in md:
            if all(b in ms for b in mt):
                return True
        return False
    return h

def conj_H(hs):
    return (lambda s: all(h(s) for h in hs))

def L(mem_oracle, eqi_oracle, bases):
    ss = [[] for _ in bases]
    hs = [(lambda s: False) for _ in bases]
    v = eqi_oracle(conj_H(hs))
    while v != True:
        todo_Is = [i for i,h in enumerate(hs) if not h(v)]
        for i in todo_Is:
            ai = bases[i]
            vi = walk(v, ai, mem_oracle, len(v))
            ss[i].append(strxor(vi,ai))
            hs[i] = make_H(M_dnf(ss[i]), ai)
        v = eqi_oracle(conj_H(hs))
    print(ss)
    return ss, hs

# [100,001], [001,100]
L(mem_oracle, eqi_oracle, ['010', '101'])
