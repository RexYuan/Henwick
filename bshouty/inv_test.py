
from z3 import *
from cdnf import *

s = Solver()
x1,x2,x3,x4 = Bools('x1 x2 x3 x4')
x1p,x2p,x3p,x4p = Bools('x1p x2p x3p x4p')

inits = And(Not(x1),Not(x2),Not(x3),Not(x4))
bads = x1
trans = Or(
And(Not(x1),Not(x2),Not(x3),Not(x4),
    Not(x1p),Not(x2p),Not(x3p),x4p),
And(Not(x1),Not(x2),Not(x3),x4,
    Not(x1p),Not(x2p),x3p,Not(x4p)),
And(Not(x1),Not(x2),x3,Not(x4),
    Not(x1p),Not(x2p),x3p,x4p),
And(Not(x1),Not(x2),x3,x4,
    Not(x1p),Not(x2p),Not(x3p),Not(x4p))
)
h = And(Not(x2),Not(x2))
hp = And(Not(x1p),Not(x2p))

def eqv(hyp,hypp):
    s.reset()
    s.add( Not(Implies(inits, hyp)) )
    if s.check() != unsat:
        print("c1:")
        return s.model()
    s.reset()
    s.add( Not(Implies(hyp, Not(bads))) )
    if s.check() != unsat:
        print("c2:")
        return s.model()
    s.reset()
    s.add( Not(Implies(And(trans, hyp), hypp)) )
    if s.check() != unsat:
        print("c3:")
        return s.model()
    return True

r = eqv(h,hp)
print(r)

'''
def inits(s):
    return s == '0000'
def bads(s):
    return s[0] == '1'
def trans(s1, s2):
    mod = int('1000',2)
    return int(s1,2)%mod + 1 == int(s2)%mod
def hyp(s):
    return s[0] != '1' and s[1] != '1'
'''