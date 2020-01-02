
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
hyp = And(Not(x1),Not(x2))
hypp = And(Not(x1p),Not(x2p))

def eqv(hyp):
    s.reset()
    s.add( Not(Implies(inits, hyp)) )
    s.add( Not(Implies(hyp, Not(bads))) )
    s.add( Not(Implies(And(trans, hyp), hypp)) )

    return s.check() == unsat

#print(eqv(hyp))

def inits(s):
    return s == '0000'
def bads(s):
    return s[0] == '1'
def trans(s1, s2):
    mod = int('1000',2)
    return int(s1,2)%mod + 1 == int(s2)%mod
def hyp(s):
    return s[0] != '1' and s[1] != '1'
