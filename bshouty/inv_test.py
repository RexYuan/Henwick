
from z3cdnf import *

total_bits = 4
s = Solver()
x1,x2,x3,x4,x1p,x2p,x3p,x4p = z3_bool_range(total_bits*2)
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
def oracle(hyp):
    hypp = substitute(hyp, *[ (Bool(str(i)),Bool(str(i+total_bits))) for i in range(total_bits) ])
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
h = And(Not(x2),Not(x2))
hp = And(Not(x1p),Not(x2p))

def oracle2(hyp):
    print(hyp)
    s.reset()
    s.add( Not(And( Implies(trans,hyp) , Implies(hyp,trans) )) )
    
    if s.check() != unsat:
        print(s.model())
        return s.model()
    return True
m = z3_CDNFAlgo(oracle2, 8)