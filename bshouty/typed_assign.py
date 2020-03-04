
from collections.abc import *
from typing import *
from z3 import *

######## to shut the linter up, remove for production
z3Formula = BoolRef # type: ignore
z3Model = ModelRef # type: ignore
z3Sat = CheckSatResult # type: ignore
######## remove for production

Assignment = NewType('Assignment', int)
BoolFunc = Callable[ [Assignment] , bool ]
BitString = NewType('BitString', str)

Term = Assignment
Dnf = AbstractSet[ Term ]
Cdnf = AbstractSet[ Dnf ]

def subseteq(a1 : Assignment, a2 : Assignment) -> bool:
    return (a1 & a2) == a1

def xor(a1 : Assignment, a2 : Assignment) -> Assignment:
    return Assignment( a1 ^ a2 )

def asgmt_to_bs(a : Assignment, bits : int) -> BitString:
    return BitString( bin(a)[2:].zfill(bits) )

def bs_to_asgmt(bs : BitString) -> Assignment:
    return Assignment( int(bs, base=2) )

def asgmt_to_z3_term(a : Assignment, bits : int) -> z3Formula:
    return And( [Bool(i) if (a >> i) & 0b1 == 0b1 else Not(Bool(i)) for i in range(bits-1, 0, -1)] )

def bs_to_z3_term(bs : BitString) -> z3Formula:
    return asgmt_to_z3_term( bs_to_asgmt(bs), len(bs) )

def asgmt_to_z3_mterm(a : Assignment, bits : int) -> z3Formula:
    vs = []
    r = cast(int, a)
    for i in range(bits):
        if (r & 0b1) == 0b1:
            vs.append(Bool(i))
        r = r >> 1
    return And( vs )

def z3_model_to_asgmt(md : z3Model, bits : int) -> Assignment:
    bs = "".join( ['1' if md[Bool(i)] else '0' for i in range(bits)] )
    return Assignment( int(bs, base=2) )

def mk_termf(t : Term) -> BoolFunc:
    def termf(a : Assignment) -> bool:
        return subseteq(a, t)
    return termf

def mk_dnff(ts : Dnf) -> BoolFunc:
    def dnff(a : Assignment) -> bool:
        return any(subseteq(a, t) for t in ts)
    return dnff

def z3_bool_range(*argv):
    if len(argv) == 1:
        bits = argv[0]
        for i in range(bits):
            yield Bool(i)
    elif len(argv) == 2:
        start = argv[0]
        bits = argv[1]
        for i in range(start,bits):
            yield Bool(i)
    elif len(argv) == 3:
        start = argv[0]
        bits = argv[1]
        step = argv[2]
        for i in range(start,bits,step):
            yield Bool(i)

class InvTeacher:
    def __init__(self, bits : int, inits : z3Formula, bads : z3Formula, trans : z3Formula) -> None:
        self.bits = bits
        self.inits = inits
        self.bads = bads
        self.trans = trans
        self.s = Solver()

    def check_valid(self, form : z3Formula) -> Optional[ Assignment ]:
        self.s.reset()
        self.s.add( form )
        if self.s.check() != unsat:
            return z3_model_to_asgmt( self.s.model() , self.bits )
        return None
    
    def check_inits(self, hyp : z3Formula) -> Optional[ Assignment ]:
        return self.check_valid( Not(Implies(self.inits , hyp)) )
    
    def check_bads(self, hyp : z3Formula) -> Optional[ Assignment ]:
        return self.check_valid( Not(Implies(hyp , self.bads)) )
    
    def check_trans(self, hyp : z3Formula) -> Optional[ Assignment ]:
        hypp = substitute( hyp , *zip(z3_bool_range(self.bits),
                                    z3_bool_range(self.bits,self.bits*2)) )
        return self.check_valid( Not(Implies(And(hyp,self.trans) , hypp)) )

class CdnfLearner:
    def __init__(self, oracle : InvTeacher) -> None:
        self.oracle = oracle
        self.basis : List[Assignment] = []
        self.dnfs : List[Dnf] = []
        self.dnf_funcs : List[BoolFunc] = []
        self.og_dnfs : List[Dnf] = []
        self.z3_forms : List[z3Formula] = []
