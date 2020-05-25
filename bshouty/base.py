
from abc import *
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
    print(a, type(a))
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
        return any(subseteq(t, a) for t in ts)
    return dnff

def z3_bool_range(*argv : int) -> Iterator[ z3Formula ]:
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

def learn_cdnf(mem_oracle : BoolFunc, eqi_oracle : Callable[ [BoolFunc] , Optional[Assignment] ], bits : int):
    def bs_flip(bs : BitString, i : int) -> BitString:
        return BitString( bs[:i]+('0' if bs[i] == '1' else '1')+bs[i+1:] )

    def walk(v : Assignment, a : Assignment, f : BoolFunc) -> Assignment:
        bs_v,bs_a = asgmt_to_bs(v,bits),asgmt_to_bs(a,bits)
        more : bool = True
        while more:
            more = False
            for i,(vi,ai) in enumerate(zip(bs_v,bs_a)):
                flipped_v = bs_flip(bs_v,i)
                if vi != ai and f( bs_to_asgmt(flipped_v) ):
                    bs_v = flipped_v
                    more = True
                    break
        return bs_to_asgmt(bs_v)
    
    def hyptize(learnd_terms_comp : Dnf, basis_comp : Assignment) -> BoolFunc:
        def h(x : Assignment) -> bool:
            x = xor(x,basis_comp)
            return mk_dnff(learnd_terms_comp)(x)
        return h

    basis : List[ Assignment ] = []
    ce : Optional[ Assignment ] = eqi_oracle( (lambda _: True) )
    if ce is None:
        return True
    basis.append(ce)

    learnd_terms : List[ Dnf ] = [ set() ]
    hypted_funcs : List[ BoolFunc ] = [ (lambda _: False) ]
    conj_hypts : BoolFunc = (lambda bs: all(h(bs) for h in hypted_funcs))
    ce = eqi_oracle(conj_hypts)

    while ce is not None:
        unaligned : List[ int ] = [i for i,h in enumerate(hypted_funcs) if not h(ce)]
        while unaligned == []:
            assert ce is not None # guarded by loop
            basis.append(ce)
            learnd_terms.append( set() )
            hypted_funcs.append( (lambda _: False) )
            conj_hypts = (lambda bs: all(h(bs) for h in hypted_funcs))
            ce = eqi_oracle(conj_hypts)
            assert ce is not None # since adding new basis restarts whole hypothesis
            unaligned = [i for i,h in enumerate(hypted_funcs) if not h(ce)]

        for i in unaligned:
            walked_ce = walk(ce, basis[i], mem_oracle)
            learnd_terms[i] = learnd_terms[i] | { xor(walked_ce,basis[i]) }
            hypted_funcs[i] = hyptize(learnd_terms[i], basis[i])

        conj_hypts = (lambda bs: all(h(bs) for h in hypted_funcs))
        ce = eqi_oracle(conj_hypts)
    return learnd_terms, hypted_funcs, conj_hypts, basis

def tabulate(f, bits):
    for i in range(2**bits):
        bs = "{:0>{w}b}".format(i, w=bits)
        b = bs_to_asgmt(bs)
        print(bs, '1' if f(b) else '0')
def eqi(f1, f2, bits):
    for i in range(2**bits):
        bs = "{:0>{w}b}".format(i, w=bits)
        bs = bs_to_asgmt(bs)
        if f1(bs) != f2(bs):
            #print('counter-example:',bs)
            return bs
    return None

def basic_test():
    def target(s):
        return s in {0b100,0b110,0b001}
    def mem_oracle(s):
        return target(s)
    def eqi_oracle(h):
        return eqi(h, target, 3)
    
    _,_,ret2f,b2 = learn_cdnf(mem_oracle, eqi_oracle, 3)
    if not eqi(ret2f,target,3):
        tabulate(ret2f,3)
        raise Exception("error: basic cdnf")
basic_test()