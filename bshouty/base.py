
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
Clause = Term
Dnf =  AbstractSet[ Term ]
Cnf = Dnf
Cdnf = AbstractSet[ Dnf ]
Dcnf = Cdnf

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

def mk_mterm_f(t : Term) -> BoolFunc:
    def termf(a : Assignment) -> bool:
        return subseteq(t, a)
    return termf

def mk_mdnf_f(ts : Dnf) -> BoolFunc:
    def dnff(a : Assignment) -> bool:
        return any(subseteq(t, a) for t in ts)
    return dnff

def mk_mcnf_f(cs : Cnf) -> BoolFunc:
    def cnff(a : Assignment) -> bool:
        return not any(subseteq(c, a) for c in cs)
    return cnff

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
            return mk_mdnf_f(learnd_terms_comp)(x)
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

def dc_hyptize(learnd_terms_comp, basis_comp):
    def mclause(bs):
        return [i for i,b in enumerate(bs) if b == '1']

    def mzeros(bs):
        return [i for i,b in enumerate(bs) if b == '0']

    def mcnf(bss):
        return map(mclause, bss)

    def h(bs):
        bs = bsxor(bs,basis_comp)
        bst = mzeros(bs)
        return all(any(i in bst for i in t) for t in mcnf(learnd_terms_comp))
    return h

def learn_dcnf(mem_oracle : BoolFunc, eqi_oracle : Callable[ [BoolFunc] , Optional[Assignment] ], bits : int):
    def bs_flip(bs : BitString, i : int) -> BitString:
        return BitString( bs[:i]+('0' if bs[i] == '1' else '1')+bs[i+1:] )

    def walk(v : Assignment, a : Assignment, f : BoolFunc) -> Assignment:
        bs_v,bs_a = asgmt_to_bs(v,bits),asgmt_to_bs(a,bits)
        more : bool = True
        while more:
            more = False
            for i,(vi,ai) in enumerate(zip(bs_v,bs_a)):
                flipped_v = bs_flip(bs_v,i)
                if vi != ai and not f( bs_to_asgmt(flipped_v) ):
                    bs_v = flipped_v
                    more = True
                    break
        return bs_to_asgmt(bs_v)
    
    def hyptize(learnd_terms_comp : Cnf, basis_comp : Assignment) -> BoolFunc:
        def h(x : Assignment) -> bool:
            x = xor(x,basis_comp)
            return mk_mcnf_f(learnd_terms_comp)(x)
        return h

    basis : List[ Assignment ] = []
    ce : Optional[ Assignment ] = eqi_oracle( (lambda _: False) )
    if ce is None:
        return True
    basis.append(ce)

    learnd_terms : List[ Cnf ] = [ set() ]
    hypted_funcs : List[ BoolFunc ] = [ (lambda _: True) ]
    disj_hypts : BoolFunc = (lambda bs: any(h(bs) for h in hypted_funcs))
    ce = eqi_oracle(disj_hypts)

    while ce is not None:
        unaligned : List[ int ] = [i for i,h in enumerate(hypted_funcs) if h(ce)]
        while unaligned == []:
            assert ce is not None # guarded by loop
            basis.append(ce)
            learnd_terms.append( set() )
            hypted_funcs.append( (lambda _: True) )
            disj_hypts = (lambda bs: any(h(bs) for h in hypted_funcs))
            ce = eqi_oracle(disj_hypts)
            assert ce is not None # since adding new basis restarts whole hypothesis
            unaligned = [i for i,h in enumerate(hypted_funcs) if h(ce)]

        for i in unaligned:
            walked_ce = walk(ce, basis[i], mem_oracle)
            learnd_terms[i] = learnd_terms[i] | { xor(walked_ce,basis[i]) }
            hypted_funcs[i] = hyptize(learnd_terms[i], basis[i])

        disj_hypts = (lambda bs: any(h(bs) for h in hypted_funcs))
        ce = eqi_oracle(disj_hypts)
    return learnd_terms, hypted_funcs, disj_hypts, basis













###############################################################################

def tabulate(f, bits):
    for i in range(2**bits):
        bs = "{:0>{w}b}".format(i, w=bits)
        b = bs_to_asgmt(bs)
        print(bs, '1' if f(b) else '0')
def eqi(f1, f2, bits):
    for i in range(2**bits):
        bs = "{:0>{w}b}".format(i, w=bits)
        b = bs_to_asgmt(bs)
        if f1(b) != f2(b):
            #print('counter-example:',bs)
            return b
    return None

from random import choice
def gen_bs(size, bits):
    tmp = []
    while len(tmp) < size:
        bs = ''.join(choice(['0','1']) for _ in range(bits))
        if bs not in tmp:
            tmp.append(int(bs,2))
    return tmp
def all_bs(bits):
    tmp = []
    for i in range(2**bits):
        bs = "{:0>{w}b}".format(i, w=bits)
        tmp.append(bs)
    return tmp

from time import time
from datetime import timedelta

def basic_test():
    def target(s):
        return s not in {0b100,0b110,0b001}
    def mem_oracle(s):
        return target(s)
    def eqi_oracle(h):
        return eqi(h, target, 3)
    
    _,_,retf,_ = learn_dcnf(mem_oracle, eqi_oracle, 3)
    if eqi(retf,target,3) is not None:
        raise Exception()
#basic_test()

def random_test(s,b):
    size = s
    bits = b
    gened = gen_bs(size,bits)
    def target(s):
        return s in gened
    def mem_oracle(s):
        return target(s)
    def eqi_oracle(h):
        return eqi(h, target, bits)

    t = time()
    _,_,retf,_ = learn_dcnf(mem_oracle, eqi_oracle, bits)
    print(timedelta(seconds=time()-t))
    if eqi(retf,target,bits) is not None:
        raise Exception()
#random_test(100,10)

