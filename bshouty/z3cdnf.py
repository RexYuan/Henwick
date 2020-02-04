
from z3 import *
from cdnf import *

# shortcuts
def B(s):
    return Bool(str(s))
def NB(s):
    return Not(Bool(str(s)))

def z3_bool_range(*argv):
    '''
    Example:
        >>> list(z3_bool_range(2))
        [0, 1]
        >>> list(z3_bool_range(1,2))
        [1]
    '''
    if len(argv) == 1:
        bits = argv[0]
        for i in range(bits):
            yield Bool(str(i))
    elif len(argv) == 2:
        start = argv[0]
        bits = argv[1]
        for i in range(start,bits):
            yield Bool(str(i))

def bs_to_z3_term(bs, bits):
    if bs is True:
        return True
    return And([ x for b,x in zip(bs,z3_bool_range(bits)) if b == '1' ])

def z3_model_to_bs(m, bits):
    '''
    set 1 for True vars and 0 for False or Don't Care vars
    '''
    return True if m is True else "".join([ '1' if m[Bool(str(i))] else '0' for i in range(bits) ])

def hyptize_funcs(learnd_terms_comp, basis_comp):
    def mterm(bs):
        return [i for i,b in enumerate(bs) if b == '1']

    def mdnf(bss):
        return map(mterm, bss)

    def h(bs):
        bs = bsxor(bs,basis_comp)
        bst = mterm(bs)
        return any(all(i in bst for i in t) for t in mdnf(learnd_terms_comp))
    return h

def hyptize_forms(learnd_terms_comp, basis_comp):
    '''
    expanded H and use the result DNF directly
    '''
    terms = []
    for l in learnd_terms_comp:
        term = []
        for n,(i,j) in enumerate(zip(l,basis_comp)):
            if i == '1' and j == '0':
                term.append(Bool(str(n)))
            elif i == '0' and j == '1':
                term.append(Not(Bool(str(n))))
        terms.append( And(term) )
    return Or(terms)

def z3_CDNFAlgo(eqi_oracle, bits, starter=False, details=False):
    if starter:
        basis,learnd_terms,learnd_terms_og,hypted_funcs,hypted_forms = starter
    else:
        basis = []
        ce = z3_model_to_bs(eqi_oracle( BoolVal(True) ), bits)
        if ce == True:
            return True
        basis.append( ce )

        learnd_terms = [ [] ]
        learnd_terms_og = [ [] ]
        hypted_funcs = [ (lambda _: False) ]
        hypted_forms = [ BoolVal(False) ]

    ce = z3_model_to_bs(eqi_oracle( And(hypted_forms) ), bits)

    while ce != True:
        unaligned = [i for i,h in enumerate(hypted_funcs) if not h(ce)]
        while unaligned == []:
            basis.append( ce )
            learnd_terms.append( [] )
            learnd_terms_og.append( [] )
            hypted_funcs.append( (lambda _: False) )
            hypted_forms.append( BoolVal(False) )
            ce = z3_model_to_bs(eqi_oracle( And(hypted_forms) ), bits)
            unaligned = [i for i,h in enumerate(hypted_funcs) if not h(ce)]
        
        for i in unaligned:
            learnd_terms[i].append( bsxor(ce,basis[i]) )
            hypted_funcs[i] = hyptize_funcs(learnd_terms[i], basis[i])
            learnd_terms_og[i].append( ce )
            hypted_forms[i] = hyptize_forms(learnd_terms_og[i], basis[i])

        ce = z3_model_to_bs(eqi_oracle( And(hypted_forms) ), bits)
        
    return And(hypted_forms) if not details else (basis,learnd_terms,learnd_terms_og,hypted_funcs,hypted_forms)

def get_invariant(bits, inits, bads, trans):
    '''
    Args:
        bits: int
        inits, bads: z3 exprs with vars from (0) to (bits-1)
        trans: z3 expr with vars from (0) to (2bits-1) where vars from (bits) to (2bits-1) are the next states
    
    Constraints:
        inits => inv
        inv => ~bads
        inv & trans => inv'
    '''
    s = Solver()
    
    # check if inits and bads overlap
    s.add( And(inits,bads) )
    if s.check() == sat:
        # no invariant exists
        return False
    
    # learn not-bads starters
    def not_bad_oracle(h):
        s.reset()
        s.add( Not(And( Implies(Not(bads),h) , Implies(h,Not(bads)) )) )
        if s.check() != unsat:
            return s.model()
        return True
    not_bads_starter = z3_CDNFAlgo(not_bad_oracle, bits, details=True)
    
    # learn invariant by always extracting the predecessor of the transition counter-example
    def trans_oracle(h):
        print(h)
        hp = substitute(h, *zip(z3_bool_range(bits),z3_bool_range(bits,bits*2)))
        s.reset()
        s.add( Not(Implies(And(h,trans) , hp)) )
        if s.check() != unsat:
            return s.model()
        return True
    breakpoint()
    return z3_CDNFAlgo(trans_oracle, bits, starter=not_bads_starter)

#get_invariant(2, Bool('0'), Not(Bool('0')), And(Bool('0'),Bool('2')))
get_invariant(3, And(B(0),B(1)),
                 And(NB(0),NB(1)),
                 Or(And(B(0),B(3)),
                    And(NB(0),NB(3))))
                 
'''
000\
001/ bads
010
011
trans
---
trans
100
101
110\
111/ inits
'''
pass