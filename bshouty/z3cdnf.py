
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
    elif len(argv) == 3:
        start = argv[0]
        bits = argv[1]
        step = argv[2]
        for i in range(start,bits,step):
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
            raise Exception("bads is empty")
        basis.append( ce )

        learnd_terms = [ [] ]
        learnd_terms_og = [ [] ]
        hypted_funcs = [ (lambda _: False) ]
        hypted_forms = [ BoolVal(False) ]

    ce = z3_model_to_bs(eqi_oracle( And(hypted_forms) ), bits)

    while ce != True:
        unaligned = [i for i,h in enumerate(hypted_funcs) if not h(ce)]
        while unaligned == []:
            # check if this negative ce was already registered as positive
            if starter:
                for i in range(len(learnd_terms)):
                    if ce in learnd_terms_og[i]:
                        # get rid of it
                        learnd_terms_og[i].remove( ce )
                        learnd_terms[i].remove( bsxor(ce,basis[i]) )
                        # add back all its successors
                        for j in range(bits):
                            if ce[j] == '0' and flip(ce,j) not in learnd_terms_og[i]:
                                learnd_terms_og[i].append( flip(ce,j) )
                            if bsxor(ce,basis[i])[j] == '0' and flip(bsxor(ce,basis[i]),j) not in learnd_terms[i]:
                                learnd_terms[i].append( flip(bsxor(ce,basis[i]),j) )
                        # refresh funcs and forms
                        hypted_forms[i] = hyptize_forms(learnd_terms_og[i], basis[i])
                        hypted_funcs[i] = hyptize_funcs(learnd_terms[i], basis[i])
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
        
        breakpoint()
        ce = z3_model_to_bs(eqi_oracle( And(hypted_forms) ), bits)
        
    return And(hypted_forms) if not details else (basis,learnd_terms,learnd_terms_og,hypted_funcs,hypted_forms)

def get_invariant(bits, inits, bads, trans):
    '''
    Args:
        bits: int
        inits, bads: z3 exprs with vars from (0) to (bits-1)
        trans: z3 expr with vars from (0) to (2bits-1) where vars from (bits) to (2bits-1) are the next states
    
    Constraints:
        c1) inits => inv
        c2) inv => ~bads
        c3) inv & trans => inv'

    Note:
        inv may be hypothesized as False which would pass (c3) but wont pass (c1),
        but in the second phase of learning,
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
    breakpoint()
    
    # learn invariant by always extracting the predecessor of the transition counter-example
    def trans_oracle(h):
        s.reset()
        s.add( Not(Implies(inits , h)) )
        if s.check() != unsat:
            return s.model()
        
        hp = substitute(h, *zip(z3_bool_range(bits),z3_bool_range(bits,bits*2)))
        s.reset()
        s.add( Not(Implies(And(h,trans) , hp)) )
        if s.check() != unsat:
            return s.model()
        return True

    breakpoint()
    return z3_CDNFAlgo(trans_oracle, bits, starter=not_bads_starter)

def v_in_f(bs,form):
    s = Solver()
    s.add(form)
    s.add(And([v if b == '1' else Not(v) for b,v in zip(bs,z3_bool_range(len(bs)))]))
    return s.check()