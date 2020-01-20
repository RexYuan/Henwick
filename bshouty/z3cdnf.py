
from z3 import *
from cdnf import *

def z3_bool_range(bits):
    for i in range(bits):
        yield Bool(str(i))

def bs_to_z3_term(bs, bits):
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

def z3_CDNFAlgo(eqi_oracle, bits):
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
    return And(hypted_forms)