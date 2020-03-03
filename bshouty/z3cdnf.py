
from time import time
from datetime import timedelta

from copy import deepcopy
from z3 import *
from cdnf import *

import functools
print = functools.partial(print, flush=True)


basis_count = 0
pos_proced = 0
neg_proced = 0
posce = 0
negce = 0
repair_time = 0.0
initba_time = 0.0
determ_time = 0.0
growpo_time = 0.0
func_time = 0.0
form_time = 0.0
bads_bs_time = 0.0
bads_bs_count = 0
pos_oracle_count = 0
neg_oracle_count = 0
solver_time = 0.0
tbegin = 0.0

def time_profile(final=False):
    print('pos_proced', pos_proced)
    print('neg_proced', neg_proced)
    print('determined positive', posce)
    print('determined negative', negce)
    print()
    print('repair_time', timedelta(seconds=repair_time))
    print('initba_time', timedelta(seconds=initba_time))
    print('determ_time', timedelta(seconds=determ_time))
    print('growpo_time', timedelta(seconds=growpo_time))
    print()
    print('func_time', timedelta(seconds=func_time))
    print('form_time', timedelta(seconds=form_time))
    print('bads_bs_time', timedelta(seconds=bads_bs_time))
    print()
    print('bads_bs_count', bads_bs_count)
    print('pos_oracle_count', pos_oracle_count)
    print('neg_oracle_count', neg_oracle_count)
    print('solver_time', timedelta(seconds=solver_time))
    print('----------------------------------------')

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

def z3_model_to_bs(m, bits):
    '''
    set 1 for True vars and 0 for False or Don't Care vars
    '''
    return True if m is True else "".join([ '1' if m[Bool(str(i))] else '0' for i in range(bits) ])

def mterm(bs):
    return {i for i,b in enumerate(bs) if b == '1'}

def hyptize_funcs(learnd_terms_comp, basis_comp):
    '''
    argument: a list of bit strings and a basis bit string
    return: a list of term functions
    '''
    def make_term_f(t):
        '''
        function factory with closure to avoid late binding/lazy evaluation
        because python is dynamically scoped instead of lexicographically
        '''
        def term_f(bs):
            return mterm(bsxor(bs,basis_comp)) >= mterm(t)
        return term_f

    return list(map(make_term_f, learnd_terms_comp))

def update_funcs(hypted_funcs, ce, basis):
    def make_term_f(t):
        def term_f(bs):
            return mterm(bsxor(bs,basis)) >= mterm(t)
        return term_f

    hypted_funcs.append( make_term_f(ce) )
    return

def make_funcs(hypted_funcs):
    '''
    argument: a list of list of term functions
    return: a list of dnf functions
    '''
    def make_dnf_f(term_fs):
        if term_fs is False:
            return (lambda _ : False)
        def dnf_f(bs):
            return any(term_f(bs) for term_f in term_fs)
        return dnf_f
    
    return list(map(make_dnf_f, hypted_funcs))

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
    return terms

def update_forms(hypted_form, ce, basis):
    term = []
    for n,(i,j) in enumerate(zip(ce,basis)):
        if i == '1' and j == '0':
            term.append(Bool(str(n)))
        elif i == '0' and j == '1':
            term.append(Not(Bool(str(n))))
    hypted_form.append( And(term) )
    return

def make_form(hypted_forms):
    cdnf = []
    for dnf in hypted_forms:
        cdnf.append( Or(dnf) )
    return And(cdnf)

def z3_CDNFAlgo_phase1(eqi_oracle, bits):
    '''
    eqi_oracle is an exact, consistent oracle
    '''
    basis = []
    ce = z3_model_to_bs(eqi_oracle( BoolVal(True) ), bits)
    if ce == True:
        raise Exception("bads is empty")
    basis.append( ce )

    learnd_terms = [ [] ]
    learnd_terms_og = [ [] ]
    hypted_funcs = [ False ]
    hypted_forms = [ BoolVal(False) ]

    ce = z3_model_to_bs(eqi_oracle( make_form(hypted_forms) ), bits)

    while ce != True:
        unaligned = [i for i,h in enumerate( make_funcs(hypted_funcs) ) if not h(ce)]
        while unaligned == []:
            basis.append( ce )
            learnd_terms.append( [] )
            learnd_terms_og.append( [] )
            hypted_funcs.append( False )
            hypted_forms.append( BoolVal(False) )
            ce = z3_model_to_bs(eqi_oracle( make_form(hypted_forms) ), bits)
            unaligned = [i for i,h in enumerate( make_funcs(hypted_funcs) ) if not h(ce)]
        
        for i in unaligned:
            learnd_terms[i].append( bsxor(ce,basis[i]) )
            hypted_funcs[i] = hyptize_funcs(learnd_terms[i], basis[i])
            learnd_terms_og[i].append( ce )
            hypted_forms[i] = hyptize_forms(learnd_terms_og[i], basis[i])
        
        ce = z3_model_to_bs(eqi_oracle( make_form(hypted_forms) ), bits)
    
    return (basis,learnd_terms,learnd_terms_og,hypted_funcs,hypted_forms)

def init_new_basis(inits_oracle, bits, new_basis, learnd_terms, learnd_terms_og, hypted_funcs, hypted_forms):
    '''
    just put the inits in first when getting a new basis
    '''
    learnd_terms.append( [] )
    learnd_terms_og.append( [] )
    hypted_funcs.append( (lambda _: False) )
    hypted_forms.append( BoolVal(False) )
    ce = z3_model_to_bs(inits_oracle( make_form(hypted_forms) ), bits)
    # always positive ce
    while ce != True:
        learnd_terms[-1].append( bsxor(ce,new_basis) )
        hypted_funcs[-1] = hyptize_funcs(learnd_terms[-1], new_basis)
        learnd_terms_og[-1].append( ce )
        hypted_forms[-1] = hyptize_forms(learnd_terms_og[-1], new_basis)
        ce = z3_model_to_bs(inits_oracle( make_form(hypted_forms) ), bits)
    return

def determine_ce(bads_bs_oracle, bits, ce, neg_ces):
    '''
    for ce of transitional pair, determine which is the negative or positve ce to learn
    if successor is a bad or a previous negative ce, then predecessor is judged a negative ce
    else successor is judged a positive ce
    '''
    global posce,negce,bads_bs_time,bads_bs_count

    if ce is True:
        return True
    pred = ce[:bits]
    succ = ce[bits:]
    t1 = time()
    ret = bads_bs_oracle(succ)
    bads_bs_time += time() - t1
    bads_bs_count += 1
    if ret or succ in neg_ces:
        negce += 1
        return pred
    else:
        posce += 1
        return succ

def blind_walk(bs, basis, bads_bs_oracle, bits, neg_ces):
    '''
    walk blindly towards basis from bs according to bads_bs_oracle and neg_ces
    '''
    more = True
    while more:
        more = False
        for i,(bi,ai) in enumerate(zip(bs,basis)):
            if bi != ai and not bads_bs_oracle(flip(bs,i)) and flip(bs,i) not in neg_ces:
                bs = flip(bs,i)
                more = True
                break
    return bs

def update_absorption(bce, learnd_terms, hypted_func, learnd_terms_og, hypted_form):
    if len(hypted_form) != len(hypted_func):
        breakpoint()
    for i,t in enumerate(learnd_terms):
        # bce absorbs t
        if mterm(bce) <= mterm(t):
            del learnd_terms[i]
            del hypted_func[i]
            del learnd_terms_og[i]
            del hypted_form[i]
    if len(learnd_terms) != len(learnd_terms_og):
        breakpoint()
    return

def z3_CDNFAlgo_phase2(inits_oracle, trans_oracle, bads_bs_oracle, bits, starter):
    '''
    eqi_oracle is a constrained, inconsistent-but-eventually-consistent oracle
    assuming only false positive is possible, since false negative wont change anything eventually
    so its okay to assume all negative judgements are final
    '''
    global basis_count, pos_proced, neg_proced, posce, negce, repair_time, initba_time, determ_time, growpo_time, func_time, form_time, bads_bs_time, bads_bs_count, pos_oracle_count, neg_oracle_count, solver_time, tbegin
    
    basis,learnd_terms,learnd_terms_og,hypted_funcs,hypted_forms = starter

    tbegin = time()
    
    # transitional ce not possible yet, must be negative since starting from not bad
    ce = z3_model_to_bs(trans_oracle( make_form(hypted_forms) ), bits)

    while ce != True:
        if pos_proced % 10 == 0:
            time_profile()
        unaligned = [i for i,h in enumerate( make_funcs(hypted_funcs) ) if not h(ce)]
        # negative ce
        while unaligned == []:
            neg_proced += 1

            # initialize new basis with inits
            tstart = time()
            basis.append( ce )
            init_new_basis(inits_oracle, bits, ce, learnd_terms, learnd_terms_og, hypted_funcs, hypted_forms)
            initba_time += time() - tstart
            
            # determine transitional ce
            tstart = time()
            ce = z3_model_to_bs(trans_oracle( make_form(hypted_forms) ), bits*2)
            solver_time += time() - tstart
            neg_oracle_count += 1
            tstart = time()
            ce = determine_ce(bads_bs_oracle, bits, ce, basis)
            determ_time += time() - tstart
            if ce == True:
                return make_form(hypted_forms)
            unaligned = [i for i,h in enumerate( make_funcs(hypted_funcs) ) if not h(ce)]
        
        # positive ce, same as before
        pos_proced += 1
        tstart = time()
        for i in unaligned:
            #ce = blind_walk(ce, basis[i], bads_bs_oracle, bits, basis)

            update_absorption(bsxor(ce,basis[i]), learnd_terms[i], hypted_funcs[i], learnd_terms_og[i], hypted_forms[i])
            
            tsstart = time()

            learnd_terms[i].append( bsxor(ce,basis[i]) )
            update_funcs(hypted_funcs[i], bsxor(ce,basis[i]), basis[i])
            
            func_time += time() - tsstart
            tsstart = time()
            
            learnd_terms_og[i].append( ce )
            update_forms(hypted_forms[i], ce, basis[i])
            
            form_time += time() - tsstart

        growpo_time += time() - tstart

        tstart = time()
        ce = z3_model_to_bs(trans_oracle( make_form(hypted_forms) ), bits*2)
        solver_time += time() - tstart
        pos_oracle_count += 1
        tstart = time()
        ce = determine_ce(bads_bs_oracle, bits, ce, basis)
        determ_time += time() - tstart
        
    algo_time = time() - tbegin
    cdnf_time = repair_time+initba_time+determ_time+growpo_time
    basis_count = len(basis)
    
    
    time_profile()
    
    print('residual time', timedelta(seconds=algo_time-solver_time-cdnf_time))
    print('cdnf_time', timedelta(seconds=cdnf_time))
    print('solver_time', timedelta(seconds=solver_time))

    print('basis_count', basis_count)
    print(list(map(len,learnd_terms)))

    return make_form(hypted_forms)

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
    
    # bootstrap by not_bads
    def not_bad_oracle(h):
        s.reset()
        s.add( Not(And( Implies(Not(bads),h) , Implies(h,Not(bads)) )) )
        if s.check() != unsat:
            return s.model()
        return True
    not_bads_starter = z3_CDNFAlgo_phase1(not_bad_oracle, bits)
    
    # need this for determination
    basis,learnd_terms,_,_,_ = not_bads_starter
    nb_basis = [b for b in basis]
    nb_learnd_terms = [[t for t in terms] for terms in learnd_terms]
    nb_hypted_funcs = [hyptize_funcs(ts, b) for (ts, b) in zip(nb_learnd_terms, nb_basis)]
    def bads_bs_oracle(bs):
        return any(not dnf(bs) for dnf in make_funcs(nb_hypted_funcs))
    
    def bads_bs_oracl2e(bs):
        s.reset()
        s.add( And([v if b == '1' else Not(v) for b,v in zip(bs,z3_bool_range(len(bs)))]) )
        s.add( bads )
        if s.check() == sat:
            return True
        return False
    
    # l
    def inits_oracle(h):
        s.reset()
        s.add( Not(Implies(inits , h)) )
        if s.check() != unsat:
            return s.model()
        return True
    def trans_oracle(h):
        hp = substitute(h, *zip(z3_bool_range(bits),z3_bool_range(bits,bits*2)))
        s.reset()
        s.add( Not(Implies(And(h,trans) , hp)) )
        if s.check() != unsat:
            return s.model()
        return True

    return z3_CDNFAlgo_phase2(inits_oracle, trans_oracle, bads_bs_oracle, bits, not_bads_starter)

def v_in_f(bs,form):
    s = Solver()
    s.add(form)
    s.add(And([v if b == '1' else Not(v) for b,v in zip(bs,z3_bool_range(len(bs)))]))
    return s.check()