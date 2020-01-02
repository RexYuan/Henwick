
def tabulate(f, bits):
    """Print function truth table."""
    for i in range(2**bits):
        bs = "{:0>{w}b}".format(i, w=bits)
        print(bs, '1' if f(bs) else '0')
def eqi(f1, f2, bits):
    for i in range(2**bits):
        bs = "{:0>{w}b}".format(i, w=bits)
        if f1(bs) != f2(bs):
            print('counter-example:',bs)
            return bs
    return True

from cdnf import *

def hyptize(learnd_terms_comp, basis_comp):
    """Construct hypothesized minimal monotone function per learned terms.

    Args:
        learnd_terms_comp (bit string list): Learned terms component.
        basis_comp (bit string): Corresponding basis component.

    Returns:
        (bit string -> bool): Hypothesized function against basis components function.

    Reference:
        learnd_terms_comp: Si
        basis_comp: ai
        return: Hi
        mterm: M_DNF(assignment)
        mdnf: M_DNF(assignment list)
    """
    def mterm(bs):
        """Construct the minimal monotone function per assignment `bs`.

        Represented as a list of indices of positive literals.

        Example:
            >>> mterm('10110')
            [0, 2, 3]
        """
        return [i for i,b in enumerate(bs) if b == '1']

    def mdnf(bss):
        """Construct the DNF of minimal monotone functions per assignments `bss`.

        Example:
            >>> list(mdnf(['10110','01001']))
            [[0, 2, 3], [1, 4]]
        """
        return map(mterm, bss)

    def h(bs):
        # keeping with the outer-most (x+a)
        bs = bsxor(bs,basis_comp)
        # since mterms are monotone, it suffices to check if all the positive
        # bits in t are also positive in `bs` for some mterm t in the mdnf
        bst = mterm(bs)
        return any(all(i in bst for i in t) for t in mdnf(learnd_terms_comp))
    return h

def LambdaAlgoP(eqi_oracle, basis):
    # learned Si terms against target Ti terms
    learnd_terms = [[] for _ in basis]
    # learned hypothesized functions Hi against target basis component functions Mai
    hypted_funcs = [(lambda _: False) for _ in basis]
    # conjunction of all of the hypothesized functions
    conj_hypts = (lambda bs: all(h(bs) for h in hypted_funcs))
    # get positive counter-example
    ce = eqi_oracle(conj_hypts)
    while ce != True:
        #breakpoint()
        # find the hypothesized functions not accommodating target basis components
        unaligned = [i for i,h in enumerate(hypted_funcs) if not h(ce)]
        for i in unaligned:
            # heart of the algorithm, see paper for explanation
            learnd_terms[i].append( bsxor(ce,basis[i]) )
            hypted_funcs[i] = hyptize(learnd_terms[i], basis[i])
        conj_hypts = (lambda bs: all(h(bs) for h in hypted_funcs))
        ce = eqi_oracle(conj_hypts)
    return learnd_terms, hypted_funcs, conj_hypts

def CDNFAlgoP(eqi_oracle):
    basis = []
    ce = eqi_oracle((lambda _: True))
    if ce == True:
        return True
    basis.append(ce)

    learnd_terms = [[]]
    hypted_funcs = [(lambda _: False)]
    conj_hypts = (lambda bs: all(h(bs) for h in hypted_funcs))
    ce = eqi_oracle(conj_hypts)

    while ce != True:
        unaligned = [i for i,h in enumerate(hypted_funcs) if not h(ce)]
        while unaligned == []:
            basis.append(ce)
            print("basis size", len(basis))
            learnd_terms.append( [] )
            hypted_funcs.append( (lambda _: False) )
            conj_hypts = (lambda bs: all(h(bs) for h in hypted_funcs))
            ce = eqi_oracle(conj_hypts)
            unaligned = [i for i,h in enumerate(hypted_funcs) if not h(ce)]

        for i in unaligned:
            learnd_terms[i].append( bsxor(ce,basis[i]) )
            hypted_funcs[i] = hyptize(learnd_terms[i], basis[i])

        conj_hypts = (lambda bs: all(h(bs) for h in hypted_funcs))
        ce = eqi_oracle(conj_hypts)
    return learnd_terms, hypted_funcs, conj_hypts, basis

basis = ['000', '011', '101']
# a xor c
def target(s):
    return s in {'100','110','001'}
def eqi_oracle(h):
    return eqi(h, target, 3)

# should learn terms [100,001], [001,100]
ts,fs,ret1f = LambdaAlgoP(eqi_oracle, basis)
print(eqi(ret1f,target,3))

ts,fs,ret2f,b2 = CDNFAlgoP(eqi_oracle)
print(eqi(ret2f,target,3))
print(b2)

# TODO: convert functions to SMT formulas