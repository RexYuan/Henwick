
def bxor(a,b):
    """XOR on bit characters."""
    return {('0','0'): '0',
            ('0','1'): '1',
            ('1','0'): '1',
            ('1','1'): '0'}[a,b]

def bsxor(x,y):
    """Bit-wise XOR on bit strings."""
    return ''.join( bxor(xi,yi) for xi,yi in zip(x,y) )

def flip(bs, i):
    return bs[:i]+('0' if bs[i] == '1' else '1')+bs[i+1:]

def walk(v, a, f):
    """Walk from v toward a while keeping f(v).

    Climb to a minimal element from v in the order of a in the reach of f.

    Example:
        >>> walk('11','00',(lambda bs: bs[1] == '1'))
        '01'
    """
    more = True
    while more:
        more = False
        for i,(vi,ai) in enumerate(zip(v,a)):
            if vi != ai and f( flip(v,i) ):
                v = flip(v,i)
                more = True
                break
    return v

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

def LambdaAlgo(mem_oracle, eqi_oracle, basis):
    """Learns a boolean function with given M-basis.

    Implementation of the Lambda algorithm.

    Args:
        mem_oracle (bit string -> bool): Membership oracle.
        eqi_oracle ((bit string -> bool) -> (bit string => bool) -> (bool | bit string)):
            Equivalence oracle. Returns True or a bit string of counter-example.
        basis (bit string list): Given t-dimensional M-basis.

    Returns:
        bit string list: Learned terms of `learnd_terms`.
        (bit string -> bool) list: Learned functions of `hypted_funcs`.
        (bit string -> bool): Learned target function.

    Reference:
        learnd_terms[i]: Si
        hypted_funcs[i]: Hi
        basis[i]: ai
        unaligned: I
        ce: v
        walked_ce: vi
    """
    # learned Si terms against target Ti terms
    learnd_terms = [[] for _ in basis]
    # learned hypothesized functions Hi against target basis component functions Mai
    hypted_funcs = [(lambda _: False) for _ in basis]
    # conjunction of all of the hypothesized functions
    conj_hypts = (lambda bs: all(h(bs) for h in hypted_funcs))
    # get positive counter-example
    ce = eqi_oracle(conj_hypts)
    while ce != True:
        # find the hypothesized functions not accommodating target basis components
        unaligned = [i for i,h in enumerate(hypted_funcs) if not h(ce)]
        for i in unaligned:
            # heart of the algorithm, see paper for explanation
            walked_ce = walk(ce, basis[i], mem_oracle) if mem_oracle else ce
            learnd_terms[i].append( bsxor(walked_ce,basis[i]) )
            hypted_funcs[i] = hyptize(learnd_terms[i], basis[i])
        conj_hypts = (lambda bs: all(h(bs) for h in hypted_funcs))
        ce = eqi_oracle(conj_hypts)
    return learnd_terms, hypted_funcs, conj_hypts

def CDNFAlgo(mem_oracle, eqi_oracle):
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
            learnd_terms.append( [] )
            hypted_funcs.append( (lambda _: False) )
            conj_hypts = (lambda bs: all(h(bs) for h in hypted_funcs))
            ce = eqi_oracle(conj_hypts)
            unaligned = [i for i,h in enumerate(hypted_funcs) if not h(ce)]

        for i in unaligned:
            walked_ce = walk(ce, basis[i], mem_oracle) if mem_oracle else ce
            learnd_terms[i].append( bsxor(walked_ce,basis[i]) )
            hypted_funcs[i] = hyptize(learnd_terms[i], basis[i])

        conj_hypts = (lambda bs: all(h(bs) for h in hypted_funcs))
        ce = eqi_oracle(conj_hypts)
    return learnd_terms, hypted_funcs, conj_hypts, basis

def eqi(f1, f2, bits):
    for i in range(2**bits):
        bs = "{:0>{w}b}".format(i, w=bits)
        if f1(bs) != f2(bs):
            print('counter-example:',bs,f1(bs),f2(bs))
            return bs
    return True
def tabulate(f, bits):
    """Print function truth table."""
    for i in range(2**bits):
        bs = "{:0>{w}b}".format(i, w=bits)
        print(bs, '1' if f(bs) else '0')

basis = ['01', '10']
# a xor c
false_test = True
def false_pos_target(s):
    return s in {'00','10','01'}
def target(s):
    return s in {'10','01'}
def mem_oracle(s):
    if false_test:
        return false_pos_target(s)
    return target(s)
def eqi_oracle(h):
    global false_test
    if false_test:
        if eqi(h, false_pos_target, 2) == True:
            false_test = False
        else:
            return eqi(h, false_pos_target, 2)
    return eqi(h, target, 2)
lt,hf,ret2f,b2 = CDNFAlgo(mem_oracle, eqi_oracle)
assert eqi(target, ret2f, 2)

false_test = True
def false_neg_target(s):
    return s in {'01'}
def target(s):
    return s in {'10','01'}
def mem_oracle(s):
    if false_test:
        return false_neg_target(s)
    return target(s)
def eqi_oracle(h):
    global false_test
    if false_test:
        if eqi(h, false_neg_target, 2) == True:
            false_test = False
        else:
            return eqi(h, false_neg_target, 2)
    return eqi(h, target, 2)
lt,hf,ret2f,b2 = CDNFAlgo(mem_oracle, eqi_oracle)
assert eqi(target, ret2f, 2)