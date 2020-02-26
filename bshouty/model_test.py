
from z3cdnf import *
from time import time
from datetime import timedelta

def B(i):
    return Bool(str(i))
def NB(i):
    return Not(Bool(str(i)))

def test_inv(inv, bits, inits, bads, trans):
    '''
    Constraints:
        c1) inits => inv
        c2) inv => ~bads
        c3) inv & trans => inv'
    '''
    s = Solver()
    s.add( Not(Implies(inits , inv)) )
    if s.check() == sat:
        return False
    
    s.reset()
    s.add( Not(Implies(inv , Not(bads))) )
    if s.check() == sat:
        return False
    
    invp = substitute(inv, *zip(z3_bool_range(bits),z3_bool_range(bits,bits*2)))
    s.reset()
    s.add( Not(Implies(And(inv,trans) , invp)) )
    if s.check() == sat:
        return False
    return True

def bs_add_one(bits):
    '''
    formulae of bits added one of length bits
    big-endian: first bit is the most significant bit
    count starts from 0 to bits-1
    '''
    new_bs = []
    # lowest bit added one is just flipped
    new_bs.insert(0,Not(Bool(str(bits-1))))
    # lowest bit carries if it's 1
    cin = Bool(str(bits-1))
    for bit in z3_bool_range(bits-2,-1,-1):
        # A+0 = A xor 0 xor cin = A xor cin
        new_bs.insert(0,Xor(bit,cin))
        # carry in is just last bit
        cin = And(bit,cin)
    return new_bs

def make_counter_trans(bits,mod=False,jumps=False):
    '''
    big-endian up-counter transition formulae with substituted variables in order
    count from 0 to 2^bits

    if mod is provided, clears back to zeros on the next state of mod
    mod should be a formula

    if jumps is provided, the first state goes to the second of each pair on next state
    jumps should be a list of pairs of formulae
    '''
    constraints = []
    for nbit,bcons in zip(z3_bool_range(bits,bits*2) , bs_add_one(bits)):
        constraints.append( nbit == bcons )
    if mod is not False:
        zeros = And([Not(bit) for bit in z3_bool_range(bits,bits*2)])
        return And(Implies( mod , zeros ),
                   Implies( Not(mod) , And(constraints) ))
    if jumps is not False:
        return And([
            And(Implies( pred , succ ),
                Implies( Not(pred) , And(constraints) ))
        for pred,succ in jumps])
    return And(constraints)

def v_in_f(bs,form):
    s = Solver()
    s.add(form)
    s.add(And([v if b == '1' else Not(v) for b,v in zip(bs,z3_bool_range(len(bs)))]))
    return s.check()

def tab_f(form,bits):
    for i in range(2**bits):
        bs = "{:0>{w}b}".format(i, w=bits)
        print(bs, '1' if v_in_f(bs,form) == sat else '0')

def tab_c(form,bits):
    bits = bits*2
    for i in range(2**bits):
        bs = "{:0>{w}b}".format(i, w=bits)
        if v_in_f(bs,form) == sat:
            print(bs)

def bs_to_z3_term(bs):
    '''
    >>> bs_to_z3_term('1011')
    And(0, Not(1), 2, 3)

    >>> bs_to_z3_term('10*1')
    And(0, Not(1), 3)

    >>> bs_to_z3_term('10 asdf *1')
    And(0, Not(1), 3)
    '''
    if bs is True:
        return True
    bools = z3_bool_range(len(bs))
    bs = filter(lambda b: b in '10*', bs)
    return And([ x if b == '1' else Not(x) for b,x in zip(bs,bools) if b != '*' ])

###################################################

def test1():
    '''
    00 - bads
    01 -
    ---
    trans: totally connected component
    10 -
    11 - inits
    '''
    bits = 2
    inits = Bool('0')
    bads = Not(Bool('0'))
    trans = And(Bool('0'),Bool('2'))
    inv = get_invariant(bits, inits, bads, trans)
    assert test_inv(inv, bits, inits, bads, trans)

def test2():
    '''
    000-
    001- bads
    010
    011
    trans: totally connected component
    ---
    trans: totally connected component
    100
    101
    110-
    111- inits
    '''
    bits = 3
    inits = And(B(0),B(1))
    bads = And(NB(0),NB(1))
    trans = Or(And(B(0),B(3)),And(NB(0),NB(3)))
    inv = get_invariant(bits, inits, bads, trans)
    assert test_inv(inv, bits, inits, bads, trans)

def test3():
    '''
    trans: count up
    00- inits
    01
    trans: cycle back to 00
    ---
    trans: count up
    10
    11- bads
    trans: cycle back to 00
    ---
    '''
    B0,B1 = Bools('0 1')
    NB0,NB1 = Not(B0),Not(B1)
    bits = 2
    inits = And(NB0,NB1)
    bads = And(B0,B1)
    mod = And(NB0,B1)
    trans = make_counter_trans(bits,mod=mod)
    inv = get_invariant(bits, inits, bads, trans)
    print(inv)
    assert test_inv(inv, bits, inits, bads, trans)

def test4():
    '''
    trans: count up
    000
    001- inits
    010
    011- inits
    100
    trans: cycle back to 000
    ---
    trans: count up
    101
    110- bads
    111
    trans: cycle back to 000
    ---
    '''
    B0,B1,B2 = Bools('0 1 2')
    NB0,NB1,NB2 = Not(B0),Not(B1),Not(B2)
    bits = 3
    inits = Or(And(NB0,NB1,B2) , And(NB0,B1,B2))
    bads = And(B0,B1,NB2)
    mod = And(B0,NB1,NB2)
    trans = make_counter_trans(bits,mod=mod)
    inv = get_invariant(bits, inits, bads, trans)
    assert test_inv(inv, bits, inits, bads, trans)

def test5():
    '''
    trans: count up
    0000- inits
    0001
    0010
    0011
    trans: cycle back to 0000
    ----
    trans: count up
    0100
    0101
    0110
    0111
    trans: cycle back to 0000
    ---
    trans: count up
    1000
    1001
    1010
    1011
    1100-
    1101- bads
    1110-
    1111-
    trans: cycle back to 1010
    '''
    B0,B1,B2,B3 = Bools('0 1 2 3')
    NB0,NB1,NB2,NB3 = Not(B0),Not(B1),Not(B2),Not(B3)
    bits = 4
    inits = And(NB0,NB1,NB2,NB3)
    bads = And(B0,B1)
    jumps = [(And(NB0,B1,B2,B3),And(NB0,NB1,NB2,NB3)),
             (And(NB0,NB1,B2,B3),And(NB0,NB1,NB2,NB3)),
             (And(B0,B1,B2,B3),And(B0,NB1,B2,NB3))]
    trans = make_counter_trans(4,jumps=jumps)
    inv = get_invariant(bits, inits, bads, trans)
    assert test_inv(inv, bits, inits, bads, trans)

def test6():
    '''
    trans: count up and cycle
    0000 0000- inits
    0001 0000- inits
    0101 00**- cycle back to 0000 0000
    1000 ****- bads
    11** ****- bads
    '''
    B0,B1,B2,B3,B4,B5,B6,B7 = Bools('0 1 2 3 4 5 6 7')
    NB0,NB1,NB2,NB3,NB4,NB5,NB6,NB7 = Not(B0),Not(B1),Not(B2),Not(B3),Not(B4),Not(B5),Not(B6),Not(B7)
    bits = 8
    inits = Or(And(NB0,NB1,NB2,NB3,NB4,NB5,NB6,NB7),
               And(NB0,NB1,NB2,B3,NB4,NB5,NB6,NB7))
    bads = Or(And(B0,NB1,NB2,NB3),And(B0,B1))
    mod = And(NB0,B1,NB2,B3,NB4,NB5)
    trans = make_counter_trans(8,mod=mod)
    inv = get_invariant(bits, inits, bads, trans)
    assert test_inv(inv, bits, inits, bads, trans)

def test7():
    '''
    trans: count up and cycle
    0000 0000 0000 0000- inits
    0001 0000 0000 0000- cycle back to 0000 0000 0000 1000
    0111 **** 0000 ****- cycle back to 0000 0000 1111 0000
    11** **** 0000 ****- bads
    '''
    bits = 16
    inits = bs_to_z3_term('0000 0000 0000 0000')
    bads = bs_to_z3_term('11** **** 0000 ****')
    jumps = [(bs_to_z3_term('0001 0000 0000 0000'),bs_to_z3_term('0000 0000 0000 1000')),
             (bs_to_z3_term('0111 **** 0000 ****'),bs_to_z3_term('0000 0000 1111 0000'))]
    trans = make_counter_trans(bits,jumps=jumps)
    inv = get_invariant(bits, inits, bads, trans)
    assert test_inv(inv, bits, inits, bads, trans)

def test8():
    '''
    trans: count up and cycle
    0000 0000 0000- inits
    0001 0000 0000- inits
    0101 00** ****- cycle back to 0000 0000
    1000 **** ****- bads
    1100 **** ****- bads
    1111 **** 0000- inits
    '''
    bits = 14
    inits = Or(bs_to_z3_term('0000 0000 0000 *1'),
               bs_to_z3_term('0001 0000 **** *0'),
               bs_to_z3_term('1111 **** 1111 00'))
    bads = Or(bs_to_z3_term('1000 **** **** 10'),
              bs_to_z3_term('1100 **** **** 01'))
    mod = bs_to_z3_term('0101 00** **** 1*')
    trans = make_counter_trans(bits,mod=mod)
    inv = get_invariant(bits, inits, bads, trans)
    assert test_inv(inv, bits, inits, bads, trans)

t1 = time()
test8()
t2 = time()
print((timedelta(seconds=t2-t1)))