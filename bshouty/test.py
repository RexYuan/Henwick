
from cdnf import *

def tabulate(f, bits):
    """Print function truth table."""
    for i in range(2**bits):
        bs = "{:0>{w}b}".format(i, w=bits)
        print(bs, '1' if f(bs) else '0')
def eqi(f1, f2, bits):
    for i in range(2**bits):
        bs = "{:0>{w}b}".format(i, w=bits)
        if f1(bs) != f2(bs):
            #print('counter-example:',bs)
            return bs
    return True

def basic_test():
    basis = ['000', '011', '101']
    # a xor c
    def target(s):
        return s in {'100','110','001'}
    def mem_oracle(s):
        return target(s)
    def eqi_oracle(h):
        return eqi(h, target, 3)
    # should learn terms [100,001], [001,100]
    _,_,ret1f = LambdaAlgo(mem_oracle, eqi_oracle, basis)
    if not eqi(ret1f,target,3):
        raise Exception("error: basic lambda")
    _,_,ret1f = LambdaAlgo(None, eqi_oracle, basis)
    if not eqi(ret1f,target,3):
        raise Exception("error: basic nomem lambda")
    _,_,ret2f,b2 = CDNFAlgo(mem_oracle, eqi_oracle)
    if not eqi(ret2f,target,3):
        raise Exception("error: basic cdnf")
    _,_,ret2f,b2 = CDNFAlgo(None, eqi_oracle)
    if not eqi(ret2f,target,3):
        raise Exception("error: basic nomem cdnf")
    print(">> basic test cleared")

# random tests
from random import choice
def gen_bs(size, bits):
    tmp = []
    while len(tmp) < size:
        bs = ''.join(choice(['0','1']) for _ in range(bits))
        if bs not in tmp:
            tmp.append(bs)
    return tmp
def all_bs(bits):
    tmp = []
    for i in range(2**bits):
        bs = "{:0>{w}b}".format(i, w=bits)
        tmp.append(bs)
    return tmp

def small_random_test():
    gened = gen_bs(10,5)
    def target(s):
        return s in gened
    def mem_oracle(s):
        return target(s)
    def eqi_oracle(h):
        return eqi(h, target, 3)
    _,_,retf,bas = CDNFAlgo(mem_oracle, eqi_oracle)
    if not eqi(retf,target,3):
        print(gened)
        raise Exception("error: small random cdnf")
    #_,_,retf,bas = CDNFAlgo(None, eqi_oracle)
    #if not eqi(retf,target,3):
    #    print(gened)
    #    raise Exception("error: small random nomem cdnf")
    #print(">> small random test cleared")
#small_random_test()

from time import time
def larger_random_sparse_test():
    gened = gen_bs(100,10)
    def target(s):
        return s in gened
    def mem_oracle(s):
        return target(s)
    def eqi_oracle(h):
        return eqi(h, target, 10)
    t1 = time()
    _,_,retf1,bas1 = CDNFAlgo(mem_oracle, eqi_oracle)
    t2 = time()
    if not eqi(retf1,target,10):
        print(gened)
        raise Exception("error: larger random sparse cdnf")
    print("larger random sparse cdnf time:",t2-t1)
    #t1 = time()
    #_,_,retf2,bas2 = CDNFAlgo(None, eqi_oracle)
    #t2 = time()
    #if not eqi(retf2,target,10):
    #    print(gened)
    #    raise Exception("error: larger random sparse nomem cdnf")
    #print("larger random sparse nomem cdnf time:",t2-t1)
    #print(">> larger random sparse test cleared")
larger_random_sparse_test()

def larger_random_dense_test():
    gened = gen_bs(900,10)
    def target(s):
        return s in gened
    def mem_oracle(s):
        return target(s)
    def eqi_oracle(h):
        return eqi(h, target, 10)
    t1 = time()
    _,_,retf1,bas1 = CDNFAlgo(mem_oracle, eqi_oracle)
    t2 = time()
    if not eqi(retf1,target,10):
        print(gened)
        raise Exception("error: larger random dense cdnf")
    print("larger random sparse cdnf time:",t2-t1)
    t1 = time()
    _,_,retf2,bas2 = CDNFAlgo(None, eqi_oracle)
    t2 = time()
    if not eqi(retf2,target,10):
        print(gened)
        raise Exception("error: larger random dense nomem cdnf")
    print("larger random dense nomem cdnf time:",t2-t1)
    print(">> larger random dense test cleared")

def huge_random_sparse_test():
    gened = gen_bs(100000,20)
    def target(s):
        return s in gened
    def mem_oracle(s):
        return target(s)
    def eqi_oracle(h):
        return eqi(h, target, 10)
    t1 = time()
    _,_,retf1,bas1 = CDNFAlgo(mem_oracle, eqi_oracle)
    t2 = time()
    if not eqi(retf1,target,10):
        print(gened)
        raise Exception("error: huge random sparse cdnf")
    print("huge random sparse cdnf time:",t2-t1)
    t1 = time()
    _,_,retf2,bas2 = CDNFAlgo(None, eqi_oracle)
    t2 = time()
    if not eqi(retf2,target,10):
        print(gened)
        raise Exception("error: huge random sparse nomem cdnf")
    print("huge random sparse nomem cdnf time:",t2-t1)
    print(">> huge random sparse test cleared")

def huge_random_dense_test():
    gened = gen_bs(900000,20)
    def target(s):
        return s in gened
    def mem_oracle(s):
        return target(s)
    def eqi_oracle(h):
        return eqi(h, target, 10)
    t1 = time()
    _,_,retf1,bas1 = CDNFAlgo(mem_oracle, eqi_oracle)
    t2 = time()
    if not eqi(retf1,target,10):
        print(gened)
        raise Exception("error: huge random dense cdnf")
    print("huge random dense cdnf time:",t2-t1)
    t1 = time()
    _,_,retf2,bas2 = CDNFAlgo(None, eqi_oracle)
    t2 = time()
    if not eqi(retf2,target,10):
        print(gened)
        raise Exception("error: huge random dense nomem cdnf")
    print("huge random dense nomem cdnf time:",t2-t1)
    print(">> huge random dense test cleared")

# standard function tests
def fn_test():
    word = 5
    def target(bs):
        # bs[:word] < bs[word:]
        return int(bs[:word],2) <= int(bs[word:],2)
    def mem_oracle(s):
        return target(s)
    def eqi_oracle(h):
        #return eqi(h, target, word*2)
        bits = word*2
        n = 2**bits
        for i,j in zip(range(n//2), range(n-1,n//2-1,-1)):
            bs = "{:0>{w}b}".format(i, w=bits)
            if target(bs) != h(bs):
                print('counter-example:',bs)
                return bs
            bs = "{:0>{w}b}".format(j, w=bits)
            if target(bs) != h(bs):
                print('counter-example:',bs)
                return bs
        return True

    terms,fs,retf,bas = CDNFAlgo(mem_oracle, eqi_oracle)
    print()
    print("equivalence:",eqi(retf,target,word*2))
    print()
    print("basis size:",len(bas))
    print("basis:",bas)
    print()
    print("terms:",terms)

from math import floor
def random_test_ratio_bits(true_ratio, bits):
    true_points = floor(2 ** bits * true_ratio)
    gened = gen_bs(true_points, bits)
    def target(s):
        return s in gened
    def mem_oracle(s):
        return target(s)
    def eqi_oracle(h):
        return eqi(h, target, 10)
    t1 = time()
    _,_,retf1,bas1 = CDNFAlgo(mem_oracle, eqi_oracle)
    t2 = time()
    if not eqi(retf1,target,10):
        print(gened)
        raise Exception("error: {} bits random {} ratio cdnf".format(bits, true_ratio))
    print("{} bits random {} cdnf time:".format(bits, true_ratio),t2-t1)
    t1 = time()
    _,_,retf2,bas2 = CDNFAlgo(None, eqi_oracle)
    t2 = time()
    if not eqi(retf2,target,10):
        print(gened)
        raise Exception("error: {} bits random {} ratio nomen cdnf".format(bits, true_ratio))
    print("{} bits random {} nomen cdnf time:".format(bits, true_ratio),t2-t1)
    print(">> {} bits random {} ratio test cleared".format(bits, true_ratio))

#basic_test()
#small_random_test()
#larger_random_sparse_test()
#larger_random_dense_test()
#huge_random_sparse_test()
#huge_random_dense_test()
#random_test_ratio_bits(0.01, 10)

def dc_small_random_test():
    siz = 8
    gened = gen_bs(100,siz)
    def target(s):
        return s in gened
    def mem_oracle(s):
        return target(s)
    def eqi_oracle(h):
        return eqi(h, target, siz)
    _,_,retf,bas = CDNFAlgo(mem_oracle, eqi_oracle)
    print(">> CDNF learned")
    _,_,dretf,bas = DCNFAlgo(mem_oracle, eqi_oracle)
    print(">> DCNF learned")
    if not eqi(retf,dretf,siz):
        print(gened)
        raise Exception("error: small random cdnf")

    print(">> small random test cleared")

#dc_small_random_test()