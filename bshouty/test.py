
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
            print('counter-example:',bs)
            return bs
    return True

# test
'''
basis = ['010', '101']
# a xor c
def target(s):
    return s in {'100','110','001','011'}
def mem_oracle(s):
    return target(s)
def eqi_oracle(h):
    return eqi(h, target, 3)
# should learn terms [100,001], [001,100]
_,_,ret1f = LambdaAlgo(mem_oracle, eqi_oracle, basis)
print(eqi(ret1f,target,3))

#_,_,ret2f,b2 = CDNFAlgo(mem_oracle, eqi_oracle)
print(eqi(ret2f,target,3))
print(b2)
'''

# random tests
'''
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

gened = gen_bs(4,3)
print("testing:", gened)
def target(s):
    return s in gened
def mem_oracle(s):
    return target(s)
def eqi_oracle(h):
    return eqi(h, target, 3)
_,_,retf,bas = CDNFAlgo(mem_oracle, eqi_oracle)
print("equivalence:",eqi(retf,target,3))
print(bas)
print()

gened = gen_bs(10,10)
print("testing:", gened)
def target(s):
    return s in gened
def mem_oracle(s):
    return target(s)
def eqi_oracle(h):
    return eqi(h, target, 10)
_,_,retf,bas = CDNFAlgo(mem_oracle, eqi_oracle)
print("equivalence:",eqi(retf,target,10))
print(bas)
print()
'''

# standard function tests
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
