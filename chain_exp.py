from poset_cover import poset_cover, is_swap
from time import time
from itertools import permutations
from random import sample, choice

s = list('abcdexyz')
ps = list(map(lambda l:''.join(l), list(permutations(s))))
# 40 hard thingly
#t = {'abecd', 'dcaeb', 'cedba', 'cabde', 'caebd', 'baced', 'dacbe', 'cebad', 'cdabe', 'badce', 'acebd', 'bcaed', 'acbde', 'acbed', 'aecbd', 'aecdb', 'daecb', 'acdeb', 'cdaeb', 'decab', 'ecdab', 'adceb', 'abced', 'ceadb', 'daceb', 'adecb', 'deabc', 'dbace', 'ecbad', 'caedb', 'acdbe', 'abcde', 'ceabd', 'acedb', 'eacdb', 'bacde', 'cedab', 'edcab', 'deacb', 'bdace'}
#lins = sample(ps, 110)

lins = []
tmp = choice(ps)
last = tmp
lins.append(tmp)
while len(lins) < 100:
    tmp = choice(ps)
    if tmp not in lins and is_swap(tmp, last):
        edge_count = 0
        for l in lins:
            if is_swap(tmp, l):
                edge_count += 1
        if edge_count == 1:
            lins.append(tmp)
            ps.remove(tmp)
            last = tmp

poset_cover(lins, render=True, timeout=10000, tau=False, dir='../long')
