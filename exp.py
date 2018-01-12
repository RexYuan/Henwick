from poset_cover import poset_cover
from time import time
from itertools import permutations
from random import sample

s = list('abcde')
ps=list(map(lambda l:''.join(l), list(permutations(s))))
# 40 hard thingly
#t = {'abecd', 'dcaeb', 'cedba', 'cabde', 'caebd', 'baced', 'dacbe', 'cebad', 'cdabe', 'badce', 'acebd', 'bcaed', 'acbde', 'acbed', 'aecbd', 'aecdb', 'daecb', 'acdeb', 'cdaeb', 'decab', 'ecdab', 'adceb', 'abced', 'ceadb', 'daceb', 'adecb', 'deabc', 'dbace', 'ecbad', 'caedb', 'acdbe', 'abcde', 'ceabd', 'acedb', 'eacdb', 'bacde', 'cedab', 'edcab', 'deacb', 'bdace'}
lins = sample(ps, 110)

poset_cover(lins, render=True, timeout=10000, tau=False)
