from poset_cover import poset_cover, is_swap

from random import shuffle, choice
from time import time
from itertools import permutations
from math import factorial
from pprint import pprint
# connected_poset_cover(ls, getall=getall, g=comp, tau=tau, log=log, breakaway_p=breakaway_p, breakaway_v=breakaway_v)

# len of powerset of 4 permutations = 16777216; too big

s = list('abcd')
t = list(map(lambda l:''.join(l), list(permutations(s))))

times = []
# get all subsets of len 23
for i in range(24):
    lins = t[:i]+t[i+1:]
    t1 = time()
    ret = poset_cover(lins)
    times.append( time()-t1 )

print(times)
print('avg',sum(times)/len(times))
