from poset_cover import poset_cover, is_swap

from random import shuffle, choice, sample
from time import time
from itertools import permutations
from math import factorial
from pprint import pprint
# connected_poset_cover(ls, getall=getall, g=comp, tau=tau, log=log, breakaway_p=breakaway_p, breakaway_v=breakaway_v)

# len of powerset of 4 permutations = 16777216; too big

s = list('abcd')
t = list(map(lambda l:''.join(l), list(permutations(s))))

times = []
seen = []
# randomly choose 1000 subsets
for _ in range(1000):
    lins = sample(t, choice(list(range(1,25))))
    while lins in seen:
        lins = sample(t, choice(list(range(1,25))))
    t1 = time()
    ret = poset_cover(lins)
    times.append( time()-t1 )
    seen.append(lins)

print(times)
print('avg',sum(times)/len(times))
