from poset_cover import poset_cover, is_swap
from time import time
from itertools import permutations
from random import sample, choice

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

poset_cover(lins, render=True, timeout=10000, tau=False, dir='long')
