from poset_cover import poset_cover, is_swap
from time import time
from itertools import permutations
from random import sample, choice, shuffle
from contextlib import redirect_stdout

for trial in range(100):
    n = choice(list(range(10,11)))
    y = choice(list(range(10,101)))

    s = list(map(str,range(n)))
    lins = [''.join(s)]
    while len(lins) < y:
        ext = list(choice(lins))
        swap = choice(list(range(n-1)))
        s = s[:swap]+[s[swap+1]]+[s[swap]]+s[swap+2:]
        if ''.join(s) not in lins:
            lins.append(''.join(s))
    with open('graphs/trial_'+str(trial+1)+'/log.txt', 'w') as f:
        with redirect_stdout(f):
            poset_cover(lins, render=True, timeout=5000, tau=False, dir='graphs/trial_'+str(trial+1))
