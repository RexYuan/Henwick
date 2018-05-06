import pickle
from poset_cover import poset_cover, is_swap
from time import time
from itertools import permutations, islice
from random import sample, choice
from multiprocessing import Pool

ele_size = 20
lin_size = 20
pickle_path = './poset.p'
trials = 3000
procs = 30

def get_rand_lins(lin_size, ele_size):
    history = frozenset()

    n = ele_size # the number of elements
    y = lin_size # the number of linearizations

    while True:
        lins = []
        s = list(map(str,range(n)))
        lins = [''.join(s)]
        while len(lins) < y:
            ext = list(choice(lins))
            swap = choice(list(range(n-1)))
            s = s[:swap]+[s[swap+1]]+[s[swap]]+s[swap+2:]
            if ''.join(s) not in lins:
                lins.append(''.join(s))
        lins = frozenset(lins)

        if lins not in history:
            history = frozenset([]) | history
            yield lins

def poset_cover_wrapper(lins):
    # 5 mins
    return poset_cover(list(lins), render=False, timeout=300000, runaway_timeout=True, getall=False)

if __name__ == '__main__':
    with Pool(processes=procs) as pool:
        ret = pool.map(poset_cover_wrapper, islice(get_rand_lins(lin_size, ele_size), trials))
        pickle.dump(ret, open(pickle_path, "wb"))
