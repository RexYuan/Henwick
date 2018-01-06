from poset_cover import poset_cover
from random import shuffle
from time import time

'''
t = [
'edcba',
'ecdba',
'cebda',
'ecabd',
'ecbda',
'cebad',
'cbeda',
'ceabd',
'cbead',
'cbaed'
]
'''

'''
t = [
'adbce',
'adcbe',
'eadbc',
'eadcb',
'eacdb',
'aecdb',
'acedb',
'acdeb',
'cdabe',
'cdaeb',
'cdbea',
'cdbae',
'dceba',
'acdbe',
'cadeb',
'dcbae',
'debca',
'dcbea',
'dbeca',
'ebadc',
'bedac',
'dbcea',
'bdeca',
'dbeac',
'ebacd',
'beadc',
'bdcea',
'bdeac',
'debac',
'ebcad',
'deabc'
]
'''

t = set()
s = list('abcde')
while len(t) < 50:
	t.add( ''.join(s) )
	shuffle(s)

print('get only one cover')
print('S =',s,'|Y| =',len(t))
time1 = time()
poset_cover(list(t), True)
time2 = time()
print(time2-time1,flush=True)
