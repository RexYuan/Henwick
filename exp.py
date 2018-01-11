from poset_cover import poset_cover
from time import time

s = list('abcde')
# 40 hard thingly
t = {'abecd', 'dcaeb', 'cedba', 'cabde', 'caebd', 'baced', 'dacbe', 'cebad', 'cdabe', 'badce', 'acebd', 'bcaed', 'acbde', 'acbed', 'aecbd', 'aecdb', 'daecb', 'acdeb', 'cdaeb', 'decab', 'ecdab', 'adceb', 'abced', 'ceadb', 'daceb', 'adecb', 'deabc', 'dbace', 'ecbad', 'caedb', 'acdbe', 'abcde', 'ceabd', 'acedb', 'eacdb', 'bacde', 'cedab', 'edcab', 'deacb', 'bdace'}
print(t, flush=True)
print('get only one cover',flush=True)
print('S =',s,'|Y| =',len(t),flush=True)
time1 = time()
count = poset_cover(list(t), True)
time2 = time()
print(time2-time1,flush=True)
