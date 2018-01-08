from poset_cover import poset_cover
#from new_poset_cover import poset_cover
from random import shuffle
from time import time

def is_swap(s1, s2):
	pair = False
	i = 0
	while i < len(s1):
		if s1[i] != s2[i]:
			if i == len(s1)-1:
				return False
			if (s1[i] == s2[i+1] and s1[i+1] == s2[i]):
				if pair:
					return False
				pair = True
				i += 1
			else:
				return False
		i += 1
	return pair

'''
s = list('abcde')
t = {
'baced',
'dabec',
'dbcae',
'bdcae',
'abced',
'abdce',
'bdace',
'ebcda',
'badce',
'bacde',
'becda',
'badec',
'dbace',
'cbaed',
'bcade',
'cbeda',
'bcead',
'eabcd',
'dbaec',
'cadbe',
'bdaec',
'becad',
'abecd',
'dabce',
'bceda',
'adbec',
'caebd',
'acbed',
'cabde',
'baecd',
'aebcd',
'cabed',
'abcde',
'beacd',
'abedc',
'acbde',
'ebcad',
'bcdae',
'ceabd',
'acdbe'
}
'''
leng = 40
t = set()
s = list('abcde')
t.add( ''.join(s) )
while len(t) < leng:
	if any(is_swap(''.join(s), l) for l in t):
		t.add( ''.join(s) )
	shuffle(s)
print(t)
print('get only one cover')
print('S =',s,'|Y| =',len(t))
time1 = time()
count = poset_cover(list(t), True)
time2 = time()
while count < 11:
	t = set()
	s = list('abcde')
	t.add( ''.join(s) )
	while len(t) < leng:
		if any(is_swap(''.join(s), l) for l in t):
			t.add( ''.join(s) )
		shuffle(s)
	print(t)
	print('get only one cover')
	print('S =',s,'|Y| =',len(t))
	time1 = time()
	poset_cover(list(t), True)
	time2 = time()

print(time2-time1,flush=True)
