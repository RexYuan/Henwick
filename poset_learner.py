from itertools import permutations

# !!!!!!!!!important
# NOTE: does L* actually help in any way getting a automaton?
#       we still need to query at worst(best?) case |Y| times,
#       making a equivalence query for every linearizations, aint it!?
#       DOESNT FUCKING MAKE SENSE why w're doing this!!?? FUUUUUUUCKKKKKKK



import fsm, angluin

'''
abc
acb

lins = {
('a','b','c'),
('a','c','b')
}
'''

'''
abcde
acbde
acdbe
acdeb
acedb
acebd

lins = {('a','b','c','d','e'),
('a','c','b','d','e'),
('a','c','d','b','e'),
('a','c','d','e','b'),
('a','c','e','d','b'),
('a','c','e','b','d')}
'''

'''
syms = {'a','b','c'}
lins = {
('a','b','c'),
('a','c','b'),
('b','a','c'),
('b','c','a')
}

syms = set('2741563')
lins ={tuple('2741563'),
tuple('7241563'),
tuple('2741653'),
tuple('7241653'),
tuple('2745163'),
tuple('7245163')}

lins =[tuple('1234567'),
tuple('1235467'),
tuple('1324567'),
tuple('1325467'),
tuple('2134567'),
tuple('2135467'),
tuple('2314567'),
tuple('2315467'),
tuple('3124567'),
tuple('3125467'),
tuple('3214567'),
tuple('3215467'),
tuple('7654321'),
tuple('7654231'),
tuple('76542317654231')]

syms = set('abc')
lins ={tuple('abc'),
tuple('cab'),
tuple('bac'),
tuple('bca'),
tuple('cba')}
'''

syms = set('1234')
lins = [
tuple('1234'),
tuple('2134'),
tuple('2314'),
tuple('3214'),
tuple('3124'),
tuple('4132'),
tuple('4312')
]
lins = list(permutations(tuple('1234')))

lins = [
'acbd',
'cabd',
'acdb',
'cadb',
'cdab'
]
lins = list(map(tuple, lins))
syms = set('acbd')

ls = list(lins)

class PosetTeacher:
    def __init__(self):
        self.M = fsm.DFA({},'',set())
    def get_alphabet(self):
        return syms
    def member(self, w):
        return 'T' if w in lins else 'F'
    def equiv(self, H):
        if ls:
            l = ls.pop()
            self.counter = tuple(l)
            return False
        print(fsm.rename(H))
        fsm.render(fsm.rename(H))
        d = input('is it good? (y/n)  ')
        if d == 'y':
            return True
        else:
            self.counter = tuple(d)
            return False
        self.counter = tuple(c)

l = angluin.Learner(PosetTeacher())
l.go(debug=True)

# do we really need cover relation, save for easy specification?
# 1) firsly the benefits of specification by cover relation only save
# for a polynomial amount of time since order can be refered by
# traversing through the input with n squared steps.
# 2) generating covers for hasse can be done with order relation with
# an extra polynomial time for sorting through the elements
# with a custom comparison function which remembers all of the
# order relation and decides order accordingly
# 3) generating a chain/linearization can be done with simply sort
# the order prefix by order occurance with ascending order which is
# polynomial in number of orders
