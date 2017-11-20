

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
'''

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

syms = set('123')
lins ={tuple('123'),
tuple('132'),
tuple('213'),
tuple('231'),
tuple('312'),
tuple('321')}

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
