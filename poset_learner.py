

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

syms = {'a','b','c'}
lins = {
('a','b','c'),
('a','c','b'),
('b','a','c'),
('b','c','a')
}

class PosetTeacher:
    def __init__(self):
        self.M = fsm.DFA({},'',set())
    def get_alphabet(self):
        return syms
    def member(self, w):
        return 'T' if w in lins else 'F'
    def equiv(self, H):
        print(fsm.rename(H))
        d = input('is it good? (y/n)  ')
        if d == 'y':
            return True
        elif d == 'n':
            c = input('counter? (string)  ')
        else:
            raise Exception()
        self.counter = tuple(c)
        return False

l = angluin.Learner(PosetTeacher())
l.go(debug=True)
