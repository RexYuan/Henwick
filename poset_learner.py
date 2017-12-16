from itertools import permutations

# !!!!!!!!!important
# NOTE: does L* actually help in any way getting a automaton?
#       we still need to query at worst(best?) case |Y| times,
#       making a equivalence query for every linearizations, aint it!?
#       DOESNT FUCKING MAKE SENSE why w're doing this!!?? FUUUUUUUCKKKKKKK

import fsm, angluin

lins = [
'abdcfe',
'badcfe'
]
lins = [
'abcdef'
]
lins = [
'badcef',
'badcfe'
]
lins = [
'abcdef',
'badcef',
'abdcfe',
'badcfe'
]
syms = set(lins[0])
lins = list(map(tuple, lins))
ls = list(lins)

class PosetTeacher:
    def __init__(self,lins):
        self.syms = set(lins[0])
        self.lins = list(map(tuple, lins))
        self.ls = list(lins)
        self.ls.append(lins[0]*2)
        self.M = fsm.DFA({},'',set())
    def get_alphabet(self):
        syms = self.syms
        lins = self.lins
        ls = self.ls
        return syms
    def member(self, w):
        syms = self.syms
        lins = self.lins
        ls = self.ls
        return 'T' if w in lins else 'F'
    def equiv(self, H):
        syms = self.syms
        lins = self.lins
        ls = self.ls
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

#l = angluin.Learner(PosetTeacher())
#l.go(debug=True)

def learn(lins):
    l = angluin.Learner(PosetTeacher(lins))
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
