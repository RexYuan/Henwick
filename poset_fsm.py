import fsm, angluin

from itertools import permutations

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
        fsm.render(fsm.rename(H), name='poset_fsm')
        return True

        '''
        d = input('is it good? (y/n)  ')
        if d == 'y':
            return True
        else:
            self.counter = tuple(d)
            return False
        self.counter = tuple(c)
        '''

def learn(lins):
    l = angluin.Learner(PosetTeacher(lins))
    l.go(debug=True)

# example
lins = [
'abcdef',
'acbdfe',
'acbfde',
'adcbef',
'acdbfe',
'acdfbe',
'bacdef'
]
learn(lins)
