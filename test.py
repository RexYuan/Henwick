from angluin import *

'''
trace_target = ['1', '2', '3']
trace1 = ['1', '4', '2', '6', '3']
trace2 = ['7', '1', '2', '6', '7', '3']
trace3 = ['4', '6', '5', '1', '2', '3']
traces = ['123','1423','1423','4123','14263', '712673', '465123']

class EvidenceTeacher:
    def __init__(self):
        pass
    def member(self, w):
        return w in traces
    def equiv(self, M):
        for w in traces:
            if not M.member(w):
                self.counter = w
                return False
        return True

states = {'q0','q1','q2','q3'}
symbols = {'1','2','3','4','5','6','7','8'}
transitions = {
    'q0': {
        '1': 'q1'
    },
    'q1': {
        '2': 'q2'
    },
    'q2': {
        '3': 'q3'
    }
}
start = 'q0'
accepting = {'q3'}
'''

class Stoplight:
    def __init__(self):
        self.light = 'r'
    def tick(self,t):
        if t == '0' and self.light == 'g':
            self.light = 'r'
        elif t == '1' and self.light == 'r':
            self.light = 'g'
        else:
            self.light = 'd'
    def alive(self):
        return self.light != 'd'
    def reset(self):
        self.light = 'r'
class EvidenceTeacher:
    def __init__(self, stoplight):
        self.stoplight = stoplight
    def member(self, w):
        for a in w:
            self.stoplight.tick(a)
        tmp = self.stoplight.alive()
        self.stoplight.reset()
        return tmp
    def equiv(self, M):
        # NOTE: how do i get this?
        tests = ['0', '1', '00', '01','10','11']
        for t in tests:
            if not (self.member(t) == M.member(t)):
                self.counter = t
                return False
        return True

#T = Teacher(DFA(states, symbols, transitions, start, accepting))
I = Stoplight()
T = EvidenceTeacher(I)
#print(T.member('00'))
L = Learner(T)
L.go()
print(L)
