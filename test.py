from angluin import *

# NOTE
# 0) dfa/mealy <-> circuit <-> function <-> tm
# 1) formal verification PR => settle a chinese name
#                              US outlets first, two-way articles:
#                              overview for programmer vs for non-programmer
#                              canonical use case?
#                              (analogous to ML's partition problem)
#                              people's feature, current breakthrough and news
#                              * what can they benefit from it
# 2) slow progress. should i worry not yet settled? suggest some problems?

# NOTE
# 3) behavior inference => finite incomplete event sequence
#                          the case when evidence membership query is also impossible
#                          "unknown" value?
#                          data may always be incomplete. noise alway exists. unfeasible MAT?
#                          how to get a "good enough" model?
#                          * "mapper"? query element is problem-specific
#                          even if membership query is good
#                          nothing as a reference for conformance testing?
#                          look-ahead when learning? how many steps?
#                          definitely unsound. but would it be "good enough"
#                          * infinite seq impossible. what's a long enough seq?

# trace_target = '(.*)1(.*)2(.*)3(.*)'
class EvidenceTeacher:
    def __init__(self):
        self.traces = ['123','1423','1423','4123','14263', '712673', '465123']
    def member(self, w):
        return w in self.traces
    def equiv(self, M):
        for w in self.traces:
            if not M.member(w):
                self.counter = w
                return False
        return True

#####################################

class Lottery:
    def __init__(self, winners):
        self.winners = winners
    def is_winner(self, w):
        return w in self.winners
class EvidenceTeacher:
    def __init__(self, sul):
        self.sul = sul
    def get_alphabet(self):
        return {'0','1','2','3','4','5','6','7','8','9'}
    def member(self, w):
        return self.sul.is_winner(w)
    def equiv(self, M):
        raise Exception()
L = Learner(EvidenceTeacher(Lottery(['22222','12345','98765'])))
#L.go()
#print(L.result)

#####################################

# NOTE
# 4) black box checking => given program, sound and complete membership query
#                          conformace testing for equivalence query
#                          but what's a sufficient equivalence query

class Stoplight:
    def __init__(self):
        self.light = 'g'
    def tick(self,t):
        if t == '0' and self.light == 'g':
            self.light = 'r'
        elif t == '1' and self.light == 'r':
            self.light = 'y'
        elif t == '2' and self.light == 'y':
            self.light = 'g'
        else:
            self.light = 'd'
    def alive(self):
        return self.light != 'd'
    def reset(self):
        self.light = 'g'
class EvidenceTeacher:
    def __init__(self, stoplight):
        self.stoplight = stoplight
    def get_alphabet(self):
        return {'0','1','2'}
    def member(self, w):
        for a in w:
            self.stoplight.tick(a)
        tmp = self.stoplight.alive()
        self.stoplight.reset()
        return tmp
    def equiv(self, M):
        # NOTE: how do i get this?
        tests = ['000','001','002','010','011','012','020','021','022','100',
                 '101','102','110','111','112','120','121','122','200','201',
                 '202','210','211','212','220','221','222','00','01','02',
                 '10','11','12','20','21','22','0','1','2']

        for t in tests:
            if not (self.member(t) == M.member(t)):
                self.counter = t
                return False
        return True
I = Stoplight()
T = EvidenceTeacher(I)
L = Learner(T)
#L.go()

config = [
    {'r','g','y'}, # states
    {'0', '1','2'}, # symbols
    { # transitions
        'g': {
            '0': 'r'
        },
        'r': {
            '1': 'y'
        },
        'y': {
            '2': 'g'
        }
    },
    'g', # start
    {'r','g','y'} # final
]
Target = DFA(*config)
#print(Target.eq(L.result))

#####################################

'''
class Even01:
    def __init__(self):
        self.ones = 0
        self.zeros = 0
    def take(self,a):
        if a == '0':
            self.zeros += 1
        elif a == '1':
            self.ones += 1
    def good(self):
        return self.ones % 2 == 0 and self.zeros % 2 == 0
    def reset(self):
        self.ones = 0
        self.zeros = 0
class EvidenceTeacher:
    def __init__(self, even):
        self.even = even
    def get_alphabet(self):
        return {'0','1'}
    def member(self, w):
        for a in w:
            self.even.take(a)
        tmp = self.even.good()
        self.even.reset()
        return tmp
    def equiv(self, M):
        # counterexamples uncaught: 100, 010 ... ?
        tests = ['0', '1', '00', '01', '10', '11']

        for t in tests:
            if not (self.member(t) == M.member(t)):
                self.counter = t
                return False
        return True
'''
def even01(w):
    ones = 0
    zeros = 0
    for a in w:
        if a == '1':
            ones += 1
        elif a == '0':
            zeros += 1
        else:
         raise Exception()
    return ones % 2 == 0 and zeros % 2 == 0
class EvidenceTeacher:
    def __init__(self, f):
        self.f = f
    def get_alphabet(self):
        return {'0','1'}
    def member(self, w):
        return self.f(w)
    def equiv(self, M):
        # counterexamples uncaught: 100, 010 ... ?
        tests = ['0', '1', '00', '01', '10', '11', '100', '010']

        for t in tests:
            if not (self.f(t) == M.member(t)):
                self.counter = t
                return False
        return True
T = EvidenceTeacher(even01)
L = Learner(T)
L.go()

config = [
    {'q0','q1','q2','q3'}, # states
    {'0', '1'}, # symbols
    { # transitions
        'q0': {
            '0': 'q2',
            '1': 'q1'
        },
        'q1': {
            '0': 'q3',
            '1': 'q0'
        },
        'q2': {
            '0': 'q0',
            '1': 'q3'
        },
        'q3': {
            '0': 'q1',
            '1': 'q2'
        }
    },
    'q0', # start
    {'q0'} # final
]
Target = DFA(*config)
print(Target.eq(L.result))
