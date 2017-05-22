from functools import partial
import sys
sys.path.append('/Users/Rex/Namara')
from dfa import *

class Teacher:
    def __init__(self, U):
        if type(U) != DFA:
            raise Exception('target U must be DFA')
        self.U = U
    def __str__(self):
        return self.U.__str__()
    def member(self, w):
        if type(w) != str:
            raise Exception('w must be str')
        return self.U.member(w)
    def equiv(self, M):
        if type(M) != DFA:
            raise Exception('conjecture M must be DFA')
        ret = self.U.eq(M)
        if ret != True:
            self.counter = ret
            return False
        return True
class Learner:
    def __init__(self, teacher):
        self.teacher = teacher
        #self.alphabet = set(teacher.U.symbols)
        self.alphabet = {'0','1','2'}
        # observation table
        self.table = {
            'S': {''},
            'E': {''},
            'T': {t: self.teacher.member(t) for t in {''} | self.alphabet}
        }
        self.result = None
    def __str__(self):
        if self.result:
            return self.result.__str__()
        raise Exception('go first')
    def row(self, s):
        return ''.join(str(int(self.teacher.member(s + e))) for e in self.table['E'])
    def step(self):
        # update T per S and E
        def extend():
            # TODO: optimize
            for s in self.table['S']:
                for a in self.alphabet | {''}:
                    for e in self.table['E']:
                        if s+a+e not in self.table['T']:
                            self.table['T'][s+a+e] = self.teacher.member(s+a+e)
        if not self.is_consistent():
            # add found a.e to E and extend T
            self.table['E'] |= {self.counter}
            extend()
            print('inconsistent, add to E:', self.counter)
            return False
        if not self.is_closed():
            # add found s.a to S and extend T
            self.table['S'] |= {self.counter}
            extend()
            print('unclosed, add to S:', self.counter)
            return False
        if self.is_consistent() and self.is_closed():
            # make conjecture
            if not self.teacher.equiv(self.get_acceptor()):
                # add found counter example and its prefixes to S and extend T
                self.table['S'] |= {self.teacher.counter[:i+1] for i in range(len(self.teacher.counter))}
                extend()
                print('conjecture inequivalent, add to S:', self.teacher.counter)
                return False
            else:
                # found it!
                print('done')
                self.result = self.get_acceptor()
                return True
        raise Exception()
    def go(self):
        print('starting...')
        c = 1
        print('attempt:',c)
        while not self.step():
            c+=1
            print('attempt:',c)
    def is_consistent(self):
        '''
        return is observation table consistent
        and set self.counter for found a.e if not

        an observation table is consistent iff:
            for all s1, s2 of S, if row(s1) = row(s2), then, for all a of A, row(s1.a)=row(s2.a)
        '''
        for s1, s2 in [(s1, s2) for s1 in self.table['S'] for s2 in self.table['S'] if s1 != s2 and self.row(s1) == self.row(s2)]:
            for a in self.alphabet:
                for e in self.table['E']:
                    if self.teacher.member(s1+a+e) != self.teacher.member(s2+a+e):
                        # not consistent
                        self.counter = a+e
                        return False
        return True
    def is_closed(self):
        '''
        return is observation table closed
        and set self.counter for found s.a if not

        an observation table is closed iff:
            for all t of S.A, there exists an s of S, such that row(t) = row(s)
        '''
        for s in self.table['S']:
            for a in self.alphabet:
                if self.row(s+a) not in [self.row(s) for s in self.table['S']]:
                    # not closed
                    self.counter = s+a
                    return False
        return True
    def get_acceptor(self):
        '''
        return the corresponding acceptor

        if (S,E,T) is a closed, consistent observation table,
        then the corresponding acceptor M(S,E,T) is:
            states = {row(s) for all s of S}
            symbols = given alphabet A
            transitions = row(s), a => row(s.a)
            start = row('')
            accepting = {row(s) for all s of S if T(s) = 1}
        '''
        states = {self.row(s) for s in self.table['S']}
        symbols = set(self.alphabet)
        transitions = {
            self.row(s): {
                a: self.row(s+a) for a in self.alphabet # NOTE: WTF why s+a need not be in S? it may not be a state!
            } for s in self.table['S']
        }
        start = self.row('')
        accepting = {self.row(s) for s in self.table['S'] if self.table['T'][s]}
        return DFA(states, symbols, transitions, start, accepting)
