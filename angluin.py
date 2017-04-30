# self.table['S'] | {s+a for s in self.table['S'] for a in self.alphabet}

from functools import partial
import sys
sys.path.append('/Users/Rex/Namara')
from dfa import *

class Teacher:
    def __init__(self, U):
        if type(U) != DFA:
            raise Exception('target U must be DFA')
        self.U = U

    def member(self, w):
        if type(w) != str:
            raise Exception('w must be str')
        return self.U.member(w)

    def equiv(self, M):
        if type(M) != DFA:
            raise Exception('conjecture M must be DFA')
        return self.U.eq(M)

class Learner:
    def __init__(self, teacher):
        self.teacher = teacher
        self.alphabet = set(teacher.U.symbols)
        # observation tables
        self.table = {
            'S': {''},
            'E': {''},
            'T': {t: self.teacher.member(t) for t in {''} | self.alphabet}
        }
    def row(self, s):
        return ''.join(str(int(self.teacher.member(s + e))) for e in self.table['E'])
        #def partial_app(e):
        #    return self.teacher.member(s+e)
        #return partial_app
    def step(self):
        def extend(sa=None, ae=None):
            if sa != None:
                self.table['S'].append(sa)
                for a in self.alphabet:
                    for e in self.table['E']:
                        self.table['T'][sa+a+e] = self.teacher.member(sa+a+e)
            elif ae != None:
                self.table['E'].append(ae)
                for a in self.alphabet:
                    for s in self.table['S']:
                        self.table['T'][s+a+ae] = self.teacher.member(s+a+ae)
        result = self.is_consistent()
        if result is not True:
            s1,s2,a,e = result
            extend(ae=a+e)
        result = is_closed()
        if result is not True:
            t = result
            extend(sa=t)
        result = self.teacher.equiv(self.get_acceptor())
        if result is not True:
            # TODO: handle symmetric difference counter example
            pass
        else:
            print('done')
    def is_closed(self):
        '''
        return is observation table closed

        an observation table is closed iff:
        for all t of S.A, there exists an s of S, such that row(t) = row(s)
        '''
        for t in [s+a for s in self.table['S'] for a in self.alphabet]:
            if self.row(t) not in [self.row(s) for s in self.table['S']]:
                # not closed
                return (t)
        return True
    def is_consistent(self):
        '''
        return is observation table consistent

        an observation table is consistent iff:
        for all s1, s2 of S, if row(s1) = row(s2), then, for all a of A, row(s1.a)=row(s2.a)
        '''
        for s1 in self.table['S']:
            for s2 in self.table['S']:
                if s1 != s2 and self.row(s1) == self.row(s2):
                    for a in self.alphabet:
                        for e in self.table['E']:
                            if self.lookup(s1+a,e) != self.lookup(s1+a,e):
                                # not consistent
                                return (s1,s2,a,e)
        return True
    def get_acceptor(self):
        '''
        return the corresponding acceptor

        if (S, E, T) is a closed, consistent observation table,
        the corresponding acceptor M(S, E, T) over the alphabet A
        , with state set Q, initial state qO, accepting states F, and transition function 6 as follows:
        Q= {row(s):sES},
        '''
        states = {self.row(s) for s in self.table['S']}
        symbols = set(self.alphabet)
        transitions = {
            self.row(s): {
                a: self.row(s+a) for a in self.alphabet if s+a in self.table['S']
            } for s in self.table['S']
        }
        start = self.row('')
        accepting = {self.row(s) for s in self.table['S'] if self.table['T'][s]}
        return DFA(states, symbols, transitions, start, accepting)
