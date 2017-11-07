# TODO: make all strings represented as tuples of symbols
# 1) modify fsm
# 2) modify this

from functools import partial
import sys
import fsm

def concat(*tps):
    tmp = tuple()
    for t in tps:
        assert(type(t)==tuple)
        for e in t:
            tmp += (e,) if e!='' else ()
    return tmp if tmp!=() else ('',)

class Teacher:
    def __init__(self, M):
        if type(M) != fsm.DFA and type(M) != fsm.Moore:
            print(type(M))
            raise Exception('M must be DFA or Moore')
        self.M = M
    def get_alphabet(self):
        if type(self.M) == fsm.DFA:
            return set(self.M.symbols)
        elif type(self.M) == fsm.Moore:
            return set(self.M.input)
    def __str__(self):
        return self.M.__str__()
    def member(self, w):
        if type(w) != tuple:
            raise Exception('w must be str tuple')
        if type(self.M) == fsm.DFA:
            return 'T' if w in self.M else 'F'
        elif type(self.M) == fsm.Moore:
            return self.M[w]
    def equiv(self, H):
        if type(H) != type(self.M):
            raise Exception('conjecture H must match M')
        ret = self.M == H
        if ret != True:
            self.counter = ret
            return False
        return True
class Learner:
    def __init__(self, teacher):
        self.teacher = teacher
        self.alphabet = teacher.get_alphabet()
        # observation table
        self.table = {
            'S': {('',)},
            'E': {('',)},
            'T': {(t,): self.teacher.member((t,)) for t in self.alphabet | {''}}
        }
        self.result = None
    def __str__(self):
        if self.result:
            return self.result.__str__()
        raise Exception('go first')
    def _print_table(self):
        pass
    def row(self, s):
        if type(s) != tuple:
            raise Exception('s must be str tuple')
        return ''.join([self.teacher.member(concat(s,e)) for e in self.table['E']])
    def step(self, debug):
        # update T per S and E
        def extend():
            # TODO: optimize
            for s in self.table['S']:
                for a in self.alphabet:
                    for e in self.table['E']:
                        if concat(s,(a,),e) not in self.table['T']:
                            self.table['T'][concat(s,(a,),e)] = self.teacher.member(concat(s,(a,),e))
        if not self.is_consistent():
            # add found a.e to E and extend T
            self.table['E'] |= {self.counter}
            extend()
            if debug:
                print('inconsistent, add to E:', self.counter)
            return False
        if not self.is_closed():
            # add found s.a to S and extend T
            self.table['S'] |= {self.counter}
            extend()
            if debug:
                print('unclosed, add to S:', self.counter)
            return False
        if self.is_consistent() and self.is_closed():
            # make conjecture
            if not self.teacher.equiv(self.get_acceptor()):
                # add found counter example and its prefixes to S and extend T
                self.table['S'] |= {self.teacher.counter[:i+1] for i in range(len(self.teacher.counter))}
                extend()
                if debug:
                    print('conjecture inequivalent, add to S:', self.teacher.counter)
                return False
            else:
                # found it!
                if debug:
                    print('done')
                self.result = self.get_acceptor()
                return True
        raise Exception()
    def go(self, debug=False):
        c = 1
        if debug:
            print('starting...')
            print('----- attempt:',c,' -----')
            self._print_table()
        while not self.step(debug):
            c+=1
            if debug:
                print('\n----- attempt:',c,' -----')
                self._print_table()
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
                    if self.teacher.member(concat(s1,(a,),e)) != self.teacher.member(concat(s2,(a,),e)):
                        # not consistent
                        self.counter = concat((a,),e)
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
                if self.row(concat(s,(a,))) not in [self.row(s) for s in self.table['S']]:
                    # not closed
                    self.counter = concat(s,(a,))
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
        if type(self.teacher.M) == fsm.DFA:
            transitions = {
                self.row(s): {
                    a: self.row(concat(s,(a,))) for a in self.alphabet
                } for s in self.table['S']
            }
            start = self.row(('',))
            finals = {self.row(s) for s in self.table['S'] if self.table['T'][s] == 'T'}
            return fsm.DFA(transitions, start, finals)
        elif type(self.teacher.M) == fsm.Moore:
            transitions = {
                self.row(s): {
                    a: self.row(concat(s,(a,))) for a in self.alphabet
                } for s in self.table['S']
            }
            start = self.row(('',))
            finals = {self.row(s) for s in self.table['S'] if self.table['T'][s]}
            outputs = {
                self.row(s): self.table['T'][s] for s in self.table['S']
            }
            return fsm.Moore(transitions, start, outputs)
