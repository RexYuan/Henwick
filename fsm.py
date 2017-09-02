from functools import reduce
from itertools import product

class FSM:
    '''
    finite state machine base

    types
        state : str
        symbol : str
        transitions : state -> symbol -> state
        start : state

    example
        t = {'A': {'0': 'A',
                   '1': 'B'},
             'B': {'0': 'A',
                   '1': 'B'}}
        s = 'A'
        m = FSM(t, s)
    '''
    def __init__(self, transitions, start, makeshift=False):
        # type check
        if type(transitions) != dict:
            raise Exception('transitions : str -> str -> str')
        if type(start) != str:
            raise Exception('start : str')
        sstates, tstates, symbols = set(), set(), set()
        for p, aqs in transitions.items():
            if type(p) != str or type(aqs) != dict:
                raise Exception('transitions : str -> str -> str')
            if p == '':
                raise Exception('state cannot be empty string')
            if not makeshift and '!' in p:
                raise Exception('illegal name')
            sstates.add(p)
            for a, q in aqs.items():
                if type(a) != str or type(q) != str:
                    raise Exception('transitions : str -> str -> str')
                if a == '':
                    raise Exception('symbol cannot be empty string')
                if q == '':
                    raise Exception('state cannot be empty string')
                if not makeshift and '!' in q:
                    raise Exception('illegal name')
                tstates.add(q)
                symbols.add(a)
        states = sstates|tstates
        dead = False
        # link to dead state if start is dead end
        if not start in sstates:
            dead = True
            transitions[start] = {a: 'd#0' for a in symbols}
        # link to dead state for dead end states
        if not tstates.issubset(sstates):
            dead = True
            for p in tstates - sstates:
                transitions[p] = {a: 'd#0' for a in symbols}
        # link to dead state for states with incomplete transition
        for p, aqs in transitions.items():
            if not set(aqs.keys())==symbols:
                dead = True
                for a in symbols - set(aqs.keys()):
                    transitions[p][a] = 'd#0'
        # dead state stays dead
        if dead:
            transitions['d#0'] = {a: 'd#0' for a in symbols}
            states = {'d#0'}|sstates|tstates
        # store data
        self.states = states
        self.symbols = symbols
        self.transitions = transitions
        self.start = start
    def __str__(self):
        tmp=''
        tmp+='states: '+', '.join(self.states)+'\n'
        tmp+='symbols: '+', '.join(self.symbols)+'\n'
        tmp+='transitions: \n'
        for p in self.transitions:
            for a in self.transitions[p]:
                tmp+='    ('+p+', '+a+') = '+self.transitions[p][a]+'\n'
        tmp+='start: '+self.start+'\n'
        return tmp.rstrip()
    def walk(self, w, verbose=False):
        '''
        returns the state delta(start, w)

        types
            w : symbol tuple
        '''
        if type(w) != tuple:
            raise Exception('w : symbol tuple')
        p = self.start
        width = len(max(w))
        tmp = 'walking from '+p+' on '+'-'.join(w)
        for a in w:
            if a == '':
                return p
            if a not in self.symbols:
                raise Exception('illegal symbol:', a)
            # dead end
            if self.transitions[p][a] == 'd#0':
                tmp += '\n({:{width}}, {:{width}}) -> {:{width}}'.format(p, a, 'd#0', width=width)
                if verbose:
                    print(tmp)
                return 'd#0'
            # transition available
            else:
                tmp += '\n({:{width}}, {:{width}}) -> {:{width}}'.format(p, a, self.transitions[p][a], width=width)
                p = self.transitions[p][a]
        if verbose:
            print(tmp)
        return p

class DFA:
    '''
    deterministic finite automaton without epsilon transition

    types
        state : str
        symbol : str
        transitions : state -> symbol -> state
        start : state
        finals : state set

    example
        t = {'A': {'0': 'A',
                   '1': 'B'},
             'B': {'0': 'A',
                   '1': 'B'}}
        s = 'A'
        f = {'B'}
        m = DFA(t, s, f)

        ('0', '1') in m   # True
        m == m.minimize() # True
    '''
    def __init__(self, transitions, start, finals, makeshift=False):
        self.fsm = FSM(transitions, start, makeshift)
        # type check
        if type(finals) != set:
            raise Exception('finals : state set')
        if not finals.issubset(self.fsm.states):
            raise Exception('finals not subset of states')
        # store data
        self.states = self.fsm.states
        self.symbols = self.fsm.symbols
        self.transitions = self.fsm.transitions
        self.start = self.fsm.start
        self.finals = finals
    def __str__(self):
        return (self.fsm.__str__()+'\nfinals: '+', '.join(self.finals)+'\n').rstrip()
    def __repr__(self):
        return 'DFA({}, {}, {})'.format(self.transitions, "'"+self.start+"'", self.finals)
    def __eq__(self, M):
        return self._eq(M)
    def __ne__(self, M):
        if type(self._eq(M)) == str:
            return True
        return False
    def __contains__(self, w):
        return self._member(w)
    def _member(self, w):
        '''
        return is string w in langauge
        '''
        return self.fsm.walk(w) in self.finals
    def _get_table(self, pt=False):
        '''
        return a table marking distinguishable states
        if _get_table()[p][q] is True, then p and q are distinguishable
        type : dict of dicts of bools (state -> state -> bool)

        print out table if pt is set
        '''
        def print_table():
            # TODO: handle state name with variable length
            print('not implemented')
        s_pairs = set(product(self.states, repeat=2))
        table = {p1: {p2: False for p2 in self.states} for p1 in self.states}
        # pairs of distinguishable states
        dstg_pairs = set()
        # symbol that distinguishes a pair of states
        dstg_symbols = {}
        # basis
        for p1, p2 in s_pairs:
            # final states and non-final states are distinguishable
            if ((p1 in self.finals and p2 not in self.finals) or
                (p1 not in self.finals and p2 in self.finals)):
                table[p1][p2] = True
                dstg_pairs.add((p1, p2))
                dstg_symbols[(p1, p2)] = ''
        # induction
        ps_quene = list(dstg_pairs)
        while ps_quene:
            p1, p2 = ps_quene.pop()
            # if r, s are distinguishable and d(p,a)=r, d(q,a)=s, then p, q are distinguishable
            # TODO: optimize with converse lookup
            for q1, q2 in s_pairs:
                for a in self.symbols:
                    if self.transitions[q1][a] == p1 and self.transitions[q2][a] == p2:
                        table[q1][q2] = True
                        if (q1, q2) not in dstg_pairs:
                            ps_quene.insert(0,(q1, q2))
                            dstg_pairs.add((q1, q2))
                            dstg_symbols[(q1, q2)] = a
        if pt:
            print_table()
        self.dstg_symbols = dstg_symbols
        self.dstg_pairs = dstg_pairs
        return table
    def minimize(self):
        '''
        return minimized DFA
        '''
        s_pairs = set(product(self.states, repeat=2))
        dstg_table = self._get_table()
        # equivalent blocks
        _eq_pairs = s_pairs - self.dstg_pairs
        blocks = []
        # join equivalent states
        for p,q in _eq_pairs:
            if blocks == []:
                blocks.append({p,q})
            elif p not in reduce(set.union, blocks) and q not in reduce(set.union, blocks):
                blocks.append({p,q})
            else:
                for b in blocks:
                    if p in b or q in b:
                        blocks.remove(b)
                        blocks.append(b | {p,q})
        # prepare DFA
        states = set(map(''.join, blocks))
        symbols = set(self.symbols)
        # if p, q are in same block, then d(p, a), d(q, a) must be in same block
        transitions = {
            ''.join(bp): {
                a: [''.join(bq) for bq in blocks if any(self.transitions[p][a] in bq for p in bp)][0]
                for a in symbols
            } for bp in blocks
        }
        # if p is in block B and is start, then B is start
        start = [''.join(bp) for bp in blocks if self.start in bp][0]
        # if p is in block B and is final, then B is final
        finals = {''.join(bp) for bp in blocks if set(bp)&self.finals != set()}
        return DFA(transitions, start, finals)
    def _eq(self, M):
        '''
        return is M equivalent to self

        types
            M : DFA
        '''
        makeshift = False
        # type check
        if type(M) != DFA:
            raise Exception('M : DFA')
        if M.symbols != self.symbols:
            raise Exception('alphabet mismatch')
        # state name conflict
        if (self.states-{'d#0'}) & (M.states-{'d#0'}) != set():
            # SSA M state name
            rename_tab = {p: 's!'+str(n) for n, p in enumerate(M.states)}
            transitions = {
                rename_tab[p]: {
                    a: rename_tab[M.transitions[p][a]] for a in M.symbols
                } for p in M.states
            }
            start = rename_tab[M.start]
            finals = {rename_tab[p] for p in M.finals}
            M = DFA(transitions, start, finals, True)
            makeshift = True
        # join states and prepare DFA
        states = self.states | M.states
        symbols = self.symbols
        transitions = {**self.transitions, **M.transitions}
        start = self.start
        finals = self.finals | M.finals
        P = DFA(transitions, start, finals, makeshift)
        # check if self's start and M's start are equivalent in joined DFA
        if P._get_table()[self.start][M.start]:
            # return a distinguishing string in symmetric difference of L(self) and L(M)
            p = self.start
            q = M.start
            w = tuple()
            while ((p not in self.finals and q not in M.finals) or
                   (p in self.finals and q in M.finals)):
                w += (P.dstg_symbols[(p, q)],)
                p, q = self.transitions[p][P.dstg_symbols[(p, q)]], M.transitions[q][P.dstg_symbols[(p, q)]]
            return w if w!=() else ('',)
        else:
            # equivalent
            return True

class Moore:
    '''
    simple moore machine

    types
        state : str
        input : str
        output : str
        transitions : state -> input -> state
        start : state
        outputs : state -> output

    example
        t = {'A': {'0': 'A',
                   '1': 'B'},
             'B': {'0': 'A',
                   '1': 'B'}}
        s = 'A'
        o = {'A': 'X',
             'B': 'Y'}
        m = Moore(t, s, o)

        m[('0', '1')]     # 'Y'
        m == m.minimize() # True
    '''
    def __init__(self, transitions, start, outputs, makeshift=False):
        self.fsm = FSM(transitions, start, makeshift)
        # type check
        if type(outputs) != dict:
            raise Exception('outputs : state -> output')
        if not outputs.keys() == self.fsm.states:
            raise Exception('outputs states mismatch')
        if any(type(o) != str for o in outputs.values()):
            raise Exception('outputs : state -> output')
        # store data
        self.states = self.fsm.states
        self.input = self.fsm.symbols
        self.output = set(outputs.values())
        self.transitions = self.fsm.transitions
        self.start = self.fsm.start
        self.outputs = outputs
    def __str__(self):
        tmp=self.fsm.__str__()
        tmp+='\noutputs: '
        for p in self.outputs:
            tmp+='\n     '+p+' = '+self.outputs[p]
        return tmp.rstrip()
    def __eq__(self, M):
        return self._eq(M)
    def __ne__(self, M):
        if type(self._eq(M)) == str:
            return True
        return False
    def __getitem__(self, w):
        return self._output(w)
    def _output(self, w):
        '''
        return last output symbol on input string w
        '''
        return self.outputs[self.fsm.walk(w)]
    def _get_table(self, pt=False):
        '''
        return a table marking distinguishable states
        if _get_table()[p][q] is True, then p and q are distinguishable
        type : dict of dicts of bools (state -> state -> bool)

        print out table if pt is set
        '''
        def print_table():
            # TODO: handle state name with variable length
            print('not implemented')
        s_pairs = set(product(self.states, repeat=2))
        table = {p1: {p2: False for p2 in self.states} for p1 in self.states}
        # pairs of distinguishable states
        dstg_pairs = set()
        # symbol that distinguishes a pair of states
        dstg_symbols = {}
        # basis
        for p1, p2 in s_pairs:
            # states with different outputs are distinguishable
            if self.outputs[p1] != self.outputs[p2]:
                table[p1][p2] = True
                dstg_pairs.add((p1, p2))
                dstg_symbols[(p1, p2)] = ''
        # induction
        ps_quene = list(dstg_pairs)
        while ps_quene:
            p1, p2 = ps_quene.pop()
            # if r, s are distinguishable and d(p,a)=r, d(q,a)=s, then p, q are distinguishable
            # TODO: optimize with converse lookup
            for q1, q2 in s_pairs:
                for a in self.input:
                    if self.transitions[q1][a] == p1 and self.transitions[q2][a] == p2:
                        table[q1][q2] = True
                        if (q1, q2) not in dstg_pairs:
                            ps_quene.insert(0,(q1, q2))
                            dstg_pairs.add((q1, q2))
                            dstg_symbols[(q1, q2)] = a
        if pt:
            print_table()
        self.dstg_symbols = dstg_symbols
        self.dstg_pairs = dstg_pairs
        return table
    def minimize(self):
        '''
        return minimized Moore machine
        '''
        s_pairs = set(product(self.states, repeat=2))
        dstg_table = self._get_table()
        # equivalent blocks
        _eq_pairs = s_pairs - self.dstg_pairs
        blocks = []
        # join equivalent states
        for p,q in _eq_pairs:
            if blocks == []:
                blocks.append({p,q})
            elif p not in reduce(set.union, blocks) and q not in reduce(set.union, blocks):
                blocks.append({p,q})
            else:
                for b in blocks:
                    if p in b or q in b:
                        blocks.remove(b)
                        blocks.append(b | {p,q})
        # prepare DFA
        states = set(map(''.join, blocks))
        input = set(self.input)
        # if p, q are in same block, then d(p, a), d(q, a) must be in same block
        transitions = {
            ''.join(bp): {
                a: [''.join(bq) for bq in blocks if any(self.transitions[p][a] in bq for p in bp)][0]
                for a in input
            } for bp in blocks
        }
        # if p is in block B and is start, then B is start
        start = [''.join(bp) for bp in blocks if self.start in bp][0]
        # if p is in block B and is output of p is o, then output of B is o
        outputs = {''.join(bp): self.outputs[next(iter(bp))] for bp in blocks}
        return Moore(transitions, start, outputs)
    def _eq(self, M):
        '''
        return is M equivalent to self

        types
            M : DFA
        '''
        makeshift = False
        # type check
        if type(M) != Moore:
            raise Exception('M : DFA')
        if M.input != self.input:
            raise Exception('alphabet mismatch')
        # state name conflict
        if (self.states-{'d#0'}) & (M.states-{'d#0'}) != set():
            # SSA M state name
            rename_tab = {p: 's!'+str(n) for n, p in enumerate(M.states)}
            transitions = {
                rename_tab[p]: {
                    a: rename_tab[M.transitions[p][a]] for a in M.input
                } for p in M.states
            }
            start = rename_tab[M.start]
            outputs = {rename_tab[p]: M.outputs[p] for p in M.states}
            M = Moore(transitions, start, outputs, True)
            makeshift = True
        # join states and prepare DFA
        states = self.states | M.states
        input = self.input
        transitions = {**self.transitions, **M.transitions}
        start = self.start
        outputs = {**self.outputs, **M.outputs}
        P = Moore(transitions, start, outputs, makeshift)
        # check if self's start and M's start are equivalent in joined DFA
        if P._get_table()[self.start][M.start]:
            # return a distinguishing string in symmetric difference of L(self) and L(M)
            p = self.start
            q = M.start
            w = tuple()
            while self.outputs[p] == M.outputs[q]:
                w += (P.dstg_symbols[(p, q)],)
                p, q = self.transitions[p][P.dstg_symbols[(p, q)]], M.transitions[q][P.dstg_symbols[(p, q)]]
            return w if w!=() else ('',)
        else:
            # equivalent
            return True
