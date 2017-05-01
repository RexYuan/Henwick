from angluin import *

states = {'q0','q1','q2','q3'}
symbols = {'0', '1'}
transitions = {
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
}
start = 'q0'
accepting = {'q0'}
T0 = Teacher(DFA(states, symbols, transitions, start, accepting))
L0 = Learner(T0)

L0.go()
print(T0.U.eq(L0.result))
