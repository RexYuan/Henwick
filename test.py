from angluin import *

# even number of 1s and 0s
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
T = Teacher(DFA(states, symbols, transitions, start, accepting))
L = Learner(T)

L.go()
print('minimized? ===> ',len(T.U.minimize().states) == len(L.result.states),'\n')

# contains substring 11
states = {'init','seen1','done'}
symbols = {'0', '1'}
transitions = {
    'init': {
        '0': 'init',
        '1': 'seen1'
    },
    'seen1': {
        '0': 'init',
        '1': 'done'
    },
    'done': {
        '0': 'done',
        '1': 'done'
    }
}
start = 'init'
accepting = {'done'}
T = Teacher(DFA(states, symbols, transitions, start, accepting))
L = Learner(T)

L.go()
print('minimized? ===> ',len(T.U.minimize().states) == len(L.result.states),'\n')

states = {'A','B','C','D','E','F','G','H'}
symbols = {'0', '1'}
transitions = {
    'A': {
        '0': 'B',
        '1': 'F'
    },
    'B': {
        '0': 'G',
        '1': 'C'
    },
    'C': {
        '0': 'A',
        '1': 'C'
    },
    'D': {
        '0': 'C',
        '1': 'G'
    },
    'E': {
        '0': 'H',
        '1': 'F'
    },
    'F': {
        '0': 'C',
        '1': 'G'
    },
    'G': {
        '0': 'G',
        '1': 'E'
    },
    'H': {
        '0': 'G',
        '1': 'C'
    }
}
start = 'A'
accepting = {'C'}
T = Teacher(DFA(states, symbols, transitions, start, accepting))
L = Learner(T)

L.go()
print('minimized? ===> ',len(T.U.minimize().states) == len(L.result.states),'\n')

states = {'A','B','C','D','E'}
symbols = {'0', '1'}
transitions = {
    'A': {
        '0': 'A',
        '1': 'B'
    },
    'B': {
        '0': 'A',
        '1': 'B'
    },
    'C': {
        '0': 'D',
        '1': 'E'
    },
    'D': {
        '0': 'D',
        '1': 'E'
    },
    'E': {
        '0': 'C',
        '1': 'E'
    }
}
start = 'E'
accepting = {'A', 'C', 'D'}
T = Teacher(DFA(states, symbols, transitions, start, accepting))
L = Learner(T)

L.go()
print('minimized? ===> ',len(T.U.minimize().states) == len(L.result.states),'\n')
