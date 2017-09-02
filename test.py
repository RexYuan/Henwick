import fsm, angluin

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
a = fsm.DFA(transitions, start, accepting)
accepting = {'B'}
b = fsm.DFA(transitions, start, accepting)

l = angluin.Learner(angluin.Teacher(a))
l.go()
print(l.result==a)
l = angluin.Learner(angluin.Teacher(b))
l.go()
print(l.result==b)

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
outputs = {
    'A': 'N',
    'B': 'N',
    'C': 'Y',
    'D': 'N',
    'E': 'N',
    'F': 'N',
    'G': 'N',
    'H': 'N',
}
m = fsm.Moore(transitions, start, outputs)
outputs = {
    'A': 'N',
    'B': 'N',
    'C': 'Y',
    'D': 'S',
    'E': 'P',
    'F': 'N',
    'G': 'Q',
    'H': 'W',
}
n = fsm.Moore(transitions, start, outputs)

l = angluin.Learner(angluin.Teacher(m))
l.go()
print(l.result==m)
l = angluin.Learner(angluin.Teacher(n))
l.go()
print(l.result==n)
