# target
# And(Implies(n>100,And(c>=0,n>100,ret==n-10+10*c)),Implies(n<=100,And(Implies(ret>=90,And(91-c<=ret,ret<=91+10*c)),Implies(ret<90,c>0))))
# expression length = 50

# vocabulary
# T->Int           : Int (n, c, ret)
# Bool->Bool->Bool : And, Or, Implies
# Int->Int->Bool   : <, <=, ==
# Int->Int->Int    : +, -, *

# grammar
# Root ::= And(BoolExp, BoolExp) | Or(BoolExp, BoolExp) | Implies(BoolExp, BoolExp)
# BoolExp ::= IntExp < IntExp | IntExp <= IntExp | IntExp == IntExp | T | F
# IntExp ::= IntExp + IntExp | IntExp - IntExp | IntExp * IntExp | Int

# how to check well-formness? and convert from string to z3?
# how many Int var to have? how to model constants? 100, 10, 90, 91, 0?
# what are the concrete examples in concolic approach here?
# how to prune program generation? time grow too fast(small limit would time out)
# prune with saving intermediate form and skip when encountered?

from z3 import *
from pprint import PrettyPrinter
from itertools import chain
from time import time
class Z3:
    def __init__(self, exp_size_limit):
        # CFG
        self.productions = {
            'Root':    [['And',     'BoolExp', 'BoolExp'],
                        ['Or',      'BoolExp', 'BoolExp'],
                        ['Implies', 'BoolExp', 'BoolExp']],
            'BoolExp': [['IntExp', '<',  'IntExp'],
                        ['IntExp', '<=', 'IntExp'],
                        ['IntExp', '==', 'IntExp'],
                        ['T'], ['F']],
            'IntExp':  [['IntExp', '+', 'IntExp'],
                        ['IntExp', '-', 'IntExp'],
                        ['IntExp', '*', 'IntExp'],
                        ['Int']]#,
            #'Int':     [['X'],
            #            ['Y'],
            #            ['Z']]
        }
        self.arity = {
            'Int': 0,
            'And': 2,
            'Or': 2,
            'Implies': 2,
            '<': 2,
            '<=': 2,
            '==': 2,
            '+': 2,
            '-': 2,
            '*': 2
        }
        self.expressions = [[] for _ in range(exp_size_limit)]
    def genesis(self, exp, depth, limit):
        '''
        Recursively generate all Z3 expressions using depth limited search
        with depth(symbol count) <= limit
        The generated expressions populate self.expressions

        When called outside:
        1) exp should be ['Root']
        2) depth should be 1
        3) limit should be larger than 1
        e.g. Z3_obj.genesis(['Root'], 1, 5)
        '''
        # recursion base
        if not exp or len(exp) > limit:
            return False
        # terminus
        elif not any(s in self.productions for s in exp):
            if exp not in self.expressions[depth-1]:
                self.expressions[depth-1].append(exp)
            return True
        # additional expansion possible
        for index, symbol in enumerate(exp):
            # symbol can be expanded
            if symbol in self.productions:
                # for every expansion it has
                for prod in self.productions[symbol]:
                    # replace symbol with its expansion
                    new_exp = list(chain(exp[:index], prod, exp[index+1:]))
                    # expand
                    self.genesis(new_exp, depth+len(prod)-1, limit)
s = Z3(10)
t = time()
s.genesis(['Root'], 1, 5)
print(time()-t)
PrettyPrinter(indent=4, width=60).pprint(s.expressions)

"""
def isImpValid(solver, imp):
    solver.push()
    solver.add(Not(imp))
    result = solver.check()
    solver.pop()
    return result == unsat
def checkInvariant(eta):
    firstReq = Implies(And(c > 0, eta), And(Implies(ret > 100, substitute(substitute(eta, (c, c-1)), (ret, ret-10))), Implies(ret <= 100, substitute(substitute(eta, (c, c+1)), (ret, ret+11)))))
    if not isImpValid(s, firstReq):
        raise Exception("firstReq failed")
    secondReq = Implies(And(ret == n, c == 1), eta)
    if not isImpValid(s, secondReq):
        raise Exception("secondReq failed")
    thirdReq = Implies(And(eta, c <= 0), And(Implies((n <= 100), (ret == 91)), Implies((n > 100), (ret == n - 10))))
    if not isImpValid(s, thirdReq):
        raise Exception("thirdReq failed")
    print("Success")
    return True
s = Solver()
n = Int('N')
ret = Int('RET')
c = Int('C')

#eta = And (Implies (n > 100, And (c >= 0, n > 100, ret == n - 10 + 10 * c)), Implies (n <= 100, And (Implies (ret >=  90, And (91 - c <= ret, ret <= 91 + 10 * c)), Implies (ret <   90, c > 0))))
#eta = gen
#checkInvariant(eta)
"""
