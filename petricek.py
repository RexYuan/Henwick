"""
generate a loop invariant expression for Tomas Petricek's
example program retrieved from http://stackoverflow.com/a/3221583/2448540
"""

# program:
# int j = 9;
# int i = 0;
# while (i < 10)
# {
#     i = i + 1;
#     j = j - 1;
# }

# req: all these implications are valid
# 1) j == 9 and i == 0 => eta
# 2) eta and not i < 10 => j <= -1
# 3) i < 10 and eta => eta[j-1/j][i+1/i]

# target: eta is
# i + j == 9

# grammar:
# S   ::= Var - Var == Cst | Var * Var == Cst | Var + Var == Cst
# Cst ::= 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10
# Var ::= i | j

from z3 import *
from time import time

class Z3:
    def __init__(self):
        self.S = Bool('S')
        self.i = Int('i')
        self.j = Int('j')
        self._1 = Int('_1')
        self._2 = Int('_2')
        self._3 = Int('_3')
        self.prod = {
            self.S:  [self._1 - self._2 == self._3, self._1 * self._2 == self._3, self._1 + self._2 == self._3],
            self._1: [self.i, self.j],
            self._2: [self.i, self.j],
            self._3: [IntVal(0), IntVal(1), IntVal(2), IntVal(3), IntVal(4), IntVal(5), IntVal(6), IntVal(7), IntVal(8), IntVal(9), IntVal(10)]
        }
        self.solver = Solver()
        self.counter_examples = []
        self.counter = 0

    def isImpValid(self, imp):
        self.solver.push()
        self.solver.add(Not(imp))
        result = self.solver.check()
        ret = True if result == unsat else self.solver.model()
        self.solver.pop()
        return ret

    def checkEta(self, eta):
        # req 1
        result = self.isImpValid(Implies(And(self.j == IntVal(9), self.i == IntVal(0)), eta))
        if result != True:
            self.counter_examples.append((result[self.i], result[self.j]))
            return False
        # req 2
        result = self.isImpValid(Implies(And(eta, Not(self.i < IntVal(10))), self.j <= IntVal(-1)))
        if result != True:
            return False
        # req 3
        result = self.isImpValid(Implies(And(self.i < IntVal(10), eta), substitute(substitute(eta, (self.j, self.j-IntVal(1))), (self.i, self.i+IntVal(1)))))
        if result != True:
            return False
        return True

    def getConstituents(self, exp):
        for c in exp.children():
            if c.children():
                yield from self.getConstituents(c)
            else:
                yield c

    def genesis(self, exp):
        # recursion base
        # if expression has children and they're all termini or
        # if expression has no child and is a terminus
        if (exp.children() and not any(c in self.prod for c in list(self.getConstituents(exp))) or
            not exp.children() and exp not in self.prod):
            # pruning
            if any(ci == 0 and cj == 9 and not simplify(substitute(exp, (self.i, ci), (self.j, cj))) for (ci, cj) in self.counter_examples):
                return False
            self.counter+=1
            if self.checkEta(exp):
                return exp
            else:
                return False
        # expression expansion
        components = list(self.getConstituents(exp))
        # single term
        if not components:
            for p in self.prod[exp]:
                ret = self.genesis(p)
                # eta is found
                if type(ret) == BoolRef:
                    return ret
        # multiple terms
        else:
            for c in [c for c in components if c in self.prod]:
                for p in self.prod[c]:
                    ret = self.genesis(substitute(exp, (c, p)))
                    # eta is found
                    if type(ret) == BoolRef:
                        return ret
        return False

z3 = Z3()
t = time()
print(z3.genesis(Bool('S')))
print("time:", time()-t)
print("z3 queried:", z3.counter)
