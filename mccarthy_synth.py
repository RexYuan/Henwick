from z3 import *
from time import time

class Z3:
    def __init__(self):
        self.n = Int('n')
        self.c = Int('c')
        self.ret = Int('ret')

        self.S = Bool('S')
        self._Simple = Bool('Simple')
        self._Hard = Bool('Hard')

        self._Cst1 = Int('Cst1')
        self._Cst2 = Int('Cst2')
        self._Cst3 = Int('Cst3')

        self._Var1 = Int('Var1')
        self._Var2 = Int('Var2')
        self._Var3 = Int('Var3')
        self._Var4 = Int('Var4')
        self._Var5 = Int('Var5')
        self._Var6 = Int('Var6')
        self._Var7 = Int('Var7')

        self.prod = {
            self.S:  [And(self._Simple, self._Hard)],

            #              Implies (self.n > IntVal(100), And (self.c >= IntVal(0), self.n > IntVal(100), self.ret == self.n - IntVal(10) + IntVal(10) * self.c))
            self._Simple: [Implies (self.n > IntVal(100), And (self._Var1 >= IntVal(0), self._Var2 > IntVal(100), self._Var3 == self.n - IntVal(10) + IntVal(10) * self.c))],
            #            Implies (self.n <= IntVal(100), And (Implies (self.ret >=  IntVal(90), And (IntVal(91) - self.c <= self.ret, self.ret <= IntVal(91) + IntVal(10) * self.c)), Implies (self.ret <   IntVal(90), self.c > 0)))
            self._Hard: [Implies (self._Var4 <= IntVal(100), And (Implies (self.ret >=  IntVal(90), And (IntVal(91) - self.c <= self.ret, self.ret <= IntVal(91) + IntVal(10) * self.c)), Implies (self.ret <   IntVal(90), self.c > 0)))],

            self._Cst1: [IntVal(100), IntVal(0), IntVal(10), IntVal(90), IntVal(91)],
            self._Cst2: [IntVal(100), IntVal(0), IntVal(10), IntVal(90), IntVal(91)],
            self._Cst3: [IntVal(100), IntVal(0), IntVal(10), IntVal(90), IntVal(91)],

            self._Var1: [self.n, self.c, self.ret],
            self._Var2: [self.n, self.c, self.ret],
            self._Var3: [self.n, self.c, self.ret],
            self._Var4: [self.n, self.c, self.ret],
            self._Var5: [self.n, self.c, self.ret],
            self._Var6: [self.n, self.c, self.ret],
            self._Var7: [self.n, self.c, self.ret]
        }
        self.solver = Solver()
        self.counter_examples1 = []
        self.counter_examples2 = []
        self.counter = 0
        self.p1counter = 0
        self.p2counter = 0
        self.hcounter = 0
        self.history = []

    def isImpValid(self, imp):
        self.solver.push()
        self.solver.add(Not(imp))
        result = self.solver.check()
        ret = True if result == unsat else self.solver.model()
        self.solver.pop()
        return ret

    def checkEta(self, eta):
        result = self.isImpValid(Implies(And(self.ret == self.n, self.c == 1), eta))
        if result != True:
            self.counter_examples1.append((result[self.ret], result[self.n], result[self.c]))
            return False
        result = self.isImpValid(Implies(And(eta, self.c <= 0), And(Implies((self.n <= 100), (self.ret == 91)), Implies((self.n > 100), (self.ret == self.n - 10)))))
        if result != True:
            self.counter_examples2.append((result[self.ret], result[self.n], result[self.c]))
            return False
        result = self.isImpValid(Implies(And(self.c > 0, eta), And(Implies(self.ret > 100, substitute(substitute(eta, (self.c, self.c-1)), (self.ret, self.ret-10))), Implies(self.ret <= 100, substitute(substitute(eta, (self.c, self.c+1)), (self.ret, self.ret+11))))))
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
        components = list(self.getConstituents(exp))
        if components in self.history:
            self.hcounter+=1
            return False
        self.history.append(components)
        # recursion base
        # if expression has children and they're all termini or
        # if expression has no child and is a terminus
        #print(components)
        if (exp.children() and not any(c in self.prod for c in components) or
            not exp.children() and exp not in self.prod):
            # pruning
            if any(simplify(cret == cn) and simplify(cc == IntVal(1)) and not simplify(substitute(exp, (self.ret, cret), (self.n, cn), (self.c, cc))) for (cret, cn, cc) in self.counter_examples1):
                self.p1counter+=1
                return False
            if any((simplify(substitute(exp, (self.ret, cret), (self.n, cn), (self.c, cc))) and simplify(cc <= IntVal(0))) and (not ((not simplify(cn <= IntVal(100)) or simplify(cret == IntVal(91))) and (simplify(cn <= IntVal(100)) or simplify(cret == IntVal(-10) + cn)))) for (cret, cn, cc) in self.counter_examples2):
                self.p2counter+=1
                return False
            self.counter+=1
            if self.checkEta(exp):
                return exp
            else:
                return False
        # expression expansion
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

    def test(self):
        print(self.checkEta(And (Implies (self.n > 100, And (self.c >= 0, self.n > 100, self.ret == self.n - 10 + 10 * self.c)), Implies (self.n <= 100, And (Implies (self.ret >=  90, And (91 - self.c <= self.ret, self.ret <= 91 + 10 * self.c)), Implies (self.ret <   90, self.c > 0))))))
        return

z3 = Z3()
t = time()
print(z3.genesis(Bool('S')))
print("time:", time()-t)
print("z3 queried:", z3.counter)
print("req1 pruned:", z3.p1counter)
print("req2 pruned:", z3.p2counter)
print("h pruned:", z3.hcounter)
#z3.test()
