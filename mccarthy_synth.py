"""
eta = And (Implies (n > 100, And (c >= 0, n > 100,
                                  ret == n - 10 + 10 * c)),
           Implies (n <= 100,
                    And (Implies (ret >=  90,
                                  And (91 - c <= ret,
                                       ret <= 91 + 10 * c)),
                         Implies (ret <   90, c > 0))))
"""
from z3 import *
from time import time

class Z3:
    def __init__(self):
        NT = DeclareSort('Nonterminal')
        self._S     = Bool('S')
        self._Bool  = Bool('Bool')
        self._Int   = Int('Int')
        self._Term  = Int('Term')
        self._Cst   = Int('Cst')
        self._Var   = Int('Var')
        self.n      = Int('n')
        self.c      = Int('c')
        self.ret      = Int('ret')

        self.prod = {
            self._S:    [self._Bool],
            self._Bool: [self._Int > self._Int,
                         self._Int >= self._Int,
                         self._Int == self._Int,
                         And(self._Bool, self._Bool),
                         Or(self._Bool, self._Bool),
                         Or(Not(self._Bool), self._Bool)],
            self._Int:  [self._Term,
                         self._Term * self._Term,
                         self._Term + self._Term],
            self._Term: [self._Cst,
                         self._Var],
            self._Cst:  [IntVal(100),
                         IntVal(0),
                         IntVal(10),
                         IntVal(90),
                         IntVal(91)],
            self._Var:  [self.n,
                         self.c,
                         self.ret]
        }
        self.solver = Solver()
        self.counter_examples1 = []
        self.counter_examples2 = []
        self.counter_examples3 = []
        self.history = []
        self.query_counter = 0
        self.pruneh_counter = 0
        self.prune1_counter = 0
        self.prune2_counter = 0
        self.prune3_counter = 0

    def isImpValid(self, imp):
        self.solver.push()
        self.solver.add(Not(imp))
        result = self.solver.check()
        ret = True if result == unsat else self.solver.model()
        self.solver.pop()
        return ret

    def checkEta(self, eta):
        # (ret == n and c == 1) => ETA
        result = self.isImpValid(Implies(And(self.ret == self.n, self.c == 1), eta))
        if result != True:
            self.counter_examples1.append((result[self.ret], result[self.n], result[self.c]))
            return False
        # (ETA and c <= 0) => (((n <= 100) => (ret == 91)) and
        #                     ((n > 100) => (ret == n - 10)))
        result = self.isImpValid(Implies(And(eta, self.c <= 0),
                                         And(Implies((self.n <= 100),
                                                     (self.ret == 91)),
                                             Implies((self.n > 100),
                                                     (self.ret == self.n - 10)))))
        if result != True:
            self.counter_examples2.append((result[self.ret], result[self.n], result[self.c]))
            return False
        # (c > 0 and ETA) => ((ret > 100) => ETA[c-1 / c][ret-10 / ret]) and
        #                    ((ret <= 100) => ETA[c+1 / c][ret+11 / ret])
        result = self.isImpValid(Implies(And(self.c > 0, eta),
                                         And(Implies(self.ret > 100,
                                                     substitute(eta, (self.c, self.c-1), (self.ret, self.ret-10))),
                                             Implies(self.ret <= 100,
                                                     substitute(eta, (self.c, self.c+1), (self.ret, self.ret+11))))))
        if result != True:
            return False
        return True

    def pruned(self, exp):
        pass

    def getConstituents(self, exp):
        for c in exp.children():
            if c.children():
                yield from self.getConstituents(c)
            else:
                yield c

    def genesis(self, exp, limit):
        print(exp)
        offsprings = list(self.getConstituents(exp))
        children = exp.children()
        # depth limited search
        if (len(offsprings) > limit or
           (len(offsprings) == limit and any(c == self._Bool for c in offsprings)) or
           sum(2 if c == self._Bool else 1 for c in offsprings) > limit):
            return False
        # recursion base
        # if expression has children and they're all termini or
        # if expression has no child and is a terminus
        if (children and not any(c in self.prod for c in offsprings) or
            not children and exp not in self.prod):
            # pruning
            #if self.pruned(exp):
            #    return False
            # query SMT solver
            self.query_counter+=1
            if self.checkEta(exp):
                return exp
            else:
                return False
        # expression expansion
        # single term
        if not offsprings:
            for p in self.prod[exp]:
                ret = self.genesis(p, limit)
                # eta is found
                if type(ret) == BoolRef:
                    return ret
        # multiple terms
        else:
            for i, c in enumerate([c for c in offsprings]):
                if c in self.prod:
                    for p in self.prod[c]:
                        ret = self.genesis(self.sub(exp, c, p, i), limit)
                        # eta is found
                        if type(ret) == BoolRef:
                            return ret
                    return False
        return False

    def synthesis(self, limit):
        # iterative deepening search
        for l in range(2, limit+1):
            result = self.genesis(self._S, l)
            # eta is found
            if type(result) == BoolRef:
                return result

    def test(self):
        eta = And (Implies (self.n > 100, And (self.c >= 0, self.n > 100,
                                          self.ret == self.n - 10 + 10 * self.c)),
                   Implies (self.n <= 100,
                            And (Implies (self.ret >=  90,
                                          And (91 - self.c <= self.ret,
                                               self.ret <= 91 + 10 * self.c)),
                                 Implies (self.ret <   90, self.c > 0))))
        print(self.checkEta(eta))
        print(self.sub(Not(Bool('x')), Bool('x'), Bool('y')))
        print(self.sub(Not(And(Bool('x'), Bool('x'))), Bool('x'), Bool('y'), 1))

    def report(self):
        # stats
        print("z3 queried:", z3.query_counter, "\n")
        print("history size:", len(self.history))
        print("history pruned:", z3.pruneh_counter, "\n")
        print("ce 1 size:", len(self.counter_examples1))
        print("req 1 pruned:", z3.prune1_counter, "\n")
        print("ce 2 size:", len(self.counter_examples2))
        print("req 2 pruned:", z3.prune2_counter, "\n")
        print("ce 3 size:", len(self.counter_examples3))
        print("req 3 pruned:", z3.prune3_counter, "\n")
        return

    def subv(self, exp, oldv, newv, order):
        parts = exp.children()
        if is_const(exp):
            if exp == oldv and not self.done and self.subc == order:
                self.done = True
                return newv
            else:
                self.subc += 1
                return exp
        elif is_and(exp):
            return And([self.subv(parts[i], oldv, newv, order) for i in range(len(parts))])
        elif is_or(exp):
            return Or([self.subv(parts[i], oldv, newv, order) for i in range(len(parts))])
        elif is_not(exp):
            return Not(self.subv(parts[0], oldv, newv, order))
        elif is_add(exp):
            return self.subv(parts[0], oldv, newv, order) + self.subv(parts[1], oldv, newv, order)
        elif is_sub(exp):
            return self.subv(parts[0], oldv, newv, order) - self.subv(parts[1], oldv, newv, order)
        elif is_mul(exp):
            return self.subv(parts[0], oldv, newv, order) * self.subv(parts[1], oldv, newv, order)
        elif is_le(exp):
            return self.subv(parts[0], oldv, newv, order) <= self.subv(parts[1], oldv, newv, order)
        elif is_lt(exp):
            return self.subv(parts[0], oldv, newv, order) < self.subv(parts[1], oldv, newv, order)
        elif is_ge(exp):
            return self.subv(parts[0], oldv, newv, order) >= self.subv(parts[1], oldv, newv, order)
        elif is_gt(exp):
            return self.subv(parts[0], oldv, newv, order) > self.subv(parts[1], oldv, newv, order)
        elif is_eq(exp):
            return self.subv(parts[0], oldv, newv, order) == self.subv(parts[1], oldv, newv, order)
        else:
            raise Exception("uncaught sub", exp, oldv, newv, order)

    def sub(self, exp, oldv, newv, order=0):
        self.done = False
        self.subc = 0
        return self.subv(exp, oldv, newv, order)

z3 = Z3()

#z3.test()

t = time()
synthed = z3.synthesis(26)
print("==========================")
print("exp =", synthed)
z3.report()
print("time:", time()-t)
print("==========================")
