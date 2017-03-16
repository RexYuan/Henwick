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
# 1) i + j == 9 => eta
# 2) eta and not i < 10 => i + j == 9 NOTE: is post i = 10 and j = -1? how? try prove
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
        """
        self.S = Bool('S')
        self.i = Int('i')
        self.j = Int('j')
        self._1 = Int('_1')
        self._2 = Int('_2')
        self._3 = Int('_3')
        self._4 = Int('_4')
        self.prod = {
            #self.S:  [self._1 - self._2 == self._3, self._1 * self._2 == self._3, self._1 + self._2 == self._3],
            #self.S:  [self._1 + self._2 == self._3, self._1 - self._2 == self._3, self._1 * self._2 == self._3],
            #self.S:  [self._1 - self._2 == self._3, self._1 + self._2 == self._3, self._1 * self._2 == self._3],
            self.S:  [self._1 == self._2, self._1 >= self._2],
            #self._1: [self.i, self.j],
            #self._2: [self.i, self.j],
            #self._3: [IntVal(0), IntVal(1), IntVal(2), IntVal(3), IntVal(4), IntVal(5), IntVal(6), IntVal(7), IntVal(8), IntVal(9), IntVal(10)]
            self._1: [self._3 + self._4, self._3 - self._4, self._3],
            self._2: [self._3 + self._4, self._3 - self._4, self._3],
            self._3: [self.i, self.j, IntVal(7), IntVal(8), IntVal(9), IntVal(0), IntVal(1), IntVal(2), IntVal(3), IntVal(4), IntVal(5), IntVal(6), IntVal(10)],
            self._4: [self.i, self.j, IntVal(7), IntVal(8), IntVal(9), IntVal(0), IntVal(1), IntVal(2), IntVal(3), IntVal(4), IntVal(5), IntVal(6), IntVal(10)]
        """
        self._S = Bool('S')
        self._Bool1 = Bool('Bool1')
        self._Bool2 = Bool('Bool2')
        self._Int1 = Int('Int1')
        self._Int2 = Int('Int2')
        self._Term1 = Int('Term1')
        self._Term2 = Int('Term2')
        self._Term3 = Int('Term3')

        self.i = Int('i')
        self.j = Int('j')

        self.prod = {
            self._S: [self._Bool1],
            self._Bool1: [self._Int1 > self._Int2, self._Int1 >= self._Int2,
                         And(self._Bool1, self._Bool2), self._Int1 == self._Int2, Or(self._Bool1, self._Bool2), Implies(self._Bool1, self._Bool2)],
            self._Bool2: [self._Int1 > self._Int2, self._Int1 >= self._Int2,
                         And(self._Bool1, self._Bool2), self._Int1 == self._Int2, Or(self._Bool1, self._Bool2), Implies(self._Bool1, self._Bool2)],
            self._Int1: [self._Term3, self._Term1 + self._Term2, self._Term1 - self._Term2],
            self._Int2: [self._Term3, self._Term1 + self._Term2, self._Term1 - self._Term2],

            self._Term1: [IntVal(7), IntVal(9), self.i, self.j],
            self._Term2: [IntVal(10), IntVal(9), self.i, self.j],
            self._Term3: [IntVal(1), IntVal(9), self.i, self.j]
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
        # req 1
        result = self.isImpValid(Implies(self.i + self.j == IntVal(9), eta))
        if result != True:
            if result[self.i] != None and result[self.j] != None:
                self.counter_examples1.append((result[self.i], result[self.j]))
            return False
        # req 2
        result = self.isImpValid(Implies(And(eta, Not(self.i < IntVal(10))), self.i + self.j == IntVal(9)))
        if result != True:
            if result[self.i] != None and result[self.j] != None:
                self.counter_examples2.append((result[self.i], result[self.j]))
            return False
        # req 3
        result = self.isImpValid(Implies(And(self.i < IntVal(10), eta), substitute(eta, (self.j, self.j-IntVal(1)), (self.i, self.i+IntVal(1)))))
        if result != True:
            if result[self.i] != None and result[self.j] != None:
                self.counter_examples3.append((result[self.i], result[self.j]))
            return False
        return True

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
        # NOTE: should depth be non-function term count or be symbol count?
        # how to get symbol(term&function) count? ast?
        if len(offsprings) > limit:
            return False

        """
        # NOTE: this doesn't work. Must rethink how to prune with history
        # NOTE: how to prune off straight up boolean val?
        # pruning with historic redundancy

        if children and type(simplify(exp)) == BoolRef:
            print(children)
            return False
        if children and type(simplify(exp)) != BoolRef and simplify(exp) in self.history:
            #print(self.history)
            self.pruneh_counter += 1
            return False
        self.history.append(simplify(exp))
        """

        # recursion base
        # if expression has children and they're all termini or
        # if expression has no child and is a terminus
        if (children and not any(c in self.prod for c in offsprings) or
            not children and exp not in self.prod):
            # NOTE: how to prune with more insight such as only when there's variable?
            """
            if all(c not in [self.i, self.j] for c in offsprings):
                return False
            """
            # pruning with counter examples
            # NOTE: i dont think this is correct way to prune. must rethink the three req
            if any(simplify(And(ci + cj == IntVal(9), Not(substitute(exp, (self.i, ci), (self.j, cj))))) for (ci, cj) in self.counter_examples1):
                self.prune1_counter += 1
                return False
            if any(simplify(And(substitute(exp, (self.i, ci), (self.j, cj)), Not(ci < IntVal(10)), Not(ci + cj == IntVal(9)))) for (ci, cj) in self.counter_examples2):
                self.prune2_counter += 1
                return False
            if any(simplify(And(ci < IntVal(10), substitute(exp, (self.i, ci), (self.j, cj)), Not(substitute(substitute(exp, (self.j, self.j-IntVal(1)), (self.i, self.i+IntVal(1))), (self.i, ci), (self.j, cj))))) for (ci, cj) in self.counter_examples3):
                self.prune3_counter += 1
                return False
            self.query_counter+=1
            if self.checkEta(exp):
                return exp
            else:
                return False
        # expression expansion
        # NOTE: there must be something else i can do here
        # NOTE: search strat? how to find insight for goal from other things?
        #       such as post like said from textbook? or anyway get some general
        #       progenitive direction from context? like changning grammar on the fly
        #       or pruning off symmetric function application such as "And, Or"
        #       when args are semantically equivalent in the sense that their
        #       production rules are the same?
        #       I should go back and read more about classic AI search for insight
        # single term
        if not offsprings:
            for p in self.prod[exp]:
                ret = self.genesis(p, limit)
                # eta is found
                if type(ret) == BoolRef:
                    return ret
        # multiple terms
        else:
            for c in [c for c in offsprings if c in self.prod]:
                for p in self.prod[c]:
                    ret = self.genesis(substitute(exp, (c, p)), limit)
                    # eta is found
                    if type(ret) == BoolRef:
                        return ret
        return False

    def synthesis(self, limit):
        # iterative deepening search
        # NOTE: how to prune based on like it's impossible for 1 symbol?
        #       and for 2 with bool functions and for all constant args?
        for l in range(1, limit+1):
            self.query_counter = 0
            self.pruneh_counter = 0
            self.prune1_counter = 0
            self.prune2_counter = 0
            self.prune3_counter = 0

            result = self.genesis(self._S, l)
            if type(result) == BoolRef:
                return result

    def test(self):
        print(self.checkEta(self.i+self.j==IntVal(9)))
        return

    def report(self):
        print("z3 queried:", z3.query_counter)
        print("history pruned:", z3.pruneh_counter)
        print("req 1 pruned:", z3.prune1_counter)
        print("req 2 pruned:", z3.prune2_counter)
        print("req 3 pruned:", z3.prune3_counter)
        return

z3 = Z3()
t = time()
print(z3.synthesis(3))
z3.report()
print("time:", time()-t)

#z3.test()
