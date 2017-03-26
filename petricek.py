# TODO: either think of a way to modify substitute or dynamically generate variables

"""
Synthesize a loop invariant expression for Tomas Petricek's
example program retrieved from http://stackoverflow.com/a/3221583/2448540
"""

# Program:
# j = 9;
# i = 0;
# while (i < 10)
# {
#     i = i + 1;
#     j = j - 1;
# }

# Goal:
# Given program pre-condition = (| T |)
# and post-condition = (| i = 10 and j = -1 |),
# Find invariant = (| i + j == 9 and i < 11 |).

# Proof:
# (| T |)
# (| eta[j/9][i/0] |) Implied
#   i = 0;
# (| eta[j/9] |) Assignment
#   j = 9;
# (| eta |) Assignment
#   while (i < 10)
#   {
#     (| eta and i < 10|)
#     (| eta[j/j-1][i/i+1] |) Implied
#       i = i + 1;
#     (| eta[j/j-1] |) Assignment
#       j = j - 1;
#     (| eta |) Assignment
#   }
# (| eta and not i < 10 |) While
# (| i = 10 and j = -1 |) Implied

# Requirements:
# Given an eta,
# prove the validity of these three implications:
# 1) T => eta[j/9][i/0]
# 2) eta and not i < 10 => i = 10 and j = -1
# 3) i < 10 and eta => eta[j-1/j][i+1/i]

# Strategy:
# 1) Prune with logical requirements for invariant.
# Given an expression E for eta, for any failure in checking some requirements R,
# SMT solver Z3 would return a particular model M (valuation), that makes R, with
# eta substituted with E, evaluate to false, when the variables in eta are
# substituted with the corresponding concrete values in M.
# Thus, we can examine the form of R and devise pruning strategies from the fact
# that M resolves much of R but the part of eta, where it can only be checked
# after substituting with some expression E. So, with the knowledge of the form
# of R and how everything but eta in R evaluates to under M, we need only to check
# what E evaluates to under M to determine if R holds or not.
# For requirement 1), T => eta[j/9][i/0], since eta is in the concequent slot of
# an implication, and under any valuation T evaluates to True, if eta[j/9][i/0]
# evaluates to False under M, this should be pruned.
# For requirement 2), eta and not i < 10 => i = 10 and j = -1, if we know from Z3
# that, for an expression E1 and model M, this requirement is False, we know that
# , under M, E1 and not i < 10 evaluates to True and i = 10 and j = -1 to False.
# So, for an expression E2, we need only to check whether E2 evaluates to True
# under M to decide if this should be pruned, and thus saving time asking Z3.
# For i < 10 and eta => eta[j-1/j][i+1/i], if i < 10 and E1 => E1[j-1/j][i+1/i]
# evaluates to False under M, E1 must evaluates to True and E1[j-1/j][i+1/i] to
# False, respectively, under M. So, we only need to check if E2 is True and
# E2[j-1/j][i+1/i] is False to prune it off.
# 2) NOTE: how to Prune with semantic requirements.
# simplify to true or false
# 3) NOTE: Prune with history or semantic equivalence like commutativity
# 4) NOTE: invariant insight
# 5) NOTE: depth limited on offsprings count

# grammar:
# S    ::= Bool
# Bool ::= And(Bool, Bool) | Or(Bool, Bool) | Implies(Bool, Bool) |
#          Int > Int | Int >= Int | Int == Int
# Int  ::= Term | Term + Term | Term - Term
# Term ::= Cst | Var
# Cst  ::= 9 | 11
# Var  ::= i | j

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
        self.i      = Int('i')
        self.j      = Int('j')

        self.prod = {
            self._S:    [self._Bool],
            self._Bool: [Or(self._Bool, self._Bool),
                         self._Int > self._Int,
                         self._Int >= self._Int,
                         self._Int == self._Int,
                         And(self._Bool, self._Bool)],
            self._Int:  [self._Term,
                         self._Term - self._Term,
                         self._Term + self._Term],
            self._Term: [self._Cst,
                         self._Var],
            self._Cst:  [IntVal(11),
                         IntVal(9)],
            self._Var:  [self.i,
                         self.j]
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
        # req 1) T => eta[j/9][i/0]
        result = self.isImpValid(Implies(True, substitute(eta, (self.j, IntVal(9)), (self.i, IntVal(0)))))
        if result != True:
            if result[self.i] != None and result[self.j] != None:
                self.counter_examples1.append((result[self.i], result[self.j]))
            return False
        # req 2) eta and not i < 10 => i = 10 and j = -1
        result = self.isImpValid(Implies(And(eta, Not(self.i < IntVal(10))), And(self.i == IntVal(10), self.j == IntVal(-1))))
        if result != True:
            if result[self.i] != None and result[self.j] != None:
                self.counter_examples2.append((result[self.i], result[self.j]))
            return False
        # req 3) i < 10 and eta => eta[j-1/j][i+1/i]
        result = self.isImpValid(Implies(And(self.i < IntVal(10), eta), substitute(eta, (self.j, self.j-IntVal(1)), (self.i, self.i+IntVal(1)))))
        if result != True:
            if result[self.i] != None and result[self.j] != None:
                self.counter_examples3.append((result[self.i], result[self.j]))
            return False
        return True

    def pruned(self, exp):
        # NOTE strat 2)
        """if simplify(exp) == True or simplify(exp) == False:
            return True
        if simplify(exp) in self.history:
            return True
        self.history.append(simplify(exp))
        """
        # pruning with counter examples
        # T => eta[j/9][i/0]
        #if any(simplify(substitute(substitute(exp, (self.j, IntVal(9)), (self.i, IntVal(0))),
        #       (self.i, ci), (self.j, cj))) == False
        #       for (ci, cj) in self.counter_examples1):"""
        if simplify(substitute(exp, (self.j, IntVal(9)), (self.i, IntVal(0)))) == False:
            self.prune1_counter += 1
            return True
        # eta and not i < 10 => i = 10 and j = -1
        if any(simplify(substitute(exp, (self.i, ci), (self.j, cj))) == True
               for (ci, cj) in self.counter_examples2):
            self.prune2_counter += 1
            return True
        # i < 10 and eta => eta[j-1/j][i+1/i]
        #if any(simplify(substitute(exp, (self.i, ci), (self.j, cj))) == True
        #       and simplify(substitute(substitute(exp, (self.j, self.j-IntVal(1)), (self.i, self.i+IntVal(1))),
        #       (self.i, ci), (self.j, cj))) for (ci, cj) in self.counter_examples3):
        if any(simplify(substitute(exp, (self.i, ci), (self.j, cj))) == True
               and simplify(substitute(exp, (self.j, cj-IntVal(1)),
                                            (self.i, ci+IntVal(1)))) == False
               for (ci, cj) in self.counter_examples3):
            self.prune3_counter += 1
            return True

    def getConstituents(self, exp):
        for c in exp.children():
            if c.children():
                yield from self.getConstituents(c)
            else:
                yield c

    def genesis(self, exp, limit):
        print(exp)
        #if simplify(exp) == True or simplify(exp) == False:
        #    print("WW")
        #    return False
        """if simplify(exp) in self.history:
            return False
        self.history.append(simplify(exp))
        """
        offsprings = list(self.getConstituents(exp))
        children = exp.children()
        # depth limited search
        if (len(offsprings) > limit or
           (len(offsprings) == limit and any(c == self._Bool for c in offsprings)) or
           sum(2 if c == self._Bool else 1 for c in offsprings) > limit):
            #print("p")
            return False
        # recursion base
        # if expression has children and they're all termini or
        # if expression has no child and is a terminus
        if (children and not any(c in self.prod for c in offsprings) or
            not children and exp not in self.prod):
            #print("H")
            # pruning
            if self.pruned(exp):
                return False
            # query SMT solver
            self.query_counter+=1
            if self.checkEta(exp):
                return exp
            else:
                return False
        # expression expansion
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
            for i, c in enumerate([c for c in offsprings]):
                if c in self.prod:
                    #print(self.prod[c])
                    for p in self.prod[c]:
                        #print(exp, c, p, i)
                        ret = self.genesis(self.sub(exp, c, p, i), limit)
                        # eta is found
                        if type(ret) == BoolRef:
                            return ret
                    return False
        return False

    def synthesis(self, limit):
        # iterative deepening search
        for l in range(5, limit+1):
            result = self.genesis(self._S, l)
            #print("==========================")
            #print("level",l)
            #self.report()
            #print("==========================")
            # eta is found
            if type(result) == BoolRef:
                return result

    def test(self):
        #print(self.checkEta(self.i+self.j==IntVal(9)))
        #print(self.checkEta(And(self.i+self.j==IntVal(9), self.i < IntVal(11))))

        self.w,self.x,self.y,self.z,self.m = Bools('w x y z m')
        #self.a,self.b,self.c,self.d,self.n = Ints('a b c d n')

        # From And(w, Or(x, b<d, a-b<=c, x, x), a+b==c-a, x)
        # To   And(w, Or(x, b<d, n-b<=c, x, x), a+b==c-a, x)
        #print(And(self.x, self.x))
        #print(self.sub(And(self.x, self.x), self.x, self.y))
        print(self.sub(And(self.x, self.y, self.x, self.x), self.x, self.y, 1))
        #print(And(self.w, Or(self.x, self.b<self.d, self.a-self.b<=self.c, self.x, self.x), self.a+self.b==self.c-self.a, self.x))
        #print(self.sub(And(self.w, Or(self.x, self.b<self.d, self.a-self.b<=self.c, self.x, self.x), self.a+self.b==self.c-self.a, self.x), self.a, self.n))
        # From And(w, Or(x, b<d, a-b<=c, x, x), a+b==c-a, x)
        # To   And(w, Or(m, b<d, a-b<=c, x, x), a+b==c-a, x)
        #print(And(w, Or(x, b<d, a-b<=c, x, x), a+b==c-a, x))
        #print(self.sub(And(w, Or(x, b<d, a-b<=c, x, x), a+b==c-a, x), x, m))
        return

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
        elif is_add(exp):
            return self.subv(parts[0], oldv, newv, order) + self.subv(parts[1], oldv, newv, order)
        elif is_sub(exp):
            return self.subv(parts[0], oldv, newv, order) - self.subv(parts[1], oldv, newv, order)
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

    def sub(self, exp, oldv, newv, order=1):
        self.done = False
        self.subc = 0
        return self.subv(exp, oldv, newv, order)

z3 = Z3()
t = time()
synthed = z3.synthesis(5)
print("==========================")
print("exp =", synthed)
z3.report()
print("time:", time()-t)
print("==========================")

#z3.test()
