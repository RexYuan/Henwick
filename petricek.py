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
# Given program, program pre-condition = (| T |)
# and post-condition = (| i = 10 and j = -1 |),
# find the invariant = (| i + j == 9 and i < 11 |).

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
# Given some eta, check its correctness by try to
# prove the validity of these three implications:
# 1) T => eta[j/9][i/0]
# 2) eta and not i < 10 => i = 10 and j = -1
# 3) i < 10 and eta => eta[j-1/j][i+1/i]

# Strategies:
# - Prune with logical requirements for invariant.
#      Given an expression E for eta, for any failure in checking some requirements R,
#    SMT solver Z3 would return a particular model M (valuation), that makes R, with
#    eta substituted with E, evaluate to false, when the variables in eta are
#    substituted with the corresponding concrete values in M.
#      Thus, we can examine the form of R and devise pruning strategies from the fact
#    that M resolves much of R but the part of eta, where it can only be checked
#    after substituting with some expression E. So, with the knowledge of the form
#    of R and how everything but eta in R evaluates to under M, we need only to check
#    what E evaluates to under M to determine if R holds or not.
#      For requirement 1), T => eta[j/9][i/0], since eta is in the concequent slot of
#    an implication, and under any valuation T evaluates to True, if eta[j/9][i/0]
#    evaluates to False under M, this should be pruned.
#      For requirement 2), eta and not i < 10 => i = 10 and j = -1, if we know from Z3
#    that, for an expression E1 and model M, this requirement is False, we know that
#    , under M, E1 and not i < 10 evaluates to True and i = 10 and j = -1 to False.
#      So, for an expression E2, we need only to check whether E2 evaluates to True
#    under M to decide if this should be pruned, and thus saving time asking Z3.
#      For i < 10 and eta => eta[j-1/j][i+1/i], if i < 10 and E1 => E1[j-1/j][i+1/i]
#    evaluates to False under M, E1 must evaluates to True and E1[j-1/j][i+1/i] to
#    False, respectively, under M. So, we only need to check if E2 is True and
#    E2[j-1/j][i+1/i] is False to prune it off.
#
# - depth pruning prune just by saying if we're at limit of depth k
#    every terminus expression with depth 1~k-1 are to be pruned
#    bc if they are the target we wouldn't have made it to k
#    NOTE: can we prune by counting B*2+terminus and check will it exceed limit?
#
# - how to Prune with semantic requirements.
#    simplify to true or false => can be done by simplification
#    (no use bc False cant be invariant and true is always an invariant)
#    NOTE: more: prune with seen equivalent expression like knowing
#    (A and B) is the same as (B and A); or, further, if E1 and E2
#    are equivalent then, if (E1 and B) is False, we dont need to
#    check (E2 and B) and it's thus pruned
#
# - NOTE: how to prune with history for dynamic programming?
#
# - greedy expansion => keep expanding on first nonterminal bc they'll all be
#   the same further down the tree
#   regardless of AST, all fo the possible concrete trees
#   of the form of AST are completely determined by the terminus value
#
# - < and <= is redundant bc enumerate > and >= will also have the equivalent
#   for Not, since Not < is >= and Not <= is > all that is left is ==
#   we only need to add Not ==
#   since Implies is Or(Not B, B), and we got Not, it's also redundant
#
# - NOTE: invariant insight: invariant may be like (post and E) or (post or E)
#
# - depth limited on offsprings count

# grammar:
# S    ::= Bool
# Bool ::= And(Bool, Bool) | Or(Bool, Bool) |
#          Int > Int | Int >= Int |
#          Int == Int | Not(Int == Int)
# Int  ::= Term | Term + Term | Term - Term
# Term ::= Cst | Var
# Cst  ::= 9 | 11
# Var  ::= i | j

from z3 import *
from time import time

class Z3:
    def __init__(self):
        #NT = DeclareSort('Nonterminal')
        self._S     = Bool('S')
        self._Bool  = Bool('Bool')
        self._btBool  = Bool('btBool')
        self._beBool  = Bool('beBool')
        self._eqBool  = Bool('eqBool')
        self._neBool  = Bool('neBool')
        self._Int   = Int('Int')
        self._Term  = Int('Term')
        self._Cst   = Int('Cst')
        self._Var   = Int('Var')
        self.i      = Int('i')
        self.j      = Int('j')

        self.prod = {
            self._S:    [self._Bool],
            #self._Bool: [And(self._Bool, self._Bool),
            #             Or(self._Bool, self._Bool),
            #             self._Int > self._Int,
            #             self._Int >= self._Int,
            #             self._Int == self._Int,
            #             Not(self._Int == self._Int)],
            #self._Int:  [self._Term,
            #             self._Term + self._Term,
            #             self._Term - self._Term],
            self._Bool: [And(self._Int > self._Int, self._btBool),
                         And(self._Int >= self._Int, self._beBool),
                         And(self._Int == self._Int, self._eqBool),
                         And(Not(self._Int == self._Int), self._neBool),
                         Or(self._Int > self._Int, self._btBool),
                         Or(self._Int >= self._Int, self._beBool),
                         Or(self._Int == self._Int, self._eqBool),
                         Or(Not(self._Int == self._Int), self._neBool),
                         self._Int > self._Int,
                         self._Int >= self._Int,
                         self._Int == self._Int,
                         Not(self._Int == self._Int)],
            self._btBool: [self._Int >= self._Int,
                           self._Int == self._Int,
                           Not(self._Int == self._Int)],
            self._beBool: [self._Int > self._Int,
                           self._Int == self._Int,
                           Not(self._Int == self._Int)],
            self._eqBool: [self._Int > self._Int,
                           self._Int >= self._Int,
                           Not(self._Int == self._Int)],
            self._neBool: [self._Int > self._Int,
                           self._Int >= self._Int,
                           self._Int == self._Int],
            self._Int:  [IntVal(9),
                         IntVal(11),
                         self.i,
                         self.j,
                         IntVal(9) + IntVal(9),
                         IntVal(9) + IntVal(11),
                         IntVal(9) + self.i,
                         IntVal(9) + self.j,
                         IntVal(11) + IntVal(11),
                         IntVal(11) + self.i,
                         IntVal(11) + self.j,
                         self.i + self.i,
                         self.i + self.j,
                         self.j + self.j,
                         IntVal(9) - IntVal(9),
                         IntVal(9) - IntVal(11),
                         IntVal(9) - self.i,
                         IntVal(9) - self.j,
                         IntVal(11) - IntVal(11),
                         IntVal(11) - self.i,
                         IntVal(11) - self.j,
                         self.i - self.i,
                         self.i - self.j,
                         self.j - self.j],
            self._Term: [self._Cst,
                         self._Var],
            self._Cst:  [IntVal(9),
                         IntVal(11)],
            self._Var:  [self.i,
                         self.j]
        }

        self.solver = Solver()

        self.counter_examples1 = []
        self.counter_examples2 = []
        self.counter_examples3 = []
        self.history = []

        self.query_counter = 0
        self.pruned_counter = 0
        self.prunes_counter = 0
        self.pruneh_counter = 0
        self.prune1_counter = 0
        self.prune2_counter = 0
        self.prune3_counter = 0

    def isImpValid(self, imp):
        """check the validity of imp"""
        self.solver.push()
        self.solver.add(Not(imp))
        result = self.solver.check()
        ret = True if result == unsat else self.solver.model()
        self.solver.pop()
        return ret

    def checkEta(self, eta):
        """check eta against requirements"""
        self.query_counter+=1
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

    def pruned(self, exp, depth, limit):
        """check if exp is pruned"""
        # depth pruning
        if depth < limit:
            self.pruned_counter += 1
            return True

        # semantic pruning:
        if simplify(exp) == True or simplify(exp) == False:
            self.prunes_counter += 1
            return True

        # historic pruning
        #if simplify(exp) in self.history:
        #    self.pruneh_counter += 1
        #    return True
        #self.history.append(simplify(exp))

        # counter example pruning
        # T => eta[j/9][i/0]
        if simplify(substitute(exp, (self.j, IntVal(9)), (self.i, IntVal(0)))) == False:
            self.prune1_counter += 1
            return True
        # eta and not i < 10 => i = 10 and j = -1
        if any(simplify(substitute(exp, (self.i, ci), (self.j, cj))) == True
               for (ci, cj) in self.counter_examples2):
            self.prune2_counter += 1
            return True
        # i < 10 and eta => eta[j-1/j][i+1/i]
        if any(simplify(substitute(exp, (self.i, ci), (self.j, cj))) == True
               and simplify(substitute(exp, (self.j, cj-IntVal(1)),
                                            (self.i, ci+IntVal(1)))) == False
               for (ci, cj) in self.counter_examples3):
            self.prune3_counter += 1
            return True

    def getConstituents(self, exp):
        """
        Generator for single terms(offsprings) in exp, ordered by DFS

        >> x, y = Bools('x y')
        >> a, b = Ints('a b')
        >> list(getConstituents(And(a > b, Or(x, Implies(a <= b, y)))))
        >> [a, b, x, a, b, y]
        """
        for c in exp.children():
            if c.children():
                yield from self.getConstituents(c)
            else:
                yield c

    def genesis(self, exp, limit):
        """DLS on offspring count bounded by limit"""
        offsprings = list(self.getConstituents(exp))
        children = exp.children()
        # depth limited search
        if (len(offsprings) > limit or
           (len(offsprings) == limit and any(c == self._Bool for c in offsprings)) or
           sum(2 if c == self._Bool else 1 for c in offsprings) > limit):
            return False
        print(exp)
        # recursion base: if expression has children and they're all termini or
        #                    expression has no child and is a terminus
        if (children and not any(c in self.prod for c in offsprings) or
            not children and exp not in self.prod):
            # pruning
            if self.pruned(exp, len(offsprings), limit):
                return False
            # query SMT solver
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
                    # greedy
                    return False
        # eta not under this expansion
        return False

    def synthesis(self, limit):
        """IDS on offspring count bounded by limit"""
        self.synth_time = time()
        self.lim = limit
        self.inv = None
        # iterative deepening search
        for l in range(5, limit+1):
            result = self.genesis(self._S, l)
            # eta is found
            if type(result) == BoolRef:
                self.synth_time = time() - self.synth_time
                self.inv = result
                return result

    def test(self):
        print(self.checkEta(self.i+self.j==IntVal(9)))
        print(self.checkEta(And(self.i+self.j==IntVal(9), self.i < IntVal(11))))
        print(self.checkEta(And(11 > self.i, 9 == self.i + self.j)))

        return

    def report(self):
        """synthesis stats report"""
        print("==========================")
        if type(self.inv) == BoolRef:
            print("invariant found:", self.inv, "\n")
        else:
            print("invariant not found within depth:", self.lim, "\n")
        print("z3 queried:", z3.query_counter, "\n")
        print("depth pruned:", z3.pruned_counter, "\n")
        print("semantics pruned:", z3.prunes_counter, "\n")
        print("history size:", len(self.history))
        print("history pruned:", z3.pruneh_counter, "\n")
        print("ce 1 size:", "N/A")
        print("req 1 pruned:", z3.prune1_counter, "\n")
        print("ce 2 size:", len(self.counter_examples2))
        print("req 2 pruned:", z3.prune2_counter, "\n")
        print("ce 3 size:", len(self.counter_examples3))
        print("req 3 pruned:", z3.prune3_counter, "\n")
        print("time:", self.synth_time)
        print("==========================")
        return

    def subv(self, exp, oldv, newv, order):
        """sub recursion helper"""
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
            return self.subv(parts[0], oldv, newv, order) +  self.subv(parts[1], oldv, newv, order)
        elif is_sub(exp):
            return self.subv(parts[0], oldv, newv, order) -  self.subv(parts[1], oldv, newv, order)
        elif is_mul(exp):
            return self.subv(parts[0], oldv, newv, order) *  self.subv(parts[1], oldv, newv, order)
        elif is_le(exp):
            return self.subv(parts[0], oldv, newv, order) <= self.subv(parts[1], oldv, newv, order)
        elif is_lt(exp):
            return self.subv(parts[0], oldv, newv, order) <  self.subv(parts[1], oldv, newv, order)
        elif is_ge(exp):
            return self.subv(parts[0], oldv, newv, order) >= self.subv(parts[1], oldv, newv, order)
        elif is_gt(exp):
            return self.subv(parts[0], oldv, newv, order) >  self.subv(parts[1], oldv, newv, order)
        elif is_eq(exp):
            return self.subv(parts[0], oldv, newv, order) == self.subv(parts[1], oldv, newv, order)
        else:
            raise Exception("uncaught sub", exp, oldv, newv, order)

    def sub(self, exp, oldv, newv, order=0):
        """
        Substitute oldv of index order with newv in exp.
        oldv should be single term expression.
        supported symbols: And, Or, Not, +, -, *, <=, <, >=, >, ==

        >> x, y = Bools('x y')
        >> sub(And(x, x), x, y)
        And(y, x)
        >> sub(And(x, x), x, y, 1)
        And(x, y)
        >> sub(And(y, x, x, x), x, y, 2)
        And(y, x, y, x)

        >> sub(And(Or(x, y), x), Or(x, y), y)
        Exception: sub oldv should be single term expression
        >> sub(And(x, Or(x, y)), x, Or(x, y))
        And(Or(x, y), Or(x, y))

        >> sub(And(x, x), y, And(x, y))
        And(x, x)
        >> sub(And(x, x), x, y, 5)
        And(x, x)

        >> sub(Implies(x, x), x, y)
        Exception: ('uncaught sub', Implies(x, x), x, y, 0)
        """
        if not is_const(oldv):
            raise Exception("sub oldv should be single term expression")
        self.done = False
        self.subc = 0
        return self.subv(exp, oldv, newv, order)

z3 = Z3()
t = time()

z3.synthesis(10)
z3.report()

#z3.test()
