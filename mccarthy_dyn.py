from z3 import *
from time import time
from sys import stdout

def Lg(a, b):
    """
    Int -> Int -> Bool
    """
    return a > b

def LgEq(a, b):
    """
    Int -> Int -> Bool
    """
    return a >= b

def Eq(a, b):
    """
    Int -> Int -> Bool
    """
    return a == b

def NotEq(a, b):
    """
    Int -> Int -> Bool
    """
    return a != b

def Add(a, b):
    """
    Int -> Int -> Int
    """
    return a + b

def Minus(a, b):
    """
    Int -> Int -> Int
    """
    return a - b

def Mult(a, b):
    """
    Int -> Int -> Int
    """
    return a * b

def get2Partition(num):
    if num <= 1:
        raise Exception("no")
    else:
        return [(i, num-i) for i in range(1,num//2+1)]

class Z3:
    def __init__(self):
        self.connectives = {
            'boolLogic': [And,
                          Or],
            'boolComp':  [Lg,
                          LgEq,
                          Eq,
                          NotEq],
            'int':       [Add,
                          Minus,
                          Mult]
        }

        self.solver = Solver()

        self.bool_sub_expr = [[], [True, False]]
        self.int_sub_expr = [[], [IntVal(0), IntVal(10), IntVal(90), IntVal(91), IntVal(100), Int('n'), Int('c'), Int('ret')]]

        self.counter_examples1 = []
        self.counter_examples2 = []
        self.counter_examples3 = []

    def isValid(self, exp):
        """check the validity of exp"""
        self.solver.push()
        self.solver.add(Not(exp))
        result = self.solver.check()
        ret = True if result == unsat else self.solver.model()
        self.solver.pop()
        return ret

    def checkEta(self, eta):
        """check eta against requirements"""
        # req 1)
        # (ret == n and c == 1) => ETA
        result = self.isValid(Implies(And(Int('ret') == Int('n'), Int('c') == IntVal(1)), eta))
        if result != True:
            if result[Int('n')] != None and result[Int('c')] != None and result[Int('ret')] != None:
                self.counter_examples1.append((result[Int('n')], result[Int('c')], result[Int('ret')]))
            return False
        # req 2)
        # (ETA and c <= 0) => (((n <= 100) => (ret == 91)) and
        #                     ((n > 100) => (ret == n - 10)))
        result = self.isValid(Implies(And(eta, Int('c') <= IntVal(0)),
                                      And(Implies((Int('n') <= IntVal(100)),
                                                  (Int('ret') == IntVal(91))),
                                          Implies((Int('n') > IntVal(100)),
                                                  (Int('ret') == Int('n') - IntVal(10))))))
        if result != True:
            if result[Int('n')] != None and result[Int('c')] != None and result[Int('ret')] != None:
                self.counter_examples2.append((result[Int('n')], result[Int('c')], result[Int('ret')]))
            return False
        # req 3)
        # (c > 0 and ETA) => ((ret > 100) => ETA[c-1 / c][ret-10 / ret]) and
        #                    ((ret <= 100) => ETA[c+1 / c][ret+11 / ret])
        result = self.isValid(Implies(And(Int('c') > IntVal(0), eta),
                                      And(Implies(Int('ret') > IntVal(100),
                                                  substitute(eta, (Int('c'), Int('c')-IntVal(1)), (Int('ret'), Int('ret')-IntVal(10)))),
                                          Implies(Int('ret') <= IntVal(100),
                                                  substitute(eta, (Int('c'), Int('c')+IntVal(1)), (Int('ret'), Int('ret')+IntVal(11)))))))
        if result != True:
            if result[Int('n')] != None and result[Int('c')] != None and result[Int('ret')] != None:
                self.counter_examples3.append((result[Int('n')], result[Int('c')], result[Int('ret')]))
            return False
        return True

    def pruned(self, exp):
        """check if exp is pruned"""
        # counter example pruning
        # (ret == n and c == 1) => ETA
        if any(simplify(cret == cn) == True and
               simplify(cc == IntVal(1)) == True and
               simplify(substitute(exp, (Int('n'), cn), (Int('c'), cc), (Int('ret'), cret))) == False
               for (cn, cc, cret) in self.counter_examples1):
            return True
        # (ETA and c <= 0) => (((n <= 100) => (ret == 91)) and
        #                     ((n > 100) => (ret == n - 10)))
        if any(simplify(substitute(exp, (Int('n'), cn), (Int('c'), cc), (Int('ret'), cret))) == True and
               simplify(cc <= IntVal(0)) == True and
               ((simplify(cn <= IntVal(100)) == True and
                 simplify(cret == IntVal(91)) == False) or
                (simplify(cn > IntVal(100)) == True and
                 simplify(cret == cn - IntVal(10)) == False))
               for (cn, cc, cret) in self.counter_examples2):
            return True
        # (c > 0 and ETA) => ((ret > 100) => ETA[c-1 / c][ret-10 / ret]) and
        #                    ((ret <= 100) => ETA[c+1 / c][ret+11 / ret])
        if any(simplify(cc > IntVal(0)) == True and
               simplify(substitute(exp, (Int('n'), cn), (Int('c'), cc), (Int('ret'), cret))) == True and
               ((simplify(cret > IntVal(100)) == True and
                 simplify(substitute(exp, (Int('n'), cn), (Int('c'), cc-IntVal(1)), (Int('ret'), cret-IntVal(10)))) == False) or
                (simplify(cret <= IntVal(100)) == True and
                 simplify(substitute(exp, (Int('n'), cn), (Int('c'), cc+IntVal(1)), (Int('ret'), cret+IntVal(11)))) == False))
               for (cn, cc, cret) in self.counter_examples3):
            return True
        return False

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

    def genesis(self, size):
        partitions = get2Partition(size)
        self.int_sub_expr.append([])
        for c in self.connectives['int']:
            for p in partitions:
                for a in self.int_sub_expr[p[0]]:
                    for b in self.int_sub_expr[p[1]]:
                        self.int_sub_expr[size].append(c(a, b))
        self.bool_sub_expr.append([])
        for c in self.connectives['boolComp']:
            for p in partitions:
                for a in self.int_sub_expr[p[0]]:
                    for b in self.int_sub_expr[p[1]]:
                        if simplify(c(a, b)) == True or simplify(c(a, b)) == False:
                            continue
                        self.bool_sub_expr[size].append(c(a, b))
                        if self.pruned(c(a, b)):
                            continue
                        if self.checkEta(c(a, b)):
                            print(c(a, b))
                            return True
        for c in self.connectives['boolLogic']:
            for p in partitions:
                for a in self.bool_sub_expr[p[0]]:
                    for b in self.bool_sub_expr[p[1]]:
                        if simplify(c(a, b)) == True or simplify(c(a, b)) == False:
                            continue
                        self.bool_sub_expr[size].append(c(a, b))
                        if self.pruned(c(a, b)):
                            continue
                        if self.checkEta(c(a, b)):
                            print(c(a, b))
                            return True

    def synthesis(self, limit):
        t0 = time()
        for size in range(2, limit):
            t = time()
            if self.genesis(size):
                print(time()-t0, 'total')
                return True
            print(time()-t, 'size', size, 'done')
            print('int_sub_expr size:', len(self.int_sub_expr[size]))
            print('bool_sub_expr size:', len(self.bool_sub_expr[size]))
            stdout.flush()
        return False

z3 = Z3()

z3.synthesis(100)
