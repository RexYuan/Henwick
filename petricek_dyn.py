from z3 import *
from time import time

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
                          Minus]
        }

        self.solver = Solver()

        self.bool_sub_expr = [[], [True, False]]
        self.int_sub_expr = [[], [IntVal(9), IntVal(11), Int('i'), Int('j')]]

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
        # req 1) T => eta[j/9][i/0]
        result = self.isValid(Implies(True, substitute(eta, (Int('j'), IntVal(9)), (Int('i'), IntVal(0)))))
        if result != True:
            if result[Int('i')] != None and result[Int('j')] != None:
                self.counter_examples1.append((result[Int('i')], result[Int('j')]))
            return False
        # req 2) eta and not i < 10 => i = 10 and j = -1
        result = self.isValid(Implies(And(eta, Not(Int('i') < IntVal(10))), And(Int('i') == IntVal(10), Int('j') == IntVal(-1))))
        if result != True:
            if result[Int('i')] != None and result[Int('j')] != None:
                self.counter_examples2.append((result[Int('i')], result[Int('j')]))
            return False
        # req 3) i < 10 and eta => eta[j-1/j][i+1/i]
        result = self.isValid(Implies(And(Int('i') < IntVal(10), eta), substitute(eta, (Int('j'), Int('j')-IntVal(1)), (Int('i'), Int('i')+IntVal(1)))))
        if result != True:
            if result[Int('i')] != None and result[Int('j')] != None:
                self.counter_examples3.append((result[Int('i')], result[Int('j')]))
            return False
        return True

    def pruned(self, exp):
        """check if exp is pruned"""
        # counter example pruning
        # T => eta[j/9][i/0]
        if simplify(substitute(exp, (Int('j'), IntVal(9)), (Int('i'), IntVal(0)))) == False:
            return True
        # eta and not i < 10 => i = 10 and j = -1
        if any(simplify(substitute(exp, (Int('i'), ci), (Int('j'), cj))) == True
               for (ci, cj) in self.counter_examples2):
            return True
        # i < 10 and eta => eta[j-1/j][i+1/i]
        if any(simplify(substitute(exp, (Int('i'), ci), (Int('j'), cj))) == True
               and simplify(substitute(exp, (Int('j'), cj-IntVal(1)),
                                            (Int('i'), ci+IntVal(1)))) == False
               for (ci, cj) in self.counter_examples3):
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

            print(time()-t, 'size', size, 'done')

z3 = Z3()

z3.synthesis(10)
#print(z3.isValid(Bool('a')==Bool('b'))==True)
