from z3 import *

class Z3:
    def __init__(self):
        self.S = Bool('S')
        self._Simple = Bool('Simple')
        self._Hard = Bool('Hard')
        self._VarLgCst = Bool('VarLgCst')
        self._And3 = Bool('And3')
        self._Var = Int('Var')
        self._Var1= Int('Var1')
        self._Var2= Int('Var2')
        self._Cst = Int('Cst')
        self._VarLgEqCst = Bool('VarLgEqCst')
        self._VarEqComplex = Bool('VarEqComplex')
        self._Complex1 = Int('Complex1')
        self._VarLtEqCst = Bool('VarLtEqCst')
        self._AndImp2 = Bool('AndImp2')
        self._Imp1 = Bool('Imp1')
        self._AndComplex = Bool('AndComplex')
        self._SubAndComplex1 = Bool('SubAndComplex1')
        self._SubAndComplex2 = Bool('SubAndComplex2')
        self._Imp2 = Bool('Imp2')
        self.n = Int('n')
        self.c = Int('c')
        self.ret = Int('ret')
        self.prod = {
            self.S:  [And(Implies(self._Var1>IntVal(100),And(self._Var2>=0,Int('n')>IntVal(100),Int('ret')==Int('n')-10+10*Int('c'))), Implies(Int('n')<=IntVal(100),And(Implies(Int('ret')>=90,And(91-Int('c')<=Int('ret'),Int('ret')<=91+10*Int('c'))),Implies(Int('ret')<90,Int('c')>0))))],
            #self._Simple: [Implies(self._Var>IntVal(100),And(self._Var>=IntVal(0),self._Var>IntVal(100),self.ret==self.n-IntVal(10)+IntVal(10)*self.c))],
            #self._Hard: [Implies(self.n<=IntVal(100),And(Implies(self.ret>=IntVal(90),And(self._Cst-self.c<=self.ret,self.ret<=IntVal(91)+IntVal(10)*self.c)),Implies(self.ret<IntVal(90),self.c>self._Cst)))],

            self._Var1: [self.n, self.c],
            self._Var2: [self.n, self.c],
            self._Cst: [IntVal(100), IntVal(0), IntVal(10), IntVal(90), IntVal(91)]
        }
        self.solver = Solver()
        self.counter_examples = []
        self.counter=0
    """
    self._Simple: [Implies(self._VarLgCst, self._And3)],
    self._VarLgCst: [self._Var > self._Cst],
    self._And3: [And(self._VarLgEqCst, self._VarLgCst, self._VarEqComplex)],
    self._VarLgEqCst: [self._Var >= self._Cst],
    self._VarEqComplex: [self._Var == self._Complex1],
    self._Complex1: [self._Var - self._Cst + self._Cst * self._Var],
    self._Hard: [Implies(self._VarLtEqCst, self._AndImp2)],
    self._VarLtEqCst: [self._Var <= self._Cst],
    self._AndImp2: [And(self._Imp1, self._Imp2)],
    self._Imp1: [Implies(self._VarLgEqCst, self._AndComplex)],
    self._AndComplex: [And(self._SubAndComplex1, self._SubAndComplex2)],
    self._SubAndComplex1: [self._Cst - self._Var <= self._Var],
    self._SubAndComplex2: [self._Var <= self._Cst + self._Cst * self._Var],
    self._Imp2: [And(self._Var < self._Cst, self._Var > self._Cst)],
    """
    def isImpValid(self, imp):
        self.solver.push()
        self.solver.add(Not(imp))
        result = self.solver.check()
        ret = True if result == unsat else self.solver.model()
        self.solver.pop()
        return ret

    def checkEta(self, eta):
        result = self.isImpValid(Implies(And(self.c > 0, eta), And(Implies(self.ret > 100, substitute(substitute(eta, (self.c, self.c-1)), (self.ret, self.ret-10))), Implies(self.ret <= 100, substitute(substitute(eta, (self.c, self.c+1)), (self.ret, self.ret+11))))))
        if result != True:
            return False
        result = self.isImpValid(Implies(And(self.ret == self.n, self.c == 1), eta))
        if result != True:
            self.counter_examples.append((result[self.ret], result[self.n], result[self.c]))
            return False
        result = self.isImpValid(Implies(And(eta, self.c <= 0), And(Implies((self.n <= 100), (self.ret == 91)), Implies((self.n > 100), (self.ret == self.n - 10)))))
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
        print(exp)
        # recursion base
        # if expression has children and they're all termini or
        # if expression has no child and is a terminus
        if (exp.children() and not any(c in self.prod for c in list(self.getConstituents(exp))) or
            not exp.children() and exp not in self.prod):
            # pruning
            #print(self.counter_examples)
            #if any(cret == cn and cc == 1 and simplify(substitute(exp, (self.ret, cret), (self.n, cn), (self.c, cc))) == False for (cret, cn, cc) in self.counter_examples):
            #    return False
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
print(z3.genesis(Bool('S')))
"""a = Solver()
a.add(z3.genesis(Bool('S')))
tar = And(Implies(Int('n')>IntVal(100),And(Int('c')>=0,Int('n')>IntVal(100),Int('ret')==Int('n')-10+10*Int('c'))),Implies(Int('n')<=IntVal(100),And(Implies(Int('ret')>=90,And(91-Int('c')<=Int('ret'),Int('ret')<=91+10*Int('c'))),Implies(Int('ret')<90,Int('c')>0))))
a.add(Not(tar))
print(a.check())
"""
#ass = And(Implies(100 < Int('n'),And(0 <= Int('n'), 100 < Int('n'), Int('ret') == Int('n') - 10 + 10*Int('c'))),Implies(100 >= Int('n'),And(Implies(90 <= Int('ret'),And(0 - Int('c') <= Int('ret'), Int('ret') <= 91 + 10*Int('c'))),Implies(90 > Int('ret'), Int('c') > 0))))
#print(z3.isImpValid(ass))
