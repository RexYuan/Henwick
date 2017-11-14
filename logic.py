import satispy, z3

class Formula(object):
    '''
    base class for all formulae
    '''
    @staticmethod
    def translate2satispy(X):
        if type(X) == Atom:
            return satispy.Variable(X.name)
        elif type(X) == Not:
            return -Formula.translate2satispy(X.subf)
        elif type(X) == And:
            return Formula.translate2satispy(X.subf1) & Formula.translate2satispy(X.subf2)
        elif type(X) == Or:
            return Formula.translate2satispy(X.subf1) | Formula.translate2satispy(X.subf2)

    @staticmethod
    def translate2z3(X):
        if type(X) == Atom:
            return z3.Bool(X.name)
        elif type(X) == Not:
            return z3.Not(Formula.translate2z3(X.subf))
        elif type(X) == And:
            return z3.And(Formula.translate2z3(X.subf1), Formula.translate2z3(X.subf2))
        elif type(X) == Or:
            return z3.Or(Formula.translate2z3(X.subf1), Formula.translate2z3(X.subf2))

    def __neg__(self):
        if self == T:
            return F
        elif self == F:
            return T
        else:
            return Not(self)

    def __and__(self, other):
        if self == T:
            return other
        elif self == F:
            return F
        elif other == T:
            return self
        elif other == F:
            return F
        else:
            return And(self, other)

    def __or__(self, other):
        if self == T:
            return T
        elif self == F:
            return other
        elif other == T:
            return T
        elif other == F:
            return self
        else:
            return Or(self, other)

    def __add__(self, other):
        return repr(self) + other

    def __radd__(self, other):
        return other + repr(self)

    def transform(self, X):
        '''
        C(X) = X
        C(-X) =  (p_nX |  p_X) &
                (-p_nX | -p_X)
        C(X & Y) = (-p_XandY |  p_X) &
                   (-p_XandY |         p_Y) &
                    (p_XandY | -p_X | -p_Y)
        C(X | Y) =  (p_XorY | -p_X) &
                    (p_XorY |        -p_Y) &
                   (-p_XorY |  p_X |  p_Y)
        '''
        if type(X) == Atom:
            raise Exception()
        elif type(X) == Not:
            p_nX = Atom('p_'+X)
            p_X  = Atom('p_'+X.subf) if type(X.subf) != Atom else X.subf
            #print((p_nX | p_X) & (-p_nX | -p_X))
            return (p_nX | p_X) & (-p_nX | -p_X)
        elif type(X) == And:
            p_XandY = Atom('p_'+X)
            p_X     = Atom('p_'+X.subf1) if type(X.subf1) != Atom else X.subf1
            p_Y     = Atom('p_'+X.subf2) if type(X.subf2) != Atom else X.subf2
            #print((-p_XandY | p_X) & (-p_XandY | p_Y) & (p_XandY | -p_X | -p_Y))
            return (-p_XandY | p_X) & (-p_XandY | p_Y) & (p_XandY | -p_X | -p_Y)
        elif type(X) == Or:
            p_XorY = Atom('p_'+X)
            p_X    = Atom('p_'+X.subf1) if type(X.subf1) != Atom else X.subf1
            p_Y    = Atom('p_'+X.subf2) if type(X.subf2) != Atom else X.subf2
            #print((p_XorY | -p_X) & (p_XorY | -p_Y) & (-p_XorY | p_X | p_Y))
            return (p_XorY | -p_X) & (p_XorY | -p_Y) & (-p_XorY | p_X | p_Y)
        else:
            raise Exception()

    def tseitin(self):
        transform = self.transform
        def walk(X):
            if type(X) == Atom:
                return T
            elif type(X) == Not:
                return transform(X) & walk(X.subf)
            elif type(X) == And:
                return transform(X) & walk(X.subf1) & walk(X.subf2)
            elif type(X) == Or:
                return transform(X) & walk(X.subf1) & walk(X.subf2)
            else:
                raise Exception()
        return Atom('p_'+self) & walk(self)

class Head(Formula):
    def __str__(self):
        return '⊤'

    def __repr__(self):
        return 'T'

class Bottom(Formula):
    def __str__(self):
        return '⊥'

    def __repr__(self):
        return 'F'

T = Head()
F = Bottom()

class Atom(Formula):
    def __init__(self, name):
        self.name = name

    def __str__(self):
        return self.name

    def __repr__(self):
        return self.name

class Not(Formula):
    def __init__(self, subf):
        self.subf = subf

    def __str__(self):
        return '¬'+str(self.subf)+''

    def __repr__(self):
        return '-'+repr(self.subf)+''

class And(Formula):
    def __init__(self, subf1, subf2):
        self.subf1 = subf1
        self.subf2 = subf2

    def __str__(self):
        return '('+str(self.subf1)+' ∧ '+str(self.subf2)+')'

    def __repr__(self):
        return '('+repr(self.subf1)+' & '+repr(self.subf2)+')'

class Or(Formula):
    def __init__(self, subf1, subf2):
        self.subf1 = subf1
        self.subf2 = subf2

    def __str__(self):
        return '('+str(self.subf1)+' ∨ '+str(self.subf2)+')'

    def __repr__(self):
        return '('+repr(self.subf1)+' | '+repr(self.subf2)+')'

from time import time
t = time()
p,q,r,s = Atom('p'),Atom('q'),Atom('r'),Atom('s')
prop = -((p & q) | (-p & r) | (q & -s) | (p & s))
print('make original took', time()-t)
t = time()
tprop = prop.tseitin()
print('translate to tseitin took', time()-t,'\n\n')

sat = satispy.solver.Minisat()
smt = z3.Solver()

t = time()
sprop = Formula.translate2satispy(prop)
print('translate original to satispy took', time()-t)
t = time()
satp = Formula.translate2satispy(tprop)
print('translate tseitin to satispy took', time()-t)

t = time()
result = sat.solve(satp)
print('satispy results for tseitin formula:')
while result.success:
    if result[satispy.Variable('p')]:
        counter = satispy.Variable('p')
    else:
        counter = -satispy.Variable('p')
    print('p', result[satispy.Variable('p')])
    for x in ('q','r','s'):
        print(x, result[satispy.Variable(x)])
        if result[satispy.Variable(x)]:
            counter = counter & satispy.Variable(x)
        else:
            counter = counter & -satispy.Variable(x)
    print()

    satp = satp & -counter
    result = sat.solve(satp)
print('satispy took', time()-t,'\n\n')

t = time()
zprop = Formula.translate2z3(prop)
print('translate original to z3 took', time()-t)
t = time()
z3p = Formula.translate2z3(tprop)
print('translate tseitin to z3 took', time()-t)

t = time()
smt.add(z3p)
result = smt.check()
print('z3 results for tseitin formula:')
while result == z3.sat:
    result = smt.model()
    if result[z3.Bool('p')]:
        counter = z3.Bool('p')
    else:
        counter = z3.Not(z3.Bool('p'))
    print('p', result[z3.Bool('p')])
    for x in ('q','r','s'):
        print(x, result[z3.Bool(x)])
        if result[z3.Bool(x)]:
            counter = z3.And(counter, z3.Bool(x))
        else:
            counter = z3.And(counter, z3.Not(z3.Bool(x)))
    print()

    smt.add(z3.Not(counter))
    result = smt.check()
print('z3 took', time()-t)
