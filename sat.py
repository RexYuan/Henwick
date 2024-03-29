import satispy, z3, pycosat

class Formula(object):
    '''
    Base class for all formulae.
    '''
    def __rshift__(self, other):
        return Or(Not(self), other)

    def __neg__(self):
        '''
        Shorthand for Not.
        '''
        if self == T:
            return F
        elif self == F:
            return T
        else:
            return Not(self)

    def __and__(self, other):
        '''
        Shorthand for And.
        '''
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
        '''
        Shorthand for Or.
        '''
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
        '''
        Shorthand for string concatenation.
        '''
        return repr(self) + other

    def __radd__(self, other):
        '''
        Shorthand for string concatenation.
        '''
        return other + repr(self)

    def nnf(self):
        '''
        Convert to negation normal form.
        '''
        def transform(X):
            if type(X) == Atom:
                return X
            elif type(X) == Not:
                if type(X.subf) == Atom:
                    return X
                if type(X.subf) == Not:
                    return transform(X.subf.subf)
                elif type(X.subf) == And:
                    return transform(Not(X.subf.subf1) | Not(X.subf.subf2))
                elif type(X.subf) == Or:
                    return transform(Not(X.subf.subf1) & Not(X.subf.subf2))
                else:
                    raise Exception()
            elif type(X) == And:
                return transform(X.subf1) & transform(X.subf2)
            elif type(X) == Or:
                return transform(X.subf1) | transform(X.subf2)
            else:
                raise Exception()
        return transform(self)

    def cnf(self):
        '''
        Convert to conjunctive normal form.
        '''
        def distribute(X, Y):
            if type(X) == And:
                # (x & y) | z => (x | z) & (y | z)
                return distribute(X.subf1,Y) & distribute(X.subf2,Y)
            elif type(Y) == And:
                # x | (y & z) => (x | y) & (x | z)
                return distribute(X,Y.subf1) & distribute(X,Y.subf2)
            else:
                return X | Y
        def transform(X):
            if type(X) == Atom:
                return X
            elif type(X) == Not:
                return X
            elif type(X) == And:
                return transform(X.subf1) & transform(X.subf2)
            elif type(X) == Or:
                return distribute(transform(X.subf1), transform(X.subf2))
            else:
                raise Exception()
        return transform(self.nnf())

    @staticmethod
    def _transform(X):
        '''
        Helper method for Tseitin Transformation.

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
            return (p_nX | p_X) & (-p_nX | -p_X)
        elif type(X) == And:
            p_XandY = Atom('p_'+X)
            p_X     = Atom('p_'+X.subf1) if type(X.subf1) != Atom else X.subf1
            p_Y     = Atom('p_'+X.subf2) if type(X.subf2) != Atom else X.subf2
            return (-p_XandY | p_X) & (-p_XandY | p_Y) & (p_XandY | -p_X | -p_Y)
        elif type(X) == Or:
            p_XorY = Atom('p_'+X)
            p_X    = Atom('p_'+X.subf1) if type(X.subf1) != Atom else X.subf1
            p_Y    = Atom('p_'+X.subf2) if type(X.subf2) != Atom else X.subf2
            return (p_XorY | -p_X) & (p_XorY | -p_Y) & (-p_XorY | p_X | p_Y)
        else:
            raise Exception()

    def tseitin(self):
        '''
        Tseitin Transformation.
        '''
        transform = self._transform
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

    @staticmethod
    def _cnf_list(X, f=str, encode=True):
        '''
        Encode CNF list.
        '''
        var_map = {}
        rev_map = {}

        def get_terms(X):
            if type(X) == Atom:
                s = repr(X)
                if s not in var_map:
                    var_map[s] = str(len(var_map)+1)
                    rev_map[f(len(var_map))] = X
                return [f(var_map[s])] if encode else [X]
            elif type(X) == Not:
                s = repr(X.subf)
                if s not in var_map:
                    var_map[s] = str(len(var_map)+1)
                    rev_map[f(len(var_map))] = X.subf
                return [f('-'+var_map[s])] if encode else [X]
            elif type(X) == And:
                raise Exception()
            elif type(X) == Or:
                return [*get_terms(X.subf1), *get_terms(X.subf2)]
            else:
                raise Exception()

        def get_clauses(X):
            if type(X) == Atom:
                s = repr(X)
                if s not in var_map:
                    var_map[s] = str(len(var_map)+1)
                    rev_map[f(len(var_map))] = X
                return [[f(var_map[s])]] if encode else [[X]]
            elif type(X) == Not:
                s = repr(X.subf)
                if s not in var_map:
                    var_map[s] = str(len(var_map)+1)
                    rev_map[f(len(var_map))] = X.subf
                return [[f('-'+var_map[s])]]if encode else [[X]]
            elif type(X) == And:
                return [*get_clauses(X.subf1), *get_clauses(X.subf2)]
            elif type(X) == Or:
                return [get_terms(X)]
            else:
                raise Exception()

        cs = get_clauses(X)
        return (cs, len(var_map), len(cs), rev_map)

    def to_dimacs(self):
        '''
        Convert to DIMACS CNF format.
        '''
        cs, nbv, nbc = self._cnf_list(self.cnf())
        tmp = 'p cnf '+str(nbv)+' '+str(nbc)+'\n'
        for c in cs:
            tmp += ' '.join(c) + ' 0\n'
        tmp = tmp.rstrip()
        return tmp

    @classmethod
    def from_satispy(cls, cnf):
        '''
        Construct Formula from satispy Cnf.
        '''
        raise NotImplementedError

    def to_satispy(self):
        '''
        Convert to satispy Cnf.
        '''
        def translate(X):
            if type(X) == Atom:
                return satispy.Variable(X.name)
            elif type(X) == Not:
                return -translate(X.subf)
            elif type(X) == And:
                return translate(X.subf1) & translate(X.subf2)
            elif type(X) == Or:
                return translate(X.subf1) | translate(X.subf2)
            else:
                raise Exception()
        return translate(self)

    def solve_satispy(self):
        raise NotImplementedError

    @classmethod
    def from_z3(cls, formula):
        '''
        Construct Formula from z3 BoolRef.
        '''
        def translate(X):
            cs = X.children()
            if z3.is_bool(X) and cs == []:
                return Atom(repr(X))
            elif z3.is_not(X):
                return Not(translate(cs[0]))
            elif z3.is_and(X):
                if len(cs) > 2:
                    return And(translate(cs[0]), translate(z3.And(*cs[1:])))
                else:
                    return And(translate(cs[0]), translate(cs[1]))
            elif z3.is_or(X):
                if len(cs) > 2:
                    return Or(translate(cs[0]), translate(z3.Or(*cs[1:])))
                else:
                    return Or(translate(cs[0]), translate(cs[1]))
        return translate(formula)

    def to_z3(self):
        '''
        Convert to z3 BoolRef.
        '''
        def translate(X):
            if type(X) == Atom:
                return z3.Bool(X.name)
            elif type(X) == Not:
                return z3.Not(translate(X.subf))
            elif type(X) == And:
                return z3.And(translate(X.subf1), translate(X.subf2))
            elif type(X) == Or:
                return z3.Or(translate(X.subf1), translate(X.subf2))
        return translate(self)

    def solve_z3(self):
        raise NotImplementedError

    def solve_pycosat(self):
        cs, nbv, _, vmap = self._cnf_list(self.cnf(), f=int)
        result = pycosat.solve(cs, vars=nbv, verbose=0)
        result = list(map((lambda x : vmap[abs(x)] if x > 0 else Not(vmap[abs(x)])), result))
        return result

    def solve_all_pycosat(self):
        cs, nbv, _, vmap = self._cnf_list(self.cnf(), f=int)
        for r in pycosat.itersolve(cs, vars=nbv, verbose=0):
            result = list(map((lambda x : vmap[abs(x)] if x > 0 else Not(vmap[abs(x)])), r))
            yield result

    def solve(self):
        return self.solve_pycosat()

    def solve_all(self):
        return self.solve_all_pycosat()

class _Head(Formula):
    '''
    Tautology constructor.
    Do not use this directly.
    Use global variable T instead.
    '''
    def __str__(self):
        return '⊤'

    def __repr__(self):
        return 'T'

class _Bottom(Formula):
    '''
    Contradiction constructor.
    Do not use this directly.
    Use global variable F instead.
    '''
    def __str__(self):
        return '⊥'

    def __repr__(self):
        return 'F'

T = _Head()
F = _Bottom()

class Atom(Formula):
    '''
    Atom variable constructor.
    For constant literals, use T and F instead.
    '''
    def __init__(self, name):
        self.name = name

    def __str__(self):
        return self.name

    def __repr__(self):
        return self.name

class Not(Formula):
    '''
    Unary Not formula constructor.
    '''
    def __init__(self, subf):
        self.subf = subf

    def __str__(self):
        return '¬'+str(self.subf)+''

    def __repr__(self):
        return '-'+repr(self.subf)+''

class And(Formula):
    '''
    Binary And formula constructor.
    '''
    def __init__(self, subf1, subf2):
        self.subf1 = subf1
        self.subf2 = subf2

    def __str__(self):
        return '('+str(self.subf1)+' ∧ '+str(self.subf2)+')'

    def __repr__(self):
        return '('+repr(self.subf1)+' & '+repr(self.subf2)+')'

class Or(Formula):
    '''
    Binary Or formula constructor.
    '''
    def __init__(self, subf1, subf2):
        self.subf1 = subf1
        self.subf2 = subf2

    def __str__(self):
        return '('+str(self.subf1)+' ∨ '+str(self.subf2)+')'

    def __repr__(self):
        return '('+repr(self.subf1)+' | '+repr(self.subf2)+')'

p,q,r,s = Atom('p'),Atom('q'),Atom('r'),Atom('s')
x = p | (q & -r & (r | -p | (s & -q & -p)))


'''
from time import time

t = time()
p,q,r,s = Atom('p'),Atom('q'),Atom('r'),Atom('s')
prop = -((p & q) | (-p & r) | (q & -s) | (p & s))
print('make original took', time()-t)

t = time()
cprop = prop.cnf()
print('translate to cnf took', time()-t)

t = time()
tprop = prop.tseitin()
print('translate to tseitin took', time()-t,'\n\n')

sat = satispy.solver.Minisat()
smt = z3.Solver()

t = time()
satc = cprop.to_satispy()
print('translate cnf to satispy took', time()-t)

t = time()
result = sat.solve(satc)
print('satispy results for cnf formula:')
while result.success:
    if result[satispy.Variable('p')]:
        counter = satispy.Variable('p')
    else:
        counter = -satispy.Variable('p')
    print('p:', result[satispy.Variable('p')], end=' ')
    for x in ('q','r','s'):
        print(x,':', result[satispy.Variable(x)], end=' ')
        if result[satispy.Variable(x)]:
            counter = counter & satispy.Variable(x)
        else:
            counter = counter & -satispy.Variable(x)
    print()
    satc = satc & -counter
    result = sat.solve(satc)
print('satispy took for cnf', time()-t,'\n')

t = time()
satt = tprop.to_satispy()
print('translate tseitin to satispy took', time()-t)

t = time()
result = sat.solve(satt)
print('satispy results for tseitin formula:')
while result.success:
    if result[satispy.Variable('p')]:
        counter = satispy.Variable('p')
    else:
        counter = -satispy.Variable('p')
    print('p:', result[satispy.Variable('p')], end=' ')
    for x in ('q','r','s'):
        print(x,':', result[satispy.Variable(x)], end=' ')
        if result[satispy.Variable(x)]:
            counter = counter & satispy.Variable(x)
        else:
            counter = counter & -satispy.Variable(x)
    print()
    satt = satt & -counter
    result = sat.solve(satt)
print('satispy took for tseitin', time()-t,'\n\n')

t = time()
z3c = cprop.to_z3()
print('translate cnf to z3 took', time()-t)

t = time()
smt.add(z3c)
result = smt.check()
print('z3 results for cnf formula:')
while result == z3.sat:
    result = smt.model()
    if result[z3.Bool('p')]:
        counter = z3.Bool('p')
    else:
        counter = z3.Not(z3.Bool('p'))
    print('p', result[z3.Bool('p')], end=' ')
    for x in ('q','r','s'):
        print(x,':', result[z3.Bool(x)], end=' ')
        if result[z3.Bool(x)]:
            counter = z3.And(counter, z3.Bool(x))
        else:
            counter = z3.And(counter, z3.Not(z3.Bool(x)))
    print()
    smt.add(z3.Not(counter))
    result = smt.check()
print('z3 took for cnf', time()-t, '\n')

smt.reset()

t = time()
z3t = tprop.to_z3()
print('translate tseitin to z3 took', time()-t)

t = time()
smt.add(z3t)
result = smt.check()
print('z3 results for tseitin formula:')
while result == z3.sat:
    result = smt.model()
    if result[z3.Bool('p')]:
        counter = z3.Bool('p')
    else:
        counter = z3.Not(z3.Bool('p'))
    print('p', result[z3.Bool('p')], end=' ')
    for x in ('q','r','s'):
        print(x,':', result[z3.Bool(x)], end=' ')
        if result[z3.Bool(x)]:
            counter = z3.And(counter, z3.Bool(x))
        else:
            counter = z3.And(counter, z3.Not(z3.Bool(x)))
    print()
    smt.add(z3.Not(counter))
    result = smt.check()
print('z3 took for tseitin', time()-t)
'''

a,b = Atom('a'),Atom('b')
