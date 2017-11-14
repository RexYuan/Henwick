class formula:
    def __neg__(self):
        return Not(self)

    def __and__(self, other):
        return And(self, other)

    def __or__(self, other):
        return Or(self, other)

    def __str__(self):
        if type(self) == Atom:
            return self.name
        elif type(self) == Not:
            return '¬'+self.subf+''
        elif type(self) == And:
            return '('+self.subf1+' ∧ '+self.subf2+')'
        elif type(self) == Or:
            return '('+self.subf1+' ∨ '+self.subf2+')'

    def __repr__(self):
        if type(self) == Atom:
            return self.name
        elif type(self) == Not:
            return '-'+self.subf+''
        elif type(self) == And:
            return '('+self.subf1+' & '+self.subf2+')'
        elif type(self) == Or:
            return '('+self.subf1+' | '+self.subf2+')'

    def __add__(self, other):
        return str(self) + other

    def __radd__(self, other):
        return other + str(self)

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
            return X
        elif type(X) == Not:
            p_nX = Atom('p_'+X)
            p_X  = Atom('p_'+X.subf)
            return (p_nX | p_X) & (-p_nX | -p_X)
        elif type(X) == And:
            p_XandY = Atom('p_'+X)
            p_X     = Atom('p_'+X.subf1)
            p_Y     = Atom('p_'+X.subf2)
            return (-p_XandY | p_X) & (-p_XandY | p_Y) & (p_XandY | -p_X | -p_Y)
        elif type(X) == Or:
            p_XorY = Atom('p_'+X)
            p_X    = Atom('p_'+X.subf1)
            p_Y    = Atom('p_'+X.subf2)
            return (p_XorY | -p_X) & (p_XorY | -p_Y) & (-p_XorY | p_X | p_Y)

    def tseitin(self):
        transform = self.transform
        def helper(X):
            if type(X) == Atom:
                return X
            elif type(X) == Not:
                return transform(X) & helper(X.subf)
            elif type(X) == And:
                return transform(X) & helper(X.subf1) & helper(X.subf2)
            elif type(X) == Or:
                return transform(X) & helper(X.subf1) & helper(X.subf2)
        return Atom('p_'+self) & helper(self)

class Atom(formula):
    def __init__(self, name):
        self.name = name

class Not(formula):
    def __init__(self, subf):
        self.subf = subf

class And(formula):
    def __init__(self, subf1, subf2):
        self.subf1 = subf1
        self.subf2 = subf2

class Or(formula):
    def __init__(self, subf1, subf2):
        self.subf1 = subf1
        self.subf2 = subf2

x = Not(And(Atom('p'), Not(Atom('q'))))
print(x.tseitin())
