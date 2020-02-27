
from collections.abc import Set,Hashable
from z3 import Bool, Bools, And

class Asgmt(Set, Hashable):
    """Immutable representation of an assignment or a term(elementary conjunction)."""
    def __init__(self, supp, dime):
        """Instantiation by support and dimension.

        >>> Asgmt([0, 1, 2, 5], 6)
        111001
        """
        self.__supp = frozenset(supp)
        self.__dime = dime
        self.__z3_mterm_form = None

    @classmethod
    def from_bit_string(cls, bs):
        """Instantiation by a bit string.

        >>> Asgmt.from_bit_string('111001')
        111001
        """
        supp = frozenset(i for i, x in enumerate(bs) if x == '1')
        dime = len(bs)
        return cls(supp, dime)
    
    @classmethod
    def from_z3_model(cls, md):
        """Instantiation by a z3 model.

        >>> s = Solver()
        >>> s.check(Bool(0), Bool(1), Bool(2), Not(Bool(3)), Not(Bool(4)), Bool(5))
        >>> Asgmt.from_z3_model(s.model())                                                                                                                    
        111001
        """
        supp = frozenset(i for i in range(len(md)) if md[Bool(i)])
        dime = len(md)
        return cls(supp, dime)

    def to_bit_string(self):
        """Return a bit string representation of self.

        >>> Asgmt.from_bit_string('111001').to_bit_string()
        '111001'
        """
        return repr(self)

    def to_z3_mterm_form(self):
        """Return a monotonized z3 term representation of self.

        >>> Asgmt.from_bit_string('111001').to_z3_mterm_form()
        And(k!0, k!1, k!2, k!5)
        """
        return And( Bools(i for i in range(self.dimension) if i in self) )

    def flip(self, ind):
        """Return an assignment with the value of the ind-th variable flipped.

        >>> Asgmt.from_bit_string('111001').flip(1).flip(3)
        101101
        """
        return Asgmt(self.support ^ {ind}, self.dimension)

    @property
    def support(self):
        return self.__supp

    @support.setter
    def support(self, value):
        raise TypeError

    @support.deleter
    def support(self):
        raise TypeError

    @property
    def dimension(self):
        return self.__dime

    @dimension.setter
    def dimension(self, value):
        raise TypeError

    @dimension.deleter
    def dimension(self):
        raise TypeError

    def __repr__(self):
        return ''.join(iter(self))

    def __hash__(self):
        return Set._hash(self.support)
    
    def __iter__(self):
        for i in range(self.dimension):
            if i in self.support:
                yield '1'
            else:
                yield '0'

    def __contains__(self, ind):
        return ind in self.support
    
    def __getitem__(self, ind):
        return ind in self

    def __len__(self):
        return self.dimension

    def __eq__(self, asgmt2):
        if self.dimension != asgmt2.dimension:
            return False
        return hash(self) == hash(asgmt2)
    
    def __and__(self, asgmt2):
        return Asgmt(self.support & asgmt2.support, self.dimension)
 
    def __or__(self, asgmt2):
        return Asgmt(self.support | asgmt2.support, self.dimension)

    def __xor__(self, asgmt2):
        return Asgmt(self.support ^ asgmt2.support, self.dimension)

    def __ge__(self, asgmt2):
        return self.support >= asgmt2.support

    def __gt__(self, asgmt2):
        return self.support > asgmt2.support

    def __le__(self, asgmt2):
        return self.support <= asgmt2.support

    def __lt__(self, asgmt2):
        return self.support < asgmt2.support

interned = dict()

def mk_asgmt(bs):
    """Bit string constructor of interned assignments."""
    if bs not in interned:
        interned[bs] = Asgmt.from_bit_string(bs)
    return interned[bs]

def mk_mterm(a):
    return mk_asgmt(a)

def mk_mterm_func(t):
    """Return a function that evaluates assignments againsts term t."""
    def mterm_func(a):
        return t <= a
    return mterm_func

def mk_mdnf_func(*ts):
    """Return a function that evaluates assignments againsts dnf of terms ts."""
    def mdnf_func(a):
        return any( f(a) for f in map(mk_mterm_func, ts) )
    return mdnf_func
