
from collections.abc import Set,Hashable
from z3 import Bool, Bools, And

class Asgmt(Set, Hashable):
    def __init__(self, supp, dime):
        self.__supp = frozenset(supp)
        self.__dime = dime
        self.__z3_mterm_form = None

    @classmethod
    def from_bit_string(cls, bs):
        supp = frozenset(i for i, x in enumerate(bs) if x == '1')
        dime = len(bs)
        return cls( supp , dime )
    
    @classmethod
    def from_z3_model(cls, md):
        raise NotImplementedError

    def to_bit_string(self):
        return repr(self)

    def to_z3_mterm_form(self):
        return And( Bools(i for i in range(self.dimension) if i in self) )

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
    if bs not in interned:
        interned[bs] = Asgmt.from_bit_string(bs)
    return interned[bs]

def mk_mterm(a):
    return mk_asgmt(a)

def mk_mterm_func(t):
    def mterm_func(a):
        return t <= a
    return mterm_func

def mk_mdnf_func(*ts):
    def mdnf_func(a):
        return any( f(a) for f in map(mk_mterm_func, ts) )
    return mdnf_func