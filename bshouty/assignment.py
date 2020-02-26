
from collections.abc import Set,Hashable

class Asgmt(Set, Hashable):
    def __init__(self, supp, dime):
        self._supp = frozenset(supp)
        self._dime = dime

    @classmethod
    def from_bit_string(cls, bs):
        supp = frozenset(i for i, x in enumerate(bs) if x == '1')
        dime = len(bs)
        return cls( supp , dime )

    @property
    def support(self):
        return self._supp

    @support.setter
    def support(self, value):
        raise TypeError

    @support.deleter
    def support(self):
        raise TypeError

    @property
    def dimension(self):
        return self._dime

    @dimension.setter
    def dimension(self, value):
        raise TypeError

    @dimension.deleter
    def dimension(self):
        raise TypeError
    
    def __repr__(self):
        return ''.join('1' if i in self.support else '0' for i in range(len(self)))

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

def make_asgmt(bs):
    if bs not in interned:
        interned[bs] = Asgmt.from_bit_string(bs)
    return interned[bs]
