
from typing import Dict, Set, FrozenSet
Assignment = Term = FrozenSet[int]
Dnf = Set[Term]
Cdnf = Dict[Assignment, Dnf]

assignment = term = frozenset

def xor(a1 : Assignment, a2 : Assignment):
    '''
    """Bit-wise XOR on bit strings."""
    '''
    pass