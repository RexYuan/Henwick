
from collections.abc import *
from typing import *
from z3 import * # type: ignore

Assignment = NewType('Assignment', int)
BitString = NewType('Bit String', str)

def asgmt_subseteq(a1 : Assignment, a2 : Assignment) -> bool:
    return (a1 & a2) == a1

def asgmt_to_bs(a : Assignment, bits : int) -> BitString:
    return bin(a)[2:].zfill(bits)

def asgmt_to_z3_term(a : Assignment, bits : int, monotone : bool = False) -> 'z3 term':
    bs = asgmt_to_bs(a, bits)
    if monotone:
        return And( [Bool(i) for i,b in enumerate(bs) if b == '1'] )
    return And( [Bool(i) if b == '1' else Not(Bool(i)) for i,b in enumerate(bs)] )

def z3_model_to_asgmt(md : 'z3 model', bits : int) -> Assignment:
    bs = "".join( ['1' if md[Bool(i)] else '0' for i in range(bits)] )
    return Assignment(int(bs, base=2))