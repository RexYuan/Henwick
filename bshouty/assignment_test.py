
from assignment import *

# 111001
a = Asgmt([0, 1, 2, 5], 6)
b = Asgmt({0, 1, 2, 5}, 6)
c = Asgmt.from_bit_string('111001')
d = make_asgmt('111001')
e = make_asgmt('111001')
assert a == b == c == d == e
assert hash(a) == hash(b) == hash(c) == hash(d) == hash(e)
assert id(d) == id(e)

a = make_asgmt('111001')
b = make_asgmt('100001')
c = make_asgmt('100001')
d = make_asgmt('001100')
assert b < a
assert b <= a
assert a > b
assert a >= b
assert b <= c
assert b >= c
assert not c <= d
assert not d <= c

a = Asgmt([0, 1, 2, 5], 6)
b = '111001'
assert list(a) == list(b)
assert len(a) == len(b)
