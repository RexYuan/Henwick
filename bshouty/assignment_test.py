
from assignment import *

# 111001
a = Asgmt([0, 1, 2, 5], 6)
b = Asgmt({0, 1, 2, 5}, 6)
c = Asgmt.from_bit_string('111001')
d = mk_asgmt('111001')
e = mk_asgmt('111001')
assert a == b == c == d == e
assert hash(a) == hash(b) == hash(c) == hash(d) == hash(e)
assert id(d) == id(e)

a = mk_asgmt('111001')
b = mk_asgmt('100001')
c = mk_asgmt('100001')
d = mk_asgmt('001100')
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
c = mk_asgmt('111001')
assert list(a) == list(b) == list(c)
assert len(a) == len(b) == len(c)

a = mk_mterm('111001')
b = mk_asgmt('111111')
c = mk_asgmt('100001')
d = mk_asgmt('000110')
e = mk_asgmt('010110')
f = mk_asgmt('111101')
fa = mk_mterm_func(a)
ad_f = mk_mdnf_func(a,d)
assert fa(b)
assert not fa(c)
assert ad_f(a)
assert ad_f(d)
assert ad_f(e)
assert ad_f(f)
assert not ad_f(c)

a = mk_mterm('111001')
af = And( Bools([0, 1, 2, 5]) )
assert a.to_z3_mterm_form() == af
