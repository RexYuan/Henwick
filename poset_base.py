from satispy import Variable
from satispy.solver import Minisat

'''
X ::= a | b | c
P ::= Ln
V ::=   X<X |
        X{X |
      P_X<X
'''

U = {'a','b','c'}
V = {}
for x in U:
    for y in U-{x}:
        V[x+'<'+y] = Variable(x+'<'+y)
        V[x+'{'+y] = Variable(x+'{'+y)
        V['L1_'+x+'<'+y] = Variable('L1_'+x+'<'+y)
        V['L2_'+x+'<'+y] = Variable('L2_'+x+'<'+y)
        V['L1_'+x+'{'+y] = Variable('L1_'+x+'{'+y)
        V['L2_'+x+'{'+y] = Variable('L2_'+x+'{'+y)
tau = Variable('dot') | -Variable('dot')
con = Variable('dot') & -Variable('dot')
sat = Minisat()

'''
----------------------------------------
ORDER RELATION AXIOM
(R)   reflexive : omitted
(ATS) antisymmetric : forall (x,y), (x<y & y<x) => x=y
                   => forall (x,y), x!=y => -(x<y & y<x)
                   => forall x!=y,  -(x<y & y<x)
(T)   transitive : forall (x,y,z), (x<y & y<z) => x<z
                => forall x!=y!=z, (x<y & y<z) => x<z

EXAMPLE : generate all order relations with universe = {a, b, c}
(ATS) -(a<b & b<a) &
      -(a<c & c<a) &
      -(b<c & c<b)
(T)   ((a<b & b<c) => a<c) &
      ((a<c & c<b) => a<b) &
      ((b<a & a<c) => b<c) &
      ((b<c & c<a) => b<a) &
      ((c<a & a<b) => c<b) &
      ((c<b & b<a) => c<a)
----------------------------------------
'''

pATS = -(V['a<b'] & V['b<a']) & -(V['a<c'] & V['c<a']) & -(V['b<c'] & V['c<b'])
pT = (((V['a<b'] & V['b<c']) >> V['a<c']) & ((V['a<c'] & V['c<b']) >> V['a<b']) &
      ((V['b<a'] & V['a<c']) >> V['b<c']) & ((V['b<c'] & V['c<a']) >> V['b<a']) &
      ((V['c<a'] & V['a<b']) >> V['c<b']) & ((V['c<b'] & V['b<a']) >> V['c<a']))
exp = pATS & pT

result = sat.solve(exp)
i = 1
print('---listing order---')
while result.success:
    print('order',i,' : ',end='')
    counter = tau
    for x in U:
        for y in U-{x}:
            if result[V[x+'<'+y]]:
                print(x+'<'+y,' ',end='')
                counter = counter & V[x+'<'+y]
            else:
                counter = counter & -V[x+'<'+y]
    exp = exp & -counter
    result = sat.solve(exp)
    i = i+1
    print()
print('---order done---\n')

'''
LINEAR ORDER AXIOM
(TO) totality : forall (x,y), (x<y | y<x)
             => forall x!=y,  (x<y | y<x)

EXAMPLE : generate all linear order relations with universe = {a, b, c}
(TO) (a<b | b<a) &
     (a<c | c<a) &
     (c<b | b<c)
'''

pTO = (V['a<b'] | V['b<a']) & (V['a<c'] | V['c<a']) & (V['c<b'] | V['b<c'])
exp = pATS & pT & pTO

result = sat.solve(exp)
i = 1
print('---listing linear order---')
while result.success:
    print('linear order',i,' : ',end='')
    counter = tau
    for x in U:
        for y in U-{x}:
            if result[V[x+'<'+y]]:
                print(x+'<'+y,' ',end='')
                counter = counter & V[x+'<'+y]
            else:
                counter = counter & -V[x+'<'+y]
    exp = exp & -counter
    result = sat.solve(exp)
    i = i+1
    print()
print('---linear order done---\n')

'''
LINEAR EXTENSION AXIOM
    Let L be a linear extension of a poset P.
(E) L extends P : forall (x,y), (x<y in P) => (x<y in L)
               => forall x!=y,  (x<y in P) => (x<y in L)

BLANKET ORDER PROBLEM
    Let Y be a set of linear orders, find a poset P such that
    every L in Y is a linear extension of P.

EXAMPLE : let L1 = abc and L2 = acb ; expected P = { a<b, a<c } | { a<b } | { a<c } | {}
(E) (a<b => (L1_a<b & L2_a<b)) &
    (a<c => (L1_a<c & L2_a<c)) &
    (b<a => (L1_b<a & L2_b<a)) &
    (b<c => (L1_b<c & L2_b<c)) &
    (c<a => (L1_c<a & L2_c<a)) &
    (c<b => (L1_c<b & L2_c<b))
(L1) L1_a<b & L1_b<c
(L2) L2_a<c & L2_c<b
'''

# L1 and L2
pL1 = V['L1_a<b'] & V['L1_b<c']
pL2 = V['L2_a<c'] & V['L2_c<b']
# L1 and L2 are themselves both posets
pATSL1 = -(V['L1_a<b'] & V['L1_b<a']) & -(V['L1_a<c'] & V['L1_c<a']) & -(V['L1_b<c'] & V['L1_c<b'])
pATSL2 = -(V['L2_a<b'] & V['L2_b<a']) & -(V['L2_a<c'] & V['L2_c<a']) & -(V['L2_b<c'] & V['L2_c<b'])
pTL1 = (((V['L1_a<b'] & V['L1_b<c']) >> V['L1_a<c']) & ((V['L1_a<c'] & V['L1_c<b']) >> V['L1_a<b']) &
        ((V['L1_b<a'] & V['L1_a<c']) >> V['L1_b<c']) & ((V['L1_b<c'] & V['L1_c<a']) >> V['L1_b<a']) &
        ((V['L1_c<a'] & V['L1_a<b']) >> V['L1_c<b']) & ((V['L1_c<b'] & V['L1_b<a']) >> V['L1_c<a']))
pTL2 = (((V['L2_a<b'] & V['L2_b<c']) >> V['L2_a<c']) & ((V['L2_a<c'] & V['L2_c<b']) >> V['L2_a<b']) &
        ((V['L2_b<a'] & V['L2_a<c']) >> V['L2_b<c']) & ((V['L2_b<c'] & V['L2_c<a']) >> V['L2_b<a']) &
        ((V['L2_c<a'] & V['L2_a<b']) >> V['L2_c<b']) & ((V['L2_c<b'] & V['L2_b<a']) >> V['L2_c<a']))
pTOL1 = (V['L1_a<b'] | V['L1_b<a']) & (V['L1_a<c'] | V['L1_c<a']) & (V['L1_c<b'] | V['L1_b<c'])
pTOL2 = (V['L2_a<b'] | V['L2_b<a']) & (V['L2_a<c'] | V['L2_c<a']) & (V['L2_c<b'] | V['L2_b<c'])
# L1 and L2 are linear extensions of P
pE = ((V['a<b'] >> (V['L1_a<b'] & V['L2_a<b'])) &
      (V['a<c'] >> (V['L1_a<c'] & V['L2_a<c'])) &
      (V['b<a'] >> (V['L1_b<a'] & V['L2_b<a'])) &
      (V['b<c'] >> (V['L1_b<c'] & V['L2_b<c'])) &
      (V['c<a'] >> (V['L1_c<a'] & V['L2_c<a'])) &
      (V['c<b'] >> (V['L1_c<b'] & V['L2_c<b'])))
exp = pATS & pATSL1 & pATSL2 & pT & pTL1 & pTL2 & pTOL1 & pTOL2 & pE & pL1 & pL2

result = sat.solve(exp)
i = 1
print('---finding blanket order for [abc, acb]---')
while result.success:
    print('blanket order',i,' : ',end='')
    counter = tau
    for x in U:
        for y in U-{x}:
            if result[V[x+'<'+y]]:
                print(x+'<'+y,' ',end='')
                counter = counter & V[x+'<'+y]
            else:
                counter = counter & -V[x+'<'+y]
    exp = exp & -counter
    result = sat.solve(exp)
    i = i+1
    print()
print('---blanket order done---\n')

'''
GENERATING ORDER PROBLEM
    Let Y be a set of linear orders, find a poset P such that
    every L in Y is a linear extension of P and that
    every L not in Y is not a linear extension of P.

CONSTRAINTS OF ABSENT LINEAR ORDER

EXAMPLE : let L1 = abc and L2 = acb ; expected P = { a<b, a<c }
          absent orders = [ bac, bca, cab, cba ]
(Abac) -((-b<a & -a<b) & (-a<c & -c<a))
(Abca) -((-b<c & -c<b) & (-c<a & -a<c))
(Acab) -((-c<a & -a<c) & (-a<b & -b<a))
(Acba) -((-c<b & -b<c) & (-b<a & -a<b))
'''

pAbac = -((-V['b<a'] & -V['a<b']) & (-V['a<c'] & -V['c<a']))
pAbca = -((-V['b<c'] & -V['c<b']) & (-V['c<a'] & -V['a<c']))
pAcab = -((-V['c<a'] & -V['a<c']) & (-V['a<b'] & -V['b<a']))
pAcba = -((-V['c<b'] & -V['b<c']) & (-V['b<a'] & -V['a<b']))

exp = pATS & pATSL1 & pATSL2 & pT & pTL1 & pTL2 & pTOL1 & pTOL2 & pE & pL1 & pL2 & pAbac & pAbca & pAcab & pAcba

result = sat.solve(exp)
i = 1
print('---finding generating order for [abc, acb]---')
while result.success:
    print('generating order',i,' : ',end='')
    counter = tau
    for x in U:
        for y in U-{x}:
            if result[V[x+'<'+y]]:
                print(x+'<'+y,' ',end='')
                counter = counter & V[x+'<'+y]
            else:
                counter = counter & -V[x+'<'+y]
    exp = exp & -counter
    result = sat.solve(exp)
    i = i+1
    print()
print('---generating order done---')











'''
----------------------------------------
COVER RELATION AXIOM
(IR) irreflexive : omitted
(AS) asymmetric : forall (x,y), x{y => -y{x
               => forall (x,y), -x{y | -y{x
               => forall x!=y,  -(x{y & y{x)
(ATS) antitransitive (w/ sym) : forall (x,y,z), (x{y & y{z) => (-x{z & -z{x)
                             => forall x!=y!=z, (x{y & y{z) => (-x{z & -z{x)
NOTE: forall x!=y!=z, x{z => -(x{y & y{z) <= this isn't enough (set x{z=F, x{y=y{z=T, -z{x is not implied)

EXAMPLE : generate all cover relations with universe = {a, b, c}
(AS) -(a{b & b{a) &
     -(a{c & c{a) &
     -(b{c & c{b)
(AT) (a{b & b{c) => (-a{c & -c{a) &
     (a{c & c{b) => (-a{b & -b{a) &
     (b{a & a{c) => (-b{c & -c{b) &
     (b{c & c{a) => (-b{a & -a{b) &
     (c{a & a{b) => (-c{b & -b{c) &
     (c{b & b{a) => (-c{a & -a{c)
----------------------------------------
'''
'''
pAS = -(V['a{b'] & V['b{a']) & -(V['a{c'] & V['c{a']) & -(V['b{c'] & V['c{b'])
pAT = (((V['a{b'] & V['b{c']) >> (-V['a{c'] & -V['c{a'])) &
       ((V['a{c'] & V['c{b']) >> (-V['a{b'] & -V['b{a'])) &
       ((V['b{a'] & V['a{c']) >> (-V['b{c'] & -V['c{b'])) &
       ((V['b{c'] & V['c{a']) >> (-V['b{a'] & -V['a{b'])) &
       ((V['c{a'] & V['a{b']) >> (-V['c{b'] & -V['b{c'])) &
       ((V['c{b'] & V['b{a']) >> (-V['c{a'] & -V['a{c'])))
exp = pAS & pAT

result = sat.solve(exp)
i = 1
while result.success:
    print('cover',i,' : ',end='')
    counter = tau
    for x in U:
        for y in U-{x}:
            if result[V[x+'{'+y]]:
                print(x+'<'+y,' ',end='')
                counter = counter & V[x+'{'+y]
            else:
                counter = counter & -V[x+'{'+y]
    exp = exp & -counter
    result = sat.solve(exp)
    i = i+1
    print()
print('cover done')
'''
'''
GENERATING POSET CONSTRAINTS
Let sequence w = (u1)(u2)(u3)...(un) be the cover sequence of the linear order L
and that L is a linear extension of a poset P.
(E) L extends P : forall (x,y), (x<y in P) => (x<y in L)
'''
