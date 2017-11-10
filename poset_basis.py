from satispy import Variable
from satispy.solver import Minisat

'''
-------------------------------------------------------------------------------
Variables for example:
X ::= a | b | c
P ::= Labc | Lacb | Lcab | Lcba | P1 | P2
V ::= X<X |
      X{X |
      P_X<X |
      P_X{X
-------------------------------------------------------------------------------
'''

U = {'a','b','c'}
V = {}
for x in U:
    for y in U-{x}:
        V[x+'<'+y] = Variable(x+'<'+y)
        V[x+'{'+y] = Variable(x+'{'+y)
        V['Labc_'+x+'<'+y] = Variable('Labc_'+x+'<'+y)
        V['Lacb_'+x+'<'+y] = Variable('Lacb_'+x+'<'+y)
        V['Lcab_'+x+'<'+y] = Variable('Lcab_'+x+'<'+y)
        V['Lcba_'+x+'<'+y] = Variable('Lcba_'+x+'<'+y)
        V['P1_'+x+'<'+y] = Variable('P1_'+x+'<'+y)
        V['P2_'+x+'<'+y] = Variable('P2_'+x+'<'+y)
        V['Labc_'+x+'{'+y] = Variable('Labc_'+x+'{'+y)
        V['Lacb_'+x+'{'+y] = Variable('Lacb_'+x+'{'+y)
        V['Lcab_'+x+'{'+y] = Variable('Lcab_'+x+'{'+y)
        V['Lcba_'+x+'{'+y] = Variable('Lcba_'+x+'{'+y)
        V['P1_'+x+'{'+y] = Variable('P1_'+x+'{'+y)
        V['P2_'+x+'{'+y] = Variable('P2_'+x+'{'+y)
tau = Variable('dot') | -Variable('dot')
con = Variable('dot') & -Variable('dot')
sat = Minisat()

'''
-------------------------------------------------------------------------------
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
-------------------------------------------------------------------------------
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
-------------------------------------------------------------------------------
COVER RELATION AXIOM
(IR) irreflexive : omitted
(AS) asymmetric : forall (x,y), x{y => -y{x
               => forall (x,y), -x{y | -y{x
               => forall x!=y,  -(x{y & y{x)
(ATT) antitransitive (w/ sym) : forall (x,y,z), (x{y & y{z) => (-x{z & -z{x)
                             => forall x!=y!=z, (x{y & y{z) => (-x{z & -z{x)
NOTE: forall x!=y!=z, x{z => -(x{y & y{z) is entailed by ATS
(CO) relation between cover and order : forall (x,y), x{y => x<y
                                     => forall x!=y,  x{y => x<y

EXAMPLE : generate all cover relations with universe = {a, b, c}
(AS) -(a{b & b{a) &
     -(a{c & c{a) &
     -(b{c & c{b)
(ATT) (a{b & b{c) => (-a{c & -c{a) &
      (a{c & c{b) => (-a{b & -b{a) &
      (b{a & a{c) => (-b{c & -c{b) &
      (b{c & c{a) => (-b{a & -a{b) &
      (c{a & a{b) => (-c{b & -b{c) &
      (c{b & b{a) => (-c{a & -a{c)
(CO) (a{b => a<b) &
     (a{c => a<c) &
     (b{a => b<a) &
     (b{c => b<c) &
     (c{a => c<a) &
     (c{b => c<b)
-------------------------------------------------------------------------------
'''

pAS = -(V['a{b'] & V['b{a']) & -(V['a{c'] & V['c{a']) & -(V['b{c'] & V['c{b'])
pATT = (((V['a{b'] & V['b{c']) >> (-V['a{c'] & -V['c{a'])) &
        ((V['a{c'] & V['c{b']) >> (-V['a{b'] & -V['b{a'])) &
        ((V['b{a'] & V['a{c']) >> (-V['b{c'] & -V['c{b'])) &
        ((V['b{c'] & V['c{a']) >> (-V['b{a'] & -V['a{b'])) &
        ((V['c{a'] & V['a{b']) >> (-V['c{b'] & -V['b{c'])) &
        ((V['c{b'] & V['b{a']) >> (-V['c{a'] & -V['a{c'])))
pCO = ((V['a{b'] >> V['a<b']) &
       (V['a{c'] >> V['a<c']) &
       (V['b{a'] >> V['b<a']) &
       (V['b{c'] >> V['b<c']) &
       (V['c{a'] >> V['c<a']) &
       (V['c{b'] >> V['c<b']))
exp = pAS & pATT & pCO

result = sat.solve(exp)
i = 1
print('---listing cover---')
while result.success:
    print('cover',i,' : ',end='')
    counter = tau
    for x in U:
        for y in U-{x}:
            if result[V[x+'{'+y]]:
                print(x+'{'+y,' ',end='')
                counter = counter & V[x+'{'+y]
            else:
                counter = counter & -V[x+'{'+y]
    exp = exp & -counter
    result = sat.solve(exp)
    i = i+1
    print()
print('---cover done---\n')

'''
-------------------------------------------------------------------------------
LINEAR ORDER AXIOM
(TO) totality : forall (x,y), (x<y | y<x)
             => forall x!=y,  (x<y | y<x)

EXAMPLE : generate all linear order relations with universe = {a, b, c}
(TO) (a<b | b<a) &
     (a<c | c<a) &
     (c<b | b<c)
-------------------------------------------------------------------------------
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
-------------------------------------------------------------------------------
LINEAR EXTENSION AXIOM
    Let L be a linear extension of a poset P.
(E) L extends P : forall (x,y), (x<y in P) => (x<y in L)
               => forall x!=y,  (x<y in P) => (x<y in L)

SINGLE BLANKET ORDER PROBLEM
    Let Y be a set of linear orders, find a poset P such that
    every L in Y is a linear extension of P.

CONSTRAINT OF PRESENT ORDER
    For every linear order L in Y, since we know cover implies order,
    totality and transitivity are ensured, and we also know that, if L extends
    P, we can set the case for L and the constraints on P will follow from the
    axiom of order extension. The constraints of a given L that should be
    blanketed by P is, simply, forall x.y in w, Lw_x{y.
(Lw) w in L(P) |= (forall x.y in w, Lw_x{y)

EXAMPLE : let Labc = abc and Lacb = acb ; expected P = { a<b, a<c } | { a<b } | { a<c } | {}
(E) (a<b => (Labc_a<b & Lacb_a<b)) &
    (a<c => (Labc_a<c & Lacb_a<c)) &
    (b<a => (Labc_b<a & Lacb_b<a)) &
    (b<c => (Labc_b<c & Lacb_b<c)) &
    (c<a => (Labc_c<a & Lacb_c<a)) &
    (c<b => (Labc_c<b & Lacb_c<b))
(Labc) Labc_a{b & Labc_b{c
(Lacb) Lacb_a{c & Lacb_c{b
-------------------------------------------------------------------------------
'''

# Labc and Lacb
pLabc = V['Labc_a{b'] & V['Labc_b{c']
pLacb = V['Lacb_a{c'] & V['Lacb_c{b']
# Labc and Lacb are themselves both posets
pLabc_ATS = (-(V['Labc_a<b'] & V['Labc_b<a']) &
             -(V['Labc_a<c'] & V['Labc_c<a']) &
             -(V['Labc_b<c'] & V['Labc_c<b']))
pLacb_ATS = (-(V['Lacb_a<b'] & V['Lacb_b<a']) &
             -(V['Lacb_a<c'] & V['Lacb_c<a']) &
             -(V['Lacb_b<c'] & V['Lacb_c<b']))
pLabc_T = (((V['Labc_a<b'] & V['Labc_b<c']) >> V['Labc_a<c']) &
           ((V['Labc_a<c'] & V['Labc_c<b']) >> V['Labc_a<b']) &
           ((V['Labc_b<a'] & V['Labc_a<c']) >> V['Labc_b<c']) &
           ((V['Labc_b<c'] & V['Labc_c<a']) >> V['Labc_b<a']) &
           ((V['Labc_c<a'] & V['Labc_a<b']) >> V['Labc_c<b']) &
           ((V['Labc_c<b'] & V['Labc_b<a']) >> V['Labc_c<a']))
pLacb_T = (((V['Lacb_a<b'] & V['Lacb_b<c']) >> V['Lacb_a<c']) &
           ((V['Lacb_a<c'] & V['Lacb_c<b']) >> V['Lacb_a<b']) &
           ((V['Lacb_b<a'] & V['Lacb_a<c']) >> V['Lacb_b<c']) &
           ((V['Lacb_b<c'] & V['Lacb_c<a']) >> V['Lacb_b<a']) &
           ((V['Lacb_c<a'] & V['Lacb_a<b']) >> V['Lacb_c<b']) &
           ((V['Lacb_c<b'] & V['Lacb_b<a']) >> V['Lacb_c<a']))
pLabc_TO = ((V['Labc_a<b'] | V['Labc_b<a']) &
            (V['Labc_a<c'] | V['Labc_c<a']) &
            (V['Labc_c<b'] | V['Labc_b<c']))
pLacb_TO = ((V['Lacb_a<b'] | V['Lacb_b<a']) &
            (V['Lacb_a<c'] | V['Lacb_c<a']) &
            (V['Lacb_c<b'] | V['Lacb_b<c']))
pLabc_AS = (-(V['Labc_a{b'] & V['Labc_b{a']) &
            -(V['Labc_a{c'] & V['Labc_c{a']) &
            -(V['Labc_b{c'] & V['Labc_c{b']))
pLacb_AS = (-(V['Lacb_a{b'] & V['Lacb_b{a']) &
            -(V['Lacb_a{c'] & V['Lacb_c{a']) &
            -(V['Lacb_b{c'] & V['Lacb_c{b']))
pLabc_ATT = (((V['Labc_a{b'] & V['Labc_b{c']) >> (-V['Labc_a{c'] & -V['Labc_c{a'])) &
             ((V['Labc_a{c'] & V['Labc_c{b']) >> (-V['Labc_a{b'] & -V['Labc_b{a'])) &
             ((V['Labc_b{a'] & V['Labc_a{c']) >> (-V['Labc_b{c'] & -V['Labc_c{b'])) &
             ((V['Labc_b{c'] & V['Labc_c{a']) >> (-V['Labc_b{a'] & -V['Labc_a{b'])) &
             ((V['Labc_c{a'] & V['Labc_a{b']) >> (-V['Labc_c{b'] & -V['Labc_b{c'])) &
             ((V['Labc_c{b'] & V['Labc_b{a']) >> (-V['Labc_c{a'] & -V['Labc_a{c'])))
pLacb_ATT = (((V['Lacb_a{b'] & V['Lacb_b{c']) >> (-V['Lacb_a{c'] & -V['Lacb_c{a'])) &
             ((V['Lacb_a{c'] & V['Lacb_c{b']) >> (-V['Lacb_a{b'] & -V['Lacb_b{a'])) &
             ((V['Lacb_b{a'] & V['Lacb_a{c']) >> (-V['Lacb_b{c'] & -V['Lacb_c{b'])) &
             ((V['Lacb_b{c'] & V['Lacb_c{a']) >> (-V['Lacb_b{a'] & -V['Lacb_a{b'])) &
             ((V['Lacb_c{a'] & V['Lacb_a{b']) >> (-V['Lacb_c{b'] & -V['Lacb_b{c'])) &
             ((V['Lacb_c{b'] & V['Lacb_b{a']) >> (-V['Lacb_c{a'] & -V['Lacb_a{c'])))
pLabc_CO = ((V['Labc_a{b'] >> V['Labc_a<b']) &
            (V['Labc_a{c'] >> V['Labc_a<c']) &
            (V['Labc_b{a'] >> V['Labc_b<a']) &
            (V['Labc_b{c'] >> V['Labc_b<c']) &
            (V['Labc_c{a'] >> V['Labc_c<a']) &
            (V['Labc_c{b'] >> V['Labc_c<b']))
pLacb_CO = ((V['Lacb_a{b'] >> V['Lacb_a<b']) &
            (V['Lacb_a{c'] >> V['Lacb_a<c']) &
            (V['Lacb_b{a'] >> V['Lacb_b<a']) &
            (V['Lacb_b{c'] >> V['Lacb_b<c']) &
            (V['Lacb_c{a'] >> V['Lacb_c<a']) &
            (V['Lacb_c{b'] >> V['Lacb_c<b']))
# Labc and Lacb are linear extensions of P
pE = ((V['a<b'] >> (V['Labc_a<b'] & V['Lacb_a<b'])) &
      (V['a<c'] >> (V['Labc_a<c'] & V['Lacb_a<c'])) &
      (V['b<a'] >> (V['Labc_b<a'] & V['Lacb_b<a'])) &
      (V['b<c'] >> (V['Labc_b<c'] & V['Lacb_b<c'])) &
      (V['c<a'] >> (V['Labc_c<a'] & V['Lacb_c<a'])) &
      (V['c<b'] >> (V['Labc_c<b'] & V['Lacb_c<b'])))
exp = (pATS & pT & pAS & pATT & pCO & pE &
       pLabc & pLabc_ATS & pLabc_T & pLabc_TO & pLabc_AS & pLabc_ATT & pLabc_CO &
       pLacb & pLacb_ATS & pLacb_T & pLacb_TO & pLacb_AS & pLacb_ATT & pLacb_CO)

result = sat.solve(exp)
i = 1
print('---finding single blanket order for [abc, acb]---')
while result.success:
    print('sblanket order',i,' : ',end='')
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
print('---single blanket order done---\n')

'''
-------------------------------------------------------------------------------
SINGLE COVER ORDER PROBLEM
    Let Y be a set of linear orders, find a poset P such that
    every L in Y is a linear extension of P and that every L
    not in Y is not a linear extension of P.
    That is, find the strictest single poset P that blankets Y.

CONSTRAINT OF ABSENT ORDER
(Aw) w not in L(P) =||= (exist (x,y), Lw_x<y & y<x)
                   => (exist x.*y in w, y<x)

EXAMPLE : let Labc = abc and Lacb = acb ; expected P = { a<b, a<c }
          absent orders = [ bac, bca, cab, cba ]
(Abac) a<b | c<b | c<a
(Abca) c<b | a<b | a<c
(Acab) a<c | b<c | b<a
(Acba) b<c | a<c | a<b

NOTE: comparability and incomparability are both intransitive.
-------------------------------------------------------------------------------
'''

pAbac = V['a<b'] | V['c<b'] | V['c<a']
pAbca = V['c<b'] | V['a<b'] | V['a<c']
pAcab = V['a<c'] | V['b<c'] | V['b<a']
pAcba = V['b<c'] | V['a<c'] | V['a<b']

exp = (pATS & pT & pAS & pATT & pCO & pE &
       pLabc & pLabc_ATS & pLabc_T & pLabc_TO & pLabc_AS & pLabc_ATT & pLabc_CO &
       pLacb & pLacb_ATS & pLacb_T & pLacb_TO & pLacb_AS & pLacb_ATT & pLacb_CO &
       pAbac & pAbca & pAcab & pAcba)

result = sat.solve(exp)
i = 1
print('---finding single cover order for [abc, acb]---')
while result.success:
    print('scover order',i,' : ',end='')
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
print('---single cover order done---\n')

# With these naive SAT constraints, the complexity is bad because:
#     1) must use every permutation : O( |U|! )
#     2) for absent permutation, must use every ui,uj such that i<j : O( |U|^2 )

# TODO possible improvement 1: find the equivalence condition for present order
# like we did for absent order, so that we don't need to build an extra poset
# for every present order.
# TODO possible improvement 2: use cover relation to reduce number of clauses
# TODO possible improvement 3: use automaton to reduce number of clauses

'''
EXTRA VARIABLES AXIOMS
'''

pLcab_ATS = (-(V['Lcab_a<b'] & V['Lcab_b<a']) &
             -(V['Lcab_a<c'] & V['Lcab_c<a']) &
             -(V['Lcab_b<c'] & V['Lcab_c<b']))
pLcab_T = (((V['Lcab_a<b'] & V['Lcab_b<c']) >> V['Lcab_a<c']) &
           ((V['Lcab_a<c'] & V['Lcab_c<b']) >> V['Lcab_a<b']) &
           ((V['Lcab_b<a'] & V['Lcab_a<c']) >> V['Lcab_b<c']) &
           ((V['Lcab_b<c'] & V['Lcab_c<a']) >> V['Lcab_b<a']) &
           ((V['Lcab_c<a'] & V['Lcab_a<b']) >> V['Lcab_c<b']) &
           ((V['Lcab_c<b'] & V['Lcab_b<a']) >> V['Lcab_c<a']))
pLcab_TO = ((V['Lcab_a<b'] | V['Lcab_b<a']) &
            (V['Lcab_a<c'] | V['Lcab_c<a']) &
            (V['Lcab_c<b'] | V['Lcab_b<c']))
pLcab_AS = (-(V['Lcab_a{b'] & V['Lcab_b{a']) &
            -(V['Lcab_a{c'] & V['Lcab_c{a']) &
            -(V['Lcab_b{c'] & V['Lcab_c{b']))
pLcab_ATT = (((V['Lcab_a{b'] & V['Lcab_b{c']) >> (-V['Lcab_a{c'] & -V['Lcab_c{a'])) &
             ((V['Lcab_a{c'] & V['Lcab_c{b']) >> (-V['Lcab_a{b'] & -V['Lcab_b{a'])) &
             ((V['Lcab_b{a'] & V['Lcab_a{c']) >> (-V['Lcab_b{c'] & -V['Lcab_c{b'])) &
             ((V['Lcab_b{c'] & V['Lcab_c{a']) >> (-V['Lcab_b{a'] & -V['Lcab_a{b'])) &
             ((V['Lcab_c{a'] & V['Lcab_a{b']) >> (-V['Lcab_c{b'] & -V['Lcab_b{c'])) &
             ((V['Lcab_c{b'] & V['Lcab_b{a']) >> (-V['Lcab_c{a'] & -V['Lcab_a{c'])))
pLcab_CO = ((V['Lcab_a{b'] >> V['Lcab_a<b']) &
            (V['Lcab_a{c'] >> V['Lcab_a<c']) &
            (V['Lcab_b{a'] >> V['Lcab_b<a']) &
            (V['Lcab_b{c'] >> V['Lcab_b<c']) &
            (V['Lcab_c{a'] >> V['Lcab_c<a']) &
            (V['Lcab_c{b'] >> V['Lcab_c<b']))
pLcba_ATS = (-(V['Lcba_a<b'] & V['Lcba_b<a']) &
             -(V['Lcba_a<c'] & V['Lcba_c<a']) &
             -(V['Lcba_b<c'] & V['Lcba_c<b']))
pLcba_T = (((V['Lcba_a<b'] & V['Lcba_b<c']) >> V['Lcba_a<c']) &
           ((V['Lcba_a<c'] & V['Lcba_c<b']) >> V['Lcba_a<b']) &
           ((V['Lcba_b<a'] & V['Lcba_a<c']) >> V['Lcba_b<c']) &
           ((V['Lcba_b<c'] & V['Lcba_c<a']) >> V['Lcba_b<a']) &
           ((V['Lcba_c<a'] & V['Lcba_a<b']) >> V['Lcba_c<b']) &
           ((V['Lcba_c<b'] & V['Lcba_b<a']) >> V['Lcba_c<a']))
pLcba_TO = ((V['Lcba_a<b'] | V['Lcba_b<a']) &
            (V['Lcba_a<c'] | V['Lcba_c<a']) &
            (V['Lcba_c<b'] | V['Lcba_b<c']))
pLcba_AS = (-(V['Lcba_a{b'] & V['Lcba_b{a']) &
            -(V['Lcba_a{c'] & V['Lcba_c{a']) &
            -(V['Lcba_b{c'] & V['Lcba_c{b']))
pLcba_ATT = (((V['Lcba_a{b'] & V['Lcba_b{c']) >> (-V['Lcba_a{c'] & -V['Lcba_c{a'])) &
             ((V['Lcba_a{c'] & V['Lcba_c{b']) >> (-V['Lcba_a{b'] & -V['Lcba_b{a'])) &
             ((V['Lcba_b{a'] & V['Lcba_a{c']) >> (-V['Lcba_b{c'] & -V['Lcba_c{b'])) &
             ((V['Lcba_b{c'] & V['Lcba_c{a']) >> (-V['Lcba_b{a'] & -V['Lcba_a{b'])) &
             ((V['Lcba_c{a'] & V['Lcba_a{b']) >> (-V['Lcba_c{b'] & -V['Lcba_b{c'])) &
             ((V['Lcba_c{b'] & V['Lcba_b{a']) >> (-V['Lcba_c{a'] & -V['Lcba_a{c'])))
pLcba_CO = ((V['Lcba_a{b'] >> V['Lcba_a<b']) &
            (V['Lcba_a{c'] >> V['Lcba_a<c']) &
            (V['Lcba_b{a'] >> V['Lcba_b<a']) &
            (V['Lcba_b{c'] >> V['Lcba_b<c']) &
            (V['Lcba_c{a'] >> V['Lcba_c<a']) &
            (V['Lcba_c{b'] >> V['Lcba_c<b']))
pP1_ATS = (-(V['P1_a<b'] & V['P1_b<a']) &
           -(V['P1_a<c'] & V['P1_c<a']) &
           -(V['P1_b<c'] & V['P1_c<b']))
pP1_T = (((V['P1_a<b'] & V['P1_b<c']) >> V['P1_a<c']) &
         ((V['P1_a<c'] & V['P1_c<b']) >> V['P1_a<b']) &
         ((V['P1_b<a'] & V['P1_a<c']) >> V['P1_b<c']) &
         ((V['P1_b<c'] & V['P1_c<a']) >> V['P1_b<a']) &
         ((V['P1_c<a'] & V['P1_a<b']) >> V['P1_c<b']) &
         ((V['P1_c<b'] & V['P1_b<a']) >> V['P1_c<a']))
pP1_TO = ((V['P1_a<b'] | V['P1_b<a']) &
          (V['P1_a<c'] | V['P1_c<a']) &
          (V['P1_c<b'] | V['P1_b<c']))
pP1_AS = (-(V['P1_a{b'] & V['P1_b{a']) &
          -(V['P1_a{c'] & V['P1_c{a']) &
          -(V['P1_b{c'] & V['P1_c{b']))
pP1_ATT = (((V['P1_a{b'] & V['P1_b{c']) >> (-V['P1_a{c'] & -V['P1_c{a'])) &
           ((V['P1_a{c'] & V['P1_c{b']) >> (-V['P1_a{b'] & -V['P1_b{a'])) &
           ((V['P1_b{a'] & V['P1_a{c']) >> (-V['P1_b{c'] & -V['P1_c{b'])) &
           ((V['P1_b{c'] & V['P1_c{a']) >> (-V['P1_b{a'] & -V['P1_a{b'])) &
           ((V['P1_c{a'] & V['P1_a{b']) >> (-V['P1_c{b'] & -V['P1_b{c'])) &
           ((V['P1_c{b'] & V['P1_b{a']) >> (-V['P1_c{a'] & -V['P1_a{c'])))
pP1_CO = ((V['P1_a{b'] >> V['P1_a<b']) &
          (V['P1_a{c'] >> V['P1_a<c']) &
          (V['P1_b{a'] >> V['P1_b<a']) &
          (V['P1_b{c'] >> V['P1_b<c']) &
          (V['P1_c{a'] >> V['P1_c<a']) &
          (V['P1_c{b'] >> V['P1_c<b']))
pP2_ATS = (-(V['P2_a<b'] & V['P2_b<a']) &
           -(V['P2_a<c'] & V['P2_c<a']) &
           -(V['P2_b<c'] & V['P2_c<b']))
pP2_T = (((V['P2_a<b'] & V['P2_b<c']) >> V['P2_a<c']) &
         ((V['P2_a<c'] & V['P2_c<b']) >> V['P2_a<b']) &
         ((V['P2_b<a'] & V['P2_a<c']) >> V['P2_b<c']) &
         ((V['P2_b<c'] & V['P2_c<a']) >> V['P2_b<a']) &
         ((V['P2_c<a'] & V['P2_a<b']) >> V['P2_c<b']) &
         ((V['P2_c<b'] & V['P2_b<a']) >> V['P2_c<a']))
pP2_TO = ((V['P2_a<b'] | V['P2_b<a']) &
          (V['P2_a<c'] | V['P2_c<a']) &
          (V['P2_c<b'] | V['P2_b<c']))
pP2_AS = (-(V['P2_a{b'] & V['P2_b{a']) &
          -(V['P2_a{c'] & V['P2_c{a']) &
          -(V['P2_b{c'] & V['P2_c{b']))
pP2_ATT = (((V['P2_a{b'] & V['P2_b{c']) >> (-V['P2_a{c'] & -V['P2_c{a'])) &
           ((V['P2_a{c'] & V['P2_c{b']) >> (-V['P2_a{b'] & -V['P2_b{a'])) &
           ((V['P2_b{a'] & V['P2_a{c']) >> (-V['P2_b{c'] & -V['P2_c{b'])) &
           ((V['P2_b{c'] & V['P2_c{a']) >> (-V['P2_b{a'] & -V['P2_a{b'])) &
           ((V['P2_c{a'] & V['P2_a{b']) >> (-V['P2_c{b'] & -V['P2_b{c'])) &
           ((V['P2_c{b'] & V['P2_b{a']) >> (-V['P2_c{a'] & -V['P2_a{c'])))
pP2_CO = ((V['P2_a{b'] >> V['P2_a<b']) &
          (V['P2_a{c'] >> V['P2_a<c']) &
          (V['P2_b{a'] >> V['P2_b<a']) &
          (V['P2_b{c'] >> V['P2_b<c']) &
          (V['P2_c{a'] >> V['P2_c<a']) &
          (V['P2_c{b'] >> V['P2_c<b']))

'''
-------------------------------------------------------------------------------
MULTIPLE BLANKET ORDER PROBLEM
    Let Y be a set of linear orders, find a set of poset Ps such that
    every L in Y is a linear extension of some poset P in Ps.

CONSTRAINT OF PRESENT ORDER
(Lw) (forall x.y in w, Lw_x{y)
(E) forall L, exists P in Ps, L extends P

EXAMPLE : for { abc, acb, cab, cba } ;
          expected Ps = { {a<b, a<c}, {c<b, c<a} } |
                        { {a<b, a<c}, {c<b     } } |
                        { {a<b, a<c}, {     c<a} } |
                        { {a<b, a<c}, {        } } |
                        ...
(E) (((P1_a<b => (Labc_a<b)) &
      (P1_a<c => (Labc_a<c)) &
      (P1_b<a => (Labc_b<a)) &
      (P1_b<c => (Labc_b<c)) &
      (P1_c<a => (Labc_c<a)) &
      (P1_c<b => (Labc_c<b))) |
     ((P1_a<b => (Labc_a<b)) &
      (P2_a<c => (Labc_a<c)) &
      (P2_b<a => (Labc_b<a)) &
      (P2_b<c => (Labc_b<c)) &
      (P2_c<a => (Labc_c<a)) &
      (P2_c<b => (Labc_c<b)))) &
    (((P1_a<b => (Lacb_a<b)) &
      (P1_a<c => (Lacb_a<c)) &
      (P1_b<a => (Lacb_b<a)) &
      (P1_b<c => (Lacb_b<c)) &
      (P1_c<a => (Lacb_c<a)) &
      (P1_c<b => (Lacb_c<b))) |
     ((P1_a<b => (Lacb_a<b)) &
      (P2_a<c => (Lacb_a<c)) &
      (P2_b<a => (Lacb_b<a)) &
      (P2_b<c => (Lacb_b<c)) &
      (P2_c<a => (Lacb_c<a)) &
      (P2_c<b => (Lacb_c<b)))) &
    (((P1_a<b => (Lcab_a<b)) &
      (P1_a<c => (Lcab_a<c)) &
      (P1_b<a => (Lcab_b<a)) &
      (P1_b<c => (Lcab_b<c)) &
      (P1_c<a => (Lcab_c<a)) &
      (P1_c<b => (Lcab_c<b))) |
     ((P1_a<b => (Lcab_a<b)) &
      (P2_a<c => (Lcab_a<c)) &
      (P2_b<a => (Lcab_b<a)) &
      (P2_b<c => (Lcab_b<c)) &
      (P2_c<a => (Lcab_c<a)) &
      (P2_c<b => (Lcab_c<b))))
    (((P1_a<b => (Lcba_a<b)) &
      (P1_a<c => (Lcba_a<c)) &
      (P1_b<a => (Lcba_b<a)) &
      (P1_b<c => (Lcba_b<c)) &
      (P1_c<a => (Lcba_c<a)) &
      (P1_c<b => (Lcba_c<b))) |
     ((P1_a<b => (Lcba_a<b)) &
      (P2_a<c => (Lcba_a<c)) &
      (P2_b<a => (Lcba_b<a)) &
      (P2_b<c => (Lcba_b<c)) &
      (P2_c<a => (Lcba_c<a)) &
      (P2_c<b => (Lcba_c<b))))
(Labc) Labc_a{b & Labc_b{c
(Lacb) Lacb_a{c & Lacb_c{b
(Lcab) Lcab_c{a & Labc_a{b
(Lcba) Lcba_c{b & Lacb_b{a
-------------------------------------------------------------------------------
'''

pLabc = V['Labc_a{b'] & V['Labc_b{c']
pLacb = V['Lacb_a{c'] & V['Lacb_c{b']
pLcab = V['Lcab_c{a'] & V['Lcab_a{b']
pLcba = V['Lcba_c{b'] & V['Lcba_b{a']

pE = ((((V['P1_a<b'] >> (V['Labc_a<b'])) &
        (V['P1_a<c'] >> (V['Labc_a<c'])) &
        (V['P1_b<a'] >> (V['Labc_b<a'])) &
        (V['P1_b<c'] >> (V['Labc_b<c'])) &
        (V['P1_c<a'] >> (V['Labc_c<a'])) &
        (V['P1_c<b'] >> (V['Labc_c<b']))) |
       ((V['P2_a<b'] >> (V['Labc_a<b'])) &
        (V['P2_a<c'] >> (V['Labc_a<c'])) &
        (V['P2_b<a'] >> (V['Labc_b<a'])) &
        (V['P2_b<c'] >> (V['Labc_b<c'])) &
        (V['P2_c<a'] >> (V['Labc_c<a'])) &
        (V['P2_c<b'] >> (V['Labc_c<b'])))) &
      (((V['P1_a<b'] >> (V['Lacb_a<b'])) &
        (V['P1_a<c'] >> (V['Lacb_a<c'])) &
        (V['P1_b<a'] >> (V['Lacb_b<a'])) &
        (V['P1_b<c'] >> (V['Lacb_b<c'])) &
        (V['P1_c<a'] >> (V['Lacb_c<a'])) &
        (V['P1_c<b'] >> (V['Lacb_c<b']))) |
       ((V['P2_a<b'] >> (V['Lacb_a<b'])) &
        (V['P2_a<c'] >> (V['Lacb_a<c'])) &
        (V['P2_b<a'] >> (V['Lacb_b<a'])) &
        (V['P2_b<c'] >> (V['Lacb_b<c'])) &
        (V['P2_c<a'] >> (V['Lacb_c<a'])) &
        (V['P2_c<b'] >> (V['Lacb_c<b'])))) &
      (((V['P1_a<b'] >> (V['Lcab_a<b'])) &
        (V['P1_a<c'] >> (V['Lcab_a<c'])) &
        (V['P1_b<a'] >> (V['Lcab_b<a'])) &
        (V['P1_b<c'] >> (V['Lcab_b<c'])) &
        (V['P1_c<a'] >> (V['Lcab_c<a'])) &
        (V['P1_c<b'] >> (V['Lcab_c<b']))) |
       ((V['P2_a<b'] >> (V['Lcab_a<b'])) &
        (V['P2_a<c'] >> (V['Lcab_a<c'])) &
        (V['P2_b<a'] >> (V['Lcab_b<a'])) &
        (V['P2_b<c'] >> (V['Lcab_b<c'])) &
        (V['P2_c<a'] >> (V['Lcab_c<a'])) &
        (V['P2_c<b'] >> (V['Lcab_c<b'])))) &
      (((V['P1_a<b'] >> (V['Lcba_a<b'])) &
        (V['P1_a<c'] >> (V['Lcba_a<c'])) &
        (V['P1_b<a'] >> (V['Lcba_b<a'])) &
        (V['P1_b<c'] >> (V['Lcba_b<c'])) &
        (V['P1_c<a'] >> (V['Lcba_c<a'])) &
        (V['P1_c<b'] >> (V['Lcba_c<b']))) |
       ((V['P2_a<b'] >> (V['Lcba_a<b'])) &
        (V['P2_a<c'] >> (V['Lcba_a<c'])) &
        (V['P2_b<a'] >> (V['Lcba_b<a'])) &
        (V['P2_b<c'] >> (V['Lcba_b<c'])) &
        (V['P2_c<a'] >> (V['Lcba_c<a'])) &
        (V['P2_c<b'] >> (V['Lcba_c<b'])))))

exp = (pP1_ATS & pP1_T & pP1_AS & pP1_ATT & pP1_CO &
       pP2_ATS & pP2_T & pP2_AS & pP2_ATT & pP2_CO &
       pE &
       pLabc & pLabc_ATS & pLabc_T & pLabc_TO & pLabc_AS & pLabc_ATT & pLabc_CO &
       pLacb & pLacb_ATS & pLacb_T & pLacb_TO & pLacb_AS & pLacb_ATT & pLacb_CO &
       pLcab & pLcab_ATS & pLcab_T & pLcab_TO & pLcab_AS & pLcab_ATT & pLcab_CO &
       pLcba & pLcba_ATS & pLcba_T & pLcba_TO & pLcba_AS & pLcba_ATT & pLcba_CO)
result = sat.solve(exp)
i = 1
print('---finding multi blanket order for [abc, acb, cab, cba]---')
while result.success:
    print('mblanket order',i,' : ',end='')
    counter = tau
    for x in U:
        for y in U-{x}:
            if result[V['P1_'+x+'<'+y]]:
                print('P1_'+x+'<'+y,' ',end='')
                counter = counter & V['P1_'+x+'<'+y]
            else:
                counter = counter & -V['P1_'+x+'<'+y]
    for x in U:
        for y in U-{x}:
            if result[V['P2_'+x+'<'+y]]:
                print('P2_'+x+'<'+y,' ',end='')
                counter = counter & V['P2_'+x+'<'+y]
            else:
                counter = counter & -V['P2_'+x+'<'+y]
    exp = exp & -counter
    result = sat.solve(exp)
    i = i+1
    print()
print('---multi blanket order done---\n')

'''
-------------------------------------------------------------------------------
MULTI COVER ORDER PROBLEM
    Let Y be a set of linear orders, find a set of posets Ps such that
    every L in Y is a linear extension of some poset P in Ps and that
    every L not in Y is not a linear extension of any poset P in Ps.

CONSTRAINT OF ABSENT ORDER
(Aw) forall P, exist x.*y in w, y<x

EXAMPLE : for { abc, acb, cab, cba } ;
          expected Ps = { {a<b, a<c}, {c<b, c<a} } |
                        { {a<b}, {c<b, c<a, b<a} } |
                        ...
          absent orders = [ bac, bca ]
(Abac) (P1_a<b | P1_c<b | P1_c<a) & (P2_a<b | P2_c<b | P2_c<a)
(Abca) (P1_c<b | P1_a<b | P1_a<c) & (P2_c<b | P2_a<b | P2_a<c)
-------------------------------------------------------------------------------
'''

pAbac = (V['P1_a<b'] | V['P1_c<b'] | V['P1_c<a']) & (V['P2_a<b'] | V['P2_c<b'] | V['P2_c<a'])
pAbca = (V['P1_c<b'] | V['P1_a<b'] | V['P1_a<c']) & (V['P2_c<b'] | V['P2_a<b'] | V['P2_a<c'])

exp = (pP1_ATS & pP1_T & pP1_AS & pP1_ATT & pP1_CO &
       pP2_ATS & pP2_T & pP2_AS & pP2_ATT & pP2_CO &
       pE &
       pLabc & pLabc_ATS & pLabc_T & pLabc_TO & pLabc_AS & pLabc_ATT & pLabc_CO &
       pLacb & pLacb_ATS & pLacb_T & pLacb_TO & pLacb_AS & pLacb_ATT & pLacb_CO &
       pLcab & pLcab_ATS & pLcab_T & pLcab_TO & pLcab_AS & pLcab_ATT & pLcab_CO &
       pLcba & pLcba_ATS & pLcba_T & pLcba_TO & pLcba_AS & pLcba_ATT & pLcba_CO &
       pAbac & pAbca)
result = sat.solve(exp)
i = 1
print('---finding multi cover order for [abc, acb, cab, cba]---')
while result.success:
    print('mcover order',i,' : ',end='')
    counter = tau
    for x in U:
        for y in U-{x}:
            if result[V['P1_'+x+'<'+y]]:
                print('P1_'+x+'<'+y,' ',end='')
                counter = counter & V['P1_'+x+'<'+y]
            else:
                counter = counter & -V['P1_'+x+'<'+y]
    for x in U:
        for y in U-{x}:
            if result[V['P2_'+x+'<'+y]]:
                print('P2_'+x+'<'+y,' ',end='')
                counter = counter & V['P2_'+x+'<'+y]
            else:
                counter = counter & -V['P2_'+x+'<'+y]
    exp = exp & -counter
    result = sat.solve(exp)
    i = i+1
    print()
print('---multi cover order done---')
