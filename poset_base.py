from satispy import Variable
from satispy.solver import Minisat

'''
-------------------------------------------------------------------------------
Variables:
X ::= a | b | c
P ::= Labc | Lacb
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
        V['Labc_'+x+'{'+y] = Variable('Labc_'+x+'{'+y)
        V['Lacb_'+x+'{'+y] = Variable('Lacb_'+x+'{'+y)
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

BLANKET ORDER PROBLEM
    Let Y be a set of linear orders, find a poset P such that
    every L in Y is a linear extension of P.

CONSTRAINT OF PRESENT ORDER
    For every linear order L in Y, since we know cover implies order,
    totality and transitivity are ensured, and we also know that, if L extends
    P, we can set the case for L and P will follow. The constraints of a give
    L that should be blanket by P is, simply, forall x.y in w, Lw_x{y.
(Lw) forall x.y in w, Lw_x{y

EXAMPLE : let Labc = abc and Lacb = acb ; expected P = { a<b, a<c } | { a<b } | { a<c } | {}
(E) (a<b => (Labc_a<b & Lacb_a<b)) &
    (a<c => (Labc_a<c & Lacb_a<c)) &
    (b<a => (Labc_b<a & Lacb_b<a)) &
    (b<c => (Labc_b<c & Lacb_b<c)) &
    (c<a => (Labc_c<a & Lacb_c<a)) &
    (c<b => (Labc_c<b & Lacb_c<b))
(Labc) Labc_a<b & Labc_b<c
(Lacb) Lacb_a<c & Lacb_c<b
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
exp = (pATS & pT & pE &
       pLabc & pLabc_ATS & pLabc_T & pLabc_TO & pLabc_AS & pLabc_ATT & pLabc_CO &
       pLacb & pLacb_ATS & pLacb_T & pLacb_TO & pLacb_AS & pLacb_ATT & pLacb_CO)

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
-------------------------------------------------------------------------------
GENERATING ORDER PROBLEM
    Let Y be a set of linear orders, find a poset P such that
    every L in Y is a linear extension of P and that
    every L not in Y is not a linear extension of P.
    That is, find the strictest poset P that blankets Y.

CONSTRAINT OF ABSENT ORDER
    For every linear order L not in Y, P must not blankets it.
    From theorem : if P blankets L, forall cover x{y in L, x{y in P xor x||y in P,
    we know that, if exists a cover x{y in L, not(x{y in P xor x||y in P), then
    P does not blanket L, namely, the constraint of the absent L.
    Since not(x xor y) is equivalent to (x & y) | (-x & -y) and that x{y and x||y
    can never coincide, it must be the case that -x{y & -x||y.
(Aw) exists x.y in w, -x{y & -x||y

EXAMPLE : let Labc = abc and Lacb = acb ; expected P = { a<b, a<c }
          absent orders = [ bac, bca, cab, cba ]
(Abac) (-b{a & -(-b<a & -a<b)) | (-a{c & -(-a<c & -c<a))
(Abca) (-b{c & -(-b<c & -c<b)) | (-c{a & -(-c<a & -a<c))
(Acab) (-c{a & -(-c<a & -a<c)) | (-a{b & -(-a<b & -b<a))
(Acba) (-c{b & -(-c<b & -b<c)) | (-b{a & -(-b<a & -a<b))
NOTE: comparability and incomparability are both intransitive.
-------------------------------------------------------------------------------
'''

pAbac = (-V['b{a'] & -(-V['b<a'] & -V['a<b'])) | (-V['a{c'] & -(-V['a<c'] & -V['c<a']))
pAbca = (-V['b{c'] & -(-V['b<c'] & -V['c<b'])) | (-V['c{a'] & -(-V['c<a'] & -V['a<c']))
pAcab = (-V['c{a'] & -(-V['c<a'] & -V['a<c'])) | (-V['a{b'] & -(-V['a<b'] & -V['b<a']))
pAcba = (-V['c{b'] & -(-V['c<b'] & -V['b<c'])) | (-V['b{a'] & -(-V['b<a'] & -V['a<b']))

exp = (pATS & pT & pE &
       pLabc & pLabc_ATS & pLabc_T & pLabc_TO & pLabc_AS & pLabc_ATT & pLabc_CO &
       pLacb & pLacb_ATS & pLacb_T & pLacb_TO & pLacb_AS & pLacb_ATT & pLacb_CO &
       pAbac & pAbca & pAcab & pAcba)

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

# TODO: 1) automate constraint generation
#       2) furthur testing with more complex poset
#       3) test it with multiple poset ; ie poset cover problem
#       4) this many clauses? are you fucking kidding me? can you not?
#          must find a way to make it more efficient
#          maybe automaton would help after all?
