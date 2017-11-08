from satispy import Variable, Cnf
from satispy.solver import Minisat

'''

----------------------------------------

COVER ATOM
for element pair (x,y) and poset k, we have atom kxy
kxy : y covers x in poset k

POSET AXIOMS
A) forall k, forall x != y, -(kxy & kyx)
B) forall k, forall x != y, kxy => forall z != [x,y], -(kxz & kzy)

kxz => -(kxy & kyz)
kxy & kyz => -kxz

ca ab
cb

POSET COVER CONSTRAINTS
given linear extension w = (u1)(u2)(u3)...(un),
Lw) exists k, forall (ui)(ui+1) where 1<=i<n, k(ui)(ui+1) | (-k(ui)(ui+1) & -k(ui+1)(ui))

----------------------------------------

EXAMPLE1
universe = {a, b, c}
linear extensions = [abc, acb]
poset cover covers = { (a,b), (a,c) }
=> axioms:
   A) -(1ab & 1ba) &
      -(1ac & 1ca) &
      -(1bc & 1cb)
   B) (1ab => -(1ac & 1cb)) &
      (1ac => -(1ab & 1bc)) &
      (1bc => -(1ba & 1ac))
=> constraints:
   Labc) (1ab | (-1ab & -1ba)) & (1bc | (-1bc & -1cb))
   Lacb) (1ac | (-1ac & -1ca)) & (1cb | (-1cb & -1bc))

----------------------------------------

'''
'''
a = 'a'
b = 'b'
c = 'c'
U = {a,b,c}
H = 1 # number of posets
atm = {}
for i in range(H):
    for x in U:
        for y in U-{x}:
            atm[str(i+1)+x+y] = Variable(str(i+1)+x+y)

axA = (-(atm['1ab'] & atm['1ba']) &
      -(atm['1ac'] & atm['1ca']) &
      -(atm['1bc'] & atm['1cb']))
axB = ((atm['1ab'] >> -(atm['1ac'] & atm['1cb'])) &
      (atm['1ac'] >> -(atm['1ab'] & atm['1bc'])) &
      (atm['1bc'] >> -(atm['1ba'] & atm['1ac'])))

# ensure L is generated by P
Labc = (atm['1ab'] | (-atm['1ab'] & -atm['1ba'])) & (atm['1bc'] | (-atm['1bc'] & -atm['1cb']))
Lacb = (atm['1ac'] | (-atm['1ac'] & -atm['1ca'])) & (atm['1cb'] | (-atm['1cb'] & -atm['1bc']))
# is this necessary?
Nbac = -(-atm['1ba'] & -atm['1ab'] & -atm['1ac'] & -atm['1ca'])
Nbca = -(-atm['1bc'] & -atm['1cb'] & -atm['1ca'] & -atm['1ac'])
Ncab = -(-atm['1ca'] & -atm['1ac'] & -atm['1ab'] & -atm['1ba'])
Ncba = -(-atm['1cb'] & -atm['1bc'] & -atm['1ba'] & -atm['1ab'])
# does SAT always find the most general case?
C1 = -(-atm['1ac'] & -atm['1ab'] & -atm['1ba'] & -atm['1bc'] & -atm['1ca'] & -atm['1cb'])
C2 = -(atm['1ac'] & -atm['1ab'] & -atm['1ba'] & -atm['1bc'] & -atm['1ca'] & -atm['1cb'])
C3 = -(-atm['1ac'] & atm['1ab'] & -atm['1ba'] & -atm['1bc'] & -atm['1ca'] & -atm['1cb'])
C4 = -(atm['1ac'] & atm['1ab'] & -atm['1ba'] & -atm['1bc'] & -atm['1ca'] & -atm['1cb'])

solver = Minisat()
exp = axA & axB & Labc & Lacb &Nbac & Nbca & Ncab & Ncba#& C1 & C2 & C3
solution = solver.solve(exp)

if solution.success:
    for i in range(H):
        for x in U:
            for y in U-{x}:
                print(str(i+1)+x+y, solution[atm[str(i+1)+x+y]])
'''
'''

----------------------------------------

EXAMPLE2
universe = {a, b, c}
linear extensions = [abc, acb, cab]
poset cover covers = { (a,b), (a,c) } & { (c,a), (a,b) } |
                     { (a,b), (c,b) } & { (a,b), (b,c) } |
                     NOTE: found new cover!!!!!!
                     1ab
                        1ac
                        2cb
                        2ab
                        TODO: lets find all of them?
=> axioms:
   A) -(1ab & 1ba) &
      -(1ac & 1ca) &
      -(1bc & 1cb) &
      -(2ab & 2ba) &
      -(2ac & 2ca) &
      -(2bc & 2cb)
   B) (1ab => -(1ac & 1cb)) &
      (1ac => -(1ab & 1bc)) &
      (1bc => -(1ba & 1ac)) &
      (2ab => -(2ac & 2cb)) &
      (2ac => -(2ab & 2bc)) &
      (2bc => -(2ba & 2ac))
=> constraints:
   Labc) ((1ab | (-1ab & -1ba)) & (1bc | (-1bc & -1cb))) |
         ((2ab | (-2ab & -2ba)) & (2bc | (-2bc & -2cb)))
   Lacb) ((1ac | (-1ac & -1ca)) & (1cb | (-1cb & -1bc))) |
         ((2ac | (-2ac & -2ca)) & (2cb | (-2cb & -2bc)))
   Lcab) ((1ca | (-1ca & -1ac)) & (1ab | (-1ab & -1ba))) |
         ((2ca | (-2ca & -2ac)) & (2ab | (-2ab & -2ba)))

----------------------------------------

'''

a = 'a'
b = 'b'
c = 'c'
U = {a,b,c}
H = 2 # number of posets
atm = {}
for i in range(H):
    for x in U:
        for y in U-{x}:
            atm[str(i+1)+x+y] = Variable(str(i+1)+x+y)

axA= (-(atm['1ab'] & atm['1ba']) &
      -(atm['1ac'] & atm['1ca']) &
      -(atm['1bc'] & atm['1cb']) &
      -(atm['2ab'] & atm['2ba']) &
      -(atm['2ac'] & atm['2ca']) &
      -(atm['2bc'] & atm['2cb']))
axB= ((atm['1ab'] >> -(atm['1ac'] & atm['1cb'])) &
      (atm['1ba'] >> -(atm['1bc'] & atm['1ca'])) &
      (atm['1ac'] >> -(atm['1ab'] & atm['1bc'])) &
      (atm['1ca'] >> -(atm['1cb'] & atm['1ba'])) &
      (atm['1bc'] >> -(atm['1ba'] & atm['1ac'])) &
      (atm['1cb'] >> -(atm['1ca'] & atm['1ab'])) &
      (atm['2ab'] >> -(atm['2ac'] & atm['2cb'])) &
      (atm['2ba'] >> -(atm['2bc'] & atm['2ca'])) &
      (atm['2ac'] >> -(atm['2ab'] & atm['2bc'])) &
      (atm['2ca'] >> -(atm['2cb'] & atm['2ba'])) &
      (atm['2bc'] >> -(atm['2ba'] & atm['2ac'])) &
      (atm['2cb'] >> -(atm['2ca'] & atm['2ab'])))
# acyclic : x<y => !Ez z<x * y<z?????
axC= ((atm['1ab'] & atm['1bc']) >> -atm['1ca'] &
(atm['1ac'] & atm['1cb']) >> -atm['1ba'] &
(atm['1ba'] & atm['1ac']) >> -atm['1cb'] &
(atm['1bc'] & atm['1ca']) >> -atm['1ab'] &
(atm['1ca'] & atm['1ab']) >> -atm['1bc'] &
(atm['1cb'] & atm['1ba']) >> -atm['1ac'] &
(atm['2ab'] & atm['2bc']) >> -atm['2ca'] &
(atm['2ac'] & atm['2cb']) >> -atm['2ba'] &
(atm['2ba'] & atm['2ac']) >> -atm['2cb'] &
(atm['2bc'] & atm['2ca']) >> -atm['2ab'] &
(atm['2ca'] & atm['2ab']) >> -atm['2bc'] &
(atm['2cb'] & atm['2ba']) >> -atm['2ac'])
# incomparability : x||y => !Ez x<z<y + y<z<x
axD=(
(-atm['1ab'] & -atm['1ba']) >> (-(atm['1ac'] & atm['1cb']) & -(atm['1bc'] & atm['1ca']))&
(-atm['1ac'] & -atm['1ca']) >> (-(atm['1ab'] & atm['1bc']) & -(atm['1cb'] & atm['1ba']))&
(-atm['1bc'] & -atm['1cb']) >> (-(atm['1ba'] & atm['1ac']) & -(atm['1ca'] & atm['1ab']))&
(-atm['2ab'] & -atm['2ba']) >> (-(atm['2ac'] & atm['2cb']) & -(atm['2bc'] & atm['2ca']))&
(-atm['2ac'] & -atm['2ca']) >> (-(atm['2ab'] & atm['2bc']) & -(atm['2cb'] & atm['2ba']))&
(-atm['2bc'] & -atm['2cb']) >> (-(atm['2ba'] & atm['2ac']) & -(atm['2ca'] & atm['2ab'])) # this line fucks up
# incomparability is with order not cover
)

Labc = (((atm['1ab'] | (-atm['1ab'] & -atm['1ba'])) & (atm['1bc'] | (-atm['1bc'] & -atm['1cb']))) |
      ((atm['2ab'] | (-atm['2ab'] & -atm['2ba'])) & (atm['2bc'] | (-atm['2bc'] & -atm['2cb']))))
Lacb = (((atm['1ac'] | (-atm['1ac'] & -atm['1ca'])) & (atm['1cb'] | (-atm['1cb'] & -atm['1bc']))) |
      ((atm['2ac'] | (-atm['2ac'] & -atm['2ca'])) & (atm['2cb'] | (-atm['2cb'] & -atm['2bc']))))
Lcab = (((atm['1ca'] | (-atm['1ca'] & -atm['1ac'])) & (atm['1ab'] | (-atm['1ab'] & -atm['1ba']))) |
      ((atm['2ca'] | (-atm['2ca'] & -atm['2ac'])) & (atm['2ab'] | (-atm['2ab'] & -atm['2ba']))))
Ncba = (-(-atm['1cb'] & -atm['1bc'] & -atm['1ba'] & -atm['1ab']) &
       -(-atm['2cb'] & -atm['2bc'] & -atm['2ba'] & -atm['2ab']))
Nbac = (-(-atm['1ba'] & -atm['1ab'] & -atm['1ac'] & -atm['1ca']) &
       -(-atm['2ba'] & -atm['2ab'] & -atm['2ac'] & -atm['2ca']))
Nbca = (-(-atm['1bc'] & -atm['1cb'] & -atm['1ca'] & -atm['1ac']) &
       -(-atm['2bc'] & -atm['2cb'] & -atm['2ca'] & -atm['2ac']))

solver = Minisat()

# method one : use absent extensions
x = atm['1ab'] & atm['1ac'] & atm['2ca'] & atm['2ab']
exp = axA & axB & Labc & Lacb & Lcab & Ncba & Nbac & Nbca & axC & axD & x
solution = solver.solve(exp)
while solution.success:
    for i in range(H):
        for x in U:
            for y in U-{x}:
                if solution[atm[str(i+1)+x+y]]:
                    print(str(i+1)+x+y)
    print()
    tmp = Variable('dot') | -Variable('dot')
    for i in range(H):
        for x in U:
            for y in U-{x}:
                if solution[atm[str(i+1)+x+y]]:
                    tmp = tmp & atm[str(i+1)+x+y]
                else:
                    tmp = tmp & -atm[str(i+1)+x+y]
    exp = exp & -tmp
    solution = solver.solve(exp)
print('done')

# method two : exhaust with counter-examples to find the strictest case
# NOTE: doesnt work?
# NOTE: axiom not enough? need to establish noncircularity ab,bc => -ca
'''
solver = Minisat()
x = atm['1ab'] & atm['1ac'] & atm['2ca'] & atm['2ab']
exp = axA & axB & axC & axD & Labc & Lacb & Lcab
solution = solver.solve(exp)
while solution.success:
    break
    tmp = Variable('dot') | -Variable('dot')
    for i in range(H):
        for x in U:
            for y in U-{x}:
                if solution[atm[str(i+1)+x+y]]:
                    tmp = tmp & atm[str(i+1)+x+y]
                else:
                    tmp = tmp & -atm[str(i+1)+x+y]
    exp = exp & -tmp
    print(tmp)
    solution = solver.solve(exp)
    print(solution[Variable('dot')])
    if solution.success:
        for i in range(H):
            for x in U:
                for y in U-{x}:
                    print(str(i+1)+x+y, solution[atm[str(i+1)+x+y]])
'''
