from satispy import Variable
from satispy.solver import Minisat
from functools import reduce
from itertools import permutations

tau = Variable('dot') | -Variable('dot')
con = Variable('dot') & -Variable('dot')
sat = Minisat()

# TODO: 1) automate constraint generation
#                 ======> optimize variable storage with global context
#       2) furthur testing with more complex poset
#       3) test it with multiple poset ; ie poset cover problem
#       4) this many clauses? are you fucking kidding me? can you not?
#          must find a way to make it more efficient
#          maybe automaton would help after all?

def get_variables(universe, name=''):
    U = universe
    V = {}
    for x in U:
        for y in U-{x}:
            V[name+x+'<'+y] = Variable(name+x+'<'+y)
            V[name+x+'{'+y] = Variable(name+x+'{'+y)
    return V

def get_poset_axioms(universe, name='', lextensions=[], total=False):
    assert(not(lextensions!=[] and total))
    assert(not(total and name==''))
    if name != '':
        name = 'L'+name+'_'
    U = universe
    V = get_variables(U, name)
    for w in lextensions:
        V = {**V, **get_variables(U, 'L'+w+'_')}

    pATS = pT = pAS = pATT = pCO = pE = pTO = tau

    for x in U:
        for y in U-{x}:
            # pATS : forall x!=y, -(x<y & y<x)
            pATS = pATS & -(V[name+x+'<'+y] & V[name+y+'<'+x])
            # pAS : forall x!=y,  -(x{y & y{x)
            pAS = pAS & -(V[name+x+'{'+y] & V[name+y+'{'+x])
            # pCO : forall x!=y, x{y => x<y
            pCO = pCO & (V[name+x+'{'+y] >> V[name+x+'<'+y])

            if total:
                # pTO : forall x!=y,  (x<y | y<x)
                pTO = pTO & (V[name+x+'<'+y] | V[name+y+'<'+x])

            for z in U-{x,y}:
                # pT : forall x!=y!=z, (x<y & y<z) => x<z
                pT = pT & ((V[name+x+'<'+y] & V[name+y+'<'+z]) >> V[name+x+'<'+z])
                # pATT : forall x!=y!=z, (x{y & y{z) => (-x{z & -z{x)
                pATT = pATT & ((V[name+x+'{'+y] & V[name+y+'{'+z]) >> (-V[name+x+'{'+z] & -V[name+z+'{'+x]))

            # NOTE: w in extension must be the name of that linear order
            for w in lextensions:
                # forall L, forall x!=y,  (x<y in P) => (x<y in L)
                pE = pE & (V[name+x+'<'+y] >>
                           reduce((lambda x,y : x & y), (V['L'+w+'_'+x+'<'+y] for w in lextensions)))

    exp = pATS & pT & pAS & pATT & pCO & pE & pTO
    return exp

def get_blanket_poset_constraints(*linears):
    assert(linears!=())
    #assert(reduce((lambda x,y : type(x)==type(y)==str and len(x)==len(y) and set(x) == set(y)), linears))

    # building the universe and axioms
    U = set(linears[0])
    exp = get_poset_axioms(U, lextensions=linears)

    for w in linears:
        exp = exp & get_poset_axioms(U, name=w, total=True)

        # pL : forall x.y in w, Lw_x{y
        for i in range(len(w)-1):
            exp = exp & Variable('L'+w+'_'+w[i]+'{'+w[i+1])
    return exp

def get_generating_poset_constraints(*linears):
    assert(linears!=())
    #assert(reduce((lambda x,y : type(x)==type(y)==str and len(x)==len(y) and set(x) == set(y)), linears))

    # universe
    U = set(linears[0])

    # blanketing poset
    exp = get_blanket_poset_constraints(*linears)

    # NOTE: this is probably the most tricky bottle neck
    # constraint of absent order ; {absent} = {permutations} - linears
    perms = {''.join(p) for p in permutations(linears[0])}
    for w in perms-set(linears):
        # pA : exists x.y in w, -x{y & -x||y
        pA = con
        for i in range(len(w)-1):
            pA = pA | (-Variable(w[i]+'{'+w[i+1]) & -(-Variable(w[i]+'<'+w[i+1]) & -Variable(w[i+1]+'<'+w[i])))

        exp = exp & pA
    return exp

exp = get_generating_poset_constraints('abc','acb','cab')
result = sat.solve(exp)
i = 1
print('---begin---')
while result.success:
    print('order',i,' : ',end='')
    counter = tau
    for x in {'a','b','c'}:
        for y in {'a','b','c'}-{x}:
            if result[Variable(x+'<'+y)]:
                print(x+'<'+y,' ',end='')
                counter = counter & Variable(x+'<'+y)
            else:
                counter = counter & -Variable(x+'<'+y)
    exp = exp & -counter
    result = sat.solve(exp)
    i = i+1
    print()
print('---end---\n')
