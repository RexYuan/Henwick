from satispy import Variable
from satispy.solver import Minisat
from functools import reduce
from itertools import permutations

sat = Minisat()
T = Variable('dot') | -Variable('dot')
F = Variable('dot') & -Variable('dot')

class poset:
    def __init__(self, universe, rel=set(), name='', total=False, linearization=''):
        self.universe = universe

        name = name+'_' if name != '' else name
        self.name = name

        # build them variables
        v = {}
        for x in universe:
            for y in universe-{x}:
                v[name+x+'<'+y] = Variable(name+x+'<'+y)
                v[name+x+'{'+y] = Variable(name+x+'{'+y)
        self.v = v

        # build them axioms
        pATS = pT = pAS = pATT = pCO = pTO = T
        for x in universe:
            for y in universe-{x}:
                # pATS : forall x!=y, -(x<y & y<x)
                pATS = pATS & -(v[name+x+'<'+y] & v[name+y+'<'+x])
                # pAS : forall x!=y, -(x{y & y{x)
                pAS = pAS & -(v[name+x+'{'+y] & v[name+y+'{'+x])
                # pCO : forall x!=y, x{y => x<y
                pCO = pCO & (v[name+x+'{'+y] >> v[name+x+'<'+y])

                if total:
                    # pTO : forall x!=y,  (x<y | y<x)
                    pTO = pTO & (v[name+x+'<'+y] | v[name+y+'<'+x])

                for z in universe-{x,y}:
                    # pT : forall x!=y!=z, (x<y & y<z) => x<z
                    pT = pT & ((v[name+x+'<'+y] & v[name+y+'<'+z]) >> v[name+x+'<'+z])
                    # pATT : forall x!=y!=z, (x{y & y{z) => (-x{z & -z{x)
                    pATT = pATT & ((v[name+x+'{'+y] & v[name+y+'{'+z]) >> (-v[name+x+'{'+z] & -v[name+z+'{'+x]))
        self.constraints = pATS & pT & pAS & pATT & pCO & pTO

        # manual constraints with <
        if rel:
            for x in universe:
                for y in universe-{x}:
                    if x+'<'+y in rel:
                        self.constraints = self.constraints & v[name+x+'<'+y]
                    else:
                        self.constraints = self.constraints & -v[name+x+'<'+y]

        # linear constraints
        if total and linearization:
            for i in range(len(linearization)-1):
                self.constraints = self.constraints & v[name+linearization[i]+'{'+linearization[i+1]]

    def get_extension_constraints(self, p):
        assert(type(p) == poset and p.name != '')

        self.v = {**self.get_variables(), **p.get_variables()}
        v = self.v
        name = self.name
        universe = self.universe

        pE = T
        for x in universe:
            for y in universe-{x}:
                # pE (P2 extends P1) : forall x!=y, (x<y in P1) => (x<y in P2)
                pE = pE & (v[name+x+'<'+y] >> v[p.name+x+'<'+y])
        return pE

    def extends(self, *ps):
        for p in ps:
            self.constraints = (self.get_constraints() &
                                self.get_extension_constraints(p) &
                                p.get_constraints())
        return True

    def get_universe(self):
        return self.universe

    def get_variables(self):
        return self.v

    def get_constraints(self):
        return self.constraints

    def generate(self, sat=sat):
        name = self.name
        v = self.v
        universe = self.universe

        exp = self.constraints
        result = sat.solve(exp)
        while result.success:
            yield result
            counter = T
            for x in universe:
                for y in universe-{x}:
                    if result[v[name+x+'<'+y]]:
                        counter = counter & v[name+x+'<'+y]
                    else:
                        counter = counter & -v[name+x+'<'+y]
            exp = exp & -counter
            result = sat.solve(exp)

    def __str__(self):
        name = self.name
        v = self.v
        universe = self.universe
        tmp = ''

        i = 1
        tmp += '---Consistent posets---\n'
        for result in self.generate():
            tmp += 'order '+str(i)+'  : '
            for x in universe:
                for y in universe-{x}:
                    if result[v[self.name+x+'<'+y]]:
                        tmp += ' '+name+x+'<'+y
            i = i+1
            tmp += '\n'
        tmp += '---done---'
        return tmp

def poset_blanket(k=1, *lins, solve=False, ret_ctx=False):
    '''
    k : the number of blanketing posets
    ls : linearizations as strings
    '''
    universe = set(lins[0])
    v = {}
    constraints = T

    # build the k blanketing posets
    ps = {}
    for i in range(1, k+1):
        ps['P'+str(i)] = poset(universe, name='P'+str(i))
        constraints = constraints & ps['P'+str(i)].get_constraints()
        v = {**v, **ps['P'+str(i)].get_variables()}

    # build the linear posets
    ls = {}
    for w in lins:
        ls['L'+w] = poset(universe, name='L'+w, total=True, linearization=w)
        constraints = constraints & ls['L'+w].get_constraints()
        v = {**v, **ls['L'+w].get_variables()}

    # build the extension constraints
    for lname, l in ls.items():
        pE = F
        # forall l, exists p, l extends p
        for pname, p in ps.items():
            pE = pE | p.get_extension_constraints(l)
        constraints = constraints & pE

    # solve
    if solve:
        exp = constraints
        result = sat.solve(exp)
        i = 1
        print('---blanket for : [ ', ' '.join(lins), ' ]---')
        while result.success:
            print('blanket',i,' : ',end='')
            counter = T
            for pname, p in ps.items():
                for x in universe:
                    for y in universe-{x}:
                        if result[v[p.name+x+'<'+y]]:
                            print(p.name+x+'<'+y,' ',end='')
                            counter = counter & v[p.name+x+'<'+y]
                        else:
                            counter = counter & -v[p.name+x+'<'+y]
            exp = exp & -counter
            result = sat.solve(exp)
            i = i+1
            print()
        print('---end---\n')

    if ret_ctx:
        return (constraints,
                universe,
                v,
                ls,
                ps)
    else:
        return constraints

def poset_cover(k=1, *lins, solve=False):
    '''
    k : the number of covering posets
    ls : linearizations as strings
    '''
    # build atop poset blanket
    constraints, universe, v, ls, ps = poset_blanket(k, *lins, ret_ctx=True)

    # {absent} = {permutations} - linears
    absent = {''.join(p) for p in permutations(lins[0])} - set(lins)
    # l not generated by any p:
    # forall p, forall l, exists l_x<y, p_y<x
    for pname, p in ps.items():
        for w in absent:
            pA = F
            for i in range(len(w)):
                for j in range(i+1,len(w)):
                    pA = pA | v[p.name+w[j]+'<'+w[i]]
            constraints = constraints & pA

    if solve:
        exp = constraints
        result = sat.solve(exp)
        i = 1
        print('---cover for : [ ', ' '.join(lins), ' ]---')
        while result.success:
            print('cover',i,' : ',end='')
            counter = T
            for x in universe:
                for y in universe-{x}:
                    for pname, p in ps.items():
                        if result[v[p.name+x+'<'+y]]:
                            print(p.name+x+'<'+y,' ',end='')
                            counter = counter & v[p.name+x+'<'+y]
                        else:
                            counter = counter & -v[p.name+x+'<'+y]
            exp = exp & -counter
            result = sat.solve(exp)
            i = i+1
            print()
        print('---end---\n')

    return constraints

poset_cover(2, 'abc', 'acb', 'cab', 'cba', solve=True)

# TODO: 1) automate constraint generation
#                 ======> optimize variable storage with global context
#       2) furthur testing with more complex poset
#       3) test it with multiple poset ; ie poset cover problem
#       4) this many clauses? are you fucking kidding me? can you not?
#          must find a way to make it more efficient
#          maybe automaton would help after all?
