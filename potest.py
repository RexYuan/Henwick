#from satispy import Variable
#from satispy.solver import Minisat
from functools import reduce
from itertools import permutations
from sat import *

def str_lin(l,*os):
    # assuming the orders are indeed consistent
    l = [[i,0] for i,_ in enumerate(range(l))]
    for x,y in map((lambda s : s.split('<')), os):
        l[int(x)-1][1] += 1
    l = sorted(l,key=(lambda e : e[1]),reverse=True)
    return int(''.join(str(x+1) for x in map((lambda a : a[0]), l)))

class poset:
    def __init__(self, universe, rel=set(), name='', total=False, linearization=''):
        self.universe = universe

        name = name+'_' if name != '' else name
        self.name = name

        # build them variables
        v = {}
        for x in universe:
            for y in universe-{x}:
                v[name+x+'<'+y] = Atom(name+x+'<'+y)
                v[name+x+'{'+y] = Atom(name+x+'{'+y)
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
                #pCO = pCO & (v[name+x+'{'+y] >> v[name+x+'<'+y])

                if total:
                    # pTO : forall x!=y,  (x<y | y<x)
                    pTO = pTO & (v[name+x+'<'+y] | v[name+y+'<'+x])

                z_in_xy = F
                for z in universe-{x,y}:
                    # pT : forall x!=y!=z, (x<y & y<z) => x<z
                    pT = pT & ((v[name+x+'<'+y] & v[name+y+'<'+z]) >> v[name+x+'<'+z])

                    # pATT : forall x!=y!=z, (x{y & y{z) => (-x{z & -z{x)
                    # NOTE: this needs more work ; the definition of cover relation
                    #       is x{z iff x<z & -(exists y, x{y & y{z) . the antitransitivity
                    #       here isn't sufficient for the right-to-left direction of the
                    #       equivalence . what we're doing here is merely one direction of
                    #       encoding, namely from cover to order . and the antitransitivity
                    #       is only useful for validating constraints on covers themselves .
                    #       it's not enough to infer from SAT results anything about covers .
                    #       need to consider using the definition itself or some other
                    #       equivalent condition, if cover relation is ever to be used as
                    #       more than a short-hand way of encoding orders .
                    #pATT = pATT & ((v[name+x+'{'+y] & v[name+y+'{'+z]) >> (-v[name+x+'{'+z] & -v[name+z+'{'+x]))
                    # -(exists y, x{y & y{z)
                    # foall z, -(x{z & z{y)
                    #pATT = pATT & (
                    #     (v[name+x+'{'+y] &  (v[name+x+'<'+y] & -(v[name+x+'{'+z] & v[name+z+'{'+y]))) |
                    #    (-v[name+x+'{'+y] & -(v[name+x+'<'+y] & -(v[name+x+'{'+z] & v[name+z+'{'+y])))
                    #)
                    #z_in_xy = z_in_xy | (v[name+x+'<'+z] & v[name+z+'<'+y])
                # lesson learned : explicitly demorgan for it
                #pATT = pATT & (
                #     (v[name+x+'{'+y] &  (v[name+x+'<'+y] & -(z_in_xy))) |
                #    (-v[name+x+'{'+y] & (-v[name+x+'<'+y] | (z_in_xy)))
                #)

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
            w = linearization
            for i in range(len(w)):
                for j in range(i+1, len(w)):
                    self.constraints = self.constraints & v[name+w[i]+'<'+w[j]]
        #    for i in range(len(linearization)-1):
        #        self.constraints = self.constraints & v[name+linearization[i]+'{'+linearization[i+1]]

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

    def get_linearizations(self, sat=None):
        '''
        generate all linearizations
        '''
        universe = self.universe

        l = poset(universe, name='L', total=True)
        exp = self.get_constraints() & self.get_extension_constraints(l) & l.get_constraints()
        v = {**self.get_variables(), **l.get_variables()}

        result = sat.solve(exp)
        while result.success:
            lin = set()
            counter = T
            for x in universe:
                for y in universe-{x}:
                    if result[v[l.name+x+'<'+y]]:
                        counter = counter & v[l.name+x+'<'+y]
                        lin.add(x+'<'+y)
                    else:
                        counter = counter & -v[l.name+x+'<'+y]
            yield lin
            exp = exp & -counter
            result = sat.solve(exp)

    def print_linearizations(self):
        i = 1
        tmp = set()
        print('---Linearizations---')
        for lin in sorted(map((lambda r : str_lin(5,*r)), self.get_linearizations())):
            print('L'+str(i)+' : ', end='')
            #str_lin(5,*lin)
            print(lin, end='')
            tmp.add(lin)
            #for r in lin:
            #    print(r, ' ', end='')
            i = i+1
            print()
        return tmp

    def solve(self, sat=None):
        '''
        get all consistent poset
        '''
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
        for result in self.solve():
            tmp += 'order '+str(i)+'  : '
            for x in universe:
                for y in universe-{x}:
                    if result[v[self.name+x+'{'+y]]:
                        tmp += ' '+name+x+'{'+y
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
                        if result[v[p.name+x+'{'+y]]:
                            print(p.name+x+'{'+y,' ',end='')
                        if result[v[p.name+x+'<'+y]]:
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
                        #if result[v[p.name+x+'{'+y]]:
                        #    print(p.name+x+'{'+y,' ',end='')
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

#poset({'a','b','c','d','e','f'}).print_linearizations()
#poset_cover(2, 'abc', 'acb', 'cab', 'cba', solve=True)

l = ['2741563',
'7241563',
'2741653',
'7241653',
'2745163',
'7245163']

l2=['1234567',
'1235467',
'1324567',
'1325467',
'2134567',
'2135467',
'2314567',
'2315467',
'3124567',
'3125467',
'3214567',
'3215467']

l3 = [*l2, '7654321','7654231']

a = poset({'1','2','3','4','5'}, rel=['1<4','2<4','2<5','3<5'])
#l1 = a.print_linearizations()
#a = poset({'1','2','3','4','5'}, rel=['1<4','1<2','1<5','3<2','3<4','3<5','2<4','2<5'])
#a = poset({'1','2','3','4','5'}, rel=['1<4','2<4','2<5','3<5','1<5','3<4'])
#a = poset({'1','2','3','4','5'}, rel=['1<4','3<5','1<5','3<4','3<2'])
#l2 = a.print_linearizations()
#a = poset({'1','2','3'})
#from time import time as t
#t1 = t()
#poset_blanket(3,'12354','43125','54231',solve=True)
#print(t()-t1)

#poset_cover(2, *l3, solve=True)

# TODO:
#       2) furthur testing with more complex poset
#       3) test it with multiple poset ; ie poset cover problem
#       4) this many clauses? are you fucking kidding me? can you not?
#          must find a way to make it more efficient
#          maybe automaton would help after all?

#cover_from_order(5,'2<4','1<5','1<4','2<1','2<5','5<4','2<3','3<5','3<4','1<3')
