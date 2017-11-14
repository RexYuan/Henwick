from z3 import *
from functools import reduce
from itertools import permutations

v = Bool
T = BoolVal(True)
F = BoolVal(False)

def str_lin(l,*os):
    '''
    string form of linear order
    '''
    # assuming the orders are indeed consistent
    l = [[i,0] for i,_ in enumerate(range(l))]
    for x,y in map((lambda s : s.split('<')), os):
        l[int(x)-1][1] += 1
    l = sorted(l,key=(lambda e : e[1]),reverse=True)
    return int(''.join(str(x+1) for x in map((lambda a : a[0]), l)))

class poset:
    def __init__(self, universe, rel=set(), name='', total=False, linearization=''):
        self.universe = universe
        self.s = Solver()
        s = self.s

        name = name+'_' if name != '' else name
        self.name = name

        constraints = T
        self.constraints = constraints

        # build them axioms
        for x in universe:
            for y in universe-{x}:
                # pATS : forall x!=y, -(x<y & y<x)
                pATS = Not(And(v(name+x+'<'+y), v(name+y+'<'+x)))
                s.add(pATS)
                constraints = simplify(And(constraints, pATS))
                # pAS : forall x!=y, -(x{y & y{x)
                pAS = Not(And(v(name+x+'{'+y), v(name+y+'{'+x)))
                s.add(pAS)
                constraints = simplify(And(constraints, pAS))
                if total:
                    # pTO : forall x!=y,  (x<y | y<x)
                    pTO = Or(v(name+x+'<'+y), v(name+y+'<'+x))
                    s.add(pTO)
                    constraints = simplify(And(constraints, pTO))

                z_in_xy = F
                for z in universe-{x,y}:
                    # pT : forall x!=y!=z, (x<y & y<z) => x<z
                    pT = Implies(And(v(name+x+'<'+y), v(name+y+'<'+z)), v(name+x+'<'+z))
                    s.add(pT)
                    constraints = simplify(And(constraints, pT))
                    # pATT : forall x!=y, (x{y) <=> (x<y & forall z, -(x<z & z<y))
                    #z_in_xy = simplify(Or(z_in_xy, And(v(name+x+'<'+z), v(name+z+'<'+y))))
                #pATT = Or(
                #    And(    v(name+x+'{'+y),      And(v(name+x+'<'+y), Not(z_in_xy))),
                #    And(Not(v(name+x+'{'+y)), Not(And(v(name+x+'<'+y), Not(z_in_xy))))
                #)
                #s.add(pATT)
                #constraints = simplify(And(constraints, pATT))

        # manual constraints with <
        if rel:
            for x in universe:
                for y in universe-{x}:
                    if x+'<'+y in rel:
                        s.add(v(name+x+'<'+y))
                        constraints = simplify(And(constraints, v(name+x+'<'+y)))
                    else:
                        s.add(Not(v(name+x+'<'+y)))
                        constraints = simplify(And(constraints, Not(v(name+x+'<'+y))))

        # linear constraints
        if total and linearization:
            w = linearization
            for i in range(len(w)):
                for j in range(i+1, len(w)):
                    s.add(v(name+w[i]+'<'+w[j]))
                    constraints = simplify(And(constraints, v(name+w[i]+'<'+w[j])))
            #for i in range(len(linearization)-1):
            #    s.add(v(name+linearization[i]+'{'+linearization[i+1]))
            #    constraints = simplify(And(constraints, v(name+linearization[i]+'{'+linearization[i+1])))

        self.constraints = constraints

    def get_extension_constraints(self, p):
        assert(type(p) == poset and p.name != '')

        name = self.name
        universe = self.universe

        pE = T
        for x in universe:
            for y in universe-{x}:
                # pE (P2 extends P1) : forall x!=y, (x<y in P1) => (x<y in P2)
                pE = And(pE , Implies(v(name+x+'<'+y) , v(p.name+x+'<'+y)))
        return pE

    def extends(self, *ps):
        s = self.s
        constraints = self.constraints

        for p in ps:
            new_c = And(self.get_extension_constraints(p), p.get_constraints())
            s.add(new_c)
            constraints = simplify(And(constraints, new_c))

        self.constraints = constraints
        return True

    def get_universe(self):
        return self.universe

    def get_constraints(self):
        return self.constraints

    def get_linearizations(self, sat=sat):
        '''
        generate all linearizations
        '''
        universe = self.universe

        l = poset(universe, name='L', total=True)
        lin_s = Solver()
        lin_s.add(self.get_constraints() , self.get_extension_constraints(l) , l.get_constraints())

        result = lin_s.check()
        while result == sat:
            lin = set()
            m = lin_s.model()
            counter = T
            for x in universe:
                for y in universe-{x}:
                    if m[v(l.name+x+'<'+y)]:
                        counter = And(counter , v(l.name+x+'<'+y))
                        lin.add(x+'<'+y)
                    else:
                        counter = And(counter , Not(v(l.name+x+'<'+y)))
            yield lin
            lin_s.add(Not(counter))
            result = lin_s.check()

    def print_linearizations(self):
        universe = self.universe

        i = 1
        tmp = set()
        print('---Linearizations---')
        for lin in sorted(map((lambda r : str_lin(len(universe),*r)), self.get_linearizations())):
            print('L'+str(i)+' : ', lin)
            tmp.add(lin)
            i = i+1
        print('---done---')
        return tmp

    def solve(self, sat=sat):
        '''
        get all consistent poset
        '''
        name = self.name
        universe = self.universe
        s = self.s

        result = s.check()
        while result == sat:
            m = s.model()
            yield m
            counter = T
            for x in universe:
                for y in universe-{x}:
                    if m[v(name+x+'<'+y)]:
                        counter = And(counter , v(name+x+'<'+y))
                    else:
                        counter = And(counter , Not(v(name+x+'<'+y)))
            s.add(Not(counter))
            result = s.check()

    def __str__(self):
        name = self.name
        universe = self.universe
        tmp = ''

        i = 1
        tmp += '---Consistent posets---\n'
        for result in self.solve():
            tmp += 'order '+str(i)+'  : '
            for x in universe:
                for y in universe-{x}:
                    if result[v(name+x+'{'+y)]:
                        tmp += ' '+name+x+'{'+y
            i = i+1
            tmp += '\n'
        tmp += '---done---'
        return tmp

def poset_blanket(k=1, *lins, solve=True):
    '''
    k : the number of blanketing posets
    ls : linearizations as strings
    '''
    b_s = Solver()

    universe = set(lins[0])
    constraints = T

    # build the k blanketing posets
    ps = {}
    for i in range(1, k+1):
        ps['P'+str(i)] = poset(universe, name='P'+str(i))
        b_s.add(ps['P'+str(i)].get_constraints())
        constraints = simplify(And(constraints , ps['P'+str(i)].get_constraints()))

    # build the linear posets
    ls = {}
    for w in lins:
        ls['L'+w] = poset(universe, name='L'+w, total=True, linearization=w)
        b_s.add(ls['L'+w].get_constraints())
        constraints = simplify(And(constraints , ls['L'+w].get_constraints()))

    # build the extension constraints
    for lname, l in ls.items():
        pE = F
        # forall l, exists p, l extends p
        for pname, p in ps.items():
            pE = Or(pE, p.get_extension_constraints(l))
        b_s.add(pE)
        constraints = simplify(And(constraints , pE))

    # solve
    if solve:
        result = b_s.check()
        i = 1
        print('---blanket for : [ ', ' '.join(lins), ' ]---')
        while result == sat:
            m = b_s.model()
            print('blanket',i,' : ',end='')
            counter = T
            for pname, p in ps.items():
                for x in universe:
                    for y in universe-{x}:
                        if m[v(p.name+x+'{'+y)]:
                            print(p.name+x+'{'+y,' ',end='')
                        if m[v(p.name+x+'<'+y)]:
                            counter = And(counter, v(p.name+x+'<'+y))
                        else:
                            counter = And(counter, Not(v(p.name+x+'<'+y)))
            b_s.add(Not(counter))
            result = b_s.check()
            i = i+1
            print()
        print('---end---\n')

    return (universe, constraints, ps, ls) if not solve else None

def poset_cover(k=1, *lins, solve=True):
    '''
    k : the number of covering posets
    ls : linearizations as strings
    '''
    c_s = Solver()

    # build atop poset blanket
    universe, constraints, ps, ls = poset_blanket(k, *lins, solve=False)
    c_s.add(constraints)

    # {absent} = {permutations} - linears
    absent = {''.join(p) for p in permutations(lins[0])} - set(lins)
    # l not generated by any p:
    # forall p, forall l, exists l_x<y, p_y<x
    for pname, p in ps.items():
        for w in absent:
            pA = F
            for i in range(len(w)):
                for j in range(i+1,len(w)):
                    pA = Or(pA , v(p.name+w[j]+'<'+w[i]))
            c_s.add(pA)
            constraints = simplify(And(constraints , pA))

    if solve:
        result = c_s.check()
        i = 1
        print('---cover for : [ ', ' '.join(lins), ' ]---')
        while result == sat:
            m = c_s.model()
            print('cover',i,' : ',end='')
            counter = T
            for x in universe:
                for y in universe-{x}:
                    for pname, p in ps.items():
                        #if m[v(p.name+x+'{'+y)]:
                            #print(p.name+x+'{'+y,' ',end='')
                        if m[v(p.name+x+'<'+y)]:
                            print(p.name+x+'<'+y,' ',end='')
                            counter = And(counter, v(p.name+x+'<'+y))
                        else:
                            counter = And(counter, Not(v(p.name+x+'<'+y)))
            #print('\n',simplify(counter))
            c_s.add(Not(simplify(counter)))
            result = c_s.check()
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

#a = poset({'1','2','3','4','5'}, rel=['1<4','2<4','2<5','3<5'])
#a.print_linearizations()
#a = poset({'1','2','3','4','5'}, rel=['1<4','1<2','1<5','3<2','3<4','3<5','2<4','2<5'])
#a = poset({'1','2','3','4','5'}, rel=['1<4','2<4','2<5','3<5','1<5','3<4'])
#a = poset({'1','2','3','4','5'}, rel=['1<4','3<5','1<5','3<4','3<2'])
#poset({'1','2','3','4','5'}, rel=['1<4','3<5','1<5','3<4','3<2'])
#a.print_linearizations()
#a = poset({'1','2','3','4','5'})
#from time import time as t
#t1 = t()
#poset_blanket(3,'12354','43125','54231',solve=True)
#print(t()-t1)

poset_cover(2, *l3, solve=True)

# TODO:
#       2) furthur testing with more complex poset
#       3) test it with multiple poset ; ie poset cover problem
#       4) this many clauses? are you fucking kidding me? can you not?
#          must find a way to make it more efficient
#          maybe automaton would help after all?

#cover_from_order(5,'2<4','1<5','1<4','2<1','2<5','5<4','2<3','3<5','3<4','1<3')
