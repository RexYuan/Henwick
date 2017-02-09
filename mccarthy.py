'''
Check if some ETA is appropriate as an loop invariant for mccarthy91 function
'''

def mccarthy91(n):
    '''
    if n > 100 returns n - 10
    else returns 91
    '''
    ret = n
    c = 1
    while (c > 0):
        if (ret > 100):
            ret = ret - 10
            c -= 1
        else:
            ret = ret + 11
            c += 1
    return ret

#print('mccarthy91(100) =', mccarthy91(100)) # 91
#print('mccarthy91(102) =', mccarthy91(102)) # 92

from z3 import *

# Initially, we have n, ret, and c, such that ret == n and c == 1:
# And(ret == n, c == 1)
# In the end, we shall have (n <= 100) => (ret == 91) and (n > 100) => (ret == n - 10):
# And(Implies(n <= 100, ret == 91), Implies(n > 100, ret == n - 10))

# For an invariant ETA to satisfy this loop and its pre/post-conditions, it must hold that
# 1. (|B and ETA|) C (|ETA|) with B being c > 0 and C being the inner ITE expression
# 2. |- PHI => ETA with PHI being the loop's precondition
# 3. |- ETA and not B => PSI with PSI being the loop's post-condition

# Namely,
# 1. (|c > 0 and ETA|) if (ret > 100) {ret = ret - 10; c -= 1} else {ret = ret + 11; c += 1} (|ETA|)
# for the Partial-while proof rule to get us a while sentence
# 2. |- (ret == n and c == 1) => ETA
# 3. |- (ETA and c <= 0) => (((n <= 100) => (ret == 91)) and ((n > 100) => (ret == n - 10)))
# for the Implied proof rule to get us to the while sentence with corresponding pre/post-conditions
# specified by the function definition of mccarthy91

# For the second and third requirements, since SMT solver checks satisfiability instead of
# validity, we can check the validity of the implication by checking the satisfiability of
# their negation, because, if an implication's negation is unsatisfiable, then it is valid
# because it's un-negatble; there's no situation that falsifies it
# Thus, to construct a handy function to check the validity of some implication PHI => PSI
def isImpValid(solver, imp):
    solver.push()
    solver.add(Not(imp))
    result = solver.check()
    solver.pop()
    return result == unsat

# For the first requirements, we examine if-command and deduce that, for it to reach some ETA
# state, it must, per the modified if-proof rule, starts at some state that satisfies
# ((ret > 100) => PHI1) and ((ret <= 100) => PH2) where PH1 and PH2 are the preconditions of
# the subsection of if-branch, namely the precondition of the program that'd be execute if
# (ret > 100) and that if not. From there, we prove, using again Implied rule, that it follows
# from the precondition (c > 0 and ETA). If they hold, then we can use the Partial-while rule
# to get (|ETA|) while (c > 0) { if (ret > 100) {ret = ret - 10; c -= 1} else {ret = ret + 11; c += 1} } (|ETA and c <= 0|),
# and, together with the previous second and third requirements, arrive at the conclusion that
# it is indeed the case that (| ret == n and c == 1 |) while (c > 0) { if (ret > 100) {ret = ret - 10; c -= 1} else {ret = ret + 11; c += 1} } (| ((n <= 100) => (ret == 91)) and ((n > 100) => (ret == n - 10)) |)
# Formatted:
# (| ret == n and c == 1 |)
# while (c > 0)
# {
#     if (ret > 100)
#     {
#         ret = ret - 10;
#         c -= 1
#     }
#     else
#     {
#         ret = ret + 11;
#         c += 1
#     }
# }
# (| ((n <= 100) => (ret == 91)) and ((n > 100) => (ret == n - 10)) |)
# And that's the mccarthy91 algorithm.
# So, what we need to check here is just if
# (c > 0 and ETA) implies
# ((ret > 100) => PHI1) and ((ret <= 100) => PH2)
# which we can check using the isImpValid function from last section.
# But exactly what PH1 and PH2 are influence our approach.
# Deriving from the proof of the if section, which is:
# (| c > 0 and ETA |) Implied
# (| (ret > 100) => PHI1) and ((ret <= 100) => PH2 |) If
#     if (ret > 100)
#     {
#         (| ETA[c-1 / c][ret-10 / ret] |) Assignment
#             ret = ret - 10;
#         (| ETA[c-1 / c] |) Assignment
#             c -= 1
#         (| ETA |) If
#     }
#     else
#     {
#         (| ETA[c+1 / c][ret+11 / ret] |) Assignment
#             ret = ret + 11;
#         (| ETA[c+1 / c] |) Assignment
#             c += 1
#         (| ETA |) If
#     }
# (| ETA |) If
# So, those preconditions are:
# PH1, the precondition when ret > 100 is true: ETA[c-1 / c][ret-10 / ret]
# PH2, the precondition when ret > 100 is false: ETA[c+1 / c][ret+11 / ret]
# From here we see that these two formulae are some substitutions, and
# we do them like this:
# For ETA[c+1 / c]: substitute(ETA, (c, c+1))
# For ETA[c+1 / c][ret+11 / ret]: substitute(substitute(ETA, (c, c+1)), (ret, ret+11))
# And now, to return to the originally problem, checking the third requirement
# is just to check the validity of
# (c > 0 and ETA) => (ret > 100 => ETA[c-1 / c][ret-10 / ret]) and (ret <= 100 => ETA[c+1 / c][ret+11 / ret])
# and we're done!

# Let's look at our goal again- to check if some ETA is suitable for proving the
# mccarthy91 algorithm. Now we know what it takes for some ETA to be eligible
# and how to check those eligibility. We're poised to finish the problem.
# We'll define a function checkInvariant that decides if some formula is eligible.
def checkInvariant(eta):
    # check first requirement
    firstReq = Implies(And(c > 0, eta), And(Implies(ret > 100, substitute(substitute(eta, (c, c-1)), (ret, ret-10))), Implies(ret <= 100, substitute(substitute(eta, (c, c+1)), (ret, ret+11)))))
    if not isImpValid(s, firstReq):
        raise Exception("firstReq failed")
    # check second requirement
    secondReq = Implies(And(ret == n, c == 1), eta)
    if not isImpValid(s, secondReq):
        raise Exception("secondReq failed")
    # check third requirement
    thirdReq = Implies(And(eta, c <= 0), And(Implies((n <= 100), (ret == 91)), Implies((n > 100), (ret == n - 10))))
    if not isImpValid(s, thirdReq):
        raise Exception("thirdReq failed")
    # if all three requirements are met(all three implications are valid),
    # then we are done, and the eta is suitable
    print("Success")
    return True
# init solver
s = Solver()
n = Int('N')
ret = Int('RET')
c = Int('C')
# check eta
eta = # NOTE: I can't figure out an eta ;(
checkInvariant(eta)
