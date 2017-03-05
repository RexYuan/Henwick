#!/usr/bin/python
""" 
Note: set PYTHONPATH=$Z3PATH:$PYTHONPATH

Loop invariant for McCarthy 91

    int mccarthy91 (int n) {
      int c;
      int ret;
      ret = n;
      c = 1;
      while (c > 0) {
        if (ret > 100) {
          ret = ret - 10;
          c--;
        } else {
          ret = ret + 11;
          c++;
        }
      }
      return ret;
    }  

"""

from z3 import *

n = Int ('n')
ret = Int ('ret')
c = Int ('c')

solver = Solver ()

def pre (eta):
    b_true  = Implies (ret > 100, 
                       substitute (substitute (eta, (c, c - 1)),
                                   (ret, ret - 10)))
    b_false = Implies (Not (ret > 100),
                       substitute (substitute (eta, (c, c + 1)),
                                   (ret, ret + 11)))
    return And (b_true, b_false)

def check_implies (phi, psi):
    solver.push ()
    f = And (phi, Not (psi))
    solver.add (f)
    result = solver.check ()
    if result == sat:
        print '(n, ret, c) = (', solver.model()[n], solver.model()[ret], solver.model()[c], ')'
    solver.pop ()
    return result != sat

def check_pre (pre, eta, name):
    result = check_implies (pre, eta)
    result_str = 'pass' if result else 'fail'
    print 'check precondition ({0}): {1}'.format (name, result_str)
    return result

def check_post (eta, post, name):
    result = check_implies (And (Not (c > 0), eta), post)
    result_str = 'pass' if result else 'fail'
    print 'check postcondition ({0}): {1}'.format (name, result_str)
    return result

def check_invariant (eta, name):
    result = check_implies (And (c > 0, eta), pre (eta))
    result_str = 'pass' if result else 'fail'
    print 'check invariant ({0}): {1}'.format (name, result_str)
    return result

""" { n > 100 } ret = mccarthy91(n) { ret == n - 10 } """

eta_easy = And (c >= 0, n > 100, ret == n - 10 + 10 * c)

check_pre (And (n > 100, ret == n, c == 1), eta_easy, 'easy')
check_invariant (eta_easy, 'easy')
check_post (eta_easy, ret == n - 10, 'easy')

""" { n <= 100 } ret = mccarthy91(n) { ret == 91 } """

eta_hard = And (Implies (ret >=  90, And (91 - c <= ret, ret <= 91 + 10 * c)),
                Implies (ret <   90, c > 0))

check_pre (And (n <= 100, ret == n, c == 1), eta_hard, 'hard')
check_invariant (eta_hard, 'hard')
check_post (eta_hard, ret == 91, 'hard')

""" { true } ret = mccarthy91(n) { (n  > 100 ==> ret == n - 10) &&
                                   (n <= 100 ==> ret == 91) } """

eta = And (Implies (n > 100, eta_easy), Implies (n <= 100, eta_hard))

check_pre (And (n <= 100, ret == n, c == 1), eta, 'all')
check_invariant (eta, 'all')
check_post (eta, And (Implies (n >  100, ret == n - 10),
                      Implies (n <= 100, ret == 91)), 'all')

