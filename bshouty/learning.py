
from base import *

class InvTeacher(BoolTeacher[z3Formula, Assignment]):
    def __init__(self, bits : int, inits : z3Formula, bads : z3Formula, trans : z3Formula) -> None:
        self.bits = bits
        self.inits = inits
        self.bads = bads
        self.trans = trans
        self.s = Solver()

    def check(self, form : z3Formula) -> Optional[ Assignment ]:
        self.s.reset()
        self.s.add( form )
        if self.s.check() == sat:
            return z3_model_to_asgmt( self.s.model() , self.bits )
        return None
    
    def check_inits(self, hyp : z3Formula) -> Optional[ Assignment ]:
        '''
        c1) inits => inv
        '''
        return self.check( Not(Implies(self.inits , hyp)) )
    
    def check_bads(self, hyp : z3Formula) -> Optional[ Assignment ]:
        '''
        c2) inv => ~bads
        '''
        return self.check( Not(Implies(hyp , self.bads)) )
    
    def check_trans(self, hyp : z3Formula) -> Optional[ Assignment ]:
        '''
        c3) inv & trans => inv'
        '''
        hypp = substitute( hyp , *zip(z3_bool_range(self.bits),
                                    z3_bool_range(self.bits,self.bits*2)) )
        return self.check( Not(Implies(And(hyp,self.trans) , hypp)) )

    def init_checks(self) -> bool:
        '''
        make sure inits and bads dont intersect already
        '''
        return self.check( And(self.inits, self.bads) ) is None

class CdnfLearner(BoolLearner[z3Formula, Assignment]):
    def __init__(self, oracle : InvTeacher) -> None:
        self.oracle = oracle
        self.basis_len = 0
        self.basis : List[Assignment] = []
        self.dnfs : List[Dnf] = []
        self.dnf_funcs : List[BoolFunc] = []
        self.og_dnfs : List[Dnf] = []
        self.z3_forms : List[z3Formula] = []

        self.resulth = None
        self.resultf = None

    def learn(self) -> bool:
        oracle = self.oracle
        basis_len = self.basis_len
        basis = self.basis
        dnfs = self.dnfs
        dnf_funcs = self.dnf_funcs
        og_dnfs = self.og_dnfs
        z3_forms = self.z3_forms
        
        if oracle.init_checks() != True:
            return False
        
        # TODO learn but how?
        
        return True

    def result(self) -> Optional[ z3Formula ]:
        if self.result is None:
            raise Exception()
        return self.resulth

    def result_func(self) -> Optional[ Callable[ [Assignment] , bool ] ]:
        if self.result_func is None:
            raise Exception()
        return self.resultf

t = InvTeacher(0, BoolVal(True), BoolVal(True), BoolVal(True))
l = CdnfLearner(t)