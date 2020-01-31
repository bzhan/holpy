# Author: Bohua Zhan

from kernel.type import TFun
from kernel.term import Const
from logic.conv import Conv, rewr_conv, refl, arg_conv, arg1_conv
from data import nat
from data.nat import natT
from data.set import setT

def mk_interval(m, n):
    return Const("nat_interval", TFun(natT, natT, setT(natT)))(m, n)

def is_interval(t):
    return t.is_binop() and t.head.is_const_name("nat_interval")

class numseg_conv(Conv):
    """Evaluate {m..n} to a concrete set. Here m and n are specific
    numerals.
    
    """
    def get_proof_term(self, t):
        assert is_interval(t), "numseg_conv"
        mt, nt = t.args
        m, n = nat.from_binary_nat(mt), nat.from_binary_nat(nt)
        pt = refl(t)
        if n < m:
            less_goal = nat.less(nt, mt)
            less_pt = nat.nat_const_less_macro().get_proof_term(less_goal, [])
            return pt.on_rhs(rewr_conv("numseg_emptyI", conds=[less_pt]))
        else:
            le_goal = nat.less_eq(mt, nt)
            le_pt = nat.nat_const_less_eq_macro().get_proof_term(le_goal, [])
            return pt.on_rhs(rewr_conv("numseg_lrec", conds=[le_pt]),
                             arg_conv(arg1_conv(nat.nat_conv())),
                             arg_conv(self))
