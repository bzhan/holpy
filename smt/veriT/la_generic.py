import math
from fractions import Fraction
from decimal import Decimal

from kernel import term as hol_term
from kernel import type as hol_type
from collections.abc import Iterable
from smt.veriT.verit_macro import VeriTException
from data import real
from data import integer
from kernel.thm import Thm
from kernel.macro import Macro
from kernel.theory import register_macro
from logic import logic

def norm_int_expr(t):
    return from_int_la(to_la(t))
    
def norm_real_expr(t):
    return from_real_la(to_la(t))


def collect_pairs(ps):
    """Reduce a list of pairs by collecting into groups according to
    first components, and adding the second component for each group.

    It is assumed that the first components are hashable.

    e.g. [("x", 1), ("y", 2), ("x", 3)] => [("x", 4), ("y", 2)]

    """
    res = {}
    for v, c in ps:
        if v in res:
            res[v] += c
        else:
            res[v] = c
    return tuple([(k, v) for k, v in res.items() if v != 0])

def eval_hol_number(tm):
    assert tm.is_number()
    if tm.get_type() == hol_type.IntType:
        return integer.int_eval(tm)
    elif tm.get_type() == hol_type.RealType:
        return real.real_eval(tm)
    else:
        raise NotImplementedError


class LinearArith:
    """Representation of a linear arithmetic expression, 
    - const: the constant part
    - lps: pairs of linear multiplication, e.g. 3 * x + 2 * y = [(x, 3), (y, 2)]    
    """
    def __init__(self, const=0, lps=tuple()) -> None:
        assert isinstance(const, (int, Fraction, Decimal))
        assert isinstance(lps, Iterable) and\
             all(isinstance(c, (int, Fraction, Decimal)) for _, c in lps)
        self.const = const
        self.lps = collect_pairs(tuple(lps))

    def __str__(self) -> str:
        if len(self.lps) == 0:
            return str(self.const)
        
        return "%s + %s" % (self.const, " + ".join("%s * %s" % (c, v) for v, c in self.lps))
    
    def __eq__(self, other) -> bool:
        return self.const == other.const and self.lps == other.lps

    def __add__(self, other):
        return LinearArith(self.const+other.const, self.lps+other.lps)
    
    def __neg__(self):
        return LinearArith(-self.const, [(v, -c) for v, c in self.lps])

    def __sub__(self, other):
        return self + -other

    def __rmul__(self, other):
        assert isinstance(other, (int, Fraction, Decimal))
        return LinearArith(other * self.const, [(v, other * c) for v, c in self.lps])

    def __len__(self):
        return len(self.lps)

def to_la(tm: hol_term.Term) -> LinearArith:
    if tm.is_number():
        return LinearArith(const=eval_hol_number(tm))
    elif tm.is_var():
        return LinearArith(lps=((tm, 1),))
    if tm.is_plus():
        return to_la(tm.arg1) + to_la(tm.arg)
    elif tm.is_uminus():
        return -to_la(tm.arg)
    elif tm.is_minus():
        return to_la(tm.arg1) - to_la(tm.arg)
    elif tm.is_times():
        assert tm.arg1.is_number()
        return eval_hol_number(tm.arg1) * to_la(tm.arg)
    else: 
        return LinearArith(const=1, lps=((tm, 1),))

def from_int_la(la: LinearArith) -> hol_term.Term:
    hol_const = hol_term.Int(la.const)
    if len(la) == 0:
        return hol_const
    
    hol_pairs = [hol_term.Int(i) * v if i != 1 else v for v, i in la.lps]

    return hol_const + sum(hol_pairs[1:], hol_pairs[0])


def from_real_la(la):
    hol_const = hol_term.Real(la.const)
    if len(la) == 0:
        return hol_const
    
    hol_pairs = [hol_term.Real(i) * v if i != 1 else v for v, i in la.lps]

    return hol_const + sum(hol_pairs[1:], hol_pairs[0])




def analyze_args(coeffs):
    """Convert all coeffs to integer."""
    denoms = []
    for coeff in coeffs:
        if coeff.is_comb("real_divide"): # fraction coeff
            denoms.append(integer.int_eval(coeff.arg))
    if len(denoms) == 0:
        return coeffs
    # compute the lcm of denoms
    lcm = 1
    for d in denoms:
        lcm = int(lcm * d / math.gcd(lcm, d))
    return [int(lcm) * c for c in coeffs]

@register_macro("verit_la_generic")
class LAGenericMacro(Macro):
    def __init__(self):
        self.level = 1
        self.sig = hol_term.Term
        self.limit = None

    def eval(self, args, prevs=None):
        dis_eqs, coeffs = args[:-1], args[-1]
        if not isinstance(coeffs, Iterable) or not all(coeff.is_number() for coeff in coeffs):
            print(coeffs)
            raise VeriTException("la_generic", "should supply a list of numbers")


        dis_eq = dis_eqs[0]
        if dis_eq.is_not():
            dis_eq = dis_eq.arg
        T = dis_eq.arg.get_type()
        assert T in (hol_type.RealType, hol_type.IntType), "unexpected type"
        # assert dis_eq.arg.get_type() == hol_type.IntType
        is_real = True if T == hol_type.RealType else False
        zero = hol_term.Real(0) if is_real else hol_term.Int(0)
        eval_const = real.real_eval if is_real else integer.int_eval
        norm = norm_real_expr if is_real else norm_int_expr
        hol_num = hol_term.Real if is_real else hol_term.Int


        # Step 1: convert each disequality to a greater/greater_eq disequality
        dis_eq_step1 = []
        for dis_eq in dis_eqs:
            if dis_eq.is_equals():
                raise VeriTException("la_generic", "clause can't contain any equality")
            # For the reason that all disequalities we met are either less or less_eq, 
            # for simplicity of implementation, we will do some aggressive checking
            if dis_eq.is_not():
                dis_eq_bd = dis_eq.arg
                if not dis_eq_bd.is_compares() and not dis_eq_bd.is_equals():
                    raise VeriTException("la_generic", "non-equality should contain a comparison")
                T = dis_eq_bd.arg.get_type()
                if dis_eq_bd.is_greater() or dis_eq_bd.is_greater_eq():
                    raise VeriTException("la_generic", "all disequalities are either less or less_eq")
                if dis_eq_bd.is_equals():
                    dis_eq_step1.append(dis_eq_bd)
                elif dis_eq_bd.is_less():
                    dis_eq_step1.append(hol_term.greater(T)(dis_eq_bd.arg, dis_eq_bd.arg1))
                elif dis_eq_bd.is_less_eq():
                    dis_eq_step1.append(hol_term.greater_eq(T)(dis_eq_bd.arg, dis_eq_bd.arg1))
                else:
                    raise VeriTException("la_generic", "unexpected disequality")
            else:
                dis_eq_bd = dis_eq
                T = dis_eq_bd.arg.get_type()
                if dis_eq_bd.is_greater() or dis_eq_bd.is_greater_eq():
                    raise VeriTException("la_generic", "all disequalities are either less or less_eq")
                if dis_eq_bd.is_less():
                    dis_eq_step1.append(hol_term.greater_eq(T)(dis_eq_bd.arg1, dis_eq_bd.arg))
                elif dis_eq_bd.is_less_eq():
                    dis_eq_step1.append(hol_term.greater(T)(dis_eq_bd.arg1, dis_eq_bd.arg))
                else:
                    print(dis_eq_bd)
                    raise VeriTException("la_generic", "unexpected disequality")

        # Step 2: move terms on rhs to left, move constants on lhs to right
        dis_eq_step2 = [] # left <> right ---> left - right <> 0
        for dis_eq in dis_eq_step1:
            norm_lhs = norm(dis_eq.arg1 - dis_eq.arg)

            sum_tms = integer.strip_plus(norm_lhs)
            left_most_tm = sum_tms[0]
            if not left_most_tm.is_number():
                dis_eq_step2.append(dis_eq.head(norm_lhs, zero))
            else:
                neg_num = hol_num(eval_const(-left_most_tm))
                if len(sum_tms) > 1:
                    rest_tm = sum(sum_tms[2:], sum_tms[1])
                else:
                    rest_tm = zero
                dis_eq_step2.append(dis_eq.head(rest_tm, neg_num))
        
        if not is_real:
        # if d is integer, convert l > d -->  l >= d+1
            for i in range(len(dis_eq_step2)):
                dis_eq = dis_eq_step2[i]
                T = dis_eq.arg1.get_type()
                if T == hol_term.IntType and dis_eq.is_greater():
                    suc_d = integer.int_eval(dis_eq.arg) + 1
                    dis_eq_step2[i] = hol_term.greater_eq(T)(dis_eq.arg1, hol_term.Int(suc_d))

        # Optional step: if there is only one disequality in clause, after Step 2,
        # both side of disequality would be constants, we can compare them directly 
        # without having to performing remainning steps.
        if len(dis_eqs) == 1:
            dis_eq = dis_eq_step2[0]
            lhs, rhs = dis_eq_step2[0].args
            if not lhs.is_number() or not rhs.is_number():
                raise VeriTException("la_generic", 
                        "after step 2, both sides would be constants if there is only one disequality")
            lhs, rhs = integer.int_eval(lhs), integer.int_eval(rhs)
            if dis_eq.is_equals():
                if lhs != rhs:
                    return Thm(dis_eqs[0])
                else:
                    raise VeriTException("la_generic", "unexpected result: %s" % dis_eqs[0])
            elif dis_eq.is_greater():
                if not lhs > rhs:
                    return Thm(dis_eqs[0])
                else:
                    raise VeriTException("la_generic", "unexpected result: %s" % dis_eqs[0])
            elif dis_eq.is_greater_eq():
                if not lhs >= rhs:
                    return Thm(dis_eqs[0])
                else:
                    raise VeriTException("la_generic", "unexpected results: %s" % dis_eqs[0])
            else:
                raise VeriTException("la_generic", "disequality should not be less or less_eq: %s" % dis_eq)
        
        
        # if all variables are integers, convert all coeffs to integer
        if not is_real:
            coeffs = analyze_args(coeffs)
                

        # Step 3: multiply each disequality with coeffs
        dis_eq_step3 = []
        assert len(coeffs) == len(dis_eq_step2)

        for coeff, dis_eq in zip(coeffs, dis_eq_step2): 
            lhs, rhs = dis_eq.args
            if not dis_eq.is_equals(): # coeff should be absoluted
                abs_coeff = hol_num(abs(eval_const(coeff)))
            else:
                abs_coeff = coeff
            c_lhs, c_rhs = norm(abs_coeff * lhs), norm(abs_coeff * rhs)
            dis_eq_step3.append(dis_eq.head(c_lhs, c_rhs))

        # Step 4: compare the sum of all lhs and the sum of all rhs
        diseq_lhs = [dis_eq.arg1 for dis_eq in dis_eq_step3]
        diseq_rhs = [dis_eq.arg for dis_eq in dis_eq_step3]
        lhs_sum = sum(diseq_lhs[1:], diseq_lhs[0])
        rhs_sum = sum(diseq_rhs[1:], diseq_rhs[0])
        lhs_sum_norm, rhs_sum_norm = norm(lhs_sum), norm(rhs_sum)
        if not lhs_sum_norm.is_number() or not rhs_sum_norm.is_number():
            raise VeriTException("la_generic", 
                "after multiplying coeffs, both sides should be number")
        lhs_const, rhs_const = eval_const(lhs_sum_norm), eval_const(rhs_sum_norm)
        cond = False
        if all(dis_eq.is_equals() for dis_eq in dis_eq_step1):
            cond = (rhs_const != lhs_const)
        elif all(dis_eq.is_equals() or dis_eq.is_greater_eq() for dis_eq in dis_eq_step1):
            cond = (rhs_const > lhs_const) # lhs <= rhs -> check 
        else:
            cond = (rhs_const >= lhs_const)

        if cond:
            return Thm(hol_term.Or(*args[:-1]))
        else:
            raise VeriTException("la_generic", "unexpected result: %s, %s" % (lhs_const, rhs_const))