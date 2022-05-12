import math
from fractions import Fraction
from decimal import Decimal
import functools

from kernel import term as hol_term
from kernel import type as hol_type
from collections.abc import Iterable
from smt.veriT.verit_macro import VeriTException
from data import real
from data import integer
from kernel.thm import Thm
from kernel.macro import Macro
from kernel.theory import register_macro
from kernel.proofterm import ProofTerm, refl
from logic import logic
from logic.conv import rewr_conv, arg1_conv, binop_conv, replace_conv, top_conv, arg_conv, Conv
from smt.veriT import verit_conv

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
    assert tm.is_constant()
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
    if tm.is_constant():
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
        assert tm.arg1.is_constant()
        return eval_hol_number(tm.arg1) * to_la(tm.arg)
    else: 
        return LinearArith(const=0, lps=((tm, 1),))

def from_int_la(la: LinearArith) -> hol_term.Term:
    c = la.const
    hol_const = hol_term.Int(c)
    if len(la) == 0:
        return hol_const
    
    hol_pairs = [hol_term.Int(i) * v if i != 1 else v for v, i in la.lps]

    return c + sum(hol_pairs[1:], hol_pairs[0])


def from_real_la(la):
    hol_const = hol_term.Real(la.const)
    if len(la) == 0:
        return hol_const
    
    hol_pairs = [hol_term.Real(i) * v if i != 1 else v for v, i in la.lps]

    return hol_const + sum(hol_pairs[1:], hol_pairs[0])




def analyze_args(coeffs):
    """Convert all coeffs to integer."""
    denoms = []
    _coeffs = []
    for coeff in coeffs:
        if coeff.is_comb("real_divide"): # fraction coeff
            denoms.append(integer.int_eval(coeff.arg))
            _coeffs.append(integer.int_eval(coeff.arg1)/integer.int_eval(coeff.arg))
        else:
            _coeffs.append(integer.int_eval(coeff))

    if len(denoms) == 0:
        return coeffs
    # compute the lcm of denoms
    lcm = 1
    for d in denoms:
        lcm = int(lcm * d / math.gcd(lcm, d))
    return [hol_term.Int(int(lcm * c)) for c in _coeffs]


@register_macro("verit_norm_lia")
class NormLIAMacro(Macro):
    def __init__(self):
        self.level = 1
        self.sig = hol_term.Term
        self.limit = None

    def eval(self, args, prevs=None) -> Thm:
        goal = args[0]
        return Thm(hol_term.Eq(goal, from_int_la(to_la(goal))))

    def get_proof_term(self, args, prevs) -> ProofTerm:
        goal = args[0]
        return verit_conv.norm_lia_conv().get_proof_term(goal)




@register_macro("verit_norm_lra")
class NormLRAMacro(Macro):
    def __init__(self):
        self.level = 1
        self.sig = hol_term.Term
        self.limit = None

    def eval(self, args, prevs=None) -> Thm:
        goal = args[0]
        return Thm(hol_term.Eq(goal, from_real_la(to_la(goal))))

    def get_proof_term(self, args, prevs) -> ProofTerm:
        goal = args[0]
        return verit_conv.norm_lra_conv().get_proof_term(goal)


def coeffs_gcd(sum_tm: hol_term.Term) -> int:
    """Compute the gcd of coefficients (note: gcd should be a positive number)"""
    la = to_la(sum_tm)
    if la.const != 0:
        raise AssertionError("when computing coeffs gcd, left side should not have constants")
    
    coeffs = [c for _, c in la.lps]
    return abs(functools.reduce(math.gcd, coeffs[1:], coeffs[0]))
    
class extract_gcd_conv(Conv):
    """rewrite a linear disequality c_1 * x_1 + ... + c_n * x_n ⋈ c to 
        k * (c_1' * x_1 + ... + c_n' * x_n) ⋈ c, where k = gcd(c_1, ..., c_n)."""
    def get_proof_term(self, t: hol_term.Term) -> ProofTerm:
        pt = refl(t)
        if not t.is_greater_eq():
            return pt
        lhs = t.arg1
        la = to_la(lhs)
        k  = coeffs_gcd(lhs)
        body = tuple(hol_term.Int(int(c / k)) * v for v, c in la.lps)
        pt_eq1 = ProofTerm("verit_norm_lia", [hol_term.Int(k) * sum(body[1:], body[0])])
        pt_eq2 = ProofTerm("verit_norm_lia", [lhs])
        return pt.on_rhs(arg1_conv(replace_conv(ProofTerm.transitive(pt_eq2, pt_eq1.symmetric()))))

@register_macro("verit_round_lia")
class RoundLiaMacro(Macro):
    """round a linear integer disequality to a stronger form"""
    def __init__(self):
        self.level = 1
        self.sig = hol_term.Term
        self.limit = None

    def get_proof_term(self, args, prevs):
        goal = args
        pt = prevs[0]
        dis_eq = pt.prop
        if not dis_eq.is_greater_eq():
            return pt
        lhs = dis_eq.arg1
        la = to_la(lhs)
        k  = coeffs_gcd(lhs)
        body = tuple(hol_term.Int(int(c / k)) * v for v, c in la.lps)
        pt_eq1 = ProofTerm("verit_norm_lia", [hol_term.Int(k) * sum(body[1:], body[0])])
        pt_eq2 = ProofTerm("verit_norm_lia", [lhs])
        pt1 = pt.on_prop(extract_gcd_conv())
        # gcd
        k = coeffs_gcd(dis_eq.arg1)
        # |- k > 0
        pt_pos_k = ProofTerm("int_const_ineq", hol_term.greater(hol_type.IntType)(hol_term.Int(k), hol_term.Int(0)))
        # lower bound
        rhs = integer.int_eval(dis_eq.arg)
        lb = rhs // k
        # |- k * lb < rhs
        pt_lb_le_rhs = ProofTerm("int_const_ineq", hol_term.less(hol_type.IntType)(hol_term.Int(k) * hol_term.Int(lb), hol_term.Int(rhs)))
        # |- k * lb + k > rhs
        pt_lb_plus_k_ge_rhs = ProofTerm("int_const_ineq", hol_term.greater(hol_type.IntType)(hol_term.Int(k) * hol_term.Int(lb) + hol_term.Int(k), hol_term.Int(rhs)))
        # |- k > 0 ⟶ k * x ≥ c ⟶ k * lb < c ⟶ k * lb + k > c ⟶ k * x ≥ k * lb + k
        pt2 = logic.apply_theorem("verit_round_lia_gcd", pt_pos_k, pt1, pt_lb_le_rhs, pt_lb_plus_k_ge_rhs)
        pt_eq = ProofTerm.transitive(pt_eq1, pt_eq2.symmetric())
        return pt2.on_prop(arg1_conv(replace_conv(pt_eq)), arg_conv(integer.int_eval_conv()))

@register_macro("verit_la_generic")
class LAGenericMacro(Macro):
    def __init__(self):
        self.level = 1
        self.sig = hol_term.Term
        self.limit = None

    def eval(self, args, prevs=None) -> Thm:
        dis_eqs, coeffs = args[:-1], args[-1]
        if not isinstance(coeffs, Iterable) or not all(coeff.is_constant() for coeff in coeffs):
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
        # eval_const = real.real_eval if is_real else integer.int_eval
        def eval_const(tm):
            if tm.is_constant():
                if tm.get_type() == hol_type.RealType:
                    return real.real_eval(tm)
                elif tm.get_type() == hol_type.IntType:
                    return integer.int_eval(tm)
                else:
                    raise VeriTException("la_generic", "unexpected coeff type")
            else:
                return tm
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

        if T == hol_type.IntType:
            dis_eq_step_round = []
            # Additional step: if lhs can be rewrited to k * x ⋈ c, s.t. c > 0 /\ c < k, 
            # then we could rewrite the disquality to a strong form: k * x ⋈ k, where ⋈ is either > or ≥
            for dis_eq in dis_eq_step2:
                if dis_eq.arg1.is_constant() and dis_eq.arg.is_constant():
                    dis_eq_step_round.append(dis_eq)
                    continue
                k = coeffs_gcd(dis_eq.arg1)
                c = integer.int_eval(dis_eq.arg)
                if dis_eq.is_equals():
                    dis_eq_step_round.append(dis_eq)
                    continue
                if c > 0 and c % k != 0:
                    t = k * (c // k + 1)
                    round_dis_eq = hol_term.greater_eq(hol_type.IntType)(dis_eq.arg1, hol_term.Int(t))
                elif c < 0 and c % k != 0:
                    t = k * (c // k + 1)
                    round_dis_eq = hol_term.greater_eq(hol_type.IntType)(dis_eq.arg1, hol_term.Int(t))
                else:
                    round_dis_eq = dis_eq
                dis_eq_step_round.append(round_dis_eq)
            dis_eq_step2 = dis_eq_step_round

        # Step 3: multiply each disequality with coeffs
        dis_eq_step3 = []
        assert len(coeffs) == len(dis_eq_step2)

        for coeff, dis_eq in zip(coeffs, dis_eq_step2): 
            lhs, rhs = dis_eq.args
            if not dis_eq.is_equals(): # coeff should be absoluted
                abs_coeff = hol_term.Real(abs(eval_const(coeff)))
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
        if all(dis_eq.is_equals() for dis_eq in dis_eq_step3):
            cond = (rhs_const != lhs_const)
        elif all(dis_eq.is_equals() or dis_eq.is_greater_eq() for dis_eq in dis_eq_step3):
            cond = (rhs_const > lhs_const) # lhs <= rhs -> check 
        else:
            cond = (rhs_const >= lhs_const)
        if cond:
            return Thm(hol_term.Or(*args[:-1]))
        else:
            raise VeriTException("la_generic", "unexpected result: %s, %s" % (lhs_const, rhs_const))

    def get_proof_term_int(self, dis_eqs, coeffs) -> ProofTerm:
        coeffs = analyze_args(coeffs)
        # store the assumed negated disequalities
        step1_pts = []
        # store the equality proof terms which convert the 
        # negated disequalities to original equalities
        step1_neg_conv_pts = []
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
                    step1_pts.append(ProofTerm.assume(dis_eq_bd))
                    pt1 = refl(dis_eq)
                    step1_neg_conv_pts.append(pt1)            
                elif dis_eq_bd.is_less():
                    g = hol_term.greater(T)(dis_eq_bd.arg, dis_eq_bd.arg1)
                    step1_pts.append(ProofTerm.assume(g))
                    pt = logic.apply_theorem('verit_la_generic_neg_greater_int1', 
                                inst=hol_term.Inst(x=g.arg1, y=g.arg))
                    step1_neg_conv_pts.append(pt)
                elif dis_eq_bd.is_less_eq():
                    ge = hol_term.greater_eq(T)(dis_eq_bd.arg, dis_eq_bd.arg1)
                    step1_pts.append(ProofTerm.assume(ge))
                    pt = logic.apply_theorem('verit_la_generic_neg_greater_eq_int1',
                                inst=hol_term.Inst(x=ge.arg1, y=ge.arg))
                    step1_neg_conv_pts.append(pt)
                else:
                    raise VeriTException("la_generic", "unexpected disequality")
            else:
                dis_eq_bd = dis_eq
                T = dis_eq_bd.arg.get_type()
                if dis_eq_bd.is_greater() or dis_eq_bd.is_greater_eq():
                    raise VeriTException("la_generic", "all disequalities are either less or less_eq")
                if dis_eq_bd.is_less():
                    ge = hol_term.greater_eq(T)(dis_eq_bd.arg1, dis_eq_bd.arg)
                    step1_pts.append(ProofTerm.assume(hol_term.greater_eq(T)(dis_eq_bd.arg1, dis_eq_bd.arg)))
                    pt = logic.apply_theorem('verit_la_generic_neg_greater_eq_int2', 
                                    inst=hol_term.Inst(x=ge.arg1, y=ge.arg))
                    step1_neg_conv_pts.append(pt)
                elif dis_eq_bd.is_less_eq():
                    g = hol_term.greater(T)(dis_eq_bd.arg1, dis_eq_bd.arg)
                    step1_pts.append(ProofTerm.assume(g))
                    pt = logic.apply_theorem('verit_la_generic_neg_greater_int2', 
                                    inst=hol_term.Inst(x=g.arg1, y=g.arg))
                    step1_neg_conv_pts.append(pt)
                else:
                    print(dis_eq_bd)
                    raise VeriTException("la_generic", "unexpected disequality")
        # print("step1")
        # for pt in step1_pts:
        #     print("pt", pt)
        # print()
        # step 2: move terms on rhs to left, move constants on lhs to right
        step2_pts = []
        for step1_pt in step1_pts:
            if step1_pt.prop.is_greater():
                # pt_minus = step1_pt.on_prop(rewr_conv("int_gt"), arg1_conv(verit_conv.norm_lia_conv()))
                pt_minus = step1_pt.on_prop(rewr_conv("int_gt"))
            elif step1_pt.prop.is_greater_eq():
                # pt_minus = step1_pt.on_prop(rewr_conv("int_geq"), arg1_conv(verit_conv.norm_lia_conv()))
                pt_minus = step1_pt.on_prop(rewr_conv("int_geq"))
            elif step1_pt.prop.is_equals():
                # pt_minus = step1_pt.on_prop(rewr_conv("int_eq_move_left"), arg1_conv(verit_conv.norm_lia_conv()))
                pt_minus = step1_pt.on_prop(rewr_conv("int_eq_move_left"))
            else:
                raise VeriTException('la_generic', 'unexpected type of disequality (less, less_eq)')
            # step2_pts.append(pt_minus)
            pt_eq = ProofTerm("verit_norm_lia", [pt_minus.prop.arg1])
            pt_dis_eq = pt_minus.on_prop(arg1_conv(replace_conv(pt_eq)))
            if not pt_dis_eq.prop.arg1.is_plus() or not pt_dis_eq.prop.arg1.arg1.is_constant():
                step2_pts.append(pt_dis_eq)
                continue
            if pt_dis_eq.prop.is_greater_eq():
                pt_dis_eq = pt_dis_eq.on_prop(rewr_conv("verit_int_add_ge_move_right"), arg_conv(integer.int_eval_conv()))
            elif pt_dis_eq.prop.is_greater():
                pt_dis_eq = pt_dis_eq.on_prop(rewr_conv("verit_int_add_gt_move_right"), arg_conv(integer.int_eval_conv()))
            elif pt_dis_eq.prop.is_equals():
                pt_dis_eq = pt_dis_eq.on_prop(rewr_conv("verit_int_add_eq_move_right"), arg_conv(integer.int_eval_conv()))
            else:
                raise VeriTException("la_generic", "the direction of dis_eq should be >, ≥ or =")
            step2_pts.append(pt_dis_eq)
        
        # print("step2")
        # for pt in step2_pts:
        #     print("pt", pt.prop)
        # print()

        if len(step2_pts) == 1:
            pt = step2_pts[0]
            if not pt.prop.arg1.is_constant() or not pt.prop.arg.is_constant():
                raise VeriTException("la_generic", "unexpected result")
            if pt.prop.is_compares():
                pt1 = integer.int_norm_neg_compares().get_proof_term(hol_term.Not(pt.prop))
                pt2 = ProofTerm("int_const_ineq", args=pt1.rhs)

                pt_false = pt1.symmetric().equal_elim(pt2).on_prop(rewr_conv('eq_false')).equal_elim(pt)
            else:
                pt2 = ProofTerm("int_const_ineq", args=pt.prop)
                pt_false = pt2.on_prop(rewr_conv('eq_false')).equal_elim(pt)
            pt_imp_false = pt_false.implies_intr(pt_false.hyps[0]).on_prop(rewr_conv('imp_false_false'))
            pt_res = pt_imp_false.on_prop(replace_conv(step1_neg_conv_pts[0]))
            return pt_res

        # convert x > 0 --> x >= 1
        step3_pts = []
        for step2_pt in step2_pts:
            if step2_pt.prop.is_greater():
                step3_pts.append(step2_pt.on_prop(verit_conv.verit_norm_lia_greater_eq()))
            else:
                step3_pts.append(step2_pt)

        # print("step3")
        # for pt in step3_pts:
        #     print(pt.prop)
        #     print()
        # print()

        # Rounding
        step_round_pts = []
        for step3_pt in step3_pts:
            dis_eq = step3_pt.prop
            if dis_eq.is_equals() or dis_eq.arg1.is_constant() and dis_eq.arg.is_constant():
                step_round_pts.append(step3_pt)
                continue
            k = coeffs_gcd(dis_eq.arg1)
            c = integer.int_eval(dis_eq.arg)
            if c % k == 0:
                step_round_pts.append(step3_pt)
                continue
            pt1 = ProofTerm("verit_round_lia", None, prevs=[step3_pt])
            step_round_pts.append(pt1)
        
        step3_pts = step_round_pts

        # multiply two sides with coeff
        step4_pts = []
        for step3_pt, c in zip(step3_pts, coeffs):
            if step3_pt.prop.is_equals():
                # print("step3_pt", step3_pt)
                pt1 = logic.apply_theorem("zero_eq_mul_const", inst=hol_term.Inst(c=c, m=step3_pt.lhs, n=step3_pt.rhs)).implies_elim(step3_pt)
                pt_eq1 = ProofTerm("verit_norm_lia", [pt1.prop.arg1])
                pt_eq2 = ProofTerm("verit_norm_lia", [pt1.prop.arg])
                # pt2 = pt1.on_prop(binop_conv(verit_conv.const_prod_lia_conv()))
                pt2 = pt1.on_prop(arg1_conv(replace_conv(pt_eq1)), arg_conv(replace_conv(pt_eq2)))
                step4_pts.append(pt2)
                # pt = step3_pt.on_prop(rewr_conv("zero_eq_mul_const"), binop_conv(const_prod_lia_conv()))
            else:
                abs_c = abs(eval_hol_number(c))
                pt_abs = ProofTerm("int_const_ineq", hol_term.greater(hol_type.IntType)(hol_term.Int(abs_c), hol_term.Int(0)))
                pt = logic.apply_theorem('int_pos_mul_greater_eq', pt_abs, step3_pt)
                pt_eq1 = ProofTerm("verit_norm_lia", [pt.prop.arg1])
                pt_eq2 = ProofTerm("verit_norm_lia", [pt.prop.arg])
                step4_pts.append(pt.on_prop(arg1_conv(replace_conv(pt_eq1)), arg_conv(replace_conv(pt_eq2))))
        
        # print("step4")
        # for pt in step4_pts:
        #     print(pt)
        # print()

        # step5: add
        pt_final = step4_pts[0]
        for step4_pt in step4_pts[1:]:
            if pt_final.prop.is_equals() and step4_pt.prop.is_equals():
                pt = logic.apply_theorem('add_equals',
                         concl=hol_term.Eq(pt_final.prop.arg1 + step4_pt.prop.arg1, pt_final.prop.arg + step4_pt.prop.arg))
            elif pt_final.prop.is_equals() and step4_pt.prop.is_greater_eq():
                pt = logic.apply_theorem('add_eq_with_ge',
                         concl=hol_term.greater_eq(hol_type.IntType)(pt_final.prop.arg1 + step4_pt.prop.arg1, pt_final.prop.arg + step4_pt.prop.arg))
            elif pt_final.prop.is_greater_eq() and step4_pt.prop.is_equals():
                pt = logic.apply_theorem('add_ge_with_eq',
                         concl=hol_term.greater_eq(hol_type.IntType)(pt_final.prop.arg1 + step4_pt.prop.arg1, pt_final.prop.arg + step4_pt.prop.arg))
            elif pt_final.prop.is_greater_eq() and step4_pt.prop.is_greater_eq():
                pt = logic.apply_theorem('add_ge_with_ge',
                         concl=hol_term.greater_eq(hol_type.IntType)(pt_final.prop.arg1 + step4_pt.prop.arg1, pt_final.prop.arg + step4_pt.prop.arg))
            # print("pt     ", pt)
            # print("pt_final", pt_final)
            pt_final = pt.implies_elim(pt_final).implies_elim(step4_pt)
            pt_eq1 = ProofTerm("verit_norm_lia", [pt_final.prop.arg1])
            pt_eq2 = ProofTerm("verit_norm_lia", [pt_final.prop.arg])
            pt_final = pt_final.on_prop(arg1_conv(replace_conv(pt_eq1)), arg_conv(replace_conv(pt_eq2)))

        # print("pt_final", pt_final)
        # print()
        
        if not pt_final.prop.arg1.is_constant() or not pt_final.prop.arg.is_constant():
            raise VeriTException("la_generic", "unexpected result %s" % pt_final)
        
        pt_const_compare = integer.int_const_compares().get_proof_term(pt_final.prop)
        pt_false = pt_const_compare.equal_elim(pt_final)

        # print('equals')
        # for pt in step1_neg_conv_pts:
        #     print(pt)
        # print()

        # print(pt_false)
        for pt in reversed(step1_neg_conv_pts):
            pt_false = pt_false.implies_intr(pt.lhs.arg)
            if pt_false.prop.arg == hol_term.false:
                pt_false = pt_false.on_prop(rewr_conv("imp_false_false"), replace_conv(pt))
            else:
                pt_false = pt_false.on_prop(rewr_conv("imp_disj_eq"), arg1_conv(replace_conv(pt)))
    
        # print("pt_false", pt_false)
        if pt_false.prop == hol_term.Or(*dis_eqs):
            return pt_false
        else:
            raise VeriTException("la_generic", "unexpected result")

    def get_proof_term_real(self, dis_eqs, coeffs) -> ProofTerm:
        # store the assumed negated disequalities
        step1_pts = []
        # store the equality proof terms which convert the 
        # negated disequalities to original equalities
        step1_neg_conv_pts = []
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
                    step1_pts.append(ProofTerm.assume(dis_eq_bd))
                    pt1 = refl(dis_eq)
                    step1_neg_conv_pts.append(pt1)            
                elif dis_eq_bd.is_less():
                    g = hol_term.greater(T)(dis_eq_bd.arg, dis_eq_bd.arg1)
                    step1_pts.append(ProofTerm.assume(g))
                    pt = logic.apply_theorem('verit_la_generic_neg_greater_real1', 
                                inst=hol_term.Inst(x=g.arg1, y=g.arg))
                    step1_neg_conv_pts.append(pt)
                elif dis_eq_bd.is_less_eq():
                    ge = hol_term.greater_eq(T)(dis_eq_bd.arg, dis_eq_bd.arg1)
                    step1_pts.append(ProofTerm.assume(ge))
                    pt = logic.apply_theorem('verit_la_generic_neg_greater_eq_real1',
                                inst=hol_term.Inst(x=ge.arg1, y=ge.arg))
                    step1_neg_conv_pts.append(pt)
                else:
                    raise VeriTException("la_generic", "unexpected disequality")
            else:
                dis_eq_bd = dis_eq
                T = dis_eq_bd.arg.get_type()
                if dis_eq_bd.is_greater() or dis_eq_bd.is_greater_eq():
                    raise VeriTException("la_generic", "all disequalities are either less or less_eq")
                if dis_eq_bd.is_less():
                    ge = hol_term.greater_eq(T)(dis_eq_bd.arg1, dis_eq_bd.arg)
                    step1_pts.append(ProofTerm.assume(hol_term.greater_eq(T)(dis_eq_bd.arg1, dis_eq_bd.arg)))
                    pt = logic.apply_theorem('verit_la_generic_neg_greater_eq_real2', 
                                    inst=hol_term.Inst(x=ge.arg1, y=ge.arg))
                    step1_neg_conv_pts.append(pt)
                elif dis_eq_bd.is_less_eq():
                    g = hol_term.greater(T)(dis_eq_bd.arg1, dis_eq_bd.arg)
                    step1_pts.append(ProofTerm.assume(g))
                    pt = logic.apply_theorem('verit_la_generic_neg_greater_real2', 
                                    inst=hol_term.Inst(x=g.arg1, y=g.arg))
                    step1_neg_conv_pts.append(pt)
                else:
                    print(dis_eq_bd)
                    raise VeriTException("la_generic", "unexpected disequality")
        # print("step1")
        # for pt in step1_pts:
        #     print("pt", pt)
        # print()
        # step 2: move terms on rhs to left, move constants on lhs to right
        step2_pts = []
        for step1_pt in step1_pts:
            if step1_pt.prop.is_greater():
                # pt_minus = step1_pt.on_prop(rewr_conv("real_gt_sub"), arg1_conv(verit_conv.norm_lra_conv()))
                pt_minus = step1_pt.on_prop(rewr_conv("real_gt_sub"))
            elif step1_pt.prop.is_greater_eq():
                # pt_minus = step1_pt.on_prop(rewr_conv("real_geq_sub"), arg1_conv(verit_conv.norm_lra_conv()))
                pt_minus = step1_pt.on_prop(rewr_conv("real_geq_sub"))
            elif step1_pt.prop.is_equals():
                # pt_minus = step1_pt.on_prop(rewr_conv("real_sub_0", sym=True), arg1_conv(verit_conv.norm_lra_conv()))
                pt_minus = step1_pt.on_prop(rewr_conv("real_sub_0", sym=True))
            else:
                raise VeriTException('la_generic', 'unexpected type of disequality (less, less_eq)')
            pt_eq = ProofTerm("verit_norm_lra", [pt_minus.prop.arg1])
            step2_pts.append(pt_minus.on_prop(arg1_conv(replace_conv(pt_eq))))
        
        # print("step2")
        # for pt in step2_pts:
        #     print("pt", pt)
        # print()

        if len(step2_pts) == 1:
            pt = step2_pts[0]
            if not pt.prop.arg1.is_constant() or not pt.prop.arg.is_constant():
                raise VeriTException("la_generic", "unexpected result")
            if pt.prop.is_compares():
                pt1 = real.norm_neg_real_ineq_conv().get_proof_term(hol_term.Not(pt.prop))
                pt2 = ProofTerm("real_const_eq", args=pt1.rhs).on_prop(rewr_conv('eq_true',sym=True))

                pt_false = pt1.symmetric().equal_elim(pt2).on_prop(rewr_conv('eq_false')).equal_elim(pt)
            else:
                pt2 = ProofTerm("real_const_ineq", args=pt.prop)
                pt_false = pt2.on_prop(rewr_conv('eq_false')).equal_elim(pt)
            pt_imp_false = pt_false.implies_intr(pt_false.hyps[0]).on_prop(rewr_conv('imp_false_false'))
            pt_res = pt_imp_false.on_prop(replace_conv(step1_neg_conv_pts[0]))
            return pt_res
        

        # multiply two sides with coeff
        step3_pts = []
        for step2_pt, c in zip(step2_pts, coeffs):
            if step2_pt.prop.is_equals():
                pt1 = logic.apply_theorem("real_eq_zero_mul_const", inst=hol_term.Inst(c=c, x=step2_pt.prop.arg1)).implies_elim(step2_pt)
                pt_arg1_eq = ProofTerm("verit_norm_lra", [pt1.prop.arg1])
                pt_arg_eq = ProofTerm("verit_norm_lra", [pt1.prop.arg])                
                # pt2 = pt1.on_prop(binop_conv(verit_conv.const_prod_lra_conv()))
                pt2 = pt1.on_prop(arg1_conv(replace_conv(pt_arg1_eq)), arg_conv(replace_conv(pt_arg_eq)))
                step3_pts.append(pt2)
                # pt = step3_pt.on_prop(rewr_conv("zero_eq_mul_const"), binop_conv(const_prod_lia_conv()))
            elif step2_pt.prop.is_greater_eq():
                abs_c = abs(eval_hol_number(c))
                pt_abs = ProofTerm("real_const_ineq", hol_term.greater(T)(hol_term.Real(abs_c), hol_term.Real(0)))
                pt = logic.apply_theorem('verit_real_greater_eq_mul_const', pt_abs, step2_pt)
                pt_arg1_eq = ProofTerm("verit_norm_lra", [pt.prop.arg1])
                pt_arg_eq = ProofTerm("verit_norm_lra", [pt.prop.arg])  
                step3_pts.append(pt.on_prop(arg1_conv(replace_conv(pt_arg1_eq)), arg_conv(replace_conv(pt_arg_eq))))
            elif step2_pt.prop.is_greater():
                abs_c = abs(eval_hol_number(c))
                pt_abs = ProofTerm("real_const_ineq", hol_term.greater(T)(hol_term.Real(abs_c), hol_term.Real(0)))
                pt = logic.apply_theorem('verit_real_greater_mul_const', pt_abs, step2_pt)
                pt_arg1_eq = ProofTerm("verit_norm_lra", [pt.prop.arg1])
                pt_arg_eq = ProofTerm("verit_norm_lra", [pt.prop.arg])  
                step3_pts.append(pt.on_prop(arg1_conv(replace_conv(pt_arg1_eq)), arg_conv(replace_conv(pt_arg_eq))))
            else:
                raise VeriTException("la_generic", "unexpected form of disequality")
        
            
        
        # print("step3")
        # for pt in step3_pts:
        #     print(pt)
        # print()
        # step4: add
        pt_dct = {pt.prop: pt for pt in step3_pts}
        pt_final = step3_pts[0]
        for step3_pt in step3_pts[1:]:
            if pt_final.prop.is_equals() and step3_pt.prop.is_equals():
                pt = logic.apply_theorem('verit_real_add_eq_eq',
                         concl=hol_term.Eq(pt_final.prop.arg1 + step3_pt.prop.arg1, hol_term.Real(0)))
            elif pt_final.prop.is_equals() and step3_pt.prop.is_greater_eq():
                pt = logic.apply_theorem('verit_real_add_eq_ge',
                         concl=hol_term.greater_eq(T)(pt_final.prop.arg1 + step3_pt.prop.arg1, hol_term.Real(0)))
            elif pt_final.prop.is_equals() and step3_pt.prop.is_greater():
                pt = logic.apply_theorem('verit_real_add_eq_gt',
                         concl=hol_term.greater(T)(pt_final.prop.arg1 + step3_pt.prop.arg1, hol_term.Real(0)))
            if pt_final.prop.is_greater() and step3_pt.prop.is_equals():
                pt = logic.apply_theorem('verit_real_add_eq_gt',
                         concl=hol_term.greater(T)(step3_pt.prop.arg1 + pt_final.prop.arg1, hol_term.Real(0)))
            elif pt_final.prop.is_greater() and step3_pt.prop.is_greater():
                pt = logic.apply_theorem('verit_real_add_gt_gt',
                         concl=hol_term.greater(T)(pt_final.prop.arg1 + step3_pt.prop.arg1, hol_term.Real(0)))
            elif pt_final.prop.is_greater() and step3_pt.prop.is_greater_eq():
                pt = logic.apply_theorem('verit_real_add_gt_ge',
                         concl=hol_term.greater(T)(pt_final.prop.arg1 + step3_pt.prop.arg1, hol_term.Real(0)))
            elif pt_final.prop.is_greater_eq() and step3_pt.prop.is_equals():
                pt = logic.apply_theorem('verit_real_add_eq_ge',
                         concl=hol_term.greater_eq(T)(step3_pt.prop.arg1 + pt_final.prop.arg1, hol_term.Real(0)))
            elif pt_final.prop.is_greater_eq() and step3_pt.prop.is_greater():
                pt = logic.apply_theorem('verit_real_add_gt_ge',
                         concl=hol_term.greater(T)(step3_pt.prop.arg1 + pt_final.prop.arg1, hol_term.Real(0)))
            elif pt_final.prop.is_greater_eq() and step3_pt.prop.is_greater_eq():
                pt = logic.apply_theorem('verit_real_add_ge_ge',
                         concl=hol_term.greater_eq(T)(pt_final.prop.arg1 + step3_pt.prop.arg1, hol_term.Real(0)))
            assms, _ = pt.prop.strip_implies()
            for assm in assms:
                pt = pt.implies_elim(pt_dct[assm])
            pt_eq = ProofTerm("verit_norm_lra", [pt.prop.arg1])
            pt_final = pt.on_prop(arg1_conv(replace_conv(pt_eq)))
            # pt_final = pt.on_prop(arg1_conv(verit_conv.norm_lra_conv()))
            pt_dct[pt_final.prop] = pt_final
            # print("pt_final ", pt_final.prop)
            # print()

        # print()
        # print("pt_final ", pt_final)
        # print("pt_final1", pt_final)
        # print()
        if not pt_final.prop.arg1.is_constant() or not pt_final.prop.arg.is_constant():
            raise VeriTException("la_generic", "unexpected result %s" % pt_final)
        
        # pt_const_compare = integer.int_const_compares().get_proof_term(pt_final.prop)
        pt_const_compare = ProofTerm("real_const_eq", pt_final.prop)
        pt_false = pt_const_compare.equal_elim(pt_final)

        # print('equals')
        # for pt in step1_neg_conv_pts:
        #     print(pt)
        # print()

        # print(pt_false)

        for pt in reversed(step1_neg_conv_pts):
            pt_false = pt_false.implies_intr(pt.lhs.arg)
            if pt_false.prop.arg == hol_term.false:
                pt_false = pt_false.on_prop(rewr_conv("imp_false_false"), replace_conv(pt))
            else:
                pt_false = pt_false.on_prop(rewr_conv("imp_disj_eq"), arg1_conv(replace_conv(pt)))
        

        if pt_false.prop == hol_term.Or(*dis_eqs):
            return pt_false
        else:
            print(pt_false)
            raise VeriTException("la_generic", "unexpected result")


    def get_proof_term(self, args, prevs) -> ProofTerm:
        # print("goal", hol_term.Or(*args[:-1]))
        # print("coeff", args[-1])
        dis_eqs, coeffs = args[:-1], args[-1]
        dis_eq = dis_eqs[0]
        if dis_eq.is_not():
            dis_eq = dis_eq.arg
        T = dis_eq.arg.get_type()
        if T == hol_type.IntType:
            return self.get_proof_term_int(dis_eqs, coeffs)
        elif T == hol_type.RealType:
            return self.get_proof_term_real(dis_eqs, coeffs)
        else:
            raise NotImplementedError