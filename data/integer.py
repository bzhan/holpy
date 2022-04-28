from kernel.type import TFun, IntType
from kernel.term import Var, Int, Eq, Term, Sum, Prod, equals, Const, less, less_eq, greater, greater_eq, Not, int_power, Nat
from kernel import term_ord
from kernel.proofterm import ProofTerm, refl
from kernel.macro import Macro
from kernel.theory import check_proof, register_macro, get_theorem
from kernel.proofterm import ProofTerm
from kernel.report import ProofReport
from logic import basic
from logic import context
from logic.logic import apply_theorem
from logic.conv import Conv, rewr_conv, arg_conv, arg1_conv, binop_conv, top_conv, ConvException, try_conv
from data import nat
from kernel.thm import Thm
from syntax.settings import settings
from math import gcd
from logic import matcher
from util import poly
import functools
basic.load_theory('real')


def strip_plus(t):
    """Given t1 + ... + tn, return [t1, ..., tn]."""
    if t.is_plus():
        return strip_plus(t.arg1) + [t.arg]
    else:
        return [t]

def strip_plus_full(t):
    """Given t1 + ... + tn, return [t1, ..., tn]."""
    if t.is_plus():
        return strip_plus_full(t.arg1) + strip_plus_full(t.arg)
    else:
        return [t]

def strip_times(t):
    """Given t1 * t2 * ... * tn, return [t1, ..., tn]."""
    if t.is_times():
        return strip_times(t.arg1) + [t.arg]
    else:
        return [t]

def dest_times(t):
    """Given t1 * t2, return (t1, t2)."""
    assert t.is_times(), "dest_times"
    return (t.arg1, t.arg)


"""Normalization of integer polynomials"""

class swap_mult_r(Conv):
    """Rewrite (a * b) * c to (a * c) * b."""
    def get_proof_term(self, t):
        return refl(t).on_rhs(
            rewr_conv('int_mult_assoc', sym=True),  # a * (b * c)
            arg_conv(rewr_conv('int_mult_comm')),  # a * (c * b)
            rewr_conv('int_mult_assoc'))  # (a * c) * b

def compare_atom(t1, t2):
    """Assume t1 and t2 are in the form a_i^{e_i} and a_j^{e_j},
    compare a_i with a_j."""
    return term_ord.fast_compare(t1.arg1, t2.arg1)

def int_eval(t):
    """Evaluate a term with arithmetic operations.
    
    Return a Python integer.
    
    """
    if t.is_number():
        return t.dest_number()
    elif t.is_plus():
        return int_eval(t.arg1) + int_eval(t.arg)
    elif t.is_minus():
        m, n = int_eval(t.arg1), int_eval(t.arg)
        return m - n
    elif t.is_uminus():
        return -(int_eval(t.arg))
    elif t.is_times():
        return int_eval(t.arg1) * int_eval(t.arg)
    else:
        raise ConvException('int_eval: %s' % str(t))

@register_macro('int_eval')
class int_eval_macro(Macro):
    """Simplify integer expression"""
    def __init__(self):
        self.level = 0 # no expand implement
        self.sig = Term
        self.limit = None

    def eval(self, goal, prevs):
        assert len(prevs) == 0, "int_eval_macro: no conditions expected"
        assert goal.is_equals(), "int_eval_macro: goal must be an equality"
        assert int_eval(goal.lhs) == int_eval(goal.rhs), "int_eval_macro: two sides are not equal"

        return Thm(goal)

class int_eval_conv(Conv):
    def get_proof_term(self, t):
        if t.get_type() != IntType:
            return refl(t)
        simp_t = Int(int_eval(t))
        if simp_t == t:
            return refl(t)
        else:
            return ProofTerm('int_eval', Eq(t, int_eval(t)))

def convert_to_poly(t):
    """Convert an integer term t to polynomial normal form."""
    if t.is_var():
        return poly.singleton(t)
    elif t.is_number():
        return poly.constant(t.dest_number())
    elif t.is_comb('of_nat', 1):
        return nat.convert_to_poly(t.arg)
    elif t.is_plus():
        t1, t2 = t.args
        return convert_to_poly(t1) + convert_to_poly(t2)
    elif t.is_minus():
        t1, t2 = t.args
        return convert_to_poly(t1) - convert_to_poly(t2)
    elif t.is_uminus():
        return -convert_to_poly(t.arg)
    elif t.is_times():
        t1, t2 = t.args
        return convert_to_poly(t1) * convert_to_poly(t2)
    else:
        return poly.singleton(t)

def from_mono(m):
    """Convert a monomial to an integer term."""
    assert isinstance(m, poly.Monomial), "from_mono: input is not a monomial"
    factors = []
    for base, power in m.factors:
        assert isinstance(base, Term), "from_mono: base is not a Term"
        baseT = base.get_type()
        if baseT != IntType:
            base = Const('of_nat', TFun(baseT, IntType))(base)
        if power == 1:
            factors.append(base)
        else:
            factors.append(int_power(base, Nat(power)))
    if m.coeff != 1:
        factors = [Int(m.coeff)] + factors
    return Prod(IntType, factors)

def from_poly(p):
    """Convert a polynomial to a term t."""
    return Sum(IntType, list(from_mono(m) for m in p.monomials))

class norm_mult_atom(Conv):
    def get_proof_term(self, t):
        pt = refl(t)
        if t.arg1.is_times():  # t is of form (a * b) * c
            cp = compare_atom(t.arg1.arg, t.arg)  # compare b with c by their base
            if cp > 0:  # if b > c, need to swap b with c
                return pt.on_rhs(
                    swap_mult_r(),  # (a * c) * b
                    arg1_conv(self))   # possibly move c further inside a
            elif cp == 0:  # if b and c have the same base, combine the exponents
                return pt.on_rhs(
                    rewr_conv('int_mult_assoc', sym=True),  # a * (b^e1 * b^e2)
                    arg_conv(rewr_conv('int_power_add', sym=True)),  # a * (b^(e1 + e2))
                    arg_conv(arg_conv(int_eval_conv())))  # evaluate e1 + e2
            else:  # if b < c, atoms already ordered since we assume b is ordered.
                return pt
        else:  # t is of the form a * b
            cp = compare_atom(t.arg1, t.arg)  # compare a with b by their base
            if cp > 0:  # if a > b, need to swap a and b
                return pt.on_rhs(rewr_conv('int_mult_comm'))
            elif cp == 0:  # if a and b have the same base, combine the exponents
                return pt.on_rhs(
                    rewr_conv('int_power_add', sym=True),
                    arg_conv(int_eval_conv()))
            else:
                return pt

class norm_mult_monomial_wo_coeff(Conv):
    def get_proof_term(self, t):
        pt = refl(t)
        if t.arg.is_times():  # t is of form a * (b * c)
            return pt.on_rhs(
                rewr_conv('int_mult_assoc'),  # (a * b) * c
                arg1_conv(self),  # merge terms in b into a
                norm_mult_atom())  # merge c into a * b
        else:
            return pt.on_rhs(norm_mult_atom())

class norm_mult_monomial(Conv):
    def get_proof_term(self, t):
        pt = refl(t)
        if t.arg1.is_number() and t.arg.is_number():  # c * d
            return pt.on_rhs(int_eval_conv())
        elif t.arg1.is_number() and not t.arg.is_number():  # c * (d * body)
            return pt.on_rhs(
                rewr_conv('int_mult_assoc'),  # (c * d) * body
                arg1_conv(int_eval_conv()))  # evaluate c * d
        elif not t.arg1.is_number() and t.arg.is_number():  # (c * body) * d
            return pt.on_rhs(rewr_conv('int_mult_comm'), self)  # d * (c * body)
        else:  # (c * body1) * (d * body2)
            return pt.on_rhs(
                rewr_conv('int_mult_assoc'),  # ((c * body1) * d) * body2
                arg1_conv(swap_mult_r()),  # ((c * d) * body1) * body2
                arg1_conv(arg1_conv(int_eval_conv())),  # evaluate c * d
                rewr_conv('int_mult_assoc', sym=True),  # cd * (body1 * body2)
                arg_conv(norm_mult_monomial_wo_coeff()))

def compare_monomial(t1, t2):
    """Assume t1 and t2 are in the form c1 * body1 and c2 * body2,
    compare body1 with body2."""
    if t1.is_number() and t2.is_number():
        return 0
    if t1.is_number() and not t2.is_number():
        return -1
    if not t1.is_number() and t2.is_number():
        return 1
    else:
        return term_ord.fast_compare(t1.arg, t2.arg)

class swap_add_r(Conv):
    """Rewrite (a + b) + c to (a + c) + b."""
    def get_proof_term(self, t):
        return refl(t).on_rhs(
            rewr_conv('int_add_assoc', sym=True),  # a + (b + c)
            arg_conv(rewr_conv('int_add_comm')),  # a + (c + b)
            rewr_conv('int_add_assoc'))  # (a + c) + b

class norm_add_monomial(Conv):
    def get_proof_term(self, t):
        pt = refl(t)
        if t.is_minus(): # a - c
            return pt.on_rhs(
                rewr_conv('int_poly_neg2'), # a + (-k) * body
                arg_conv(norm_mult_monomial()),
                norm_add_monomial())
        elif t.arg1.is_plus():  # (a + b) + c
            cp = compare_monomial(t.arg1.arg, t.arg)  # compare b with c
            if cp > 0:  # if b > c, need to swap b with c
                return pt.on_rhs(
                    swap_add_r(),  # (a + c) + b
                    arg1_conv(self),  # possibly move c further into a
                    try_conv(rewr_conv('int_add_0_left'))) # 0 +b = 0
            elif cp == 0:  # if b and c have the same body, combine coefficients
                return pt.on_rhs(
                    rewr_conv('int_add_assoc', sym=True),  # a + (c1 * b + c2 * b)
                    arg_conv(rewr_conv('int_mul_add_distr_r', sym=True)), # a + (c1 + c2) * b
                    arg_conv(arg1_conv(int_eval_conv())), # evaluate c1 + c2
                    try_conv(arg_conv(rewr_conv('int_mul_0_l'))),
                    try_conv(rewr_conv('int_add_0_right')))
            else:  # if b < c, monomials are already sorted
                return pt
        
        else:  # a + b
            if t.arg.is_zero():
                return pt.on_rhs(rewr_conv('int_add_0_right'))
            if t.arg1.is_zero():
                return pt.on_rhs(rewr_conv('int_add_0_left'))
            cp = compare_monomial(t.arg1, t.arg)  # compare a with b
            if cp > 0:  # if a > b, need to swap a with b
                return pt.on_rhs(rewr_conv('int_add_comm'))
            elif cp == 0:  # if b and c have the same body, combine coefficients
                if t.arg.is_number():
                    return pt.on_rhs(int_eval_conv())
                else:
                    return pt.on_rhs(
                        rewr_conv('int_mul_add_distr_r', sym=True),
                        arg1_conv(int_eval_conv()),
                        try_conv(rewr_conv('int_mul_0_l')))
            else:
                return pt

class norm_add_polynomial(Conv):
    def get_proof_term(self, t):
        pt = refl(t)
        if t.is_plus():
            if t.arg1.is_zero():
                return pt.on_rhs(rewr_conv('int_add_0_left'))
            elif t.arg.is_zero():
                return pt.on_rhs(rewr_conv('int_add_0_right'))
            elif t.arg.is_plus():  # t is of form a + (b + c)
                return pt.on_rhs(
                    rewr_conv('int_add_assoc'),  # (a + b) + c
                    arg1_conv(self),  # merge terms in b into a
                    norm_add_monomial())  # merge c into a + b
            elif t.arg.is_minus():  # t is of form a + (b - c)
                return pt.on_rhs(
                    arg_conv(norm_add_monomial()), # a + b + (-1) * c
                    arg1_conv(self),
                    norm_add_polynomial()
                )
            else:
                return pt.on_rhs(norm_add_monomial())
        elif t.is_minus(): 
            if t.arg.is_plus(): # t is of form a - (b + c)
                return pt.on_rhs(
                    rewr_conv('int_sub_add_distr'), # a - b - c
                    arg1_conv(self), # merge terms in b into a
                    norm_add_monomial() # merge c into a - b
                )
            elif t.arg.is_minus(): # t is of form a - (b - c)
                return pt.on_rhs(
                    rewr_conv('int_sub_sub_distr'), # a - b + c
                    arg1_conv(self), # merge terms in b into c
                    norm_add_monomial() # merge c into a - b
                )
            else:
                return pt.on_rhs(
                    norm_add_monomial(),) 
                    #norm_add_polynomial())

class norm_mult_poly_monomial(Conv):
    """Multiply a polynomial a_1 + ... + a_n with a monomial c."""
    def get_proof_term(self, t):
        pt = refl(t)
        if t.arg1.is_plus():  # (a + b) * c
            return pt.on_rhs(
                rewr_conv('int_mul_add_distr_r'),  # a * c + b * c
                arg1_conv(self),  # process a * c
                arg_conv(norm_mult_monomial()), # process b * c
                norm_add_polynomial())  # add the results
        else:
            return pt.on_rhs(norm_mult_monomial())
        
class norm_mult_polynomials(Conv):
    """Multiply two polynomials."""
    def get_proof_term(self, t):
        pt = refl(t)
        if t.arg1.is_zero():
            return pt.on_rhs(rewr_conv('int_mul_0_l'))
        elif t.arg.is_zero():
            return pt.on_rhs(rewr_conv('int_mul_0_r'))
        elif t.arg.is_plus():  # a * (b + c)
            return pt.on_rhs(
                rewr_conv('int_mul_add_distr_l'), # a * b + a * c
                arg1_conv(self),  # process a * b
                arg_conv(norm_mult_poly_monomial()),  # process a * c
                norm_add_polynomial())
        elif t.arg.is_minus():
            return pt.on_rhs(
                arg_conv(norm_add_polynomial()),
                norm_mult_polynomials()
            )
        elif t.arg1.is_minus():
            return pt.on_rhs(
                arg1_conv(norm_add_polynomial()),
                norm_mult_polynomials()
            )
        else:
            return pt.on_rhs(norm_mult_poly_monomial())

class simp_full(Conv):
    def get_proof_term(self, t):
        pt = refl(t)
        if t.is_plus() or t.is_minus():
            return pt.on_rhs(binop_conv(self), norm_add_polynomial())
        elif t.is_times():
            return pt.on_rhs(binop_conv(self), norm_mult_polynomials())
        elif t.is_number():
            return pt
        elif t.is_nat_power() and t.arg.is_number():  # rewrite x ^ n to 1 * x ^ n
            return pt.on_rhs(rewr_conv('int_mul_1_l', sym=True))
        elif t.is_uminus():
            pt_mul_neg1 = pt.on_rhs(rewr_conv('int_poly_neg1'))
            pt_new = self.get_proof_term(pt_mul_neg1.prop.rhs)
            return pt.transitive(pt_mul_neg1).transitive(pt_new)
        else:  # rewrite x to 1 * x ^ 1
            return pt.on_rhs(
                rewr_conv('int_pow_1_r', sym=True),
                rewr_conv('int_mul_1_l', sym=True))

class int_norm_conv(Conv):
    def eval(self, t):
        norm_t = from_poly(convert_to_poly(t))
        return Thm(Eq(t, norm_t))

    def get_proof_term(self, t):
        return refl(t).on_rhs(
            simp_full(),
            top_conv(rewr_conv('int_mul_1_l')),
            top_conv(rewr_conv('int_pow_1_r')))

class norm_eq(Conv):
    """Given an equality(inequality), move all term from rhs to lhs, and .
    """
    def get_proof_term(self, t):
        assert t.is_equals() or t.is_less_eq() or t.is_less()\
            or t.is_greater_eq() or t.is_greater(), "%s is not an equality term" % t
        pt1 = refl(t) # a = b <==> a = b
        if t.is_equals():
            pt2 = pt1.on_rhs(rewr_conv('int_sub_move_0_r', sym=True)) # a = b <==> a - b = 0
            eq_refl = ProofTerm.reflexive(equals(IntType))
        elif t.is_less_eq():
            pt2 = pt1.on_rhs(rewr_conv('int_leq'))
            eq_refl = ProofTerm.reflexive(less_eq(IntType))
        elif t.is_less():
            pt2 = pt1.on_rhs(rewr_conv('int_less'))
            eq_refl = ProofTerm.reflexive(less(IntType))
        elif t.is_greater_eq():
            pt2 = pt1.on_rhs(rewr_conv('int_geq'))
            eq_refl = ProofTerm.reflexive(greater_eq(IntType))
        elif t.is_greater():
            pt2 = pt1.on_rhs(rewr_conv('int_gt'))
            eq_refl = ProofTerm.reflexive(greater(IntType))
        pt3 = simp_full().get_proof_term(pt2.prop.arg.arg1) # a - b = a + (-1) * b
        pt4 = ProofTerm.combination(eq_refl, pt3)
        pt5 = ProofTerm.combination(pt4, refl(Const('zero', IntType))) # a - b = 0 <==> a + (-1)*b = 0
        return pt2.transitive(pt5) # a = b <==> a + (-1) * b = 0

@register_macro('int_eq_macro')
class int_eq_macro(Macro):
    """Prove 2 integer equations(inequations) are equal.
    
    Example: a = b + 3 <==> a - 3 = b.
    """
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def get_proof_term(self, goal, prevs):
        assert goal.is_equals(), "int_eq_norm, %s is not equation" % goal

        # Get normal form on both sides.
        pt1 = refl(goal.lhs).on_rhs(norm_eq())
        pt2 = refl(goal.rhs).on_rhs(norm_eq())

        assert pt1.rhs == pt2.rhs
        return pt1.transitive(pt2.symmetric())

@register_macro('int_ineq')
class int_ineq_macro(Macro):
    """
    Convert all kinds of inequalities to less equalities.
    Method: 
    1) First move all terms to lhs, normalize lhs
    2) c * x + ⋯ < 0, no conversion;
    3) c * x + ⋯ ≤ 0 --> c * x + ⋯ < 1;
    3) c * x + ⋯ > 0 --> (-c) * x + ⋯ < 0;
    4) c * x + ⋯ ≥ 0 --> (-c) * x + ⋯ < 1;
    """
    def get_proof_term(self, goal):
        assert isinstance(goal, Term), "%s should be a hol term" % str(goal)
        assert goal.is_less() or goal.is_less_eq() or goal.is_greater() or goal.is_greater_eq(),\
            "%s should be an inequality term" % str(goal)

        norm_ineq_pt = norm_eq().get_proof_term(goal)
        # find the first monomial
        first_monomial = norm_ineq_pt.rhs
        while not first_monomial.is_times() and not first_monomial.is_number():
            first_monomial = first_monomial.arg1

        coeff = first_monomial.arg1 if first_monomial.is_times() else first_monomial
        assert coeff.is_int()
        coeff_value = int_eval(coeff)
        # normalize
        if norm_ineq_pt.rhs.is_less():
            return norm_ineq_pt
        elif norm_ineq_pt.rhs.is_less_eq():
            return norm_ineq_pt.on_rhs(rewr_conv('int_lesseq_0'))
        else:
            if norm_ineq_pt.rhs.is_greater():
                pt_less = norm_ineq_pt.on_rhs(rewr_conv('int_greater_less'))
            elif norm_ineq_pt.rhs.is_greater_eq():
                pt_less = norm_ineq_pt.on_rhs(rewr_conv('int_greatereq_less'))
            pt_norm_lhs = refl(pt_less.rhs.arg1).on_rhs(simp_full())
            return pt_less.transitive(refl(pt_less.rhs.head).combination(pt_norm_lhs).combination(refl(pt_less.rhs.arg)))

@register_macro('int_ineq_mul_const')
class int_ineq_mul_const_macro(Macro):
    """
    Multiply a constant on both side of an inequality.

    prevs is a list contain two proof term:
    1) m ⋈ n
    2) c ⋈ 0

    return a proof term like: c * m ⋈ c * n
    """
    def get_proof_term(self, prevs, args):
        assert isinstance(prevs, ProofTerm) and prevs.prop.arg1.is_int() and prevs.prop.arg.is_zero(), "Unexpected %s" % str(prevs)
        assert isinstance(args, Term) and (args.is_less() or args.is_less_eq() or args.is_greater or args.is_greater_eq())
        th_names = ['int_pos_mul_less', 'int_neg_mul_less', 'int_pos_mul_less_eq', 'int_neg_mul_less_eq',
                    'int_pos_mul_greater', 'int_neg_mul_greater', 'int_pos_mul_greater_eq', 'int_neg_mul_greater_eq']
        for th in th_names:
            try:
                th1 = get_theorem(th)
                inst = matcher.first_order_match(th1.prop.arg.lhs, args)
                pt_concl = apply_theorem(th, prevs, inst=inst)
                return pt_concl
            except:
                continue

        raise NotImplementedError

def collect_int_polynomial_coeff(poly):
    """Give an polynomial p, normalize it
    return a list of triple: (coeff, var_name, power)
    """
    assert poly.get_type() == IntType, "%s should be an integer term" % str(poly)
    p = simp_full().get_proof_term(poly).rhs
    triple = []
    while p.is_plus() or p.is_times():
        t = p.arg if p.is_plus() else p
        if t.is_number():
            triple.append((int_eval(t), '', 0))
        else:
            triple.append((int_eval(t.arg1), t.arg.arg1.name, nat.nat_eval(t.arg.arg)))
        p = p.arg1
    
    return tuple(reversed(triple))


@register_macro('int_const_ineq')
class int_const_ineq_macro(Macro):
    """Get an pure integer inequality"""
    def __init__(self):
        self.level = 0 # no expand implement
        self.sig = Term
        self.limit = None

    def eval(self, goal, prevs):
        assert len(prevs) == 0, "int_const_ineq: no conditions expected"

        if goal.is_not():
            goal = goal.arg

        assert (goal.is_compares() or goal.is_equals()) and goal.arg1.is_constant() and goal.arg.is_constant()\
            and goal.arg1.get_type() == IntType, repr(goal)
        lhs, rhs = int_eval(goal.arg1), int_eval(goal.arg)
        if goal.is_less():
            if lhs < rhs:
                return Thm(goal)
            else:
                return Thm(Not(goal))
        elif goal.is_less_eq():
            if lhs <= rhs:
                return Thm(goal)
            else:
                return Thm(Not(goal))
        elif goal.is_greater():
            if lhs > rhs:
                return Thm(goal)
            else:
                return Thm(Not(goal))
        elif goal.is_greater_eq():
            if lhs >= rhs:
                return Thm(goal)
            else:
                return Thm(Not(goal))
        elif goal.is_equals():
            if lhs == rhs:
                return Thm(goal)
            else:
                return Thm(Not(goal))
        else:
            raise NotImplementedError


@register_macro('int_multiple_ineq_equiv')
class int_multiple_ineq_equiv(Macro):
    """
    Give two inequalities:
    1) c1 * m ⋈ c1 * n
    2) c2 * m ⋈ c2 * n
    prove their equaivalence.
    """
    def get_proof_term(self, prevs):
        p1, p2 = prevs
        lhs_triple = collect_int_polynomial_coeff(p1.arg1)
        rhs_triple = collect_int_polynomial_coeff(p2.arg1)
        lhs_singleton = [(p[1], p[2]) for p in lhs_triple]
        rhs_singleton = [(p[1], p[2]) for p in rhs_triple]
        if lhs_singleton != rhs_singleton or len(lhs_singleton) != len(rhs_singleton):
            raise NotImplementedError

        lhs_coeff = [p[0] for p in lhs_triple]
        rhs_coeff = [p[0] for p in rhs_triple]

        ratios = [p1/p2 for p1, p2 in zip(lhs_coeff, rhs_coeff)]
        if len(set(ratios)) != 1:
            raise NotImplementedError
        
        lhs_mul = int(rhs_coeff[0] / gcd(lhs_coeff[0], rhs_coeff[0]))
        rhs_mul = int(lhs_coeff[0] / gcd(lhs_coeff[0], rhs_coeff[0]))

        if lhs_mul > 0:
            pt_lhs_mul = ProofTerm('int_const_ineq', greater(IntType)(Int(lhs_mul), Int(0)))

        if lhs_mul < 0:
            pt_lhs_mul = ProofTerm('int_const_ineq', less(IntType)(Int(lhs_mul), Int(0)))

        if rhs_mul > 0:
            pt_rhs_mul = ProofTerm('int_const_ineq', greater(IntType)(Int(rhs_mul), Int(0)))

        if rhs_mul < 0:
            pt_rhs_mul = ProofTerm('int_const_ineq', less(IntType)(Int(rhs_mul), Int(0)))

        pt_lhs_mul = int_ineq_mul_const_macro().get_proof_term(pt_lhs_mul, p1)
        pt_rhs_mul = int_ineq_mul_const_macro().get_proof_term(pt_rhs_mul, p2)

        # normalize both sides
        pt_lhs_mul_norm = pt_lhs_mul.transitive(norm_eq().get_proof_term(pt_lhs_mul.prop.rhs))
        pt_rhs_mul_norm = pt_rhs_mul.transitive(norm_eq().get_proof_term(pt_rhs_mul.prop.rhs))

        return pt_lhs_mul_norm.transitive(pt_rhs_mul_norm.symmetric())
        
def omega_compare_monomial(t1, t2):
    """Assume t1 and t2 are in the form c1 * body1 and c2 * body2,
    compare body1 with body2."""
    if t1.is_number() and t2.is_number():
        return 0
    if t1.is_number() and not t2.is_number():
        return 1
    if not t1.is_number() and t2.is_number():
        return -1
    else:
        return term_ord.fast_compare(t1.arg, t2.arg)

class omega_norm_add_num(Conv):
    """
    If there is an number in the term, move it to the right-most side.
    """
    def get_proof_term(self, t):
        pt = refl(t)
        if t.is_number() and t.is_int():
            return pt.on_rhs(int_eval_conv())
        elif t.arg1.is_plus():
            pt1 = pt.on_rhs(arg1_conv(self))
            cp = omega_compare_monomial(pt1.rhs.arg1.arg, pt1.rhs.arg)
            if cp > 0:
                return pt1.on_rhs(swap_add_r())
            else:
                return pt1
        elif t.is_plus():
            cp = omega_compare_monomial(t.arg1, t.arg)
            if cp > 0:
                return pt.on_rhs(rewr_conv('int_add_comm'))
            else:
                return pt
        else:
            return pt

class omega_simp_full_conv(Conv):
    def get_proof_term(self, t):
        return refl(t).on_rhs(
            simp_full(),
            top_conv(rewr_conv('int_pow_1_r')),
            omega_norm_add_num())


@register_macro('omega_norm_int_ineq')
class omega_norm_int_ineq_macro(Macro):
    """
    Convert all kinds of inequalities to less equalities.
    Method: 
    1) First move all terms to lhs, normalize lhs
    2) c * x + ⋯ < 0, (-c) * x + ⋯ ≥ 1;
    3) c * x + ⋯ ≤ 0 --> (-c) * x + ⋯ ≥ 0;
    3) c * x + ⋯ > 0 --> c * x + ⋯ ≥ 1;
    4) c * x + ⋯ ≥ 0 --> no conversion;
    """
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def get_proof_term(self, goal):
        assert isinstance(goal, Term), "%s should be a hol term" % str(goal)
        assert goal.is_less() or goal.is_less_eq() or goal.is_greater() or goal.is_greater_eq(),\
            "%s should be an inequality term" % str(goal)

        norm_ineq_pt = norm_eq().get_proof_term(goal)
        # find the first monomial
        first_monomial = norm_ineq_pt.rhs
        while not first_monomial.is_times() and not first_monomial.is_number():
            first_monomial = first_monomial.arg1

        coeff = first_monomial.arg1 if first_monomial.is_times() else first_monomial
        assert coeff.is_int()
        coeff_value = int_eval(coeff)
        # normalize
        if norm_ineq_pt.rhs.is_greater_eq():
            return norm_ineq_pt
        elif norm_ineq_pt.rhs.is_greater():
            return norm_ineq_pt.on_rhs(rewr_conv('int_great_to_geq'))
        else:
            if norm_ineq_pt.rhs.is_less():
                pt_great = norm_ineq_pt.on_rhs(rewr_conv('int_less_to_geq'))
            elif norm_ineq_pt.rhs.is_less_eq():
                pt_great = norm_ineq_pt.on_rhs(rewr_conv('int_leq_to_geq'))
            pt_norm_lhs = refl(pt_great.rhs.arg1).on_rhs(omega_simp_full_conv())
            return pt_great.transitive(refl(pt_great.rhs.head).combination(pt_norm_lhs).combination(refl(pt_great.rhs.arg)))

class omega_form_conv(Conv):
    """
    Convert all integer inequalities to 0 <= Σ c * x + k
    """
    def get_proof_term(self, t):
        if not (t.is_compares() and t.arg.get_type() == IntType):
            raise ConvException("%s is not an integer comparison." % str(t))
        pt_refl = refl(t)
        if t.is_less():
            pt = pt_refl.on_rhs(rewr_conv('int_zero_less'))
        elif t.is_less_eq():
            pt = pt_refl.on_rhs(rewr_conv('int_zero_less_eq'))
        elif t.is_greater():
            pt = pt_refl.on_rhs(rewr_conv('int_zero_greater'))
        else:
            pt = pt_refl.on_rhs(rewr_conv('int_zero_greater_eq')) 

        return pt.on_rhs(arg_conv(omega_simp_full_conv()))

@register_macro('int_eq_comparison')
class int_eq_comparison_macro(Macro):
    """
    Prove two comparisons' equivalence.
    """
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def get_proof_term(self, goal):
        assert goal.is_equals() and goal.lhs.is_compares() and goal.rhs.is_compares()

        pt1 = refl(goal.lhs).on_rhs(omega_form_conv())
        pt2 = refl(goal.rhs).on_rhs(omega_form_conv())

        if pt1.rhs != pt2.rhs:
            raise ConvException(str(goal))
        return pt1.transitive(pt2.symmetric())

class int_norm_eq(Conv):
    """Prove two linear equations are equal."""
    def get_proof_term(self, t):
        if not t.is_equals():
            raise ConvException("%s must be an equality." % str(t))
        pt = refl(t)
        pt1 = pt.on_rhs(
            rewr_conv('int_sub_move_0_r', sym=True),
            arg1_conv(simp_full()),
            top_conv(rewr_conv('int_pow_1_r'))
        )
        summands = strip_plus(pt1.rhs.arg1)
        if summands[0].is_number():
            first_coeff = summands[0]
        else:
            first_coeff = summands[0].arg1
        if int_eval(first_coeff) < 0:
            return pt1.on_rhs(
                rewr_conv('int_pos_neg_eq_0'),
                arg1_conv(simp_full()),
                top_conv(rewr_conv('int_pow_1_r'))
            )
        else:
            return pt1

class int_norm_neg_compares(Conv):
    """Convert a negative comparison term to a normal comparison term."""
    def get_proof_term(self, t):
        if not (t.is_not() and t.arg.is_compares()):
            raise ConvException("%s is not a negative comparison term." % str(t))
        pt = refl(t)
        ineq = t.arg
        if ineq.is_less():
            return pt.on_rhs(rewr_conv('int_not_less'))
        elif ineq.is_less_eq():
            return pt.on_rhs(rewr_conv('int_not_less_eq'))
        elif ineq.is_greater():
            return pt.on_rhs(rewr_conv('int_not_greater'))
        elif ineq.is_greater_eq():
            return pt.on_rhs(rewr_conv('int_not_greater_eq'))
        else:
            raise ConvException

class int_gcd_compares(Conv):
    """Elimates the greatest common divisor of coefficients in comparison."""
    def get_proof_term(self, t):
        if not t.is_compares():
            raise ConvException('%s is not a comparison.' % str(t))
        
        pt = refl(t)
        pt_norm_form = pt.on_rhs(norm_eq(), arg1_conv(omega_simp_full_conv()))
        summands = strip_plus(pt_norm_form.rhs.arg1)
        coeffs = [int_eval(s.arg1) if not s.is_number() else int_eval(s) for s in summands]
        g = functools.reduce(gcd, coeffs)
        if g <= 1:
            return pt

        vars = [s.arg for s in summands if not s.is_number()]
        elim_gcd_coeffs = [int(i/g) for i in coeffs]
        if len(vars) < len(coeffs):
            simp_t = sum([coeff * v for coeff, v in zip(elim_gcd_coeffs[1:-1], vars[1:])], elim_gcd_coeffs[0] * vars[0]) + Int(elim_gcd_coeffs[-1])
        else:
            simp_t = sum([coeff * v for coeff, v in zip(elim_gcd_coeffs[1:], vars[1:])], elim_gcd_coeffs[0] * vars[0])

        simp_t_times_gcd = Int(g) * simp_t
        pt_simp_t_times_gcd = refl(simp_t_times_gcd).on_rhs(omega_simp_full_conv()).symmetric()
        pt_c = ProofTerm('int_const_ineq', greater(IntType)(Int(g), Int(0)))
        if t.is_less():
            gcd_pt = ProofTerm.theorem('int_simp_less')
        elif t.is_less_eq():
            gcd_pt = ProofTerm.theorem('int_simp_leq')
        elif t.is_greater():
            gcd_pt = ProofTerm.theorem('int_simp_gt')
        elif t.is_greater_eq():
            gcd_pt = ProofTerm.theorem('int_simp_geq')

        inst1 = matcher.first_order_match(gcd_pt.prop.arg1, pt_c.prop)
        inst2 = matcher.first_order_match(gcd_pt.prop.arg.rhs.arg1, simp_t, inst=inst1)
        
        pt_simp = gcd_pt.substitution(inst2).implies_elim(pt_c).on_lhs(arg1_conv(omega_simp_full_conv()))
        return pt_norm_form.transitive(pt_simp).on_rhs(omega_form_conv())   

class int_neq_false_conv(Conv):
    """Given a equality term a = 0 in which a is a constant and a is indeed not zero,
    Return (a = 0) <--> false proof term.
    """   
    def get_proof_term(self, tm):
        if not tm.is_equals() or not int_eval(tm.lhs) != 0 or not int_eval(tm.rhs) == 0:
            raise ConvException(str(tm))
        
        lhs_value = int_eval(tm.lhs)
        if lhs_value > 0:
            premise_pt = ProofTerm("int_const_ineq", greater(IntType)(Int(lhs_value), Int(0)))
            return apply_theorem("int_pos_neq_zero", premise_pt)
        else:
            premise_pt = ProofTerm("int_const_ineq", less(IntType)(Int(lhs_value), Int(0)))
            return apply_theorem("int_neg_neq_zero", premise_pt)

class int_compare_to_real(Conv):
    """Given an integer comparison, convert it to a real comparison.
    Suppose the linear expression of both side is an addition.
    """
    def get_proof_term(self, t):
        if not (t.is_compares() or t.is_equals()) or not t.arg1.get_type() == IntType:
            raise ConvException(str(t))
        pt = refl(t)
        if t.is_equals():
            pt1 = pt.on_rhs(rewr_conv("real_of_int_eq", sym=True))
        elif t.is_greater_eq():
            pt1 = pt.on_rhs(rewr_conv("real_of_int_geq", sym=True))
        elif t.is_greater():
            pt1 = pt.on_rhs(rewr_conv("real_of_int_gt", sym=True))
        elif t.is_less_eq():
            pt1 = pt.on_rhs(rewr_conv("real_of_int_leq", sym=True))
        elif t.is_less():
            pt1 = pt.on_rhs(rewr_conv("real_of_int_lt", sym=True))
        else:
            raise NotImplementedError

        return pt1.on_rhs(
                top_conv(rewr_conv('real_of_int_add', sym=True)),
                top_conv(rewr_conv('real_of_int_mul', sym=True)),   
        )

class int_simplex_form(Conv):
    """Convert an integer comparison to a simplex normal form:
                        y ⋈ b
    """
    def get_proof_term(self, t):
        if not t.is_compares() or not t.arg1.get_type() == IntType:
            raise ConvException(str(t))
        pt = refl(t)
        # first move all terms in rhs to lhs and normalize lhs
        if t.is_greater():
            pt1 = pt.on_rhs(
                rewr_conv('int_gt_to_geq'),
                rewr_conv('int_geq'),
                arg1_conv(omega_simp_full_conv())
            )
        elif t.is_greater_eq():
            pt1 = pt.on_rhs(
                rewr_conv('int_geq'),
                arg1_conv(omega_simp_full_conv())
            )
        elif t.is_less():
            pt1 = pt.on_rhs(
                rewr_conv('int_less_to_leq'),
                rewr_conv('int_leq'),
                arg1_conv(omega_simp_full_conv())
            )
        elif t.is_less_eq():
            pt1 = pt.on_rhs(
                rewr_conv('int_leq'),
                arg1_conv(omega_simp_full_conv())
            )
        else:
            raise NotImplementedError
        # move all constant term on lhs to rhs
        lhs = pt1.rhs.arg1
        if lhs.is_number() or lhs.is_times() or lhs.arg.is_times():
            return pt1
        elif pt1.rhs.is_greater_eq() and lhs.arg.is_number():
            return pt1.on_rhs(rewr_conv('int_geq_shift'), arg_conv(int_eval_conv()))
        elif pt1.rhs.is_less_eq() and lhs.arg.is_number():
            return pt1.on_rhs(rewr_conv('int_leq_shift'), arg_conv(int_eval_conv()))
        else:
            raise NotImplementedError       

class int_const_compares(Conv):
    """
    Given an int constant comparison, convert it to false or true.
    """
    def get_proof_term(self, tm):
        if not ((tm.is_compares() or tm.is_equals()) and \
            tm.arg1.is_constant() and tm.arg.is_constant()):
            return refl(tm)
        pt = ProofTerm("int_const_ineq", tm)
        if pt.prop.is_not():
            return pt.on_prop(rewr_conv("eq_false"))
        else:
            return pt.on_prop(rewr_conv("eq_true"))