from kernel.type import TFun, IntType
from kernel.term import Var, Int, Eq
from kernel import term_ord
from kernel.proofterm import refl
from kernel.macro import Macro
from kernel.theory import check_proof, register_macro
from kernel.proofterm import ProofTerm
from kernel.report import ProofReport
from logic import basic
from logic import context
from logic.conv import Conv, rewr_conv, arg_conv, arg1_conv, binop_conv, top_conv, ConvException, try_conv
from data import nat
from kernel.thm import Thm
from syntax.settings import settings
basic.load_theory('int')


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
    elif t.is_times():
        return int_eval(t.arg1) * int_eval(t.arg)
    else:
        raise ConvException('int_eval: %s' % str(t))

class int_conv(Conv):
    def eval(self, t):
        return Thm([], Eq(t, int_eval(t)))
    
    def get_proof_term(self, t):
        return ProofTerm.sorry(Thm([], Eq(t, int_eval(t))))

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
                    arg_conv(arg_conv(int_conv())))  # evaluate e1 + e2
            else:  # if b < c, atoms already ordered since we assume b is ordered.
                return pt
        else:  # t is of the form a * b
            cp = compare_atom(t.arg1, t.arg)  # compare a with b by their base
            if cp > 0:  # if a > b, need to swap a and b
                return pt.on_rhs(rewr_conv('int_mult_comm'))
            elif cp == 0:  # if a and b have the same base, combine the exponents
                return pt.on_rhs(
                    rewr_conv('int_power_add', sym=True),
                    arg_conv(int_conv()))
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
            return pt.on_rhs(int_conv())
        elif t.arg1.is_number() and not t.arg.is_number():  # c * (d * body)
            return pt.on_rhs(
                rewr_conv('int_mult_assoc'),  # (c * d) * body
                arg1_conv(int_conv()))  # evaluate c * d
        elif not t.arg1.is_number() and t.arg.is_number():  # (c * body) * d
            return pt.on_rhs(rewr_conv('int_mult_comm'), self)  # d * (c * body)
        else:  # (c * body1) * (d * body2)
            return pt.on_rhs(
                rewr_conv('int_mult_assoc'),  # ((c * body1) * d) * body2
                arg1_conv(swap_mult_r()),  # ((c * d) * body1) * body2
                arg1_conv(arg1_conv(int_conv())),  # evaluate c * d
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
            if t.arg.arg1.dest_number() < 0: # a - (-k) * body, k > 0
                return pt.on_rhs(
                    arg_conv(rewr_conv('mul_opp_l')), # a - (-(k * body))
                    rewr_conv('sub_opp_r'), # a + k * body
                    arg_conv(norm_mult_monomial()),
                    norm_add_monomial())
            else:
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
                    arg_conv(rewr_conv('mul_add_distr_r', sym=True)), # a + (c1 + c2) * b
                    arg_conv(arg1_conv(int_conv())), # evaluate c1 + c2
                    try_conv(arg_conv(rewr_conv('mul_0_l'))),
                    try_conv(rewr_conv('int_add_0_right')))
            else:  # if b < c, monomials are already sorted
                return pt
        
        else:  # a + b
            cp = compare_monomial(t.arg1, t.arg)  # compare a with b
            if cp > 0:  # if a > b, need to swap a with b
                return pt.on_rhs(rewr_conv('int_add_comm'))
            elif cp == 0:  # if b and c have the same body, combine coefficients
                if t.arg.is_number():
                    return pt.on_rhs(int_conv())
                else:
                    return pt.on_rhs(
                        rewr_conv('mul_add_distr_r', sym=True),
                        arg1_conv(int_conv()),
                        try_conv(rewr_conv('mul_0_l')))
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
                    rewr_conv('sub_add_distr'), # a - b - c
                    arg1_conv(self), # merge terms in b into a
                    norm_add_monomial() # merge c into a - b
                )
            elif t.arg.is_minus(): # t is of form a - (b - c)
                return pt.on_rhs(
                    rewr_conv('sub_sub_distr'), # a - b + c
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
                rewr_conv('mul_add_distr_r'),  # a * c + b * c
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
            return pt.on_rhs(rewr_conv('mul_0_l'))
        elif t.arg.is_zero():
            return pt.on_rhs(rewr_conv('mul_0_r'))
        elif t.arg.is_plus():  # a * (b + c)
            return pt.on_rhs(
                rewr_conv('mul_add_distr_l'), # a * b + a * c
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

class norm_full(Conv):
    def get_proof_term(self, t):
        pt = refl(t)
        if t.is_plus() or t.is_minus():
            return pt.on_rhs(binop_conv(self), norm_add_polynomial())
        elif t.is_times():
            return pt.on_rhs(binop_conv(self), norm_mult_polynomials())
        elif t.is_number():
            return pt
        elif t.is_nat_power() and t.arg.is_number():  # rewrite x ^ n to 1 * x ^ n
            return pt.on_rhs(rewr_conv('mul_1_l', sym=True))
        else:  # rewrite x to 1 * x ^ 1
            return pt.on_rhs(
                rewr_conv('pow_1_r', sym=True),
                rewr_conv('mul_1_l', sym=True))

@register_macro('int_norm')
class int_norm_macro(Macro):
    def __init__(self):
        self.level = 1
        self.limit = 'int_power_add'
        
    def get_proof_term(self, goal, prevs):
        assert goal.is_equals(), 'int_norm: goal is not an equality'
        
        # Obtain the normalization of the two sides
        pt1 = refl(goal.lhs).on_rhs(norm_full())
        pt2 = refl(goal.rhs).on_rhs(norm_full())
        
        assert pt1.rhs == pt2.rhs, 'int_norm: normalizations are not equal.'
        return pt1.transitive(pt2.symmetric())

class simp_full(Conv):
    def get_proof_term(self, t):
        return refl(t).on_rhs(
            norm_full(),
            top_conv(rewr_conv('mul_1_l')),
            top_conv(rewr_conv('pow_1_r')))

