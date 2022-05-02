from logic.conv import Conv, rewr_conv, ConvException, \
    arg1_conv, arg_conv, binop_conv, top_conv, beta_conv, abs_conv, try_conv
from data import integer, real
from kernel.term_ord import fast_compare
from kernel import term as hol_term
from kernel.proofterm import refl, ProofTerm
from logic import logic


def compare_atom(tm1, tm2):
    return fast_compare(tm1.arg, tm2.arg)

class int_norm_add_atom_conv(Conv):
    """Normalize the expression (c + a_1 * x_1 + ... + a_n * x_n) + atom
    an atom is either a number n or a linear term a * x
    """
    def get_proof_term(self, t):
        pt = refl(t)
        if t.arg.is_zero():
            return pt.on_rhs(rewr_conv("int_add_0_right"))
        elif t.arg1.is_zero():
            return pt.on_rhs(rewr_conv("int_add_0_left"))
        if not t.arg.is_number() and not t.arg.is_times():
            pt = pt.on_rhs(arg_conv(rewr_conv("int_mul_1_l", sym=True))) 
        if t.is_constant():
            return pt.on_rhs(integer.int_eval_conv())
        if t.arg1.is_times(): # a * x + atom
            if t.arg.is_number(): # a * x + c
                return pt.on_rhs(rewr_conv("int_add_comm"))
            elif t.arg.is_times(): # a * x + b * y
                cp = compare_atom(t.arg1, t.arg)
                if cp == 0: # a * x + b * x
                    pt1 = pt.on_rhs(
                        rewr_conv("int_mul_add_distr_r", sym=True),
                        arg1_conv(integer.int_eval_conv())
                    )
                    if pt1.rhs.arg1.is_zero():
                        return pt1.on_rhs(rewr_conv('int_mul_0_l'))
                    else:
                        return pt1
                elif cp > 0:
                    return pt.on_rhs(rewr_conv("int_add_comm"))
                else:
                    return pt
            else:
                raise ConvException
        elif t.arg1.is_plus():
            if t.arg.is_number():
                return pt.on_rhs(integer.swap_add_r(), arg1_conv(self), try_conv(rewr_conv('int_add_0_left')))
            elif t.arg.is_times():
                cp = compare_atom(t.arg1.arg, t.arg)
                if cp > 0:
                    return pt.on_rhs(integer.swap_add_r(), arg1_conv(self))
                elif cp == 0:
                    pt1 = pt.on_rhs(
                        rewr_conv("int_add_assoc", sym=True), 
                        arg_conv(rewr_conv("int_mul_add_distr_r", sym=True)),
                        arg_conv(arg1_conv(integer.int_eval_conv())))
                    if pt1.rhs.arg.arg1.is_zero():
                        return pt1.on_rhs(arg_conv(rewr_conv('int_mul_0_l')), rewr_conv('int_add_0_right'))
                    else:
                        return pt1
                else:
                    return pt
            else:
                raise ConvException
        else:
            return pt

class norm_add_lia_conv(Conv):
    def get_proof_term(self, t: hol_term.Term) -> ProofTerm:
        pt = refl(t)
        if t.is_constant():
            return pt.on_rhs(integer.int_eval_conv())
        elif t.arg1.is_zero():
            return pt.on_rhs(rewr_conv("int_add_0_left"))
        elif t.arg.is_zero():
            return pt.on_rhs(rewr_conv("int_add_0_right"))
        elif t.arg.is_plus():
            return pt.on_rhs(
                rewr_conv('int_add_assoc'),
                arg1_conv(self),
                int_norm_add_atom_conv()
            )
        else:
            return pt.on_rhs(int_norm_add_atom_conv())



class norm_lia_conv(Conv):
    def get_proof_term(self, t):
        pt = refl(t)
        if t.is_constant():
            return pt.on_rhs(integer.int_eval_conv())
        elif t.is_plus():
            return pt.on_rhs(binop_conv(self), norm_add_lia_conv())
        elif t.is_minus():
            return pt.on_rhs(binop_conv(self), 
                rewr_conv("add_opp_r", sym=True), arg_conv(neg_lia_conv()), self)
        elif t.is_times():
            if not t.arg1.is_number():
                return pt
            if t.arg.is_uminus(): # c * (-x)
                return pt.on_rhs(
                    rewr_conv('mul_opp_comm', sym=True),
                    arg1_conv(integer.int_eval_conv())
                )
            elif t.arg.is_plus():
                return pt.on_rhs(
                    const_prod_lia_conv(),
                    self
                )
            elif t.arg.is_minus():
                return pt.on_rhs(arg_conv(self), self)
            elif t.arg.is_times() and t.arg.arg1.is_constant():
                return pt.on_rhs(rewr_conv('int_mult_assoc'), arg1_conv(int.int_eval_conv()), self)
            else:
                return pt
        elif t.is_uminus():
            return pt.on_rhs(rewr_conv('int_poly_neg1'))
        else:
            return pt.on_rhs(rewr_conv('int_mul_1_l', sym=True))

class neg_lia_conv(Conv):
    def get_proof_term(self, t: hol_term.Term) -> ProofTerm:
        pt = refl(t)
        if not t.is_uminus():
            return pt
        if t.arg.is_constant():
            return pt.on_rhs(integer.int_eval_conv())
        elif t.arg.is_times():
            return pt.on_rhs(rewr_conv("mul_opp_l", sym=True))
        elif t.arg.is_plus():
            return pt.on_rhs(rewr_conv('opp_add_distr'), binop_conv(self), norm_lia_conv())
        else:
            return pt.on_rhs(rewr_conv('int_poly_neg1'))        

class simp_lia_conv(Conv):
    """rewrite 0 + lia -> lia, rewrite 1 * x -> x"""
    def get_proof_term(self, t: hol_term.Term) -> ProofTerm:
        return refl(t).on_rhs(
            norm_lia_conv(),
            top_conv(rewr_conv('int_mul_1_l'))
        )
        

class const_prod_lia_conv(Conv):
    def get_proof_term(self, t):
        pt = refl(t)
        if t.is_constant():
            return pt.on_rhs(integer.int_eval_conv())
        if not t.is_times() or not t.arg1.is_number():
            return pt
        if t.arg1.is_zero():
            return pt.on_rhs(rewr_conv('int_mul_0_l'))
        elif t.arg.is_zero():
            return pt.on_rhs(rewr_conv('int_mul_0_r'))
        elif t.arg.is_plus():
            return pt.on_rhs(rewr_conv('int_mul_add_distr_l'), binop_conv(self))
        elif t.arg.is_times():
            return pt.on_rhs(rewr_conv('int_mult_assoc'), arg1_conv(integer.int_eval_conv()))
        else:
            return pt

class verit_norm_lia_greater_eq(Conv):
    def get_proof_term(self, t: hol_term.Term) -> ProofTerm:
        if t.is_greater() and t.arg.is_zero():
            return refl(t).on_rhs(rewr_conv('int_great_to_geq'))
        else:
            return refl(t)


class deMorgan_conj_conv(Conv):
    """Prove ~(t_1 /\ t_2 /\ ... /\ t_n) <--> ~t_1 \/ ~t_2 \/ ... \/ ~t_n.
    
    If rm is set, stop expanding conjunction when t_n becomes rm.
    
    """
    def __init__(self, rm=None):
        self.rm = rm  # rm is the right-most conjunction

    def get_proof_term(self, t: hol_term.Term) -> ProofTerm:
        if t.is_not() and t.arg.is_conj():
            if self.rm is not None and self.rm == t.arg:
                return refl(t)
            else:
                return refl(t).on_rhs(rewr_conv('de_morgan_thm1'), arg_conv(self))
        else:
            return refl(t)

class deMorgan_disj_conv(Conv):
    """Prove ~(t_1 \/ t_2 \/ ... \/ t_n) <--> ~t_1 /\ ~t_2 /\ ... /\ ~t_n.
    
    If rm is set, stop expanding disjunction when t_n becomes rm.

    """
    def __init__(self, rm=None):
        self.rm = rm  # rm is the right-most disjunction
    
    def get_proof_term(self, t: hol_term.Term) -> ProofTerm:
        if t.is_not() and t.arg.is_disj():
            if self.rm is not None and self.rm == t.arg:
                return refl(t)
            else:
                return refl(t).on_rhs(rewr_conv('de_morgan_thm2'), arg_conv(self))
        else:
            return refl(t)

class imp_false_conv(Conv):
    """Prove t_1 -> t_2 -> .. -> t_n --> false <--> ~t_1 | ~t_2 | ... | ~t_n"""
    def get_proof_term(self, t: hol_term.Term) -> ProofTerm:
        if t.is_implies():
            if t.arg == hol_term.false:
                return refl(t).on_rhs(rewr_conv('disj_conv_imp', sym=True), rewr_conv('disj_false_right'))
            else:
                return refl(t).on_rhs(rewr_conv('disj_conv_imp', sym=True), arg_conv(self))
        else:
            return refl(t)

class real_norm_add_atom_conv(Conv):
    """Normalize the expression (c + a_1 * x_1 + ... + a_n * x_n) + atom
    an atom is either a number n or a linear term a * x
    """
    def get_proof_term(self, t):
        pt = refl(t)
        if t.arg.is_zero():
            return pt.on_rhs(rewr_conv("real_add_rid"))
        elif t.arg1.is_zero():
            return pt.on_rhs(rewr_conv("real_add_lid"))
        if not t.arg.is_number() and not t.arg.is_times():
            pt = pt.on_rhs(arg_conv(rewr_conv("real_mul_lid", sym=True))) 
        if t.is_constant():
            return pt.on_rhs(real.real_eval_conv())
        if t.arg1.is_times(): # a * x + atom
            if t.arg.is_number(): # a * x + c
                return pt.on_rhs(rewr_conv("real_add_comm"))
            elif t.arg.is_times(): # a * x + b * y
                cp = compare_atom(t.arg1, t.arg)
                if cp == 0: # a * x + b * x
                    pt1 = pt.on_rhs(
                        rewr_conv("real_add_rdistrib", sym=True),
                        arg1_conv(real.real_eval_conv())
                    )
                    if pt1.rhs.arg1.is_zero():
                        return pt1.on_rhs(rewr_conv('real_mul_lzero'))
                    else:
                        return pt1
                elif cp > 0:
                    return pt.on_rhs(rewr_conv("real_add_comm"))
                else:
                    return pt
            else:
                raise ConvException
        elif t.arg1.is_plus():
            if t.arg.is_number():
                return pt.on_rhs(real.swap_add_r(), arg1_conv(self), try_conv(rewr_conv('real_add_lid')))
            elif t.arg.is_times():
                cp = compare_atom(t.arg1.arg, t.arg)
                if cp > 0:
                    return pt.on_rhs(real.swap_add_r(), arg1_conv(self))
                elif cp == 0:
                    pt1 = pt.on_rhs(
                        rewr_conv("real_add_assoc", sym=True), 
                        arg_conv(rewr_conv("real_add_rdistrib", sym=True)),
                        arg_conv(arg1_conv(real.real_eval_conv())))
                    if pt1.rhs.arg.arg1.is_zero():
                        return pt1.on_rhs(arg_conv(rewr_conv('real_mul_lzero')), rewr_conv('real_add_rid'))
                    else:
                        return pt1
                else:
                    return pt
            else:
                raise ConvException
        else:
            return pt

class norm_add_lra_conv(Conv):
    def get_proof_term(self, t: hol_term.Term) -> ProofTerm:
        pt = refl(t)
        if t.is_constant():
            return pt.on_rhs(real.real_eval_conv())
        elif t.arg1.is_zero():
            return pt.on_rhs(rewr_conv("real_add_lid"))
        elif t.arg.is_zero():
            return pt.on_rhs(rewr_conv("real_add_rid"))
        elif t.arg.is_plus():
            return pt.on_rhs(
                rewr_conv('real_add_assoc'),
                arg1_conv(self),
                real_norm_add_atom_conv()
            )
        else:
            return pt.on_rhs(real_norm_add_atom_conv())



class norm_lra_conv(Conv):
    def get_proof_term(self, t):
        pt = refl(t)
        if t.is_constant():
            return pt.on_rhs(real.real_eval_conv())
        elif t.is_plus():
            return pt.on_rhs(binop_conv(self), norm_add_lra_conv())
        elif t.is_minus():
            return pt.on_rhs(binop_conv(self), 
                rewr_conv("real_poly_neg2"), arg_conv(rewr_conv('real_poly_neg1', sym=True)), 
                arg_conv(neg_lra_conv()), self)
        elif t.is_times():
            if not t.arg1.is_constant():
                return pt
            if t.arg.is_uminus(): # c * (-x)
                return pt.on_rhs(
                    arg_conv(rewr_conv('real_poly_neg1')), # c * (-1 * x)
                    rewr_conv('real_mult_assoc'),
                    arg1_conv(real.real_eval_conv())
                )
            elif t.arg.is_plus():
                return pt.on_rhs(
                    const_prod_lra_conv(),
                    self
                )
            elif t.arg.is_minus():
                return pt.on_rhs(arg_conv(self), self)
            elif t.arg.is_times() and t.arg.arg1.is_constant():
                return pt.on_rhs(rewr_conv('real_mult_assoc'), arg1_conv(real.real_eval_conv()), self)
            else:
                return pt
        elif t.is_uminus():
            return pt.on_rhs(rewr_conv('real_poly_neg1'))
        else:
            return pt.on_rhs(rewr_conv('real_mul_lid', sym=True))

class neg_lra_conv(Conv):
    def get_proof_term(self, t: hol_term.Term) -> ProofTerm:
        pt = refl(t)
        if not t.is_uminus():
            return pt
        if t.arg.is_constant():
            return pt.on_rhs(real.real_eval_conv())
        elif t.arg.is_times():
            return pt.on_rhs(rewr_conv("real_mul_lneg", sym=True), arg1_conv(real.real_eval_conv()))
        elif t.arg.is_plus():
            return pt.on_rhs(rewr_conv('real_neg_add'), binop_conv(self), norm_lra_conv())
        else:
            return pt.on_rhs(rewr_conv('real_poly_neg1'))        

class simp_lra_conv(Conv):
    """rewrite 0 + lra -> lra, rewrite 1 * x -> x"""
    def get_proof_term(self, t: hol_term.Term) -> ProofTerm:
        return refl(t).on_rhs(
            norm_lra_conv(),
            top_conv(rewr_conv('real_mul_lid'))
        )
        

class const_prod_lra_conv(Conv):
    def get_proof_term(self, t):
        pt = refl(t)
        if t.is_constant():
            return pt.on_rhs(real.real_eval_conv())
        if not t.is_times() or not t.arg1.is_number():
            return pt
        if t.arg1.is_zero():
            return pt.on_rhs(rewr_conv('real_mul_lzero'))
        elif t.arg.is_zero():
            return pt.on_rhs(rewr_conv('real_mul_rzero'))
        elif t.arg.is_plus():
            return pt.on_rhs(rewr_conv('real_add_ldistrib'), binop_conv(self))
        elif t.arg.is_times():
            return pt.on_rhs(rewr_conv('real_mult_assoc'), arg1_conv(real.real_eval_conv()))
        else:
            return pt


class combine_clause(Conv):
    """Rewrite (s_1 \/ s_2 ... \/ s_m) \/ (t_1 \/ t_2 ... \/ t_n) <-->
               s_1 \/ s_2 ... \/ s_m \/ t_1 \/ t_2 ... \/ t_n.
               
    """
    def get_proof_term(self, t):
        if t.arg1.is_disj():
            return refl(t).on_rhs(rewr_conv('disj_assoc_eq', sym=True), arg_conv(self))
        else:
            return refl(t)

class combine_clause_cnf(Conv):
    """Rewrite s \/ (t_1 /\ t_2 ... /\ t_n) <-->
               (s \/ t_1) /\ (s \/ t_2) /\ ... /\ (s \/ t_n).
    Note s and each t_1, ... t_n are clauses, and clauses are combined
    on disjunction.
    
    """
    def get_proof_term(self, t):
        if t.arg.is_conj():
            return refl(t).on_rhs(
                rewr_conv('disj_conj_distribL1'),
                arg1_conv(combine_clause()),
                arg_conv(self))
        else:
            return refl(t).on_rhs(combine_clause())

class combine_disj_cnf(Conv):
    """Rewrite (s_1 /\ s_2 ... /\ s_m) \/ (t_1 /\ t_2 ... /\ t_n) <-->
               (s_1 \/ t_1) /\ (s_1 \/ t_2) /\ ... /\ (s_m \/ t_n).
    Note each s_i and t_j are clauses, and clauses are combined on disjunction.
    
    """
    def get_proof_term(self, t):
        if t.arg1.is_conj():
            return refl(t).on_rhs(
                rewr_conv('disj_conj_distribL2'),
                arg1_conv(combine_clause_cnf()),
                arg_conv(self))
        else:
            return refl(t).on_rhs(combine_clause_cnf())

class combine_conj_cnf(Conv):
    """Rewrite (s_1 /\ s_2 ... /\ s_m) /\ (t_1 /\ t_2 ... /\ t_n) <-->
               s_1 /\ s_2 ... /\ s_m /\ t_1 /\ t_2 ... /\ t_n.
    
    """
    def get_proof_term(self, t):
        if t.arg1.is_conj():
            return refl(t).on_rhs(rewr_conv('conj_assoc', sym=True), arg_conv(self))
        else:
            return refl(t)

class cnf_conv(Conv):
    """Rewriting to CNF form"""
    def get_proof_term(self, t: hol_term.Term) -> ProofTerm:
        pt = refl(t)
        if t.is_not():
            if t.arg.is_not():
                return pt.on_rhs(rewr_conv('double_neg'), self)
            elif t.arg.is_disj():
                return pt.on_rhs(deMorgan_disj_conv(), self)
            elif t.arg.is_conj():
                return pt.on_rhs(deMorgan_conj_conv(), self)
            elif t.arg.is_implies():
                return pt.on_rhs(rewr_conv('not_imp'), self)
            elif t.arg.is_equals() and t.arg.arg1.get_type() == hol_term.BoolType:
                return pt.on_rhs(rewr_conv('verit_not_iff_eq'), self)
            elif logic.is_if(t.arg) and t.arg.args[1].get_type() == hol_term.BoolType:
                return pt.on_rhs(rewr_conv('verit_not_ite_eq'), self)
            else:
                return pt
        elif t.is_disj():
            return pt.on_rhs(binop_conv(self), combine_disj_cnf())
        elif t.is_conj():
            return pt.on_rhs(binop_conv(self), combine_conj_cnf())
        elif t.is_implies():
            return pt.on_rhs(rewr_conv('disj_conv_imp', sym=True), self)
        elif t.is_equals() and t.arg1.get_type() == hol_term.BoolType:
            return pt.on_rhs(rewr_conv('verit_iff_eq'), self)
        elif logic.is_if(t) and t.args[1].get_type() == hol_term.BoolType:
            return pt.on_rhs(rewr_conv('verit_ite_eq'), self)
        elif t.is_forall():
            return pt.on_rhs(arg_conv(abs_conv(self)))
        else:
            return pt


class exists_forall_conv(Conv):
    """Prove the equivalence between
        EX x_1 x_2 ... x_n. P x_1 x_2 ... x_n
    and ~ALL x_1 x_2 ... x_n. ~P x_1 x_2 ... x_n.
    
    """
    def get_proof_term(self, t):
        if not t.is_exists():
            return refl(t)
        
        pt1 = refl(t).on_rhs(rewr_conv('verit_connective_def4'))
        pt2 = pt1.on_rhs(arg_conv(arg_conv(abs_conv(arg_conv(try_conv(beta_conv()))))))
        if not t.arg.body.is_exists():
            return pt2
        pt3 = pt2.on_rhs(arg_conv(arg_conv(abs_conv(arg_conv(self)))))
        pt4 = pt3.on_rhs(arg_conv(arg_conv(abs_conv(rewr_conv('double_neg')))))
        return pt4
