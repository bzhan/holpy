from kernel.term import Term, BoolType, Not, Var, true, false
from logic.conv import Conv, rewr_conv, arg1_conv, arg_conv, binop_conv, try_conv
from kernel.proofterm import refl
from kernel import term_ord
from logic import basic
basic.load_theory('int')

class nnf_conv(Conv):
    """
    Convert a term to negation normal form.
    """
    def get_proof_term(self, t):
        pt = refl(t)
        if t.is_not():
            if t.arg == true:
                return pt.on_rhs(rewr_conv('not_true'))
            elif t.arg == false:
                return pt.on_rhs(rewr_conv('not_false'))
            elif t.arg.is_not():
                return pt.on_rhs(rewr_conv('double_neg'), self)
            elif t.arg.is_conj():
                return pt.on_rhs(rewr_conv('de_morgan_thm1'), arg1_conv(self), arg_conv(self))
            elif t.arg.is_disj():
                return pt.on_rhs(rewr_conv('de_morgan_thm2'), arg1_conv(self), arg_conv(self))
            elif t.arg.is_equals() and t.arg.lhs.get_type() == BoolType:
                return pt.on_rhs(rewr_conv('neg_iff'), binop_conv(self))
            else:
                return pt
        elif t.is_disj() or t.is_conj() or t.is_equals():
            return pt.on_rhs(arg1_conv(self), arg_conv(self))
        else:
            return pt

class swap_conj_r(Conv):
    """Rewrite A1 /\ (A2 /\ A3) to A2 /\ (A1 /\ A3), or if the left argument
    is an atom, rewrite A1 /\ A2 to A2 /\ A1."""
    def get_proof_term(self, t):
        pt = refl(t)
        if t.arg.is_conj():
            return pt.on_rhs(rewr_conv('conj_assoc'),
                            arg1_conv(rewr_conv('conj_comm')),
                            rewr_conv('conj_assoc', sym=True))
        else:
            return pt.on_rhs(rewr_conv('conj_comm'))

class norm_conj_atom(Conv):
    """Normalize conjunction A /\ (A_1 /\ ... /\ A_n). """
    def get_proof_term(self, t):
        pt = refl(t)
        if t.arg1 == true:
            return pt.on_rhs(rewr_conv('conj_true_left'))
        elif t.arg == true:
            return pt.on_rhs(rewr_conv('conj_true_right'))
        elif t.arg1 == false:
            return pt.on_rhs(rewr_conv('conj_false_right'))
        elif t.arg == false:
            return pt.on_rhs(rewr_conv('conj_false_left'))
        elif t.arg.is_conj():
            if t.arg1 == Not(t.arg.arg1): # A /\ (A_1 /\ ... /\ A_n) 
                return pt.on_rhs(rewr_conv('conj_assoc'), 
                                arg1_conv(rewr_conv('conj_neg_pos')),
                                rewr_conv('conj_false_right'))
            elif Not(t.arg1) == t.arg.arg1:
                return pt.on_rhs(rewr_conv('conj_assoc'),
                                arg1_conv(rewr_conv('conj_pos_neg')),
                                rewr_conv('conj_false_right'))
            
            cp = term_ord.fast_compare(t.arg1, t.arg.arg1)
            if cp > 0:
                return pt.on_rhs(swap_conj_r(), arg_conv(self), try_conv(self))
            elif cp == 0:
                return pt.on_rhs(rewr_conv('conj_assoc'), 
                                arg1_conv(rewr_conv('conj_same_atom')))
            else:
                return pt
        else:
            if t.arg == Not(t.arg1):
                return pt.on_rhs(rewr_conv('conj_pos_neg'))
            elif t.arg1 == Not(t.arg):
                return pt.on_rhs(rewr_conv('conj_neg_pos'))
            cp = term_ord.fast_compare(t.arg1, t.arg)
            if cp > 0:
                return pt.on_rhs(swap_conj_r())
            elif cp == 0:
                return pt.on_rhs(rewr_conv('conj_same_atom'))
            else:
                return pt

class norm_conj_conjunction(Conv):
    """Normalize term like (A_1 /\ ... /\ A_m) /\ (B_1 /\ ... /\ B_n) """
    def get_proof_term(self, t):
        pt = refl(t)
        if t.arg1.is_conj():
            return pt.on_rhs(
                rewr_conv('conj_assoc', sym=True),
                arg_conv(self),
                norm_conj_atom()
            )
        else:
            return pt.on_rhs(norm_conj_atom())

class swap_disj_r(Conv):
    """Rewrite A1 \/ (A2 \/ A3) to A2 \/ (A1 \/ A3), or if the left argument
    is an atom, rewrite A1 \/ A2 to A2 \/ A1."""
    def get_proof_term(self, t):
        pt = refl(t)
        if t.arg.is_disj():
            return pt.on_rhs(rewr_conv('disj_assoc_eq'),
                            arg1_conv(rewr_conv('disj_comm')),
                            rewr_conv('disj_assoc_eq', sym=True))
        else:
            return pt.on_rhs(rewr_conv('disj_comm'))

class norm_disj_atom(Conv):
    """Normalize disjunction A \/ (A_1 \/ ... \/ A_n). """
    def get_proof_term(self, t):
        pt = refl(t)
        if t.arg1 == true:
            return pt.on_rhs(rewr_conv('disj_true_left'))
        elif t.arg == true:
            return pt.on_rhs(rewr_conv('disj_true_right'))
        elif t.arg1 == false:
            return pt.on_rhs(rewr_conv('disj_false_left'))
        elif t.arg == false:
            return pt.on_rhs(rewr_conv('disj_false_right'))
        elif t.arg.is_disj():
            if t.arg1 == Not(t.arg.arg1): # A \/ (A_1 \/ ... \/ A_n) 
                return pt.on_rhs(rewr_conv('disj_assoc_eq'), 
                                arg1_conv(rewr_conv('disj_neg_pos')),
                                rewr_conv('disj_true_left'))
            elif Not(t.arg1) == t.arg.arg1:
                return pt.on_rhs(rewr_conv('disj_assoc_eq'),
                                arg1_conv(rewr_conv('disj_pos_neg')),
                                rewr_conv('disj_true_left'))
            
            cp = term_ord.fast_compare(t.arg1, t.arg.arg1)
            if cp > 0:
                return pt.on_rhs(swap_disj_r(), arg_conv(self))
            elif cp == 0:
                return pt.on_rhs(rewr_conv('disj_assoc_eq'), 
                                arg1_conv(rewr_conv('disj_same_atom')))
            else:
                return pt
        else:
            cp = term_ord.fast_compare(t.arg1, t.arg)
            if cp > 0:
                return pt.on_rhs(swap_disj_r())
            elif cp == 0:
                return pt.on_rhs(rewr_conv('disj_same_atom'))
            else:
                return pt

class norm_disj_disjunction(Conv):
    """Normalize term like (A_1 \/ ... \/ A_m) \/ (B_1 \/ ... \/ B_n) """
    def get_proof_term(self, t):
        pt = refl(t)
        if t.arg1.is_disj():
            return pt.on_rhs(
                rewr_conv('disj_assoc_eq', sym=True),
                arg_conv(self),
                norm_disj_atom()
            )
        else:
            return pt.on_rhs(norm_disj_atom())

class norm_full(Conv):
    """Normalize the full propostional formula."""
    def get_proof_term(self, t):
        pt = refl(t)
        if t.is_conj():
            return pt.on_rhs(binop_conv(self), norm_conj_conjunction())
        elif t.is_disj():
            return pt.on_rhs(binop_conv(self), norm_disj_disjunction())
        elif t.is_equals():
            return pt.on_rhs(binop_conv(self))
        elif t.is_not() and (t.arg.is_conj() or t.arg.is_disj() or t.arg.is_not() or t.arg == true or t.arg == false):
            return pt.on_rhs(nnf_conv(), self)
        elif t.is_not() and t.arg.is_equals():
            return pt.on_rhs(nnf_conv())
        else:
            return pt