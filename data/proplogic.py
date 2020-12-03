from kernel.term import Term, BoolType, Not, Var, true, false, And
from logic.conv import Conv, rewr_conv, arg1_conv, arg_conv, binop_conv, try_conv
from kernel.proofterm import refl, ProofTerm
from logic.logic import apply_theorem
from logic import matcher
from kernel import term_ord
from logic import basic
from collections import deque
import functools

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
            return pt.on_rhs(binop_conv(self), sort_conj())
        elif t.is_disj():
            return pt.on_rhs(binop_conv(self), sort_disj())
        elif t.is_equals():
            lhs, rhs = t.lhs, t.rhs
            if lhs == rhs:
                return pt.on_rhs(rewr_conv('eq_mean_true'))
            elif lhs == true: # (true ⟷ P) ⟷ P
                return pt.on_rhs(rewr_conv('eq_sym_eq'), rewr_conv('eq_true', sym=True))
            elif rhs == true: # (P ⟷ true) ⟷ P
                return pt.on_rhs(rewr_conv('eq_true', sym=True))
            elif lhs == false: # (false ⟷ P) ⟷ ¬P
                return pt.on_rhs(rewr_conv('eq_sym_eq'), rewr_conv('eq_false', sym=True))
            elif rhs == true: # (P ⟷ false) ⟷ ¬P
                return pt.on_rhs(rewr_conv('eq_false', sym=True))
            else:
                return pt.on_rhs(binop_conv(self))
        elif t.is_not() and (t.arg.is_conj() or t.arg.is_disj() or t.arg.is_not() or t.arg == true or t.arg == false):
            return pt.on_rhs(nnf_conv(), self)
        elif t.is_not() and t.arg.is_equals():
            return pt.on_rhs(nnf_conv())
        else:
            return pt

class sort_conj(Conv):
    """Given a conjunction, return its normal form"""
    def get_proof_term(self, t):
        
        if not t.is_conj():
            return refl(t)

        d_pos = dict()
        d_neg = dict()
        qu = deque([ProofTerm.assume(t)])
        # collect each conjunct's proof term in conjuntion
        while qu:
            pt = qu.popleft()
            if pt.prop.is_conj():
                conj1, conj2 = pt.prop.arg1, pt.prop.arg
                pt_conj1, pt_conj2 = apply_theorem('conjD1', pt), apply_theorem('conjD2', pt)
                if conj1 == false:
                    th = ProofTerm.theorem("falseE")
                    inst = matcher.first_order_match(th.prop.arg, t)
                    pt_false_implies_conj = th.substitution(inst)
                    return ProofTerm.equal_intr(pt_conj1.implies_intr(t), pt_false_implies_conj)
                elif conj2 == false:
                    th = ProofTerm.theorem("falseE")
                    inst = matcher.first_order_match(th.prop.arg, t)
                    pt_false_implies_conj = th.substitution(inst)
                    return ProofTerm.equal_intr(pt_conj2.implies_intr(t), pt_false_implies_conj)
                if conj1.is_conj():
                    qu.appendleft(pt_conj1)
                else:
                    if conj1.is_not():
                        d_neg[conj1] = pt_conj1
                    else:
                        d_pos[conj1] = pt_conj1
                if conj2.is_conj():
                    qu.appendleft(pt_conj2)
                else:
                    if conj2.is_not():
                        d_neg[conj2] = pt_conj2
                    else:
                        d_pos[conj2] = pt_conj2
            else:
                d[pt.prop] = pt

        # first check if there are opposite terms in conjunctions, if there exists, return a false proof term
        for key in d_pos:
            if Not(key) in d_neg:
                pos_pt, neg_pt = d_pos[key], d_neg[Not(key)]
                pt_conj_pos_neg = apply_theorem("conjI", pos_pt, neg_pt)
                pt_conj_implies_false = pt_conj_pos_neg.on_prop(rewr_conv("conj_pos_neg")).implies_intr(t)
                th = ProofTerm.theorem("falseE")
                inst = matcher.first_order_match(th.prop.arg, t)
                pt_false_implies_conj = th.substitution(inst)
                return ProofTerm.equal_intr(pt_conj_implies_false, pt_false_implies_conj)

        d_pos.update(d_neg)
        d = d_pos
        def right_assoc(ts):
            l = len(ts)
            if l == 1:
                return d[ts[0]]
            elif l == 2:
                return apply_theorem('conjI', d[ts[0]], d[ts[1]])
            else:
                return apply_theorem('conjI', d[ts[0]], right_assoc(ts[1:]))

        # pt_right = functools.reduce(lambda x, y: apply_theorem('conjI', x, d[y]), sorted(d.keys()), d[sorted(d.keys())[0]])
        if true not in d:
            sorted_keys = term_ord.sorted_terms(d.keys())
        else:
            d_keys_without_true = term_ord.sorted_terms([k for k in d if k != true])
            sorted_keys = [true] + d_keys_without_true
        pt_right = right_assoc(sorted_keys)
        # order implies chaos
        dd = dict()
        norm_conj = And(*sorted_keys)
        norm_conj_pt = ProofTerm.assume(norm_conj)
        for k in sorted_keys:
            if k != sorted_keys[-1]:
                dd[k] = apply_theorem('conjD1', norm_conj_pt)
                norm_conj_pt = apply_theorem('conjD2', norm_conj_pt)
            else:
                dd[k] = norm_conj_pt

        def traverse(t):
            if not t.is_conj():
                return dd[t]
            else:
                return apply_theorem('conjI', traverse(t.arg1), traverse(t.arg))

        pt_left =  traverse(t)

        pt_final = ProofTerm.equal_intr(pt_right.implies_intr(t), pt_left.implies_intr(norm_conj))
        if true in d:
            return pt_final.on_rhs(rewr_conv("conj_true_left"))
        else:
            return pt_final

class sort_disj(Conv):
    """Given a conjunction, return its normal form"""
    def get_proof_term(self, t):
        if not t.is_disj():
            return refl(t)

        nnf_pt = nnf_conv().get_proof_term(Not(t))
        norm_neg_disj_pt = sort_conj().get_proof_term(nnf_pt.rhs)
        nnf_pt_norm = nnf_pt.transitive(norm_neg_disj_pt)
        return nnf_pt_norm.on_prop(rewr_conv('neg_iff_both_sides'), arg1_conv(rewr_conv('double_neg')), arg_conv(nnf_conv()))