"""
Macros used in the proof reconstruction.
"""

from kernel.macro import Macro
from kernel.theory import register_macro
from kernel.proofterm import ProofTerm, Thm
from kernel.term import Term, Not, Or, Eq, Implies, false, true
from prover.proofrec import int_th_lemma_1_omega, int_th_lemma_1_simplex, real_th_lemma
from logic import conv, logic
from data import integer, real, proplogic
import functools

@register_macro("imp_to_or")
class ImpEqToMacro(Macro):
    """Given a proof term ⊢ A --> B --> ... --> C, 
    construct ⊢ ~A | ~B | ... | C"""
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def eval(self, args, prevs):
        pt = prevs[0]
        goal = args[-1]
        # preds, concl = pt.prop.strip_implies()
        concl = Or(*args[:-1], pt.prop)
        assert concl == goal, "%s %s" % (concl, goal)
        return Thm([], concl)
    
    def get_proof_term(self, args, prevs):
        disjs = [tm.arg for arg in args]
        pt0 = prevs[0]
        pt1 = functools.reduce(lambda x, y: x.implies_intr(y).on_prop(rewr_conv("imp_disj_eq")), reversed(disjs), pt0)
        return pt1

@register_macro("verit_and_rule")
class AndRuleMacro(Macro):
    """Given a disj term which pattern is like not (= x_1 x_2)) | ... | not (= x_{n-1} x_n) | (= x_1 x_n)."""
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def get_proof_term(self, goal, prevs=None):
        elems = goal.strip_disj()
        
        disjs = [tm.arg for tm in elems[:-1]]
        disj_pts = [ProofTerm.assume(disj) for disj in disjs]
        pt0 = disj_pts[0]
        for pt1 in disj_pts[1:]:
            if pt1.lhs == pt0.rhs:
                pt0 = pt0.transitive(pt1)
            elif pt1.lhs == pt0.lhs:
                pt0 = pt0.symmetric().transitive(pt1)
            elif pt1.rhs == pt0.lhs:
                pt0 = pt0.symmetric().transitive(pt1.symmetric())
            elif pt1.rhs == pt0.rhs:
                pt0 = pt0.transitive(pt1.symmetric())
            
            else:
                print(pt0.prop)
                print(pt1.prop)
                raise NotImplementedError
        
        if pt0.symmetric().prop == elems[-1]:
            pt0 = pt0.symmetric() 

        assert pt0.prop == elems[-1], "%s \n %s" % (str(pt0.prop), str(goal.strip_disj()[-1]))
        
        return ProofTerm("imp_to_or", elems[:-1]+[goal], prevs=[pt0])

@register_macro("verit_eq_congurent")
class EqCongurentMacro(Macro):
    """Given a disj term which pattern is like (not (= x_1 y_1)) ... (not (= x_n y_n)) (= (f x_1 ... x_n) (f y_1 ... y_n)).
    Note: 
    1) The following situation is possible: (... (not (= x_i y_i) ...) (= (f ... y_i ...) (f ... x_i ...)).
    2) Using a pair twice but only given one. (not (= x_1 y_1)) (not (= x_2 y_2)) (= (f x_1 x_2 x_2) (f y_1 y_2 y_2))

    """
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None
    
    def get_proof_term(self, goal, prevs=None):
        elems = goal.strip_disj()
        preds, concl = elems[:-1], elems[-1]
        args_pair = [(i, j) for i, j in zip(concl.lhs.strip_comb()[1], concl.rhs.strip_comb()[1])]
        preds_pair = [(i.arg.lhs, i.arg.rhs) for i in preds]
        fun = concl.lhs.head
        pt0 = ProofTerm.reflexive(fun)
        pt_args_assms = []
        for pair in args_pair:
            r_pair = pair[::-1]
            if pair in args_pair:
                pt_args_assms.append(ProofTerm.assume(Eq(*pair)))
            elif r_pair in args_pair:
                pt_args_assms.append(ProofTerm.assume(Eq(*r_pair)))

        pt1 = functools.reduce(lambda x, y: x.combination(y), pt_args_assms, pt0)
        return ProofTerm("imp_to_or", elems[:-1]+[goal], prevs=[pt1])

@register_macro("verit_eq_congurent_pred")
class EqCongurentPredMacro(Macro):
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None
    def get_proof_term(self, goal, prevs=None):
        """{(not (= x_1 y_1)) ... (not (= x_n y_n)) (not (p x_1 ... x_n)) (p y_1 ... y_n)}
        Special case: (not (= x y)) (not (p x y)) (p y x)
        """
        elems = goal.strip_disj()
        preds, pred_fun, concl = elems[:-2], elems[-2], elems[-1] 
        if pred_fun.is_not():
            args_pair = [(i, j) for i, j in zip(pred_fun.arg.strip_comb()[1], concl.strip_comb()[1])]
        else:
            args_pair = [(i, j) for i, j in zip(pred_fun.strip_comb()[1], concl.arg.strip_comb()[1])]
        if len(preds) > 1:
            preds_pair = [(i.arg.lhs, i.arg.rhs) for i in preds]
        else:
            preds_pair = [(preds[0].arg.lhs, preds[0].arg.rhs), (preds[0].arg.lhs, preds[0].arg.rhs)]
        if pred_fun.is_not():
            fun = concl.head
        else:
            fun = pred_fun.head
        pt0 = ProofTerm.reflexive(fun)
        pt_args_assms = []
        for arg, pred in zip(args_pair, preds_pair):
            if arg == pred:
                pt_args_assms.append(ProofTerm.assume(Eq(pred[0], pred[1])))
            elif arg[0] == pred[1] and pred[0] == arg[1]:
                pt_args_assms.append(ProofTerm.assume(Eq(pred[0], pred[1])).symmetric())
            else:
                raise NotImplementedError
        pt1 = functools.reduce(lambda x, y: x.combination(y), pt_args_assms, pt0)
        if pred_fun.is_not():
            pt2 = logic.apply_theorem("eq_implies1", pt1).implies_elim(ProofTerm.assume(pred_fun.arg))
            return ProofTerm("imp_to_or", elems[:-1]+[goal], prevs=[pt2])
        else:
            pt2 = pt1.on_prop(conv.rewr_conv("neg_iff_both_sides"))
            pt3 = logic.apply_theorem("eq_implies1", pt2).implies_elim(ProofTerm.assume(Not(pred_fun)))
            return ProofTerm("imp_to_or", elems[:-1]+[goal], prevs=[pt3])   


@register_macro("not_or_rule")
class NotOrRuleMacro(Macro):
    """prove {(not (or a_1 ... a_n))} --> {(not a_i)}"""
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def eval(self, args, prevs):
        pt0 = prevs[0]
        goal = args[0]
        disjs = pt0.prop.arg.strip_disj()
        # assert goal.arg in disjs, "proof: %s, goal %s" % (pt0, goal)
        return Thm(pt0.hyps, goal)

    def get_proof_term(self, args, prevs):
        pt0 = prevs[0]
        goal = args[0]

        pt1 = pt0.on_prop(rewr_conv("de_morgan_thm2"))
        pt2 = pt1
        while pt2.prop != goal:
            pt_l = logic.apply_theorem("conjD1", pt2)
            pt_r = logic.apply_theorem("conjD2", pt2)
            if pt_l.prop == goal:
                pt2 = pt_l
                break
            else:
                pt2 = pt_r

        return pt2

def strip_num(tm, num):
    """Strip the disjunction/conjunction by the provided number, in case of
    over-strip.
    """
    disj = tm
    atoms = []
    for i in range(num-1):
        atoms.append(disj.arg1)
        disj = disj.arg

    return atoms + [disj]

@register_macro('verit_resolution')
class VeritResolutionMacro(Macro):
    def __init__(self):
        self.level = 1
        self.sig = None
        self.limit = 'resolution_right'

    def get_proof_term(self, args, pts):

        # First, find the pair i, j such that B_j = ~A_i or A_i = ~B_j, the
        # variable side records the side of the positive literal.
        pt1, pt2 = pts
        disj1 = strip_num(pt1.prop, args[0])
        disj2 = strip_num(pt2.prop, args[1])
        side = None
        for i, t1 in enumerate(disj1):
            for j, t2 in enumerate(disj2):
                if t2 == Not(t1):
                    side = 'left'
                    break
                elif t1 == Not(t2):
                    side = 'right'
                    break
            if side is not None:
                break
                
        assert side is not None, "resolution: literal not found"
        
        # If side is wrong, just swap:
        if side == 'right':
            return self.get_proof_term([args[1], args[0]], [pt2, pt1])
        
        # Move items i and j to the front
        disj1 = [disj1[i]] + disj1[:i] + disj1[i+1:]
        disj2 = [disj2[j]] + disj2[:j] + disj2[j+1:]
        eq_pt1 = logic.imp_disj_iff(Eq(pt1.prop, Or(*disj1)))
        eq_pt2 = logic.imp_disj_iff(Eq(pt2.prop, Or(*disj2)))
        pt1 = eq_pt1.equal_elim(pt1)
        pt2 = eq_pt2.equal_elim(pt2)
        
        if len(disj1) > 1 and len(disj2) > 1:
            pt = logic.apply_theorem('resolution', pt1, pt2)
        elif len(disj1) > 1 and len(disj2) == 1:
            pt = logic.apply_theorem('resolution_left', pt1, pt2)
        elif len(disj1) == 1 and len(disj2) > 1:
            pt = logic.apply_theorem('resolution_right', pt1, pt2)
        else:
            pt = logic.apply_theorem('negE', pt2, pt1)

        # return pt.on_prop(disj_norm())
        disj_new = set(disj1[1:] + disj2[1:])
        # eq_pt_norm = logic.imp_disj_iff(Eq(pt.prop, Or(*disj_new)))
        implies_pt_norm = ProofTerm("imp_disj", Implies(pt.prop, Or(*disj_new)))
        pt_final = implies_pt_norm.implies_elim(pt)
        self.arity = len(disj_new)
        return pt_final.on_prop(conv.top_conv(conv.rewr_conv("double_neg")))

def verit_resolution(pt1, pt2, arity1, arity2):
    marc = VeritResolutionMacro()
    pt = marc.get_proof_term([arity1, arity2], [pt1, pt2])
    return pt, marc.arity
    # return ProofTerm("verit_resolution", [arity1, arity2], [pt1, pt2])
    
@register_macro("and_neg")
class AndNegMacro(Macro):
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def eval(self, args, prevs=None):
        arity, goal = args[0], args[1]
        conj, disj = goal.arg1, goal.arg
        conj_atoms = strip_num(conj, arity-1)
        disj_atoms = strip_num(disj, arity-1)
        for i, j in zip(conj_atoms, disj_atoms):
            if i.is_not():
                assert i.arg == j
            elif j.is_not():
                assert i == j.arg
            else:
                raise NotImplementedError
        return Thm([], goal)

@register_macro("not_and")
class NotAndMacro(Macro):
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def eval(self, args, prevs):
        goal, pt0 = args[0], prevs[0]
        conj_atoms = pt0.prop.arg.strip_conj()
        disj_atoms = strip_num(goal, len(conj_atoms))
        for i, j in zip(conj_atoms, disj_atoms):
            if i.is_not():
                assert i.arg == j
            elif j.is_not():
                assert i == j.arg
            else:
                raise NotImplementedError
        return Thm([], goal)

@register_macro("or_pos")
class OrPosMacro(Macro):
    """⊢ ¬(a_1 ∨ ... ∨ a_n) ∨ a_1 ∨ ... ∨ a_n"""
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def eval(self, goal, prevs=None):
        assert goal.arg1.arg == goal.arg
        return Thm([], goal)

@register_macro("la_generic")
class LaGenericMacro(Macro):
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def is_constant(self, tm):
        """Determine whether tm is an inequality only containing constants."""
        return tm.is_compares() and tm.arg1.is_number() and tm.arg.is_number()

    def real_solver(self, args):
        refl_pt = conv.refl(args).on_rhs(
            conv.top_conv(conv.rewr_conv("real_ge_le_same_num")),
            conv.top_conv(conv.rewr_conv("de_morgan_thm1")),
            conv.top_conv(real.norm_neg_real_ineq_conv()),
            conv.top_conv(real.real_norm_comparison()),
            conv.top_conv(real.real_const_compares()),
            proplogic.norm_full()
        )
        if refl_pt.rhs == true:
            return refl_pt.on_prop(conv.rewr_conv("eq_true", sym=True))

        pt_result = real_th_lemma([refl_pt.rhs])
        return refl_pt.symmetric().equal_elim(pt_result)

    def int_solver(self, args):
        refl_pt = conv.refl(args).on_rhs(
                conv.top_conv(conv.rewr_conv("int_eq_leq_geq")),
                conv.top_conv(conv.rewr_conv("de_morgan_thm1")),
                conv.top_conv(integer.int_norm_neg_compares()),
                conv.top_conv(integer.omega_form_conv()),
                conv.top_conv(integer.int_const_compares()),
                proplogic.norm_full()
        )
        if refl_pt.rhs == true:
            return refl_pt.on_prop(conv.rewr_conv("eq_true", sym=True))

        try:
            pt_result = int_th_lemma_1_omega(refl_pt.rhs)
        except:
            pt_result = int_th_lemma_1_simplex(refl_pt.rhs)
        return refl_pt.symmetric().equal_elim(pt_result)
        

    def get_proof_term(self, args, is_int=True):
        if is_int:
            return self.int_solver(args)
        else:
            return self.real_solver(args)