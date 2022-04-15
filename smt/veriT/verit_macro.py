"""
Macros used in the proof reconstruction.
"""

from atexit import register
from re import L
from kernel.macro import Macro
from kernel.theory import register_macro
from kernel.proofterm import ProofTerm, Thm
from kernel.term import Term, Not, Or, Eq, Implies, false, true, IntType, RealType
from prover.proofrec import int_th_lemma_1_omega, int_th_lemma_1_simplex, real_th_lemma
from logic import conv, logic
from data import integer, real, proplogic
import functools


def expand_disj(t):
    """Only expand disjunction at the outer level."""
    def rec(t):
        if t.is_disj():
            return (t.arg1,) + rec(t.arg)
        else:
            return (t,)
    return list(rec(t))

@register_macro("verit_not_or")
class NotOrMacro(Macro):
    """prove {(not (or a_1 ... a_n))} --> {(not a_i)}"""
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def eval(self, args, prevs):
        """args is the negation we want to prove
        prevs is the negative disjunction
        """
        goal, pt0 = args[0], prevs[0]
        disjs = pt0.prop.arg.strip_disj()
        for d in disjs:
            if d == goal.arg:
                return Thm(pt0.hyps, goal)
        raise NotImplementedError

    def get_proof_term(self, args, prevs):
        goal, pt0 = args[0], prevs[0]
        pt1 = pt0.on_prop(conv.rewr_conv("de_morgan_thm2"))
        pt2 = pt1
        while pt2.prop != goal:
            pt_l = logic.apply_theorem("conjD1", pt2)
            pt_r = logic.apply_theorem("conjD2", pt2)
            if pt_l.prop == goal:
                pt2 = pt_l
                break
            pt2 = pt_r.on_prop(conv.try_conv(conv.rewr_conv("de_morgan_thm2")))
            
        return pt2

@register_macro("verit_not_and")
class NotAndMacro(Macro):
    """Prove ¬(a_1 ∧ ... ∧ a_n) --> ¬a_1 ∨ ... ∨ ¬a_n"""
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def eval(self, args, prevs):
        goal, pt0 = Or(*args), prevs[0]
        conj_atoms = pt0.prop.arg.strip_conj()
        # disj_atoms = strip_num(goal, len(conj_atoms))
        disj_atoms = goal.strip_disj()
        for i, j in zip(conj_atoms, disj_atoms):
            if Not(i) != j:
                raise NotImplementedError(str(i), str(j))

        return Thm(pt0.hyps, goal)

    def get_proof_term(self, args, prevs):
        goal, pt0 = Or(*args), prevs[0]
        conj_atoms = pt0.prop.arg.strip_conj()
        # disj_atoms = strip_num(goal, len(conj_atoms))
        pt1 = pt0.on_prop(conv.top_conv(conv.rewr_conv("de_morgan_thm1")))
        # while pt1.prop != goal:
        #     pt1 = pt1.on_rhs(conv.rewr_conv("de_morgan_thm1"), conv.top_conv(conv.rewr_conv("double_neg")))
        if pt1.prop != goal:
            return ProofTerm.sorry(Thm(pt0.hyps, goal))
        return pt1

@register_macro("verit_not_not")
class NotNotMacro(Macro):
    """Prove tautology ¬(¬¬p) ∨ p"""
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def eval(self, args, prevs=None):
        neg_arg, pos_arg = args
        if neg_arg.arg.arg.arg == pos_arg:
            return Thm([], Or(neg_arg, pos_arg))
        else:
            raise NotImplementedError(str(neg_arg), str(pos_arg))
    
    def get_proof_term(self, args, prevs=None):
        neg_arg, pos_arg = args
        return logic.apply_theorem("neg_neg", concl=Or(neg_arg, pos_arg))

@register_macro("verit_th_resolution")
class ThResolutionMacro(Macro):
    """Return the resolution result of multiple proof terms."""
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    # def eval(self, args, prevs):
    #     for pt in prevs:
    #         print(pt.prop)
    #     props = [pt.prop for pt in prevs]
    #     prop_res = props[0]
    #     disj_atoms = prop_res.strip_disj()
    #     for prop in props[1:]:
    #         # print("prop_rs", prop_res)
    #         # print("prop", prop)
    #         if prop == Not(prop_res) or prop_res == Not(prop):
    #             return Thm([hyp for pt in prevs for hyp in pt.hyps], false)
    #         abandon1, abandon2 = [], []
    #         for d1 in prop_res.strip_disj():                
    #             for d2 in prop.strip_disj():
    #                 if d1 == Not(d2) or d2 == Not(d1):
    #                     # disj_atoms.remove(d1)
    #                     # disj_prop.remove(d2)
    #                     abandon1.append(d1)
    #                     abandon2.append(d2)
    #         disjs = [d1 for d1 in prop_res.strip_disj() if d1 not in abandon1] + \
    #                     [d2 for d2 in prop.strip_disj() if d2 not in abandon2]

    #         # disj_atoms = disj_atoms | disj_prop
    #         prop_res = Or(*disjs)
            

    #     if len(args) == 0:
    #         if len(disj_atoms) == 0:
    #             return Thm([hyp for pt in prevs for hyp in pt.hyps], false)
    #         else:
    #             print("Resolution with following proof terms.")
    #             for pt in prevs:
    #                 print(pt)
    #             print("prop_res", prop_res)
    #             raise NotImplementedError(disj_atoms, args)
    #     if Or(*args) == Or(*disjs):
    #         return Thm([hyp for pt in prevs for hyp in pt.hyps], Or(*args))
    #     else:
    #         print("args", Or(*args), "disjs", Or(*disjs))
    #         raise NotImplementedError

    def resolution_two_pt(self, pt1, pt2):
        disj1 = expand_disj(pt1.prop)
        disj2 = expand_disj(pt2.prop)
        side = None
        total = False
        for i, t1 in enumerate(disj1):
            for j, t2 in enumerate(disj2):
                if t2 == Not(t1) :
                    side = 'left'
                    break
                elif t1 == Not(t2) or t1 == Not(pt2.prop):
                    side = 'right'
                    break
                elif t2 == Not(pt1.prop):
                    side = 'left'
                    total = True
                elif t1 == Not(pt1.prop):
                    side = 'right'
                    total = True
            if side is not None:
                break
                
        assert side is not None, "resolution: literal not found"
        
        # If side is wrong, just swap:
        if side == 'right':
            return self.resolution_two_pt(pt2, pt1)
        
        # Move items i and j to the front
        if not total:
            disj1 = [disj1[i]] + disj1[:i] + disj1[i+1:]
        disj2 = [disj2[j]] + disj2[:j] + disj2[j+1:]
        eq_pt1 = logic.imp_disj_iff(Eq(pt1.prop, Or(*disj1)))        
        eq_pt2 = logic.imp_disj_iff(Eq(pt2.prop, Or(*disj2)))
        if not total:
            pt1 = eq_pt1.equal_elim(pt1)
        pt2 = eq_pt2.equal_elim(pt2)
        if total:
            pt = logic.apply_theorem('resolution_right', pt1, pt2)
        elif len(disj1) > 1 and len(disj2) > 1:
            pt = logic.apply_theorem('resolution', pt1, pt2)
        elif len(disj1) > 1 and len(disj2) == 1:
            pt = logic.apply_theorem('resolution_left', pt1, pt2)
        elif len(disj1) == 1 and len(disj2) > 1:
            pt = logic.apply_theorem('resolution_right', pt1, pt2)
        else:
            pt = logic.apply_theorem('negE', pt2, pt1)

        return pt.on_prop(logic.disj_norm())


    def get_proof_term(self, args, prevs):
        pt_res = prevs[0]
        for pt in prevs[1:]:
            if pt_res.prop == Not(pt.prop):
                pt_res = logic.apply_theorem("negE", pt_res, pt)
            elif pt.prop == Not(pt_res.prop):
                pt_res = logic.apply_theorem("negE", pt, pt_res)
            else:
                pt_res = self.resolution_two_pt(pt_res, pt)
        if len(args) == 0: # |- false
            return pt_res
    
        goal = Or(*args)
        if goal == pt_res.prop:
            return pt_res

        pt_eq_disj = ProofTerm("imp_disj", Implies(pt_res.prop, goal))
        return pt_eq_disj.implies_elim(pt_res)


@register_macro("verit_implies")
class VeritImpliesMacro(Macro):
    """Prove (a --> b) --> ~a | b. """
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def eval(self, args, prevs):
        # goal : ~a | b  pt: |- a --> b
        goal = Or(*args)
        pt = prevs[0]
        if Or(Not(pt.prop.arg1), pt.prop.arg) == goal:
            return Thm(pt.hyps, goal)
        else:
            raise NotImplementedError(str(Or(Not(pt.prop.arg1), pt.prop.arg)), str(goal))

    def get_proof_term(self, args, prevs):
        return prevs[0].on_prop(conv.rewr_conv("imp_disj_eq"))

@register_macro("verit_and_pos")
class VeriTAndPos(Macro):
    """Prove ~(p1 & p2 & ... & pn) | pk"""
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def eval(self, args, prevs=None):
        # args: ~(p1 & p2 & ... & pn) and pk
        neg_conj, pk = args
        conjs = neg_conj.arg.strip_conj()
        if pk in conjs:
            return Thm([], Or(neg_conj, pk))
        else:
            raise NotImplementedError

    def get_proof_term(self, args, prevs=None):
        pt0 = ProofTerm("imp_conj", Implies(args[0].arg, args[1]))
        pt1 = pt0.on_prop(conv.rewr_conv("disj_conv_imp", sym=True))
        return pt1

@register_macro("verit_or_pos")
class VeriTOrPos(Macro):
    """Prove ~(p1 | p2 | ... | pn) | p1 | p2 | ... | pn."""
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def eval(self, args, prevs=None):
        neg_disj = args[0]
        disjs = neg_disj.arg.strip_disj()
        for a, b in zip(disjs, args[1:]):
            if a != b:
                raise NotImplementedError(a, b)
        if tuple(disjs) == tuple(args[1:]):
            return Thm([], Or(*args))
        else:
            raise NotImplementedError
    
    def get_proof_term(self, args, prevs=None):
        pt0 = ProofTerm("imp_disj", Implies(args[0].arg, args[0].arg))
        pt1 = pt0.on_prop(conv.rewr_conv("disj_conv_imp", sym=True))
        return pt1

@register_macro("verit_not_equiv1")
class VeriTNotEquiv1(Macro):
    """Prove ~(p1 <--> p2) --> p1 | p2"""
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def eval(self, args, prevs):
        pt = prevs[0]
        p1, p2 = args
        pt_p1, pt_p2 = pt.prop.arg.arg1, pt.prop.arg.arg
        if p1 == pt_p1 and p2 == pt_p2:
            return Thm(pt.hyps, Or(p1, p2))
        else:
            raise NotImplementedError
    
    def get_proof_term(self, args, prevs):
        pt = prevs[0]
        return logic.apply_theorem("not_equiv1", pt)

@register_macro("verit_not_equiv2")
class VeriTNotEquiv1(Macro):
    """Prove ~(p1 <--> p2) --> ~p1 | ~p2"""
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def eval(self, args, prevs):
        pt = prevs[0]
        p1, p2 = args
        pt_p1, pt_p2 = pt.prop.arg.arg1, pt.prop.arg.arg
        if p1.arg == pt_p1 and p2.arg == pt_p2:
            return Thm(pt.hyps, Or(p1, p2))
        else:
            raise NotImplementedError
    
    def get_proof_term(self, args, prevs):
        pt = prevs[0]
        return logic.apply_theorem("not_equiv2", pt)


@register_macro("verit_equiv1")
class Equiv1Macro(Macro):
    """Prove (p1 <--> p2) --> (~p1 | p2)"""
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None
    
    def eval(self, args, prevs):
        pt = prevs[0]
        p1, p2 = pt.prop.args
        if Not(p1) == args[0] and p2 == args[1]:
            return Thm(pt.hyps, Or(*args))
        else:
            raise NotImplementedError
    def get_proof_term(self, args, prevs):
        pt = prevs[0]
        return logic.apply_theorem("equiv1", pt)

@register_macro("verit_equiv2")
class Equiv1Macro(Macro):
    """Prove (p1 <--> p2) --> (p1 | ~p2)"""
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None
    
    def eval(self, args, prevs):
        pt = prevs[0]
        p1, p2 = pt.prop.args
        if p1 == args[0] and Not(p2) == args[1]:
            return Thm(pt.hyps, Or(*args))
        else:
            raise NotImplementedError
    def get_proof_term(self, args, prevs):
        pt = prevs[0]
        return logic.apply_theorem("equiv2", pt)


@register_macro("verit_or_neg")
class VeriTOrNeg(Macro):
    """Prove (p1 | ... | pn) | ~pk"""
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None
    def eval(self, args, prevs):
        disj = args[0]
        neg_tm = args[1]
        if neg_tm.arg in expand_disj(disj):
            return Thm([], Or(*args))
        else:
            raise NotImplementedError

    def get_proof_term(self, args, prevs):
        pt0 = ProofTerm.reflexive(Or(*args))
        pt1 = pt0.on_rhs(conv.rewr_conv("disj_comm"), conv.rewr_conv("disj_conv_imp"))
        pt2 = ProofTerm("imp_disj", pt1.prop.rhs)
        pt3 = pt1.symmetric().equal_elim(pt2)
        return pt3

@register_macro("verit_eq_reflexive")
class EqReflexive(Macro):
    """Prove x = x."""
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None
    def eval(self, args, prevs=None):
        goal = args[0]
        if goal.is_equals() and goal.lhs == goal.rhs:
            return Thm([], goal)
        else:
            raise NotImplementedError

    def get_proof_term(self, args, prevs=None):
        goal = args[0]
        return ProofTerm.reflexive(goal.lhs)


@register_macro("verit_eq_transitive")
class EqTransitive(Macro):
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def eval(self, args, prevs=None):
        head, tail = args[0], args[-2]
        if args[-1].lhs == head.arg.lhs and args[-1].rhs == tail.arg.rhs:
            return Thm([], Or(*args))
        elif args[-1].lhs == head.arg.lhs and args[-1].rhs == tail.arg.lhs:
            return Thm([], Or(*args))
        else:
            raise NotImplementedError

    def get_proof_term(self, args, prevs=None):
        disjs = [tm.arg for tm in args[:-1]]
        disj_pts = [ProofTerm.assume(disj) for disj in disjs]
        pt0 = disj_pts[0]
        for pt1 in disj_pts[1:]: # bugs in verit
            if pt1.lhs == pt0.rhs:
                pt0 = pt0.transitive(pt1)
            elif pt1.lhs == pt0.lhs:
                pt0 = pt0.symmetric().transitive(pt1)
            elif pt1.rhs == pt0.lhs:
                pt0 = pt0.symmetric().transitive(pt1.symmetric())
            elif pt1.rhs == pt0.rhs:
                pt0 = pt0.transitive(pt1.symmetric())
            
            else:
                raise NotImplementedError(str(pt0.prop), str(pt1.prop))
        
        if pt0.symmetric().prop == args[-1]:
            pt0 = pt0.symmetric() 

        assert pt0.prop == args[-1], "%s \n %s" % (str(pt0.prop), str(args[-1]))
        pt1 = pt0
        for disj in reversed(disjs):
            pt1 = pt1.implies_intr(disj).on_prop(conv.rewr_conv("imp_disj_eq"))
        return pt1

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
    
    def get_proof_term(self, args, prevs=None):
        # goal = Or(*goal)
        # elems = goal.strip_disj()
        elems = list(args)
        preds, concl = elems[:-1], elems[-1]
        args_pair = [(i, j) for i, j in zip(concl.lhs.strip_comb()[1], concl.rhs.strip_comb()[1])]
        # preds_pair = [(i.arg.lhs, i.arg.rhs) for i in preds]
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
        return ProofTerm("imp_to_or", elems[:-1]+[Or(*elems)], prevs=[pt1])

@register_macro("verit_equiv_pos1")
class EquivPos1(Macro):
    """Prove ~(p1 <--> p2) | p1 | ~p2"""
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def eval(self, args, prevs=None):
        arg1, arg2, arg3 = args
        eq_tm = arg1.arg
        if eq_tm.arg1 == arg2 and Not(eq_tm.arg) == arg3:
            return Thm([], Or(*args))
        else:
            raise NotImplementedError
    
    def get_proof_term(self, args, prevs):
        return logic.apply_theorem("equiv_pos1", concl = Or(*args))

@register_macro("verit_equiv_pos2")
class EquivPos2(Macro):
    """Prove ~(p1 <--> p2) | ~p1 | p2"""
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def eval(self, args, prevs=None):
        arg1, arg2, arg3 = args
        eq_tm = arg1.arg
        if Not(eq_tm.arg1) == arg2 and eq_tm.arg == arg3:
            return Thm([], Or(*args))
        else:
            raise NotImplementedError
    
    def get_proof_term(self, args, prevs):
        return logic.apply_theorem("equiv_pos2", concl = Or(*args))

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
                raise NotImplementedError(str(pt0.prop), str(pt1.prop))
        
        if pt0.symmetric().prop == elems[-1]:
            pt0 = pt0.symmetric() 

        assert pt0.prop == elems[-1], "%s \n %s" % (str(pt0.prop), str(goal.strip_disj()[-1]))
        
        return ProofTerm("imp_to_or", elems[:-1]+[goal], prevs=[pt0])


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
    
@register_macro("verit_and_neg")
class AndNegMacro(Macro):
    """Prove ~(p1 & p2 & ... & pn) | ~p1 | ... | ~pn"""
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def eval(self, args, prevs=None):
        conj = args[0]
        neg_disjs = args[1:]
        disjs = [nd.arg for nd in neg_disjs]
        if tuple(conj.strip_conj()) == tuple(disjs):
            return Thm([], Or(*args))
        else:
            raise NotImplementedError

    # def get_proof_term(self, args, prevs):
        

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
            conv.top_conv(real.real_simplex_form()),
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
            pt_result = int_th_lemma_1_simplex(refl_pt.rhs)
        except:
            pt_result = int_th_lemma_1_omega(refl_pt.rhs)
        return refl_pt.symmetric().equal_elim(pt_result)
        

    def analyze_type(self, args):
        tm = args.arg1.arg1 if args.arg1.is_compares() else args.arg1.arg.arg1
        return tm.get_type()

    def get_proof_term(self, args, prevs=None):
        T = self.analyze_type(args)
        if T == IntType:
            return self.int_solver(args)
        else:
            return self.real_solver(args)