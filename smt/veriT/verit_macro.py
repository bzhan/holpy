"""
Macros used in the proof reconstruction.
"""

from kernel.macro import Macro
from kernel.theory import register_macro
from kernel.proofterm import ProofTerm, Thm
from kernel.term import Term, Not, And, Or, Eq, Implies, false, true, IntType, RealType, BoolType, Int
from prover.proofrec import int_th_lemma_1_omega, int_th_lemma_1_simplex, real_th_lemma
from logic import conv, logic
from data import integer, real, proplogic
from data import list as hol_list
import functools
from kernel import term_ord


class VeriTException(Exception):
    def __init__(self, rule_name, message):
        self.rule_name = rule_name
        self.message = message

    def __str__(self):
        return "%s: %s" % (self.rule_name, self.message)


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

def strip_disj_n(tm, n):
    """Strip the disjunction into n parts."""
    if n == 1:
        return [tm]
    assert tm.is_disj(), "strip_disj_n: not enough terms"
    return [tm.arg1] + strip_disj_n(tm.arg, n-1)

def strip_conj_n(tm, n):
    """Strip the conjunction into n parts."""
    if n == 1:
        return [tm]
    assert tm.is_conj(), "strip_disj_n: not enough terms"
    return [tm.arg1] + strip_conj_n(tm.arg, n-1)

def try_resolve(prop1, prop2):
    """Try to resolve two propositions."""
    for i in range(len(prop1)):
        for j in range(len(prop2)):
            if prop2[j] == Not(prop1[i]):
                return 'left', i, j
            if prop1[i] == Not(prop2[j]):
                return 'right', i, j                
    return None

def resolve_order(props):
    """Given a list of props, each of which is a clause, find an optimal
    order of performing resolution on these propositions.
    
    """
    # List of propositions remaining to be resolved
    id_remain = list(range(len(props)))

    # List of resolution steps
    resolves = []

    while len(id_remain) > 1:
        # Find resolution among all possible pairs.
        resolve = None
        for i in range(len(id_remain)):
            for j in range(i+1, len(id_remain)):
                id1 = id_remain[i]
                id2 = id_remain[j]
                res = try_resolve(props[id1], props[id2])
                if res:
                    if res[0] == 'left':
                        resolve = (id1, id2, res[1], res[2])
                    else:
                        resolve = (id2, id1, res[2], res[1])
                    break
            if resolve:
                break

        if resolve is None:
            # Sometimes resolution solver may have bugs, such as resolving one proof term twice
            # Example: QF_UFLIA\\wisas\\xs_5_5.smt2 step t213
            # raise VeriTException("th_resolution", "cannot find resolution")
            break

        # Perform this resolution
        id1, id2, t1, t2 = resolve
        prop1, prop2 = props[id1], props[id2]
        if t1 == -1:
            res_list = prop2[:t2] + prop2[t2+1:]
        else:
            assert t1 != -1 and t2 != -1
            res_list = prop1[:t1] + prop1[t1+1:]
            for t in prop2[:t2] + prop2[t2+1:]:
                if t not in res_list:
                    res_list.append(t)
        id_remain.remove(id2)
        props[id1] = res_list
        resolves.append(resolve + (res_list,))

    return resolves, props[id_remain[0]]

@register_macro("verit_th_resolution")
class ThResolutionMacro(Macro):
    """Return the resolution result of multiple proof terms."""
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None
        
    def eval(self, args, prevs):
        cl, cl_sizes = args
        assert len(cl_sizes) == len(prevs)
        prems = []
        for cl_size, prev in zip(cl_sizes, prevs):
            prems.append(strip_disj_n(prev.prop, cl_size))

        _, cl_concl = resolve_order(prems)
        if set(cl_concl) == set(cl):
            return Thm([hyp for pt in prevs for hyp in pt.hyps], Or(*cl))
        else:
            raise VeriTException("th_resolution", "unexpected conclusion")

    def get_proof_term(self, args, prevs):
        cl, cl_sizes = args
        assert len(cl_sizes) == len(prevs)
        prems = []
        for cl_size, prev in zip(cl_sizes, prevs):
            prems.append(strip_disj_n(prev.prop, cl_size))

        # Make a copy of prems, as it needs to be used later
        resolves, _ = resolve_order(list(prems))

        # Use a list to store intermediate resolvants.
        prevs = list(prevs)

        for i, res_step in enumerate(resolves):
            id1, id2, t1, t2, res_list = res_step
            pt1, pt2 = prevs[id1], prevs[id2]
            prem1, prem2 = prems[id1], prems[id2]

            # First, move t1 and t2 to the left
            if t1 > 0:
                disj1 = [prem1[t1]] + prem1[:t1] + prem1[t1+1:]
                eq_pt1 = logic.imp_disj_iff(Eq(pt1.prop, Or(*disj1)))
                pt1 = eq_pt1.equal_elim(pt1)
            if t2 > 0:
                disj2 = [prem2[t2]] + prem2[:t2] + prem2[t2+1:]
                eq_pt2 = logic.imp_disj_iff(Eq(pt2.prop, Or(*disj2)))
                pt2 = eq_pt2.equal_elim(pt2)

            # Apply the resolution theorem
            if len(prem1) > 1 and len(prem2) > 1:
                pt = logic.apply_theorem('resolution', pt1, pt2)
            elif len(prem1) > 1 and len(prem2) == 1:
                pt = logic.apply_theorem('resolution_left', pt1, pt2)
            elif len(prem1) == 1 and len(prem2) > 1:
                pt = logic.apply_theorem('resolution_right', pt1, pt2)
            else:
                pt = logic.apply_theorem('negE', pt2, pt1)

            # Reorder the result if necessary
            if i == len(resolves) - 1:
                res = Or(*cl)
            else:
                res = Or(*res_list)
            if pt.prop != res:
                eq_pt = logic.imp_disj_iff(Eq(pt.prop, res))
                pt = eq_pt.equal_elim(pt)
            
            prems[id1] = res_list
            prevs[id1] = pt
        
        # Return the result of last step of resolution
        return pt


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
        if len(args) < 3:
            raise VeriTException("eq_transitive", "must have at least three disjuncts")
        prems = []
        for arg in args[:-1]:
            if not arg.is_not() or not arg.arg.is_equals():
                raise VeriTException("eq_transitive", "all but last disjunct must be a negation")
            prems.append(arg.arg)

        cur_eq = prems[0]
        for prem in prems[1:]:
            if cur_eq.lhs == prem.lhs:
                cur_eq = Eq(cur_eq.rhs, prem.rhs)
            elif cur_eq.lhs == prem.rhs:
                cur_eq = Eq(cur_eq.rhs, prem.lhs)
            elif cur_eq.rhs == prem.lhs:
                cur_eq = Eq(cur_eq.lhs, prem.rhs)
            elif cur_eq.rhs == prem.rhs:
                cur_eq = Eq(cur_eq.lhs, prem.lhs)
            else:
                raise VeriTException("eq_transitive", "cannot connect equalities")
        
        if not args[-1].is_equals():
            raise VeriTException("eq_transitive", "last disjunct must be an equality")

        if cur_eq == args[-1]:
            return Thm([], Or(*args))
        elif cur_eq.lhs == args[-1].rhs and cur_eq.rhs == args[-1].lhs:
            return Thm([], Or(*args))
        else:
            raise VeriTException("eq_transitive", "unexpected equality")

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
        disjs = [arg.arg for arg in args]
        pt0 = prevs[0]
        pt1 = functools.reduce(lambda x, y: x.implies_intr(y).on_prop(conv.rewr_conv("imp_disj_eq")), reversed(disjs), pt0)
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
        goal = Or(*goal)
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


@register_macro("verit_distinct_elim")
class DistinctElimMacro(Macro):
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def eval(self, args, prevs):
        if len(args) != 1:
            raise VeriTException("distinct_elim", "clause must have a single term")
        arg = args[0]
        if not arg.is_equals():
            raise VeriTException("distinct_elim", "goal must be an equality")
        lhs, rhs = arg.lhs, arg.rhs
        if not lhs.is_comb("distinct", 1):
            raise VeriTException("distinct_elim", "lhs is not a distinct predicate")

        distinct_ts = hol_list.dest_literal_list(lhs.arg)

        # Form conjunction of pairs in ts
        conjs = []
        for i in range(len(distinct_ts)):
            for j in range(i+1, len(distinct_ts)):
                conjs.append(Not(Eq(distinct_ts[i], distinct_ts[j])))
        expected_rhs = And(*conjs)
        if rhs != expected_rhs:
            raise VeriTException("distinct_elim", "incorrect rhs")

        return Thm([], arg)
    
    def get_proof_term(self, goal, prevs=None):
        raise NotImplementedError


@register_macro("verit_and")
class AndMacro(Macro):
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def eval(self, args, prevs):
        if len(args) != 1:
            raise VeriTException("and", "clause must have a single term")
        if len(prevs) != 1:
            raise VeriTException("and", "must have a single premise")

        prem = prevs[0].prop
        prem_conjs = prem.strip_conj()
        arg = args[0]
        if arg not in prem_conjs:
            raise VeriTException("and", "goal not found in premise")
        
        return Thm(prevs[0].hyps, arg)

    def get_proof_term(self, goal, prevs=None):
        raise NotImplementedError


@register_macro("verit_or")
class OrMacro(Macro):
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def eval(self, args, prevs):
        if len(prevs) != 1:
            raise VeriTException("or", "must have a single premise")

        prev = prevs[0].prop
        prev_disjs = prev.strip_disj()
        if tuple(prev_disjs) != args:
            raise VeriTException("or", "incorrect conclusion")
        return Thm(prevs[0].hyps, Or(*args))

@register_macro("verit_false")
class FalseMacro(Macro):
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def eval(self, args, prevs=None):
        if len(args) != 1:
            raise VeriTException("false", "clause must have a term")
        arg = args[0]
        if arg != Not(false):
            raise VeriTException("false", "goal must be ~false")
        return Thm([], arg)

@register_macro("verit_not_simplify")
class NotSimplifyMacro(Macro):
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def eval(self, args, prevs=None):
        if len(args) != 1:
            raise VeriTException("not_simplify", "clause must have a term")
        arg = args[0]
        if not arg.is_equals():
            raise VeriTException("not_simplify", "goal must be an equality")
        lhs, rhs = arg.lhs, arg.rhs

        if not lhs.is_not():
            raise VeriTException("not_simplify", "lhs should be a negation")

        if lhs == Not(false) and rhs == true:
            return Thm([], arg)
        elif lhs == Not(true) and rhs == false:
            return Thm([], arg)
        elif lhs.is_not():
            if not lhs == Not(Not(rhs)):
                raise VeriTException("not_simplify", "lhs should be equal to the double negation of rhs")
            else:
                return Thm([], arg)
        else:
            raise VeriTException("not_simplify", "negated term should among true, false or negation")

@register_macro("verit_eq_simplify")
class NotSimplifyMacro(Macro):
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def eval(self, args, prevs=None):
        if len(args) != 1:
            raise VeriTException("eq_simplify", "clause must have a term")
        arg = args[0]
        if not arg.is_equals():
            raise VeriTException("eq_simplify", "goal must be an equality")
        lhs, rhs = arg.lhs, arg.rhs

        if lhs.is_equals():
            if lhs.lhs == lhs.rhs and rhs == true:
                return Thm([], arg)
            elif lhs.rhs != lhs.rhs and rhs == false:
                return Thm([], arg)
            else:
                raise VeriTException("eq_simplify", "rhs doesn't obey eq_simplify rule")
        elif lhs.is_not():
            if not lhs.arg.is_equals() or lhs.arg.lhs == lhs.arg.rhs:
                raise VeriTException("eq_simplify", "lhs should be an inequality.")
            if rhs == false:
                return Thm([], arg)
            else:
                raise VeriTException("eq_simplify", "rhs doesn't obey eq_simplify rule")
        else:
            raise VeriTException("eq_simplify", "lhs should be either an equality or an inequality")

@register_macro("verit_trans")
class TransMacro(Macro):
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def eval(self, args, prevs):
        if len(args) != 1:
            raise VeriTException("trans", "trans must have a term")
        arg = args[0]
        if not arg.is_equals():
            raise VeriTException("trans", "goal must be an equality")

        if len(prevs) < 2:
             raise VeriTException("trans", "must have at least two proof terms")
        
        if not all(pt.prop.is_equals() for pt in prevs):
            raise VeriTException("trans", "all props should be equality")        

        cur_eq = prevs[0].prop
        for prev in prevs[1:]:
            prev_prop = prev.prop
            if cur_eq.rhs == prev_prop.lhs:
                cur_eq = Eq(cur_eq.lhs, prev_prop.rhs)
            else:
                raise VeriTException("trans", "cannot connect equalities")
        
        if cur_eq == arg:
            return Thm([], cur_eq)
        else:
            raise VeriTException("trans", "unexpected equality")

@register_macro("verit_cong")
class CongMacro(Macro):
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def eval(self, args, prevs): # contain bugs
        if len(args) != 1:
            raise VeriTException("cong", "goal should be a single term.")
        goal = args[0]
        if not goal.is_equals():
            raise VeriTException("cong", "goal should be an equality")
        
        lhs, rhs = goal.lhs, goal.rhs
        if lhs.head != rhs.head:
            raise VeriTException("cong", "head should be same")
        
        # Treat | and & as n-ary operators when 
        # the number of premises are larger than 2
        if lhs.is_conj():
            size = lhs.arity
            l_args, r_args = strip_conj_n(lhs, size), strip_conj_n(rhs,size)
        elif lhs.is_disj():
            size = lhs.arity
            l_args, r_args = strip_disj_n(lhs, size), strip_disj_n(rhs, size)
        elif lhs.is_comb("distinct"):
            l_args, r_args = hol_list.dest_literal_list(lhs.arg), hol_list.dest_literal_list(rhs.arg)
        else:
            l_args, r_args = lhs.args, rhs.args
        h, i = lhs.head, 0
        subst_args = []
        for arg in l_args:
            if i >= len(prevs):
                subst_args.append(arg)
            elif prevs[i].lhs == arg:
                subst_args.append(prevs[i].rhs)
                i += 1
            elif prevs[i].rhs == arg:
                subst_args.append(prevs[i].lhs)
                i += 1
            else:
                subst_args.append(arg)
        if subst_args == r_args:
            return Thm([], goal)
        elif lhs.is_equals() and Eq(subst_args[0], subst_args[1]) == Eq(rhs.rhs, rhs.lhs):
            return Thm([], goal)
        else:
            raise VeriTException("cong", "unexpected result")

@register_macro("verit_refl")
class ReflMacro(Macro):
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def eval(self, args, prevs=None):
        if len(args) != 2:
            raise VeriTException("refl", "args should contain two terms")
        goal, contexts = args
        if not goal.is_equals():
            raise VeriTException("refl", "goal should be an equality")
        if not isinstance(contexts, dict):
            raise VeriTException("refl", "context should be a mapping")
        if str(goal.lhs) in contexts and contexts[str(goal.lhs)] == goal.rhs:
            return Thm([], goal)
        if str(goal.rhs) in contexts and contexts[str(goal.rhs)] == goal.lhs:
            return Thm([], goal)
        else:
            raise VeriTException("refl", "either lhs and rhs of goal is not in ctx")

def expand_to_ite(t):
    if t.is_comb():
        # First check whether one of the arguments is a non-constant boolean formula
        for i, arg in enumerate(t.args):
            if arg.get_type() == BoolType and arg != true and arg != false:
                arg_true = t.args[:i] + [true] + t.args[i+1:]
                arg_false = t.args[:i] + [false] + t.args[i+1:]
                return logic.mk_if(arg, expand_to_ite(t.head(*arg_true)),
                                   expand_to_ite(t.head(*arg_false)))
        # Now it is clear that none of the arguments are non-constant booleans
        expand_args = [expand_to_ite(arg) for arg in t.args]
        return t.head(*expand_args)
    else:
        return t

@register_macro("verit_bfun_elim")
class BFunElimMacro(Macro):
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def eval(self, args, prevs):
        if len(args) != 1:
            raise VeriTException("bfun_elim", "clause must have a single term")
        if len(prevs) != 1:
            raise VeriTException("bfun_elim", "must have a single premise")

        arg = args[0]
        prev = prevs[0].prop

        # Second step: replace every function application with argument of
        # boolean type with an if-then-else expression.
        expected_arg = expand_to_ite(prev)
        if expected_arg != arg:
            print("Expected:", expected_arg)
            print("Actual:", arg)
            raise VeriTException("bfun_elim", "unexpected goal")

        return Thm(prevs[0].hyps, arg)


def collect_ite_intro(t):
    if logic.is_if(t):
        P, x, y = t.args
        ite_eq = logic.mk_if(P, Eq(x, t), Eq(y, t))
        return [ite_eq] + collect_ite_intro(x) + collect_ite_intro(y)
    elif t.is_comb():
        res = []
        for arg in t.args:
            res.extend(collect_ite_intro(arg))
        return res
    else:
        return []

@register_macro("verit_ite_intro")
class ITEIntroMacro(Macro):
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def eval(self, args, prevs):
        if len(args) != 1:
            raise VeriTException("ite_intro", "clause must have a single term")
        arg = args[0]
        if not arg.is_equals():
            raise VeriTException("ite_intro", "goal is not an equality")

        lhs, rhs = arg.lhs, arg.rhs
        ite_intros = collect_ite_intro(lhs)
        ite_intros_distinct = []
        for ite in ite_intros:
            if ite not in ite_intros_distinct:
                ite_intros_distinct.append(ite)
        expected_ites = rhs.strip_conj()[1:]

        if len(ite_intros_distinct) != len(expected_ites):
            raise VeriTException("let_intro", "unexpected number of ites")

        # Should consider symmetry of equality
        for actual_ite, expected_ite in zip(ite_intros_distinct, expected_ites):
            P, x, y = actual_ite.args
            Q, a, b = expected_ite.args
            if P != Q:
                raise VeriTException("let_intro", "unexpected condition")
            if x == a and y == b:
                continue
            elif Eq(x.rhs, x.lhs) == a and y == b:
                continue
            elif x == a and Eq(y.rhs, y.lhs) == b:
                continue
            elif Eq(x.rhs, x.lhs) and Eq(y.rhs, y.lhs) == b:
                continue
            else:
                raise VeriTException("let_intro", "unexpected ite")

        expected_rhs = And(lhs, *ite_intros_distinct)
        if not compare_sym_tm(expected_rhs, rhs):
            print("Expected:", expected_rhs)
            print("Actual:", rhs)
            raise VeriTException("ite_intro", "unexpected goal")
        return Thm([], arg)


@register_macro("verit_ite1")
class ITE1(Macro):
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def eval(self, args, prevs):
        if len(args) != 2:
            raise VeriTException("ite1", "clause must have two terms")
        if len(prevs) != 1:
            raise VeriTException("ite1", "must have a single premise")

        arg1, arg2 = args
        prev = prevs[0].prop
        if not logic.is_if(prev):
            raise VeriTException("ite1", "premise must be in if-then-else form")
        if arg1 != prev.args[0] or arg2 != prev.args[2]:
            raise VeriTException("ite1", "unexpected goal")
        return Thm(prevs[0].hyps, Or(arg1, arg2))

@register_macro("verit_ite2")
class ITE2(Macro):
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def eval(self, args, prevs):
        if len(args) != 2:
            raise VeriTException("ite2", "clause must have two terms")
        if len(prevs) != 1:
            raise VeriTException("ite2", "must have a single premise")

        arg1, arg2 = args
        prev = prevs[0].prop
        if not logic.is_if(prev):
            raise VeriTException("ite2", "premise must be in if-then-else form")
        if arg1 != Not(prev.args[0]) or arg2 != prev.args[1]:
            raise VeriTException("ite2", "unexpected goal")
        return Thm(prevs[0].hyps, Or(arg1, arg2))

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
        neg_conj_args = tuple(Not(arg) for arg in conj.strip_conj())
        if neg_disjs != neg_conj_args:
            raise VeriTException("Unexpected goal")
        return Thm([], Or(*args))

    # def get_proof_term(self, args, prevs):

@register_macro("verit_contraction")
class ContractionMacro(Macro):
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def eval(self, args, prevs=None):
        if len(prevs) != 1:
            raise VeriTException("contraction", "must have a single premise")

        prev = prevs[0].prop
        prev_disjs = prev.strip_disj()
        distinct_disjs = []
        for disj in prev_disjs:
            if disj not in distinct_disjs:
                distinct_disjs.append(disj)
        if tuple(distinct_disjs) != args:
            raise VeriTException("contraction", "unexpected goal")
        return Thm(prevs[0].hyps, Or(*args))

def let_substitute(tm, ctx):
    """Substitue all variables in ctx into concrete terms, 
    and move the all variables at lhs to rhs (sort).
    """
    if tm.is_var():
        if str(tm) in ctx:
            return ctx[str(tm)]
        else:
            return tm
    elif tm.is_comb():
        if tm.is_conj():
            conjs = [let_substitute(conj, ctx) for conj in tm.strip_conj()]
            return And(*conjs)
        elif tm.is_disj():
            disjs = [let_substitute(disj, ctx) for disj in tm.strip_disj()]
            return Or(*disjs)
        else:
            args = [let_substitute(arg, ctx) for arg in tm.args]
            return tm.head(*args)
    elif tm.is_const():
        return tm
    else:
        raise NotImplementedError

def compare_sym_tm(tm1, tm2):
    """Compare tm1 and tm2 with the symmetry property."""
    if tm1.head != tm2.head:
        return False
    elif tm1.is_equals():
        if tm1.lhs == tm2.lhs and tm1.rhs == tm2.rhs:
            return True
        elif tm1.rhs == tm2.lhs and tm1.lhs == tm2.rhs:
            return True
        else:
            return False
    else:
        for l_arg, r_arg in zip(tm1.args, tm2.args):
            if not compare_sym_tm(l_arg, r_arg):
                return False
        return True

@register_macro("verit_let")
class LetMacro(Macro):
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def eval(self, args, prevs):
        goal, ctx = args
        beta_lhs = goal.lhs
        if compare_sym_tm(let_substitute(beta_lhs, ctx), goal.rhs):
            return Thm([], goal)
        else:
            raise VeriTException("let", "Unexpected result")

def flatten_prop(tm):
    """Unfold a nested proposition formula."""
    if not tm.is_conj() and not tm.is_disj() and not tm.is_not():
        return tm
    elif tm.is_conj():
        conjs = logic.strip_conj(tm)
        flat_conjs = [flatten_prop(t) for t in conjs]
        distinct_conjs = []
        for f in flat_conjs:
            if f not in distinct_conjs:
                distinct_conjs.append(f)
        return And(*term_ord.sorted_terms(distinct_conjs))
    elif tm.is_disj():
        disjs = logic.strip_disj(tm)
        flat_disjs = [flatten_prop(t) for t in disjs]
        distinct_disjs = []
        for f in flat_disjs:
            if f not in distinct_disjs:
                distinct_disjs.append(f)
        return Or(*term_ord.sorted_terms(distinct_disjs))
    elif tm.is_not():
        return Not(flatten_prop(tm.arg))
    else:
        raise NotImplementedError
        

@register_macro("verit_ac_simp")
class ACSimpMacro(Macro):
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def eval(self, args, prevs=None):
        if len(args) != 1:
            raise VeriTException("ac_simp", "must have a single goal")
        goal = args[0]
        if not goal.is_equals():
            raise VeriTException("ac_simp", "goal should be an equality")

        lhs, rhs = goal.lhs, goal.rhs
        if not lhs.is_conj() and not lhs.is_disj():
            raise VeriTException("ac_simp", "lhs and rhs are not both disjunction or conjunction.")
        rhs_flat = flatten_prop(rhs)
        lhs_flat = flatten_prop(lhs)
        if lhs_flat == rhs_flat:
            return Thm([], goal)
        else:
            raise VeriTException("ac_simp", "unexpected result")
        
@register_macro("verit_and_simplify")
class AndSimplifyMacro(Macro):
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def eval(self, args, prevs=None):
        if len(args) != 1:
            raise VeriTException("and_simplify", "must have a single goal")
        goal = args[0]
        if not goal.is_equals():
            raise VeriTException("and_simplify", "goal should be an equality")

        lhs_conjs = goal.lhs.strip_conj()
        # p_1 & .... & p_n <--> false if ?i, j. p_i = ~p_j
        for i in range(len(lhs_conjs)):
            for j in range(i+1, len(lhs_conjs)):
                if Not(lhs_conjs[i]) == lhs_conjs[j] or lhs_conjs[i] == Not(lhs_conjs[j]):
                    if goal.rhs == false:
                        return Thm([], goal)
                    else:
                        raise VeriTException("and_simplify", "unexpected rhs")
        elim_true_conj = []
        for conj in lhs_conjs:
            if conj != true:
                elim_true_conj.append(conj)
        if And(*elim_true_conj) == goal.rhs:
            return Thm([], goal)
        if false in lhs_conjs:
            if goal.rhs == false:
                return Thm([], goal)
            else:
                raise VeriTException("and_simplify", "unexpected rhs")
        raise VeriTException("and_simplify", "haven't implemented")

@register_macro("verit_or_simplify")
class OrSimplifyMacro(Macro):
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def eval(self, args, prevs=None):
        if len(args) != 1:
            raise VeriTException("or_simplify", "must have a single goal")
        goal = args[0]
        if not goal.is_equals():
            raise VeriTException("or_simplify", "goal should be an equality")

        lhs_disjs = goal.lhs.strip_disj()
        # p_1 & .... & p_n <--> false if ?i, j. p_i = ~p_j
        for i in range(len(lhs_disjs)):
            for j in range(i+1, len(lhs_disjs)):
                if Not(lhs_disjs[i]) == lhs_disjs[j] or lhs_disjs[i] == Not(lhs_disjs[j]):
                    if goal.rhs == true:
                        return Thm([], goal)
                    else:
                        raise VeriTException("or_simplify", "unexpected rhs")
        
        # delete redundant false
        elim_true_disj = []
        for disj in lhs_disjs:
            if disj != false:
                elim_true_disj.append(disj)
        if Or(*elim_true_disj) == goal.rhs:
            return Thm([], goal)
        if true in lhs_disjs:
            if goal.rhs == true:
                return Thm([], goal)
            else:
                raise VeriTException("or_simplify", "unexpected rhs")
        raise VeriTException("or_simplify", "haven't implemented")


@register_macro("verit_bool_simplify")
class BoolSimplifyMacro(Macro):
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def eval(self, args, prevs=None):
        if len(args) != 1:
            raise VeriTException("bool_simplify", "args should only contain one element")
        
        goal = args[0]
        if not goal.is_equals():
            raise VeriTException("bool_simplify", "goal should be an equality")
        lhs, rhs = goal.lhs, goal.rhs
        # case 1: ~(p --> q) <--> (p and ~q)
        if lhs.is_not() and lhs.arg.is_implies() and rhs.is_conj():
            l_p, l_q = lhs.arg.args
            r_p, r_q = rhs.args
            if l_p == r_p and Not(l_q) == r_q:
                return Thm([], goal)
            else:
                raise VeriTException("bool_simplify", "goal cannot match  ~(p --> q) <--> (p and ~q)")
        # case 2: ~(p | q) <--> (~p & ~q)
        elif lhs.is_not() and lhs.arg.is_disj() and rhs.is_conj():
            l_p, l_q = lhs.arg.args
            r_p, r_q = rhs.args
            if Not(l_p) == r_p and Not(l_q) == r_q:
                return Thm([], goal)
            else:
                raise VeriTException("bool_simplify", "goal cannot match ~(p | q) <--> (~p & ~q)")
        # case 2: ~(p & q) <--> (~p | ~q)
        elif lhs.is_not() and lhs.arg.is_conj() and rhs.is_disj():
            l_p, l_q = lhs.arg.args
            r_p, r_q = rhs.args
            if Not(l_p) == r_p and Not(l_q) == r_q:
                return Thm([], goal)
            else:
                raise VeriTException("bool_simplify", "goal cannot match ~(p | q) <--> (~p & ~q)")
        else:
            raise VeriTException("bool_simplify", "implementation is incomplete")

@register_macro("verit_la_disequality")
class LADisequalityMacro(Macro):
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def eval(self, args, prevs=None):
        if len(args) != 1:
            raise VeriTException("verit_la_disequality", "args should only contain one element")
        
        goal = args[0]
        if not goal.is_disj():
            raise VeriTException("verit_la_disequality", "goal should be a disjunction")
        
        eq, neg_less_eq, neg_less_eq_sym = goal.strip_disj()
        if not eq.is_equals() or not neg_less_eq.is_not() or not \
            neg_less_eq.arg.is_less_eq() or not neg_less_eq_sym.is_not() or not \
                neg_less_eq_sym.arg.is_less_eq():
            raise VeriTException("verit_la_disequality", "can't match goal's shape")
        
        eq_t1, eq_t2 = eq.args
        neg_less_eq_t1, neg_less_eq_t2 = neg_less_eq.arg.args
        neg_less_eq_sym_t1, neg_less_eq_sym_t2 = neg_less_eq_sym.arg.args

        if eq_t1 == neg_less_eq_t1 and eq_t1 == neg_less_eq_sym_t2 and \
                eq_t2 == neg_less_eq_t2 and eq_t2 == neg_less_eq_sym_t1:
            return Thm([], goal)
        else:
            raise VeriTException("verit_la_disequality", "can't match goal")


def split_num_expr(t):
    summands = integer.strip_plus_full(t)
    nums, non_nums = [Int(0)], []
    for s in summands:
        if s.is_number():
            nums.append(s)
        else:
            non_nums.append(s)

    const = integer.int_eval(sum(nums[1:], nums[0]))
    if len(non_nums) == 0: # t is a constant
        return Int(const)
    
    non_nums_sum = sum(non_nums[1:], non_nums[0])
    if const == 0:
        return non_nums_sum
    else:
        return Int(const) + non_nums_sum

@register_macro("verit_sum_simplify")
class SumSimplifyMacro(Macro):
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def eval(self, args, prevs=None):
        if len(args) != 1:
            raise VeriTException("sum_simplify", "args should only contain one element")
        
        goal = args[0]
        if not goal.is_equals():
            raise VeriTException("sum_simplify", "goal should be an equality")
        
        lhs, rhs = goal.lhs, goal.rhs

        lhs_simp = split_num_expr(lhs)
        if lhs_simp == rhs:
            return Thm([], goal)
        elif lhs_simp == split_num_expr(rhs):
            """Verit bugs: QF_UFLIA\\wisas\\xs_5_10.smt2 step t27 rhs side has zero on the right."""
            return Thm([], goal)
        else:
            raise VeriTException("sum_simplify", "unexpected result")

@register_macro("verit_comp_simplify")
class CompSimplifyMacro(Macro):
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def eval(self, args, prevs=None):
        if len(args) != 1:
            raise VeriTException("comp_simplify", "args should only contain one element")
        
        goal = args[0]
        if not goal.is_equals():
            raise VeriTException("comp_simplify", "goal should be an equality")
        
        lhs, rhs = goal.lhs, goal.rhs
        # Case 5: a >= b <--> b <= a 
        if lhs.is_greater_eq():
            if not rhs.is_less_eq():
                raise VeriTException("comp_simplify", "rhs should be a less_eq when lhs is greater_eq")
            l_a, l_b = lhs.args
            r_a, r_b = rhs.args
            if l_a == r_b and l_b == r_a:
                return Thm([], goal)
            else:
                raise VeriTException("comp_simplify", "can't match a >= b <--> b <= a")
        # Case 7: a > b <--> ~(a <= b)
        elif lhs.is_greater():
            if not (rhs.is_not() and rhs.arg.is_less_eq()):
                raise VeriTException("comp_simplify", "rhs should be a less_eq when lhs is greater_eq")
            l_a, l_b = lhs.args
            r_a, r_b = rhs.arg.args
            if l_a == r_a and l_b == r_b:
                return Thm([], goal)
            else:
                print("lhs", lhs, l_a, l_b)
                print("rhs", rhs, r_a, r_b)
                raise VeriTException("comp_simplify", "can't match a > b <--> ~(b <= a)")
        else:
            print("goal", goal)
            raise VeriTException("comp_simplify", "implementation is incomplete")

@register_macro("verit_ite_simplify")
class ITESimplifyMacro(Macro):
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def eval(self, args, prevs=None):
        if len(args) != 1:
            raise VeriTException("ite_simplify", "args should only contain one element")
        
        goal = args[0]
        if not goal.is_equals():
            raise VeriTException("ite_simplify", "goal should be an equality")
        
        lhs, rhs = goal.lhs, goal.rhs

        if logic.is_if(lhs) and logic.is_if(rhs):
            l_P, l_then, l_else = lhs.args
            r_P, r_then, r_else = rhs.args
            if logic.is_if(l_then): # Case 7: ite P (ite P x y) z <--> ite P x z
                l_then_P, l_then_then, _ = l_then.args
                if l_P == l_then_P and l_then_then == r_then and l_else == r_else:
                    return Thm([], goal)
                else:
                    raise VeriTException("ite_simplify", "can't match ite P (ite P x y) z <--> ite P x z")
            elif logic.is_if(l_else): # Case 8: ite P x (ite P y z) <--> ite P x z
                l_else_P, _, l_else_else = l_then.args
                if l_P == l_else_P and l_then == r_then and l_else_else == r_else:
                    return Thm([], goal)
                else:
                    raise VeriTException("ite_simplify", "can't match ite P x (ite P y z) <--> ite P x z")
            elif l_P == Not(r_P) and l_then == r_else and l_else == r_then:
                return Thm([], goal)
            else:
                raise VeriTException("ite_simplify", "can't match ite P x y <--> ite ~P y x")
        else:
            raise VeriTException("ite_simplify", "implementation is incomplete")
            

@register_macro("verit_minus_simplify")
class ITESimplifyMacro(Macro):
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def eval(self, args, prevs=None):
        if len(args) != 1:
            raise VeriTException("minus_simplify", "args should only contain one element")
        
        goal = args[0]
        if not goal.is_equals():
            raise VeriTException("minus_simplify", "goal should be an equality")
        
        lhs, rhs = goal.lhs, goal.rhs

        if not lhs.is_uminus():
            raise VeriTException("minus_simplify", "lhs should be an uminus term")
        lhs_neg_tm = lhs.arg
        if lhs_neg_tm.is_minus():
            if lhs_neg_tm.arg == rhs:
                return Thm([], goal)
            else:
                raise VeriTException("minus_simplify", "-(-lhs) != lhs")
        elif lhs_neg_tm.is_number():
            lhs_num = integer.int_eval(lhs)
            rhs_num = integer.int_eval(rhs)
            if  lhs_num == rhs_num:
                return Thm([], goal)
            else:
                raise VeriTException("minus_simplify", "lhs and rhs should be equal after evaluation")
        else:
            raise VeriTException("minus_simplify", "unexpected result")

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