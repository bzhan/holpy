"""
Macros used in the proof reconstruction.
"""

import functools
import itertools
import operator
from typing import Optional

from kernel.macro import Macro
from kernel.theory import register_macro
from kernel.proofterm import ProofTerm, Thm, refl
from kernel import term as hol_term
from kernel import type as hol_type
from kernel.term import Lambda, Term, Not, And, Or, Eq, Implies, false, true, \
    BoolType, Int, Forall, Exists, Inst, conj, disj, Var, neg, implies, plus, IntType, RealType
from logic import logic
from logic.conv import ConvException, try_conv, rewr_conv, arg_conv,\
         top_conv, arg1_conv, replace_conv, abs_conv, Conv, bottom_conv, beta_conv, beta_norm_conv
from data import integer, real
from data import list as hol_list
from kernel import term_ord
from smt.veriT import verit_conv


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
                return Thm(goal, pt0.hyps)
        raise VeriTException("not_or", "unexpected result")

    def get_proof_term(self, args, prevs):
        goal, pt0 = args[0], prevs[0]
        pt1 = pt0.on_prop(rewr_conv("de_morgan_thm2"))
        pt2 = pt1
        while pt2.prop != goal:
            pt_l = logic.apply_theorem("conjD1", pt2)
            pt_r = logic.apply_theorem("conjD2", pt2)
            if pt_l.prop == goal:
                pt2 = pt_l
                break
            pt2 = pt_r.on_prop(try_conv(rewr_conv("de_morgan_thm2")))
            
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
        disj_atoms = goal.strip_disj()
        for i, j in zip(conj_atoms, disj_atoms):
            if Not(i) != j:
                raise VeriTException("not_and", "unexpected goal: %s" % goal)

        return Thm(goal, pt0.hyps)

    def get_proof_term(self, args, prevs):
        goal, pt0 = Or(*args), prevs[0]
        pt1 = pt0.on_prop(verit_conv.deMorgan_conj_conv())
        if pt1.prop != goal:
            raise VeriTException("not_and", "unexpected goal: %s" % goal)
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
            return Thm(Or(neg_arg, pos_arg))
        else:
            raise VeriTException("not_not", "unexpected goal: %s" % Or(*args))
    
    def get_proof_term(self, args, prevs=None):
        neg_arg, pos_arg = args
        pt = logic.apply_theorem("neg_neg", concl=Or(neg_arg, pos_arg))
        if pt.prop != Or(*args):
            raise VeriTException("not_not", "unexpected goal: %s" % Or(*args))
        return pt

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

def strip_plus_n(tm, n):
    if n == 1:
        return [tm]
    return strip_plus_n(tm.arg1, n-1) + [tm.arg]

def strip_forall_n(tm, n):
    args = []
    while tm.is_forall() and n > 0:
        body = tm.arg
        v = hol_term.Var(body.var_name, body.var_T)
        args.append(v)
        tm = body.subst_bound(v)
        n -= 1
    return args, tm

def try_resolve(prop1, prop2):
    """Try to resolve two propositions."""
    for i in range(len(prop1)):
        ai, ni = prop1[i]
        for j in range(len(prop2)):
            aj, nj = prop2[j]
            if ai == aj and ni + 1 == nj:
                return 'left', i, j
            if ai == aj and ni == nj + 1:
                return 'right', i, j                
    return None

def resolve_order(props):
    """Given a list of props, each of which is a clause, find an optimal
    order of performing resolution on these propositions.
    
    """
    # List of resolution steps
    resolves = []

    # Mapping from indices to literals
    id_to_lit = dict()

    # Mapping from literal to index
    lit_to_id = dict()

    def strip_not(t):
        count = 0
        while t.is_not():
            count += 1
            t = t.arg
        return t, count

    # Find list of literals, ignoring negation. Assign each unique
    # literal to an index.
    for prop in props:
        for t in prop:
            a, _ = strip_not(t)
            if a not in lit_to_id:
                new_id = len(lit_to_id)
                lit_to_id[a] = new_id
                id_to_lit[new_id] = a
    
    def term_to_id(t):
        a, n = strip_not(t)
        return (lit_to_id[a], n)

    for i in range(len(props)):
        props[i] = [term_to_id(t) for t in props[i]]

    # List of propositions remaining to be resolved.
    # Clear repeated props that are immediately next to each other.
    id_remain = []
    for i, prop in enumerate(props):
        if i == 0 or tuple(prop) != tuple(props[i-1]):
            id_remain.append(i)

    def id_to_term(a, n):
        if n == 0:
            return id_to_lit[a]
        else:
            return Not(id_to_term(a, n - 1))

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
        resolves.append(resolve + ([id_to_term(a, n) for (a, n) in res_list],))

    return resolves, [id_to_term(a, n) for (a, n) in props[id_remain[0]]]

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

        if len(prevs) == 1 and prevs[0].prop == Not(true) and len(cl) == 0:
            return Thm(Or(*cl), *(pt.hyps for pt in prevs))

        prems = []
        for cl_size, prev in zip(cl_sizes, prevs):
            prems.append(strip_disj_n(prev.prop, cl_size))

        _, cl_concl = resolve_order(prems)
        if set(cl_concl) == set(cl):
            return Thm(Or(*cl), *(pt.hyps for pt in prevs))
        # Sometimes the expected goal is ~~A while resolve_order returns A.
        elif len(cl_concl) == 1 and len(cl) == 1 and Not(Not(cl_concl[0])) == cl[0]:
            return Thm(Or(*cl), *(pt.hyps for pt in prevs))
        else:
            print('prev')
            for prev in prevs:
                print(prev)
            print('cl_concl')
            for t in cl_concl:
                print(t)
            print('cl')
            for t in cl:
                print(t)
            raise VeriTException("th_resolution", "unexpected conclusion")

    def get_proof_term(self, args, prevs):
        cl, cl_sizes = args
        assert len(cl_sizes) == len(prevs)

        if len(prevs) == 1 and prevs[0].prop == Not(true) and len(cl) == 0:
            return prevs[0].on_prop(rewr_conv('verit_not_simplify1'))

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
            if Not(Not(pt.prop)) == res:
                pt = pt.on_prop(rewr_conv('double_neg', sym=True))
            elif pt.prop != res:
                eq_pt = logic.imp_disj_iff(Eq(pt.prop, res))
                pt = eq_pt.equal_elim(pt)
            
            prems[id1] = res_list
            prevs[id1] = pt
        
        # Return the result of last step of resolution
        if pt.prop == Or(*cl):
            return pt
        if Not(Not(pt.prop)) == Or(*cl):
            return pt.on_prop(rewr_conv('double_neg', sym=True))
        raise VeriTException('th_resolution', 'unexpected conclusion')


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
            return Thm(goal, pt.hyps)
        else:
            raise VeriTException("implies", "unexpected goal %s" % goal)

    def get_proof_term(self, args, prevs):
        return prevs[0].on_prop(rewr_conv("imp_disj_eq"))

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
            return Thm(Or(neg_conj, pk))
        else:
            if not pk.is_conj():
                raise VeriTException("and_pos", "can't find the positive literal")
            conjs = set(conjs)
            pk = set(pk.strip_conj())
            if conjs.issuperset(pk):
                return Thm(Or(*args))
            else:
                raise VeriTException("and_pos", "unexpected result")

    def get_proof_term(self, args, prevs=None):
        pt0 = ProofTerm("imp_conj", Implies(args[0].arg, args[1]))
        pt1 = pt0.on_prop(rewr_conv("disj_conv_imp", sym=True))
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
                raise VeriTException("or_pos", "unexpected goal: %s" % Or(*args))
        if tuple(disjs) == tuple(args[1:]):
            return Thm(Or(*args))
        else:
            raise VeriTException("or_pos", "unexpected goal: %s" % Or(*args))
    
    def get_proof_term(self, args, prevs=None):
        pt0 = ProofTerm("imp_disj", Implies(args[0].arg, args[0].arg))
        pt1 = pt0.on_prop(rewr_conv("disj_conv_imp", sym=True))
        if pt1.prop == Or(*args):
            return pt1
        raise VeriTException("or_pos", "unexpected goal: %s" % Or(*args))

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
            return Thm(Or(p1, p2), pt.hyps)
        else:
            raise VeriTException("not_equiv1", "unexpected goal: %s" % Or(*args))
    
    def get_proof_term(self, args, prevs) -> ProofTerm:
        pt = prevs[0]
        pt1 = logic.apply_theorem("not_equiv1", pt)
        if pt1.prop != Or(*args):
            raise VeriTException("not_equiv1", "unexpected goal: %s" % Or(*args))
        else:
            return pt1

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
            return Thm(Or(p1, p2), pt.hyps)
        else:
            raise VeriTException("not_equiv2", "unexpected goal %s" % Or(*args))
    
    def get_proof_term(self, args, prevs) -> ProofTerm:
        pt = prevs[0]
        pt1 = logic.apply_theorem("not_equiv2", pt)
        if pt1.prop != Or(*args):
            raise VeriTException("not_equiv2", "unexpected goal %s" % Or(*args))
        else:
            return pt1


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
            return Thm(Or(*args), pt.hyps)
        else:
            raise VeriTException("equiv1", "unexpected result")
    def get_proof_term(self, args, prevs):
        pt = prevs[0]
        pt1 = logic.apply_theorem("equiv1", pt)
        if pt1.prop != Or(*args):
            raise VeriTException("equiv1", "unexpected goal %s" % Or(*args))
        else:
            return pt1

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
            return Thm(Or(*args), pt.hyps)
        else:
            raise VeriTException("equiv1", "unexpected result")
    def get_proof_term(self, args, prevs):
        pt = prevs[0]
        pt1 = logic.apply_theorem("equiv2", pt)
        if pt1.prop != Or(*args):
            raise VeriTException("equiv2", "unexpected goal %s" % Or(*args))
        else:
            return pt1



@register_macro("verit_or_neg")
class VeriTOrNeg(Macro):
    """Prove (p1 | ... | pn) | ~pk"""
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def eval(self, args, prevs):
        if len(args) != 2:
            raise VeriTException("or_neg", "should only have on argumentt")

        disj_tm, neg_tm = args
        if not disj_tm.is_disj() or not neg_tm.is_not():
            raise VeriTException("or_neg", "goal should be of the form (p1 | ... | pn) | ~pk")
        
        while disj_tm.is_disj():
            if disj_tm.arg1 == neg_tm.arg:
                return Thm(Or(*args))
            if disj_tm.arg == neg_tm.arg:
                return Thm(Or(*args))
            disj_tm = disj_tm.arg
        raise VeriTException("or_neg", "unexpected result")

    def get_proof_term(self, args, prevs):
        pt0 = ProofTerm.reflexive(Or(*args))
        pt1 = pt0.on_rhs(rewr_conv("disj_comm"), rewr_conv("disj_conv_imp"))
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
            return Thm(goal)
        else:
            raise VeriTException("eq_reflexive", "unexpected goal %s" % goal)

    def get_proof_term(self, args, prevs=None) -> ProofTerm:
        goal = args[0]
        pt = ProofTerm.reflexive(goal.lhs)
        if pt.prop != goal:
            raise VeriTException("eq_reflexive", "unexpected goal %s" % goal)
        return pt


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
            return Thm(Or(*args))
        elif cur_eq.lhs == args[-1].rhs and cur_eq.rhs == args[-1].lhs:
            return Thm(Or(*args))
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
                raise VeriTException("eq_transitive", "unexpected equality")
        
        if pt0.symmetric().prop == args[-1]:
            pt0 = pt0.symmetric() 

        assert pt0.prop == args[-1], "%s \n %s" % (str(pt0.prop), str(args[-1]))
        pt1 = pt0
        for disj in reversed(disjs):
            pt1 = pt1.implies_intr(disj).on_prop(rewr_conv("imp_disj_eq"))
        return pt1

@register_macro("verit_eq_congruent")
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
            return Thm(Or(*args))
        else:
            raise VeriTException("equiv_pos1", "unexpected goal %s" % Or(*args))
    
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
            return Thm(Or(*args))
        else:
            raise VeriTException("equiv_pos2", "unexpected goal %s" % Or(*args))
    
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
        return Thm(concl)
    
    def get_proof_term(self, args, prevs):
        disjs = [arg.arg for arg in args]
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
                raise VeriTException("imp_to_or", "unexpected prevs: %s %s" % (str(pt0.prop), str(pt1.prop)))
        
        if pt0.symmetric().prop == elems[-1]:
            pt0 = pt0.symmetric() 

        if pt0.prop != elems[-1]:
            raise VeriTException("imp_to_or", "%s \n %s" % (str(pt0.prop), str(goal.strip_disj()[-1])))
        
        return ProofTerm("imp_to_or", elems[:-1]+[goal], prevs=[pt0])


@register_macro("verit_eq_congruent_pred")
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
                raise VeriTException("eq_congruent_pred", "unexpected goal")
        pt1 = functools.reduce(lambda x, y: x.combination(y), pt_args_assms, pt0)
        if pred_fun.is_not():
            pt2 = logic.apply_theorem("eq_implies1", pt1).implies_elim(ProofTerm.assume(pred_fun.arg))
            return ProofTerm("imp_to_or", elems[:-1]+[goal], prevs=[pt2])
        else:
            pt2 = pt1.on_prop(rewr_conv("neg_iff_both_sides"))
            pt3 = logic.apply_theorem("eq_implies1", pt2).implies_elim(ProofTerm.assume(Not(pred_fun)))
            return ProofTerm("imp_to_or", elems[:-1]+[goal], prevs=[pt3])   


@register_macro("verit_distinct_elim")
class DistinctElimMacro(Macro):
    """From a theorem of the form distinct [t1, t2, ..., tn], obtain the
    conjunction of disequalities t1 ~= t2 /\ t1 ~= t3 /\ ...
    
    """
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
        if not compare_sym_tm(rhs, expected_rhs):
            raise VeriTException("distinct_elim", "incorrect rhs")
        return Thm(arg)
    
    def get_proof_term(self, goal, prevs=None):
        goal = Or(*goal)
        lhs = goal.lhs
        pt = ProofTerm.reflexive(lhs).on_rhs(verit_conv.distinct_conv())
        try:
            pt_eq = logic.imp_conj_iff(Eq(pt.prop.rhs, goal.rhs))
            return ProofTerm.transitive(pt, pt_eq)
        except AssertionError:
            # Form conjunction of pairs in ts
            distinct_ts = hol_list.dest_literal_list(lhs.arg)
            conjs = []
            for i in range(len(distinct_ts)):
                for j in range(i+1, len(distinct_ts)):
                    conjs.append(Not(Eq(distinct_ts[i], distinct_ts[j])))
            expected_rhs = And(*conjs)
            pt_eq_expected = logic.imp_conj_iff(Eq(pt.prop.rhs, expected_rhs))
            pt_sym = compare_sym_tm_thm(expected_rhs, goal.rhs)
            return ProofTerm.transitive(pt, pt_eq_expected).transitive(pt_sym)

@register_macro("verit_and")
class AndMacro(Macro):
    """Take one literal of a conjunct.
    
         A1 /\ ... /\ An
        =================
               Ai
        In the implementation, we save time by unwinding the input theorem
        one conjunct at a time.

    """
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
        arg = args[0]
        while prem.is_conj():
            if arg == prem.arg1:
                return Thm(arg, prevs[0].hyps)
            if arg == prem.arg:
                return Thm(arg, prevs[0].hyps)
            prem = prem.arg

        # Not found
        print('arg', arg)
        print('prem', prem.prop)
        raise VeriTException("and", "goal not found in premise")

    def get_proof_term(self, goal, prevs=None):
        prev = prevs[0]
        goal = Or(*goal)
        while prev.prop.is_conj():
            if goal == prev.prop.arg1:
                return logic.apply_theorem('conjD1', prev)
            if goal == prev.prop.arg:
                return logic.apply_theorem('conjD2', prev)
            prev = logic.apply_theorem('conjD2', prev)

        # Not found
        raise VeriTException("and", "goal not found in premise")

def verit_and_all(pt, ts):
    res = dict()
    ts_set = set(ts)
    if pt.prop in ts_set:
        res[pt.prop] = pt
    while pt.prop.is_conj():
        if pt.prop.arg1 in ts_set:
            res[pt.prop.arg1] = logic.apply_theorem('conjD1', pt)
        pt = logic.apply_theorem('conjD2', pt)
        if pt.prop in ts_set:
            res[pt.prop] = pt
    res_list = []
    for t in ts:
        if t not in res:
            raise VeriTException("and", "conclusion not found")
        res_list.append(res[t])
    return res_list

def verit_and_single(pt, t):
    return verit_and_all(pt, [t])[0]

@register_macro("verit_or")
class OrMacro(Macro):
    """Deconstructs a proposition A1 \/ ... \/ An into a clause. """
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def eval(self, args, prevs):
        if len(prevs) != 1:
            raise VeriTException("or", "must have a single premise")

        prev = prevs[0].prop
        prev_disjs = strip_disj_n(prev, len(args))
        if tuple(prev_disjs) != args:
            raise VeriTException("or", "incorrect conclusion")
        return Thm(Or(*args), prevs[0].hyps)

    def get_proof_term(self, args, prevs):
        # This requires no proof, as the form of the statement is unchanged
        return prevs[0]


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
        return Thm(arg)

    def get_proof_term(self, args, prevs=None):
        return logic.apply_theorem("not_false_res")

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
            return Thm(arg)
        elif lhs == Not(true) and rhs == false:
            return Thm(arg)
        elif lhs.is_not():
            if not lhs == Not(Not(rhs)):
                raise VeriTException("not_simplify", "lhs should be equal to the double negation of rhs")
            else:
                return Thm(arg)
        else:
            raise VeriTException("not_simplify", "negated term should among true, false or negation")

    def get_proof_term(self, args, prevs=None):
        goal = args[0]
        lhs, rhs = goal.args
        if lhs == Not(true) and rhs == false:
            return logic.apply_theorem("verit_not_simplify1")
        if lhs == Not(false) and rhs == true:
            return logic.apply_theorem("verit_not_simplify2")
        elif lhs == Not(Not(rhs)):
            return logic.apply_theorem("double_neg", concl=goal)
        else:
            raise VeriTException("not_simplify", "unexpcected goal")

@register_macro("verit_eq_simplify")
class EqSimplifyMacro(Macro):
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
                return Thm(arg)
            elif lhs.lhs != lhs.rhs and rhs == false:
                return Thm(arg)
            else:
                raise VeriTException("eq_simplify", "rhs doesn't obey eq_simplify rule")
        elif lhs.is_not():
            if not lhs.arg.is_equals() or lhs.arg.lhs == lhs.arg.rhs:
                raise VeriTException("eq_simplify", "lhs should be an inequality.")
            if rhs == false:
                return Thm(arg)
            else:
                raise VeriTException("eq_simplify", "rhs doesn't obey eq_simplify rule")
        else:
            raise VeriTException("eq_simplify", "lhs should be either an equality or an inequality")

    def get_proof_term(self, args, prevs=None):
        goal = args[0]
        lhs, rhs = goal.args
        if lhs.is_equals():
            if lhs.lhs == lhs.rhs and rhs == true:
                return logic.apply_theorem("eq_mean_true", concl=goal)

        if lhs.is_equals() and lhs.lhs.is_constant() and lhs.rhs.is_constant() and rhs == false:
            T = lhs.lhs.get_type()
            if T == hol_type.IntType:
                pt = ProofTerm('int_const_ineq', lhs).on_prop(rewr_conv('eq_false'))
                if pt.prop == goal:
                    return pt
            if T == hol_type.RealType:
                pt = ProofTerm('real_const_eq', lhs).on_prop(rewr_conv('eq_false'))
                if pt.prop == goal:
                    return pt

        if lhs.is_not() and lhs.arg.is_equals() and lhs.arg.lhs.is_constant()\
                 and lhs.arg.lhs == lhs.arg.rhs and rhs == false:
            return logic.apply_theorem('verit_eq_simplify', concl=goal)
        
        raise VeriTException("eq_simplify", "unexpected result")


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
            elif cur_eq.rhs == prev_prop.rhs:
                cur_eq = Eq(cur_eq.lhs, prev_prop.lhs)
            elif cur_eq.lhs == prev_prop.lhs:
                cur_eq = Eq(cur_eq.rhs, prev_prop.rhs)
            elif cur_eq.lhs == prev_prop.rhs:
                cur_eq = Eq(prev_prop.lhs, cur_eq.rhs)
            else:
                continue # verit bugs
        
        if cur_eq == arg:
            return Thm(arg, tuple([hyp for pt in prevs for hyp in pt.hyps]))
        elif Eq(cur_eq.rhs, cur_eq.lhs) == arg:
            return Thm(arg, tuple([hyp for pt in prevs for hyp in pt.hyps]))
        else:
            raise VeriTException("trans", "unexpected equality")

    def get_proof_term(self, args, prevs):
        pt = prevs[0]
        goal = args[0]
        for prev in prevs[1:]:
            if pt.rhs == prev.lhs:
                pt = ProofTerm.transitive(pt, prev)
            elif pt.rhs == prev.rhs:
                pt = ProofTerm.transitive(pt, ProofTerm.symmetric(prev))
            elif pt.lhs == prev.lhs:
                pt = pt.symmetric().transitive(prev)
            elif pt.lhs == prev.rhs:
                pt = prev.transitive(pt)
            else:
                continue # verit bugs: not all premises could be chains for transition
        if pt.prop == goal:
            return pt
        if pt.prop == Eq(goal.rhs, goal.lhs):
            return pt.symmetric()
        else:
            raise VeriTException("trans", "unexpected result")

def compare_sym_tm(tm1, tm2, *, ctx=None, depth=-1):
    """Compare tm1 and tm2 up to symmetry of equality and identification
    of terms in ctx.

    ctx is a set containing pairs (t1, t2) that should be identified. This
    function does not consider transitivity of term identifications.
    
    """
    if ctx is None:
        ctx = set()
    cache = set()
    def helper(t1, t2, depth):
        if (t1, t2) in ctx:
            return True
        if (t2, t1) in ctx:
            return True
        if depth == 0:
            return t1 == t2
        if t1.is_var() or t2.is_var():
            return t1 == t2
        elif (t1._id, t2._id) in cache:
            return True
        elif t1.is_comb():
            if not t2.is_comb() or t1.head != t2.head:
                return False
            elif t1.is_equals():
                if helper(t1.lhs, t2.lhs, depth-1) and helper(t1.rhs, t2.rhs, depth-1):
                    cache.add((t1._id, t2._id))
                    return True
                elif helper(t1.rhs, t2.lhs, depth-1) and helper(t1.lhs, t2.rhs, depth-1):
                    cache.add((t1._id, t2._id))
                    return True
                else:
                    return False
            elif t1.is_conj():
                cur_t1, cur_t2 = t1, t2
                while cur_t1.is_conj() and cur_t2.is_conj() and helper(cur_t1.arg1, cur_t2.arg1, depth-1):
                    cur_t1 = cur_t1.arg
                    cur_t2 = cur_t2.arg
                    if (cur_t1, cur_t2) in ctx:
                        cache.add((t1._id, t2._id))
                        return True
                if cur_t1 == t1 and cur_t2 == t2:
                    return False
                else:
                    return helper(cur_t1, cur_t2, depth-1)
            elif t1.is_disj():
                cur_t1, cur_t2 = t1, t2
                while cur_t1.is_disj() and cur_t2.is_disj() and helper(cur_t1.arg1, cur_t2.arg1, depth-1):
                    cur_t1 = cur_t1.arg
                    cur_t2 = cur_t2.arg
                    if (cur_t1, cur_t2) in ctx:
                        cache.add((t1._id, t2._id))
                        return True
                if cur_t1 == t1 and cur_t2 == t2:
                    return False
                else:
                    return helper(cur_t1, cur_t2, depth-1)
            elif t1.is_plus():
                cur_t1, cur_t2 = t1, t2
                while cur_t1.is_plus() and cur_t2.is_plus() and helper(cur_t1.arg, cur_t2.arg, depth-1):
                    cur_t1 = cur_t1.arg1
                    cur_t2 = cur_t2.arg1
                    if (cur_t1, cur_t2) in ctx:
                        cache.add((t1._id, t2._id))
                        return True
                if cur_t1 == t1 and cur_t2 == t2:
                    return False
                else:
                    return helper(cur_t1, cur_t2, depth-1)
            elif t1.is_let():
                cur_t1, cur_t2 = t1, t2
                while cur_t1.is_let() and cur_t2.is_let() and helper(cur_t1.arg1, cur_t2.arg1, depth-1):
                    v1, _, cur_t1 = cur_t1.dest_let()
                    v2, _, cur_t2 = cur_t2.dest_let()
                    if (cur_t1, cur_t2) in ctx:
                        cache.add((t1._id, t2._id))
                        return True
                if cur_t1 == t1 and cur_t2 == t2:
                    return False
                else:
                    return helper(cur_t1, cur_t2, depth-1)
            elif t1.is_comb('distinct'):
                if not t2.is_comb('distinct'):
                    return False
                l_args, r_args = hol_list.dest_literal_list(t1.arg), hol_list.dest_literal_list(t2.arg)
                res = all(helper(l_arg, r_arg, depth-1) for l_arg, r_arg in zip(l_args, r_args))
                if res:
                    cache.add((t1._id, t2._id))
                return res
            else:
                res = all(helper(l_arg, r_arg, depth-1) for l_arg, r_arg in zip(t1.args, t2.args))
                if res:
                    cache.add((t1._id, t2._id))
                return res
        elif t1.is_abs():
            if not t2.is_abs():
                return False
            v1, body1 = t1.dest_abs()
            v2, body2 = t2.dest_abs()
            res = (v1 == v2 and helper(body1, body2, depth-1))
            if res:
                cache.add((t1._id, t2._id))
            return res
        else:
            return t1 == t2
    return helper(tm1, tm2, depth)

def compare_sym_tm_thm(tm1: Term, tm2: Term, *, eqs=None, depth=-1) -> Optional[ProofTerm]:
    """Given two terms and a dictionary from pairs of terms to equality theorems
    relating them, form the equality between the two terms.
    
    """
    if eqs is None:
        eqs = dict()
    
    cache = dict()

    def helper(t1, t2, depth):
        """Returns one of the following:
        
        None - no equality is found between t1 and t2.
        pt - t1 and t2 are not the same term, and pt is "t1 = t2".
        
        """
        if (t1, t2) in eqs:
            return eqs[(t1, t2)]
        elif (t2, t1) in eqs:
            return eqs[(t2, t1)].symmetric()
        elif t1 == t2:
            return ProofTerm.reflexive(t1)
        elif depth == 0:
            return None
        elif (t1._id, t2._id) in cache:
            return cache[(t1._id, t2._id)]
        elif t1.is_comb():
            if not t2.is_comb() or t1.head != t2.head:
                return None
            elif t1.is_equals():
                # First, the case without exchanging equality
                lhs_eq = helper(t1.lhs, t2.lhs, depth-1)
                rhs_eq = helper(t1.rhs, t2.rhs, depth-1)
                if lhs_eq is not None and rhs_eq is not None:
                    pt = ProofTerm.reflexive(t1)
                    pt = pt.on_rhs(arg1_conv(replace_conv(lhs_eq)))
                    pt = pt.on_rhs(arg_conv(replace_conv(rhs_eq)))
                    cache[(t1._id, t2._id)] = pt
                    return pt

                # Second, the case with exchanging equality
                lhs_eq = helper(t1.rhs, t2.lhs, depth-1)
                rhs_eq = helper(t1.lhs, t2.rhs, depth-1)
                if lhs_eq is not None and rhs_eq is not None:
                    pt = ProofTerm.reflexive(t1)
                    pt = pt.on_rhs(rewr_conv("eq_sym_eq"))
                    pt = pt.on_rhs(arg1_conv(replace_conv(lhs_eq)))
                    pt = pt.on_rhs(arg_conv(replace_conv(rhs_eq)))
                    cache[(t1._id, t2._id)] = pt
                    return pt

                # Either case yield equality
                return None
            elif t1.is_conj():
                cur_t1, cur_t2 = t1, t2
                eq_pts = []
                while cur_t1.is_conj() and cur_t2.is_conj():
                    pt = helper(cur_t1.arg1, cur_t2.arg1, depth-1)
                    if not pt:
                        break
                    eq_pts.append(pt)
                    cur_t1 = cur_t1.arg
                    cur_t2 = cur_t2.arg
                    if (cur_t1, cur_t2) in eqs:
                        break
                if cur_t1 == t1 and cur_t2 == t2 and depth < 0: # avoid non-termination
                    return None
                res = helper(cur_t1, cur_t2, depth-1)
                if res is None:
                    return None
                for pt in reversed(eq_pts):
                    res = ProofTerm.reflexive(conj).combination(pt).combination(res)
                cache[(t1._id, t2._id)] = res
                return res
            elif t1.is_disj():
                cur_t1, cur_t2 = t1, t2
                eq_pts = []
                while cur_t1.is_disj() and cur_t2.is_disj():
                    pt = helper(cur_t1.arg1, cur_t2.arg1, depth-1)
                    if not pt:
                        break
                    eq_pts.append(pt)
                    cur_t1 = cur_t1.arg
                    cur_t2 = cur_t2.arg
                    if (cur_t1, cur_t2) in eqs:
                        break
                if cur_t1 == t1 and cur_t2 == t2 and depth < 0: # avoid non-termination
                    return None
                res = helper(cur_t1, cur_t2, depth-1)
                if res is None:
                    return None
                for pt in reversed(eq_pts):
                    res = ProofTerm.reflexive(disj).combination(pt).combination(res)
                cache[(t1._id, t2._id)] = res
                return res
            elif t1.is_plus():
                cur_t1, cur_t2 = t1, t2
                eq_pts = []
                while cur_t1.is_plus() and cur_t2.is_plus():
                    pt = helper(cur_t1.arg, cur_t2.arg, depth-1)
                    if not pt:
                        break
                    eq_pts.append(pt)
                    cur_t1 = cur_t1.arg1
                    cur_t2 = cur_t2.arg1
                    if (cur_t1, cur_t2) in eqs:
                        break
                if cur_t1 == t1 and cur_t2 == t2:
                    return None
                res = helper(cur_t1, cur_t2, depth-1)
                T = cur_t1.get_type()
                if res is None:
                    return None
                for pt in reversed(eq_pts):
                    res = ProofTerm.reflexive(plus(T)).combination(res).combination(pt)
                cache[(t1._id, t2._id)] = res
                return res
            elif t1.is_comb('distinct'):
                l_args, r_args = hol_list.dest_literal_list(t1.arg), hol_list.dest_literal_list(t2.arg)
                pts = []
                for l_arg, r_arg in zip(l_args, r_args):
                    pts.append(helper(l_arg, r_arg, depth-1))
                T = l_args[0].get_type()
                res = ProofTerm.reflexive(hol_list.nil(T))
                for pt in reversed(pts):
                    res = ProofTerm.reflexive(hol_list.cons(T)).combination(pt).combination(res)
                res = ProofTerm.reflexive(t1.head).combination(res)
                cache[(t1._id, t2._id)] = res
                return res
            else:
                pts = []
                for l_arg, r_arg in zip(t1.args, t2.args):
                    pts.append(helper(l_arg, r_arg, depth-1))
                if any(pt is None for pt in pts):
                    return None
                res = ProofTerm.reflexive(t1.head)
                for pt in pts:
                    res = res.combination(pt)
                cache[(t1._id, t2._id)] = res
                return res
        elif t1.is_abs():
            if not t2.is_abs():
                return None
            v2, body2 = t2.dest_abs()
            _, body1 = t1.dest_abs(var_name=v2.name)
            pt = helper(body2, body1, depth-1)
            if pt is None:
                return None
            res = ProofTerm.reflexive(t2).on_rhs(abs_conv(replace_conv(pt))).symmetric()
            cache[(t1._id, t2._id)] = res
            return res
        else:
            return None
    return helper(tm1, tm2, depth)


@register_macro("verit_cong")
class CongMacro(Macro):
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def eval(self, args, prevs):
        if len(args) != 1:
            raise VeriTException("cong", "goal should be a single term.")
        goal = args[0]
        if not goal.is_equals():
            raise VeriTException("cong", "goal should be an equality")
        
        lhs, rhs = goal.lhs, goal.rhs
        if lhs.head != rhs.head:
            raise VeriTException("cong", "head should be same")
        
        ctx = set()
        for prev in prevs:
            ctx.add((prev.lhs, prev.rhs))
            ctx.add((prev.rhs, prev.lhs))

        if compare_sym_tm(lhs, rhs, ctx=ctx, depth=1):
            return Thm(goal, *(pt.hyps for pt in prevs))
        else:
            print("lhs", lhs)
            print("rhs", rhs)
            print("prevs")
            for prev in prevs:
                print(prev)
            raise VeriTException("cong", "unexpected result")

    def get_proof_term(self, args, prevs):
        goal = args[0]
        lhs, rhs = goal.lhs, goal.rhs

        # Form dictionary from terms to proofterms rewriting that term
        prev_dict = dict()
        for prev in prevs:
            prev_dict[(prev.lhs, prev.rhs)] = prev

        pt = compare_sym_tm_thm(lhs, rhs, eqs=prev_dict, depth=1)
        if pt is not None:
            return pt

        print("lhs:", lhs)
        print("rhs:", rhs)
        print("prevs")
        for prev in prevs:
            print(prev)
        raise AssertionError

@register_macro("verit_refl")
class ReflMacro(Macro):
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def eval(self, args, prevs=None):
        if len(args) != 2:
            raise VeriTException("refl", "args should contain two terms")
        goal, ctxt = args
        if not goal.is_equals():
            raise VeriTException("refl", "goal should be an equality")
        if not isinstance(ctxt, dict):
            raise VeriTException("refl", "context should be a mapping")
        if goal.lhs.is_var() and goal.lhs.name in ctxt and ctxt[goal.lhs.name] == goal.rhs:
            return Thm(goal, goal)
        if goal.rhs.is_var() and goal.rhs.name in ctxt and ctxt[goal.rhs.name] == goal.lhs:
            return Thm(goal, Eq(goal.rhs, goal.lhs))
        else:
            raise VeriTException("refl", "either lhs and rhs of goal is not in ctx")

    def get_proof_term(self, args, prevs):
        goal, ctxt = args
        if goal.lhs.is_var() and goal.lhs.name in ctxt and ctxt[goal.lhs.name] == goal.rhs:
            return ProofTerm.assume(goal)
        if goal.rhs.is_var() and goal.rhs.name in ctxt and ctxt[goal.rhs.name] == goal.lhs:
            return ProofTerm.assume(Eq(goal.rhs, goal.lhs)).symmetric()
        else:
            raise VeriTException("refl", "either lhs and rhs of goal is not in ctx")

def gen_and(t1, t2):
    """Move conjunction within forall quantifiers."""
    if t1.is_forall() and t2.is_forall():
        v1, body1 = t1.arg.dest_abs()
        v2, body2 = t2.arg.dest_abs()
        if v1 == v2:
            return Forall(v1, gen_and(body1, body2))
        else:
            return And(t1, t2)
    else:
        return And(t1, t2)

def gen_or(t1, t2):
    """Move disjunction within exists quantifiers."""
    if t1.is_exists() and t2.is_exists():
        v1, body1 = t1.arg.dest_abs()
        v2, body2 = t2.arg.dest_abs()
        if v1 == v2:
            return Exists(v1, gen_or(body1, body2))
        else:
            return Or(t1, t2)
    else:
        return Or(t1, t2)

def quant_bool(t):
    if t.is_forall():
        if t.arg.var_T == BoolType:
            new_conj = quant_bool(gen_and(t.arg.subst_bound(false), t.arg.subst_bound(true)))
            conjs = [conj for conjs in new_conj.strip_conj() for conj in conjs.strip_conj()]
            return And(*conjs)
        else:
            v, body = t.arg.dest_abs()
            return Forall(v, quant_bool(body))
    elif t.is_exists():
        v, body = t.arg.dest_abs()
        if v.get_type() == BoolType:
            new_disj = quant_bool(gen_or(t.arg.subst_bound(false), t.arg.subst_bound(true)))
            disjs = [disj for disjs in new_disj.strip_disj() for disj in disjs.strip_disj()]
            return Or(*disjs)
        else:
            v, body = t.arg.dest_abs()
            return Exists(v, quant_bool(body))
    elif t.is_comb():
        return t.head(*(quant_bool(arg) for arg in t.args))
    elif t.is_abs():
        v, body = t.dest_abs()
        return Lambda(v, quant_bool(body))
    else:
        return t

def expand_to_ite(t):
    if t.is_conj() or t.is_disj() or t.is_implies():
        return t.head(*(expand_to_ite(arg) for arg in t.args))
    elif t.is_comb():
        # First check whether one of the arguments is a non-constant boolean formula
        for i, arg in enumerate(t.args):
            if arg.get_type() == BoolType and len(arg.get_vars()) != 0 and all(a.get_type() == BoolType for a in arg.get_vars()):
                arg_true = t.args[:i] + [true] + t.args[i+1:]
                arg_false = t.args[:i] + [false] + t.args[i+1:]
                return logic.mk_if(arg, expand_to_ite(t.head(*arg_true)),
                                   expand_to_ite(t.head(*arg_false)))
        # Now it is clear that none of the arguments are non-constant booleans
        expand_args = [expand_to_ite(arg) for arg in t.args]
        return t.head(*expand_args)
    elif t.is_abs():
        v, body = t.dest_abs()
        return Lambda(v, expand_to_ite(body))
    else:
        return t

class expand_ite_conv(Conv):
    """convert the function which has boolean non-constant argument
    to an ite term.

    Example: f x P y <--> ite P (f x true y) (f x false y)
    """
    def get_proof_term(self, t):
        if t.get_type().is_fun():
            return refl(t)
        if t.is_conj() or t.is_disj() or t.is_implies():
            return refl(t)
        elif t.is_comb():
            head_pt = refl(t.head)
            for i, arg in enumerate(t.args):
                head_pt = head_pt.combination(refl(arg))
                if arg.get_type() == BoolType and len(arg.get_vars()) != 0 and all(a.get_type() == BoolType for a in arg.get_vars()):
                    pt = head_pt.on_rhs(
                        rewr_conv("verit_bfun_elim")
                    )
                    for arg_j in t.args[i+1:]:
                        pt = pt.combination(refl(arg_j)).on_rhs(
                            rewr_conv("verit_ite_apply")
                        )
                    return pt
            return head_pt
        elif t.is_abs():
            return refl(t).on_rhs(abs_conv(self))
        else:
            return refl(t)
           

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

        # First step: replace forall and exists over boolean type
        prev1 = quant_bool(prev)

        # Second step: replace every function application with argument of
        # boolean type with an if-then-else expression.
        expected_arg = expand_to_ite(prev1)
        if not compare_sym_tm(expected_arg, arg) and not compare_sym_tm(Not(Not(expected_arg)), arg):
            print("Expected:", expected_arg)
            print("Actual:", arg)
            raise VeriTException("bfun_elim", "unexpected goal")

        return Thm(arg, prevs[0].hyps)

    def get_proof_term(self, args, prevs) -> ProofTerm:
        pt = prevs[0]
        pt1 = pt.on_prop(top_conv(verit_conv.bfun_elim_conv()), bottom_conv(expand_ite_conv()))
        if pt1.prop == args[0]:
            return pt1
        if Not(Not(pt1.prop)) == args[0]:
            return pt1.on_prop(rewr_conv("double_neg", sym=True)) # verit bug
        pt2 = compare_sym_tm_thm(pt1.prop, args[0], depth=-1)
        if pt2 is not None:
            return pt2.equal_elim(pt1)
        else:
            print("goal", args[0])
            print("pt ", prevs[0].prop)
            print("pt1", pt1.prop)
            raise AssertionError

def collect_ite(t: Term):
    """Return the list of distinct ite terms in t."""
    res = []

    def helper(t: Term):
        if logic.is_if(t):
            if t not in res:
                res.append(t)
        if t.is_comb():
            for arg in t.args:
                helper(arg)
    helper(t)
    return res

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
        if lhs == rhs: # bugs in verit
            return Thm(args[0])

        ites = collect_ite(lhs)
        ite_intros = []
        for t in ites:
            P, x, y = t.args
            ite_intros.append(logic.mk_if(P, Eq(x, t), Eq(y, t)))
        expected_ites = rhs.strip_conj()[1:]

        # Sometimes the expected result has fewer conjuncts
        expected_set = set(expected_ites)
        intros_set = set(ite_intros)
        if expected_set <= intros_set:
            return Thm(arg)

        def can_find_ite(ite, ite_set):
            if ite in ite_set:
                return True
            for sym_ite in ite_set:
                if compare_sym_tm(ite, sym_ite):
                    return True
            return False
        
        if all(can_find_ite(ite, intros_set) for ite in expected_set):
            return Thm(arg)

        expected_rhs = And(lhs, *ite_intros)
        if compare_sym_tm(expected_rhs, rhs):
            return Thm(arg)

        print("lhs", lhs)
        print("rhs", rhs)
        print()
        print("ite_intro")
        for ite in ite_intros:
            print(ite)
        print()
        print("expected")
        for ite in expected_ites:
            print(ite)
        print()
        raise VeriTException("ite_intro", "unexpected goal")

    def get_proof_term(self, args, prevs):
        # Obtain left side
        goal = args[0]
        lhs, rhs = goal.lhs, goal.rhs

        # Collect list of ite expressions
        ites = collect_ite(lhs)
        

        # For each t of the form (if P then x else y), form the theorem
        # (if P then x = t else y = t).
        ite_intros = []
        for t in ites:
            P, x, y = t.args
            ite_intros.append(logic.apply_theorem('verit_ite_intro', inst=Inst(P=P, x=x, y=y)))

        expected_ites = rhs.strip_conj()[1:]

        # Sometimes there is no extra conjunct in rhs.
        if len(expected_ites) == 0 and lhs == rhs:
            return ProofTerm.reflexive(lhs)

        # Each element of expected_ites should be equal (according to compare_sym_tm)
        # to one of ite_intros
        expected_res = []

        def find_ite(ite):
            for ite2 in ite_intros:
                if ite == ite2.prop:
                    return ite2                    
                eq_pt = compare_sym_tm_thm(ite2.prop, ite) # symmetric in ite
                if eq_pt:
                    return eq_pt.equal_elim(ite2)
            raise VeriTException("ite_intro", "cannot find conjunct in goal")

        for i, ite in enumerate(expected_ites):
            expected_res.append(find_ite(ite))
            
        # Create the conjunction of these theorems.
        ite_intros_pt = expected_res[-1]
        for pt in reversed(expected_res[:-1]):
            ite_intros_pt = logic.apply_theorem('conjI', pt, ite_intros_pt)

        # Finally, obtain the theorem lhs = (lhs & ite_intros)
        pt = logic.apply_theorem('verit_eq_conj', ite_intros_pt, inst=Inst(P=lhs))
        if goal.lhs == goal.rhs.arg1:
            return pt
        # Special case: lhs = (lhs' & ite_intros), equalities in lhs' are reordered
        return pt.on_rhs(arg1_conv(replace_conv(compare_sym_tm_thm(lhs, rhs.arg1))))

@register_macro("verit_ite1")
class ITE1(Macro):
    """Take the else branch of ite.

          if p1 then p2 else p3
       ===========================
              p1 \/ p3
    """
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
        return Thm(Or(arg1, arg2), prevs[0].hyps)

    def get_proof_term(self, goal, prevs):
        return logic.apply_theorem('verit_ite1', prevs[0])

@register_macro("verit_ite2")
class ITE2(Macro):
    """Take the then branch of ite.

          if p1 then p2 else p3
       ===========================
              ~p1 \/ p2
    """
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
        return Thm(Or(arg1, arg2), prevs[0].hyps)

    def get_proof_term(self, goal, prevs):
        return logic.apply_theorem('verit_ite2', prevs[0])
    

@register_macro("verit_and_neg")
class AndNegMacro(Macro):
    """Prove (p1 & p2 & ... & pn) | ~p1 | ... | ~pn"""
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def eval(self, args, prevs=None):
        conj = args[0]
        neg_disjs = args[1:]
        expected_conj = []
        while conj.is_conj():
            expected_conj.append(Not(conj.arg1))
            if Not(conj.arg) == args[-1]:
                expected_conj.append(Not(conj.arg))
                break
            conj = conj.arg
        if neg_disjs != tuple(expected_conj):
            raise VeriTException("and_neg", "Unexpected goal")
        return Thm(Or(*args))

    def get_proof_term(self, args, prevs):
        # First form (p1 & p2 & ... & pn) | ~(p1 & p2 & ... & pn)
        conj = args[0]
        conj_pt = logic.apply_theorem('classical', inst=Inst(A=conj))

        # Then apply deMorgan's rule to the right side
        pt = conj_pt.on_prop(arg_conv(verit_conv.deMorgan_conj_conv(rm=args[-1].arg)))
        if pt.prop == Or(*args):
            return pt
        else:
            print('Obtained', pt.prop)
            print('Expected', Or(*args))
            raise VeriTException("and_neg", "unexpected result")
        


@register_macro("verit_contraction")
class ContractionMacro(Macro):
    """Remove duplicate literals in a disjunction."""
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
        return Thm(Or(*args), prevs[0].hyps)

    def get_proof_term(self, goal, prevs):
        prev = prevs[0].prop
        goal = Or(*goal)

        pt = ProofTerm('imp_disj', Implies(prev, goal))
        return pt.implies_elim(prevs[0])


@register_macro("verit_let")
class LetMacro(Macro):
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def eval(self, args, prevs):
        goal = args[0]
        prop_eq = prevs[:-1]
        last_step = prevs[-1]
        ctx = set()
        for prop in prop_eq:
            ctx.add((prop.lhs, prop.rhs))

        body = goal.lhs
        xs = []
        while body != last_step.lhs and body.is_let():
            x, _, body = body.dest_let()
            xs.append(x)

        # body should equal to the left side of last_step
        if body != last_step.lhs:
            print('body:', body)
            print('last_step.lhs:', last_step.lhs)
            raise VeriTException("let", "left side does not equal body of let term")

        if goal.rhs != last_step.rhs:
            raise VeriTException("let", "right side does not equal")

        remain_hyps = []
        for hyp in last_step.hyps:
            if not (hyp.is_equals() and hyp.lhs in xs):
                remain_hyps.append(hyp)
        return Thm(goal, tuple(remain_hyps), *(prop.hyps for prop in prevs[:-1]))

    def get_proof_term(self, args, prevs):
        goal = args[0]
        prop_eq = prevs[:-1]
        last_step = prevs[-1]
        eqs = dict()
        for prop in prop_eq:
            eqs[(prop.lhs, prop.rhs)] = prop
        
        let_eqs = []
        body = goal.lhs
        while body != last_step.lhs and body.is_let():
            x, t, body = body.dest_let()
            let_eqs.append((x, t))

        # Start from last_step, which is body == goal.rhs, successively
        # introduce hypothesis of the form x = s, where either s = t or
        # (t, s) is in eqs.
        cur_pt = last_step
        var_map = dict()
        for hyp in last_step.hyps:
            if hyp.is_equals() and hyp.lhs.is_var():
                var_map[hyp.lhs] = hyp.rhs

        inst = Inst()
        # Introduce x = s as an assumption
        for x, t in let_eqs:
            found_hyp = Eq(x, t)
            if x in var_map:
                found_hyp = Eq(x, var_map[x])
            cur_pt = cur_pt.implies_intr(found_hyp)
            inst.var_inst[x.name] = t

        # Replace x with t globally
        cur_pt = cur_pt.substitution(inst)

        # Discharge t = s using either eqs or using reflexivity
        for x, t in reversed(let_eqs):
            found_hyp = Eq(x, t)
            if x in var_map:
                found_hyp = Eq(x, var_map[x])
            if found_hyp.rhs == t:
                cur_pt = cur_pt.implies_elim(ProofTerm.reflexive(t))
            else:
                cur_pt = cur_pt.implies_elim(eqs[(t, found_hyp.rhs)])

        # Now the left side is u[t/x], rewrite it from let x = t in u.
        let_pt = ProofTerm.reflexive(goal.lhs)
        for _ in range(len(let_eqs)):
            t, let_abs = let_pt.rhs.args
            eq_pt = ProofTerm.theorem('Let_def').substitution(Inst(s=t, f=let_abs)).on_rhs(beta_conv())
            let_pt = ProofTerm.transitive(let_pt, eq_pt)

        # Finally combine using transitivity
        return ProofTerm.transitive(let_pt, cur_pt)


def flatten_prop(tm):
    """Unfold a nested proposition formula."""
    if tm.is_conj():
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
    elif tm.is_implies():
        prem, concl = tm.args
        return hol_term.Implies(flatten_prop(prem), flatten_prop(concl))
    elif tm.is_equals():
        lhs, rhs = tm.args
        return Eq(flatten_prop(lhs), flatten_prop(rhs))
    elif tm.is_forall():
        x, body = tm.arg.dest_abs()
        return hol_term.Forall(x, flatten_prop(body))
    elif logic.is_if(tm):
        P, x, y = tm.args
        return logic.mk_if(flatten_prop(P), flatten_prop(x), flatten_prop(y))
    elif tm.is_comb():
        return tm.head(*(flatten_prop(arg) for arg in tm.args))
    else:
        return tm

def compare_ac(tm1, tm2):
    """Compare two terms up to AC of conjunction and disjunction."""
    if tm1.is_conj():
        conjs1 = logic.strip_conj(tm1)
        conjs2 = logic.strip_conj(tm2)
        if set(conjs1) == set(conjs2):
            return True
        if len(conjs1) == len(conjs2) and all(compare_ac(t1, t2) for t1, t2 in zip(conjs1, conjs2)):
            return True
        conjs1 = [flatten_prop(t) for t in conjs1]
        conjs2 = [flatten_prop(t) for t in conjs2]
        return set(conjs1) == set(conjs2)
    elif tm1.is_disj():
        disjs1 = logic.strip_disj(tm1)
        disjs2 = logic.strip_disj(tm2)
        if set(disjs1) == set(disjs2):
            return True
        if len(disjs1) == len(disjs2) and all(compare_ac(t1, t2) for t1, t2 in zip(disjs1, disjs2)):
            return True
        disjs1 = [flatten_prop(t) for t in disjs1]
        disjs2 = [flatten_prop(t) for t in disjs2]
        return set(disjs1) == set(disjs2)
    elif tm1.is_not():
        return tm2.is_not() and compare_ac(tm1.arg, tm2.arg)
    elif tm1.is_implies():
        return tm2.is_implies() and compare_ac(tm1.arg1, tm2.arg1) and compare_ac(tm1.arg, tm2.arg)
    elif tm1.is_equals():
        return compare_ac(tm1.arg1, tm2.arg1) and compare_ac(tm1.arg, tm2.arg)
    elif tm1.is_forall():
        if not tm2.is_forall():
            return False
        x1, body1 = tm1.arg.dest_abs()
        x2, body2 = tm2.arg.dest_abs()
        return x1 == x2 and compare_ac(body1, body2)
    elif tm1.is_exists():
        if not tm2.is_exists():
            return False
        x1, body1 = tm1.arg.dest_abs()
        x2, body2 = tm2.arg.dest_abs()
        return x1 == x2 and compare_ac(body1, body2)
    elif logic.is_if(tm1):
        P1, x1, y1 = tm1.args
        P2, x2, y2 = tm2.args
        return compare_ac(P1, P2) and compare_ac(x1, x2) and compare_ac(y1, y2)
    elif tm1.is_plus():
        return compare_ac(tm1.arg1, tm2.arg1) and compare_ac(tm1.arg, tm2.arg)
    elif tm1.is_times():
        return compare_ac(tm1.arg1, tm2.arg1) and compare_ac(tm1.arg, tm2.arg)
    else:
        return tm1 == tm2

def compare_ac_thm(tm1, tm2):
    if tm1.is_conj():
        conjs1 = logic.strip_conj(tm1)
        conjs2 = logic.strip_conj(tm2)
        conjs1_set = set(conjs1)
        conjs2_set = set(conjs2)

        if conjs1_set == conjs2_set:
            return logic.imp_conj_iff(Eq(tm1, tm2))

        # remove the repeated conjuncts in conjs1_set
        if len(conjs1) != len(conjs2) and len(conjs1_set) == len(conjs2_set):
            conjs1_unique = []
            for conj1 in conjs1:
                if conj1 not in conjs1_unique:
                    conjs1_unique.append(conj1)
            assert len(conjs1_unique) == len(conjs2)
            conjs1 = conjs1_unique
        
        if len(conjs1) == len(conjs2) and all(compare_ac(t1, t2) for t1, t2 in zip(conjs1, conjs2)):
            eqs = dict()
            for t1, t2 in zip(conjs1, conjs2):
                if t1 != t2:
                    eqs[(t1, t2)] = compare_ac_thm(t1, t2)
            tm1_eq = logic.imp_conj_iff(Eq(tm1, And(*conjs1)))
            tm2_eq = logic.imp_conj_iff(Eq(tm2, And(*conjs2)))
            sub_eq = compare_sym_tm_thm(tm1_eq.rhs, tm2_eq.rhs, eqs=eqs)
            return ProofTerm.transitive(tm1_eq, sub_eq, tm2_eq.symmetric())
        raise AssertionError
    elif tm1.is_disj():
        disjs1 = logic.strip_disj(tm1)
        disjs2 = logic.strip_disj(tm2)
        if set(disjs1) == set(disjs2):
            return logic.imp_disj_iff(Eq(tm1, tm2))
        if len(disjs1) == len(disjs2) and all(compare_ac(t1, t2) for t1, t2 in zip(disjs1, disjs2)):
            eqs = dict()
            for t1, t2 in zip(disjs1, disjs2):
                if t1 != t2:
                    eqs[(t1, t2)] = compare_ac_thm(t1, t2)
            tm1_eq = logic.imp_disj_iff(Eq(tm1, Or(*disjs1)))
            tm2_eq = logic.imp_disj_iff(Eq(tm2, Or(*disjs2)))
            sub_eq = compare_sym_tm_thm(tm1_eq.rhs, tm2_eq.rhs, eqs=eqs)
            return ProofTerm.transitive(tm1_eq, sub_eq, tm2_eq.symmetric())

        raise NotImplementedError
    elif tm1.is_not():
        eq_pt = compare_ac_thm(tm1.arg, tm2.arg)
        return ProofTerm.reflexive(neg).combination(eq_pt)
    elif tm1.is_implies():
        eq_pt1 = compare_ac_thm(tm1.arg1, tm2.arg1)
        eq_pt2 = compare_ac_thm(tm1.arg, tm2.arg)
        return ProofTerm.reflexive(implies).combination(eq_pt1).combination(eq_pt2)
    elif tm1.is_equals():
        eq_pt1 = compare_ac_thm(tm1.lhs, tm2.lhs)
        eq_pt2 = compare_ac_thm(tm1.rhs, tm2.rhs)
        return ProofTerm.reflexive(tm1.head).combination(eq_pt1).combination(eq_pt2)
    elif tm1.is_forall() or tm1.is_exists():
        x1, body1 = tm1.arg.dest_abs()
        x2, body2 = tm2.arg.dest_abs()
        eq_pt = compare_ac_thm(body1, body2)
        return ProofTerm.reflexive(tm1).on_rhs(arg_conv(abs_conv(replace_conv(eq_pt))))
    elif logic.is_if(tm1):
        P1, x1, y1 = tm1.args
        P2, x2, y2 = tm2.args
        eq_P1_P2 = compare_ac_thm(P1, P2)
        eq_x1_x2 = compare_ac_thm(x1, x2)
        eq_y1_y2 = compare_ac_thm(y1, y2)
        return ProofTerm.reflexive(tm1.head).combination(eq_P1_P2).combination(eq_x1_x2).combination(eq_y1_y2)
    elif tm1.is_plus():
        x1, y1 = tm1.args
        x2, y2 = tm2.args
        eq_x1_x2 = compare_ac_thm(x1, x2)
        eq_y1_y2 = compare_ac_thm(y1, y2)
        return ProofTerm.reflexive(tm1.head).combination(eq_x1_x2).combination(eq_y1_y2)
    elif tm1.is_times():
        x1, y1 = tm1.args
        x2, y2 = tm2.args
        eq_x1_x2 = compare_ac_thm(x1, x2)
        eq_y1_y2 = compare_ac_thm(y1, y2)
        return ProofTerm.reflexive(tm1.head).combination(eq_x1_x2).combination(eq_y1_y2)
    else:
        if tm1 != tm2:
            print("tm1", tm1)
            print("tm2", tm2)
            raise VeriTException("ac_simp", "arguments not equal")
        return ProofTerm.reflexive(tm1)


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
        if compare_ac(lhs, rhs):
            return Thm(goal)
        else:
            print('lhs:', lhs)
            print('rhs:', rhs)
            raise VeriTException("ac_simp", "unexpected result")
    
    def get_proof_term(self, args, prevs):
        goal = args[0]
        lhs, rhs = goal.lhs, goal.rhs
        return compare_ac_thm(lhs, rhs)


@register_macro('verit_imp_conj')
class imp_conj_macro(Macro):
    def __init__(self):
        self.level = 0
        self.sig = Term
        self.limit = None

    def get_proof_term(self, goal, pts, num=None):
        dct = dict()
        A = goal.arg1
        ptA = ProofTerm.assume(A)
        if num is not None:
            rhs_conjs = strip_conj_n(goal.arg, num)
        else:
            rhs_conjs = goal.arg.strip_conj()
        while ptA.prop.is_conj():
            pt1 = logic.apply_theorem("conjD1", ptA)
            pt2 = logic.apply_theorem("conjD2", ptA)
            if pt1.prop != true:
                dct[pt1.prop] = pt1
            if pt2.prop in rhs_conjs:
                dct[pt2.prop] = pt2
                break
            ptA = pt2
        dct[ptA.prop] = ptA

        C = goal.arg
        ptCs = []
        if C in dct:
            ptCs.append(dct[C])
        while C.is_conj() and C not in dct:
            l, r = C.args
            if l == true:
                ptCs.append(logic.apply_theorem("trueI"))
            else:
                assert l in dct
                ptCs.append(dct[l])

            if not r.is_conj():
                if r == true:
                    ptCs.append(logic.apply_theorem("trueI"))
                else:
                    assert r in dct
                    ptCs.append(dct[r])
            elif r in dct:
                ptCs.append(dct[r])
                break
            C = r
        if len(ptCs) == 0:
            ptCs = [dct[goal.arg]]
        ptC = ptCs[-1]
        for pt in reversed(ptCs[:-1]):
            ptC = logic.apply_theorem("conjI", pt, ptC)

        return ptC.implies_intr(A)

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

        # Case 2: remove true
        elim_true_conj = []
        for conj in lhs_conjs:
            if conj != true:
                elim_true_conj.append(conj)
        if And(*elim_true_conj) == goal.rhs:
            return Thm(goal)

        # Case 3: remove duplicates
        nodup_conj = []
        for conj in lhs_conjs:
            if conj not in nodup_conj:
                nodup_conj.append(conj)
        if And(*nodup_conj) == goal.rhs:
            return Thm(goal)

        # Case 4: false appears on the left side, and right side is false.
        if false in lhs_conjs and goal.rhs == false:
            return Thm(goal)

        # Case 5: p_1 & .... & p_n <--> false if ?i, j. p_i = ~p_j
        for i in range(len(lhs_conjs)):
            for j in range(i+1, len(lhs_conjs)):
                if Not(lhs_conjs[i]) == lhs_conjs[j] or lhs_conjs[i] == Not(lhs_conjs[j]):
                    if goal.rhs == false:
                        return Thm(goal)
                elif lhs_conjs[i] == Not(And(*lhs_conjs[j:])) and goal.rhs == false:
                    return Thm(goal)

        print('goal', goal)
        raise VeriTException("and_simplify", "unexpected rhs")

    def get_proof_term(self, args, prevs=None):
        def find_pos_neg_pair(conjs):
            for i in range(len(conjs)):
                for j in range(i+1, len(conjs)):
                    if Not(conjs[i]) == conjs[j]:
                        # p_1 & ... & p_i & ... & ~p_i & ... p_n --> p_i & ~p_i
                        return ProofTerm("verit_imp_conj", args=Implies(lhs, And(conjs[i], conjs[j])))
                    elif conjs[i] == Not(conjs[j]):
                       # p_1 & ... & p_i & ... & ~p_i & ... p_n --> ~p_i & p_i
                        return ProofTerm("verit_imp_conj", args=Implies(lhs, And(conjs[j], conjs[i])))
                    elif Not(conjs[i]) == And(*conjs[j:]):
                        return ProofTerm("verit_imp_conj", args=Implies(lhs, And(conjs[i], And(*conjs[j:]))))
                    elif conjs[i] == Not(And(*conjs[j:])):
                        return ProofTerm("verit_imp_conj", args=Implies(lhs, And(And(*conjs[j:]), conjs[i])))
            return None

        goal = args[0]
        lhs, rhs = goal.args
        if rhs == false:
            lhs_conjs = lhs.strip_conj()
            pt_r_l = logic.apply_theorem("falseE", concl=lhs) # false -> anything
            if false in lhs_conjs:
                # p_1 & ... & false & ... & p_n --> false
                pt_l_r = ProofTerm("verit_imp_conj", args=Implies(lhs, rhs))
                return ProofTerm.equal_intr(pt_l_r, pt_r_l)
            else:
                pt = find_pos_neg_pair(lhs_conjs)
                assert pt is not None
                pt_imp_false = logic.apply_theorem("verit_conj_pos_neg", inst=Inst(P=pt.prop.arg.arg1))
                pt_l_r = logic.apply_theorem("syllogism", pt, pt_imp_false)
                return ProofTerm.equal_intr(pt_l_r, pt_r_l)
        else:
            pt1 = ProofTerm("verit_imp_conj", args=Implies(lhs, rhs))
            pt2 = ProofTerm("verit_imp_conj", args=Implies(rhs, lhs))
            if pt1.prop.arg1 == lhs and pt1.prop.arg == rhs:
                return ProofTerm.equal_intr(pt1, pt2)

        raise VeriTException("and_simplify", "unexpected result")



@register_macro('verit_imp_disj')
class imp_disj_macro(Macro):
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def get_proof_term(self, goal, pts):
        """Goal is of the form A_1 | ... | A_m --> B_1 | ...| B_n, where
        {A_1, ..., A_m} is a subset of {B_1, ..., B_n}."""

        # Dictionary from B_i to B_i --> B_1 | ... | B_n
        pts_B = dict()
        concl = goal.arg
        triv_pt = logic.apply_theorem("trivial", concl=concl)
        if not concl.is_disj():
            pts_B[concl]= triv_pt
        prem_disjs = goal.arg1.strip_disj()
        if concl in prem_disjs:
            pts_B[concl] = triv_pt

        while concl.is_disj() and concl not in prem_disjs:
            l, r = concl.args
            pt1 = logic.apply_theorem("syllogism",\
                    logic.apply_theorem("disjI1", concl=triv_pt.prop.arg1), triv_pt)
            pt2 = logic.apply_theorem("syllogism",\
                    logic.apply_theorem("disjI2", concl=triv_pt.prop.arg1), triv_pt)
            pts_B[l] = pt1
            if not r.is_disj():
                pts_B[r] = pt2
                break
            concl = r
            triv_pt = pt2

        A = goal.arg1
        pts_A = []
        if not A.is_disj():
            assert A in pts_B
            pts_A = [pts_B[A]]
        if A in pts_B:
            pts_A = [pts_B[A]]
        while A.is_disj() and A not in pts_B:
            l, r = A.args
            if l == false:
                pts_A.append(logic.apply_theorem("falseE", concl=goal.arg))
            else:
                assert l in pts_B
                pts_A.append(pts_B[l])
            if not r.is_disj():
                if r == false:
                    pts_A.append(logic.apply_theorem("falseE", concl=goal.arg))
                else:
                    assert r in pts_B, str(r)
                    pts_A.append(pts_B[r])
                break
            A = r

        assert isinstance(pts_A[-1], ProofTerm), "not implemented yet"
        
        pt_A = pts_A[-1]
        for pt in reversed(pts_A[:-1]):
            pt_A = logic.apply_theorem("disjE2", pt, pt_A)
        
        return pt_A

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
                        return Thm(goal)
                    else:
                        raise VeriTException("or_simplify", "unexpected rhs")
        
        # delete redundant false
        elim_false_disj = []
        for disj in lhs_disjs:
            if disj != false:
                elim_false_disj.append(disj)
        if Or(*elim_false_disj) == goal.rhs:
            return Thm(goal)
        
        if set(lhs_disjs) == set(goal.rhs.strip_disj()):
            return Thm(goal)

        if true in lhs_disjs and goal.rhs == true:
                return Thm(goal)
            # else:
            #     #  ~(p3 c_0) | ~(p4 c_1) | ~(p1 c_0 c_1) | true | true <--> ~(p3 c_0) | ~(p4 c_1) | ~(p1 c_0 c_1) | true
            #     print("goal", goal)
            #     raise VeriTException("or_simplify", "unexpected rhs")
        raise VeriTException("or_simplify", "unexpected goal")

    def get_proof_term(self, args, prevs):
        goal = args[0]
        lhs, rhs = goal.args
        if lhs == rhs:
            return ProofTerm.reflexive(lhs)
        if not lhs.is_disj() and not rhs.is_disj():
            raise VeriTException("or_simplify", "unexpected argument")
        if rhs == true:
            pt_true = logic.apply_theorem("trueI")
            pt_l_r = pt_true.implies_intr(lhs)
            disjs = lhs.strip_disj()
            if true in disjs:
                pt_r_l = ProofTerm("verit_imp_disj", args=Implies(true, lhs))
            else:
                pair = []
                for i, disj1 in enumerate(disjs):
                    for j, disj2 in enumerate(disjs):
                        if disj1 == Not(disj2):
                            pair = [disj1, disj2]
                    if len(pair) > 0:
                        break
                pt0 = logic.apply_theorem("or_pos", concl=Or(*pair))
                pt1 = ProofTerm("verit_imp_disj", args=Implies(Or(*pair), lhs))
                pt2 = pt0.implies_intr(true)
                pt_r_l = logic.apply_theorem("syllogism", pt2, pt1)


            return ProofTerm.equal_intr(pt_l_r, pt_r_l)

        pt1 = ProofTerm("verit_imp_disj", args=Implies(lhs, rhs))
        pt2 = ProofTerm("verit_imp_disj", args=Implies(rhs, lhs))
        if pt1.prop.arg1 == lhs and pt1.prop.arg == rhs:
            return ProofTerm.equal_intr(pt1, pt2)


        raise VeriTException("or_simplify", "unexpected result")




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
                return Thm(goal)
            else:
                raise VeriTException("bool_simplify", "goal cannot match  ~(p --> q) <--> (p and ~q)")
        # case 2: ~(p | q) <--> (~p & ~q)
        elif lhs.is_not() and lhs.arg.is_disj() and rhs.is_conj():
            l_p, l_q = lhs.arg.args
            r_p, r_q = rhs.args
            if Not(l_p) == r_p and Not(l_q) == r_q:
                return Thm(goal)
            else:
                raise VeriTException("bool_simplify", "goal cannot match ~(p | q) <--> (~p & ~q)")
        # case 3: ~(p & q) <--> (~p | ~q)
        elif lhs.is_not() and lhs.arg.is_conj() and rhs.is_disj():
            l_p, l_q = lhs.arg.args
            r_p, r_q = rhs.args
            if Not(l_p) == r_p and Not(l_q) == r_q:
                return Thm(goal)
            else:
                raise VeriTException("bool_simplify", "goal cannot match ~(p | q) <--> (~p & ~q)")
        # case 4: (p1 --> p2 --> p3) <--> (q1 & q2) --> q3
        elif lhs.is_implies() and lhs.arg.is_implies() and rhs.is_implies() and rhs.arg1.is_conj():
            p1, p2, p3 = lhs.arg1, lhs.arg.arg1, lhs.arg.arg
            q1, q2, q3 = rhs.arg1.arg1, rhs.arg1.arg, rhs.arg
            if p1 == q1 and p2 == q2 and p3 == q3:
                return Thm(goal)
            else:
                raise VeriTException("bool_simplify", "goal cannot match (p1 --> p2 --> p3) <--> (q1 & q2) --> q3")
        # case 5: ((p1 --> p2) --> p2) <--> p1 | p2
        elif lhs.is_implies() and lhs.arg1.is_implies() and rhs.is_disj():
            p1, p2, p3 = lhs.arg1.arg1, lhs.arg1.arg, lhs.arg
            # q1, q2, q3 = rhs.arg1.arg1, rhs.arg1.arg, rhs.arg
            q1, q2 = rhs.args
            if p1 == q1 and p2 == q2 and p3 == q2:
                return Thm(goal)
            else:
                raise VeriTException("bool_simplify", "goal cannot match ((p1 --> p2) --> p2) <--> p1 | p2")
        # case 6: (p1 & (p1 --> p2)) <--> p1 & p2
        elif lhs.is_conj() and lhs.arg.is_implies() and rhs.is_conj():
            p1, p2, p3 = lhs.arg1, lhs.arg.arg1, lhs.arg.arg
            q1, q2 = rhs.args
            if p1 == p2 and p1 == q1 and p3 == q2:
                return Thm(goal)
            else:
                raise VeriTException("bool_simplify", "goal cannot match (p1 & (p1 --> p2)) <--> p1 & p2")
        # case 7: (p1 --> p2) & p1 <--> p1 & p2
        elif lhs.is_conj() and lhs.arg1.is_implies() and rhs.is_conj():
            p1, p2, p3 = lhs.arg1.arg1, lhs.arg1.arg, lhs.arg
            q1, q2 = rhs.args
            if p1 == p3 and p1 == q1 and p2 == q2:
                return Thm(goal)
            else:
                raise VeriTException("bool_simplify", "goal cannot match (p1 --> p2) & p1 <--> p1 & p2")
        else:
            print("lhs", lhs)
            print("rhs", rhs)
            raise VeriTException("bool_simplify", "unexpected result")

    def get_proof_term(self, args, prevs):
        goal = args[0]

        lhs, rhs = goal.lhs, goal.rhs
        # case 1: ~(p --> q) <--> (p and ~q)
        if lhs.is_not() and lhs.arg.is_implies() and rhs.is_conj():
            l_p, l_q = lhs.arg.args
            r_p, r_q = rhs.args
            if l_p == r_p and Not(l_q) == r_q:
                return logic.apply_theorem("verit_bool_simplify1", concl=goal)
            else:
                raise VeriTException("bool_simplify", "goal cannot match  ~(p --> q) <--> (p and ~q)")
        # case 2: ~(p | q) <--> (~p & ~q)
        elif lhs.is_not() and lhs.arg.is_disj() and rhs.is_conj():
            l_p, l_q = lhs.arg.args
            r_p, r_q = rhs.args
            if Not(l_p) == r_p and Not(l_q) == r_q:
                return logic.apply_theorem("de_morgan_thm2", concl=goal)
            else:
                raise VeriTException("bool_simplify", "goal cannot match ~(p | q) <--> (~p & ~q)")
        # case 3: ~(p & q) <--> (~p | ~q)
        elif lhs.is_not() and lhs.arg.is_conj() and rhs.is_disj():
            l_p, l_q = lhs.arg.args
            r_p, r_q = rhs.args
            if Not(l_p) == r_p and Not(l_q) == r_q:
                return logic.apply_theorem("de_morgan_thm1", concl=goal)
            else:
                raise VeriTException("bool_simplify", "goal cannot match ~(p | q) <--> (~p & ~q)")
        # case 4: (p1 --> p2 --> p3) <--> (q1 & q2) --> q3
        elif lhs.is_implies() and lhs.arg.is_implies() and rhs.is_implies() and rhs.arg1.is_conj():
            p1, p2, p3 = lhs.arg1, lhs.arg.arg1, lhs.arg.arg
            q1, q2, q3 = rhs.arg1.arg1, rhs.arg1.arg, rhs.arg
            if p1 == q1 and p2 == q2 and p3 == q3:
                return logic.apply_theorem("verit_bool_simplify4", concl=goal)
            else:
                raise VeriTException("bool_simplify", "goal cannot match (p1 --> p2 --> p3) <--> (q1 & q2) --> q3")
        # case 5: ((p1 --> p2) --> p2) <--> p1 | p2
        elif lhs.is_implies() and lhs.arg1.is_implies() and rhs.is_disj():
            p1, p2, p3 = lhs.arg1.arg1, lhs.arg1.arg, lhs.arg
            # q1, q2, q3 = rhs.arg1.arg1, rhs.arg1.arg, rhs.arg
            q1, q2 = rhs.args
            if p1 == q1 and p2 == q2 and p3 == q2:
                return logic.apply_theorem("verit_bool_simplify5", concl=goal)
            else:
                raise VeriTException("bool_simplify", "goal cannot match ((p1 --> p2) --> p2) <--> p1 | p2")
        # case 6: (p1 & (p1 --> p2)) <--> p1 & p2
        elif lhs.is_conj() and lhs.arg.is_implies() and rhs.is_conj():
            p1, p2, p3 = lhs.arg1, lhs.arg.arg1, lhs.arg.arg
            q1, q2 = rhs.args
            if p1 == p2 and p1 == q1 and p3 == q2:
                return logic.apply_theorem("verit_bool_simplify6", concl=goal)
            else:
                raise VeriTException("bool_simplify", "goal cannot match (p1 & (p1 --> p2)) <--> p1 & p2")
        # case 7: (p1 --> p2) & p1 <--> p1 & p2
        elif lhs.is_conj() and lhs.arg1.is_implies() and rhs.is_conj():
            p1, p2, p3 = lhs.arg1.arg1, lhs.arg1.arg, lhs.arg
            q1, q2 = rhs.args
            if p1 == p3 and p1 == q1 and p2 == q2:
                return logic.apply_theorem("verit_bool_simplify7", concl=goal)
            else:
                raise VeriTException("bool_simplify", "goal cannot match (p1 --> p2) & p1 <--> p1 & p2")
        else:
            print("lhs", lhs)
            print("rhs", rhs)
            raise VeriTException("bool_simplify", "unexpected result")

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
            return Thm(goal)
        else:
            raise VeriTException("verit_la_disequality", "can't match goal")

    def get_proof_term(self, args, prevs) -> ProofTerm:
        goal = args[0]
        T = goal.arg1.lhs.get_type()
        if T == hol_type.IntType:
            pt = logic.apply_theorem('verit_la_disequality_int', concl=goal)

        if T == hol_type.RealType:
            pt = logic.apply_theorem('verit_la_disequality_real', concl=goal)

        if pt.prop == goal:
            return pt
        else:        
            raise VeriTException("verit_la_disequality", "can't match goal")

def int_split_num_expr(t):
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

def real_split_num_expr(t):
    summands = integer.strip_plus_full(t)
    nums, non_nums = [hol_term.Real(0)], []
    for s in summands:
        if s.is_number():
            nums.append(s)
        else:
            non_nums.append(s)

    const = real.real_eval(sum(nums[1:], nums[0]))
    if len(non_nums) == 0: # t is a constant
        return hol_term.Real(const)
    
    non_nums_sum = sum(non_nums[1:], non_nums[0])
    if const == 0:
        return non_nums_sum
    else:
        return hol_term.Real(const) + non_nums_sum


def split_num_expr(t):
    T = t.get_type()
    if T == hol_type.IntType:
        return int_split_num_expr(t)
    elif T == hol_type.RealType:
        return real_split_num_expr(t)
    else:
        raise AssertionError

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
            return Thm(goal)
        elif lhs_simp == split_num_expr(rhs):
            """Verit bugs: QF_UFLIA\\wisas\\xs_5_10.smt2 step t27 rhs side has zero on the right."""
            return Thm(goal)
        else:
            raise VeriTException("sum_simplify", "unexpected result")

    def get_proof_term(self, args, prevs) -> ProofTerm:
        goal = args[0]
        T = goal.lhs.get_type()
        if T == hol_type.RealType:
            simp_conv = verit_conv.simp_lra_conv()
        else:
            simp_conv = verit_conv.simp_lia_conv()
        pt_lhs_simp = refl(goal.lhs).on_rhs(simp_conv)
        if pt_lhs_simp.rhs == goal.rhs:
            return pt_lhs_simp

        # try to normalize rhs        
        pt_rhs_simp = refl(goal.rhs).on_rhs(simp_conv)
        if pt_rhs_simp.rhs == pt_lhs_simp.rhs:
            return pt_lhs_simp.transitive(pt_rhs_simp.symmetric())
        else:
            raise VeriTException("sum_simplify", "unexpected result")

def eval_hol_number(tm):
    assert tm.is_constant()
    if tm.get_type() == hol_type.IntType:
        return integer.int_eval(tm)
    elif tm.get_type() == hol_type.RealType:
        return real.real_eval(tm)
    else:
        raise NotImplementedError
    

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
        if not lhs.is_compares():
            raise VeriTException("comp_simplify", "lhs should be a comparison")
        t1, t2 = lhs.args
        # Case 1 and 3: numerical constants
        if t1.is_constant() and t2.is_constant():
            t1_n, t2_n = eval_hol_number(t1), eval_hol_number(t2)
            if lhs.is_less():
                if t1_n < t2_n and rhs == true:
                    return Thm(goal)
                elif t1_n >= t2_n and rhs == false:
                    return Thm(goal)
                else:
                    raise VeriTException("comp_simplify", "unexpected lhs")
            elif lhs.is_less_eq():
                if t1_n <= t2_n and rhs == true:
                    return Thm(goal)
                elif t1_n > t2_n and rhs == false:
                    return Thm(goal)
                else:
                    raise VeriTException("comp_simplify", "unexpected lhs")
        # Case 2: a < a <--> false
        if lhs.is_less() and lhs.arg1 == lhs.arg and rhs == false:
            return Thm(goal)
        # Case 4: a <= a <--> true
        if lhs.is_less_eq() and lhs.arg1 == lhs.arg and rhs == true:
            return Thm(goal)
        # Case 5: a >= b <--> b <= a 
        if lhs.is_greater_eq():
            if not rhs.is_less_eq():
                raise VeriTException("comp_simplify", "rhs should be a less_eq when lhs is greater_eq")
            l_a, l_b = lhs.args
            r_a, r_b = rhs.args
            if l_a == r_b and l_b == r_a:
                return Thm(goal)
            else:
                raise VeriTException("comp_simplify", "can't match a >= b <--> b <= a")
        # Case 6: a < b <--> ~(b <= a)
        elif lhs.is_less():
            if not (rhs.is_not() and rhs.arg.is_less_eq()):
                raise VeriTException("comp_simplify", "rhs should be a less_eq when lhs is greater_eq")
            l_a, l_b = lhs.args
            r_a, r_b = rhs.arg.args
            if l_a == r_b and l_b == r_a:
                return Thm(goal)
            else:
                print("lhs", lhs, l_a, l_b)
                print("rhs", rhs, r_a, r_b)
                raise VeriTException("comp_simplify", "can't match a < b <--> ~(b <= a)")        
        # Case 7: a > b <--> ~(a <= b)
        elif lhs.is_greater():
            if not (rhs.is_not() and rhs.arg.is_less_eq()):
                raise VeriTException("comp_simplify", "rhs should be a less_eq when lhs is greater_eq")
            l_a, l_b = lhs.args
            r_a, r_b = rhs.arg.args
            if l_a == r_a and l_b == r_b:
                return Thm(goal)
            else:
                print("lhs", lhs, l_a, l_b)
                print("rhs", rhs, r_a, r_b)
                raise VeriTException("comp_simplify", "can't match a > b <--> ~(a <= b)")
        else:
            print("goal", goal)
            raise VeriTException("comp_simplify", "unexpected result")

    def get_proof_term(self, args, prevs) -> ProofTerm:
        goal = args[0]
        lhs, rhs = goal.args
        l_t1, l_t2 = lhs.args
        T = l_t1.get_type()
        assert T in (hol_type.IntType, hol_type.RealType)
        # case 1 and 3: compare constants
        if l_t1.is_number() and l_t2.is_number():
            if T == hol_type.IntType:
                pt = ProofTerm('int_const_ineq', lhs)
                if pt.prop.is_not():
                    pt = pt.on_prop(rewr_conv("eq_false"))
                else:
                    pt = pt.on_prop(rewr_conv("eq_true"))
            else:
                pt = ProofTerm('real_const_eq', lhs)
            if pt.prop == goal:
                return pt
        # case 2: x < x ⟷ false
        if lhs.is_less() and l_t1 == l_t2 and rhs == false:
            if T == hol_type.IntType:
                pt = logic.apply_theorem('verit_comp_simplify2', concl=goal)
            else:
                pt = logic.apply_theorem('verit_comp_simplify2_real', concl=goal)
        # case 4: x ≤ x ⟷ true
        elif lhs.is_less_eq() and l_t1 == l_t2 and rhs == true:
            if T == hol_type.IntType:
                pt = logic.apply_theorem('verit_comp_simplify4', concl=goal)
            else:
                pt = logic.apply_theorem('verit_comp_simplify4_real', concl=goal)
        # case 5: x ≥ y ⟷ y ≤ x
        elif lhs.is_greater_eq() and rhs.is_less_eq():
            if T == hol_type.IntType:
                pt = logic.apply_theorem('verit_comp_simplify5', concl=goal)
            else:
                pt = logic.apply_theorem('verit_comp_simplify5_real', concl=goal)
        # case 6: x < y ⟷ ¬(y ≤ x)
        elif lhs.is_less() and rhs.is_not() and rhs.arg.is_less_eq():
            if T == hol_type.IntType:
                pt = logic.apply_theorem('verit_comp_simplify6', concl=goal)
            else:
                pt = logic.apply_theorem('verit_comp_simplify6_real', concl=goal)
        # case 7: x > y ⟷ ¬(x ≤ y)
        elif lhs.is_greater() and rhs.is_not() and rhs.arg.is_less_eq():
            if T == hol_type.IntType:
                pt = logic.apply_theorem('verit_comp_simplify7', concl=goal)
            else:
                pt = logic.apply_theorem('verit_comp_simplify7_real', concl=goal)
        else:
            raise VeriTException("comp_simplify", "unexpected cases")
        if pt.prop == goal:
            return pt
        else:
            print("goal", goal)
            print("pt  ", pt)
            raise VeriTException("comp_simplify", "unexpected result")

@register_macro("verit_ite_simplify")
class ITESimplifyMacro(Macro):
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def compare_ite(self, ite1, ite2):
        if logic.is_if(ite1) and logic.is_if(ite2):
            l_P, l_then, l_else = ite1.args
            r_P, r_then, r_else = ite2.args

            # Case 4: ite ~P x y <--> ite P y x
            if l_P == Not(r_P) and l_then == r_else and l_else == r_then:
                return True
            # Case 7: ite P (ite P x y) z <--> ite P x z
            elif logic.is_if(l_then):
                l_then_P, l_then_then, _ = l_then.args
                if l_P == l_then_P and l_then_then == r_then and l_else == r_else:
                    return True
                else:
                    return False
            # Case 8: ite P x (ite P y z) <--> ite P x z
            elif logic.is_if(l_else):
                l_else_P, _, l_else_else = l_else.args
                if l_P == l_else_P and l_then == r_then and l_else_else == r_else:
                    return True
                else:
                    return False
            else:
                return False
        elif logic.is_if(ite1):
            l_P, l_then, l_else = ite1.args
            # Case 1: ite true x y <--> x (repeat case 5)
            if l_P == true and ite2 == l_then:
                return True
            # Case 2: ite false x y <--> y (repeat case 6)
            elif l_P == false and ite2 == l_else:
                return True
            # Case 3: ite P x x <--> x
            elif l_then == l_else and ite2 == l_then:
                return True
            # Case 9: ite P true false <--> P
            elif l_then == true and l_else == false and ite2 == l_P:
                return True
            # Case 10: ite P false true <--> ~P
            elif l_then == false and l_else == true and ite2 == Not(l_P):
                return True
            # Case 11: ite P true Q <--> P | Q
            elif l_then == true and ite2 == Or(l_P, l_else):
                return True
            # Case 12: ite P Q false <--> P & Q
            elif l_else == false and ite2 == And(l_P, l_then):
                return True
            # Case 13: ite P false Q <--> ~P & Q
            elif l_then == false and ite2 == And(Not(l_P), l_else):
                return True
            # Case 14: ite P Q true <--> ~P | Q
            elif l_else == true and ite2 == Or(Not(l_P), l_then):
                return True
            # case 15: ite ~P Q true <--> P | Q
            elif l_else == true and l_P.is_not() and ite2 == Or(l_P.arg, l_then):
                return True
            else:
                return False
        else:
            return False
            
    def compare_ite_thm(self, ite1, ite2) -> ProofTerm:
        goal = Eq(ite1, ite2)
        if logic.is_if(ite1) and logic.is_if(ite2):
            l_P, l_then, l_else = ite1.args
            r_P, r_then, r_else = ite2.args

            # Case 4: ite ~P x y <--> ite P y x
            if l_P == Not(r_P) and l_then == r_else and l_else == r_then:
                return logic.apply_theorem('verit_ite_simplify4', concl=goal)
            # Case 7: ite P (ite P x y) z <--> ite P x z
            elif logic.is_if(l_then):
                l_then_P, l_then_then, _ = l_then.args
                if l_P == l_then_P and l_then_then == r_then and l_else == r_else:
                    return logic.apply_theorem('verit_ite_simplify7', concl=goal)
                else:
                    return None
            # Case 8: ite P x (ite P y z) <--> ite P x z
            elif logic.is_if(l_else):
                l_else_P, _, l_else_else = l_else.args
                if l_P == l_else_P and l_then == r_then and l_else_else == r_else:
                    return logic.apply_theorem('verit_ite_simplify8', concl=goal)
                else:
                    return None
            else:
                return None
        elif logic.is_if(ite1):
            l_P, l_then, l_else = ite1.args
            # Case 1: ite true x y <--> x (repeat case 5)
            if l_P == true and ite2 == l_then:
                return logic.apply_theorem('verit_ite_simplify1', concl=goal)
            # Case 2: ite false x y <--> y (repeat case 6)
            elif l_P == false and ite2 == l_else:
                return logic.apply_theorem('verit_ite_simplify2', concl=goal)
            # Case 3: ite P x x <--> x
            elif l_then == l_else and ite2 == l_then:
                return logic.apply_theorem('verit_ite_simplify3', concl=goal)
            # Case 9: ite P true false <--> P
            elif l_then == true and l_else == false and ite2 == l_P:
                return logic.apply_theorem('verit_ite_simplify9', concl=goal)
            # Case 10: ite P false true <--> ~P
            elif l_then == false and l_else == true and ite2 == Not(l_P):
                return logic.apply_theorem('verit_ite_simplify10', concl=goal)
            # Case 11: ite P true Q <--> P | Q
            elif l_then == true and ite2 == Or(l_P, l_else):
                return logic.apply_theorem('verit_ite_simplify11', concl=goal)
            # Case 12: ite P Q false <--> P & Q
            elif l_else == false and ite2 == And(l_P, l_then):
                return logic.apply_theorem('verit_ite_simplify12', concl=goal)
            # Case 13: ite P false Q <--> ~P & Q
            elif l_then == false and ite2 == And(Not(l_P), l_else):
                return logic.apply_theorem('verit_ite_simplify13', concl=goal)
            # Case 14: ite P Q true <--> ~P | Q
            elif l_else == true and ite2 == Or(Not(l_P), l_then):
                return logic.apply_theorem('verit_ite_simplify14', concl=goal)
            # case 15: ite ~P Q true <--> P | Q
            elif l_else == true and l_P.is_not() and ite2 == Or(l_P.arg, l_then):
                return logic.apply_theorem('verit_ite_simplify15', concl=goal)
            else:
                return None
        else:
            return None

    def eval(self, args, prevs=None):
        if len(args) != 1:
            raise VeriTException("ite_simplify", "args should only contain one element")
        
        goal = args[0]
        if not goal.is_equals():
            raise VeriTException("ite_simplify", "goal should be an equality")
        
        lhs, rhs = goal.lhs, goal.rhs
        if self.compare_ite(lhs, rhs) or self.compare_ite(rhs, lhs):
            return Thm(goal)
        else:
            raise VeriTException("ite_simplify", "unexpected result")

    def get_proof_term(self, args, prevs) -> ProofTerm:
        goal = args[0]
        lhs, rhs = goal.lhs, goal.rhs
        pt_lhs_rhs = self.compare_ite_thm(lhs, rhs)
        if pt_lhs_rhs is not None and pt_lhs_rhs.prop == goal:
            return pt_lhs_rhs
        pt_rhs_lhs = self.compare_ite_thm(rhs, lhs)

        if pt_rhs_lhs is not None and pt_rhs_lhs.symmetric().prop == goal:
            return pt_rhs_lhs.symmetric()
        else:
            print("goal", goal)
            raise VeriTException("ite_simplify", "unexpected result")

@register_macro("verit_minus_simplify")
class MinusSimplify(Macro):
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def compare_tm(self, lhs, rhs):
        if lhs.is_minus() and lhs.arg1 == lhs.arg and rhs.is_zero():
            return True
        elif lhs.is_minus() and lhs.arg.is_zero() and lhs.arg1 == rhs:
            return True
        elif lhs.is_minus() and lhs.arg1.is_zero() and rhs.is_uminus() and rhs.arg == lhs.arg:
            return True
        elif rhs.is_uminus() and rhs.arg.is_uminus() and rhs.arg.arg == lhs: # bugs in veriT, f = --f
            return True
        else:
            return False

    def compare_tm_thm(self, lhs, rhs):
        T = lhs.get_type()
        if lhs.arg1 == lhs.arg and rhs.is_zero():
            if T == hol_type.IntType:
                return logic.apply_theorem('sub_diag', concl=Eq(lhs, rhs))
            else:
                return logic.apply_theorem('real_sub_refl', concl=Eq(lhs, rhs))
        if lhs.arg1 == rhs and lhs.arg.is_zero():
            if T == hol_type.IntType:
                return logic.apply_theorem('int_sub_n_0', concl=Eq(lhs, rhs))
            else:
                return logic.apply_theorem('real_sub_rzero', concl=Eq(lhs, rhs))
        elif rhs.is_uminus() and rhs.arg == lhs.arg and lhs.arg1.is_zero():
            if T == hol_type.IntType:
                return logic.apply_theorem('sub_0_l', concl=Eq(lhs, rhs))
            else:
                return logic.apply_theorem('real_zero_minus', concl=Eq(lhs, rhs))
        else:
            return None

    def eval(self, args, prevs=None):
        if not len(args) == 1:
            raise VeriTException("minus_simplify", "should only have one argument")
        goal = args[0]
        if not goal.is_equals():
            raise VeriTException("minus_simplify", "goal should be an equality")
        
        lhs, rhs = goal.args
        T = lhs.get_type()
        if lhs.is_constant() and rhs.is_constant(): # bugs in verit, it should be proved by uminus_simplify
            if T == hol_type.IntType and integer.int_eval(lhs) == integer.int_eval(rhs):
                return Thm(goal)
            elif T == hol_type.RealType and real.real_eval(lhs) == real.real_eval(rhs):
                return Thm(goal)
            else:
                raise VeriTException("minus_simplify", "unexpected result")

        if self.compare_tm(lhs, rhs):
            return Thm(goal)
        
        if self.compare_tm(rhs, lhs):
            return Thm(goal)

        print("goal", goal)
        raise VeriTException("minus_simplify", "unexpected result")

    def get_proof_term(self, args, prevs=None):
        goal = args[0]
        lhs, rhs = goal.args
        T = lhs.get_type()
        if T not in (hol_type.IntType, hol_type.RealType):
            raise VeriTException("minus_simplify", "unexpected numerical data type")
        if lhs.is_constant() and rhs.is_constant():
            if T == hol_type.IntType:
                macro_name = "int_eval"
            elif T == hol_type.RealType:
                macro_name = "real_eval"
                return ProofTerm("real_eval", goal)
            return ProofTerm(macro_name, Eq(lhs, rhs))

        if rhs.is_uminus() and rhs.arg.is_uminus() and rhs.arg.arg == lhs:
            if T == hol_type.IntType:
                return logic.apply_theorem('opp_involutive', concl=Eq(rhs, lhs)).symmetric()
            if T == hol_type.RealType:
                return logic.apply_theorem('real_neg_neg', concl=Eq(rhs, lhs)).symmetric()

        if lhs.is_minus():
            pt = self.compare_tm_thm(lhs, rhs)
            if pt is not None and pt.prop == goal:
                return pt
        if rhs.is_minus():
            pt = self.compare_tm_thm(rhs, lhs)
            if pt is not None and pt.prop == Eq(rhs, lhs):
                return pt.symmetric()
        print("goal", goal)
        raise VeriTException("minus_simplify", "unexpected result")
@register_macro("verit_unary_minus_simplify")
class UnaryMinusSimplifyMacro(Macro):
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
                return Thm(goal)
            else:
                raise VeriTException("minus_simplify", "-(-lhs) != lhs")
        elif lhs_neg_tm.is_constant():
            lhs_num = integer.int_eval(lhs)
            rhs_num = integer.int_eval(rhs)
            if  lhs_num == rhs_num:
                return Thm(goal)
            else:
                raise VeriTException("minus_simplify", "lhs and rhs should be equal after evaluation")
        else:
            raise VeriTException("minus_simplify", "unexpected result")

    def get_proof_term(self, args, prevs) -> ProofTerm:
        goal = args[0]
        lhs, rhs = goal.lhs, goal.rhs
        T = lhs.get_type()

        # case 1: --t = t
        if lhs.is_uminus() and lhs.arg.is_uminus() and lhs.arg.arg == rhs:
            if T == hol_type.IntType:
                return logic.apply_theorem("opp_involutive", concl=goal)
            if T == hol_type.RealType:
                return logic.apply_theorem("real_neg_neg", concl=goal)

        # case 2: -t = u
        if lhs.is_uminus() and lhs.is_constant() and rhs.is_constant():
            if T == hol_type.IntType:
                pt_lhs = refl(lhs).on_rhs(integer.int_eval_conv())
                pt_rhs = refl(rhs).on_rhs(integer.int_eval_conv())
                if pt_lhs.rhs == pt_rhs.rhs:
                    return pt_lhs.transitive(pt_rhs.symmetric())
            if T == hol_type.RealType:
                pt_lhs = refl(lhs).on_rhs(real.real_eval_conv())
                pt_rhs = refl(rhs).on_rhs(real.real_eval_conv())
                if pt_lhs.rhs == pt_rhs.rhs:
                    return pt_lhs.transitive(pt_rhs.symmetric())

        raise VeriTException("uminus_simplify", "unexpected result")

@register_macro("verit_connective_def")
class ConnectiveDefMacro(Macro):
    """Extension: the alethe document doesn't contain the following equality.
    
    ?x. P(x) <--> ~!x. ~P(x)
    """
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def eval(self, args, prevs=None):
        if len(args) != 1:
            raise VeriTException("connective_def", "should only contain one argument")
        goal = args[0]
        if not goal.is_equals():
            raise VeriTException("connective_def", "goal should be an equality")
        
        lhs, rhs = goal.args
        if lhs.is_equals():
            p1, p2 = lhs.args
            if rhs.is_conj() and rhs.arg1.is_implies() and rhs.arg.is_implies():
                q1, q2 = rhs.arg1.args
                o1, o2 = rhs.arg.args
                if q1 == p1 and o2 == p1 and p2 == q2 and p1 == o2:
                    return Thm(goal)
                else:
                    raise VeriTException("connective_def", "can't match  (p <--> q) <--> (p --> q) /\ (q --> p)")
            else:
                raise VeriTException("connective_def", "can't match (p <--> q) <--> (p --> q) /\ (q --> p)")
        elif logic.is_if(lhs): # alethe document has typos
            p1, p2, p3 = lhs.args # if p1 then p2 else p3
            if rhs.is_conj() and rhs.arg1.is_implies() and rhs.arg.is_implies():
                q1, q2 = rhs.arg1.args # p1 --> p2
                o1, o2 = rhs.arg.args # ~p1 --> p3
                if q1 == p1 and o1 == Not(p1) and p2 == q2 and o2 == p3:
                    return Thm(goal)
        elif lhs.is_exists() and rhs.is_not() and rhs.arg.is_forall():
            l_var, l_body = lhs.strip_exists()
            r_var, r_body = rhs.arg.strip_forall()
            if l_var == r_var and Not(l_body) == r_body:
                return Thm(goal)
            else:
                raise VeriTException("connective_def", "can't match ?x. P(x) <--> ~!x. ~P(x)")
        else:
            # print("lhs", lhs)
            # print("rhs", rhs)
            raise VeriTException("connective_def", "unexpected goals")
    
    def get_proof_term(self, args, prevs) -> ProofTerm:
        goal = args[0]
        if logic.is_xor(goal.lhs):
            return logic.apply_theorem('verit_connective_def1', concl=goal)
        elif goal.lhs.is_equals():
            return logic.apply_theorem('verit_connective_def2', concl=goal)
        elif logic.is_if(goal.lhs):
            return logic.apply_theorem('verit_connective_def3', concl=goal)
        elif goal.lhs.is_exists():
            pt = refl(goal.lhs).on_rhs(verit_conv.exists_forall_conv())
            if pt.prop == goal:
                return pt
        raise VeriTException("connective_def", "unexpected goal")

@register_macro("verit_bind")
class BindMacro(Macro):
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def eval(self, args, prevs):
        if len(args) != 2:
            raise VeriTException("bind", "should have two arguments")
        
        goal, ctx = args
        if not goal.is_equals():
            raise VeriTException("bind", "the first argument should be equality")
        if not isinstance(ctx, dict):
            raise VeriTException("bind", "the second argument should be a context")

        lhs, rhs = goal.args
        if not lhs.is_forall() and not lhs.is_exists():
            raise VeriTException("bind", "bind rules applies to quantifiers")

        if lhs.head() != rhs.head():
            raise VeriTException("bind", "lhs and rhs should have the same quantifier")

        if len(prevs) != 1:
            raise VeriTException("bind", "should have one premise")
        prem = prevs[0]
        if not prem.is_equals():
            raise VeriTException("bind", "premise should be an equality")

        l_vars, l_bd = [], lhs
        r_vars, r_bd = [], rhs
        if lhs.is_forall():
            while l_bd.is_forall() and l_bd != prem.lhs:
                x, l_bd = l_bd.arg.dest_abs()
                l_vars.append(x)
            while r_bd.is_forall() and r_bd != prem.rhs:
                x, r_bd = r_bd.arg.dest_abs()
                r_vars.append(x)
        else:  # lhs.is_exists()
            while l_bd.is_exists() and l_bd != prem.lhs:
                x, l_bd = l_bd.arg.dest_abs()
                l_vars.append(x)
            while r_bd.is_exists() and r_bd != prem.rhs:
                x, r_bd = r_bd.arg.dest_abs()
                r_vars.append(x)

        if not (prem.lhs == l_bd and prem.rhs == r_bd):
            print('prem', prem)
            print('goal', goal)
            raise VeriTException("bind", "unexpected result")

        if len(l_vars) != len(r_vars):
            raise VeriTException("bind", "lhs and rhs should have the same number of quantifiers")

        for lv, rv in zip(l_vars, r_vars):
            if not lv.is_var() or lv.name not in ctx or ctx[lv.name] != rv:
                print('prem', prem)
                print('goal', goal)
                raise VeriTException("bind", "can't map lhs quantified variables to rhs")

        remain_hyps = []
        for hyp in prem.hyps:
            if not (hyp.is_equals() and hyp.lhs in l_vars):
                remain_hyps.append(hyp)

        return Thm(goal, tuple(remain_hyps))

    def get_proof_term(self, args, prevs) -> ProofTerm:
        goal, ctx = args
        lhs, rhs = goal.lhs, goal.rhs

        prem = prevs[0]

        # The hypotheses that can be used include those in hyps of prem, whose
        # left side does not appear in the quantifiers of goal.lhs.
        if lhs.is_forall():
            l_vars, _ = lhs.strip_forall()
        else:  # lhs.is_exists()
            l_vars, _ = lhs.strip_exists()

        eq_pts = dict()
        eq_pts[(prem.lhs, prem.rhs)] = prem
        for hyp in prem.hyps:
            if hyp.is_equals() and hyp.lhs not in l_vars:
                eq_pts[(hyp.lhs, hyp.rhs)] = ProofTerm.assume(hyp)

        pt = compare_sym_tm_thm(lhs, rhs, eqs=eq_pts)

        if pt is not None:
            res = ProofTerm("transitive", None, [ProofTerm.reflexive(lhs), pt])
            return res

        print(lhs)
        print(rhs)
        for k, v in ctx.items():
            print(k, v)
        prem = prevs[0]
        print(prem.th)
        raise VeriTException("bind", "unexpected result")


@register_macro("verit_forall_inst")
class ForallInstMacro(Macro):
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def eval(self, args, prevs=None):
        goal = args[0]
        if not goal.is_disj():
            print("goal", goal)
            print("goal.arg", goal.arg)
            raise VeriTException("forall_inst", "goal should be a disjunction")
        neg_tm, inst_tm = goal.args
        if not neg_tm.is_not() or not neg_tm.arg.is_forall():
            print("neg_tm", neg_tm)
            raise VeriTException("forall_inst", "unexpected argument")

        forall_tm = neg_tm.arg
        dct = {k: v for k, v in args[1:]}
        while forall_tm.is_forall():
            forall_tm = forall_tm.arg.subst_bound(dct[forall_tm.arg.var_name])
        if forall_tm == inst_tm:
            return Thm(goal)
        elif compare_sym_tm(forall_tm, inst_tm):
            return Thm(goal)
        else:
            print("forall_tm", forall_tm)
            print("rhs", inst_tm)
            raise VeriTException("forall_inst", "unexpected result")

    def get_proof_term(self, args, prevs) -> ProofTerm:
        goal = args[0]
        forall_tm, inst_tm = goal.arg1.arg, goal.arg
        pt = ProofTerm.assume(forall_tm)
        dct = {k: v for k, v in args[1:]}
        while pt.prop.is_forall():
            pt = pt.forall_elim(dct[pt.prop.arg.var_name])        
        pt = pt.implies_intr(forall_tm).on_prop(rewr_conv('imp_disj_eq'))
        if pt.prop == goal:
            return pt
        else:
            eq_pt = compare_sym_tm_thm(pt.prop, goal)
            return eq_pt.equal_elim(pt)

@register_macro("verit_implies_pos")
class ImpliesPosMacro(Macro):
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def eval(self, args, prevs=None):
        if not len(args) == 3:
            raise VeriTException("implies_pos", "should have three arguments")
        arg1, arg2, arg3 = args
        if not (arg1.is_not() and arg1.arg.is_implies() and arg2.is_not()):
            raise VeriTException("implies_pos", "unexpected arguments")
        arg1_p1, arg1_p2 = arg1.arg.args
        arg2_p1 = arg2.arg
        if arg1_p1 == arg2_p1 and arg1_p2 == arg3:
            return Thm(Or(*args))
        else:
            raise VeriTException("implies_pos", "unexpected result")

    def get_proof_term(self, args, prevs) -> ProofTerm:
        return logic.apply_theorem('verit_implies_pos', concl=Or(*args))
        

@register_macro("verit_implies_simplify")
class ImpliesSimplifyMacro(Macro):
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def eval(self, args, prevs=None):
        if not len(args) == 1 or not args[0].is_equals() or not args[0].lhs.is_implies():
            raise VeriTException("implies_simplify", "goal should be an equality and lhs should be an implication")
        goal = args[0]
        lhs, rhs = goal.args
        prem, concl = lhs.args
        # case 1: (~p1 --> ~p2) <--> (p2 --> p1)
        if lhs.is_implies() and rhs.is_implies():
            p1, p2 = lhs.args
            q1, q2 = rhs.args
            if p1 == Not(q2) and p2 == Not(q1):
                return Thm(goal)
        # case 2: (false --> P) <--> true
        if prem == false and rhs ==  true:
            return Thm(goal)
        # case 3 (p --> true) --> true
        elif concl == true and concl == rhs:
            return Thm(goal)
        # case 4: (p1 --> p1) <--> true
        elif prem == true and concl == rhs:
            return Thm(goal)
        # case 5: (p1 --> false) <--> ~p1
        elif concl == false and Not(prem) == rhs:
            return Thm(goal)
        # case 6: (P --> P) <--> true
        elif prem == concl and rhs == true:
            return Thm(goal)
        # case 7: (~P --> P) <--> P
        elif prem == Not(concl) and rhs == concl:
            return Thm(goal)
        # case 8: (P --> ~P) <--> ~P
        elif concl == Not(prem) and rhs == concl:
            return Thm(goal)
        # case 9: (P --> Q) --> Q <--> P | Q
        elif prem.is_implies() and rhs.is_disj() and prem.arg1.is_implies() \
                and prem.arg1.arg1 == rhs.arg1 and prem.arg1.arg == prem.arg \
                    and prem.arg == rhs.arg:
            return Thm(goal)
        else:
            print("goal", goal)
            raise VeriTException("implies_simplify", "unexpected goal")

    def get_proof_term(self, args, prevs) -> ProofTerm:
        goal = args[0]
        lhs, rhs = goal.args
        prem, concl = lhs.args
        # case 1: (~p1 --> ~p2) <--> (p2 --> p1)
        if lhs.is_implies() and rhs.is_implies():
            p1, p2 = lhs.args
            q1, q2 = rhs.args
            if p1 == Not(q2) and p2 == Not(q1):
                return logic.apply_theorem('verit_imp_simplify1', concl=goal)
        # case 2: (false --> P) <--> true
        if prem == false and rhs ==  true:
            return logic.apply_theorem('verit_imp_simplify2', concl=goal)
        # case 3 (p --> true) --> true
        elif concl == true and concl == rhs:
            return logic.apply_theorem('verit_imp_simplify3', concl=goal)
        # case 4: (p1 --> p1) <--> true
        elif prem == true and concl == rhs:
            return logic.apply_theorem('verit_imp_simplify4', concl=goal)
        # case 5: (p1 --> false) <--> ~p1
        elif concl == false and Not(prem) == rhs:
            return logic.apply_theorem('verit_imp_simplify5', concl=goal)
        # case 6: (P --> P) <--> true
        elif prem == concl and rhs == true:
            return logic.apply_theorem('verit_imp_simplify6', concl=goal)
        # case 7: (~P --> P) <--> P
        elif prem == Not(concl) and rhs == concl:
            return logic.apply_theorem('verit_imp_simplify7', concl=goal)
        # case 8: (P --> ~P) <--> ~P
        elif concl == Not(prem) and rhs == concl:
            return logic.apply_theorem('verit_imp_simplify8', concl=goal)
        # case 9: (P --> Q) --> Q <--> P | Q
        elif prem.is_implies() and rhs.is_disj() and prem.arg1.is_implies() \
                and prem.arg1.arg1 == rhs.arg1 and prem.arg1.arg == prem.arg \
                    and prem.arg == rhs.arg:
            return logic.apply_theorem('verit_imp_simplify9', concl=goal)
        else:
            print("goal", goal)
            raise VeriTException("implies_simplify", "unexpected goal")


@register_macro("verit_ite_pos1")
class ITEPos2Macro(Macro):
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def eval(self, args, prevs=None):
        if not len(args) == 3:
            raise VeriTException("ite_pos1", "should have three arguments")
        arg1, arg2, arg3 = args
        if not (arg1.is_not() and logic.is_if(arg1.arg)):
            raise VeriTException("ite_pos1", "unexpected arguments")
        p1, _, p3 = arg1.arg.args
        if p1 == arg2 and p3 == arg3:
            return Thm(Or(*args))
        else:
            raise VeriTException("ite_pos1", "unexpected result")

    def get_proof_term(self, args, prevs=None):
        return logic.apply_theorem("verit_ite_pos1", concl=Or(*args))

@register_macro("verit_ite_pos2")
class ITEPos2Macro(Macro):
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def eval(self, args, prevs=None):
        if not len(args) == 3:
            raise VeriTException("ite_pos2", "should have three arguments")
        arg1, arg2, arg3 = args
        if not (arg1.is_not() and logic.is_if(arg1.arg) and arg2.is_not()):
            raise VeriTException("ite_pos2", "unexpected arguments")
        p1, p2, p3 = arg1.arg.args
        q1 = arg2.arg
        if p1 == q1 and p2 == arg3:
            return Thm(Or(*args))
        else:
            raise VeriTException("ite_pos2", "unexpected results")

    def get_proof_term(self, args, prevs=None):
        return logic.apply_theorem("verit_ite_pos2", concl=Or(*args))

@register_macro("verit_ite_neg1")
class ITEPos2Macro(Macro):
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def eval(self, args, prevs=None):
        if not len(args) == 3:
            raise VeriTException("ite_neg1", "should have three arguments")
        arg1, arg2, arg3 = args
        if not logic.is_if(arg1) or not arg3.is_not():
            raise VeriTException("ite_neg1", "unexpected arguments")
        p1, _, p3 = arg1.args
        if p1 == arg2 and Not(p3) == arg3:
            return Thm(Or(*args))
        else:
            raise VeriTException("ite_neg1", "unexpected result")

    def get_proof_term(self, args, prevs=None):
        return logic.apply_theorem("verit_ite_neg1", concl=Or(*args))

@register_macro("verit_ite_neg2")
class ITEPos2Macro(Macro):
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def eval(self, args, prevs=None):
        if not len(args) == 3:
            raise VeriTException("ite_neg2", "should have three arguments")
        arg1, arg2, arg3 = args
        if not logic.is_if(arg1) or not arg2.is_not() or not arg3.is_not():
            raise VeriTException("ite_neg2", "unexpected arguments")
        p1, p2, _ = arg1.args
        if Not(p1) == arg2 and Not(p2) == arg3:
            return Thm(Or(*args))
        else:
            raise VeriTException("ite_neg2", "unexpected results")

    def get_proof_term(self, args, prevs=None):
        return logic.apply_theorem("verit_ite_neg2", concl=Or(*args))


@register_macro("verit_subproof")
class SubProofMacro(Macro):
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def eval(self, args, prevs=None):
        if len(args) <= 1:
            raise VeriTException("subproof", "should contain more than one args")
        if len(prevs) == 0:
            raise VeriTException("subproof", "prevs should have at least one proof term")
        if len(args) != len(prevs):
            raise VeriTException("subproof", "args and prevs should have the same number of arguments")

        props = [pt.prop for pt in prevs]
        input_prop = props[:-1]
        concl = props[-1]
        goal_neg_tms = args[:-1]
        goal_concl = args[-1]
        if all(g == Not(p) for g, p in zip(goal_neg_tms, input_prop)) and goal_concl == concl:
            return Thm(Or(*args))
        else:
            raise VeriTException("subproof", "unexpected result")

    def get_proof_term(self, args, prevs) -> ProofTerm:
        pt = prevs[-1]
        for prev in reversed(prevs[:-1]):
            pt = pt.implies_intr(prev.prop).on_prop(rewr_conv('imp_disj_eq'))
        return pt


@register_macro("verit_sko_ex")
class SkoExMacro(Macro):
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def eval(self, args, prevs):
        if len(args) != 2:
            raise VeriTException("sko_ex", "expected two arguments")
        goal, ctx = args
        if not goal.is_equals():
            raise VeriTException("sko_ex", "goal should be an equality")
        if not isinstance(ctx, dict):
            raise VeriTException("sko_ex", "the second argument should be a mapping")
        
        lhs, rhs = goal.args
        if not lhs.is_exists():
            raise VeriTException("sko_ex", "lhs should be an exist quantification")
        
        if len(prevs) != 1:
            raise VeriTException("sko_ex", "expected one prev")

        pt = prevs[0]
        if pt.rhs != rhs:
            raise VeriTException("sko_ex", "rhs should be equal to pt's rhs")

        xs, lhs_body = lhs.strip_exists()

        if pt.lhs != lhs_body:
            print('pt.lhs:', pt.lhs)
            print('lhs_body:', lhs_body)
            raise VeriTException("sko_ex", "unexpected form of lhs in goal")

        eq_ctx = set()
        for k, v in ctx.items():
            vT = v.get_type()
            eq_ctx.add((Var(k, vT), v))

        for i, x in enumerate(xs):
            if x.name not in ctx:
                raise VeriTException("sko_ex", "the skolem variable does not occur in context")
            sko_tm_x = ctx[x.name]
            if not logic.is_some(sko_tm_x):
                raise VeriTException("sko_ex", "%s should be a skolemization term" % sko_tm_x)
            _, sko_tm_x_body = sko_tm_x.arg.dest_abs()

            # Body of skolem term for x should equal lhs_body after adding exists
            # quantifiers to all ensuing variables.
            exp_x_body = Exists(*(xs[i+1:] + [lhs_body]))
            if not compare_sym_tm(sko_tm_x_body, exp_x_body, ctx=eq_ctx):
                print('sko_tm_body:', sko_tm_x_body)
                print('exp_x_body:', exp_x_body)
                raise VeriTException("sko_ex", "unexpected result")

        remain_hyps = []
        for hyp in prevs[0].hyps:
            if not (hyp.is_equals() and hyp.lhs in xs):
                remain_hyps.append(hyp)
        return Thm(goal, tuple(remain_hyps))

    def get_proof_term(self, args, prevs) -> ProofTerm:
        goal, ctx = args
        lhs, rhs = goal.args
        xs, lhs_body = lhs.strip_exists()

        pt = prevs[0]

        eqs = dict()
        for hyp in pt.hyps:
            if hyp.is_equals():
                eqs[(hyp.lhs, hyp.rhs)] = ProofTerm.assume(hyp)

        for x in reversed(xs):
            # Obtain equality for x
            found_hyp = None
            for hyp in pt.hyps:
                if hyp.is_equals() and hyp.lhs == x:
                    found_hyp = hyp
                    break
            if found_hyp is None:
                raise VeriTException("sko_ex", "hypothesis not found")
            del eqs[(found_hyp.lhs, found_hyp.rhs)]
            # t has the form SOME x. P x
            t = found_hyp.rhs
            # Save left side as P
            P = Lambda(x, pt.lhs)
            # Introduce assumption x = t, then replace x by t
            inst = Inst()
            inst.var_inst[x.name] = t
            pt = pt.implies_intr(found_hyp).substitution(inst)
            # Discharge assumption t = t using reflexivity
            pt = pt.implies_elim(ProofTerm.reflexive(t))
            # Rewrite using P (SOME x. P x) <--> (EX x. P x), may need to use some of
            # the other equality hypotheses.
            Some_eq = logic.apply_theorem('verit_some_eq_ex', inst=Inst(P=P))
            eq_pt = compare_sym_tm_thm(Some_eq.lhs, pt.lhs, eqs=eqs)
            pt = ProofTerm.transitive(Some_eq.symmetric(), eq_pt, pt)
        return pt


@register_macro("verit_sko_forall")
class SkoForallMacro(Macro):
    """Prove an equality of the form !x1, ..., xn. p <--> q, given fact
    p <--> q proved under the context
        x1 -> SOME x1. ~p, ..., xn -> SOME xn. ~p.

    """
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def eval(self, args, prevs):
        if len(args) != 2:
            raise VeriTException("sko_forall", "expected two arguments")
        goal, ctx = args
        if not goal.is_equals():
            raise VeriTException("sko_forall", "goal should be an equality")
        if not isinstance(ctx, dict):
            raise VeriTException("sko_forall", "the second argument should be a mapping")
        
        lhs, rhs = goal.args
        if not lhs.is_forall():
            raise VeriTException("sko_forall", "lhs should be an exist quantification")
        
        if len(prevs) != 1:
            raise VeriTException("sko_forall", "expected one prev")

        pt = prevs[0]
        if pt.rhs != rhs:
            raise VeriTException("sko_forall", "rhs should be equal to pt's rhs")

        xs, lhs_body = lhs.strip_forall()

        if pt.lhs != lhs_body:
            print('pt.lhs:', pt.lhs)
            print('lhs_body:', lhs_body)
            raise VeriTException("sko_forall", "unexpected form of lhs in goal")

        eq_ctx = set()
        for k, v in ctx.items():
            vT = v.get_type()
            eq_ctx.add((Var(k, vT), v))

        for i, x in enumerate(xs):
            if x.name not in ctx:
                raise VeriTException("sko_forall", "the skolem variable does not occur in context")
            sko_tm_x = ctx[x.name]
            if not logic.is_some(sko_tm_x):
                raise VeriTException("sko_forall", "%s should be a skolemization term" % sko_tm_x)
            _, sko_tm_x_body = sko_tm_x.arg.dest_abs()

            # Body of skolem term for x should equal lhs_body after adding forall
            # quantifiers to all ensuing variables.
            exp_x_body = Not(Forall(*(xs[i+1:] + [lhs_body])))
            if not compare_sym_tm(sko_tm_x_body, exp_x_body, ctx=eq_ctx):
                print('sko_tm_body:', sko_tm_x_body)
                print('exp_x_body:', exp_x_body)
                raise VeriTException("sko_forall", "unexpected result")

        remain_hyps = []
        for hyp in prevs[0].hyps:
            if not (hyp.is_equals() and hyp.lhs in xs):
                remain_hyps.append(hyp)
        return Thm(goal, tuple(remain_hyps))

    def get_proof_term(self, args, prevs) -> ProofTerm:
        goal, ctx = args
        lhs, rhs = goal.args
        xs, lhs_body = lhs.strip_forall()

        pt = prevs[0]

        eqs = dict()
        for hyp in pt.hyps:
            if hyp.is_equals():
                eqs[(hyp.lhs, hyp.rhs)] = ProofTerm.assume(hyp)

        for x in reversed(xs):
            # Obtain equality for x
            found_hyp = None
            for hyp in pt.hyps:
                if hyp.is_equals() and hyp.lhs == x:
                    found_hyp = hyp
                    break
            if found_hyp is None:
                raise VeriTException("sko_all", "hypothesis not found")
            del eqs[(found_hyp.lhs, found_hyp.rhs)]
            # t has the form SOME x. ~P x.
            t = found_hyp.rhs
            # Save left side as P
            P = Lambda(x, pt.lhs)
            # Introduce assumption x = t, then replace x by t
            inst = Inst()
            inst.var_inst[x.name] = t
            pt = pt.implies_intr(found_hyp).substitution(inst)
            # Discharge assumption t = t using reflexivity
            pt = pt.implies_elim(ProofTerm.reflexive(t))
            # Rewrite using P (SOME x. ~P x) <--> (ALL x. P x), may need to use some of
            # the other equality hypotheses.
            Some_eq = logic.apply_theorem('verit_some_neg_eq_all', inst=Inst(P=P))
            eq_pt = compare_sym_tm_thm(Some_eq.lhs, pt.lhs, eqs=eqs)
            pt = ProofTerm.transitive(Some_eq.symmetric(), eq_pt, pt)
        return pt


def check_onepoint(goal, ctx):
    """Check the validity of goal for the onepoint rule. If check passes,
    return information needed to reconstruct the proof.
    
    """
    lhs, rhs = goal.args

    # Deconstruct quantifiers at lhs and rhs
    if lhs.is_forall():
        is_forall = True
        l_vars, l_bd = lhs.strip_forall()
        r_vars, r_bd = rhs.strip_forall()
    elif lhs.is_exists():
        is_forall = False
        l_vars, l_bd = lhs.strip_exists()
        r_vars, r_bd = rhs.strip_exists()
    else:
        raise VeriTException("onepoint", "left side is not forall or exists")

    if len(l_vars) < len(r_vars):
        raise VeriTException("onepoint", "unexpected number of quantified variables")

    # Discover variables with one value
    one_val_var = dict()
    remain_var = []
    for v in l_vars:
        if v.is_var() and v.name in ctx and ctx[v.name] != v and ctx[v.name].get_type() == v.get_type():
            one_val_var[v] = ctx[v.name]
        else:
            remain_var.append(v)
    if remain_var != r_vars:
        raise VeriTException("onepoint", "lhs doesn't keep the same variables as rhs")

    # Substituting left side by the equations must yield the right side
    subst_lhs = l_bd
    for v, tm in one_val_var.items():
        T = tm.get_type()
        subst_lhs = hol_term.Abs(v.name, T, subst_lhs.abstract_over(v)).subst_bound(tm)

    if not compare_sym_tm(subst_lhs, r_bd):
        raise VeriTException("onepoint", "unexpected result")

    # For each variable with one value, check for corresponding equality
    # in the body of lhs.
    if is_forall:
        # body must be in implies form, with each equation in the premise
        if l_bd.is_implies():
            assms, concl = l_bd.strip_implies()
            conjs = []
            for assm in assms:
                conjs.extend(assm.strip_conj())
            for v, t in one_val_var.items():
                found = False
                for i, conj in enumerate(conjs):
                    if conj.is_equals() and conj.lhs == v:
                        found = True
                        break
                    if conj.is_equals() and conj.rhs == v:
                        found = True
                        break
                if concl.is_not() and concl.arg.is_equals() and concl.arg.lhs == v:
                    found = True
                    break
                if concl.is_not() and concl.arg.is_equals() and concl.arg.rhs == v:
                    found = True
                    break
                if not found:
                    raise VeriTException("onepoint", "forall - equation not found")
            return "FORALL-DISJ", l_bd, one_val_var, remain_var
        elif l_bd.is_disj():
            disjs = l_bd.strip_disj()
            for v, t in one_val_var.items():
                found = False
                for i, disj in enumerate(disjs):
                    if disj.is_not() and disj.arg.is_equals() and disj.arg.lhs == v:
                        found = True
                        break
                    if disj.is_not() and disj.arg.is_equals() and disj.arg.rhs == v:
                        found = True
                        break
                if not found:
                    raise VeriTException("onepoint", "forall - equation not found")
            return "FORALL-DISJ", l_bd, one_val_var, remain_var
        elif l_bd.is_not() and l_bd.arg.is_conj():
            conjs = l_bd.arg.strip_conj()
            for v, t in one_val_var.items():
                found = False
                for i, conj in enumerate(conjs):
                    if conj.is_equals() and conj.lhs == v:
                        found = True
                        break
                    if conj.is_equals() and conj.rhs == v:
                        found = True
                        break
                if not found:
                    raise VeriTException("onepoint", "forall - equation not found")
            return "FORALL-DISJ", l_bd, one_val_var, remain_var
        else:
            raise VeriTException("onepoint", "forall - body is neither implies nor disjunction")
    else:
        # body must be in conjunction form, with each equation as a conjunct
        conjs = l_bd.strip_conj()
        for v, t in one_val_var.items():
            for i, conj in enumerate(conjs):
                if conj.is_equals() and conj.lhs == v:
                    found = True
                    break
                if conj.is_equals() and conj.rhs == v:
                    found = True
                    conjs[i] = Eq(conj.rhs, conj.lhs)
                    break
            if not found:
                raise VeriTException("onepoint", "exists - equation not found")
        return "EXISTS-CONJ", conjs, one_val_var, remain_var

@register_macro("verit_onepoint")
class OnepointMacro(Macro):
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def eval(self, args, prevs):
        goal, ctx = args
        check_onepoint(goal, ctx)
        return Thm(goal)

    def get_proof_term(self, args, prevs) -> ProofTerm:
        goal, ctx = args
        onepoint_type, info, one_val_var, remain_var = check_onepoint(goal, ctx)
        one_val_var = tuple(one_val_var.items())
        if onepoint_type == "FORALL-DISJ":
            cur_t_eq = ProofTerm.reflexive(info).on_rhs(verit_conv.norm_to_disj_conv())
            cur_t = cur_t_eq.rhs
            for x, _ in one_val_var:
                cur_t = Forall(x, cur_t)
            pt = ProofTerm.reflexive(cur_t).on_rhs(verit_conv.onepoint_forall_conv())
            for x in remain_var:
                pt = ProofTerm.reflexive(hol_term.forall(x.T)).combination(pt.abstraction(x))
            
            # Reorder the foralls 
            goal_lhs_xs, _ = goal.lhs.strip_forall()
            eq_lhs = verit_conv.forall_reorder_iff(pt.lhs, goal_lhs_xs)
            goal_rhs_xs, goal_rhs = goal.rhs.strip_forall()
            eq_rhs = verit_conv.forall_reorder_iff(pt.rhs, goal_rhs_xs)
            pt = pt.on_lhs(replace_conv(eq_lhs)).on_rhs(replace_conv(eq_rhs))

            goal_rhs_eq = ProofTerm.reflexive(goal_rhs).on_rhs(verit_conv.norm_to_disj_conv())
            _, pt_rhs = pt.rhs.strip_forall()
            goal_rhs_eq2 = compare_sym_tm_thm(goal_rhs_eq.rhs, pt_rhs)
            goal_rhs_eq = ProofTerm.transitive(goal_rhs_eq, goal_rhs_eq2)
            eqs = dict()
            eqs[(cur_t_eq.lhs, cur_t_eq.rhs)] = cur_t_eq
            eqs[(goal_rhs_eq.lhs, goal_rhs_eq.rhs)] = goal_rhs_eq
            eq_pt = compare_sym_tm_thm(pt.prop, goal, eqs=eqs)
            if eq_pt is None:
                print('pt', pt.th)
                print('goal', goal)
                raise AssertionError
            return eq_pt.equal_elim(pt)
        elif onepoint_type == "EXISTS-CONJ":
            cur_t = And(*info)
            for x, _ in one_val_var:
                cur_t = Exists(x, cur_t)
            pt = ProofTerm.reflexive(cur_t).on_rhs(verit_conv.onepoint_exists_conv())
            for x in remain_var:
                pt = ProofTerm.reflexive(hol_term.exists(x.T)).combination(pt.abstraction(x))
            
            goal_lhs_xs, _ = goal.lhs.strip_exists()
            eq_lhs = verit_conv.exists_reorder_iff(pt.lhs, goal_lhs_xs)
            goal_rhs_xs, _ = goal.rhs.strip_exists()
            eq_rhs = verit_conv.exists_reorder_iff(pt.rhs, goal_rhs_xs)
            pt = pt.on_lhs(replace_conv(eq_lhs)).on_rhs(replace_conv(eq_rhs))
            eq_pt = compare_sym_tm_thm(pt.prop, goal)
            if eq_pt is None:
                print('pt', pt.th)
                print('goal', goal)
                raise AssertionError
            return eq_pt.equal_elim(pt)
        else:
            raise VeriTException("onepoint", "unrecognized type")


def get_cnf(t: Term) -> Term:
    """Obtain the CNF form of t."""
    if t.is_not():
        if t.arg.is_not():
            # ~~A becomes A
            return get_cnf(t.arg.arg)
        elif t.arg.is_disj():
            # ~(A1 \/ ... \/ An) becomes ~A1 /\ ... /\ ~An
            disjs = t.arg.strip_disj()
            conjs = [Not(disj) for disj in disjs]
            return get_cnf(And(*conjs))
        elif t.arg.is_conj():
            # ~(A1 /\ ... /\ An) becomes ~A1 \/ ... \/ ~An
            conjs = t.arg.strip_conj()
            disjs = [Not(conj) for conj in conjs]
            return get_cnf(Or(*disjs))
        elif t.arg.is_implies():
            # ~(A --> B) becomes A & ~B
            A, B = t.arg.args
            return get_cnf(And(A, Not(B)))
        elif t.arg.is_equals() and t.arg.arg1.get_type() == BoolType:
            # ~(A <--> B) becomes (A & ~B) | (~A & B)
            A, B = t.arg.lhs, t.arg.rhs
            return get_cnf(Or(And(A, Not(B)), And(B, Not(A))))
        elif logic.is_if(t.arg) and t.arg.args[1].get_type() == BoolType:
            # ~(if P then Q else R) becomes (P & ~Q) | (~P & R)
            P, Q, R = t.arg.args
            return get_cnf(Or(And(P, Not(Q)), And(Not(P), R)))
        else:
            return t
    elif t.is_disj():
        # To compute CNF form of a disjunction, first compute CNF of
        # each of the disjuncts.
        disjs = t.strip_disj()
        cnf_disjs = [get_cnf(disj) for disj in disjs]

        # Expand CNF of each disjunct into a conjunction
        cnf_disj_conjs = []
        for disj in cnf_disjs:
            cnf_disj_conjs.append(disj.strip_conj())

        # For each combination, form the corresponding disjunction
        cnf_res = []
        for element in itertools.product(*cnf_disj_conjs):
            cur_disj = []
            for t in element:
                cur_disj.extend(t.strip_disj())
            cnf_res.append(Or(*cur_disj))
        return And(*cnf_res)
    elif t.is_conj():
        # To compute CNF form of a conjunction, first compute CNF of
        # each of the conjuncts
        conjs = t.strip_conj()
        cnf_conjs = [get_cnf(conj) for conj in conjs]

        # Expand CNF of each conjunct into a conjunction
        cnf_res = []
        for t in cnf_conjs:
            cnf_res.extend(t.strip_conj())
        return And(*cnf_res)
    elif t.is_implies():
        # A --> B becomes ~A | B
        A, B = t.args
        return get_cnf(Or(Not(A), B))
    elif t.is_equals() and t.arg.get_type() == BoolType:
        # A <--> B becomes (~A | B) & (~B | A)
        A, B = t.lhs, t.rhs
        return get_cnf(And(Or(Not(A), B), Or(Not(B), A)))
    elif logic.is_if(t) and t.args[1].get_type() == BoolType:
        # (if P then Q else R) becomes (~P | Q) & (P | R)
        P, Q, R = t.args
        return get_cnf(And(Or(Not(P), Q), Or(P, R)))
    elif t.is_forall():
        x, body = t.arg.dest_abs()
        return get_cnf(body)
    else:
        return t


@register_macro("verit_qnt_cnf")
class QntCnfMacro(Macro):
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def eval(self, args, prevs):
        if len(args) != 1:
            raise VeriTException("qnt_cnt", "clause should contain one term")
        arg = args[0]
        if not arg.is_disj() or not arg.arg1.is_not():
            raise VeriTException("qnt_cnt", "clause should be of the form ~P | Q")

        prem, concl = arg.arg1.arg, arg.arg
        
        xs, body = prem.strip_forall()
        cnf_body = get_cnf(body)

        ys, concl_body = concl.strip_forall()

        cnf_body_conjs = cnf_body.strip_conj()
        if any(concl_body == t for t in cnf_body_conjs):
            return Thm(arg)

        print("args")
        for arg in args:
            print(arg)
        print('cnf_body_conjs')
        for conj in cnf_body_conjs:
            print(conj)
        print('concl_body')
        print(concl_body)
        raise NotImplementedError

    def get_proof_term(self, args, prevs) -> ProofTerm:
        goal = args[0]
        prem, concl = goal.arg1.arg, goal.arg

        # Obtain the CNF form of premise in the form prem |- CNF(prem)
        prem_pt = ProofTerm.assume(prem).on_prop(verit_conv.cnf_conv())

        # Next, clear the forall quantifiers and find the required conjunct
        while prem_pt.prop.is_forall():
            x, _ = prem_pt.prop.arg.dest_abs()
            prem_pt = prem_pt.forall_elim(x)
        
        # The conclusion is also cleared of forall quantifiers, collecting the
        # quantified variables
        xs = []
        while concl.is_forall():
            x, concl = concl.arg.dest_abs()
            xs.append(x)

        # Now find the conclusion among the clauses of prem_pt
        try:
            concl_pt = verit_and_single(prem_pt, concl)
        except VeriTException:
            # print('prem')
            # print(prem)
            # print('clauses')
            # for clause in prem_pt.prop.strip_conj():
            #     print(clause)
            print('concl')
            print(concl)
            raise AssertionError

        # Re-introduce the forall quantifiers
        for x in reversed(xs):
            concl_pt = concl_pt.forall_intr(x)
        
        # Finally, form the implication prem -> concl and rewrite to ~prem \/ concl
        return concl_pt.implies_intr(prem).on_prop(rewr_conv('disj_conv_imp', sym=True))


@register_macro("verit_equiv_simplify")
class BoolSimplifyMacro(Macro):
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def get_proof_term(self, args, prevs):
        goal = args[0]
        if not goal.is_equals():
            raise VeriTException("equiv_simplify", "goal should be an equality")
        lhs, rhs = goal.args
        if not lhs.is_equals():
            raise VeriTException("equiv_simplify", "lhs should be an equality")
        # case 1
        if rhs.is_equals() and lhs.lhs == Not(rhs.lhs) and lhs.rhs == Not(rhs.rhs):
            return logic.apply_theorem("verit_equiv_simplify1", concl=goal)
        # case 2
        elif lhs.lhs == lhs.rhs and rhs == true:
            return logic.apply_theorem("verit_equiv_simplify2", concl=goal)
        # case 3
        elif Not(lhs.lhs) == lhs.rhs and rhs == false:
            return logic.apply_theorem("verit_equiv_simplify3", concl=goal)
        # case 4
        elif Not(lhs.rhs) == lhs.lhs and rhs == false:
            return logic.apply_theorem("verit_equiv_simplify4", concl=goal)
        # case 5
        elif lhs.lhs == true and lhs.rhs == rhs:
            return logic.apply_theorem("verit_equiv_simplify5", concl=goal)
        # case 6
        elif lhs.rhs == true and lhs.lhs == rhs:
            return logic.apply_theorem("verit_equiv_simplify6", concl=goal)
        # case 7
        elif Not(lhs.rhs) == rhs and lhs.lhs == false:
            return logic.apply_theorem("verit_equiv_simplify7", concl=goal)
        # case 8
        elif Not(lhs.lhs) == rhs and lhs.rhs == false:
            return logic.apply_theorem("verit_equiv_simplify8", concl=goal)
        else:
            raise VeriTException("equiv_simplify", "unexpected goal")

@register_macro("verit_not_implies1")
class NotImplies1Macro(Macro):
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def get_proof_term(self, args, prevs):
        goal = args[0]
        prop = prevs[0].prop
        if not prop.is_not() or not prop.arg.is_implies():
            raise VeriTException("not_implie1s", "unexpected prevs")

        if goal != prop.arg.arg1:
            raise VeriTException("not_implies1", "unexpected argument")
        
        return logic.apply_theorem("not_implies1", prevs[0])

@register_macro("verit_not_implies2")
class NotImplies2Macro(Macro):
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def get_proof_term(self, args, prevs):
        goal = args[0]
        prop = prevs[0].prop
        if not prop.is_not() or not prop.arg.is_implies():
            raise VeriTException("not_implies2", "unexpected argument")

        if goal != Not(prop.arg.arg):
            raise VeriTException("not_implies2", "unexpected argument")
        
        return logic.apply_theorem("not_implies2", prevs[0])

@register_macro("verit_implies_neg1")
class ImpliesNeg1Macro(Macro):
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def eval(self, args, prevs):
        if len(args) != 2 or not args[0].is_implies() or args[0].arg1 != args[1]:
            raise VeriTException("implies_neg1", "unexpected arguments")
        return Thm(Or(*args))

    def get_proof_term(self, args, prevs=None):
        return logic.apply_theorem("verit_implies_neg1", concl=Or(*args))

@register_macro("verit_implies_neg2")
class ImpliesNeg1Macro(Macro):
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def eval(self, args, prevs):
        if len(args) != 2 or not args[0].is_implies() or Not(args[0].arg) != args[1]:
            raise VeriTException("implies_neg2", "unexpected arguments")
        return Thm(Or(*args))

    def get_proof_term(self, args, prevs=None):
        return logic.apply_theorem("verit_implies_neg2", concl=Or(*args))

@register_macro("verit_qnt_simplify")
class QNTSimplifyMacro(Macro):
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def eval(self, args, prevs=None):
        if len(args) != 1 or not args[0].is_equals():
            raise VeriTException("qnt_simplify", "unexpected arguments")
        goal = args[0]
        lhs, rhs = goal.args
        if rhs not in (true, false):
            raise VeriTException("qnf_simplify", "rhs should be true or false")

        if not lhs.is_forall():
            raise VeriTException("qnf_simplify", "lhs should be a quantification")
        
        _, l_bd = lhs.strip_forall()
        if l_bd == rhs:
            return Thm(goal)
        else:
            raise VeriTException("qnf_simplify", "unexpected result")

    def get_proof_term(self, args, prevs):
        goal = args[0]
        lhs, rhs = goal.args
        vars, _ = lhs.strip_forall()
        pt1 = ProofTerm.assume(lhs)
        for v in vars:
            pt1 = pt1.forall_elim(v)
        pt1 = pt1.implies_intr(lhs)
        pt2 = ProofTerm.assume(rhs)
        for v in vars:
            pt2 = pt2.forall_intr(v)
        pt2 = pt2.implies_intr(rhs)
        return logic.apply_theorem("iffI", pt1, pt2)

@register_macro("verit_qnt_join")
class QNTJoinMacro(Macro):
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def eval(self, args, prevs=None):
        if len(args) != 1:
            raise VeriTException("qnt_join", "should have only one argument")
        goal = args[0]
        if not goal.is_equals():
            raise VeriTException("qnt_join", "goal should be an equality")
        
        lhs, rhs = goal.args
        if lhs != rhs:
            raise VeriTException("qnt_join", "implementation is incomplete")

        return Thm(Eq(args[0].lhs, args[0].rhs))

    def get_proof_term(self, args, prevs):
        return logic.apply_theorem("eq_refl", concl=args[0])

@register_macro("verit_equiv_neg1")
class EquivNeg1Macro(Macro):
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def eval(self, args, prevs=None):
        if len(args) != 3:
            raise VeriTException("equiv_neg1", "unexpected number of arguments")
        
        eq, p1, p2 = args
        if not eq.is_equals():
            raise VeriTException("equiv_neg1", "the first argument should be an equality")

        lhs, rhs = eq.args
        if p1 == Not(lhs) and p2 == Not(rhs):
            return Thm(Or(*args))
        else:
            raise VeriTException("equiv_neg1", "unexpected result")

    def get_proof_term(self, args, prevs):
        return logic.apply_theorem("equiv_neg1", concl=Or(*args))

@register_macro("verit_equiv_neg2")
class EquivNeg1Macro(Macro):
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def eval(self, args, prevs=None):
        if len(args) != 3:
            raise VeriTException("equiv_neg2", "unexpected number of arguments")
        
        eq, p1, p2 = args
        if not eq.is_equals():
            raise VeriTException("equiv_neg2", "the first argument should be an equality")

        lhs, rhs = eq.args
        if p1 == lhs and p2 == rhs:
            return Thm(Or(*args))
        else:
            raise VeriTException("equiv_neg2", "unexpected result")

    def get_proof_term(self, args, prevs):
        return logic.apply_theorem("equiv_neg2", concl=Or(*args))


@register_macro("verit_la_rw_eq")
class LaRwEqMacro(Macro):
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def eval(self, args, prevs=None):
        if len(args) != 1:
            raise VeriTException("la_rw_eq", "unexpected number of arguments")
        goal = args[0]
        if not goal.is_equals():
            raise VeriTException("la_rw_eq", "goal should be an equality")
        lhs, rhs = goal.args
        if not lhs.is_equals():
            raise VeriTException("la_rw_eq", "lhs should be an equality")
        t, u = lhs.args
        if not rhs.is_conj() or not rhs.arg1.is_less_eq() or not rhs.arg.is_less_eq():
            raise VeriTException("la_rw_eq", "rhs should be a conjunction of two less_eq term")
        less_eq1, less_eq2 = rhs.args
        # (t = u) <--> (t <= u) & (u <= t)
        if t == less_eq1.arg1 and t == less_eq2.arg and u == less_eq1.arg and u == less_eq2.arg1:
            return Thm(goal)
        else:
            raise VeriTException("la_rw_eq", "unexpected result")

    def get_proof_term(self, args, prevs=None):
        goal = args[0]
        lhs, rhs = goal.args
        t, u = lhs.args
        less_eq1, less_eq2 = rhs.args
        T = t.get_type()
        if T not in (hol_type.IntType, hol_type.RealType):
            raise VeriTException("la_rw_eq", "unexpected data type")

        # (t = u) <--> (t <= u) & (u <= t)
        if t == less_eq1.arg1 and t == less_eq2.arg and u == less_eq1.arg and u == less_eq2.arg1:
            if T == hol_type.IntType:
                return logic.apply_theorem("verit_lw_rw_eq_int", concl=goal)
            else:
                return logic.apply_theorem("verit_lw_rw_eq_real", concl=goal)
        else:
            raise VeriTException("la_rw_eq", "unexpected result")

@register_macro("verit_qnt_rm_unused")
class QntRmUnusedMacro(Macro):
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def eval(self, args, prevs=None) -> Thm:
        if not len(args) == 1 or not args[0].is_equals():
            raise VeriTException("qnt_rm_unused", "argument should be an equality term")
        
        goal = args[0]
        lhs, rhs = goal.args
        if not lhs.is_forall() and not lhs.is_exists():
            raise VeriTException("qnt_rm_unused", "lhs should have a quantifier")
        l_vars, l_bd = lhs.strip_quant()
        if rhs.is_forall() or rhs.is_exists():
            r_vars, r_bd = rhs.strip_quant()
        else:
            r_vars, r_bd = [], rhs
        free_vars = []
        if l_bd != r_bd:
            print("lhs", lhs)
            print("rhs", rhs)
            raise VeriTException("qnt_rm_unused", "lhs and rhs body are not equal")
        
        for l in l_vars:
            if l not in r_vars:
                if r_bd.occurs_var(l):
                    raise VeriTException("qnt_rm_unused", "a free variable was removed")
            else:
                free_vars.append(l)

        if free_vars != r_vars:
            raise VeriTException("qnt_rm_unused", "after removing unused vars in lhs, \
                                    lhs and rhs still have different quantified variables")
        
        return Thm(goal)    

    def get_proof_term(self, args, prevs) -> ProofTerm:
        goal = args[0]
        pt = refl(goal.lhs).on_rhs(verit_conv.qnt_rm_unsed_conv())
        if pt.prop == goal:
            return pt
        raise VeriTException("qnt_rm_unused", "unexpected result %s" % goal)

@register_macro("verit_prod_simplify")
class ProdSimplifyMacro(Macro):
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def eval(self, args, prevs=None) -> Thm:
        if len(args) != 1 or not args[0].is_equals():
            raise VeriTException("prod_simplify", "argument should be an equality")
        
        goal = args[0]
        lhs, rhs = goal.args

        if not lhs.is_times() and not rhs.is_times():
            raise VeriTException("prod_simplify", "neither side of equality is product")

        if not lhs.is_times() and rhs.is_times():
            lhs, rhs = rhs, lhs

        T = lhs.get_type()
        if T == hol_type.IntType:
            hol_eval = integer.int_eval
        elif T == hol_type.RealType:
            hol_eval = real.real_eval
        else:
            raise VeriTException("prod_simplify", "unsupported data type")

        lhs_prods = integer.strip_times_full(lhs)
        # case 1: t1 * t2 * ... * tn = u if all ti are constants and u is the product
        if all(p.is_number() for p in lhs_prods) and rhs.is_number():
            if hol_eval(lhs) == hol_eval(rhs):
                return Thm(goal)

        # case 2: t1 * t2 * ... * tn = 0 if any ti is zero
        if rhs.is_zero() and any(p.is_zero() for p in lhs_prods):
            return Thm(goal)

        rhs_prods = integer.strip_times_full(rhs)
        lhs_consts = [hol_eval(p) for p in lhs_prods if p.is_number()]
        assert len(lhs_consts) > 0
        lhs_c = functools.reduce(operator.mul, lhs_consts[1:], lhs_consts[0])
        rhs_consts = [hol_eval(p) for p in rhs_prods if p.is_number()]
        if len(rhs_consts) > 0:
            rhs_c = functools.reduce(operator.mul, rhs_consts[1:], rhs_consts[0])
        else:
            rhs_c = 1
        lhs_tms = [p for p in lhs_prods if not p.is_number()]
        rhs_tms = [p for p in rhs_prods if not p.is_number()]
        if lhs_c == rhs_c and lhs_tms == rhs_tms:
            return Thm(goal)
        else:
            raise VeriTException('prod_simplify', 'unexpected result')

    def get_proof_term(self, args, prevs) -> ProofTerm:
        goal = args[0]
        lhs, rhs = goal.args

        if not lhs.is_times() and rhs.is_times():
            lhs, rhs = rhs, lhs

        T = lhs.get_type()
        if T == hol_type.IntType:
            eval_conv = integer.int_eval_conv()
            norm_conv = integer.int_norm_conv()
        elif T == hol_type.RealType:
            eval_conv = real.real_eval_conv()
            norm_conv = real.real_norm_conv()
        else:
            raise VeriTException("prod_simplify", "unsupported data type")

        if lhs.is_constant() and rhs.is_constant():
            pt = refl(lhs).on_rhs(eval_conv)
            if pt.prop == goal:
                return pt
            elif pt.symmetric().prop == goal:
                return pt.symmetric()
            else:
                raise VeriTException('prod_simplify', "unexpected result")

        pt_lhs = refl(lhs).on_rhs(norm_conv)
        pt_rhs = refl(rhs).on_rhs(norm_conv)
        if pt_lhs.rhs == pt_rhs.rhs:
            pt_eq = pt_lhs.transitive(pt_rhs.symmetric())
            if pt_eq.prop == goal:
                return pt_eq
            elif pt_eq.symmetric().prop == goal:
                return pt_eq.symmetric()
            else:
                raise VeriTException('prod_simplify', "unexpected result")

        print("goal", goal)
        raise AssertionError


@register_macro('verit_div_simplify')
class DivSimplifyMacro(Macro):
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def eval(self, args, prevs=None) -> Thm:
        if len(args) != 1 or not args[0].is_equals() or not args[0].lhs.is_divides():
            raise VeriTException('div_simplify', "goal should be an equality whose lhs is a division")

        goal = args[0]
        lhs, rhs = goal.args
        # case 1: t / t <--> 1
        if lhs.arg1 == lhs.arg and rhs.is_one():
            return Thm(goal)
        # case 2: t / 1 <--> t
        if lhs.arg1 == rhs and lhs.arg.is_one():
            return Thm(goal)
        if not lhs.is_constant() or not rhs.is_constant():
            raise VeriTException('div_simplify', "both lhs and rhs should be constants")
        T = lhs.get_type()
        if T == hol_type.IntType:
            rhs_val = integer.int_eval(rhs)
            lhs_num = integer.int_eval(lhs.arg1)
            lhs_denom = integer.int_eval(lhs.arg)
            if lhs_num // lhs_denom == rhs_val:
                return Thm(goal)
            else:
                raise VeriTException('div_simplify', "integer division error")
        elif T == hol_type.RealType:
            lhs_val = real.real_eval(lhs)
            rhs_val = real.real_eval(rhs)
            if lhs_val == rhs_val:
                return Thm(goal)
            else:
                raise VeriTException('div_simplify', "real number division error")
        else:
            raise VeriTException('div_simplify', 'unspported number type')

    def get_proof_term(self, args, prevs) -> ProofTerm:
        goal = args[0]
        lhs, rhs = goal.args
        T = lhs.get_type()
        if T == hol_type.IntType:
            raise VeriTException('div_simplify', "integer division is not supported now")

        denom = lhs.arg
        pt_denom = ProofTerm('real_const_eq', 
                    Eq(denom, hol_term.Real(0))).on_prop(rewr_conv('eq_false', sym=True))
        # case 1: t / t <--> 1
        # note: should check zero division
        if lhs.arg1 == lhs.arg and rhs.is_one():
            pt = logic.apply_theorem('real_div_refl', pt_denom)
            if pt.prop == goal:
                return pt
            else:
                raise VeriTException('div_simplify', "unexpected result")
        # case 2: t / 1 <--> t
        elif lhs.arg1 == rhs and lhs.arg.is_one():
            return logic.apply_theorem('real_div_1', concl=goal)
        


        pt = refl(lhs).on_rhs(real.real_eval_conv())
        if pt.prop == goal:
            return pt
        
        raise VeriTException('div_simplify', "unexpected result")

@register_macro('verit_xor_pos1')
class XORPos1Macro(Macro):
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def eval(self, args, prevs=None) -> Thm:
        # prove ~(xor t1 t2) | t1 | t2
        if len(args) != 3:
            raise VeriTException('xor_pos1', "should have three arguments")
        
        P, Q, R = args
        if not P.is_not() or not logic.is_xor(P.arg):
            raise VeriTException('xor_pos1', "arguments can't match goal")
        
        P_t1, P_t2 = P.arg.args
        if P_t1 == Q and P_t2 == R:
            return Thm(Or(*args))

        raise VeriTException('xor_pos1', "unexpected result")

    def get_proof_term(self, args, prevs) -> ProofTerm:
        return logic.apply_theorem('verit_xor_pos1', concl=Or(*args))

@register_macro('verit_xor_pos2')
class XORPos2Macro(Macro):
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def eval(self, args, prevs=None) -> Thm:
        # prove ~(xor t1 t2) | ~t1 | ~t2
        if len(args) != 3:
            raise VeriTException('xor_pos2', "should have three arguments")
        
        P, Q, R = args
        if not P.is_not() or not logic.is_xor(P.arg) or not \
            Q.is_not() or not R.is_not():
            raise VeriTException('xor_pos2', "arguments can't match goal")
        
        P_t1, P_t2 = P.arg.args
        if Not(P_t1) == Q and Not(P_t2) == R:
            return Thm(Or(*args))

        raise VeriTException('xor_pos2', "unexpected result")

    def get_proof_term(self, args, prevs) -> ProofTerm:
        return logic.apply_theorem('verit_xor_pos2', concl=Or(*args))
@register_macro('verit_xor_neg1')
class XORNeg1Macro(Macro):
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def eval(self, args, prevs=None) -> Thm:
        # prove (xor t1 t2) | t1 | ~t2
        if len(args) != 3:
            raise VeriTException('xor_neg1', "should have three arguments")
        
        P, Q, R = args
        if not logic.is_xor(P) or not R.is_not():
            raise VeriTException('xor_neg1', "arguments can't match goal")
        
        P_t1, P_t2 = P.args
        if P_t1 == Q and Not(P_t2) == R:
            return Thm(Or(*args))

        raise VeriTException('xor_neg1', "unexpected result")

    def get_proof_term(self, args, prevs) -> ProofTerm:
        return logic.apply_theorem('verit_xor_neg1', concl=Or(*args))

@register_macro('verit_xor_neg2')
class XORNeg2Macro(Macro):
    def __init__(self):
        self.level = 1
        self.sig = Term
        self.limit = None

    def eval(self, args, prevs=None) -> Thm:
        # prove (xor t1 t2) | ~t1 | t2
        if len(args) != 3:
            raise VeriTException('xor_neg2', "should have three arguments")
        
        P, Q, R = args
        if not logic.is_xor(P) or not Q.is_not():
            raise VeriTException('xor_neg2', "arguments can't match goal")
        
        P_t1, P_t2 = P.args
        if Not(P_t1) == Q and P_t2 == R:
            return Thm(Or(*args))

        raise VeriTException('xor_neg2', "unexpected result")

    def get_proof_term(self, args, prevs) -> ProofTerm:
        return logic.apply_theorem('verit_xor_neg2', concl=Or(*args))
