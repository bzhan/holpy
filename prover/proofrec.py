"""
Z3 proof reconstruction.
Reference: Fast LCF-Style Proof Reconstruction for Z3
by Sascha Böhme and Tjark Weber.
"""

import z3
from z3.z3consts import *
from data.integer import int_norm_macro
from kernel.type import TFun, BoolType, NatType, IntType, RealType, STVar, TVar
from kernel.term import *
from kernel.thm import Thm
from kernel.proofterm import ProofTerm
from kernel.macro import Macro
from kernel.theory import check_proof, register_macro
from kernel import theory
from logic import basic, context, matcher
from logic.logic import apply_theorem, imp_disj_iff, disj_norm
from logic.tactic import rewrite_goal_with_prev
from logic.conv import rewr_conv, try_conv, top_conv
# from syntax.settings import settings
# settings.unicode = True
from collections import deque
import functools
import operator
import json
import time

# Z3 proof method name.
method = ('mp', 'mp~', 'asserted', 'trans', 'monotonicity', 'rewrite', 'and-elim', 'not-or-elim',
            'iff-true', 'iff-false', 'unit-resolution', 'commutativity', 'def-intro', 'apply-def',
            'def-axiom', 'iff~', 'nnf-pos', 'nnf-neg', 'sk', 'proof-bind', 'quant-inst', 'quant-intro',
            'lemma', 'hypothesis', 'symm', 'refl', 'apply-def', 'intro-def', 'th-lemma')


def index_and_relation(proof):
    """Index all terms in z3 proof and get the relation between the terms."""
    s = dict()
    id = 0
    def rec(term, parent=None):
        nonlocal id
        if term in s.keys() and parent != None:
            s[parent][1].append(s[term][0])
        else:
            s[term] = [id, []]
            if parent is not None:
                s[parent][1].append(id)
            id += 1
            if not z3.is_quantifier(term):
                for child in term.children():
                    rec(child, term)
    rec(proof)
    return {value[0]: key for key, value in s.items()}, {value[0]: value[1] for key, value in s.items()}

def DepthFirstOrder(G):
    """Traverse graph in reversed DFS order."""
    reversePost = deque()
    marked = [False for i in range(len(G))]
    
    def dfs(G, v):
        marked[v] = True
        for w in G[v]:
            if not marked[w]:
                dfs(G, w)
        reversePost.append(v)

    for v in G.keys():
        if not marked[v]:
            dfs(G, v)
    
    return reversePost

def lambda_to_quantifier(l, forall=True):
    """
    Give a term of abs:
    λ x1, x2, ... x_k. L
    if forall is true: return 
    """
    def helper(l):
        if l.is_abs():
            return [Var(l.var_name, l.var_T)] + helper(l.body)
        else:
            return []
    
    var = helper(l)

    for v in reversed(var):
        l = l.subst_bound(v)

    for v in reversed(var):
        l = Forall(v, l) if forall else Exists(v, l)

    return l

def lambda_var(l):
    """
    Give a lambda expression λ x1 x2 ... xk. f
    Return [(x1, T1), (x2, T2), ... , (xk, tk)]
    """
    if l.is_abs():
        return [(l.var_name, l.var_T)] + lambda_var(l.body)
    else:
        return []

def forall_body(t, vars):
    """
    Give a term of comb:
    Return a forall expression which use vars as bounded variable.
    """
    pass

def arity(l):
    """
    Give a lambda term %x1 x2 ... xn. body
    return n
    """
    return 1 + arity(l.body) if l.is_abs() else 0

def translate_type(sort):
    """Translate z3 type into holpy type."""
    T = sort.kind()
    if T == Z3_BOOL_SORT:
        return BoolType
    elif T == Z3_INT_SORT:
        return IntType
    elif T == Z3_REAL_SORT:
        return RealType
    elif T == Z3_UNINTERPRETED_SORT:
        return TVar(sort.name())
    else:
        raise NotImplementedError

def translate(term, bounds=deque()):
    """Transalte z3 term into holpy term.
       bounds represents bounded variables, key is de-Bruijn index of the var, value is the bounded variable already in holpy.
    """
    if z3.is_func_decl(term): # z3 function, including name, sort of each arguments, constant is function with 0 arg.
        arity = term.arity()
        rangeT = translate_type(term.range())
        domainT = [translate_type(term.domain(i)) for i in range(arity)]
        types = domainT + [rangeT]
        return Var(term.name(), TFun(*types))
    elif z3.is_quantifier(term): 
        body = term.body()
        var = tuple(Var(term.var_name(i), translate_type(term.var_sort(i))) for i in range(term.num_vars()))
        for v in var:
            bounds.appendleft(v)
        # patterns = tuple(term.patterns(i) for i in range(term.num_patterns()))
        if term.is_lambda():
            if body.decl().name() == 'refl':
                lhs = translate(body.arg(0).arg(0), bounds)
                return ProofTerm.reflexive(Lambda(*var, lhs))
            elif body.decl().name() in method:
                subst_var = [z3.Const(term.var_name(term.num_vars()-1-i), term.var_sort(term.num_vars()-1-i)) for i in range(term.num_vars())]
                prf = proofrec(z3.substitute_vars(body, *subst_var), bounds=bounds)
                bounds.clear()
                for v in reversed(var):
                    prf = prf.abstraction(v)
                return prf
            else:
                raise NotImplementedError
            l = Lambda(*var, translate(body, bounds))
            bounds.clear()
            return l
        elif term.is_exists():
            e = Exists(*var, translate(body, bounds))
            bounds.clear()
            return e
        elif term.is_forall():
            f = Forall(*var, translate(body, bounds))
            bounds.clear()
            return f
        else:
            raise NotImplementedError
    elif z3.is_expr(term):
        if z3.is_var(term):
            return bounds[z3.get_var_index(term)]
        kind = term.decl().kind() # term function application
        sort = translate_type(term.sort()) # term sort
        args = tuple(translate(term.arg(i), bounds) for i in range(term.num_args()))
        if z3.is_int_value(term): # int number
            return Int(term.as_long())
        elif z3.is_rational_value(term): # Return `True` if term is rational value of sort Real
            return Real(term.as_fraction())
        elif z3.is_algebraic_value(term): # a number
            return Real(term.as_fraction())
        elif z3.is_true(term):
            return true
        elif z3.is_false(term):
            return false
        elif z3.is_const(term): 
            # incomplete, is_const(Int(1)) == true, but Int(1) have already been
            # translated above
            if term.decl().name() in local.keys():
                return local[term.decl().name()]
            return Var(term.decl().name(), sort)
        elif z3.is_add(term):
            return functools.reduce(lambda x, y: x + y, args)
        elif term.decl().kind() == Z3_OP_UMINUS:
            return uminus(sort)(*args)
        elif z3.is_sub(term):
            return functools.reduce(lambda x, y: x - y, args)
        elif z3.is_mul(term):
            return functools.reduce(lambda x, y: x * y, args)
        elif z3.is_div(term) or z3.is_idiv(term):
            return divides(sort)(*args)
        elif z3.is_eq(term):
            return Eq(*args)
        elif z3.is_and(term):
            return And(*args)
        elif z3.is_or(term):
            return Or(*args)
        elif z3.is_implies(term):
            return Implies(*args)
        elif z3.is_not(term):
            return Not(*args)
        elif z3.is_lt(term):
            return less(args[0].get_type())(*args)
        elif z3.is_le(term):
            return less_eq(args[0].get_type())(*args)
        elif z3.is_gt(term):
            return greater(args[0].get_type())(*args)
        elif z3.is_ge(term):
            return greater_eq(args[0].get_type())(*args)
        elif z3.is_distinct(term):
            ineq = [Eq(translate(args[i], bounds), translate(args[j]), bounds) for j in range(i+1, len(args)) 
                        for i in range(len(args))]
            return Not(Or(*ineq))
        elif kind == Z3_OP_ITE:
            cond, stat1, stat2 = translate(term.arg(0)), translate(term.arg(1)), translate(term.arg(2))
            T = stat1.get_type() # stat1 and stat2 must have same type
            return Const('IF', TFun(BoolType, T, T, T))(cond, stat1, stat2)
        elif kind == Z3_OP_UNINTERPRETED: # s(0)
            uf = translate(term.decl(), bounds)
            args = [translate(term.arg(i), bounds) for i in range(term.num_args())]
            return uf(*args)
        elif z3.is_bool(term) and kind == Z3_OP_OEQ: # "~"" operator in z3 is ambiguous
            return Eq(translate(term.arg(0)), translate(term.arg(1)))
        else:
            raise NotImplementedError
    else:
        raise NotImplementedError

def and_elim(pt, concl):
    context.set_context('logic_base')
    r = dict()
    def rec(pt):
        if pt.prop == concl:
            r[pt.prop] = pt
        elif pt.prop.is_conj():
            rec(apply_theorem('conjD1', pt))
            rec(apply_theorem('conjD2', pt))
        else:
            r[pt.prop] = pt
    rec(pt)
    return r[concl]

def monotonicity(pts, concl):
    """
    f = g, x1 = y1, x2 = y2, ..., xn = yn
    =====================================
        f(x1,...,xn) = g(y1,...,yn)

    Note: In HOL, disj and conj are both binary right-associative operators,
    but in z3, they are polyadic, so if f and g are disj/conj, the
    first thing is to abstract over the bool var in them to get the real 
    f and g. If f and g are not disj and conj, we can easily get the fun
    by calling specific method(*.fun). 

    After getting f and g, the next thing is to find x1...xn and y1...yn, although
    z3 has provided some equality instances like above, but when xk = yk, it will 
    ignore the equality(even when f=g), so we need to find out them. This can be done by ranging
    over the last argument f(x1,...,xn). If f and g are disj or conj, we can easily 
    get them by "strip_disj()/strip_conj()" method. Or else we can use "strip_comb()"
    method to get them.

    As soon as we've collected all necessary stuff, we can reconstrcut the proof by
    recursively using combination rule.

    There is a special case for conj and disj, for example: the provided equality is
    B∨C = C∨B, and we want to prove A∨B∨C = A∨C∨B, it is inappropriate to use strip_disj(),
    because disj is right-associate, we have no chance to get complete B∨C term. So we need
    to implemented custom strip_disj()/strip_conj() method.

    The translate process have bugs(∧,∨ are polyadic), that's why disj and conj are special.
    """

    def get_argument(f):
        """
        Suppose f is f x1 x2 x3, return [x1, x2, x3]
        """
        _, fx = f.strip_comb()
        return fx

    # First get f, g.
    f_expr, g_expr = concl.lhs, concl.rhs
    if not f_expr.is_disj() and not f_expr.is_conj():
        f, g = f_expr.head, g_expr.head

        # Next collect arguments: x1...xn/y1...yn
        # We can't split the term in pts into subterms.
        fx, gy = get_argument(f_expr), get_argument(g_expr)
        # Then put all useful equalities proofterm in equalities.
        equalities = []
        if f == g:
            equalities.append(ProofTerm.reflexive(f))
            index = 0
        else:
            index = 1

        for x, y in zip(fx, gy):
            if x == y: # z3 not provide it
                equalities.append(ProofTerm.reflexive(x))
            else:
                equalities.append(pts[index])
                index += 1

        # use combination get final proof
        return functools.reduce(lambda f, x : f.combination(x), equalities)
    else:
        eq_prop = concl # f x1 x2 ... xk ~ f y1 y2 ... yk
        eq_hyps = pts
        assert eq_prop.lhs.head == eq_prop.rhs.head
        head = eq_prop.lhs.head
        head_arity = arity(head)
        # collect xi ~ yi
        lhs_param, rhs_param = [], []
        eq_assms_lhs = [p.prop.lhs for p in eq_hyps]
        eq_assms_rhs = [p.prop.rhs for p in eq_hyps]

        def rec(p, param, known_eq):
            if p in known_eq:
                param.append(p)
            elif p.head == head:
                param.append(p.args[0])
                if len(p.args) > 1:
                    rec(p.args[1], param, known_eq)
            elif p.head != head:
                param.append(p)

        rec(eq_prop.lhs, lhs_param, eq_assms_lhs)
        rec(eq_prop.rhs, rhs_param, eq_assms_rhs)

        pt_concl = ProofTerm.reflexive(head)
        index = 0
        
        eq_pts = deque()
        
        for l, r in zip(lhs_param, rhs_param):
            if l != r:
                eq_pts.appendleft(eq_hyps[index])
                index += 1
            else:
                eq_pts.appendleft(ProofTerm.reflexive(l))
        pt1 = eq_pts[0]
        if len(eq_pts) == 1:
            return pt_concl.combination(eq_pts[0])
        for i in range(len(eq_pts) - 1):
            for j in range(head_arity - 1):
                pt_left = pt_concl.combination()
            pt1 = pt_concl.combination(eq_pts[i+1]).combination(pt1)

        return pt1
    

def schematic_rules_rewr(thms, lhs, rhs):
    """Rewrite by instantiating schematic theorems."""
    context.set_context('smt')
    for thm in thms:
        context.set_context('smt')
        pt = ProofTerm.theorem(thm)
        try:
            inst1 = matcher.first_order_match(pt.prop.lhs, lhs)
            inst2 = matcher.first_order_match(pt.prop.rhs, rhs, inst=inst1)
            return pt.substitution(inst1)
        except matcher.MatchException:
            continue
    return None

def rewrite(t):
    def norm_int(t):
        """Use nat norm macro to normalize nat expression."""
        # context.set_context('int')
        # print("t: ", t)
        # assert t.is_equals() and t.lhs.get_type() == IntType and t.rhs.get_type() == IntType
        return int_norm_macro().get_proof_term(t, [])

    def equal_is_true(pt):
        """pt is ⊢ x = y, return: ⊢ (x = y) ↔ true"""
        context.set_context('logic_base')
        pt0 = apply_theorem('trueI') # ⊢ true
        pt1 = pt0.implies_intr(pt.prop) # ⊢ (x = y) → true
        pt2 = pt.implies_intr(pt0.prop) # ⊢ true → (x = y)
        return ProofTerm.equal_intr(pt1, pt2)

    if t.lhs == t.rhs:
        return ProofTerm.reflexive(t.lhs)

    # first try use schematic theorems
    with open('library/smt.json', 'r', encoding='utf-8') as f:
        f_data = json.load(f)
    th_name = [f_data['content'][i]['name'] for i in range(len(f_data['content'])) if f_data['content'][i]['name'][0]=='r']
    pt = schematic_rules_rewr(th_name, t.lhs, t.rhs)  # rewrite by schematic theorems 
    if pt is None:
        if t.rhs == true and t.lhs.is_equals(): # prove ⊢ (x = y) ↔ true
            eq = t.lhs
            if eq.lhs.get_type() == IntType: # Maybe can reuse schematic theorems to prove ⊢ (x = y) in further
                pt_eq = norm_int(eq)
                return equal_is_true(pt_eq)
            else:
                raise NotImplementedError
        elif t.is_equals(): # Equations that can't match with schematic theorems
            # Try nat norm macro:
            if t.lhs.get_type() == IntType:
                return norm_int(t)
            else:
                return ProofTerm.sorry(Thm([], t))
        else:
            raise NotImplementedError
    else:
        return pt  

def norm_nnf(term):
    # incomplete
    def rec(pt):
        fm = pt.prop
        if fm.is_conj():
            pt1 = rec(ProofTerm.assume(fm.arg1)).implies_intr(fm.arg1) 
            pt2 = rec(ProofTerm.assume(fm.arg)).implies_intr(fm.arg)
            pt3 = apply_theorem('conjD1', pt)
            pt4 = apply_theorem('conjD2', pt)
            pt5 = pt1.implies_elim(pt3)
            pt6 = pt2.implies_elim(pt4)
            return apply_theorem('conjI', pt5, pt6)
        elif fm.is_disj():
            pt1 = rec(ProofTerm.assume(fm.arg1))
            pt2 = rec(ProofTerm.assume(fm.arg))
            pt3 = apply_theorem('disjI1', pt1, inst=Inst(B=pt2.prop))
            pt4 = apply_theorem('disjI2', pt2, inst=Inst(A=pt1.prop))
            pt5 = apply_theorem('disjE', pt, pt3.implies_intr(pt3.hyps[0]), pt4.implies_intr(pt4.hyps[0]))
            return pt5
        elif fm.is_implies():
            pt1 = apply_theorem('disj_conv_imp', inst=Inst(A=fm.arg1, B=fm.arg))
            pt2 = pt1.symmetric()
            return rec(pt2.equal_elim(pt))
        elif fm.is_not():
            p = fm.arg
            if p.is_not():
                pt1 = apply_theorem('double_neg', inst=Inst(A=p.arg))
                return rec(pt1.equal_elim(pt))
            elif p.is_conj():
                pt1 = apply_theorem('de_morgan_thm1', inst=Inst(A=p.arg1, B=p.arg))
                pt7 = pt1.equal_elim(pt)
                pt2 = rec(ProofTerm.assume(pt7.prop.arg1))
                pt3 = rec(ProofTerm.assume(pt7.prop.arg))
                pt4 = apply_theorem('disjI1', pt2, inst=Inst(B=pt3.prop))
                pt5 = apply_theorem('disjI2', pt3, inst=Inst(A=pt2.prop))
                pt6 = apply_theorem('disjE', pt7, pt4.implies_intr(pt4.hyps[0]), pt5.implies_intr(pt5.hyps[0]))
                return pt6
            elif p.is_disj():
                pt1 = apply_theorem('de_morgan_thm2', inst=Inst(A=p.arg1, B=p.arg))
                pt7 = pt1.equal_elim(pt)
                pt2 = rec(ProofTerm.assume(pt7.prop.arg1)).implies_intr(pt7.prop.arg1)
                pt3 = rec(ProofTerm.assume(pt7.prop.arg)).implies_intr(pt7.prop.arg)
                pt4 = apply_theorem('conjD1', pt7)
                pt5 = apply_theorem('conjD2', pt7)
                pt6 = pt2.implies_elim(pt4)
                pt7 = pt3.implies_elim(pt5)
                pt8 = apply_theorem('conjI', pt6, pt7)
                return pt8
            elif p.is_forall():
                pt1 = apply_theorem('not_all', inst=Inst(p.arg.fun))
                pt2 = pt1.equal_elim(pt)
                pt3 = rec(ProofTerm.assume(pt2.prop.arg.body))
            else:
                return pt
        else:
            return pt
    return rec(ProofTerm.assume(term))

def quant_inst(p):
    basic.load_theory('logic')
    pat = ProofTerm.theorem('forall_elim')
    f = Implies(p.arg1.arg, p.arg)
    inst = matcher.first_order_match(pat.prop, f)
    pt1 = apply_theorem('forall_elim', inst=inst)
    pt2 = apply_theorem('disj_conv_imp', inst=Inst(A=pt1.prop.arg1, B=pt1.prop.arg)).symmetric()
    pt3 = pt2.equal_elim(pt1)
    return pt3

def quant_intro(p, q):
    def helper(l):
        if l.is_abs():
            return [Var(l.var_name, l.var_T)] + helper(l.body)
        else:
            return []
    
    l, r = p.prop.lhs, p.prop.rhs
    var = helper(l)
    is_forall = q.lhs.is_forall()
    pt = p
    for v in var:
        pf_refl = ProofTerm.reflexive(v)
        pt = ProofTerm.combination(pt, pf_refl)
        pt_l = ProofTerm.beta_conv(l(v)).symmetric()
        pt_r = ProofTerm.beta_conv(r(v))
        pt_l_beta_norm = pt_l.transitive(pt)
        pt = pt_l_beta_norm.transitive(pt_r)
        l, r = pt.prop.lhs, pt.prop.rhs

    for v in reversed(var):
        pf_quant = ProofTerm.reflexive(forall(v.get_type())) if is_forall else ProofTerm.reflexive(exists(v.get_type()))
        pt = pt.abstraction(v)
        pt = ProofTerm.combination(pf_quant, pt)

    return pt

def mp(arg1, arg2):
    """modus ponens:
    
    arg1: ⊢ p
    arg2: ⊢ p <--> q
    then have: ⊢ q
    """
    try:
        pt = ProofTerm.equal_elim(arg2, arg1)
    except:
        pt = ProofTerm.sorry(Thm(arg2.th.hyps + arg1.th.hyps, arg1.prop))
    return pt

def iff_true(arg1, arg2):
    """
    arg1: ⊢ p
    return: ⊢ p <--> true
    """
    basic.load_theory('logic')
    pt1 = apply_theorem('eq_true', inst=Inst(A=arg1.prop))
    return ProofTerm.equal_elim(pt1, arg1)

def iff_false(arg1, arg2):
    """
    arg1: ⊢ ¬p
    return: ⊢ ¬p <--> false
    """
    basic.load_theory('logic')
    pt1 = apply_theorem('eq_false', inst=Inst(A=arg1.prop.arg))
    return ProofTerm.equal_elim(pt1, arg1)

def not_or_elim(arg1, arg2):
    """
    """
    context.set_context('logic')
    th = theory.get_theorem('de_morgan_thm2')
    r = dict()
    def rec(pt):
        if pt.prop.is_not() and pt.prop.arg.is_disj():
            inst = matcher.first_order_match(th.prop.lhs, pt.prop)
            pt1 = apply_theorem('de_morgan_thm2', inst=inst)
            pt2 = ProofTerm.equal_elim(pt1, pt)
            pt_lhs = apply_theorem('conjD1', pt2)
            pt_rhs = apply_theorem('conjD2', pt2)
            rec(pt_lhs)
            rec(pt_rhs)
        else:
            r[pt.prop] = pt
    rec(arg1)
    dict_items = [(key, value) for key, value in r.items()] # dictionary keys can't change during loop
    for key, value in dict_items:
        new_key = try_conv(rewr_conv('double_neg')).get_proof_term(key)
        if new_key.prop.rhs != key:
            r.pop(key)
            new_key_pt = ProofTerm.equal_elim(new_key, value)
            r[new_key.prop.rhs] = new_key_pt
            
    return r[arg2]

def double_neg(pt):
    """
    If pt prop is in double neg form, try to simplify it.
    """
    cv = top_conv(try_conv(rewr_conv('double_neg')))
    return pt.on_prop(cv)

def nnf(pt):
    """
    Sometimes z3 get a proof which propositions is not in nnf-form.
    And z3 directly use it to operate unit-resolution, so we implemented a rule here
    to use de Morgan law when the propositions is not in nnf form.
    """
    cv_de_morgan_and = top_conv(try_conv(rewr_conv('de_morgan_thm1')))
    cv_de_morgan_or = top_conv(try_conv(rewr_conv('de_morgan_thm2')))
    
    if pt != pt.on_prop(cv_de_morgan_and):
        return nnf(pt.on_prop(cv_de_morgan_and))
    elif pt != pt.on_prop(cv_de_morgan_or):
        return nnf(pt.on_prop(cv_de_morgan_or))
    else:
        return pt

def beta_norm_lambda_eq(pt):
    """
    Suppose pt is: ⊢ (λx. p)(x) <--> (λy. q)(y)
    return a proofterm: ⊢ p x <--> q y
    """
    assert isinstance(pt, ProofTerm) and pt.prop.is_equals() and\
        pt.prop.lhs.head.is_abs() and pt.prop.rhs.head.is_abs(), \
        "Invalid ProofTerm: %s" % str(pt)
    lhs, rhs = pt.prop.lhs, pt.prop.rhs
    pt_lhs = ProofTerm.beta_conv(lhs).symmetric()
    pt_rhs = ProofTerm.beta_conv(rhs)
    return pt_lhs.transitive(pt).transitive(pt_rhs)

def schematic_rules_def_axiom(axiom):
    """Rewrite by instantiating def_axiom schematic theorems."""
    context.set_context('smt')
    with open('library/smt.json', 'r', encoding='utf-8') as f:
        f_data = json.load(f)
    thms = [f_data['content'][i]['name'] for i in range(len(f_data['content'])) if f_data['content'][i]['name'][0]=='d']
    for thm in thms:
        pt = ProofTerm.theorem(thm)
        try:
            inst1 = matcher.first_order_match(pt.prop, axiom)
            return pt.substitution(inst1)
        except matcher.MatchException:
            continue
    return None
    

def def_axiom(arg1):
    """
    def-axiom rule prove propositional tautologies axioms.
    because of this need propositional logic decision procedure,
    currently use proofterm.sorry
    """
    if schematic_rules_def_axiom(arg1) != None:
        return schematic_rules_def_axiom(arg1)
    else:
        return ProofTerm.sorry(Thm([], arg1))

def intro_def(concl):
    """
    Introduce a name for a formula/term e.
    There are several cases according to different type of e:
    
    a) e is of boolean type:
    return n = e ⊢ (n ∨ ¬e) ∧ (¬n ∨ e)
    b) e is of form "ite cond th e1":
    return n = e ⊢ (¬cond ∨ n = th) ∧ (cond ∨ n = e1)
    c) otherwise:
    return n = e ⊢ n = e
    
    But z3 only provide the right hands of proofterm instead of n,
    so we need to find n at first. After find n, we need to prove
    n = e ⊢ concl. 
    """
    case = ""
    if concl.is_conj(): # a), b) cases
        if concl.arg1.arg.is_equals():
            n = concl.arg1.arg.lhs
            case = "b"
        else:
            n = concl.arg1.arg1
            case = "a"
    else:
        n = concl.lhs
        case = "c"
    
    #prove.
    if case == "c":
        return ProofTerm.assume(concl)
    elif case == "a":
        e = concl.arg.arg
        pt = apply_theorem('iff_conv_conj_disj', inst = Inst(A=n, B=e))
        pt_assume = ProofTerm.assume(Eq(n, e))
        return ProofTerm.equal_elim(pt, pt_assume)
    else: # case == "b"
        cond = concl.arg.arg1
        th = concl.arg1.arg.rhs
        e1 = concl.arg.arg.rhs
        T = th.get_type()
        ite = Const("IF", TFun(BoolType, T, T, T))(cond, th, e1)
        redundant.append(Eq(n, ite)) # we need to delete the equalities after reconstruction.
        # First prove ⊢ (¬cond ∨ n = th)
        pt = apply_theorem('if_P', inst=Inst(P=cond, x=th, y=e1))
        pt_cond_assm = ProofTerm.assume(cond)
        pt1 = pt.implies_elim(pt_cond_assm) # cond ⊢ ite = th
        pt_eq = ProofTerm.assume(Eq(n, ite)) # n = ite ⊢ n = ite
        pt2 = pt_eq.transitive(pt1) # n = ite, cond ⊢ n = th
        pt3 = pt2.implies_intr(cond) # n = ite ⊢ cond -> n = th
        cv = rewr_conv('disj_conv_imp', sym=True)
        pt4 = cv.get_proof_term(pt3.prop) # ⊢ cond -> n = th <--> ¬cond ∨ n = th
        pt5 = ProofTerm.equal_elim(pt4, pt3) # n = ite ⊢ ¬cond ∨ n = th
        # then prove ⊢ (cond ∨ n = e1)
        pt6 = apply_theorem('if_not_P', inst=Inst(P=cond, x=th, y=e1)) # ⊢ ¬cond --> (if cond then th else e1) = e1
        pt_not_con_assm = ProofTerm.assume(Not(cond)) # ¬cond ⊢ ¬cond
        pt7 = pt6.implies_elim(pt_not_con_assm) # ¬cond ⊢ (if cond then th else e1) = e1
        pt8 = pt_eq.transitive(pt7) # n = ite, ¬cond ⊢ n = e1
        pt9 = pt8.implies_intr(Not(cond)) # n = ite ⊢ ¬cond --> n = e1
        pt10 = cv.get_proof_term(pt9.prop) # ⊢ ¬cond --> n = e1 <--> ¬¬cond ∨ n = e1
        pt11 = ProofTerm.equal_elim(pt10, pt9)
        pt12 = double_neg(pt11) # n = ite ⊢ cond ∨ n = e1
        pt13 = apply_theorem('conjI', pt5, pt12)
        return pt13


def apply_def(arg1):
    return ProofTerm.reflexive(arg1.lhs)

def resolution(pt1, pt2):
    """Input proof terms are A_1 | ... | A_m and B_1 | ... | B_n, where
    there is some i, j such that B_j = ~A_i or A_i = ~B_j."""
    
    # First, find the pair i, j such that B_j = ~A_i or A_i = ~B_j, the
    # variable side records the side of the positive literal.
    disj1 = pt1.prop.strip_disj()
    disj2 = pt2.prop.strip_disj()
    
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
        return resolution(pt2, pt1)
    
    # Move items i and j to the front
    disj1 = [disj1[i]] + disj1[:i] + disj1[i+1:]
    disj2 = [disj2[j]] + disj2[:j] + disj2[j+1:]
    eq_pt1 = imp_disj_iff(Eq(pt1.prop, Or(*disj1)))
    eq_pt2 = imp_disj_iff(Eq(pt2.prop, Or(*disj2)))
    pt1 = eq_pt1.equal_elim(pt1)
    pt2 = eq_pt2.equal_elim(pt2)
    
    if len(disj1) > 1 and len(disj2) > 1:
        pt = apply_theorem('resolution', pt1, pt2)
    elif len(disj1) > 1 and len(disj2) == 1:
        pt = apply_theorem('resolution_left', pt1, pt2)
    elif len(disj1) == 1 and len(disj2) > 1:
        pt = apply_theorem('resolution_right', pt1, pt2)
    else:
        pt = apply_theorem('negE', pt2, pt1)

    return pt.on_prop(disj_norm())

def lemma(arg1, arg2):
    """
    arg1 is proof: Γ ∪ {L1, L2, ..., Ln} ⊢ ⟂
    return proof: Γ ⊢ ¬L1 ∨ ... ∨ ¬Ln
    """
    th = theory.get_theorem('negI')
    pt1 = arg1.implies_intr(Not(arg2))
    inst = matcher.first_order_match(th.prop.arg1, pt1.prop)
    pt = apply_theorem('negI', pt1, inst=inst)
    return double_neg(pt)

def sk(arg1):
    """
    Skolemization rule, currently have no idea on how to reconstruct it.
    """
    return ProofTerm.sorry(Thm([], Eq(arg1.lhs, arg1.rhs)))


def th_lemma(args):
    """
    th-lemma: Generic proof for theory lemmas.
    currently use proofterm.sorry.
    args may contains several parameters, like:
    ⊢ x ≥ 0
    ⊢ x ≤ 0
    --------
    ⊢ x == 0
    so for now, we just use the last parameter
    as sorry.
    """
    pts = args[-1]  
    return ProofTerm.sorry(Thm([], args[-1]))

def convert_method(term, *args):
    name = term.decl().name()
    if name in ('asserted', 'hypothesis'): # {P} ⊢ {P}
        return ProofTerm.assume(args[0])
    elif name == 'and-elim':
        arg1, arg2 = args
        return and_elim(arg1, arg2)
    elif name == 'not-or-elim':
        arg1, arg2, = args
        return not_or_elim(arg1, arg2)
    elif name == 'monotonicity':
        *equals, concl = args
        return monotonicity(equals, concl)
    elif name == 'trans':
        arg1, arg2, _ = args
        return arg1.transitive(arg2)
    elif name in ('mp', 'mp~'):
        arg1, arg2, _ = args
        return mp(arg1, arg2)
    elif name in ('rewrite', 'commutativity'):
        arg1, = args
        return rewrite(arg1)
    elif name == 'unit-resolution':
        pt = args[0]
        for i in range(len(args) - 2):
            pt = resolution(pt, args[i+1])
        return pt
    elif name in ('nnf-pos', 'nnf-neg'):
        return ProofTerm.sorry(Thm([], args[-1]))
    elif name == 'proof-bind':
        return args[0]
    elif name == 'quant-inst':
        arg1, = args
        return quant_inst(arg1)
    elif name == 'quant-intro':
        arg1, arg2, = args
        return quant_intro(arg1, arg2)
    elif name == 'iff-true':
        arg1, arg2, = args
        return iff_true(arg1, arg2)
    elif name == 'iff-false':
        arg1, arg2, = args
        return iff_false(arg1, arg2)
    # elif name == 'lemma':
    #     return 
    elif name == 'symm':
        return args[0].symmetric()
    elif name == 'refl':
        return ProofTerm.reflexive(args[0])
    elif name == 'def-axiom':
        arg1, = args
        return def_axiom(arg1)
    elif name == 'intro-def':
        arg1, = args
        return intro_def(arg1)
    elif name == 'apply-def':
        arg1, arg2, = args
        return apply_def(arg2)
    elif name == 'lemma':
        arg1, arg2 = args
        return lemma(arg1, arg2)
    elif name == 'sk':
        arg1, = args
        return sk(arg1)
    elif name == 'th-lemma':
        return th_lemma(args)
    else:
        raise NotImplementedError
    
local = dict()
redundant = []

def delete_redundant(pt, redundant):
    """
    Because we introduce abbreviations for formula during def-intro,
    after reconstruction complete, we can delete these formulas use 
    theorem "(?t = ?t ⟹ False) ⟹ False"
    """
    new_pt = pt
    for r in redundant:
        pt1 = apply_theorem('eq_imp_false', inst=Inst(A=r.lhs, B=r.rhs)) # ⊢ (A = B --> false) --> false
        pt2 = new_pt.implies_intr(r) # ⊢ A = B --> false
        new_pt = pt1.implies_elim(pt2)
    
    return new_pt


def proofrec(proof, bounds=deque(), trace=False, debug=False):
    """
    If trace is true, print reconstruction trace.
    """
    term, net = index_and_relation(proof)
    order = DepthFirstOrder(net)
    r = dict()

    for i in order:
        args = (r[j] for j in net[i])
        if trace:
            print('term['+str(i)+']', term[i])
        if z3.is_quantifier(term[i]) or term[i].decl().name() not in method:
            r[i] = translate(term[i],bounds=bounds)
        else:
            r[i] = convert_method(term[i], *args)
            if trace:
                basic.load_theory('int')
                basic.load_theory('real')
                print('r['+str(i)+']', r[i])
    conclusion = delete_redundant(r[0], redundant)
    redundant.clear()
    return conclusion