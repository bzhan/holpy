"""
Z3 proof reconstruction.
Reference: Fast LCF-Style Proof Reconstruction for Z3
by Sascha Böhme and Tjark Weber.
"""

import z3
from z3.z3consts import *
from data import integer
from data import proplogic
from data.real import norm_real_ineq_conv, norm_neg_real_ineq_conv, real_const_eq_conv, real_eval_conv, real_norm_comparison
from kernel.type import TFun, BoolType, NatType, IntType, RealType, STVar, TVar
from kernel.term import *
from kernel.thm import Thm
from kernel.proofterm import ProofTerm, refl
from kernel.macro import Macro
from kernel.theory import check_proof, register_macro
from kernel import theory
from kernel.report import ProofReport
from logic import basic, context, matcher
from logic.logic import apply_theorem, imp_disj_iff, disj_norm, imp_conj_macro, resolution
from logic.tactic import rewrite_goal_with_prev
from logic.conv import rewr_conv, try_conv, top_conv, top_sweep_conv, bottom_conv, arg_conv, ConvException, Conv, arg1_conv, binop_conv
from logic import auto
from prover import sat, tseitin, simplex
from syntax.settings import settings
from syntax import parser
from prover import omega
settings.unicode = True
from collections import deque
import functools
import operator
import json
import time
import sys
sys.setrecursionlimit(10000000)

basic.load_theory('smt')

conj_expr = dict()
disj_expr = dict()

# Z3 proof method name.
method = ('mp', 'mp~', 'asserted', 'trans', 'trans*', 'monotonicity', 'rewrite', 'and-elim', 'not-or-elim',
            'iff-true', 'iff-false', 'unit-resolution', 'commutativity', 'def-intro', 'apply-def',
            'def-axiom', 'iff~', 'nnf-pos', 'nnf-neg', 'sk', 'proof-bind', 'quant-inst', 'quant-intro',
            'lemma', 'hypothesis', 'symm', 'refl', 'apply-def', 'intro-def', 'th-lemma', 'elim-unused')


class Z3Term:
    def __init__(self, t):
        assert isinstance(t, z3.AstRef), "%s is not z3 term!" % str(t)
        self.t = t

    def __eq__(self, value):
        return self.t.sort() == value.t.sort() and self.t == value.t

    def __hash__(self):
        return z3.AstRef.__hash__(self.t)

    def __str__(self):
        return str(self.t)

def index_and_relation(proof):
    """Index all terms in z3 proof and get the relation between the terms."""
    s = dict()
    id = 0
    def rec(term, parent=None):
        nonlocal id
        if term in s.keys() and parent is not None:
            s[parent][1].append(s[term][0])
        else:
            s[term] = [id, []]
            if parent is not None:
                s[parent][1].append(id)
            id += 1
            if not z3.is_quantifier(term.t):
                for child in term.t.children():
                    rec(Z3Term(child), term)
    rec(Z3Term(proof))
    return {value[0]: key.t for key, value in s.items()}, {value[0]: value[1] for key, value in s.items()}

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

def solve_cnf(F):
    encode_pt = tseitin.encode(Not(F))
    cnf = tseitin.convert_cnf(encode_pt.prop)
    res, proof = sat.solve_cnf(cnf)
    assert res == 'unsatisfiable', 'solve_cnf: statement is not provable'
    
    # Perform the resolution steps
    clause_pts = [ProofTerm.assume(clause) for clause in encode_pt.prop.strip_conj()]
    for new_id in sorted(proof.keys()):
        steps = proof[new_id]
        pt = clause_pts[steps[0]]
        for step in steps[1:]:
            pt = resolution(pt, clause_pts[step])
        clause_pts.append(pt)

    contra_pt = clause_pts[-1]
    assert contra_pt.prop == false
    
    # Show contradiction from ~F and definitions of new variables
    pt1, pt2 = encode_pt, contra_pt
    while pt1.prop.is_conj():
        pt_left = apply_theorem('conjD1', pt1)
        pt2 = pt2.implies_intr(pt_left.prop).implies_elim(pt_left)  # remove one clause from assumption
        pt1 = apply_theorem('conjD2', pt1)
    pt2 = pt2.implies_intr(pt1.prop).implies_elim(pt1)  # remove last clause from assumption

    # Clear definition of new variables from antecedent
    eqs = [t for t in pt2.hyps if t.is_equals()]
    eqs = list(reversed(sorted(eqs, key=lambda t: int(t.lhs().name[1:]))))

    for eq in eqs:
        pt2 = pt2.implies_intr(eq).forall_intr(eq.lhs).forall_elim(eq.rhs) \
                 .implies_elim(ProofTerm.reflexive(eq.rhs))

    return apply_theorem('negI', pt2.implies_intr(pt2.hyps[0])).on_prop(rewr_conv('double_neg'))

def translate(term, bounds=deque(), subterms=[]):
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
            for i in range(len(var)):
                bounds.popleft()
            return e
        elif term.is_forall():
            f = Forall(*var, translate(body, bounds))
            for i in range(len(var)):
                bounds.popleft()
            return f
        else:
            raise NotImplementedError
    elif z3.is_expr(term):
        if z3.is_var(term):
            return bounds[z3.get_var_index(term)]
        kind = term.decl().kind() # term function application
        sort = translate_type(term.sort()) # term sort
        args = subterms
        if len(subterms) == 0 and term.num_args() != 0:
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
            return Eq(args[0], args[1])
        elif z3.is_and(term):
            return And(*args)
        elif z3.is_or(term):
            return Or(*args)
        elif z3.is_implies(term):
            return Implies(*args)
        elif z3.is_not(term):
            return Not(args[0])
        elif z3.is_lt(term):
            return less(args[0].get_type())(*args)
        elif z3.is_le(term):
            return less_eq(args[0].get_type())(*args)
        elif z3.is_gt(term):
            return greater(args[0].get_type())(*args)
        elif z3.is_ge(term):
            return greater_eq(args[0].get_type())(*args)
        elif z3.is_distinct(term):
            ineq = [Not(Eq(args[i], args[j])) for i in range(len(args)) for j in range(i+1, len(args))]
            return And(*ineq)
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

def and_elim(arg1, concl):
    global conj_expr
    if arg1.prop not in conj_expr:
        conj_expr.update({arg1.prop: dict()})
    
    for key, value in conj_expr[arg1.prop].items():
        if key == concl:
            print("!!")
            return value    

    pt = arg1
    while pt.prop.is_conj():
        left, right = pt.prop.arg1, pt.prop.arg
        pt_l, pt_r = apply_theorem('conjD1', pt), apply_theorem('conjD2', pt)
        conj_expr[arg1.prop].update({left: pt_l, right: pt_r})
        if left == concl:
            return pt_l
        elif right == concl:
            return pt_r
        else:
            pt = pt_r
    assert pt.prop == concl # I will implement proofrec exception later
    return pt

def monotonicity(pts, concl):
    """
    f = f, x1 = y1, x2 = y2, ..., xn = yn
    =====================================
        f(x1,...,xn) = f(y1,...,yn)

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

    When f is +/-/*, there is another pitfall: in HOL, while ∧ or ∨ is right associative, +/-/*
    is left associative when construct terms.
    """

    def strip_fun(fun, tm, tl):
        """
        tm is a function term, fun is its function name, tl is a term list, 
        in which are arguments occured in tm(but not all). strip_fun will strip
        tm's arguments based on tl.
        
        For example, fun is plus, tm is v1 * 2 - s_0 * 16 + v0, tl is [v1 * 2 - s_0 * 16],
        then the return list is [v1 * 2 - s_0 * 16, v0]
        """
        if tm.is_comb(fun, None):
            if tm.arg1 in tl:
                return tm.args
            else:
                return strip_fun(fun, tm.arg1, tl) + [tm.arg]
        else:
            return [tm]

    def get_argument(f, left_assoc=False):
        """
        Suppose f is f x1 x2 x3, return [x1, x2, x3]
        When assoc_direction is true, we can't use strip_comb.
        """
        if not left_assoc:
            _, fx = f.strip_comb()
            return fx
        else:
            args = deque()
            while f.is_plus():
                args.appendleft(f.args[1])
                f = f.args[0]
            return [f] + list(args)

    def arith_eq(fun_eq, pts):
        """
        fun is ⊢+ = +/- = -/* = *,
        pts is a list of equality proof terms: [a = a', b = b', c = c', ...]
        return a proofterm: ⊢ a + b + c + ⋯ = a' + b' + c' + ⋯
        """
        if len(pts) == 1:
            return pts[0]
        else:
            return fun_eq.combination(arith_eq(fun_eq, pts[:-1])).combination(pts[-1])

    # First get f, g.
    f_expr, g_expr = concl.lhs, concl.rhs
    if not f_expr.is_disj() and not f_expr.is_conj():
        f, g = f_expr.head, g_expr.head

        # Next collect arguments: x1...xn/y1...yn
        # We can't split the term in pts into subterms.
        # if not f_expr.is_plus():
        #     fx, gy = get_argument(f_expr), get_argument(g_expr)
        # else:
        #     fx, gy = get_argument(f_expr, True), get_argument(g_expr, True)
        # fx = get_argument(f_expr) if not (f_expr.is_plus() or f_expr().is_minus()) else get_argument(f_expr, True)
        # gy = get_argument(g_expr) if not (g_expr.is_plus() or g_expr().is_minus()) else get_argument(g_expr, True)
        # Then put all useful equalities proofterm in equalities.
        if f_expr.is_plus() or f_expr.is_minus() or f_expr.is_times():
            pts_lhs, pts_rhs = [pt.lhs for pt in pts], [pt.rhs for pt in pts]
            fx, gy = strip_fun(f.name, f_expr, pts_lhs), strip_fun(g.name, g_expr, pts_rhs)
        else:
            fx, gy = get_argument(f_expr), get_argument(g_expr)
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
        if not f_expr.is_plus():
            return functools.reduce(lambda f, x : f.combination(x), equalities)
        else:
            return arith_eq(ProofTerm.reflexive(f_expr.head), equalities[1:])
    else:
        eq_prop = concl # f x1 x2 ... xk ~ f y1 y2 ... yk
        eq_hyps = pts
        assert eq_prop.lhs.head == eq_prop.rhs.head
        head = eq_prop.lhs.head
        if head.name == "disj":
            head_arity = len(concl.lhs.strip_disj())
        elif head.name == "conj":
            head_arity = len(concl.lhs.strip_conj())
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
                if l in eq_assms_lhs:
                    index += 1
        pt1 = eq_pts[0]
        if len(eq_pts) == 1:
            return pt_concl.combination(eq_pts[0])
        for i in range(len(eq_pts) - 1):
            pt1 = pt_concl.combination(eq_pts[i+1]).combination(pt1)

        return pt1

def distinct_monotonicity(pts, concl, z3terms):
    """
    If we want to prove distinct[x, y, z] <--> distinct[a, b, c]
    with premises: [x = a, y = b, z = c], because HOL doesn't have distinct 
    operator, we need to implement one.
    For example, we can use monotonicity to get 
    "x = a, y = b ⊢ x = y <--> a = b", and use combination we can get 
    "x = a, y = b ⊢ Not(x = y) <--> Not(a = b)". If we have n premises, we
    can get n(n-1)/2 similarly proofterms. These proofterms are
    enough to call a monotonicity rule, in which function is conjunction.
    """

    def equal_mono(pt1, pt2):
        """
        Due to bugs in monotonicity method(not use z3terms as argument indicator), 
        we temporarily implement a little equal monotonicity rule here.
        pt1: ⊢ a = b
        pt2: ⊢ c = d
        concl: a = c <--> b = d
        """
        eq = equals(pt1.prop.lhs.get_type())
        eq_refl = ProofTerm.reflexive(eq)
        pt1 = ProofTerm.combination(eq_refl, pt1)
        pt2 = ProofTerm.combination(pt1, pt2)
        return pt2

    arg_num = z3terms[-1].arg(0).num_args()
    lhs_arguments = [translate(z3terms[-1].arg(0).arg(i)) for i in range(arg_num)]
    rhs_arguments = [translate(z3terms[-1].arg(1).arg(i)) for i in range(arg_num)]
    new_equals = []
    index = 0
    for l, r in zip(lhs_arguments, rhs_arguments):
        if l == r:
            new_equals.append(ProofTerm.reflexive(l))
        else:
            new_equals.append(pts[index])
            index += 1
    new_pts = [(new_equals[i], new_equals[j], \
        Eq(Eq(new_equals[i].prop.lhs, new_equals[j].prop.lhs), Eq(new_equals[i].prop.rhs, new_equals[j].prop.rhs))) \
        for i in range(len(new_equals)) for j in range(i+1, len(new_equals))]

    new_pts1 = [equal_mono(p[0], p[1]) for p in new_pts]
    neg_refl = ProofTerm.reflexive(neg)
    new_pts2 = [ProofTerm.combination(neg_refl, p) for p in new_pts1]
    conj_refl = ProofTerm.reflexive(conj)
    pt_conj = new_pts2[-1]
    for i in reversed(range(len(new_pts2) - 1)):
        pt = ProofTerm.combination(conj_refl, new_pts2[i]).combination(pt_conj)
        pt_conj = pt
    return pt_conj

def schematic_rules_rewr(thms, lhs, rhs):
    """Rewrite by instantiating schematic theorems."""
    for thm in thms:
        pt = ProofTerm.theorem(thm)
        try:
            inst1 = matcher.first_order_match(pt.prop.lhs, lhs)
            inst2 = matcher.first_order_match(pt.prop.rhs, rhs, inst=inst1)
            return pt.substitution(inst2)
        except matcher.MatchException:
            continue
    return ProofTerm.sorry(Thm([], Eq(lhs, rhs)))

def is_ineq(t):
    """determine whether t is an inequality"""
    return t.is_less() or t.is_less_eq() or t.is_greater() or t.is_greater_eq()

class flat_left_assoc_conj_conv(Conv):
    """convert the left-associative conjunction to right-associative conjunction."""
    def get_proof_term(self, t):
        pt = refl(t)
        if t.is_conj():
            if t.arg1.is_conj():
                return pt.on_rhs(
                    rewr_conv('conj_assoc', sym=True),
                    self
                )
            else:
                return pt
        else:
            return pt

class flat_left_assoc_disj_conv(Conv):
    """convert the left-associative disjunction to right-associative disjunction."""
    def get_proof_term(self, t):
        pt = refl(t)
        if t.is_disj():
            if t.arg1.is_disj():
                return pt.on_rhs(
                    rewr_conv('disj_assoc_eq', sym=True),
                    self
                )
            else:
                return pt
        else:
            return pt

def compare_lhs_rhs(tm, cvs):
    """
    tm is an equality term, first try use conversions in cvs iteratively to normalize left-hand side
    to match tm's right-hand side. If failed, then use conversions to normalize right-hand side similarly.
    If they still can't match, we can only return sorry.
    """
    norm_lhs_pt = refl(tm.lhs)
    for cv in cvs:
        norm_lhs_pt = norm_lhs_pt.on_rhs(cv)
        if norm_lhs_pt.rhs == tm.rhs:
            return norm_lhs_pt
    norm_rhs_pt = refl(tm.rhs)
    for cv in cvs:
        norm_rhs_pt = norm_rhs_pt.on_rhs(cv)
        if norm_rhs_pt.rhs == norm_lhs_pt.rhs:
            return norm_lhs_pt.transitive(norm_rhs_pt.symmetric())
        
    return ProofTerm.sorry(Thm([], tm))

def match_pattern(pat, tm):
    """If the schematic pattern can match with term tm, return true, else false"""
    if isinstance(pat, str):
        pat = parser.parse_term(pat).convert_svar()
    try:
        matcher.first_order_match(pat, tm)
        return True
    except matcher.MatchException:
        return False

def try_tran_pt(pt1, pt2):
    """Try to do transition with pt1 and pt2, """
    if pt1.rhs == pt2.lhs:
        return pt1.transitive(pt2)
    else:
        return ProofTerm.sorry(Thm([], Eq(pt1.lhs, pt2.rhs)))

def analyze_type(tm):
    """
    Infer the theory which term tm most likely belongs to.
    """
    if tm.is_number():
        return tm.get_type()
    else:
        types = [v.T for v in tm.get_vars()] + [v.T for v in tm.get_consts()]
        range_types = [T.strip_type()[-1] for T in types]
        if not types: # only have true or false
            return set([BoolType])
        else:
            return set(range_types)

def rewrite_bool(tm):
    pt1 = compare_lhs_rhs(tm, [proplogic.norm_full()])
    if pt1.rule == 'sorry':
        return compare_lhs_rhs(tm, [
            proplogic.norm_full(),
            top_conv(rewr_conv('neg_iff_both_sides')),
            proplogic.norm_full()
        ])
    else:
        return pt1

def rewrite_int(tm, has_bool=False):
    """
    Patterns:
    1) a ⋈ b <--> c ⋈ d
    2) a = b <--> c = d
    3) a = b
    4) ¬(a = b) <--> ¬(c = d)
    5) (a = b) <--> (a ≤ b) & (a ≥ b)
    6) a ⋈ b <--> ¬(c ⋈ d)
    7) ¬(a ⋈ b) <--> ¬(c ⋈ d)
    8) a | b = c <--> a | b ≤ c & b ≥ c
    9) ¬(a ⋈ b) <--> ¬(c ⋈ d) (k * a = c, k * b = d)
    10) (a = b) <--> false

    If all above patterns cannot match tm, we have to apply a more general strategy:
    1) normalize the logic term;
    2) normalize all comparison;
    3) convert all equality term to less_eq /\ greater_eq

    """
    if tm.lhs.is_compares() and tm.rhs.is_compares():
        """
        Two cases:
        1. prove equality by moving terms
        2. simplified one side by dividing GCD to match with the other
        """
        try:
            return integer.int_eq_comparison_macro().get_proof_term(tm)
        except:
            return compare_lhs_rhs(tm, [top_conv(integer.int_gcd_compares()), integer.omega_form_conv()])
    elif match_pattern('((a::int) = b) <--> ((c::int) = d)', tm):
        return compare_lhs_rhs(tm, [integer.int_norm_eq()])
    elif tm.lhs.get_type() == IntType and tm.rhs.get_type() == IntType:
        pt1 = refl(tm.lhs).on_rhs(integer.simp_full())
        pt2 = refl(tm.rhs).on_rhs(integer.simp_full())
        res = try_tran_pt(pt1, pt2.symmetric())
        if res.rule != 'sorry':
            return res
    elif tm.lhs.is_not() and tm.rhs.is_not() and tm.lhs.arg.is_equals() and tm.rhs.arg.is_equals():
        return refl(neg).combination(compare_lhs_rhs(Eq(tm.lhs.arg, tm.rhs.arg), [integer.int_norm_eq()]))
    elif tm.lhs.is_equals() and tm.rhs.is_conj() and tm.rhs.arg1.is_less_eq() and tm.rhs.arg.is_greater_eq():
        pt = refl(tm.lhs).on_rhs(rewr_conv('int_eq_leq_geq'))
        if pt.rhs == tm.rhs:
            return pt
        else:
            return ProofTerm.sorry(Thm([], tm))
    elif tm.lhs.is_compares() and tm.rhs.is_not() and tm.rhs.arg.is_compares():
        pt_elim_neg_sym = refl(tm.rhs).on_rhs(integer.int_norm_neg_compares(), integer.omega_form_conv()).symmetric()
        pt_eq = integer.int_eq_comparison_macro().get_proof_term(Eq(tm.lhs, pt_elim_neg_sym.lhs))
        return try_tran_pt(pt_eq, pt_elim_neg_sym)
    elif tm.lhs.is_not() and tm.lhs.arg.is_compares() and tm.rhs.is_not() and tm.rhs.arg.is_compares():
        """
        Two cases:
        1. normalize the comparisons can prove they are equal.
        2. use gcd, ¬(a ⋈ b) <--> ¬(m * c ⋈ m * d)
        """
        pt_lhs_elim_neg = refl(tm.lhs).on_rhs(integer.int_norm_neg_compares(), integer.omega_form_conv())
        pt_rhs_elim_neg_sym = refl(tm.rhs).on_rhs(integer.int_norm_neg_compares(), integer.omega_form_conv()).symmetric()
        pt1 = try_tran_pt(pt_lhs_elim_neg, pt_rhs_elim_neg_sym)
        if pt1.rule != 'sorry':
            return pt1
        return compare_lhs_rhs(tm, [top_conv(integer.int_gcd_compares()), integer.int_norm_neg_compares(), integer.omega_form_conv()])
    elif match_pattern('a | (b::int) = c <--> a | ~(~((b::int) <= c) | ~(b >=c))', tm):
        pt_lhs = refl(tm.lhs).on_rhs(arg_conv(rewr_conv('int_eq_leq_geq')), arg_conv(proplogic.norm_full()))
        pt_rhs_sym = refl(tm.rhs).on_rhs(arg_conv(proplogic.norm_full())).symmetric()        
        return try_tran_pt(pt_lhs, pt_rhs_sym)
    elif match_pattern('(a :: int) = b <--> false', tm):
        return refl(tm.lhs).on_rhs(integer.int_norm_eq(), integer.int_neq_false_conv())
    
    return rewrite_int_second_level(tm)

def rewrite_int_second_level(tm):
    """Use single rewrite conversion"""
    armony = [
        (proplogic.norm_full(), ),
        (try_conv(rewr_conv('pos_eq_neg')), ),
        (try_conv(rewr_conv('neg_eq_pos')), ),
        (bottom_conv(integer.int_norm_conv()), ),
        # (proplogic.norm_full(), top_conv(rewr_conv('int_eq_geq_leq_conj'))),
        # (proplogic.norm_full(), top_conv(rewr_conv('int_eq_leq_geq'))),
        # (proplogic.norm_full(), top_conv(rewr_conv('int_eq_geq_leq_conj')), proplogic.norm_full()),
        # (proplogic.norm_full(), top_conv(rewr_conv('int_eq_leq_geq')), proplogic.norm_full()),
        # (proplogic.norm_full(), try_conv(bottom_conv(integer.int_norm_eq())), top_conv(rewr_conv('int_eq_geq_leq_conj'))),
        # (proplogic.norm_full(), try_conv(bottom_conv(integer.int_norm_eq())), bottom_conv(integer.omega_form_conv())),
        # (proplogic.norm_full(),try_conv(top_conv(integer.int_norm_eq())), try_conv(bottom_conv(integer.simp_full())), top_conv(rewr_conv('int_eq_geq_leq_conj')), proplogic.norm_full()),
        # (proplogic.norm_full(), top_conv(integer.int_gcd_compares()), top_conv(integer.int_norm_neg_compares()), top_conv(integer.omega_form_conv())),
        (top_conv(rewr_conv('neg_iff_both_sides')), top_conv(rewr_conv('double_neg'))),
        (try_conv(bottom_conv(integer.omega_form_conv())),
        try_conv(bottom_conv(integer.int_norm_neg_compares())), try_conv(bottom_conv(integer.omega_form_conv())),
        try_conv(bottom_conv(integer.int_norm_eq())),
        try_conv(proplogic.norm_full()),
        top_conv(rewr_conv('neg_iff_both_sides')), 
        try_conv(proplogic.norm_full()))
    ]

    for arm in armony:
        pt = compare_lhs_rhs(tm, arm)
        if pt.rule != 'sorry':
            return pt

    armony_with_norm = [
        (top_conv(rewr_conv('int_eq_geq_leq_conj')), ),
        (top_conv(rewr_conv('int_eq_geq_leq_conj')), ),
        (top_conv(rewr_conv('int_eq_leq_geq')), ),
        (top_conv(rewr_conv('int_eq_geq_leq_conj')), proplogic.norm_full()),
        (top_conv(rewr_conv('int_eq_leq_geq')), proplogic.norm_full()),
        (try_conv(bottom_conv(integer.int_norm_eq())), top_conv(rewr_conv('int_eq_geq_leq_conj'))),
        (try_conv(bottom_conv(integer.int_norm_eq())), bottom_conv(integer.omega_form_conv())),
        (proplogic.norm_full(),try_conv(top_conv(integer.int_norm_eq())), try_conv(bottom_conv(integer.simp_full())), top_conv(rewr_conv('int_eq_geq_leq_conj')), proplogic.norm_full()),
        (top_conv(integer.int_gcd_compares()), top_conv(integer.int_norm_neg_compares()), top_conv(integer.omega_form_conv())),
    ]

    pt_norm_full = refl(tm).on_rhs(binop_conv(proplogic.norm_full()))
    tm_norm_full = pt_norm_full.rhs
    for arm in armony_with_norm:
        pt = compare_lhs_rhs(tm_norm_full, arm)
        if pt.rule != 'sorry':
            return pt_norm_full.symmetric().equal_elim(pt)

    return ProofTerm.sorry(Thm([], tm))

def rewrite_by_assertion(tm):
    """
    Rewrite the tm by assertions. Currently we only rewrite the absolute boolean variables.
    """
    global atoms
    pt = refl(tm)
    # boolvars = [v for v in tm.get_vars()] + [v for v in tm.get_consts()]
    return pt.on_rhs(*[top_conv(replace_conv(v)) for _, v in atoms.items()])

def rewrite_real(tm, has_bool=False):
    if match_pattern("(x::real) = y <--> x <= y & x >= y", tm):
        return refl(tm.lhs).on_rhs(rewr_conv('real_ge_le_same_num'))
    elif match_pattern("((x::real) = y) <--> false", tm) or match_pattern("((x::real) = y) <--> true", tm):
        return real_const_eq_conv().get_proof_term(tm.lhs)
    elif match_pattern("(if P then (t :: 'a) else t) = t", tm):
        return refl(tm.lhs).on_rhs(rewr_conv('cond_id'))
    elif match_pattern("(if P then (x::'a) else if Q then x else y) = (if P ∨ Q then (x::'a) else y)", tm):
        return refl(tm.lhs).on_rhs(rewr_conv('ite_elim_else_if'))
    return rewrite_real_second_level(tm)

def rewrite_real_second_level(tm):
    global atoms
    cvs = [value for _, value in atoms.items()]
    
    armony = [
        # (auto.auto_conv(), top_conv(rewr_conv('ite_to_disj')), bottom_conv(norm_neg_real_ineq_conv()), bottom_conv(real_norm_comparison()), proplogic.norm_full()),
        (bottom_conv(rewr_conv("if_true")), bottom_conv(rewr_conv("if_false"))),
        
        (bottom_conv(real_norm_comparison()),
        auto.auto_conv(), 
        bottom_conv(rewr_conv('not_true')),
        bottom_conv(rewr_conv('not_false')),
        bottom_conv(real_const_eq_conv()),
        bottom_conv(proplogic.norm_full()),
        bottom_conv(rewr_conv('if_true')),
        bottom_conv(rewr_conv('if_false')), 
        bottom_conv(rewr_conv('ite_to_disj')),
        bottom_conv(rewr_conv('ite_cond_disj_to_conj')),
        bottom_conv(rewr_conv('eq_false', sym=True)),
        top_conv(rewr_conv('real_ge_le_same_num')),
        bottom_conv(rewr_conv('norm_neg_equality')),
        bottom_conv(proplogic.norm_full()),
        bottom_conv(norm_neg_real_ineq_conv()),
        bottom_conv(real_norm_comparison()),
        bottom_conv(rewr_conv('cond_swap')), 
        bottom_conv(proplogic.norm_full()),),

        (bottom_conv(rewr_conv('ite_eq_value')), bottom_conv(real_const_eq_conv()), proplogic.norm_full()),

        (proplogic.norm_full(), real_eval_conv(), ),
    
        (proplogic.norm_full(), top_conv(rewr_conv('cond_swap')), )
    ]

    # pt_norm_full = refl(tm).on_rhs(binop_conv(proplogic.norm_full()))
    # tm_norm_full = pt_norm_full.rhs
    for arm in armony:
        pt = compare_lhs_rhs(tm, arm)
        if pt.rule != 'sorry':
            return pt
    return ProofTerm.sorry(Thm([], tm))

def _rewrite(tm):
    with open('library/smt.json', 'r', encoding='utf-8') as f:
        f_data = json.load(f)
    th_name = sorted([f_data['content'][i]['name'] for i in range(len(f_data['content'])) if f_data['content'][i]['name'][0]=='r'])
    if tm.lhs == tm.rhs:
        return refl(tm.lhs)
    Ts = analyze_type(tm)
    if IntType not in Ts and RealType not in Ts: # only have bool type variables
        pt1 = rewrite_bool(tm)
        if pt1.rule != 'sorry':
            return pt1
        pt_asst_lhs = rewrite_by_assertion(tm.lhs)
        pt_asst_rhs = rewrite_by_assertion(tm.rhs)
        tm_asst = Eq(pt_asst_lhs.rhs, pt_asst_rhs.rhs)
        pt2 = rewrite_bool(tm_asst)
        if pt2.rule != 'sorry':
            return pt_asst_lhs.transitive(pt2).transitive(pt_asst_rhs.symmetric())
        else:
            return schematic_rules_rewr(th_name[:60], tm.lhs, tm.rhs)
    elif IntType in Ts:
        pt1 = rewrite_int(tm, True) if BoolType in Ts else rewrite_int(tm, False)
        if pt1.rule != 'sorry':
            return pt1
        pt_asst_lhs = rewrite_by_assertion(tm.lhs)
        pt_asst_rhs = rewrite_by_assertion(tm.rhs)
        tm_asst = Eq(pt_asst_lhs.rhs, pt_asst_rhs.rhs)
        pt2 = rewrite_int(tm_asst)
        if pt2.rule != 'sorry':
            return pt_asst_lhs.transitive(pt2).transitive(pt_asst_rhs.symmetric())
        else:
            return schematic_rules_rewr(th_name, tm.lhs, tm.rhs)
    elif RealType in Ts:
        pt1 = rewrite_real(tm, has_bool=True) if BoolType in Ts else rewrite_real(tm, False)
        if pt1.rule != 'sorry':
            return pt1
        pt_asst_lhs = rewrite_by_assertion(tm.lhs)
        pt_asst_rhs = rewrite_by_assertion(tm.rhs)
        tm_asst = Eq(pt_asst_lhs.rhs, pt_asst_rhs.rhs)
        pt2 = rewrite_real(tm_asst)
        if pt2.rule != 'sorry':
            return pt_asst_lhs.transitive(pt2).transitive(pt_asst_rhs.symmetric())
        else:
            return ProofTerm.sorry(Thm([], tm))
    else:
        return ProofTerm.sorry(Thm([], tm))

def rewrite(t, z3terms, assertions=[]):
    """
    Multiple strategies for rewrite rule:
    a) if we want to rewrite distinct[a,...,z] to false, we can check whether there are
    same terms in args.
    """
    try:
        return _rewrite(t)
    except ConvException:
        return ProofTerm.sorry(Thm([], t))
    # if z3.is_distinct(z3terms[0].arg(0)) and z3.is_false(z3terms[0].arg(1)):
    #     conjs = t.lhs.strip_conj()
    #     same = None
    #     for i in range(len(conjs)):
    #         if conjs[i].arg.is_reflexive():
    #             pt1 = imp_conj_macro().get_proof_term(Implies(t.lhs, conjs[i]), None) # ⊢ ~A ∧ B --> ~A
    #             pt2 = ProofTerm.reflexive(conjs[i].arg.lhs) # ⊢ A
    #             pt3 = apply_theorem('double_neg', inst=Inst(A=pt2.prop)).symmetric() # ⊢ A = ~~(A)
    #             pt4 = apply_theorem('negE', inst=Inst(A=Not(pt2.prop))) # ~~A --> ~A --> false
    #             pt5 = pt3.equal_elim(pt2) # ⊢ ~~A
    #             pt6 = pt4.implies_elim(pt5) # ⊢ ~A --> false
    #             pt7 = pt1.implies_elim(ProofTerm.assume(t.lhs)) # ~A ∧ B ⊢ ~A
    #             pt8 = pt6.implies_elim(pt7) # ~A ∧ B ⊢ false
    #             pt9 = pt8.implies_intr(pt8.hyps[0]) # ⊢ ~A ∧ B --> false
    #             pt10 = apply_theorem('falseE', inst=Inst(A=t.lhs)) # ⊢ false --> ~A ∧ B
    #             return apply_theorem('iffI', pt9, pt10, inst=Inst(A=t.lhs, B=false)) # ~A ∧ B <--> false

    # occur_vars = t.get_vars()
    # occur_consts = t.get_consts()
    # # real situation
    # if (len(occur_vars) != 0 and all(v.T in (RealType, BoolType) for v in occur_vars))\
    #         or (len(occur_consts) != 0 and all(v.T in (RealType, BoolType) for v in occur_vars)):
    #     refl_pt = refl_pt_simp = refl(t)
        
    #     # preprocess by implicitly asssertions
    #     for c in assert_atom:
    #         refl_pt_simp = refl_pt_simp.on_rhs(
    #             bottom_conv(replace_conv(c)),
    #             bottom_conv(rewr_conv('eq_false', sym=True)),
    #             bottom_conv(rewr_conv('not_false')),
    #             bottom_conv(rewr_conv('if_false')),
    #             bottom_conv(rewr_conv('if_true')),
    #             bottom_conv(rewr_conv('r049')),
    #             bottom_conv(rewr_conv('r050'))
    #         )
        
    #     conv_pt = refl_pt_simp.on_rhs(
    #         try_conv(bottom_conv(rewr_conv('de_morgan_thm1'))),
    #         try_conv(bottom_conv(rewr_conv('de_morgan_thm2'))),
    #         try_conv(bottom_conv(rewr_conv('double_neg'))),
    #         try_conv(top_conv(flat_left_assoc_conj_conv())),
    #         try_conv(top_conv(flat_left_assoc_disj_conv())),
    #         try_conv(bottom_conv(rewr_conv('cond_swap'))),
    #         try_conv(bottom_conv(norm_neg_real_ineq_conv())),
    #         try_conv(bottom_conv(norm_real_ineq_conv())),
    #         try_conv(bottom_conv(real_const_eq_conv())),
    #         try_conv(bottom_conv(rewr_conv('conj_false_right'))),
    #         try_conv(bottom_conv(rewr_conv('conj_false_left'))),
    #         try_conv(bottom_conv(rewr_conv('disj_false_right'))),
    #         try_conv(bottom_conv(rewr_conv('disj_false_left'))),
    #         try_conv(auto.auto_conv()),        
    #         try_conv(rewr_conv('eq_mean_true')))

    #     # print("###real pt: ", conv_pt.on_prop(try_conv(rewr_conv('eq_true', sym=True))))
    #     pt_after_conv = conv_pt.on_prop(try_conv(rewr_conv('eq_true', sym=True)))
    #     if pt_after_conv.prop == t:
    #         return pt_after_conv
    #     else:
    #         if t.is_equals() and t.lhs.is_equals() and t.rhs.is_conj() and t.lhs.lhs.get_type() == RealType: # maybe x = y ⟷ x ≥ y ∧ x ≤ y
    #             pt = refl(t.lhs).on_rhs(rewr_conv('real_ge_le_same_num'))
    #             if pt.prop == t:
    #                 return pt

    # def norm_int(t):
    #     """Use nat norm macro to normalize nat expression."""
    #     return int_norm_macro().get_proof_term(t, [])

    # def equal_is_true(pt):
    #     """pt is ⊢ x = y, return: ⊢ (x = y) ↔ true"""
    #     pt0 = apply_theorem('trueI') # ⊢ true
    #     pt1 = pt0.implies_intr(pt.prop) # ⊢ (x = y) → true
    #     pt2 = pt.implies_intr(pt0.prop) # ⊢ true → (x = y)
    #     return ProofTerm.equal_intr(pt1, pt2)

    # if t.lhs == t.rhs:
    #     return ProofTerm.reflexive(t.lhs)
    # if is_ineq(t.lhs) and is_ineq(t.rhs) and t.lhs.arg1.get_type() == IntType:
        
    #     lhs_norm = int_ineq_macro().get_proof_term(t.lhs)
    #     rhs_norm = int_ineq_macro().get_proof_term(t.rhs)
    #     try:
    #         return lhs_norm.transitive(rhs_norm.symmetric())
    #     except:
    #         pass
    #     try:
    #         return int_multiple_ineq_equiv().get_proof_term([t.lhs, t.rhs])
    #     except:
    #         pass        

    # # first try use schematic theorems
    # with open('library/smt.json', 'r', encoding='utf-8') as f:
    #     f_data = json.load(f)
    # th_name = [f_data['content'][i]['name'] for i in range(len(f_data['content'])) if f_data['content'][i]['name'][0]=='r']
    # pt = schematic_rules_rewr(th_name, t.lhs, t.rhs)  # rewrite by schematic theorems 
    # if pt is None:
    #     if t.rhs == true and t.lhs.is_equals(): # prove ⊢ (x = y) ↔ true
    #         eq = t.lhs
    #         if eq.lhs.get_type() == IntType: # Maybe can reuse schematic theorems to prove ⊢ (x = y) in further
    #             pt_eq = norm_int(eq)
    #             return equal_is_true(pt_eq)
    #         else:
    #             raise NotImplementedError
    #     elif t.is_equals(): # Equations that can't match with schematic theorems
    #         # Try int norm macro:
    #         # Note that if t is of form: if (x::real) > 1 then (0::int) else 1
    #         # get_type will also return IntType, but we can't solve this by norm_int()
    #         if t.lhs.get_type() == IntType:
    #             try:
    #                 return norm_int(t)
    #             except AssertionError:
    #                 return ProofTerm.sorry(Thm([], t))
    #         # elif t.lhs.get_type() == BoolType and is_prop_fm(t):
    #         #     basic.load_theory('sat')
    #         #     f = Implies(*assertions, t)
    #         #     time1 = time.perf_counter()
    #         #     pt = zchaff.zChaff(Not(f)).solve()
    #         #     time2 = time.perf_counter()
    #         #     print("Time: ", time2 - time1)
    #         #     for assertion in assertions:
    #         #         pt_assert = ProofTerm.assume(assertion)
    #         #         pt = ProofTerm.implies_elim(pt, pt_assert)
    #         #     return pt
    #         else:
    #             return ProofTerm.sorry(Thm([], t))
    #     else:
    #         raise NotImplementedError

    # # Try use sat solver combines with assertions to prove the conclusion
    # else:
    #     return pt  

def quant_inst(p):
    """
    A proof of (or (not (forall (x) (P x))) (P a))
    Note: because "a" maybe not equal to "x", so we need to
    replace "x" by "a" when necessary.
    """
    pat = ProofTerm.theorem('forall_elim')
    f = Implies(p.arg1.arg, p.arg)
    inst = matcher.first_order_match(pat.prop, f)
    pt1 = apply_theorem('forall_elim', inst=inst)
    
    old_var = Var("x", pt1.prop.arg1.arg.var_T)
    new_var = Var(p.arg1.arg.arg.var_name, p.arg1.arg.arg.var_T)

    if old_var != new_var: 
        # we must subsitute old_var by new var
        # example: |- (!x. s x = 0) --> s 2 = 0) to |- (!n. s n = 0) --> s 2 = 0)
        ptn1 = ProofTerm.assume(pt1.prop.arg1) # !x. s x = 0 |- !x. s x = 0
        ptn2 = ptn1.forall_elim(new_var) # !x. s x = 0 |- s n = 0 
        ptn3 = ptn2.forall_intr(new_var) # !x. s x = 0 |- !n. s n = 0
        ptn4 = ProofTerm.assume(ptn3.prop) # !n. s n = 0 |- !n. s n = 0
        ptn5 = ptn4.forall_elim(old_var) # !n. s n = 0 |- s x = 0
        ptn6 = ptn5.forall_intr(old_var) # !n. s n = 0 |- !x. s x = 0
        ptn7 = pt1.implies_elim(ptn6) # !n. s n = 0 |- s 2 = 0
        pt1 = ptn7.implies_intr(ptn7.hyps[0]) # |- (!n. s n = 0) --> s 2 = 0

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
        pt = ProofTerm.sorry(Thm(arg2.th.hyps + arg1.th.hyps, arg2.prop))
    return pt

def iff_true(arg1, arg2):
    """
    arg1: ⊢ p
    return: ⊢ p <--> true
    """
    pt1 = apply_theorem('eq_true', inst=Inst(A=arg1.prop))
    return ProofTerm.equal_elim(pt1, arg1)

def iff_false(arg1, arg2):
    """
    arg1: ⊢ ¬p
    return: ⊢ ¬p <--> false
    """
    pt1 = apply_theorem('eq_false', inst=Inst(A=arg1.prop.arg))
    return ProofTerm.equal_elim(pt1, arg1)

def not_or_elim(arg1, arg2):
    """
    For the reason that z3 elimates double neg term implicitly, so arg2 may be negative or positive.  
    There are two cases:
    1) arg2 is a negative term: ¬t: we need to check if there exists a disjunct in arg1
    proposition which is equal to t;
    2) arg2 is a positive term t: we need to check if there exists a disjunct in arg1's proposition
    which is equal to ¬t;
    """
    global disj_expr
    if arg1.prop not in disj_expr:
        disj_expr.update({arg1.prop: dict()})
    
    for key, value in disj_expr[arg1.prop].items():
        if key == arg2:
            print("!!!")
            return value        

    disj = arg2.arg if arg2.is_not() else Not(arg2)

    pt = arg1
    while pt.prop.arg.is_disj():
        disj1, disj2 = pt.prop.arg.arg1, pt.prop.arg.arg
        pt_l, pt_r = apply_theorem('not_or_elim1', pt).on_prop(try_conv(rewr_conv('double_neg'))),\
            apply_theorem('not_or_elim2', pt).on_prop(try_conv(rewr_conv('double_neg')))
        disj_expr[arg1.prop].update({disj1: pt_l, disj2: pt_r})
        if disj1 == disj:
            return pt_l.on_prop(try_conv(rewr_conv('double_neg')))
        elif disj2 == disj:
            return pt_r.on_prop(try_conv(rewr_conv('double_neg')))
        else:
            pt = pt_r
    assert pt.prop == disj
    return pt.on_prop(try_conv(rewr_conv('double_neg')))

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
    for reason that prove need propositional logic decision procedure,
    currently use proofterm.sorry
    """
    # Ts = analyze_type(arg1)
    # if IntType in Ts:
    #     pt = refl(arg1).on_rhs(
    #         top_conv(rewr_conv('int_ite01')),
    #         bottom_conv(rewr_conv('eq_mean_true')),
    #         bottom_conv(integer.int_norm_eq()),
    #         bottom_conv(integer.int_neq_false_conv()),
    #         proplogic.norm_full()
    #     )
    #     pt = pt.symmetric()
    #     try:
    #         basic.load_theory('sat')
    #         pt_cnf = solve_cnf(pt.lhs)
    #         basic.load_theory('smt')
    #         return pt.equal_elim(pt_cnf)
    #     except:
    #         pass
    # try:
    #     return solve_cnf(arg1)
    # except:
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

def unit_resolution(pt1, pts, concl, z3terms):
    """
    T1: (or l_1 ... l_n l_1' ... l_m')
    T2: (not l_1)
    ...
    T(n+1): (not l_n)
    [unit-resolution T1 ... T(n+1)]: (or l_1' ... l_m')

    parameters: pt1 is T1 in HOL, pts is [T2,...,Tn+1] in HOL, concl is the prop in HOL 
    which we want to prove, z3terms are the original T1,...,Tn+1, with unit-resolution ...

    a) get n, n = len(z3terms) - 2
    b) use a set to record T1's disjunction structure, every time resolution
    with Ti, the set delete corresponding li.
    c) call resolution method to resolve each Ti.
    """
    n = len(z3terms) - 2
    original_disj = z3terms[0].arg(z3terms[0].num_args() - 1)
    if z3.is_or(original_disj):
        literals = [translate(original_disj.arg(i)) for i in range(original_disj.num_args())]
    else:
        literals = [translate(original_disj)]
    resolved_literal = None
    disj1 = literals
    pt_resolved = pt1

    for i in range(n):
        if resolved_literal is not None:
            disj1.remove(resolved_literal)

        disj2 = [translate(z3terms[i+1].arg(z3terms[i+1].num_args() - 1))]
        side = None
        for j, t1 in enumerate(disj1):
            if t1 == Not(disj2[0]):
                side = 'right'
                break
            elif Not(t1) == disj2[0]:
                side = 'left'
                break
        
        assert side is not None, 'literal not found'

        resolved_literal = disj1[j]

        
        disj1 = [disj1[j]] + disj1[:j] + disj1[j+1:]
        eq_pt1 = imp_disj_iff(Eq(pt_resolved.prop, Or(*disj1)))
        new_pt1 = ProofTerm.equal_elim(eq_pt1, pt_resolved)
        new_pt2 = pts[i]
        if side == 'left': 
            if len(disj1) > 1:
                pt_resolved = apply_theorem('resolution_left', new_pt1, new_pt2)
            else: # len(disj1) == 1 and len(disj2) == 1
                pt_resolved = apply_theorem('negE', new_pt2, new_pt1)
        else: # side == 'right'
            if len(disj1) > 1:
                pt_resolved = apply_theorem('resolution_right', new_pt2, new_pt1)
            else:
                pt_resolved = apply_theorem('negE', new_pt1, new_pt2)

    return pt_resolved


def lemma(arg1, arg2, subterm):
    """
    arg1 is proof: Γ ∪ {L1, L2, ..., Ln} ⊢ ⟂
    return proof: Γ ⊢ ¬L1 ∨ ... ∨ ¬Ln

    L1,...,Ln are propositions stored in the set when use hypothesis rule. 

    the implementation stategy is match arg1's hyps with the set, and use implies_intr()
    move them to props, then
    recursively using theorem "A->B --> ¬A ∨ B"

    And because L1, L2, ..., Ln have an order, so we need the original z3 term.
    """
    subterm = subterm[-1]
    if z3.is_or(subterm):
        subs = [subterm.arg(i) for i in range(subterm.num_args())]
    else:
        subs = [subterm]
    literal = []
    for s in subs:
        if z3.is_not(s):
            literal.append(translate(s.arg(0)))
        else:
            literal.append(Not(translate(s)))
    # hyps = [p for p in arg1.th.hyps if p in hypos] # store hyps
    pt1 = arg1
    for h in reversed(literal):
        pt1 = pt1.implies_intr(h)
    # now we have Γ ⊢ L1 --> L2 --> ...--> Ln --> ⟂
    cv1 = top_conv(rewr_conv('disj_conv_imp', sym=True))
    cv2 = top_sweep_conv(rewr_conv('disj_false_right'))
    cv3 = top_conv(rewr_conv('double_neg'))
    return pt1.on_prop(cv1, cv2, cv3)


def sk(arg1):
    """
    Skolemization rule, currently have no idea on how to reconstruct it.
    """
    return ProofTerm.sorry(Thm([], Eq(arg1.lhs, arg1.rhs)))

class replace_conv(Conv):
    def __init__(self, pt):
        self.pt = pt

    def get_proof_term(self, t):
        if t == self.pt.prop.lhs:
            return self.pt
        else:
            raise ConvException


def real_th_lemma(args):
    """handle real th-lemma."""
    def traverse_A(pt):
        if pt.prop.is_conj():
            return traverse_A(apply_theorem('conjD1', pt)) + traverse_A(apply_theorem('conjD2', pt))
        else:
            return [pt]
    if len(args) == 1: 
        # case1: single term. e.g. Or(Not(x_4 <= 0), Not(x_4 >= 60))
        # In this case, we need to prove its negation is false.
        
        # First step, negate it and use de morgan to simplify it: And(x_4 <= 0, x_4 >= 60)
        pt1 = ProofTerm.assume(Not(args[0])).on_prop(
            top_conv(rewr_conv('de_morgan_thm2')),
            top_conv(rewr_conv('double_neg')),
            bottom_conv(norm_neg_real_ineq_conv())
        )

        # Second step, send the inequalies in conjunction to simplex, get
        # |- x_4 <= 0 --> x_4 >= 60 --> false
        # pt_norm_prop = pt1.on_prop(bottom_conv(rewr_conv('real_mul_lid', sym=True)), bottom_conv(real_eval_conv()))
        conjs = pt1.prop.strip_conj()
        try:
            pt2 = simplex.solve_hol_ineqs(conjs) # 1 * x_4 <= 0, 1 * x_4 >= 60 |- false
        except:
            return ProofTerm.sorry(Thm([], args[-1]))
        for h in reversed(conjs): # |- 1 * x_4 <= 0 --> 1 * x_4 >= 60 --> false
            pt2 = pt2.implies_intr(h)
        pt2 = pt2.on_prop(bottom_conv(rewr_conv('real_mul_lid'))) # |- x_4 <= 0 --> x_4 >= 60 --> false
        
        # Third step, construct the proof for each conjunct from the conjunction assumption, e.g.
        # 1 * x_4 <= 0, 1 * x_4 >= 60 |- 1 * x_4 <= 0
        # 1 * x_4 <= 0, 1 * x_4 >= 60 |- 1 * x_4 >= 60

        pts_A = traverse_A(ProofTerm.assume(pt1.prop))

        # Fourth step, use the conjunct proofs to do implies_elim, finally got 
        # |- 1 * x_4 <= 0 & 1 * x_4 >= 60 --> false
        pt3 = functools.reduce(lambda x, y: x.implies_elim(y), [pt2] + pts_A)
        pt4 = pt3.implies_intr(pt3.hyps[0])
        
        # Last step, prove the original formula is true
        pt5 = refl(Not(args[0])).on_rhs(
            top_conv(rewr_conv('de_morgan_thm2')),
            top_conv(rewr_conv('double_neg')),
        ) # |- Not(Or(Not(x_4 <= 0), Not(x_4 >= 60))) <--> And(x_4 <= 0, x_4 >= 60)
        pt6 = pt4.on_prop(top_conv(replace_conv(pt5.symmetric()))) # |- Not(Or(Not(x_4 <= 0), Not(x_4 >= 60))) --> false
        pt7 = apply_theorem('negI', pt6).on_prop(rewr_conv('double_neg'))
        return pt7

    else:
        # case2, there are several proofterms in args, and the last arg is false, e.g.
        # |- x_4 ≥ 60
        # |- x_2 ≤ 1
        # |- x_2 + -1 * x_4 ≥ 0
        # false
        
        # First step, send these inequalies to simplex, get
        # |- x_4 ≥ 60 --> x_2 ≤ 1 --> x_2 + -1 * x_4 ≥ 0 --> false
        ineqs = [pt.prop for pt in args[:-1]]
        try:
            pt1 = simplex.solve_hol_ineqs(ineqs)
        except:
            return ProofTerm.sorry(Thm([h for a in args[:-1] for h in a.hyps], args[-1]))
        for h in reversed(ineqs): # |- 1 * x_4 <= 0 --> 1 * x_4 >= 60 --> false
            pt1 = pt1.implies_intr(h)
        pt2 = pt1.on_prop(bottom_conv(rewr_conv('real_mul_lid')))
        
        # Second step, implies elim each given proof term's proposition with the simplex's proof term
        pt_final = functools.reduce(lambda x, y: x.implies_elim(y), [pt1] + list(args[:-1]))

        return pt_final

def int_th_lemma_1_omega(tm):
    def traverse_A(pt):
            if pt.prop.is_conj():
                return traverse_A(apply_theorem('conjD1', pt)) + traverse_A(apply_theorem('conjD2', pt))
            else:
                return [pt]
    pt_refl = refl(Not(tm))
    pt_norm = pt_refl.on_rhs(
        top_conv(proplogic.norm_full()),
        top_conv(integer.int_norm_neg_compares()), top_conv(integer.omega_form_conv()),
        top_conv(integer.omega_form_conv())
    )
    conjs = pt_norm.rhs.strip_conj()
    solver = omega.OmegaHOL(conjs)

    pt = solver.solve()
    
    # reconstruction, get proof ⊢ P
    # for now, we have a proof of e_1, ..., e_n ⊢ false
    # the proof is as following:
    # a) get ⊢ e_1 → ... → e_n -> false
    # b) get e_1 ∧ ... ∧ e_n ⊢ e_1, ..., e_1 ∧ ... ∧ e_n ⊢ e_n
    # c) get e_1 ∧ ... ∧ e_n ⊢ false QED
    # a)  
    pt_implies_false = functools.reduce(lambda x, y: x.implies_intr(y), reversed(conjs), pt)
    # b)
    conj_pts = [p.on_prop(integer.omega_form_conv()) for p in traverse_A(ProofTerm.assume(pt_norm.rhs))]
    # c)
    pt_conj_false = functools.reduce(lambda x, y: x.implies_elim(y), conj_pts, pt_implies_false)

    # final step, we already have ⊢ ¬P ⟷ e_1 ∧ ... ∧ e_n and ⊢ e_1 ∧ ... ∧ e_n → false
    # so we could derive ⊢ P
    pt_neg_prop_implies_false = pt_conj_false.implies_intr(pt_norm.rhs).on_prop(top_conv(replace_conv(pt_norm.symmetric())))
    return apply_theorem('negI', pt_neg_prop_implies_false).on_prop(rewr_conv('double_neg'))

def int_th_lemma_n_omega(tms):
    pts = tms[:-1]
    pt_norm_eq = [refl(pt.prop).on_rhs(try_conv(integer.int_norm_neg_compares()), try_conv(integer.omega_form_conv())).symmetric() for pt in pts]
    solver = omega.OmegaHOL([pt.lhs for pt in pt_norm_eq])
    pt_unsat = solver.solve()
    pt_implies_false = functools.reduce(lambda x, y: x.implies_intr(y), pt_unsat.hyps, pt_unsat)
    pt_implies_false_initial = pt_implies_false
    for pt in pt_norm_eq:
       pt_implies_false_initial = pt_implies_false_initial.on_prop(top_conv(replace_conv(pt)))
    imps, _ = pt_implies_false_initial.prop.strip_implies()
    pt_final = pt_implies_false_initial
    for imp in imps:
        pt_final = pt_final.implies_elim(ProofTerm.assume(imp))
    return pt_final 

def int_th_lemma_1_simplex(tm):
    def traverse_A(pt):
            if pt.prop.is_conj():
                return traverse_A(apply_theorem('conjD1', pt)) + traverse_A(apply_theorem('conjD2', pt))
            else:
                return [pt]
    pt_refl = refl(Not(tm))
    pt_norm = pt_refl.on_rhs(
        top_conv(rewr_conv('int_neg_equal')),
        top_conv(proplogic.norm_full()),
        top_conv(integer.int_norm_neg_compares()),
        top_conv(integer.int_simplex_form())
    )
    conjs = pt_norm.rhs.strip_conj()
    pt = simplex.unsat_integer_simplex(conjs)

    # pt = solver.solve()
    
    # reconstruction, get proof ⊢ P
    # for now, we have a proof of e_1, ..., e_n ⊢ false
    # the proof is as following:
    # a) get ⊢ e_1 → ... → e_n -> false
    # b) get e_1 ∧ ... ∧ e_n ⊢ e_1, ..., e_1 ∧ ... ∧ e_n ⊢ e_n
    # c) get e_1 ∧ ... ∧ e_n ⊢ false QED
    # a)  
    pt_implies_false = functools.reduce(lambda x, y: x.implies_intr(y), reversed(conjs), pt)
    # b)
    conj_pts = [p.on_prop(integer.int_simplex_form()) for p in traverse_A(ProofTerm.assume(pt_norm.rhs))]
    # c)
    pt_conj_false = functools.reduce(lambda x, y: x.implies_elim(y), conj_pts, pt_implies_false)

    # final step, we already have ⊢ ¬P ⟷ e_1 ∧ ... ∧ e_n and ⊢ e_1 ∧ ... ∧ e_n → false
    # so we could derive ⊢ P
    pt_neg_prop_implies_false = pt_conj_false.implies_intr(pt_norm.rhs).on_prop(top_conv(replace_conv(pt_norm.symmetric())))
    return apply_theorem('negI', pt_neg_prop_implies_false).on_prop(rewr_conv('double_neg'))

def int_th_lemma_n_simplex(tms):
    """Two cases, 
        1) ... ⊢ false
        2) ... ⊢   
    """
    pts = tms[:-1]
    pt_norm_eq = [refl(pt.prop).on_rhs(try_conv(integer.int_norm_neg_compares()), try_conv(integer.int_simplex_form())).symmetric() for pt in pts]
    # solver = omega.OmegaHOL([pt.lhs for pt in pt_norm_eq])
    # pt_unsat = solver.solve()
    pt_unsat = simplex.unsat_integer_simplex([pt.lhs for pt in pt_norm_eq])
    pt_implies_false = functools.reduce(lambda x, y: x.implies_intr(y), pt_unsat.hyps, pt_unsat)
    pt_implies_false_initial = pt_implies_false
    for pt in pt_norm_eq:
       pt_implies_false_initial = pt_implies_false_initial.on_prop(top_conv(replace_conv(pt)))
    imps, _ = pt_implies_false_initial.prop.strip_implies()
    pt_final = pt_implies_false_initial
    for imp in imps:
        pt_final = pt_final.implies_elim(ProofTerm.assume(imp))
    return pt_final

def int_th_lemma_equation(args):
    """
    args[-1] is an equation, args[:-1] can derive the only possible value for variable
    occurs in args[-1].
    For example, ¬(y ≤ 3), y ≤ 4 ⊢ 0 = -4 + y
    The proving strategy is first get the conjunction of the two hyps, eliminate the negation,
    then get the conclusion of the possible value for the varibale, finally use conversion.
    1) ¬(y ≤ 3), y ≤ 4 ⊢ ¬(y ≤ 3) ∧ y ≤ 4
    2) ¬(y ≤ 3), y ≤ 4 ⊢ y ≥ 4 ∧ y ≤ 4
    3) ¬(y ≤ 3), y ≤ 4 ⊢ y = 4
    4) ⊢ 0 = -4 + y ⟷ y = 4
    5) ⊢ ¬(y ≤ 3), y ≤ 4 ⊢ 0 = -4 + y
    """
    # if len(args) != 3 or not args[-1].prop.is_equals():
    #     return None
    
    pt1 = apply_theorem('conjI', args[0], args[1])
    pt2 = pt1.on_prop(
        top_conv(rewr_conv('int_not_less_eq')),
        top_conv(rewr_conv('int_not_greater_eq')),
        top_conv(rewr_conv('int_less_to_leq')),
        top_conv(rewr_conv('int_gt_to_geq')),
        top_conv(integer.int_eval_conv()),
    )
    if pt2.prop.arg1.is_less_eq():
        pt2 = pt2.on_prop(rewr_conv('conj_comm'))

    pt3 = pt2.on_prop(rewr_conv('int_eq_geq_leq_conj', sym=True))
    
    pt4 = refl(args[-1]).on_rhs(rewr_conv('int_eq_move_left'), arg1_conv(integer.omega_simp_full_conv()))
    if pt4.rhs.arg1.is_plus() and integer.int_eval(pt4.rhs.arg1.arg1.arg1) == -1:
        pt4 = pt4.on_rhs(rewr_conv('int_pos_neg_eq_0'), arg1_conv(integer.omega_simp_full_conv()))
    elif pt4.rhs.arg1.is_times() and integer.int_eval(pt4.rhs.arg1.arg1) == -1:
        pt4 = pt4.on_rhs(rewr_conv('int_pos_neg_eq_0'), arg1_conv(integer.omega_simp_full_conv()))
    if pt4.rhs.arg1.arg.is_number():
        pt4 = pt4.on_rhs(rewr_conv('add_move_0_r'), arg_conv(integer.int_eval_conv()))
    pt5 = pt4.on_rhs(arg1_conv(rewr_conv('int_mul_1_l')))
    return pt5.symmetric().equal_elim(pt3)
    

def match_and_apply(tm, th_name):
    """Match tm with the theorem, if successful, instantiate it."""
    for name in th_name:
        try:
            pt = ProofTerm.theorem(name)
            inst = matcher.first_order_match(pt.prop, tm)
            return pt.substitution(inst)
        except:
            continue
    return None

def int_th_lemma(args):
    if len(args) == 1:
        th_name = ['int_ite_tau', 't036', 't037']
        res = match_and_apply(args[0], th_name)
        if res:
            return res
    if len(args) == 3 and args[-1].is_equals():
        res = int_th_lemma_equation(args)
        if res:
            return res
    if len(args) == 1:        
        return int_th_lemma_1_simplex(args[0])
    else:
        return int_th_lemma_n_simplex(args)


def th_lemma(args):
    """
    th-lemma: Generic proof for theory lemmas.
    """
    tms = [p.prop if isinstance(p, ProofTerm) else p for p in args]
    Ts = set(sum([list(analyze_type(tm)) for tm in tms], []))
    try:
        if IntType in Ts:
            return int_th_lemma(args)
        elif RealType in Ts:
            return real_th_lemma(args)
    except:
        hyps = [h.prop for h in args[:-1]]
        return ProofTerm.sorry(Thm(hyps, args[-1]))

def hypothesis(prop):
    """
    any proposition asserted by hyp rule must be explicitly discharged
    later on in the proof using lemma rule.

    In order to find them quickly when apply lemma rule, we should store them
    in a set.
    """
    hypos.add(prop)
    return ProofTerm.assume(prop)

def asserted(prop):
    """
    asserted rule is used to get assertions refutation proof.
    
    There is a special case: asserted true
    """
    if prop == true:
        return apply_theorem('trueI')
    else:
        return ProofTerm.assume(prop)


def nnf_pos(pts, concl, z3terms):
    """nnf-pos are used in following cases:

    a) creating a quantifier: q = q_new ⊢ forall (x T) q = forall (x T) q_new
    b) elimating implies: p -> q ⊢ ¬p ∨ q
    iff: p <--> q ⊢ (¬p ∨ q) ∧ (p ∨ ¬q)
    
    We need to check the concl is whether a quantifier formula.
    """
    is_quant = concl.lhs.is_forall() or concl.lhs.is_exists()
    if concl.lhs.is_forall():
        pt_forall = ProofTerm.reflexive(forall(concl.lhs.arg.var_T))
        return ProofTerm.combination(pt_forall, pts[0])

def elim_unused(eq):
    """
    Given an formula ?X. p, p doesn't have X, return ?X.p ⟷ p.
    """
    lhs, rhs = eq.lhs, eq.rhs
    pt_lhs_assume = ProofTerm.assume(lhs)
    pt_rhs_assume = ProofTerm.assume(rhs)
    var = Var(lhs.arg.var_name, lhs.arg.var_T)
    # first prove ?X.p ⟶ p
    pt_lhs_elim_var = pt_lhs_assume.forall_elim(var).implies_intr(lhs)
    # second prove p ⟶ ?X.p
    pt_rhs_intro_var = pt_rhs_assume.forall_intr(var).implies_intr(rhs)
    return ProofTerm.equal_intr(pt_lhs_elim_var, pt_rhs_intro_var)

def trans(args):
    return functools.reduce(lambda x, y: x.transitive(y), args[:-1])


def convert_method(term, *args, subterms=None, assertions=[]):
    name = term.decl().name()
    if name == 'asserted': # {P} ⊢ {P}
        return asserted(args[0])
    elif name == 'hypothesis':
        return hypothesis(args[0])
    elif name == 'and-elim':
        arg1, arg2 = args
        return and_elim(arg1, arg2)
    elif name == 'not-or-elim':
        arg1, arg2, = args
        return not_or_elim(arg1, arg2)
    elif name == 'monotonicity':
        *equals, concl = args
        if subterms[-1].arg(0).decl().name() == 'distinct':
            return distinct_monotonicity(equals, concl, subterms)
        return monotonicity(equals, concl)
    elif name in ('trans', 'trans*'):
        return trans(args)
    elif name in ('mp', 'mp~'):
        arg1, arg2, _ = args
        return mp(arg1, arg2)
    elif name in ('rewrite', 'commutativity'):
        arg1, = args
        return rewrite(arg1, subterms, assertions=assertions)
    elif name == 'unit-resolution':
        return unit_resolution(args[0], args[1:-1], args[-1], subterms)
    elif name == 'nnf-pos':
        return nnf_pos(args[:-1], args[-1], subterms)
    elif name in ('nnf-pos', 'nnf-neg'):
        raise NotImplementedError
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
        return lemma(arg1, arg2, subterms)
    elif name == 'sk':
        arg1, = args
        return sk(arg1)
    elif name == 'th-lemma':
        return th_lemma(args)
    elif name == 'elim-unused':
        return elim_unused(args[0])
    else:
        raise NotImplementedError
    
local = dict()
redundant = []
hypos = set()
# store boolvars' true value in assertion which maybe implicitly used in rewrite rules.
assert_atom = set()

def delete_redundant(pt, redundant):
    """
    Because we introduce abbreviations for formula during def-intro,
    after reconstruction complete, we can delete these formulas use 
    theorem "(?t = ?t ⟹ False) ⟹ False"
    """
    new_pt = pt
    for r in redundant:
        new_pt = new_pt.implies_intr(r).forall_intr(r.lhs).forall_elim(r.rhs) \
             .implies_elim(ProofTerm.reflexive(r.rhs))
    
    return new_pt

def is_prop_fm(f):
    """Determine an assertion is whether a propositional formula."""
    if f.is_var() or f.is_const():
        return f.T == BoolType
    elif f.is_comb():
        head, args = f.head, f.args
        head_ty = head.get_type()
        head_range_ty = head_ty.strip_type()[-1]
        return head_range_ty == BoolType and all(is_prop_fm(arg) for arg in args)
    else:
        return False

atoms = dict()

def handle_assertion(ast):
    """
    Two cases:
    1) If the assertion is a conjunction, find all boolean variables or negative boolean variables
    in assertion, convert them to proofterm like "⊢ x ⟷ true" or "⊢ x ⟷ false"
    Note, the assertion conjunction may not have already been flatten, we need to preprocess it.
    
    This is a iterative process, every time we get an atom is true or false, we can also use it to get 
    more information by rewriting the assertion, until no more new information we can get.
    2) If there are more than one assertion Γ_1, ..., Γ_n, we need to first get the set of proof terms:
                                Γ_1, ..., Γ_n ⊢ Γ_1 ∧ ... ∧ Γ_n
    then do the same things as above
    """    
    global atoms
    
    def traverse(pt):
        """Note that we assume pt is right-associative"""
        while pt.prop.is_conj():
            lhs, rhs = pt.prop.arg1, pt.prop.arg
            if not lhs.is_conj():
                d[lhs] = apply_theorem('conjD1', pt)
            if not rhs.is_conj():
                d[rhs] = apply_theorem('conjD2', pt)
                break
            else:
                pt = apply_theorem('conjD2', pt)
    
    if len(ast) == 1:
        hol_ast = translate(ast[0])
        pt_ast = ProofTerm.assume(hol_ast).on_prop(proplogic.norm_full())
    else:
        hol_asts = [translate(a) for a in ast]
        pt_ast = functools.reduce(lambda x, y: apply_theorem('conjI', x, ProofTerm.assume(y)),\
                                hol_asts[1:], ProofTerm.assume(hol_asts[0])).on_prop(proplogic.norm_full())
    flag = True
    while True:
        if not pt_ast.prop.is_conj():
            break
        new_conv = []
        d = dict()
        traverse(pt_ast)
        for key, value in d.items():
            if key.is_var() and (key not in atoms or value != atoms[key]):
                atoms[key] = value.on_prop(rewr_conv('eq_true'))
                new_conv.append(atoms[key])
                flag = True
            elif key.is_not() and (key.arg not in atoms or value != atoms[key.arg]):
                atoms[key.arg] = value.on_prop(rewr_conv('eq_false'))    
                flag = True
                new_conv.append(atoms[key.arg])
            elif key.is_equals():
                lhs, rhs = key.lhs, key.rhs
                if lhs in (true, false):
                    atoms[rhs] = value.symmetric()
                    new_conv.append(atoms[rhs])
                elif rhs in (true, false):
                    atoms[lhs] = value
                    new_conv.append(atoms[lhs])
                elif not (lhs.head.is_const("IF") or rhs.head.is_const("IF")):
                    atoms[lhs] = value
                    new_conv.append(atoms[lhs])

        if flag:
            flag = False
            pt_ast = pt_ast.on_prop(
                *[top_conv(replace_conv(cv)) for cv in new_conv],
                proplogic.norm_full(),
                bottom_conv(rewr_conv('not_true')),
                bottom_conv(rewr_conv('not_false')),
                bottom_conv(rewr_conv('if_true')),
                bottom_conv(rewr_conv('if_false')), 
                bottom_conv(proplogic.norm_full()))
        else:
            break

    # normalize atoms key, for example, a pair in atoms maybe "x_9 ≤ x_3: x_9 ≤ x_3 ⟷ false",
    # we need to add a new pair: "x_3 + -1 * x_9 < 0: x_3 + -1 * x_9 < 0 ⟷ false"
    for key in list(atoms.keys()):
        if key.is_equals() or key.is_compares() and key.arg1.get_type() == RealType:
            norm_key = refl(key).on_rhs(
                bottom_conv(real_norm_comparison())
            )
            atoms[norm_key.rhs] = atoms[key].on_prop(top_conv(replace_conv(norm_key)))
            ori = atoms[key]
            if ori.rhs == false:
                pt_true = ori.on_prop(
                    rewr_conv('eq_false', sym=True),
                    norm_neg_real_ineq_conv(),
                    real_norm_comparison(),
                    rewr_conv('eq_true')
                )
                atoms[pt_true.lhs] = pt_true

def proofrec(proof, bounds=deque(), trace=False, debug=False, assertions=None):
    """
    If trace is true, print reconstruction trace.
    """
    time1 = time.perf_counter()
    global conj_expr, disj_expr
    term, net = index_and_relation(proof)
    order = DepthFirstOrder(net)
    r = dict()
    conj_expr.clear()
    disj_expr.clear()
    assert_atom.clear()
    atoms.clear()
    gaps = set()
    handle_assertion(assertions)
    for key, value in atoms.items():
        print(key, value.prop)
    with open('int_prf.txt', 'a', encoding='utf-8') as f:
        f.seek(0)
        f.truncate()
    for i in order:
        args = tuple(r[j] for j in net[i])
        # if trace:
        #     print('term['+str(i)+']', term[i])
        if z3.is_quantifier(term[i]) or term[i].decl().name() not in method:
            r[i] = translate(term[i], bounds=bounds, subterms=args)
        else:
            method_name = term[i].decl().name()
            subterms = [term[j] for j in net[i]]
            t1 = time.perf_counter()
            r[i] = convert_method(term[i], *args, subterms=subterms)
            t2 = time.perf_counter()
            with open('int_prf.txt', 'a', encoding='utf-8') as f:
                if r[i].rule == 'sorry' and method_name != 'def-axiom':
                    gaps |= set(r[i].gaps)
                    print('term['+str(i)+']', term[i], file=f)
                    print('r['+str(i)+']', r[i], t2 - t1, file=f)
                if trace:
                    print('r['+str(i)+']', term[i].decl().name(), t2 - t1, file=f)
    # conclusion = delete_redundant(r[0], redundant)
    # redundant.clear()
    time2 = time.perf_counter()
    print("total time: ", time2 - time1)
    # rpt = ProofReport()
    # theory.check_proof(r[0].export(), rpt)
    # print(rpt)
    return r[0]