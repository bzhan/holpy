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
from logic.logic import apply_theorem, resolution
from collections import deque
from functools import reduce
import operator
import json

# Z3 proof method name.
method = ('mp', 'mp~', 'asserted', 'trans', 'monotonicity', 'rewrite', 'and-elim', 'not-or-elim',
            'iff-true', 'iff-false', 'unit-resolution', 'commutativity', 'def-intro', 'apply-def',
            'def-axiom', 'iff~', 'nnf-pos', 'nnf-neg', 'sk', 'proof-bind', 'quant-inst', 'quant-intro',
            'lemma', 'hypothesis', 'symm', 'refl')

def Z3Term(proof):
    """Index all terms in z3 proof."""
    s = dict()
    id = 0
    def rec(term):
        nonlocal id
        if term not in s.keys():
            s[term] = id
            id += 1
        if not z3.is_quantifier(term) and term.decl().name() in method:
            for child in term.children():
                rec(child)
    rec(proof)
    return {value: key for key, value in s.items()}

def Z3TermGraph(proof):
    """Relation between proof terms."""
    r = dict()
    c = Z3Term(proof)
    s = {value: key for key, value in c.items()}
    for i in range(len(s)):
        r[i] = []
    def rec(proof):
        for child in proof.children():
            if proof in s.keys():
                r[s[proof]].append(s[child])
            if not z3.is_quantifier(child) and child.decl().name() in method:
                rec(child)

    rec(proof)
    return {key: list(dict.fromkeys(value).keys()) for key, value in r.items()}

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

def translate(term, bounds=dict()):
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
        bounds = {i : var[i] for i in range(term.num_vars())}
        # patterns = tuple(term.patterns(i) for i in range(term.num_patterns()))
        if term.is_lambda():
            if body.decl().name() == 'refl':
                lhs = translate(body.arg(0).arg(0), bounds)
                return ProofTerm.reflexive(Lambda(*var, lhs))
            elif body.decl().name() in method:
                prf = proofrec(z3.substitute_vars(body, z3.Const(term.var_name(0), term.var_sort(0))))
                return prf.abstraction(var[0])
            else:
                raise NotImplementedError
            
            return Lambda(*var, translate(body, bounds))
        elif term.is_exists():
            return Exists(*var, translate(body, bounds))
        elif term.is_forall():
            return Forall(*var, translate(body, bounds))
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
        elif z3.is_algebraic_value(term): # real number
            return Real(term.as_fraction())
        elif z3.is_true(term):
            return true
        elif z3.is_false(term):
            return false
        elif z3.is_const(term): # incomplete, is_const(Int(1)) == true
            return Var(term.decl().name(), sort)
        elif z3.is_add(term):
            return reduce(lambda x, y: x + y, args)
        elif term.decl().kind() == Z3_OP_UMINUS:
            return uminus(sort)(*args)
        elif z3.is_sub(term):
            return reduce(lambda x, y: x - y, args)
        elif z3.is_mul(term):
            return reduce(lambda x, y: x * y, args)
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
            return less(sort)(*args)
        elif z3.is_le(term):
            return less_eq(sort)(*args)
        elif z3.is_gt(term):
            return greater(sort)(*args)
        elif z3.is_ge(term):
            return greater_eq(sort)(*args)
        elif z3.is_distinct(term):
            ineq = [Eq(translate(args[i], bounds), translate(args[j]), bounds) for j in range(i+1, len(args)) 
                        for i in range(len(args))]
            return Not(Or(*ineq))
        elif kind == Z3_OP_UNINTERPRETED: # s(0)
            uf = translate(term.decl(), bounds)
            args = [translate(term.arg(i), bounds) for i in range(term.num_args())]
            return uf(*args)
        elif z3.is_bool(term) and kind == Z3_OP_OEQ:
            return Eq(translate(term.arg(0)), translate(term.arg(0)))
        else:
            raise NotImplementedError
    else:
        raise NotImplementedError

def and_elim(pt, concl):
    context.set_context('logic_base')
    r = dict()
    def rec(pt):
        if pt.prop.is_conj():
            rec(apply_theorem('conjD1', pt))
            rec(apply_theorem('conjD2', pt))
        else:
            r[pt.prop] = pt
    rec(pt)
    return r[concl]

def monotonicity(*pts):
    ptl = pts[-1]
    lhs, rhs = ptl.arg1, ptl.arg
    assert lhs.head == rhs.head
    pf = ProofTerm.reflexive(lhs.head)

    new_pf = []
    if len(lhs.args) == 2:
        if lhs.arg1 == rhs.arg1:
            new_pf = [ProofTerm.reflexive(lhs.arg1)] + [pts[0]]
        elif lhs.arg == rhs.arg:
            new_pf = [pts[0]] + [ProofTerm.reflexive(lhs.arg)]
        else:
            new_pf = pts[:-1]
    else:
        new_pf = pts[:-1]

    for pt in new_pf:
        pf = pf.combination(pt)

    return pf

def schematic_rules(thms, lhs, rhs):
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
    th_name = [f_data['content'][i]['name'] for i in range(len(f_data['content']))]
    pt = schematic_rules(th_name, t.lhs, t.rhs)  # rewrite by schematic theorems 
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
                raise NotImplementedError
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
    basic.load_theory('logic')
    f = Implies(p.prop, q)
    is_exists = q.lhs.is_exists()
    pat = ProofTerm.theorem('quant_intro_exists') if is_exists else ProofTerm.theorem('quant_intro_forall')
    inst = matcher.first_order_match(pat.prop, f)
    pt1 = apply_theorem('quant_intro_exists', inst=inst) if is_exists else apply_theorem('quant_intro_forall', inst=inst)
    pt3 = pt1.implies_elim(p)
    return pt3

def convert_method(term, *args):
    name = term.decl().name()
    if name in ('asserted', 'hypothesis'): # {P} ⊢ {P}
        return ProofTerm.assume(args[0])
    elif name == 'and-elim':
        arg1, arg2 = args
        return and_elim(arg1, arg2)
    elif name == 'monotonicity':
        return monotonicity(*args)
    elif name == 'trans':
        arg1, arg2, _ = args
        return arg1.transitive(arg2)
    elif name in ('mp', 'mp~'):
        arg1, arg2, _ = args
        return ProofTerm.equal_elim(arg2, arg1)
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
    # elif name == 'lemma':
    #     return 
    elif name == 'symm':
        return args[0].symmetric()
    elif name == 'refl':
        return ProofTerm.reflexive(args[0])
    else:
        raise NotImplementedError
    


def proofrec(proof):
    term = Z3Term(proof)
    net = Z3TermGraph(proof)
    order = DepthFirstOrder(net)
    r = dict()

    for i in order:
        args = (r[j] for j in net[i])
        # print('term['+str(i)+']', term[i])
        if z3.is_quantifier(term[i]) or term[i].decl().name() not in method:
            r[i] = translate(term[i])
        else:
            r[i] = convert_method(term[i], *args)
            # basic.load_theory('int')
            # print('r['+str(i)+']', r[i])
    return r[0]

    