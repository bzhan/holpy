import z3
from z3.z3consts import *

from kernel.type import TFun, BoolType, NatType, IntType, RealType, STVar
from kernel.term import *
from kernel.thm import Thm
from kernel.proofterm import ProofTerm
from kernel import theory
from logic import basic, context
from logic.logic import apply_theorem

from collections import deque, namedtuple
from functools import reduce
import operator

# Z3 proof method name.
method = ('mp', 'mp~', 'asserted', 'trans', 'monotonicity', 'rewrite', 'and-elim', 'not-or-elim',
            'iff-true', 'iff-false', 'unit-resolution', 'comm', 'def-intro', 'apply-def', 'lambda',
            'def-axiom', 'iff~', 'nnf-pos', 'nnf-neg', 'sk')

Node = namedtuple('Node', ['term', 'tree'])

def Z3Term(proof):
    """Index all terms in z3 proof."""
    s = dict()
    id = 0
    def rec(term):
        nonlocal id
        if term not in s.keys():
            s[term] = id
            id += 1
        if term.decl().name() in method:
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
            if child.decl().name() in method:
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

def translate_type(T):
    """Translate z3 type into holpy type."""
    if T == Z3_BOOL_SORT:
        return BoolType
    elif T == Z3_INT_SORT:
        return NatType
    elif T == Z3_REAL_SORT:
        return RealType
    else:
        raise NotImplementedError

# def translate_term(term, *args, isNat=False):
#     """Convert a z3 term into holpy term. If term is a variable in nat, its type is NatType."""
#     assert all(isinstance(arg, Term) for arg in args)

#     kind = term.decl().kind() # kind of the term  
#     name = term.decl().name() # name of the term
#     sort = term.sort_kind() #sort of the term
    
#     if z3.is_int_value(term):
#         n = term.as_long()
#         if n < 0:
#             return Int(n)
#         return Nat(n) if isNat else Int(n)
#     elif z3.is_algebraic_value(term):
#         return Real(term.as_fraction())
#     elif name == 'true':
#         return true
#     elif name == 'false':
#         return false
#     elif z3.is_const(term): # note the difference of variable notion between SMT and HOL
#         return Var(name, NatType) if isNat else Var(name, translate_type(sort))
#     elif kind == Z3_OP_UMINUS: # -x
#         return -Var(term.arg(0).decl().name(), translate_type(term.sort_kind()))
#     elif kind == Z3_OP_NOT:
#         return Not(args[0]) # ¬x
#     elif kind == Z3_OP_ADD: # (+ x y z)
#         return sum(args)
#     elif kind == Z3_OP_SUB: # (- x y z)
#         return reduce(operator.sub, args[1:], args[0])
#     elif kind == Z3_OP_MUL: # (* x y z)
#         return reduce(operator.mul, args[1:], args[0])
#     elif kind == Z3_OP_DIV: # (/ x y z)
#         return reduce(operator.truediv, args[1:], args[0])
#     elif kind == Z3_OP_AND: # (and x y z)
#         return And(*args)
#     elif kind == Z3_OP_OR: # (or x y z)
#         return Or(*args)
#     elif kind == Z3_OP_IMPLIES: # (=> x y)
#         return Implies(*args) # note: z3 implies is binary.
#     elif kind == Z3_OP_EQ: # (= x y)
#         return Eq(*args)
#     elif kind == Z3_OP_GT: # (> x y)
#         return greater(translate_type(sort))(*args)
#     elif kind == Z3_OP_GE: # (≥ x y)
#         return greater_eq(translate_type(sort))(*args)
#     elif kind == Z3_OP_LT: # (< x y)
#         return less(translate_type(sort))(*args)
#     elif kind == Z3_OP_LE: # (≤ x y)
#         return less_eq(translate_type(sort))(*args)
#     elif kind == Z3_OP_UNINTERPRETED: # s(0)
#         types = [translate_type(term.arg(i).sort_kind()) for i in range(term.num_args())]
#         print(*types)
#         f = Var(name, TFun(types))
#         return f(*args)
#     else:
#         raise NotImplementedError

def translate(term, vars=[], isNat=True):

    if isinstance(term, z3.FuncDeclRef):
        arity = term.arity()
        rangeT = translate_type(term.range().kind())
        domainT = [translate_type(term.domain(i).kind()) for i in range(arity)]
        types = domainT + [rangeT]
        return Var(term.name(), TFun(*types))
    elif isinstance(term, z3.ExprRef):
        kind = term.decl().kind() # kind of the term  
        name = term.decl().name() # name of the term
        sort = term.sort_kind() #sort of the term

        if z3.is_int_value(term):
            n = term.as_long()
            if n < 0:
                return Int(n)
            return Nat(n) if isNat else Int(n)
        elif z3.is_algebraic_value(term):
            return Real(term.as_fraction())
        elif name == 'true':
            return true
        elif name == 'false':
            return false
        elif z3.is_const(term): # note the difference of variable notion between SMT and HOL
            return Var(name, NatType) if name in vars else Var(name, IntType)
        elif kind == Z3_OP_ADD:
            return sum([translate(term.arg(i), vars) for i in range(term.num_args())])
        elif kind == Z3_OP_MUL:
            args = [translate(term.arg(i), vars) for i in range(term.num_args())]
            return reduce(operator.mul, args[1:], args[0])
        elif kind == Z3_OP_EQ:
            return Eq(translate(term.arg(0), vars), translate(term.arg(1), vars))
        elif kind == Z3_OP_NOT:
            return Not(translate(term.arg(0), vars))
        elif kind == Z3_OP_AND:
            args = [translate(term.arg(i), vars) for i in range(term.num_args())]
            return And(*args)
        elif kind == Z3_OP_OR:
            args = [translate(term.arg(i), vars) for i in range(term.num_args())]
            return Or(*args)
        elif kind == Z3_OP_UNINTERPRETED: # s(0)
            uf = translate(term.decl())
            args = [translate(term.arg(i), vars) for i in range(term.num_args())]
            return uf(*args)
        else:
            raise NotImplementedError
    else:
        raise NotImplementedError

def and_elim(imp):
    context.set_context('nat')
    macro = theory.global_macros['imp_conj']
    pt1 = macro.get_proof_term(imp, None)
    return macro.get_proof_term(imp, None)

def new_and_elim(pt, concl):
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

def mono(*pts):
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

def rewrite(t):
    if t.arg1.get_type() == BoolType:
        return ProofTerm.sorry(Thm([], t))
    else:
        context.set_context('nat')
        macro = theory.global_macros['nat_norm']
        return macro.get_proof_term(t, [])

def convert_method(term, *args):
    name = term.decl().name()
    if name == 'asserted': # {P} ⊢ {P}
        return ProofTerm.assume(args[0])
    elif name == 'and-elim':
        arg1, arg2 = args
        return new_and_elim(arg1, arg2)
    elif name == 'monotonicity':
        return mono(*args)
    elif name == 'trans':
        arg1, arg2, _ = args
        return arg1.transitive(arg2)
    elif name == 'mp':
        arg1, arg2, _ = args
        return ProofTerm.equal_elim(arg2, arg1)
    elif name == 'rewrite':
        arg1, = args
        return rewrite(arg1)
    else:
        raise NotImplementedError
    


def proofrec(proof):
    term = Z3Term(proof)
    net = Z3TermGraph(proof)
    order = DepthFirstOrder(net)
    r = dict()

    for i in order:
        name = term[i].decl().name()
        args = (r[j] for j in net[i])
        if name not in method:
            r[i] = translate(term[i], ['A', 'B'])
        else:
            r[i] = convert_method(term[i], *args)
            basic.load_theory('nat')
    return r[0]