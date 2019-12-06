# Author: Bohua Zhan

import itertools

from kernel.type import TVar, TFun, boolT, Type
from kernel import term
from kernel.term import Var, Const, Term
from kernel.thm import Thm

from kernel import extension
from logic import logic

"""Inductive definitions.

Example:

Definition of natural numbers:

nat = 0 | Suc nat

Automatically generated theorems:

nat_0_Suc_neq: 0 ~= Suc n
nat_Suc_inject: Suc m = Suc n --> m = n
nat_induct: P 0 --> (!n. P n --> P (Suc n)) --> P x

Examples of definitions by induction:

plus: nat => nat => nat
  plus 0 n = n
| plus (Suc m) n = Suc (plus m n)

"""

def add_induct_type(thy, name, targs, constrs):
    """Add the given inductive type to the theory.
    
    The inductive type is specified by name, arity (as list of default
    names of type arguments), and a list of constructors (triple
    consisting of name of the constant, type of the constant, and a
    list of suggested names of the arguments).

    For example, the natural numbers is specified by:
    (nat, [], [(0, nat, []), (Suc, nat => nat, ["n"])]).

    List type is specified by:
    (list, ["a"], [(nil, 'a list, []), (cons, 'a => 'a list => 'a list, ["x", "xs"])]).

    """
    exts = []

    # Add to type and term signature.
    exts.append(extension.Type(name, len(targs)))
    for constr_name, cT, _ in constrs:
        ref_name = thy.get_overload_const_name(constr_name, cT)
        exts.append(extension.Constant(constr_name, cT, ref_name=ref_name))

    # Add non-equality theorems.
    for (cname1, cT1, vars1), (cname2, cT2, vars2) in itertools.combinations(constrs, 2):
        # For each A x_1 ... x_m and B y_1 ... y_n, get the theorem
        # ~ A x_1 ... x_m = B y_1 ... y_n.
        argT1, _ = cT1.strip_type()
        argT2, _ = cT2.strip_type()
        lhs_vars = [Var(nm, T) for nm, T in zip(vars1, argT1)]
        rhs_vars = [Var(nm, T) for nm, T in zip(vars2, argT2)]
        A = Const(cname1, cT1)
        B = Const(cname2, cT2)
        lhs = A(*lhs_vars)
        rhs = B(*rhs_vars)
        neq = logic.neg(Term.mk_equals(lhs, rhs))
        th_name = name + "_" + cname1 + "_" + cname2 + "_neq"
        exts.append(extension.Theorem(th_name, Thm([], neq)))

    # Add injectivity theorems.
    for cname, cT, vars in constrs:
        # For each A x_1 ... x_m with m > 0, get the theorem
        # A x_1 ... x_m = A x_1' ... x_m' --> x_1 = x_1' & ... & x_m = x_m'
        if vars:
            argT, _ = cT.strip_type()
            lhs_vars = [Var(nm, T) for nm, T in zip(vars, argT)]
            rhs_vars = [Var(nm + "'", T) for nm, T in zip(vars, argT)]
            A = Const(cname, cT)
            assum = Term.mk_equals(A(*lhs_vars), A(*rhs_vars))
            concls = [Term.mk_equals(var1, var2) for var1, var2 in zip(lhs_vars, rhs_vars)]
            concl = logic.mk_conj(*concls) if len(concls) > 1 else concls[0]
            th_name = name + "_" + cname + "_inject"
            exts.append(extension.Theorem(th_name, Thm.mk_implies(assum, concl)))

    # Add the inductive theorem.
    tvars = [TVar(targ) for targ in targs]
    T = Type(name, *tvars)
    var_P = Var("P", TFun(T, boolT))
    ind_assums = []
    for cname, cT, vars in constrs:
        A = Const(cname, cT)
        argT, _ = cT.strip_type()
        args = [Var(nm, T2) for nm, T2 in zip(vars, argT)]
        C = var_P(A(*args))
        As = [var_P(Var(nm, T2)) for nm, T2 in zip(vars, argT) if T2 == T]
        ind_assum = Term.mk_implies(*(As + [C]))
        for arg in reversed(args):
            ind_assum = Term.mk_all(arg, ind_assum)
        ind_assums.append(ind_assum)
    ind_concl = var_P(Var("x", T))
    th_name = name + "_induct"
    exts.append(extension.Theorem(th_name, Thm.mk_implies(*(ind_assums + [ind_concl]))))
    exts.append(extension.Attribute(th_name, "var_induct"))

    return exts

def add_induct_def(thy, name, T, eqs):
    """Add the given inductive definition.

    The inductive definition is specified by the name and type of
    the constant, and a list of equations.

    For example, addition on natural numbers is specified by:
    ('plus', nat => nat => nat,
     [(plus(0,n) = n, plus(Suc(m), n) = Suc(plus(m, n)))]).

    Multiplication on natural numbers is specified by:
    ('times', nat => nat => nat,
    [(times(0,n) = 0, times(Suc(m), n) = plus(n, times(m,n)))]).

    """
    exts = []
    cname = thy.get_overload_const_name(name, T)
    exts.append(extension.Constant(name, T, ref_name=cname))
    for i, prop in enumerate(eqs):
        th_name = cname + "_def_" + str(i + 1)
        exts.append(extension.Theorem(th_name, Thm([], prop)))
        exts.append(extension.Attribute(th_name, "hint_rewrite"))

    return exts

def add_induct_predicate(thy, name, T, props):
    """Add the given inductive predicate.

    The inductive predicate is specified by the name and type of
    the predicate, and a list of introduction rules, where each
    introduction rule must be given a name.

    """
    exts = []
    cname = thy.get_overload_const_name(name, T)
    exts.append(extension.Constant(name, T, ref_name=cname))

    for th_name, prop in props:
        exts.append(extension.Theorem(th_name, Thm([], prop)))
        exts.append(extension.Attribute(th_name, "hint_backward"))

    # Case rule
    Targs, _ = T.strip_type()
    vars = []
    for i, Targ in enumerate(Targs):
        vars.append(Var("_a" + str(i+1), Targ))

    P = Var("P", boolT)
    pred = Const(name, T)
    assum0 = pred(*vars)
    assums = []
    for th_name, prop in props:
        As, C = prop.strip_implies()
        assert C.head == pred, "add_induct_predicate: wrong form of prop."
        eq_assums = [Term.mk_equals(var, arg) for var, arg in zip(vars, C.args)]
        assum = Term.mk_implies(*(eq_assums + As), P)
        prop_vars = term.get_vars(prop)
        for var in reversed(term.get_vars(prop)):
            assum = Term.mk_all(var, assum)
        assums.append(assum)

    cname = thy.get_overload_const_name(name, T)
    prop = Term.mk_implies(*([assum0] + assums + [P]))
    exts.append(extension.Theorem(cname + "_cases", Thm([], prop)))

    return exts
