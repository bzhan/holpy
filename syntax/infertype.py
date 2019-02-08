# Author: Bohua Zhan

"""Hindley-Milner type inference algorithm."""

from kernel.type import HOLType, TVar, TFun
from kernel.term import Term, Var
from util import unionfind


class TypeInferenceException(Exception):
    def __init__(self, err):
        self.str = str

    
def is_internal_type(T):
    """Whether T is an internal type used for type inference
    (and hence can be unified).

    """
    return T.ty == HOLType.TVAR and T.name.startswith("_t")

def unify(uf, T1, T2):
    """Unification of two types. This modifies the supplied union-find
    data structure.
    
    """
    T1 = uf.find(T1)
    T2 = uf.find(T2)
    if T1.ty == HOLType.TYPE and T2.ty == HOLType.TYPE and T1.name == T2.name:
        for i in range(len(T1.args)):
            unify(uf, T1.args[i], T2.args[i])
    elif T1.ty == HOLType.TVAR and T2.ty == HOLType.TVAR and T1.name == T2.name:
        return
    elif is_internal_type(T1):
        uf.union(T2, T1, force_first=True)
    elif is_internal_type(T2):
        uf.union(T1, T2, force_first=True)
    else:
        raise TypeInferenceException("Unable to unify " + str(T1) + " with " + str(T2))

def type_infer(thy, ctxt, t):
    """Perform type inference on the given term. The input term
    has all types marked None, except those subterms whose type is
    explicitly given.
    
    """
    ctxt = ctxt.copy()  # Do not modify the input ctxt
    uf = unionfind.UnionFind()

    # Number of internal type variables created.
    num_internal = 0

    # Returns a new type variable.
    def new_type():
        nonlocal num_internal
        T = TVar("_t" + str(num_internal))
        num_internal += 1
        return T

    # Add type and all subtypes to union-find.
    def add_type(T):
        for Ts in T.get_tsubs():
            if not uf.has_key(Ts):
                uf.insert(Ts)

    # Infer the type of T.
    def infer(t):
        # Var case: if type is not known, try to obtain it from context,
        # otherwise, make a new type.
        if t.ty == Term.VAR:
            if t.T is None:
                if t.name in ctxt:
                    t.T = ctxt[t.name]
                else:
                    t.T = new_type()
            add_type(t.T)
            return t.T

        # Const case: if type is not known, obtain it from theory,
        # replacing arbitrary variables by new types.
        elif t.ty == Term.CONST:
            if t.T is None:
                T = thy.get_term_sig(t.name)
                Tvars = T.get_tvars()
                tyinst = dict()
                for Tv in Tvars:
                    tyinst[Tv.name] = new_type()
                t.T = T.subst(tyinst)
            add_type(t.T)
            return t.T

        # Comb case: recursively infer type of fun and arg, then
        # unify funT with argT => resT, where resT is a new type.
        elif t.ty == Term.COMB:
            funT = infer(t.fun)
            argT = infer(t.arg)
            resT = new_type()
            add_type(TFun(argT, resT))
            unify(uf, funT, TFun(argT, resT))
            return resT

        # Abs case: if var_T is not known, make a new type. Recursively
        # call infer on the body under the context where var_name has
        # type var_T. The resulting type is var_T => body_T.
        elif t.ty == Term.ABS:
            if t.var_T is None:
                t.var_T = new_type()
                add_type(t.var_T)
            ctxt[t.var_name] = t.var_T
            bodyT = infer(t.body)
            del ctxt[t.var_name]
            resT = TFun(t.var_T, bodyT)
            add_type(resT)
            return resT

        # Bound variables should not appear during inference.
        elif t.ty == Term.BOUND:
            raise TypeInferenceException("Unexpected bound variable")

        else:
            raise TypeError()

    infer(t)

    # Replace vars and constants with the appropriate type.
    tyinst = dict()
    for i in range(num_internal):
        rep = uf.find(TVar("_t" + str(i)))
        if is_internal_type(rep):
            raise TypeInferenceException("Unspecified type")
        tyinst["_t" + str(i)] = rep

    # Perform the necessary abstractions
    def abstract(t):
        if t.ty == Term.COMB:
            abstract(t.fun)
            abstract(t.arg)
        elif t.ty == Term.ABS:
            abstract(t.body)
            t.body = t.body.abstract_over(Var(t.var_name, t.var_T))

    abstract(t)

    # Substitute using inst until no internal variable remains
    def has_internalT(T):
        return any(is_internal_type(subT) for subT in T.get_tsubs())

    def has_internal(t):
        if t.ty == Term.VAR or t.ty == Term.CONST:
            return has_internalT(t.T)
        elif t.ty == Term.COMB:
            return has_internal(t.fun) or has_internal(t.arg)
        elif t.ty == Term.ABS:
            return has_internalT(t.var_T) or has_internal(t.body)
        else:
            return False

    while has_internal(t):
        t = t.subst_type(tyinst)

    return t
