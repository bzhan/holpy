# Author: Bohua Zhan

"""Hindley-Milner type inference algorithm."""

from kernel.type import STVar, TFun
from kernel.term import Term
from kernel import term
from kernel import theory
from logic import context
from util import unionfind


class TypeInferenceException(Exception):
    def __init__(self, err):
        assert isinstance(err, str)
        self.err = err


def is_internal_type(T):
    return T.is_stvar() and T.name.startswith('_t')

def type_infer(t, *, forbid_internal=True):
    """Perform type inference on the given term. The input term
    has all types marked None, except those subterms whose type is
    explicitly given. This function works on terms with overloaded
    constants.
    
    """
    # Union-find mapping for representatives of temporary
    # type variables.
    uf = dict()

    # Reachability relation between temporary type variables.
    reach = dict()

    # Number of internal type variables created.
    num_internal = 0

    # Records type of variables assigned during inference. This enforces
    # the condition that all occurrence of a variable have the same type.
    incr_ctxt = dict()
    incr_sctxt = dict()

    # Create and return a new type variable.
    def new_type():
        nonlocal num_internal
        T = STVar('_t' + str(num_internal))
        uf[num_internal] = T
        reach[num_internal] = set()
        num_internal += 1
        return T

    def union(T1, T2):
        """Join temporary type variable T1 with T2."""
        # Compute the set of temporary type variables reachable from T2.
        if is_internal_type(T2):
            new_reach = reach[int(T2.name[2:])]
        else:
            new_reach = set()
            for T in T2.get_stvars():
                if is_internal_type(T):
                    new_reach.add(int(T.name[2:]))
                    new_reach.update(reach[int(T.name[2:])])

        # Update uf and reach, check for cycles in reach.
        for k, v in uf.items():
            if uf[k] == T1:
                if k in new_reach:
                    raise TypeInferenceException("Infinite loop")
                uf[k] = T2
                reach[k].update(new_reach)

    def unify(T1, T2):
        """Unification of two types."""
        # First, find representatives of T1 and T2
        if is_internal_type(T1):
            T1 = uf[int(T1.name[2:])]
        if is_internal_type(T2):
            T2 = uf[int(T2.name[2:])]

        # Type constructors, recursively unify each argument
        if T1.is_type() and T2.is_type() and T1.name == T2.name:
            for i in range(len(T1.args)):
                unify(T1.args[i], T2.args[i])

        # Concrete type variables
        elif T1.is_tvar() and T2.is_tvar() and T1.name == T2.name:
            return

        elif T1.is_stvar() and T2.is_stvar() and T1.name == T2.name:
            return

        # Internal (unifiable) type variables
        elif is_internal_type(T1):
            union(T1, T2)
        elif is_internal_type(T2):
            union(T2, T1)
        else:
            raise TypeInferenceException("Unable to unify " + str(T1) + " with " + str(T2))

    def infer(t, bd_vars):
        """Infer the type of T."""
        # Var case: if type is not known, try to obtain it from context,
        # otherwise, make a new type.
        if t.is_svar():
            if t.T is None:
                if t.name in context.ctxt.svars:
                    t.T = context.ctxt.svars[t.name]
                elif t.name in incr_sctxt:
                    t.T = incr_sctxt[t.name]
                else:
                    t.T = new_type()
                    incr_sctxt[t.name] = t.T
            return t.T

        elif t.is_var():
            if t.T is None:
                if t.name in context.ctxt.vars:
                    t.T = context.ctxt.vars[t.name]
                elif t.name in incr_ctxt:
                    t.T = incr_ctxt[t.name]
                else:
                    t.T = new_type()
                    incr_ctxt[t.name] = t.T
            return t.T

        # Const case: if type is not known, obtain it from theory,
        # replacing arbitrary variables by new types.
        elif t.is_const():
            if t.T is None:
                try:
                    T = theory.thy.get_term_sig(t.name, stvar=True)
                except theory.TheoryException as e:
                    if t.name in context.ctxt.defs:
                        T = context.ctxt.defs[t.name]
                    else:
                        raise e
                tyinst = dict()
                for STv in T.get_stvars():
                    tyinst[STv.name] = new_type()
                t.T = T.subst(tyinst)
            return t.T

        # Comb case: recursively infer type of fun and arg, then
        # unify funT with argT => resT, where resT is a new type.
        elif t.is_comb():
            funT = infer(t.fun, bd_vars)
            argT = infer(t.arg, bd_vars)
            try:
                if not funT.is_fun() and not is_internal_type(funT):
                    raise TypeInferenceException(str(funT) + ' is not of function type')
                if funT.is_fun():
                    unify(funT.domain_type(), argT)
                    return funT.range_type()
                else:
                    resT = new_type()
                    unify(funT, TFun(argT, resT))
                    return resT
            except TypeInferenceException as e:
                err_str = e.err + '\n'
                err_str += "When infering type of " + str(t) + "\n"
                err_str += "Type of %s: %s\n" % (t.fun, str(funT))
                err_str += "Type of %s: %s\n" % (t.arg, str(argT))
                raise TypeInferenceException(err_str)

        # Abs case: if var_T is not known, make a new type. Recursively
        # call infer on the body under the context where var_name has
        # type var_T. The resulting type is var_T => body_T.
        elif t.is_abs():
            if t.var_T is None:
                t.var_T = new_type()
            bodyT = infer(t.body, [t.var_T] + bd_vars)
            return TFun(t.var_T, bodyT)

        # Bound variables.
        elif t.is_bound():
            return bd_vars[t.n]

        else:
            raise TypeError

    if context.ctxt.defs and t.is_equals():
        t_head, t_args = t.lhs.strip_comb()
        if t_head.is_const() and t_head.name in context.ctxt.defs:
            t_head.T = context.ctxt.defs[t_head.name]

    infer(t, [])

    # Replace vars and constants with the appropriate type.
    tyinst = dict()
    for i in range(num_internal):
        tyinst['_t' + str(i)] = uf[i]

    unspecified = []
    for k, v in tyinst.items():
        if v == STVar(k):
            unspecified.append(k)

    if forbid_internal and len(unspecified) > 0:
        raise TypeInferenceException("Unspecified type\n" + repr(t))

    has_repl = True
    while has_repl:
        has_repl = False
        for i in range(num_internal):
            T = tyinst['_t' + str(i)]
            stvars = [subT for subT in T.get_stvars() if is_internal_type(subT)]
            if any(v.name not in unspecified for v in stvars):
                tyinst['_t' + str(i)] = T.subst(tyinst)
                has_repl = True

    t.subst_type_inplace(tyinst)

    return t

def infer_printed_type(t):
    """Infer the types that should be printed.
    
    The algorithm is as follows:
    1. Replace all constant types with None.
    2. Apply type-inference on the resulting type.
    3. For the first internal type variable that appears, find a constant
       whose type contains that variable, set that constant to print_type.
    4. Repeat until no internal type variables appear.
    
    """
    from logic.context import Context

    def clear_const_type(t):
        if t.is_const() and not hasattr(t, "print_type"):
            t.backupT = t.T
            t.T = None
        elif t.is_comb():
            clear_const_type(t.fun)
            clear_const_type(t.arg)
        elif t.is_abs():
            if not hasattr(t, "print_type"):
                t.backup_var_T = t.var_T
                t.var_T = None
            clear_const_type(t.body)

    def recover_const_type(t):
        if t.is_const():
            t.T = t.backupT
        elif t.is_comb():
            recover_const_type(t.fun)
            recover_const_type(t.arg)
        elif t.is_abs():
            t.var_T = t.backup_var_T
            recover_const_type(t.body)

    for i in range(100):
        clear_const_type(t)
        type_infer(t, forbid_internal=False)

        def has_internalT(T):
            return any(is_internal_type(subT) for subT in T.get_tsubs())

        to_replace, to_replaceT = None, None
        def find_to_replace(t):
            nonlocal to_replace, to_replaceT
            if (t.is_zero() or t.is_one() or \
                (t.is_comb('of_nat', 1) and t.arg.is_binary() and t.arg.dest_binary() >= 2)) and \
                has_internalT(t.get_type()):
                replT = t.get_type()
                if t.is_comb():
                    t = t.fun
                if to_replace is None or len(str(replT)) < len(str(to_replaceT)):
                    to_replace = t
                    to_replaceT = replT
            elif t.is_const() and has_internalT(t.T):
                if to_replace is None or len(str(t.T)) < len(str(to_replaceT)):
                    to_replace = t
                    to_replaceT = t.T
            elif t.is_abs():
                if has_internalT(t.var_T):
                    if to_replace is None or len(str(t.var_T)) < len(str(to_replaceT)):
                        to_replace = t
                        to_replaceT = t.var_T
                find_to_replace(t.body)
            elif t.is_comb():
                find_to_replace(t.fun)
                find_to_replace(t.arg)

        find_to_replace(t)
        recover_const_type(t)

        if to_replace is None:
            break

        to_replace.print_type = True

    assert i != 99, "infer_printed_type: infinite loop."

    return None
