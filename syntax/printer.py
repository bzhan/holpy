# Author: Bohua Zhan

from copy import copy

from kernel.type import HOLType
from kernel.term import Term, OpenTermException
from kernel.extension import Extension
from kernel import proof
from syntax.operator import OperatorData
from syntax import settings
from syntax import infertype

# 0, 1, 2, 3 = NORMAL, BOUND, VAR, TVAR
def N(s):
    return [(s, 0)] if settings.highlight() else s

def B(s):
    return [(s, 1)] if settings.highlight() else s

def V(s):
    return [(s, 2)] if settings.highlight() else s

def TV(s):
    return [(s, 3)] if settings.highlight() else s

def Gray(s):
    return [(s, 4)] if settings.highlight() else s

def optimize_highlight(lst):
    """Optimize a highlight list (s1, n1), ... by combining parts that have
    the same color.

    """
    if len(lst) == 0:
        return lst
    else:
        prev = lst[0]
        new_lst = []
        for s, n in lst[1:]:
            if s.strip() == "" or prev[1] == n:
                # Combine with previous:
                prev = (prev[0] + s, prev[1])
            else:
                new_lst.append(prev)
                prev = (s, n)
        new_lst.append(prev)
    return new_lst

@settings.with_settings
def commas_join(strs):
    """Given a list of output (with or without highlight), join them with
    commas, adding commas with normal color in the highlight case.

    """
    strs = list(strs)  # convert possible generator to concrete list
    if settings.highlight():
        if strs:
            res = strs[0]
            for s in strs[1:]:
                res.append((', ', 0))
                res = res + s
            return res
        else:
            return []
    else:
        return ', '.join(strs)

@settings.with_settings
def print_type(thy, T):
    def helper(T):
        if T.ty == HOLType.TVAR:
            return TV("'" + T.name)
        elif T.ty == HOLType.TYPE:
            if len(T.args) == 0:
                return N(T.name)
            elif len(T.args) == 1:
                # Insert parenthesis if the single argument is a function.
                if HOLType.is_fun(T.args[0]):
                    return N("(") + helper(T.args[0]) + N(") " + T.name)
                else:
                    return helper(T.args[0]) + N(" " + T.name)
            elif HOLType.is_fun(T):
                # 'a => 'b => 'c associates to the right. So parenthesis is
                # needed to express ('a => 'b) => 'c.
                fun_str = N(" ⇒ ") if settings.unicode() else N(" => ")
                if HOLType.is_fun(T.args[0]):
                    return N("(") + helper(T.args[0]) + N(")") + fun_str + helper(T.args[1])
                else:
                    return helper(T.args[0]) + fun_str + helper(T.args[1])
            else:
                return N("(") + commas_join(helper(t) for t in T.args) + N(") " + T.name)
        else:
            raise TypeError()

    res = helper(T)
    if settings.highlight():
        res = optimize_highlight(res)
    return res

@settings.with_settings
def print_term(thy, t):
    """More sophisticated printing function for terms. Handles printing
    of operators.
    
    Note we do not yet handle name collisions in lambda terms.

    """
    # Import modules for custom parsed data
    from logic import logic
    from data import nat
    from data import list
    from data import set
    from data import function
    
    def get_info_for_operator(t):
        return thy.get_data("operator").get_info_for_fun(t.head)

    def get_priority(t):
        if nat.is_binary(t) or list.is_literal_list(t):
            return 100  # Nat atom case
        elif t.is_comb():
            op_data = get_info_for_operator(t)
            if op_data is not None:
                return op_data.priority
            elif t.is_all() or logic.is_exists(t) or logic.is_if(t):
                return 10
            else:
                return 95  # Function application
        elif t.is_abs():
            return 10
        else:
            return 100  # Atom case

    def helper(t, bd_vars):
        LEFT, RIGHT = OperatorData.LEFT_ASSOC, OperatorData.RIGHT_ASSOC

        # Some special cases:
        # Natural numbers:
        if nat.is_binary(t):
            return N(str(nat.from_binary(t)))

        if list.is_literal_list(t):
            items = list.dest_literal_list(t)
            res = N('[') + commas_join(helper(item, bd_vars) for item in items) + N(']')
            if hasattr(t, "print_type"):
                return N("(") + res + N("::") + print_type(thy, t.T) + N(")")
            else:
                return res

        if set.is_literal_set(t):
            empty_set = "∅" if settings.unicode() else "{}"
            if hasattr(t, "print_type"):
                return N("(") + N(empty_set) + N("::") + print_type(thy, t.T) + N(")")
            else:
                return N(empty_set)

        if logic.is_if(t):
            P, x, y = t.args
            return N("if ") + helper(P, bd_vars) + N(" then ") + helper(x, bd_vars) + \
                   N(" else ") + helper(y, bd_vars)

        if t.is_var():
            return V(t.name)

        elif t.is_const():
            if hasattr(t, "print_type") and t.print_type:
                return N("(" + t.name + "::") + print_type(thy, t.T) + N(")")
            else:
                return N(t.name)

        elif t.is_comb():
            op_data = get_info_for_operator(t)
            # First, we take care of the case of operators
            if op_data and op_data.arity == OperatorData.BINARY and t.is_binop():
                arg1, arg2 = t.args

                # Obtain output for first argument, enclose in parenthesis
                # if necessary.
                if (op_data.assoc == LEFT and get_priority(arg1) < op_data.priority or
                    op_data.assoc == RIGHT and get_priority(arg1) <= op_data.priority):
                    str_arg1 = N("(") + helper(arg1, bd_vars) + N(")")
                else:
                    str_arg1 = helper(arg1, bd_vars)

                if settings.unicode() and op_data.unicode_op:
                    str_op = N(' ' + op_data.unicode_op + ' ')
                else:
                    str_op = N(' ' + op_data.ascii_op + ' ')

                # Obtain output for second argument, enclose in parenthesis
                # if necessary.
                if (op_data.assoc == LEFT and get_priority(arg2) <= op_data.priority or
                    op_data.assoc == RIGHT and get_priority(arg2) < op_data.priority):
                    str_arg2 = N("(") + helper(arg2, bd_vars) + N(")")
                else:
                    str_arg2 = helper(arg2, bd_vars)

                return str_arg1 + str_op + str_arg2

            # Unary case
            elif op_data and op_data.arity == OperatorData.UNARY:
                if settings.unicode() and op_data.unicode_op:
                    str_op = N(op_data.unicode_op)
                else:
                    str_op = N(op_data.ascii_op)

                if get_priority(t.arg) < op_data.priority:
                    str_arg = N("(") + helper(t.arg, bd_vars) + N(")")
                else:
                    str_arg = helper(t.arg, bd_vars)

                return str_op + str_arg

            # Next, the case of binders
            elif t.is_all():
                all_str = "!" if not settings.unicode() else "∀"
                if hasattr(t.arg, "print_type"):
                    var_str = B(t.arg.var_name) + N("::") + print_type(thy, t.arg.var_T)
                else:
                    var_str = B(t.arg.var_name)
                body_repr = helper(t.arg.body, [t.arg.var_name] + bd_vars)

                return N(all_str) + var_str + N(". ") + body_repr

            elif logic.is_exists(t):
                exists_str = "?" if not settings.unicode() else "∃"
                if hasattr(t.arg, "print_type"):
                    var_str = B(t.arg.var_name) + N("::") + print_type(thy, t.arg.var_T)
                else:
                    var_str = B(t.arg.var_name)
                body_repr = helper(t.arg.body, [t.arg.var_name] + bd_vars)

                return N(exists_str) + var_str + N(". ") + body_repr

            # Function update
            elif function.is_fun_upd(t):
                f, upds = function.strip_fun_upd(t)
                upd_strs = [helper(a, bd_vars) + N(" := ") + helper(b, bd_vars) for a, b in upds]
                return N("(") + helper(f, bd_vars) + N(")(") + commas_join(upd_strs) + N(")")

            # Finally, usual function application
            else:
                if get_priority(t.fun) < 95:
                    str_fun = N("(") + helper(t.fun, bd_vars) + N(")")
                else:
                    str_fun = helper(t.fun, bd_vars)
                if get_priority(t.arg) <= 95:
                    str_arg = N("(") + helper(t.arg, bd_vars) + N(")")
                else:
                    str_arg = helper(t.arg, bd_vars)
                return str_fun + N(" ") + str_arg

        elif t.is_abs():
            lambda_str = "%" if not settings.unicode() else "λ"
            if hasattr(t, "print_type"):
                var_str = B(t.var_name) + N("::") + print_type(thy, t.var_T)
            else:
                var_str = B(t.var_name)
            body_repr = helper(t.body, [t.var_name] + bd_vars)
            return N(lambda_str) + var_str + N(". ") + body_repr

        elif t.is_bound():
            if t.n >= len(bd_vars):
                raise OpenTermException
            else:
                return B(bd_vars[t.n])
        else:
            raise TypeError()

    t = copy(t)  # make copy here, because infer_printed_type may change t.
    infertype.infer_printed_type(thy, t)

    res = helper(t, [])
    if settings.highlight():
        res = optimize_highlight(res)
    return res

@settings.with_settings
def print_thm(thy, th):
    """Print the given theorem with highlight."""
    turnstile = N("⊢") if settings.unicode() else N("|-")
    if th.hyps:
        str_hyps = commas_join(print_term(thy, hyp) for hyp in th.hyps)
        return str_hyps + N(" ") + turnstile + N(" ") + print_term(thy, th.prop)
    else:
        return turnstile + N(" ") + print_term(thy, th.prop)

@settings.with_settings
def print_extension(thy, ext):
    if ext.ty == Extension.AX_TYPE:
        return "AxType " + ext.name + " " + str(ext.arity)
    elif ext.ty == Extension.AX_CONSTANT:
        return "AxConstant " + ext.name + " :: " + print_type(thy, ext.T)
    elif ext.ty == Extension.CONSTANT:
        return "Constant " + ext.name + " = " + print_term(thy, ext.expr)
    elif ext.ty == Extension.THEOREM:
        return "Theorem " + ext.name + ": " + print_term(thy, ext.th.prop)
    elif ext.ty == Extension.ATTRIBUTE:
        return "Attribute " + ext.name + " [" + ext.attribute + "]"
    elif ext.ty == Extension.MACRO:
        return "Macro " + ext.name
    else:
        raise TypeError()

@settings.with_settings
def print_extensions(thy, exts):
    return "\n".join(print_extension(thy, ext) for ext in exts.data)

@settings.with_settings
def print_str_args(thy, rule, args, prop):
    def str_val(val):
        if isinstance(val, dict):
            items = sorted(val.items(), key = lambda pair: pair[0])
            return N('{') + commas_join(N(key + ': ') + str_val(val) for key, val in items) + N('}')
        elif isinstance(val, Term):
            if val == prop and rule != 'assume' and settings.highlight():
                return Gray("⟨goal⟩")
            else:
                return print_term(thy, val)
        elif isinstance(val, HOLType):
            return print_type(thy, val)
        else:
            return N(str(val))

    # Print var :: T for variables
    if rule == 'variable' and settings.highlight():
        return N(args[0] + ' :: ') + str_val(args[1])

    if isinstance(args, tuple):
        return commas_join(str_val(val) for val in args)
    elif args:
        return str_val(args)
    else:
        return [] if settings.highlight() else ""

@settings.with_settings
def export_proof_item(thy, item):
    """Export the given proof item as a dictionary."""
    str_th = print_term(thy, item.th.prop) if item.th else ""
    str_args = print_str_args(thy, item.rule, item.args, item.th.prop)
    res = {'id': proof.print_id(item.id), 'th': str_th, 'rule': item.rule,
           'args': str_args, 'prevs': [proof.print_id(prev) for prev in item.prevs]}
    if settings.highlight():
        res['th_raw'] = print_thm(thy, item.th, highlight=False) if item.th else ""
        res['args_raw'] = print_str_args(thy, item.rule, item.args, item.th.prop, highlight=False)
    if item.subproof:
        return [res] + sum([export_proof_item(thy, i) for i in item.subproof.items], [])
    else:
        return [res]

@settings.with_settings
def print_proof_item(thy, item):
    """Print the given proof item."""
    str_id = proof.print_id(item.id)
    str_args = " " + print_str_args(thy, item.rule, item.args, item.th.prop) if item.args else ""
    str_prevs = " from " + ", ".join(proof.print_id(prev) for prev in item.prevs) if item.prevs else ""
    str_th = print_thm(thy, item.th) + " by " if item.th else ""
    cur_line = str_id + ": " + str_th + item.rule + str_args + str_prevs
    if item.subproof:
        return cur_line + "\n" + "\n".join(print_proof_item(thy, item) for item in item.subproof.items)
    else:
        return cur_line

@settings.with_settings
def print_proof(thy, prf):
    """Print the given proof."""
    return '\n'.join(print_proof_item(thy, item) for item in prf.items)

@settings.with_settings
def print_tyinst(thy, tyinst):
    """Print a type instantiation."""
    return "{" + ", ".join(nm + ": " + print_type(thy, T) for nm, T in sorted(tyinst.items())) + "}"

@settings.with_settings
def print_inst(thy, inst):
    """Print a term instantiation."""
    return "{" + ", ".join(nm + ": " + print_term(thy, t) for nm, t in sorted(inst.items())) + "}"

@settings.with_settings
def print_instsp(thy, instsp):
    """Print a pair of type and term instantiations."""
    tyinst, inst = instsp
    return print_tyinst(thy, tyinst) + ", " + print_inst(thy, inst)
