# Author: Bohua Zhan

from copy import copy

from kernel import settings
from kernel.term import Term, OpenTermException
from logic.operator import OperatorData
from logic import logic
from logic import nat
from logic import list as hol_list
from syntax import infertype

# 0, 1, 2 = NORMAL, BOUND, VAR
def N(s):
    return [(s, 0)] if settings.highlight() else s

def B(s):
    return [(s, 1)] if settings.highlight() else s

def V(s):
    return [(s, 2)] if settings.highlight() else s

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
def print_term(thy, t):
    """More sophisticated printing function for terms. Handles printing
    of operators.
    
    Note we do not yet handle name collisions in lambda terms.

    """
    def get_info_for_operator(t):
        return thy.get_data("operator").get_info_for_fun(t.get_head())

    def get_priority(t):
        if nat.is_binary(t) or hol_list.is_literal_list(t):
            return 100  # Nat atom case
        elif t.ty == Term.COMB:
            op_data = get_info_for_operator(t)
            if op_data is not None:
                return op_data.priority
            elif t.is_all() or logic.is_exists(t) or logic.is_if(t):
                return 10
            else:
                return 95  # Function application
        elif t.ty == Term.ABS:
            return 10
        else:
            return 100  # Atom case

    def helper(t, bd_vars):
        LEFT, RIGHT = OperatorData.LEFT_ASSOC, OperatorData.RIGHT_ASSOC

        # Some special cases:
        # Natural numbers:
        if nat.is_binary(t):
            return N(str(nat.from_binary(t)))

        if hol_list.is_literal_list(t):
            items = hol_list.dest_literal_list(t)
            res = N('[') + commas_join(helper(item, bd_vars) for item in items) + N(']')
            if hasattr(t, "print_type"):
                return N("(") + res + N("::" + str(t.T) + ")")
            else:
                return res

        if logic.is_if(t):
            P, x, y = logic.dest_if(t)
            return N("if ") + helper(P, bd_vars) + N(" then ") + helper(x, bd_vars) + \
                N(" else ") + helper(y, bd_vars)

        if t.ty == Term.VAR:
            return V(t.name)

        elif t.ty == Term.CONST:
            if hasattr(t, "print_type") and t.print_type:
                return N("(" + t.name + "::" + str(t.T) + ")")
            else:
                return N(t.name)

        elif t.ty == Term.COMB:
            op_data = get_info_for_operator(t)
            # First, we take care of the case of operators
            if op_data and op_data.arity == OperatorData.BINARY and t.is_binop():
                arg1, arg2 = t.dest_binop()

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
                var_str = B(t.arg.var_name) + N("::") + \
                    N(str(t.arg.var_T)) if hasattr(t.arg, "print_type") else B(t.arg.var_name)
                body_repr = helper(t.arg.body, [t.arg.var_name] + bd_vars)

                return N(all_str) + var_str + N(". ") + body_repr

            elif logic.is_exists(t):
                exists_str = "?" if not settings.unicode() else "∃"
                var_str = B(t.arg.var_name) + N("::") + \
                    N(str(t.arg.var_T)) if hasattr(t.arg, "print_type") else B(t.arg.var_name)
                body_repr = helper(t.arg.body, [t.arg.var_name] + bd_vars)

                return N(exists_str) + var_str + N(". ") + body_repr

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

        elif t.ty == Term.ABS:
            lambda_str = "%" if not settings.unicode() else "λ"
            var_str = B(t.var_name) + N("::") + N(str(t.var_T)) if hasattr(t, "print_type") else B(t.var_name)
            body_repr = helper(t.body, [t.var_name] + bd_vars)
            return N(lambda_str) + var_str + N(". ") + body_repr

        elif t.ty == Term.BOUND:
            if t.n >= len(bd_vars):
                raise OpenTermException
            else:
                return B(bd_vars[t.n])
        else:
            raise TypeError()

    t = copy(t)  # make copy here, because infer_printed_type may change t.
    infertype.infer_printed_type(thy, t)
    return helper(t, [])

@settings.with_settings
def print_thm(th):
    """Print the given theorem with highlight."""
    turnstile = N("⊢") if settings.unicode() else N("|-")
    if th.assums:
        str_assums = commas_join(assum.print() for assum in th.assums)
        return str_assums + N(" ") + turnstile + N(" ") + th.concl.print()
    else:
        return turnstile + N(" ") + th.concl.print()

@settings.with_settings
def print_str_args(item):
    def str_val(val):
        if isinstance(val, dict):
            items = sorted(val.items(), key = lambda pair: pair[0])
            return N('{') + commas_join(N(key + ': ') + str_val(val) for key, val in items) + N('}')
        elif isinstance(val, Term):
            return val.print()
        else:
            return N(str(val))

    if isinstance(item.args, tuple):
        return commas_join(str_val(val) for val in item.args)
    elif item.args:
        return str_val(item.args)
    else:
        return [] if settings.highlight() else ""

@settings.with_settings
def export_proof_item(item):
    """Export the given proof item as a dictionary."""
    str_args = print_str_args(item)
    if not settings.highlight():
        str_th = str(item.th) if self.th else ""
    else:
        str_th = print_thm(item.th) if item.th else ""
    res = {'id': item.id, 'th': str_th, 'rule': item.rule, 'args': str_args, 'prevs': item.prevs}
    if settings.highlight():
        res['th_raw'] = print_thm(item.th, highlight=False) if item.th else ""
        res['args_raw'] = print_str_args(item, highlight=False)
    return res
