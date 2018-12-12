# Author: Bohua Zhan

from kernel.term import Term,OpenTermException
from logic.operator import OperatorData
from logic import logic

NORMAL, BOUND, VAR = range(3)

def print_term(thy, t, *, print_abs_type=False, unicode=False, highlight=False):
    """More sophisticated printing function for terms. Handles printing
    of operators.
    
    Note we do not yet handle name collisions in lambda terms.

    """
    def get_info_for_operator(t):
        return thy.get_data("operator").get_info_for_fun(t.get_head())

    def get_priority(t):
        if t.ty == Term.COMB:
            op_data = get_info_for_operator(t)
            if op_data is not None:
                return op_data.priority
            elif t.is_all() or logic.is_exists(t):
                return 10
            else:
                return 95  # Function application
        elif t.ty == Term.ABS:
            return 10
        else:
            return 100  # Atom case

    def helper(t, bd_vars):
        LEFT, RIGHT = OperatorData.LEFT_ASSOC, OperatorData.RIGHT_ASSOC

        if t.ty == Term.VAR:
            if highlight:                
                return [(t.name, VAR)]
            else:
                return t.name

        elif t.ty == Term.CONST:
            op_data = get_info_for_operator(t)
            if op_data:
                if unicode and op_data.unicode_op:
                    if highlight:
                        return [(op_data.unicode_op, NORMAL)]
                    else:
                        return op_data.unicode_op
                else:
                    if highlight:
                        return [(op_data.ascii_op, NORMAL)]
                    else:
                        return op_data.ascii_op

            else:
                if highlight:
                    return [(t.name, NORMAL)]
                else:
                    return t.name

        elif t.ty == Term.COMB:
            op_data = get_info_for_operator(t)
            # First, we take care of the case of operators
            if op_data and op_data.arity == OperatorData.BINARY:
                # Partial application of operators, to implement later
                if not t.is_binop():
                    raise NotImplementedError()

                arg1, arg2 = t.dest_binop()

                # Obtain output for first argument, enclose in parenthesis
                # if necessary.
                if (op_data.assoc == LEFT and get_priority(arg1) < op_data.priority or
                    op_data.assoc == RIGHT and get_priority(arg1) <= op_data.priority):
                    if highlight:
                        str_arg1 = [("(", NORMAL)] + helper(arg1, bd_vars) + [(")", NORMAL)]
                    else:
                        str_arg1 = "(" + helper(arg1, bd_vars) + ")"
                else:
                    str_arg1 = helper(arg1, bd_vars)

                if unicode and op_data.unicode_op:
                    str_op = op_data.unicode_op
                else:
                    str_op = op_data.ascii_op
                if highlight:
                    str_op = [(str_op, NORMAL)]

                # Obtain output for second argument, enclose in parenthesis
                # if necessary.
                if (op_data.assoc == LEFT and get_priority(arg2) <= op_data.priority or
                    op_data.assoc == RIGHT and get_priority(arg2) < op_data.priority):
                    if highlight:
                        str_arg2 = [("(", NORMAL)] + helper(arg2, bd_vars) + [(")", NORMAL)]
                    else:
                        str_arg2 = "(" + helper(arg2, bd_vars) + ")"
                else:
                    str_arg2 = helper(arg2, bd_vars)

                if highlight:
                    return str_arg1 + [(" ", NORMAL)] + str_op + [(" ", NORMAL)] + str_arg2
                else:
                    return str_arg1 + " " + str_op + " " + str_arg2

            # Unary case
            elif op_data and op_data.arity == OperatorData.UNARY:
                if unicode and op_data.unicode_op:
                    str_op = op_data.unicode_op
                else:
                    str_op = op_data.ascii_op
                if highlight:
                    str_op = [(str_op, NORMAL)]

                if get_priority(t.arg) < op_data.priority:
                    if highlight:
                        str_arg = [("(", NORMAL)] + helper(t.arg, bd_vars) + [(")", NORMAL)]
                    else:
                        str_arg = "(" + helper(t.arg, bd_vars) + ")"
                else:
                    str_arg = helper(t.arg, bd_vars)

                return str_op + str_arg

            # Next, the case of binders
            elif t.is_all():
                all_str = "!" if not unicode else "∀"
                if highlight:
                    var_str = [(t.arg.var_name, VAR)] + [("::", NORMAL)] + [(str(t.arg.T), NORMAL)] if print_abs_type else [(t.arg.var_name, VAR)]
                else:
                    var_str = t.arg.var_name + "::" + str(t.arg.T) if print_abs_type else t.arg.var_name
                body_repr = helper(t.arg.body, [t.arg.var_name] + bd_vars)

                if highlight:
                    return [(all_str, NORMAL)] + var_str + [(". ", NORMAL)] + body_repr
                else:
                    return all_str + var_str + ". " + body_repr

            elif logic.is_exists(t):
                exists_str = "?" if not unicode else "∃"
                if highlight:
                    var_str = [(t.arg.var_name, VAR)] + [("::", NORMAL)] + [(str(t.arg.T), NORMAL)] if print_abs_type else [(t.arg.var_name, VAR)]
                else:
                    var_str = t.arg.var_name + "::" + str(t.arg.T) if print_abs_type else t.arg.var_name
                body_repr = helper(t.arg.body, [t.arg.var_name] + bd_vars)

                if highlight:
                    return [(exists_str, NORMAL)] + var_str + [(". ", NORMAL)] + body_repr
                else:
                    return exists_str + var_str + ". " + body_repr

            # Finally, usual function application
            else:
                if get_priority(t.fun) < 95:
                    if highlight:
                        str_fun = [("(", NORMAL)] + helper(t.fun, bd_vars) + [(")", NORMAL)]
                    else:
                        str_fun = "(" + helper(t.fun, bd_vars) + ")"
                else:
                    str_fun = helper(t.fun, bd_vars)
                if get_priority(t.arg) <= 95:
                    if highlight:
                        str_arg = [("(", NORMAL)] + helper(t.arg, bd_vars) + [(")", NORMAL)]
                    else:
                        str_arg = "(" + helper(t.arg, bd_vars) + ")"
                else:
                    str_arg = helper(t.arg, bd_vars)
                if highlight:
                    return str_fun + [(" ", NORMAL)] + str_arg
                else:
                    return str_fun + " " + str_arg

        elif t.ty == Term.ABS:
            lambda_str = "%" if not unicode else "λ"
            if highlight:
                var_str = [(t.var_name, BOUND)] + [("::", NORMAL)] + [(str(t.T), NORMAL)] if print_abs_type else [(t.var_name, BOUND)]
            else:
                var_str = t.var_name + "::" + str(t.T) if print_abs_type else t.var_name
            body_repr = helper(t.body, [t.var_name] + bd_vars)
            if highlight:
                return [(lambda_str, NORMAL)] + var_str + [(". ", NORMAL)] + body_repr
            else:
                return lambda_str + var_str + ". " + body_repr

        elif t.ty == Term.BOUND:
            if t.n >= len(bd_vars):
                raise OpenTermException
            else:
                if highlight:
                    return [(bd_vars[t.n], VAR)]
                else:
                    return bd_vars[t.n]
        else:
            raise TypeError()

    return helper(t, [])
