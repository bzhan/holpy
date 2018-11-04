# Author: Bohua Zhan

from kernel.term import Term
from logic.basic import OperatorData

def print_term(thy, t, *, print_abs_type = False, unicode = False):
    """More sophisticated printing function for terms. Handles printing
    of operators.
    
    Note we do not yet handle name collisions in lambda terms.

    """
    def get_info_for_binop(t):
        return thy.get_data("operator").get_info_for_fun(t.get_head())

    def get_priority(t):
        if t.ty == Term.COMB:
            if t.is_binop() and get_info_for_binop(t) is not None:
                op_data = get_info_for_binop(t)
                return op_data.priority
            elif t.is_all():
                return 10
            else:
                return 95  # Function application
        elif t.ty == Term.ABS:
            return 10
        else:
            return 100  # Atom case

    def helper(t, bd_vars):
        if t.ty == Term.VAR or t.ty == Term.CONST:
            return t.name

        elif t.ty == Term.COMB:
            # First, we take care of the case of operators
            if t.is_binop() and get_info_for_binop(t) is not None:
                # Obtain the priority and the string of the operator
                op_data = get_info_for_binop(t)
                arg1, arg2 = t.dest_binop()

                # Obtain output for first argument, enclose in parenthesis
                # if necessary.
                str_arg1 = helper(arg1, bd_vars)
                if (op_data.assoc == OperatorData.LEFT_ASSOC and get_priority(arg1) < op_data.priority or
                    op_data.assoc == OperatorData.RIGHT_ASSOC and get_priority(arg1) <= op_data.priority):
                    str_arg1 = "(" + str_arg1 + ")"

                # Obtain output for second argument, enclose in parenthesis
                # if necessary.
                str_arg2 = helper(arg2, bd_vars)
                if (op_data.assoc == OperatorData.LEFT_ASSOC and get_priority(arg2) <= op_data.priority or
                    op_data.assoc == OperatorData.RIGHT_ASSOC and get_priority(arg2) < op_data.priority):
                    str_arg2 = "(" + str_arg2 + ")"

                if unicode and op_data.unicode_op is not None:
                    str_op = op_data.unicode_op
                else:
                    str_op = op_data.ascii_op

                return str_arg1 + " " + str_op + " " + str_arg2

            elif t.is_all():
                all_str = "!" if not unicode else "∀"
                var_str = t.arg.var_name + "::" + repr(t.arg.T) if print_abs_type else t.arg.var_name
                body_repr = helper(t.arg.body, [t.arg.var_name] + bd_vars)
                return all_str + var_str + ". " + body_repr

            # a b c associates to the left. So parenthesis is needed to express
            # a (b c). Parenthesis is also needed for lambda terms.
            elif t.fun.ty == Term.ABS:
                str_fun = "(" + helper(t.fun, bd_vars) + ")"
            else:
                str_fun = helper(t.fun, bd_vars)
            if t.arg.ty == Term.COMB or t.arg.ty == Term.ABS:
                str_arg = "(" + helper(t.arg, bd_vars) + ")"
            else:
                str_arg = helper(t.arg, bd_vars)
            return str_fun + " " + str_arg
        elif t.ty == Term.ABS:
            var_str = t.var_name + "::" + repr(t.T) if print_abs_type else t.var_name
            body_repr = helper(t.body, [t.var_name] + bd_vars)
            lambda_str = "%" if not unicode else "λ"
            return lambda_str + var_str + ". " + body_repr
        elif t.ty == Term.BOUND:
            if t.n >= len(bd_vars):
                raise OpenTermException
            else:
                return bd_vars[t.n]
        else:
            raise TypeError()

    return helper(t, [])
