# Author: Bohua Zhan

from kernel import settings
from kernel.term import Term, OpenTermException
from logic.operator import OperatorData
from logic import logic

NORMAL, BOUND, VAR = range(3)

@settings.with_settings
def print_term(thy, t):
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

        def N(s):
            return [(s, NORMAL)] if settings.highlight() else s

        def B(s):
            return [(s, BOUND)] if settings.highlight() else s

        def V(s):
            return [(s, VAR)] if settings.highlight() else s

        if t.ty == Term.VAR:
            return V(t.name)

        elif t.ty == Term.CONST:
            op_data = get_info_for_operator(t)
            if op_data:
                if settings.unicode() and op_data.unicode_op:
                    return N(op_data.unicode_op)
                else:
                    return N(op_data.ascii_op)

            else:
                return N(t.name)

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
                var_str = B(t.arg.var_name) + N("::") + N(str(t.arg.T)) if settings.print_abs_type() else B(t.arg.var_name)
                body_repr = helper(t.arg.body, [t.arg.var_name] + bd_vars)

                return N(all_str) + var_str + N(". ") + body_repr

            elif logic.is_exists(t):
                exists_str = "?" if not settings.unicode() else "∃"
                var_str = B(t.arg.var_name) + N("::") + N(str(t.arg.T)) if settings.print_abs_type() else B(t.arg.var_name)
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
            var_str = B(t.var_name) + N("::") + N(str(t.T)) if settings.print_abs_type() else B(t.var_name)
            body_repr = helper(t.body, [t.var_name] + bd_vars)
            return N(lambda_str) + var_str + N(". ") + body_repr

        elif t.ty == Term.BOUND:
            if t.n >= len(bd_vars):
                raise OpenTermException
            else:
                return B(bd_vars[t.n])
        else:
            raise TypeError()

    return helper(t, [])
