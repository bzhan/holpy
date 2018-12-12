# Author: Bohua Zhan

from kernel.term import Term,OpenTermException
from logic.operator import OperatorData
from logic import logic

def print_term(thy, t, *, print_abs_type = False, unicode = False, high_light=False):
    """More sophisticated printing function for terms. Handles printing
    of operators.
    
    Note we do not yet handle name collisions in lambda terms.

    """
    result = []
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
        NORMAL, BOUND, VAR = range(3)

        if t.ty == Term.VAR:
            result.append((t.name, VAR))
            return t.name

        elif t.ty == Term.CONST:
            op_data = get_info_for_operator(t)
            if op_data:
                if unicode and op_data.unicode_op:
                    result.append((op_data.unicode_op, NORMAL))
                    return op_data.unicode_op
                else:
                    result.append((op_data.ascii_op, NORMAL))
                    return op_data.ascii_op

            else:
                result.append((t.name, NORMAL))
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
                    result.append(('(', NORMAL))
                    str_arg1 = "(" + helper(arg1, bd_vars) + ")"
                    result.append((')', NORMAL))
                else:
                    str_arg1 = helper(arg1, bd_vars)

                if unicode and op_data.unicode_op:
                    str_op = op_data.unicode_op
                else:
                    str_op = op_data.ascii_op
                result.extend([(' ', NORMAL), (str_op, NORMAL), (' ', NORMAL)])

                # Obtain output for second argument, enclose in parenthesis
                # if necessary.
                if (op_data.assoc == LEFT and get_priority(arg2) <= op_data.priority or
                    op_data.assoc == RIGHT and get_priority(arg2) < op_data.priority):
                    result.append(('(', NORMAL))
                    str_arg2 = "(" + helper(arg2, bd_vars) + ")"
                    result.append((')', NORMAL))
                else:
                    str_arg2 = helper(arg2, bd_vars)

                return str_arg1 + " " + str_op + " " + str_arg2

            # Unary case
            elif op_data and op_data.arity == OperatorData.UNARY:
                if unicode and op_data.unicode_op:
                    str_op = op_data.unicode_op
                else:
                    str_op = op_data.ascii_op

                result.append((str_op, NORMAL))

                if get_priority(t.arg) < op_data.priority:
                    result.append(('(', NORMAL))
                    str_arg = "(" + helper(t.arg, bd_vars) + ")"
                    result.append((')', NORMAL))
                else:
                    str_arg = helper(t.arg, bd_vars)

                return str_op + str_arg

            # Next, the case of binders
            elif t.is_all():
                all_str = "!" if not unicode else "∀"
                var_str = t.arg.var_name + "::" + str(t.arg.T) if print_abs_type else t.arg.var_name
                if print_abs_type:
                    result.extend([(all_str, NORMAL), (t.arg.var_name, VAR), ('::', NORMAL), (str(t.arg.T), NORMAL), ('. ', NORMAL)])
                else:
                    result.extend([(all_str, NORMAL), (t.arg.var_name, VAR), ('. ', NORMAL)])
                body_repr = helper(t.arg.body, [t.arg.var_name] + bd_vars)

                return all_str + var_str + ". " + body_repr

            elif logic.is_exists(t):
                exists_str = "?" if not unicode else "∃"
                var_str = t.arg.var_name + "::" + str(t.arg.T) if print_abs_type else t.arg.var_name
                if print_abs_type:
                    result.extend([(exists_str, NORMAL),(t.arg.var_name, VAR), ('::', NORMAL), (str(t.arg.T), NORMAL), ('. ', NORMAL)])
                else:
                    result.extend([(exists_str, NORMAL), (t.arg.var_name, VAR), ('. ', NORMAL)])
                body_repr = helper(t.arg.body, [t.arg.var_name] + bd_vars)

                return exists_str + var_str + ". " + body_repr

            # Finally, usual function application
            else:
                if get_priority(t.fun) < 95:
                    result.append(('(', NORMAL))
                    str_fun = "(" + helper(t.fun, bd_vars) + ")"
                    result.append((')', NORMAL))
                else:
                    str_fun = helper(t.fun, bd_vars)
                result.append((' ', NORMAL))
                if get_priority(t.arg) <= 95:
                    result.append(('(', NORMAL))
                    str_arg = "(" + helper(t.arg, bd_vars) + ")"
                    result.append((')', NORMAL))
                else:
                    str_arg = helper(t.arg, bd_vars)
                return str_fun + " " + str_arg

        elif t.ty == Term.ABS:
            var_str = t.var_name + "::" + str(t.T) if print_abs_type else t.var_name
            lambda_str = "%" if not unicode else "λ"
            if print_abs_type:
                result.extend([(lambda_str, NORMAL), (t.var_name, BOUND), ('::', NORMAL), (str(t.T), NORMAL), ('. ', NORMAL)])
            else:
                result.extend([(lambda_str, NORMAL), (t.var_name, BOUND), ('. ', NORMAL)])
            body_repr = helper(t.body, [t.var_name] + bd_vars)
            return lambda_str + var_str + ". " + body_repr

        elif t.ty == Term.BOUND:
            if t.n >= len(bd_vars):
                raise OpenTermException
            else:
                result.append((bd_vars[t.n], VAR))
                return bd_vars[t.n]
        else:
            raise TypeError()

    if high_light:
        return helper(t, []), result

    else:
        return helper(t,[])
