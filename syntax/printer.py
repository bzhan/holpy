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
        NORMAL,BOUND,VAR = range(3)

        if t.ty == Term.VAR:
            res_tuple = (t.name, VAR)
            result.append(res_tuple)
            return t.name

        elif t.ty == Term.CONST:
            op_data = get_info_for_operator(t)
            if op_data:
                if unicode and op_data.unicode_op:
                    res_tuple = (op_data.unicode_op, NORMAL)
                    result.append(res_tuple)
                    return op_data.unicode_op
                else:
                    res_tuple = (op_data.ascii_op, NORMAL)
                    result.append(res_tuple)
                    return op_data.ascii_op

            else:
                res_tuple = (t.name, NORMAL)
                result.append(res_tuple)
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
                    res_tuple1 = ('(', NORMAL)
                    res_tuple2 = (')', NORMAL)
                    result.append(res_tuple1)
                    str_arg1 = "(" + helper(arg1, bd_vars) + ")"
                    result.append(res_tuple2)
                else:
                    str_arg1 = helper(arg1, bd_vars)

                if unicode and op_data.unicode_op:
                    str_op = op_data.unicode_op
                else:
                    str_op = op_data.ascii_op
                res_tuple3 = (' ', NORMAL)
                res_tuple4 = (str_op, NORMAL)
                res_tuple5 = (' ', NORMAL)
                result.extend([res_tuple3, res_tuple4, res_tuple5])

                # Obtain output for second argument, enclose in parenthesis
                # if necessary.
                if (op_data.assoc == LEFT and get_priority(arg2) <= op_data.priority or
                    op_data.assoc == RIGHT and get_priority(arg2) < op_data.priority):
                    res_tuple1 = ('(', NORMAL)
                    res_tuple2 = (')', NORMAL)
                    result.append(res_tuple1)
                    str_arg2 = "(" + helper(arg2, bd_vars) + ")"
                    result.append(res_tuple2)
                else:
                    str_arg2 = helper(arg2, bd_vars)

                return str_arg1 + " " + str_op + " " + str_arg2

            # Unary case
            elif op_data and op_data.arity == OperatorData.UNARY:
                if unicode and op_data.unicode_op:
                    str_op = op_data.unicode_op
                else:
                    str_op = op_data.ascii_op
                if high_light:
                    res_tuple = (str_op, NORMAL)
                    result.append(res_tuple)

                if get_priority(t.arg) < op_data.priority:
                    res_tuple1 = ('(', NORMAL)
                    res_tuple2 = (')', NORMAL)
                    result.append(res_tuple1)
                    str_arg = "(" + helper(t.arg, bd_vars) + ")"
                    result.append(res_tuple2)
                else:
                    str_arg = helper(t.arg, bd_vars)

                return str_op + str_arg

            # Next, the case of binders
            elif t.is_all():
                all_str = "!" if not unicode else "∀"
                var_str = t.arg.var_name + "::" + str(t.arg.T) if print_abs_type else t.arg.var_name
                res_tuple1 = (all_str, NORMAL)
                res_tuple2 = ('::', NORMAL)
                res_tuple3 = (t.arg.var_name, VAR)
                res_tuple4 = ('. ', NORMAL)
                res_tuple5 = (str(t.arg.T), NORMAL)
                if print_abs_type:
                    result.extend([res_tuple1, res_tuple3, res_tuple2, res_tuple5, res_tuple4])
                else:
                    result.extend([res_tuple1, res_tuple3, res_tuple4])
                body_repr = helper(t.arg.body, [t.arg.var_name] + bd_vars)

                return all_str + var_str + ". " + body_repr

            elif logic.is_exists(t):
                exists_str = "?" if not unicode else "∃"
                var_str = t.arg.var_name + "::" + str(t.arg.T) if print_abs_type else t.arg.var_name
                res_tuple1 = (exists_str, NORMAL)
                res_tuple2 = (t.arg.var_name, VAR)
                res_tuple3 = ('::', NORMAL)
                res_tuple4 = ('. ', NORMAL)
                res_tuple5 = (str(t.arg.T), NORMAL)
                if print_abs_type:
                    result.extend([res_tuple1,res_tuple2, res_tuple3, res_tuple5, res_tuple4])
                else:
                    result.extend([res_tuple1, res_tuple2, res_tuple4])
                body_repr = helper(t.arg.body, [t.arg.var_name] + bd_vars)

                return exists_str + var_str + ". " + body_repr

            # Finally, usual function application
            else:
                res_tuple1 = ('(', NORMAL)
                res_tuple2 = (')', NORMAL)
                res_tuple3 = (' ', NORMAL)
                if get_priority(t.fun) < 95:
                    result.append(res_tuple1)
                    str_fun = "(" + helper(t.fun, bd_vars) + ")"
                    result.append(res_tuple2)
                else:
                    str_fun = helper(t.fun, bd_vars)
                result.extend([res_tuple3])
                if get_priority(t.arg) <= 95:
                    result.append(res_tuple1)
                    str_arg = "(" + helper(t.arg, bd_vars) + ")"
                    result.append(res_tuple2)
                else:
                    str_arg = helper(t.arg, bd_vars)
                return str_fun + " " + str_arg

        elif t.ty == Term.ABS:
            var_str = t.var_name + "::" + str(t.T) if print_abs_type else t.var_name
            lambda_str = "%" if not unicode else "λ"
            res_tuple1 = (lambda_str, NORMAL)
            res_tuple2 = (t.var_name, BOUND)
            res_tuple3 = ('::', NORMAL)
            res_tuple4 = ('. ', NORMAL)
            res_tuple5 = (str(t.T), NORMAL)
            if print_abs_type:
                result.extend([res_tuple1, res_tuple2, res_tuple3, res_tuple5, res_tuple4])
            else:
                result.extend([res_tuple1, res_tuple2, res_tuple4])
            body_repr = helper(t.body, [t.var_name] + bd_vars)
            return lambda_str + var_str + ". " + body_repr

        elif t.ty == Term.BOUND:
            if t.n >= len(bd_vars):
                raise OpenTermException
            else:
                res_tuple = (bd_vars[t.n], VAR)
                result.append(res_tuple)
                return bd_vars[t.n]
        else:
            raise TypeError()

    if high_light:
        return helper(t, []), result

    else:
        return helper(t,[])
