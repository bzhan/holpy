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
            if high_light:
                result.append(res_tuple)
            return t.name

        elif t.ty == Term.CONST:
            op_data = get_info_for_operator(t)
            if op_data:
                if unicode and op_data.unicode_op:
                    if high_light:
                        res_tuple = (op_data.unicode_op, NORMAL)
                        result.append(res_tuple)
                    return op_data.unicode_op
                else:
                    if high_light:
                        res_tuple = (op_data.ascii_op, NORMAL)
                        result.append(res_tuple)
                    return op_data.ascii_op

            else:
                if high_light:
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
                str_arg1 = helper(arg1, bd_vars)
                if (op_data.assoc == LEFT and get_priority(arg1) < op_data.priority or
                    op_data.assoc == RIGHT and get_priority(arg1) <= op_data.priority):
                    str_arg1 = "(" + str_arg1 + ")"
                    if high_light:
                        res_tuple1 = ('(', NORMAL)
                        res_tuple2 = (')', NORMAL)
                        result.extend([res_tuple1, res_tuple2])

                # Obtain output for second argument, enclose in parenthesis
                # if necessary.
                str_arg2 = helper(arg2, bd_vars)
                if (op_data.assoc == LEFT and get_priority(arg2) <= op_data.priority or
                    op_data.assoc == RIGHT and get_priority(arg2) < op_data.priority):
                    str_arg2 = "(" + str_arg2 + ")"
                    if high_light:
                        res_tuple1 = ('(', NORMAL)
                        res_tuple2 = (')', NORMAL)
                        result.extend([res_tuple1, res_tuple2])

                if unicode and op_data.unicode_op:
                    str_op = op_data.unicode_op
                else:
                    str_op = op_data.ascii_op
                if high_light:
                    res_tuple1 = (str_op, NORMAL)
                    res_tuple2 = (' ', NORMAL)
                    result.extend([res_tuple1,res_tuple2])

                return str_arg1 + " " + str_op + " " + str_arg2

            # Unary case
            elif op_data and op_data.arity == OperatorData.UNARY:
                str_arg = helper(t.arg, bd_vars)
                if get_priority(t.arg) < op_data.priority:
                    str_arg = "(" + str_arg + ")"
                    if high_light:
                        res_tuple1 = ('(', NORMAL)
                        res_tuple2 = (')', NORMAL)
                        result.extend([res_tuple1,res_tuple2])

                if unicode and op_data.unicode_op:
                    str_op = op_data.unicode_op
                else:
                    str_op = op_data.ascii_op
                if high_light:
                    res_tuple = (str_op, NORMAL)
                    result.append(res_tuple)

                return str_op + str_arg

            # Next, the case of binders
            elif t.is_all():
                all_str = "!" if not unicode else "∀"
                var_str = t.arg.var_name + "::" + str(t.arg.T) if print_abs_type else t.arg.var_name
                body_repr = helper(t.arg.body, [t.arg.var_name] + bd_vars)
                if high_light:
                    res_tuple1 = (all_str, NORMAL)
                    res_tuple2 = ('::', NORMAL)
                    res_tuple3 = (t.arg.var_name, VAR)
                    res_tuple4 = ('. ', NORMAL)
                    res_tuple5 = (str(t.arg.T), NORMAL)
                    if print_abs_type:
                        result.extend([res_tuple1, res_tuple2, res_tuple3, res_tuple4, res_tuple5])
                    else:
                        result.extend([res_tuple1, res_tuple3, res_tuple4])
                return all_str + var_str + ". " + body_repr
            elif logic.is_exists(t):
                exists_str = "?" if not unicode else "∃"
                var_str = t.arg.var_name + "::" + str(t.arg.T) if print_abs_type else t.arg.var_name
                body_repr = helper(t.arg.body, [t.arg.var_name] + bd_vars)
                res_tuple1 = (exists_str, NORMAL)
                res_tuple2 = (t.arg.var_name, VAR)
                res_tuple3 = ('::', NORMAL)
                res_tuple4 = ('. ', NORMAL)
                res_tuple5 = (str(t.arg.T), NORMAL)
                if high_light:
                    if print_abs_type:
                        result.extend([res_tuple1, res_tuple2, res_tuple3, res_tuple4, res_tuple5])
                    else:
                        result.extend([res_tuple1, res_tuple2, res_tuple4])

                return exists_str + var_str + ". " + body_repr

            # Finally, usual function application
            else:
                str_fun = helper(t.fun, bd_vars)
                res_tuple1 = ('(', NORMAL)
                res_tuple2 = (')', NORMAL)
                res_tuple3 = (' ', NORMAL)
                if get_priority(t.fun) < 95:
                    str_fun = "(" + helper(t.fun, bd_vars) + ")"
                    if high_light:
                        result.extend([res_tuple1,res_tuple2])
                str_arg = helper(t.arg, bd_vars)
                if get_priority(t.arg) <= 95:
                    str_arg = "(" + helper(t.arg, bd_vars) + ")"
                    if high_light:
                        result.extend([res_tuple1, res_tuple2])
                result.extend([res_tuple3])
                return str_fun + " " + str_arg

        elif t.ty == Term.ABS:
            var_str = t.var_name + "::" + str(t.T) if print_abs_type else t.var_name
            body_repr = helper(t.body, [t.var_name] + bd_vars)
            lambda_str = "%" if not unicode else "λ"
            if high_light:
                res_tuple1 = (lambda_str, NORMAL)
                res_tuple2 = (t.var_name, BOUND)
                res_tuple3 = ('::', NORMAL)
                res_tuple4 = ('. ', NORMAL)
                res_tuple5 = (str(t.T), NORMAL)
                if print_abs_type:
                    result.extend([res_tuple1, res_tuple2, res_tuple3, res_tuple4,res_tuple5])
                else:
                    result.extend([res_tuple1, res_tuple2, res_tuple4])

            return lambda_str + var_str + ". " + body_repr

        elif t.ty == Term.BOUND:
            if t.n >= len(bd_vars):
                raise OpenTermException
            else:
                if high_light:
                    res_tuple = (bd_vars[t.n], VAR)
                    result.append(res_tuple)
                return bd_vars[t.n]
        else:
            raise TypeError()

    #result = list(set(result))
    return helper(t, []), list(set(result))
