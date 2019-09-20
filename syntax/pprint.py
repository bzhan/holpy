"""Pretty-print functions."""

from copy import copy

from kernel.type import HOLType
from kernel import term
from syntax import settings
from syntax import infertype
from syntax import operator
from util import name


class AST:
    pass

class Bracket(AST):
    def __init__(self, body):
        self.ty = "bracket"
        self.body = body
    
    def __repr__(self):
        return "Bracket(%s)" % repr(self.body)

class ShowType(AST):
    def __init__(self, body):
        self.ty = "show_type"
        self.body = body

    def __repr__(self):
        return "ShowType(%s)" % repr(self.body)

class VarName(AST):
    def __init__(self, name, T):
        self.ty = "var_name"
        self.name = name
        self.T = T

    def __repr__(self):
        return "VarName(%s,%s)" % (self.name, self.T)

class ConstName(AST):
    def __init__(self, name, T):
        self.ty = "const_name"
        self.name = name
        self.T = T

    def __repr__(self):
        return "ConstName(%s,%s)" % (self.name, self.T)

class Number(AST):
    def __init__(self, n, T):
        self.ty = "number"
        self.n = n
        self.T = T

    def __repr__(self):
        return "Number(%s,%s)" % (self.n, self.T)

class List(AST):
    def __init__(self, entries, T):
        self.ty = "list"
        self.entries = tuple(entries)
        self.T = T

    def __repr__(self):
        return "List(%s,%s)" % (','.join(str(e) for e in self.entries), self.T)

class Set(AST):
    def __init__(self, entries, T):
        self.ty = "set"
        self.entries = tuple(entries)
        self.T = T

    def __repr__(self):
        return "Set(%s,%s)" % (','.join(str(e) for e in self.entries), self.T)

class Operator(AST):
    def __init__(self, symbol, T):
        self.ty = "operator"
        self.symbol = symbol
        self.T = T

    def __repr__(self):
        return "Operator(%s,%s)" % (self.symbol, self.T)

class BinaryOp(AST):
    def __init__(self, arg1, op, arg2, T):
        self.ty = "binary_op"
        self.arg1 = arg1
        self.op = op
        self.arg2 = arg2
        self.T = T

    def __repr__(self):
        return "BinaryOp(%s,%s,%s,%s)" % (self.arg1, self.op, self.arg2, self.T)

class UnaryOp(AST):
    def __init__(self, op, arg, T):
        self.ty = "unary_op"
        self.op = op
        self.arg = arg
        self.T = T

    def __repr__(self):
        return "UnaryOp(%s,%s,%s)" % (self.op, self.arg, self.T)

class Binder(AST):
    def __init__(self, symbol):
        self.ty = "binder"
        self.symbol = symbol

    def __repr__(self):
        return "Binder(%s)" % self.symbol

class BinderAppl(AST):
    def __init__(self, op, bind_var, body, T):
        self.ty = "binder_appl"
        self.op = op
        self.bind_var = bind_var
        self.body = body
        self.T = T

    def __repr__(self):
        return "Binder(%s,%s,%s,%s)" % (self.op, self.bind_var, self.body, self.T)

class Bound(AST):
    def __init__(self, name, T):
        self.ty = "bound"
        self.name = name
        self.T = T

    def __repr__(self):
        return "Bound(%s,%s)" % (self.name, self.T)

class FunAppl(AST):
    def __init__(self, fun, arg, T):
        self.ty = "fun_appl"
        self.fun = fun
        self.arg = arg
        self.T = T

    def __repr__(self):
        return "FunAppl(%s,%s,%s)" % (self.fun, self.arg, self.T)

class ITE(AST):
    def __init__(self, cond, a1, a2, T):
        self.ty = "ite"
        self.cond = cond
        self.a1 = a1
        self.a2 = a2
        self.T = T

class Interval(AST):
    def __init__(self, left, right, T):
        self.ty = "interval"
        self.left = left
        self.right = right
        self.T = T

class FunUpd(AST):
    def __init__(self, f, upds, T):
        self.ty = "fun_upd"
        self.f = f
        self.upds = upds
        self.T = T

class Collect(AST):
    def __init__(self, bind_var, body, T):
        self.ty = "collect"
        self.bind_var = bind_var
        self.body = body
        self.T = T


@settings.with_settings
def get_ast(thy, t):
    """Print term possibly in multiple lines."""
    assert isinstance(t, term.Term), "pprint_term: input is not a term."

    # Import modules for custom parsed data
    from logic import logic
    from data import nat
    from data import list
    from data import set
    from data import function
    from data import interval

    def get_priority(t):
        if nat.is_binary(t) or list.is_literal_list(t):
            return 100  # Nat atom case
        elif t.is_comb():
            op_data = operator.get_info_for_fun(thy, t.head)
            binder_data = operator.get_binder_info_for_fun(thy, t.head)

            if op_data is not None:
                return op_data.priority
            elif binder_data is not None or logic.is_if(t):
                return 10
            else:
                return 95  # Function application
        elif t.is_abs():
            return 10
        else:
            return 100  # Atom case

    def helper(t, bd_vars):
        # Some special cases:
        # Natural numbers:
        if t.is_const_name("zero") or t.is_const_name("one") or \
           (t.is_comb() and t.fun.is_const_name("of_nat") and nat.is_binary(t.arg)):
            # First find the number
            if t.is_const_name("zero"):
                n = 0
            elif t.is_const_name("one"):
                n = 1
            else:
                n = nat.from_binary(t.arg)
            res = Number(n, t.get_type())
            if (t.is_const() and hasattr(t, "print_type")) or \
               (t.is_comb() and hasattr(t.fun, "print_type")):
                res = Bracket(ShowType(res))
            return res

        elif list.is_literal_list(t):
            items = list.dest_literal_list(t)
            res = List([helper(item, bd_vars) for item in items], t.get_type())
            if hasattr(t, "print_type"):
                res = Bracket(ShowType(res))
            return res

        elif set.is_literal_set(t):
            items = set.dest_literal_set(t)
            if set.is_empty_set(t):
                res = Operator("∅", t.T) if settings.unicode() else Operator("{}", t.T)
                if hasattr(t, "print_type"):
                    res = Bracket(ShowType(res))
                return res
            else:
                return Set([helper(item, bd_vars) for item in items], t.get_type())

        elif interval.is_interval(t):
            return Interval(helper(t.arg1, bd_vars), helper(t.arg, bd_vars), t.get_type())

        elif t.is_comb() and t.fun.is_const_name('collect') and t.arg.is_abs():
            var_names = [v.name for v in term.get_vars(t.arg.body)]
            nm = name.get_variant_name(t.arg.var_name, var_names)

            bind_var = Bound(nm, t.arg.var_T)
            body_ast = helper(t.arg.body, [bind_var] + bd_vars)

            return Collect(bind_var, body_ast, t.get_type())

        elif logic.is_if(t):
            P, x, y = t.args
            return ITE(helper(P, bd_vars), helper(x, bd_vars), helper(y, bd_vars), t.get_type())

        elif t.is_var():
            return VarName(t.name, t.T)

        elif t.is_const():
            res = ConstName(t.name, t.T)
            if hasattr(t, "print_type"):
                res = Bracket(ShowType(res))
            return res

        elif t.is_comb():
            op_data = operator.get_info_for_fun(thy, t.head)
            binder_data = operator.get_binder_info_for_fun(thy, t.head)

            # First, we take care of the case of operators
            if op_data and op_data.arity == operator.BINARY and t.is_binop():
                arg1, arg2 = t.args

                # Obtain output for first argument, enclose in parenthesis
                # if necessary.
                arg1_ast = helper(arg1, bd_vars)
                if (op_data.assoc == operator.LEFT and get_priority(arg1) < op_data.priority or
                    op_data.assoc == operator.RIGHT and get_priority(arg1) <= op_data.priority):
                    arg1_ast = Bracket(arg1_ast)

                op_str = op_data.unicode_op if settings.unicode() else op_data.ascii_op
                op_ast = Operator(op_str, t.head.get_type())

                # Obtain output for second argument, enclose in parenthesis
                # if necessary.
                arg2_ast = helper(arg2, bd_vars)
                if (op_data.assoc == operator.LEFT and get_priority(arg2) <= op_data.priority or
                    op_data.assoc == operator.RIGHT and get_priority(arg2) < op_data.priority):
                    arg2_ast = Bracket(arg2_ast)

                return BinaryOp(arg1_ast, op_ast, arg2_ast, t.get_type())

            # Unary case
            elif op_data and op_data.arity == operator.UNARY:
                op_str = op_data.unicode_op if settings.unicode() else op_data.ascii_op
                op_ast = Operator(op_str, t.head.get_type())

                arg_ast = helper(t.arg, bd_vars)
                if get_priority(t.arg) < op_data.priority:
                    arg_ast = Bracket(arg_ast)

                return UnaryOp(op_ast, arg_ast, t.get_type())

            # Next, the case of binders
            elif binder_data and t.arg.is_abs():
                binder_str = binder_data.unicode_op if settings.unicode() else binder_data.ascii_op
                op_ast = Binder(binder_str)

                var_names = [v.name for v in term.get_vars(t.arg.body)]
                nm = name.get_variant_name(t.arg.var_name, var_names)

                bind_var = Bound(nm, t.arg.var_T)
                body_ast = helper(t.arg.body, [bind_var] + bd_vars)
                if hasattr(t.arg, "print_type"):
                    bind_var = ShowType(bind_var)

                return BinderAppl(op_ast, bind_var, body_ast, t.get_type())

            # Function update
            elif function.is_fun_upd(t):
                f, upds = function.strip_fun_upd(t)
                f_ast = helper(f, bd_vars)
                upds_ast = [(helper(a, bd_vars), helper(b, bd_vars)) for a, b in upds]
                return FunUpd(f_ast, upds_ast, t.get_type())

            # Finally, usual function application
            else:
                fun_ast = helper(t.fun, bd_vars)
                if get_priority(t.fun) < 95:
                    fun_ast = Bracket(fun_ast)

                arg_ast = helper(t.arg, bd_vars)
                if get_priority(t.arg) <= 95:
                    arg_ast = Bracket(arg_ast)

                return FunAppl(fun_ast, arg_ast, t.get_type())

        elif t.is_abs():
            op_ast = Binder("λ") if settings.unicode() else Binder("%")

            var_names = [v.name for v in term.get_vars(t.body)]
            nm = name.get_variant_name(t.var_name, var_names)

            bind_var = Bound(nm, t.var_T)
            body_ast = helper(t.body, [bind_var] + bd_vars)
            if hasattr(t, "print_type"):
                bind_var = ShowType(bind_var)

            return BinderAppl(op_ast, bind_var, body_ast, t.get_type())

        elif t.is_bound():
            if t.n >= len(bd_vars):
                raise OpenTermException
            else:
                return bd_vars[t.n]
        else:
            raise TypeError()

    t = copy(t)  # make copy here, because infer_printed_type may change t.
    infertype.get_overload(thy, t)
    infertype.infer_printed_type(thy, t)

    return helper(t, [])

@settings.with_settings
def print_ast(ast):
    if ast.ty == "bracket":
        return "(" + print_ast(ast.body) + ")"
    elif ast.ty == "show_type":
        return print_ast(ast.body) + "::" + str(ast.body.T)
    elif ast.ty == "var_name":
        return ast.name
    elif ast.ty == "const_name":
        return ast.name
    elif ast.ty == "number":
        return str(ast.n)
    elif ast.ty == "list":
        return "[" + ", ".join(print_ast(e) for e in ast.entries) + "]"
    elif ast.ty == "set":
        return "{" + ", ".join(print_ast(e) for e in ast.entries) + "}"
    elif ast.ty == "operator":
        return ast.symbol
    elif ast.ty == "binary_op":
        return "%s %s %s" % (print_ast(ast.arg1), print_ast(ast.op), print_ast(ast.arg2))
    elif ast.ty == "unary_op":
        return "%s%s" % (print_ast(ast.op), print_ast(ast.arg))
    elif ast.ty == "binder":
        return ast.symbol
    elif ast.ty == "binder_appl":
        return "%s%s. %s" % (print_ast(ast.op), print_ast(ast.bind_var), print_ast(ast.body))
    elif ast.ty == "bound":
        return ast.name
    elif ast.ty == "fun_appl":
        return "%s %s" % (print_ast(ast.fun), print_ast(ast.arg))
    elif ast.ty == "ite":
        return "if %s then %s else %s" % (print_ast(ast.cond), print_ast(ast.a1), print_ast(ast.a2))
    elif ast.ty == "interval":
        return "{%s..%s}" % (print_ast(ast.left), print_ast(ast.right))
    elif ast.ty == "fun_upd":
        upd_strs = ["%s := %s" % (print_ast(a), print_ast(b)) for a, b in ast.upds]
        return "(%s)(%s)" % (print_ast(ast.f), ', '.join(upd_strs))
    elif ast.ty == "collect":
        return "{%s. %s}" % (print_ast(ast.bind_var), print_ast(ast.body))
    else:
        raise TypeError
