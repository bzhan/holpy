"""Pretty-print functions."""

from copy import copy

from kernel import type as hol_type
from kernel.type import HOLType
from kernel import term
from kernel import extension
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
    def __init__(self, body, ast_T):
        self.ty = "show_type"
        self.body = body
        self.ast_T = ast_T

    def __repr__(self):
        return "ShowType(%s,%s)" % (repr(self.body), repr(self.ast_T))

class SVarName(AST):
    def __init__(self, name, T):
        self.ty = "svar_name"
        self.name = name
        self.T = T

    def __repr__(self):
        return "SVarName(%s,%s)" % (self.name, self.T)

class VarName(AST):
    def __init__(self, name, T):
        self.ty = "var_name"
        self.name = name
        self.T = T

    def __repr__(self):
        return "VarName(%s,%s)" % (self.name, self.T)

class ConstName(AST):
    def __init__(self, name, T, link_name):
        self.ty = "const_name"
        self.name = name
        self.T = T
        self.link_name = link_name

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
    def __init__(self, symbol, T, link_name):
        self.ty = "operator"
        self.symbol = symbol
        self.T = T
        self.link_name = link_name

    def __repr__(self):
        return "Operator(%s,%s,%s)" % (self.symbol, self.T, self.link_name)

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
    def __init__(self, op, bind_var, body):
        self.ty = "binder_appl"
        self.op = op
        self.bind_var = bind_var
        self.body = body

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
    def __init__(self, fun, arg):
        self.ty = "fun_appl"
        self.fun = fun
        self.arg = arg

    def __repr__(self):
        return "FunAppl(%s,%s)" % (self.fun, self.arg)

class ITE(AST):
    def __init__(self, cond, a1, a2, T):
        self.ty = "ite"
        self.cond = cond
        self.a1 = a1
        self.a2 = a2
        self.T = T

class Char(AST):
    def __init__(self, c):
        self.ty = "char"
        self.c = c

class String(AST):
    def __init__(self, s):
        self.ty = "string"
        self.s = s

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

class STVarName(AST):
    def __init__(self, name):
        self.ty = 'stvar_name'
        self.name = name

class TVarName(AST):
    def __init__(self, name):
        self.ty = 'tvar_name'
        self.name = name

class TypeConstr(AST):
    def __init__(self, name, args):
        self.ty = 'type_constr'
        self.name = name
        self.args = args

class FunType(AST):
    def __init__(self, arg1, fun_op, arg2):
        self.ty = 'fun_type'
        self.arg1 = arg1
        self.fun_op = fun_op
        self.arg2 = arg2


@settings.with_settings
def get_ast_type(thy, T):
    """Obtain the abstract syntax tree for a type."""
    assert isinstance(T, HOLType), "get_ast_type: input is not a type."

    def helper(T):
        if T.ty == hol_type.STVAR:
            return STVarName(T.name)
        elif T.ty == hol_type.TVAR:
            return TVarName(T.name)
        elif T.ty == hol_type.TYPE:
            if len(T.args) == 0:
                return TypeConstr(T.name, [])
            elif len(T.args) == 1:
                arg_ast = helper(T.args[0])
                # Insert parenthesis if the single argument is a function.
                if HOLType.is_fun(T.args[0]):
                    arg_ast = Bracket(arg_ast)
                return TypeConstr(T.name, [arg_ast])
            elif HOLType.is_fun(T):
                # 'a => 'b => 'c associates to the right. So parenthesis is
                # needed to express ('a => 'b) => 'c.
                fun_op = " ⇒ " if settings.unicode() else " => "
                arg1_ast = helper(T.args[0])
                if HOLType.is_fun(T.args[0]):
                    arg1_ast = Bracket(arg1_ast)
                arg2_ast = helper(T.args[1])
                return FunType(arg1_ast, fun_op, arg2_ast)
            else:
                return TypeConstr(T.name, [helper(arg) for arg in T.args])
        else:
            raise TypeError

    return helper(T)

# Hash table for ASTs.
term_ast = dict()

@settings.with_settings
def get_ast_term(thy, t):
    """Obtain the abstract syntax tree for a term."""
    if (thy, t, settings.unicode()) in term_ast:
        return term_ast[(thy, t, settings.unicode())]

    assert isinstance(t, term.Term), "get_ast_term: input is not a term."

    # Import modules for custom parsed data
    from logic import logic
    from data import nat
    from data import list
    from data import set
    from data import function
    from data import interval
    from data import string

    def get_priority(t):
        """Obtain the binding priority of the top-most operation of t."""
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
            return 200  # Atom case

    def helper(t, bd_vars):
        """Main recursive function. Here bd_vars is the list of bound
        variables (represented by a list of AST Bound objects).
        
        """
        # Some special cases:
        # Natural numbers:
        if t.is_const_name("zero") or t.is_const_name("one") or \
           (t.is_comb() and t.fun.is_const_name("of_nat") and
            nat.is_binary(t.arg) and nat.from_binary(t.arg) >= 2):
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
                res = Bracket(ShowType(res, get_ast_type(thy, res.T)))
            return res

        # Lists
        elif list.is_literal_list(t):
            items = list.dest_literal_list(t)
            res = List([helper(item, bd_vars) for item in items], t.get_type())
            if hasattr(t, "print_type"):
                res = Bracket(ShowType(res, get_ast_type(thy, res.T)))
            return res

        # Sets
        elif set.is_literal_set(t):
            items = set.dest_literal_set(t)
            if set.is_empty_set(t):
                res = Operator("∅", t.T, "empty_set") if settings.unicode() else Operator("{}", t.T, "empty_set")
                if hasattr(t, "print_type"):
                    res = Bracket(ShowType(res, get_ast_type(thy, res.T)))
                return res
            else:
                return Set([helper(item, bd_vars) for item in items], t.get_type())

        # Chars and Strings
        elif string.is_char(t):
            return Char(string.dest_char(t))
        elif string.is_string(t):
            return String(string.dest_string(t))

        # Intervals
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

        elif t.is_svar():
            return SVarName(t.name, t.T)

        elif t.is_var():
            return VarName(t.name, t.T)

        elif t.is_const():
            link_name = thy.get_overload_const_name(t.name, t.T)
            res = ConstName(t.name, t.T, link_name=link_name)
            if hasattr(t, "print_type"):
                res = Bracket(ShowType(res, get_ast_type(thy, res.T)))
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
                op_name = thy.get_overload_const_name(op_data.fun_name, t.head.get_type())
                op_ast = Operator(op_str, t.head.get_type(), op_name)

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
                op_name = thy.get_overload_const_name(op_data.fun_name, t.head.get_type())
                op_ast = Operator(op_str, t.head.get_type(), op_name)

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
                    bind_var = ShowType(bind_var, get_ast_type(thy, bind_var.T))

                return BinderAppl(op_ast, bind_var, body_ast)

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

                return FunAppl(fun_ast, arg_ast)

        elif t.is_abs():
            op_ast = Binder("λ") if settings.unicode() else Binder("%")

            var_names = [v.name for v in term.get_vars(t.body)]
            nm = name.get_variant_name(t.var_name, var_names)

            bind_var = Bound(nm, t.var_T)
            body_ast = helper(t.body, [bind_var] + bd_vars)
            if hasattr(t, "print_type"):
                bind_var = ShowType(bind_var, get_ast_type(thy, bind_var.T))

            return BinderAppl(op_ast, bind_var, body_ast)

        elif t.is_bound():
            if t.n >= len(bd_vars):
                raise OpenTermException
            else:
                return bd_vars[t.n]
        else:
            raise TypeError

    copy_t = copy(t)  # make copy here, because infer_printed_type may change t.
    infertype.infer_printed_type(thy, copy_t)

    ast = helper(copy_t, [])
    term_ast[(thy, t, settings.unicode())] = ast
    return ast

def print_length(res):
    if settings.highlight():
        return sum(len(node['text']) for node in res)
    else:
        return len(res)

# 0, 1, 2, 3 = NORMAL, BOUND, VAR, TVAR
@settings.with_settings
def N(s, *, link=None):
    if settings.highlight():
        res = {'text': s, 'color': 0}
        if link:
            if link['name'] == s:
                res['link_name'] = ''
            else:
                res['link_name'] = link['name']
            res['link_ty'] = link['ty']
        return [res]
    else:
        return s

@settings.with_settings
def B(s):
    """Bound variable"""
    if settings.highlight():
        return [{'text': s, 'color': 1}]
    else:
        return s

@settings.with_settings
def V(s):
    """Free variable"""
    if settings.highlight():
        return [{'text': s, 'color': 2}]
    else:
        return s

@settings.with_settings
def TV(s):
    """Type variable"""
    if settings.highlight():
        return [{'text': s, 'color': 3}]
    else:
        return s

@settings.with_settings
def Gray(s):
    """Grey output"""
    if settings.highlight():
        return [{'text': s, 'color': 4}]
    else:
        return s

@settings.with_settings
def KWRed(s):
    """Red keyword"""
    if settings.highlight():
        return [{'text': s, 'color': 5}]
    else:
        return s

@settings.with_settings
def KWGreen(s):
    """Green keyword"""
    if settings.highlight():
        return [{'text': s, 'color': 6}]
    else:
        return s

@settings.with_settings
def print_ast(thy, ast, *, line_length=None):
    res = [[]]
    cur_line = 0
    indent = 0

    def add_normal(s, **kwargs):
        res[cur_line].extend(N(s, **kwargs))
    
    def add_bound(s):
        res[cur_line].extend(B(s))

    def add_var(s):
        res[cur_line].extend(V(s))

    def add_tvar(s):
        res[cur_line].extend(TV(s))

    def newline():
        nonlocal cur_line
        res.append([])
        cur_line += 1
        if indent > 0:
            add_normal(' ' * indent)

    def rec(ast):
        nonlocal indent

        if ast.ty == "bracket":
            add_normal('(')
            indent += 1
            rec(ast.body)
            indent -= 1
            add_normal(')')
        elif ast.ty == "show_type":
            rec(ast.body)
            add_normal('::')
            rec(ast.ast_T)
        elif ast.ty == "svar_name":
            add_var("?" + ast.name)
        elif ast.ty == "var_name":
            add_var(ast.name)
        elif ast.ty == "const_name":
            add_normal(ast.name, link={'name': ast.link_name, 'ty': extension.CONSTANT})
        elif ast.ty == "number":
            add_normal(str(ast.n))
        elif ast.ty == "list":
            add_normal("[")
            if len(ast.entries) > 0:
                rec(ast.entries[0])
            for e in ast.entries[1:]:
                add_normal(", ")
                rec(e)
            add_normal("]")
        elif ast.ty == "set":
            add_normal("{")
            if len(ast.entries) > 0:
                rec(ast.entries[0])
            for e in ast.entries[1:]:
                add_normal(", ")
                rec(e)
            add_normal("}")
        elif ast.ty == "operator":
            add_normal(ast.symbol, link={'name': ast.link_name, 'ty': extension.CONSTANT})
        elif ast.ty == "binary_op":
            if line_length and print_length(print_ast(thy, ast)) > line_length:
                if ast.op.symbol in ("-->", "⟶"):
                    rec(ast.arg1)
                    add_normal(" ")
                    newline()
                    rec(ast.op)
                    add_normal(" ")
                    indent += 3
                    rec(ast.arg2)
                    indent -= 3
                else:
                    rec(ast.arg1)
                    add_normal(" ")
                    rec(ast.op)
                    add_normal(" ")
                    newline()
                    rec(ast.arg2)
            else:
                rec(ast.arg1)
                add_normal(" ")
                rec(ast.op)
                add_normal(" ")
                rec(ast.arg2)
        elif ast.ty == "unary_op":
            rec(ast.op)
            rec(ast.arg)
        elif ast.ty == "binder":
            add_normal(ast.symbol)
        elif ast.ty == "binder_appl":
            rec(ast.op)
            rec(ast.bind_var)
            add_normal('. ')
            indent += 2
            rec(ast.body)
            indent -= 2
        elif ast.ty == "bound":
            add_bound(ast.name)
        elif ast.ty == "fun_appl":
            if line_length and print_length(print_ast(thy, ast)) > line_length:
                rec(ast.fun)
                add_normal(' ')
                indent += 2
                newline()
                rec(ast.arg)
                indent -= 2
            else:
                rec(ast.fun)
                add_normal(' ')
                rec(ast.arg)
        elif ast.ty == "ite":
            if line_length and print_length(print_ast(thy, ast)) > line_length:
                add_normal('if ')
                rec(ast.cond)
                add_normal(' then ')
                indent += 2
                newline()
                rec(ast.a1)
                indent -= 2
                newline()
                add_normal('else ')
                indent += 2
                newline()
                rec(ast.a2)
                indent -= 2
            else:                    
                add_normal('if ')
                rec(ast.cond)
                add_normal(' then ')
                rec(ast.a1)
                add_normal(' else ')
                rec(ast.a2)
        elif ast.ty == "char":
            add_normal("'" + ast.c + "'")
        elif ast.ty == "string":
            add_normal('"' + ast.s + '"')
        elif ast.ty == "interval":
            add_normal('{')
            rec(ast.left)
            add_normal('..')
            rec(ast.right)
            add_normal('}')
        elif ast.ty == "fun_upd":
            add_normal('(')
            rec(ast.f)
            add_normal(')(')
            assert len(ast.upds) > 0
            rec(ast.upds[0][0])
            add_normal(' := ')
            rec(ast.upds[0][1])
            for a, b in ast.upds[1:]:
                add_normal(', ')
                rec(a)
                add_normal(' := ')
                rec(b)
            add_normal(')')
        elif ast.ty == "collect":
            add_normal('{')
            rec(ast.bind_var)
            add_normal('. ')
            rec(ast.body)
            add_normal('}')
        elif ast.ty == 'stvar_name':
            add_tvar("'?" + ast.name)
        elif ast.ty == 'tvar_name':
            add_tvar("'" + ast.name)
        elif ast.ty == 'type_constr':
            if len(ast.args) == 0:
                add_normal(ast.name)
            elif len(ast.args) == 1:
                rec(ast.args[0])
                add_normal(' ')
                add_normal(ast.name)
            else:
                add_normal('(')
                rec(ast.args[0])
                for arg in ast.args[1:]:
                    add_normal(', ')
                    rec(arg)
                add_normal(') ')
                add_normal(ast.name)
        elif ast.ty == 'fun_type':
            rec(ast.arg1)
            add_normal(ast.fun_op)
            rec(ast.arg2)
        else:
            raise TypeError

    rec(ast)

    for i in range(len(res)):
        if not settings.highlight():
            res[i] = ''.join(res[i])

    if not line_length:
        res = res[0]

    return res
