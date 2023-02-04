from kernel.type import RealType, TFun
from kernel import term
from logic import conv
from data import real
from data import set as hol_set
from integral import expr
from integral.expr import Expr


evalat = term.Const('evalat', TFun(TFun(RealType, RealType), RealType, RealType, RealType))
real_derivative = term.Const('real_derivative', TFun(TFun(RealType, RealType), RealType, RealType))
real_integral = term.Const('real_integral', TFun(hol_set.setT(RealType), TFun(RealType, RealType), RealType))

def expr_to_holpy(expr: Expr) -> term.Term:
    """Convert an expression to holpy term."""
    assert isinstance(expr, Expr), "expr_to_holpy"
    if expr.is_var():
        return term.Var(expr.name, RealType)
    elif expr.is_const():
        return term.Real(expr.val)
    elif expr.is_op():
        if expr.op == '-' and len(expr.args) == 1:
            return -(expr_to_holpy(expr.args[0]))

        if len(expr.args) != 2:
            raise NotImplementedError

        a, b = [expr_to_holpy(arg) for arg in expr.args]
        if expr.op == '+':
            return a + b
        elif expr.op == '-':
            return a - b
        elif expr.op == '*':
            return a * b
        elif expr.op == '/':
            return a / b
        elif expr.op == '^':
            if expr.args[1].is_const() and isinstance(expr.args[1].val, int) and expr.args[1].val >= 0:
                return a ** term.Nat(expr.args[1].val)
            else:
                return a ** b
        else:
            raise NotImplementedError
    elif expr.is_fun():
        if expr.func_name == 'pi':
            return real.pi

        if len(expr.args) != 1:
            raise NotImplementedError

        a = expr_to_holpy(expr.args[0])
        if expr.func_name == 'sin':
            return real.sin(a)
        elif expr.func_name == 'cos':
            return real.cos(a)
        elif expr.func_name == 'tan':
            return real.tan(a)
        elif expr.func_name == 'cot':
            return real.cot(a)
        elif expr.func_name == 'sec':
            return real.sec(a)
        elif expr.func_name == 'csc':
            return real.csc(a)
        elif expr.func_name == 'log':
            return real.log(a)
        elif expr.func_name == 'exp':
            return real.exp(a)
        elif expr.func_name == 'abs':
            return real.hol_abs(a)
        elif expr.func_name == 'sqrt':
            return real.sqrt(a)
        elif expr.func_name == 'atan':
            return real.atn(a)
        else:
            raise NotImplementedError
    elif expr.is_deriv():
        raise NotImplementedError
    elif expr.is_integral():
        a, b = expr_to_holpy(expr.lower), expr_to_holpy(expr.upper)
        var = term.Var(expr.var, RealType)
        f = term.Lambda(var, expr_to_holpy(expr.body))
        return real_integral(real.closed_interval(a, b), f)
    elif expr.is_evalat():
        a, b = expr_to_holpy(expr.lower), expr_to_holpy(expr.upper)
        var = term.Var(expr.var, RealType)
        f = term.Lambda(var, expr_to_holpy(expr.body))
        return evalat(f, a, b)
    else:
        print("expr_to_holpy: unknown expression %s" % expr)
        raise NotImplementedError


def holpy_to_expr(t: term.Term) -> Expr:
    """Convert a HOL term to expression."""
    assert isinstance(t, term.Term), "holpy_to_expr"
    if t.is_var():
        if t.T == RealType:
            return expr.Var(t.name)
        else:
            raise NotImplementedError
    elif t == real.pi:
        return expr.pi
    elif t.is_number():
        val = t.dest_number()
        return expr.Const(val)
    elif t.is_plus():
        return holpy_to_expr(t.arg1) + holpy_to_expr(t.arg)
    elif t.is_minus():
        return holpy_to_expr(t.arg1) - holpy_to_expr(t.arg)
    elif t.is_uminus():
        return -holpy_to_expr(t.arg)
    elif t.is_times():
        return holpy_to_expr(t.arg1) * holpy_to_expr(t.arg)
    elif t.is_divides():
        return holpy_to_expr(t.arg1) / holpy_to_expr(t.arg)
    elif t.is_nat_power() and t.arg.is_number():
        return holpy_to_expr(t.arg1) ** t.arg.dest_number()
    elif t.is_real_power():
        return holpy_to_expr(t.arg1) ** holpy_to_expr(t.arg)
    elif t.is_comb('sqrt', 1):
        return expr.sqrt(holpy_to_expr(t.arg))
    elif t.is_comb('abs', 1):
        return expr.Fun('abs', holpy_to_expr(t.arg))
    elif t.is_comb('exp', 1):
        return expr.exp(holpy_to_expr(t.arg))
    elif t.is_comb('log', 1):
        return expr.log(holpy_to_expr(t.arg))
    elif t.is_comb('sin', 1):
        return expr.sin(holpy_to_expr(t.arg))
    elif t.is_comb('cos', 1):
        return expr.cos(holpy_to_expr(t.arg))
    elif t.is_comb('tan', 1):
        return expr.tan(holpy_to_expr(t.arg))
    elif t.is_comb('cot', 1):
        return expr.cot(holpy_to_expr(t.arg))
    elif t.is_comb('sec', 1):
        return expr.sec(holpy_to_expr(t.arg))
    elif t.is_comb('csc', 1):
        return expr.csc(holpy_to_expr(t.arg))
    else:
        raise NotImplementedError


def eval_hol_expr(t: term.Term):
    """Evaluate an HOL term of type real.

    First try the exact evaluation with real_eval. If that fails, fall back
    to approximate evaluation with real_approx_eval.

    """
    try:
        res = real.real_eval(t)
    except conv.ConvException:
        res = real.real_approx_eval(t)

    return res
