"""Functions for solving equations"""

from typing import Optional, Tuple

from integral import expr
from integral.expr import Expr, POS_INF, NEG_INF, Const, Var


def solve_equation(f: Expr, a: Expr, x: str) -> Optional[Expr]:
    """Solve the equation f(x) = a for the variable x.
    
    First, try to isolate x on the left side by moving expressions
    independent of x to the right side.

    Next, several other heuristics are tried, such as using linearity.

    """
    if f.is_var():
        if f.name == x:
            return a
    if f.is_plus():
        u, v = f.args
        if not u.contains_var(x):
            # u + v = a  ==>  v = a - u
            return solve_equation(v, a - u, x)
        if not v.contains_var(x):
            # u + v = a  ==>  u = a - v
            return solve_equation(u, a - v, x)
    if f.is_uminus():
        # -u = a  ==>  u = -a
        u, = f.args
        return solve_equation(u, -a, x)
    if f.is_minus():
        u, v = f.args
        if not u.contains_var(x):
            # u - v = a  ==>  v = u - a
            return solve_equation(v, u - a, x)
        if not v.contains_var(x):
            # u - v = a  ==>  u = v + a
            return solve_equation(u, v + a, x)
    if f.is_times():
        u, v = f.args
        if not u.contains_var(x):
            # u * v = a  ==>  v = a / u
            return solve_equation(v, a / u, x)
        if not v.contains_var(x):
            # u * v = a  ==>  u = a / v
            return solve_equation(u, a / v, x)
    if f.is_divides():
        u, v = f.args
        if not u.contains_var(x):
            # u / v = a  ==>  v = a / u
            rhs = u / a
            if u.is_constant() and a in (POS_INF, NEG_INF):
                rhs = Const(0)
            return solve_equation(v, rhs, x)
        if not v.contains_var(x):
            # u / v = a  ==>  u = v * a
            return solve_equation(u, v * a, x)
    if f.is_fun():
        if f.func_name == "log":
            return solve_equation(f.args[0], expr.exp(a), x)
        elif f.func_name == "exp":
            return solve_equation(f.args[0], expr.log(a), x)
    
    # Try linearity
    extract_res = extract_linear(f, x)
    if extract_res:
        # b * x + c = a  ==>  x = (a - c) / b
        b, c = extract_res
        if b.normalize() != Const(0):
            return ((a - c) / b).normalize()


def extract_linear(e: Expr, x: str) -> Optional[Tuple[Expr, Expr]]:
    """Attempt to write e in the form a * x + b.
    
    If this is possible, return the pair (a, b). Otherwise return None.
    The results should be normalized before use.
    
    """
    if not e.contains_var(x):
        return Const(0), e
    elif e.is_var():
        assert e.name == x
        return Const(1), Const(0)
    elif e.is_plus():
        res1 = extract_linear(e.args[0], x)
        res2 = extract_linear(e.args[1], x)
        if res1 and res2:
            return res1[0] + res2[0], res1[1] + res2[1]
    elif e.is_uminus():
        res = extract_linear(e.args[0], x)
        if res:
            return -res[0], -res[1]
    elif e.is_minus():
        res1 = extract_linear(e.args[0], x)
        res2 = extract_linear(e.args[1], x)
        if res1 and res2:
            return res1[0] - res2[0], res1[1] - res2[1]
    elif e.is_times():
        u, v = e.args
        if not u.contains_var(x):
            res = extract_linear(v, x)
            if res:
                return u * res[0], u * res[1]
        elif not v.contains_var(x):
            res = extract_linear(u, x)
            if res:
                return v * res[0], v * res[1]
    elif e.is_divides():
        u, v = e.args
        if not v.contains_var(x):
            res = extract_linear(u, x)
            if res:
                return res[0] / v, res[1] / v

def solve_for_term(eq: Expr, t: Expr) -> Optional[Expr]:
    """A more general solving procedure for term t.
    
    Given equation of the form f = g, where both f and g may contain t.
    Try to derive an equation of the form t = t' from f = g.
    
    """
    if not eq.is_equals():
        raise AssertionError("solve_for_term: input should be an equation.")

    # Take variable name that have not appeared
    var_name = "_v"
    var = Var(var_name)

    # Replace all appearances of t in equation by var
    eq = eq.replace(t, var)

    # Now consider some simple cases
    if not eq.rhs.contains_var(var_name):
        return solve_equation(eq.lhs, eq.rhs, var_name)
    
    if not eq.lhs.contains_var(var_name):
        return solve_equation(eq.rhs, eq.lhs, var_name)
    
    # Finally, try transforming the equation to f = 0
    res = solve_equation(eq.lhs - eq.rhs, Const(0), var_name)
    if res:
        if res.contains_var(var_name):
            raise AssertionError("solve_equation returns %s" % res)
        else:
            return res
