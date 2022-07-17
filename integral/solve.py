"""Functions for solving equations"""

from integral.expr import Expr

def solve_equation(f: Expr, a: Expr, x: str):
    """Solve the equation f(x) = a for the variable x.
    
    The method is try to isolate x on the left side by moving expressions
    independent of x to the right side.

    """
    if f.is_var():
        if f.name == x:
            return a
        else:
            raise NotImplementedError
    elif f.is_times():
        u, v = f.args
        if not u.contains_var(x):
            return solve_equation(v, a / u, x)
        elif not v.contains_var(x):
            return solve_equation(u, a / v, x)
        else:
            raise NotImplementedError
    else:
        raise NotImplementedError
