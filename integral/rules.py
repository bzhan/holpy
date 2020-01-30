"""Rules for integration."""

from integral import expr
from integral import poly
from integral.expr import Var, Const, Fun, EvalAt, Op, Integral, Expr, trig_identity, sympy_style, holpy_style, OP, CONST, INTEGRAL
import functools, operator
from sympy.parsing import sympy_parser
from sympy import solvers, Interval, solveset, expand_multinomial, apart
from integral import parser
from fractions import Fraction
import copy

class Rule:
    """Represents a rule for integration. It takes an integral
    to be evaluated (as an expression), then outputs a new
    expression that it is equal to.
    
    """
    def eval(self, e):
        """Evaluation of the rule on the given expression. Returns
        a new expression.

        """
        raise NotImplementedError

class Simplify(Rule):
    """Perform algebraic simplification. This treats the
    expression as a polynomial, and normalizes the polynomial.

    """
    def __init__(self):
        self.name = "Simplify"
    
    def eval(self, e):
        return e.normalize()

class Linearity(Rule):
    """Applies linearity rules:
    
    INT (a + b) = INT a + INT b,
    INT (c * a) = c * INT a  (where c is a constant).
    INT (c / a) = c * INT 1 / a (where c is a contant)
    """
    def __init__(self):
        self.name = "Linearity"
    
    def eval(self, e):
        def eval1(e):
            if e.ty != expr.INTEGRAL:
                return e           
            p = e.body.to_poly()
            ts = []
            for mono in p.monomials:
                t = expr.Integral(e.var, e.lower, e.upper, expr.from_mono(poly.Monomial(Const(1), mono.factors)))
                if mono.coeff != Const(1):
                    t = mono.coeff * t
                ts.append(t)
            if len(ts) == 0:
                return Const(0)
            else:
                return sum(ts[1:], ts[0])
        def eval2(c):
            integrals = c.separate_integral()
            result = []
            for i in integrals:
                result.append(eval1(i[0]))
            for i in range(len(integrals)):
                c = c.replace_trig(integrals[i][0], result[i]) # e = a * b * INT c
            return c
        c = eval2(e).normalize().normalize()
        return eval2(c)

class CommonIntegral(Rule):
    """Applies common integrals:

    INT c = c * x,
    INT x ^ n = x ^ (n + 1) / (n + 1),  (where n != -1, c is a constant)
    INT 1 / x ^ n = (-n) / x ^ (n + 1), (where n != 1)
    INT sin(x) = -cos(x),
    INT cos(x) = sin(x),
    INT 1 / x = log(|x|)
    INT e^x = e^x
    INT 1 / (x^2 + 1) = arctan(x)
    INT sec(x)^2 = tan(x)
    INT csc(x)^2 = -cot(x)
    """
    def __init__(self):
        self.name = "CommonIntegral"


    def eval(self, e):
        if e.ty != expr.INTEGRAL:
            return e

        if e.body == Var(e.var):
            # Integral of x is x^2/2.
            return EvalAt(e.var, e.lower, e.upper, (Var(e.var) ^ Const(2)) / Const(2))
        elif e.body.is_constant(): 
            if e.body.ty == expr.CONST and e.body.val == 1:
                # Integral of 1 is x
                integral = Var(e.var)
            else:
                # Integral of c is c*x
                integral = e.body * Var(e.var)
            return EvalAt(e.var, e.lower, e.upper, integral)
        elif e.body.ty == expr.OP:
            if e.body.op == "^":
                a, b = e.body.args
                if a.ty == expr.CONST and b.ty == expr.CONST:
                    integral = e.body * Var(e.var)
                    return EvalAt(e.var, e.lower, e.upper, integral)
                elif a == Var(e.var) and b.ty == expr.CONST and b.val != -1:
                    # Integral of x ^ n is x ^ (n + 1)/(n + 1)
                    # Intgeral of (x + c) ^ n = (x + c) ^ (n + 1) / (n + 1)
                    integral = (a ^ Const(b.val + 1)) / Const(b.val + 1)
                    return EvalAt(e.var, e.lower, e.upper, integral)
                elif a == Var(e.var) and b.ty == expr.CONST and b.val == -1:
                    # Integral of x ^ -1 is log(x)
                    # Integral of (x + c) ^ -1 is log(x)
                    return EvalAt(e.var, e.lower, e.upper, expr.log(Fun("abs",a)))
                elif a.ty == expr.FUN:
                    if b ==  Const(2):
                        if a.func_name == "sec" and a.args[0] == Var(e.var):
                            return EvalAt(e.var, e.lower, e.upper, expr.Fun("tan", *a.args))
                        elif a.func_name == "csc" and a.args[0] == Var(e.var):
                            return EvalAt(e.var, e.lower, e.upper, -expr.Fun("cot", *a.args))
                        else:
                            return e
                    else:
                        return e
                if a.ty == OP and a.op == "+" and a.args[0] == Const(1) and a.args[1].ty == OP \
                    and a.args[1].op == "^" and a.args[1].args[0] == Var(e.var) and a.args[1].args[1] == Const(2) \
                    and b == Const(-1):
                    # (1 + x^2) ^ (-1) => arctan(x)
                    return EvalAt(e.var, e.lower, e.upper, expr.arctan(Var(e.var)))
                else:
                    return e
            elif e.body.op == "/":
                a, b = e.body.args
                if b.ty == expr.OP and a.ty == expr.CONST:
                    c, d = b.args
                    if b.op == "^":
                        if (c == Var(e.var) or c.op in ("+", "-") and c.args[0] == Var(e.var) and \
                                c.args[1].ty == expr.CONST) and d.ty == expr.CONST and d.val != 1:
                            #Integral of 1 / x ^ n is (-n) / x ^ (n + 1)
                            #Integral of 1 / (x + c) ^ n is (-1) / (n - 1) * x ^ (n - 1)
                            integral = a * Const(-1) / (Const(d.val - 1) * (c ^ Const(d.val - 1)))
                            return EvalAt(e.var, e.lower, e.upper, integral)
                        else:
                            return e
                    elif b.op in ("+", "-"):
                        if c == Var(e.var) and d.ty == expr.CONST:
                            #Integral of 1 / (x + c) is log(x + c)
                            return EvalAt(e.var, e.lower, e.upper, a * expr.log(Fun("abs", b)))
                        elif b.op == "+" and d.ty == expr.OP and d.op == "^" and \
                                d.args[0] == Var(e.var) and d.args[1] == Const(2) and \
                                c == expr.Const(1):
                            #Integral of 1 / x ^ 2 + 1 is arctan(x)
                            return EvalAt(e.var, e.lower, e.upper, expr.arctan(Var(e.var)))
                        else:
                            return e
                    else:
                        return e
                elif b == Var(e.var):
                    return EvalAt(e.var, e.lower, e.upper, a * expr.log(Fun("abs", b)))
                else:
                    return e
            else:
                return e

        elif e.body.ty == expr.FUN:
            if e.body.func_name == "sin" and e.body.args[0] == Var(e.var):
                return EvalAt(e.var, e.lower, e.upper, -expr.cos(Var(e.var)))
            elif e.body.func_name == "cos" and e.body.args[0] == Var(e.var):
                return EvalAt(e.var, e.lower, e.upper, expr.sin(Var(e.var)))
            elif e.body.func_name == "exp" and e.body.args[0] == Var(e.var):
                return EvalAt(e.var, e.lower, e.upper, expr.exp(Var(e.var)))
            else:
                return e
        else:
            return e

class CommonDeriv(Rule):
    """Common rules for evaluating a derivative."""

    def eval(self, e):
        if e.ty == expr.DERIV:
            return expr.deriv(e.var, e.body)
        else:
            return e

class OnSubterm(Rule):
    """Apply given rule on subterms."""
    def __init__(self, rule):
        assert isinstance(rule, Rule)
        self.rule = rule

    def eval(self, e):
        rule = self.rule
        if e.ty in (expr.VAR, expr.CONST):
            return rule.eval(e)
        elif e.ty == expr.OP:
            args = [self.eval(arg) for arg in e.args]
            return rule.eval(expr.Op(e.op, *args))
        elif e.ty == expr.FUN:
            args = [self.eval(arg) for arg in e.args]
            return rule.eval(expr.Fun(e.func_name, *args))
        elif e.ty == expr.DERIV:
            return rule.eval(expr.Deriv(e.var, self.eval(e.body)))
        elif e.ty == expr.INTEGRAL:
            return rule.eval(expr.Integral(e.var, self.eval(e.lower), self.eval(e.upper), self.eval(e.body)))
        elif e.ty == expr.EVAL_AT:
            return rule.eval(expr.EvalAt(e.var, self.eval(e.lower), self.eval(e.upper), self.eval(e.body)))
        else:
            raise NotImplementedError

class Substitution1(Rule):
    """Apply substitution u = g(x) x = y(u)  f(x) = x+5  u=>x+1   (x+1)+4 """
    """INT x:[a, b]. f(g(x))*g(x)' = INT u:[g(a), g(b)].f(u)"""
    def __init__(self, var_name, var_subst):
        self.name = "Substitution"
        self.var_name = var_name
        self.var_subst = var_subst

    def eval(self, e):
        var_name = parser.parse_expr(self.var_name)
        var_subst = self.var_subst
        dfx = expr.deriv(e.var, var_subst)
        body =holpy_style(sympy_style(e.body/dfx).simplify())
        body = body.normalize().replace_trig(var_subst.normalize(), var_name)
        lower = var_subst.subst(e.var, e.lower).normalize()
        upper = var_subst.subst(e.var, e.upper).normalize()
        if parser.parse_expr(e.var) not in body.findVar():
            if sympy_style(lower) <= sympy_style(upper):
                return Integral(self.var_name, lower, upper, body), body
            else:
                return Integral(self.var_name, upper, lower, Op("-", body).normalize()), body
        else:
            gu = solvers.solve(expr.sympy_style(var_subst - var_name), expr.sympy_style(e.var))
            gu = gu[-1] if isinstance(gu, list) else gu
            gu = expr.holpy_style(gu)
            c = e.body.replace_trig(parser.parse_expr(e.var), gu)
            new_problem_body = holpy_style(sympy_style(e.body.replace_trig(parser.parse_expr(e.var), gu)*expr.deriv(str(var_name), gu)))
            lower = holpy_style(sympy_style(var_subst).subs(sympy_style(e.var), sympy_style(e.lower)))
            upper = holpy_style(sympy_style(var_subst).subs(sympy_style(e.var), sympy_style(e.upper)))
            if sympy_style(lower) < sympy_style(upper):
                return Integral(self.var_name, lower, upper, new_problem_body), new_problem_body
            else:
                return Integral(self.var_name, upper, lower, Op("-", new_problem_body).normalize()), new_problem_body

class Substitution2(Rule):
    """Apply substitution x = f(u)"""
    def __init__(self, var_name, var_subst):
        #such as var_name: "u" var_subst: "sin(u)"
        self.var_name = var_name
        self.var_subst = var_subst
        self.name = "Substitution inverse"

    def eval(self, e):
        subst_deriv = expr.deriv(self.var_name, self.var_subst) #dx = d(x(u)) = x'(u) *du
        new_e_body = e.body.replace_trig(expr.holpy_style(str(e.var)), self.var_subst) #replace all x with x(u)
        new_e_body = expr.Op("*", new_e_body, subst_deriv) # g(x) = g(x(u)) * x'(u)
        lower = solvers.solve(expr.sympy_style(self.var_subst - e.lower))[0]
        upper = solvers.solve(expr.sympy_style(self.var_subst - e.upper))[0]
        return expr.Integral(self.var_name, expr.holpy_style(lower), expr.holpy_style(upper), new_e_body)
        

class unfoldPower(Rule):
    def eval(self, e):
        assert isinstance(e, expr.Integral)
        body = e.body
        if body.ty != OP or not (body.op == "^" and body.args[1].ty == CONST and Fraction(body.args[1].val).denominator == 1):
            return e
        unfold = holpy_style(expand_multinomial(sympy_style(body)))
        return Integral(e.var, e.lower, e.upper, unfold)


class Equation(Rule):
    """Apply substitution for equal expressions"""
    def __init__(self, old_expr, new_expr):
        assert isinstance(old_expr, Expr) and isinstance(new_expr, Expr)
        self.old_expr = old_expr
        self.new_expr = new_expr
        self.name = "Equation"
    
    def eval(self, e):
        if self.new_expr.normalize() != self.old_expr.normalize():
            return Integral(e.var, e.lower, e.upper, self.old_expr)
        else:
            return Integral(e.var, e.lower, e.upper, self.new_expr)

class TrigSubstitution(Rule):
    """Apply trig identities transformation on expression."""
    def eval(self, e):
        exprs =  e.body.identity_trig_expr(trig_identity)
        n_expr = [] #exprs in a tuple        
        for i in range(len(exprs)):
            n_expr.append((Integral(e.var, e.lower, e.upper, exprs[i][0]),exprs[i][1]))
        return n_expr
        

class IntegrationByParts(Rule):
    """Apply integration by parts."""
    def __init__(self, u, v):
        assert isinstance(u, expr.Expr) and isinstance(v, expr.Expr)
        self.u = u
        self.v = v
        self.name = "Integrate by parts"

    def eval(self, e):
        if e.ty != expr.INTEGRAL:
            return e
        e.body = e.body.normalize()
        du = expr.deriv(e.var, self.u)
        dv = expr.deriv(e.var, self.v)
        udv = (self.u * dv).normalize().normalize()
        if udv == e.body:
            return expr.EvalAt(e.var, e.lower, e.upper, (self.u * self.v).normalize()) - \
                   expr.Integral(e.var, e.lower, e.upper, (self.v * du).normalize())
        else:
            print("%s != %s" % (str(udv), str(e.body)))
            raise NotImplementedError

class PolynomialDivision(Rule):
    """Simplify the representation of polynomial divided by polinomial.
    """
    def __init__(self):
        self.name = "Fraction Division"
    def eval(self, e):
        if e.ty != expr.INTEGRAL:
            return e
        result = apart(expr.sympy_style(e.body))
        return expr.Integral(e.var, e.lower, e.upper, parser.parse_expr(str(result).replace("**","^")))

class ElimAbs(Rule):
    """Eliminate abstract value."""
    def __init__(self):
        self.name = "Elimate abs"

    def check_zero_point(self, e):
        integrals = e.separate_integral()
        if not integrals:
            return False
        abs_info = []
        for i, j in integrals:
            abs_expr = i.getAbs()
            abs_info += [(a, i) for a in abs_expr]
        zero_point = []
        for a, i in abs_info:
            arg = a.args[0]
            zeros = solveset(expr.sympy_style(arg), expr.sympy_style(i.var), Interval(sympy_style(i.lower), sympy_style(i.upper), left_open = True, right_open = True))
            zero_point += zeros
        return len(zero_point) > 0

    def get_zero_point(self, e):
        abs_expr = e.body.getAbs()
        zero_point = []
        for a in abs_expr:
            arg = a.args[0]
            zeros = solveset(expr.sympy_style(arg), expr.sympy_style(e.var), Interval(sympy_style(e.lower), sympy_style(e.upper), left_open = True, right_open = True))
            zero_point += zeros
        return holpy_style(zero_point[0])

    def eval(self, e):
        if e.ty != expr.INTEGRAL:
            return e
        abs_expr = e.body.normalize().getAbsByMonomial()
        if abs_expr != Const(1):
            greator = [] #collect all abs values greater than 0's set
            smallor = [] #collect all abs values smaller than 0's set
            g, s = abs_expr.args[0].ranges(e.var, e.lower, e.upper) # g: value in abs > 0, s: value in abs < 0
            new_integral = []
            for l, h in g:
                body1 = copy.deepcopy(e.body)
                new_integral.append(expr.Integral(e.var, l, h, body1.replace_trig(abs_expr, abs_expr.args[0])))
            for l, h in s:
                body2 = copy.deepcopy(e.body)
                new_integral.append(expr.Integral(e.var, l, h, body2.replace_trig(abs_expr, Op("-", abs_expr.args[0]))))
            return sum(new_integral[1:], new_integral[0])
        else:
            abs_expr = e.body.getAbs()
            zero_point = []
            for a in abs_expr:
                arg = a.args[0]
                zeros = solveset(expr.sympy_style(arg), expr.sympy_style(e.var), Interval(sympy_style(e.lower), sympy_style(e.upper), left_open = True, right_open = True))
                zero_point += zeros
            body = e.body
            new_integral = []
            if not zero_point:
                for a in abs_expr:
                    s = solveset(sympy_style(a.args[0]) > 0, expr.sympy_style(e.var), Interval.open(sympy_style(e.lower), sympy_style(e.upper)))
                    if not s.is_empty:
                        body.replace_trig(a, a.args[0])
                    else:
                        body.replace_trig(a, -a.args[0])
                return expr.Integral(e.var, e.lower, e.upper, body)
            else:
                zero_point += [sympy_style(e.upper), sympy_style(e.lower)]
                zero_point.sort()
                for i in range(len(zero_point) - 1):
                    body = copy.deepcopy(e.body)
                    integer = expr.Integral(e.var, holpy_style(zero_point[i]), holpy_style(zero_point[i + 1]), body)
                    for a in abs_expr:
                        arg = a.args[0]
                        g, l = arg.ranges(e.var, zero_point[i], zero_point[i + 1])
                        if g:
                            integer.body = integer.body.replace_trig(a, a.args[0])
                        if l:
                            integer.body = body.replace_trig(a, Op("-",a.args[0]))
                    new_integral.append(integer)
                        #if Interval(sympy_style(zero_point[i]), sympy_style(zero_point[i + 1]))
                return sum(new_integral[1:], new_integral[0])

class IntegrateByEquation(Rule):
    """When the initial integral occurs in the steps."""
    def __init__(self, lhs, rhs):
        assert isinstance(lhs, Integral)
        self.lhs = lhs.normalize()
        self.rhs = rhs.normalize()
        self.var = lhs.var

    def validate(self):
        """Determine whether the lhs exists in rhs"""
        integrals = self.rhs.separate_integral()
        if not integrals:
            return False
        for i,j in integrals:
            if i.normalize() == self.lhs:
                return True
        return False

    def getCoeff(self):
        """Get coeff of the lhs integral in the rhs."""
        coeff = Const(1)
        def coe(e, uminus = 1):
            nonlocal coeff
            if e.ty == expr.OP:
                if len(e.args) == 1:
                    if e.args[0].normalize() == self.lhs:
                        self.var = e.args[0].var
                        coeff = coeff * Const(-uminus)
                    else:
                        coe(e.arg[0], uminus=-uminus)
                else:
                    if e.op == "+":
                        if e.args[0].normalize() == self.lhs or e.args[1].normalize() == self.lhs:
                            self.var = e.args[0].var
                            coeff = coeff * Const(uminus)
                        else:
                            coe(e.args[0],uminus=uminus)
                            coe(e.args[1],uminus=uminus)
                    elif e.op == "-":
                        if e.args[0].normalize() == self.lhs:
                            self.var = e.args[0].var
                            coeff = coeff * Const(uminus)
                        elif e.args[1].normalize() == self.lhs:
                            self.var = e.args[1].var
                            coeff = coeff * Const(-uminus)
                        else:
                            coe(e.args[0],uminus=uminus)
                            coe(e.args[1], uminus=-uminus)
                    elif e.op == "*":
                        if e.args[1].normalize() == self.lhs:
                            self.var = e.args[1].var
                            coeff = e.args[0]*Const(uminus)
                        else:
                            coe(e.args[0],uminus=uminus)
                            coe(e.args[1],uminus=uminus)
        coe(self.rhs)
        if self.validate():
            return coeff
        else:
            return Const(0)
                
    def eval(self):
        """Eliminate the lhs's integral in rhs by solving equation."""
        coeff = self.getCoeff()
        if coeff == Const(0):
            return self.rhs
        new_rhs = (self.rhs+((-coeff)*self.lhs.alpha_convert(self.var))).normalize().normalize()
        return (new_rhs/(Const(1) - coeff)).normalize()
        