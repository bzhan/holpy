"""Rules for integration."""

from integral import expr
from integral import poly
from integral.expr import Var, Const, Fun, EvalAt, Op, Integral, Expr, trig_identity, sympy_style, holpy_style
import functools, operator
from sympy import apart
from sympy.parsing import sympy_parser
from sympy import solvers, Interval, solveset
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
        e = e.normalize()
        if e.ty == expr.INTEGRAL and e.body.ty == expr.OP and e.body.op == "/":
            old = e
            up_monos, up_common     = expr.extract(e.body.args[0].to_poly())
            down_monos, down_common = expr.extract(e.body.args[1].to_poly())
            common_item = up_common.keys() & down_common.keys()
            min_value = {}
            for key in common_item:
                min_value[key]    = up_common[key] if up_common[key] < down_common[key] else down_common[key]
                up_common[key]   -= min_value[key]
                down_common[key] -= min_value[key]
            if len(min_value) != 0:
                #numerartor and denominator have same element.
                upp   = [(k ^ Const(v)).normalize() for k, v in up_common.items()]
                dpp   = [(k ^ Const(v)).normalize() for k, v in down_common.items()]
                upp_1 = functools.reduce(operator.mul, upp[1:], upp[0])
                dpp_1 = functools.reduce(operator.mul, dpp[1:], dpp[0])
                simp  = (sum(up_monos[1:], up_monos[0]) * upp_1).normalize() / (sum(down_monos[1:], down_monos[0]) * dpp_1).normalize()
                return Integral(old.var, old.lower, old.upper, simp.normalize())
            else:
                return Integral(old.var, old.lower, old.upper, old.body.args[0].normalize()/old.body.args[1].normalize())
        else:
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
                        if a.func_name == "sec":
                            return EvalAt(e.var, e.lower, e.upper, expr.Fun("tan", *a.args))
                        elif a.func_name == "csc":
                            return EvalAt(e.var, e.lower, e.upper, -expr.Fun("cot", *a.args))
                        else:
                            raise NotImplementedError
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
                    elif b.op in ("+", "-"):
                        if c == Var(e.var) and d.ty == expr.CONST:
                            #Integral of 1 / (x + c) is log(x + c)
                            return EvalAt(e.var, e.lower, e.upper, a * expr.log(Fun("abs", b)))
                        elif b.op == "+" and d.ty == expr.OP and d.op == "^" and \
                                d.args[0] == Var(e.var) and d.args[1] == Const(2) and \
                                c == expr.Const(1):
                            #Integral of 1 / x ^ 2 + 1 is arctan(x)
                            return EvalAt(e.var, e.lower, e.upper, expr.arctan(Var(e.var)))
                elif b == Var(e.var):
                    return EvalAt(e.var, e.lower, e.upper, a * expr.log(Fun("abs", b)))
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

class Substitution(Rule):
    """Apply substitution."""
    def __init__(self, var_name, var_subst):
        assert isinstance(var_name, str) and isinstance(var_subst, expr.Expr)
        self.var_name = var_name
        self.var_subst = var_subst
        self.name = "Substitution"

    def eval(self, e):
        if e.ty != expr.INTEGRAL:
            return e
        self.var_name = parser.parse_expr(self.var_name)
        d_name = expr.deriv(str(self.var_name.findVar()), self.var_name) # Derivates substitute expr
        d_subst = expr.deriv(e.var, self.var_subst) #Derivates initial expr
        d_subst = d_subst.replace_trig(self.var_subst.normalize(), self.var_subst)
        div = d_name / d_subst
        body2 = (e.body * div).replace_trig(self.var_subst, self.var_name)
        body2 = parser.parse_expr(str(sympy_parser.parse_expr(str(body2).replace("^","**"))).replace("**","^"))
        sol = solvers.solve(expr.sympy_style(self.var_name - self.var_subst), expr.sympy_style(str(e.var)))
        body2 = body2.replace_trig(expr.holpy_style(str(e.var)), expr.holpy_style(sol[0]))
        if self.var_name.ty == expr.VAR:
            #u subsitutes f(x)
            lower2 = self.var_subst.subst(e.var, e.lower).normalize()
            upper2 = self.var_subst.subst(e.var, e.upper).normalize()
        else:
            #x substitue g(u)
            lower2 = solvers.solve(sympy_parser.parse_expr(str(self.var_name - e.lower).replace("^","**")), sympy_parser.parse_expr(str(self.var_name.findVar())))[0]
            upper2 = solvers.solve(sympy_parser.parse_expr(str(self.var_name - e.upper).replace("^","**")), sympy_parser.parse_expr(str(self.var_name.findVar())))[0]
            lower2 = parser.parse_expr(str(lower2).replace("**", "^"))
            upper2 = parser.parse_expr(str(upper2).replace("**", "^"))
        var_subst_subst = expr.deriv(e.var, self.var_subst)
        g, l = var_subst_subst.ranges(e.var, e.lower, e.upper)
        new_integral = []
        var = parser.parse_expr(str(e.var))
        if len(g) != 0:
            for i, j in g:
                x, y = self.var_subst.replace(var, i).normalize(), self.var_subst.replace(var, j).normalize()
                new_integral.append(expr.Integral(str(self.var_name.findVar()), x, y, body2))
        if len(l) != 0:
            for i, j in l:
                x, y = self.var_subst.replace(var, i).normalize(), self.var_subst.replace(var, j).normalize()
                new_integral.append(expr.Integral(str(self.var_name.findVar()), y, x, expr.Op("-", body2)))
        return sum(new_integral[1:], new_integral[0])

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
        gu = solvers.solve(expr.sympy_style(var_subst - var_name), expr.sympy_style(e.var))
        gu = gu[0] if isinstance(gu, list) else gu
        gu = expr.holpy_style(gu)
        c = e.body.replace_trig(parser.parse_expr(e.var), gu)
        new_problem_body = (e.body.replace_trig(parser.parse_expr(e.var), gu)*expr.deriv(str(var_name), gu)).normalize().normalize()
        var_subst_deriv = expr.deriv(e.var, var_subst)
        up, down = var_subst_deriv.ranges(e.var, e.lower, e.upper)
        new_integral = []
        if len(up) != 0:
            for l, u in up:
                i = expr.holpy_style(expr.sympy_style(var_subst).subs(expr.sympy_style(e.var), expr.sympy_style(l)))
                j = expr.holpy_style(expr.sympy_style(var_subst).subs(expr.sympy_style(e.var), expr.sympy_style(u)))
                new_integral.append(expr.Integral(self.var_name, i, j, new_problem_body))
        if len(down) != 0:
            for l, u in down:
                i = expr.holpy_style(expr.sympy_style(var_subst).subs(expr.sympy_style(e.var), expr.sympy_style(l)))
                j = expr.holpy_style(expr.sympy_style(var_subst).subs(expr.sympy_style(e.var), expr.sympy_style(u)))
                new_integral.append(expr.Integral(self.var_name, j, i, expr.Op("-",new_problem_body).normalize()))
        return sum(new_integral[1:], new_integral[0]), new_problem_body



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
    def eval(self, e):
        if e.ty != expr.INTEGRAL:
            return e
        abs_expr, norm_expr = e.body.normalize().getAbsByMonomial()
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
                    body.replace_trig(a, a.args[0])
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
    def __init__(self, lhs):
        assert isinstance(lhs, expr.Expr)
        self.lhs = lhs
        self.name = "Integrate by equation"
    
    def eval(self, e):
        integral_in_e = e.separate_integral()
        flag = 0 # If e have integral same as lhs
        if integral_in_e == []:
            return e
        same_integral = []
        print("----", e)
        print("integral_in_e: ", integral_in_e)
        print("self.lhs", self.lhs)
        for i in integral_in_e:
            if i[0].normalize() == self.lhs.normalize():
                same_integral.append(i[0])
        if len(same_integral) == 0:
            return e
        same_integral = same_integral[0]
        body = copy.deepcopy(e)
        temp_body = copy.deepcopy(body)
        temp_body = temp_body.replace_trig(same_integral, Const(0)).normalize()
        g = expr.Var("G")
        i = expr.Var("I")
        body = body.replace_trig(temp_body, g).replace(same_integral, i)
        print("temp:", temp_body)
        print("body: ", body)
        k = same_integral - self.lhs
        print("same: ", same_integral)
        print("k: ", k.normalize())
        s = solvers.solve(expr.sympy_style(body - i), expr.sympy_style(i))
        print("s: ", s, temp_body)
        s = holpy_style(s[0]).replace_trig(g, temp_body)
        return s
        # print("final: ", s.replace_trig(g, ))
        # v = expr.Var("I")
        # new_e = copy.deepcopy(e)
        # for i in same_integral:
        #     new_e = new_e.replace_trig(i[0], v)
        # s = solvers.solve(expr.sympy_style(new_e - v), expr.sympy_style(v))
        # return expr.holpy_style(s[0])