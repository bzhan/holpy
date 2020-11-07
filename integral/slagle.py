import random, string
import collections
import functools
import operator
from integral.expr import *
from integral.parser import parse_expr
from integral import rules
from integral import calc
import math
import multiprocessing.pool

a = Symbol('a', [CONST])
b = Symbol('b', [CONST])
x = Symbol('x', [VAR])
e = Symbol('e', [OP])
pat0 = b + a*x
pat1 = a * x + b
pat2 = a * x
pat3 = e ^ a
pat4 = a + x
pat5 = x + a

linear_pat = [pat0, pat1, pat2, pat4, pat5]


def gen_rand_letter(ex):
    return string.ascii_lowercase[(string.ascii_lowercase.index(ex) + 1) % len(string.ascii_lowercase)]

def linearize(integral):
    """integral is an Expr."""
    new_integral = rules.Linearity().eval(integral)
    new_integral.steps = [calc.LinearityStep(new_integral)]
    return new_integral

def substitution(integral, subst):
    new_var = gen_rand_letter(integral.var)
    new_e, new_e_body = rules.Substitution1(new_var, subst).eval(integral)
    new_e.steps = [calc.SubstitutionStep(e=new_e, var_name=new_var, var_subst=subst, f=new_e_body)]
    return new_e

def linear_substitution(integral):
    assert isinstance(integral, Integral), "%s Should be an integral." % (integral)
    func_body = collect_spec_expr(integral.body, Symbol('f', [FUN]))
    integral.steps = []

    if len(func_body) == 1 and any([match(func_body[0], p) for p in linear_pat]): 
        new_e_1 = substitution(integral, func_body[0])
        new_e_2 = rules.Linearity().eval(new_e_1)
        new_e_2.steps = new_e_1.steps + [calc.LinearityStep(new_e_2)]
        return new_e_2

    elif len(func_body) == 0:
        power_body = collect_spec_expr(integral.body, pat3)
        if len(power_body) == 0:
            return integral
        is_linear = functools.reduce(lambda x,y:x or y, [match(power_body[0], pat) for pat in linear_pat])
        if len(power_body) == 1 and is_linear:
            new_e_1 = substitution(integral, power_body[0])
            new_e_2 = rules.Linearity().eval(new_e_1)
            new_e_2.steps = new_e_1.steps + [calc.LinearityStep(new_e_2)] 
            return new_e_2
        else:
            return integral

    else:
        return integral

def algo_trans(integral):
    assert isinstance(integral, Integral), "%s Should be an integral.l"
    integral = integral.normalize()
    return linear_substitution(linearize(integral))

def add_simplify_step(e, loc=[]):
    """e is an integral, normalize e and add simplify step into e's steps."""
    steps = []
    if hasattr(e, 'steps'):
        steps = e.steps
    e = e.normalize()
    e.steps = steps + [calc.SimplifyStep(e, loc=loc)]
    return e

class AlgorithmRule:
    def eval(self, e):
        """Algorithmic transformation of e.

        Parameters:
        e: original integral.

        Returns:
        If succeed, returns the new integral. Otherwise return e.

        """
        pass

class HeuristicRule:
    def eval(self, e):
        """Heuristic transformation of e.

        Parameters:
        e: original integral.

        Returns:
        A list of possible new integrals. Each of which should equal e.

        """
        pass


class CommonIntegral(AlgorithmRule):
    """Evaluate common integrals."""

    def eval(self, e):
        new_e = rules.OnSubterm(rules.CommonIntegral()).eval(e)
        steps = []
        if new_e != e:
            steps.append(calc.CommonIntegralStep(new_e))
        new_e.steps = steps
        return new_e


class DividePolynomial(AlgorithmRule):
    """Algorithm rule (g) in Slagle's thesis.

    If the integral is in the form f(x)/g(x), attempt to divide f(x)
    by g(x).

    """
    def eval(self, e):
        steps = []
        e_body = e.body
        if e_body.ty == OP and e_body.op == "/" or e_body.ty == OP and e_body.op == "*" and \
            e_body.args[1].ty == OP and e_body.args[1].op == "^" and e_body.args[1].args[1].ty == CONST\
                and e_body.args[1].args[1].val < 0: # e_body is fraction
            if e_body.ty == OP and e_body.op == "/":
                denom = e_body.args[1]
            else:
                denom = e_body.args[1].args[0]
            try:
                new_e_1 = rules.PolynomialDivision().eval(e)
                rhs = new_e_1.body
                new_e_2 = Linearity().eval(new_e_1)
                new_e_2.steps = steps + [calc.PolynomialDivisionStep(e=new_e_1, denom=denom, rhs=rhs),
                                         calc.LinearityStep(new_e_2)]
                
                return new_e_2
            except:
                e.steps = []
                return e
        else:
            e.steps = []
            return e

class Linearity(AlgorithmRule):
    """Algorithm rule (a),(b),(c) in Slagle's thesis.

    (a) Factor constant. ∫cg(v)dv = c∫g(v)dv  
    (b) Negate. ∫-g(v)dv = -∫g(v)dv
    (c) Decompose. ∫∑g(v)dv = ∑∫g(v)dv 
    
    """
    def eval(self, e):
        steps = []
        new_e = rules.Linearity().eval(e, single=True)
        if new_e != e:
            steps.append(calc.LinearityStep(new_e))
            new_e.steps = steps
            return new_e
        else:
            e.steps = steps
            return e
                

class LinearSubstitution(AlgorithmRule):
    """Algorithm rule (d) in Slagle's thesis.

    Find linear expression in integral's sub functions. 
    If there is only one function and its body is linear,
    try to substitute the original variable by the function 
    linear body.
    """
    def eval(self, e):
        integrals = e.separate_integral()
        steps = []
        for i, loc in integrals:
            new_e_i = linear_substitution(i)
            e = e.replace_trig(i, new_e_i)
            steps += new_e_i.steps 
        e.steps = steps
        return e

class HalfAngleIdentity(AlgorithmRule):
    """Algorithm rule (h) in Slagle's thesis.

    Take following identity:
    a) sin(v)cos(v) = 1/2 * sin(2v)
    b) cos^2(v) = 1/2 + 1/2 * cos(2v)
    c) sin^2(v) = 1/2 - 1/2 * cos(2v)
    
    """
    def eval(self, e):
        x = Symbol('x', [CONST, VAR, OP, FUN])
        y = Symbol('y', [CONST, VAR, OP, FUN])
        pat1 = sin(x) * cos(x)
        pat2 = cos(x) * sin(x)
        pat3 = sin(x) ^ Const(2)
        pat4 = cos(x) ^ Const(2)
        pat5 = y * sin(x) * cos(x)
        pat6 = y * cos(x) * sin(x)

        sin_cos_expr = find_pattern(e, pat1, loc=True)
        cos_sin_expr = find_pattern(e, pat2, loc=True)
        sin_power_expr = find_pattern(e, pat3, loc=True)
        cos_power_expr = find_pattern(e, pat4, loc=True)
        y_sin_cos_expr = find_pattern(e, pat5, loc=True)
        y_cos_sin_expr = find_pattern(e, pat6, loc=True)


        half = Const(Fraction(1, 2))

        for t, loc in sin_cos_expr:
            e = e.replace_trig(t, half * sin(Const(2) * t.args[0].args[0]))

        for t, loc in cos_sin_expr:
            e = e.replace_trig(t, half * sin(Const(2) * t.args[0].args[0]))

        for t, loc in sin_power_expr:
            e = e.replace_trig(t, half + half * cos(Const(2) * t.args[0].args[0]))

        for t, loc in cos_power_expr:
            e = e.replace_trig(t, half - half * cos(Const(2) * t.args[0].args[0]))
        
        for t, loc in y_sin_cos_expr:
            e = e.replace_trig(t, half * t.args[0].args[0] * sin(Const(2) * t.args[1].args[0]))

        for t, loc in y_cos_sin_expr:
            e = e.replace_trig(t, half * t.args[0].args[0] * sin(Const(2) * t.args[1].args[0]))

        e.steps = []
        return e

algorithm_rules = [
    DividePolynomial,
    HalfAngleIdentity,
    Linearity,
    LinearSubstitution,
    CommonIntegral,
]

class TrigFunction(HeuristicRule):
    """Heuristic rule (a) in Slagle's thesis.
    
    There are three options:
    1) Transform to sine and cosine.
    2) Transform to tangent and secant.
    3) Transform to cotangent and cosecant.

    """

    def sin_cos(self, e):
        """1) Transform to sine and cosine.

        a) tan(x) => sin(x)/cos(x)
        b) cot(x) => cos(x)/sin(x)
        c) sec(x) => 1/cos(x)
        d) csc(x) => 1/sin(x)

        TR1, TR2
        
        """
        x = Symbol('x', [OP,CONST,VAR,FUN])
        tan_pat = tan(x)
        cot_pat = cot(x)
        sec_pat = sec(x)
        csc_pat = csc(x)

        tan_expr = find_pattern(e, tan_pat, loc=True)
        cot_expr = find_pattern(e, cot_pat, loc=True)
        sec_expr = find_pattern(e, sec_pat, loc=True)
        csc_expr = find_pattern(e, csc_pat, loc=True)

        steps = []

        reason = "sine cosine"

        for t, loc in tan_expr:
            e = e.replace_trig(t, sin(t.args[0])/cos(t.args[0]))
            steps.append(calc.TrigSubstitutionStep(e, loc, t, sin(t.args[0])/cos(t.args[0]), reason))          

        for t, loc in cot_expr:
            e = e.replace_trig(t, cos(t.args[0])/sin(t.args[0]))
            steps.append(calc.TrigSubstitutionStep(e, loc, t, cos(t.args[0])/sin(t.args[0]), reason))  

        for t, loc in sec_expr:
            e = e.replace_trig(t, Const(1)/cos(t.args[0]))
            steps.append(calc.TrigSubstitutionStep(e, loc, t, Const(1)/cos(t.args[0]), reason))

        for t, loc in csc_expr:
            e = e.replace_trig(t, Const(1)/sin(t.args[0]))
            steps.append(calc.TrigSubstitutionStep(e, loc, t, Const(1)/sin(t.args[0]), reason))

        e.steps = steps
        return e

    def tan_sec(self, e):
        """1) Transform to tangent and secant.

        a) sin(x) => tan(x)/sec(x)
        b) cos(x) => 1/sec(x)
        c) cot(x) => 1/tan(x)
        d) csc(x) => sec(x)/tan(x)
        
        """
        # e_body = e.body
        # lower = e.lower
        # upper = e.upper

        x = Symbol('x', [OP,CONST,VAR,FUN])
        sin_pat = sin(x)
        cos_pat = cos(x)
        cot_pat = cot(x)
        csc_pat = csc(x)

        sin_expr = find_pattern(e, sin_pat, loc=True)
        cos_expr = find_pattern(e, cos_pat, loc=True)
        cot_expr = find_pattern(e, cot_pat, loc=True)
        csc_expr = find_pattern(e, csc_pat, loc=True)

        steps = []

        reason = "tangent secant"

        for t, loc in sin_expr:
            e = e.replace_trig(t, tan(t.args[0])/sec(t.args[0]))
            steps.append(calc.TrigSubstitutionStep(e, loc, t, tan(t.args[0])/sec(t.args[0]), reason))

        for t, loc in cos_expr:
            e = e.replace_trig(t, Const(1)/sec(t.args[0]))
            steps.append(calc.TrigSubstitutionStep(e, loc, t, Const(1)/sec(t.args[0]), reason))

        for t, loc in cot_expr:
            e = e.replace_trig(t, Const(1)/tan(t.args[0]))
            steps.append(calc.TrigSubstitutionStep(e, loc, t, Const(1)/tan(t.args[0]), reason))

        for t, loc in csc_expr:
            e = e.replace_trig(t, sec(t.args[0])/tan(t.args[0]))
            steps.append(calc.TrigSubstitutionStep(e, loc, t, sec(t.args[0])/tan(t.args[0]), reason))

        e.steps = steps
        return e

    def cot_csc(self, e):
        """3) Transform to cotangent and cosecant.
        
        a) sin(x) => 1/csc(x)
        b) cos(x) => cot(x)/csc(x)
        c) tan(x) => 1/cot(x)
        d) sec(x) => csc(x)/cot(x)
        """
        x = Symbol('x', [OP,CONST,VAR,FUN])
        sin_pat = sin(x)
        cos_pat = cos(x)
        tan_pat = tan(x)
        sec_pat = sec(x)

        sin_expr = find_pattern(e, sin_pat, loc=True)
        cos_expr = find_pattern(e, cos_pat, loc=True)
        tan_expr = find_pattern(e, tan_pat, loc=True)
        sec_expr = find_pattern(e, sec_pat, loc=True)

        steps = []
        reason = "cotangent cosecant"
        for t, loc in sin_expr:
            e = e.replace_trig(t, Const(1)/csc(t.args[0]))
            steps.append(calc.TrigSubstitutionStep(e, loc, t, Const(1)/csc(t.args[0]), reason))

        for t, loc in cos_expr:
            e = e.replace_trig(t, cot(t.args[0])/csc(t.args[0]))
            steps.append(calc.TrigSubstitutionStep(e, loc, t, cot(t.args[0])/csc(t.args[0]), reason))

        for t, loc in tan_expr:
            e = e.replace_trig(t, Const(1)/cot(t.args[0]))
            steps.append(calc.TrigSubstitutionStep(e, loc, t, Const(1)/cot(t.args[0]), reason))

        for t, loc in sec_expr:
            e = e.replace_trig(t, csc(t.args[0])/cot(t.args[0]))
            steps.append(calc.TrigSubstitutionStep(e, loc, t, csc(t.args[0])/cot(t.args[0]), reason))

        e.steps = steps
        return e

    def eval(self, e, loc=[]):
        initial_step = calc.SimplifyStep(e)
        
        res = []

        if self.sin_cos(e) != e:
            tmp = self.sin_cos(e)
            tmp = add_simplify_step(tmp, loc)
            res.append(tmp)

        if self.tan_sec(e) != e:
            tmp = self.tan_sec(e)
            tmp = add_simplify_step(tmp, loc)
            res.append(tmp)

        if self.cot_csc(e) != e:
            tmp = self.cot_csc(e)
            tmp = add_simplify_step(tmp, loc)
            res.append(tmp)
 
        return res

class HeuristicTrigonometricSubstitution(HeuristicRule):
    """Heuristic rule (b) in Slagle's thesis.(elf means "elementary function")

    The substitution rules:
    1) elf{sin(v),cos^2(v)}cos^{2n+1}(v) ==> u = sin(v);
    2) elf{cos(v),sin^2(v)}sin^{2n+1}(v) ==> u = cos(v);
    3) elf{tan(v),sec^2(v)}              ==> u = tan(v);
    4) elf{cot(v),csc^2(v)}              ==> u = cot(v);
    5) elf{sec(v),tan^2(v)}tan^{2n+1}(v) ==> u = sec(v);
    6) elf{csc(v),cot^2(v)}              ==> u = csc(v);
    """
    def eval(self, e, loc=[]):

        def is_pat1(e):
            """elf{sin(v),cos^2(v)}cos^{2n+1}(v)"""
            v = Symbol('v', [VAR, OP, FUN])
            n = Symbol('n', [CONST])
            pat1 = (cos(v)^n) * sin(v)
            pat2 = cos(v) * sin(v)
            pat3 = cos(v)^n
            if match(e, pat1):
                n_value = e.args[0].args[1].val
                return True, e.args[1].args[0] if n_value % 2 == 1 else (False, None)
            elif match(e, pat3):
                n_value = e.args[1].val
                return True, e.args[0].args[0] if n_value % 2 == 1 else (False, None)
            elif match(e, pat2):
                return True, e.args[0].args[0]
            else:
                return False, None

        def is_pat2(e):
            """elf{cos(v),sin^2(v)}sin^{2n+1}(v)"""
            v = Symbol('v', [VAR, OP, FUN])
            n = Symbol('n', [CONST])
            pat1 = cos(v) * (sin(v)^n)
            pat2 = cos(v) * sin(v)
            pat3 = sin(v)^n
            if match(e, pat1):
                n_value = e.args[1].args[1].val
                return True, e.args[0].args[0] if n_value % 2 == 1 else (False, None)
            elif match(e, pat3):
                n_value = e.args[1].val
                return True, e.args[0].args[0] if n_value % 2 == 1 else (False, None)
            elif match(e, pat2):
                return True, e.args[0].args[0]
            else:
                return False, None

        def is_pat3(e):
            """elf{tan(v),sec^2(v)}"""
            v = Symbol('v', [VAR, OP, FUN])
            pat1 = tan(v)
            pat2 = sec(v)^Const(2)
            if match(e, pat1):
                return True, e.args[0]
            elif match(e, pat2):
                return True, e.args[0].args[0]
            else:
                return False, None

        def is_pat4(e):
            """elf{cot(v),csc^2(v)}"""
            v = Symbol('v', [VAR, OP, FUN])
            pat1 = cot(v)
            pat2 = csc(v)^Const(2)
            if match(e, pat1):
                return True, e.args[0]
            elif match(e, pat2):
                return True, e.args[0].args[0]
            else:
                return False, None
        
        def is_pat5(e):
            """elf{sec(v),tan^2(v)}tan^{2n+1}(v)"""
            v = Symbol('v', [VAR, OP, FUN])
            n = Symbol('n', [CONST])
            pat1 = sec(v) * (tan(v)^n)
            pat2 = sec(v) * tan(v)
            pat3 = tan(v)^n
            if match(e, pat1):
                n_value = e.args[1].args[1].val
                return (True, e.args[0].args[0]) if n_value % 2 == 1 else (False, None)
            elif match(e, pat3):
                n_value = e.args[1].val
                return (True, e.args[0].args[0]) if n_value % 2 == 1 else (False, None)
            elif match(e, pat2):
                return True, e.args[0].args[0]
            else:
                return False, None

        def is_pat6(e):
            """elf{csc(v),cot^2(v)}"""
            v = Symbol('v', [VAR, OP, FUN])
            pat1 = csc(v)
            pat2 = cot(v)^Const(2)
            if match(e, pat1):
                return True, e.args[0]
            elif match(e, pat2):
                return True, e.args[0].args[0]
            else:
                return False, None

        initial_step = [calc.SimplifyStep(e)]

        e_body = e.body
        new_var = gen_rand_letter(e.var)
            
        if is_pat1(e_body)[0]:
            """Substitute sin(v) by u."""
            _, b = is_pat1(e_body)
            integ, f = rules.Substitution1(new_var, sin(b)).eval(e)
            integ.steps = initial_step + [calc.SubstitutionStep(integ, new_var, sin(b), f, loc)]
            integ = add_simplify_step(integ, loc)
            return [integ]
        elif is_pat2(e_body)[0]:
            """Substitute cos(v) by u."""
            _, b = is_pat2(e_body)
            integ, f = rules.Substitution1(new_var, cos(b)).eval(e)
            integ.steps = initial_step + [calc.SubstitutionStep(integ, new_var, cos(b), f, loc)]
            integ = add_simplify_step(integ, loc)
            return [integ]
        elif is_pat3(e_body)[0]:
            """Substitute tan(v) by u."""
            _, b = is_pat3(e_body)
            integ, f = rules.Substitution1(new_var, tan(b)).eval(e)
            integ.steps = initial_step + [calc.SubstitutionStep(integ, new_var, tan(b), f, loc)]
            integ = add_simplify_step(integ, loc)
            return [integ]
        elif is_pat4(e_body)[0]:
            """Substitute cot(v) by u."""
            _, b = is_pat4(e_body)
            integ, f = rules.Substitution1(new_var, cot(b)).eval(e)
            integ.steps = initial_step + [calc.SubstitutionStep(integ, new_var, cot(b), f, loc)]
            integ = add_simplify_step(integ, loc)
            return [integ]
        elif is_pat5(e_body)[0]:
            """Substitute sec(v) by u."""
            _, b = is_pat5(e_body)
            integ, f = rules.Substitution1(new_var, sec(b)).eval(e)
            integ.steps = initial_step + [calc.SubstitutionStep(integ, new_var, sec(b), f, loc)]
            integ = add_simplify_step(integ, loc)
            return [integ]
        elif is_pat6(e_body)[0]:
            """Substitute csc(v) by u."""
            _, b = is_pat6(e_body)
            integ, f = rules.Substitution1(new_var, csc(b)).eval(e)
            integ.steps = initial_step + [calc.SubstitutionStep(integ, new_var, csc(b), f, loc)]
            integ = add_simplify_step(integ, loc)
            return [integ]
        else:
            e.steps = []
            return [e]

class HeuristicSubstitution(HeuristicRule):
    """Heuristic rule (c) in Slagle's thesis.

    Currently we implement a naive strategy of substitution for
    y subterm corresponds to lowest depth expression after substitution.  


    It can't return correct result when body is not monotonic in the given range.
    """
    def eval(self, e, loc=[]):
        res = []
        initial_step = [calc.SimplifyStep(e, loc=loc)]
        all_subterms = e.body.nonlinear_subexpr()

        depth = 0
        for subexpr in all_subterms:
            try:    
                r, f = rules.Substitution1(gen_rand_letter(e.var), subexpr).eval(e)
                r.steps = initial_step + [calc.SubstitutionStep(r, r.var, subexpr, f, loc)]
                r = add_simplify_step(r, loc)
                res.append(r)
            except:
                continue

        if res: # res is not empty
            res = [r for r in res if r != Const(0)] # May have bug when result is 0.
            res = sorted(res, key=lambda x:x.depth)
            return [res[0]] if res != [] else [] 

        else:
            return []

class HeuristicIntegrationByParts(HeuristicRule):
    """Heuristic rule (d) in Slagle's thesis.
    
    Find each factor h in the integral production, try find ∫hdv = H.
    And do integration by parts: ∫Gh dv = GH - ∫(dG/dv)H dv.

    Currently we implemented a naive strategy to find h: the ∫hdv can be
    solved by CommonIntegral rule after algorithm transformation.
    
    """
    def eval(self, e, loc=[]):
        if not isinstance(e, Integral):
            return e

        initial_step = [calc.SimplifyStep(e, loc=loc)]
        res = []
        
        factors = decompose_expr_factor(e.body)
        
        if len(factors) <= 1:
            return []
        
        for i in range(len(factors)):
            h = factors[i]
            rest_factor = [f for f in factors if f != h]
            G = functools.reduce(operator.mul, rest_factor)
            H = rules.CommonIntegral().eval(Integral(e.var, e.lower, e.upper, h))
            if H.body != h or h == exp(Var(e.var)):
                u = G
                v = H.body
                try: # can't deriv abs now
                    new_integral = rules.IntegrationByParts(u, v).eval(e)
                except:
                    continue
                new_integral.steps = [calc.IntegrationByPartsStep(new_integral, u, v, loc)]
                new_integral = add_simplify_step(new_integral, loc)
                res.append(new_integral)
        
        return res

class HeuristicElimQuadratic(HeuristicRule):
    """Heuristic rule (e) in Slagle's thesis.

    For quadratic subexpressions like a + b * x + c * x ^ 2,
    substitute x by y + b/2c, transform to a - b^2/4a + ay^2.
    
    The search for quadratic subexprs is not complete because of
    the non-standard normalization.

    """
    def eval(self, e, loc=[]):
        def find_abc(quad):
            """Find the value of a, b, c in a + b * x + c * x ^ 2."""
            quad = quad.normalize()
            if not (quad.args[0].ty == OP and quad.args[0].op in ("+","-")): # b*x +/- a*x^2
                if quad.args[0].ty == VAR: # x +/- a*x^2 
                    if quad.args[1].ty == OP and quad.args[1].op == "^": # x +/- x^2
                        return (Const(0), Const(1), Const(1)) if quad.op == "+" else (Const(0), Const(1), Const(-1))
                    else: # x +/- a * x^2
                        return (Const(0), Const(1), quad.args[1].args[0]) if quad.op == "+" else (Const(0), Const(1), -quad.args[1].args[0])
                else: # b*x + a*x^2
                    if quad.args[1].ty == OP and quad.args[1].op == "^": # b*x +/- x^2
                        return (Const(0), quad.args[0].args[0], Const(1)) if quad.op == "+" else (Const(0), quad.args[0].args[0], Const(-1))
                    else: # b* x +/- a * x^2
                        return (Const(0), quad.args[0].args[0], quad.args[1].args[0]) if quad.op == "+" else (Const(0), quad.args[0].args[0], -quad.args[1].args[0])
            else: # c +/- b*x +/- a * x ^ 2
                if quad.args[0].args[1].ty == VAR: # c +/- x +/- x^2
                    if quad.args[1].args[1] == Const(2): # c +/- x +/- x^2
                        return check(quad, (quad.args[0].args[0], Const(1), Const(1)))
                    else:# c + x + a*x^2
                        return check(quad, (quad.args[0].args[0], Const(1), quad.args[1].args[0])) 
                else:# c +/- b*x +/- a * x^2
                    if quad.args[1].args[1] == Const(2): # c +/- b*x +/- x^2
                        return check(quad, (quad.args[0].args[0], quad.args[0].args[1].args[0], Const(1))) 
                    else:
                        return check(quad, (quad.args[0].args[0], quad.args[0].args[1].args[0], quad.args[1].args[0]))

        def check(quad, t):
            """Input: quad is a expression in a +/- b * x +/- c * x ^ 2 form, 
                      t is (a, b, c) tuple
            
               Output: the quadratic expression's coefficient.
            """
            symbol = [quad.op, quad.args[0].op]
            if symbol == ["+", "+"]:
                return (t[0], t[1], t[2])
            elif symbol == ["-", "+"]:
                return (t[0], t[1], Op("-",t[2]).normalize())
            elif symbol == ["+", "-"]:
                return (t[0], Op("-",t[1]).normalize(), t[2])
            elif symbol == ["-", "-"]:
                return (t[0], Op("-",t[1]).normalize(), Op("-",t[2]).normalize())
            else:
                raise NotImplementedError

        initial_step = [calc.SimplifyStep(e, loc=loc)]

        x = Symbol('x', [VAR, FUN])
        a = Symbol('a', [CONST])
        b = Symbol('b', [CONST])
        c = Symbol('c', [CONST])
        steps = []
        quadratic_patterns = [
            x + (x^Const(2)),
            x + a * (x^Const(2)),
            b * x + a * (x^Const(2)),
            c + x + (x^Const(2)),
            c + x + a * (x^Const(2)),
            c + b * x + (x^Const(2)),
            c + b * x + a*(x^Const(2)),
            c + (x ^ Const(2))
        ]
        
        quadratic_terms = []
        for p in quadratic_patterns:
            quad = find_pattern(e.body, p, True)
            if quad:
                quadratic_terms.append(quad)

        if not quadratic_terms:
            return []

        quadratics = [l for r in quadratic_terms for l in r]
        res = []

        for quad, l in quadratics:
            a, b, c = find_abc(quad)
            new_integral, f = rules.Substitution1(gen_rand_letter(e.var), Var(e.var) + (b/(Const(2)*c))).eval(e)

            steps.append(calc.SubstitutionStep(new_integral, new_integral.var, Var(e.var) + (b/(Const(2)*c)), f, loc + [0] + l))
            new_integral = HeuristicExpandPower().eval(new_integral)[0]
            steps += new_integral.steps
            steps.append(calc.SimplifyStep(new_integral))
            new_integral.steps = steps
            new_integral = add_simplify_step(new_integral)
            res.append(new_integral)

        return res

class HeuristicTrigSubstitution(HeuristicRule):
    """Heuristic rule (g) in Slagle's thesis.
    
    Find subexpressions in form: a + b * x^2.
    There are 3 cases:
    (1) a > 0, b > 0, substitute x by sqrt(a/b)*tan(u);
    (2) a > 0, b < 0, substitute x by sqrt(a/-b)*sin(u);
    (1) a < 0, b > 0, substitute x by sqrt(-a/b)*sec(u);

    """

    def eval(self, e, loc=None):
        def find_ab(p):
            """Find a, b in a + b*x^2"""
            p = p.normalize()
            if p.args[1].args[1] == Const(2): # a + x ^ 2
                return (p.args[0], Const(1))
            else: # a + b*x^2
                return (p.args[0], p.args[1].args[0])

        initial_step = [calc.SimplifyStep(e, loc=loc)]

        a = Symbol('a', [CONST])
        b = Symbol('b', [CONST])
        x = Symbol('x', [VAR])

        pats = [
            a + (x ^ Const(2)),
            a + b * (x ^ Const(2)),
        ]

        all_subterms = []
        for p in pats:
            all_subterms.append(find_pattern(e.body, p, loc=True))

        if not all_subterms:
            return []
        all_subterms = [p for l in all_subterms for p in l]        
        res = []

        for s, loc in all_subterms:
            a, b = find_ab(s)
            assert not a.val < 0 or not b.val < 0, "Invalid value: a=%s, b=%s" % (a.val, b.val)
            if a.val > 0 and b.val > 0:
                subst = Op("^", Const(Fraction(a.val, b.val)), Const(Fraction(1,2))).normalize()*tan(Var("u"))
                
            elif a.val > 0 and b.val < 0:
                subst = Op("^", Const(Fraction(a.val, -b.val)), Const(Fraction(1,2))).normalize() * sin(Var("u"))
            
            elif a.val < 0 and b.val > 0:
                subst = Op("^", Const(Fraction(-a.val, b.val)), Const(Fraction(1,2))).normalize() * sec(Var("u"))

            new_integral = rules.Substitution2("u", subst).eval(e)
            new_integral.steps = [calc.SubstitutionInverseStep(new_integral, "u", subst)]
            res.append(new_integral)

        return res

class HeuristicExpandPower(HeuristicRule):
    """Heuristic rule (g) in Slagle's thesis.

    Expansion of positive integer powers of nonconstant sums.
    
    """
    def eval(self, e, loc=[]):
        initial_step = [calc.SimplifyStep(e, loc=loc)]
        steps = []

        a = Symbol('a', [CONST])
        c = Symbol('c', [OP])
        pat = c ^ a
        subexpr = find_pattern(e, pat, loc=True)

        expand_expr = e
        for s, l in subexpr:
            base = s.args[0].to_poly()
            exp = s.args[1].val
            if isinstance(exp, int) and exp > 1:
                pw = base
                for i in range(exp-1):
                    pw = pw * base
                expand_expr = expand_expr.replace_expr(l, from_poly(pw))
                steps.append(calc.UnfoldPowerStep(expand_expr, loc+l))

        expand_expr.steps = initial_step + steps
        expand_expr = add_simplify_step(expand_expr, loc)
        return [expand_expr]

class HeuristicExponentBase(HeuristicRule):
    """Heuristic rule(i) in Slgle's thesis.

    If the integrand has a list of subexpression like [b^{mv}, b^{nv}, ...],
    the base b is an exponent function, n is integer and v is var.
    Try to find the great divisor of m, n... assume it is k.
    Then try substitution: u = b^{kv}. 

    """
    def eval(self, e, loc=[]):
        n = Symbol('n', [CONST])
        x = Symbol('x', [VAR])

        initial_step = [calc.SimplifyStep(e, loc=loc)]

        pat = exp(n*x)
        exponents = find_pattern(e.body, pat)

        if len(exponents) <= 1:
            return []

        coeffs = []
        for exponent in exponents:
            if exponent.args[0].ty == CONST:
                coeffs.append(1)
            else:
                coeffs.append(exponent.args[0].args[0].val)

        if not any(isinstance(n, int) for n in coeffs):
            return []


        gcd = functools.reduce(math.gcd, coeffs)
        new_integral, f = rules.Substitution1("u", exp(Const(gcd)*Var(e.var))).eval(e)

        new_integral.steps = [calc.SubstitutionStep(new_integral, "u", exp(Const(gcd)*Var(e.var)), f, loc)]
        new_integral = add_simplify_step(new_integral, loc)
        return [new_integral]

class HeuristicRationalSineCosine(HeuristicRule):
    """
    When the integrand is a rational function of sines and cosines,
    try substituting u=tan(v/2) 
    """
    def eval(self, e):
        e_body = e.body
        if e_body.is_spec_function("sin"):
            """
            Repalce sin(v) by 2*u/(1+u^2) 
            """
            v = Symbol("v", [VAR,OP,FUN])
            pat1 = sin(v)
            s = find_pattern(e_body, pat1)
            new_e_body = e_body.replace_trig(s, parse_expr('2*u/(1+u^2)')) * parse_expr('2/(1+u^2)')
            lower = tan(e.lower/2)
            upper = tan(e.upper/2)
            return [Integral("u", lower, upper, new_e_body)]
            
        elif e.is_spec_function("cos"):
            """
            Repalce cos(v) by (1-u^2)/(1+u^2) 
            """
            v = Symbol("v", [VAR,OP,FUN])
            pat1 = sin(v)
            s = find_pattern(e_body, pat1)
            new_e_body = e_body.replace_trig(s, parse_expr('(1-u^2)/(1+u^2)')) * parse_expr('2/(1+u^2)')
            lower = tan(e.lower/2)
            upper = tan(e.upper/2)
            return Integral("u", lower, upper, new_e_body)
        else:
            return [e]


heuristic_rules = [
    TrigFunction,
    HeuristicTrigonometricSubstitution,
    HeuristicSubstitution,
    HeuristicIntegrationByParts,
    HeuristicElimQuadratic,
    HeuristicExpandPower,
    HeuristicTrigSubstitution,
    HeuristicExponentBase,
]


class GoalNode:
    def trace(self):
        '''Give computation trace for resolved integration.'''
        assert self.resolved == True, '%s haven\'t been solved' % self.root
        
        if hasattr(self.root, 'steps'):
            t = self.root.steps if self.root.steps is not None else []
        else:
            t = []
        
        if isinstance(self, OrNode):
            for c in self.children:
                if c.resolved == True:
                    return t + c.trace()
        
        else:
            for c in self.children:
                t += c.trace()
            return t


class OrNode(GoalNode):
    """OR relationship in Slagle's thesis.
    
    To evaluate the integral at the root, only need to evaluate one of the
    child nodes. Each of the child nodes is a GoalNode.

    """
    def __init__(self, root, loc=[], parent=None):
        if isinstance(root, str):
            root = parse_expr(root)

        self.root = root
        self.parent = parent
        self.children = []
        self.resolved = False
        self.loc = loc
        self.root.loc = self.loc

    def __str__(self):
        if len(self.children) == 0:
            return 'OrNode(%s,%s,[])' % (str(self.root), str(self.resolved))

        s = 'OrNode(%s,%s,[\n' % (str(self.root), str(self.resolved))
        for c in self.children:
            str_c = str(c)
            for line in str_c.splitlines():
                s += '   %s\n' % line
        s += ']'
        return s

    def expand(self, not_solved_integral):
        """Expand the current node.

        This tries all algorithm rules. If the result is itself an integral, then
        apply each of the heuristic rules and collect the results. If the
        result is a linear combination of integrals, then put a single AndNode
        as the child nodes.

        If we get a new integral after transformation, we need to store them in a set, 
        in case of repeatedly try to solve same integral(Trigonometric functions can 
        transform to them self). 

        """
        cur_integral = self.root
        old_cur_integral = cur_integral
        
        not_solved_integral.add(cur_integral)
        for rule in algorithm_rules:
            cur_integral = rule().eval(cur_integral)
            steps = cur_integral.steps
            cur_integral = cur_integral.normalize()
            cur_integral.steps = steps

        if cur_integral.ty == INTEGRAL:
            # Single integral case
            for rule in heuristic_rules:
                res = rule().eval(cur_integral)
                for r in res:
                    steps = r.steps
                    r = r.normalize()
                    r.steps = steps
                    if r == cur_integral:
                        continue
                    if r.ty == INTEGRAL and r not in not_solved_integral:
                        self.children.append(OrNode(r, r.steps[-1].loc, parent=self))
                    elif r not in not_solved_integral:
                        self.children.append(AndNode(r, r.steps[-1].loc, parent=self))
        
        else:
            # Linear combination of integrals
            not_solved_integral.remove(old_cur_integral)
            self.children.append(AndNode(cur_integral, self.loc, parent=self))

        self.compute_resolved()

    def compute_resolved(self):
        self.resolved = any(c.resolved for c in self.children)
        if self.resolved and self.parent is not None:
            self.parent.compute_resolved()

    def compute_value(self):
        if not self.resolved or len(self.children) == 0:
            return self.root
        else:
            for c in self.children:
                if c.resolved:
                    return c.compute_value()

class AndNode(GoalNode):
    """AND relationship in Slagle's thesis.

    To evaluate the integral at the root, need to evaluate all of the child
    nodes. In our case, the root is necessarily a sum (or difference) of
    integrals, and the child nodes are the individual integrals.

    """
    def __init__(self, root, loc, parent=None):
        if isinstance(root, str):
            root = parse_expr(root)

        self.root = root
        self.parent = parent
        self.loc = loc
        self.root.loc = loc
        self.children = [OrNode(r, self.loc+list(Location(l).data), parent=self) for r, l in root.separate_integral()]
        self.resolved = (len(self.children) == 0)
        if self.resolved:
            self.parent.compute_resolved()

    def __str__(self):
        if len(self.children) == 0:
            return 'AndNode(%s,%s,[])' % (str(self.root), str(self.resolved))

        s = 'AndNode(%s,%s,[\n' % (str(self.root), str(self.resolved))
        for c in self.children:
            str_c = str(c)
            for line in str_c.splitlines():
                s += '   %s\n' % line
        s += ']'
        return s

    def compute_resolved(self):
        self.resolved = all(c.resolved for c in self.children)
        if self.resolved and self.parent is not None:
            self.parent.compute_resolved()

    def compute_value(self):
        value = self.root
        if not self.resolved:
            return self.root
        if len(self.children) == 0:
            return self.root.normalize()
        else:
            for c in self.children:
                value = value.replace_trig(c.root, c.compute_value())
                
            return value.normalize()


def bfs(node):
    q = collections.deque()
    not_solved_integral = set()
    q.append(node)
    while q and not node.resolved:
        n = q.popleft()
        if isinstance(n, OrNode):
            n.expand(not_solved_integral)
        
        n.children = sorted(n.children, key=lambda x:x.root.depth)
        for c in n.children:
            q.append(c)

    return node

def timeout(max_timeout):
    """Timeout decorator, parameter in seconds."""
    def timeout_decorator(item):
        """Wrap the original function."""
        @functools.wraps(item)
        def func_wrapper(*args, **kwargs):
            """Closure for function."""
            pool = multiprocessing.pool.ThreadPool(processes=1)
            async_result = pool.apply_async(item, args, kwargs)
            # raises a TimeoutError if execution exceeds max_timeout
            res = async_result.get(max_timeout)
            pool.close()
            return res
        return func_wrapper
    return timeout_decorator


