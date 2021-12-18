import random, string
import collections
import heapq
import functools
import operator
from integral.expr import *
from integral.parser import parse_expr
from integral import rules
from integral import calc
from integral import latex
import math
import multiprocessing.pool
import json
from sympy.solvers import solveset
from sympy import Interval

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
    return "u" if ex != "u" else "v"

def has_fun(e):
    """Return true if e has function."""
    if e.ty in (CONST, VAR):
        return False
    elif e.ty == OP:
        return any(has_fun(arg) for arg in e.args)
    elif e.ty == FUN and e.func_name != "sqrt":
        return True
    else:
        return False

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

class FullSimplify(AlgorithmRule):
    """
    Compose Linearity, CommonIntegral and Simplify.
    """
    def eval(self, e, loc=[]):
        s = rules.FullSimplify().eval(e)
        if s == e:
            return e, None
        else:
            return s, [calc.SimplifyStep(s, loc)]

class CommonIntegral(AlgorithmRule):
    """Evaluate common integrals."""

    def eval(self, e):
        new_e = rules.OnSubterm(rules.CommonIntegral()).eval(e)
        steps = []
        if new_e != e:
            steps.append(calc.CommonIntegralStep(new_e))
        return new_e, steps


class DividePolynomial(AlgorithmRule):
    """Algorithm rule (g) in Slagle's thesis.

    If the integral is in the form f(x)/g(x), attempt to divide f(x)
    by g(x).

    """
    def eval(self, e):
        if e.ty != INTEGRAL:
            return e, None
        e_body = e.body

        a = Symbol("a", [CONST, VAR, OP])
        b = Symbol("b", [CONST, VAR, OP])
        c = Symbol("c", [CONST])
        pat1 = a / b
        pat2 = a * (b ^ c)

        if not match(e_body, pat1) and not match(e_body, pat2):
            return e, None
        
        mapping2 = match(e_body, pat2)
        if mapping2 is not None:
            c_value = mapping2[c].val
            if c_value > 0 or not isinstance(c_value, int):
                return e, None

        if e_body.ty == OP and e_body.op == "/":
            denom = e_body.args[1]
        else:
            denom = e_body.args[1].args[0]
        try:
            divide_expr = rules.PolynomialDivision().eval(e_body)
            new_integral = Integral(e.var, e.lower, e.upper, divide_expr)
            step = calc.PolynomialDivisionStep(new_integral, denom, divide_expr, Location([0]))
            return new_integral, [step]
        except NotImplementedError:
            return e, None


class Linearity(AlgorithmRule):
    """Algorithm rule (a),(b),(c) in Slagle's thesis.

    (a) Factor constant. ∫cg(v)dv = c∫g(v)dv  
    (b) Negate. ∫-g(v)dv = -∫g(v)dv
    (c) Decompose. ∫∑g(v)dv = ∑∫g(v)dv 
    
    """
    def eval(self, e):
        new_e = rules.Linearity().eval(e)
        if new_e != e:
            steps = [calc.LinearityStep(new_e)]
            return new_e, steps
        else:
            return e, None

class AlgoNonLinearSubstitution(AlgorithmRule):
    """
    When there are log and exponential expresion in integral, use this rule.
    """
    def eval(self, e):
        if not (e.body.ty == OP and (e.body.op == "/" or e.body.op == "*" 
                and e.body.args[1].ty == OP and e.body.args[1].op == "^" and 
                e.body.args[1].args[1].ty == CONST and e.body.args[1].args[1].val <= -1 )):
            return e, None
        if not has_fun(e.body):
            return e, None
        heur_e = HeuristicSubstitution().eval(e)
        if not heur_e:
            return e, None
        heur_e, step = heur_e[0]
        if heur_e.depth < e.depth:
            return heur_e, step
        else:
            return e, None
        # return e, None

def substitution(integral, subst):
    new_var = gen_rand_letter(integral.var)
    rule = rules.Substitution1(new_var, subst)
    new_e = rule.eval(integral)
    steps = [calc.SubstitutionStep(e=new_e, var_name=new_var, var_subst=subst, f=rule.f, loc=[])]
    return new_e, steps

def linear_substitution(integral):
    assert isinstance(integral, Integral), "%s Should be an integral." % (integral)
    func_body = collect_spec_expr(integral.body, Symbol('f', [FUN]))

    if len(func_body) == 1 and any([match(func_body[0], p) for p in linear_pat]): 
        return substitution(integral, func_body[0])

    elif len(func_body) == 0:
        power_body = collect_spec_expr(integral.body, pat3)
        if len(power_body) == 0:
            return integral, None
        is_linear = functools.reduce(lambda x,y:x or y, [match(power_body[0], pat) for pat in linear_pat])
        if len(power_body) == 1 and is_linear:
            return substitution(integral, power_body[0])
        else:
            return integral, None

    else:
        return integral, None

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
            new_e_i, step = linear_substitution(i)
            if step is None:
                continue
            step[0].prepend_loc(Location(loc))
            steps.append(step[0])
            e = e.replace_trig(i, new_e_i)
        return e, steps

class HalfAngleIdentity(AlgorithmRule):
    """Algorithm rule (h) in Slagle's thesis.

    Take following identity:
    a) sin(v)cos(v) = 1/2 * sin(2v)
    b) cos^2(v) = 1/2 + 1/2 * cos(2v)
    c) sin^2(v) = 1/2 - 1/2 * cos(2v)
    """
    def eval(self, e, _loc=[]):
        x = Symbol('x', [CONST, VAR, OP, FUN])
        y = Symbol('y', [CONST, VAR, OP, FUN])
        pat1 = sin(x) * cos(x)
        pat2 = cos(x) * sin(x)
        pat3 = sin(x) ^ Const(2)
        pat4 = cos(x) ^ Const(2)
        pat5 = y * sin(x) * cos(x)
        pat6 = y * cos(x) * sin(x)

        sin_cos_expr = find_pattern(e, pat1)
        cos_sin_expr = find_pattern(e, pat2)
        sin_power_expr = find_pattern(e, pat3)
        cos_power_expr = find_pattern(e, pat4)
        y_sin_cos_expr = find_pattern(e, pat5)
        y_cos_sin_expr = find_pattern(e, pat6)


        half = Const(Fraction(1, 2))

        steps = []

        for t, loc, _ in sin_cos_expr:
            new_trig = half * sin(Const(2) * t.args[0].args[0])
            e = e.replace_trig(t, new_trig)
            steps.append(calc.TrigIdentityStep(e, "TR8", t, new_trig, _loc+list(loc)))
        for t, loc, _ in cos_sin_expr:
            new_trig = half * sin(Const(2) * t.args[0].args[0])
            e = e.replace_trig(t, new_trig)
            steps.append(calc.TrigIdentityStep(e, "TR8", t, new_trig, _loc+list(loc)))
        for t, loc, _ in sin_power_expr:
            new_trig = half - half * cos(Const(2) * t.args[0].args[0])
            e = e.replace_trig(t, new_trig)
            steps.append(calc.TrigIdentityStep(e, "TR8", t, new_trig, _loc+list(loc)))
        for t, loc, _ in cos_power_expr:
            new_trig = half + half * cos(Const(2) * t.args[0].args[0])
            e = e.replace_trig(t, new_trig)
            steps.append(calc.TrigIdentityStep(e, "TR7", t, new_trig, _loc+list(loc)))
        for t, loc, _ in y_sin_cos_expr:
            new_trig = half * t.args[0].args[0] * sin(Const(2) * t.args[1].args[0])
            e = e.replace_trig(t, new_trig)
            steps.append(calc.TrigIdentityStep(e, "TR8", t, new_trig, _loc+list(loc)))
        for t, loc, _ in y_cos_sin_expr:
            new_trig = half * t.args[0].args[0] * sin(Const(2) * t.args[1].args[0])
            e = e.replace_trig(t, new_trig)
            steps.append(calc.TrigIdentityStep(e, "TR8", t, new_trig, _loc+list(loc)))
        return e, steps

class TrigIdentity(AlgorithmRule):
    """
    Take the following identities:
    1) a + (-a) * sin^2(x) = a * cos^2(x)
    2) a + (-a) * cos^2(x) = a * sin^2(x)
    3) 1 + -sin^2(x) = cos^2(x)
    4) 1 + -cos^2(x) = sin^2(x)

    TR5(sin -> cos), TR6(cos -> sin)
    """
    def eval(self, e):
        x = Symbol('x', [VAR, OP, FUN])
        a = Symbol('a', [CONST])
        b = Symbol('b', [CONST])
        pat1 = a + b * (sin(x) ** Const(2))
        pat2 = a + b * (cos(x) ** Const(2))
        pat3 = Const(1) + -(sin(x) ** Const(2))
        pat4 = Const(1) + -(cos(x) ** Const(2))
        
        sin_power_expr = [(t, loc) for t, loc, _ in find_pattern(e, pat1)
                          if t.args[1].args[0].val < 0 and t.args[0].val + t.args[1].args[0].val == 0]
        cos_power_expr = [(t, loc) for t, loc, _ in find_pattern(e, pat2)
                          if t.args[1].args[0].val < 0 and t.args[0].val + t.args[1].args[0].val == 0]
        sin_power1_expr = find_pattern(e, pat3)
        cos_power1_expr = find_pattern(e, pat4)
    
        steps = []
        for t, loc in sin_power_expr:
            sin_coeff = t.args[0]
            body = t.args[1].args[1].args[0].args[0]
            e = e.replace_trig(t, sin_coeff * (cos(body) ** Const(2)))
            steps.append(calc.TrigIdentityStep(e, "TR5", t, sin_coeff * (cos(body) ** Const(2)), loc)) 
        for t, loc in cos_power_expr:
            cos_coeff = t.args[0]
            body = t.args[1].args[1].args[0].args[0]
            e = e.replace_trig(t, cos_coeff * (sin(body) ** Const(2)))
            steps.append(calc.TrigIdentityStep(e, "TR6", t, cos_coeff * (sin(body) ** Const(2)), loc))
        for t, loc, _ in sin_power1_expr:
            body = t.args[1].args[0].args[0].args[0]
            e = e.replace_trig(t, (cos(body) ** Const(2)))
            steps.append(calc.TrigIdentityStep(e, "TR5", t, cos(body) ** Const(2), loc)) 
        for t, loc, _ in cos_power1_expr:
            body = t.args[1].args[0].args[0].args[0]
            e = e.replace_trig(t, (sin(body) ** Const(2)))
            steps.append(calc.TrigIdentityStep(e, "TR6", t, sin(body) ** Const(2), loc))
        return e, steps


class ElimAbsRule(AlgorithmRule):
    """
    Eliminate absolute expression in the integration body.
    """
    def eval(self, e, loc=[]):
        if e.ty == OP and e.op == "*" and not e.args[1].ty == INTEGRAL\
            or e.is_constant() or not e.ty == INTEGRAL:
            return e, None

        if e.ty == OP and e.op == "*":
            integ = e.args[1]
        else:
            # assert e.ty == INTEGRAL, "Invalid %s" % str(e)
            integ = e
        rule = rules.ElimAbs()
        # first check if there are abs expr in e
        x = Symbol("x", [VAR, OP, FUN])
        abs_exprs = find_pattern(integ, Fun("abs", x))
        # don't have abs express
        if not abs_exprs:
            return e, None
        # don't have zero point
        loc = loc if e.ty == INTEGRAL else loc + [1]
        if not rule.check_zero_point(integ):
            result = e.replace_trig(integ, rule.eval(integ))
            step = calc.ElimAbsStep(result, loc)
            return result, [step]
        # handle zero point
        c = rule.get_zero_point(integ)
        new_problem = e.replace_trig(integ, rule.eval(integ))
        step = calc.ElimAbsStep(new_problem, loc, c)
        return new_problem, [step]

# TrigIdentity must execute before HalfAngleIndetity
algorithm_rules = [
    AlgoNonLinearSubstitution,
    DividePolynomial,
    LinearSubstitution,
    TrigIdentity,
    ElimAbsRule,
    HalfAngleIdentity,    
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

        tan_expr = find_pattern(e, tan_pat)
        cot_expr = find_pattern(e, cot_pat)
        sec_expr = find_pattern(e, sec_pat)
        csc_expr = find_pattern(e, csc_pat)

        steps = []
        reason = "sine cosine"

        for t, loc, _ in tan_expr:
            e = e.replace_trig(t, sin(t.args[0])/cos(t.args[0]))
            steps.append(calc.TrigIdentityStep(e, "TR2", t, sin(t.args[0])/cos(t.args[0]), loc))          

        for t, loc, _ in cot_expr:
            e = e.replace_trig(t, cos(t.args[0])/sin(t.args[0]))
            steps.append(calc.TrigIdentityStep(e, "TR2", t, cos(t.args[0])/sin(t.args[0]), loc))  

        for t, loc, _ in sec_expr:
            e = e.replace_trig(t, Const(1)/cos(t.args[0]))
            steps.append(calc.TrigIdentityStep(e, "TR1", t, Const(1)/cos(t.args[0]), loc))

        for t, loc, _ in csc_expr:
            e = e.replace_trig(t, Const(1)/sin(t.args[0]))
            steps.append(calc.TrigIdentityStep(e, "TR1", t, Const(1)/sin(t.args[0]), loc))

        return e, steps

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

        sin_expr = find_pattern(e, sin_pat)
        cos_expr = find_pattern(e, cos_pat)
        cot_expr = find_pattern(e, cot_pat)
        csc_expr = find_pattern(e, csc_pat)

        steps = []
        reason = "tangent secant"

        for t, loc, _ in sin_expr:
            e = e.replace_trig(t, tan(t.args[0])/sec(t.args[0]))
            steps.append(calc.TrigSubstitutionStep(e, loc, t, tan(t.args[0])/sec(t.args[0]), reason))

        for t, loc, _ in cos_expr:
            e = e.replace_trig(t, Const(1)/sec(t.args[0]))
            steps.append(calc.TrigSubstitutionStep(e, loc, t, Const(1)/sec(t.args[0]), reason))

        for t, loc, _ in cot_expr:
            e = e.replace_trig(t, Const(1)/tan(t.args[0]))
            steps.append(calc.TrigSubstitutionStep(e, loc, t, Const(1)/tan(t.args[0]), reason))

        for t, loc, _ in csc_expr:
            e = e.replace_trig(t, sec(t.args[0])/tan(t.args[0]))
            steps.append(calc.TrigSubstitutionStep(e, loc, t, sec(t.args[0])/tan(t.args[0]), reason))

        return e, steps

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

        sin_expr = find_pattern(e, sin_pat)
        cos_expr = find_pattern(e, cos_pat)
        tan_expr = find_pattern(e, tan_pat)
        sec_expr = find_pattern(e, sec_pat)

        steps = []
        reason = "cotangent cosecant"

        for t, loc, _ in sin_expr:
            e = e.replace_trig(t, Const(1)/csc(t.args[0]))
            steps.append(calc.TrigSubstitutionStep(e, loc, t, Const(1)/csc(t.args[0]), reason))

        for t, loc, _ in cos_expr:
            e = e.replace_trig(t, cot(t.args[0])/csc(t.args[0]))
            steps.append(calc.TrigSubstitutionStep(e, loc, t, cot(t.args[0])/csc(t.args[0]), reason))

        for t, loc, _ in tan_expr:
            e = e.replace_trig(t, Const(1)/cot(t.args[0]))
            steps.append(calc.TrigSubstitutionStep(e, loc, t, Const(1)/cot(t.args[0]), reason))

        for t, loc, _ in sec_expr:
            e = e.replace_trig(t, csc(t.args[0])/cot(t.args[0]))
            steps.append(calc.TrigSubstitutionStep(e, loc, t, csc(t.args[0])/cot(t.args[0]), reason))

        return e, steps

    def eval(self, e, loc=[]):
        initial_step = calc.SimplifyStep(e)
        
        res = []

        res1, step1 = self.sin_cos(e)
        if step1:
            res.append((res1, step1))

        # res2, step2 = self.tan_sec(e)
        # if step2:
        #     res.append((res2, step2))

        # res3, step3 = self.cot_csc(e)
        # if step3:
        #     res.append((res3, step3))
 
        return res

class HeuristicTrigonometricSubstitution(HeuristicRule):
    """Heuristic rule (b) in Slagle's thesis.(elf means "elementary function")

    The substitution rules:
    1) elf{sin(v),cos^2(v)}cos^{2n+1}(v) ==> u = sin(v);
    2) elf{cos(v),sin^2(v)}sin^{2n+1}(v) ==> u = cos(v);
    3) elf{tan(v),sec^2(v)}              ==> u = tan(v);(desparated)
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
                if n_value % 2 == 0:
                    return False, None
                return (True, e.args[1].args[0]) if n_value % 2 == 1 else (False, None)
            elif match(e, pat3):
                n_value = e.args[1].val
                return (True, e.args[0].args[0]) if n_value % 2 == 1 else (False, None)
            elif match(e, pat2):
                n = e.args[1].val
                if n % 2 == 0:
                    return False, None
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

        e_body = e.body
            
        if is_pat1(e_body)[0]:
            """Substitute sin(v) by u."""
            _, b = is_pat1(e_body)
            result, step = substitution(e, sin(b))
            return [(result, step)]
        elif is_pat2(e_body)[0]:
            """Substitute cos(v) by u."""
            _, b = is_pat2(e_body)
            result, step = substitution(e, cos(b))
            return [(result, step)]
        # elif is_pat3(e_body)[0]:
        #     """Substitute tan(v) by u."""
        #     _, b = is_pat3(e_body)
        #     result, step = substitution(e, tan(b))
        #     return [(result, step)]
        elif is_pat4(e_body)[0]:
            """Substitute cot(v) by u."""
            _, b = is_pat4(e_body)
            result, step = substitution(e, cot(b))
            return [(result, step)]
        elif is_pat5(e_body)[0]:
            """Substitute sec(v) by u."""
            _, b = is_pat5(e_body)
            result, step = substitution(e, sec(b))
            return [(result, step)]
        elif is_pat6(e_body)[0]:
            """Substitute csc(v) by u."""
            _, b = is_pat6(e_body)
            result, step = substitution(e, csc(b))
            return [(result, step)]
        else:
            return [(e, None)]

class HeuristicSubstitution(HeuristicRule):
    """Heuristic rule (c) in Slagle's thesis.

    Currently we implement a naive strategy of substitution for
    y subterm corresponds to lowest depth expression after substitution.  


    It can't return correct result when body is not monotonic in the given range.
    """
    def eval(self, e, loc=[]):
        res = []
        all_subterms = e.body.nonlinear_subexpr()

        depth = 0
        for subexpr in all_subterms:
            try:
                result, step = substitution(e, subexpr)   
                res.append((result, step))
            except:
                continue

        if res: # res is not empty
            res = [(r, step) for r, step in res if r != Const(0)] # May have bug when result is 0.
            res = sorted(res, key=lambda x:x[0].depth)
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

        res = []        
        factors = decompose_expr_factor(e.body)
        
        if len(factors) == 1:
            factors.append(Const(1))
        
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
                step = [calc.IntegrationByPartsStep(new_integral, u, v, loc)]
                res.append((new_integral, step))
        
        return res

class HeuristicElimQuadratic(HeuristicRule):
    """Heuristic rule (e) in Slagle's thesis.

    For quadratic subexpressions like a + b * x + c * x ^ 2,
    substitute x by y + b/2c, transform to a - b^2/4a + ay^2.
    
    The search for quadratic subexprs is not complete because of
    the non-standard normalization.

    """
    def eval(self, e, loc=[]):
        x = Symbol('x', [VAR, FUN])
        a = Symbol('a', [CONST])
        b = Symbol('b', [CONST])
        c = Symbol('c', [CONST])

        quadratic_patterns = [
            (x + (x^Const(2)), lambda m: (Const(0), Const(1), Const(1))),
            (x + a * (x^Const(2)), lambda m: (Const(0), Const(1), m[a])),
            (b * x + a * (x^Const(2)), lambda m: (Const(0), m[b], m[a])),
            (c + x + (x^Const(2)), lambda m: (m[c], Const(1), Const(1))),
            (c + x + a * (x^Const(2)), lambda m: (m[c], Const(1), m[a])),
            (c + b * x + (x^Const(2)), lambda m: (m[c], m[b], Const(1))),
            (c + b * x + a*(x^Const(2)), lambda m: (m[c], m[b], m[a])),
            (c + (x ^ Const(2)), lambda m: (m[c], Const(0), Const(1))),
        ]

        quadratic_terms = []
        for p, f in quadratic_patterns:
            quad = find_pattern(e.body, p, transform=f)
            if quad:
                quadratic_terms.append(quad)

        if not quadratic_terms:
            return []

        quadratics = [l for r in quadratic_terms for l in r]
        res = []
        v = gen_rand_letter(e.var)
        for quad, l, (a, b, c) in quadratics:
            # new_integral, f = rules.Substitution1(gen_rand_letter(e.var), Var(e.var) + (b/(Const(2)*c))).eval(e)
            new_integral, step1 = substitution(e, Var(e.var) + (b/(Const(2)*c)))
            # step1 = [calc.SubstitutionStep(
                # new_integral, new_integral.var, Var(e.var) + (b/(Const(2)*c)), f, tuple(loc) + (0,) + l)]
            new_integral, step2 = HeuristicExpandPower().eval(new_integral)[0]
            res.append((new_integral, step1 + step2))

        return res

class HeuristicTrigSubstitution(HeuristicRule):
    """Heuristic rule (g) in Slagle's thesis.
    
    Find subexpressions in form: a + b * x^2.
    There are 3 cases:
    (1) a > 0, b > 0, substitute x by sqrt(a/b)*tan(u);
    (2) a > 0, b < 0, substitute x by sqrt(a/-b)*sin(u);
    (3) a < 0, b > 0, substitute x by sqrt(-a/b)*sec(u);

    """
    def eval(self, e, loc=None):
        a = Symbol('a', [CONST])
        b = Symbol('b', [CONST])
        x = Symbol('x', [VAR])

        pats = [
            (a + (x ^ Const(2)), lambda m: (m[a], Const(1))),
            (a + b * (x ^ Const(2)), lambda m: (m[a], m[b])),
            (a - b * (x ^ Const(2)), lambda m: (m[a], Const(-(m[b].val)))),
            (a + -(x ^ Const(2)), lambda m: (m[a], Const(-1))),
            (a - (x ^ Const(2)), lambda m: (m[a], Const(-1)))
        ]

        all_subterms = []
        for p, f in pats:
            all_subterms.extend(find_pattern(e.body, p, transform=f))

        if not all_subterms:
            return []

        res = []
        new_var = Var(gen_rand_letter(str(e.var)))
        for s, loc, (a, b) in all_subterms:
            a, b = a.val, b.val
            assert not a < 0 or not b < 0, "Invalid value: a=%s, b=%s" % (a, b)
            if a > 0 and b > 0:
                subst = Op("^", Const(Fraction(a, b)), Const(Fraction(1,2))).normalize() * tan(new_var)
                
            elif a > 0 and b < 0:
                subst = Op("^", Const(Fraction(a, -b)), Const(Fraction(1,2))).normalize() * sin(new_var)
            
            elif a < 0 and b > 0:
                subst = Op("^", Const(Fraction(-a, b)), Const(Fraction(1,2))).normalize() * sec(new_var)
            new_integral = rules.Substitution2(str(new_var), subst).eval(e)
            step = [calc.SubstitutionInverseStep(new_integral, str(new_var), subst)]
            res.append((new_integral, step))

        return res

class HeuristicExpandPower(HeuristicRule):
    """Heuristic rule (g) in Slagle's thesis.

    Expansion of positive integer powers of nonconstant sums.
    
    """
    def eval(self, e, loc=[]):
        steps = []

        a = Symbol('a', [CONST])
        c = Symbol('c', [OP])
        pat = c ^ a
        subexpr = find_pattern(e, pat)

        expand_expr = e
        for s, l, _ in subexpr:
            base = s.args[0].to_poly()
            exp = s.args[1].val
            if isinstance(exp, int) and exp > 1 and exp <= 3:
                pw = base
                for i in range(exp-1):
                    pw = pw * base
                expand_expr = expand_expr.replace_expr(l, from_poly(pw))
                steps.append(calc.UnfoldPowerStep(expand_expr, tuple(loc)+l))

        return [(expand_expr, steps)]

class HeuristicExponentBase(HeuristicRule):
    """Heuristic rule(i) in Slagle's thesis.

    If the integrand has a list of subexpression like [b^{mv}, b^{nv}, ...],
    the base b is an exponent function, n is integer and v is var.
    Try to find the greatest divisor of m, n... assume it is k.
    Then try substitution: u = b^{kv}. 

    """
    def eval(self, e, loc=[]):
        n = Symbol('n', [CONST])
        x = Symbol('x', [VAR])

        pat = exp(n*x)
        exponents = find_pattern(e.body, pat)

        if len(exponents) <= 1:
            return []

        coeffs = []
        for exponent, _, _ in exponents:
            if exponent.args[0].ty == CONST:
                coeffs.append(1)
            else:
                coeffs.append(exponent.args[0].args[0].val)

        if not any(isinstance(n, int) for n in coeffs):
            return []


        gcd = functools.reduce(math.gcd, coeffs)
        new_integral, step = substitution(e, exp(Const(gcd)*Var(e.var)))        
        return [(new_integral, step)]


class HeuristicRationalSineCosine(HeuristicRule):
    """
    When the integrand is a rational function of sines and cosines,
    try substituting u=tan(v/2) 
    """
    def eval(self, e):
        e_body = e.body
        if e_body.is_spec_function("sin"):
            """
            Replace sin(v) by 2*u/(1+u^2) 
            """
            v = Symbol("v", [VAR, OP, FUN])
            pat1 = sin(v)
            s = find_pattern(e_body, pat1)
            new_e_body = e_body.replace_trig(s, parse_expr('2*u/(1+u^2)')) * parse_expr('2/(1+u^2)')
            lower = tan(e.lower/2)
            upper = tan(e.upper/2)
            return [(Integral("u", lower, upper, new_e_body), None)]
            
        elif e.is_spec_function("cos"):
            """
            Repalce cos(v) by (1-u^2)/(1+u^2) 
            """
            v = Symbol("v", [VAR, OP, FUN])
            pat1 = sin(v)
            s = find_pattern(e_body, pat1)
            new_e_body = e_body.replace_trig(s, parse_expr('(1-u^2)/(1+u^2)')) * parse_expr('2/(1+u^2)')
            lower = tan(e.lower/2)
            upper = tan(e.upper/2)
            return [(Integral("u", lower, upper, new_e_body), None)]

        else:
            return [(e, None)]


heuristic_rules = [
    TrigFunction,
    HeuristicTrigonometricSubstitution,
    HeuristicSubstitution,
    HeuristicIntegrationByParts,
    HeuristicElimQuadratic,
    HeuristicExpandPower,
    HeuristicTrigSubstitution,
    HeuristicExponentBase,
    HeuristicRationalSineCosine
]


class GoalNode:
    def trace(self):
        '''Give computation trace for resolved integration.'''
        assert self.resolved == True, '%s haven\'t been solved' % self.root
        return self.resolved_steps

class OrNode(GoalNode):
    """OR relationship in Slagle's thesis.
    
    To evaluate the integral at the root, only need to evaluate one of the
    child nodes. Each of the child nodes is a GoalNode.

    """
    def __init__(self, root, loc=None, parent=None, steps=None):
        if isinstance(root, str):
            root = parse_expr(root)

        self.root = root
        self.parent = parent
        self.children = []
        self.resolved = False
        if loc is None:
            loc = list()
        self.loc = Location(loc)
        self.root.loc = self.loc

        # Step used to go from parent to self.
        if steps is None:
            steps = tuple()
        self.steps = tuple(steps)

        # When resolved, total chain of steps to resolution
        self.resolved_steps = None

    def __str__(self):
        if len(self.children) == 0:
            return 'OrNode(%s,%s,[])' % (str(self.root), str(self.resolved))

        s = 'OrNode(%s,%s,\n' % (str(self.root), str(self.resolved))
        for step in self.steps:
            s += '   %s\n' % step
        for c in self.children:
            str_c = str(c)
            for line in str_c.splitlines():
                s += '   %s\n' % line
        s += ')'
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
        
        algo_steps = []

        not_solved_integral.add(cur_integral)
        for rule in algorithm_rules:
            cur_integral, cur_steps = rule().eval(cur_integral)
            if cur_steps:
                # cur_integral = cur_integral.normalize()
                for step in cur_steps:
                    step.prepend_loc(self.loc)
                    algo_steps.append(step)
            if rule == AlgoNonLinearSubstitution:
                continue
        
            norm_integral = rules.FullSimplify().eval(cur_integral)
            if norm_integral != cur_integral:
                algo_steps.append(calc.SimplifyStep(norm_integral, self.loc))
                cur_integral = norm_integral

        if cur_integral.ty == INTEGRAL:
            # Single integral case
            for rule in heuristic_rules:
                res = rule().eval(cur_integral)
                for r, steps in res:
                    if steps:
                        for step in steps:
                            step.prepend_loc(self.loc)
                        norm_r = rules.FullSimplify().eval(r)
                        if norm_r != r:
                            steps.append(calc.SimplifyStep(norm_r, self.loc))
                        if norm_r.ty == INTEGRAL and norm_r not in not_solved_integral:
                            self.children.append(OrNode(norm_r, loc=self.loc, parent=self, steps=algo_steps+steps))
                        elif norm_r not in not_solved_integral:
                            self.children.append(AndNode(norm_r, loc=self.loc, parent=self, steps=algo_steps+steps))
        
        else:
            # Linear combination of integrals
            not_solved_integral.remove(self.root)
            self.children.append(AndNode(cur_integral, loc=self.loc, parent=self, steps=algo_steps))
        self.compute_resolved()

    def compute_resolved(self):
        for c in self.children:
            if c.resolved:
                self.resolved = True
                self.resolved_steps = self.steps + c.resolved_steps
                break

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
    def __init__(self, root, loc, parent=None, steps=None):
        if isinstance(root, str):
            root = parse_expr(root)

        self.root = root
        self.parent = parent
        self.loc = Location(loc)
        self.children = [OrNode(r, self.loc.data+Location(l).data, parent=self)
                         for r, l in root.separate_integral()]

        if steps is None:
            steps = tuple()
        self.steps = tuple(steps)

        # When resolved, total chain of steps to resolution
        self.resolved_steps = None        
        self.resolved = (len(self.children) == 0)
        if self.resolved:
            self.resolved_steps = self.steps
            self.parent.compute_resolved()

    def __str__(self):
        if len(self.children) == 0:
            return 'AndNode(%s,%s,%s)' % (str(self.root), str(self.resolved), self.steps)

        s = 'AndNode(%s,%s,(\n' % (str(self.root), str(self.resolved))
        for step in self.steps:
            s += '   %s\n' % step
        for c in self.children:
            str_c = str(c)
            for line in str_c.splitlines():
                s += '   %s\n' % line
        s += ')'
        return s

    def compute_resolved(self):
        self.resolved_steps = self.steps
        for c in self.children:
            if c.resolved:
                self.resolved_steps += c.resolved_steps  # need to add location info
            else:
                self.resolved_steps = None
                break

        if self.resolved_steps:
            self.resolved = True

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

def is_mono(var, e, lower, upper):
    """Determine whether an expression is monotonic in the given interval."""
    e_deriv = deriv(var, e)
    zeros = solveset(sympy_style(e_deriv), sympy_style(var), Interval(sympy_style(lower), \
                        sympy_style(upper), left_open=True, right_open=True))
    return list([holpy_style(z) for z in zeros])

def split_integral(e, points):
    """"""
    split_points = [e.lower] + [holpy_style(p) for p in points] + [e.upper]
    split_integrals = [Integral(e.var, split_points[i], split_points[i+1], e.body) \
                        for i in range(len(points) + 1)]
    return sum(split_integrals[1:], split_integrals[0])

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

class Slagle(rules.Rule):
    def __init__(self, time_out=None):
        if time_out is None:
            self.timeout = 20
        else:
            self.timeout = time_out

    def compute_node(self, e):
        try:
            return bfs(OrNode(e))
        except multiprocessing.context.TimeoutError:
            return None

    def eval(self, e):
        try:
            node = timeout(self.timeout)(bfs)(OrNode(e))
            result = node.compute_value()
            return result
        except multiprocessing.context.TimeoutError:
            # print("Time out!")
            return None

def perform_steps(node):
    """
    Perform the real solving steps. 
    """        
    real_steps = []

    current = node.root

    for step in node.trace():
        loc = step.loc
        if step.reason == "Simplification":
            rule = rules.FullSimplify()
            current = rules.OnLocation(rule, loc).eval(current)
            real_steps.append({
                "text": str(current),
                "latex": latex.convert_expr(current),
                "reason": step.reason,
                "location": str(loc)
            })
        elif step.reason == "Substitution":
            rule = rules.Substitution1(step.var_name, step.var_subst)
            current = rules.OnLocation(rule, loc).eval(current)
            real_steps.append({
                "text": str(current),
                "latex": latex.convert_expr(current),
                "location": str(loc),
                "params": {
                    "f": str(step.f),
                    "g": str(step.var_subst),
                    "var_name": step.var_name
                },
                "_latex_reason": "Substitute \\(%s\\) for  \\(%s\\)" %\
                                    (latex.convert_expr(Var(step.var_name)), latex.convert_expr(step.var_subst)),
                "reason": step.reason
            })
        elif step.reason == "Integrate by parts":
            rule = rules.IntegrationByParts(step.u, step.v)
            current = rules.OnLocation(rule, loc).eval(current)
            real_steps.append({
                "text": str(current),
                "latex": latex.convert_expr(current),
                "location": str(loc),
                "reason": step.reason,
                "_latex_reason": "Integrate by parts, \\(u = %s, v = %s\\)" %\
                    (latex.convert_expr(step.u), latex.convert_expr(step.v)),
                "params": {
                    "parts_u": str(step.u),
                    "parts_v": str(step.v)
                }
            })
        elif step.reason == "Rewrite trigonometric":
            rule = rules.RewriteTrigonometric(step.rule_name)
            current = rules.OnLocation(rule, loc).eval(current)
            real_steps.append({
                "reason": step.reason,
                "text": str(current),
                "latex": latex.convert_expr(current),
                "params":{
                    "rule": step.rule_name
                },
                "_latex_reason": "Rewrite trigonometric \\(%s\\) to \\(%s\\)" % 
                            (latex.convert_expr(step.before_trig), latex.convert_expr(step.after_trig)), 
                # If there is only one integral in the full expression, location begins from the body;
                # Else from the integral
                "location": str(step.loc)
            })
        elif step.reason == "Elim abs":
            rule = rules.ElimAbs()
            current = rules.OnLocation(rule, loc).eval(current)
            info = {
                "reason": step.reason,
                "text": str(current),
                "latex": latex.convert_expr(current),
                "location": str(loc)
            }
            if step.zero_point is not None:
                info["params"] = {
                    "c": str(step.zero_point)
                }
            real_steps.append(info)
        elif step.reason == "Substitution inverse":
            rule = rules.Substitution2(step.var_name, step.var_subst)
            current = rules.OnLocation(rule, loc).eval(current)
            real_steps.append({
                "text": str(current),
                "latex": latex.convert_expr(current),
                "_latex_reason": "Substitute \\(%s\\) for \\(%s\\)" % \
                                    (latex.convert_expr(Var(step.var_name)), latex.convert_expr(step.var_subst)),
                "reason": step.reason,
                "location": str(loc),
                "params": {
                    "a": str(step.e.lower),
                    "b": str(step.e.upper),
                    "g": str(step.var_subst),
                    "var_name": str(step.var_name)
                }
            })
        elif step.reason == "Unfold power":
            rule = rules.UnfoldPower()
            current = rules.OnLocation(rule, loc).eval(current)
            real_steps.append({
                "text": str(current),
                "latex": latex.convert_expr(current),
                "reason": "Unfold power",
                "location": str(loc)
            })
        elif step.reason == "Rewrite fraction":
            rule = rules.PolynomialDivision()
            current = rules.OnLocation(rule, loc).eval(current)
            real_steps.append({
                "text": str(current),
                "latex": latex.convert_expr(current),
                "reason": step.reason,
                "params": {
                    "rhs": str(step.rhs),
                    "denom": str(step.denom),
                },
                "location": str(step.loc)
            })
        elif step.reason == "Split region":
            rule = rules.SplitRegion(step.zero_point)
            current = rules.OnLocation(rule, loc).eval(current)
            real_steps.append({
                "text": str(current),
                "latex": latex.convert_expr(current),
                "reason": step.reason,
                "location": str(step.loc),
                "params": {
                    "c": str(step.zero_point)
                }
            })
        else:
            raise NotImplementedError(step.reason)

    last_expr = parse_expr(real_steps[-1]["text"])
    if last_expr.is_constant() and last_expr.normalize() == last_expr:
        return real_steps
    final_expr = rules.FullSimplify().eval(last_expr)
    real_steps.append({
        "text": str(final_expr),
        "latex": latex.convert_expr(final_expr),
        "reason": "Simplification",
        "location": "."
    })

    return real_steps
        