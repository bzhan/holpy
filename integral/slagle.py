import random, string
from integral.expr import *
from integral.rules import *

a = Symbol('a', [CONST])
b = Symbol('b', [CONST])
x = Symbol('x', [VAR])
e = Symbol('e', [OP])
pat1 = a * x + b
pat2 = a * x
pat3 = e ^ a

def gen_rand_letter(ex):
    return random.choices(string.ascii_lowercase.replace(ex, ''))[0]

def linearize(integral):
    return Linearity().eval(integral)

def substitution(integral, subst):
    new_var = gen_rand_letter(integral.var)
    return Substitution1(new_var, subst).eval(integral)[0]

def linear_substitution(integral):
    assert isinstance(integral, Integral), "%s Should be an integral." % (integral)
    func_body = collect_spec_expr(integral.body, Symbol('f', [FUN]))
    if len(func_body) == 1 and (match(func_body[0], pat1) or match(func_body[0], pat2)): 
        return linearize(substitution(integral, func_body[0]).normalize())
    elif len(func_body) == 0:
        power_body = collect_spec_expr(integral.body, pat3)
        if len(power_body) == 1 and (match(power_body[0], pat1) or match(power_body[0], pat2)): 
            return linearize(substitution(integral, power_body[0]))
        else:
            return integral
    else:
        return integral

def algo_trans(integral):
    assert isinstance(integral, Integral), "%s Should be an integral.l"
    integral = integral.normalize()
    return linear_substitution(linearize(integral))

