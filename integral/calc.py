"""
Record integral calculation process.

"""
import json
from integral import latex
from integral import rules
from integral.expr import Location, Var


class IntegrationStep:
    def info(self):
        """Return necessary information on current integration step.
        """
        pass

    def compute(self):
        """Use given info do integration.
        """
        pass

    def prepend_loc(self, prefix):
        self.loc = Location(prefix.data + self.loc.data)

    def __repr__(self):
        return str(self)


class InitialStep(IntegrationStep):
    def __init__(self, e):
        self.e = e
        self.latex = latex.convert_expr(e)
        self.loc = Location()

    def __str__(self):
        return "Initial"
    
    def info(self):
        return {
            "reason" : "Initial",
            "latex" : self.latex,
            "text": str(self.e)
        }

class SimplifyStep(IntegrationStep):
    def __init__(self, e, loc=[]):
        """comp is the integration method.
        """
        self.e = e
        self.reason = "Simplification"
        self.latex = latex.convert_expr(e)
        self.loc = Location(loc)

    def __str__(self):
        return "Simplification on %s" % self.loc

    def info(self):
        return {
            "text": str(self.e),
            "latex": self.latex,
            "reason": "Simplification",
            "location": str(self.loc),
        }

class LinearityStep(IntegrationStep):
    def __init__(self, e, loc=[]):
        self.e = e
        self.reason = "Linearity"
        self.latex = latex.convert_expr(e)
        self.loc = Location(loc)

    def __str__(self):
        return "Linearity on %s" % self.loc

    def info(self):
        return {
            "text": str(self.e),
            "latex": self.latex,
            "location": str(self.loc),
            "reason": "Linearity"
        }
        
class CommonIntegralStep(IntegrationStep):
    def __init__(self, e, loc=[]):
        self.e = e
        self.reason = "CommonIntegral"
        self.latex = latex.convert_expr(e)
        self.loc = Location(loc)

    def __str__(self):
        return "Common integral on %s" % self.loc

    def info(self):
        return {
            "text": str(self.e),
            "latex": self.latex,
            "location": str(self.loc),
            "reason": "CommonIntegral"
        }

class SubstitutionStep(IntegrationStep):
    def __init__(self, e, var_name, var_subst, f, loc=[]):
        self.e = e
        self.var_name = var_name
        self.var_subst = var_subst
        self.f = f
        self.latex = latex.convert_expr(e)
        self.loc = Location(loc)
        self.reason = "Substitution"

    def __str__(self):
        return "Substitute %s for %s on %s" % (self.var_name, self.var_subst, self.loc)

    def info(self):
        return  {
            "text": str(self.e),
            "latex": self.latex,
            "location": str(self.loc),
            "params": {
                "f": str(self.f),
                "g": str(self.var_subst),
                "var_name": self.var_name
            },
            "_latex_reason": "Substitute \\(%s\\) for  \\(%s\\)" %\
                                (latex.convert_expr(Var(self.var_name)), latex.convert_expr(self.var_subst)),
            "reason": self.reason
        }

class SubstitutionInverseStep(IntegrationStep):
    def __init__(self, e, var_name, var_subst, loc=[]):
        self.e = e
        self.reason = "Substitution inverse"
        self.latex = latex.convert_expr(e)
        self.var_name = var_name
        self.var_subst = var_subst
        self.comp = rules.Substitution2(var_name, var_subst).eval  
        self.loc = Location(loc) 

    def __str__(self):
        return "Inverse substitute %s for %s on %s" % (self.var_name, self.var_subst, self.loc)

    def info(self):
        return {
            "text": str(self.e),
            "latex": self.latex,
            "_latex_reason": "Substitute \\(%s\\) for \\(%s\\)" % \
                                (latex.convert_expr(Var(self.var_name)), latex.convert_expr(self.var_subst)),
            "reason": self.reason,
            "location": str(self.loc),
            "params": {
                "a": str(self.e.lower),
                "b": str(self.e.upper),
                "g": str(self.var_subst),
                "var_name": self.var_name
            }
        }

    def compute(self):
        return self.comp(e)

class UnfoldPowerStep(IntegrationStep):
    def __init__(self, e, loc=[]):
        self.e = e
        self.latex = latex.convert_expr(e)
        self.reason = "Unfold power"
        self.comp = rules.UnfoldPower.eval
        self.loc = Location(loc)

    def __str__(self):
        return "Unfold power on %s" % self.loc

    def info(self):
        return {
            "text": str(self.e),
            "latex": self.latex,
            "reason": self.reason,
            "location": str(self.loc),
        }

    def compute(self):
        return self.comp(e)

class EquationSubstitutionStep(IntegrationStep):
    def __init__(self, e, loc=[]):
        self.e = e
        self.latex = latex.convert_expr(e)
        self.loc = Location(loc)
        self.reason = "Solve equation"

    def __str__(self):
        return "Equation substitution on %s" % self.loc

    def info(self):
        return {
            "text": str(self.e),
            "latex": self.latex,
            "location": str(self.loc),
            "reason": "Solve equation"
        }

    def compute(self):
        return self.comp(e)

class TrigSubstitutionStep(IntegrationStep):
    def __init__(self, e, loc, old_trig, new_trig, tr_rule):
        self.e = e
        self.old_trig = old_trig
        self.new_trig = new_trig
        self.loc = Location(loc)
        self.latex =  latex.convert_expr(e)
        self.tr_rule = tr_rule
        self.reason = "Rewrite trigonometric"

    def __str__(self):
        return "Trig substitution %s for %s on %s" % (self.old_trig, self.new_trig, self.loc)
    
    def info(self):
        return {
            "text": str(self.e),
            "reason": self.reason,
            "_latex_reason": "Rewrite trigonometric \\(%s\\) to \\(%s\\)" %\
                (latex.convert_expr(self.old_trig), latex.convert_expr(self.new_trig)),
            "latex": self.latex,
            "params": {
                "rule": self.tr_rule
            },
            "old_trig": str(self.old_trig),
            "new_trig": str(self.new_trig),
            "location": str(self.loc),
        }

class IntegrationByPartsStep(IntegrationStep):
    def __init__(self, e, u, v, loc=[]):
        self.e = e
        self.u = u
        self.v = v
        self.loc = Location(loc)
        self.latex = latex.convert_expr(e)
        self.reason = "Integrate by parts"

    def __str__(self):
        return "Integrate by parts with u = %s and v = %s on %s" % (self.u, self.v, self.loc)

    def info(self):
        return {
            "text": str(self.e),
            "latex": self.latex,
            "reason": self.reason,
            "_latex_reason": "Integrate by parts, \\(u = %s, v = %s\\)" %\
                            (latex.convert_expr(self.u), latex.convert_expr(self.v)),
            "location": str(self.loc),
            "params": {
                "parts_u": str(self.u),
                "parts_v": str(self.v)
            }
        }

class PolynomialDivisionStep(IntegrationStep):
    def __init__(self, e, denom, rhs, loc=[]):
        self.e = e
        self.denom = denom
        self.loc = Location(loc)
        self.rhs = rhs
        self.latex= latex.convert_expr(e)
        self.reason = "Rewrite fraction"

    def __str__(self):
        return "Polynomial division on %s" % self.loc

    def info(self):
        return {
            "latex": latex.convert_expr(self.e),
            "location": str(self.loc),
            "params": {
                "denom": str(self.denom),
                "rhs": str(self.rhs)
            },
            "reason": self.reason,
            "text": str(self.e)
        }

class ElimAbsStep(IntegrationStep):
    def __init__(self, e, loc, zero_point=None):
        self.e = e
        self.loc = Location(loc)
        self.zero_point = zero_point
        self.reason = "Elim abs"

    def __str__(self):
        return "Elim abs point is %s, loc is %s" % (self.zero_point, self.loc)

    def info(self):
        logs = {
            "text": str(self.e),
            "latex": latex.convert_expr(self.e),
            "location": str(self.loc),
            "reason": self.reason,   
        }

        if self.zero_point is not None:
            logs["params"] = {
                "c": str(self.zero_point)
            }

        return logs

class TrigIndentityStep(IntegrationStep):
    def __init__(self, e, rule_name, before_trig, after_trig, loc=[]):
        self.e = e
        self.rule_name = rule_name
        self.before_trig = before_trig
        self.after_trig = after_trig
        self.loc = Location(loc)
        self.reason = "Rewrite trigonometric"

    def __str__(self):
        return "Trig substitution: %s by %s" % (self.before_trig, self.after_trig)

    def info(self):
        return {
            "reason": self.reason,
            'text': str(self.e),
            'latex': latex.convert_expr(self.e),
            "params":{
                "rule": self.rule_name
            },
            '_latex_reason': "Rewrite trigonometric \\(%s\\) to \\(%s\\)" % 
                        (latex.convert_expr(self.before_trig), latex.convert_expr(self.after_trig)), 
            # If there is only one integral in the full expression, location begins from the body;
            # Else from the integral
            "location": str(self.loc)
        }