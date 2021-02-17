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
            "text": str(self.compute()),
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
            "reason": "Simplification"
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
            "reason": "Simplification"
        }

class SubstitutionStep(IntegrationStep):
    def __init__(self, e, var_name, var_subst, f, loc=[]):
        self.e = e
        self.var_name = var_name
        self.var_subst = var_subst
        self.f = f
        self.latex = latex.convert_expr(e)
        self.loc = Location(loc)

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
            "reason": "Substitution"
        }

class SubstitutionInverseStep(IntegrationStep):
    def __init__(self, e, var_name, var_subst, loc=[]):
        self.e = e
        self.reason = "Substitution Inverse"
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
        self.reason = "Unfold Power"
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

    def __str__(self):
        return "Equation substitution on %s" % self.loc

    def info(self):
        return {
            "text": str(self.e),
            "latex": self.latex,
            "location": str(self.loc),
        }

    def compute(self):
        return self.comp(e)

class TrigSubstitutionStep(IntegrationStep):
    def __init__(self, e, loc, old_trig, new_trig, reason):
        self.e = e
        self.old_trig = old_trig
        self.new_trig = new_trig
        self.loc = Location(loc)
        self.latex =  latex.convert_expr(e)
        self.reason = reason

    def __str__(self):
        return "Trig substitution %s for %s on %s" % (self.old_trig, self.new_trig, self.loc)
    
    def info(self):
        return {
            "text": str(self.e),
            "reason": "Rewrite trigonometric",
            "_latex_reason": "Rewrite trigonometric \\(%s\\) to \\(%s\\)" %\
                (latex.convert_expr(old_trig), latex.convert_expr(new_trig)),
            "latex": self.latex,
            "old_trig": self.old_trig,
            "new_trig": self.new_trig,
            "location": str(self.loc),
        }

class IntegrationByPartsStep(IntegrationStep):
    def __init__(self, e, u, v, loc=[]):
        self.e = e
        self.u = u
        self.v = v
        self.loc = Location(loc)
        self.latex = latex.convert_expr(e)

    def __str__(self):
        return "Integrate by parts with u = %s and v = %s on %s" % (self.u, self.v, self.loc)

    def info(self):
        return {
            "text": str(self.e),
            "latex": self.latex,
            "reason": "Integrate by parts",
            "_latex_reason": "Integrate by parts, \\(u = %s, v = %s\\)" %\
                            (latex.convert_expr(self.u), latex.convert_expr(self.v)),
            "location": str(self.loc),
            "params": {
                "part_u": str(self.u),
                "part_v": str(self.v)
            }
        }

class PolynomialDivisionStep(IntegrationStep):
    def __init__(self, e, denom, rhs, loc=[]):
        self.e = e
        self.denom = denom
        self.loc = Location(loc)
        self.rhs = rhs
        self.latex= latex.convert_expr(e)

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
            "reason": "Rewrite fraction",
            "text": str(self.e)
        }