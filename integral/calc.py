"""
Record integral calculation process.

"""
import json
from integral import latex
from integral import rules

class IntegrationStep:
    def info(self):
        """Return necessary information on current integration step.
        """
        pass

    def compute(self):
        """Use given info do integration.
        """
        pass

class SimplifyStep(IntegrationStep):
    def __init__(self, e, comp, loc=[]):
        """comp is the integration method.
        """
        self.e = e
        self.reason = "Simplification"
        self.latex = latex.convert_expr(e)
        self.comp = comp.eval
        self.loc = loc

    def info(self):
        return {
            "text": str(self.compute()),
            "latex": self.latex,
            "reason": "Simplification",
            "loc": self.loc
        }

    def compute(self):
        return self.comp(self.e)

class LinearityStep(IntegrationStep):
    def __init__(self, e, loc=[]):
        self.e = e
        self.reason = "Linearity"
        self.latex = latex.convert_expr(e)
        self.loc = loc

    def info(self):
        return {
            "text": str(e),
            "latex": self.latex,
            "reason": "Simplification"
        }
        
class CommonIntegralStep(IntegrationStep):
    def __init__(self, e, loc=[]):
        self.e = e
        self.reason = "CommonIntegral"
        self.latex = latex.convert_expr(e)
        self.loc = loc

    def info(self):
        return {
            "text": str(e),
            "latex": self.latex,
            "reason": "Simplification"
        }

class SubstitutionStep(IntegrationStep):
    def __init__(self, e, var_name, var_subst, f, loc=[]):
        self.e = e
        self.var_name = var_name
        self.var_subst = var_subst
        self.reason = "Substitution"
        self.f = f
        self.latex = latex.convert_expr(e)
        self.loc = loc

    def info(self):
        return {
            "text": str(self.e),
            "latex": self.latex,
            "location":  self.loc,
            "params": {
                "f": str(f),
                "g": str(self.var_subst),
                "var_name": self.var_name
            },
            "reason": self.reason,
        }

class SubstitutionInverseStep(IntegrationStep):
    def __init__(self, e, var_name, var_subst, loc=[]):
        self.e = e
        self.reason = "Substitution Inverse"
        self.latex = latex.convert_expr(e)
        self.var_name = var_name
        self.var_subst = var_subst
        self.comp = rules.Substitution2(var_name, var_subst).eval  
        self.loc = loc 

    def info(self):
        return {
            "text": str(self.e),
            "latex": self.latex,
            "reason": self.reason,
            "params": {
                "a": str(e.lower),
                "b": str(e.upper),
                "g": str(var_subst),
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
        self.comp = rules.unfoldPower.eval
        self.loc = loc

    def info(self):
        return {
            "text": str(self.e),
            "latex": self.latex,
            "reason": self.reason,
            "location": self.loc
        }

    def compute(self):
        return self.comp(e)

class EquationSubstitutionStep(IntegrationStep):
    def __init__(self, e, loc=[]):
        self.e = e
        self.latex = latex.convert_expr(e)
        
    def info(self):
        return {
            "text": str(self.e),
            "latex": self.latex
        }

    def compute(self):
        return self.comp(e)

class TrigSubstitutionStep(IntegrationStep):
    def __init__(self, e, loc, old_trig, new_trig, reason):
        self.e = e
        self.old_trig = old_trig
        self.new_trig = new_trig
        self.loc = loc
        self.latex =  latex.convert_expr(e)
        self.reason = reason
    
    def info(self):
        return {
            "text": str(self.e),
            "latex": self.latex,
            "old_trig": self.old_trig,
            "new_trig": self.new_trig,
            "location": self.loc
        }

class IntegrationByPartsStep(IntegrationStep):
    def __init__(self, e, u, v, loc=[]):
        self.e = e
        self.u = u
        self.v = v
        self.loc = loc
        self.latex = latex.convert_expr(e)

    def info(self):
        return {
            "text": str(self.e),
            "latex": self.latex,
            "location": self.loc,
            "params": {
                "part_u": str(self.u),
                "part_v": str(self.v)
            }
        }

class PolynomialDivisionStep(IntegrationStep):
    def __init__(self, e, denom, rhs, loc=[]):
        self.e = e
        self.denom = denom
        self.loc = loc
        self.rhs = rhs
        self.latex= latex.convert_expr(e)

    


class Calc:
    def __init__(self, history,):
        pass