"""Proof reconstruction of verit proof."""
class ProofCommand:
    """The proofs in veriT is a list of proof command.
    Each command has a unique index as the first argument to 
    later reference.

    Proof commands come in two flavors: assume and step.
    - assume introduces a new assumption which is neither 
      tautological or derived from permises.
    - step: introduce a derived or tautological formula.
    """
    def __init__(self) -> None:
        pass

class Assume(ProofCommand):
    """Assume command introduces a new assumption (pt) 
    which is neither tautological or derived from permises."""
    def __init__(self, id, pt) -> None:
        self.id = id
        self.pt = pt

    def __str__(self):
        return "(assume %s (%s))" % (self.name, self.pt)

class Step(ProofCommand):
    """Step command introduces a derived or tautological formula.
    
    cl : a list of proof terms, in order to express (n-ary) 
            disjunction in SMT-LIB `or` command.
    rule_name : a deduction method.
    pm: the premises of the rule.
    """
    def __init__(self, id, rule_name, cl, pm=None) -> None:
        self.id = id
        self.rule_name = rule_name
        self.cl = cl
        self.pm = pm

    def __str__(self):
        cl = " ".join(str(c) for c in self.cl)
        pm = " ".join(str(p) for p in self.pm)
        if self.pm is None:
            return "(step %s (cl %s) :rule %s)" % \
                (self.id, cl, self.rule_name)
        else:
            return "(step %s (cl %s) :rule %s :premises %s)" % \
                (self.id, cl, self.rule_name, pm)

