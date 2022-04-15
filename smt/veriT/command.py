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
    def __init__(self, id, assm) -> None:
        self.id = id
        self.assm = assm

    def __str__(self):
        return "(assume %s (%s))" % (self.id, self.assm)

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
        if pm is None:
            pm = []
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

class Anchor(ProofCommand):
    """An anchor is a start of a subproof, every anchor
    has a ":step" annotation to indicate the step which
    will end the subproof. Anchor can add arguments to the context
    for the subproof.
    """
    def __init__(self, id, ctx=None) -> None:
        self.id = id
        self.ctx = ctx

    def __str__(self) -> str:
        if self.ctx is None:
            return "(anchor :step %s)" % self.id
        else:
            return "(anchor :step %s :args(%s)" % (self.id, self.ctx)