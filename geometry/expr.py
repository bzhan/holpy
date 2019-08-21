"""Expressions in geometry prover."""

class Fact:
    """Represent a fact in geometry prover, e.g.:

    coll(A, C, B) is Fact("coll", ["A", "C", "B"]).

    """
    def __init__(self, pred_name, args):
        assert isinstance(pred_name, str)
        assert isinstance(args, list) and all(isinstance(arg, str) for arg in args)
        self.pred_name = pred_name
        self.args = args

    def __eq__(self, other):
        return isinstance(other, Fact) and self.pred_name == other.pred_name and \
            self.args == other.args

    def __str__(self):
        return "%s(%s)" % (self.pred_name, ",".join(self.args))


class Rule:
    """Represent a rule in geometry prover, e.g.:

    coll(A, C, B) := coll(A, B, C) is
    Rule([coll(A, B, C)], coll(A, C, B))

    """
    def __init__(self, assums, concl):
        assert isinstance(assums, list) and all(isinstance(assum, Fact) for assum in assums)
        assert isinstance(concl, Fact)
        self.assums = assums
        self.concl = concl

    def __eq__(self, other):
        return isinstance(other, Rule) and self.assums == other.assums and self.concl == other.concl

    def __str__(self):
        return "%s :- %s" % (str(self.concl), ", ".join(str(assum) for assum in self.assums))

class MatchException(Exception):
    pass


def match_expr(pat, f, inst):
    """Match pattern with f, record results in inst.

    Example:

    match(coll(A, B, C), coll(P, Q, R), {}) -> {A: P, B: Q, C: R}.

    match(coll(A, B, C), coll(P, Q, R), {A: P}) -> {A: P, B: Q, C: R}.

    match(coll(A, B, C), coll(P, Q, R), {A: Q}) -> raise MatchException.

    match(coll(A, B, C), para(P, Q, R, S), {}) -> raise MatchException.

    """
    assert isinstance(pat, Fact) and isinstance(f, Fact)
    if pat.pred_name != f.pred_name:
        raise MatchException

    if len(pat.args) != len(f.args):
        raise MatchException

    for p_arg, f_arg in zip(pat.args, f.args):
        if p_arg in inst:
            if f_arg != inst[p_arg]:
                raise MatchException
        else:
            inst[p_arg] = f_arg

def apply_rule(rule, facts):
    """Apply given rule to the list of facts, either return a new fact
    (on success) or raise MatchException.

    """
    assert isinstance(rule, Rule)
    assert isinstance(facts, list) and all(isinstance(fact, Fact) for fact in facts)
