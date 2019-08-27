"""Expressions in geometry prover."""

import itertools


class Fact:
    """Represent a fact in geometry prover, e.g.:

    coll(A, C, B) is Fact("coll", ["A", "C", "B"]).

    """
    def __init__(self, pred_name, args, updated=False, lemma=None, cond=None):
        assert isinstance(pred_name, str)
        assert isinstance(args, list) and all(isinstance(arg, str) for arg in args)
        self.pred_name = pred_name
        self.args = args
        self.updated = updated
        self.lemma = lemma
        self.cond = cond

    def __hash__(self):
        return hash(("Fact", self.pred_name, tuple(self.args)))

    def __eq__(self, other):
        return isinstance(other, Fact) and self.pred_name == other.pred_name and \
            self.args == other.args

    def __str__(self):
        return "%s(%s)" % (self.pred_name, ",".join(self.args))


class Line:
    """Represent a line contains more than one point.
    """
    def __init__(self, args, source=None):
        assert isinstance(args, list)
        assert len(args) > 1
        assert all(isinstance(arg, str) for arg in args)
        self.args = set(args)
        self.source = source

    def __hash__(self):
        return hash(("line", tuple(sorted(self.args))))

    def __eq__(self, other):
        return isinstance(other, Line) and self.args == other.args

    def is_same_line(self, other):
        # Two lines are same if they have at least 2 identical points.
        if isinstance(other, Line) and len(self.args.intersection(other.args)) >= 2:
            return True
        return False

    def extend(self, args):
        assert all(isinstance(arg, str) for arg in args)
        self.args.update(args)

    def extend_line(self, line):
        assert isinstance(line, Line)
        self.extend(line.args)


class Rule:
    """Represent a rule in geometry prover, e.g.:

    coll(A, C, B) :- coll(A, B, C) is
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


def make_line(coll):
    """Construct a line from a collinear fact. """
    assert isinstance(coll, Fact)
    assert coll.pred_name == "coll"

    return Line(coll.args)


def make_line_facts(facts):
    """Construct lines from a list of given facts. """
    assert isinstance(facts, list)
    assert all(isinstance(fact, Fact) for fact in facts)

    lines = []
    for fact in facts:
        if fact.pred_name == "coll":
            new_line = make_line(fact)
            same = [inx for inx, _ in enumerate(lines) if new_line.is_same_line(lines[inx])]
            if len(same) > 0:
                lines[same[0]].extend_line(new_line)
            else:
                lines.append(new_line)
    return lines


def extend_line(line, n):
    """Return a list contains all line segments of length 2 to n+1
    in the given line.
    
    """
    assert isinstance(n, int) and n >= 2
    assert isinstance(line, Line)
    segments = []
    for i in range(2, n + 1):
        for j in itertools.permutations(line.args, i):
            segments.append(list(j))
    return segments


def apply_rule(rule, facts, record=False, lemma=None):
    """Apply given rule to the list of facts, either return a new fact
    (on success) or raise MatchException.

    record: whether to record application of the rule in the new fact.

    Example:

        apply_rule(Rule([para(A, B, C, D), para(C, D, E, F)], para(A, B, E, F)), [para(P, Q, R, S), para(R, S, U, V)])
        -> para(P, Q, U, V).

        apply_rule(Rule([coll(A, B, C)], coll(A, C, B)), [para(A, B, D, C)]) -> raise MatchException.

    """

    assert isinstance(rule, Rule)
    assert isinstance(facts, list) and all(isinstance(fact, Fact) for fact in facts)

    inst = {}
    for assume, fact in zip(rule.assums, facts):
        match_expr(assume, fact, inst)

    args = [inst[i] for i in rule.concl.args]

    if record:
        return Fact(rule.concl.pred_name, args, updated=True, lemma=lemma, cond=facts)
    else:
        return Fact(rule.concl.pred_name, args)


def apply_rule_line(rule, facts, lines, record=False, lemma=None):
    """
    (unfinished)
    Apply given rule to the list of facts.
    If any fact in the list refers to lines in the given list of lines, then try to apply given rule to
    all the combinations of dots on the lines.
    Example:
        apply_rule_line(Rule([perp(A, B, C, D), perp(C, D, E, F)], para(A, B, E, F)),
                        [perp(P, Q, R, S), perp(R, S, U, V)],
                        [line(P, Q, T), line(R, S), line(U, V)])
        ->[para(P, Q, U, V), para(P, T, U, V), para(Q, T, U, V)]
    """
    assert isinstance(rule, Rule)
    assert isinstance(facts, list)
    assert isinstance(lines, list)

    new_facts = []

    for fact in facts:
        name = fact.pred_name
        if name == "perp":
            n = 2

        l = Line(fact.args)
        same_line = [line for line in lines if l.is_same_line(line)]
        assert len(same_line) == 1
        extended = extend_line(same_line[0], n)


def apply_rule_hyps(rule, hyps, only_updated=False):
    """Try to apply given rule to one or more facts in a list, generate
    new facts (as many new facts as possible), return a list of new facts.

    Repetitive facts as hypotheses apply to one rule is not allowed.
    Example:

        apply_rule_hyps(
            Rule([coll(A, B, C)], coll(A, C, B)),
            [coll(D, E, F), coll(P, Q, R), para(A, B, D, C)]
        ) -> [coll(D, F, E), coll(P, R, Q)].

    """
    assert isinstance(rule, Rule)
    assert isinstance(hyps, list)
    assert all(isinstance(fact, Fact) for fact in hyps)
    new_facts = []
    for seq in itertools.permutations(range(len(hyps)), len(rule.assums)):
        facts = []
        for num in list(seq):
            facts.append(hyps[int(num)])
        try:
            if only_updated:
                updated = [fact for fact in facts if fact.updated]
                if len(updated) > 0:
                    new_fact = apply_rule(rule, facts, record=True, lemma=list(seq))
            else:
                new_fact = apply_rule(rule, facts, record=True, lemma=list(seq))
        except MatchException:
            pass
        else:
            if new_fact not in new_facts:
                new_facts.append(new_fact)
    return new_facts


def apply_ruleset_hyps(ruleset, hyps, only_updated=False):
    """Try to apply every rule in a ruleset to one or more fact
    in a list (as many as possible), return a list of new facts.

    Repetitive facts as hypotheses apply to one rule is not allowed.
    """
    assert isinstance(ruleset, dict)
    assert all(isinstance(rule, Rule) for _, rule in ruleset.items())

    new_facts = []
    for _, rule in ruleset.items():
        if only_updated:
            unique = [fact for fact in apply_rule_hyps(rule, hyps, only_updated=True)
                      if fact not in new_facts]
        else:
            unique = [fact for fact in apply_rule_hyps(rule, hyps)
                      if fact not in new_facts]

        new_facts.extend(unique)

    return new_facts


def search_fixpoint(ruleset, hyps, concl):
    """Recursively apply given ruleset to a list of hypotheses to
    obtain new facts. Recursion exits when a new fact is exactly
    the same as the given conclusion, or when new fact is not able
    to be generated.
    
    """
    def union_hyps_and_facts(hyps, facts):
        unique = [fact for fact in facts if fact not in hyps]
        return hyps.extend(unique)

    def is_in_new_facts(concl, facts):
        p = [Fact(fact.pred_name, fact.args) for fact in facts]
        if concl in p:
            return True
        return False

    assert isinstance(concl, Fact)

    new_facts = apply_ruleset_hyps(ruleset, hyps)
    facts = union_hyps_and_facts(hyps, new_facts)
    if is_in_new_facts(concl, new_facts):
        return facts

    while True:
        new_facts = apply_ruleset_hyps(ruleset, facts, only_updated=True)
        if new_facts == [] or is_in_new_facts(concl, new_facts):
            return facts
        facts = union_hyps_and_facts(hyps, new_facts)
