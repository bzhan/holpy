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

    def __eq__(self, other):
        return isinstance(other, Fact) and self.pred_name == other.pred_name and \
            self.args == other.args

    def __str__(self):
        return "%s(%s)" % (self.pred_name, ",".join(self.args))


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


def apply_rule(rule, facts, record=False, lemma=None):
    """Apply given rule to the list of facts, either return a new fact
    (on success) or raise MatchException.

    Example:

        apply_rule(Rule([para(A, B, C, D), para(C, D, E, F)], para(A, B, E, F)), [para(P, Q, R, S), para(R, S, U, V)])
        -> para(P, Q, U, V).

        apply_rule(Rule([coll(A, B, C)], coll(A, C, B)), [para(A, B, D, C)]) -> raise MatchException.

    """

    assert isinstance(rule, Rule)
    assert isinstance(facts, list) and all(isinstance(fact, Fact) for fact in facts)

    matched = {}
    for assume, fact in zip(rule.assums, facts):
        match_expr(assume, fact, matched)

    args = [matched[i] for i in rule.concl.args]

    if record:
        return Fact(rule.concl.pred_name, args, updated=True, lemma=lemma, cond=facts)
    else:
        return Fact(rule.concl.pred_name, args)


def apply_rule_hyps(rule, hyps, only_updated=False):
    """Try to apply given rule to one or more facts in a list, generate new facts (as many new facts as possible),
    return a list of new facts.
    Repetitive facts as hypotheses apply to one rule is not allowed.
    Example:

        apply_rule_hyps(Rule([coll(A, B, C)], coll(A, C, B)), [coll(D, E, F), coll(P, Q, R), para(A, B, D, C)]
        ) -> [coll(D, F, E), coll(P, R, Q)].

    """

    assert isinstance(rule, Rule)
    assert isinstance(hyps, list)
    assert all(isinstance(fact, Fact) for fact in hyps)

    new_facts = []

    def traverse_hyps(len, n, seq):
        if n == 0:
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
            finally:
                return
        for i in range(len):
            if str(i) not in str(seq):
                 traverse_hyps(len, n - 1, str(seq) + str(i))

    traverse_hyps(len(hyps), len(rule.assums), "")
    return new_facts


def apply_ruleset_hyps(ruleset, hyps, only_updated=False):
    """Try to apply every rule in a ruleset to one or more facts in a list (as many as possible),
    return a list of new facts.
    Repetitive facts as hypotheses apply to one rule is not allowed.
    """
    assert isinstance(ruleset, dict)
    assert all(isinstance(rule, Rule) for _, rule in ruleset.items())

    new_facts = []
    for _, rule in ruleset.items():
        if only_updated:
            unique = [fact for fact in apply_rule_hyps(rule, hyps, only_updated=True) if fact not in new_facts]
        else:
            unique = [fact for fact in apply_rule_hyps(rule, hyps) if fact not in new_facts]

        new_facts.extend(unique)

    return new_facts


def search_fixpoint(ruleset, hyps, concl):
    """Recursively apply given ruleset to a list of hypotheses to obtain new facts.
    Recursion exits when a new fact is exactly the same as the given conclusion,
    or when new fact is not able to be generated. """

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
