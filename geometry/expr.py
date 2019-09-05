"""Expressions in geometry prover."""

import itertools, re, copy
from functools import reduce


POINT, LINE, PonL = range(3)

def arg_type(s):
    """Upper case means points, lower case means lines.
    The pattern {[A-Z](,[A-Z])*} represents a line with points on it need to be matched.
    """
    assert isinstance(s, str)
    if len(s) == 1:
        if s.isupper():
            return POINT
        elif s.islower():
            return LINE
    else:
        if re.match(r'{([A-Z])(, [A-Z])*}', s):
            return PonL
        else:
            raise NotImplementedError

class Fact:
    """Represent a fact in geometry prover, e.g.:

    coll(A, C, B) is Fact("coll", ["A", "C", "B"]).

    """
    def __init__(self, pred_name, args, *, updated=False, lemma=None, cond=None):
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

    def __repr__(self):
        return str(self)


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

    def __str__(self):
        return "Line(%s)" % (",".join(self.args))

    def __repr__(self):
        return str(self)

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


def get_line(lines, pair):
    """Returns a line from lines containing the given pair of points, if
    it exists. Otherwise return a line containing the pair.
    
    Examples:

    get_line([Line(P,Q,R)], (P, Q)) -> Line(P,Q,R)
    get_line([Line(P,Q,R)], (O, P)) -> Line(O,P)

    """
    assert isinstance(lines, list) and all(isinstance(line, Line) for line in lines)
    assert isinstance(pair, tuple) and len(pair) == 2 and all(isinstance(p, str) for p in pair)

    new_line = Line(list(pair))
    for line in lines:
        if line.is_same_line(new_line):
            return line

    return new_line


def match_expr(pat, f, inst, *, lines=None):
    """Match pattern with f, return a list of result(s).

        inst is a dictionary that assigns point variables to points,
        and line variables to pairs of points.

        lines: list of currently known lines.

        Multiple results will be generated if a line and two points on it need to be matched simultaneously.

        Example:

        match(coll(A, B, C), coll(P, Q, R), {}) -> {A: P, B: Q, C: R}.
        match(coll(A, B, C), coll(P, Q, R), {A: P}) -> {A: P, B: Q, C: R}.
        match(coll(A, B, C), coll(P, Q, R), {A: Q}) -> raise MatchException.
        match(coll(A, B, C), para(P, Q, R, S), {}) -> raise MatchException.

        match(perp(l, m), perp(P, Q, R, S), {}) -> {l: (P, Q), m: (R, S)}
        match(perp(l, m), perp(P, Q, R, S), {l: (Q, P)}) -> {l: (Q, P), m: (R, S)}
        match(perp(l, m), perp(P, Q, R, S), {l: (O, P)}, lines=[Line(O, P, Q)]) -> {l: (O, P), m: (R, S)}
        match(perp(l, m), perp(P, Q, R, S), {l: (O, P)}) -> raise MatchException.


        """
    assert isinstance(pat, Fact) and isinstance(f, Fact)
    if lines is None:
        lines = []
    else:
        assert isinstance(lines, list) and all(isinstance(line, Line) for line in lines)

    if pat.pred_name != f.pred_name:
        raise MatchException

    pos = 0
    new_insts = [inst]

    for p_arg in pat.args:
        insts = new_insts
        new_insts = []
        for inst in insts:
            if arg_type(p_arg) == POINT:
                if pos + 1 > len(f.args):
                    raise MatchException
                if p_arg in inst:
                    if f.args[pos] != inst[p_arg]:
                        raise MatchException
                else:
                    inst[p_arg] = f.args[pos]
            elif arg_type(p_arg) == LINE:
                if pos + 2 > len(f.args):
                    raise MatchException
                if p_arg in inst:
                    l1 = get_line(lines, inst[p_arg])
                    l2 = get_line(lines, (f.args[pos], f.args[pos + 1]))
                    if l1 != l2:
                        raise MatchException
                else:
                    inst[p_arg] = (f.args[pos], f.args[pos + 1])
            elif arg_type(p_arg) == PonL:
                a, b = [], []
                if pos + 2 > len(f.args):
                    raise MatchException
                groups = re.match(r'{([A-Z])(, [A-Z])*}', p_arg).groups()
                points = [groups[0]] + [i[2:] for i in groups[1:]]
                l2 = get_line(lines, (f.args[pos], f.args[pos + 1]))
                pts_in_inst = [point for point in points if point in inst]

                if len(pts_in_inst) == 2:
                    l1 = get_line(lines, (inst[pts_in_inst[0]], inst[pts_in_inst[1]]))
                    if l1 != l2:
                        raise MatchException
                    a, b = inst[points[0]], inst[points[1]]

                elif len(pts_in_inst) == 1:
                    pt_in_inst_pos = pos + groups.index(pts_in_inst[0])
                    if f.args[pt_in_inst_pos] != inst[pts_in_inst[0]]:
                        if len([point for point in points if point not in inst]) == 1:
                            a, b = inst[pts_in_inst[0]], l2.args
                    else:
                        raise NotImplementedError

                elif len(pts_in_inst) == 0:
                    a, b = l2.args, l2.args

                else:
                    raise NotImplementedError

                perms = [[x, y] for x in a for y in b if x != y]
                ds = []
                for perm in perms:
                    d = inst
                    for i in range(len(points)):
                        d[points[i]] = perm[i]
                    ds.append(copy.copy(d))
            else:
                raise NotImplementedError

            if isinstance(inst, list):
                new_insts.extend(ds)
            else:
                new_insts = insts

        if arg_type(p_arg) == POINT:
            pos += 1
        elif arg_type(p_arg) == PonL or arg_type(p_arg) == LINE:
            pos += 2

    return insts

def make_line_facts(facts):
    """Construct lines from a list of given facts. """
    assert isinstance(facts, list)
    assert all(isinstance(fact, Fact) for fact in facts)

    lines = []
    for fact in facts:
        if fact.pred_name == "coll":
            new_line = Line(fact.args)
            same = [inx for inx, _ in enumerate(lines) if new_line.is_same_line(lines[inx])]
            if len(same) > 0:
                lines[same[0]].extend_line(new_line)
            else:
                lines.append(new_line)
    length = 0
    while length != len(lines):
        length = len(lines)
        for line in lines:
            same = [inx for inx, _ in enumerate(lines) if line.is_same_line(lines[inx]) and line is not lines[inx]]
            if len(same) > 0:
                lines[same[0]].extend_line(line)
                lines.remove(line)

    return lines


def apply_rule(rule, facts, *, lines=None, record=False, lemma=None):
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
    assert len(facts) == len(rule.assums)

    inst = {}
    for assume, fact in zip(rule.assums, facts):
        match_expr(assume, fact, inst, lines=lines)

    concl_args = []
    for arg in rule.concl.args:
        if arg_type(arg) == POINT:
            concl_args.append(inst[arg])
        elif arg_type(arg) == LINE:
            concl_args.extend(inst[arg])
        else:
            raise NotImplementedError

    if record:
        return Fact(rule.concl.pred_name, concl_args, updated=True, lemma=lemma, cond=facts)
    else:
        return Fact(rule.concl.pred_name, concl_args)


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
    lines = make_line_facts(hyps)
    for seq in itertools.permutations(range(len(hyps)), len(rule.assums)):
        facts = []
        for num in list(seq):
            facts.append(hyps[int(num)])
        try:
            if only_updated:
                updated = [fact for fact in facts if fact.updated]
                if len(updated) > 0:
                    new_fact = apply_rule(rule, facts, lines=lines, record=True, lemma=list(seq))
            else:
                new_fact = apply_rule(rule, facts, lines=lines, record=True, lemma=list(seq))
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
