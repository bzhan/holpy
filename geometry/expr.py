"""Expressions in geometry prover."""

import itertools, copy

POINT, LINE, PonL, SEG, TRI, CIRC = range(6)

def get_arg_type_by_fact(fact):
    """Obtain the type of given argument by a given pred_name of a fact.
    Return a list of types.
    """
    pred_name = fact.pred_name
    arg_len = len(fact.args)

    if pred_name in ("para", "perp", "eqangle"):
        types = []
        idx = 0
        while idx < len(fact.args):
            if fact.args[idx].isupper():
                assert fact.args[idx + 1].isupper()
                types.append(PonL)
                idx += 2
            elif fact.args[idx].islower():
                idx += 1
                types.append(LINE)
            else:
                raise NotImplementedError
    else:
        assert all(arg.isupper() for arg in fact.args)
        if pred_name == "coll":
            types = [POINT for _ in range(arg_len)]
        elif pred_name == "eqratio" or pred_name == "cong":
            types = [SEG] * int(arg_len / 2)
        elif pred_name == "midp":
            types = [POINT, POINT, POINT]
        elif pred_name == "cyclic":
            types = [CIRC for _ in range(arg_len)]
        elif pred_name == "simtri":
            types = [TRI] * int(arg_len / 3)
        elif pred_name == "circle":
            types = [CIRC for _ in range(arg_len)]
        else:
            raise NotImplementedError

    return types


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

    def combine(self, other):
        # If the other line refers to the same line of this line,
        # add the points of other line that are not in this line.
        if self.is_same_line(other):
            if self.args != other.args:
                self.args = self.args.union(other.args)

    def extend(self, args):
        assert all(isinstance(arg, str) for arg in args)
        self.args.update(args)


class Circle:
    """Represent a circle.
    """

    def __init__(self, args, center=None, source=None):
        assert isinstance(args, list)
        assert len(args) >= 3
        assert all(isinstance(arg, str) for arg in args)
        self.args = set(args)
        self.source = source
        self.center = center

    def __hash__(self):
        return hash(("circle", self.center, tuple(sorted(self.args))))

    def __eq__(self, other):
        if self.center and other.center:
            if self.center != other.center:
                return False
        return isinstance(other, Circle) and self.args == other.args

    def __str__(self):
        return "Circle(%s,%s)" % (self.center, ",".join(self.args))

    def __repr__(self):
        return str(self)

    def is_same_circle(self, other):
        """Two circles are the same if they have 3 or more identical points.
        If both circles have center and they have 3 or more identical points
        then two centers must be the same.
        """
        if isinstance(other, Circle) and len(self.args.intersection(other.args)) >= 3:
            if self.center and other.center:
                if self.center == other.center:
                    return True
                return False
            return True
        return False

    def combine(self, other):
        # If the other circle refers to the same as this circle,
        # add the points of other circle that are not in this circle.
        if self.is_same_circle(other):
            if self.args != other.args:
                self.args = self.args.union(other.args)
            if other.center and not self.center:
                self.center = other.center

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


def get_circle(circles, points, center=None):
    """Return a circle from circles containing the given points and center (optional),
    if it exists. Otherwise return a circle containing the points and center (optional).
    """
    assert isinstance(circles, list) and all(isinstance(circle, Circle) for circle in circles)
    assert isinstance(points, list) and len(points) >= 3 and all(isinstance(p, str) for p in points)
    if center:
        assert isinstance(center, str)

    new_circle = Circle(points, center=center)

    for circle in circles:
        if new_circle.is_same_circle(circle):
            return circle

    centers = [circle.center for circle in circles]
    assert center not in centers
    return new_circle


def match_expr(pat, f, inst, *, lines=None, circles=None):
    """Match pattern with f, return a list of result(s).

    inst is a dictionary that assigns point variables to points,
    and line variables to pairs of points.

    lines: list of currently known lines.

    Multiple results will be generated if a line and two points on it
    need to be matched simultaneously.

    Example:

    match(coll(A, B, C), coll(P, Q, R), {}) -> [{A: P, B: Q, C: R}].
    match(coll(A, B, C), coll(P, Q, R), {A: P}) -> [{A: P, B: Q, C: R}].
    match(coll(A, B, C), coll(P, Q, R), {A: Q}) -> [].
    match(coll(A, B, C), para(P, Q, R, S), {}) -> [].

    match(perp(l, m), perp(P, Q, R, S), {}) -> [{l: (P, Q), m: (R, S)}]
    match(perp(l, m), perp(P, Q, R, S), {l: (Q, P)}) -> [{l: (Q, P), m: (R, S)}]
    match(perp(l, m), perp(P, Q, R, S), {l: (O, P)}, lines=[Line(O, P, Q)]) -> [{l: (O, P), m: (R, S)}]
    match(perp(l, m), perp(P, Q, R, S), {l: (O, P)}) -> [].

    """
    assert isinstance(pat, Fact) and isinstance(f, Fact)
    if lines is None:
        lines = []
    else:
        assert isinstance(lines, list) and all(isinstance(line, Line) for line in lines)

    if pat.pred_name != f.pred_name:
        return []

    pat_pos = 0  # Current position in pattern
    pos = 0  # Current position in fact

    insts = [inst]
    arg_types = get_arg_type_by_fact(pat)  # Get types of every argument.

    for arg_ty in arg_types:
        new_insts = []
        for inst in insts:
            if arg_ty == POINT:
                if pos + 1 > len(f.args):
                    continue
                p_arg = pat.args[pat_pos]
                if p_arg in inst:
                    if f.args[pos] == inst[p_arg]:
                        new_insts.append(inst)
                elif f.args[pos] not in inst.values():
                    inst[p_arg] = f.args[pos]
                    new_insts.append(inst)

            elif arg_ty == LINE:
                if pos + 2 > len(f.args):
                    continue
                p_arg = pat.args[pat_pos]
                if p_arg in inst:
                    l1 = get_line(lines, inst[p_arg])
                    l2 = get_line(lines, (f.args[pos], f.args[pos + 1]))
                    if l1 == l2:
                        new_insts.append(inst)
                else:
                    inst[p_arg] = (f.args[pos], f.args[pos + 1])
                    new_insts.append(inst)

            elif arg_ty == CIRC:
                if pos > 0:
                    new_insts.append(inst)
                else:
                    if f.pred_name == "circle":
                        c = get_circle(circles, f.args[1:], f.args[0])
                        error = False
                        if pat.args[0] in inst:
                            if f.args[0] != inst[pat.args[0]]:
                                error = True
                        else:
                            inst[pat.args[0]] = f.args[0]
                        del f.args[0]
                        del pat.args[0]

                    else:
                        c = get_circle(circles, f.args)
                        error = False

                    fixed = []  # arguments in pattern that are also in inst.
                    same_args = list(set(pat.args).intersection(set(inst.keys())))
                    for same_arg in same_args:
                        if inst[same_arg] in c.args:
                            fixed.append(same_arg)
                        else:
                            error = True

                    # for_comb = list(c.args - set([inst[i] for i in fixed]))
                    for_comb = list(c.args - set(inst.values()))
                    if not error:
                        if len(f.args) - len(fixed) > 0:
                            # Order is not considered.
                            # TODO: To decide generate more possibilities or not.
                            comb = list(itertools.combinations(sorted(for_comb),
                                                               len(f.args) - len(fixed)))  # For more than one insts.
                            # comb = [sorted(for_comb)[0:len(f.args) - len(fixed)]]  # Only generate one inst.
                            for item in comb:
                                p = 0
                                for i in range(len(pat.args)):
                                    if pat.args[pos + i] in fixed:
                                        continue
                                    inst[pat.args[pos + i]] = item[p]
                                    p += 1
                                new_insts.append(copy.copy(inst))
                        else:
                            new_insts.append(inst)


            elif arg_ty == PonL:
                if pos + 2 > len(f.args):
                    continue

                # Target line
                l2 = get_line(lines, (f.args[pos], f.args[pos + 1]))

                pat_a, pat_b = pat.args[pat_pos:pat_pos + 2]

                # Obtain possible choices for a and b
                if pat_a in inst:
                    if inst[pat_a] in l2.args:
                        a = [inst[pat_a]]
                    else:
                        a = []
                else:
                    a = sorted(list(l2.args))

                if pat_b in inst:
                    if inst[pat_b] in l2.args:
                        b = [inst[pat_b]]
                    else:
                        b = []
                else:
                    b = sorted(list(l2.args))

                # Permutations of pairs of a and b.
                perms = [[x, y] for x in a for y in b if x != y]
                for a, b in perms:
                    inst[pat_a] = a
                    inst[pat_b] = b
                    new_insts.append(copy.copy(inst))

            elif arg_ty == SEG:
                # Two endpoints of a segment can be exchanged when matching.
                if pos + 2 > len(f.args):
                    continue

                pat_a, pat_b = pat.args[pat_pos:pat_pos + 2]

                def f_not_in_inst(pat, arg):
                    if pat not in inst:
                        if arg not in inst.values():
                            return True
                        return False
                    return False

                def same_value(pat, arg):
                    if pat in inst:
                        if inst[pat] == arg:
                            return True
                        return False
                    return False

                if (f_not_in_inst(pat_a, f.args[pos]) or same_value(pat_a, f.args[pos])) and \
                        (f_not_in_inst(pat_b, f.args[pos + 1]) or same_value(pat_b, f.args[pos + 1])):
                    new_inst = copy.copy(inst)
                    new_inst[pat_a] = f.args[pos]
                    new_inst[pat_b] = f.args[pos + 1]
                    new_insts.append(new_inst)

                if (f_not_in_inst(pat_a, f.args[pos + 1]) or same_value(pat_a, f.args[pos + 1])) and \
                        (f_not_in_inst(pat_b, f.args[pos]) or same_value(pat_b, f.args[pos])):
                    new_inst = copy.copy(inst)
                    new_inst[pat_a] = f.args[pos + 1]
                    new_inst[pat_b] = f.args[pos]
                    new_insts.append(new_inst)


            # TODO: Support more types.
            elif arg_ty == TRI:
                raise NotImplementedError

            else:
                raise NotImplementedError

        if arg_ty == POINT:
            pos += 1
            pat_pos += 1
        elif arg_ty == LINE:
            pos += 2
            pat_pos += 1
        elif arg_ty == PonL or arg_ty == SEG:
            pos += 2
            pat_pos += 2
        elif arg_ty == TRI:
            pos += 3
            pat_pos += 1
        elif arg_ty == CIRC:
            pos += len(pat.args)
            pat_pos += len(pat.args)

        insts = new_insts

    return insts


def make_new_lines(facts, lines):
    """Construct new lines from a list of given facts.

    The arguments of collinear facts will be used to construct new lines.
    Points in a new line will be merged into one of given lines,
    if the new line and the given line is the same line.
    The given list of lines will be updated.

    """
    assert isinstance(facts, list)
    assert all(isinstance(fact, Fact) for fact in facts)
    assert isinstance(lines, list)
    assert all(isinstance(line, Line) for line in lines)

    for fact in facts:
        if fact.pred_name == "coll":
            new_line = Line(fact.args)
            same = [inx for inx, _ in enumerate(lines) if new_line.is_same_line(lines[inx])]
            if len(same) >= 1:
                lines[same[0]].combine(new_line)
            elif len(same) == 0:
                lines.append(new_line)

    # Combine pairs of lines in the list that can be combined (if any).
    length = 0
    while length != len(lines):
        length = len(lines)
        for line in lines:
            same = [inx for inx, _ in enumerate(lines) if line.is_same_line(lines[inx]) and line is not lines[inx]]
            if len(same) > 0:
                lines[same[0]].combine(line)
                lines.remove(line)


def make_new_circles(facts, circles):
    """
    Construct new circles from a list of given facts.
    The arguments of cyclic and circle facts will be used to construct new circles.
    Points in a new line will be merged into one of given circles,
    if the new circle and the given circle is the same circle.
    The given list of circles will be updated.
    """
    assert isinstance(facts, list) and all(isinstance(fact, Fact) for fact in facts)
    assert isinstance(circles, list) and all(isinstance(circle, Circle) for circle in circles)

    for fact in facts:
        if fact.pred_name in ("cyclic", "circle"):
            if fact.pred_name == "cyclic":
                new_circle = Circle(fact.args)
            if fact.pred_name == "circle":
                new_circle = Circle(fact.args[1:], center=fact.args[0])
            same = [inx for inx, _ in enumerate(circles) if new_circle.is_same_circle(circles[inx])]
            if len(same) >= 1:
                circles[same[0]].combine(new_circle)
            elif len(same) == 0:
                circles.append(new_circle)

    # Combine pairs of circles in the list that can be combined (if any).
    length = 0
    while length != len(circles):
        length = len(circles)
        for circle in circles:
            same = [inx for inx, _ in enumerate(circles) if circle.is_same_circle(circles[inx]) and circle is not circles[inx]]
            if len(same) > 0:
                circles[same[0]].combine(circle)
                circles.remove(circle)


def get_short_facts(fact):
    """
    If a given fact has two or more arguments,
    return a list of shorter facts that can be deduced from this fact with given quantity of arguments.
    Notice: Different sequences of arguments in a shorter fact are not considered.
            Some rules in ruleset will handle this.
    Only fact has enough arguments and has pred_name of para, eqangle, cong, eqratio or simtri take effect.
    A list with all short facts will be returned. Otherwise, return a list only has the given fact.
    """

    def get_short_args(args, length):
        arranged = []
        idx = 0
        while idx < len(args):
            arranged.append(args[idx:idx + length])
            idx += length
        return arranged

    def args_to_facts(arranged):
        short_args = itertools.combinations(arranged, 2)
        short_args = [list(itertools.chain.from_iterable(short_arg)) for short_arg in short_args]
        short_facts = [Fact(fact.pred_name, short_arg, updated=fact.updated, lemma=fact.lemma, cond=fact.cond)
                       for short_arg in short_args]
        return short_facts

    pred_name = fact.pred_name
    if pred_name == "para":
        if len(fact.args) == 2:
            return fact
        arranged = []
        idx = 0
        while idx < len(fact.args):
            if fact.args[idx].isupper():
                assert fact.args[idx + 1].isupper()
                arranged.append([fact.args[idx], fact.args[idx + 1]])
                idx += 2
            elif fact.args[idx].islower():
                arranged.append(fact.args[idx])
                idx += 1
        return args_to_facts(arranged)
    if pred_name == "eqangle" and pred_name == "eqratio":
        assert len(fact.args) % 4 == 0
        if len(fact.args) == 8:
            return [fact]
        return args_to_facts(get_short_args(fact.args, 4))
    elif pred_name == "simtri":
        assert len(fact.args) % 3 == 0
        if len(fact.args) == 6:
            return [fact]
        return args_to_facts(get_short_args(fact.args, 3))
    elif pred_name == "cong":
        assert len(fact.args) % 2 == 0
        if len(fact.args) == 4:
            return [fact]
        return args_to_facts(get_short_args(fact.args, 2))
    else:
        return [fact]


def apply_rule(rule, facts, *, lines=None, record=False, circles=None):
    """Apply given rule to the list of facts, returns a list of new
    facts that can be derived from the rule.

    record: whether to record application of the rule in the new fact.

    Example:

    apply_rule(
        Rule([para(A, B, C, D), para(C, D, E, F)], para(A, B, E, F)),
             [para(P, Q, R, S), para(R, S, U, V)])
    -> para(P, Q, U, V).

    apply_rule(
        Rule([coll(A, B, C)], coll(A, C, B)),
             [para(A, B, D, C)])
    -> [].

    """
    assert isinstance(rule, Rule)
    assert isinstance(facts, list) and all(isinstance(fact, Fact) for fact in facts)
    assert len(facts) == len(rule.assums)

    insts = [dict()]
    for assume, fact in zip(rule.assums, facts):
        new_insts = []
        for inst in insts:
            new_insts.extend(match_expr(assume, fact, inst, lines=lines, circles=circles))
        insts = new_insts

    new_facts = []
    arg_types = get_arg_type_by_fact(rule.concl)
    for inst in insts:
        concl_args = []
        pat_pos = 0
        for arg_type in arg_types:
            if arg_type == POINT:
                arg = rule.concl.args[pat_pos]
                pat_pos += 1
                concl_args.append(inst[arg])
            elif arg_type == LINE:
                arg = rule.concl.args[pat_pos]
                pat_pos += 1
                concl_args.extend(inst[arg])
            elif arg_type == PonL or arg_type == SEG:
                arg1, arg2 = rule.concl.args[pat_pos:pat_pos + 2]
                pat_pos += 2
                concl_args.extend([inst[arg1], inst[arg2]])
            elif arg_type == CIRC:
                arg = rule.concl.args[pat_pos]
                pat_pos += 1
                concl_args.append(inst[arg])
            else:
                # TODO: Support more types.
                raise NotImplementedError

        if record:
            new_facts.append(Fact(rule.concl.pred_name, concl_args, updated=True, lemma=rule, cond=facts))
        else:
            new_facts.append(Fact(rule.concl.pred_name, concl_args))
    return new_facts


def apply_rule_hyps(rule, hyps, only_updated=False, lines=None, circles=None):
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

        if only_updated:
            updated = [fact for fact in facts if fact.updated]
            if len(updated) > 0:
                new_facts.extend(apply_rule(rule, facts, lines=lines, circles=circles, record=True))
        else:
            new_facts.extend(apply_rule(rule, facts, lines=lines, circles=circles, record=True))
    return new_facts


def apply_ruleset_hyps(ruleset, hyps, only_updated=False, lines=None, circles=None):
    """Try to apply every rule in a ruleset to one or more fact
    in a list (as many as possible), return a list of new facts.

    Repetitive facts as hypotheses apply to one rule is not allowed.

    """
    assert isinstance(ruleset, dict)
    assert all(isinstance(rule, Rule) and isinstance(name, str) for name, rule in ruleset.items())

    new_facts = []
    for _, rule in ruleset.items():
        if only_updated:
            unique = [fact for fact in apply_rule_hyps(rule, hyps, only_updated=True, lines=lines, circles=circles)
                      if fact not in new_facts]
        else:
            unique = [fact for fact in apply_rule_hyps(rule, hyps, lines=lines, circles=circles)
                      if fact not in new_facts]

        new_facts.extend(unique)

    return new_facts


def search_step(ruleset, hyps, only_updated=False, lines=None, circles=None):
    """One step of searching fixpoint.

    Apply given ruleset to a list of hypotheses to obtain new facts.
    If collinear facts are included in hypotheses, new lines can be
    automatically generated, these new lines might be used when
    applying rules to hypotheses.

    """
    # Update the list of lines.
    make_new_lines(hyps, lines)
    make_new_circles(hyps, circles)

    if only_updated:
        new_facts = apply_ruleset_hyps(ruleset, hyps, only_updated=True, lines=lines, circles=circles)
    else:
        new_facts = apply_ruleset_hyps(ruleset, hyps, lines=lines, circles=circles)

    # Update the list of facts.
    for new_fact in new_facts:
        if new_fact not in hyps:
            hyps.append(new_fact)


def search_fixpoint(ruleset, hyps, lines, circles, concl):
    """Recursively apply given ruleset to a list of hypotheses to
    obtain new facts. Recursion exits when new fact is not able
    to be generated, or conclusion is in the list of facts.
    Return the list of facts.
    """

    # Any fact in original hypotheses might be used for the first step.
    short = [get_short_facts(hyp) for hyp in hyps]
    hyps = []
    for item in short:
        hyps.extend(item)
    search_step(ruleset, hyps, lines=lines, circles=circles)
    prev_hyps = []
    prev_lines = []
    prev_circles = []

    while hyps != prev_hyps or lines != prev_lines or circles != prev_circles:
        search_step(ruleset, hyps, only_updated=True, lines=lines, circles=circles)

        if concl in hyps:
            break

        prev_hyps = copy.copy(hyps)
        prev_lines = copy.copy(lines)
        prev_circles = copy.copy(circles)

    return hyps


def match_goal(fact, goal, lines, circles):
    """Given a fact and a goal, determine whether the fact directly
    implies the goal.

    """
    if fact.pred_name != goal.pred_name:
        return False

    if fact.pred_name in ('para', 'perp'):
        # For para and perp, it is only necessary for the lines
        # containing the first two points and the last two points
        # be the same.
        A, B, C, D = fact.args
        P, Q, R, S = goal.args
        return get_line(lines, (A, B)) == get_line(lines, (P, Q)) and \
               get_line(lines, (C, D)) == get_line(lines, (R, S))
    elif fact.pred_name in ('eqangle'):
        # For eqangle, check each angle with two lines respectively.
        A, B, C, D, E, F, G, H = fact.args
        P, Q, R, S, T, U, V, W = goal.args
        return get_line(lines, (A, B)) == get_line(lines, (P, Q)) and \
               get_line(lines, (C, D)) == get_line(lines, (R, S)) and \
               get_line(lines, (E, F)) == get_line(lines, (T, U)) and \
               get_line(lines, (G, H)) == get_line(lines, (V, W))
    elif fact.pred_name in ('cong'):
        # For congruent segments, check if both fact and goal refers to
        # the same set of segments.
        A, B, C, D = fact.args
        P, Q, R, S = goal.args
        return (A == P and B == Q and C == R and D == S) or \
               (A == R and B == S and C == P and D == Q)
    elif fact.pred_name in ('cyclic'):
        return get_circle(circles, fact.args) == get_circle(circles, goal.args)
    elif fact.pred_name in ('circle'):
        return get_circle(circles, fact.args[1:], center=fact.args[0]) == \
               get_circle(circles, goal.args[1:], center=goal.args[0])

    else:
        # TODO: make other cases more precise.
        return fact.args == goal.args


def find_goal(facts, goal, lines, circles):
    """Tries to find the goal among a list of facts. Return the
    fact if it is found. Otherwise return None.

    """
    for fact in facts:
        if match_goal(fact, goal, lines, circles):
            return fact

    return None


def rewrite_fact(fact):
    """Generate more explicit form of given fact in terms of printing (if possible). """
    if fact.pred_name == "eqangle":
        return "∠[" + fact.args[0] + fact.args[1] + "," + fact.args[2] + fact.args[3] + "]" + " = ∠[" \
               + fact.args[4] + fact.args[5] + "," + fact.args[6] + fact.args[7] + "]"
    else:
        return str(fact)


def print_search(ruleset, facts, concl):
    """Print the process of searching fixpoint.

    The given list of facts must contains all the deduce procedures
    (as parameters of facts in the list). Using a given ruleset to
    find out the name of rules used in deduce procedures.
    
    """

    def print_step(fact):
        r = list(ruleset.keys())[list(ruleset.values()).index(fact.lemma)]
        s = "(" + str(r) + ") " + rewrite_fact(fact) + " :- "
        for sub_fact in fact.cond:
            if sub_fact.updated:
                s = s + rewrite_fact(sub_fact) + ", "
                print_step(sub_fact)
            else:
                s = s + "(hyp)" + rewrite_fact(sub_fact) + ", "
        print(s[:-2])

    concl_in_facts = [fact for fact in facts if fact == concl][0]
    print_step(concl_in_facts)
