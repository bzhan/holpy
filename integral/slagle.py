import random, string
import collections

from integral.expr import *
from integral.parser import parse_expr
from integral import rules

a = Symbol('a', [CONST])
b = Symbol('b', [CONST])
x = Symbol('x', [VAR])
e = Symbol('e', [OP])
pat1 = a * x + b
pat2 = a * x
pat3 = e ^ a

def gen_rand_letter(ex):
    return random.choices(string.ascii_lowercase.replace(ex, ''))[0]

def linearize(integral):
    """integral is an Expr."""
    return rules.Linearity().eval(integral)

def substitution(integral, subst):
    new_var = gen_rand_letter(integral.var)
    return rules.Substitution1(new_var, subst).eval(integral)[0]

def linear_substitution(integral):
    assert isinstance(integral, Integral), "%s Should be an integral." % (integral)
    func_body = collect_spec_expr(integral.body, Symbol('f', [FUN]))
    if len(func_body) == 1 and (match(func_body[0], pat1) or match(func_body[0], pat2)): 
        return linearize(substitution(integral, func_body[0]).normalize())
    elif len(func_body) == 0:
        power_body = collect_spec_expr(integral.body, pat3)
        if len(power_body) == 1 and (match(power_body[0], pat1) or match(power_body[0], pat2)): 
            return linearize(substitution(integral, power_body[0]))
        else:
            return integral
    else:
        return integral

def algo_trans(integral):
    assert isinstance(integral, Integral), "%s Should be an integral.l"
    integral = integral.normalize()
    return linear_substitution(linearize(integral))


class AlgorithmRule:
    def eval(self, e):
        """Algorithmic transformation of e.

        Parameters:
        e: original integral.

        Returns:
        If succeed, returns the new integral. Otherwise return e.

        """
        pass

class HeuristicRule:
    def eval(self, e):
        """Heuristic transformation of e.

        Parameters:
        e: original integral.

        Returns:
        A list of possible new integrals. Each of which should equal e.

        """
        pass


class CommonIntegral(AlgorithmRule):
    """Evaluate common integrals."""

    def eval(self, e):
        return rules.OnSubterm(rules.CommonIntegral()).eval(e)


class DividePolynomial(AlgorithmRule):
    """Algorithm rule (g) in Slagle's thesis.

    If the integral is in the form f(x)/g(x), attempt to divide f(x)
    by g(x).

    """
    def eval(self, e):
        try:
            return rules.Linearity().eval(rules.PolynomialDivision().eval(e))
        except NotImplementedError:
            return e

algorithm_rules = [
    CommonIntegral,
    DividePolynomial
]

class TrigFunction(HeuristicRule):
    """Heuristic rule (a) in Slagle's thesis.
    
    There are three options:
    1) Transform to sine and cosine.
    2) Transform to tangent and secant.
    3) Transform to cotangent and cosecant.

    """
    def eval(self, e):
        res = []

        subst_res = rules.TrigSubstitution().eval(e, rule_list=[TR2i])
        for expr, rule in subst_res:

            if rule != 'Unchanged' and expr not in res:
                res.append(expr)

        return res

class HeuristicSubstitution(HeuristicRule):
    """Heuristic rule (c) in Slagle's thesis.

    Currently we implement a naive strategy of substitution for
    each of the subterms.

    """
    def eval(self, e):
        res = []

        all_subterms = e.body.nonlinear_subexpr()

        if len(all_subterms) != 1:
            return []

        for subexpr in all_subterms:
            r = rules.Substitution1('y', subexpr).eval(e)
            res.append(r[0])

        return res

heuristic_rules = [
    TrigFunction,
    HeuristicSubstitution
]


class GoalNode:
    pass


class OrNode(GoalNode):
    """OR relationship in Slagle's thesis.
    
    To evaluate the integral at the root, only need to evaluate one of the
    child nodes. Each of the child nodes is a GoalNode.

    """
    def __init__(self, root, parent=None):
        if isinstance(root, str):
            root = parse_expr(root)

        self.root = root
        self.parent = parent
        self.children = []
        self.resolved = False

    def __str__(self):
        if len(self.children) == 0:
            return 'OrNode(%s,%s,[])' % (str(self.root), str(self.resolved))

        s = 'OrNode(%s,%s,[\n' % (str(self.root), str(self.resolved))
        for c in self.children:
            str_c = str(c)
            for line in str_c.splitlines():
                s += '  %s\n' % line
        s += ']'
        return s

    def expand(self):
        """Expand the current node.

        This tries all algorithm rules. If the result is itself an integral, then
        apply each of the heuristic rules and collect the results. If the
        result is a linear combination of integrals, then put a single AndNode
        as the child nodes.

        """
        cur_integral = self.root
        for rule in algorithm_rules:
            cur_integral = rule().eval(cur_integral)

        if cur_integral.ty == INTEGRAL:
            # Single integral case
            for rule in heuristic_rules:
                res = rule().eval(cur_integral)
                for r in res:
                    if r == cur_integral:
                        continue
                    if r.ty == INTEGRAL:
                        self.children.append(OrNode(r, parent=self))
                    else:
                        self.children.append(AndNode(r, parent=self))
        
        else:
            # Linear combination of integrals
            self.children.append(AndNode(cur_integral, parent=self))

        self.compute_resolved()

    def compute_resolved(self):
        self.resolved = any(c.resolved for c in self.children)
        if self.resolved and self.parent is not None:
            self.parent.compute_resolved()


class AndNode(GoalNode):
    """AND relationship in Slagle's thesis.

    To evaluate the integral at the root, need to evaluate all of the child
    nodes. In our case, the root is necessarily a sum (or difference) of
    integrals, and the child nodes are the individual integrals.

    """
    def __init__(self, root, parent=None):
        if isinstance(root, str):
            root = parse_expr(root)

        self.root = root
        self.parent = parent
        self.children = [OrNode(r, parent=self) for r, _ in root.separate_integral()]
        self.resolved = (len(self.children) == 0)
        if self.resolved:
            self.parent.compute_resolved()

    def __str__(self):
        if len(self.children) == 0:
            return 'AndNode(%s,%s,[])' % (str(self.root), str(self.resolved))

        s = 'AndNode(%s,%s,[\n' % (str(self.root), str(self.resolved))
        for c in self.children:
            str_c = str(c)
            for line in str_c.splitlines():
                s += '  %s\n' % line
        s += ']'
        return s

    def compute_resolved(self):
        self.resolved = all(c.resolved for c in self.children)
        if self.resolved and self.parent is not None:
            self.parent.compute_resolved()


def bfs(node):
    q = collections.deque()

    q.append(node)
    while q and not node.resolved:
        n = q.popleft()
        if isinstance(n, OrNode):
            n.expand()
        for c in n.children:
            q.append(c)

    return node
