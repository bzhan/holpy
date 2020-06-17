import random, string
import collections
import functools
import operator
from integral.expr import *
from integral.parser import parse_expr
from integral import rules

a = Symbol('a', [CONST])
b = Symbol('b', [CONST])
x = Symbol('x', [VAR])
e = Symbol('e', [OP])
pat0 = b + a*x
pat1 = a * x + b
pat2 = a * x
pat3 = e ^ a
pat4 = a + x
pat5 = x + a

linear_pat = [pat0, pat1, pat2, pat4, pat5]


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
        if len(power_body) == 0:
            return integral
        is_linear = functools.reduce(lambda x,y:x or y, [match(power_body[0], pat) for pat in linear_pat])
        if len(power_body) == 1 and is_linear: 
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
            return Linearity().eval(rules.PolynomialDivision().eval(e))
        except NotImplementedError:
            return e

class Linearity(AlgorithmRule):
    """Algorithm rule (a),(b),(c) in Slagle's thesis.

    (a) Factor constant. ∫cg(v)dv = c∫g(v)dv  
    (b) Negate. ∫-g(v)dv = -∫g(v)dv
    (c) Decompose. ∫∑g(v)dv = ∑∫g(v)dv 
    
    """
    def eval(self, e):
        if not isinstance(e, Integral) or e.body.ty != OP:
            return e

        if e.body.op == "*":
            if e.body.args[0].is_constant() and e.body.args[1].is_constant():
                return e.body * Linearity().eval(Integral(e.var, e.lower, e.upper, Const(1)))
            elif e.body.args[0].is_constant():
                return e.body.args[0] * Linearity().eval(Integral(e.var, e.lower, e.upper, e.body.args[1]))
            elif e.body.args[1].is_constant():
                return e.body.args[1] * Linearity().eval(Integral(e.var, e.lower, e.upper, e.body.args[0]))
            else:
                return e
        elif e.body.op == "+":
            return Linearity().eval(Integral(e.var, e.lower, e.upper, e.body.args[0])) + Integral(e.var, e.lower, e.upper, e.body.args[1])
        
        elif e.body.op == "-": 
            if len(e.body.args) == 2:
                return Linearity().eval(Integral(e.var, e.lower, e.upper, e.body.args[0])) - Integral(e.var, e.lower, e.upper, e.body.args[1])
            else:
                return Op("-", Linearity().eval(Integral(e.var, e.lower, e.upper, e.body.args[0]))) 
        else:
            return e

class LinearSubstitution(AlgorithmRule):
    """Algorithm rule (d) in Slagle's thesis.

    Find linear expression in integral's sub functions. 
    If there is only one function and its body is linear,
    try to substitute the original variable by the function 
    linear body.
    """
    def eval(self, e):
        integrals = e.separate_integral()
        for i, _ in integrals:
            e = e.replace_trig(i, linear_substitution(i))
        return e


algorithm_rules = [
    Linearity,
    LinearSubstitution,
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
    y subterm corresponds to lowest depth expression after substitution.  

    """
    def eval(self, e):
        res = []

        all_subterms = e.body.normalize().nonlinear_subexpr()

        depth = 0
        try:
            for subexpr in all_subterms:
                r = rules.Substitution1(gen_rand_letter(e.var), subexpr).eval(e)
                res.append(r[0])

            return [sorted(res, key=lambda x:x.depth)[0]] if res else []
        except:
            return []

class HeuristicIntegrationByParts(HeuristicRule):
    """Heuristic rule (d) in Slagle's thesis.
    
    Find each factor h in the integral production, try find ∫hdv = H.
    And do integration by parts: ∫Gh dv = GH - ∫(dG/dv)H dv.

    Currently we implemented a naive strategy to find h: the ∫hdv can be
    solved by CommonIntegral rule after algorithm transformation.
    
    """
    def eval(self, e):
        if not isinstance(e, Integral):
            return e

        res = []
        
        factors = decompose_expr_factor(e.body.normalize())
        
        if len(factors) <= 1:
            return e
        
        for i in range(len(factors)):
            node = bfs(OrNode(Integral(e.var, e.lower, e.upper, factors[i])))
            if node.resolved:
                u = functools.reduce(operator.mul, factors[:i], Const(1)) * functools.reduce(operator.mul, factors[i+1:], Const(1))
                v = node.compute_value()
                res.append(rules.IntegrationByParts(u, v).eval(e))
        
        return res

class HeuristicElimQuadratic(HeuristicRule):
    """Heuristic rule (e) in Slagle's thesis.

    For quadratic subexpressions like a + b * x + c * x ^ 2,
    substitute x by y + b/2c, transform to a - b^2/4a + ay^2.
    
    The search for quadratic subexprs is not complete because of
    the non-standard normalization.

    """
    def eval(self, e):
        def find_abc(quad):
            """Find the value of a, b, c in a + b * x + c * x ^ 2."""
            quad = quad.normalize()
            if not (quad.args[0].ty == OP and quad.args[0].op in ("+","-")): # b*x +/- a*x^2
                if quad.args[0].ty == VAR: # x +/- a*x^2 
                    if quad.args[1].ty == OP and quad.args[1].op == "^": # x +/- x^2
                        return (Const(0), Const(1), Const(1)) if quad.op == "+" else (Const(0), Const(1), Const(-1))
                    else: # x +/- a * x^2
                        return (Const(0), Const(1), quad.args[1].args[0]) if quad.op == "+" else (Const(0), Const(1), -quad.args[1].args[0])
                else: # b*x + a*x^2
                    if quad.args[1].ty == OP and quad.args[1].op == "^": # b*x +/- x^2
                        return (Const(0), quad.args[0].args[0], Const(1)) if quad.op == "+" else (Const(0), quad.args[0].args[0], Const(-1))
                    else: # b* x +/- a * x^2
                        return (Const(0), quad.args[0].args[0], quad.args[1].args[0]) if quad.op == "+" else (Const(0), quad.args[0].args[0], -quad.args[1].args[0])
            else: # c +/- b*x +/- a * x ^ 2
                if quad.args[0].args[1].ty == VAR: # c +/- x +/- x^2
                    if quad.args[1].args[1] == Const(2): # c +/- x +/- x^2
                        return check(quad, (quad.args[0].args[0], Const(1), Const(1)))
                    else:# c + x + a*x^2
                        return check(quad, (quad.args[0].args[0], Const(1), quad.args[1].args[0])) 
                else:# c +/- b*x +/- a * x^2
                    if quad.args[1].args[1] == Const(2): # c +/- b*x +/- x^2
                        return check(quad, (quad.args[0].args[0], quad.args[0].args[1].args[0], Const(1))) 
                    else:
                        return check(quad, (quad.args[0].args[0], quad.args[0].args[1].args[0], quad.args[1].args[0]))

        def check(quad, t):
            """Input: quad is a expression in a +/- b * x +/- c * x ^ 2 form, 
                      t is (a, b, c) tuple
            
               Output: the quadratic expression's coefficient.
            """
            symbol = [quad.op, quad.args[0].op]
            if symbol == ["+", "+"]:
                return (t[0], t[1], t[2])
            elif symbol == ["-", "+"]:
                return (t[0], t[1], Op("-",t[2]).normalize())
            elif symbol == ["+", "-"]:
                return (t[0], Op("-",t[1]).normalize(), t[2])
            elif symbol == ["-", "-"]:
                return (t[0], Op("-",t[1]).normalize(), Op("-",t[2]).normalize())
            else:
                raise NotImplementedError

        x = Symbol('x', [VAR, FUN])
        a = Symbol('a', [CONST])
        b = Symbol('b', [CONST])
        c = Symbol('c', [CONST])
        quadratic_patterns = [
            x + (x^Const(2)),
            x - (x^Const(2)),
            x + a * (x^Const(2)),
            x - a * (x^Const(2)),
            b * x + a * (x^Const(2)),
            b * x - a * (x^Const(2)),
            c + x + (x^Const(2)),
            c + x - (x^Const(2)),
            c - x + (x^Const(2)),
            c - x - (x^Const(2)),
            c + x + a * (x^Const(2)),
            c + x - a * (x^Const(2)),
            c - x + a * (x^Const(2)),
            c - x - a * (x^Const(2)),
            c + b*x + (x^Const(2)),
            c + b*x - (x^Const(2)),
            c - b*x + (x^Const(2)),
            c - b*x - (x^Const(2)),
            c + b * x + a*(x^Const(2)),
            c + b * x - a*(x^Const(2)),
            c - b * x + a*(x^Const(2)),
            c - b * x - a*(x^Const(2))
        ]
        
        quadratic_terms = []
        for p in quadratic_patterns:
            quadratic_terms.append((find_pattern1(e.body, p), p))

        quadratics = [(l[0][i], l[1]) for l in quadratic_terms for i in range(len(l[0]))]
        res = []

        for quad, _ in quadratics:
            a, b, c = find_abc(quad)
            new_integral, _ = rules.Substitution1(gen_rand_letter(e.var), Var(e.var) + (b/(Const(2)*c))).eval(e)
            new_integral.body = new_integral.body.expand().normalize()
            res.append(new_integral)

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

    def compute_value(self):
        if not self.resolved or len(self.children) == 0:
            return self.root
        else:
            for c in self.children:
                if c.resolved:
                    return c.compute_value()

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

    def compute_value(self):
        if not self.resolved:
            return self.root
        if len(self.children) == 0:
            return self.root.normalize()
        else:
            for c in self.children:
                self.root = self.root.replace_trig(c.root, c.compute_value())
                
            return self.root.normalize()


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
