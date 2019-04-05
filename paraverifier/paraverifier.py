# Author: Bohua Zhan

import os
import json

from kernel.term import Term, Var
from logic import basic
from logic import logic
from logic.nat import natT
from prover import z3wrapper
from syntax import parser
from syntax import printer

thy = basic.loadTheory('function')


GUARD, PRE, INV = range(3)

def convert_hint_type(s):
    if s == "GUARD":
        return GUARD
    elif s == "PRE":
        return PRE
    elif s == "INV":
        return INV
    else:
        raise NotImplementedError

class ParaSystem():
    """Describes a parametrized system. The system consists of:

    name: name of the system.
    vars: list of variables.
    states: list of states, assumed to be distinct.
    rules: list of rules.
    invs: list of invariants.

    """
    def __init__(self, name, vars, states, rules, invs):
        self.name = name
        self.vars = vars
        self.states = states
        self.rules = rules
        self.invs = invs

    def __str__(self):
        res = "Variables: " + ", ".join(v.name for v in self.vars) + "\n"

        res += "States: " + ", ".join(v.name for v in self.states) + "\n"

        res += "Number of rules: %d\n" % len(self.rules)
        for i, rule in enumerate(self.rules):
            _, guard, assigns = rule
            assigns_str = ", ".join("%s := %s" % (str(k), str(v)) for k, v in assigns.items())
            res += "%d: [%s] %s" % (i, printer.print_term(thy, guard), assigns_str) + "\n"

        res += "Number of invariants: %d\n" % len(self.invs)
        for i, inv in enumerate(self.invs):
            _, inv_term = inv
            res += "%d: %s" % (i, printer.print_term(thy, inv_term)) + "\n"

        return res

    def get_subgoal(self, inv_id, rule_id, case_id, hint):
        """Obtain the subgoal for the given case and hint.

        inv_id: index of the invariant to be shown at the end of the
                transition.
        rule_id: index of the transition rule.
        case_id: index of the case. The cases are as follows:
            - 0 to n-1: parameter in rule equals i'th parameter in inv.
            - n: parameter in rule does not equal any parameter in inv.
        hint: either:
            - GUARD: invariant is implied by the guard.
            - PRE: invariant is implied by the same invariant in the
                   previous state.
            - INV, i, inst:
                Invariant is implied by the guard and a different
                invariant i in the previous state. inst is a list specifying
                how to instantiate the invariant.

        """
        rule_var, guard, assigns = self.rules[rule_id]
        inv_vars, inv = self.invs[inv_id]
        assert case_id >= 0 and case_id <= len(inv_vars), \
               "get_subgoal: unexpected case_id."

        # Obtain invariant on the updated state.
        def subst(t):
            if t.ty == Term.COMB and t.fun in self.vars and t.arg in inv_vars:
                # Substitution for a parameterized variable
                if case_id < len(inv_vars) and inv_vars[case_id] == t.arg and \
                   t.fun(rule_var) in assigns:
                    return assigns[t.fun(rule_var)]
                else:
                    return t
            elif t.ty == Term.VAR:
                # Substitution for a non-parameterized variable
                if t in assigns:
                    return assigns[t]
                else:
                    return t
            elif t.ty == Term.CONST:
                return t
            elif t.ty == Term.COMB:
                return subst(t.fun)(subst(t.arg))
            else:
                raise NotImplementedError

        inv_after = subst(inv)
        if hint == GUARD:
            return Term.mk_implies(guard, inv_after)
        elif hint == PRE:
            return Term.mk_implies(inv, inv_after)
        else:
            hint_ty, hint_inv_id, subst_vars = hint
            if hint_ty == INV:
                inv_vars, inv = self.invs[hint_inv_id]
                inv_var_nms = [v.name for v in inv_vars]
                subst = dict((nm, Var(subst_var, natT)) for nm, subst_var in zip(inv_var_nms, subst_vars))
                inv_subst = inv.subst(subst)
                return Term.mk_implies(inv_subst, guard, inv_after)

    def verify_subgoal(self, inv_id, rule_id, case_id, hint):
        """Verify the subgoal from the given hints.

        In addition to the assumptions given in get_subgoal, we need
        some additional assumptions, including distinctness of states.

        """
        goal = self.get_subgoal(inv_id, rule_id, case_id, hint)
        ans = z3wrapper.solve(goal, assums=[z3wrapper.distinct(self.states)])
        return goal, ans


def load_system(filename):
    dn = os.path.dirname(os.path.realpath(__file__))
    with open(os.path.join(dn, 'examples/' + filename + '.json'), encoding='utf-8') as a:
        data = json.load(a)

    name = data['name']
    vars = []
    for nm, str_T in data['vars'].items():
        T = parser.parse_type(thy, str_T)
        vars.append(Var(nm, T))

    states = [Var(nm, natT) for nm in data['states']]

    rules = []
    for rule in data['rules']:
        rule_var = Var(rule['var'], natT)
        ctxt = dict((v.name, v.T) for v in vars + states + [rule_var])
        guard = parser.parse_term(thy, ctxt, rule['guard'])
        assign = dict()
        for k, v in rule['assign'].items():
            assign[parser.parse_term(thy, ctxt, k)] = parser.parse_term(thy, ctxt, v)
        rules.append((rule_var, guard, assign))

    invs = []
    for inv in data['invs']:
        inv_vars = [Var(nm, natT) for nm in inv['vars']]
        ctxt = dict((v.name, v.T) for v in vars + states + inv_vars)
        prop = parser.parse_term(thy, ctxt, inv['prop'])
        invs.append((inv_vars, prop))

    return ParaSystem(name, vars, states, rules, invs)

def load_hints(filename):
    dn = os.path.dirname(os.path.realpath(__file__))
    with open(os.path.join(dn, 'examples/' + filename + '.txt'), encoding='utf-8') as a:
        lines = a.readlines()

    hints = []
    for line in lines:
        args = [s.strip() for s in line.split(",")]
        inv_id, rule_id, case_id = int(args[0]), int(args[1]), int(args[2])
        if len(args) == 4:
            hints.append((inv_id, rule_id, case_id, convert_hint_type(args[3])))
        else:
            hints.append((inv_id, rule_id, case_id, (convert_hint_type(args[3]), int(args[4]), args[5:])))

    return hints
