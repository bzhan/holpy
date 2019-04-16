# Author: Bohua Zhan

import os
import json

from kernel.type import TFun, hol_bool
from kernel.term import Term, Var, Const
from kernel.thm import Thm
from kernel import extension
from logic import basic
from logic import logic
from logic import induct
from logic.nat import natT, to_binary
from logic.conv import rewr_conv
from logic.proofterm import ProofTerm, ProofTermDeriv
from logic.logic_macro import apply_theorem, init_theorem
from prover import z3wrapper
from syntax import parser
from syntax import printer
from paraverifier import gcl


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
    def __init__(self, thy, name, vars, states, rules, invs):
        self.thy = thy
        self.name = name
        self.vars = vars
        self.states = states
        self.rules = rules
        self.invs = invs

        # var_map used in gcl library
        self.var_map = dict()
        for i, v in enumerate(self.vars):
            self.var_map[v] = i

        # state_map
        self.state_map = dict()
        for i, state in enumerate(self.states):
            self.state_map[state] = i

    def __str__(self):
        res = "Variables: " + ", ".join(v.name for v in self.vars) + "\n"

        res += "States: " + ", ".join(v.name for v in self.states) + "\n"

        res += "Number of rules: %d\n" % len(self.rules)
        for i, rule in enumerate(self.rules):
            _, guard, assigns = rule
            assigns_str = ", ".join("%s := %s" % (str(k), str(v)) for k, v in assigns.items())
            res += "%d: [%s] %s" % (i, printer.print_term(self.thy, guard), assigns_str) + "\n"

        res += "Number of invariants: %d\n" % len(self.invs)
        for i, inv in enumerate(self.invs):
            _, inv_term = inv
            res += "%d: %s" % (i, printer.print_term(self.thy, inv_term)) + "\n"

        return res

    def replace_states(self, t):
        """Replace states by their corresponding numbers."""
        if t in self.states:
            return to_binary(self.state_map[t])
        elif t.ty == Term.COMB:
            return self.replace_states(t.fun)(self.replace_states(t.arg))
        else:
            return t

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
                elif t.fun in assigns:
                    return assigns[t.fun](t.arg)
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
        goal = self.replace_states(goal)
        if z3wrapper.z3_loaded:
            ans = z3wrapper.solve(goal)
        else:
            ans = True
        return goal, ans

    def add_invariant(self):
        """Add the invariant for the system in GCL."""
        s = Var("s", gcl.stateT)
        invC = Const("inv", TFun(gcl.stateT, hol_bool))
        inv_rhs = logic.mk_conj(*[gcl.convert_term(self.var_map, s, t) for _, t in self.invs])
        prop = Term.mk_equals(invC(s), inv_rhs)

        exts = extension.TheoryExtension()
        exts.add_extension(extension.AxConstant("inv", TFun(gcl.stateT, hol_bool)))
        exts.add_extension(extension.Theorem("inv_def", Thm([], prop)))
        self.thy.unchecked_extend(exts)
        print(printer.print_extensions(self.thy, exts))

    def add_semantics(self):
        """Add the semantics of the system in GCL."""
        transC = Const("trans", TFun(gcl.stateT, gcl.stateT, hol_bool))
        s = Var("s", gcl.stateT)
        props = []
        for i, (_, guard, assign) in enumerate(self.rules):
            t = gcl.convert_term(self.var_map, s, guard)
            t2 = gcl.mk_assign(self.var_map, s, assign)
            props.append(("trans_rule" + str(i), Term.mk_implies(t, transC(s, t2))))

        exts = induct.add_induct_predicate("trans", TFun(gcl.stateT, gcl.stateT, hol_bool), props)
        self.thy.unchecked_extend(exts)
        print(printer.print_extensions(self.thy, exts))

    def get_proof(self):
        invC = Const("inv", TFun(gcl.stateT, hol_bool))
        transC = Const("trans", TFun(gcl.stateT, gcl.stateT, hol_bool))
        s1 = Var("s1", gcl.stateT)
        s2 = Var("s2", gcl.stateT)
        prop = Thm.mk_implies(invC(s1), transC(s1,s2), invC(s2))
        print(printer.print_thm(self.thy, prop))

        trans_pt = ProofTerm.assume(transC(s1,s2))
        print(printer.print_thm(self.thy, trans_pt.th))
        P = Term.mk_implies(invC(s1), invC(s2))
        ind_pt = init_theorem(self.thy, "trans_cases", inst={"a1": s1, "a2": s2, "P": P})
        print(printer.print_thm(self.thy, ind_pt.th))

        ind_As, ind_C = ind_pt.prop.strip_implies()
        for ind_A in ind_As[1:-1]:
            print("ind_A: ", printer.print_term(self.thy, ind_A))
            vars, As, C = logic.strip_all_implies(ind_A, ["s", "k"])
            for A in As:
                print("A: ", printer.print_term(self.thy, A))
            print("C: ", printer.print_term(self.thy, C))
            eq1 = ProofTerm.assume(As[0])
            eq2 = ProofTerm.assume(As[1])
            guard = ProofTerm.assume(As[2])
            inv_pre = ProofTerm.assume(As[3]).on_arg(self.thy, rewr_conv(eq1)) \
                                             .on_prop(self.thy, rewr_conv("inv_def"))
            C_goal = ProofTerm.assume(C).on_arg(self.thy, rewr_conv(eq2)) \
                                        .on_prop(self.thy, rewr_conv("inv_def"))
            for t in logic.strip_conj(inv_pre.prop):
                print("inv_pre: ", printer.print_term(self.thy, t))
            for t in logic.strip_conj(C_goal.prop):
                print("C_goal: ", printer.print_term(self.thy, t))


def load_system(filename):
    dn = os.path.dirname(os.path.realpath(__file__))
    with open(os.path.join(dn, 'examples/' + filename + '.json'), encoding='utf-8') as a:
        data = json.load(a)

    thy = basic.loadTheory('gcl')

    name = data['name']
    vars = []
    for nm, str_T in data['vars'].items():
        T = parser.parse_type(thy, str_T)
        vars.append(Var(nm, T))

    for i, nm in enumerate(data['states']):
        thy.add_term_sig(nm, natT)
        thy.add_theorem(nm + "_def", Thm.mk_equals(Const(nm, natT), to_binary(i)))

    states = [Const(nm, natT) for nm in data['states']]

    rules = []
    for rule in data['rules']:
        if isinstance(rule['var'], str):
            rule_var = Var(rule['var'], natT)
            ctxt = dict((v.name, v.T) for v in vars + [rule_var])
        else:
            assert isinstance(rule['var'], list)
            rule_var = [Var(nm, natT) for nm in rule['var']]
            ctxt = dict((v.name, v.T) for v in vars + rule_var)
        guard = parser.parse_term(thy, ctxt, rule['guard'])
        assign = dict()
        for k, v in rule['assign'].items():
            assign[parser.parse_term(thy, ctxt, k)] = parser.parse_term(thy, ctxt, v)
        rules.append((rule_var, guard, assign))

    invs = []
    for inv in data['invs']:
        inv_vars = [Var(nm, natT) for nm in inv['vars']]
        ctxt = dict((v.name, v.T) for v in vars + inv_vars)
        prop = parser.parse_term(thy, ctxt, inv['prop'])
        invs.append((inv_vars, prop))

    return ParaSystem(thy, name, vars, states, rules, invs)

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
