# Author: Bohua Zhan

import unittest
import io
import json

from kernel.type import TVar, TFun, boolT
from kernel.term import Term, Var, Const
from kernel.thm import Thm
from kernel import theory
from kernel.report import ProofReport
from logic import logic
from logic import basic
from data import nat
from data import list
from data import function
from syntax import parser
from syntax import printer
from syntax.context import Context
from server import tactic, method, server
from server.server import ProofState
from imperative import imp

thy = basic.load_theory('logic_base')

A = Var("A", boolT)
B = Var("B", boolT)
conj = logic.mk_conj
disj = logic.mk_disj
imp = Term.mk_implies
neg = logic.neg
exists = logic.mk_exists

def testMethods(self, thy_name, thm_name, *, no_gaps=True, print_proof=False, \
                print_stat=False, print_search=False, print_steps=False):
    """Test list of steps for the given theorem."""
    def test_val(thy, val):
        state = ProofState.parse_init_state(thy, val)
        goal = state.prf.items[-1].th
        num_found = 0
        if print_stat and 'steps' not in val:
            print("%20s %s" % (val['name'], "No steps found"))
            return

        for i, step in enumerate(val['steps']):
            if print_search or print_stat:
                if 'fact_ids' not in step:
                    step['fact_ids'] = []
                if print_steps:
                    print(method.display_method(state, step))
                if print_search:
                    select_ids = "goal " + step['goal_id']
                    if step['fact_ids']:
                        select_ids += ", fact " + ", ".join(step['fact_ids'])
                    print('Step ' + str(i) + " (" + select_ids + ")")
                search_res = state.search_method(step['goal_id'], step['fact_ids'])
                found = 0
                for res in search_res:
                    m = theory.global_methods[res['_method_name']]
                    if res['_method_name'] == step['method_name'] and \
                       all(sig not in res or res[sig] == step[sig] for sig in m.sig):
                        if print_search:
                            print('* ' + m.display_step(state, step['goal_id'], res, step['fact_ids']))
                        found += 1
                    else:
                        if print_search:
                            print('  ' + m.display_step(state, step['goal_id'], res, step['fact_ids']))
                assert found <= 1, "test_val: multiple found"
                if found == 0:
                    if print_search:
                        m = theory.global_methods[step['method_name']]
                        print('- ' + m.display_step(state, step['goal_id'], step, step['fact_ids']))
                else:
                    num_found += 1
            method.apply_method(state, step)
        self.assertEqual(state.check_proof(no_gaps=no_gaps), goal)
        if print_proof:
            print("Final state:")
            print(printer.print_proof(thy, state.prf))
        if print_stat:
            total = len(val['steps'])
            print("%20s %5d %5d %5d" % (val['name'], total, num_found, total - num_found))
        
    thy = basic.load_theory(thy_name, limit=('thm', thm_name))
    with open('./library/' + thy_name + '.json', 'r', encoding='utf-8') as f:
        f_data = json.load(f)
        for val in f_data['content']:
            if val['ty'] == 'thm' and val['name'] == thm_name:
                test_val(thy, val)


class ServerTest(unittest.TestCase):
    def testInitProof(self):
        state = ProofState.init_state(thy, [A, B], [conj(A, B)], conj(B, A))
        self.assertEqual(len(state.prf.items), 3)
        self.assertEqual(state.check_proof(), Thm.mk_implies(conj(A, B), conj(B, A)))

    def testInitProof2(self):
        state = ProofState.init_state(thy, [A, B], [A, B], conj(A, B))
        self.assertEqual(len(state.prf.items), 4)
        self.assertEqual(state.check_proof(), Thm.mk_implies(A, B, conj(A, B)))

    def testParseInitState(self):
        state = ProofState.parse_init_state(
            thy, {'vars': {'A': 'bool', 'B': 'bool'}, 'prop': "A & B --> B & A"})
        self.assertEqual(len(state.prf.items), 3)
        self.assertEqual(state.check_proof(), Thm.mk_implies(conj(A, B), conj(B, A)))

    def testJsonData(self):
        state = ProofState.parse_init_state(
            thy, {'vars': {'A': 'bool', 'B': 'bool'}, 'prop': "A & B --> B & A"})
        json_data = state.json_data()
        self.assertEqual(len(json_data['vars']), 2)
        self.assertEqual(len(json_data['proof']), 3)
        self.assertIn('report', json_data)

    def testParseProof(self):
        data = {
            'vars': {'A': 'bool', 'B': 'bool'},
            'proof': [
                {'id': 0, 'rule': 'assume', 'args': 'A & B', 'prevs': [], 'th': ''},
                {'id': 1, 'rule': 'sorry', 'args': '', 'prevs': [], 'th': 'A & B |- B & A'},
                {'id': 2, 'rule': 'implies_intr', 'args': 'A & B', 'prevs': [1], 'th': ''}
            ]
        }
        state = ProofState.parse_proof(thy, data)
        self.assertEqual(len(state.vars), 2)
        self.assertEqual(len(state.prf.items), 3)

    def testParseProof2(self):
        data = {
            'vars': {},
            'proof': [
                {'id': 0, 'rule': 'variable', 'args': "a, 'a", 'prevs': [], 'th': ''}
            ]
        }
        state = ProofState.parse_proof(thy, data)
        self.assertEqual(len(state.prf.items), 1)

    def testGetCtxt(self):
        state = ProofState.init_state(thy, [A, B], [conj(A, B)], conj(B, A))
        self.assertEqual(state.get_ctxt(0), Context(thy, vars={'A': 'bool', 'B': 'bool'}))

    def testAddLineBefore(self):
        state = ProofState.init_state(thy, [A, B], [conj(A, B)], conj(B, A))

        state.add_line_before(2, 1)
        self.assertEqual(len(state.prf.items), 4)
        self.assertEqual(state.check_proof(), Thm.mk_implies(conj(A, B), conj(B, A)))

        state.add_line_before(2, 3)
        self.assertEqual(len(state.prf.items), 7)
        self.assertEqual(state.check_proof(), Thm.mk_implies(conj(A, B), conj(B, A)))

    def testRemoveLine(self):
        state = ProofState.init_state(thy, [A, B], [conj(A, B)], conj(B, A))
        state.add_line_before(2, 1)
        state.remove_line(2)
        self.assertEqual(len(state.prf.items), 3)
        self.assertEqual(state.check_proof(), Thm.mk_implies(conj(A, B), conj(B, A)))

    def testSetLine(self):
        state = ProofState.init_state(thy, [A, B], [conj(A, B)], conj(B, A))
        state.add_line_before(2, 1)
        state.set_line(2, "theorem", args="conjD1")
        self.assertEqual(len(state.prf.items), 4)
        self.assertEqual(state.check_proof(), Thm.mk_implies(conj(A, B), conj(B, A)))

    def testApplyBackwardStepThms(self):
        state = ProofState.init_state(thy, [A, B], [conj(A, B)], conj(B, A))
        search_res = state.apply_search(1, method.apply_backward_step())
        self.assertEqual([res['theorem'] for res in search_res], ["conjI"])

    def testApplyBackwardStepThms2(self):
        state = ProofState.init_state(thy, [A, B], [disj(A, B)], disj(B, A))
        search_res = state.apply_search(1, method.apply_backward_step(), prevs=[0])
        self.assertEqual([res['theorem'] for res in search_res], ["disjE"])

    def testApplyBackwardStepThms3(self):
        """Example of two results."""
        state = ProofState.init_state(thy, [A, B], [disj(A, B)], disj(B, A))
        search_res = state.apply_search(1, method.apply_backward_step())
        self.assertEqual([res['theorem'] for res in search_res], ["disjI1", "disjI2"])

    def testApplyBackwardStepThms4(self):
        """Example with no variables."""
        state = ProofState.init_state(thy, [], [], logic.true)
        search_res = state.apply_search(0, method.apply_backward_step())
        self.assertEqual([res['theorem'] for res in search_res], ["trueI"])

    def testApplyBackwardStep(self):
        state = ProofState.init_state(thy, [A, B], [conj(A, B)], conj(B, A))
        state.apply_backward_step(1, "conjI")
        self.assertEqual(state.check_proof(), Thm.mk_implies(conj(A, B), conj(B, A)))
        self.assertEqual(len(state.rpt.gaps), 2)

    def testApplyBackwardStep2(self):
        """Case where one or more assumption also needs to be matched."""
        state = ProofState.init_state(thy, [A, B], [disj(A, B)], disj(B, A))
        state.apply_backward_step(1, "disjE", prevs=[0])
        self.assertEqual(state.check_proof(), Thm.mk_implies(disj(A, B), disj(B, A)))
        self.assertEqual(len(state.rpt.gaps), 2)

    def testApplyBackwardStep3(self):
        """Test handling of additional instantiations."""
        state = ProofState.init_state(thy, [A, B], [conj(A, B)], A)
        state.apply_backward_step(1, "conjD1", instsp=(dict(), {'B': B}))
        self.assertEqual(state.check_proof(no_gaps=True), Thm.mk_implies(conj(A, B), A))

    def testApplyBackwardStep4(self):
        """Test when additional instantiation is not provided."""
        state = ProofState.init_state(thy, [A, B], [conj(A, B)], A)
        self.assertRaises(theory.ParameterQueryException, state.apply_backward_step, 1, "conjD1")

    def testApplyBackwardStep5(self):
        """Test strong induction."""
        ctxt = Context('set', vars={'s': "'a set"})
        s = parser.parse_term(ctxt, "s")
        assum = parser.parse_term(ctxt, "finite s")
        concl = parser.parse_term(ctxt, "card s >= 0")
        state = ProofState.init_state(ctxt.thy, [s], [assum], concl)
        state.apply_backward_step(1, "finite_induct_strong", prevs=[0])

    def testApplyBackwardStep6(self):
        """Test case with type variable only."""
        ctxt = Context('real')
        concl = parser.parse_term(ctxt, "finite (empty_set::real set)")
        state = ProofState.init_state(ctxt.thy, [], [], concl)
        state.apply_backward_step(0, 'finite_empty')

    def testApplyForwardStep1(self):
        state = ProofState.init_state(thy, [A, B], [conj(A, B)], conj(B, A))
        state.apply_forward_step(1, "conjD1", prevs=[0])
        self.assertEqual(state.check_proof(), Thm.mk_implies(conj(A, B), conj(B, A)))
        item = state.get_proof_item((1,))
        self.assertEqual(item.th.concl, A)

    def testApplyForwardStep2(self):
        state = ProofState.init_state(thy, [A, B], [conj(A, B)], conj(B, A))
        state.apply_forward_step(1, "conjD2", prevs=[0])
        self.assertEqual(state.check_proof(), Thm.mk_implies(conj(A, B), conj(B, A)))
        item = state.get_proof_item((1,))
        self.assertEqual(item.th.concl, B)

    def testApplyForwardStep3(self):
        state = ProofState.init_state(thy, [A, B], [A], disj(A, B))
        method.apply_method(state, {
            'method_name': 'apply_forward_step',
            'goal_id': "1", 'fact_ids': ["0"], 'theorem': 'disjI1',
            'param_B': "B"})
        self.assertEqual(state.check_proof(), Thm.mk_implies(A, disj(A, B)))

    def testApplyForwardStep4(self):
        state = ProofState.init_state(thy, [A, B], [A], disj(A, B))
        self.assertRaises(theory.ParameterQueryException, method.apply_method,
            state, {'method_name': 'apply_forward_step',
                    'goal_id': "1", 'fact_ids': ["0"], 'theorem': 'disjI1'})

    def testApplyForwardStepThms1(self):
        state = ProofState.init_state(thy, [A, B], [conj(A, B)], conj(B, A))
        search_res = state.apply_search(1, method.apply_forward_step(), prevs=[0])
        self.assertEqual([res['theorem'] for res in search_res], ['conjD1', 'conjD2'])

    def testApplyForwardStepThms2(self):
        state = ProofState.init_state(thy, [A, B], [disj(A, B)], disj(B, A))
        search_res = state.apply_search(1, method.apply_forward_step(), prevs=[0])
        self.assertEqual([res['theorem'] for res in search_res], [])

    def testIntroduction(self):
        state = ProofState.init_state(thy, [A, B], [], imp(disj(A, B), disj(B, A)))
        state.introduction(0)
        self.assertEqual(state.check_proof(), Thm.mk_implies(disj(A, B), disj(B, A)))

    def testIntroduction2(self):
        state = ProofState.init_state(thy, [A, B], [], imp(A, B, conj(A, B)))
        state.introduction(0)
        self.assertEqual(state.check_proof(), Thm.mk_implies(A, B, conj(A, B)))

    def testIntroduction3(self):
        Ta = TVar("a")
        A = Var("A", TFun(Ta, boolT))
        B = Var("B", TFun(Ta, boolT))
        x = Var("x", Ta)
        state = ProofState.init_state(thy, [A, B], [], Term.mk_all(x, imp(A(x), B(x))))
        state.introduction(0, ["x"])
        self.assertEqual(state.check_proof(), Thm([], Term.mk_all(x, imp(A(x), B(x)))))
        self.assertEqual(len(state.prf.items), 1)
        self.assertEqual(len(state.prf.items[0].subproof.items), 4)

    def testApplyInduction(self):
        thy = basic.load_theory('nat')
        n = Var("n", nat.natT)
        state = ProofState.init_state(thy, [n], [], Term.mk_equals(nat.plus(n, nat.zero), n))
        state.apply_induction(0, "nat_induct", "n")
        self.assertEqual(state.check_proof(), Thm([], Term.mk_equals(nat.plus(n, nat.zero), n)))
        self.assertEqual(len(state.prf.items), 3)

    def testRewriteGoalThms(self):
        thy = basic.load_theory('nat')
        n = Var("n", nat.natT)
        state = ProofState.init_state(thy, [n], [], Term.mk_equals(nat.plus(nat.zero, n), n))
        search_res = state.apply_search(0, method.rewrite_goal())
        self.assertEqual([res['theorem'] for res in search_res], ["nat_plus_def_1"])

    def testRewriteGoalWithAssum(self):
        Ta = TVar("a")
        a = Var("a", Ta)
        b = Var("b", Ta)
        eq_a = Term.mk_equals(a, a)
        if_t = logic.mk_if(eq_a, b, a)
        state = ProofState.init_state(thy, [a, b], [], Term.mk_equals(if_t, b))
        state.rewrite_goal(0, "if_P")
        state.set_line(0, "reflexive", args=a)
        self.assertEqual(state.check_proof(no_gaps=True), Thm.mk_equals(if_t, b))

    def testConjComm(self):
        """Proof of A & B --> B & A."""
        testMethods(self, 'logic', 'conj_comm')

    def testDisjComm(self):
        """Proof of A | B --> B | A."""
        testMethods(self, 'logic', 'disj_comm')

    def testDoubleNegInv(self):
        """Proof of ~~A = A."""
        testMethods(self, 'logic', 'double_neg')

    def testExistsConj(self):
        """Proof of (?x. A x & B x) --> (?x. A x) & (?x. B x)."""
        testMethods(self, 'logic', 'ex_conj_distrib')

    def testForallConj(self):
        """Proof of (!x. A x & B x) --> (!x. A x) & (!x. B x)."""
        testMethods(self, 'logic', 'all_conj_distrib')

    def testAddZeroRight(self):
        """Proof of n + 0 = n by induction."""
        testMethods(self, 'nat', 'add_0_right')

    def testMultZeroRight(self):
        """Proof of n * 0 = 0 by induction."""
        testMethods(self, 'nat', 'mult_0_right')

    def testAppendNil(self):
        """Proof of xs @ [] = xs by induction."""
        testMethods(self, 'list', 'append_right_neutral')

    def testFunUpdTriv(self):
        """Proof of (f)(a := f a) = f."""
        testMethods(self, 'function', 'fun_upd_triv')

    def testAVal1(self):
        """Proof of aval (Plus (V 1) (N 5)) ((λx. 0)(1 := 7)) = 12."""
        testMethods(self, 'expr', 'aval_test1')

    def testAVal2(self):
        """Proof of aval (Plus (V 0) (N 5)) ((%x. 0)(1 := 7)) = 5."""
        testMethods(self, 'expr', 'aval_test2')

    def testPierce(self):
        """Proof of ((A --> B) --> A) --> A."""
        testMethods(self, 'logic', 'pierce')

    def testHoarePreRule(self):
        """Proof of Entail P Q --> Valid Q c R --> Valid P c R."""
        testMethods(self, 'hoare', 'pre_rule')

    def testNatLessEqTrans(self):
        """Proof of k <= m --> m <= n --> k <= n."""
        testMethods(self, 'nat', 'less_eq_trans')

    def testDrinker(self):
        """Proof of ?x. P x --> (!x. P x)."""
        testMethods(self, 'logic', 'drinker')

    def testCantor(self):
        """Proof of ?a. !x. ~f x = a."""
        testMethods(self, 'set', 'cantor')

    def testSubsetEmpty(self):
        """Proof of subset empty A."""
        testMethods(self, 'set', 'subset_empty')

    def testUnionUnion(self):
        """Proof of UN (A Un B) = (UN A) Un (UN B)."""
        testMethods(self, 'set', 'Union_union')

    def testFixpoint(self):
        """Proof of bnd_mono h --> h (lfp h) = lfp h."""
        testMethods(self, 'set', 'lfp_unfold')

    def testInjectiveCompFun(self):
        """Proof of injective f --> injective g --> injective (g o f)."""
        testMethods(self, 'function', 'injective_comp_fun')

    def testSurjectiveD(self):
        """Proof of surjective f --> (?x. f x = y)."""
        testMethods(self, 'function', 'surjectiveD')

    def testHasLimitUnique(self):
        """Proof of has_limit f x --> has_limit f y --> x = y."""
        testMethods(self, 'limits', 'has_limit_unique', no_gaps=False)

    def testTheI(self):
        """Proof of P a --> (!x. P x --> x = a) --> P (THE x. P x)."""
        testMethods(self, 'logic_base', 'theI')


if __name__ == "__main__":
    unittest.main()
