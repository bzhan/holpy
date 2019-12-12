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
from syntax import parser
from syntax import printer
from logic.context import Context
from server import tactic, method, server
from server.server import ProofState
from imperative import imp

thy = basic.load_theory('logic_base')

A = Var("A", boolT)
B = Var("B", boolT)
conj = logic.mk_conj
disj = logic.mk_disj


def testSteps(self, thy_name, thm_name, *, no_gaps=True, print_proof=False, \
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
                    print(method.output_step(state, step))
                if print_search:
                    select_ids = "goal " + step['goal_id']
                    if step['fact_ids']:
                        select_ids += ", fact " + ", ".join(step['fact_ids'])
                    print('Step ' + str(i) + " (" + select_ids + ")")
                search_res = state.search_method(step['goal_id'], step['fact_ids'])
                found = 0
                for res in search_res:
                    m = theory.global_methods[res['method_name']]
                    if res['method_name'] == step['method_name'] and \
                       all(sig not in res or sig not in step or res[sig] == step[sig] for sig in m.sig):
                        if print_search:
                            print('* ' + m.display_step(state, res))
                        found += 1
                    else:
                        if print_search:
                            print('  ' + m.display_step(state, res))
                assert found <= 1, "test_val: multiple found"
                if found == 0:
                    if print_search:
                        m = theory.global_methods[step['method_name']]
                        print('- ' + m.display_step(state, step))
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
    def testInitState(self):
        state = ProofState.init_state(thy, [A, B], [conj(A, B)], conj(B, A))
        self.assertEqual(len(state.prf.items), 3)
        self.assertEqual(state.check_proof(), Thm.mk_implies(conj(A, B), conj(B, A)))

    def testInitState2(self):
        state = ProofState.init_state(thy, [A, B], [A, B], conj(A, B))
        self.assertEqual(len(state.prf.items), 4)
        self.assertEqual(state.check_proof(), Thm.mk_implies(A, B, conj(A, B)))

    def testInitState3(self):
        state = ProofState.init_state(thy, [A], [], disj(A, logic.neg(A)))
        self.assertEqual(len(state.prf.items), 2)
        self.assertEqual(state.check_proof(), Thm([], disj(A, logic.neg(A))))

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
        self.assertEqual(json_data['num_gaps'], 1)

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

    def testConjComm(self):
        """Proof of A & B --> B & A."""
        testSteps(self, 'logic', 'conj_comm')

    def testDisjComm(self):
        """Proof of A | B --> B | A."""
        testSteps(self, 'logic', 'disj_comm')

    def testDoubleNegInv(self):
        """Proof of ~~A = A."""
        testSteps(self, 'logic', 'double_neg')

    def testExistsConj(self):
        """Proof of (?x. A x & B x) --> (?x. A x) & (?x. B x)."""
        testSteps(self, 'logic', 'ex_conj_distrib')

    def testForallConj(self):
        """Proof of (!x. A x & B x) --> (!x. A x) & (!x. B x)."""
        testSteps(self, 'logic', 'all_conj_distrib')

    def testAddZeroRight(self):
        """Proof of n + 0 = n by induction."""
        testSteps(self, 'nat', 'add_0_right')

    def testAddComm(self):
        """Proof of n + m = m + n."""
        testSteps(self, 'nat', 'add_comm')

    def testMultZeroRight(self):
        """Proof of n * 0 = 0 by induction."""
        testSteps(self, 'nat', 'mult_0_right')

    def testAppendNil(self):
        """Proof of xs @ [] = xs by induction."""
        testSteps(self, 'list', 'append_right_neutral')

    def testFunUpdTriv(self):
        """Proof of (f)(a := f a) = f."""
        testSteps(self, 'function', 'fun_upd_triv')

    def testAVal1(self):
        """Proof of aval (Plus (V 1) (N 5)) ((λx. 0)(1 := 7)) = 12."""
        testSteps(self, 'expr', 'aval_test1')

    def testAVal2(self):
        """Proof of aval (Plus (V 0) (N 5)) ((%x. 0)(1 := 7)) = 5."""
        testSteps(self, 'expr', 'aval_test2')

    def testPierce(self):
        """Proof of ((A --> B) --> A) --> A."""
        testSteps(self, 'logic', 'pierce')

    def testHoarePreRule(self):
        """Proof of Entail P Q --> Valid Q c R --> Valid P c R."""
        testSteps(self, 'hoare', 'pre_rule')

    def testNatLessEqTrans(self):
        """Proof of k <= m --> m <= n --> k <= n."""
        testSteps(self, 'nat', 'less_eq_trans')

    def testDrinker(self):
        """Proof of ?x. P x --> (!x. P x)."""
        testSteps(self, 'logic', 'drinker')

    def testCantor(self):
        """Proof of ?a. !x. ~f x = a."""
        testSteps(self, 'set', 'cantor')

    def testSubsetEmpty(self):
        """Proof of subset empty A."""
        testSteps(self, 'set', 'subset_empty')

    def testUnionUnion(self):
        """Proof of UN (A Un B) = (UN A) Un (UN B)."""
        testSteps(self, 'set', 'Union_union')

    def testFixpoint(self):
        """Proof of bnd_mono h --> h (lfp h) = lfp h."""
        testSteps(self, 'set', 'lfp_unfold')

    def testInjectiveCompFun(self):
        """Proof of injective f --> injective g --> injective (g o f)."""
        testSteps(self, 'function', 'injective_comp_fun')

    def testSurjectiveCompFun(self):
        """Proof of surjective f --> surjective g --> surjective (g o f)."""
        testSteps(self, 'function', 'surjective_comp_fun')

    def testSurjectiveD(self):
        """Proof of surjective f --> (?x. f x = y)."""
        testSteps(self, 'function', 'surjectiveD')

    def testHasLimitUnique(self):
        """Proof of has_limit f x --> has_limit f y --> x = y."""
        testSteps(self, 'limits', 'has_limit_unique', no_gaps=False)

    def testTheI(self):
        """Proof of P a --> (!x. P x --> x = a) --> P (THE x. P x)."""
        testSteps(self, 'logic_base', 'theI')


if __name__ == "__main__":
    unittest.main()
