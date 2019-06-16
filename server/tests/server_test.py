# Author: Bohua Zhan

import unittest
import io
import json

from kernel.type import TVar, TFun, boolT
from kernel.term import Term, Var, Const
from kernel.thm import Thm
from kernel.proof import Proof
from kernel.theory import global_methods
from kernel.report import ProofReport
from logic import logic
from logic import basic
from data import nat
from data import list
from data import function
from syntax import printer
from server import server
from server import method
from server.server import ProofState
from imp import imp

thy = basic.load_theory('logic_base')

A = Var("A", boolT)
B = Var("B", boolT)
conj = logic.mk_conj
disj = logic.mk_disj
imp = Term.mk_implies
neg = logic.neg
exists = logic.mk_exists

def testMethods(self, thy_name, thm_name, *, no_gaps=True, print_proof=False, print_search=False):
    """Test list of steps for the given theorem."""
    def test_val(thy, val):
        state = ProofState.parse_init_state(thy, val)
        goal = state.prf.items[-1].th
        for i, step in enumerate(val['steps']):
            if print_search:
                print('Step ' + str(i))
                if 'fact_ids' not in step:
                    step['fact_ids'] = []
                res = state.search_method(step['goal_id'], step['fact_ids'])
                for r in res:
                    m = global_methods[r['_method_name']]
                    print(m.display_step(state, step['goal_id'], r, step['fact_ids']))
            method.apply_method(state, step)
        self.assertEqual(state.check_proof(no_gaps=no_gaps), goal)
        if print_proof:
            print("Final state:")
            print(printer.print_proof(thy, state.prf))
        
    thy = basic.load_theory(thy_name, limit=('thm', thm_name))
    with open('./library/' + thy_name + '.json', 'r', encoding='utf-8') as f:
        f_data = json.load(f)
        for val in f_data['content']:
            if val['ty'] == 'thm' and val['name'] == thm_name:
                test_val(thy, val)


class ServerTest(unittest.TestCase):
    def testIncrIdAfter(self):
        test_data = [
            (((0,), (0,), 1), (1,),),
            (((0, 1), (0,), 1), (1, 1)),
            (((1,), (2, 2), 1), (1,)),
            (((2, 1), (2, 2), 1), (2, 1)),
            (((2, 2), (2, 2), 1), (2, 3)),
            (((2, 3, 2), (2, 2), 1), (2, 4, 2)),
            (((3,), (2, 2), 1), (3,)),
        ]

        for (id, start, n), res in test_data:
            self.assertEqual(server.incr_id_after(id, start, n), res)

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
        self.assertEqual(state.get_ctxt(0), {'vars': {'A': boolT, 'B': boolT}})

    def testAddLineAfter(self):
        state = ProofState.init_state(thy, [A, B], [conj(A, B)], conj(B, A))

        state.add_line_after(0)
        self.assertEqual(len(state.prf.items), 4)
        self.assertEqual(state.check_proof(), Thm.mk_implies(conj(A, B), conj(B, A)))
        self.assertEqual(state.prf.items[1].rule, "")

    def testAddLineAfter2(self):
        state = ProofState.init_state(thy, [A, B], [conj(A, B)], conj(B, A))

        state.add_line_after(1)
        self.assertEqual(len(state.prf.items), 4)
        self.assertEqual(state.check_proof(), Thm.mk_implies(conj(A, B), conj(B, A)))
        self.assertEqual(state.prf.items[2].rule, "")

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
        state.add_line_after(1)
        state.remove_line(2)
        self.assertEqual(len(state.prf.items), 3)
        self.assertEqual(state.check_proof(), Thm.mk_implies(conj(A, B), conj(B, A)))

    def testSetLine(self):
        state = ProofState.init_state(thy, [A, B], [conj(A, B)], conj(B, A))
        state.add_line_after(1)
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
        self.assertEqual([res['theorem'] for res in search_res], ["plus_def_1"])

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


if __name__ == "__main__":
    unittest.main()
