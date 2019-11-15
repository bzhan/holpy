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
from syntax.context import Context
from server import tactic, method, server
from server.server import ProofState
from imperative import imp

thy = basic.load_theory('logic_base')

A = Var("A", boolT)
B = Var("B", boolT)
conj = logic.mk_conj
disj = logic.mk_disj

def test_method(self, thy, *, vars=None, assms=None, concl, method_name, prevs=None, args=None,
                gaps=None, lines=None, query=None, failed=None):
    """Test run a method.

    gaps -- expected gaps remaining.
    query -- expected query for variables.
    failed -- if None, expected Exception.

    """
    # Build context
    ctxt = Context(thy, vars=vars)
    thy = ctxt.thy

    # Build starting state
    vars = [Var(nm, T) for nm, T in ctxt.vars.items()]
    if assms is not None:
        assert isinstance(assms, list), "test_method: assms need to be a list"
        assms = [parser.parse_term(ctxt, t) for t in assms]
    else:
        assms = []
    concl = parser.parse_term(ctxt, concl)
    state = ProofState.init_state(thy, vars, assms, concl)

    # Obtain and run method
    if args is None:
        args = dict()
    args['method_name'] = method_name
    args['goal_id'] = len(assms)
    args['fact_ids'] = prevs

    if failed is not None:
        self.assertRaises(failed, method.apply_method, state, args)
        return

    if query is not None:
        self.assertRaises(theory.ParameterQueryException, method.apply_method, state, args)
        return

    method.apply_method(state, args)
    self.assertEqual(state.check_proof(), Thm.mk_implies(*(assms + [concl])))
    
    # Compare list of gaps
    if gaps is None:
        gaps = [concl]  # gaps unchanged
    elif gaps == False:
        gaps = []  # assert no gaps
    else:
        assert isinstance(gaps, list), "test_method: gaps need to be a list"
        gaps = [parser.parse_term(ctxt, gap) for gap in gaps]
    self.assertEqual([gap.prop for gap in state.rpt.gaps], gaps)

    # Compare list of lines
    if lines:
        for id, t in lines.items():
            t = parser.parse_term(ctxt, t)
            self.assertEqual(state.get_proof_item(id).th.prop, t)

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
                       all(sig not in res or sig not in step or res[sig] == step[sig] for sig in m.sig):
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

    def run_search_thm(self, thy, *, vars=None, assms=None, concl, method_name, prevs=None, res):
        # Build context
        ctxt = Context(thy, vars=vars)
        thy = ctxt.thy

        # Build starting state
        vars = [Var(nm, T) for nm, T in ctxt.vars.items()]
        assms = [parser.parse_term(ctxt, t) for t in assms] if assms is not None else []
        concl = parser.parse_term(ctxt, concl)
        state = ProofState.init_state(thy, vars, assms, concl)

        # Obtain method and run its search function
        method = theory.global_methods[method_name]
        search_res = state.apply_search(len(assms), method, prevs=prevs)
        self.assertEqual([res['theorem'] for res in search_res], res)

    def testCases(self):
        test_method(self,
            'logic_base',
            vars={'B': 'bool', 'C': 'bool'},
            concl='B | C',
            method_name='cases',
            args={'case': 'B'},
            gaps=['B --> B | C', '~B --> B | C']
        )

    def testCasesFail(self):
        test_method(self,
            'logic_base',
            vars={'B': 'bool', 'C': 'bool'},
            concl='B | C',
            method_name='cases',
            args={'case': '(A::bool)'},
            failed=AssertionError
        )

    def testGoal(self):
        test_method(self,
            'logic_base',
            vars={'B': 'bool', 'C': 'bool'},
            concl='B & C',
            method_name='cut',
            args={'goal': 'B'},
            gaps=['B', 'B & C']
        )

    def testGoalFail(self):
        test_method(self,
            'logic_base',
            vars={'B': 'bool', 'C': 'bool'},
            concl='B & C',
            method_name='cut',
            args={'goal': '(A::bool)'},
            failed=AssertionError
        )

    def testApplyBackwardStepThms(self):
        self.run_search_thm(
            'logic_base',
            vars={'A': 'bool', 'B': 'bool'},
            assms=['A & B'],
            concl='B & A',
            method_name='apply_backward_step',
            res=['conjI']
        )

    def testApplyBackwardStepThms2(self):
        self.run_search_thm(
            'logic_base',
            vars={'A': 'bool', 'B': 'bool'},
            assms=['A | B'],
            concl='B | A',
            method_name='apply_backward_step',
            prevs=[0],
            res=['disjE']
        )

    def testApplyBackwardStepThms3(self):
        """Example of two results."""
        self.run_search_thm(
            'logic_base',
            vars={'A': 'bool', 'B': 'bool'},
            assms=['A | B'],
            concl='B | A',
            method_name='apply_backward_step',
            res=['disjI1', 'disjI2']
        )

    def testApplyBackwardStepThms4(self):
        """Example with no variables."""
        self.run_search_thm(
            'logic_base',
            concl='true',
            method_name='apply_backward_step',
            res=['trueI']
        )

    def testApplyBackwardStep(self):
        test_method(self,
            'logic_base',
            vars={'A': 'bool', 'B': 'bool'},
            assms=['A & B'],
            concl='B & A',
            method_name='apply_backward_step',
            args={'theorem': 'conjI'},
            gaps=['B', 'A']
        )

    def testApplyBackwardStep2(self):
        """Case where one or more assumption also needs to be matched."""
        test_method(self,
            'logic_base',
            vars={'A': 'bool', 'B': 'bool'},
            assms=['A | B'],
            concl='B | A',
            method_name='apply_backward_step',
            args={'theorem': 'disjE'},
            prevs=[0],
            gaps=['A --> B | A', 'B --> B | A']
        )

    def testApplyBackwardStep3(self):
        """Test when additional instantiation is not provided."""
        test_method(self,
            'logic_base',
            vars={'A': 'bool', 'B': 'bool'},
            assms=['A & B'],
            concl='A',
            method_name='apply_backward_step',
            args={'theorem': 'conjD1'},
            query=['B']
        )

    def testApplyBackwardStep4(self):
        """Test when additional instantiation is not provided."""
        test_method(self,
            'logic_base',
            vars={'A': 'bool', 'B': 'bool'},
            assms=['A & B'],
            concl='A',
            method_name='apply_backward_step',
            args={'theorem': 'conjD1', 'param_B': 'B'},
            gaps=False
        )

    def testApplyBackwardStep5(self):
        """Test case with type variable only."""
        test_method(self,
            'set',
            concl='finite (empty_set::nat set)',
            method_name='apply_backward_step',
            args={'theorem': 'finite_empty'},
            gaps=False
        )

    def testApplyForwardStepThms(self):
        self.run_search_thm(
            'logic_base',
            vars={'A': 'bool', 'B': 'bool'},
            assms=['A & B'],
            concl='B & A',
            method_name='apply_forward_step',
            prevs=[0],
            res=['conjD1', 'conjD2']
        )

    def testApplyForwardStep1(self):
        test_method(self,
            'logic_base',
            vars={'A': 'bool', 'B': 'bool'},
            assms=['A & B'],
            concl='B & A',
            method_name='apply_forward_step',
            args={'theorem': 'conjD1'},
            prevs=[0],
            lines={'1': 'A'}
        )

    def testApplyForwardStep2(self):
        test_method(self,
            'logic_base',
            vars={'A': 'bool', 'B': 'bool'},
            assms=['A'],
            concl='A | B',
            method_name='apply_forward_step',
            args={'theorem': 'disjI1'},
            prevs=[0],
            query=['B']
        )

    def testApplyForwardStep3(self):
        test_method(self,
            'logic_base',
            vars={'A': 'bool', 'B': 'bool'},
            assms=['A'],
            concl='A | B',
            method_name='apply_forward_step',
            args={'theorem': 'disjI1', 'param_B': 'B'},
            prevs=[0],
            gaps=False
        )

    def testApplyForwardStep4(self):
        test_method(self,
            'set',
            vars={'A': 'nat set', 'B': 'nat set'},
            assms=['A Sub B'],
            concl='false',
            method_name='apply_forward_step',
            args={'theorem': 'subset_trans', 'param_C': ''},
            prevs=[0],
            lines={'1': '!C. B Sub C --> A Sub C'}
        )

    def testApplyForwardStep5(self):
        test_method(self,
            'set',
            vars={'A': 'nat set', 'B': 'nat set', 'C': 'nat set'},
            assms=['A Sub B'],
            concl='B Sub C',
            method_name='apply_forward_step',
            args={'theorem': 'subset_trans', 'param_C': 'C'},
            prevs=[0],
            lines={'1': 'B Sub C --> A Sub C'}
        )

    def testApplyResolveStepThms(self):
        self.run_search_thm(
            'set',
            vars={'x': "'a"},
            assms=['x Mem empty_set'],
            concl=['false'],
            method_name='apply_resolve_step',
            prevs=[0],
            res=['member_empty']
        )

    def testApplyResolveStepThms2(self):
        self.run_search_thm(
            'logic_base',
            assms=['false'],
            concl=['false'],
            method_name='apply_resolve_step',
            prevs=[0],
            res=['not_false_res']
        )

    def testIntroduction(self):
        test_method(self,
            'logic_base',
            vars={'A': 'bool', 'B': 'bool'},
            concl="A | B --> B | A",
            method_name='introduction',
            gaps=['B | A']
        )

    def testIntroduction2(self):
        test_method(self,
            'logic_base',
            vars={'A': 'bool', 'B': 'bool'},
            concl='A --> B --> A & B',
            method_name='introduction',
            gaps=['A & B'],
        )

    def testIntroduction3(self):
        test_method(self,
            'logic_base',
            vars={'A': "'a => bool", 'B': "'a => bool"},
            concl='!x. A x --> B x',
            method_name='introduction',
            args={'names': 'x'},
            gaps=['B x']
        )

    def testApplyInduction(self):
        test_method(self,
            'nat',
            vars={'n': 'nat'},
            concl='n + 0 = n',
            method_name='induction',
            args={'theorem': 'nat_induct', 'var': 'n'},
            gaps=['(0::nat) + 0 = 0', '!n. n + 0 = n --> Suc n + 0 = Suc n']
        )

    def testRewriteGoalThms(self):
        self.run_search_thm(
            'nat',
            vars={'n': 'nat'},
            concl='0 + n = 0',
            method_name='rewrite_goal',
            res=['eq_sym_eq', 'nat_plus_def_1']
        )

    def testRewriteGoalThms2(self):
        self.run_search_thm(
            'set',
            vars={'f': "nat => nat", 'S': "nat set", 'T': "nat set"},
            concl='image f (image f S) = T',
            method_name='rewrite_goal',
            res=['eq_sym_eq', 'image_combine', 'image_def']
        )

    def testRewriteGoal(self):
        test_method(self,
            'logic_base',
            vars={'P': 'bool', 'a': "'a", 'b': "'a"},
            assms=['P'],
            concl='(if P then a else b) = b',
            method_name='rewrite_goal',
            args={'theorem': 'if_P'},
            prevs=[0],
            gaps=['a = b']
        )

    def testRewriteGoal2(self):
        test_method(self,
            'logic_base',
            vars={'P': 'bool', 'a': "'a", 'b': "'a"},
            assms=['P'],
            concl='(if P then a else b) = a',
            method_name='rewrite_goal',
            args={'theorem': 'if_P'},
            prevs=[0],
            gaps=False
        )

    def testRewriteGoal3(self):
        test_method(self,
            'set',
            vars={'g': "'a => 'b", 'f': "'b => 'c", 's': "'a set", 't': "'c set"},
            concl='image f (image g s) = t',
            method_name='rewrite_goal',
            args={'theorem': 'image_combine', 'sym': 'true'},
            gaps=["image (f O g) s = t"]
        )

    def testForallElim(self):
        test_method(self,
            'nat',
            vars={'n': 'nat', 'P': 'nat => bool', 'Q': 'nat => bool'},
            assms=['!x. P x --> Q x'],
            concl='Q n',
            method_name='forall_elim',
            args={'s': 'n'},
            prevs=[0],
            lines={'1': 'P n --> Q n'}
        )

    def testForallElimFail(self):
        test_method(self,
            'nat',
            vars={'n': 'nat', 'P': 'nat => bool', 'Q': 'nat => bool'},
            assms=['!x. P x --> Q x'],
            concl='Q n',
            method_name='forall_elim',
            args={'s': '(m::nat)'},
            prevs=[0],
            failed=AssertionError
        )

    def testInstExistsGoal(self):
        test_method(self,
            'nat',
            vars={'n': 'nat', 'P': 'nat => bool', 'Q': 'nat => bool'},
            assms=['P n'],
            concl='?x. P x --> Q x',
            method_name='inst_exists_goal',
            args={'s': 'n'},
            gaps=['P n --> Q n']
        )

    def testInstExistsGoalFail(self):
        test_method(self,
            'nat',
            vars={'n': 'nat', 'P': 'nat => bool', 'Q': 'nat => bool'},
            assms=['P n'],
            concl='?x. P x --> Q x',
            method_name='inst_exists_goal',
            args={'s': '(m::nat)'},
            failed=AssertionError
        )

    def testInstExistsFact(self):
        test_method(self,
            'nat',
            assms=['?n::nat. n + 1 = 2'],
            concl='false',
            method_name='exists_elim',
            args={'names': 'n'},
            prevs=[0],
            lines={'1': '_VAR (n::nat)', '2': '(n::nat) + 1 = 2'}
        )

    def testInstExistsFactFail(self):
        test_method(self,
            'nat',
            vars={'n': 'nat'},
            assms=['?n::nat. n + 1 = 2'],
            concl='n = 1',
            method_name='exists_elim',
            args={'names': 'n'},
            prevs=[0],
            failed=AssertionError
        )

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
