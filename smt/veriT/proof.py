"""
Basic proof rules in veriT solver.
"""
from smt.veriT.verit_macro import *
from kernel.proofterm import ProofTerm, Thm
from logic import basic, matcher, logic, conv
from kernel import term
import functools

basic.load_theory("verit")

class Input(object):
    def __init__(self, seq_num, concl):
        self.seq_num = seq_num
        self.concl = concl

class Rule(object):
    def __init__(self, seq_num, proof_name, concl, assms=[], args=None):
        self.seq_num = seq_num
        self.proof_name = str(proof_name)
        self.concl = concl
        self.assms = assms
        self.args = args
    def __str__(self):
        return "%s: %s: %s: %s: %s" % (
            self.seq_num,
            self.proof_name,
            self.concl,
            self.assms,
            self.args
        )


class ProofReconstruction(object):
    def __init__(self, steps):
        # A list of proof steps.
        self.steps = steps

        # map seq number to proof number
        self.proof = dict()

    def main(self):
        for step in self.steps:
            self.reconstruct(step)
            print(step.seq_num)
        return self.proof[len(self.steps)]

    def reconstruct(self, step):
        name = step.proof_name
        if name == "input":
            self.input_rule(step)
        elif name == "true":
            self.true_rule(step)
        elif name == "false":
            self.false_rule(step)
        elif name == "tmp_betared":
            self.tmp_betared(step)
        elif name == "tmp_qnt_tidy":
            self.tmp_qnt_tidy(step)
        elif name == "or_pos":
            self.or_pos(step)
        elif name == "or":
            self.or_rule(step)
        elif name == "resolution" or name == "th_resolution":
            self.resolution(step)
        elif name == "forall_inst":
            self.forall_inst(step)
        elif name == "eq_reflexive":
            self.eq_reflexive(step)
        elif name == "eq_transitive":
            self.eq_transitive(step)
        elif name == "and":
            self.and_rule(step)
        elif name == "and_pos":
            self.and_pos(step)
        elif name == "eq_congruent":
            self.eq_congruent(step)
        elif name == "equiv1":
            self.equiv1(step)
        elif name == "equiv2":
            self.equiv2(step)
        elif name == "equiv_pos1":
            self.equiv_pos1(step)
        else:
            print(step.proof_name)
            print(step)
            # raise NotImplementedError
            self.not_imp(step)
    
    def not_imp(self, step):
        self.proof[step.seq_num] = ProofTerm.sorry(Thm([hyp for i in step.assms for hyp in self.proof[i].hyps], step.concl))

    def schematic_rule1(self, th_name, pt):
        """
        The th is in a ⊢ A --> B form, pt is ⊢ A, return ⊢ B. 
        """
        pt_th = ProofTerm.theorem(th_name)
        inst = matcher.first_order_match(pt_th.prop.arg1, pt.prop)
        pt_th_inst = pt_th.substitution(inst=inst)
        return pt_th_inst.implies_elim(pt)

    def schematic_rule2(self, th_name, tm):
        """
        The th is in ⊢ A, A is a tautology, instantiate th by tm.
        """
        pt_th = ProofTerm.theorem(th_name)
        inst = matcher.first_order_match(pt_th.prop, tm)
        return pt_th.substitution(inst=inst)

    def input_rule(self, step):
        """
        Verit will give each (sub-)expression a name in input rule,
        hence it is not a proof.
        """
        self.proof[step.seq_num] = ProofTerm.assume(step.concl)

    def tmp_betared(self, step):
        """
        Assume that tmp_betared rules are only followed by input rules, 
        For now, we only return the conclusion as input.
        """
        self.proof[step.seq_num] = ProofTerm.assume(step.concl)

    def tmp_qnt_tidy(self, step):
        """
        Normalize quantifiers, but we don't know the mechanism now, 
        so only return the formula waited for normalizing. 
        """
        self.proof[step.seq_num] = self.proof[step.assms[0]]

    def forall_inst(self, step):
        """⊢ (¬∀x. P (x)) ∨ P(x0)"""
        self.proof[step.seq_num] = self.schematic_rule("forall_inst")

    def or_pos(self, step):
        """⊢ ¬(a_1 ∨ ... ∨ a_n) ∨ a_1 ∨ ... ∨ a_n"""
        self.proof[step.seq_num] = self.schematic_rule("or_pos")

    def or_rule(self, step):
        """
        {(or a_1 ... a_n)} --> {a_1 ... a_n}
        this rule doesn't have effect in HOL, so return the assms[0]
        """
        self.proof[step.seq_num] = self.proof[step.assms[0]]

    def resolution(self, step):
        """Given a sequence of proof terms, take resolution on them one by one."""
        res_pts = [self.proof[num] for num in step.assms]
        self.proof[step.seq_num] = functools.reduce(lambda x, y: logic.resolution(x, y), res_pts[1:], res_pts[0])

    def eq_reflexive(self, step):
        """{(= x x)}"""
        self.proof[step.seq_num] = ProofTerm.reflexive(step.concl.lhs)
    
    def eq_transitive(self, step):
        """{(not (= x_1 x_2)) ... (not (= x_{n-1} x_n)) (= x_1 x_n)}"""
        self.proof[step.seq_num] = ProofTerm("verit_and_rule", step.concl)
    
    def and_rule(self, step):
        """{(and a_1 ... a_n)} --> {a_i}
            a_1 ∧ ... ∧ a_n --> a_i
        """
        pt = ProofTerm("imp_conj", term.Implies(self.proof[step.assms[0]].prop, step.concl))
        self.proof[step.seq_num] = pt.implies_elim(self.proof[step.assms[0]])

    def and_pos(self, step):
        """
        ⊢ ¬(a_1 ∧ ... ∧ a_n) ∨ a_i
        """
        pt = ProofTerm("imp_conj", term.Implies(step.concl.arg1.arg, step.concl.arg))
        self.proof[step.seq_num] = pt.on_prop(conv.rewr_conv("imp_disj_eq"))

    def eq_congruent(self, step):
        self.proof[step.seq_num] = ProofTerm("verit_eq_congurent", step.concl)

    def equiv1(self, step):
        """a ⟷ b --> ¬a ∨ b """
        self.proof[step.seq_num] = self.schematic_rule1("equiv1", self.proof[step.assms[0]])

    def equiv2(self, step):
        """a ⟷ b --> a ∨ ¬b """
        self.proof[step.seq_num] = self.schematic_rule1("equiv2", self.proof[step.assms[0]])

    def equiv_pos1(self, step):
        """¬(a ⟷ b) ∨ a ∨ ¬b"""
        self.proof[step.seq_num] = self.schematic_rule2("equiv_pos1", step.concl)


# class InputRule(Rule):
#     """Assertion."""
#     def __init__(self, seq_num, params, concl):
#         super.__init__(self, seq_num, params, concl)

# class TrueRule(Rule):
#     """⊢ true"""
#     def __init__(self, seq_num, params, concl):
#         super.__init__(self, seq_num, params, concl)

# class FalseRule(Rule):
#     """⊢ ¬false"""
#     def __init__(self, seq_num):
#         super.__init__(self, seq_num, params, concl)

# class AndPos(Rule):
#     """⊢ ¬(a_1 ∧ ... ∧ a_n) ∨ a_i"""
#     def __init__(self, seq_num, params, concl):
#         super.__init__(self, seq_num, params, concl)

# class AndNeg(Rule):
#     """⊢ (a_1 ∧ ... ∧ a_n) ∨ ¬a_1 ∨ ... ∨ ¬a_n"""
#     def __init__(self, seq_num, params, concl):
#         super.__init__(self, seq_num, params, concl)

# class OrPos(Rule):
#     """⊢ ¬(a_1 ∨ ... ∨ a_n) ∨ a_1 ∨ ... ∨ a_n"""
#     def __init__(self, seq_num, params, concl):
#         super.__init__(self, seq_num, params, concl)

# class OrNeg(Rule):
#     """⊢ (a_1 ∨ ... ∨ a_n) ∨ ¬a_i"""
#     def __init__(self, seq_num, params, concl):
#         super.__init__(self, seq_num, params, concl)

# class ImpliesPos(Rule):
#     """⊢ ¬(a ⟶ b) ∨ ¬a ∨ b"""
#     def __init__(self, seq_num, params, concl):
#         super.__init__(self, seq_num, params, concl)

# class ImpliesNeg1(Rule):
#     """⊢ (a ⟶ b) ∨ a"""
#     def __init__(self, seq_num, params, concl):
#         super.__init__(self, seq_num, params, concl)

# class ImpliesNeg2(Rule):
#     """⊢ (a ⟶ b) ∨ ¬b"""
#     def __init__(self, seq_num, params, concl):
#         super.__init__(self, seq_num, params, concl)

# class EquivPos1(Rule):
#     """¬(a ⟷ b) ∨ a ∨ ¬b"""
#     def __init__(self, seq_num, params, concl):
#         super.__init__(self, seq_num, params, concl)

# class EquivPos2(Rule):
#     """¬(a ⟷ b) ∨ ¬a ∨ b"""
#     def __init__(self, seq_num, params, concl):
#         super.__init__(self, seq_num, params, concl)

# class EquivNeg1(Rule):
#     """(a ⟷ b) ∨ ¬a ∨ ¬b"""
#     def __init__(self, seq_num, params, concl):
#         super.__init__(self, seq_num, params, concl)

# class EquivNeg2(Rule):
#     """(a ⟷ b) ∨ a ∨ b"""
#     def __init__(self, seq_num, params, concl):
#         super.__init__(self, seq_num, params, concl)

# class ITEPos1(Rule):
#     """¬(ite a b c) ∨ a ∨ c"""
#     def __init__(self, seq_num, params, concl):
#         super.__init__(self, seq_num, params, concl)  

# class ITEPos2(Rule):
#     """¬(ite a b c) ∨ ¬a ∨ b"""
#     def __init__(self, seq_num, params, concl):
#         super.__init__(self, seq_num, params, concl)

# class ITENeg1(Rule):
#     """(ite a b c) ∨ a ∨ ¬c"""
#     def __init__(self, seq_num, params, concl):
#         super.__init__(self, seq_num, params, concl)  

# class ITEPos2(Rule):
#     """(ite a b c) ∨ ¬a ∨ ¬b"""
#     def __init__(self, seq_num, params, concl):
#         super.__init__(self, seq_num, params, concl)

# class EqReflexive(Rule):
#     """x = x"""
#     def __init__(self, seq_num, params, concl):
#         super.__init__(self, seq_num, params, concl)

# class EqTransitive(Rule):
#     """¬(x_1 = x_2 ∨ x_2 = x_3 ∨ ... ∨ x_{n-1} = x_n) ∨ x_1 = x_n"""
#     def __init__(self, seq_num, params, concl):
#         super.__init__(self, seq_num, params, concl)

# class EqCongurent(Rule):
#     """¬(x_1 = y_1 ∨ ... ∨ x_n = y_n) ∨ f x_1 ... x_n = f y_1 ... y_n"""
#     def __init__(self, seq_num, params, concl):
#         super.__init__(self, seq_num, params, concl)

# class EqCongurentPred(Rule):
#     """¬(x_1 = y_1) ∨ ... ∨ ¬(x_n = y_n) ∨ ¬(p x_1 ... x_n) ∨ (p y_1 ... y_n)"""
#     def __init__(self, seq_num, params, concl):
#         super.__init__(self, seq_num, params, concl)

# class EqCongurentGeneral(Rule):
#     """¬(x_1 = y_1) ∨ ... ∨ ¬(x_n = y_n) ∨ 
#     ¬(p t_1 ... x_1 ... t_m ... x_n) ∨ (p t_1 ... y_1 ... t_m ... y_n)"""
#     def __init__(self, seq_num, params, concl):
#         super.__init__(self, seq_num, params, concl)

# class DistinctElim(Rule):
#     """DIST x y ⟷ x ≠ y"""
#     def __init__(self, seq_num, params, concl):
#         super.__init__(self, seq_num, params, concl)

# class LaRwEq(Rule):
#     """x = y ⟷ x ≤ y ∧ x ≥ y"""
#     def __init__(self, seq_num, params, concl):
#         super.__init__(self, seq_num, params, concl)

# class LaGeneric(Rule):
#     """Not defined."""
#     def __init__(self, seq_num, params, concl):
#         super.__init__(self, seq_num, params, concl)

# class LiaGeneric(Rule):
#     """Not defined."""
#     def __init__(self, seq_num, params, concl):
#         super.__init__(self, seq_num, params, concl)

# class NlaGeneric(Rule):
#     """Not defined."""
#     def __init__(self, seq_num, params, concl):
#         super.__init__(self, seq_num, params, concl)

# class LaDisequality(Rule):
#     """Not defined."""
#     def __init__(self, seq_num, params, concl):
#         super.__init__(self, seq_num, params, concl)

# class LaTotality(Rule):
#     """t_1 ≤ t_2 ∨ t_2 ≤ t_1"""
#     def __init__(self, seq_num, params, concl):
#         super.__init__(self, seq_num, params, concl)

# class LaTautology(Rule):
#     """Linear arithmetic tautology without variable."""
#     def __init__(self, seq_num, params, concl):
#         super.__init__(self, seq_num, params, concl)

# class ForAllInst(Rule):
#     """∀x. A x --> A t"""
#     def __init__(self, seq_num, params, concl):
#         super.__init__(self, seq_num, params, concl)

# class ExistsInst(Rule):
#     """A t --> ∃x. A x"""
#     def __init__(self, seq_num, params, concl):
#         super.__init__(self, seq_num, params, concl)

# class Resolution(Rule):
#     """Resolution."""
#     def __init__(self, seq_num, params, concl):
#         super.__init__(self, seq_num, params, concl)

# class AndRule(Rule):
#     """a_1 ∧ ... ∧ a_n --> a_i"""
#     def __init__(self, seq_num, params, concl):
#         super.__init__(self, seq_num, params, concl)

# class NotOrRule(Rule):
#     """¬(a_1 ∨ ... ∨ a_n) --> ¬a_i"""
#     def __init__(self, seq_num, params, concl):
#         super.__init__(self, seq_num, params, concl)

# class OrRule(Rule):
#     """{(or a_1 ... a_n)} --> {a_1 ... a_n}"""
#     def __init__(self, seq_num, params, concl):
#         super.__init__(self, seq_num, params, concl)

# class NotAndRule(Rule):
#     """¬(a_1 ∧ ... ∧ a_n) --> ¬a_1 ∨ ... ∨ ¬a_n"""
#     def __init__(self, seq_num, params, concl):
#         super.__init__(self, seq_num, params, concl)

# class NotImplies1(Rule):
#     """¬(a --> b) ∨ a"""
#     def __init__(self, seq_num, params, concl):
#         super.__init__(self, seq_num, params, concl)

# class NotImplies2(Rule):
#     """¬(a --> b) ∨ ¬b"""
#     def __init__(self, seq_num, params, concl):
#         super.__init__(self, seq_num, params, concl)

# class Equiv1(Rule):
#     """a ⟷ b --> ¬a ∨ b """
#     def __init__(self, seq_num, params, concl):
#         super.__init__(self, seq_num, params, concl)

# class Equiv2(Rule):
#     """a ⟷ b --> a ∨ ¬b """
#     def __init__(self, seq_num, params, concl):
#         super.__init__(self, seq_num, params, concl)

# class NotEquiv1(Rule):
#     """¬(a ⟷ b) --> a ∨ b """
#     def __init__(self, seq_num, params, concl):
#         super.__init__(self, seq_num, params, concl)

# class NotEquiv2(Rule):
#     """¬(a ⟷ b) --> ¬a ∨ ¬b """
#     def __init__(self, seq_num, params, concl):
#         super.__init__(self, seq_num, params, concl)

# class ITE1(Rule):
#     """ite a b c --> a ∨ c"""
#     def __init__(self, seq_num, params, concl):
#         super.__init__(self, seq_num, params, concl)

# class ITE2(Rule):
#     """ite a b c --> ¬a ∨ b"""
#     def __init__(self, seq_num, params, concl):
#         super.__init__(self, seq_num, params, concl)

# class NotITE1(Rule):
#     """¬(ite a b c) --> a ∨ ¬c"""
#     def __init__(self, seq_num, params, concl):
#         super.__init__(self, seq_num, params, concl)

# class NotITE2(Rule):
#     """¬(ite a b c) --> ¬a ∨ ¬b"""
#     def __init__(self, seq_num, params, concl):
#         super.__init__(self, seq_num, params, concl)

