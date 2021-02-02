"""
Basic proof rules in veriT solver.
"""
from smt.veriT.verit_macro import *
from kernel.proofterm import ProofTerm, Thm
from logic import basic, matcher, logic, conv
from kernel import term
import functools
from prover.proofrec import int_th_lemma_1_omega

basic.load_theory("verit")

class Concl(object):
    def __init__(self, *tms):
        self.tms = tms
    
    def __len__(self):
        return len(self.tms)
        

class Input(object):
    def __init__(self, seq_num, concl):
        self.seq_num = seq_num
        self.concl = concl

class Rule(object):
    def __init__(self, seq_num, proof_name, concl, assms=[], args=None):
        self.seq_num = seq_num
        self.proof_name = str(proof_name)
        arity = len(concl)
        if arity > 1:
            self.concl = Or(*concl.tms) 
        elif arity == 1:
            self.concl = concl.tms[0]
        else:
            self.concl = term.false
        self.arity = arity
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
        step_num = len(self.steps)
        for step in self.steps:
            try:
                self.reconstruct(step)
            except:
                print(step.seq_num)
                break
            print("{:.2%}".format(step.seq_num/step_num))
        print("finished")
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
        elif name == "not_equiv1":
            self.not_equiv1(step)
        elif name == "not_equiv2":
            self.not_equiv2(step)
        elif name == "equiv_pos1":
            self.equiv_pos1(step)
        elif name == "equiv_pos2":
            self.equiv_pos2(step)
        elif name == "equiv_neg1":
            self.equiv_neg1(step)
        elif name == "equiv_neg2":
            self.equiv_neg2(step)
        elif name == "tmp_distinct_elim":
            self.tmp_distinct_elim(step)
        elif name == "and_neg":
            self.and_neg(step)
        elif name == "tmp_LA_pre":
            self.tmp_LA_pre(step)
        elif name == "not_or":
            self.not_or_rule(step)
        elif name == "or_neg":
            self.or_neg(step)
        elif name == "not_and":
            self.not_and(step)
        elif name == "implies":
            self.implies_rule(step)
        elif name == "not_implies1":
            self.not_implies1(step)
        elif name == "not_implies2":
            self.not_implies2(step)
        elif name == "ite1":
            self.ite1(step)
        elif name == "ite2":
            self.ite2(step)
        elif name == "not_ite1":
            self.not_ite1(step)
        elif name == "not_ite2":
            self.not_ite2(step)
        elif name == "ite_pos1":
            self.ite_pos1(step)
        elif name == "ite_pos2":
            self.ite_pos2(step)
        elif name == "ite_neg1":
            self.ite_neg1(step)
        elif name == "ite_neg2":
            self.ite_neg2(step)
        elif name == "la_generic":
            self.la_generic(step)
        elif name == "la_disequality":
            self.la_disequality(step)
        elif name == "eq_congruent_pred":
            self.eq_congruent_pred(step)
        # elif name == "tmp_ite_elim":
        #     self.tmp_ite_elim(step)
        else:   
            self.not_imp(step)
    
    def not_imp(self, step):
        print(step.seq_num, step.proof_name)
        if step.proof_name != "tmp_ite_elim":
            print(step)
        self.proof[step.seq_num] = ProofTerm.sorry(Thm([hyp for i in step.assms for hyp in self.proof[i].hyps], step.concl))

    def schematic_rule1(self, th_name, pt):
        """
        The th is in a ⊢ A --> B form, pt is ⊢ A, return ⊢ B. 
        """
        pt_th = ProofTerm.theorem(th_name)
        inst = matcher.first_order_match(pt_th.prop.arg1, pt.prop)
        pt_th_inst = pt_th.substitution(inst=inst)
        return pt_th_inst.implies_elim(pt).on_prop(conv.top_conv(conv.rewr_conv("double_neg")))

    def schematic_rule2(self, th_name, tm):
        """
        The th is in ⊢ A, A is a tautology, instantiate th by tm.
        """
        pt_th = ProofTerm.theorem(th_name)
        inst = matcher.first_order_match(pt_th.prop.arg1, tm.arg1)
        return pt_th.substitution(inst=inst).on_prop(conv.top_conv(conv.rewr_conv("double_neg")))

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
        pt_th = ProofTerm.theorem("forall_inst")
        inst = matcher.first_order_match(pt_th.prop, step.concl)
        self.proof[step.seq_num] = pt_th.substitution(inst=inst).on_prop(conv.top_conv(conv.beta_conv()))

    def or_pos(self, step):
        """⊢ ¬(a_1 ∨ ... ∨ a_n) ∨ a_1 ∨ ... ∨ a_n"""
        # self.proof[step.seq_num] = self.schematic_rule2("or_pos", step.concl)
        self.proof[step.seq_num] = ProofTerm("or_pos", step.concl)

    def or_rule(self, step):
        """
        {(or a_1 ... a_n)} --> {a_1 ... a_n}
        this rule doesn't have effect in HOL, so return the assms[0]
        """
        self.proof[step.seq_num] = self.proof[step.assms[0]]

    def resolution(self, step):
        """Given a sequence of proof terms, take resolution on them one by one."""
        res_pts = [self.proof[num] for num in step.assms]
        pt_0 = self.proof[step.assms[0]]
        arity1 = self.steps[step.assms[0]-1].arity
        for i in step.assms[1:]:
            arity2 = self.steps[i-1].arity
            assert self.proof[i].prop == self.steps[i-1].concl, i
            pt_1 = pt_0
            pt_0, arity1 = verit_resolution(pt_0, self.proof[i], arity1, arity2)

        if pt_0.prop == step.concl:
            self.proof[step.seq_num] = pt_0
        else:
            concl_disjs = strip_num(step.concl, step.arity)
            pt_disjs = strip_num(pt_0.prop, step.arity)
            assert set(concl_disjs) == set(pt_disjs)
            implies_pt_norm = ProofTerm("imp_disj", term.Implies(pt_0.prop, Or(*concl_disjs)))
            self.proof[step.seq_num] = implies_pt_norm.implies_elim(pt_0)

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

    def not_equiv1(self, step):
        """¬(P ⟷ Q) ⟶ P ∨ Q"""
        self.proof[step.seq_num] = self.schematic_rule1("not_equiv1", self.proof[step.assms[0]])

    def not_equiv2(self, step):
        """¬(P ⟷ Q) ⟶ ¬P ∨ ¬Q"""
        self.proof[step.seq_num] = self.schematic_rule1("not_equiv2", self.proof[step.assms[0]])

    def equiv_pos1(self, step):
        """¬(a ⟷ b) ∨ a ∨ ¬b"""
        self.proof[step.seq_num] = self.schematic_rule2("equiv_pos1", step.concl)

    def equiv_pos2(self, step):
        """¬(a ⟷ b) ∨ a ∨ ¬b"""
        self.proof[step.seq_num] = self.schematic_rule2("equiv_pos2", step.concl)

    def equiv_neg1(self, step):
        """(a ⟷ b) ∨ ¬a ∨ ¬b"""
        self.proof[step.seq_num] = self.schematic_rule2("equiv_neg1", step.concl)

    def equiv_neg2(self, step):
        """(a ⟷ b) ∨ a ∨ b"""
        self.proof[step.seq_num] = self.schematic_rule2("equiv_neg2", step.concl)

    def tmp_distinct_elim(self, step):
        """formula where distinct have been eliminated, which have done in the parsing process."""
        self.proof[step.seq_num] = self.proof[step.assms[0]]

    def and_neg(self, step):
        """⊢ (a_1 ∧ ... ∧ a_n) ∨ ¬a_1 ∨ ... ∨ ¬a_n"""
        self.proof[step.seq_num] = ProofTerm("and_neg", [step.arity, step.concl])

    def tmp_LA_pre(self, step):
        """formula with = replaced by conjunction of two inequalities"""
        self.proof[step.seq_num] = self.proof[step.assms[0]].on_prop(conv.top_conv(conv.rewr_conv("tmp_LA_pre_int")))        

    def not_or_rule(self, step):
        """¬(a_1 ∨ ... ∨ a_n) --> ¬a_i"""
        self.proof[step.seq_num] = ProofTerm("not_or_rule", [step.concl], [self.proof[i] for i in step.assms])

    def or_neg(self, step):
        """⊢ (a_1 ∨ ... ∨ a_n) ∨ ¬a_i"""
        concl = step.concl
        disj, atom = concl.arg1, concl.arg
        if atom.is_not():
            pt0 = ProofTerm("imp_disj", term.Implies(atom.arg, disj))
        else:
            pt0 = ProofTerm("imp_disj", term.Implies(term.Not(atom), disj))
        pt1 = pt0.on_prop(conv.rewr_conv("imp_disj_eq"), conv.rewr_conv("disj_comm"))
        self.proof[step.seq_num] = pt1

    def not_and(self, step):
        """⊢ ¬(a_1 ∧ ... ∧ a_n) --> ¬a_1 ∨ ... ∨ ¬a_n"""
        arity = len(step.concl.arg.strip_disj())
        pt = ProofTerm("not_and", [step.concl], [self.proof[step.assms[0]]])
        self.proof[step.seq_num] = pt

    def implies_rule(self, step):
        """{(implies a b)} --> {(not a) b}"""
        self.proof[step.seq_num] = self.proof[step.assms[0]].on_prop(conv.rewr_conv("imp_disj_eq"))

    def not_implies1(self, step):
        """¬(a --> b) --> a"""
        self.proof[step.seq_num] = self.schematic_rule1("not_implies1", self.proof[step.assms[0]])

    def not_implies2(self, step):
        """¬(a --> b) --> ¬b"""
        self.proof[step.seq_num] = self.schematic_rule1("not_implies2", self.proof[step.assms[0]])

    def ite1(self, step):
        """ite a b c --> a ∨ c"""
        self.proof[step.seq_num] = self.schematic_rule1("verit_ite1", self.proof[step.assms[0]])

    def ite2(self, step):
        """ite a b c --> ¬a ∨ b"""
        self.proof[step.seq_num] = self.schematic_rule1("verit_ite2", self.proof[step.assms[0]])
    
    def not_ite1(self, step):
        """¬(ite a b c) --> a ∨ ¬c"""
        self.proof[step.seq_num] = self.schematic_rule1("verit_not_ite1", self.proof[step.assms[0]])

    def not_ite2(self, step):
        """¬(ite a b c) --> ¬a ∨ ¬b"""
        self.proof[step.seq_num] = self.schematic_rule1("verit_not_ite2", self.proof[step.assms[0]])

    def la_generic(self, step):
        """"""
        self.proof[step.seq_num] = ProofTerm("la_generic", step.concl)
    
    def eq_congruent_pred(self, step):
        """{(not (= x_1 y_1)) ... (not (= x_n y_n)) (not (p x_1 ... x_n)) (p y_1 ... y_n)}"""
        try:
            self.proof[step.seq_num] = ProofTerm("verit_eq_congurent_pred", step.concl)
        except:
            self.not_imp(step)

    def la_disequality(self, step):
        self.proof[step.seq_num] = self.schematic_rule2("la_disequality", step.concl)
        assert self.proof[step.seq_num].prop == step.concl

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

