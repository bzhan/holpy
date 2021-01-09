"""
Basic proof rules in veriT solver.
"""


class Rule(object):
    def __init__(self, seq_num, concl):
        self.seq_num = seq_num
        self.concl = concl


class Input(Rule):
    """Assertion."""
    def __init__(self, seq_num, concl):
        super.__init__(self, seq_num, concl)

class TrueRule(Rule):
    """⊢ true"""
    def __init__(self, seq_num, concl):
        super.__init__(self, seq_num, concl)

class FalseRule(Rule):
    """⊢ ¬false"""
    def __init__(self, seq_num):
        super.__init__(self, seq_num, concl)

class AndPos(Rule):
    """⊢ ¬(a_1 ∧ ... ∧ a_n) ∨ a_i"""
    def __init__(self, seq_num, concl):
        super.__init__(self, seq_num, concl)

class AndNeg(Rule):
    """⊢ (a_1 ∧ ... ∧ a_n) ∨ ¬a_1 ∨ ... ∨ ¬a_n"""
    def __init__(self, seq_num, concl):
        super.__init__(self, seq_num, concl)

class OrPos(Rule):
    """⊢ ¬(a_1 ∨ ... ∨ a_n) ∨ a_1 ∨ ... ∨ a_n"""
    def __init__(self, seq_num, concl):
        super.__init__(self, seq_num, concl)

class OrNeg(Rule):
    """⊢ (a_1 ∨ ... ∨ a_n) ∨ ¬a_i"""
    def __init__(self, seq_num, concl):
        super.__init__(self, seq_num, concl)

class ImpliesPos(Rule):
    """⊢ ¬(a ⟶ b) ∨ ¬a ∨ b"""
    def __init__(self, seq_num, concl):
        super.__init__(self, seq_num, concl)

class ImpliesNeg1(Rule):
    """⊢ (a ⟶ b) ∨ a"""
    def __init__(self, seq_num, concl):
        super.__init__(self, seq_num, concl)

class ImpliesNeg2(Rule):
    """⊢ (a ⟶ b) ∨ ¬b"""
    def __init__(self, seq_num, concl):
        super.__init__(self, seq_num, concl)

class EquivPos1(Rule):
    """¬(a ⟷ b) ∨ a ∨ ¬b"""
    def __init__(self, seq_num, concl):
        super.__init__(self, seq_num, concl)

class EquivPos2(Rule):
    """¬(a ⟷ b) ∨ ¬a ∨ b"""
    def __init__(self, seq_num, concl):
        super.__init__(self, seq_num, concl)

class EquivNeg1(Rule):
    """(a ⟷ b) ∨ ¬a ∨ ¬b"""
    def __init__(self, seq_num, concl):
        super.__init__(self, seq_num, concl)

class EquivNeg2(Rule):
    """(a ⟷ b) ∨ a ∨ b"""
    def __init__(self, seq_num, concl):
        super.__init__(self, seq_num, concl)

class ITEPos1(Rule):
    """¬(ite a b c) ∨ a ∨ c"""
    def __init__(self, seq_num, concl):
        super.__init__(self, seq_num, concl)  

class ITEPos2(Rule):
    """¬(ite a b c) ∨ ¬a ∨ b"""
    def __init__(self, seq_num, concl):
        super.__init__(self, seq_num, concl)

class ITENeg1(Rule):
    """(ite a b c) ∨ a ∨ ¬c"""
    def __init__(self, seq_num, concl):
        super.__init__(self, seq_num, concl)  

class ITEPos2(Rule):
    """(ite a b c) ∨ ¬a ∨ ¬b"""
    def __init__(self, seq_num, concl):
        super.__init__(self, seq_num, concl)

class EqReflexive(Rule):
    """x = x"""
    def __init__(self, seq_num, concl):
        super.__init__(self, seq_num, concl)

class EqTransitive(Rule):
    """¬(x_1 = x_2 ∨ x_2 = x_3 ∨ ... ∨ x_{n-1} = x_n) ∨ x_1 = x_n"""
    def __init__(self, seq_num, concl):
        super.__init__(self, seq_num, concl)

class EqCongurent(Rule):
    """¬(x_1 = y_1 ∨ ... ∨ x_n = y_n) ∨ f x_1 ... x_n = f y_1 ... y_n"""
    def __init__(self, seq_num, concl):
        super.__init__(self, seq_num, concl)

class EqCongurentPred(Rule):
    """¬(x_1 = y_1) ∨ ... ∨ ¬(x_n = y_n) ∨ ¬(p x_1 ... x_n) ∨ (p y_1 ... y_n)"""
    def __init__(self, seq_num, concl):
        super.__init__(self, seq_num, concl)

class EqCongurentGeneral(Rule):
    """¬(x_1 = y_1) ∨ ... ∨ ¬(x_n = y_n) ∨ 
    ¬(p t_1 ... x_1 ... t_m ... x_n) ∨ (p t_1 ... y_1 ... t_m ... y_n)"""
    def __init__(self, seq_num, concl):
        super.__init__(self, seq_num, concl)

class DistinctElim(Rule):
    """DIST x y ⟷ x ≠ y"""
    def __init__(self, seq_num, concl):
        super.__init__(self, seq_num, concl)

class LaRwEq(Rule):
    """x = y ⟷ x ≤ y ∧ x ≥ y"""
    def __init__(self, seq_num, concl):
        super.__init__(self, seq_num, concl)

class LaGeneric(Rule):
    """Not defined."""
    def __init__(self, seq_num, concl):
        super.__init__(self, seq_num, concl)

class LiaGeneric(Rule):
    """Not defined."""
    def __init__(self, seq_num, concl):
        super.__init__(self, seq_num, concl)

class NlaGeneric(Rule):
    """Not defined."""
    def __init__(self, seq_num, concl):
        super.__init__(self, seq_num, concl)

class LaDisequality(Rule):
    """Not defined."""
    def __init__(self, seq_num, concl):
        super.__init__(self, seq_num, concl)

class LaTotality(Rule):
    """t_1 ≤ t_2 ∨ t_2 ≤ t_1"""
    def __init__(self, seq_num, concl):
        super.__init__(self, seq_num, concl)

class LaTautology(Rule):
    """Linear arithmetic tautology without variable."""
    def __init__(self, seq_num, concl):
        super.__init__(self, seq_num, concl)

class ForAllInst(Rule):
    """∀x. A x --> A t"""
    def __init__(self, seq_num, concl):
        super.__init__(self, seq_num, concl)

class ExistsInst(Rule):
    """A t --> ∃x. A x"""
    def __init__(self, seq_num, concl):
        super.__init__(self, seq_num, concl)

class Resolution(Rule):
    """Resolution."""
    def __init__(self, seq_num, concl):
        super.__init__(self, seq_num, concl)

class AndRule(Rule):
    """a_1 ∧ ... ∧ a_n --> a_i"""
    def __init__(self, seq_num, concl):
        super.__init__(self, seq_num, concl)

class NotOrRule(Rule):
    """¬(a_1 ∨ ... ∨ a_n) --> ¬a_i"""
    def __init__(self, seq_num, concl):
        super.__init__(self, seq_num, concl)

class OrRule(Rule):
    """{(or a_1 ... a_n)} --> {a_1 ... a_n}"""
    def __init__(self, seq_num, concl):
        super.__init__(self, seq_num, concl)

class NotAndRule(Rule):
    """¬(a_1 ∧ ... ∧ a_n) --> ¬a_1 ∨ ... ∨ ¬a_n"""
    def __init__(self, seq_num, concl):
        super.__init__(self, seq_num, concl)

class NotImplies1(Rule):
    """¬(a --> b) ∨ a"""
    def __init__(self, seq_num, concl):
        super.__init__(self, seq_num, concl)

class NotImplies2(Rule):
    """¬(a --> b) ∨ ¬b"""
    def __init__(self, seq_num, concl):
        super.__init__(self, seq_num, concl)

class Equiv1(Rule):
    """a ⟷ b --> ¬a ∨ b """
    def __init__(self, seq_num, concl):
        super.__init__(self, seq_num, concl)

class Equiv2(Rule):
    """a ⟷ b --> a ∨ ¬b """
    def __init__(self, seq_num, concl):
        super.__init__(self, seq_num, concl)

class NotEquiv1(Rule):
    """¬(a ⟷ b) --> a ∨ b """
    def __init__(self, seq_num, concl):
        super.__init__(self, seq_num, concl)

class NotEquiv2(Rule):
    """¬(a ⟷ b) --> ¬a ∨ ¬b """
    def __init__(self, seq_num, concl):
        super.__init__(self, seq_num, concl)

class ITE1(Rule):
    """ite a b c --> a ∨ c"""
    def __init__(self, seq_num, concl):
        super.__init__(self, seq_num, concl)

class ITE2(Rule):
    """ite a b c --> ¬a ∨ b"""
    def __init__(self, seq_num, concl):
        super.__init__(self, seq_num, concl)

class NotITE1(Rule):
    """¬(ite a b c) --> a ∨ ¬c"""
    def __init__(self, seq_num, concl):
        super.__init__(self, seq_num, concl)

class NotITE2(Rule):
    """¬(ite a b c) --> ¬a ∨ ¬b"""
    def __init__(self, seq_num, concl):
        super.__init__(self, seq_num, concl)

