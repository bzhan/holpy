# Author: Bohua Zhan

from kernel.type import Type, TFun, boolT
from kernel.term import Term, Var, Const
from kernel.thm import Thm
from kernel.macro import global_macros
from kernel.theory import Method, global_methods
from data import nat
from data import function
from logic import logic
from logic.conv import arg_conv, then_conv, top_conv, beta_conv, binop_conv, \
    every_conv, rewr_conv, assums_conv, beta_norm
from logic.proofterm import ProofTerm, ProofTermMacro, ProofTermDeriv
from logic.logic import apply_theorem
from syntax import pprint, settings
from server.tactic import Tactic, MacroTactic
from prover import z3wrapper


"""Automation for Hoare logic."""

def comT(T):
    return Type("com", T)

def Skip(T):
    return Const("Skip", comT(T))

def Assign(Ta, Tb):
    return Const("Assign", TFun(Ta, TFun(TFun(Ta, Tb), Tb), comT(TFun(Ta, Tb))))

def Seq(T):
    return Const("Seq", TFun(comT(T), comT(T), comT(T)))

def Cond(T):
    return Const("Cond", TFun(TFun(T, boolT), comT(T), comT(T), comT(T)))

def While(T):
    return Const("While", TFun(TFun(T, boolT), TFun(T, boolT), comT(T), comT(T)))

def Sem(T):
    return Const("Sem", TFun(comT(T), T, T, boolT))

def Valid(T):
    return Const("Valid", TFun(TFun(T, boolT), comT(T), TFun(T, boolT), boolT))

def Entail(T):
    return Const("Entail", TFun(TFun(T, boolT), TFun(T, boolT), boolT))

# Normalize evaluation of function as well as arithmetic.
norm_cv = then_conv(top_conv(function.fun_upd_eval_conv()), nat.norm_full())

# Normalize a condition.
norm_cond_cv = every_conv(
    norm_cv,
    top_conv(nat.nat_eq_conv()),
    logic.norm_bool_expr()
)

def eval_Sem(thy, com, st):
    """Evaluates the effect of program com on state st."""
    f, args = com.strip_comb()
    T = st.get_type()
    if f.is_const_name("Skip"):
        return apply_theorem(thy, "Sem_Skip", tyinst={"a": T}, inst={"s": st})
    elif f.is_const_name("Assign"):
        a, b = args
        Ta = a.get_type()
        Tb = b.get_type().range_type()
        pt = apply_theorem(thy, "Sem_Assign", tyinst={"a": Ta, "b": Tb}, inst={"a": a, "b": b, "s": st})
        return pt.on_arg(thy, arg_conv(norm_cv))
    elif f.is_const_name("Seq"):
        c1, c2 = args
        pt1 = eval_Sem(thy, c1, st)
        pt2 = eval_Sem(thy, c2, pt1.prop.arg)
        pt = apply_theorem(thy, "Sem_seq", pt1, pt2)
        return pt.on_arg(thy, function.fun_upd_norm_one_conv())
    elif f.is_const_name("Cond"):
        b, c1, c2 = args
        b_st = beta_norm(thy, b(st))
        b_eval = norm_cond_cv.get_proof_term(thy, b_st)
        if b_eval.prop.arg == logic.true:
            b_res = rewr_conv("eq_true", sym=True).apply_to_pt(thy, b_eval)
            pt1 = eval_Sem(thy, c1, st)
            return apply_theorem(thy, "Sem_if1", b_res, pt1, concl=Sem(T)(com, st, pt1.prop.arg))
        else:
            b_res = rewr_conv("eq_false", sym=True).apply_to_pt(thy, b_eval)
            pt2 = eval_Sem(thy, c2, st)
            return apply_theorem(thy, "Sem_if2", b_res, pt2, concl=Sem(T)(com, st, pt2.prop.arg))
    elif f.is_const_name("While"):
        b, inv, c = args
        b_st = beta_norm(thy, b(st))
        b_eval = norm_cond_cv.get_proof_term(thy, b_st)
        if b_eval.prop.arg == logic.true:
            b_res = rewr_conv("eq_true", sym=True).apply_to_pt(thy, b_eval)
            pt1 = eval_Sem(thy, c, st)
            pt2 = eval_Sem(thy, com, pt1.prop.arg)
            pt = apply_theorem(thy, "Sem_while_loop", b_res, pt1, pt2,
                               concl=Sem(T)(com, st, pt2.prop.arg), inst={"s3": pt1.prop.arg})
            return pt.on_arg(thy, function.fun_upd_norm_one_conv())
        else:
            b_res = rewr_conv("eq_false", sym=True).apply_to_pt(thy, b_eval)
            return apply_theorem(thy, "Sem_while_skip", b_res, concl=Sem(T)(com, st, st))
    else:
        raise NotImplementedError

class eval_Sem_macro(ProofTermMacro):
    """Prove a theorem of the form Sem com st st2."""
    def __init__(self):
        self.level = 10
        self.sig = Term
        self.limit = 'Sem_Assign'

    def can_eval(self, thy, goal):
        assert isinstance(goal, Term), "eval_Sem_macro"
        f, (com, st, st2) = goal.strip_comb()
        try:
            pt = eval_Sem(thy, com, st)
        except NotImplementedError:
            return False
        return st2 == pt.prop.arg        

    def get_proof_term(self, thy, args, pts):
        assert len(pts) == 0, "eval_Sem_macro"
        f, (com, st, st2) = args.strip_comb()
        pt = eval_Sem(thy, com, st)
        assert st2 == pt.prop.arg, "eval_Sem_macro: wrong result."
        return pt

class eval_Sem_method(Method):
    """Apply eval_Sem macro."""
    def __init__(self):
        self.sig = []
        self.limit = 'Sem_Assign'

    def search(self, state, id, prevs, data=None):
        if data:
            return [data]

        if len(prevs) != 0:
            return []

        cur_th = state.get_proof_item(id).th
        if eval_Sem_macro().can_eval(state.thy, cur_th.prop):
            return [{}]
        else:
            return []

    @settings.with_settings
    def display_step(self, state, data):
        return pprint.N("eval_Sem: (solves)")

    def apply(self, state, id, data, prevs):
        assert len(prevs) == 0, "eval_Sem_method"
        state.apply_tactic(id, MacroTactic('eval_Sem'))


def compute_wp(thy, T, c, Q):
    """Compute the weakest precondition for the given command
    and postcondition. Here c is the program and Q is the postcondition.
    The computation is by case analysis on the form of c. The function
    returns a proof term showing [...] |- Valid P c Q, where P is the
    computed precondition, and [...] contains the additional subgoals.

    """
    if c.head.is_const_name("Skip"):  # Skip
        return apply_theorem(thy, "skip_rule", concl=Valid(T)(Q, c, Q))
    elif c.head.is_const_name("Assign"):  # Assign a b
        a, b = c.args
        s = Var("s", T)
        P2 = Term.mk_abs(s, Q(function.mk_fun_upd(s, a, b(s).beta_conv())))
        return apply_theorem(thy, "assign_rule", inst={"b": b}, concl=Valid(T)(P2, c, Q))
    elif c.head.is_const_name("Seq"):  # Seq c1 c2
        c1, c2 = c.args
        wp1 = compute_wp(thy, T, c2, Q)  # Valid Q' c2 Q
        wp2 = compute_wp(thy, T, c1, wp1.prop.args[0])  # Valid Q'' c1 Q'
        return apply_theorem(thy, "seq_rule", wp2, wp1)
    elif c.head.is_const_name("Cond"):  # Cond b c1 c2
        b, c1, c2 = c.args
        wp1 = compute_wp(thy, T, c1, Q)
        wp2 = compute_wp(thy, T, c2, Q)
        res = apply_theorem(thy, "if_rule", wp1, wp2, inst={"b": b})
        return res
    elif c.head.is_const_name("While"):  # While b I c
        _, I, _ = c.args
        pt = apply_theorem(thy, "while_rule", concl=Valid(T)(I, c, Q))
        pt0 = ProofTerm.assume(pt.assums[0])
        pt1 = vcg(thy, T, pt.assums[1])
        return ProofTerm.implies_elim(pt, pt0, pt1)
    else:
        raise NotImplementedError

def vcg(thy, T, goal):
    """Compute the verification conditions for the goal. Here the
    goal is of the form Valid P c Q. The function returns a proof term
    showing [] |- Valid P c Q.
    
    """
    P, c, Q = goal.args
    pt = compute_wp(thy, T, c, Q)
    entail_P = ProofTerm.assume(Entail(T)(P, pt.prop.args[0]))
    return apply_theorem(thy, "pre_rule", entail_P, pt)

def vcg_norm(thy, T, goal):
    """Compute vcg, then normalize the result into the form

    A_1 --> A_2 --> ... --> A_n --> Valid P c Q,

    where A_i are the normalized verification conditions.

    """
    pt = vcg(thy, T, goal)
    for A in reversed(pt.hyps):
        pt = ProofTerm.implies_intr(A, pt)

    # Normalize each of the assumptions
    return pt.on_assums(thy, rewr_conv("Entail_def"), top_conv(beta_conv()),
                        top_conv(function.fun_upd_eval_conv()))

class vcg_macro(ProofTermMacro):
    """Macro wrapper for verification condition generation.
    
    Compute the verification conditions for a hoare triple, then
    normalizes the verification conditions, finally uses the previous
    facts to discharge the verification conditions.
    
    """
    def __init__(self):
        self.level = 10
        self.sig = Term
        self.limit = 'while_rule'

    def get_proof_term(self, thy, goal, pts):
        f, (P, c, Q) = goal.strip_comb()
        assert f.is_const_name("Valid"), "vcg_macro"

        # Obtain the theorem [...] |- Valid P c Q
        T = Q.get_type().domain_type()
        pt = vcg_norm(thy, T, goal)

        # Discharge the assumptions using the previous facts
        return ProofTerm.implies_elim(pt, *pts)

class vcg_tactic(Tactic):
    """Tactic corresponding to VCG macro."""
    def get_proof_term(self, thy, goal, args, prevs):
        assert len(goal.hyps) == 0, "vcg_tactic"
        f, (P, c, Q) = goal.prop.strip_comb()
        assert f.is_const_name("Valid"), "vcg_tactic"

        # Obtain the theorem [...] |- Valid P c Q
        T = Q.get_type().domain_type()
        pt = vcg_norm(thy, T, goal.prop)

        ptAs = [ProofTerm.sorry(Thm(goal.hyps, A)) for A in pt.assums]
        return ProofTermDeriv("vcg", thy, goal.prop, ptAs)


def vcg_solve(thy, goal):
    """Compute the verification conditions for a hoare triple, then
    solves the verification conditions using SMT.
    
    """
    f, (P, c, Q) = goal.strip_comb()
    assert f.is_const_name("Valid"), "vcg_solve"

    T = Q.get_type().domain_type()
    pt = vcg_norm(thy, T, goal)
    vc_pt = [ProofTermDeriv("z3", thy, vc, []) for vc in pt.assums]
    return ProofTermDeriv("vcg", thy, goal, vc_pt)

class vcg_method(Method):
    """Method corresponding to VCG."""
    def __init__(self):
        self.sig = []
        self.limit = 'while_rule'

    def search(self, state, id, prevs, data=None):
        if data:
            return [data]

        cur_th = state.get_proof_item(id).th
        if len(cur_th.hyps) == 0 and cur_th.prop.head.is_const_name("Valid"):
            return [{}]
        else:
            return []

    @settings.with_settings
    def display_step(self, state, data):
        return pprint.N("Apply VCG")

    def apply(self, state, id, data, prevs):
        state.apply_tactic(id, vcg_tactic(), prevs=prevs)


global_macros.update({
    "eval_Sem": eval_Sem_macro(),
    "vcg": vcg_macro(),
})

global_methods.update({
    "eval_Sem": eval_Sem_method(),
    "vcg": vcg_method(),
})
