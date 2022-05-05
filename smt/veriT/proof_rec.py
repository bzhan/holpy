"""Proof reconstruction."""
import re
import os

from smt.veriT.proof_parser import decl_parser, proof_parser, smt_assertion_parser
from smt.veriT import command
from smt.veriT.verit_macro import NotOrMacro, verit_and_all, compare_sym_tm
from smt.veriT import la_generic
from kernel.proofterm import ProofTerm
from kernel.thm import Thm
from kernel import term
from kernel.term import Or
from kernel import theory
from logic import logic
from alive_progress import alive_bar


def bind_var(file_name: str) -> dict:
    """Convert the declaration in context to higher-order types and terms."""
    ctx = dict()
    with open(file_name, "r") as f:
        for s in f.readlines():
            if s.strip().startswith("(declare-fun"):
                tm = decl_parser.parse(s.strip())
                ctx.update(tm)
    return ctx

def matched_paras(s: str) -> bool:
    """check whether the parentheses in s are balanced"""
    count = 0
    for i in s:
        if i == "(":
            count += 1
        elif i == ")":
            count -= 1
        if count < 0:
            return False
    return count == 0

def get_complete_line(file_name: str) -> list:
    """given a text file, return lines with balanced parentheses"""
    with open(file_name, "r") as f:
        complete_lines = []
        s = ""
        for line in f.readlines():
            s += line
            if matched_paras(s):
                complete_lines.append(s)
                s = ""
        return complete_lines

def get_assertions(file_name: str) -> set:
    """return the assertions declared in file_name.smt2"""
    ctx = bind_var(file_name)
    parser = smt_assertion_parser(ctx)
    assertions = set()
    lines = get_complete_line(file_name)
    for s in lines:
        if s.startswith("(assert"):
            l = re.sub("\s{4,}"," ", s.replace("\n", ""))
            if l.startswith("(assert"):
                asst = parser.parse(l)
                assertions.add(asst)
            else:
                print("l", l)
                print("s", s)
                raise AssertionError

    return assertions

class ProofReconstruction:
    """Verit proof reconstruction.
    
    - steps: a list of parsed proof rules.
    """
    def __init__(self, steps, smt_assertions=set()) -> None:
        # set maximum memory usage as 8GB
        if os.name == 'posix':
            import resource
            _, hard = resource.getrlimit(resource.RLIMIT_AS)
            resource.setrlimit(resource.RLIMIT_AS, (8589934592, hard))
        # List of steps
        self.steps = steps

        # Dictionary from step id to steps
        self.steps_dict = dict()
        for step in self.steps:
            self.steps_dict[step.id] = step

        # map from step id to proof term
        self.pts = dict()

        # map from step id to steps
        self.step_map = {step.id : step for step in self.steps}

        # # a list of contexts
        self.ctx = dict()

        # current subproof id
        self.subprf_id = None

        # assumption
        self.assms = set()

        # indicate current anchor id, if the step is not in an anchor, it should be None
        self.anchor_id = None

        # store the original assertions declared in .smt2 file
        self.smt_assertions = smt_assertions

    def to_pts(self, ids):
        """ids is a tuple of step name, return their corresponding pts."""
        return tuple(self.pts[i] for i in ids)

    def get_clause_sizes(self, ids):
        """Return the list of clause sizes, used in resolution."""
        return tuple(self.steps_dict[i].get_clause_size() for i in ids)

    def add_subproof_context(self, step):
        self.ctx = step.ctx
        self.subprf_id = step.id

    def find_local_assms(self, step_id):
        """Find all assumptions declared in step_id's subproof."""
        assms = []
        for step in self.steps:
            if step.id.startswith(step_id):
                sub_ids = step.id.split(".")
                if sub_ids[:-1] == step_id.split(".") and isinstance(step, command.Assume):
                    assms.append(self.pts[step.id])

        return tuple(assms)

    def find_last_subproof(self, step_id):
        size = len(step_id.split("."))
        for i in range(len(self.steps)-1):
            if self.steps[i+1].id == step_id:
                if not isinstance(self.steps[i+1], command.Anchor) and not isinstance(self.steps[i], command.Anchor):
                    return self.pts[self.steps[i].id]

    def validate_step(self, step, is_eval=True, omit_proofterm=None):
        if omit_proofterm is None:
            omit_proofterm = []
        
        if self.anchor_id is not None and step.id == self.anchor_id:
            self.anchor_id = None

        if isinstance(step, command.Anchor):
            self.anchor_id = step.id
            return
        if isinstance(step, command.Assume):
            pt_assm = ProofTerm.assume(step.assm)
            self.pts[step.id] = pt_assm
            if self.anchor_id is None:
                self.assms.add(pt_assm.prop)
            return

        assert isinstance(step, command.Step)
        rule_name = step.rule_name
        # print(rule_name)
        macro_name = "verit_" + rule_name
        prevs = self.to_pts(step.pm)
        args = step.cl
        if rule_name == "refl":
            args += (step.cur_ctx,)
        elif rule_name == "let":
            last_prf = self.find_last_subproof(step.id)
            prevs += (last_prf,)
        elif rule_name in ("bind", "sko_ex", "sko_forall", "onepoint"):
            args += (step.cur_ctx,)
            last_prf = self.find_last_subproof(step.id)
            prevs += (last_prf,)
        elif rule_name in ("la_generic", "forall_inst"):
            args += step.args
        elif rule_name == "subproof":
            sub_assms = self.find_local_assms(step.id)
            last_prf = self.find_last_subproof(step.id)
            prevs += sub_assms
            prevs += (last_prf,)
        elif rule_name in ("resolution", "th_resolution"):
            args = (step.cl, self.get_clause_sizes(step.pm))
            macro_name = "verit_th_resolution"
        elif rule_name == "la_tautology":
            macro_name = "verit_la_generic"
            args += tuple([[]])
        elif rule_name == "lia_generic":
            raise AssertionError("currently lia_generic is not supported")

        # Evaluation case
        if is_eval or macro_name in omit_proofterm:
            self.pts[step.id] = ProofTerm(macro_name, args, prevs)
            return
        
        # Proofterm case
        if macro_name == "verit_and":
            if step.id not in self.pts:
                goal_to_id = dict()
                for st in self.steps:
                    if isinstance(st, command.Step) and st.rule_name == "and" and st.pm == step.pm:
                        goal_to_id[Or(*st.cl)] = st.id
                pts = verit_and_all(prevs[0], goal_to_id.keys())
                for pt in pts:
                    cur_id = goal_to_id[pt.prop]
                    self.pts[cur_id] = pt
        else:
            macro = theory.get_macro(macro_name)
            try:
                self.pts[step.id] = macro.get_proof_term(args, prevs)
            except NotImplementedError as e:
                print(step.id, rule_name)
                self.pts[step.id] = ProofTerm.sorry(
                    Thm(term.Or(*step.cl), *(self.pts[step_id].hyps for step_id in step.pm)))

        # Check proof term
        if self.pts[step.id] is None:
            print(macro_name)
            raise AssertionError("Returned theorem is None")

        if self.pts[step.id].prop != Or(*step.cl):
            print(macro_name)
            print("Computed: ", self.pts[step.id].prop)
            print("In proof: ", Or(*step.cl))
            raise AssertionError("Unexpected returned theorem")

        # Compare with eval
        eval_pt = ProofTerm(macro_name, args, prevs)
        if not set(self.pts[step.id].hyps) <= set(eval_pt.hyps):
            print(macro_name)
            print("Proofterm hyps:")
            for hyp in self.pts[step.id].hyps:
                print(hyp)
            print("Eval hyps:")
            for hyp in eval_pt.hyps:
                print(hyp)
            raise AssertionError("Disagreement between eval and proof term: hyps")
        if self.pts[step.id].prop != eval_pt.prop:
            print(macro_name)
            print("Proofterm prop:")
            print(self.pts[step.id].prop)
            print("Eval prop:")
            print(eval_pt.prop)
            raise AssertionError("Disagreement between eval and proof term: prop")


    def validate(self, is_eval=True, step_limit=None, omit_proofterm=None, with_bar=True):
        if with_bar:
            with alive_bar(len(self.steps), spinner=None, bar=None) as bar:
                for i, step in enumerate(self.steps):
                    self.validate_step(step, is_eval=is_eval, omit_proofterm=omit_proofterm)
                    bar()
                    if step_limit and i > step_limit:
                        break
        else:
            for i, step in enumerate(self.steps):
                self.validate_step(step, is_eval=is_eval, omit_proofterm=omit_proofterm)
                if step_limit and i > step_limit:
                    break

        # check hypothesis consistency
        def check_consistency(hyp):
            if hyp in self.smt_assertions:
                return True
            for smt_asst in self.smt_assertions:
                if compare_sym_tm(hyp, smt_asst):
                    return True
            return False

        if not set(self.pts[step.id].hyps) <= self.assms:
            raise AssertionError("not compatible with assertions given by veriT proof")

        if self.smt_assertions and not all(check_consistency(hyp) for hyp in self.pts[step.id].hyps):
            raise AssertionError("not compatible with assertions given by SMT file")
        try:
            return self.pts[step.id]
        except:
            print(self.steps)
            raise AssertionError("can't find the last proof")