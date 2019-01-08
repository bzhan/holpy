# Author: Bohua Zhan

import io

from kernel.term import Term, Var
from kernel.thm import Thm
from kernel.proof import ProofItem, Proof
from kernel.report import ProofReport
from logic.basic import BasicTheory
from logic import logic, matcher
from logic.proofterm import ProofTerm
from logic.conv import top_conv, rewr_conv
from syntax import parser, printer


class TacticException(Exception):
    pass

# Helper functions

def parse_proof(thy, input):
    """Parse the given proof in string form."""
    prf = Proof()
    ctxt = {}
    for line in input:
        if line.startswith("var "):
            name, T = parser.parse_var_decl(thy, line)
            assert name not in ctxt, "variable already declared"
            ctxt[name] = T
            prf.vars.append(Var(name, T))
        else:
            prf.items.append(parser.parse_proof_rule(thy, ctxt, line))
    return prf

def incr_id(id, start, n):
    """Increment the given id by n, with the starting integer index given
    by start.

    """
    if id.startswith("S") and int(id[1:]) >= start:
        return "S" + str(int(id[1:]) + n)
    else:
        return id

def incr_proof_item(item, start, n):
    """Increment all ids in the given proof item."""
    return ProofItem(incr_id(item.id, start, n), item.rule, args=item.args,
        prevs=[incr_id(id, start, n) for id in item.prevs], th=item.th)

def decr_id(id, id_remove=0):
    """Decrement a single id, with the aim of closing the gap at id_remove.
    id_remove defaults to 0 (decrement all ids > 0).
    
    """
    if id.startswith("S") and int(id[1:]) > id_remove:
        return "S" + str(int(id[1:]) - 1)
    else:
        return id

def decr_proof_item(item, id_remove):
    """Decrement all ids in the given proof item."""
    return ProofItem(decr_id(item.id, id_remove), item.rule, args=item.args,
        prevs=[decr_id(id, id_remove) for id in item.prevs], th=item.th)

def strip_all_implies(t, names):
    """Given a term of the form

    !x_1 ... x_k. A_1 --> ... --> A_n --> C.

    Return the triple ([v_1, ..., v_k], [A_1, ... A_n], C), where
    v_1, ..., v_k are new variables with the given names, and
    A_1, ..., A_n, C are the body of the input term, with bound variables
    substituted for v_1, ..., v_k.

    """
    if Term.is_all(t):
        assert len(names) > 0, "strip_all_implies: not enough names input."
        v = Var(names[0], t.arg.T)
        vars, As, C = strip_all_implies(t.arg.subst_bound(v), names[1:])
        return ([v] + vars, As, C)
    else:
        assert len(names) == 0, "strip_all_implies: too many names input."
        As, C = t.strip_implies()
        return ([], As, C)


class ProofState():
    """Represents proof state on the server side."""

    def __init__(self, vars, assums, concl):
        """Given a theorem statement, construct the initial partial proof.
        
        assums - assumptions of the theorem A1, ... An.
        concl - conclusion of the theorem C.
        
        Constructs:

        A1: assume A1
        ...
        An: assume An
        S1: C by sorry
        S2: An --> C by implies_intr An from S1
        ...
        S{n+1}: A1 --> ... --> An --> C by implies_intr A1 from Sn.
        
        """
        self.thy = BasicTheory

        self.vars = vars
        self.assums = assums
        self.concl = concl

        self.prf = Proof(*assums)
        self.prf.add_item("S1", "sorry", th=Thm(assums, concl))
        self.prf.vars = vars
        for n, assum in enumerate(reversed(assums), 2):
            self.prf.add_item("S" + str(n), "implies_intr", args=assum, prevs=["S" + str(n-1)])
        self.check_proof()

    @staticmethod
    def parse_init_state(data):
        """Obtain proof state from a data dictionary."""
        thy = BasicTheory
        ctxt = {}
        vars = []
        assums = []
        for var in data.get('variables'):
            name, t = parser.parse_var_decl(thy, var)
            if name and t:
                vars.append(Var(name, t))
                ctxt[name] = t
        for assum in data.get('assumes'):
            t = parser.parse_term(thy, ctxt, assum)
            if t:
                assums.append(t)
        concl = parser.parse_term(thy, ctxt, data.get('conclusion'))
        return ProofState(vars, assums, concl)

    def parse_proof(self, input):
        """Parse the given proof in string form."""
        self.prf = parse_proof(self.thy, io.StringIO(input))

    def print_proof(self):
        """Print proof for user-interface."""
        def term_printer(t):
            return printer.print_term(self.thy, t, unicode=True, print_abs_type=True)
        return self.prf.print(term_printer=term_printer, print_vars=True, unicode=True)

    def check_proof(self, *, no_gaps=False):
        """Check the given proof. Report is stored in rpt."""
        self.rpt = ProofReport()
        return self.thy.check_proof(self.prf, rpt=self.rpt, no_gaps=no_gaps)

    def obtain_init_data(self):
        """Returns the initial string values for variables, assumptions,
        and conclusion.

        """
        def print_variable(v):
            return "var " + v.name + " :: " + str(v.T)

        def print_term(t):
            return printer.print_term(self.thy, t, unicode=True, print_abs_type=True)

        return {
            "variables": [print_variable(v) for v in self.vars],
            "assumes": [print_term(t) for t in self.assums],
            "conclusion": print_term(self.concl)
        }

    def add_line_after(self, id):
        """Add given line after the given id."""
        # Determine the index of the new line.
        if id.startswith("S"):
            id_new = int(id[1:]) + 1
        else:
            id_new = 1

        new_prf = Proof()
        new_prf.vars = self.prf.vars
        for item in self.prf.items:
            new_prf.items.append(incr_proof_item(item, id_new, 1))
            if item.id == id:
                new_prf.add_item("S" + str(id_new), "")

        self.prf = new_prf
        self.check_proof()

    def add_line_before(self, id, n):
        """Add given line before the given id."""
        # Determine the index of the new line.
        assert id.startswith("S"), "add_line_before"

        id_new = int(id[1:])
        new_prf = Proof()
        new_prf.vars = self.prf.vars
        for item in self.prf.items:
            if item.id == id:
                for i in range(n):
                    new_prf.add_item("S" + str(id_new + i), "")
            new_prf.items.append(incr_proof_item(item, id_new, n))

        self.prf = new_prf
        self.check_proof()

    def remove_line(self, id):
        """Remove line with the given id."""
        # Determine the index of the line to be removed.
        if id.startswith("S"):
            id_remove = int(id[1:])
        else:
            raise TacticException()

        # Remove the given line. Replace all S{i} with S{i-1} whenever
        # i > id_remove.
        new_prf = Proof()
        new_prf.vars = self.prf.vars
        for item in self.prf.items:
            if not item.id == id:
                new_prf.items.append(decr_proof_item(item, id_remove))
            
        self.prf = new_prf
        self.check_proof()

    def set_line(self, id, rule, *, args=None, prevs=None, th=None):
        """Set the item with the given id to the following data."""
        new_prf = Proof()
        new_prf.vars = self.prf.vars
        for item in self.prf.items:
            if item.id == id:
                new_prf.items.append(ProofItem(id, rule, args=args, prevs=prevs, th=th))
            else:
                new_prf.items.append(item)

        self.prf = new_prf
        self.check_proof()

    def get_proof_item(self, id):
        """Obtain the proof item with the given id."""
        for item in self.prf.items:
            if item.id == id:
                return item
        
        raise TacticException()

    def replace_id(self, old_id, new_id):
        """Replace old_id with new_id in prevs."""
        def replace_line(item):
            return ProofItem(item.id, item.rule, args=item.args,
                prevs=[new_id if id == old_id else id for id in item.prevs], th=item.th)

        new_prf = Proof()
        new_prf.vars = self.prf.vars
        for item in self.prf.items:
            new_prf.items.append(replace_line(item))

        self.prf = new_prf
        self.remove_line(old_id)

    def find_goal(self, concl, upto_id):
        """Determine if the given conclusion is already proved. Search up to
        the given id.

        """
        for item in self.prf.items:
            if item.id == upto_id:
                return None
            if item.th is not None and item.th.can_prove(concl):
                return item.id

        # upto_id not found
        raise TacticException()

    def apply_backward_step(self, id, th_name, *, prevs=None, inst=None):
        """Apply backward step using the given theorem.
        
        prevs - list of previous proved facts to use.
        inst - existing instantiation.

        """
        if prevs is None:
            prevs = []

        # Obtain the statement to be proved.
        for i, item in enumerate(self.prf.items):
            if item.id == id:
                cur_item = item

        assert cur_item.rule == "sorry", "apply_backward_step: id is not a gap"

        # Instantiate the given theorem.
        th = self.thy.get_theorem(th_name)

        if inst is None:
            inst = dict()
            As, C = logic.subst_norm(th.concl, inst).strip_implies()
            for pat, prev in zip(As, prevs):
                item = self.get_proof_item(prev)
                matcher.first_order_match_incr(pat, item.th.concl, inst)
            matcher.first_order_match_incr(C, cur_item.th.concl, inst)

        As, _ = logic.subst_norm(th.concl, inst).strip_implies()

        num_goal = len(As) - len(prevs)
        self.add_line_before(id, num_goal)
        start = int(id[1:])
        all_ids = ["S" + str(start + i - len(prevs)) for i in range(len(prevs), len(As))]
        for goal_id, A in zip(all_ids, As[len(prevs):]):
            self.set_line(goal_id, "sorry", th=Thm(cur_item.th.assums, A))

        self.set_line("S" + str(start + num_goal), "apply_theorem_for",
                      args=(th_name, inst), prevs=prevs + all_ids)

        # Test if the goals are already proved:
        for goal_id, A in reversed(list(zip(all_ids, As[len(prevs):]))):
            goal = Thm(cur_item.th.assums, A)
            new_id = self.find_goal(goal, goal_id)
            if new_id is not None:
                self.replace_id(goal_id, new_id)

    def introduction(self, id, names=None):
        """Introduce assumptions for a goal of the form

        !x_1 ... x_k. A_1 --> ... --> A_n --> C.

        Argument names specifies list of variable names.
        
        """
        cur_item = self.get_proof_item(id)
        assert cur_item.rule == "sorry", "introduction: id is not a gap"

        if names is None:
            names = []

        vars, As, C = strip_all_implies(cur_item.th.concl, names)

        # Add necessary variables
        for var in vars:
            if var not in self.prf.vars:
                self.prf.vars.append(var)

        # len(As) lines for the assumptions, one line for the sorry,
        # len(vars) lines for forall_intr, len(As) lines for implies_intr,
        # one line already available.
        self.add_line_before(id, len(vars) + 2 * len(As))

        # Starting id number
        start = int(id[1:])

        # Assumptions
        for i, A in enumerate(As):
            new_id = "S" + str(start + i)
            self.set_line(new_id, "assume", args=A, th=Thm([A], A))

        # Goal
        goal_id = "S" + str(start + len(As))
        goal = Thm(list(cur_item.th.assums) + As, C)
        self.set_line(goal_id, "sorry", th=goal)

        # implies_intr invocations
        for i, A in enumerate(reversed(As)):
            prev_id = "S" + str(start + len(As) + i)
            new_id = "S" + str(start + len(As) + i + 1)
            self.set_line(new_id, "implies_intr", args=A, prevs=[prev_id])

        # forall_intr invocations
        for i, var in enumerate(reversed(vars)):
            prev_id = "S" + str(start + 2 * len(As) + i)
            new_id = "S" + str(start + 2 * len(As) + i + 1)
            self.set_line(new_id, "forall_intr", args=var, prevs=[prev_id])

        # Test if the goal is already proved
        new_id = self.find_goal(goal, goal_id)
        if new_id is not None:
            self.replace_id(goal_id, new_id)

    def apply_induction(self, id, th_name, var):
        """Apply induction using the given theorem and on the given
        variable.
        
        """
        cur_item = self.get_proof_item(id)
        assert cur_item.rule == "sorry", "apply_induction: id is not a gap"

        # Find variable
        assert isinstance(var, str), "apply_induction: input must be a string"
        for v in self.prf.vars:
            if v.name == var:
                var = v
                break

        assert not isinstance(var, str), "apply_induction: variable not found"

        # Current goal
        concl = cur_item.th.concl

        # Instantiation for P
        P = concl.abstract_over(var)
        inst = {"P": P, "x": var}
        self.apply_backward_step(id, th_name, inst=inst)

    def rewrite_goal(self, id, th_name, *, backward=False):
        """Apply an existing equality theorem to the given goal."""

        cur_item = self.get_proof_item(id)
        assert cur_item.rule == "sorry", "apply_induction: id is not a gap"

        goal = cur_item.th.concl
        cv = top_conv(rewr_conv(ProofTerm.theorem(self.thy, th_name)))
        _, new_goal = cv(goal).concl.dest_binop()

        self.add_line_before(id, 1)
        start = int(id[1:])
        self.set_line(id, "sorry", th=Thm(cur_item.th.assums, new_goal))
        self.set_line("S" + str(start + 1), "rewrite_goal", args=(th_name, goal), prevs=[id])

        # Test if the goal is already proved
        new_id = self.find_goal(Thm(cur_item.th.assums, new_goal), id)
        if new_id is not None:
            self.replace_id(id, new_id)
