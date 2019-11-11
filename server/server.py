# Author: Bohua Zhan

import io

from kernel import term
from kernel.term import Term, Var
from kernel.thm import Thm
from kernel.proof import ProofItem, Proof, ItemID
from kernel import report
from logic import logic, matcher
from logic.proofterm import ProofTerm, ProofTermAtom
from syntax import parser, printer, pprint
from syntax.context import Context
from server import tactic
from server import method


class TacticException(Exception):
    pass

# Helper functions

def incr_proof_item(item, start, n):
    """Increment all ids in the given proof item. Recursively increment
    ids in subproofs.
    
    """
    item.id = item.id.incr_id_after(start, n)
    item.prevs = [id.incr_id_after(start, n) for id in item.prevs]
    if item.subproof:
        for subitem in item.subproof.items:
            incr_proof_item(subitem, start, n)

def decr_proof_item(item, id_remove):
    """Decrement all ids in the given proof item."""
    item.id = item.id.decr_id(id_remove)
    item.prevs = [id.decr_id(id_remove) for id in item.prevs]
    if item.subproof:
        for subitem in item.subproof.items:
            decr_proof_item(subitem, id_remove)


class ProofState():
    """Represents proof state on the server side."""

    def __init__(self, thy):
        """Empty proof state."""
        self.thy = thy
        self.vars = []
        self.prf = Proof()

    def get_ctxt(self, id):
        """Obtain the context at the given id."""
        id = ItemID(id)
        ctxt = Context(self.thy)
        for v in self.vars:
            ctxt.vars[v.name] = v.T

        prf = self.prf
        try:
            for n in id.id:
                for item in prf.items[:n+1]:
                    if item.rule == "variable":
                        nm, T = item.args
                        ctxt.vars[nm] = T
                prf = prf.items[n].subproof
            return ctxt
        except (AttributeError, IndexError):
            raise TacticException

    def __str__(self):
        vars = sorted(self.vars, key = lambda v: v.name)
        lines = "\n".join('var ' + v.name + ' :: ' + str(v.T) for v in vars)
        return lines + "\n" + str(self.prf)

    @staticmethod
    def init_state(thy, vars, assums, concl):
        """Construct initial partial proof for the given assumptions and
        conclusion.

        assums - assumptions A1, ... An.
        concl - conclusion C.
        
        Constructs:

        0: assume A1
        ...
        n-1: assume An
        n: C by sorry
        n+1: A1 --> ... --> An --> C by intros from 0, 1, ..., n.

        """
        assert all(isinstance(var, Term) for var in vars), "init_state: vars must be terms."
        assert all(isinstance(a, Term) for a in assums), "init_state: assums must be terms."
        assert isinstance(concl, Term), "init_state: conclusion must be a term."
        state = ProofState(thy)

        state.vars = vars
        state.prf = Proof(*assums)
        n = len(assums)
        state.prf.add_item(n, "sorry", th=Thm(assums, concl))
        if len(assums) > 0:
            state.prf.add_item(n + 1, "intros", prevs=range(n+1))
        state.check_proof(compute_only=True)
        return state

    @staticmethod
    def parse_init_state(thy, data):
        """Given data for a theorem statement, construct the initial partial proof.
        
        data['vars']: list of variables.
        data['prop']: proposition to be proved. In the form A1 --> ... --> An --> C.

        """
        ctxt = Context(thy, vars=data['vars'])
        prop = parser.parse_term(ctxt, data['prop'])
        assums, concl = prop.strip_implies()

        return ProofState.init_state(thy, ctxt.get_vars(), assums, concl)

    def get_method_sig(self):
        """Obtain signature of all methods in the theory."""
        sig = {}
        for name, method in self.thy.get_data('method').items():
            sig[name] = method.sig
        return sig

    def export_proof(self, prf):
        return sum([printer.export_proof_item(self.thy, item, unicode=True, highlight=True)
                    for item in prf.items], [])

    def json_data(self):
        """Export proof in json format."""
        self.check_proof()
        res = {
            "vars": {v.name: str(v.T) for v in self.vars},
            "proof": self.export_proof(self.prf),
            "report": self.rpt.json_data(),
            "method_sig": self.get_method_sig(),
        }
        if hasattr(self, 'steps'):
            res['steps'] = self.steps
        if hasattr(self, 'history'):
            res['history'] = self.history

        return res

    @staticmethod
    def parse_proof(thy, data):
        """Obtain proof from json format."""
        if 'steps' in data:
            state = ProofState.parse_init_state(thy, data)
            state.steps = data['steps']
            state.history = []
            for step in data['steps']:
                state.history.append({
                    'steps_output': method.display_method(state, step, unicode=True, highlight=True),
                    'proof': state.export_proof(state.prf),
                    'report': state.rpt.json_data()
                })
                method.apply_method(state, step)
            state.history.append({
                'steps_output': pprint.N('Current state', highlight=True),
                'proof': state.export_proof(state.prf),
                'report': state.rpt.json_data()
            })
        else:
            ctxt = Context(thy, vars=data['vars'])
            state = ProofState(thy)
            state.vars = ctxt.get_vars()
            state.prf = Proof()
            for line in data['proof']:
                if line['rule'] == "variable":
                    nm, str_T = line['args'].split(',', 1)
                    ctxt.vars[nm] = parser.parse_type(thy, str_T.strip())
                item = parser.parse_proof_rule(ctxt, line)
                state.prf.insert_item(item)

        state.check_proof(compute_only=True)
        return state

    def check_proof(self, *, no_gaps=False, compute_only=False):
        """Check the given proof. Report is stored in rpt."""
        self.rpt = report.ProofReport()
        return self.thy.check_proof(self.prf, rpt=self.rpt, no_gaps=no_gaps, compute_only=compute_only)

    def add_line_before(self, id, n):
        """Add n lines before the given id."""
        id = ItemID(id)
        prf = self.prf.get_parent_proof(id)
        split = id.last()
        new_items = [ProofItem(id.incr_id(i), "") for i in range(n)]
        prf.items = prf.items[:split] + new_items + prf.items[split:]
        for item in prf.items[split+n:]:
            incr_proof_item(item, id, n)

        self.check_proof(compute_only=True)

    def remove_line(self, id):
        """Remove line with the given id."""
        id = ItemID(id)
        prf = self.prf.get_parent_proof(id)
        split = id.last()
        prf.items = prf.items[:split] + prf.items[split+1:]
        for item in prf.items[split:]:
            decr_proof_item(item, id)

        self.check_proof(compute_only=True)

    def set_line(self, id, rule, *, args=None, prevs=None, th=None):
        """Set the item with the given id to the following data."""
        id = ItemID(id)
        prf = self.prf.get_parent_proof(id)
        prf.items[id.last()] = ProofItem(id, rule, args=args, prevs=prevs, th=th)
        self.check_proof(compute_only=True)

    def get_proof_item(self, id):
        """Obtain the proof item with the given id."""
        return self.prf.find_item(ItemID(id))

    def replace_id(self, old_id, new_id):
        """Replace old_id with new_id in prevs."""
        def replace(prf):
            for item in prf.items:
                item.prevs = [new_id if id == old_id else id for id in item.prevs]
                if item.subproof:
                    replace(item.subproof)

        prf = self.prf.get_parent_proof(old_id)
        replace(prf)

        self.remove_line(old_id)

    def find_goal(self, concl, goal_id):
        """Determine if the given conclusion is already proved,
        for the purpose of showing goal_id.

        Proof items that can be used include all items with id
        whose length is at most that of goal_id, where all but
        the last number agrees with that of goal_id, and the
        last number is less than the corresponding number in goal_id.

        """
        prf = self.prf
        try:
            for n in goal_id.id:
                for item in prf.items[:n]:
                    if item.th is not None and item.th.can_prove(concl):
                        return item.id
                prf = prf.items[n].subproof
        except (AttributeError, IndexError):
            raise TacticException

    def apply_search(self, id, method, prevs=None):
        id = ItemID(id)
        prevs = [ItemID(prev) for prev in prevs] if prevs else []
        return method.search(self, id, prevs)
    
    def search_method(self, id, prevs):
        """Perform search for each method."""
        id = ItemID(id)
        prevs = [ItemID(prev) for prev in prevs] if prevs else []
        results = []
        method_data = self.thy.get_data("method")
        for name, method in method_data.items():
            res = method.search(self, id, prevs)
            for r in res:
                r['_method_name'] = name
                r['display'] = method.display_step(self, id, r, prevs, highlight=True, unicode=True)
            results.extend(res)

        # If there is an element in results that solves the goal,
        # output only results that solves.
        if any('_goal' in r and len(r['_goal']) == 0 for r in results):
            results = list(filter(lambda r: '_goal' in r and len(r['_goal']) == 0, results))
        return results

    def apply_tactic(self, id, tactic, args=None, prevs=None):
        id = ItemID(id)
        prevs = [ItemID(prev) for prev in prevs] if prevs else []
        prevs = [ProofTermAtom(prev, self.get_proof_item(prev).th) for prev in prevs]
        
        cur_item = self.get_proof_item(id)
        assert cur_item.rule == "sorry", "apply_tactic: id is not a gap"

        pt = tactic.get_proof_term(self.thy, cur_item.th, args=args, prevs=prevs)
        new_prf = pt.export(prefix=id, subproof=False)

        self.add_line_before(id, len(new_prf.items) - 1)
        for i, item in enumerate(new_prf.items):
            cur_id = item.id
            prf = self.prf.get_parent_proof(cur_id)
            prf.items[cur_id.last()] = item
        self.check_proof(compute_only=True)

        # Test if the goals are already proved:
        for item in new_prf.items:
            if item.rule == 'sorry':
                new_id = self.find_goal(self.get_proof_item(item.id).th, item.id)
                if new_id is not None:
                    self.replace_id(item.id, new_id)

        # Resolve trivial subgoals
        for item in new_prf.items:
            if item.rule == 'sorry':
                if logic.trivial_macro().can_eval(self.thy, item.th.prop):
                    self.set_line(item.id, 'trivial', args=item.th.prop)

    def apply_backward_step(self, id, th_name, *, prevs=None, instsp=None):
        """Apply backward step using the given theorem.
        
        prevs - list of previous proved facts to use.
        inst - existing instantiation.

        """
        self.apply_tactic(id, tactic.rule(), args=(th_name, instsp), prevs=prevs)

    def apply_forward_step(self, id, th_name, prevs=None):
        """Apply forward step using the given theorem."""
        method.apply_method(self, {
            'method_name': 'apply_forward_step',
            'goal_id': id, 'fact_ids': prevs, 'theorem': th_name
        })

    def introduction(self, id, names=None):
        """Introduce variables and assumptions."""
        if names is None:
            names = ""
        elif isinstance(names, list):
            names = ",".join(names)
        method.apply_method(self, {
            'method_name': 'introduction',
            'goal_id': id, 'fact_ids': [], 'names': names
        })

    def apply_forall_elim(self, id, prev, s):
        """Elimination of forall statement."""
        method.apply_method(self, {
            'method_name': 'forall_elim',
            'goal_id': id, 'fact_ids': [prev], 's': s
        })

    def apply_induction(self, id, th_name, var):
        """Apply induction using the given theorem and variable."""
        method.apply_method(self, {
            'method_name': 'induction',
            'goal_id': id, 'fact_ids': [], 'theorem': th_name, 'var': var
        })

    def rewrite_goal(self, id, th_name, *, backward=False, prevs=None):
        """Apply an existing equality theorem to the given goal."""
        self.apply_tactic(id, tactic.rewrite(), args=th_name, prevs=prevs)

    def rewrite_goal_with_prev(self, id, prev):
        """Apply existence fact to the given goal."""
        self.apply_tactic(id, tactic.rewrite_goal_with_prev(), prevs=[prev])

    def apply_cases(self, id, A):
        """Apply case analysis on A."""
        self.apply_tactic(id, tactic.cases(), args=A)

    def apply_prev(self, id, prev):
        """Apply previously proved rule."""
        self.apply_tactic(id, tactic.apply_prev(), prevs=[prev])
