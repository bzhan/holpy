"""Implementation of best-first-search automation."""

import queue

from kernel.term import Not
from kernel.proofterm import ProofTerm
from kernel import theory
from logic import matcher
from logic.conv import rewr_conv


class ProofStateException(Exception):
    def __init__(self, msg):
        self.msg = msg
        
    def __str__(self):
        return self.msg
    

class ProofStepException(Exception):
    def __init__(self, msg):
        self.msg = msg
        
    def __str__(self):
        return self.msg        
    

class Item:
    pass

class FactItem(Item):
    """A known fact, represented as a proof term."""
    def __init__(self, pt):
        self.pt = pt
        self.prop = self.pt.prop

    def size(self):
        return self.prop.size()
    
    def __eq__(self, other):
        return isinstance(other, FactItem) and self.prop == other.prop

    def __str__(self):
        return str(self.prop)
        
class TermItem(Item):
    """A term that currently exists in the proof."""
    def __init__(self, t):
        self.t = t

    def size(self):
        return self.t.size()

    def __eq__(self, other):
        return isinstance(other, TermItem) and self.t == other.t

    def __str__(self):
        return '[%s]' % str(self.t)
    
    
class ProofStep:
    pass

def get_subterms(t):
    """Obtain the immediate subterms of a term."""
    def dest_at_head(t):
        if t.is_abs():
            return dest_at_head(t.body)
        elif t.is_open():
            res = []
            for arg in t.args:
                res.extend(dest_at_head(arg))
            return res
        else:
            return [t]
        
    def dest(t):
        if t.is_comb():
            return t.args
        elif t.is_abs():
            return dest_at_head(t.body)
        else:
            return []
        
    return dest(t)
        
def get_all_subterms(t):
    """Obtain all strict subterms of a term."""
    def rec(t):
        res = []
        for subt in get_subterms(t):
            res.extend(rec(subt))
        res.extend([t])
        return res
    
    distinct_list = []
    for subt in rec(t):
        if subt not in distinct_list and subt != t:
            distinct_list.append(subt)
    return distinct_list
    
class TermProofStep(ProofStep):
    """Add subterms of a fact."""
    def __init__(self):
        self.incr_sc = 0
        
    def __str__(self):
        return '$TERM'

    def __call__(self, *args):
        if not (len(args) == 1 and isinstance(args[0], FactItem)):
            return []
        
        t = args[0].prop
        
        # Add subterms of the proposition. Ignore negation symbol.
        if t.is_not():
            t = t.arg

        return list(TermItem(subt) for subt in get_all_subterms(t))
        

class ForwardProofStep(ProofStep):
    """Apply a theorem in the forward direction."""
    def __init__(self, th_name):
        self.th_name = th_name
        self.pt = ProofTerm.theorem(th_name)
        self.th = self.pt.th
        self.prop = self.pt.prop
        self.incr_sc = 'SIZE'
        
    def __str__(self):
        return 'forward %s' % self.th_name

    def __call__(self, *args):
        if not (len(args) == 1 and isinstance(args[0], FactItem)):
            return []
        
        t = args[0].prop
        pt = args[0].pt
        res = []

        if self.prop.is_equals():
            try:
                inst = matcher.first_order_match(self.prop.lhs, t)
                res.append(FactItem(self.pt.substitution(inst).equal_elim(pt)))
            except matcher.MatchException:
                pass
        elif self.prop.is_implies():
            try:
                inst = matcher.first_order_match(self.prop.arg1, t)
                res.append(FactItem(self.pt.substitution(inst).implies_elim(pt)))
            except matcher.MatchException:
                pass
        else:
            pass
        
        return res
    

global_prfsteps1 = list()
global_prfsteps1.append(TermProofStep())

from logic import basic
basic.load_theory('topology')
forward_ths = [
    'is_topology_def'
]

for th_name in forward_ths:
    global_prfsteps1.append(ForwardProofStep(th_name))


class Update:
    """An update to the proof state.
    
    sc -- score of the update, indicating priority.
    prfstep -- proof step generating the update.
    source -- list of ids of source items.
    item -- item to be added.

    """
    def __init__(self, sc, prfstep, source, item):
        self.sc = sc
        self.prfstep = prfstep
        self.source = source
        self.item = item
        
    def __str__(self):
        res = '%s by %s' % (self.item, self.prfstep)
        if len(self.source) > 0:
            res += ' from %s' % ', '.join(str(i) for i in self.source)
        return res
    
    def eq_item(self, other):
        return self.item == other.item
        
    def __le__(self, other):
        return self.sc <= other.sc
    
    def __lt__(self, other):
        return self.sc < other.sc
        
class ProofState:
    """Overall state of the proof.
    
    vars -- list of initial variables.
    assms -- list of initial assumptions.
    updates -- list of currently added updates.
    queue -- list of pending items.

    """
    def __init__(self, vars, assms):
        self.vars = vars
        self.assms = assms
        self.updates = []
        self.queue = queue.PriorityQueue()
        
        # Add the initial assumptions to the queue
        for assm in self.assms:
            self.queue.put(Update(0, '$INIT', [], FactItem(ProofTerm.assume(assm))))
        
        # Overall count of number of steps
        self.step_count = 0
            
    def __str__(self):
        res = 'Variables: %s\n' % ', '.join(str(var) for var in self.vars)
        res += 'Assumptions: %s\n' % ', '.join(str(assm) for assm in self.assms)
        res += 'Updates:\n'
        for i, item in enumerate(self.updates):
            res += '%d: %s\n' % (i, item)
        res += 'Remaining in queue: %d items' % self.queue.qsize()
        
        return res
    
    def has_item(self, item):
        return any(item == updt.item for updt in self.updates)
    
    def step(self):
        """Apply one step of automation.
        
        In each step, extract the item with the smallest score (highest priority),
        add it to the list of items, and process the item.

        """
        if self.queue.empty():
            raise ProofStateException('Queue is empty.')
        
        self.step_count += 1
        cur_update = self.queue.get()
        
        if self.has_item(cur_update.item):
            return

        self.updates.append(cur_update)
        cur_sc = cur_update.sc
        cur_item = cur_update.item
        cur_id = len(self.updates) - 1
        
        for prfstep1 in global_prfsteps1:
            new_items = prfstep1(cur_item)
            for new_item in new_items:
                if not self.has_item(new_item):
                    if prfstep1.incr_sc == 'SIZE':
                        new_sc = cur_sc + new_item.size()
                    else:
                        new_sc = cur_sc + prfstep1.incr_sc
                    self.queue.put(Update(new_sc, prfstep1, [cur_id], new_item))

    def step_for(self, n, debug=True):
        while n > 0 and not self.queue.empty():
            self.step()
            n -= 1

        if debug:
            if n == 0:
                print('Reached limit at %d steps' % self.step_count)
            else:
                print('Finished after %d steps' % self.step_count)


def init_proof(prop):
    """Initialize proof for proposition."""
    vars = prop.get_vars()
    assms, concl = prop.strip_implies()
    assms.append(concl.arg if concl.is_not() else Not(concl))
    return ProofState(vars, assms)

def init_proof_theorem(th_name):
    th = theory.thy.get_theorem(th_name, svar=False)
    return init_proof(th.prop)
