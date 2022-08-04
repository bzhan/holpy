# Author: Bohua Zhan

import copy
import itertools
from typing import List, Union

from kernel import term
from kernel.term import Term, Var
from kernel.thm import Thm
from kernel.proof import ProofItem, Proof, ItemID, ProofStateException
from kernel import report
from kernel import theory
from kernel.proofterm import ProofTerm
from logic import logic, matcher
from logic import context
from logic import tactic
from logic.context import Context
from syntax import parser, printer
from syntax.settings import settings, global_setting
from server.method import ProofState
from util import typecheck


def parse_init_state(prop: Union[str, List[str], Term]) -> ProofState:
    """Given data for a theorem statement, construct the initial partial proof.
    
    data['vars']: list of variables.
    data['prop']: proposition to be proved. In the form A1 --> ... --> An --> C.

    Construct initial partial proof for the given assumptions and
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
    typecheck.checkinstance('parse_init_state', prop, (str, list, Term))
    if isinstance(prop, (str, list)):
       prop = parser.parse_term(prop)
    assums, concl = prop.strip_implies()

    state = ProofState()
    for nm, T in context.ctxt.vars.items():
        state.vars.append(Var(nm, T))
    state.prf = Proof(*assums)
    n = len(assums)
    state.prf.add_item(n, "sorry", th=Thm(concl, tuple(assums)))
    state.prf.add_item(n + 1, "intros", prevs=range(n+1))
    state.check_proof(compute_only=True)
    return state

def parse_proof(proof) -> ProofState:
    """Obtain proof from json format."""
    state = ProofState()
    for nm, T in context.ctxt.vars.items():
        state.vars.append(Var(nm, T))
    state.prf = Proof()
    for line in proof:
        if line['rule'] == "variable":
            nm, str_T = line['args'].split(',', 1)
            context.ctxt.vars[nm] = parser.parse_type(str_T.strip())
        item = parser.parse_proof_rule(line)
        state.prf.insert_item(item)
    state.check_proof()

    return state
