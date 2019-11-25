# Author: Bohua Zhan

"""Facility for checking theory files."""

import traceback2

from kernel.proof import Proof
from logic import basic
from logic.context import Context
from server.server import ProofState
from server import method
from logic import logic
from syntax import parser


def check_proof(thy, item):
    if 'steps' in item:
        state = ProofState.parse_init_state(thy, item)
        state.steps = item['steps']
        try:
            for step in item['steps']:
                method.apply_method(state, step)
                state.check_proof(compute_only=True)
            state.check_proof()
        except Exception as e:
            return {
                'status': 'Failed',
                'err_type': e.__class__.__name__,
                'err_str': str(e),
                'trace': traceback2.format_exc()
            }

        return {
            'status': 'OK' if len(state.rpt.gaps) == 0 else 'Partial',
            'num_steps': len(item['steps']),
        }
    elif 'proof' in item:
        ctxt = Context(thy, vars=item['vars'])
        state = ProofState(thy)
        state.vars = ctxt.get_vars()
        state.prf = Proof()
        try:
            for line in item['proof']:
                if line['rule'] == "variable":
                    nm, str_T = line['args'].split(',', 1)
                    ctxt.vars[nm] = parser.parse_type(thy, str_T.strip())
                proof_item = parser.parse_proof_rule(ctxt, line)
                state.prf.insert_item(proof_item)
            state.check_proof(no_gaps=True)
        except Exception as e:
            return {
                'status': 'ProofFail',
                'err_type': e.__class__.__name__,
                'err_str': str(e),
                'trace': traceback2.format_exc()
            }
        
        return {
            'status': 'ProofOK'
        }
    else:
        return {
            'status': 'NoSteps'
        }

def check_theory(filename, username='master'):
    """Check the theory with the given name."""
    data = basic.load_json_data(filename, username)
    thy = basic.load_theories(data['imports'], username)

    res = []
    stat = {'OK': 0, 'NoSteps': 0, 'Failed': 0, 'Partial': 0,
            'ProofOK': 0, 'ProofFail': 0, 'ParseOK': 0, 'ParseFail': 0}

    for item in data['content']:
        try:
            parse_item = basic.parse_item(thy, item)
            exts = basic.get_extension(thy, parse_item)
        except Exception as e:
            item_res = {
                'ty': item['ty'],
                'name': item['name'],
                'status': 'ParseFail',
                'err_type': e.__class__.__name__,
                'err_str': str(e),
                'trace': traceback2.format_exc()
            }
        else:
            if item['ty'] == 'thm':
                item_res = check_proof(thy, item)
                item_res['ty'] = 'thm'
                item_res['name'] = item['name']
            else:
                item_res = {
                    'ty': item['ty'],
                    'name': item['name'],
                    'status': 'ParseOK'
                }
            thy.unchecked_extend(exts)

        stat[item_res['status']] += 1
        res.append(item_res)

    return {
        'data': res,
        'stat': stat
    }