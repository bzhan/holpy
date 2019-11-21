# Author: Bohua Zhan

"""Facility for checking theory files."""

import traceback2

from logic import basic
from server.server import ProofState
from server import method
from logic import logic


def check_proof(thy, item):
    if 'steps' not in item:
        return {
            'name': item['name'],
            'status': 'NoSteps'
        }

    state = ProofState.parse_init_state(thy, item)
    state.steps = item['steps']
    try:
        for step in item['steps']:
            method.apply_method(state, step)
            state.check_proof(compute_only=True)
        state.check_proof()
    except Exception as e:
        return {
            'name': item['name'],
            'status': 'Failed',
            'err_type': e.__class__.__name__,
            'err_str': str(e),
            'trace': traceback2.format_exc()
        }

    return {
        'name': item['name'],
        'status': 'OK' if len(state.rpt.gaps) == 0 else 'Partial',
        'num_steps': len(item['steps']),
    }

def check_theory(filename, username='master'):
    """Check the theory with the given name."""
    data = basic.load_json_data(filename, username)
    thy = basic.load_theories(data['imports'], username)

    res = []
    stat = {'OK': 0, 'NoSteps': 0, 'Failed': 0, 'Partial': 0}

    for item in data['content']:
        if item['ty'] == 'thm':
            item_res = check_proof(thy, item)
            stat[item_res['status']] += 1
            res.append(item_res)

        item = basic.parse_item(thy, item)
        exts = basic.get_extension(thy, item)
        thy.unchecked_extend(exts)

    return {
        'data': res,
        'stat': stat
    }