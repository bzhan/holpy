# Author: Bohua Zhan

"""Facility for checking theory files."""

import traceback2
import json
import copy

from kernel.proof import Proof
from kernel import theory
from logic import basic
from logic import context
from server import server
from server import method
from logic import logic
from server import items
from syntax import parser


def check_proof(item, *, rewrite):
    if item.steps:
        context.set_context(None, vars=item.vars)
        state = server.parse_init_state(item.prop)
        history = state.parse_steps(item.steps)
        if rewrite:
            item.proof = state.export_proof(unicode=True, highlight=False)

        for step in history:
            if 'error' in step:
                return {
                    'status': 'Failed',
                    'err_type': step['error']['err_type'],
                    'err_str': step['error']['err_str'],
                    'trace': step['error']['trace']
                }

        try:
            state.check_proof()
        except Exception as e:
            return {
                'status': 'Failed',
                'err_type': e.__class__.__name__,
                'err_str': str(e),
                'trace': traceback2.format_exc()
            }

        # Otherwise OK
        return {
            'status': 'OK' if len(state.rpt.gaps) == 0 else 'Partial',
            'num_steps': len(item.steps),
        }
    elif item.proof:
        try:
            context.set_context(None, vars=item.vars)
            state = server.parse_proof(item.proof)
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

def check_theory(filename, username='master', rewrite=False):
    """Check the theory with the given name."""
    data = basic.load_json_data(filename, username)
    basic.load_theory(filename, limit='start', username=username)

    res = []
    stat = {'OK': 0, 'NoSteps': 0, 'Failed': 0, 'Partial': 0,
            'ProofOK': 0, 'ProofFail': 0, 'ParseOK': 0, 'ParseFail': 0, 'EditFail': 0}

    content = []

    for raw_item in data['content']:
        item = items.parse_item(raw_item)
        if item.error:
            e = item.error
            item_res = {
                'ty': item.ty,
                'name': item.name,
                'status': 'ParseFail',
                'err_type': e.__class__.__name__,
                'err_str': str(e),
                'trace': item.trace
            }
        else:
            exts = item.get_extension()
            old_thy = copy.copy(theory.thy)
            theory.thy.unchecked_extend(exts)
            new_thy = theory.thy

            # Check consistency with edit_item
            edit_item = item.get_display(unicode=True, highlight=False)
            theory.thy = old_thy
            item2 = items.parse_edit(edit_item)
            if item.ty == 'thm':
                item2.proof = item.proof
                item2.steps = item.steps
                item2.num_gaps = item.num_gaps
            if item2.error or item != item2:
                item_res = {
                    'ty': item.ty,
                    'name': item.name,
                    'status': 'EditFail'
                }
            elif item.ty == 'thm':
                item_res = check_proof(item, rewrite=rewrite)
                item_res['ty'] = 'thm'
                item_res['name'] = item.name
            else:
                item_res = {
                    'ty': item.ty,
                    'name': item.name,
                    'status': 'ParseOK'
                }
            theory.thy = new_thy

        stat[item_res['status']] += 1
        res.append(item_res)

        if rewrite:
            content.append(item.export_json())

    if rewrite:
        data['content'] = content
        with open(basic.user_file(filename, username), 'w+', encoding='utf-8') as f:
            json.dump(data, f, indent=4, ensure_ascii=False, sort_keys=True)

    return {
        'data': res,
        'stat': stat
    }
