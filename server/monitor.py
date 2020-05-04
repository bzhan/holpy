# Author: Bohua Zhan

"""Facility for checking theory files."""

import traceback2
import json
import copy
import time
from pstats import Stats
import cProfile

from kernel import theory
from logic import basic
from logic import context
from server import server
from server import method
from logic import logic
from server import items
from syntax import parser
from prover import z3wrapper
from syntax.settings import settings, global_setting


def check_proof(item, *, rewrite):
    if item.steps:
        context.set_context(None, vars=item.vars)
        state = server.parse_init_state(item.prop)
        history = state.parse_steps(item.steps)
        if rewrite:
            with global_setting(unicode=True):
                item.proof = state.export_proof()

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
    start_time = time.perf_counter()

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
            with global_setting(unicode=True, highlight=False):
                edit_item = item.get_display()
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

    stat['exec_time'] = time.perf_counter() - start_time

    return {
        'data': res,
        'stat': stat
    }


if __name__ == "__main__":
    import sys, getopt

    opts, args = getopt.getopt(sys.argv[1:], 'p')

    basic.load_metadata()
    z3wrapper.check_z3 = False

    files = []
    if not args:
        # Load all file names.
        for name, cache in basic.theory_cache['master'].items():
            files.append((cache['order'], name))
        files.sort()
        files = [name for _, name in files]
    else:
        # Load provided names
        files = args

    profile = False
    for opt, arg in opts:
        if opt == '-p':
            profile = True

    if profile:
        pr = cProfile.Profile()
        pr.enable()

    def print_stat(filename, stat):
        return '%17s | %4d | %7d | %6d | %7d | %7d | %9d | %7d | %9d | %8d | %5.2f' % (
            filename, stat['OK'], stat['Partial'], stat['Failed'], stat['NoSteps'], stat['ProofOK'],
            stat['ProofFail'], stat['ParseOK'], stat['ParseFail'], stat['EditFail'], stat['exec_time'])

    print('       File       |  OK  | Partial | Failed | NoSteps | ProofOK | ProofFail | ParseOK | ParseFail | EditFail | Time')
    print('--------------------------------------------------------------------------------------------------------------------')
    total_stat = {
        'OK': 0, 'Partial': 0, 'Failed': 0, 'NoSteps': 0,
        'ProofOK': 0, 'ProofFail': 0, 'ParseOK': 0, 'ParseFail': 0, 'EditFail': 0, 'exec_time': 0.0
    }
    for filename in files:
        res = check_theory(filename)
        print(print_stat(filename, res['stat']))
        for s in total_stat.keys():
            total_stat[s] += res['stat'][s]

    if len(files) > 1:
        print('--------------------------------------------------------------------------------------------------------------------')
        print(print_stat('Total', total_stat))
    else:
        print()
        print(' Item type |           Name           |   Status   ')
        print('---------------------------------------------------')
        for line in res['data']:
            if 'err_type' in line:
                err = " %s: %s" % (line['err_type'], line['err_str'])
            else:
                err = ''
            print("%10s | %24s | %9s%s" % (line['ty'], line['name'], line['status'], err))

    if profile:
        p = Stats(pr)
        p.strip_dirs()
        p.sort_stats('cumtime')
        p.print_stats(100)
