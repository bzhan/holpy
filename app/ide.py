# Author: Chaozhu Xiang, Bohua Zhan

import json, os, traceback2, time
from flask import request
from flask.json import jsonify
from pstats import Stats
import cProfile

from kernel import theory
from syntax import parser, printer, settings, pprint
from server import server, method
from logic import basic
from logic.context import Context
from server import monitor
from server import items
from app.app import app


@app.route('/api/init-saved-proof', methods=['POST'])
def init_saved_proof():
    """Load a saved proof.
    
    Input:
    * username: username.
    * theory_name: name of the theory.
    * thm_name: name of the theorem.
    * proof: initial data for the proof.

    Returns:
    * saved proof of the theorem.

    """
    data = json.loads(request.get_data().decode("utf-8"))
    username = data['username']
    start_time = time.perf_counter()

    if 'thm_name' in data:
        limit = ('thm', data['thm_name'])
    else:
        limit = None

    if data['profile']:
        pr = cProfile.Profile()
        pr.enable()

    thy = basic.load_theory(data['theory_name'], limit=limit, username=username)
    print("Load: %f" % (time.perf_counter() - start_time))
    start_time = time.perf_counter()

    # Obtain initial state
    ctxt = Context(thy, vars=data['vars'])
    state = server.parse_init_state(ctxt, data['prop'])

    # Traverse data['steps'] upto index, save state, then continue traversal.
    index = data['index']
    history = state.parse_steps(data['steps'][:index])
    json_state = state.json_data()
    history.extend(state.parse_steps(data['steps'][index:]))

    res = {
        'state': json_state,
        'history': history
    }
    try:
        state.check_proof()
    except Exception as e:
        res['error'] = {
            'err_type': e.__class__.__name__,
            'err_str': str(e),
            'trace': traceback2.format_exc()
        }
    print("Parse: %f" % (time.perf_counter() - start_time))

    if data['profile']:
        p = Stats(pr)
        p.strip_dirs()
        p.sort_stats('cumtime')
        p.print_stats()

    return jsonify(res)


@app.route('/api/apply-method', methods=['POST'])
def apply_method():
    """Apply a proof method.

    Input:
    * username: username.
    * theory_name: name of the theory.
    * thm_name: name of the theorem to be proved.
    * proof: starting proof.
    * step: step to be applied.

    Returns:
    * On success: the updated proof.
    * On failure: query for parameters, or fail outright.

    """
    data = json.loads(request.get_data().decode("utf-8"))
    username = data['username']
    if 'thm_name' in data:
        limit = ('thm', data['thm_name'])
    else:
        limit = None

    start_time = time.perf_counter()
    thy = basic.load_theory(data['theory_name'], limit=limit, username=username)
    ctxt = Context(thy, vars=data['vars'])
    state = server.parse_init_state(ctxt, data['prop'])
    index = data['index']
    history = state.parse_steps(data['steps'][:index])
    print("Parse:", time.perf_counter() - start_time)
    start_time = time.perf_counter()

    try:
        step_output = method.output_step(state, data['step'], unicode=True, highlight=True)
        method.apply_method(state, data['step'])
        state.check_proof(compute_only=True)
        history.append({
            'step_output': step_output,
            'goal_id': data['step']['goal_id'],
            'fact_ids': data['step']['fact_ids']
        })
    except Exception as e:
        if isinstance(e, theory.ParameterQueryException):
            return jsonify({
                "query": e.params
            })
        else:
            return jsonify({
                "error": {
                    "err_type": e.__class__.__name__,
                    "err_str": str(e),
                    "trace": traceback2.format_exc()
                }
            })

    json_state = state.json_data()
    history.extend(state.parse_steps(data['steps'][index:]))
    return jsonify({
        'state': json_state,
        'history': history
    })


@app.route('/api/load-json-file', methods=['POST'])
def load_json_file():
    """Loads json file for the given user and file name.

    Input:
    * username: username.
    * filename: name of the file.
    * line_length: maximum length of printed line.

    Returns:
    * content of the file.

    """
    data = json.loads(request.get_data().decode("utf-8"))
    username = data['username']
    filename = data['filename']
    line_length = data.get('line_length')

    if data['profile']:
        pr = cProfile.Profile()
        pr.enable()

    cache = basic.load_theory_cache(filename, username)
    f_data = {
        'name': filename,
        'imports': cache['imports'],
        'description': cache['description'],
        'content': []
    }
    thy = basic.load_theories(cache['imports'])
    for item in cache['content']:
        if item.error is None:
            thy.unchecked_extend(item.get_extension())
        output_item = item.export_web(thy, line_length=line_length)
        f_data['content'].append(output_item)

    if data['profile']:
        p = Stats(pr)
        p.strip_dirs()
        p.sort_stats('cumtime')
        p.print_stats()

    return jsonify(f_data)


@app.route('/api/save-file', methods=['POST'])
def save_file():
    """Save given data to file.
    
    Input:
    * username: username
    * filename: name of the file.
    
    """
    data = json.loads(request.get_data().decode("utf-8"))
    username = data['username']
    filename = data['filename']

    with open(basic.user_file(filename, username), 'w+', encoding='utf-8') as f:
        json.dump(data['content'], f, indent=4, ensure_ascii=False, sort_keys=True)

    return jsonify({})


@app.route('/api/search-method', methods=['POST'])
def search_method():
    """Match for applicable methods and their arguments.
    
    Input:
    * username: username.
    * theory_name: name of the theory.
    * thm_name: name of the theorem.

    Returns:
    * search_res: list of search results.
    * ctxt: current proof context.

    """
    data = json.loads(request.get_data().decode("utf-8"))
    username = data['username']

    if 'thm_name' in data:
        limit = ('thm', data['thm_name'])
    else:
        limit = None
    start_time = time.perf_counter()

    if data['profile']:
        pr = cProfile.Profile()
        pr.enable()

    thy = basic.load_theory(data['theory_name'], limit=limit, username=username)
    print("Load:", time.perf_counter() - start_time)
    start_time = time.perf_counter()

    ctxt = Context(thy, vars=data['vars'])
    state = server.parse_init_state(ctxt, data['prop'])
    index = data['index']
    state.parse_steps(data['steps'][:index])
    print("Parse:", time.perf_counter() - start_time)
    start_time = time.perf_counter()
    fact_ids = data['step']['fact_ids']
    goal_id = data['step']['goal_id']

    search_res = state.search_method(goal_id, fact_ids)
    for res in search_res:
        if '_goal' in res:
            res['_goal'] = [printer.print_term(thy, t, unicode=True) for t in res['_goal']]
        if '_fact' in res:
            res['_fact'] = [printer.print_term(thy, t, unicode=True) for t in res['_fact']]

    ctxt = state.get_ctxt(goal_id)
    print_ctxt = dict((k, printer.print_type(thy, v, unicode=True, highlight=True))
                      for k, v in ctxt.vars.items())
    print("Response:", time.perf_counter() - start_time)

    if data['profile']:
        p = Stats(pr)
        p.strip_dirs()
        p.sort_stats('cumtime')
        p.print_stats()

    return jsonify({
        'search_res': search_res,
        'ctxt': print_ctxt
    })


@app.route('/api/check-modify', methods=['POST'])
def check_modify():
    """Check a modified item for validity.
    
    Input:
    * username: username.
    * filename: name of the file.
    * line_length: maximum length of printed line.
    * item: item to be checked.

    Returns:
    * checked item.

    """
    data = json.loads(request.get_data().decode("utf-8"))
    username = data['username']
    edit_item = data['item']
    line_length = data.get('line_length')

    if 'limit_ty' in data:
        limit = (data['limit_ty'], data['limit_name'])
    else:
        limit = None

    thy = basic.load_theory(data['filename'], limit=limit, username=username)
    item = items.parse_edit(thy, edit_item)
    if item.error is None:
        thy.unchecked_extend(item.get_extension())
    output_item = item.export_web(thy, line_length=line_length)

    return jsonify({
        'item': output_item
    })


@app.route('/api/find-files', methods=['POST'])
def find_files():
    """Find list of files in user's directory.
    
    Input:
    * username: username.

    """
    data = json.loads(request.get_data().decode("utf-8"))
    username = data['username']

    basic.load_metadata(username=username)

    files = []
    for name, cache in basic.theory_cache[username].items():
        files.append((cache['order'], name))
    files.sort()

    return jsonify({
        'theories': tuple(name for _, name in files)
    })


@app.route('/api/remove-file', methods=['PUT'])
def remove_file():
    """Remove file with the given name.
    
    Input:
    * username: username.
    * filename: name of the file.

    """
    data = json.loads(request.get_data().decode("utf-8"))
    username = data['username']
    filename = data['filename']
    os.remove(basic.user_file(filename, username))

    return jsonify({})


@app.route('/api/find-link', methods=['POST'])
def find_link():
    """Return the location of the link.

    Input:
    * username: username.
    * filename: name of the file in which the query originates.
    * ty: type of item.
    * name: name of the item to find.

    Returns:
    * filename: name of the theory file.
    * position: index of the item in the theory.

    """
    data = json.loads(request.get_data().decode("utf-8"))
    username = data['username']

    res = basic.query_item_index(username, data['filename'], data['ext_ty'], data['name'])
    if res:
        filename, index = res
        return jsonify({
            'filename': filename,
            'index': index
        })
    else:
        return jsonify({})

@app.route('/api/check-theory', methods=['POST'])
def check_theory():
    """Check a theory.
    
    * username: username.
    * filename: name of the theory file.

    """
    data = json.loads(request.get_data().decode("utf-8"))
    username = data['username']
    filename = data['filename']

    res = monitor.check_theory(filename, username, rewrite=data['rewrite'])
    return jsonify(res)


# Initialization
basic.load_metadata('master')
