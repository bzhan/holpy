# Author: Chaozhu Xiang, Bohua Zhan

import os, sqlite3, shutil
import json, sys, io, traceback2
from flask import Flask, request, render_template, redirect, session
from flask.json import jsonify
from flask_cors import CORS
import time
from pstats import Stats
import cProfile

from kernel.type import TVar, Type, TFun
from kernel import extension, theory
from syntax import parser, printer, settings, pprint
from server import server, method
from logic import basic
from logic.basic import user_dir, user_file
from logic import induct
from imperative import parser2
from imperative import imp
from prover import z3wrapper
from server.server import ProofState
from server import monitor
from imperative.parser2 import cond_parser, com_parser
import integral


app = Flask(__name__, static_url_path='/static')
CORS(app)
app.secret_key = b'_5#y2L"F4Q8z\n\xec]/'


@app.route('/api/login', methods=['POST'])
def login():
    """Login for an user.

    Input:
    * username: username
    * password: password

    Returns:
    * result: success - login is successful.
    * result: failed - login failed (username / password do not match).

    """
    data = json.loads(request.get_data().decode('utf-8'))
    username = data['username']
    password = data['password']
    for k in get_users():
        if username == k[1] and password == str(k[2]):
            user_list = os.listdir('./users')
            if username != 'master' and username not in user_list:
                shutil.copytree('./library', user_dir(username))

            return jsonify({'result': 'success'})

    return jsonify({'result': 'failed'})


@app.route('/api/register', methods=['POST'])
def register():
    """Register a new user.

    Input:
    * username: username
    * password: password

    Returns:
    * result: success - registration is successful.
    * result: failed - registration failed (user already exists).

    """
    data = json.loads(request.get_data().decode('utf-8'))
    username = data['username']
    password = data['password']
    for k in get_users():
        if username == k[1]:
            return jsonify({'result': 'failed'})

    if username and password:
        add_user(username, password)

    return jsonify({'result': 'success'})


DATABASE = os.getcwd() + '/users/user.db'


def add_user(username, password):
    """Add new user to the database."""
    with sqlite3.connect(DATABASE) as conn:
        cursor = conn.cursor()
        cursor.execute('insert into users(name, password) values("'+ username +'","'+ password +'");')
        cursor.close()
        conn.commit()

def init_user():
    """Create users table."""
    with sqlite3.connect(DATABASE) as conn:
        cursor = conn.cursor()
        cursor.execute('create table users(id auto_increment,name CHAR(50) not null,password CHAR(50) not null);')
        cursor.close()
        conn.commit()

def get_users():
    """Get list of username-password from the database."""
    with sqlite3.connect(DATABASE) as conn:
        cursor = conn.cursor()
        cursor.execute('select * from users;')
        results = cursor.fetchall()
        cursor.close()
        conn.commit()
    return results

@app.route('/api/get-program-file', methods = ['POST'])
def get_program_file():
    """Load a json file for program verification.
    
    Input:
    * file_name: name of the file (under imperative/examples).

    Returns:
    * file_data: content of the file.

    """
    data = json.loads(request.get_data().decode("utf-8"))
    file_name = data['file_name']
    thy = basic.load_theory('hoare')
    path = 'imperative/examples/' + file_name + '.json'
    with open(path, 'r', encoding='utf-8') as f:
        file_data = json.load(f)

    for i, item in enumerate(file_data['content']):
        if item['ty'] == 'vcg':
            program = parser2.com_parser.parse(item['com']).print_com(item['vars'])
            item['com'] = '\n'.join(program)

    return jsonify({'file_data': file_data['content']})

@app.route('/api/program-verify', methods=['POST'])
def verify():
    """Verify a program by generating verification conditions,
    and attempt to solve the conditions using SMT.

    """
    data = json.loads(request.get_data().decode("utf-8"))
    thy = basic.load_theory('hoare')
    pre = cond_parser.parse(data['pre'])
    post = cond_parser.parse(data['post'])
    com = com_parser.parse(data['com'])
    com.pre = [pre]
    com.compute_wp(post)
    lines = com.get_lines(data['vars'])

    for line in lines:
        if line['ty'] == 'vc':
            vc_hol = line['prop']
            line['prop'] = printer.print_term(thy, line['prop'])
            line['smt'] = z3wrapper.solve(thy, vc_hol)

    return jsonify({
        'lines': lines,
    })

@app.route('/api/save-program-proof', methods=['POST'])
def save_program_proof():
    """Save a proof for program verification.
    
    """
    data = json.loads(request.get_data().decode("utf-8"))

    file_name = data['file_name']
    path = 'imperative/examples/' + file_name + '.json'
    with open(path, 'r', encoding='utf-8') as f:
        file_data = json.load(f)

    cur_index = data['index']
    proof = data['proof']
    file_data['content'][cur_index]['proof'] = proof

    with open(path, 'w', encoding='utf-8') as f:
        json.dump(file_data, f, indent=4, ensure_ascii=False, sort_keys=True)

    return jsonify({})


@app.route('/api/refresh-files', methods=['POST'])
def refresh_files():
    """Replace user data with library data.

    Input:
    * username: username.

    """
    data = json.loads(request.get_data().decode("utf-8"))
    username = data['username']
    if username != 'master':
        shutil.rmtree(user_dir(username))
        shutil.copytree('./library', user_dir(username))

    return jsonify({})


@app.route('/api/init-empty-proof', methods=['POST'])
def init_empty_proof():
    """Initialize an empty proof for the given theorem.

    Input:
    * username: username.
    * theory_name: name of the theory.
    * thm_name: name of the theorem.
    * proof: initial data for the proof.

    Returns:
    * initial proof of the theorem.
    
    """
    data = json.loads(request.get_data().decode("utf-8"))
    username = data['username']
    if 'thm_name' in data:
        limit = ('thm', data['thm_name'])
    else:
        limit = None
    thy = basic.load_theory(data['theory_name'], limit=limit, username=username)
    cell = server.ProofState.parse_init_state(thy, data['proof'])
    return jsonify(cell.json_data())


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
    try:
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
        cell = server.ProofState.parse_proof(thy, data['proof'])
        print("Parse: %f" % (time.perf_counter() - start_time))

        if data['profile']:
            p = Stats(pr)
            p.strip_dirs()
            p.sort_stats('cumtime')
            p.print_stats()

        return jsonify(cell.json_data())
    except Exception as e:
        error = {
            "err_type": e.__class__.__name__,
            "err_str": str(e),
            "trace": traceback2.format_exc()
        }
    return jsonify(error)


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
    thy = basic.load_theory(data['theory_name'], limit=limit, username=username)
    cell = server.ProofState.parse_proof(thy, data['proof'])
    try:
        step_output = method.output_step(cell, data['step'], unicode=True, highlight=True)
        method.apply_method(cell, data['step'])
        cell_data = cell.json_data()
        cell_data['steps_output'] = step_output
        return jsonify(cell_data)
    except Exception as e:
        if isinstance(e, theory.ParameterQueryException):
            return jsonify({
                "query": e.params
            })
        else:
            return jsonify({
                "err_type": e.__class__.__name__,
                "err_str": str(e),
                "trace": traceback2.format_exc()
            })

@app.route('/api/apply-steps', methods=['POST'])
def apply_steps():
    """Apply multiple steps in batch mode.

    Unlike apply_method, failure in one of the steps does not lead
    to exit of the function. Instead, error information is returned
    along with the history.

    Input:
    * username: username.
    * theory_name: name of the theory.
    * thm_name: name of the theorem to be proved.
    * proof: starting proof.
    * steps: steps to be applied.

    Returns:
    * history: history of the proof when applying steps.

    """
    data = json.loads(request.get_data().decode("utf-8"))
    username = data['username']
    if 'thm_name' in data:
        limit = ('thm', data['thm_name'])
    else:
        limit = None
    thy = basic.load_theory(data['theory_name'], limit=limit, username=username)
    state = server.ProofState.parse_proof(thy, data['proof'])

    history = []
    for step in data['steps']:
        history.append({
            'steps_output': step['method_name'],
            'proof': state.export_proof(state.prf),
            'num_gaps': len(state.rpt.gaps)
        })
        try:
            step_output = method.output_step(state, step, unicode=True, highlight=True),
            history[-1]['steps_output'] = step_output
            method.apply_method(state, step)
            state.check_proof(compute_only=True)
        except Exception as e:
            history[-1]['error'] = {
                'err_type': e.__class__.__name__,
                'err_str': str(e),
                'trace': traceback2.format_exc()
            }
    history.append({
        'proof': state.export_proof(state.prf),
        'num_gaps': len(state.rpt.gaps)
    })
    try:    
        state.check_proof()
    except Exception as e:
        history[-1]['error'] = {
            'err_type': e.__class__.__name__,
            'err_str': str(e),
            'trace': traceback2.format_exc()
        }
    
    return jsonify({
        'history': history
    })


def file_data_to_output(thy, data, *, line_length=None):
    """Convert items in the theory from json format for the file to
    json format for the web client. Modifies data in-place.
    Also modifies argument thy in parsing the item.

    """
    parsed_data = None
    ext = None

    # Attempt to parse the item, creating a parsed version (with
    # strings replaced by types and terms) and the extension. If
    # parsing succeeds, apply the extension to the theory. Otherwise,
    # add exception information to the item.
    try:
        parsed_data = basic.parse_item(thy, data)
        ext = basic.get_extension(thy, parsed_data)
        thy.unchecked_extend(ext)
    except Exception as e:
        data['err_type'] = e.__class__.__name__
        data['err_str'] = str(e)
        data['trace'] = traceback2.format_exc()

    # If parsing failed, still create strings for editing.
    if parsed_data is None:
        if data['ty'] in ('thm', 'thm.ax'):
            data['vars_lines'] = '\n'.join(k + ' :: ' + v for k, v in data['vars'].items())
            data['prop_lines'] = data['prop']
            if not isinstance(data['prop_lines'], str):
                data['prop_lines'] = '\n'.join(data['prop_lines'])
        elif data['ty'] == 'def':
            data['prop_lines'] = data['prop']
            if not isinstance(data['prop_lines'], str):
                data['prop_lines'] = '\n'.join(data['prop_lines'])

        return

    # If parsing succeeds, fill data with pretty-printed form of
    # types and terms
    if data['ty'] == 'type.ax':
        Targs = [TVar(arg) for arg in data['args']]
        T = Type(data['name'], *Targs)
        data['type_hl'] = printer.print_type(thy, T, unicode=True, highlight=True)

    elif data['ty'] == 'def.ax':
        data['type_hl'] = printer.print_type(thy, parsed_data['type'], unicode=True, highlight=True)

    elif data['ty'] in ('thm', 'thm.ax'):
        data['vars_lines'] = '\n'.join(nm + ' :: ' + printer.print_type(thy, T, unicode=True)
                                       for nm, T in parsed_data['vars'].items())
        ast = pprint.get_ast_term(thy, parsed_data['prop'], unicode=True)
        data['prop_lines'] = '\n'.join(pprint.print_ast(thy, ast, highlight=False, line_length=line_length))
        data['prop_hl'] = pprint.print_ast(thy, ast, highlight=True, line_length=line_length)

    elif data['ty'] == 'type.ind':
        constrs = []
        data['constrs_lines'] = []
        data['constrs_hl'] = []
        for constr in parsed_data['constrs']:
            data['constrs_lines'].append(printer.print_type_constr(thy, constr, unicode=True, highlight=False))
            data['constrs_hl'].append(printer.print_type_constr(thy, constr, unicode=True, highlight=True))
        data['constrs_lines'] = '\n'.join(data['constrs_lines'])

        # Obtain type to be defined
        T = Type(data['name'], *(TVar(nm) for nm in data['args']))
        data['type_hl'] = printer.print_type(thy, T, unicode=True, highlight=True)
        data['edit_type'] = printer.print_type(thy, T, unicode=True, highlight=False)

    elif data['ty'] in ('def.ind', 'def.pred'):
        data['type_hl'] = printer.print_type(thy, parsed_data['type'], unicode=True, highlight=True)

        rules = []
        data['prop_lines'] = []
        for i, rule in enumerate(data['rules']):
            prop = parsed_data['rules'][i]['prop']
            rule['prop_hl'] = printer.print_term(thy, prop, unicode=True, highlight=True)
            content = printer.print_term(thy, prop, unicode=True, highlight=False)
            if data['ty'] == 'def.pred':
                content = rule['name'] + ': ' + content
                rules.append((rule['name'], prop))
            else:
                rules.append(prop)
            data['prop_lines'].append(content)

        data['prop_lines'] = '\n'.join(data['prop_lines'])

    elif data['ty'] == 'def':
        data['type'] = printer.print_type(thy, parsed_data['type'], unicode=True)
        data['type_hl'] = printer.print_type(thy, parsed_data['type'], unicode=True, highlight=True)

        ast = pprint.get_ast_term(thy, parsed_data['prop'], unicode=True)
        data['prop_lines'] = '\n'.join(pprint.print_ast(thy, ast, highlight=False, line_length=line_length))
        data['prop_hl'] = pprint.print_ast(thy, ast, highlight=True, line_length=line_length)

    # Ignore other types of information.
    else:
        pass

    # Obtain items added by the extension
    if ext and data['ty'] in ('type.ind', 'def', 'def.ind', 'def.pred'):
        data['ext'] = printer.print_extensions(thy, ext, unicode=True)


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
    with open(user_file(filename, username), 'r', encoding='utf-8') as f:
        f_data = json.load(f)

    if data['profile']:
        pr = cProfile.Profile()
        pr.enable()
        
    if 'content' in f_data:
        thy = basic.load_theories(f_data['imports'], username=username)
        for item in f_data['content']:
            file_data_to_output(thy, item, line_length=line_length)
    else:
        f_data['content'] = []

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

    with open(user_file(filename, username), 'w+', encoding='utf-8') as f:
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
    cell = server.ProofState.parse_proof(thy, data['proof'])
    print("Parse:", time.perf_counter() - start_time)
    start_time = time.perf_counter()
    fact_ids = data['step']['fact_ids']
    goal_id = data['step']['goal_id']
    search_res = cell.search_method(goal_id, fact_ids)
    for res in search_res:
        if '_goal' in res:
            res['_goal'] = [printer.print_term(thy, t, unicode=True) for t in res['_goal']]
        if '_fact' in res:
            res['_fact'] = [printer.print_term(thy, t, unicode=True) for t in res['_fact']]

    ctxt = cell.get_ctxt(goal_id)
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
    item = data['item']
    line_length = data.get('line_length')

    start_time = time.perf_counter()
    try:
        if 'limit_ty' in data:
            limit = (data['limit_ty'], data['limit_name'])
        else:
            limit = None
        thy = basic.load_theory(data['filename'], limit=limit, username=username)
        print("Load:", time.perf_counter() - start_time)
        start_time = time.perf_counter()
        if item['ty'] == 'thm' or item['ty'] == 'thm.ax':
            item['vars'] = dict()
            for var_decl in item['vars_lines'].split('\n'):
                if var_decl:
                    nm, T = parser.parse_var_decl(thy, var_decl)
                    item['vars'][nm] = str(T)

            item['prop'] = item['prop_lines'].split('\n')
            if len(item['prop']) == 1:
                item['prop'] = item['prop'][0]

        if item['ty'] == 'type.ind':
            T = parser.parse_type(thy, item['edit_type'])
            assert T.is_type() and all(argT.is_tvar() for argT in T.args), "invalid input type."
            item['name'] = T.name
            item['args'] = [argT.name for argT in T.args]

            item['constrs'] = []
            for constr in item['constrs_lines'].split('\n'):
                if constr:
                    constr = parser.parse_ind_constr(thy, constr)
                    constr['type'] = str(TFun(*(constr['type'] + [T])))
                    item['constrs'].append(constr)

        if item['ty'] == 'def':
            item['prop'] = item['prop_lines'].split('\n')
            if len(item['prop']) == 1:
                item['prop'] = item['prop'][0]

        if item['ty'] == 'def.ind':
            item['rules'] = []
            for line in item['prop_lines'].split('\n'):
                item['rules'].append({'prop': line})

        if item['ty'] == 'def.pred':
            T = parser.parse_type(thy, item['type'])
            item['rules'] = []
            for line in item['prop_lines'].split('\n'):
                colon = line.find(':')
                item['rules'].append({
                    'name': line[0:colon].strip(),
                    'prop': line[colon+1:].strip()
                })

        file_data_to_output(thy, item, line_length=line_length)
    except Exception as e:
        item['err_type'] = e.__class__.__name__
        item['err_str'] = str(e)
        item['trace'] = traceback2.format_exc()

    print("Check:", time.perf_counter() - start_time)
    return jsonify({
        'item': item
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
    os.remove(user_file(filename, username))

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


@app.route("/api/integral-open-file", methods=['POST'])
def integral_open_file():
    data = json.loads(request.get_data().decode('utf-8'))
    file_name = "integral/examples/%s.json" % data['filename']
    with open(file_name, 'r', encoding='utf-8') as f:
        f_data = json.load(f)

    for item in f_data['content']:
        problem = integral.parser.parse_expr(item['problem'])
        item['_problem_latex'] = integral.latex.convert_expr(problem)

    return jsonify(f_data)

@app.route("/api/integral-initialize", methods=['POST'])
def integral_initialize():
    data = json.loads(request.get_data().decode('utf-8'))
    problem = integral.parser.parse_expr(data['problem'])
    return jsonify({
        'text': str(problem),
        'latex': integral.latex.convert_expr(problem),
        'reason': "Initial"
    })

@app.route("/api/integral-linearity", methods=['POST'])
def integral_linearity():
    data = json.loads(request.get_data().decode('utf-8'))
    rule = integral.rules.Linearity()
    problem = integral.parser.parse_expr(data['problem'])
    new_problem = rule.eval(problem)
    return jsonify({
        'text': str(new_problem),
        'latex': integral.latex.convert_expr(new_problem),
        'reason': "Linearity"
    })

@app.route("/api/integral-simplify", methods=['POST'])
def integral_simplify():
    data = json.loads(request.get_data().decode('utf-8'))
    rule = integral.rules.Simplify()
    problem = integral.parser.parse_expr(data['problem'])
    new_problem = rule.eval(problem)
    return jsonify({
        'text': str(new_problem),
        'latex': integral.latex.convert_expr(new_problem),
        'reason': "Simplification"
    })

@app.route("/api/integral-common-integral", methods=['POST'])
def integral_common_integral():
    data = json.loads(request.get_data().decode('utf-8'))
    rule = integral.rules.OnSubterm(integral.rules.CommonIntegral())
    problem = integral.parser.parse_expr(data['problem'])
    new_problem = rule.eval(problem)
    return jsonify({
        'text': str(new_problem),
        'latex': integral.latex.convert_expr(new_problem),
        'reason': "Common integrals"
    })

@app.route("/api/integral-trig-transformation", methods=['POST'])
def integral_trig_transformation():
    data = json.loads(request.get_data().decode('utf-8'))
    rule = integral.rules.TrigSubstitution()
    del integral.expr.trig_identity[:]
    problem = integral.parser.parse_expr(data['problem'])
    e = integral.parser.parse_expr(data['exp'])
    if e.normalize() == problem.body.normalize():
        e = integral.expr.Integral(problem.var, problem.lower, problem.upper, e)
        possible_new_problem = rule.eval(e)
        for i in possible_new_problem:
            print(i)
        n = []
        index = 1
        for p in possible_new_problem:
            n.append({ 
                'text': str(p),
                'latex': integral.latex.convert_expr(p),
                'reason': "Trig Identity"
            })
            index += 1
        return json.dumps(n)
    else:
        return jsonify({
            'text': str(problem),
            'latex': integral.latex.convert_expr(problem),
            'reason': "The expression you write is not equal to the initial one."
        })

@app.route("/api/integral-substitution", methods=['POST'])
def integral_substitution():
    data = json.loads(request.get_data().decode('utf-8'))
    expr = integral.parser.parse_expr(data['expr'])
    rule = integral.rules.Substitution(data['var_name'], expr)
    problem = integral.parser.parse_expr(data['problem'])
    new_problem = rule.eval(problem)
    return jsonify({
        'text': str(new_problem),
        'latex': integral.latex.convert_expr(new_problem),
        'reason': "Substitution",
        'params': {
            'var_name': data['var_name'],
            'expr': data['expr'],
        },
        '_latex_reason': "Substitute \\(%s\\) for \\(%s\\)" % (
            data['var_name'], integral.latex.convert_expr(expr)
        )
    })

@app.route("/api/integral-integrate-by-parts", methods=['POST'])
def integral_integrate_by_parts():
    data = json.loads(request.get_data().decode('utf-8'))
    parts_u = integral.parser.parse_expr(data['parts_u'])
    parts_v = integral.parser.parse_expr(data['parts_v'])
    rule = integral.rules.IntegrationByParts(parts_u, parts_v)
    problem = integral.parser.parse_expr(data['problem'])
    new_problem = rule.eval(problem)
    return jsonify({
        'text': str(new_problem),
        'latex': integral.latex.convert_expr(new_problem),
        'reason': "Integrate by parts",
        'params': {
            'parts_u': data['parts_u'],
            'parts_v': data['parts_v'],
        },
        '_latex_reason': "Integrate by parts, \\(u = %s, v = %s\\)" % (
            integral.latex.convert_expr(parts_u), integral.latex.convert_expr(parts_v)
        )
    })

@app.route("/api/integral-equation-substitution", methods=['POST'])
def integral_equation_substitution():
    data = json.loads(request.get_data().decode('utf-8'))
    old_expr = integral.parser.parse_expr(data['old_expr']).body
    new_expr = integral.parser.parse_expr(data['new_expr'])
    rule = integral.rules.Equation(old_expr, new_expr)
    problem = integral.parser.parse_expr(data['problem'])
    new_problem = rule.eval(problem)
    if new_problem != problem:
        return jsonify({
            'text': str(new_problem),
            'latex': integral.latex.convert_expr(new_problem),
            'reason': "Integrate by parts",
            'params': {
                'old_expr': data['old_expr'],
                'new_expr': data['new_expr'],
            },
            '_latex_reason': "Equation substitution successful, \\( %s\\) = \\(%s\\)" % (
                integral.latex.convert_expr(old_expr), integral.latex.convert_expr(new_expr)
            )
        })
    else:
        return jsonify({
            'text': str(new_problem),
            'latex': integral.latex.convert_expr(new_problem),
            'reason': "Integrate by parts",
            'params': {
                'old_expr': data['old_expr'],
                'new_expr': data['new_expr'],
            },
            '_latex_reason': "Equation substitution failed, \\( %s\\) != \\(%s\\)" % (
                integral.latex.convert_expr(old_expr), integral.latex.convert_expr(new_expr)
            )
        })

@app.route("/api/integral-polynomial-division", methods=['POST'])
def integral_polynomial_division():
    data = json.loads(request.get_data().decode('utf-8'))
    rule = integral.rules.PolynomialDivision()
    problem = integral.parser.parse_expr(data['problem'])
    new_problem = rule.eval(problem)
    return jsonify({
        'text': str(new_problem),
        'latex': integral.latex.convert_expr(new_problem),
        'reason': "Polynomial division"
    })

@app.route("/api/integral-save-file", methods=['POST'])
def integral_save_file():
    data = json.loads(request.get_data().decode('utf-8'))
    file_name = "integral/examples/%s.json" % data['filename']
    with open(file_name, 'w', encoding='utf-8') as f:
        json.dump({"content": data['content']}, f, indent=4, ensure_ascii=False, sort_keys=True)

    return jsonify({
        'status': 'success'
    })


# Initialization
basic.load_metadata('master')
