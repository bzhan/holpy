# Author: Chaozhu Xiang, Bohua Zhan

import os, sqlite3, shutil
import json, sys, io, traceback2
from flask import Flask, request, render_template, redirect, session
from flask.json import jsonify
import time

from kernel import type as hol_type
from kernel.type import HOLType, TVar, Type, TFun
from kernel.term import get_vars
from kernel import extension, theory
from syntax import parser, printer, settings, pprint
from server import server, method
from logic import basic
from logic.basic import user_dir, user_file
from logic import induct
from imperative import parser2
from imperative import imp
from prover import z3wrapper
from syntax import infertype
from server.server import ProofState
from imperative.parser2 import cond_parser, com_parser
from flask_cors import CORS


app = Flask(__name__, static_url_path='/static')
CORS(app)
app.secret_key = b'_5#y2L"F4Q8z\n\xec]/'

app.config.from_object('config')


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
            line['smt'] = z3wrapper.solve(vc_hol)

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
    start_time = time.clock()
    try:
        if 'thm_name' in data:
            limit = ('thm', data['thm_name'])
        else:
            limit = None
        thy = basic.load_theory(data['theory_name'], limit=limit, username=username)
        print("Load: %f" % (time.clock() - start_time))
        start_time = time.clock()
        cell = server.ProofState.parse_proof(thy, data['proof'])
        print("Parse: %f" % (time.clock() - start_time))
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
    * thm_name: name of the theorem.

    Returns:
    * updated proof.

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
        step_output = method.display_method(cell, data['step'], unicode=True, highlight=True)
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
        parsed_data = parser.parse_item(thy, data)
        ext = parser.get_extension(thy, parsed_data)
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
    if data['ty'] == 'def.ax':
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
    if 'content' in f_data:
        thy = basic.load_theories(f_data['imports'], username=username)
        for item in f_data['content']:
            file_data_to_output(thy, item, line_length=line_length)
    else:
        f_data['content'] = []

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
    start_time = time.clock()
    thy = basic.load_theory(data['theory_name'], limit=limit, username=username)
    print("Load:", time.clock() - start_time)
    start_time = time.clock()
    cell = server.ProofState.parse_proof(thy, data['proof'])
    print("Parse:", time.clock() - start_time)
    start_time = time.clock()
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
                      for k, v in ctxt['vars'].items())
    print("Response:", time.clock() - start_time)
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

    start_time = time.clock()
    try:
        limit = (item['ty'], data['prev_name'])
        thy = basic.load_theory(data['filename'], limit=limit, username=username)
        print("Load:", time.clock() - start_time)
        start_time = time.clock()
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
            assert T.ty == hol_type.TYPE and all(argT.ty == hol_type.TVAR for argT in T.args), \
                "invalid input type."
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

    print("Check:", time.clock() - start_time)
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
    * ty: type of item.
    * name: name of the item to find.

    Returns:
    * filename: name of the theory file.
    * position: index of the item in the theory.

    """
    data = json.loads(request.get_data().decode("utf-8"))
    username = data['username']

    res = basic.query_item_index(username, data['ty'], data['name'])
    if res:
        filename, index = res
        return jsonify({
            'filename': filename,
            'index': index
        })
    else:
        return jsonify({})


# Initialization
basic.load_metadata('master')
