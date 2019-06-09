# Author: Chaozhu Xiang, Bohua Zhan

from copy import copy
import os, sqlite3, shutil
import json, sys, io, traceback2
from flask import Flask, request, render_template, redirect, session
from flask.json import jsonify
from kernel.type import HOLType, TVar, Type
from syntax import parser, printer, settings
from server import method
from server.server import ProofState
from logic import basic
from logic import induct
from kernel.extension import AxType, AxConstant, Theorem
from kernel.type import TFun

sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding='utf-8')
app = Flask(__name__, static_url_path='/static')
app.secret_key = b'_5#y2L"F4Q8z\n\xec]/'

app.config.from_object('config')

# Dictionary from id to ProofState
cells = dict()

user_info = {
    # Whether there is an user signed in
    'is_signed_in': False,

    # Name of the user signed in
    'username': "",

    # List of files in user's directory
    'file_list': []
}

# Templates
@app.route('/display_results.html', methods=['GET'])
def display_results_template():
    return render_template('display_results.html')

@app.route('/edit_area.html', methods=['GET'])
def edit_area_template():
    return render_template('edit_area.html')

@app.route('/proof_area.html', methods=['GET'])
def proof_area_template():
    return render_template('proof_area.html')


# Login page
@app.route('/', methods=['GET', 'POST'])
def index():
    return render_template('login.html')

# Sign out
@app.route('/sign-out', methods=['get'])
def sign_out():
    user_info['is_signed_in'] = False
    return redirect('/')

# Register page
@app.route('/register', methods=['GET'])
def register():
    return render_template('register.html')

# Error for user already exists
@app.route('/register-error', methods=['GET'])
def register_error():
    return render_template('register.html', info='User already exists')

# Error for incorrect username or password
@app.route('/login-error', methods=['GET', 'POST'])
def login_error():
    return render_template('login.html', info='Incorrect username or password')

# Register new user
@app.route('/register_login', methods=['POST'])
def register_login():
    username = request.form.get('name')
    password = request.form.get('password')
    for k in get_users():
        if username == k[1]:
            return redirect('register-error')
    if username and password:
        add_user(username, password)

    return redirect('/')

# Load main page for the given user
@app.route('/load', methods=['GET'])
def load():
    if not user_info['is_signed_in']:
        return redirect('/')

    return render_template('index.html', user=user_info['username'])


def add_user(username, password):
    """Add new user to the database."""
    DATABASE = os.getcwd() + '/users/user.db'

    conn = sqlite3.connect(DATABASE)
    cursor = conn.cursor()
    cursor.execute('insert into users(name, password) values("'+ username +'","'+ password +'");')
    cursor.close()
    conn.commit()
    conn.close()

def init_user():
    """Create users table."""
    DATABASE = os.getcwd() + '/users/user.db'

    conn = sqlite3.connect(DATABASE)
    cursor = conn.cursor()
    cursor.execute('create table users(id auto_increment,name CHAR(50) not null,password CHAR(50) not null);')
    cursor.close()
    conn.commit()
    conn.close()

def get_users():
    """Get list of username-password from the database."""
    DATABASE = os.getcwd() + '/users/user.db'

    conn = sqlite3.connect(DATABASE)
    cursor = conn.cursor()
    cursor.execute('select * from users;')
    results = cursor.fetchall()
    cursor.close()
    conn.commit()
    conn.close()

    return results


# Login for user
@app.route('/login', methods=['GET', 'POST'])
def login():
    username = request.form.get('name')
    password = request.form.get('password')
    user_path = './users/' + username
    for k in get_users():
        if username == k[1] and password == str(k[2]):
            user_info['is_signed_in'] = True
            user_info['username'] = username
            user_list = os.listdir('./users')
            if username not in user_list:
                shutil.copytree('./library', user_path)

            return redirect('/load')

    return redirect('login-error')


# Replace user data with library data
@app.route('/api/refresh-files', methods=['POST'])
def refresh_files():
    if user_info['username']:
        user_path = './users/' + user_info['username']
        shutil.rmtree(user_path)
        shutil.copytree('./library', user_path)
        basic.clear_cache(user=user_info['username'])

    return jsonify({})


@app.route('/api/init-empty-proof', methods=['POST'])
def init_empty_proof():
    """Initialize empty proof."""
    data = json.loads(request.get_data().decode("utf-8"))
    if data:
        thy = basic.load_theory(data['theory_name'], limit=('thm', data['thm_name']), user=user_info['username'])
        cell = ProofState.parse_init_state(thy, data)
        cells[data['id']] = cell
        return jsonify(cell.json_data())
    return jsonify({})


@app.route('/api/init-saved-proof', methods=['POST'])
def init_saved_proof():
    """Load saved proof."""
    data = json.loads(request.get_data().decode("utf-8"))
    if data:
        try:
            thy = basic.load_theory(data['theory_name'], limit=('thm', data['thm_name']), user=user_info['username'])
            cell = ProofState.parse_proof(thy, data)
            cells[data['id']] = cell
            return jsonify(cell.json_data())
        except Exception as e:
            error = {
                "failed": e.__class__.__name__,
                "message": str(e)
            }
        return jsonify(error)
    return jsonify({})


@app.route('/api/add-line-after', methods=['POST'])
def add_line_after():
    data = json.loads(request.get_data().decode("utf-8"))
    if data:
        cell = cells[data['id']]
        cell.add_line_after(data['line_id'])
        return jsonify(cell.json_data())
    return jsonify({})


@app.route('/api/remove-line', methods=['POST'])
def remove_line():
    data = json.loads(request.get_data().decode("utf-8"))
    if data:
        cell = cells[data['id']]
        cell.remove_line(data['line_id'])
        return jsonify(cell.json_data())
    return jsonify({})


@app.route('/api/set-line', methods=['POST'])
def set_line():
    data = json.loads(request.get_data().decode("utf-8"))
    if data:
        cell = cells[data['id']]
        line_id = data['item']['id']
        try:
            item = parser.parse_proof_rule(cell.thy, cell.get_ctxt(line_id), data['item'])
            cell.set_line(item.id, item.rule, args=item.args, prevs=item.prevs, th=item.th)
            return jsonify(cell.json_data())
        except Exception as e:
            error = {
                "failed": e.__class__.__name__,
                "message": str(e)
            }
            return jsonify(error)
    return jsonify({})


@app.route('/api/apply-method', methods=['POST'])
def apply_method():
    data = json.loads(request.get_data().decode("utf-8"))
    cell = cells[data['id']]
    try:
        method.apply_method(cell, data)
        return jsonify(cell.json_data())
    except Exception as e:
        error = {
            "failed": e.__class__.__name__,
            "message": str(e)
        }
        return jsonify(error)

def str_of_extension(thy, exts):
    """Print given extension for display in the edit area."""
    res = []
    for ext in exts.data:
        if isinstance(ext, AxType):
            res.append("Type " + ext.name)
        elif isinstance(ext, AxConstant):
            res.append("Constant " + ext.name + " :: " + printer.print_type(thy, ext.T, unicode=True))
        elif isinstance(ext, Theorem):
            res.append("Theorem " + ext.name + ": " + printer.print_term(thy, ext.th.prop, unicode=True))
    return '\n'.join(res)

@settings.with_settings
def str_of_constr(thy, constr):
    """Print a given constructor."""
    T = parser.parse_type(thy, constr['type'])
    argsT, _ = T.strip_type()
    assert len(argsT) == len(constr['args']), "file_data_to_output: unexpected number of args."
    res = printer.N(constr['name'])
    for i, arg in enumerate(constr['args']):
        res += printer.N(' (' + arg + ' :: ') + printer.print_type(thy, argsT[i]) + printer.N(')')
    return res

def file_data_to_output(thy, data):
    """Convert items in the theory from json format for the file to
    json format for the web client. Modifies data in-place.
    Also modifies argument thy in parsing the item.

    """
    parser.parse_extension(thy, data)
    if data['ty'] == 'def.ax':
        T = parser.parse_type(thy, data['type'])
        data['type_hl'] = printer.print_type(thy, T, unicode=True, highlight=True)

    elif data['ty'] == 'thm' or data['ty'] == 'thm.ax':
        ctxt = parser.parse_vars(thy, data['vars'])
        prop = parser.parse_term(thy, ctxt, data['prop'])
        data['prop_hl'] = printer.print_term(thy, prop, unicode=True, highlight=True)
        data['vars_lines'] = [k + ' :: ' + v for k, v in data['vars'].items()]

    elif data['ty'] == 'type.ind':
        constrs = []
        data['constr_output'] = []
        data['constr_output_hl'] = []
        for constr in data['constrs']:
            T = parser.parse_type(thy, constr['type'])
            constrs.append((constr['name'], T, constr['args']))
            data['constr_output'].append(str_of_constr(thy, constr, unicode=True, highlight=False))
            data['constr_output_hl'].append(str_of_constr(thy, constr, unicode=True, highlight=True))
        exts = induct.add_induct_type(data['name'], data['args'], constrs)

        # Obtain type to be defined
        T = Type(data['name'], *(TVar(nm) for nm in data['args']))
        data['type_hl'] = printer.print_type(thy, T, unicode=True, highlight=True)
        data['edit_type'] = printer.print_type(thy, T, unicode=True, highlight=False)

        # Obtain items added by the extension
        data['ext_output'] = str_of_extension(thy, exts)

    elif data['ty'] == 'def.ind' or data['ty'] == 'def.pred':
        T = parser.parse_type(thy, data['type'])
        data['type_hl'] = printer.print_type(thy, T, unicode=True, highlight=True)
        rules = []
        data['edit_content'] = []
        data['edit_names'] = []
        for rule in data['rules']:
            ctxt = {'vars': {}, 'consts': {data['name']: T}}
            prop = parser.parse_term(thy, ctxt, rule['prop'])
            rules.append(prop)
            rule['prop_hl'] = printer.print_term(thy, prop, unicode=True, highlight=True)
            data['edit_content'].append(printer.print_term(thy, prop, unicode=True, highlight=False))
            if 'name' in rule:
                data['edit_names'].append(rule['name'])
        exts = induct.add_induct_def(data['name'], T, rules)

        # Obtain items added by the extension
        data['ext_output'] = str_of_extension(thy, exts)

        # Type of the item (for display)
        if data['ty'] == 'def.ind':
            data['type_name'] = 'fun'
        else:  # data['ty'] == 'def.pred':
            data['type_name'] = 'inductive'

    elif data['ty'] == 'def':
        T = parser.parse_type(thy, data['type'])
        data['type_hl'] = printer.print_type(thy, T, unicode=True, highlight=True)

        ctxt = {'vars': {}, 'consts': {data['name']: T}}
        prop = parser.parse_term(thy, ctxt, data['prop'])
        data['prop_hl'] = printer.print_term(thy, prop, unicode=True, highlight=True)
        data['edit_content'] = printer.print_term(thy, prop, unicode=True, highlight=False)
        data['type_name'] = 'definition'

    # Ignore other types of information.
    else:
        pass


def open_file(filename, mode):
    """Open json file for the current user and given filename, and mode."""
    return open('users/' + user_info['username'] + '/' + filename + '.json', mode, encoding='utf-8')


# Loads json file for the given user and file name.
@app.route('/api/load-json-file', methods=['POST'])
def load_json_file():
    filename = json.loads(request.get_data().decode("utf-8"))
    with open_file(filename, 'r') as f:
        f_data = json.load(f)
    if 'content' in f_data:
        thy = basic.load_imported_theory(f_data['imports'], user=user_info['username'])
        for data in f_data['content']:
            file_data_to_output(thy, data)
    else:
        f_data['content'] = []
    return jsonify(f_data)


@app.route('/api/save-file', methods=['POST'])
def save_file():
    """Save given data to file."""
    data = json.loads(request.get_data().decode("utf-8"))

    with open_file(data['name'], 'w+') as f:
        json.dump(data, f, indent=4, ensure_ascii=False, sort_keys=True)
    basic.clear_cache(user=user_info['username'])

    if data['name'] not in user_info['file_list']:
        user_info['file_list'].append(data['name'])
        user_info['file_list'].sort()

    return jsonify({})


@app.route('/api/search-method', methods=['POST'])
def search_method():
    """Match for applicable methods and their arguments."""
    data = json.loads(request.get_data().decode("utf-8"))
    if data:
        cell = cells[data['id']]
        thy = cell.thy
        fact_ids = data['fact_ids']
        goal_id = data['goal_id']
        search_res = cell.search_method(goal_id, fact_ids)
        for res in search_res:
            if '_goal' in res:
                res['_goal'] = [printer.print_term(thy, t, unicode=True) for t in res['_goal']]
            if '_fact' in res:
                res['_fact'] = [printer.print_term(thy, t, unicode=True) for t in res['_fact']]

        ctxt = cell.get_ctxt(goal_id)
        print_ctxt = dict((k, printer.print_type(thy, v, highlight=True))
                          for k, v in ctxt['vars'].items())
        return jsonify({
            'search_res': search_res,
            'ctxt': print_ctxt
        })

    return jsonify({})


def parse_var_decls(thy, var_decls):
    res = dict()
    for var_decl in var_decls:
        if var_decl:
            nm, T = parser.parse_var_decl(thy, var_decl)
            res[nm] = str(T)
    return res

@app.route('/api/check-modify', methods=['POST'])
def check_modify():
    """Check a modified item for validity."""
    data = json.loads(request.get_data().decode("utf-8"))
    error = {}
    item = data['content']
    thy = basic.load_theory('list')
    if item['ty'] == 'thm' or item['ty'] == 'thm.ax':
        item['vars'] = parse_var_decls(thy, item['vars'])

    if item['ty'] == 'type.ind':
        T = parser.parse_type(thy, item['data_name'])
        assert T.ty == HOLType.TYPE and all(argT.ty == HOLType.TVAR for argT in T.args), \
            "invalid input type."
        item['name'] = T.name
        item['args'] = [argT.name for argT in T.args]

        item['constrs'] = []
        for constr in item['data_content']:
            if constr:
                constr = parser.parse_ind_constr(thy, constr)
                constr['type'] = str(TFun(*(constr['type'] + [T])))
                item['constrs'].append(constr)

    if item['ty'] == 'def':
        pass

    if item['ty'] == 'def.ind':
        item['rules'] = []
        for prop in item['data_content']:
            item['rules'].append({'prop': prop})

    if item['ty'] == 'def.pred':
        item['rules'] = []
        assert len(item['names_list']) == len(item['data_content']), \
            "number of lines in input do not match"
        for name, prop in zip(item['names_list'], item['data_content']):
            item['rules'].append({'name': name, 'prop': prop})

    with open_file(data['file_name'], 'r') as f:
        f_data = json.load(f)
    try:
        thy = basic.load_imported_theory(f_data['imports'], user_info['username'])
        for d in data['prev_list']:
            parser.parse_extension(thy, d)
        file_data_to_output(thy, item)
    except Exception as e:
        exc_detailed = traceback2.format_exc()
        return jsonify({
            "failed": e.__class__.__name__,
            "message": str(e),
            "detail_content": exc_detailed
        })

    return jsonify({'content': item, 'error': error})


@app.route('/api/find-files', methods=['GET'])
def find_files():
    """Find list of files in user's directory."""
    fileDir = './users/' + user_info['username']
    files = []
    for f in os.listdir(fileDir):
        if f.endswith('.json'):
            files.append(f[:-5])

    user_info['file_list'] = sorted(files)
    return jsonify({'theories': user_info['file_list']})


@app.route('/api/remove-file', methods=['PUT'])
def remove_file():
    """Remove file with the given name."""
    filename = json.loads(request.get_data().decode('utf-8'))
    fileDir = './users/' + user_info['username'] + '/' + filename + '.json'
    user_info['file_list'].remove(filename)
    os.remove(fileDir)

    return jsonify({})

