# Author: Chaozhu Xiang, Bohua Zhan

from copy import copy
import os, sqlite3, shutil
import json, sys, io, traceback2
from flask import Flask, request, render_template, redirect, session
from flask.json import jsonify
from kernel.type import HOLType, TVar, Type
from syntax import parser, printer
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


def print_extension(thy, ext):
    """Print given extension."""
    if isinstance(ext, AxType):
        return "Type " + ext.name
    elif isinstance(ext, AxConstant):
        return "Constant " + ext.name + " :: " + printer.print_type(thy, ext.T, unicode=True)
    elif isinstance(ext, Theorem):
        return "Theorem " + ext.name + ": " + printer.print_term(thy, ext.th.prop, unicode=True)


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
        temp_list = []
        for k, v in data['vars'].items():
            temp_list.append(k + ' :: ' + v)
        ctxt = parser.parse_vars(thy, data['vars'])
        prop = parser.parse_term(thy, ctxt, data['prop'])
        data['prop_hl'] = printer.print_term(thy, prop, unicode=True, highlight=True)
        data['vars_lines'] = temp_list

    elif data['ty'] == 'type.ind':
        constrs = []
        data_content = ''
        for constr in data['constrs']:
            T = parser.parse_type(thy, constr['type'])
            constrs.append((constr['name'], T, constr['args']))
        exts = induct.add_induct_type(data['name'], data['args'], constrs)

        # Obtain items added by the extension
        ext_output = []
        for ext in exts.data:
            s = print_extension(thy, ext)
            if s:
                ext_output.append(s)
        data['ext'] = ext_output

        # Obtain type to be defined
        T = Type(data['name'], *(TVar(nm) for nm in data['args']))
        data['type_hl'] = printer.print_type(thy, T, unicode=True, highlight=True)

        # Obtain types of arguments for each constructor
        data['argsT'] = dict()
        for i, constr in enumerate(data['constrs']):
            str_temp_var = ''
            T = parser.parse_type(thy, constr['type'])
            argsT, _ = HOLType.strip_type(T)
            argsT = [printer.print_type(thy, argT, unicode=True, highlight=True) for argT in argsT]
            data['argsT'][str(i)] = argsT
            for j, a in enumerate(constr['args']):
                str_temp_term = ''
                for m, t in enumerate(data['argsT'][str(i)][j]):
                    str_temp_term += t[0]
                str_temp_var += ' (' + a + ' :: ' + str_temp_term + ')'
            data_content += '\n' + constr['name'] + str_temp_var
        data['type_content'] = data_content

    elif data['ty'] == 'def.ind' or data['ty'] == 'def.pred':
        container = [[], [], [], '', '', '']
        data_content_list, data_rule_names, data_vars_list, data_new_content, data_rule_name, data_vars_str = container
        T = parser.parse_type(thy, data['type'])
        data['type_hl'] = printer.print_type(thy, T, unicode=True, highlight=True)
        rules = []
        for rule in data['rules']:
            ctxt = parser.parse_vars(thy, rule['vars'])
            prop = parser.parse_term(thy, ctxt, rule['prop'])
            rule['prop_hl'] = printer.print_term(thy, prop, unicode=True, highlight=True)
            rules.append(prop)
        exts = induct.add_induct_def(data['name'], T, rules)

        # Obtain items added by the extension
        ext_output = []
        for ext in exts.data:
            s = print_extension(thy, ext)
            if s:
                ext_output.append(s)
        data['ext'] = ext_output

        if data['ty'] == 'def.ind':
            type_name = 'fun'
        if data['ty'] == 'def.pred':
            type_name = 'inductive'
        data['ext_output'] = '\n'.join(ext_output)
        data['type_name'] = type_name

        for k, r in enumerate(data['rules']):
            vars_str = ''
            data_con = ''
            for m, v in enumerate(r['vars']):
                vars_str += str(m) + '::' + v + '   '
            data_vars_list.append(vars_str)
            for p in r['prop_hl']:
                data_con += p[0]
            data_content_list.append(data_con)
            if 'name' in r:
                data_rule_names.append(r['name'])
        for n, dv in enumerate(data_vars_list):
            data_vars_str += ' ' + dv + '\n'
        for j,dc in enumerate(data_content_list):
            data_new_content += ' ' + dc + '\n'
            data_rule_name +=  ' ' + dc + '\n'
        data['data_new_content'] = data_new_content
        data['data_rule_name'] = data_rule_name
        data['data_vars_str'] = data_vars_str

    elif data['ty'] == 'def':
        i = 0
        vars = ''
        data_new_content = ''
        data_content_list = []
        data_content_list.append(data['prop'])
        for j,dc in enumerate(data_content_list):
            data_new_content += str(j) + ': ' + dc + '\n'
        for j, v in enumerate(data['vars']):
            vars += str(i) + ': ' + str(j) + '::' + v + '\n'
            i += 1
        data['item_vars'] = vars
        T = parser.parse_type(thy, data['type'])
        data['type_name'] = 'definition'
        data['data_new_content'] = data_new_content
        data['type_hl'] = printer.print_type(thy, T, unicode=True, highlight=True)

        ctxt = parser.parse_vars(thy, data['vars'])
        prop = parser.parse_term(thy, ctxt, data['prop'])
        data['prop_hl'] = printer.print_term(thy, prop, unicode=True, highlight=True)

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
                          for k, v in ctxt.items())
        return jsonify({
            'search_res': search_res,
            'ctxt': print_ctxt
        })

    return jsonify({})


@app.route('/api/check-modify', methods=['POST'])
def check_modify():
    """Check a modified item for validity."""
    data = json.loads(request.get_data().decode("utf-8"))
    error = {}
    item = data['content']
    thy = basic.load_theory('list')
    vars = {}
    if item['ty'] == 'thm' or item['ty'] == 'thm.ax':
        if item['vars']:
            for v in item['vars'].split('\n'):
                (nm, T) = parser.parse_thm_vars(thy, v)
                if nm:
                    vars[nm.strip()] = T.strip()
        item['vars'] = vars
    if item['ty'] == 'type.ind':
        constrs, temp_list = [], []
        if len(item['data_name'].split(' ')) > 1:
            temp_list.append(item['data_name'].split(' ')[0][1:])
            item['name'] = item['data_name'].split(' ')[1]
        else:
            item['name'] = item['data_name']
        item['args'] = temp_list
        apd = Type(item['name'], *(TVar(nm) for nm in item['args']))
        for c in item['data_content'].split('\n'):
            constr = parser.parse_type_ind(thy, c)
            type_list = constr['type'] + [apd]
            constr['type'] = str(TFun(type_list))
            constrs.append(constr)
        item['constrs'] = constrs
    # if item['ty'] == 'def.ind' or item['ty'] == 'def' or item['ty'] == 'def.pred':
    #     item['name'] = parser.parse_thm_vars(thy, item['data_name'])[0]
    #     item['type'] = parser.parse_thm_vars(thy, item['data_name'])[1]


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

