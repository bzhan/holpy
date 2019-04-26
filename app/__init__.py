# Author: Chaozhu Xiang, Bohua Zhan

from copy import copy
import os, sqlite3, shutil
import json, sys, io, traceback2
from flask import Flask, request, render_template, redirect, session
from flask.json import jsonify
from kernel.type import HOLType
from kernel.term import Term
from kernel.thm import primitive_deriv
from kernel import extension
from syntax import parser, printer
from server.tactic import ProofState
from logic import basic
from logic import induct
from kernel.extension import AxType, AxConstant, Theorem
from syntax import settings

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

    # Current list of files
    'file_list': []
}

# templates
@app.route('/display_results.html', methods = ['GET'])
def display_results_template():
    return render_template('display_results.html')


@app.route('/edit_area.html', methods = ['GET'])
def edit_area_template():
    return render_template('edit_area.html')


# init page of HOL
@app.route('/', methods = ['GET', 'POST'])
def index():
    return render_template('login.html')


# sign out;
@app.route('/sign', methods=['get'])
def sign():
    user_info['is_signed_in'] = False
    return redirect('/')


# register page;
@app.route('/register', methods = ['GET'])
def re():
    return render_template('register.html')


# error for same name;
@app.route('/register_error', methods = ['GET'])
def regi_err():
    return render_template('register.html', info = 'User already exists')


@app.route('/login_error', methods = ['GET', 'POST'])
def login_err():
    return render_template('login.html', info = 'Incorrect username or password')


# register page for new user;
@app.route('/register_login', methods = ['POST'])
def register_login():
    username = request.form.get('name')
    password = request.form.get('password')
    for k in match_user():
        if username == k[1]:
            return redirect('register_error')
    if username and password:
        add_user(username, password)

    return redirect('/')


#load the page of HOL with username
@app.route('/load', methods = ['GET'])
def load():
    if not user_info['is_signed_in']:
        return redirect('/')

    return render_template('index.html', user = user_info['username'])


def add_user(username, password):
    DATABASE = os.getcwd() + '/users/user.db'

    conn = sqlite3.connect(DATABASE)
    cursor = conn.cursor()
    cursor.execute('insert into users(name, password) values("'+ username +'","'+ password +'");')
    cursor.close()
    conn.commit()
    conn.close()


# init database to create table users;
def init_user():
    DATABASE = os.getcwd() + '/users/user.db'

    conn = sqlite3.connect(DATABASE)
    cursor = conn.cursor()
    cursor.execute('create table users(id auto_increment,name CHAR(50) not null,password CHAR(50) not null);')
    cursor.close()
    conn.commit()
    conn.close()


# match the user-info in the database;
def match_user():
    DATABASE = os.getcwd() + '/users/user.db'

    conn = sqlite3.connect(DATABASE)
    cursor = conn.cursor()
    cursor.execute('select * from users;')
    results = cursor.fetchall()
    cursor.close()
    conn.commit()
    conn.close()

    return results


# login for user;
@app.route('/login', methods = ['GET', 'POST'])
def login():
    username = request.form.get('name')
    password = request.form.get('password')
    user_path = os.path.abspath('..') + '/holpy/users/' + username
    for k in match_user():
        if username == k[1] and password == str(k[2]):
            user_info['is_signed_in'] = True
            user_info['username'] = username
            user_list = os.listdir(os.path.abspath('..') + '/holpy/users')
            if username not in user_list:
                shutil.copytree(os.path.abspath('..') + '/holpy/library', user_path)

            return redirect('/load')

    return redirect('login_error')


@app.route('/api/init', methods=['POST'])
def init_component():
    data = json.loads(request.get_data().decode("utf-8"))
    if data:
        thy = basic.loadTheory(data['theory_name'], limit=('thm', data['thm_name']), user = user_info['username'])
        cell = ProofState.parse_init_state(thy, data)
        cells[data['id']] = cell
        return jsonify(cell.json_data())
    return jsonify({})


@app.route('/api/init-saved-proof', methods=['POST'])
def init_saved_proof():
    data = json.loads(request.get_data().decode("utf-8"))
    if data:
        try:
            thy = basic.loadTheory(data['theory_name'], limit=('thm', data['thm_name']), user = user_info['username'])
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


@app.route('/api/introduction', methods=['POST'])
def introduction():
    data = json.loads(request.get_data().decode("utf-8"))
    if data:
        cell = cells.get(data.get('id'))
        len_before = len(cell.prf.items)
        cell.introduction(data['line_id'], data.get('var_name'))
        line_diff = (len(cell.prf.items) - len_before) / 2
        result = cell.json_data()
        result["line-diff"] = line_diff
        return jsonify(result)
    return jsonify({})


@app.route('/api/apply-backward-step', methods=['POST'])
def apply_backward_step():
    data = json.loads(request.get_data().decode("utf-8"))
    if data:
        cell = cells.get(data['id'])
        theorem = data['theorem'].split(",")
        theorem, prevs = theorem[0], theorem[1:]
        if prevs:
            prevs = [prev.strip() for prev in prevs]
        cell.apply_backward_step(data['line_id'], theorem, prevs=prevs)
        return jsonify(cell.json_data())
    return jsonify({})


@app.route('/api/apply-induction', methods=['POST'])
def apply_induction():
    data = json.loads(request.get_data().decode("utf-8"))
    if data:
        cell = cells.get(data.get('id'))
        theorem, var = data.get('theorem').split(",")
        cell.apply_induction(data['line_id'], theorem, var)
        return jsonify(cell.json_data())
    return jsonify({})


@app.route('/api/rewrite-goal', methods=['POST'])
def rewrite_goal():
    data = json.loads(request.get_data().decode("utf-8"))
    if data:
        cell = cells.get(data.get('id'))
        theorem = data.get('theorem')
        cell.rewrite_goal(data['line_id'], theorem)
        return jsonify(cell.json_data())
    return jsonify({})


@app.route('/api/set-line', methods=['POST'])
def set_line():
    data = json.loads(request.get_data().decode("utf-8"))
    if data:
        cell = cells.get(data['id'])
        try:
            line_id = data['item']['id']
            item = parser.parse_proof_rule(cell.thy, cell.get_ctxt(line_id), data['item'])
            cell.set_line(item.id, item.rule, args=item.args, prevs=item.prevs, th=item.th)
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
        ctxt = parser.parse_vars(thy, data['vars'])
        prop = parser.parse_term(thy, ctxt, data['prop'])
        data['prop_hl'] = printer.print_term(thy, prop, unicode=True, highlight=True)

    elif data['ty'] == 'type.ind':
        constrs = []
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

        # Obtain types of arguments for each constructor
        data['argsT'] = dict()
        for i, constr in enumerate(data['constrs']):
            T = parser.parse_type(thy, constr['type'])
            argsT, _ = HOLType.strip_type(T)
            argsT = [printer.print_type(thy, a, unicode=True, highlight=True) for a in argsT]
            data['argsT'][str(i)] = argsT

    elif data['ty'] == 'def.ind' or data['ty'] == 'def.pred':
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

    elif data['ty'] == 'def':
        T = parser.parse_type(thy, data['type'])
        data['type_hl'] = printer.print_type(thy, T, unicode=True, highlight=True)

        ctxt = parser.parse_vars(thy, data['vars'])
        prop = parser.parse_term(thy, ctxt, data['prop'])
        data['prop_hl'] = printer.print_term(thy, prop, unicode=True, highlight=True)

    # Ignore other types of information.
    else:
        pass


@app.route('/api/load-json-file', methods=['POST'])
def load_json_file():
    """Loads json file for the given user and file name."""
    file_name = json.loads(request.get_data().decode("utf-8"))
    with open('users/' + user_info['username'] + '/' + file_name + '.json', 'r', encoding='utf-8') as f:
        f_data = json.load(f)
    if 'content' in f_data:
        thy = basic.loadImportedTheory(f_data['imports'], user=user_info['username'])
        for data in f_data['content']:
            file_data_to_output(thy, data)
    else:
        f_data['content'] = []
    return jsonify({'data': f_data})


# add-button to add data-info;
@app.route('/api/add-info', methods=['POST'])
def json_add_info():
    data = json.loads(request.get_data().decode("utf-8"))

    thy = basic.loadTheory(data['theory_name'], user=user_info['username'])
    item = data['item']
    file_data_to_output(thy, item)

    return jsonify({'data': item})


# save the related data to json file;
@app.route('/api/save_file', methods=['POST'])
def save_file():
    json_data = json.loads(request.get_data().decode("utf-8"))

    data = json_data['data']
    file_name = json_data['name']

    with open('users/' + user_info['username'] + '/' + file_name + '.json', 'w+', encoding='utf-8') as f:
        json.dump(data, f, indent=4, ensure_ascii=False, sort_keys=True)

    return jsonify({})


# match the thms for backward or rewrite;
@app.route('/api/match_thm', methods=['POST'])
def match_thm():
    dict = {}
    data = json.loads(request.get_data().decode("utf-8"))
    thy = basic.loadTheory(data['theory_name'], user=user_info['username'])
    if data:
        cell = cells.get(data.get('id'))
        target_id = data.get('target_id')
        ctxt = cell.get_ctxt(target_id)
        settings.settings_stack[0]['highlight'] = True
        for k, v in ctxt.items():
            dict[k] = printer.print_type(thy, v)
        conclusion_id = data.get('conclusion_id')
        if not conclusion_id:
            conclusion_id = None
        settings.settings_stack[0]['highlight'] = False
        ths_rewrite = cell.rewrite_goal_thms(target_id)
        ths_abs = cell.apply_backward_step_thms(target_id, prevs=conclusion_id)
        ths_afs = cell.apply_forward_step_thms(target_id, prevs=conclusion_id)
        if (ths_abs or ths_rewrite) or ths_afs:
            return jsonify({
                'ths_abs': ths_abs,
                'ths_afs': ths_afs,
                'ths_rewrite': ths_rewrite,
                'ctxt': dict
            })
        else:
            return jsonify({'ctxt': dict})


# save the edited data to left-json for updating;
@app.route('/api/save_modify', methods=['POST'])
def save_modify():
    data = json.loads(request.get_data().decode("utf-8"))
    error = {}
    with open('users/' + user_info['username'] + '/' + data['file-name'] + '.json', 'r', encoding='utf-8') as f:
        f_data = json.load(f)
    try:
        thy = basic.loadImportedTheory(f_data['imports'], user_info['username'])
        for d in data['prev-list']:
            parser.parse_extension(thy, d)
        file_data_to_output(thy, data)
    except Exception as e:
        exc_detailed = traceback2.format_exc()
        error = {
            "failed": e.__class__.__name__,
            "message": str(e),
            "detail-content": exc_detailed
        }

    return jsonify({'data': data, 'error': error})


# save the edited data to the json file;
@app.route('/api/editor_file', methods=['PUT'])
def save_edit():
    data = json.loads(request.get_data().decode("utf-8"))
    file_name = data['name']
    username = user_info['username']
    with open('users/' + username + '/' + file_name + '.json', 'r', encoding='utf-8') as file:
        f_data = json.load(file)
    f_data['content'] = data['data']
    j = open('users/' + username + '/' + file_name + '.json', 'w', encoding='utf-8')
    json.dump(f_data, j, indent=4, ensure_ascii=False, sort_keys=True)
    j.close()

    return jsonify({})


# create new json file;
@app.route('/api/add-new', methods=['PUT'])
def add_new():
    data = json.loads(request.get_data().decode("utf-8"))
    file_name = data['name']
    username = user_info['username']
    if file_name in user_info['file_list']:
        with open('users/' + username + '/' + file_name + '.json', 'r', encoding='utf-8') as f:
            file_data = json.load(f)
            for key in data.keys():
                file_data[key] = data[key]
            f.close()
        with open('users/' + username + '/' + file_name + '.json', 'w', encoding='utf-8') as f:
            json.dump(file_data, f, ensure_ascii=False, indent=4)
    else:
        with open('users/' + username + '/' + file_name + '.json', 'w', encoding='utf-8') as f:
            json.dump(data, f, ensure_ascii=False, indent=4)
            f.close()

    return jsonify({})


# locate the files in the library;
@app.route('/api/find_files', methods=['GET'])
def find_files():
    fileDir = os.path.abspath('..') + '/holpy/users/' + user_info['username']
    for i in os.walk(fileDir):
        files = [x[:-5] for x in i[2]]
        if files:
            user_info['file_list'] = sorted(files)
            return jsonify({'theories': sorted(files)})

    return jsonify({})


# get the metadata of the json-file;
@app.route('/api/edit_jsonFile', methods=['POST'])
def edit_jsonFile():
    content = {}
    file_name = json.loads(request.get_data().decode('utf-8'))
    username = user_info['username']
    with open('users/' + username + '/' + file_name + '.json', 'r', encoding='utf-8') as f:
        file_data = json.load(f)
    content['description'] = file_data['description']
    content['imports'] = file_data['imports']
    content['name'] = file_name

    return jsonify(content)


# save the file_list
@app.route('/api/save_file_list', methods=['PUT'])
def save_file_list():
    file_name = json.loads(request.get_data().decode('utf-8'))
    fileDir = os.path.abspath('..') + '/holpy/users/' + user_info['username'] + '/' + file_name + '.json'
    user_info['file_list'].remove(file_name)
    os.remove(fileDir)

    return jsonify({})


@app.route('/api/apply-forward-step', methods=['POST'])
def apply_forward_step():
    data = json.loads(request.get_data().decode("utf-8"))
    if data:
        cell = cells.get(data['id'])
        theorem = data['theorem'].split(",")
        theorem, prevs = theorem[0], theorem[1:]
        if prevs:
            prevs = [prev.strip() for prev in prevs]
        cell.apply_forward_step(data['line_id'], theorem, prevs=prevs)
        return jsonify(cell.json_data())
    return jsonify({})
