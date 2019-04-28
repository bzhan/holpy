# Author: Chaozhu Xiang, Bohua Zhan

from copy import copy
import os, sqlite3, shutil
import json, sys, io, traceback2
from flask import Flask, request, render_template, redirect, session
from flask.json import jsonify
from kernel.type import HOLType
from syntax import parser, printer
from server.tactic import ProofState
from logic import basic
from logic import induct
from kernel.extension import AxType, AxConstant, Theorem

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


@app.route('/api/init-empty-proof', methods=['POST'])
def init_empty_proof():
    """Initialize empty proof."""
    data = json.loads(request.get_data().decode("utf-8"))
    if data:
        thy = basic.loadTheory(data['theory_name'], limit=('thm', data['thm_name']), user=user_info['username'])
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
            thy = basic.loadTheory(data['theory_name'], limit=('thm', data['thm_name']), user=user_info['username'])
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
        cell = cells[data['id']]
        cell.introduction(data['line_id'], data['var_name'])
        return jsonify(cell.json_data())
    return jsonify({})


@app.route('/api/apply-backward-step', methods=['POST'])
def apply_backward_step():
    data = json.loads(request.get_data().decode("utf-8"))
    if data:
        cell = cells[data['id']]
        theorem = data['theorem'].split(",")
        theorem, prevs = theorem[0], theorem[1:]
        prevs = [prev.strip() for prev in prevs]
        cell.apply_backward_step(data['line_id'], theorem, prevs=prevs)
        return jsonify(cell.json_data())
    return jsonify({})


@app.route('/api/apply-forward-step', methods=['POST'])
def apply_forward_step():
    data = json.loads(request.get_data().decode("utf-8"))
    if data:
        cell = cells[data['id']]
        theorem = data['theorem'].split(",")
        theorem, prevs = theorem[0], theorem[1:]
        prevs = [prev.strip() for prev in prevs]
        cell.apply_forward_step(data['line_id'], theorem, prevs=prevs)
        return jsonify(cell.json_data())
    return jsonify({})


@app.route('/api/apply-induction', methods=['POST'])
def apply_induction():
    data = json.loads(request.get_data().decode("utf-8"))
    if data:
        cell = cells[data['id']]
        theorem, var = data['theorem'].split(",")
        cell.apply_induction(data['line_id'], theorem, var)
        return jsonify(cell.json_data())
    return jsonify({})


@app.route('/api/rewrite-goal', methods=['POST'])
def rewrite_goal():
    data = json.loads(request.get_data().decode("utf-8"))
    if data:
        cell = cells[data['id']]
        theorem = data['theorem']
        cell.rewrite_goal(data['line_id'], theorem)
        return jsonify(cell.json_data())
    return jsonify({})


@app.route('/api/set-line', methods=['POST'])
def set_line():
    data = json.loads(request.get_data().decode("utf-8"))
    if data:
        cell = cells[data['id']]
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
        thy = basic.loadImportedTheory(f_data['imports'], user=user_info['username'])
        for data in f_data['content']:
            file_data_to_output(thy, data)
    else:
        f_data['content'] = []
    return jsonify({'data': f_data})


@app.route('/api/save-file', methods=['POST'])
def save_file():
    """Save given data to file."""
    data = json.loads(request.get_data().decode("utf-8"))

    with open_file(data['name'], 'w+') as f:
        json.dump(data, f, indent=4, ensure_ascii=False, sort_keys=True)

    return jsonify({})


@app.route('/api/match-thm', methods=['POST'])
def match_thm():
    """Match for hints to backward, forward, and rewrite steps."""
    data = json.loads(request.get_data().decode("utf-8"))
    thy = basic.loadTheory(data['theory_name'], user=user_info['username'])
    if data:
        cell = cells[data['id']]
        facts_id = data['facts_id']
        goal_id = data['goal_id']
        backward_ths = cell.apply_backward_step_thms(goal_id, prevs=facts_id)
        forward_ths = cell.apply_forward_step_thms(goal_id, prevs=facts_id)
        rewrite_ths = cell.rewrite_goal_thms(goal_id)
        ctxt = cell.get_ctxt(goal_id)
        print_ctxt = dict((k, printer.print_type(thy, v, highlight=True))
                          for k, v in ctxt.items())
        return jsonify({
            'backward': backward_ths,
            'forward': forward_ths,
            'rewrite': rewrite_ths,
            'ctxt': print_ctxt
        })


@app.route('/api/check-modify', methods=['POST'])
def check_modify():
    """Check a modified item for validity."""
    data = json.loads(request.get_data().decode("utf-8"))
    error = {}
    with open_file(data['file_name'], 'r') as f:
        f_data = json.load(f)
    try:
        thy = basic.loadImportedTheory(f_data['imports'], user_info['username'])
        for d in data['prev_list']:
            parser.parse_extension(thy, d)
        file_data_to_output(thy, data['content'])
    except Exception as e:
        exc_detailed = traceback2.format_exc()
        return jsonify({
            "failed": e.__class__.__name__,
            "message": str(e),
            "detail_content": exc_detailed
        })

    return jsonify({'content': data['content'], 'error': error})


# save the edited data to the json file;
@app.route('/api/editor_file', methods=['PUT'])
def save_edit():
    data = json.loads(request.get_data().decode("utf-8"))
    filename = data['name']
    with open_file(filename, 'r') as f:
        f_data = json.load(f)
    f_data['content'] = data['data']
    with open_file(filename, 'w') as j:
        json.dump(f_data, j, indent=4, ensure_ascii=False, sort_keys=True)

    return jsonify({})


# Save metadata for an existing or new json file.
@app.route('/api/save-metadata', methods=['PUT'])
def save_metadata():
    data = json.loads(request.get_data().decode("utf-8"))
    file_name = data['name']
    if file_name in user_info['file_list']:
        # Existing file
        with open_file(file_name, 'r') as f:
            file_data = json.load(f)
            for key in data.keys():
                file_data[key] = data[key]
        with open_file(file_name, 'w') as f:
            json.dump(file_data, f, ensure_ascii=False, indent=4)
    else:
        # New file
        with open_file(file_name, 'w') as f:
            json.dump(data, f, ensure_ascii=False, indent=4)

    return jsonify({})


@app.route('/api/find_files', methods=['GET'])
def find_files():
    """Find list of files in user's directory."""
    fileDir = './users/' + user_info['username']
    files = []
    for f in os.listdir(fileDir):
        if f.endswith('.json'):
            files.append(f[:-5])

    user_info['file_list'] = sorted(files)
    return jsonify({'theories': user_info['file_list']})


@app.route('/api/get-metadata', methods=['POST'])
def get_metadata():
    """Get metadata for the json file."""
    content = {}
    filename = json.loads(request.get_data().decode('utf-8'))
    username = user_info['username']
    with open_file(filename, 'r') as f:
        file_data = json.load(f)
    content['description'] = file_data['description']
    content['imports'] = file_data['imports']
    content['name'] = filename

    return jsonify(content)


@app.route('/api/remove-file', methods=['PUT'])
def remove_file():
    """Remove file with the given name."""
    filename = json.loads(request.get_data().decode('utf-8'))
    fileDir = './users/' + user_info['username'] + '/' + filename + '.json'
    user_info['file_list'].remove(filename)
    os.remove(fileDir)

    return jsonify({})
