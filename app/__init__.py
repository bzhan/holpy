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
from logic.context import Context
from logic.basic import user_dir, user_file
from imperative import parser2
from imperative import imp
from prover import z3wrapper
from server.server import ProofState
from server import monitor
from server import items
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

    print("Parse: %f" % (time.perf_counter() - start_time))

    if data['profile']:
        p = Stats(pr)
        p.strip_dirs()
        p.sort_stats('cumtime')
        p.print_stats()

    return jsonify({
        'state': json_state,
        'history': history
    })


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
                "err_type": e.__class__.__name__,
                "err_str": str(e),
                "trace": traceback2.format_exc()
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

@app.route("/api/integral-elim-abs", methods=["POST"])
def integral_elim_abs():
    data = json.loads(request.get_data().decode('utf-8'))
    rule = integral.rules.OnSubterm(integral.rules.ElimAbs())
    problem = integral.parser.parse_expr(data['problem'])
    new_problem = rule.eval(problem)
    return jsonify({
        'text': str(new_problem),
        'latex': integral.latex.convert_expr(new_problem),
        'reason': "Eliminate abs"
    })

@app.route("/api/integral-separate-integrals", methods=['POST'])
def integral_separate_integrals():
    data = json.loads(request.get_data().decode('utf-8'))
    problem = integral.parser.parse_expr(data['problem'])
    integrals = problem.separate_integral()
    n = []
    for i in integrals:
        n.append({
            "text": str(i),
            "body": str(i.body),
            "latex": integral.latex.convert_expr(i)
        })
    return json.dumps(n)

@app.route("/api/integral-compose-integral", methods=['POST'])
def integral_compose_integral():
    data = json.loads(request.get_data().decode('utf-8'))
    new_integral = []
    reason = ""
    for d in data['problem']:
        new_integral.append(integral.parser.parse_expr(str(d['text'])))
        if '_latex_reason' in d:
            reason += d['_latex_reason']
            reason += "."
        elif 'reason' in d:
            reason += d['reason']
            reason += "."
    curr = integral.parser.parse_expr(data['cur_calc'])
    new_expr = curr
    old_integral = curr.separate_integral()
    for i in range(len(old_integral)):
        new_expr = new_expr.replace_trig(old_integral[i], new_integral[i])
    return jsonify({
        'text': str(new_expr),
        'latex': integral.latex.convert_expr(new_expr),
        '_latex_reason': reason
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
        #need to do more
        possible_form = list(integral.expr.trig_transform(integral.expr.trig_identity[0]))
        n = []
        for p in range(len(possible_new_problem)):
            n.append({ 
                'text': str(possible_new_problem[p][0]),
                'latex': integral.latex.convert_expr(possible_new_problem[p][0]),
                '_latex_reason': "Trig identities: \(%s = %s\\); Method : %s"
                % (integral.latex.convert_expr(integral.expr.trig_identity[0]),
                integral.latex.convert_expr(integral.parser.parse_expr(str(possible_form[p][0]).replace("**", "^"))),
                str(possible_new_problem[p][1]))
            })
        return json.dumps(n)
    else:
        return jsonify({
            'text': str(problem),
            'latex': integral.latex.convert_expr(problem),
            'reason': "Rewrite is invalid."
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
            integral.latex.convert_expr(integral.parser.parse_expr(data['var_name'])), integral.latex.convert_expr(expr)
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
    old_expr = integral.parser.parse_expr(data['problem']).body
    new_expr = integral.parser.parse_expr(data['new_expr'])
    rule = integral.rules.Equation(old_expr, new_expr)
    problem = integral.parser.parse_expr(data['problem'])
    new_problem = rule.eval(problem)
    if new_problem != problem and new_problem != old_expr:
        return jsonify({
            'text': str(new_problem),
            'latex': integral.latex.convert_expr(new_problem),
            '_latex_reason': "Equation substitution successful, \\( %s\\) == \\(%s\\)" % (
                integral.latex.convert_expr(old_expr), integral.latex.convert_expr(new_expr)
            ),
            'flag': "success"
        })
    else:
        return jsonify({
            'flag': "fail",
            "_latex_reason": "\\(%s != %s\\)" % 
            (integral.latex.convert_expr(old_expr), integral.latex.convert_expr(new_expr))
        })

@app.route("/api/integral-polynomial-division", methods=['POST'])
def integral_polynomial_division():
    data = json.loads(request.get_data().decode('utf-8'))
    rule = integral.rules.OnSubterm(integral.rules.PolynomialDivision())
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
