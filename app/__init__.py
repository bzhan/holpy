# Author: Chaozhu Xiang, Bohua Zhan

from copy import copy
import json,sys,io
sys.stdout = io.TextIOWrapper(sys.stdout.buffer,encoding='utf-8')

from flask import Flask, request, render_template
from flask.json import jsonify
from kernel.type import HOLType
from kernel.term import Term
from kernel.thm import primitive_deriv
from kernel import extension
from syntax import parser, printer
from server.tactic import ProofState
from logic import basic


app = Flask(__name__, static_url_path='/static')
app.secret_key = b'_5#y2L"F4Q8z\n\xec]/'

app.config.from_object('config')

# Dictionary from id to ProofState
cells = dict()

@app.route('/')
def index():
    return render_template('index.html')


@app.route('/api/init', methods=['POST'])
def init_component():
    data = json.loads(request.get_data().decode("utf-8"))
    if data:
        thy = basic.loadTheory(data['theory_name'], limit=('thm', data['thm_name']))
        cell = ProofState.parse_init_state(thy, data)
        cells[data['id']] = cell
        return jsonify(cell.json_data())
    return jsonify({})


@app.route('/api/init-saved-proof', methods=['POST'])
def init_saved_proof():
    data = json.loads(request.get_data().decode("utf-8"))
    if data:
        try:
            thy = basic.loadTheory(data['theory_name'], limit=('thm', data['thm_name']))
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


def file_data_to_output(thy, data):
    """Convert an item in the theory in json format in the file to
    json format sent to the web client. Modifies data in-place.
    Also modifies thy in parsing the item.

    """
    parser.parse_extension(thy, data)
    if data['ty'] == 'def.ax':
        T = parser.parse_type(thy, data['type'])
        data['type_hl'] = printer.print_type(thy, T, unicode=True, highlight=True)

    elif data['ty'] == 'thm':
        ctxt = parser.parse_vars(thy, data['vars'])
        prop = parser.parse_term(thy, ctxt, data['prop'])
        data['prop_hl'] = printer.print_term(thy, prop, unicode=True, highlight=True)

    elif data['ty'] == 'type.ind':
        type_dic = dict()
        for i, constr in enumerate(data['constrs']):
            type_list = []
            T = parser.parse_type(thy, constr['type'])
            argsT, res = HOLType.strip_type(T)
            for a in argsT:
                type_list.append(printer.print_type(thy, a, unicode=True, highlight=True))
            type_dic[str(i)] = type_list
            type_dic['concl'] = printer.print_type(thy, res, unicode=True, highlight=True)
        data['argsT'] = type_dic

    elif data['ty'] == 'def.ind':
        T = parser.parse_type(thy, data['type'])
        data['type_hl'] = printer.print_type(thy, T, unicode=True, highlight=True)
        for rule in data['rules']:
            ctxt = parser.parse_vars(thy, rule['vars'])
            prop = parser.parse_term(thy, ctxt, rule['prop'])
            rule['prop_hl'] = printer.print_term(thy, prop, unicode=True, highlight=True)
    # Ignore other types of information.
    else:
        pass


@app.route('/api/json', methods=['POST'])
def json_parse():
    file_name = json.loads(request.get_data().decode("utf-8"))
    with open('library/'+ file_name +'.json', 'r', encoding='utf-8') as f:
        f_data = json.load(f)
    thy = basic.loadImportedTheory(f_data)
    for data in f_data['content']:
        file_data_to_output(thy, data)
    return jsonify({'data': f_data})


@app.route('/api/add-info', methods=['POST'])
def json_add_info():
    data = json.loads(request.get_data().decode("utf-8"))

    thy = basic.loadTheory(data['theory_name'])
    item = data['item']
    file_data_to_output(thy, item)
    return jsonify({'data': item})


@app.route('/api/save_file', methods=['POST'])
def save_file():
    json_data = json.loads(request.get_data().decode("utf-8"))

    data = json_data['data']
    name = json_data['name']

    with open('library/' + name + '.json', 'w+', encoding='utf-8') as f:
        json.dump(data, f, indent=4, ensure_ascii=False, sort_keys=True)

    return jsonify({})


@app.route('/api/root_file', methods=['GET'])
def get_root():
    json_data = {}
    with open('library/root.json', 'r+', encoding='utf-8') as f:
        json_data = json.load(f)
        f.close()
    return jsonify(json_data)


@app.route('/api/match_thm', methods=['POST'])
def match_thm():
    data = json.loads(request.get_data().decode("utf-8"))
    if data:
        cell = cells.get(data.get('id'))
        target_id = data.get('target_id')
        conclusion_id = data.get('conclusion_id')
        if not conclusion_id:
            conclusion_id = None
        ths = cell.apply_backward_step_thms(target_id, prevs=conclusion_id)
        if ths:
            return jsonify({'ths': [item[0] for item in ths]})
        else:
            return jsonify({})


@app.route('/api/save_modify', methods=['POST'])
def save_modify():
    data = json.loads(request.get_data().decode("utf-8"))
    with open('library/'+ data['file-name'] +'.json', 'r', encoding='utf-8') as f:
        f_data = json.load(f)
    thy = basic.loadImportedTheory(f_data)
    for d in data['result-list']:
        parser.parse_extension(thy, d)
    file_data_to_output(thy, data)

    return jsonify({'data' : data})


@app.route('/api/editor_file', methods=['PUT'])
def save_edit():
    data = json.loads(request.get_data().decode("utf-8"))
    file_name = ''
    for d in data:
        file_name = d['file-name']
        with open('library/' + file_name + '.json', 'r', encoding='utf-8') as f:
            f_data = json.load(f)
        for f in f_data['content']:
            if f['name'] == d['name']:
                for k,v in d.items():
                    if k in f.keys():
                        f[k] = v
    with open('library/'+ file_name+ '.json', 'w', encoding='utf-8') as file:
        json.dump(f_data, file, ensure_ascii=False)

    return jsonify({})





