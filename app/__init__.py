# Author: Chaozhu Xiang, Bohua Zhan

import json

from flask import Flask, request, render_template
from flask.json import jsonify
from kernel.term import Term
from kernel.thm import primitive_deriv
from syntax import parser, printer
from server.tactic import ProofState
from logic.basic import BasicTheory
from kernel.type import HOLType
from file_function import save_file, save_proof

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
        cell = ProofState.parse_init_state(data)
        cells[data['id']] = cell
        return jsonify(cell.json_data())
    return jsonify({})


@app.route('/api/init-saved-proof', methods=['POST'])
def init_saved_proof():
    data = json.loads(request.get_data().decode("utf-8"))
    if data:
        try:
            cell = ProofState.parse_proof(data)
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
        cell = cells.get(data.get('id'))
        try:
            item = parser.parse_proof_rule(cell.thy, cell.get_ctxt(), data['line'])
            cell.set_line(item.id, item.rule, args=item.args, prevs=item.prevs, th=item.th)
            return jsonify(cell.json_data())
        except Exception as e:
            error = {
                "failed": e.__class__.__name__,
                "message": str(e)
            }
        return jsonify(error)


@app.route('/api/json', methods=['POST'])
def json_parse():
    thy = BasicTheory
    output_data = []
    f_data = json.loads(request.get_data().decode("utf-8"))
    data = []
    if type(f_data) == str:
        with open('library/' + f_data + '.json', 'r', encoding='utf-8') as f:
            data = json.load(f)
            f.close()
    else:
        data = f_data['data']
        name = f_data['name']
        save_file(name, data)

    if data:
        for d in data:
            vars = []
            output = {}
            proof = dict()
            prop = parser.parse_extension(thy, d)
            if d['ty'] == 'def.ax':
                output['name'] = d['name']
                output['prop'] = str(prop)
                output['ty'] = d['ty']
                output_data.append(output)

            if d['ty'] == 'thm':
                output['name'] = d['name']
                output['vars'] = d['vars']
                output['prop_raw'] = printer.print_term(thy, prop, print_abs_type=True)
                output['prop'] = printer.print_term(thy, prop, unicode=True, highlight=True)
                output['ty'] = d['ty']
                if 'instructions' in d:
                    output['instructions'] = d['instructions']
                if 'proof' in d:
                    output['proof'] = d['proof']
                    output['status'] = 'yellow' if d['num_gaps'] > 0 else 'green'
                else:
                    output['status'] = 'red'

                output_data.append(output)

            if d['ty'] == 'type.ind':
                output['name'] = d['name']
                constrs = d['constrs']
                temp = HOLType.strip_type(prop[1])
                output['constrs'] = constrs
                output['prop'] = [str(tl) for tl in temp[0]]
                output['ty'] = d['ty']
                output_data.append(output)

            if d['ty'] == 'def.ind':
                output['name'] = d['name']
                output['prop'] = [printer.print_term(thy, t, highlight=True, unicode=True) for t in prop]
                output['type'] = d['type']
                output['ty'] = d['ty']
                output_data.append(output)

    return jsonify({'data': output_data})


@app.route('/api/root_file', methods=['GET'])
def get_root():
    json_data = {}
    with open('library/root.json', 'r+', encoding='utf-8') as f:
        json_data = json.load(f)
        f.close()
    return jsonify(json_data)


@app.route('/api/save_proof', methods=['PUT'])
def save_proof_file():
    data = json.loads(request.get_data().decode("utf-8"))
    save_proof(data['name'], data['id'], data['proof'], data['num_gaps'])

    return ''


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
