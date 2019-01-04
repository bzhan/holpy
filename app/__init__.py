# Author: Chaozhu Xiang, Bohua Zhan

import json

from flask import Flask, request, render_template
from flask.json import jsonify
from kernel.thm import primitive_deriv
from syntax import parser
from server.tactic import ProofState
from logic.basic import BasicTheory
from syntax.parser import *
from syntax.printer import *
from kernel.type import HOLType

app = Flask(__name__, static_url_path='/static')
app.secret_key = b'_5#y2L"F4Q8z\n\xec]/'

app.config.from_object('config')

# Dictionary from id to ProofState
cells = dict()


def get_result_from_cell(cell):
    return {
        "proof": cell.print_proof(),
        "report": cell.rpt.json_data()
    }


@app.route('/')
def index():
    return render_template('index.html')


@app.route('/api/check-proof', methods=['POST'])
def check_proof():
    data = json.loads(request.get_data().decode("utf-8"))
    if not data:
        return jsonify({})

    cell = cells[data.get('id')]
    proof = data.get('proof')
    try:
        cell.parse_proof(proof)
        cell.check_proof()
        return jsonify(get_result_from_cell(cell))
    except Exception as e:
        error = {
            "failed": e.__class__.__name__,
            "message": str(e)
        }
        return jsonify(error)


@app.route('/api/init', methods=['POST'])
def init_component():
    data = json.loads(request.get_data().decode("utf-8"))
    if data.get('event') == 'init_theorem':
        macro_dict = {0: 'NONE', 1: 'TERM', 2: 'TYINST', 3: 'INST', 4: 'STRING'}
        result = {}
        for key, value in primitive_deriv.items():
            result[key] = macro_dict[value[1]]
        return jsonify(result)
    elif data.get('event') == 'init_theorem_abs':
        pass
    elif data.get('event') == 'init_cell':
        cell = ProofState.parse_init_state(data)
        cells[data.get('id')] = cell
        return jsonify(get_result_from_cell(cell))
    return jsonify({})


@app.route('/api/add-line-after', methods=['POST'])
def add_line_after():
    data = json.loads(request.get_data().decode("utf-8"))
    if data:
        cell = cells[data.get('id')]
        (id, _, _, _, _) = parser.split_proof_rule(data.get('line'))
        cell.add_line_after(id)
        return jsonify(get_result_from_cell(cell))
    return jsonify({})


@app.route('/api/remove-line', methods=['POST'])
def remove_line():
    data = json.loads(request.get_data().decode("utf-8"))
    if data:
        cell = cells[data.get('id')]
        (id, _, _, _, _) = parser.split_proof_rule(data.get('line'))
        cell.remove_line(id)
        return jsonify(get_result_from_cell(cell))
    return jsonify({})


@app.route('/api/introduction', methods=['POST'])
def introduction():
    data = json.loads(request.get_data().decode("utf-8"))
    if data:
        cell = cells.get(data.get('id'))
        len_before = cell.prf.get_num_item()
        (id, _, _, _, _) = parser.split_proof_rule(data.get('line'))
        cell.introduction(id, data.get('var_name'))
        line_diff = (cell.prf.get_num_item() - len_before) / 2
        result = get_result_from_cell(cell)
        result["line-diff"] = line_diff
        return jsonify(result)
    return jsonify({})


@app.route('/api/apply-backward-step', methods=['POST'])
def apply_backward_step():
    data = json.loads(request.get_data().decode("utf-8"))
    if data:
        cell = cells.get(data.get('id'))
        (id, _, _, _, _) = parser.split_proof_rule(data.get('line'))
        theorem = data.get('theorem').split(",")
        theorem, prevs = theorem[0], theorem[1:]
        if prevs:
            prevs = [prev.strip() for prev in prevs]
        cell.apply_backward_step(id, theorem, prevs=prevs)
        return jsonify(get_result_from_cell(cell))
    return jsonify({})


@app.route('/api/apply-induction', methods=['POST'])
def apply_induction():
    data = json.loads(request.get_data().decode("utf-8"))
    if data:
        cell = cells.get(data.get('id'))
        (id, _, _, _, _) = parser.split_proof_rule(data.get('line'))
        theorem, var = data.get('theorem').split(",")
        cell.apply_induction(id, theorem, var)
        return jsonify(get_result_from_cell(cell))
    return jsonify({})


@app.route('/api/rewrite-goal', methods=['POST'])
def rewrite_goal():
    data = json.loads(request.get_data().decode("utf-8"))
    if data:
        cell = cells.get(data.get('id'))
        (id, _, _, _, _) = parser.split_proof_rule(data.get('line'))
        theorem = data.get('theorem')
        cell.rewrite_goal(id, theorem)
        return jsonify(get_result_from_cell(cell))
    return jsonify({})


@app.route('/api/set-line', methods=['POST'])
def set_line():
    data = json.loads(request.get_data().decode("utf-8"))
    if data:
        cell = cells.get(data.get('id'))
        try:
            (id, rule_name, args, prevs, th) = parser.split_proof_rule(data.get('line'))
            cell.set_line(id, rule_name, args=args, prevs=prevs, th=th)
            return jsonify(get_result_from_cell(cell))
        except Exception as e:
            error = {
                "failed": e.__class__.__name__,
                "message": str(e)
            }
        return jsonify(error)


@app.route('/api/json', methods=['POST'])
def json_parse():
    thy = BasicTheory
    data = json.loads(request.get_data().decode("utf-8"))
    output_data = []
    if data:
        for d in data:
            output = {}
            prop = parse_extension(thy, d)
            if d['ty'] == 'def.ax':
                output['name'] = d['name']
                output['prop'] = str(prop)
                output['ty'] = d['ty']
                output_data.append(output)

            if d['ty'] == 'thm':
                output['name'] = d['name']
                output['prop'] = print_term(thy, prop, unicode=True, highlight=True)
                output['ty'] = d['ty']
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
                output['prop'] = [print_term(thy, t, highlight=True, unicode=True) for t in prop]
                output['type'] = d['type']
                output['ty'] = d['ty']
                output_data.append(output)

    return jsonify({'data': output_data})
