# Author: Chaozhu Xiang, Bohua Zhan

import json

from flask import Flask, request, render_template
from flask.json import jsonify
from kernel.term import Var
from kernel.thm import primitive_deriv
from kernel.theory import TheoryException, CheckProofException
from logic.basic import BasicTheory
from server.tactic import ProofState
from syntax import parser
from syntax.parser import term_parser, ParserException

app = Flask(__name__, static_url_path='/static')
app.secret_key = b'_5#y2L"F4Q8z\n\xec]/'

app.config.from_object('config')

# Dictionary from id to ProofState
cells = dict()

thy = BasicTheory()
ctxt = dict()
parse = parser.term_parser(thy, ctxt).parse


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
        ctxt = {}
        vars = []
        assums = []
        for var in data.get('variables'):
            name, t = parser.var_decl_parser(thy).parse(var)
            if name and t:
                vars.append(Var(name, t))
                ctxt[name] = t
        for assum in data.get('assumes'):
            t = term_parser(thy, ctxt).parse(assum)
            if t:
                assums.append(t)
        concl = term_parser(thy, ctxt).parse(data.get('conclusion'))
        cell = ProofState(vars, assums, concl)
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
        cell.apply_backward_step(id, theorem, prevs=prevs)
        return jsonify(get_result_from_cell(cell))
    return jsonify({})


@app.route('/api/check-type', methods=['POST'])
def check_type():
    data = json.loads(request.get_data().decode("utf-8"))
    if data:
        line = data['line']
        if not line.startswith('var '):
            (id, rule_name, args, prevs, th) = parser.split_proof_rule(line)
            result = {'theorem': rule_name}
            return jsonify(result)
    return jsonify({})


@app.route('/api/get-cell-state', methods=['POST'])
def get_cell_state():
    data = json.loads(request.get_data().decode("utf-8"))
    if data:
        id = data.get('id')
        if cells.get(id):
            cell = cells.get(id)
            return jsonify(cell.obtain_init_data())
    return jsonify({})
