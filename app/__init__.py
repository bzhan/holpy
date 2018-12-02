# Author: Chaozhu Xiang, Bohua Zhan

import json

from app.cell import Cell
from flask import Flask, request, render_template
from flask.json import jsonify
from kernel.term import Var
from kernel.thm import primitive_deriv
from kernel.theory import TheoryException, CheckProofException
from logic.basic import BasicTheory
import server.tactic as tactic
from server.server import Server
from syntax import parser
from syntax.parser import term_parser, ParserException

app = Flask(__name__, static_url_path='/static')
app.secret_key = b'_5#y2L"F4Q8z\n\xec]/'

app.config.from_object('config')

# Dictionary from id to cells
cells = dict()

thy = BasicTheory()
ctxt = dict()
parse = parser.term_parser(thy, ctxt).parse


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
        result = {
            "proof": cell.print_proof(),
            "report": cell.rpt.json_data()
        }
        return jsonify(result)
    except Exception as e:
        result = {
            "failed": e.__class__.__name__,
            "message": str(e)
        }
        return jsonify(result)


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
        variables = data.get('variables')
        assumes = data.get('assumes')
        conclusion = data.get('conclusion')
        variables_parser = []
        assumes_parser = []
        for variable in variables:
            name, t = parser.var_decl_parser(thy).parse(variable)
            if name and t:
                variables_parser.append(Var(name, t))
                ctxt[name] = t
        for assume in assumes:
            term = term_parser(thy, ctxt).parse(assume)
            if term:
                assumes_parser.append(term)
        conclusion_parser = term_parser(thy, ctxt).parse(conclusion)
        cell = Cell(variables_parser,
                    assumes_parser,
                    conclusion_parser,
                    ctxt=ctxt)
        cells[data.get('id')] = cell
        return jsonify({"result": cell.print_proof()})
    return jsonify({})


@app.route('/api/add-line-after', methods=['POST'])
def add_line_after():
    data = json.loads(request.get_data().decode("utf-8"))
    if data:
        cell = cells[data.get('id')]
        (id, _, _, _, _) = parser.split_proof_rule(data.get('line'))
        cell.proof = tactic.add_line_after(cell.proof, id)
        cell.check_proof()
        return jsonify({"result": cell.print_proof()})
    return jsonify({})


@app.route('/api/remove-line', methods=['POST'])
def remove_line():
    data = json.loads(request.get_data().decode("utf-8"))
    if data:
        cell = cells[data.get('id')]
        (id, _, _, _, _) = parser.split_proof_rule(data.get('line'))
        cell.proof = tactic.remove_line(cell.proof, id)
        cell.check_proof()
        return jsonify({"result": cell.print_proof()})
    return jsonify({})


@app.route('/api/introduction', methods=['POST'])
def introduction():
    data = json.loads(request.get_data().decode("utf-8"))
    if data:
        cell = cells.get(data.get('id'))
        len_before = cell.proof.get_num_item()
        (id, _, _, _, _) = parser.split_proof_rule(data.get('line'))
        cell.proof = tactic.introduction(cell.proof, id, data.get('var_name'))
        line_diff = (cell.proof.get_num_item() - len_before) / 2
        cell.check_proof()
        return jsonify({"line-diff": line_diff, "result": cell.print_proof()})
    return jsonify({})


@app.route('/api/apply-backward-step', methods=['POST'])
def apply_backward_step():
    data = json.loads(request.get_data().decode("utf-8"))
    if data:
        cell = cells.get(data.get('id'))        
        (id, _, _, _, _) = parser.split_proof_rule(data.get('line'))
        theorem = data.get('theorem').split(",")
        theorem, prevs = theorem[0], theorem[1:]
        cell.proof = tactic.apply_backward_step(cell.proof, id, thy, theorem, prevs=prevs)
        cell.check_proof()
        return jsonify({"result": cell.print_proof()})
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
