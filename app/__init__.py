import json
# from typing import Dict, AnyStr

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
from syntax.parser import term_parser

app = Flask(__name__, static_url_path='/static')
app.secret_key = b'_5#y2L"F4Q8z\n\xec]/'

app.config.from_object('config')

# Dict[AnyStr, Cell]
cells = dict()

thy = BasicTheory()
ctxt = dict()
parse = parser.term_parser(thy, ctxt).parse


@app.route('/')
def index():
    return render_template('index.html')


@app.route('/api/check-proof', methods=['POST'])
def data_process():
    data = json.loads(request.get_data().decode("utf-8"))
    # Sort by integer value of k
    input = [v for (k, v) in sorted(data.items(), key=lambda p: int(p[0]))]
    server = Server(BasicTheory())
    try:
        result_string = server.check_proof(input)
    except TheoryException:
        result = {"failed": "TheoryException"}
        return jsonify(result)
    except CheckProofException as e:
        result = {
            "failed": "CheckProofException",
            "message": e.str
        }
        return jsonify(result)
    else:
        result_list = result_string.splitlines()
        result_dict = dict(enumerate(result_list, 1))
        return jsonify(result_dict)


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
        origin = {'variables': variables,
                  'assumes': assumes,
                  'conclunsion': conclusion}
        cell = Cell(variables_parser,
                    assumes_parser,
                    conclusion_parser,
                    origin,
                    ctxt=ctxt)
        cells[data.get('id')] = cell
        return jsonify({"result": cell.proof.print(print_vars=True)})
    return jsonify({})


@app.route('/api/add-line-after', methods=['POST'])
def add_line_after():
    data = json.loads(request.get_data().decode("utf-8"))
    if data:
        cell = cells[data.get('id')]
        (id, _, _, _, _) = parser.split_proof_rule(data.get('line'))
        cell.proof = tactic.add_line_after(cell.proof, id)
        return jsonify({"result": cell.proof.print(print_vars=True)})
    return jsonify({})


@app.route('/api/introduction', methods=['POST'])
def introduction():
    data = json.loads(request.get_data().decode("utf-8"))
    if data:
        cell = cells.get(data.get('id'))
        len_before = cell.proof.get_num_item()
        (id, _, _, _, _) = parser.split_proof_rule(data.get('line'))
        cell.proof = tactic.introduction(cell.proof, id)
        line_diff = (cell.proof.get_num_item() - len_before) / 2
        return jsonify({"line-diff": line_diff, "result": cell.proof.print(print_vars=True)})
    return jsonify({})


@app.route('/api/apply-backward-step', methods=['POST'])
def apply_backward_step():
    data = json.loads(request.get_data().decode("utf-8"))
    if data:
        cell = cells.get(data.get('id'))
        theorem = data.get('theorem')
        (id, _, _, _, _) = parser.split_proof_rule(data.get('line'))
        cell.proof = tactic.apply_backward_step(cell.proof, id, thy, theorem)
        return jsonify({"result": cell.proof.print(print_vars=True)})
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
            return jsonify(cell.origin)
    return jsonify({})
