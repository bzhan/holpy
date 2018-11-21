import json
# from typing import Dict, AnyStr

from app.cell import Cell
from flask import Flask, request, render_template
from flask.json import jsonify
from kernel.term import Var
from kernel.thm import primitive_deriv
from logic.basic import BasicTheory
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
    result_string = server.check_proof(input)
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
    elif data.get('event') == 'init_cell':
        variables = data.get('variables')
        assumes = data.get('assumes')
        conclusion = data.get('conclusion')
        variables_parser = []
        assumes_parser = []
        for variable in variables:
            name, t = parser.var_decl_parser(thy).parse(variable)
            if name and t:
                variables_parser.append(Var(name, t))
        for assume in assumes:
            term = term_parser(thy, ctxt).parse(assume)
            if term:
                assumes_parser.append(term)
        conclusion_parser = term_parser(thy, ctxt).parse(conclusion)
        cell = Cell(variables_parser, assumes_parser, conclusion_parser, {'variables': variables,
                                                                          'assumes': assumes,
                                                                          'conclunsion': conclusion})
        cells[data.get('id')] = cell
        return jsonify({"result": cell.proof.print(print_vars=True)})
    return jsonify({})


@app.route('/api/check-type', methods=['POST'])
def check_type():
    data = json.loads(request.get_data().decode("utf-8"))
    if data:
        thy = BasicTheory()
        line = data['line']
        if not line.startswith('var '):
            (id, rule_name, args, prevs) = parser.split_proof_rule(line)
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
