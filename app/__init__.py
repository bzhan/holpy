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
from file_function import save_file,save_proof

app = Flask(__name__, static_url_path='/static')
app.secret_key = b'_5#y2L"F4Q8z\n\xec]/'

app.config.from_object('config')

# Dictionary from id to ProofState
cells = dict()


def get_result_from_cell(cell):
    # Check proof at the end of each operation
    cell.check_proof()
    return {
        "proof": cell.export_proof(unicode=True),
        "report": cell.rpt.json_data()
    }

@app.route('/')
def index():
    return render_template('index.html')


@app.route('/api/init', methods=['POST'])
def init_component():
    data = json.loads(request.get_data().decode("utf-8"))
    if data.get('event') == 'init_cell':
        cell = ProofState.parse_init_state(data['vars'], data['prop'])
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
            item = parser.parse_proof_rule(cell.thy, cell.get_ctxt(), data.get('line'))
            cell.set_line(item.id, item.rule, args=item.args, prevs=item.prevs, th=item.th)
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
    output_data = []
    f_data = json.loads(request.get_data().decode("utf-8"))
    data = []
    if type(f_data) == str:
        with open('library/'+ f_data +'.json', 'r', encoding='utf-8') as f:
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
                if 'save-proof' in d:
                    output['save-proof'] = d['save-proof']
                    output['status']='green'
                    if 'sorry' in d['save-proof']:
                        output['status'] = 'yellow'
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
    save_proof(data['name'], data['id'], data['proof'])

    return ''







