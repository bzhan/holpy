import json

from flask.json import jsonify

from logic.basic import BasicTheory
from kernel.thm import primitive_deriv
from server.server import Server
from syntax import parser
from flask import Flask, send_from_directory, session, redirect, url_for, escape, request, g, render_template

app = Flask(__name__, static_url_path='/static')
app.secret_key = b'_5#y2L"F4Q8z\n\xec]/'

app.config.from_object('config')


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
    data = json.loads(request.get_data())
    if data['event'] == 'init_theorem':
        macro_dict = {0: 'NONE', 1: 'TERM', 2: 'TYINST', 3: 'INST', 4: 'STRING'}
        result = {}
        for key, value in primitive_deriv.items():
            result[key] = macro_dict[value[1]]
        return jsonify(result)
    return jsonify({})

@app.route('/api/check-type', methods=['POST'])
def check_type():
    data = json.loads(request.get_data())
    if data:
        thy = BasicTheory()
        line = data['line']
        (id, rule_name, args, prevs) = parser.split_proof_rule(line)
        result = {'theorem': rule_name}
        return jsonify(result)
    return jsonify({})