import json, os
from flask import Flask, render_template, request
from flask.json import jsonify

from integral import parser
from integral import rules


app = Flask(__name__)

@app.route('/', methods=['GET', 'POST'])
def integral():
    return render_template('integral.html')

@app.route('/templ', methods=['GET'])
def templ():
    return render_template('templ.html')

@app.route("/open_file", methods=['POST'])
def open_file():
    data = json.loads(request.get_data().decode('utf-8'))
    file_name = data['file_name']
    with open("integral/examples/test.json", 'r', encoding='utf-8') as f:
        f_data = json.load(f)

    return jsonify(f_data)

@app.route("/linearity", methods=['POST'])
def linearity():
    data = json.loads(request.get_data().decode('utf-8'))
    rule = rules.Linearity()
    problem = parser.parse_expr(data['problem'])
    new_problem = rule.eval(problem)
    return jsonify({'new_problem': str(new_problem)})

@app.route("/simplify", methods=['POST'])
def simplify():
    data = json.loads(request.get_data().decode('utf-8'))
    rule = rules.Simplify()
    problem = parser.parse_expr(data['problem'])
    new_problem = rule.eval(problem)
    return jsonify({'new_problem': str(new_problem)})

@app.route("/common-integral", methods=['POST'])
def common_integral():
    data = json.loads(request.get_data().decode('utf-8'))
    rule = rules.OnSubterm(rules.CommonIntegral())
    problem = parser.parse_expr(data['problem'])
    new_problem = rule.eval(problem)
    return jsonify({'new_problem': str(new_problem)})


if __name__ == "__main__":
    app.run(host='127.0.0.1', port=5000, use_reloader=False, debug=True, threaded=True)
