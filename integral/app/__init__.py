import json, os
from flask import Flask, render_template, request
from flask.json import jsonify

from integral import parser
from integral import rules
from integral import latex

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
    file_name = "integral/examples/%s.json" % data['file_name']
    with open(file_name, 'r', encoding='utf-8') as f:
        f_data = json.load(f)

    for item in f_data['content']:
        problem = parser.parse_expr(item['problem'])
        item['_problem_latex'] = latex.convert_expr(problem)

    return jsonify(f_data)

@app.route("/initialize", methods=['POST'])
def initialize():
    data = json.loads(request.get_data().decode('utf-8'))
    problem = parser.parse_expr(data['problem'])
    return jsonify({
        'text': str(problem),
        'latex': latex.convert_expr(problem),
        'reason': "Initial"
    })

@app.route("/linearity", methods=['POST'])
def linearity():
    data = json.loads(request.get_data().decode('utf-8'))
    rule = rules.Linearity()
    problem = parser.parse_expr(data['problem'])
    new_problem = rule.eval(problem)
    return jsonify({
        'text': str(new_problem),
        'latex': latex.convert_expr(new_problem),
        'reason': "Linearity"
    })

@app.route("/simplify", methods=['POST'])
def simplify():
    data = json.loads(request.get_data().decode('utf-8'))
    rule = rules.Simplify()
    problem = parser.parse_expr(data['problem'])
    new_problem = rule.eval(problem)
    return jsonify({
        'text': str(new_problem),
        'latex': latex.convert_expr(new_problem),
        'reason': "Simplification"
    })

@app.route("/common-integral", methods=['POST'])
def common_integral():
    data = json.loads(request.get_data().decode('utf-8'))
    rule = rules.OnSubterm(rules.CommonIntegral())
    problem = parser.parse_expr(data['problem'])
    new_problem = rule.eval(problem)
    return jsonify({
        'text': str(new_problem),
        'latex': latex.convert_expr(new_problem),
        'reason': "Common integrals"
    })

@app.route("/substitution", methods=['POST'])
def substitution():
    data = json.loads(request.get_data().decode('utf-8'))
    expr = parser.parse_expr(data['expr'])
    rule = rules.Substitution(data['var_name'], expr)
    problem = parser.parse_expr(data['problem'])
    new_problem = rule.eval(problem)
    return jsonify({
        'text': str(new_problem),
        'latex': latex.convert_expr(new_problem),
        'reason': "Substitution",
        'params': {
            'var_name': data['var_name'],
            'expr': data['expr'],
        },
        '_latex_reason': "Substitute \\(%s\\) for \\(%s\\)" % (
            data['var_name'], latex.convert_expr(expr)
        )
    })

@app.route("/integrate-by-parts", methods=['POST'])
def integrate_by_parts():
    data = json.loads(request.get_data().decode('utf-8'))
    parts_u = parser.parse_expr(data['parts_u'])
    parts_v = parser.parse_expr(data['parts_v'])
    rule = rules.IntegrationByParts(parts_u, parts_v)
    problem = parser.parse_expr(data['problem'])
    new_problem = rule.eval(problem)
    return jsonify({
        'text': str(new_problem),
        'latex': latex.convert_expr(new_problem),
        'reason': "Integrate by parts",
        'params': {
            'parts_u': data['parts_u'],
            'parts_v': data['parts_v'],
        },
        '_latex_reason': "Integrate by parts, \\(u = %s, v = %s\\)" % (
            latex.convert_expr(parts_u), latex.convert_expr(parts_v)
        )
    })

@app.route("/save-file", methods=['POST'])
def save_file():
    data = json.loads(request.get_data().decode('utf-8'))
    file_name = "integral/examples/%s.json" % data['file_name']
    with open(file_name, 'w', encoding='utf-8') as f:
        json.dump({"content": data['content']}, f, indent=4, ensure_ascii=False, sort_keys=True)

    return jsonify({
        'status': 'success'
    })

if __name__ == "__main__":
    app.run(host='127.0.0.1', port=5000, use_reloader=False, debug=True, threaded=True)
