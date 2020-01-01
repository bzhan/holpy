# Author: Runqing Xu, Bohua Zhan

"""API for computing integrals."""

import json
from flask import request
from flask.json import jsonify

import integral
from app.app import app


@app.route("/api/integral-open-file", methods=['POST'])
def integral_open_file():
    data = json.loads(request.get_data().decode('utf-8'))
    file_name = "integral/examples/%s.json" % data['filename']
    with open(file_name, 'r', encoding='utf-8') as f:
        f_data = json.load(f)

    for item in f_data['content']:
        problem = integral.parser.parse_expr(item['problem'])
        item['_problem_latex'] = integral.latex.convert_expr(problem)

    return jsonify(f_data)

@app.route("/api/integral-initialize", methods=['POST'])
def integral_initialize():
    data = json.loads(request.get_data().decode('utf-8'))
    problem = integral.parser.parse_expr(data['problem'])
    return jsonify({
        'text': str(problem),
        'latex': integral.latex.convert_expr(problem),
        'reason': "Initial"
    })

@app.route("/api/integral-linearity", methods=['POST'])
def integral_linearity():
    data = json.loads(request.get_data().decode('utf-8'))
    rule = integral.rules.Linearity()
    problem = integral.parser.parse_expr(data['problem'])
    new_problem = rule.eval(problem)
    return jsonify({
        'text': str(new_problem),
        'latex': integral.latex.convert_expr(new_problem),
        'reason': "Linearity"
    })

@app.route("/api/integral-simplify", methods=['POST'])
def integral_simplify():
    data = json.loads(request.get_data().decode('utf-8'))
    rule = integral.rules.Simplify()
    problem = integral.parser.parse_expr(data['problem'])
    new_problem = rule.eval(problem)
    return jsonify({
        'text': str(new_problem),
        'latex': integral.latex.convert_expr(new_problem),
        'reason': "Simplification"
    })

@app.route("/api/integral-common-integral", methods=['POST'])
def integral_common_integral():
    data = json.loads(request.get_data().decode('utf-8'))
    rule = integral.rules.OnSubterm(integral.rules.CommonIntegral())
    problem = integral.parser.parse_expr(data['problem'])
    new_problem = rule.eval(problem)
    return jsonify({
        'text': str(new_problem),
        'latex': integral.latex.convert_expr(new_problem),
        'reason': "Common integrals"
    })

@app.route("/api/integral-elim-abs", methods=["POST"])
def integral_elim_abs():
    data = json.loads(request.get_data().decode('utf-8'))
    rule = integral.rules.OnSubterm(integral.rules.ElimAbs())
    problem = integral.parser.parse_expr(data['problem'])
    new_problem = rule.eval(problem)
    return jsonify({
        'text': str(new_problem),
        'latex': integral.latex.convert_expr(new_problem),
        'reason': "Eliminate abs"
    })

@app.route("/api/integral-integrate-by-equation", methods=['POST'])
def integrate_by_equation():
    data = json.loads(request.get_data().decode('utf-8'))
    problem = integral.parser.parse_expr(data['problem'])
    lhs = integral.parser.parse_expr(data['left'])
    rule = integral.rules.IntegrateByEquation(lhs)
    result = rule.eval(problem)
    return jsonify({
        "text": str(result),
        "latex": integral.latex.convert_expr(result),
        "params": {
            "lhs": data['left'],
            "rhs": data['problem']
        },
        "_latex_reason": "By solving equation: \\(%s = %s\\)" % (
            integral.latex.convert_expr(lhs), integral.latex.convert_expr(problem)
        )
    })

@app.route("/api/integral-separate-integrals", methods=['POST'])
def integral_separate_integrals():
    data = json.loads(request.get_data().decode('utf-8'))
    problem = integral.parser.parse_expr(data['problem'])
    integrals = problem.separate_integral()
    n = []
    for i in integrals:
        n.append({
            "text": str(i),
            "body": str(i.body),
            "latex": integral.latex.convert_expr(i)
        })
    return json.dumps(n)

@app.route("/api/integral-compose-integral", methods=['POST'])
def integral_compose_integral():
    data = json.loads(request.get_data().decode('utf-8'))
    new_integral = []
    reason = ""
    for d in data['problem']:
        new_integral.append(integral.parser.parse_expr(str(d['text'])))
        if '_latex_reason' in d:
            reason += d['_latex_reason']
            reason += "."
        elif 'reason' in d:
            reason += d['reason']
            reason += "."
    curr = integral.parser.parse_expr(data['cur_calc'])
    new_expr = curr
    old_integral = curr.separate_integral()
    for i in range(len(old_integral)):
        new_expr = new_expr.replace_trig(old_integral[i], new_integral[i])
    return jsonify({
        'text': str(new_expr),
        'latex': integral.latex.convert_expr(new_expr),
        '_latex_reason': reason
    })
    

@app.route("/api/integral-trig-transformation", methods=['POST'])
def integral_trig_transformation():
    data = json.loads(request.get_data().decode('utf-8'))
    rule = integral.rules.TrigSubstitution()
    del integral.expr.trig_identity[:]
    problem = integral.parser.parse_expr(data['problem'])
    e = integral.parser.parse_expr(data['exp'])
    if e.normalize() == problem.body.normalize():
        e = integral.expr.Integral(problem.var, problem.lower, problem.upper, e)
        possible_new_problem = rule.eval(e)
        #need to do more
        possible_form = list(integral.expr.trig_transform(integral.expr.trig_identity[0]))
        n = []
        for p in range(len(possible_new_problem)):
            n.append({ 
                'text': str(possible_new_problem[p][0]),
                'latex': integral.latex.convert_expr(possible_new_problem[p][0]),
                '_latex_reason': "Trig identities: \(%s = %s\\); Method : %s"
                % (integral.latex.convert_expr(integral.expr.trig_identity[0]),
                integral.latex.convert_expr(integral.parser.parse_expr(str(possible_form[p][0]).replace("**", "^"))),
                str(possible_new_problem[p][1]))
            })
        return json.dumps(n)
    else:
        return jsonify({
            'text': str(problem),
            'latex': integral.latex.convert_expr(problem),
            'reason': "Rewrite is invalid."
        })

@app.route("/api/integral-substitution", methods=['POST'])
def integral_substitution():
    data = json.loads(request.get_data().decode('utf-8'))
    expr = integral.parser.parse_expr(data['expr'])
    rule = integral.rules.Substitution(data['var_name'], expr)
    problem = integral.parser.parse_expr(data['problem'])
    new_problem = rule.eval(problem)
    return jsonify({
        'text': str(new_problem),
        'latex': integral.latex.convert_expr(new_problem),
        'reason': "Substitution",
        'params': {
            'var_name': data['var_name'],
            'expr': data['expr'],
        },
        '_latex_reason': "Substitute \\(%s\\) for \\(%s\\)" % (
            integral.latex.convert_expr(integral.parser.parse_expr(data['var_name'])), integral.latex.convert_expr(expr)
        )
    })

@app.route("/api/integral-integrate-by-parts", methods=['POST'])
def integral_integrate_by_parts():
    data = json.loads(request.get_data().decode('utf-8'))
    parts_u = integral.parser.parse_expr(data['parts_u'])
    parts_v = integral.parser.parse_expr(data['parts_v'])
    rule = integral.rules.IntegrationByParts(parts_u, parts_v)
    problem = integral.parser.parse_expr(data['problem'])
    new_problem = rule.eval(problem)
    return jsonify({
        'text': str(new_problem),
        'latex': integral.latex.convert_expr(new_problem),
        'reason': "Integrate by parts",
        'params': {
            'parts_u': data['parts_u'],
            'parts_v': data['parts_v'],
        },
        '_latex_reason': "Integrate by parts, \\(u = %s, v = %s\\)" % (
            integral.latex.convert_expr(parts_u), integral.latex.convert_expr(parts_v)
        )
    })

@app.route("/api/integral-equation-substitution", methods=['POST'])
def integral_equation_substitution():
    data = json.loads(request.get_data().decode('utf-8'))
    old_expr = integral.parser.parse_expr(data['problem']).body
    new_expr = integral.parser.parse_expr(data['new_expr'])
    rule = integral.rules.Equation(old_expr, new_expr)
    problem = integral.parser.parse_expr(data['problem'])
    new_problem = rule.eval(problem)
    if new_problem != problem and new_problem != old_expr:
        return jsonify({
            'text': str(new_problem),
            'latex': integral.latex.convert_expr(new_problem),
            '_latex_reason': "Equation substitution successful, \\( %s\\) == \\(%s\\)" % (
                integral.latex.convert_expr(old_expr), integral.latex.convert_expr(new_expr)
            ),
            'flag': "success"
        })
    else:
        return jsonify({
            'flag': "fail",
            "_latex_reason": "\\(%s != %s\\)" % 
            (integral.latex.convert_expr(old_expr), integral.latex.convert_expr(new_expr))
        })

@app.route("/api/integral-polynomial-division", methods=['POST'])
def integral_polynomial_division():
    data = json.loads(request.get_data().decode('utf-8'))
    rule = integral.rules.OnSubterm(integral.rules.PolynomialDivision())
    problem = integral.parser.parse_expr(data['problem'])
    new_problem = rule.eval(problem)
    return jsonify({
        'text': str(new_problem),
        'latex': integral.latex.convert_expr(new_problem),
        'reason': "Polynomial division"
    })

@app.route("/api/integral-save-file", methods=['POST'])
def integral_save_file():
    data = json.loads(request.get_data().decode('utf-8'))
    file_name = "integral/examples/%s.json" % data['filename']
    with open(file_name, 'w', encoding='utf-8') as f:
        json.dump({"content": data['content']}, f, indent=4, ensure_ascii=False, sort_keys=True)

    return jsonify({
        'status': 'success'
    })
