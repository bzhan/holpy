# Author: Runqing Xu, Bohua Zhan

"""API for computing integrals."""

import json
from flask import request
from flask.json import jsonify
from lark import Lark, Transformer, v_args, exceptions
from fractions import Fraction
from sympy import expand_multinomial

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

@app.route("/api/integral-super-simplify", methods=['POST'])
def integral_super_simplify():
    data = json.loads(request.get_data().decode('utf-8'))
    rules_set = [integral.rules.OnSubterm(integral.rules.ElimAbs()), 
                        integral.rules.Simplify(), integral.rules.Linearity(), integral.rules.OnSubterm(integral.rules.CommonIntegral())]
    def simplify(problem):
        for i in range(3):
            for r in rules_set:               
                problem = r.eval(problem)
        return problem
    problem = simplify(integral.parser.parse_expr(data['problem']))
    return jsonify({
        'text': str(problem),
        'latex': integral.latex.convert_expr(problem),
        'reason': "Simplification"
    })

@app.route("/api/integral-same-integral", methods=['POST'])
def integral_same_integral():
    data = json.loads(request.get_data().decode('utf-8'))
    lhs = integral.parser.parse_expr(data['lhs'])
    rhs = integral.parser.parse_expr(data['rhs'])
    rule = integral.rules.IntegrateByEquation(lhs)
    same_integral = rule.find_same_integral(rhs)
    s = []
    for i in same_integral:
        s.append({
            'text': str(i),
            'latex': integral.latex.convert_expr(i)
        })

    return json.dumps(s)
    

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

@app.route("/api/integral-integrate-by-equation1", methods=['POST'])
def integrate_by_equation1():
    data = json.loads(request.get_data().decode('utf-8'))
    problem = integral.parser.parse_expr(data['equation_part'])
    lhs = integral.parser.parse_expr(data['lhs'])
    rhs = integral.parser.parse_expr(data['rhs'])
    rule = integral.rules.IntegrateByEquation(lhs)
    result = rule.eval(rhs, problem)
    return jsonify({
        "text": str(result),
        "latex": integral.latex.convert_expr(result),
        "params": {
            "lhs": data['lhs'],
            "rhs": data['equation_part']
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
            "text": str(i[0]),
            "body": str(i[0].body),
            "latex": integral.latex.convert_expr(i[0]),
            "location": str(i[1])
        })
    return json.dumps(n)

@app.route("/api/integral-compose-integral", methods=['POST'])
def integral_compose_integral():
    data = json.loads(request.get_data().decode('utf-8'))
    new_integral = []
    latex_reason = ""
    reason = ""
    modified_index = int(data['index'])
    location = data['problem'][modified_index]['location']
    denom = ""
    rhs = ""
    params = {}
    for d in data['problem']:
        new_integral.append(integral.parser.parse_expr(d['text']))
        if '_latex_reason' in d:
            latex_reason += d['_latex_reason']
        if 'reason' in d:
            reason += d['reason']
        if 'params' in d:
            params = d['params']
        if 'denom' in d:
            denom = d['denom']
        if 'rhs' in d:
            rhs = d['rhs']
    curr = integral.parser.parse_expr(data['cur_calc'])
    new_expr = curr
    old_integral = curr.separate_integral()
    for i in range(len(old_integral)):
        new_expr = new_expr.replace_trig(old_integral[i][0], new_integral[i])
    info = {
        'text': str(new_expr),
        'latex': integral.latex.convert_expr(new_expr),
        'reason': reason,
    }
    if location != "":
        info.update({'location': location})
    if params:
        info.update({'params': params})
    if denom:
        info.update({'denom': denom})
    if rhs:
        info.update({'rhs': rhs})
    if latex_reason:
        info.update({'_latex_reason': latex_reason})
    return json.dumps(info)

    

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
    rule = integral.rules.Substitution1(data['var_name'], expr)
    problem = integral.parser.parse_expr(data['problem'])
    new_problem, new_problem_body = rule.eval(problem)
    print("problem: ", problem)
    print("loaction:", data['location'])
    return jsonify({
        'text': str(new_problem),
        'latex': integral.latex.convert_expr(new_problem),
        'reason': "Substitution",
        'location': data['location'],
        'params': {
            'f': str(new_problem_body),
            'g': str(expr),
            'var_name': str(data['var_name'])
        },
        '_latex_reason': "Substitute \\(%s\\) for \\(%s\\)" % (
            integral.latex.convert_expr(integral.parser.parse_expr(data['var_name'])), integral.latex.convert_expr(expr)
        )
    })

@app.route("/api/integral-substitution2", methods=['POST'])
def integral_substitution2():
    data = json.loads(request.get_data().decode('utf-8'))
    expr = integral.parser.parse_expr(data['expr'])
    rule = integral.rules.Substitution2(data['var_name'], expr)
    problem = integral.parser.parse_expr(data['problem'])
    new_problem = rule.eval(problem)
    return jsonify({
        'text': str(new_problem),
        'latex': integral.latex.convert_expr(new_problem),
        'reason': "Substitution inverse",
        'params': {
            'g': str(expr),
            'var_name': str(data['var_name']),
            "a": str(new_problem.lower),
            "b": str(new_problem.upper)
        },
        '_latex_reason': "Substitute \\(%s\\) for \\(%s\\)" % (
            integral.latex.convert_expr(integral.parser.parse_expr(data['var_name'])), integral.latex.convert_expr(expr)
        )
    })

@app.route("/api/integral-validate-expr", methods=['POST'])
def integral_validate_expr():
    data = json.loads(request.get_data().decode('utf-8'))
    problem = integral.parser.parse_expr(data['problem'])
    flag = None # if dollar is valid, flag = true
    try:
        dollar = integral.parser.parse_expr(data['dollar'])
        if dollar.normalize() != problem.body.normalize():
            return jsonify({
                'flag': False
            })
        else:
            # Do trig transform
            select = integral.parser.parse_expr(data['select'])
            dollar_location = dollar.get_location()
            location = ""
            if data["integral_location"] != "":
                location = data["integral_location"] + ".0"
            else:
                location = "0"
            if dollar_location != "":
                location += "." + dollar_location
            
            # location = data["integral_location"] + ".0." + dollar_location if data["integral_location"] != "" else "0." + dollar_location
            new_trig_set = tuple(integral.expr.trig_transform(select))
            new_integral_set = [integral.expr.Integral(problem.var, problem.lower, problem.upper, problem.body.replace_expr(dollar_location, t[0])) for t in new_trig_set]
            transform_info = []
            for i in range(len(new_integral_set)):
                transform_info.append({
                    "reason": "Rewrite trigonometric",
                    'text': str(new_integral_set[i]),
                    'latex': integral.latex.convert_expr(new_integral_set[i]),
                    "params":{
                        "rule": new_trig_set[i][1]
                    },
                    '_latex_reason': "Rewrite trigonometric \\(%s\\) to \\(%s\\)" % 
                                (integral.latex.convert_expr(select), integral.latex.convert_expr(new_trig_set[i][0])), 
                    # If there is only one integral in the full expression, location begins from the body;
                    # Else from the integral
                    "location": location
                })
            return jsonify({
                "flag": True,
                "content": transform_info
            })
    except (exceptions.UnexpectedCharacters, exceptions.UnexpectedToken) as e:
        return jsonify({
                'flag': False
            })
    
@app.route("/api/integral-validate-power-expr", methods=['POST'])
def integral_validate_power_expr():
    data = json.loads(request.get_data().decode('utf-8'))
    problem = integral.parser.parse_expr(data['problem'])
    flag = None # if dollar is valid, flag = true
    try:
        dollar = integral.parser.parse_expr(data['dollar'])
        if dollar.normalize() != problem.body.normalize():
            return jsonify({
                'flag': False
            })
        else:
            select = integral.parser.parse_expr(data['select'])
            if not (select.ty == integral.expr.OP and select.op == "^" and select.args[1].ty == integral.expr.CONST and Fraction(select.args[1].val).denominator == 1):
                return jsonify({
                    'flag': False
                })
            dollar_location = dollar.get_location()
            location = ""
            if data["integral_location"] != "":
                location = data["integral_location"] + ".0"
            else:
                location = "0"
            if dollar_location != "":
                location += "." + dollar_location
            body = problem.body
            body = body.replace_expr(dollar_location, integral.expr.holpy_style(expand_multinomial(integral.expr.sympy_style(select))))
            new_integral = integral.expr.Integral(problem.var, problem.lower, problem.upper, body)
            return jsonify({
                "flag": True,
                "text": str(new_integral),
                "latex":  integral.latex.convert_expr(new_integral),
                "location": location,
                "reason": "Unfold power"
            })
    except (exceptions.UnexpectedCharacters, exceptions.UnexpectedToken) as e:
        return jsonify({
                'flag': False
            })

@app.route("/api/integral-validate-rewrite", methods=['POST'])
def integral_validate_rewrite():
    data = json.loads(request.get_data().decode('utf-8'))
    problem = integral.parser.parse_expr(data['problem'])
    flag = None # if dollar is valid, flag = true
    try:
        dollar = integral.parser.parse_expr(data['dollar'])
        if dollar.normalize() != problem.body.normalize():
            return jsonify({
                'flag': False
            })
        else:
            # Do trig transform
            select = integral.parser.parse_expr(data['select'])
            dollar_location = dollar.get_location()
            location = ""
            if data["integral_location"] != "":
                location = data["integral_location"] + ".0"
            else:
                location = "0"
            if dollar_location != "":
                location += "." + dollar_location
            return jsonify({
                "rewrite": str(select),
                "flag": True,
                "absolute_location": location, #location in the whole Integral
                "relative_location": dollar_location # location in its own integral
            })
    except (exceptions.UnexpectedCharacters, exceptions.UnexpectedToken) as e:
        return jsonify({
                'flag': False
            })

@app.route("/api/integral-rewrite-expr", methods=['POST'])
def integral_rewrite_expr():
    data = json.loads(request.get_data().decode('utf-8'))
    problem = integral.parser.parse_expr(data['problem'])
    
    old_expr = integral.parser.parse_expr(data['old_expr'])
    try:
        new_expr = integral.parser.parse_expr(data['new_expr'])
        location = data['relative_location']
        if new_expr.normalize() != old_expr.normalize() or new_expr.findVar().name != problem.var:
            return jsonify({
                'flag': False
            })
        new_problem = integral.expr.Integral(problem.var, problem.lower, problem.upper, problem.body.replace_expr(location, new_expr))
        return jsonify({
            'flag': True,
            'text': str(new_problem),
            'latex': integral.latex.convert_expr(new_problem),
            'reason': "Rewrite",
            '_latex_reason': "Rewrite \\(%s\\) to \\(%s\\)"%(integral.latex.convert_expr(old_expr),
                                                            integral.latex.convert_expr(new_expr)),
            'params': {
                'rhs': data['new_expr']
            },
            "location": data['absolute_location']
        })
    except (exceptions.UnexpectedCharacters, exceptions.UnexpectedToken) as e:
        return jsonify({
                'flag': False
            })

@app.route("/api/integral-split", methods=['POST'])
def integral_split():
    data = json.loads(request.get_data().decode('utf-8'))
    problem = integral.parser.parse_expr(data['problem'])
    point  = integral.parser.parse_expr(data['point'])
    assert isinstance(point, integral.expr.Const)
    upper = problem.upper
    lower = problem.lower
    if integral.expr.sympy_style(upper) <= integral.expr.sympy_style(point) or integral.expr.sympy_style(lower) >= integral.expr.sympy_style(point):
        return jsonify({
            "flag": 'fail'
        })
    new_integral1 = integral.expr.Integral(problem.var, problem.lower, point, problem.body)
    new_integral2 = integral.expr.Integral(problem.var, point, problem.upper, problem.body)
    return jsonify({
        "flag": 'success',
        "reason": "Split region",
        "location": data['location'],
        "params": {
            "c": str(point)
        },
        "text": str(new_integral1 + new_integral2),
        "latex": integral.latex.convert_expr(new_integral1 + new_integral2) 
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
        'location': data['location'],
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
    rule = integral.rules.PolynomialDivision()
    problem = integral.parser.parse_expr(data['problem'])
    body = problem.body
    if not (body.ty == integral.expr.OP and body.op == "/"):
        return jsonify({
            'flag': False
        })
    denom = body.args[1]
    new_problem = rule.eval(problem)
    rhs = new_problem.body
    return jsonify({
        'flag': True,
        'text': str(new_problem),
        'latex': integral.latex.convert_expr(new_problem),
        'params': {
            'denom': str(denom),
            'rhs': str(rhs)
        },
        'reason': "Rewrite fraction",
        "location": data['location']
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

@app.route("/api/integral-save-format-file", methods=['POST'])
def integral_save_format_file():
    data = json.loads(request.get_data().decode('utf-8'))
    file_name = "integral/examples/%s.json" % data['filename']
    with open(file_name, 'w', encoding='utf-8') as f:
        json.dump({"content": data['content']}, f, indent=4, ensure_ascii=False, sort_key=True)
    
    return jsonify({
        'status': 'success'
    })