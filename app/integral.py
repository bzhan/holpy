# Author: Runqing Xu, Bohua Zhan

"""API for computing integrals."""

import json
from flask import request
from flask.json import jsonify
from lark import Lark, Transformer, v_args, exceptions
from fractions import Fraction
from sympy import expand_multinomial
import pathlib
import os
import integral
from integral import slagle
from app.app import app


@app.route("/api/integral-load-file-list", methods=['POST'])
def integral_load_file_list():
    os.chdir('./integral/examples')
    json_files = tuple(str(z) for z in list(pathlib.Path('./').rglob('*.json')))
    os.chdir('../../')
    return jsonify({
        'file_list': json_files
    })

@app.route("/api/integral-open-file", methods=['POST'])
def integral_open_file():
    data = json.loads(request.get_data().decode('utf-8'))
    file_name = "integral/examples/%s" % data['filename']
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

@app.route("/api/integral-validate-integral", methods=['POST'])
def integral_validate_integral():
    data = json.loads(request.get_data().decode('utf-8'))
    try:
        problem = integral.parser.parse_expr(data['expr'])
        index = int(data['index'])
        return jsonify({
            'flag': True,            
            'content': {
                'name': 'Exercise ' + str(data['index']),
                'problem': data['expr'],
                '_problem_latex': integral.latex.convert_expr(problem),
            }
        })
    except:
        return jsonify({
            'flag': False
        })

@app.route("/api/integral-super-simplify", methods=['POST'])
def integral_super_simplify():
    data = json.loads(request.get_data().decode('utf-8'))
    rules_set = [integral.rules.Simplify(), integral.rules.OnSubterm(integral.rules.Linearity()), integral.rules.OnSubterm(integral.rules.CommonIntegral())]
    abs_rule = integral.rules.ElimAbs()
    problem = integral.parser.parse_expr(data['problem'])
    if not (abs_rule.check_zero_point(problem) and len(problem.getAbs()) == 0):
        # If there are no abs expression or there are no zero point
        rules_set.append(integral.rules.OnSubterm(integral.rules.ElimAbs()))
    def simplify(problem):
        for i in range(5):
            for r in rules_set:             
                problem = r.eval(problem)
                if problem.is_constant():
                    return problem
        return problem
    problem = simplify(integral.parser.parse_expr(data['problem']))
    return jsonify({
        'text': str(problem),
        'latex': integral.latex.convert_expr(problem),
        'reason': "Simplification"
    })

@app.route("/api/integral-elim-abs", methods=["POST"])
def integral_elim_abs():
    data = json.loads(request.get_data().decode('utf-8'))
    rule = integral.rules.ElimAbs()
    problem = integral.parser.parse_expr(data['problem'])
    if not rule.check_zero_point(problem):
        new_problem = rule.eval(problem)
        return jsonify({
            'reason': "Simplification",
            'text': str(new_problem),
            'latex': integral.latex.convert_expr(new_problem)
        })
    c = rule.get_zero_point(problem)
    new_problem = integral.expr.Integral(problem.var, problem.lower, c, problem.body) + integral.expr.Integral(problem.var, 
                            c, problem.upper, problem.body)
    return jsonify({
        'text': str(new_problem),
        'latex': integral.latex.convert_expr(new_problem),
        'reason': "Split region",
        'params': {
            'c': str(c)
        },
        'location': data['location']
    })

@app.route("/api/integral-integrate-by-equation", methods=['POST'])
def integrate_by_equation():
    data = json.loads(request.get_data().decode('utf-8'))
    rhs = integral.parser.parse_expr(data['rhs'])
    lhs = integral.parser.parse_expr(data['lhs'])
    rule = integral.rules.IntegrateByEquation(lhs, rhs)
    if not rule.validate():
        return jsonify({
            'flag': False
        })
    # coeff = rule.getCoeff()
    # coeff = (-coeff).normalize()
    new_problem, coeff = rule.eval()
    return jsonify({
        "text": str(new_problem),
        "latex": integral.latex.convert_expr(new_problem),
        "params": {
            "factor": str(coeff),
            "prev_id": str(int(data['prev_id']) - 1)
        },
        "reason": "Solve equation",
        "_latex_reason": "By solving equation: \\(%s = %s\\)" % (
            integral.latex.convert_expr(lhs), integral.latex.convert_expr(rhs)
        )
    })

@app.route("/api/integral-separate-integrals", methods=['POST'])
def integral_separate_integrals():
    data = json.loads(request.get_data().decode('utf-8'))
    problem = integral.parser.parse_expr(data['problem'])
    integrals = problem.separate_integral()
    n = []
    for i, loc in integrals:
        n.append({
            "text": str(i),
            "var_name": i.var,
            "body": str(i.body),
            "latex": integral.latex.convert_expr(i),
            "location": str(loc)
        })
    return json.dumps(n)

@app.route("/api/integral-compose-integral", methods=['POST'])
def integral_compose_integral():
    data = json.loads(request.get_data().decode('utf-8'))
    new_integral = []
    latex_reason = ""
    reason = ""
    modified_index = int(data['index'])
    location = ""
    if 'location' in data['problem'][modified_index]:
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
    old_integral, _ = curr.separate_integral()
    for i in range(len(old_integral)):
        new_expr = new_expr.replace_trig(old_integral[i], new_integral[i])
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

@app.route("/api/integral-substitution", methods=['POST'])
def integral_substitution():
    data = json.loads(request.get_data().decode('utf-8'))
    try:
        expr = integral.parser.parse_expr(data['expr'])
    except:
        return jsonify({
                'flag': False,
                'reason': "%s is not a valid substitution expression." % data['expr']
            })
    rule = integral.rules.Substitution1(data['var_name'], expr)
    problem = integral.parser.parse_expr(data['problem'])
    if data['var_name'] == problem.var:
        return jsonify({
            'flag': False,
            'reason': "%s is not a valid variable for substitution." % data['var_name']
        })
    try:
        new_problem, new_problem_body = rule.eval(problem)
    except:
        return jsonify({
            'flag': False,
            'reason': "Substitution failed."
        })
    log = {
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
    }
    return jsonify({
            'flag': True,
            'log': log
        })

@app.route("/api/integral-substitution2", methods=['POST'])
def integral_substitution2():
    data = json.loads(request.get_data().decode('utf-8'))
    try:
        expr = integral.parser.parse_expr(data['expr'])
    except:
        return jsonify({
            'flag': False,
            'reason': "%s is not a valid expression" % data['expr']
        })
    rule = integral.rules.Substitution2(data['var_name'], expr)
    
    problem = integral.parser.parse_expr(data['problem'])
    new_problem = rule.eval(problem)
    log = jsonify({
        'text': str(new_problem),
        'latex': integral.latex.convert_expr(new_problem),
        'reason': "Substitution inverse",
        'location': data['location'],
        'params': {
            'g': str(expr),
            'var_name': str(data['var_name']),
            "a": str(new_problem.lower),
            "b": str(new_problem.upper)
        },
        '_latex_reason': "Substitute \\(%s\\) for \\(%s\\)" % (
            integral.latex.convert_expr(integral.parser.parse_expr(problem.var)), integral.latex.convert_expr(expr)
        )
    })
    return jsonify({
        'flag': True,
        'log': log
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
            new_trig_set = tuple(integral.expr.trig_transform(select, problem.var))
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
        if expand_multinomial(integral.expr.sympy_style(new_expr.normalize()).simplify()) != expand_multinomial(integral.expr.sympy_style(old_expr.normalize()).simplify()) or new_expr.findVar()[0].name != problem.var:
            return jsonify({
                'flag': False
            })
        new_problem = integral.expr.Integral(problem.var, problem.lower, problem.upper, problem.body.replace_expr(location, new_expr))
        if old_expr.ty == integral.expr.OP and old_expr.op == "/" or\
            old_expr.ty == integral.expr.OP and old_expr.op == "*" and\
                old_expr.args[1].ty == integral.expr.OP and old_expr.args[1].op == "^" and\
                    old_expr.args[1].args[1] == integral.expr.Const(-1):
            denom = old_expr.args[1]
            return jsonify({
                'flag': True,
                'text': str(new_problem),
                'latex': integral.latex.convert_expr(new_problem),
                'reason': "Rewrite fraction",
                '_latex_reason': "Rewrite \\(%s\\) to \\(%s\\)"%(integral.latex.convert_expr(old_expr),
                                                                integral.latex.convert_expr(new_expr)),
                'params': {
                    'rhs': data['new_expr'],
                    'denom': str(denom)
                },
                "location": data['absolute_location']
             })
        else:
            return jsonify({
                'flag': True,
                'text': str(new_problem),
                'latex': integral.latex.convert_expr(new_problem),
                'reason': "Rewrite fraction",
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
    assert  integral.parser.parse_expr(problem.var) not in point.findVar()
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
    try:
        parts_u = integral.parser.parse_expr(data['parts_u'])
    except:
        return jsonify({
            "flag": False,
            "reason": "%s is not valid expression." % data['parts_u']
        })
    try:
        parts_v = integral.parser.parse_expr(data['parts_v'])
    except:
        print("wow")
        return jsonify({
            "flag": False,
            "reason": "%s is not valid expression." % data['parts_v']
        })
    rule = integral.rules.IntegrationByParts(parts_u, parts_v)
    problem = integral.parser.parse_expr(data['problem'])
    try:
        new_problem = rule.eval(problem)
    except NotImplementedError as e:
        return jsonify({
            "flag": False,
            "reason": str(e)
        })
    log = {
        'text': str(new_problem),
        'latex': integral.latex.convert_expr(new_problem),
        'reason': "Integrate by parts",
        'params': {
            'parts_u': data['parts_u'],
            'parts_v': data['parts_v'],
        },
        '_latex_reason': "Integrate by parts, \\(u = %s, v = %s\\)" % (
            integral.latex.convert_expr(parts_u), integral.latex.convert_expr(parts_v)
        ),
        'location': data['location']
    }
    return jsonify({
        "flag": True,
        "log": log
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
    try:
        new_problem = rule.eval(problem)
    except:
        return jsonify({
            'flag': False,
            'reason': "Can't do divison now."
        })
    rhs = new_problem.body
    location = data['location']
    if location:
        location += ".0"
    else:
        location = "0"
    return jsonify({
        'flag': True,
        'text': str(new_problem),
        'latex': integral.latex.convert_expr(new_problem),
        'params': {
            'rhs': str(rhs)
        },
        'reason': "Rewrite fraction",
        "location": location
    })

@app.route("/api/integral-save-file", methods=['POST'])
def integral_save_file():
    data = json.loads(request.get_data().decode('utf-8'))
    file_name = "integral/examples/%s" % data['filename']
    with open(file_name, 'w', encoding='utf-8') as f:
        json.dump({"content": data['content']}, f, indent=4, ensure_ascii=False, sort_keys=True)

    return jsonify({
        'status': 'success'
    })

@app.route("/api/integral-slagle", methods=['POST'])
def integral_slagle():
    data = json.loads(request.get_data().decode('utf-8'))
    problem = data['problem']
    t = 20
    # limit slagle only run 60 seconds 
    limit_bfs = slagle.timeout(t)(slagle.bfs)
    try:
        node = limit_bfs(slagle.OrNode(problem))
        new_problem = node.compute_value()
        trace = node.trace()
        final_simp = trace[-1]
        last_expr = new_problem.normalize().normalize_constant()
        last_step = {
            'text': str(last_expr),
            'latex': integral.latex.convert_expr(last_expr),
            'reason': 'Simplification'
        }
        t = [i.info() for i in trace]
        t.append(last_step)
        return json.dumps(t)
    except:
        new_problem = integral.parser.parse_expr(problem)
        return json.dumps([{
            'text': str(new_problem),
            'latex': integral.latex.convert_expr(new_problem),
            'reason': "By Slagle algorithm"
        }])
    