# Author: Runqing Xu, Bohua Zhan

"""API for computing integrals."""

import json
from flask import request
from flask.json import jsonify
import pathlib
import os
import integral
from integral import compstate
from app.app import app

dirname = os.path.dirname(__file__)

@app.route("/api/integral-load-book-content", methods=['POST'])
def integral_load_book_content():
    data = json.loads(request.get_data().decode('utf-8'))
    file_name = os.path.join(dirname, "../integral/examples/" + data['bookname'] + '.json')

    # Load raw data
    with open(file_name, 'r', encoding='utf-8') as f:
        f_data = json.load(f)

    # For each expression, load its latex form
    print('here')
    for item in f_data['content']:
        # Expressions in item
        if 'expr' in item:
            e = integral.parser.parse_expr(item['expr'])
            latex_str = integral.latex.convert_expr(e)
            item['latex_str'] = latex_str
        # Conditions in item
        if 'conds' in item:
            latex_conds = []
            for cond_str in item['conds']:
                cond = integral.parser.parse_expr(cond_str)
                latex_conds.append(integral.latex.convert_expr(cond))
            item['latex_conds'] = latex_conds
        # Table elements
        if item['type'] == 'table':
            new_table = list()
            funcexpr = integral.expr.Fun(item['name'], integral.expr.Var('x'))
            item['funcexpr'] = integral.latex.convert_expr(funcexpr)
            for x, y in item['table'].items():
                x = integral.parser.parse_expr(x)
                y = integral.parser.parse_expr(y)
                new_table.append({
                    'x': integral.latex.convert_expr(x),
                    'y': integral.latex.convert_expr(y)
                })
            item['latex_table'] = new_table

    return jsonify(f_data)

@app.route("/api/integral-load-file-list", methods=['POST'])
def integral_load_file_list():
    json_files = []
    for res in pathlib.Path('../integral/examples').rglob('*.json'):
        # remove .json
        json_files.append(str(res.relative_to('../integral/examples'))[:-5])
    return jsonify({
        'file_list': tuple(json_files)
    })

@app.route("/api/integral-open-file", methods=['POST'])
def integral_open_file():
    data = json.loads(request.get_data().decode('utf-8'))
    file_name = os.path.join(dirname, "../integral/examples/" + data['filename'] + '.json')
    with open(file_name, 'r', encoding='utf-8') as f:
        f_data = json.load(f)

    for item in f_data['content']:
        if 'problem' in item:
            problem = integral.parser.parse_expr(item['problem'])
            item['_problem_latex'] = integral.latex.convert_expr(problem)
        
    return jsonify(f_data)

@app.route("/api/integral-save-file", methods=['POST'])
def integral_save_file():
    data = json.loads(request.get_data().decode('utf-8'))
    file_name = os.path.join(dirname, "../integral/examples/" + data['filename'])
    with open(file_name, 'w', encoding='utf-8') as f:
        json.dump({"content": data['content']}, f, indent=4, ensure_ascii=False, sort_keys=True)

    return jsonify({
        'status': 'success'
    })

@app.route("/api/clear-item", methods=['POST'])
def clear_item():
    data = json.loads(request.get_data().decode('UTF-8'))
    st = compstate.parse_item(data['item'])
    label = compstate.Label(data['selected_item'])
    st.get_by_label(label).clear()
    res = {
        "status": "ok",
        "item": st.export(),
    }
    if isinstance(st, (compstate.Calculation)):
        if len(st.steps) == 0:
            res['selected_item'] = str(compstate.Label([]))
        else:
            res['selected_item'] = str(compstate.Label([len(st.steps) - 1]))
    return jsonify(res)

@app.route("/api/query-expr", methods=['POST'])
def query_expr():
    data = json.loads(request.get_data().decode('UTF-8'))
    try:
        e = integral.parser.parse_expr(data['expr'])
        return jsonify({
            "status": "ok",
            "latex_expr": integral.latex.convert_expr(e)
        })
    except Exception as e:
        return jsonify({
            "status": "fail",
            "exception": str(e)
        })

@app.route("/api/query-integral", methods=['POST'])
def query_integral():
    data = json.loads(request.get_data().decode('UTF-8'))
    item = compstate.parse_item(data['item'])
    label = compstate.Label(data['selected_item'])
    subitem = item.get_by_label(label)
    if isinstance(subitem, compstate.CalculationStep):
        integrals = subitem.res.separate_integral()
    elif isinstance(subitem, compstate.Calculation):
        integrals = subitem.start.separate_integral()
    else:
        return jsonify({
            "status": "error",
            "msg": "Selected item is not part of a calculation."
        })
    
    res = []
    for e, loc in integrals:
        res.append({
            "expr": str(e),
            "var_name": e.var,
            "body": str(e.body),
            "latex_expr": integral.latex.convert_expr(e),
            "latex_body": integral.latex.convert_expr(e.body),
            "loc": str(loc)
        })
    return jsonify({
        "status": "ok",
        "integrals": res
    })

@app.route("/api/query-trig-identity", methods=['POST'])
def query_trig_identity():
    data = json.loads(request.get_data().decode('UTF-8'))
    try:
        e = integral.parser.parse_expr(data['expr'])
        results = []
        return jsonify({
            "status": "ok",
            "latex_expr": integral.latex.convert_expr(e),
            "results": results
        })
    except Exception as e:
        return jsonify({
            "status": "fail",
            "exception": str(e)
        })

@app.route("/api/add-function-definition", methods=['POST'])
def add_function_definition():
    data = json.loads(request.get_data().decode('UTF-8'))
    file = compstate.parse_file(data['name'], data['problem'], data['items'])
    eq = integral.parser.parse_expr(data['eq'])
    conds = integral.conditions.Conditions(integral.parser.parse_expr(cond) for cond in data['conds'])
    file.add_item(compstate.FuncDef(eq, conds=conds))
    return jsonify({
        "status": "ok",
        "state": file.export(),
    })

@app.route("/api/add-goal", methods=["POST"])
def add_goal():
    data = json.loads(request.get_data().decode('UTF-8'))
    file = compstate.parse_file(data['name'], data['problem'], data['items'])
    goal = integral.parser.parse_expr(data['goal'])
    conds = integral.conditions.Conditions(integral.parser.parse_expr(cond) for cond in data['conds'])
    file.add_item(compstate.Goal(goal, conds=conds))
    return jsonify({
        "status": "ok",
        "state": file.export(),
        "selected_item": str(compstate.Label([len(file.items)-1])),
    })

@app.route("/api/proof-by-calculation", methods=["POST"])
def proof_by_calculation():
    data = json.loads(request.get_data().decode('UTF-8'))
    item = compstate.parse_item(data['item'])
    label = compstate.Label(data['selected_item'])
    subitem = item.get_by_label(label)
    if isinstance(subitem, compstate.Goal):
        subitem.proof_by_calculation()
        return jsonify({
            "status": "ok",
            "item": item.export(),
            "selected_item": str(compstate.Label(label.data + [0]))
        })
    else:
        return jsonify({
            "status": "error",
            "msg": "Selected item is not a goal."
        })

@app.route("/api/proof-by-induction", methods=["POST"])
def proof_by_induction():
    data = json.loads(request.get_data().decode('UTF-8'))
    item = compstate.parse_item(data['item'])
    label = compstate.Label(data['selected_item'])
    subitem = item.get_by_label(label)
    induct_var = data['induct_var']
    proof = subitem.proof_by_induction(induct_var)
    proof.base_case.proof_by_calculation()
    proof.induct_case.proof_by_calculation()
    return jsonify({
        "status": "ok",
        "item": item.export(),
        "selected_item": str(compstate.Label(label.data + [0]))
    })

@app.route("/api/expand-definition", methods=["POST"])
def expand_definition():
    data = json.loads(request.get_data().decode('UTF-8'))
    item = compstate.parse_item(data['item'])
    prev_items = []
    for prev_item in data['prev_items']:
        prev_items.append(compstate.parse_item(prev_item))
    label = compstate.Label(data['selected_item'])
    func_defs = []
    for prev_item in prev_items:
        if isinstance(prev_item, compstate.FuncDef):
            func_defs.append(prev_item.eq)
    # assert len(func_defs) == 1, "expand_definition: unexpected number of definitions"
    subitem = item.get_by_label(label)
    if isinstance(subitem, (compstate.CalculationStep, compstate.Calculation)):
        if isinstance(subitem, compstate.Calculation):
            ex = subitem.start
        else:
            ex = subitem.res
        for func_def in func_defs:
            if ex.has_func(func_def.lhs.func_name):
                rule = integral.rules.OnSubterm(integral.rules.ExpandDefinition(func_def))
                subitem.perform_rule(rule)
        return jsonify({
            "status": "ok",
            "item": item.export(),
            "selected_item": str(compstate.get_next_step_label(subitem, label))
        })
    else:
        return jsonify({
            "status": "error",
            "msg": "Selected item is not part of a calculation."
        })

@app.route("/api/solve-equation", methods=["POST"])
def integral_solve_equation():
    data = json.loads(request.get_data().decode('UTF-8'))
    item = compstate.parse_item(data['item'])
    label = compstate.Label(data['selected_item'])
    facts = data['selected_facts']
    if len(facts) != 1:
        return jsonify({
            "status": "error",
            "msg": "Exactly one fact must be selected"
        })
    lhs: integral.expr.Expr
    for fact_label in facts:
        fact = item.get_by_label(integral.compstate.Label(fact_label))
        if isinstance(fact, compstate.CalculationStep):
            lhs = fact.res
        elif isinstance(fact, compstate.Calculation):
            lhs = fact.start
        else:
            return jsonify({
                "status": "error",
                "msg": "Selected fact is not part of a calculation."
            })
    
    subitem = item.get_by_label(label)
    if isinstance(subitem, (compstate.CalculationStep, compstate.Calculation)):
        rule = integral.rules.IntegrateByEquation(lhs)
        subitem.perform_rule(rule)
        return jsonify({
            "status": "ok",
            "item": item.export(),
            "selected_item": str(compstate.get_next_step_label(subitem, label))
        })
    else:
        return jsonify({
            "status": "error",
            "msg": "Selected item is not part of a calculation."
        })

@app.route("/api/perform-step", methods=["POST"])
def integral_perform_step():
    data = json.loads(request.get_data().decode('UTF-8'))
    item = compstate.parse_item(data['item'])
    label = compstate.Label(data['selected_item'])
    rule = compstate.parse_rule(data['rule'])
    subitem = item.get_by_label(label)
    if isinstance(subitem, (compstate.CalculationStep, compstate.Calculation)):
        subitem.perform_rule(rule)
    elif isinstance(subitem, compstate.RewriteGoalProof):
        subitem.begin.perform_rule(rule)
    else:
        return jsonify({
            "status": "error",
            "msg": "Selected item is not part of a calculation."
        })
    return jsonify({
        "status": "ok",
        "item": item.export(),
        "selected_item": str(compstate.get_next_step_label(subitem, label))
    })

@app.route("/api/query-theorems", methods=["POST"])
def integral_query_theorems():
    data = json.loads(request.get_data().decode('UTF-8'))
    item = compstate.parse_item(data['item'])
    prev_items = []
    for prev_item in data['prev_items']:
        prev_items.append(compstate.parse_item(prev_item))
    label = compstate.Label(data['selected_item'])
    subitem = item.get_by_label(label)
    eqs = []
    for prev_item in prev_items:
        for eq in prev_item.get_facts():
            if eq.is_equals():
                eqs.append({
                    'eq': str(eq),
                    'latex_eq': integral.latex.convert_expr(eq)
                })
    return jsonify({
        "status": "ok",
        "theorems": eqs
    })

@app.route("/api/apply-inductive-hyp", methods=["POST"])
def integral_apply_inductive_hyp():
    data = json.loads(request.get_data().decode('UTF-8'))
    item = compstate.parse_item(data['item'])
    label = compstate.Label(data['selected_item'])
    subitem = item.get_by_label(label)
    
    if not isinstance(item, compstate.Goal) or not isinstance(item.proof, compstate.InductionProof):
        # TODO: search for induction more generally
        return jsonify({
            "status": "error",
            "msg": "Not part of an induction proof"
        })
    if not isinstance(subitem, (compstate.Calculation, compstate.CalculationStep)):
        return jsonify({
            "status": "error",
            "msg": "Selected item is not part of a calculation."
        })

    rule = integral.rules.OnSubterm(integral.rules.ApplyInductHyp(item.goal))
    subitem.perform_rule(rule)
    return jsonify({
        "status": "ok",
        "item": item.export(),
        "selected_item": str(compstate.get_next_step_label(subitem, label))
    })

@app.route("/api/integral-apply-theorem", methods=["POST"])
def integral_apply_theorem():
    data = json.loads(request.get_data().decode('UTF-8'))
    item = compstate.parse_item(data['item'])
    label = compstate.Label(data['selected_item'])
    subitem = item.get_by_label(label)
    eq = integral.parser.parse_expr(data['theorem'])
    rule = integral.rules.ApplyEquation(eq)
    e: integral.expr.Expr
    conds: integral.conditions.Conditions
    if isinstance(subitem, compstate.Calculation):
        e = subitem.start
        conds = subitem.conds
    elif isinstance(subitem, compstate.CalculationStep):
        e = subitem.res
        conds = subitem.parent.conds
    else:
        return jsonify({
            "status": "error",
            "msg": "Selected item is not part of a calculation."
        })
    
    new_e = rule.eval(e, conds=conds)
    if new_e == e:
        query_vars = []
        for var in eq.get_vars():
            query_vars.append({"var": var, "expr": ""})
        return jsonify({
            "status": "query",
            "query_vars": query_vars
        })
    else:
        subitem.perform_rule(rule)
        return jsonify({
            "status": "ok",
            "item": item.export(),
            "selected_item": str(compstate.get_next_step_label(subitem, label))
        })

@app.route("/api/query-last-expr", methods=["POST"])
def query_last_expr():
    # query selected expression by given label
    data = json.loads(request.get_data().decode('UTF-8'))
    item = compstate.parse_item(data['item'])
    label = compstate.Label(data['selected_item'])
    subitem = item.get_by_label(label)
    if isinstance(subitem, (compstate.CalculationStep,compstate.Calculation)):
        res = subitem.res if isinstance(subitem, compstate.CalculationStep) else subitem.start
    elif isinstance(subitem, compstate.RewriteGoalProof):
        res = subitem.begin.start
    else:
        return jsonify({
            "status": "error",
        })
    return jsonify({
        "last_expr": str(res),
        "latex_expr": integral.latex.convert_expr(res),
        "status": "ok",
    })


@app.route("/api/query-integrate-both-side", methods=['POST'])
def query_integrate_both_side():
    fail = jsonify({
            "status": "error",
            "msg": "Selected item is not part of a calculation."
        })
    data = json.loads(request.get_data().decode('UTF-8'))
    item = compstate.parse_item(data['item'])
    label = compstate.Label(data['selected_item'])
    subitem = item.get_by_label(label)
    integral_var = data['integral_var']
    if isinstance(subitem, compstate.CalculationStep):
        e = subitem.res
    elif isinstance(subitem, compstate.Calculation):
        e = subitem.start
    elif isinstance(subitem, compstate.RewriteGoalProof):
        e = subitem.begin.start
    else:
        return fail
    if not e.is_equals():
        return fail
    left_skolem = right_skolem = False
    if e.lhs.is_deriv() and e.lhs.var == integral_var:
        left_skolem = True
    if e.rhs.is_deriv() and e.rhs.var == integral_var:
        right_skolem = True
    return jsonify({
        "status": "ok",
        "left_skolem": left_skolem,
        "right_skolem": right_skolem,
    })