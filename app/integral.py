# Author: Runqing Xu, Bohua Zhan

"""API for computing integrals."""

import json
from flask import request
from flask.json import jsonify
import pathlib
import os
import integral
from logic import basic
from integral import slagle
from integral import proof
from integral import compstate
from app.app import app

basic.load_theory('interval_arith')

dirname = os.path.dirname(__file__)

@app.route("/api/integral-load-file-list", methods=['POST'])
def integral_load_file_list():
    json_files = []
    for res in pathlib.Path('../integral/examples').rglob('*.json'):
        json_files.append(str(res.relative_to('../integral/examples')))
    return jsonify({
        'file_list': tuple(json_files)
    })

@app.route("/api/integral-open-file", methods=['POST'])
def integral_open_file():
    data = json.loads(request.get_data().decode('utf-8'))
    file_name = os.path.join(dirname, "../integral/examples/" + data['filename'])
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
    return jsonify({
        "status": "ok",
        "item": st.export(),
    })

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
        # For each Fu's rule, try to apply
        for rule_name, (rule_fun, _) in integral.expr.trigFun.items():
            try:
                sympy_result = rule_fun(integral.expr.sympy_style(e))
                new_e = integral.expr.holpy_style(sympy_result)
                if new_e != e:
                    results.append({
                        "rule_name": rule_name,
                        "new_e": str(new_e),
                        "latex_new_e": integral.latex.convert_expr(new_e)
                    })
            except Exception as e:
                pass
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
    st = compstate.parse_state(data['name'], data['problem'], data['items'])
    eq = integral.parser.parse_expr(data['eq'])
    conds = integral.conditions.Conditions(integral.parser.parse_expr(cond) for cond in data['conds'])
    st.add_item(compstate.FuncDef(eq, conds=conds))
    return jsonify({
        "status": "ok",
        "state": st.export(),
    })

@app.route("/api/add-goal", methods=["POST"])
def add_goal():
    data = json.loads(request.get_data().decode('UTF-8'))
    st = compstate.parse_state(data['name'], data['problem'], data['items'])
    goal = integral.parser.parse_expr(data['goal'])
    conds = integral.conditions.Conditions(integral.parser.parse_expr(cond) for cond in data['conds'])
    st.add_item(compstate.Goal(goal, conds=conds))
    return jsonify({
        "status": "ok",
        "state": st.export(),
        "selected_item": str(compstate.Label([len(st.items)-1])),
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
    st = compstate.parse_state(data['name'], data['problem'], data['items'])
    label = compstate.Label(data['selected_item'])
    induct_var = data['induct_var']
    proof = st.get_by_label(label).proof_by_induction(induct_var)
    proof.base_case.proof_by_calculation()
    proof.induct_case.proof_by_calculation()
    return jsonify({
        "status": "ok",
        "state": st.export(),
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
    assert len(func_defs) == 1, "expand_definition: unexpected number of definitions"
    subitem = item.get_by_label(label)
    if isinstance(subitem, (compstate.CalculationStep, compstate.Calculation)):
        rule = integral.rules.OnSubterm(integral.rules.ExpandDefinition(func_defs[0]))
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
