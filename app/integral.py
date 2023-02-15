# Author: Runqing Xu, Bohua Zhan

"""API for computing integrals."""

import json
from flask import request
from flask.json import jsonify
import os

import integral
from integral import compstate
from app.app import app

dirname = os.path.dirname(__file__)

@app.route("/api/integral-load-book-list", methods=['POST'])
def integral_load_book_list():
    # Load book list from index.json
    file_name = os.path.join(dirname, "../integral/examples/index.json")

    with open(file_name, 'r', encoding='utf-8') as f:
        f_data = json.load(f)

    return jsonify(f_data)

@app.route("/api/integral-load-book-content", methods=['POST'])
def integral_load_book_content():
    data = json.loads(request.get_data().decode('utf-8'))
    file_name = os.path.join(dirname, "../integral/examples/" + data['bookname'] + '.json')

    # Load raw data
    with open(file_name, 'r', encoding='utf-8') as f:
        f_data = json.load(f)

    # For each expression, load its latex form
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
    book_name = data['book']
    filename = data['file']
    cur_id = data['cur_id']
    file = compstate.CompFile(book_name, filename)
    for item in data['content']:
        file.add_item(compstate.parse_item(file, item))
    label = compstate.Label(data['selected_item'])
    st: compstate.StateItem = file.content[cur_id]
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
    book_name = data['book']
    filename = data['file']
    cur_id = data['cur_id']
    file = compstate.CompFile(book_name, filename)
    for item in data['content']:
        file.add_item(compstate.parse_item(file, item))
    label = compstate.Label(data['selected_item'])
    st: compstate.StateItem = file.content[cur_id]
    subitem = st.get_by_label(label)
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

@app.route("/api/query-latex-expr", methods=['POST'])
def query_latex_expr():
    """Find latex form of an expression."""
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

@app.route("/api/query-identities", methods=['POST'])
def query_identities():
    """Find list of identity rewerites for an expression."""
    data = json.loads(request.get_data().decode('UTF-8'))
    book_name = data['book']
    filename = data['file']
    cur_id = data['cur_id']
    file = compstate.CompFile(book_name, filename)
    for item in data['content']:
        file.add_item(compstate.parse_item(file, item))
    label = compstate.Label(data['selected_item'])
    st: compstate.StateItem = file.content[cur_id]
    subitem = st.get_by_label(label)
    try:
        e = integral.parser.parse_expr(data['expr'])
        results = integral.rules.ApplyIdentity.search(e, subitem.ctx)
        json_results = []
        for res in results:
            json_results.append({
                "res": str(res),
                "latex_res": integral.latex.convert_expr(res)
            })
        return jsonify({
            "status": "ok",
            "latex_expr": integral.latex.convert_expr(e),
            "results": json_results
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
    book_name = data['book']
    filename = data['file']
    cur_id = data['cur_id']
    file = compstate.CompFile(book_name, filename)
    for item in data['content']:
        file.add_item(compstate.parse_item(file, item))
    label = compstate.Label(data['selected_item'])
    st: compstate.StateItem = file.content[cur_id]
    subitem = st.get_by_label(label)
    if isinstance(subitem, (compstate.CalculationStep, compstate.Calculation)):
        if isinstance(subitem, compstate.Calculation):
            e = subitem.start
        else:
            e = subitem.res
        results = integral.rules.ExpandDefinition.search(e, subitem.ctx)
        if len(results) == 1:
            sube, loc = results[0]
            assert sube.is_fun()
            rule = integral.rules.ExpandDefinition(sube.func_name)
            if loc.data:
                rule = integral.rules.OnLocation(rule, loc)
            subitem.perform_rule(rule)
            return jsonify({
                "status": "ok",
                "item": st.export(),
                "selected_item": str(compstate.get_next_step_label(subitem, label))
            })
        else:
            return jsonify({
                "status": "choose",
                "item": st.export(),
                "selected_item": str(compstate.get_next_step_label(subitem, label))
            })
    else:
        return jsonify({
            "status": "error",
            "msg": "Selected item is not part of a calculation."
        })

@app.route("/api/fold-definition", methods=["POST"])
def fold_definition():
    data = json.loads(request.get_data().decode('UTF-8'))
    book_name = data['book']
    filename = data['file']
    cur_id = data['cur_id']
    file = compstate.CompFile(book_name, filename)
    for item in data['content']:
        file.add_item(compstate.parse_item(file, item))
    label = compstate.Label(data['selected_item'])
    st: compstate.StateItem = file.content[cur_id]
    subitem = st.get_by_label(label)
    if isinstance(subitem, (compstate.CalculationStep, compstate.Calculation)):
        if isinstance(subitem, compstate.Calculation):
            e = subitem.start
        else:
            e = subitem.res
        results = integral.rules.FoldDefinition.search(e, subitem.ctx)
        if len(results) == 1:
            _, loc, func_name = results[0]
            rule = integral.rules.FoldDefinition(func_name)
            if loc.data:
                rule = integral.rules.OnLocation(rule, loc)
            subitem.perform_rule(rule)
            return jsonify({
                "status": "ok",
                "item": st.export(),
                "selected_item": str(compstate.get_next_step_label(subitem, label))
            })
        else:
            return jsonify({
                "status": "choose",
                "item": st.export(),
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
    book_name = data['book']
    filename = data['file']
    cur_id = data['cur_id']
    file = compstate.CompFile(book_name, filename)
    for item in data['content']:
        file.add_item(compstate.parse_item(file, item))
    label = compstate.Label(data['selected_item'])
    st: compstate.StateItem = file.content[cur_id]
    subitem = st.get_by_label(label)
    facts = data['selected_facts']
    if len(facts) != 1:
        return jsonify({
            "status": "error",
            "msg": "Exactly one fact must be selected"
        })
    lhs: integral.expr.Expr
    for fact_label in facts:
        fact = st.get_by_label(integral.compstate.Label(fact_label))
        if isinstance(fact, compstate.CalculationStep):
            lhs = fact.res
        elif isinstance(fact, compstate.Calculation):
            lhs = fact.start
        else:
            return jsonify({
                "status": "error",
                "msg": "Selected fact is not part of a calculation."
            })
    
    if isinstance(subitem, (compstate.CalculationStep, compstate.Calculation)):
        rule = integral.rules.IntegrateByEquation(lhs)
        subitem.perform_rule(rule)
        return jsonify({
            "status": "ok",
            "item": st.export(),
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
    book_name = data['book']
    filename = data['file']
    cur_id = data['cur_id']
    file = compstate.CompFile(book_name, filename)
    for item in data['content']:
        file.add_item(compstate.parse_item(file, item))
    label = compstate.Label(data['selected_item'])
    st: compstate.StateItem = file.content[cur_id]
    rule = compstate.parse_rule(data['rule'])
    if isinstance(rule, integral.rules.ApplyInductHyp):
        rule = integral.rules.OnSubterm(rule)
    subitem = st.get_by_label(label)
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
        "item": st.export(),
        "selected_item": str(compstate.get_next_step_label(subitem, label))
    })

@app.route("/api/query-theorems", methods=["POST"])
def integral_query_theorems():
    data = json.loads(request.get_data().decode('UTF-8'))
    book_name = data['book']
    filename = data['file']
    cur_id = data['cur_id']
    file = compstate.CompFile(book_name, filename)
    for item in data['content']:
        file.add_item(compstate.parse_item(file, item))
    eqs = []
    for prev_item in file.content[:cur_id]:
        for eq in prev_item.get_facts():
            eqs.append({
                'eq': str(eq),
                'latex_eq': integral.latex.convert_expr(eq)
            })
    return jsonify({
        "status": "ok",
        "theorems": eqs
    })

@app.route("/api/query-vars", methods=["POST"])
def integral_query_vars():
    data = json.loads(request.get_data().decode('UTF-8'))
    book_name = data['book']
    filename = data['file']
    cur_id = data['cur_id']
    file = compstate.CompFile(book_name, filename)
    for item in data['content']:
        file.add_item(compstate.parse_item(file, item))
    label = compstate.Label(data['selected_item'])
    st: compstate.StateItem = file.content[cur_id]
    subitem = st.get_by_label(label)
    if isinstance(subitem, (compstate.CalculationStep, compstate.Calculation)):
        res = subitem.res if isinstance(subitem, compstate.CalculationStep) else subitem.start
    elif isinstance(subitem, compstate.RewriteGoalProof):
        res = subitem.begin.start
    else:
        return jsonify({
            "status": "error",
        })
    vars = list(res.get_vars())
    query_vars = []
    for var in vars:
        query_vars.append({'var': var, 'expr': ""})
    return jsonify({
        "status": "ok",
        "query_vars": query_vars
    })

@app.route("/api/query-last-expr", methods=["POST"])
def integral_query_last_expr():
    # Query selected expression according to label
    data = json.loads(request.get_data().decode('UTF-8'))
    book_name = data['book']
    filename = data['file']
    cur_id = data['cur_id']
    file = compstate.CompFile(book_name, filename)
    for item in data['content']:
        file.add_item(compstate.parse_item(file, item))
    label = compstate.Label(data['selected_item'])
    st: compstate.StateItem = file.content[cur_id]
    subitem = st.get_by_label(label)
    if isinstance(subitem, (compstate.CalculationStep, compstate.Calculation)):
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
