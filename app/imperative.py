# Author: Wenfan Zhou, Bohua Zhan

"""API for program verification."""

import json
from flask import request
from flask.json import jsonify

from logic import basic
from imperative import parser2
from imperative import imp  # for the imp methods
from syntax import printer
from prover import z3wrapper
from app.app import app


@app.route('/api/get-program-file', methods = ['POST'])
def get_program_file():
    """Load a json file for program verification.
    
    Input:
    * file_name: name of the file (under imperative/examples).

    Returns:
    * file_data: content of the file.

    """
    data = json.loads(request.get_data().decode("utf-8"))
    file_name = data['file_name']
    thy = basic.load_theory('hoare')
    path = 'imperative/examples/' + file_name + '.json'
    with open(path, 'r', encoding='utf-8') as f:
        file_data = json.load(f)

    for i, item in enumerate(file_data['content']):
        if item['ty'] == 'vcg':
            program = parser2.com_parser.parse(item['com']).print_com(item['vars'])
            item['com'] = '\n'.join(program)

    return jsonify({'file_data': file_data['content']})

@app.route('/api/program-verify', methods=['POST'])
def verify():
    """Verify a program by generating verification conditions,
    and attempt to solve the conditions using SMT.

    """
    data = json.loads(request.get_data().decode("utf-8"))
    thy = basic.load_theory('hoare')
    pre = parser2.cond_parser.parse(data['pre'])
    post = parser2.cond_parser.parse(data['post'])
    com = parser2.com_parser.parse(data['com'])
    com.pre = [pre]
    com.compute_wp(post)
    lines = com.get_lines(data['vars'])

    for line in lines:
        if line['ty'] == 'vc':
            vc_hol = line['prop']
            line['prop'] = printer.print_term(thy, line['prop'])
            line['smt'] = z3wrapper.solve(thy, vc_hol)

    return jsonify({
        'lines': lines,
    })

@app.route('/api/save-program-proof', methods=['POST'])
def save_program_proof():
    """Save a proof for program verification.
    
    """
    data = json.loads(request.get_data().decode("utf-8"))

    file_name = data['file_name']
    path = 'imperative/examples/' + file_name + '.json'
    with open(path, 'r', encoding='utf-8') as f:
        file_data = json.load(f)

    cur_index = data['index']
    proof = data['proof']
    file_data['content'][cur_index]['proof'] = proof

    with open(path, 'w', encoding='utf-8') as f:
        json.dump(file_data, f, indent=4, ensure_ascii=False, sort_keys=True)

    return jsonify({})
