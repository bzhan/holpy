# Author: Bohua Zhan

"""Output theory to JSON file."""

import json

from kernel.term import get_vars
from kernel import proof
from logic import basic
from syntax import printer

class JSONTheory():
    def __init__(self, name, imports, description):
        self.name = name
        self.imports = imports
        self.thy = basic.load_imported_theory(imports)
        self.description = description
        self.content = []

    def export_proof_json(self, item):
        str_th = printer.print_thm(self.thy, item.th) if item.th else ""
        str_args = printer.print_str_args(self.thy, item.rule, item.args)
        res = {
            'id': proof.print_id(item.id),
            'th': str_th,
            'rule': item.rule,
            'args': str_args,
            'prevs': [proof.print_id(prev) for prev in item.prevs]
        }
        if item.subproof:
            return [res] + sum([self.export_proof_json(i) for i in item.subproof.items], [])
        else:
            return [res]

    def add_theorem(self, name, th, prf):
        """Add a theorem with proof to the file."""

        assert len(th.hyps) == 0, "add_theorem"
        vars = dict((v.name, str(v.T)) for v in get_vars(th.prop))
        data = {
            "name": name,
            "ty": "thm",
            "prop": printer.print_term(self.thy, th.prop),
            "vars": vars,
            "num_gaps": 0,
            "proof": sum([self.export_proof_json(item) for item in prf.items], []),
        }
        self.content.append(data)

    def export_json(self):
        data = {
            "name": self.name,
            "imports": self.imports,
            "description": self.description,
            "content": self.content
        }
        with open('library/' + self.name + '.json', 'w+', encoding='utf-8') as f:
            json.dump(data, f, indent=4, ensure_ascii=False, sort_keys=True)
