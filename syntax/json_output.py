# Author: Bohua Zhan

"""Output theory to JSON file."""

import json

from kernel.term import get_vars
from logic import basic
from syntax import printer

class JSONTheory():
    def __init__(self, name, imports, description):
        self.name = name
        self.imports = imports
        self.thy = basic.loadImportedTheory(imports)
        self.description = description
        self.content = []

    def add_theorem(self, name, th, prf):
        """Add a theorem with proof to the file."""

        assert len(th.assums) == 0, "add_theorem"
        vars = dict((v.name, str(v.T)) for v in get_vars(th.concl))
        data = {
            "name": name,
            "ty": "thm",
            "prop": printer.print_term(self.thy, th.concl),
            "vars": vars,
            "num_gaps": 0,
            "proof": sum([printer.export_proof_item(self.thy, item, unicode=False, highlight=False)
                          for item in prf.items], []),
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
