## holpy

Implementation of higher-order logic in Python.

This project is developed under Python 3.

Required packages: see requirements.txt.

Directory structure:

* [`kernel`](kernel/): kernel for higher-order logic.
  * [`type`](kernel/type.py): datatype for HOL types.
  * [`term`](kernel/term.py): datatype for HOL terms.
  * [`thm`](kernel/thm.py): datatype for HOL theorems, including list of basic derivations.
  * [`proof`](kernel/proof.py): linear representation of a proof, consisting of a list of instructions to the kernel.
  * [`macro`](kernel/macro.py): macros as user-defined proof methods.
  * [`theory`](kernel/theory.py): theory state, containing signature for types and constants, and list of axioms and theorems.
  * [`extension`](kernel/extension.py): types of extensions to a theory.
  * [`report`](kernel/report.py): statistics and debugging information for checking a theory extension.

* [`logic`](logic/): base logic and standard automation.
  * [`matcher`](logic/matcher.py): matching of terms.
  * [`proofterm`](logic/proofterm.py): tree-like representation of a proof. Used for convenient construction of proofs, and can be transformed to the linear representation.
  * [`conv`](logic/conv.py): conversions.
  * [`operator`](logic/operator.py): data for unary and binary operators.
  * [`logic`](logic/logic.py): utilities for logic.
  * [`nat`](logic/nat.py): utilities for natural numbers.
  * [`induct`](logic/induct.py): definition of types and constants by induction.
  * [`logic_macro`](logic/logic_macro.py): definition of standard macros in logic.
  * [`basic`](logic/basic.py): definition of base logic.

* [`syntax`](syntax/): parsing and printing.
  * [`printer`](syntax/printer.py): printing functions.
  * [`parser`](syntax/parser.py): parsing functions, built using Lark parser.

* [`server`](server/): toplevel functions.
  * [`tactic`](server/tactic.py): definition of proof state and standard operations on proof states.

* [`app`](app/): web application.
  * [`static/main.js`](app/static/main.js): main javascript file.
  * [`templates/index.html`](app/templates/index.html): main HTML page.
  * [`__init__.py`](app/__init__.py): main server program.

* [`examples`](examples/): sample input files.
