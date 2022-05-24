# Staged reconstruction of SMT proofs using macros
This tool aims to reconstruct the Alethe format proof returned by the SMT solver [veriT](https://verit.loria.fr/) in the higher-order logic interactive theorem prover HolPy.

## Installation
**(All the commands below are assumed to run in the root directory of HolPy)**

At first, you need to install all the packages required by HolPy (the recommended Python version is >= 3.8.10):

`python -m pip install -r requirements.txt`

(Depending on your system, may need to replace python by python3 or python3.x).

The version of veriT solver is `2021.06.2-RMX`, you may download it at [here](https://verit.loria.fr/download/).

If you use Windows system, please add the folder containing `veriT.exe` to the system path.

If you use UNIX system, you need to compile the code according to the instruction in the `README.md` file in the downloaded veriT folder. And then you also need to add `veriT` to the system environment. 

#### Optional
To accelerate the reconstruction process, you can also use [PyPy](https://www.pypy.org/) instead of Python to run the tests. The recommended PyPy version is 3.9.

Note: if you want to use PyPy, you need to reinstall all the packages via: 

`pypy3 -m pip install ...(package name)`

## Run tests
We have collected several examples for each theory in the folder `./smt/veriT/example/`.

You can run run a selection of examples from SMT-LIB via:

`python -m smt.veriT.run_smt_file OPTION`

or

`pypy3 -m smt.veriT.run_smt_file OPTION`

There are three possible `OPTION`:
- `--eval`: run the evaluation function in each macro 
- `--proofterm`: run the expansion function in each macro (**lower-level macros are not expanded**)
- `--expand`: expanding all the macros

Similarly, you can test a single `.smt2` file (please make sure that it is **UNSAT**) via:

`python -m smt.veriT.run_smt_file OPTION FILE_PATH`

or

`pypy3 -m smt.veriT.run_smt_file OPTION FILE_PATH`

where `FILE_PATH` is the path of `.smt2` file.

The results can be found in `./smt/veriT/example/result.csv`.