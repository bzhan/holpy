(set-info :smt-lib-version 2.6)
(set-logic UFLIA)
(set-info :source |These benchmarks are translations from the TPTP Library (Thousands of
Problems for Theorem Provers), see http://www.cs.miami.edu/~tptp/

The TPTP is maintained by Geoff Sutcliffe, and he contributed this
selection of benchmarks to SMT-LIB.
|)
(set-info :category "industrial")
(set-info :status unsat)
(declare-fun f (Int) Int)
(assert (not (=> (forall ((?X Int)) (> (f ?X) ?X)) (forall ((?X Int)) (< (- (f (- ?X))) (f ?X))))))
(check-sat)
(exit)
