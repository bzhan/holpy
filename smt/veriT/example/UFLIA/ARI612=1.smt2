(set-info :smt-lib-version 2.6)
(set-logic UFLIA)
(set-info :source |These benchmarks are translations from the TPTP Library (Thousands of
Problems for Theorem Provers), see http://www.cs.miami.edu/~tptp/

The TPTP is maintained by Geoff Sutcliffe, and he contributed this
selection of benchmarks to SMT-LIB.
|)
(set-info :category "industrial")
(set-info :status unsat)
(declare-fun p (Int) Bool)
(declare-fun q (Int) Bool)
(assert (not (=> (and (forall ((?X Int)) (= (and (< 5 ?X) (< ?X 15)) (p ?X))) (forall ((?X Int)) (= (and (< 8 ?X) (< ?X 12)) (q ?X)))) (forall ((?X Int)) (=> (q ?X) (p ?X))))))
(check-sat)
(exit)
