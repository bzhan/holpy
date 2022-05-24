(set-info :smt-lib-version 2.6)
(set-logic UFLIA)
(set-info :source |These benchmarks are translations from the TPTP Library (Thousands of
Problems for Theorem Provers), see http://www.cs.miami.edu/~tptp/

The TPTP is maintained by Geoff Sutcliffe, and he contributed this
selection of benchmarks to SMT-LIB.
|)
(set-info :category "industrial")
(set-info :status unsat)
(declare-fun p (Int Int Int) Bool)
(assert (not (=> (forall ((?X Int) (?Y Int) (?Z Int)) (= (and (<= (+ ?Y (- ?Z)) ?X) (<= ?X (+ ?Y ?Z))) (p ?X ?Y ?Z))) (forall ((?X Int) (?Y Int) (?Z Int) (?W Int)) (=> (<= ?Z ?W) (=> (p ?X ?Y ?Z) (p ?X ?Y ?W)))))))
(check-sat)
(exit)
