(set-info :smt-lib-version 2.6)
(set-logic QF_UFLRA)
(set-info :source |Benchmarks from the paper: "Extending Sledgehammer with SMT Solvers" by Jasmin Blanchette, Sascha Bohme, and Lawrence C. Paulson, CADE 2011.  Translated to SMT2 by Andrew Reynolds and Morgan Deters.|)
(set-info :category "industrial")
(set-info :status unsat)
(declare-sort S1 0)
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (Real) Real)
(declare-fun f4 () Real)
(declare-fun f5 () Real)
(assert (not (= f1 f2)))
(assert (not (not (= (f3 f4) 1.0))))
(assert (= f4 f5))
(assert (= f4 f5))
(assert (= (f3 f5) (- 1)))
(check-sat)
(exit)
