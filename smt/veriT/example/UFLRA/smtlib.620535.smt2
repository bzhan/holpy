(set-info :smt-lib-version 2.6)
(set-logic UFLRA)
(set-info :source |Benchmarks from the paper: "Extending Sledgehammer with SMT Solvers" by Jasmin Blanchette, Sascha Bohme, and Lawrence C. Paulson, CADE 2011.  Translated to SMT2 by Andrew Reynolds and Morgan Deters.|)
(set-info :category "industrial")
(set-info :status unsat)
(declare-sort S1 0)
(declare-sort S2 0)
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S2 Real) Real)
(declare-fun f4 () S2)
(declare-fun f5 () Real)
(declare-fun f6 () Real)
(assert (not (= f1 f2)))
(assert (forall ((?v0 Real)) (= (f3 f4 (+ f5 ?v0)) (- (f3 f4 ?v0)))))
(assert (not (= (f3 f4 (- f6 f5)) (- (f3 f4 f6)))))
(check-sat)
(exit)
