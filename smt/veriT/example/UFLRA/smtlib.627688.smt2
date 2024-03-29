(set-info :smt-lib-version 2.6)
(set-logic UFLRA)
(set-info :source |Benchmarks from the paper: "Extending Sledgehammer with SMT Solvers" by Jasmin Blanchette, Sascha Bohme, and Lawrence C. Paulson, CADE 2011.  Translated to SMT2 by Andrew Reynolds and Morgan Deters.|)
(set-info :category "industrial")
(set-info :status unsat)
(declare-sort S1 0)
(declare-sort S2 0)
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 () Real)
(declare-fun f4 (S2 Real) Real)
(declare-fun f5 () S2)
(declare-fun f6 () Real)
(assert (not (= f1 f2)))
(assert (forall ((?v0 Real)) (let ((?v_0 0.0)) (=> (< ?v_0 ?v0) (=> (< ?v0 f3) (< ?v_0 (f4 f5 ?v0)))))))
(assert (let ((?v_1 0.0) (?v_0 (- f6 f3))) (not (=> (< ?v_1 ?v_0) (=> (< ?v_0 f3) (not (= (f4 f5 ?v_0) ?v_1)))))))
(check-sat)
(exit)
