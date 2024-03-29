(set-info :smt-lib-version 2.6)
(set-logic UF)
(set-info :source |Benchmarks from the paper: "Extending Sledgehammer with SMT Solvers" by Jasmin Blanchette, Sascha Bohme, and Lawrence C. Paulson, CADE 2011.  Translated to SMT2 by Andrew Reynolds and Morgan Deters.|)
(set-info :category "industrial")
(set-info :status unsat)
(declare-sort S1 0)
(declare-sort S2 0)
(declare-sort S3 0)
(declare-sort S4 0)
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S3 S4) S1)
(declare-fun f4 (S2 S2) S3)
(declare-fun f5 () S4)
(declare-fun f6 () S2)
(declare-fun f7 () S2)
(assert (not (= f1 f2)))
(assert (not (and (forall ((?v0 S2) (?v1 S2)) (let ((?v_2 (= ?v0 f6))) (let ((?v_1 (not ?v_2)) (?v_0 (= ?v1 f6))) (let ((?v_3 (not ?v_0))) (and (=> (and (= (f3 (f4 ?v0 ?v1) f5) f1) (and ?v_1 ?v_3)) (forall ((?v2 S2)) (let ((?v_4 (= ?v2 f6)) (?v_5 (or (= ?v0 f7) (= (f3 (f4 ?v0 f7) f5) f1)))) (and (=> (and (= ?v1 f7) ?v_4) ?v_5) (and (=> (and (= (f3 (f4 ?v1 ?v2) f5) f1) (not ?v_4)) (= (f3 (f4 ?v0 ?v2) f5) f1)) (=> (and ?v_4 (= (f3 (f4 ?v1 f7) f5) f1)) ?v_5)))))) (and (=> (and ?v_0 (and (= (f3 (f4 ?v0 f7) f5) f1) ?v_1)) (forall ((?v2 S2)) (=> (and (= (f3 (f4 f7 ?v2) f5) f1) (not (= ?v2 f6))) (= (f3 (f4 ?v0 ?v2) f5) f1)))) (=> (and ?v_2 (and (= (f3 (f4 f7 ?v1) f5) f1) ?v_3)) (forall ((?v2 S2)) (let ((?v_7 (= ?v2 f6))) (let ((?v_6 (not ?v_7))) (and (=> (= ?v1 f7) ?v_6) (and (=> (and (= (f3 (f4 ?v1 ?v2) f5) f1) ?v_6) (= (f3 (f4 f7 ?v2) f5) f1)) (=> ?v_7 (not (= (f3 (f4 ?v1 f7) f5) f1))))))))))))))) (forall ((?v0 S2) (?v1 S2)) (let ((?v_8 (= ?v1 f6)) (?v_10 (= ?v0 f6))) (let ((?v_9 (not ?v_10)) (?v_11 (not ?v_8))) (=> (not (= ?v0 ?v1)) (or (and (= ?v0 f7) ?v_8) (or (and (= (f3 (f4 ?v0 ?v1) f5) f1) (and ?v_9 ?v_11)) (or (and ?v_8 (and (= (f3 (f4 ?v0 f7) f5) f1) ?v_9)) (or (and ?v_10 (and (= (f3 (f4 f7 ?v1) f5) f1) ?v_11)) (or (and (= ?v1 f7) ?v_10) (or (and (= (f3 (f4 ?v1 ?v0) f5) f1) (and ?v_11 ?v_9)) (or (and ?v_10 (and (= (f3 (f4 ?v1 f7) f5) f1) ?v_11)) (and ?v_8 (and (= (f3 (f4 f7 ?v0) f5) f1) ?v_9))))))))))))))))
(assert (not (= f7 f6)))
(assert (and (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 (f4 ?v0 ?v1) f5) f1) (forall ((?v2 S2)) (=> (= (f3 (f4 ?v1 ?v2) f5) f1) (= (f3 (f4 ?v0 ?v2) f5) f1))))) (and (forall ((?v0 S2)) (not (= (f3 (f4 ?v0 ?v0) f5) f1))) (forall ((?v0 S2) (?v1 S2)) (=> (not (= ?v0 ?v1)) (or (= (f3 (f4 ?v0 ?v1) f5) f1) (= (f3 (f4 ?v1 ?v0) f5) f1)))))))
(check-sat)
(exit)
