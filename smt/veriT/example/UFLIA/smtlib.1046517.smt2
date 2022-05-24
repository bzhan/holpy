(set-info :smt-lib-version 2.6)
(set-logic UFLIA)
(set-info :source |Benchmarks from the paper: "Extending Sledgehammer with SMT Solvers" by Jasmin Blanchette, Sascha Bohme, and Lawrence C. Paulson, CADE 2011.  Translated to SMT2 by Andrew Reynolds and Morgan Deters.|)
(set-info :category "industrial")
(set-info :status unsat)
(declare-sort S1 0)
(declare-sort S2 0)
(declare-sort S3 0)
(declare-sort S4 0)
(declare-sort S5 0)
(declare-sort S6 0)
(declare-sort S7 0)
(declare-sort S8 0)
(declare-sort S9 0)
(declare-sort S10 0)
(declare-sort S11 0)
(declare-sort S12 0)
(declare-sort S13 0)
(declare-sort S14 0)
(declare-sort S15 0)
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S2) S1)
(declare-fun f4 (S3 S2) S1)
(declare-fun f5 (S4 S2) S5)
(declare-fun f6 () S4)
(declare-fun f7 (S6 S2) S2)
(declare-fun f8 (S3) S6)
(declare-fun f9 (S7 Int) S5)
(declare-fun f10 () S7)
(declare-fun f11 (S8 S5) Int)
(declare-fun f12 () S8)
(declare-fun f13 (S9) S1)
(declare-fun f14 (S10 S9) S1)
(declare-fun f15 (S11 S9) S5)
(declare-fun f16 () S11)
(declare-fun f17 (S12 S9) S9)
(declare-fun f18 (S10) S12)
(declare-fun f19 () S2)
(declare-fun f20 (S14 S2) S9)
(declare-fun f21 (S15) S14)
(declare-fun f22 () S15)
(declare-fun f23 (S15 S3) S10)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2) (?v1 S3)) (=> (= (f3 ?v0) f1) (=> (not (= (f4 ?v1 ?v0) f1)) (= (f5 f6 (f7 (f8 ?v1) ?v0)) (f9 f10 (+ (f11 f12 (f5 f6 ?v0)) 1)))))))
(assert (forall ((?v0 S9) (?v1 S10)) (=> (= (f13 ?v0) f1) (=> (not (= (f14 ?v1 ?v0) f1)) (= (f15 f16 (f17 (f18 ?v1) ?v0)) (f9 f10 (+ (f11 f12 (f15 f16 ?v0)) 1)))))))
(assert (not (forall ((?v0 S5) (?v1 S9) (?v2 S13) (?v3 S3)) (let ((?v_0 (f11 f12 (f15 f16 (f20 (f21 f22) f19)))) (?v_3 (f11 f12 ?v0))) (let ((?v_1 (+ ?v_3 1)) (?v_2 (f23 f22 ?v3))) (=> (= (f3 f19) f1) (=> (<= ?v_1 ?v_0) (=> (= (f15 f16 ?v1) (f9 f10 (- ?v_0 ?v_1))) (=> (= (f4 ?v3 f19) f1) (=> (not (= (f14 ?v_2 ?v1) f1)) (=> (= (f13 ?v1) f1) (= (f15 f16 (f17 (f18 ?v_2) ?v1)) (f9 f10 (- ?v_0 ?v_3))))))))))))))
(assert (forall ((?v0 S5)) (= (f9 f10 (f11 f12 ?v0)) ?v0)))
(assert (forall ((?v0 Int)) (=> (<= 0 ?v0) (= (f11 f12 (f9 f10 ?v0)) ?v0))))
(assert (forall ((?v0 Int)) (=> (< ?v0 0) (= (f11 f12 (f9 f10 ?v0)) 0))))
(check-sat)
(exit)
