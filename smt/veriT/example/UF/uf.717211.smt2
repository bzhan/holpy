(set-info :smt-lib-version 2.6)
(set-logic UF)
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
(declare-sort S16 0)
(declare-sort S17 0)
(declare-sort S18 0)
(declare-sort S19 0)
(declare-sort S20 0)
(declare-sort S21 0)
(declare-sort S22 0)
(declare-sort S23 0)
(declare-sort S24 0)
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S3 S2) S1)
(declare-fun f4 () S3)
(declare-fun f5 (S2 S3) S1)
(declare-fun f6 (S4) S3)
(declare-fun f7 () S4)
(declare-fun f8 (S5 S6) S3)
(declare-fun f9 (S7 S6) S5)
(declare-fun f10 (S8) S7)
(declare-fun f11 () S8)
(declare-fun f12 () S6)
(declare-fun f13 () S3)
(declare-fun f14 () S8)
(declare-fun f15 () S6)
(declare-fun f16 (S8 S9) S10)
(declare-fun f17 (S1 S8) S10)
(declare-fun f18 () S8)
(declare-fun f19 (S11 S9) S1)
(declare-fun f20 () S11)
(declare-fun f21 (S13 S9) S9)
(declare-fun f22 (S14 S9) S13)
(declare-fun f23 () S14)
(declare-fun f24 (S15 S12) S9)
(declare-fun f25 (S16 S12) S15)
(declare-fun f26 () S16)
(declare-fun f27 (S17 S12) S12)
(declare-fun f28 () S17)
(declare-fun f29 () S12)
(declare-fun f30 (S18 S12) S2)
(declare-fun f31 (S19 S9) S18)
(declare-fun f32 () S19)
(declare-fun f33 (S3) S3)
(declare-fun f34 (S10 S12) S1)
(declare-fun f35 (S9) S11)
(declare-fun f36 () S9)
(declare-fun f37 (S6 S9) S8)
(declare-fun f38 (S2 S12) S1)
(declare-fun f39 () S2)
(declare-fun f40 (S20 S9) S17)
(declare-fun f41 () S20)
(declare-fun f42 () S9)
(declare-fun f43 () S14)
(declare-fun f44 () S14)
(declare-fun f45 () S14)
(declare-fun f46 (S21 S11) S9)
(declare-fun f47 () S21)
(declare-fun f48 (S11) S11)
(declare-fun f49 () S15)
(declare-fun f50 (S22 S4) S12)
(declare-fun f51 (S23 S24) S22)
(declare-fun f52 () S23)
(declare-fun f53 () S24)
(declare-fun f54 (S3 S4) S4)
(declare-fun f55 () S9)
(declare-fun f56 () S14)
(declare-fun f57 (S24 S2) S9)
(declare-fun f58 () S24)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2)) (= (= (f3 f4 ?v0) f1) (and (= (f5 ?v0 (f6 f7)) f1) (= (f3 (f8 (f9 (f10 f11) f12) f12) ?v0) f1)))))
(assert (forall ((?v0 S2)) (= (= (f3 f13 ?v0) f1) (and (= (f5 ?v0 (f6 f7)) f1) (= (f3 (f8 (f9 (f10 f14) f15) f15) ?v0) f1)))))
(assert (forall ((?v0 S9)) (= (f16 f14 ?v0) (f17 f2 f18))))
(assert (forall ((?v0 S9)) (= (= (f19 f20 ?v0) f1) (exists ((?v1 S12) (?v2 S9)) (and (= ?v0 (f21 (f22 f23 (f24 (f25 f26 (f27 f28 ?v1)) f29)) ?v2)) (= (f5 (f30 (f31 f32 ?v2) ?v1) (f33 f13)) f1))))))
(assert (forall ((?v0 S9) (?v1 S12)) (= (= (f34 (f16 f18 ?v0) ?v1) f1) (= (f19 (f35 ?v0) f36) f1))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S12)) (= (= (f34 (f16 (f37 f15 ?v0) ?v1) ?v2) f1) false)))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S12)) (= (= (f34 (f16 (f37 f12 ?v0) ?v1) ?v2) f1) true)))
(assert (forall ((?v0 S9) (?v1 S12)) (= (= (f34 (f16 f11 ?v0) ?v1) f1) false)))
(assert (let ((?v_0 (f22 f23 f42)) (?v_1 (f24 f49 (f50 (f51 f52 f53) (f54 (f8 (f9 (f10 f11) f12) f12) f7))))) (not (= (f38 f39 (f27 (f40 f41 (f21 ?v_0 (f21 (f22 f43 (f21 (f22 f44 (f21 (f22 f45 (f21 ?v_0 (f46 f47 (f48 f20)))) ?v_1)) f55)) ?v_1))) f29)) f1))))
(assert (let ((?v_0 (f22 f23 f42)) (?v_1 (f24 f49 (f50 (f51 f52 f53) (f54 (f8 (f9 (f10 f11) f12) f12) f7)))) (?v_2 (f57 f53 f39))) (= (f21 (f22 f56 (f21 ?v_0 (f21 (f22 f43 (f21 (f22 f44 (f21 (f22 f45 (f21 ?v_0 (f46 f47 (f48 f20)))) ?v_1)) f55)) ?v_1))) ?v_2) (f21 (f22 f56 f42) ?v_2))))
(assert (forall ((?v0 S2)) (=> (= (f5 ?v0 (f33 f4)) f1) (= (f38 ?v0 (f27 (f40 f41 f42) f29)) f1))))
(assert (forall ((?v0 S12)) (let ((?v_1 (f8 (f9 (f10 f11) f12) f12)) (?v_0 (f22 f23 f42))) (let ((?v_2 (f24 f49 (f50 (f51 f52 f53) (f54 ?v_1 f7))))) (let ((?v_4 (f21 ?v_0 (f21 (f22 f43 (f21 (f22 f44 (f21 (f22 f45 (f21 ?v_0 (f46 f47 (f48 f20)))) ?v_2)) f55)) ?v_2))) (?v_3 (f57 f53 f39))) (=> (= (f3 ?v_1 f39) f1) (=> (= (f57 f58 f39) f55) (=> (= (f21 (f22 f56 f42) ?v_3) (f21 (f22 f56 ?v_4) ?v_3)) (= (= (f38 f39 (f27 (f40 f41 f42) ?v0)) f1) (= (f38 f39 (f27 (f40 f41 ?v_4) ?v0)) f1))))))))))
(assert (= (f5 f39 (f33 f4)) f1))
(assert (forall ((?v0 S2)) (=> (= (f5 ?v0 (f33 f4)) f1) (= (f57 f58 ?v0) f55))))
(assert (forall ((?v0 S2) (?v1 S3)) (= (= (f5 ?v0 ?v1) f1) (= (f3 ?v1 ?v0) f1))))
(assert (forall ((?v0 S3)) (= (f33 ?v0) ?v0)))
(assert (forall ((?v0 S11)) (= (f48 ?v0) ?v0)))
(check-sat)
(exit)
