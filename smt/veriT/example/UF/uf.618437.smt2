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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S2 S3) S3)
(declare-fun f4 (S4 S3) S2)
(declare-fun f5 () S4)
(declare-fun f6 () S2)
(declare-fun f7 () S3)
(declare-fun f8 () S4)
(declare-fun f9 () S4)
(declare-fun f10 () S2)
(declare-fun f11 () S2)
(declare-fun f12 () S3)
(declare-fun f13 () S3)
(declare-fun f14 () S3)
(declare-fun f15 (S5 S3) S1)
(declare-fun f16 (S3) S5)
(declare-fun f17 (S3) S1)
(declare-fun f18 () S3)
(declare-fun f19 (S6 S3) S5)
(declare-fun f20 (S3) S6)
(declare-fun f21 (S3) S5)
(declare-fun f22 (S7 S8) S8)
(declare-fun f23 (S9 S8) S7)
(declare-fun f24 () S9)
(declare-fun f25 () S8)
(declare-fun f26 (S10 S3) S8)
(declare-fun f27 () S10)
(declare-fun f28 () S9)
(declare-fun f29 () S8)
(declare-fun f30 () S4)
(declare-fun f31 (S11 S8) S1)
(declare-fun f32 (S8) S11)
(declare-fun f33 (S8) S11)
(declare-fun f34 () S9)
(assert (not (= f1 f2)))
(assert (not (= (f3 (f4 f5 (f3 f6 f7)) (f3 (f4 f8 (f3 (f4 f9 (f3 f6 (f3 f10 (f3 f10 (f3 f11 f12))))) f13)) f14)) f14)))
(assert (let ((?v_2 (f3 f10 (f3 f11 f12)))) (let ((?v_0 (f3 (f4 f8 (f3 (f4 f9 (f3 f6 (f3 f10 ?v_2))) f13)) f14))) (let ((?v_1 (f16 ?v_0))) (or (= (f3 (f4 f5 (f3 f6 f7)) ?v_0) f14) (or (= (f15 ?v_1 f14) f1) (= (f15 ?v_1 (f3 f6 ?v_2)) f1)))))))
(assert (let ((?v_1 (f3 f10 (f3 f11 f12)))) (let ((?v_0 (f16 (f3 (f4 f8 (f3 (f4 f9 (f3 f6 (f3 f10 ?v_1))) f13)) f14)))) (=> (or (= (f15 ?v_0 f14) f1) (= (f15 ?v_0 (f3 f6 ?v_1)) f1)) false))))
(assert (let ((?v_1 (f3 f10 (f3 f11 f12)))) (let ((?v_0 (f16 (f3 (f4 f8 (f3 (f4 f9 (f3 f6 (f3 f10 ?v_1))) f13)) f14)))) (=> (or (= (f15 ?v_0 f14) f1) (= (f15 ?v_0 (f3 f6 ?v_1)) f1)) false))))
(assert (let ((?v_2 (f3 f10 (f3 f11 f12)))) (let ((?v_0 (f3 (f4 f8 (f3 (f4 f9 (f3 f6 (f3 f10 ?v_2))) f13)) f14))) (let ((?v_1 (f16 ?v_0))) (or (= (f3 (f4 f5 (f3 f6 f7)) ?v_0) f14) (or (= (f15 ?v_1 f14) f1) (= (f15 ?v_1 (f3 f6 ?v_2)) f1)))))))
(assert (= (f17 (f3 (f4 f8 (f3 (f4 f9 (f3 f6 (f3 f10 (f3 f10 (f3 f11 f12))))) f13)) f14)) f1))
(assert (let ((?v_1 (f3 f6 f7))) (let ((?v_0 (f3 (f4 f5 ?v_1) (f3 (f4 f8 (f3 (f4 f9 (f3 f6 (f3 f10 (f3 f10 (f3 f11 f12))))) f13)) f14)))) (or (= ?v_0 f14) (or (= ?v_0 f18) (= ?v_0 ?v_1))))))
(assert (let ((?v_0 (f3 (f4 f8 (f3 (f4 f9 (f3 f6 (f3 f10 (f3 f10 (f3 f11 f12))))) f13)) f14))) (= (f15 (f19 (f20 f14) (f3 (f4 f5 (f3 f6 f7)) ?v_0)) ?v_0) f1)))
(assert (let ((?v_0 (f3 f10 (f3 f11 f12)))) (= (f15 (f21 (f3 f6 ?v_0)) (f3 (f4 f8 (f3 (f4 f9 (f3 f6 (f3 f10 ?v_0))) f13)) f14)) f1)))
(assert (forall ((?v0 S3)) (= (f3 (f4 f8 f14) (f3 f6 ?v0)) (f3 f6 (f3 (f4 f8 (f3 f11 f12)) ?v0)))))
(assert (forall ((?v0 S3)) (= (f3 (f4 f8 (f3 f6 ?v0)) f14) (f3 f6 (f3 (f4 f8 ?v0) (f3 f11 f12))))))
(assert (= (f3 (f4 f8 f14) f14) (f3 f6 (f3 f10 (f3 f11 f12)))))
(assert (= (f3 (f4 f8 f14) f14) (f3 f6 (f3 f10 (f3 f11 f12)))))
(assert (= (f22 (f23 f24 f25) f25) (f26 f27 (f3 f10 (f3 f11 f12)))))
(assert (forall ((?v0 S3)) (= (f3 (f4 f9 ?v0) (f3 f6 (f3 f10 (f3 f11 f12)))) (f3 (f4 f8 ?v0) ?v0))))
(assert (forall ((?v0 S3)) (= (f3 (f4 f9 ?v0) (f3 f6 (f3 f10 (f3 f11 f12)))) (f3 (f4 f8 ?v0) ?v0))))
(assert (forall ((?v0 S8)) (= (f22 (f23 f28 ?v0) (f26 f27 (f3 f10 (f3 f11 f12)))) (f22 (f23 f24 ?v0) ?v0))))
(assert (forall ((?v0 S3)) (= (f3 (f4 f9 (f3 f6 (f3 f10 (f3 f11 f12)))) ?v0) (f3 (f4 f8 ?v0) ?v0))))
(assert (forall ((?v0 S3)) (= (f3 (f4 f9 (f3 f6 (f3 f10 (f3 f11 f12)))) ?v0) (f3 (f4 f8 ?v0) ?v0))))
(assert (forall ((?v0 S8)) (= (f22 (f23 f28 (f26 f27 (f3 f10 (f3 f11 f12)))) ?v0) (f22 (f23 f24 ?v0) ?v0))))
(assert (forall ((?v0 S3)) (= (f3 (f4 f9 (f3 (f4 f8 f14) f14)) (f3 f6 ?v0)) (f3 f6 (f3 f10 ?v0)))))
(assert (= (f15 (f21 f18) f14) f1))
(assert (= (= (f15 (f21 f7) f18) f1) true))
(assert (= (= (f15 (f21 f12) f18) f1) false))
(assert (forall ((?v0 S3) (?v1 S3)) (or (= (f15 (f21 ?v0) ?v1) f1) (or (= ?v0 ?v1) (= (f15 (f21 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S3)) (= (= (f15 (f21 (f3 f10 ?v0)) f18) f1) (= (f15 (f21 ?v0) f18) f1))))
(assert (forall ((?v0 S3)) (= (= (f15 (f21 (f3 f11 ?v0)) f18) f1) (= (f15 (f21 ?v0) f18) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f15 (f21 (f3 f6 ?v0)) (f3 f6 ?v1)) f1) (= (f15 (f21 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3)) (= (= (f15 (f21 (f3 (f4 f8 ?v0) ?v0)) f18) f1) (= (f15 (f21 ?v0) f18) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f15 (f21 f18) ?v0) f1) (=> (= (f15 (f21 ?v0) ?v1) f1) (not (= (f15 (f16 ?v1) ?v0) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f4 f9 ?v2))) (=> (= (f15 (f21 ?v0) ?v1) f1) (=> (= (f15 (f21 f18) ?v2) f1) (= (f15 (f21 (f3 ?v_0 ?v0)) (f3 ?v_0 ?v1)) f1))))))
(assert (forall ((?v0 S3)) (= (= (f15 (f21 (f3 f6 ?v0)) f18) f1) (= (f15 (f21 ?v0) f12) f1))))
(assert (forall ((?v0 S3)) (= (= (f15 (f21 f18) (f3 f6 ?v0)) f1) (= (f15 (f21 f12) ?v0) f1))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f4 f9 ?v0))) (=> (= (f15 (f16 (f3 ?v_0 ?v1)) (f3 ?v_0 ?v2)) f1) (=> (not (= ?v0 f18)) (= (f15 (f16 ?v1) ?v2) f1))))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f15 (f21 (f3 f11 ?v0)) (f3 f11 ?v1)) f1) (= (f15 (f21 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f15 (f21 (f3 f11 ?v0)) (f3 f11 ?v1)) f1) (= (f15 (f21 ?v0) ?v1) f1))))
(assert (= (= (f15 (f21 f12) f12) f1) false))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f15 (f21 (f3 f10 ?v0)) (f3 f10 ?v1)) f1) (= (f15 (f21 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f15 (f21 (f3 f10 ?v0)) (f3 f10 ?v1)) f1) (= (f15 (f21 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3)) (= (= (f3 (f4 f8 ?v0) ?v0) f18) (= ?v0 f18))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f15 (f21 (f3 f6 ?v0)) (f3 f6 ?v1)) f1) (= (f15 (f21 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= (f15 (f21 ?v0) ?v1) f1) (= (f15 (f21 (f3 (f4 f8 ?v0) ?v2)) (f3 (f4 f8 ?v1) ?v2)) f1))))
(assert (= f12 f18))
(assert (= (= (f15 (f21 f7) f7) f1) false))
(assert (not (= f18 f14)))
(assert (forall ((?v0 S3)) (= (f3 (f4 f8 ?v0) f18) ?v0)))
(assert (forall ((?v0 S3)) (= (f3 (f4 f8 f18) ?v0) ?v0)))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f15 (f21 f18) ?v0) f1) (= (= (f3 (f4 f9 ?v0) ?v1) f14) (and (= ?v0 f14) (= ?v1 f14))))))
(assert (forall ((?v0 S3)) (= (= (f15 (f21 (f3 (f4 f8 (f3 (f4 f8 f14) ?v0)) ?v0)) f18) f1) (= (f15 (f21 ?v0) f18) f1))))
(assert (forall ((?v0 S3)) (= (= (f15 (f21 (f3 f11 ?v0)) f12) f1) (= (f15 (f21 ?v0) f12) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f15 (f21 (f3 f11 ?v0)) (f3 f10 ?v1)) f1) (= (f15 (f21 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f15 (f21 (f3 f11 ?v0)) (f3 f10 ?v1)) f1) (= (f15 (f21 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3)) (= (= (f15 (f21 (f3 f10 ?v0)) f12) f1) (= (f15 (f21 ?v0) f12) f1))))
(assert (forall ((?v0 S3)) (let ((?v_0 (f21 f12))) (= (= (f15 ?v_0 (f3 f10 ?v0)) f1) (= (f15 ?v_0 ?v0) f1)))))
(assert (= (f3 f6 f12) f18))
(assert (= (f26 f27 f12) f29))
(assert (= (f3 f6 f12) f18))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f21 ?v0))) (= (= (f15 ?v_0 (f3 (f4 f8 ?v1) f14)) f1) (or (= (f15 ?v_0 ?v1) f1) (= ?v0 ?v1))))))
(assert (forall ((?v0 S3)) (= (= (f15 (f21 (f3 f11 ?v0)) f7) f1) (= (f15 (f21 ?v0) f7) f1))))
(assert (forall ((?v0 S3)) (let ((?v_0 (f21 f7))) (= (= (f15 ?v_0 (f3 f11 ?v0)) f1) (= (f15 ?v_0 ?v0) f1)))))
(assert (= (= (f15 (f21 f12) f7) f1) false))
(assert (= (= (f15 (f21 f7) f12) f1) true))
(assert (forall ((?v0 S3)) (let ((?v_0 (f21 f7))) (= (= (f15 ?v_0 (f3 f10 ?v0)) f1) (= (f15 ?v_0 ?v0) f1)))))
(assert (= f18 (f3 f6 f12)))
(assert (forall ((?v0 S3)) (not (= (f3 (f4 f8 (f3 (f4 f8 f14) ?v0)) ?v0) f18))))
(assert (forall ((?v0 S3)) (= (= (f15 (f21 (f3 f6 ?v0)) f14) f1) (= (f15 (f21 ?v0) (f3 f11 f12)) f1))))
(assert (forall ((?v0 S3)) (= (= (f15 (f21 f14) (f3 f6 ?v0)) f1) (= (f15 (f21 (f3 f11 f12)) ?v0) f1))))
(assert (forall ((?v0 S3)) (let ((?v_0 (f3 f6 ?v0))) (= (f3 f6 (f3 f10 ?v0)) (f3 (f4 f8 (f3 (f4 f8 f18) ?v_0)) ?v_0)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 f6 ?v0) (f3 f6 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f3 f6 ?v0))) (= (= ?v_0 ?v1) (= ?v1 ?v_0)))))
(assert (forall ((?v0 S3) (?v1 S8)) (let ((?v_0 (f26 f27 ?v0))) (= (= ?v_0 ?v1) (= ?v1 ?v_0)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 f11 ?v0) (f3 f11 ?v1)) (= ?v0 ?v1))))
(assert (= (= f12 f12) true))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 f10 ?v0) (f3 f10 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f4 f9 ?v0))) (= (f3 (f4 f9 (f3 ?v_0 ?v1)) ?v2) (f3 ?v_0 (f3 (f4 f9 ?v1) ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f3 (f4 f9 ?v0) ?v1) (f3 (f4 f9 ?v1) ?v0))))
(assert (forall ((?v0 S3)) (= (f3 f6 ?v0) ?v0)))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f4 f8 ?v0))) (= (f3 (f4 f8 (f3 ?v_0 ?v1)) ?v2) (f3 ?v_0 (f3 (f4 f8 ?v1) ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_1 (f4 f8 ?v0)) (?v_0 (f4 f8 ?v1))) (= (f3 ?v_1 (f3 ?v_0 ?v2)) (f3 ?v_0 (f3 ?v_1 ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f3 (f4 f8 ?v0) ?v1) (f3 (f4 f8 ?v1) ?v0))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3) (?v4 S3)) (let ((?v_0 (f16 ?v0)) (?v_1 (f4 f8 ?v2))) (=> (= (f15 ?v_0 ?v1) f1) (= (= (f15 ?v_0 (f3 ?v_1 ?v3)) f1) (= (f15 ?v_0 (f3 (f4 f8 (f3 ?v_1 (f3 (f4 f9 ?v4) ?v1))) ?v3)) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f16 ?v0))) (= (= (f15 ?v_0 (f3 (f4 f8 ?v1) (f3 (f4 f9 ?v0) ?v2))) f1) (= (f15 ?v_0 ?v1) f1)))))
(assert (= (= f7 f7) true))
(assert (forall ((?v0 S3)) (= (= (f3 f11 ?v0) f12) false)))
(assert (forall ((?v0 S3)) (= (= f12 (f3 f11 ?v0)) false)))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 f11 ?v0) (f3 f10 ?v1)) false)))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 f10 ?v0) (f3 f11 ?v1)) false)))
(assert (forall ((?v0 S3)) (= (= (f3 f10 ?v0) f12) (= ?v0 f12))))
(assert (forall ((?v0 S3)) (= (= f12 (f3 f10 ?v0)) (= f12 ?v0))))
(assert (= (f3 f10 f12) f12))
(assert (forall ((?v0 S3)) (= (f3 (f4 f9 f12) ?v0) f12)))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f3 (f4 f9 (f3 f10 ?v0)) ?v1) (f3 f10 (f3 (f4 f9 ?v0) ?v1)))))
(assert (forall ((?v0 S3)) (= (f3 (f4 f8 ?v0) f12) ?v0)))
(assert (forall ((?v0 S3)) (= (f3 (f4 f8 f12) ?v0) ?v0)))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f3 (f4 f8 (f3 f10 ?v0)) (f3 f10 ?v1)) (f3 f10 (f3 (f4 f8 ?v0) ?v1)))))
(assert (forall ((?v0 S3)) (= (f3 f10 ?v0) (f3 (f4 f8 ?v0) ?v0))))
(assert (forall ((?v0 S3)) (= (f3 (f4 f9 ?v0) f14) ?v0)))
(assert (forall ((?v0 S3)) (= (f3 (f4 f9 f14) ?v0) ?v0)))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f3 (f4 f9 (f3 f6 ?v0)) (f3 f6 ?v1)) (f3 f6 (f3 (f4 f9 ?v0) ?v1)))))
(assert (forall ((?v0 S3)) (= (= (f3 f11 ?v0) f7) (= ?v0 f7))))
(assert (forall ((?v0 S3)) (= (= f7 (f3 f11 ?v0)) (= f7 ?v0))))
(assert (= (f3 f11 f7) f7))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (= (f3 (f4 f9 (f3 (f4 f8 ?v0) ?v1)) ?v2) (f3 (f4 f8 (f3 (f4 f9 ?v0) ?v2)) (f3 (f4 f9 ?v1) ?v2)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f4 f9 ?v0))) (= (f3 ?v_0 (f3 (f4 f8 ?v1) ?v2)) (f3 (f4 f8 (f3 ?v_0 ?v1)) (f3 ?v_0 ?v2))))))
(assert (= (= f12 f7) false))
(assert (= (= f7 f12) false))
(assert (forall ((?v0 S3)) (= (= (f3 f10 ?v0) f7) false)))
(assert (forall ((?v0 S3)) (= (= f7 (f3 f10 ?v0)) false)))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f3 (f4 f8 (f3 f6 ?v0)) (f3 f6 ?v1)) (f3 f6 (f3 (f4 f8 ?v0) ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f3 f6 ?v2))) (= (f3 (f4 f9 (f3 (f4 f8 ?v0) ?v1)) ?v_0) (f3 (f4 f8 (f3 (f4 f9 ?v0) ?v_0)) (f3 (f4 f9 ?v1) ?v_0))))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S3)) (let ((?v_0 (f26 f27 ?v2))) (= (f22 (f23 f28 (f22 (f23 f24 ?v0) ?v1)) ?v_0) (f22 (f23 f24 (f22 (f23 f28 ?v0) ?v_0)) (f22 (f23 f28 ?v1) ?v_0))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f4 f9 (f3 f6 ?v0)))) (= (f3 ?v_0 (f3 (f4 f8 ?v1) ?v2)) (f3 (f4 f8 (f3 ?v_0 ?v1)) (f3 ?v_0 ?v2))))))
(assert (forall ((?v0 S3) (?v1 S8) (?v2 S8)) (let ((?v_0 (f23 f28 (f26 f27 ?v0)))) (= (f22 ?v_0 (f22 (f23 f24 ?v1) ?v2)) (f22 (f23 f24 (f22 ?v_0 ?v1)) (f22 ?v_0 ?v2))))))
(assert (forall ((?v0 S3)) (= (f3 (f4 f8 (f3 f6 f12)) ?v0) ?v0)))
(assert (forall ((?v0 S3)) (= (f3 (f4 f8 ?v0) (f3 f6 f12)) ?v0)))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (= (f3 (f4 f9 (f3 f6 ?v0)) (f3 (f4 f9 (f3 f6 ?v1)) ?v2)) (f3 (f4 f9 (f3 f6 (f3 (f4 f9 ?v0) ?v1))) ?v2))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f3 (f4 f9 (f3 f6 ?v0)) (f3 f6 ?v1)) (f3 f6 (f3 (f4 f9 ?v0) ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f3 f6 (f3 (f4 f9 ?v0) ?v1)) (f3 (f4 f9 (f3 f6 ?v0)) (f3 f6 ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (= (f3 (f4 f8 (f3 f6 ?v0)) (f3 (f4 f8 (f3 f6 ?v1)) ?v2)) (f3 (f4 f8 (f3 f6 (f3 (f4 f8 ?v0) ?v1))) ?v2))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f3 (f4 f8 (f3 f6 ?v0)) (f3 f6 ?v1)) (f3 f6 (f3 (f4 f8 ?v0) ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f3 f6 (f3 (f4 f8 ?v0) ?v1)) (f3 (f4 f8 (f3 f6 ?v0)) (f3 f6 ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f3 (f4 f8 (f3 f11 ?v0)) (f3 f10 ?v1)) (f3 f11 (f3 (f4 f8 ?v0) ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f3 (f4 f8 (f3 f10 ?v0)) (f3 f11 ?v1)) (f3 f11 (f3 (f4 f8 ?v0) ?v1)))))
(assert (forall ((?v0 S3)) (= (f3 f11 ?v0) (f3 (f4 f8 (f3 (f4 f8 f14) ?v0)) ?v0))))
(assert (forall ((?v0 S3)) (let ((?v_0 (f3 f6 ?v0))) (= (f3 f6 (f3 f11 ?v0)) (f3 (f4 f8 (f3 (f4 f8 f14) ?v_0)) ?v_0)))))
(assert (forall ((?v0 S3)) (= (f3 (f4 f9 (f3 f6 (f3 f11 f12))) ?v0) ?v0)))
(assert (forall ((?v0 S3)) (= (f3 (f4 f9 ?v0) (f3 f6 (f3 f11 f12))) ?v0)))
(assert (= (f3 f6 (f3 f11 f12)) f14))
(assert (= (f26 f27 (f3 f11 f12)) f25))
(assert (= (f3 f6 (f3 f11 f12)) f14))
(assert (= f14 (f3 f6 (f3 f11 f12))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f3 (f4 f9 (f3 f11 ?v0)) ?v1) (f3 (f4 f8 (f3 f10 (f3 (f4 f9 ?v0) ?v1))) ?v1))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f3 (f4 f9 ?v0) ?v1) f14) (or (= ?v0 f14) (= ?v0 (f3 f6 f7))))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f3 f6 f7))) (= (= (f3 (f4 f9 ?v0) ?v1) f14) (or (and (= ?v0 f14) (= ?v1 f14)) (and (= ?v0 ?v_0) (= ?v1 ?v_0)))))))
(assert (let ((?v_0 (f3 (f4 f8 (f3 (f4 f9 (f3 f6 (f3 f10 (f3 f10 (f3 f11 f12))))) f13)) f14))) (= (f15 (f16 ?v_0) (f3 (f4 f30 f14) (f3 (f4 f5 (f3 f6 f7)) ?v_0))) f1)))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f20 ?v1))) (=> (= (f15 (f21 (f3 f6 (f3 f10 (f3 f11 f12)))) ?v0) f1) (=> (= (f15 (f19 ?v_0 (f3 f6 f7)) ?v0) f1) (not (= (f15 (f19 ?v_0 f14) ?v0) f1)))))))
(assert (forall ((?v0 S3)) (=> (= (f15 (f21 (f3 f6 (f3 f10 (f3 f11 f12)))) ?v0) f1) (not (= (f15 (f19 (f20 f14) (f3 f6 f7)) ?v0) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= (f17 ?v0) f1) (=> (= (f15 (f21 f18) ?v1) f1) (=> (and (not (= (f15 (f19 (f20 ?v1) f18) ?v0) f1)) (not (= (f15 (f19 (f20 ?v2) f18) ?v0) f1))) (not (= (f15 (f19 (f20 (f3 (f4 f9 ?v1) ?v2)) f18) ?v0) f1)))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= (f17 ?v0) f1) (=> (= (f15 (f21 f18) ?v1) f1) (=> (= (f15 (f19 (f20 (f3 (f4 f9 ?v1) ?v2)) f18) ?v0) f1) (or (= (f15 (f19 (f20 ?v1) f18) ?v0) f1) (= (f15 (f19 (f20 ?v2) f18) ?v0) f1)))))))
(assert (= (f17 (f3 f6 (f3 f10 (f3 f11 f12)))) f1))
(assert (forall ((?v0 S8)) (= (f31 (f32 ?v0) f29) f1)))
(assert (forall ((?v0 S3)) (= (f15 (f16 ?v0) f18) f1)))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= (f17 ?v0) f1) (=> (not (= (f15 (f19 (f20 ?v1) f18) ?v0) f1)) (=> (not (= (f15 (f19 (f20 ?v2) f18) ?v0) f1)) (not (= (f15 (f19 (f20 (f3 (f4 f9 ?v1) ?v2)) f18) ?v0) f1)))))))
(assert (= f14 (f3 f6 (f3 f11 f12))))
(assert (forall ((?v0 S11) (?v1 S8)) (= (exists ((?v2 S8)) (= (f31 ?v0 (f22 (f23 f28 ?v1) ?v2)) f1)) (exists ((?v2 S8)) (and (= (f31 (f32 ?v1) (f22 (f23 f24 ?v2) f29)) f1) (= (f31 ?v0 ?v2) f1))))))
(assert (forall ((?v0 S5) (?v1 S3)) (= (exists ((?v2 S3)) (= (f15 ?v0 (f3 (f4 f9 ?v1) ?v2)) f1)) (exists ((?v2 S3)) (and (= (f15 (f16 ?v1) (f3 (f4 f8 ?v2) f18)) f1) (= (f15 ?v0 ?v2) f1))))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f3 f6 (f3 (f4 f30 ?v0) ?v1)) (f3 (f4 f30 (f3 f6 ?v0)) (f3 f6 ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f16 ?v0))) (=> (= (f15 ?v_0 ?v1) f1) (=> (= (f15 ?v_0 ?v2) f1) (= (f15 ?v_0 (f3 (f4 f30 ?v1) ?v2)) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= (f3 (f4 f30 ?v0) ?v1) ?v2) (= ?v0 (f3 (f4 f8 ?v2) ?v1)))))
(assert (= (f26 f27 f12) f29))
(assert (= f29 (f26 f27 f12)))
(assert (forall ((?v0 S3)) (= (= (f31 (f33 f29) (f26 f27 ?v0)) f1) (= (f15 (f21 f12) ?v0) f1))))
(assert (forall ((?v0 S3)) (= (f3 (f4 f30 ?v0) f12) ?v0)))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f3 (f4 f30 (f3 f10 ?v0)) (f3 f10 ?v1)) (f3 f10 (f3 (f4 f30 ?v0) ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f4 f9 ?v0))) (= (f3 ?v_0 (f3 (f4 f30 ?v1) ?v2)) (f3 (f4 f30 (f3 ?v_0 ?v1)) (f3 ?v_0 ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (= (f3 (f4 f9 (f3 (f4 f30 ?v0) ?v1)) ?v2) (f3 (f4 f30 (f3 (f4 f9 ?v0) ?v2)) (f3 (f4 f9 ?v1) ?v2)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f16 ?v0))) (=> (= (f15 ?v_0 (f3 (f4 f30 ?v1) ?v2)) f1) (=> (= (f15 ?v_0 ?v2) f1) (= (f15 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3) (?v4 S3)) (= (= (f3 (f4 f8 (f3 (f4 f9 ?v0) ?v1)) ?v2) (f3 (f4 f8 (f3 (f4 f9 ?v3) ?v1)) ?v4)) (= ?v2 (f3 (f4 f8 (f3 (f4 f9 (f3 (f4 f30 ?v3) ?v0)) ?v1)) ?v4)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3) (?v4 S3)) (= (= (f3 (f4 f8 (f3 (f4 f9 ?v0) ?v1)) ?v2) (f3 (f4 f8 (f3 (f4 f9 ?v3) ?v1)) ?v4)) (= (f3 (f4 f8 (f3 (f4 f9 (f3 (f4 f30 ?v0) ?v3)) ?v1)) ?v2) ?v4))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f31 (f33 (f26 f27 ?v0)) (f26 f27 ?v1)) f1) (ite (= (f15 (f21 ?v0) ?v1) f1) (= (f15 (f21 f12) ?v1) f1) false))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3) (?v4 S3)) (= (= (f15 (f21 (f3 (f4 f8 (f3 (f4 f9 ?v0) ?v1)) ?v2)) (f3 (f4 f8 (f3 (f4 f9 ?v3) ?v1)) ?v4)) f1) (= (f15 (f21 ?v2) (f3 (f4 f8 (f3 (f4 f9 (f3 (f4 f30 ?v3) ?v0)) ?v1)) ?v4)) f1))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3) (?v4 S3)) (= (= (f15 (f21 (f3 (f4 f8 (f3 (f4 f9 ?v0) ?v1)) ?v2)) (f3 (f4 f8 (f3 (f4 f9 ?v3) ?v1)) ?v4)) f1) (= (f15 (f21 (f3 (f4 f8 (f3 (f4 f9 (f3 (f4 f30 ?v0) ?v3)) ?v1)) ?v2)) ?v4) f1))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= (f15 (f16 ?v0) ?v1) f1) (forall ((?v3 S3) (?v4 S3)) (let ((?v_0 (f16 ?v0))) (= (not (= (f15 ?v_0 (f3 (f4 f8 ?v3) ?v2)) f1)) (not (= (f15 ?v_0 (f3 (f4 f8 (f3 (f4 f30 ?v3) (f3 (f4 f9 ?v4) ?v1))) ?v2)) f1))))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= (f15 (f16 ?v0) ?v1) f1) (forall ((?v3 S3) (?v4 S3)) (let ((?v_0 (f16 ?v0))) (= (= (f15 ?v_0 (f3 (f4 f8 ?v3) ?v2)) f1) (= (f15 ?v_0 (f3 (f4 f8 (f3 (f4 f30 ?v3) (f3 (f4 f9 ?v4) ?v1))) ?v2)) f1)))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f4 f9 (f3 f6 ?v0)))) (= (f3 ?v_0 (f3 (f4 f30 ?v1) ?v2)) (f3 (f4 f30 (f3 ?v_0 ?v1)) (f3 ?v_0 ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f3 f6 ?v2))) (= (f3 (f4 f9 (f3 (f4 f30 ?v0) ?v1)) ?v_0) (f3 (f4 f30 (f3 (f4 f9 ?v0) ?v_0)) (f3 (f4 f9 ?v1) ?v_0))))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f3 (f4 f30 (f3 f11 ?v0)) (f3 f10 ?v1)) (f3 f11 (f3 (f4 f30 ?v0) ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f3 (f4 f30 (f3 f11 ?v0)) (f3 f11 ?v1)) (f3 f10 (f3 (f4 f30 ?v0) ?v1)))))
(assert (forall ((?v0 S3)) (let ((?v_0 (f4 f30 f12))) (= (f3 ?v_0 (f3 f10 ?v0)) (f3 f10 (f3 ?v_0 ?v0))))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f15 (f21 ?v0) ?v1) f1) (= (f15 (f21 (f3 (f4 f30 ?v0) ?v1)) f18) f1))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S8)) (= (f22 (f23 f28 (f26 f27 ?v0)) (f22 (f23 f28 (f26 f27 ?v1)) ?v2)) (ite (= (f15 (f21 ?v0) f12) f1) f29 (f22 (f23 f28 (f26 f27 (f3 (f4 f9 ?v0) ?v1))) ?v2)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f22 (f23 f28 (f26 f27 ?v0)) (f26 f27 ?v1)) (ite (= (f15 (f21 ?v0) f12) f1) f29 (f26 f27 (f3 (f4 f9 ?v0) ?v1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (= (f3 (f4 f8 (f3 f6 ?v0)) (f3 (f4 f30 (f3 f6 ?v1)) ?v2)) (f3 (f4 f30 (f3 f6 (f3 (f4 f8 ?v0) ?v1))) ?v2))))
(assert (forall ((?v0 S3)) (= (f3 (f4 f30 f12) (f3 f11 ?v0)) (f3 f11 (f3 (f4 f30 f7) ?v0)))))
(assert (forall ((?v0 S3)) (let ((?v_0 (f4 f30 f7))) (= (f3 ?v_0 (f3 f10 ?v0)) (f3 f11 (f3 ?v_0 ?v0))))))
(assert (forall ((?v0 S3)) (let ((?v_0 (f4 f30 f7))) (= (f3 ?v_0 (f3 f11 ?v0)) (f3 f10 (f3 ?v_0 ?v0))))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (not (= ?v0 ?v1)) (=> (=> (= (f15 (f21 ?v0) ?v1) f1) false) (=> (=> (= (f15 (f21 ?v1) ?v0) f1) false) false)))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8)) (let ((?v_0 (f32 ?v0))) (=> (= (f31 ?v_0 ?v1) f1) (=> (= (f31 (f32 ?v1) ?v2) f1) (= (f31 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f16 ?v0))) (=> (= (f15 ?v_0 ?v1) f1) (=> (= (f15 (f16 ?v1) ?v2) f1) (= (f15 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S8)) (= (f31 (f32 ?v0) ?v0) f1)))
(assert (forall ((?v0 S3)) (= (f15 (f16 ?v0) ?v0) f1)))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3) (?v4 S3)) (let ((?v_0 (f20 ?v0))) (=> (= (f15 (f19 ?v_0 ?v1) ?v2) f1) (=> (= ?v1 ?v3) (=> (= (f15 (f19 (f20 ?v3) ?v4) ?v2) f1) (= (f15 (f19 ?v_0 ?v4) ?v2) f1)))))))
(assert (forall ((?v0 S3)) (= (f3 (f4 f9 f18) ?v0) f18)))
(assert (forall ((?v0 S8)) (= (f22 (f23 f28 f29) ?v0) f29)))
(assert (forall ((?v0 S3)) (= (f3 (f4 f9 ?v0) f18) f18)))
(assert (forall ((?v0 S8)) (= (f22 (f23 f28 ?v0) f29) f29)))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f4 f9 ?v0) ?v1) f18) (or (= ?v0 f18) (= ?v1 f18)))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (not (= ?v0 f18)) (=> (not (= ?v1 f18)) (not (= (f3 (f4 f9 ?v0) ?v1) f18))))))
(assert (forall ((?v0 S8) (?v1 S8)) (=> (not (= ?v0 f29)) (=> (not (= ?v1 f29)) (not (= (f22 (f23 f28 ?v0) ?v1) f29))))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f3 (f4 f9 ?v0) ?v1) f18) (or (= ?v0 f18) (= ?v1 f18)))))
(assert (forall ((?v0 S8) (?v1 S8)) (=> (= (f22 (f23 f28 ?v0) ?v1) f29) (or (= ?v0 f29) (= ?v1 f29)))))
(assert (not (= f14 f18)))
(assert (not (= f25 f29)))
(assert (not (= f18 f14)))
(assert (not (= f29 f25)))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (= (f3 (f4 f9 (f3 (f4 f8 ?v0) ?v1)) ?v2) (f3 (f4 f8 (f3 (f4 f9 ?v0) ?v2)) (f3 (f4 f9 ?v1) ?v2)))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8)) (= (f22 (f23 f28 (f22 (f23 f24 ?v0) ?v1)) ?v2) (f22 (f23 f24 (f22 (f23 f28 ?v0) ?v2)) (f22 (f23 f28 ?v1) ?v2)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (= (f3 (f4 f8 (f3 (f4 f9 ?v0) ?v1)) (f3 (f4 f8 (f3 (f4 f9 ?v2) ?v1)) ?v3)) (f3 (f4 f8 (f3 (f4 f9 (f3 (f4 f8 ?v0) ?v2)) ?v1)) ?v3))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8) (?v3 S8)) (= (f22 (f23 f24 (f22 (f23 f28 ?v0) ?v1)) (f22 (f23 f24 (f22 (f23 f28 ?v2) ?v1)) ?v3)) (f22 (f23 f24 (f22 (f23 f28 (f22 (f23 f24 ?v0) ?v2)) ?v1)) ?v3))))
(assert (forall ((?v0 S8)) (=> (= (f31 (f32 f29) ?v0) f1) (= ?v0 f29))))
(assert (forall ((?v0 S3)) (=> (= (f15 (f16 f18) ?v0) f1) (= ?v0 f18))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (f31 (f32 ?v0) (f22 (f23 f28 ?v0) ?v1)) f1)))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f15 (f16 ?v0) (f3 (f4 f9 ?v0) ?v1)) f1)))
(assert (forall ((?v0 S8) (?v1 S8)) (= (f31 (f32 ?v0) (f22 (f23 f28 ?v1) ?v0)) f1)))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f15 (f16 ?v0) (f3 (f4 f9 ?v1) ?v0)) f1)))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8)) (let ((?v_0 (f32 ?v0))) (=> (= (f31 ?v_0 ?v1) f1) (= (f31 ?v_0 (f22 (f23 f28 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f16 ?v0))) (=> (= (f15 ?v_0 ?v1) f1) (= (f15 ?v_0 (f3 (f4 f9 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8)) (let ((?v_0 (f32 ?v0))) (=> (= (f31 ?v_0 ?v1) f1) (= (f31 ?v_0 (f22 (f23 f28 ?v2) ?v1)) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f16 ?v0))) (=> (= (f15 ?v_0 ?v1) f1) (= (f15 ?v_0 (f3 (f4 f9 ?v2) ?v1)) f1)))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8) (?v3 S8)) (=> (= (f31 (f32 ?v0) ?v1) f1) (=> (= (f31 (f32 ?v2) ?v3) f1) (= (f31 (f32 (f22 (f23 f28 ?v0) ?v2)) (f22 (f23 f28 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (=> (= (f15 (f16 ?v0) ?v1) f1) (=> (= (f15 (f16 ?v2) ?v3) f1) (= (f15 (f16 (f3 (f4 f9 ?v0) ?v2)) (f3 (f4 f9 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8)) (=> (= ?v0 (f22 (f23 f28 ?v1) ?v2)) (= (f31 (f32 ?v1) ?v0) f1))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= ?v0 (f3 (f4 f9 ?v1) ?v2)) (= (f15 (f16 ?v1) ?v0) f1))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8)) (=> (= (f31 (f32 (f22 (f23 f28 ?v0) ?v1)) ?v2) f1) (= (f31 (f32 ?v0) ?v2) f1))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= (f15 (f16 (f3 (f4 f9 ?v0) ?v1)) ?v2) f1) (= (f15 (f16 ?v0) ?v2) f1))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8)) (=> (= (f31 (f32 (f22 (f23 f28 ?v0) ?v1)) ?v2) f1) (= (f31 (f32 ?v1) ?v2) f1))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= (f15 (f16 (f3 (f4 f9 ?v0) ?v1)) ?v2) f1) (= (f15 (f16 ?v1) ?v2) f1))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8)) (let ((?v_0 (f32 ?v0))) (=> (= (f31 ?v_0 ?v1) f1) (=> (= (f31 ?v_0 ?v2) f1) (= (f31 ?v_0 (f22 (f23 f24 ?v1) ?v2)) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f16 ?v0))) (=> (= (f15 ?v_0 ?v1) f1) (=> (= (f15 ?v_0 ?v2) f1) (= (f15 ?v_0 (f3 (f4 f8 ?v1) ?v2)) f1))))))
(assert (forall ((?v0 S8)) (= (f31 (f32 f25) ?v0) f1)))
(assert (forall ((?v0 S3)) (= (f15 (f16 f14) ?v0) f1)))
(assert (= f25 (f26 f27 (f3 f11 f12))))
(assert (= (f26 f27 (f3 f11 f12)) f25))
(assert (forall ((?v0 S3)) (= (f15 (f19 (f20 ?v0) f18) ?v0) f1)))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3) (?v4 S3)) (let ((?v_0 (f20 ?v3))) (=> (= (f15 (f19 (f20 ?v0) ?v1) ?v2) f1) (= (= (f15 (f19 ?v_0 (f3 (f4 f9 ?v0) ?v4)) ?v2) f1) (= (f15 (f19 ?v_0 (f3 (f4 f9 ?v1) ?v4)) ?v2) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3) (?v4 S3)) (let ((?v_0 (f20 ?v3)) (?v_1 (f4 f9 ?v4))) (=> (= (f15 (f19 (f20 ?v0) ?v1) ?v2) f1) (= (= (f15 (f19 ?v_0 (f3 ?v_1 ?v0)) ?v2) f1) (= (f15 (f19 ?v_0 (f3 ?v_1 ?v1)) ?v2) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (=> (= (f15 (f19 (f20 ?v0) ?v1) ?v2) f1) (= (f15 (f19 (f20 (f3 (f4 f8 ?v0) ?v3)) (f3 (f4 f8 ?v1) ?v3)) ?v2) f1))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f4 f9 ?v2))) (=> (= (f15 (f21 ?v0) ?v1) f1) (=> (= (f15 (f21 ?v2) f18) f1) (= (f15 (f21 (f3 ?v_0 ?v1)) (f3 ?v_0 ?v0)) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= (f15 (f21 ?v0) ?v1) f1) (=> (= (f15 (f21 ?v2) f18) f1) (= (f15 (f21 (f3 (f4 f9 ?v1) ?v2)) (f3 (f4 f9 ?v0) ?v2)) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f4 f9 ?v2))) (=> (= (f15 (f21 ?v0) ?v1) f1) (=> (= (f15 (f21 f18) ?v2) f1) (= (f15 (f21 (f3 ?v_0 ?v0)) (f3 ?v_0 ?v1)) f1))))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8)) (let ((?v_0 (f23 f28 ?v2))) (=> (= (f31 (f33 ?v0) ?v1) f1) (=> (= (f31 (f33 f29) ?v2) f1) (= (f31 (f33 (f22 ?v_0 ?v0)) (f22 ?v_0 ?v1)) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f4 f9 ?v2))) (=> (= (f15 (f21 ?v0) ?v1) f1) (=> (= (f15 (f21 f18) ?v2) f1) (= (f15 (f21 (f3 ?v_0 ?v0)) (f3 ?v_0 ?v1)) f1))))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8)) (let ((?v_0 (f23 f28 ?v2))) (=> (= (f31 (f33 ?v0) ?v1) f1) (=> (= (f31 (f33 f29) ?v2) f1) (= (f31 (f33 (f22 ?v_0 ?v0)) (f22 ?v_0 ?v1)) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= (f15 (f21 ?v0) ?v1) f1) (=> (= (f15 (f21 f18) ?v2) f1) (= (f15 (f21 (f3 (f4 f9 ?v0) ?v2)) (f3 (f4 f9 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8)) (=> (= (f31 (f33 ?v0) ?v1) f1) (=> (= (f31 (f33 f29) ?v2) f1) (= (f31 (f33 (f22 (f23 f28 ?v0) ?v2)) (f22 (f23 f28 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f15 (f21 ?v0) f18) f1) (=> (= (f15 (f21 ?v1) f18) f1) (= (f15 (f21 f18) (f3 (f4 f9 ?v0) ?v1)) f1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f15 (f21 ?v0) f18) f1) (=> (= (f15 (f21 f18) ?v1) f1) (= (f15 (f21 (f3 (f4 f9 ?v0) ?v1)) f18) f1)))))
(assert (forall ((?v0 S8) (?v1 S8)) (=> (= (f31 (f33 ?v0) f29) f1) (=> (= (f31 (f33 f29) ?v1) f1) (= (f31 (f33 (f22 (f23 f28 ?v0) ?v1)) f29) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f4 f9 ?v0))) (=> (= (f15 (f21 ?v0) f18) f1) (= (= (f15 (f21 (f3 ?v_0 ?v1)) (f3 ?v_0 ?v2)) f1) (= (f15 (f21 ?v2) ?v1) f1))))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f21 f18))) (=> (= (f15 ?v_0 (f3 (f4 f9 ?v0) ?v1)) f1) (=> (= (f15 ?v_0 ?v1) f1) (= (f15 ?v_0 ?v0) f1))))))
(assert (forall ((?v0 S8) (?v1 S8)) (let ((?v_0 (f33 f29))) (=> (= (f31 ?v_0 (f22 (f23 f28 ?v0) ?v1)) f1) (=> (= (f31 ?v_0 ?v1) f1) (= (f31 ?v_0 ?v0) f1))))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f21 f18))) (=> (= (f15 ?v_0 (f3 (f4 f9 ?v0) ?v1)) f1) (=> (= (f15 ?v_0 ?v0) f1) (= (f15 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S8) (?v1 S8)) (let ((?v_0 (f33 f29))) (=> (= (f31 ?v_0 (f22 (f23 f28 ?v0) ?v1)) f1) (=> (= (f31 ?v_0 ?v0) f1) (= (f31 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f15 (f21 f18) ?v0) f1) (=> (= (f15 (f21 ?v1) f18) f1) (= (f15 (f21 (f3 (f4 f9 ?v1) ?v0)) f18) f1)))))
(assert (forall ((?v0 S8) (?v1 S8)) (=> (= (f31 (f33 f29) ?v0) f1) (=> (= (f31 (f33 ?v1) f29) f1) (= (f31 (f33 (f22 (f23 f28 ?v1) ?v0)) f29) f1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f15 (f21 f18) ?v0) f1) (=> (= (f15 (f21 ?v1) f18) f1) (= (f15 (f21 (f3 (f4 f9 ?v0) ?v1)) f18) f1)))))
(assert (forall ((?v0 S8) (?v1 S8)) (=> (= (f31 (f33 f29) ?v0) f1) (=> (= (f31 (f33 ?v1) f29) f1) (= (f31 (f33 (f22 (f23 f28 ?v0) ?v1)) f29) f1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f21 f18))) (=> (= (f15 ?v_0 ?v0) f1) (=> (= (f15 ?v_0 ?v1) f1) (= (f15 ?v_0 (f3 (f4 f9 ?v0) ?v1)) f1))))))
(assert (forall ((?v0 S8) (?v1 S8)) (let ((?v_0 (f33 f29))) (=> (= (f31 ?v_0 ?v0) f1) (=> (= (f31 ?v_0 ?v1) f1) (= (f31 ?v_0 (f22 (f23 f28 ?v0) ?v1)) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f4 f9 ?v0))) (=> (= (f15 (f21 f18) ?v0) f1) (= (= (f15 (f21 (f3 ?v_0 ?v1)) (f3 ?v_0 ?v2)) f1) (= (f15 (f21 ?v1) ?v2) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f4 f9 ?v0))) (= (= (f15 (f21 (f3 ?v_0 ?v1)) (f3 ?v_0 ?v2)) f1) (or (and (= (f15 (f21 f18) ?v0) f1) (= (f15 (f21 ?v1) ?v2) f1)) (and (= (f15 (f21 ?v0) f18) f1) (= (f15 (f21 ?v2) ?v1) f1)))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (= (= (f15 (f21 (f3 (f4 f9 ?v0) ?v1)) (f3 (f4 f9 ?v2) ?v1)) f1) (or (and (= (f15 (f21 f18) ?v1) f1) (= (f15 (f21 ?v0) ?v2) f1)) (and (= (f15 (f21 ?v1) f18) f1) (= (f15 (f21 ?v2) ?v0) f1))))))
(assert (forall ((?v0 S3)) (not (= (f15 (f21 (f3 (f4 f9 ?v0) ?v0)) f18) f1))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f21 ?v1))) (=> (= (f15 (f21 f18) ?v0) f1) (=> (= (f15 ?v_0 ?v2) f1) (= (f15 ?v_0 (f3 (f4 f8 ?v0) ?v2)) f1))))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8)) (let ((?v_0 (f33 ?v1))) (=> (= (f31 (f33 f29) ?v0) f1) (=> (= (f31 ?v_0 ?v2) f1) (= (f31 ?v_0 (f22 (f23 f24 ?v0) ?v2)) f1))))))
(assert (= (f15 (f21 f18) f14) f1))
(assert (= (f31 (f33 f29) f25) f1))
(assert (not (= (f15 (f21 f14) f18) f1)))
(assert (not (= (f31 (f33 f25) f29) f1)))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f4 f8 (f3 (f4 f9 ?v0) ?v0)) (f3 (f4 f9 ?v1) ?v1)) f18) (and (= ?v0 f18) (= ?v1 f18)))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f21 f14))) (=> (= (f15 ?v_0 ?v0) f1) (=> (= (f15 ?v_0 ?v1) f1) (= (f15 ?v_0 (f3 (f4 f9 ?v0) ?v1)) f1))))))
(assert (forall ((?v0 S8) (?v1 S8)) (let ((?v_0 (f33 f25))) (=> (= (f31 ?v_0 ?v0) f1) (=> (= (f31 ?v_0 ?v1) f1) (= (f31 ?v_0 (f22 (f23 f28 ?v0) ?v1)) f1))))))
(assert (forall ((?v0 S3)) (= (f15 (f21 ?v0) (f3 (f4 f8 ?v0) f14)) f1)))
(assert (forall ((?v0 S8)) (= (f31 (f33 ?v0) (f22 (f23 f24 ?v0) f25)) f1)))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (= (= (f15 (f16 (f3 (f4 f9 ?v0) ?v1)) (f3 (f4 f9 ?v2) ?v1)) f1) (or (= ?v1 f18) (= (f15 (f16 ?v0) ?v2) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f4 f9 ?v0))) (= (= (f15 (f16 (f3 ?v_0 ?v1)) (f3 ?v_0 ?v2)) f1) (or (= ?v0 f18) (= (f15 (f16 ?v1) ?v2) f1))))))
(assert (= f18 (f3 f6 f12)))
(assert (= (f22 (f23 f24 f25) f25) (f26 f27 (f3 f10 (f3 f11 f12)))))
(assert (forall ((?v0 S8)) (= (f22 (f23 f28 ?v0) (f26 f27 (f3 f10 (f3 f11 f12)))) (f22 (f23 f24 ?v0) ?v0))))
(assert (forall ((?v0 S8)) (= (f22 (f23 f28 (f26 f27 (f3 f10 (f3 f11 f12)))) ?v0) (f22 (f23 f24 ?v0) ?v0))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f21 f18))) (=> (= (f15 ?v_0 ?v0) f1) (=> (= (f15 ?v_0 (f3 (f4 f9 ?v0) ?v1)) f1) (= (f15 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_1 (f26 f27 ?v0)) (?v_0 (f26 f27 ?v1))) (= (f22 (f23 f24 ?v_1) ?v_0) (ite (= (f15 (f21 ?v0) f12) f1) ?v_0 (ite (= (f15 (f21 ?v1) f12) f1) ?v_1 (f26 f27 (f3 (f4 f8 ?v0) ?v1))))))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f15 (f21 f18) ?v0) f1) (=> (= (f15 (f21 ?v0) ?v1) f1) (not (= (f15 (f19 (f20 ?v0) f18) ?v1) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f21 f18))) (=> (= (f15 ?v_0 ?v0) f1) (=> (= (f15 ?v_0 ?v1) f1) (=> (= (f15 ?v_0 ?v2) f1) (=> (= (f15 (f19 (f20 ?v0) ?v1) ?v2) f1) (=> (= (f15 (f21 ?v0) ?v2) f1) (=> (= (f15 (f21 ?v1) ?v2) f1) (= ?v0 ?v1))))))))))
(assert (not (= (f3 f6 f12) (f3 f6 f7))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f4 f9 ?v0))) (=> (not (= ?v0 f18)) (= (= (f15 (f16 ?v1) ?v2) f1) (= (f15 (f16 (f3 ?v_0 ?v1)) (f3 ?v_0 ?v2)) f1))))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f15 (f19 (f20 ?v0) f18) ?v1) f1) (= (f15 (f16 ?v1) ?v0) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f15 (f19 (f20 ?v0) f18) ?v1) f1) (= (f15 (f16 ?v1) ?v0) f1))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f16 ?v0))) (=> (= (f17 ?v0) f1) (=> (= (f15 ?v_0 (f3 (f4 f9 ?v1) ?v2)) f1) (or (= (f15 ?v_0 ?v1) f1) (= (f15 ?v_0 ?v2) f1)))))))
(assert (forall ((?v0 S3) (?v1 S3)) (not (= (f15 (f21 (f3 (f4 f8 (f3 (f4 f9 ?v0) ?v0)) (f3 (f4 f9 ?v1) ?v1))) f18) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f15 (f21 f18) (f3 (f4 f8 (f3 (f4 f9 ?v0) ?v0)) (f3 (f4 f9 ?v1) ?v1))) f1) (or (not (= ?v0 f18)) (not (= ?v1 f18))))))
(assert (= (f15 (f21 f18) (f3 (f4 f8 f14) f14)) f1))
(assert (= (f31 (f33 f29) (f22 (f23 f24 f25) f25)) f1))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f20 ?v1))) (=> (= (f17 ?v0) f1) (=> (= (f15 (f21 f18) ?v1) f1) (=> (= (f15 (f19 (f20 (f3 (f4 f9 ?v1) ?v1)) f14) ?v0) f1) (or (= (f15 (f19 ?v_0 f14) ?v0) f1) (= (f15 (f19 ?v_0 (f3 (f4 f30 ?v0) f14)) ?v0) f1))))))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f17 ?v0) f1) (=> (= (f15 (f21 f18) ?v1) f1) (=> (= (f15 (f21 ?v1) ?v0) f1) (=> (= (f15 (f19 (f20 (f3 (f4 f9 ?v1) ?v1)) f14) ?v0) f1) (or (= ?v1 f14) (= ?v1 (f3 (f4 f30 ?v0) f14)))))))))
(assert (forall ((?v0 S3)) (=> (= (f15 (f21 f14) ?v0) f1) (exists ((?v1 S3)) (and (= (f17 ?v1) f1) (= (f15 (f16 ?v1) ?v0) f1))))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f3 (f4 f30 ?v1) f14))) (= (= (f15 (f19 (f20 (f3 (f4 f9 ?v0) ?v_0)) f14) ?v1) f1) (= (f15 (f19 (f20 ?v0) ?v_0) ?v1) f1)))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (f22 (f23 f28 ?v0) ?v1) (ite (= ?v0 f29) f29 (f22 (f23 f24 ?v1) (f22 (f23 f28 (f22 (f23 f34 ?v0) f25)) ?v1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (= (= (f15 (f19 (f20 ?v0) ?v1) ?v2) f1) (= (f15 (f19 (f20 ?v1) ?v0) ?v2) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f15 (f19 (f20 ?v0) ?v0) ?v1) f1)))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (let ((?v_0 (f20 ?v0))) (=> (= (f15 (f19 ?v_0 ?v1) ?v2) f1) (=> (= (f15 (f19 (f20 ?v1) ?v3) ?v2) f1) (= (f15 (f19 ?v_0 ?v3) ?v2) f1))))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f15 (f19 (f20 ?v0) ?v1) f18) f1) (= ?v0 ?v1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f15 (f19 (f20 ?v0) ?v1) f14) f1)))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3) (?v4 S3)) (=> (= (f15 (f19 (f20 ?v0) ?v1) ?v2) f1) (=> (= (f15 (f19 (f20 ?v3) ?v4) ?v2) f1) (= (f15 (f19 (f20 (f3 (f4 f9 ?v0) ?v3)) (f3 (f4 f9 ?v1) ?v4)) ?v2) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (let ((?v_0 (f4 f9 ?v3))) (=> (= (f15 (f19 (f20 ?v0) ?v1) ?v2) f1) (= (f15 (f19 (f20 (f3 ?v_0 ?v0)) (f3 ?v_0 ?v1)) ?v2) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (=> (= (f15 (f19 (f20 ?v0) ?v1) ?v2) f1) (= (f15 (f19 (f20 (f3 (f4 f9 ?v0) ?v3)) (f3 (f4 f9 ?v1) ?v3)) ?v2) f1))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (= (f15 (f19 (f20 (f3 (f4 f9 ?v0) ?v1)) (f3 (f4 f9 ?v2) ?v1)) ?v1) f1)))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3) (?v4 S3)) (=> (= (f15 (f19 (f20 ?v0) ?v1) ?v2) f1) (=> (= (f15 (f19 (f20 ?v3) ?v4) ?v2) f1) (= (f15 (f19 (f20 (f3 (f4 f8 ?v0) ?v3)) (f3 (f4 f8 ?v1) ?v4)) ?v2) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3) (?v4 S3)) (=> (= (f15 (f19 (f20 ?v0) ?v1) ?v2) f1) (=> (= (f15 (f19 (f20 ?v3) ?v4) ?v2) f1) (= (f15 (f19 (f20 (f3 (f4 f30 ?v0) ?v3)) (f3 (f4 f30 ?v1) ?v4)) ?v2) f1)))))
(check-sat)
(exit)
