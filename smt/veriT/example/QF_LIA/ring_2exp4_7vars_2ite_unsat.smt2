(set-info :smt-lib-version 2.6)
(set-logic QF_LIA)
(set-info :source |
Alberto Griggio

|)
(set-info :category "crafted")
(set-info :status unsat)
(declare-fun v0 () Int)
(declare-fun v1 () Int)
(declare-fun v2 () Int)
(declare-fun v3 () Int)
(declare-fun v4 () Int)
(declare-fun v5 () Int)
(declare-fun v6 () Int)
(declare-fun o_0 () Int)
(declare-fun s_1 () Int)
(declare-fun s_2 () Int)
(declare-fun o_1 () Int)
(declare-fun s_3 () Int)
(declare-fun s_4 () Int)
(declare-fun o_2 () Int)
(declare-fun s_5 () Int)
(declare-fun o_3 () Int)
(declare-fun o_4 () Int)
(declare-fun o_5 () Int)
(declare-fun o_6 () Int)
(declare-fun s_7 () Int)
(declare-fun o_7 () Int)
(declare-fun s_8 () Int)
(declare-fun o_8 () Int)
(declare-fun s_9 () Int)
(declare-fun o_9 () Int)
(declare-fun s_10 () Int)
(declare-fun o_10 () Int)
(declare-fun s_11 () Int)
(declare-fun o_11 () Int)
(declare-fun A_itev1 () Int)
(declare-fun A_itev2 () Int)
(declare-fun A_itev3 () Int)
(declare-fun A_itev4 () Int)
(assert (let ((?v_38 (* v6 64)) (?v_74 (* A_itev2 32)) (?v_12 (* v1 2)) (?v_71 (* v2 4)) (?v_70 (* v3 8)) (?v_69 (* v4 16)) (?v_68 (* v5 32)) (?v_65 (* A_itev2 16)) (?v_60 (* A_itev2 8)) (?v_33 (* v3 2)) (?v_57 (* v4 4)) (?v_56 (* v5 8)) (?v_53 (* A_itev2 4)) (?v_48 (* A_itev2 2)) (?v_25 (* v5 2)) (?v_29 (+ (- s_5) (* v6 4))) (?v_26 (- s_4))) (let ((?v_28 (+ (+ (+ ?v_25 v4) ?v_26) (- s_3)))) (let ((?v_27 (+ (- o_2) ?v_28)) (?v_24 (+ ?v_26 ?v_25)) (?v_1 (<= 16 v6))) (let ((?v_17 (not ?v_1)) (?v_9 (<= 16 v1))) (let ((?v_16 (not ?v_9)) (?v_15 (= A_itev4 A_itev3)) (?v_14 (= (+ (- A_itev4) ?v_12) 0)) (?v_13 (<= 8 v1)) (?v_8 (+ (- A_itev3) ?v_12))) (let ((?v_11 (= ?v_8 16)) (?v_10 (= ?v_8 32)) (?v_7 (= A_itev2 A_itev1)) (?v_4 (* v6 2))) (let ((?v_6 (= (+ (- A_itev2) ?v_4) 0)) (?v_5 (<= 8 v6)) (?v_0 (+ (- A_itev1) ?v_4))) (let ((?v_3 (= ?v_0 16)) (?v_2 (= ?v_0 32)) (?v_30 (* o_0 (- 16)))) (let ((?v_18 (+ (+ ?v_30 v0) A_itev4)) (?v_21 (* s_1 (- 4)))) (let ((?v_19 (+ ?v_21 v2)) (?v_20 (+ (* s_2 (- 2)) v3)) (?v_34 (* s_2 (- 4)))) (let ((?v_23 (+ (+ (+ ?v_33 v2) ?v_34) ?v_21)) (?v_35 (* o_1 (- 4)))) (let ((?v_22 (+ ?v_23 ?v_35)) (?v_39 (* s_5 (- 16)))) (let ((?v_32 (+ (+ (+ ?v_38 v0) ?v_39) ?v_30)) (?v_40 (* o_3 (- 16)))) (let ((?v_31 (+ (+ ?v_32 ?v_40) A_itev4)) (?v_37 (+ (+ (+ (+ (+ (+ (+ (+ (+ ?v_57 ?v_56) ?v_33) v2) (* s_4 (- 4))) (* s_3 (- 4))) (* o_2 (- 4))) ?v_34) ?v_21) ?v_35))) (let ((?v_36 (+ (* o_4 (- 4)) ?v_37)) (?v_75 (* s_4 (- 16))) (?v_76 (* s_3 (- 16))) (?v_77 (* o_2 (- 16))) (?v_78 (* s_2 (- 16))) (?v_79 (* s_1 (- 16))) (?v_80 (* o_1 (- 16))) (?v_81 (* o_4 (- 16)))) (let ((?v_42 (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ ?v_38 ?v_68) ?v_69) ?v_70) ?v_71) v0) ?v_75) ?v_76) ?v_77) ?v_78) ?v_79) ?v_80) ?v_81) ?v_39) ?v_30) ?v_40)) (?v_82 (* o_5 (- 16)))) (let ((?v_41 (+ (+ ?v_42 ?v_82) A_itev4)) (?v_44 (+ (* o_6 (- 16)) v5))) (let ((?v_43 (+ ?v_44 A_itev2)) (?v_45 (+ (+ (* s_7 (- 8)) ?v_44) A_itev2)) (?v_47 (+ (+ (+ (* o_6 (- 32)) ?v_25) (* s_7 (- 16))) v4))) (let ((?v_49 (+ ?v_47 (* o_7 (- 16))))) (let ((?v_46 (+ ?v_49 ?v_48)) (?v_50 (+ (+ (* s_8 (- 8)) ?v_49) ?v_48)) (?v_52 (+ (+ (+ (+ (+ (+ (* o_6 (- 64)) (* v5 4)) (* s_7 (- 32))) (* v4 2)) (* o_7 (- 32))) (* s_8 (- 16))) v3))) (let ((?v_54 (+ ?v_52 (* o_8 (- 16))))) (let ((?v_51 (+ ?v_54 ?v_53)) (?v_55 (+ (+ (* s_9 (- 8)) ?v_54) ?v_53)) (?v_59 (+ (+ (+ (+ (+ (+ (+ (+ (+ (* o_6 (- 128)) ?v_56) (* s_7 (- 64))) ?v_57) (* o_7 (- 64))) (* s_8 (- 32))) ?v_33) (* o_8 (- 32))) (* s_9 (- 16))) v2))) (let ((?v_61 (+ ?v_59 (* o_9 (- 16))))) (let ((?v_58 (+ ?v_61 ?v_60)) (?v_62 (+ (+ (* s_10 (- 8)) ?v_61) ?v_60)) (?v_64 (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (* o_6 (- 256)) (* v5 16)) (* s_7 (- 128))) (* v4 8)) (* o_7 (- 128))) (* s_8 (- 64))) (* v3 4)) (* o_8 (- 64))) (* s_9 (- 32))) (* v2 2)) (* o_9 (- 32))) (* s_10 (- 16))) v1))) (let ((?v_66 (+ ?v_64 (* o_10 (- 16))))) (let ((?v_63 (+ ?v_66 ?v_65)) (?v_67 (+ (+ (* s_11 (- 8)) ?v_66) ?v_65)) (?v_73 (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (* o_6 (- 512)) ?v_68) (* s_7 (- 256))) ?v_69) (* o_7 (- 256))) (* s_8 (- 128))) ?v_70) (* o_8 (- 128))) (* s_9 (- 64))) ?v_71) (* o_9 (- 64))) (* s_10 (- 32))) ?v_12) (* o_10 (- 32))) (* s_11 (- 16))) v0))) (let ((?v_72 (+ (+ (* o_11 (- 16)) ?v_73) ?v_74))) (and (and (and (and (and (and (and (and (and (and (and (and (or ?v_2 ?v_17) (or ?v_3 ?v_1)) (or ?v_2 ?v_3)) (or ?v_5 ?v_6)) (or (not ?v_5) ?v_7)) (or ?v_6 ?v_7)) (or ?v_11 ?v_9)) (or ?v_10 ?v_16)) (or ?v_10 ?v_11)) (or ?v_13 ?v_14)) (or (not ?v_13) ?v_15)) (or ?v_14 ?v_15)) (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (<= 0 v0) (not (<= 16 v0))) (and (<= 0 v1) ?v_16)) (and (<= 0 v2) (not (<= 16 v2)))) (and (<= 0 v3) (not (<= 16 v3)))) (and (<= 0 v4) (not (<= 16 v4)))) (and (<= 0 v5) (not (<= 16 v5)))) (and (<= 0 v6) ?v_17)) (and (<= 0 o_0) (<= o_0 1))) (and (<= 0 ?v_18) (not (<= 16 ?v_18)))) (= (not (<= (+ A_itev4 v0) 16)) (= o_0 1))) (and (not (<= 4 s_1)) (<= 0 s_1))) (and (<= 0 ?v_19) (not (<= 4 ?v_19)))) (= (<= 1 s_1) (not (<= v2 4)))) (and (not (<= 8 s_2)) (<= 0 s_2))) (and (<= 0 ?v_20) (not (<= 2 ?v_20)))) (= (<= 1 s_2) (not (<= v3 2)))) (and (<= 0 o_1) (<= o_1 1))) (and (<= 0 ?v_22) (not (<= 4 ?v_22)))) (= (not (<= ?v_23 4)) (= o_1 1))) (and (not (<= 16 s_3)) (<= 0 s_3))) (and (<= s_3 v4) (not (<= 1 (- v4 s_3))))) (= (<= 1 s_3) (not (<= v4 1)))) (and (not (<= 32 s_4)) (<= 0 s_4))) (and (<= 0 ?v_24) (not (<= 1 ?v_24)))) (= (<= 1 s_4) (not (<= v5 0)))) (and (<= 0 o_2) (<= o_2 1))) (and (<= 0 ?v_27) (not (<= 1 ?v_27)))) (= (not (<= ?v_28 1)) (= o_2 1))) (and (not (<= 64 s_5)) (<= 0 s_5))) (and (<= 0 ?v_29) (not (<= 1 ?v_29)))) (= (<= 1 s_5) (not (<= v6 0)))) (and (<= 0 o_3) (<= o_3 1))) (and (<= 0 ?v_31) (not (<= 16 ?v_31)))) (= (not (<= (+ ?v_32 A_itev4) 16)) (= o_3 1))) (and (<= 0 o_4) (<= o_4 1))) (and (<= 0 ?v_36) (not (<= 4 ?v_36)))) (= (not (<= ?v_37 4)) (= o_4 1))) (and (<= 0 o_5) (<= o_5 1))) (and (<= 0 ?v_41) (not (<= 16 ?v_41)))) (= (not (<= (+ ?v_42 A_itev4) 16)) (= o_5 1))) (and (<= 0 o_6) (<= o_6 1))) (and (<= 0 ?v_43) (not (<= 16 ?v_43)))) (= (not (<= (+ A_itev2 v5) 16)) (= o_6 1))) (and (not (<= 2 s_7)) (<= 0 s_7))) (and (<= 0 ?v_45) (not (<= 8 ?v_45)))) (= (<= 1 s_7) (not (<= ?v_43 8)))) (and (<= 0 o_7) (<= o_7 1))) (and (<= 0 ?v_46) (not (<= 16 ?v_46)))) (= (not (<= (+ ?v_47 ?v_48) 16)) (= o_7 1))) (and (not (<= 2 s_8)) (<= 0 s_8))) (and (<= 0 ?v_50) (not (<= 8 ?v_50)))) (= (<= 1 s_8) (not (<= ?v_46 8)))) (and (<= 0 o_8) (<= o_8 1))) (and (<= 0 ?v_51) (not (<= 16 ?v_51)))) (= (not (<= (+ ?v_52 ?v_53) 16)) (= o_8 1))) (and (not (<= 2 s_9)) (<= 0 s_9))) (and (<= 0 ?v_55) (not (<= 8 ?v_55)))) (= (<= 1 s_9) (not (<= ?v_51 8)))) (and (<= 0 o_9) (<= o_9 1))) (and (<= 0 ?v_58) (not (<= 16 ?v_58)))) (= (not (<= (+ ?v_59 ?v_60) 16)) (= o_9 1))) (and (not (<= 2 s_10)) (<= 0 s_10))) (and (<= 0 ?v_62) (not (<= 8 ?v_62)))) (= (<= 1 s_10) (not (<= ?v_58 8)))) (and (<= 0 o_10) (<= o_10 1))) (and (<= 0 ?v_63) (not (<= 16 ?v_63)))) (= (not (<= (+ ?v_64 ?v_65) 16)) (= o_10 1))) (and (not (<= 2 s_11)) (<= 0 s_11))) (and (<= 0 ?v_67) (not (<= 8 ?v_67)))) (= (<= 1 s_11) (not (<= ?v_63 8)))) (and (<= 0 o_11) (<= o_11 1))) (and (<= 0 ?v_72) (not (<= 16 ?v_72)))) (= (not (<= (+ ?v_73 ?v_74) 16)) (= o_11 1))) (not (= (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (* o_6 512) ?v_38) (* s_7 256)) (* o_7 256)) (* s_8 128)) (* o_8 128)) (* s_9 64)) (* o_9 64)) (* s_10 32)) (* v1 (- 2))) (* o_10 32)) (* s_11 16)) (* o_11 16)) ?v_75) ?v_76) ?v_77) ?v_78) ?v_79) ?v_80) ?v_81) ?v_39) ?v_30) ?v_40) ?v_82) (* A_itev2 (- 32))) A_itev4) 0))))))))))))))))))))))))))))))))
(check-sat)
(exit)
