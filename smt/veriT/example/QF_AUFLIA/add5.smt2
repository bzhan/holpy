(set-info :smt-lib-version 2.6)
(set-logic QF_AUFLIA)
(set-info :source |
Translated from old SVC processor verification benchmarks.  Contact Clark
Barrett at barrett@cs.nyu.edu for more information.

This benchmark was automatically translated into SMT-LIB format from
CVC format using CVC Lite
|)
(set-info :category "industrial")
(set-info :status unsat)
(declare-fun Squash_0 (Int) Bool)
(declare-fun s__1 () Int)
(declare-fun t__1 () Int)
(declare-fun icache (Int) (Array Int Int))
(declare-fun s_0 () Int)
(declare-fun PC (Int) Int)
(declare-fun t__2 () Int)
(declare-fun selAreg (Int) Int)
(declare-fun Stall_Control_0 (Int) Int)
(declare-fun t_0 () Int)
(declare-fun selDest (Int) Int)
(declare-fun Stall_Control_1 (Int) Int)
(declare-fun selBreg (Int) Int)
(declare-fun selIType (Int) Int)
(declare-fun s__2 () Int)
(declare-fun dcache (Int) Int)
(declare-fun RF (Int) Int)
(declare-fun s_1 () Int)
(declare-fun t_1 () Int)
(assert (let ((?v_18 (+ s__2 t__2)) (?v_20 (= s__1 s__2)) (?v_25 (+ s__1 t__1))) (let ((?v_26 (Stall_Control_0 ?v_25)) (?v_28 (Stall_Control_1 ?v_25))) (let ((?v_27 (selDest ?v_28))) (let ((?v_30 (ite (ite (= (selAreg ?v_26) ?v_27) true (= (selBreg ?v_26) ?v_27)) (= (selIType ?v_28) 11) false)) (?v_29 (+ (+ 1 s__1) t__1)) (?v_31 (= s__1 s_0)) (?v_32 (+ s_0 t_0))) (let ((?v_33 (Stall_Control_0 ?v_32)) (?v_35 (Stall_Control_1 ?v_32))) (let ((?v_34 (selDest ?v_35)) (?v_36 (+ (+ 1 s_0) t_0))) (let ((?v_37 (Stall_Control_0 ?v_36)) (?v_39 (Stall_Control_1 ?v_36))) (let ((?v_38 (selDest ?v_39))) (let ((?v_41 (ite (ite (= (selAreg ?v_37) ?v_38) true (= (selBreg ?v_37) ?v_38)) (= (selIType ?v_39) 11) false)) (?v_40 (+ (+ 2 s_0) t_0)) (?v_42 (= s_0 s_1)) (?v_21 (+ (+ (- 1) s__1) t__1)) (?v_0 (+ (- 1) s_0)) (?v_5 (+ (- 2) s_0))) (let ((?v_1 (+ ?v_0 t_0))) (let ((?v_2 (Stall_Control_0 ?v_1)) (?v_4 (Stall_Control_1 ?v_1))) (let ((?v_3 (selDest ?v_4)) (?v_6 (+ ?v_5 t_0))) (let ((?v_7 (Stall_Control_0 ?v_6)) (?v_9 (Stall_Control_1 ?v_6))) (let ((?v_8 (selDest ?v_9)) (?v_10 (+ (+ (- 2) s__2) t__2))) (let ((?v_11 (Stall_Control_0 ?v_10)) (?v_13 (Stall_Control_1 ?v_10))) (let ((?v_12 (selDest ?v_13)) (?v_14 (+ (+ (- 1) s__2) t__2))) (let ((?v_15 (Stall_Control_0 ?v_14)) (?v_17 (Stall_Control_1 ?v_14))) (let ((?v_16 (selDest ?v_17))) (let ((?v_19 (ite (ite (= (selAreg ?v_15) ?v_16) true (= (selBreg ?v_15) ?v_16)) (= (selIType ?v_17) 11) false)) (?v_22 (Stall_Control_0 ?v_21)) (?v_24 (Stall_Control_1 ?v_21))) (let ((?v_23 (selDest ?v_24))) (not (ite (ite (= (ite (Squash_0 ?v_21) 10 (select (icache (+ ?v_0 t__1)) (PC (+ ?v_5 t__2)))) (ite (ite (ite (= (selAreg ?v_2) ?v_3) true (= (selBreg ?v_2) ?v_3)) (= (selIType ?v_4) 11) false) ?v_2 (ite (Squash_0 ?v_1) 10 (select (icache ?v_1) (PC ?v_6))))) false true) (ite (ite (= (ite (ite (ite (= (selAreg ?v_7) ?v_8) true (= (selBreg ?v_7) ?v_8)) (= (selIType ?v_9) 11) false) ?v_7 (ite (Squash_0 ?v_6) 10 (select (icache ?v_6) (PC (+ (+ (- 3) s_0) t_0))))) ?v_2) (ite (ite (ite (ite (ite (= (selAreg ?v_11) ?v_12) true (= (selBreg ?v_11) ?v_12)) (= (selIType ?v_13) 11) false) false true) (ite (ite ?v_19 (ite (= (PC ?v_14) (PC ?v_10)) (ite (= (dcache ?v_18) (dcache ?v_14)) (= (RF ?v_18) (RF ?v_14)) false) false) (ite ?v_20 (= t__1 t__2) false)) (ite ?v_19 (ite ?v_20 (= t__1 (+ 1 t__2)) false) true) false) false) (ite (ite (ite (ite (ite (= (selAreg ?v_22) ?v_23) true (= (selBreg ?v_22) ?v_23)) (= (selIType ?v_24) 11) false) false true) (ite (ite ?v_30 (ite (= (dcache ?v_29) (dcache ?v_25)) (= (RF ?v_29) (RF ?v_25)) false) (ite ?v_31 (= t__1 t_0) false)) (ite ?v_30 (ite ?v_31 (= t__1 (+ (- 1) t_0)) false) true) false) false) (ite (ite (ite (ite (= (selAreg ?v_33) ?v_34) true (= (selBreg ?v_33) ?v_34)) (= (selIType ?v_35) 11) false) false true) (ite (ite ?v_41 (ite (= (dcache ?v_40) (dcache ?v_36)) (= (RF ?v_40) (RF ?v_36)) false) (ite ?v_42 (= t_0 t_1) false)) (ite ?v_41 (ite ?v_42 (= t_0 (+ (- 1) t_1)) false) true) false) false) false) false) false) false true) true)))))))))))))))))))))))
(check-sat)
(exit)
