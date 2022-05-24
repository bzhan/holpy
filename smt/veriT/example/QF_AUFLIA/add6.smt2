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
(declare-fun selAreg (Int) Int)
(declare-fun Stall_Control_0 (Int) Int)
(declare-fun s_0 () Int)
(declare-fun t_0 () Int)
(declare-fun selDest (Int) Int)
(declare-fun Stall_Control_1 (Int) Int)
(declare-fun selBreg (Int) Int)
(declare-fun selIType (Int) Int)
(declare-fun Squash_0 (Int) Bool)
(declare-fun icache (Int) (Array Int Int))
(declare-fun PC (Int) Int)
(declare-fun s__2 () Int)
(declare-fun t__2 () Int)
(declare-fun dcache (Int) Int)
(declare-fun RF (Int) Int)
(declare-fun s__1 () Int)
(declare-fun t__1 () Int)
(declare-fun s_1 () Int)
(declare-fun t_1 () Int)
(assert (let ((?v_12 (+ s__2 t__2)) (?v_14 (= s__1 s__2)) (?v_19 (+ t__1 s__1))) (let ((?v_20 (Stall_Control_0 ?v_19)) (?v_22 (Stall_Control_1 ?v_19))) (let ((?v_21 (selDest ?v_22))) (let ((?v_24 (ite (ite (= (selAreg ?v_20) ?v_21) true (= (selBreg ?v_20) ?v_21)) (= (selIType ?v_22) 11) false)) (?v_23 (+ (+ 1 t__1) s__1)) (?v_25 (= s__1 s_0)) (?v_26 (+ s_0 t_0))) (let ((?v_27 (Stall_Control_0 ?v_26)) (?v_29 (Stall_Control_1 ?v_26))) (let ((?v_28 (selDest ?v_29)) (?v_30 (+ (+ 1 s_0) t_0))) (let ((?v_31 (Stall_Control_0 ?v_30)) (?v_33 (Stall_Control_1 ?v_30))) (let ((?v_32 (selDest ?v_33))) (let ((?v_35 (ite (ite (= (selAreg ?v_31) ?v_32) true (= (selBreg ?v_31) ?v_32)) (= (selIType ?v_33) 11) false)) (?v_34 (+ (+ 2 s_0) t_0)) (?v_36 (= s_0 s_1)) (?v_38 (+ (- 2) s_0))) (let ((?v_0 (+ ?v_38 t_0))) (let ((?v_1 (Stall_Control_0 ?v_0)) (?v_3 (Stall_Control_1 ?v_0))) (let ((?v_2 (selDest ?v_3)) (?v_37 (+ (- 1) s_0))) (let ((?v_40 (+ ?v_37 t_0))) (let ((?v_39 (Stall_Control_0 ?v_40)) (?v_4 (+ (+ (- 2) s__2) t__2))) (let ((?v_5 (Stall_Control_0 ?v_4)) (?v_7 (Stall_Control_1 ?v_4))) (let ((?v_6 (selDest ?v_7)) (?v_8 (+ (+ (- 1) s__2) t__2))) (let ((?v_9 (Stall_Control_0 ?v_8)) (?v_11 (Stall_Control_1 ?v_8))) (let ((?v_10 (selDest ?v_11))) (let ((?v_13 (ite (ite (= (selAreg ?v_9) ?v_10) true (= (selBreg ?v_9) ?v_10)) (= (selIType ?v_11) 11) false)) (?v_15 (+ (+ (- 1) t__1) s__1))) (let ((?v_16 (Stall_Control_0 ?v_15)) (?v_18 (Stall_Control_1 ?v_15))) (let ((?v_17 (selDest ?v_18)) (?v_42 (Stall_Control_1 ?v_40))) (let ((?v_41 (selDest ?v_42))) (not (ite (ite (= (ite (ite (ite (= (selAreg ?v_1) ?v_2) true (= (selBreg ?v_1) ?v_2)) (= (selIType ?v_3) 11) false) ?v_1 (ite (Squash_0 ?v_0) 10 (select (icache ?v_0) (PC (+ (+ (- 3) s_0) t_0))))) ?v_39) (ite (ite (ite (ite (ite (= (selAreg ?v_5) ?v_6) true (= (selBreg ?v_5) ?v_6)) (= (selIType ?v_7) 11) false) false true) (ite (ite ?v_13 (ite (= (dcache ?v_12) (dcache ?v_8)) (ite (= (PC ?v_8) (PC ?v_4)) (= (RF ?v_12) (RF ?v_8)) false) false) (ite ?v_14 (= t__1 t__2) false)) (ite ?v_13 (ite ?v_14 (= t__1 (+ 1 t__2)) false) true) false) false) (ite (ite (ite (ite (ite (= (selAreg ?v_16) ?v_17) true (= (selBreg ?v_16) ?v_17)) (= (selIType ?v_18) 11) false) false true) (ite (ite ?v_24 (ite (= (dcache ?v_23) (dcache ?v_19)) (ite (= (PC ?v_19) (PC ?v_15)) (= (RF ?v_23) (RF ?v_19)) false) false) (ite ?v_25 (= t__1 t_0) false)) (ite ?v_24 (ite ?v_25 (= t__1 (+ (- 1) t_0)) false) true) false) false) (ite (ite (ite (ite (= (selAreg ?v_27) ?v_28) true (= (selBreg ?v_27) ?v_28)) (= (selIType ?v_29) 11) false) false true) (ite (ite ?v_35 (ite (= (dcache ?v_34) (dcache ?v_30)) (ite (= (PC ?v_30) (PC ?v_26)) (= (RF ?v_34) (RF ?v_30)) false) false) (ite ?v_36 (= t_0 t_1) false)) (ite ?v_35 (ite ?v_36 (= t_0 (+ (- 1) t_1)) false) true) false) false) false) false) false) (= (ite (Squash_0 ?v_15) 10 (select (icache (+ ?v_37 t__1)) (PC (+ ?v_38 t__2)))) (ite (ite (ite (= (selAreg ?v_39) ?v_41) true (= (selBreg ?v_39) ?v_41)) (= (selIType ?v_42) 11) false) ?v_39 (ite (Squash_0 ?v_40) 10 (select (icache ?v_40) (PC ?v_0))))) true)))))))))))))))))))))))))
(check-sat)
(exit)
