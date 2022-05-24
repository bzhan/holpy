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
(declare-fun opsel (Int) Int)
(declare-fun squash_1 (Int) Bool)
(declare-fun s__1 () Int)
(declare-fun fb_var_31 (Int) Bool)
(declare-fun s__2 () Int)
(declare-fun s__3 () Int)
(declare-fun icache () (Array Int Int))
(declare-fun PC (Int) Int)
(declare-fun RF (Int) (Array Int Int))
(declare-fun selAreg (Int) Int)
(declare-fun ALU (Int Int Int) Int)
(declare-fun constsel (Int) Int)
(declare-fun selBreg (Int) Int)
(declare-fun s_0 () Int)
(declare-fun selDest (Int) Int)
(declare-fun dcache (Int) (Array Int Int))
(declare-fun regAsel (Int) Int)
(declare-fun fb_var_33 (Int) Int)
(declare-fun fb_var_32 (Int) Int)
(declare-fun add (Int Int) Int)
(assert (let ((?v_19 (squash_1 s_0)) (?v_29 (+ 1 s_0))) (let ((?v_14 (RF ?v_29)) (?v_0 (+ 1 s__1))) (let ((?v_43 (squash_1 ?v_0)) (?v_18 (fb_var_31 s__1)) (?v_39 (squash_1 s__2)) (?v_6 (RF ?v_0)) (?v_27 (RF s_0)) (?v_36 (+ 2 s__3)) (?v_37 (+ 1 s__3)) (?v_40 (+ 2 s__2)) (?v_41 (+ 1 s__2)) (?v_42 (+ 3 s__2)) (?v_44 (+ 2 s__1)) (?v_45 (+ 3 s__1)) (?v_46 (+ 4 s__1)) (?v_38 (+ (- 1) s__2)) (?v_35 (+ (- 1) s__3))) (let ((?v_34 (squash_1 ?v_35)) (?v_33 (+ (- 2) s__3)) (?v_2 (PC (+ (- 3) s__3)))) (let ((?v_1 (ite ?v_43 10 (ite ?v_18 10 (ite ?v_39 10 (ite (fb_var_31 ?v_38) 10 (ite ?v_34 10 (ite (fb_var_31 ?v_33) 10 (select icache ?v_2))))))))) (let ((?v_3 (opsel ?v_1)) (?v_4 (select ?v_6 (selAreg ?v_1))) (?v_5 (constsel ?v_1)) (?v_7 (+ (- 1) s_0))) (let ((?v_20 (squash_1 ?v_7)) (?v_21 (fb_var_31 ?v_7)) (?v_8 (+ (- 2) s_0))) (let ((?v_22 (squash_1 ?v_8)) (?v_23 (fb_var_31 ?v_8)) (?v_24 (+ (- 3) s_0))) (let ((?v_10 (PC ?v_24))) (let ((?v_9 (ite ?v_19 10 (ite (fb_var_31 s_0) 10 (ite ?v_20 10 (ite ?v_21 10 (ite ?v_22 10 (ite ?v_23 10 (select icache ?v_10))))))))) (let ((?v_11 (opsel ?v_9)) (?v_12 (select ?v_14 (selAreg ?v_9))) (?v_13 (constsel ?v_9)) (?v_15 (+ (- 1) s__1)) (?v_16 (+ (- 2) s__1)) (?v_17 (+ (- 3) s__1)) (?v_30 (squash_1 ?v_24)) (?v_31 (fb_var_31 ?v_24)) (?v_32 (PC (+ (- 4) s_0)))) (let ((?v_26 (ite ?v_19 10 (ite ?v_20 10 (ite ?v_21 10 (ite ?v_22 10 (ite ?v_23 10 (ite ?v_30 10 (ite ?v_31 10 (select icache ?v_32)))))))))) (let ((?v_25 (opsel ?v_26)) (?v_28 (selDest ?v_26))) (not (ite (ite (= (ite (ite (= ?v_3 11) (ite (= ?v_4 10) false true) false) (ALU 12 ?v_2 ?v_5) (ite (= ?v_3 13) (ALU ?v_3 ?v_4 ?v_5) (ALU ?v_3 ?v_4 (select ?v_6 (selBreg ?v_1))))) (ite (ite (= 11 ?v_11) (ite (= ?v_12 10) false true) false) (ALU 12 ?v_10 ?v_13) (ite (= 13 ?v_11) (ALU ?v_11 ?v_12 ?v_13) (ALU ?v_11 ?v_12 (select ?v_14 (selBreg ?v_9)))))) false true) (ite (ite (= (= 14 (ite (squash_1 ?v_15) 10 (ite (fb_var_31 ?v_15) 10 (ite (squash_1 ?v_16) 10 (ite (fb_var_31 ?v_16) 10 (ite (squash_1 ?v_17) 10 (ite (fb_var_31 ?v_17) 10 (select icache (PC (+ (- 4) s__1)))))))))) ?v_18) (ite (= (ite (ite (= 15 ?v_25) true (ite (= ?v_25 11) true (ite (= ?v_25 14) true (= ?v_28 10)))) ?v_27 (store ?v_27 ?v_28 (ite (= 16 ?v_25) (select (dcache s_0) (regAsel ?v_26)) (fb_var_33 ?v_29)))) ?v_14) (ite (= (ite ?v_30 (fb_var_33 ?v_24) (ite ?v_31 (fb_var_32 ?v_24) (add ?v_32 17))) ?v_10) (ite (ite (squash_1 ?v_33) false true) (ite (ite ?v_34 (ite (= s__2 ?v_36) (ite (ite (fb_var_31 ?v_35) false true) (ite (ite (fb_var_31 s__3) false true) (ite (ite (fb_var_31 ?v_37) false true) (ite (ite (fb_var_31 ?v_36) false true) (ite (ite ?v_34 false true) (ite (ite (squash_1 s__3) false true) (ite (ite (squash_1 ?v_37) false true) (ite (ite (squash_1 ?v_36) false true) (ite (squash_1 (+ 3 s__3)) false true) false) false) false) false) false) false) false) false) false) (= s__2 s__3)) (ite (ite (squash_1 ?v_38) false true) (ite (ite ?v_39 (ite (= s__1 ?v_40) (ite (ite (fb_var_31 s__2) false true) (ite (ite (fb_var_31 ?v_41) false true) (ite (ite (fb_var_31 ?v_40) false true) (ite (ite (fb_var_31 ?v_42) false true) (ite (ite ?v_39 false true) (ite (ite (squash_1 ?v_41) false true) (ite (ite (squash_1 ?v_40) false true) (ite (ite (squash_1 ?v_42) false true) (ite (squash_1 (+ 4 s__2)) false true) false) false) false) false) false) false) false) false) false) (= s__1 s__2)) (ite (ite (squash_1 s__1) false true) (ite (ite ?v_43 (ite (= s__1 ?v_8) (ite (ite (fb_var_31 ?v_0) false true) (ite (ite (fb_var_31 ?v_44) false true) (ite (ite (fb_var_31 ?v_45) false true) (ite (ite (fb_var_31 ?v_46) false true) (ite (ite ?v_43 false true) (ite (ite (squash_1 ?v_44) false true) (ite (ite (squash_1 ?v_45) false true) (ite (ite (squash_1 ?v_46) false true) (ite (squash_1 (+ 5 s__1)) false true) false) false) false) false) false) false) false) false) false) (= s__1 s_0)) (ite (= (opsel 10) 10) (= (selDest 10) 10) false) false) false) false) false) false) false) false) false) false) false true) true))))))))))))))))
(check-sat)
(exit)
