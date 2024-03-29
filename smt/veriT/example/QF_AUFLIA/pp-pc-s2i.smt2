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
(declare-fun CLOCK_INIT () Bool)
(declare-fun INSTRISLOAD_S2E_INIT () Bool)
(declare-fun INSTRISSTORE_S2E_INIT () Bool)
(declare-fun STALL_S2R_INIT () Bool)
(declare-fun BDEST_S2E_INIT () Int)
(declare-fun PCDRVRESULT_S2E_INIT () Bool)
(declare-fun ADEST_S2E_INIT () Int)
(declare-fun BOPCODE_S2E_INIT () Int)
(declare-fun INSTRISLOAD_S2M_INIT () Bool)
(declare-fun DMEM_INIT () (Array Int Int))
(declare-fun STOREADDR_S2M_INIT () Int)
(declare-fun CACHEDOUT_S2_INIT () Int)
(declare-fun plus (Int Int) Int)
(declare-fun PC_S2I_INIT () Int)
(declare-fun PC_PLUS_S2I_INIT () Int)
(declare-fun ABUBBLE_S2R_INIT () Bool)
(declare-fun BBUBBLE_S2R_INIT () Bool)
(declare-fun SRC1_OF (Int) Int)
(declare-fun AINST_S2R_INIT () Int)
(declare-fun SRC2_OF (Int) Int)
(declare-fun BINST_S2R_INIT () Int)
(declare-fun OPCODE_OF (Int) Int)
(declare-fun IMEM_INIT () (Array Int Int))
(declare-fun DEST_OF (Int) Int)
(declare-fun NON_DET_STALL_INIT () Bool)
(declare-fun TAKENBRANCH_S2E_INIT () Bool)
(declare-fun BRANCH_CONDITION (Int Int) Bool)
(declare-fun BDEST_S2M_INIT () Int)
(declare-fun ADEST_S2M_INIT () Int)
(declare-fun BSBUS_S2E_INIT () Int)
(declare-fun BSRC2BUS_S2E_INIT () Int)
(declare-fun ALU (Int Int Int) Int)
(declare-fun ALU_OP_OF (Int) Int)
(declare-fun PCPLUS_S2R_INIT () Int)
(declare-fun AOPCODE_S2E_INIT () Int)
(declare-fun ASBUS_S2E_INIT () Int)
(declare-fun ASRC2BUS_S2E_INIT () Int)
(declare-fun NO_VALUE0 () Int)
(declare-fun BLOADDATA_S1W_INIT () Int)
(declare-fun BDATA_S2M_INIT () Int)
(declare-fun ADATA_S2M_INIT () Int)
(declare-fun REGFILE_INIT () (Array Int Int))
(declare-fun OFFSET_OF (Int) Int)
(declare-fun PC_CHAIN_S2R_INIT () Int)
(assert (let ((?v_13 (ite STALL_S2R_INIT false true)) (?v_0 (= BOPCODE_S2E_INIT 10)) (?v_1 (= BOPCODE_S2E_INIT 11)) (?v_3 (plus 4 PC_S2I_INIT)) (?v_15 (SRC1_OF AINST_S2R_INIT))) (let ((?v_16 (= ?v_15 BDEST_S2E_INIT)) (?v_19 (SRC2_OF AINST_S2R_INIT))) (let ((?v_20 (= ?v_19 BDEST_S2E_INIT)) (?v_6 (select IMEM_INIT PC_S2I_INIT))) (let ((?v_2 (OPCODE_OF ?v_6)) (?v_5 (select IMEM_INIT ?v_3))) (let ((?v_4 (OPCODE_OF ?v_5)) (?v_7 (DEST_OF ?v_6)) (?v_8 (SRC1_OF ?v_5)) (?v_10 (SRC2_OF ?v_5)) (?v_9 (= ?v_2 14)) (?v_11 (= (OPCODE_OF BINST_S2R_INIT) 10)) (?v_12 (DEST_OF BINST_S2R_INIT)) (?v_28 (ite NON_DET_STALL_INIT false true)) (?v_14 (OPCODE_OF AINST_S2R_INIT))) (let ((?v_26 (= ?v_14 13)) (?v_17 (ite (= ?v_15 0) 0 (ite ?v_16 2 (ite (= ?v_15 ADEST_S2E_INIT) 1 (ite (= ?v_15 BDEST_S2M_INIT) 4 (ite (= ?v_15 ADEST_S2M_INIT) 3 5)))))) (?v_22 (ite (ite INSTRISLOAD_S2E_INIT true INSTRISSTORE_S2E_INIT) (plus BSBUS_S2E_INIT BSRC2BUS_S2E_INIT) (ALU (ALU_OP_OF BOPCODE_S2E_INIT) BSBUS_S2E_INIT BSRC2BUS_S2E_INIT))) (?v_23 (ite PCDRVRESULT_S2E_INIT PCPLUS_S2R_INIT (ALU (ALU_OP_OF AOPCODE_S2E_INIT) ASBUS_S2E_INIT ASRC2BUS_S2E_INIT)))) (let ((?v_18 (= ?v_17 4)) (?v_24 (ite INSTRISLOAD_S2M_INIT (ite INSTRISLOAD_S2M_INIT CACHEDOUT_S2_INIT NO_VALUE0) BLOADDATA_S1W_INIT))) (let ((?v_27 (ite (= ?v_17 0) 0 (ite (= ?v_17 2) ?v_22 (ite (= ?v_17 1) ?v_23 (ite (ite ?v_18 INSTRISLOAD_S2M_INIT false) ?v_24 (ite ?v_18 BDATA_S2M_INIT (ite (= ?v_17 3) ADATA_S2M_INIT (select REGFILE_INIT ?v_15)))))))) (?v_21 (ite (= ?v_19 0) 0 (ite ?v_20 2 (ite (= ?v_19 ADEST_S2E_INIT) 1 (ite (= ?v_19 BDEST_S2M_INIT) 4 (ite (= ?v_19 ADEST_S2M_INIT) 3 5))))))) (let ((?v_25 (= ?v_21 4))) (let ((?v_29 (ite (ite (ite TAKENBRANCH_S2E_INIT false true) (ite ?v_13 (ite (= ?v_14 12) true (ite (= ?v_14 14) true (ite ?v_26 true (ite (= ?v_14 15) (BRANCH_CONDITION ?v_27 (ite (= ?v_21 0) 0 (ite (= ?v_21 2) ?v_22 (ite (= ?v_21 1) ?v_23 (ite (ite ?v_25 INSTRISLOAD_S2M_INIT false) ?v_24 (ite ?v_25 BDATA_S2M_INIT (ite (= ?v_21 3) ADATA_S2M_INIT (select REGFILE_INIT ?v_19)))))))) false)))) false) false) (ite ?v_26 ?v_27 (plus (OFFSET_OF AINST_S2R_INIT) (plus 4 PC_CHAIN_S2R_INIT))) PC_PLUS_S2I_INIT))) (not (ite (ite (ite CLOCK_INIT (ite (ite (ite INSTRISLOAD_S2E_INIT false true) true (ite INSTRISSTORE_S2E_INIT false true)) (ite ?v_13 (ite (ite INSTRISSTORE_S2E_INIT (= BDEST_S2E_INIT 0) true) (ite (ite PCDRVRESULT_S2E_INIT (ite (= ADEST_S2E_INIT 31) true (= ADEST_S2E_INIT 0)) true) (ite (ite INSTRISLOAD_S2E_INIT ?v_0 (ite ?v_0 false true)) (ite (ite INSTRISSTORE_S2E_INIT ?v_1 (ite ?v_1 false true)) (ite (ite INSTRISLOAD_S2M_INIT (= (select DMEM_INIT STOREADDR_S2M_INIT) CACHEDOUT_S2_INIT) true) (ite (= (plus 4 ?v_3) PC_PLUS_S2I_INIT) (ite (ite ABUBBLE_S2R_INIT false true) (ite BBUBBLE_S2R_INIT false true) false) false) false) false) false) false) false) false) false) false) (ite (ite (ite INSTRISLOAD_S2E_INIT ?v_16 false) false true) (ite (ite (ite INSTRISLOAD_S2E_INIT ?v_20 false) false true) (ite (ite (ite INSTRISLOAD_S2E_INIT (= (SRC1_OF BINST_S2R_INIT) BDEST_S2E_INIT) false) false true) (ite (ite (ite INSTRISLOAD_S2E_INIT (= (SRC2_OF BINST_S2R_INIT) BDEST_S2E_INIT) false) false true) (ite (ite (= ?v_2 10) false true) (ite (ite (= ?v_2 11) false true) (ite (ite (= ?v_4 12) false true) (ite (ite (= ?v_4 13) false true) (ite (ite (= ?v_4 14) false true) (ite (ite (= ?v_4 15) false true) (ite (ite (= ?v_8 ?v_7) false true) (ite (ite (= ?v_10 ?v_7) false true) (ite (ite (= (DEST_OF ?v_5) ?v_7) false true) (ite (ite (ite ?v_9 (= ?v_8 31) false) false true) (ite (ite (ite ?v_9 (= ?v_10 31) false) false true) (ite (ite (ite ?v_11 (= (SRC1_OF ?v_6) ?v_12) false) false true) (ite (ite (ite ?v_11 (= (SRC2_OF ?v_6) ?v_12) false) false true) (ite (ite (ite ?v_11 (= ?v_8 ?v_12) false) false true) (ite (ite ?v_11 (= ?v_10 ?v_12) false) false true) false) false) false) false) false) false) false) false) false) false) false) false) false) false) false) false) false) false) false) (= (ite ?v_28 ?v_29 PC_S2I_INIT) (ite (ite ?v_28 false true) PC_S2I_INIT ?v_29)) true)))))))))))))
(check-sat)
(exit)
