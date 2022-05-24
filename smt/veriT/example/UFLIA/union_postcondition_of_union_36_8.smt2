(set-info :smt-lib-version 2.6)
(set-logic UFLIA)
(set-info :source |
  GRASShopper benchmarks.
  Authors: Ruzica Piskac, Thomas Wies, and Damien Zufferey
  URL: http://cs.nyu.edu/wies/software/grasshopper
  See also: GRASShopper - Complete Heap Verification with Mixed Specifications. In TACAS 2014, pages 124-139.

  If this benchmark is satisfiable, GRASShopper reports the following error message:
  tests/spl/sl_sorted_set/union.spl:36:8-20:A postcondition of procedure union might not hold at this return point
  tests/spl/sl_sorted_set/union.spl:28:10-53:Related location: This is the postcondition that might not hold
  |)
(set-info :category "crafted")
(set-info :status unsat)

(declare-sort Loc 0)
(declare-sort SetLoc 0)
(declare-sort SetInt 0)
(declare-sort FldBool 0)
(declare-sort FldLoc 0)
(declare-sort FldInt 0)
(declare-fun null$0 () Loc)
(declare-fun read$0 (FldInt Loc) Int)
(declare-fun read$1 (FldLoc Loc) Loc)
(declare-fun write$0 (FldLoc Loc Loc) FldLoc)
(declare-fun ep$0 (FldLoc SetLoc Loc) Loc)
(declare-fun emptyset$0 () SetInt)
(declare-fun emptyset$1 () SetLoc)
(declare-fun setenum$0 (Int) SetInt)
(declare-fun setenum$1 (Loc) SetLoc)
(declare-fun union$0 (SetInt SetInt) SetInt)
(declare-fun union$1 (SetLoc SetLoc) SetLoc)
(declare-fun intersection$0 (SetInt SetInt) SetInt)
(declare-fun intersection$1 (SetLoc SetLoc) SetLoc)
(declare-fun setminus$0 (SetInt SetInt) SetInt)
(declare-fun setminus$1 (SetLoc SetLoc) SetLoc)
(declare-fun Btwn$0 (FldLoc Loc Loc Loc) Bool)
(declare-fun Frame$0 (SetLoc SetLoc FldLoc FldLoc) Bool)
(declare-fun Frame$1 (SetLoc SetLoc FldInt FldInt) Bool)
(declare-fun in$0 (Int SetInt) Bool)
(declare-fun in$1 (Loc SetLoc) Bool)
(declare-fun Alloc$0 () SetLoc)
(declare-fun Alloc_4$0 () SetLoc)
(declare-fun Axiom_20$0 () Bool)
(declare-fun Axiom_21$0 () Bool)
(declare-fun Axiom_22$0 () Bool)
(declare-fun Axiom_23$0 () Bool)
(declare-fun Axiom_24$0 () Bool)
(declare-fun Axiom_25$0 () Bool)
(declare-fun Axiom_26$0 () Bool)
(declare-fun Axiom_27$0 () Bool)
(declare-fun Axiom_28$0 () Bool)
(declare-fun FP$0 () SetLoc)
(declare-fun FP_6$0 () SetLoc)
(declare-fun FP_7$0 () SetLoc)
(declare-fun FP_Caller$0 () SetLoc)
(declare-fun FP_Caller_1$0 () SetLoc)
(declare-fun FP_Caller_final_3$0 () SetLoc)
(declare-fun content1$0 () SetInt)
(declare-fun content1_3$0 () SetInt)
(declare-fun content2$0 () SetInt)
(declare-fun content2_3$0 () SetInt)
(declare-fun data$0 () FldInt)
(declare-fun lst1$0 () Loc)
(declare-fun lst2$0 () Loc)
(declare-fun next$0 () FldLoc)
(declare-fun next_4$0 () FldLoc)
(declare-fun next_5$0 () FldLoc)
(declare-fun res_4$0 () Loc)
(declare-fun sk_?X_24$0 () SetLoc)
(declare-fun sk_?X_25$0 () SetLoc)
(declare-fun sk_?X_26$0 () SetLoc)
(declare-fun sk_?X_27$0 () SetLoc)
(declare-fun sk_?X_28$0 () SetLoc)
(declare-fun sk_?X_29$0 () SetLoc)
(declare-fun sk_?X_30$0 () SetLoc)
(declare-fun sk_?X_31$0 () SetLoc)
(declare-fun sk_?e_2$0 () Int)
(declare-fun sk_l1_3$0 () Loc)
(declare-fun sk_l2_3$0 () Loc)
(declare-fun sorted_set_c$0 (FldInt FldLoc Loc Loc) SetInt)
(declare-fun sorted_set_domain$0 (FldInt FldLoc Loc Loc) SetLoc)
(declare-fun sorted_set_struct$0 (SetLoc FldInt FldLoc Loc Loc SetInt) Bool)
(declare-fun t_98$0 () Loc)
(declare-fun t_99$0 () Int)
(declare-fun t_100$0 () Int)
(declare-fun t_101$0 () Int)
(declare-fun t_102$0 () Int)
(declare-fun t_103$0 () Int)
(declare-fun t_104$0 () Int)
(declare-fun t_105$0 () Int)
(declare-fun t_106$0 () Int)
(declare-fun t_107$0 () Int)
(declare-fun t_108$0 () Int)
(declare-fun t_109$0 () Int)
(declare-fun t_110$0 () Int)
(declare-fun t_111$0 () Int)
(declare-fun t_112$0 () Int)
(declare-fun t_113$0 () Int)
(declare-fun t_114$0 () Int)
(declare-fun t_115$0 () Int)
(declare-fun t_116$0 () Int)
(declare-fun t_117$0 () Int)
(declare-fun t_118$0 () Int)
(declare-fun t_119$0 () Int)
(declare-fun t_120$0 () Int)
(declare-fun t_121$0 () Int)
(declare-fun t_122$0 () Int)
(declare-fun t_123$0 () Int)
(declare-fun t_124$0 () Loc)
(declare-fun t_125$0 () Loc)
(declare-fun t_126$0 () Loc)
(declare-fun t_127$0 () Loc)
(declare-fun t_128$0 () Loc)
(declare-fun t_129$0 () Loc)
(declare-fun t_130$0 () Loc)
(declare-fun t_131$0 () Loc)
(declare-fun t_132$0 () Loc)
(declare-fun t_133$0 () Loc)
(declare-fun t_134$0 () Loc)
(declare-fun t_135$0 () Loc)
(declare-fun t_136$0 () Loc)
(declare-fun t_137$0 () Loc)
(declare-fun t_138$0 () Loc)
(declare-fun t_139$0 () Loc)
(declare-fun t_140$0 () Loc)
(declare-fun t_141$0 () Loc)
(declare-fun t_142$0 () Loc)
(declare-fun t_143$0 () Loc)
(declare-fun t_144$0 () Loc)
(declare-fun t_145$0 () Loc)
(declare-fun t_146$0 () Loc)
(declare-fun t_147$0 () Loc)
(declare-fun t_148$0 () Loc)
(declare-fun t_149$0 () Loc)
(declare-fun t_150$0 () Loc)
(declare-fun t_151$0 () Loc)
(declare-fun t_152$0 () Loc)
(declare-fun t_153$0 () Loc)
(declare-fun t_154$0 () Loc)
(declare-fun t_155$0 () Loc)
(declare-fun t_156$0 () Loc)
(declare-fun t_157$0 () Loc)
(declare-fun t_158$0 () Loc)
(declare-fun t_159$0 () Loc)
(declare-fun t_160$0 () Loc)
(declare-fun t_161$0 () Loc)
(declare-fun t_162$0 () Loc)
(declare-fun t_163$0 () Loc)
(declare-fun t_164$0 () Loc)
(declare-fun t_165$0 () Loc)
(declare-fun t_166$0 () Loc)
(declare-fun t_167$0 () Loc)
(declare-fun t_168$0 () Loc)
(declare-fun t_169$0 () Loc)
(declare-fun t_170$0 () Loc)
(declare-fun t_171$0 () Loc)
(declare-fun t_172$0 () Loc)
(declare-fun t_173$0 () Loc)
(declare-fun t_174$0 () Loc)
(declare-fun t_175$0 () Loc)
(declare-fun t_176$0 () Loc)
(declare-fun t_177$0 () Loc)
(declare-fun t_178$0 () Loc)
(declare-fun t_179$0 () Loc)
(declare-fun t_180$0 () Loc)
(declare-fun t_181$0 () Loc)
(declare-fun t_182$0 () Loc)
(declare-fun tmp_3$0 () Loc)
(declare-fun witness$0 (FldInt Int SetInt) Loc)

(assert (=
  (witness$0 data$0 sk_?e_2$0
    (sorted_set_c$0 data$0 next_5$0 res_4$0 null$0))
  t_182$0))

(assert (=
  (witness$0 data$0 sk_?e_2$0
    (sorted_set_c$0 data$0 next_4$0 tmp_3$0 null$0))
  t_181$0))

(assert (= (witness$0 data$0 sk_?e_2$0 (sorted_set_c$0 data$0 next$0 lst2$0 null$0))
  t_180$0))

(assert (= (witness$0 data$0 sk_?e_2$0 (sorted_set_c$0 data$0 next$0 lst1$0 null$0))
  t_179$0))

(assert (=
  (witness$0 data$0 sk_?e_2$0
    (sorted_set_c$0 data$0 next$0 (read$1 next$0 lst1$0) null$0))
  t_178$0))

(assert (=
  (witness$0 data$0 (read$0 data$0 sk_l2_3$0)
    (sorted_set_c$0 data$0 next_5$0 res_4$0 null$0))
  t_177$0))

(assert (=
  (witness$0 data$0 (read$0 data$0 sk_l2_3$0)
    (sorted_set_c$0 data$0 next_4$0 tmp_3$0 null$0))
  t_176$0))

(assert (=
  (witness$0 data$0 (read$0 data$0 sk_l2_3$0)
    (sorted_set_c$0 data$0 next$0 lst2$0 null$0))
  t_175$0))

(assert (=
  (witness$0 data$0 (read$0 data$0 sk_l2_3$0)
    (sorted_set_c$0 data$0 next$0 lst1$0 null$0))
  t_174$0))

(assert (=
  (witness$0 data$0 (read$0 data$0 sk_l2_3$0)
    (sorted_set_c$0 data$0 next$0 (read$1 next$0 lst1$0) null$0))
  t_173$0))

(assert (=
  (witness$0 data$0 (read$0 data$0 sk_l1_3$0)
    (sorted_set_c$0 data$0 next_5$0 res_4$0 null$0))
  t_172$0))

(assert (=
  (witness$0 data$0 (read$0 data$0 sk_l1_3$0)
    (sorted_set_c$0 data$0 next_4$0 tmp_3$0 null$0))
  t_171$0))

(assert (=
  (witness$0 data$0 (read$0 data$0 sk_l1_3$0)
    (sorted_set_c$0 data$0 next$0 lst2$0 null$0))
  t_170$0))

(assert (=
  (witness$0 data$0 (read$0 data$0 sk_l1_3$0)
    (sorted_set_c$0 data$0 next$0 lst1$0 null$0))
  t_169$0))

(assert (=
  (witness$0 data$0 (read$0 data$0 sk_l1_3$0)
    (sorted_set_c$0 data$0 next$0 (read$1 next$0 lst1$0) null$0))
  t_168$0))

(assert (=
  (witness$0 data$0 (read$0 data$0 lst2$0)
    (sorted_set_c$0 data$0 next_5$0 res_4$0 null$0))
  t_167$0))

(assert (=
  (witness$0 data$0 (read$0 data$0 lst2$0)
    (sorted_set_c$0 data$0 next_4$0 tmp_3$0 null$0))
  t_166$0))

(assert (=
  (witness$0 data$0 (read$0 data$0 lst2$0)
    (sorted_set_c$0 data$0 next$0 lst2$0 null$0))
  t_165$0))

(assert (=
  (witness$0 data$0 (read$0 data$0 lst2$0)
    (sorted_set_c$0 data$0 next$0 lst1$0 null$0))
  t_164$0))

(assert (=
  (witness$0 data$0 (read$0 data$0 lst2$0)
    (sorted_set_c$0 data$0 next$0 (read$1 next$0 lst1$0) null$0))
  t_163$0))

(assert (=
  (witness$0 data$0 (read$0 data$0 lst1$0)
    (sorted_set_c$0 data$0 next_5$0 res_4$0 null$0))
  t_162$0))

(assert (=
  (witness$0 data$0 (read$0 data$0 lst1$0)
    (sorted_set_c$0 data$0 next_4$0 tmp_3$0 null$0))
  t_161$0))

(assert (=
  (witness$0 data$0 (read$0 data$0 lst1$0)
    (sorted_set_c$0 data$0 next$0 lst2$0 null$0))
  t_160$0))

(assert (=
  (witness$0 data$0 (read$0 data$0 lst1$0)
    (sorted_set_c$0 data$0 next$0 lst1$0 null$0))
  t_159$0))

(assert (=
  (witness$0 data$0 (read$0 data$0 lst1$0)
    (sorted_set_c$0 data$0 next$0 (read$1 next$0 lst1$0) null$0))
  t_158$0))

(assert (=
  (ep$0 next$0 FP_6$0
    (witness$0 data$0 sk_?e_2$0
      (sorted_set_c$0 data$0 next_5$0 res_4$0 null$0)))
  t_157$0))

(assert (=
  (ep$0 next$0 FP_6$0
    (witness$0 data$0 sk_?e_2$0
      (sorted_set_c$0 data$0 next_4$0 tmp_3$0 null$0)))
  t_156$0))

(assert (=
  (ep$0 next$0 FP_6$0
    (witness$0 data$0 sk_?e_2$0 (sorted_set_c$0 data$0 next$0 lst2$0 null$0)))
  t_155$0))

(assert (=
  (ep$0 next$0 FP_6$0
    (witness$0 data$0 sk_?e_2$0 (sorted_set_c$0 data$0 next$0 lst1$0 null$0)))
  t_154$0))

(assert (=
  (ep$0 next$0 FP_6$0
    (witness$0 data$0 sk_?e_2$0
      (sorted_set_c$0 data$0 next$0 (read$1 next$0 lst1$0) null$0)))
  t_153$0))

(assert (=
  (ep$0 next$0 FP_6$0
    (witness$0 data$0 (read$0 data$0 sk_l2_3$0)
      (sorted_set_c$0 data$0 next_5$0 res_4$0 null$0)))
  t_152$0))

(assert (=
  (ep$0 next$0 FP_6$0
    (witness$0 data$0 (read$0 data$0 sk_l2_3$0)
      (sorted_set_c$0 data$0 next_4$0 tmp_3$0 null$0)))
  t_151$0))

(assert (=
  (ep$0 next$0 FP_6$0
    (witness$0 data$0 (read$0 data$0 sk_l2_3$0)
      (sorted_set_c$0 data$0 next$0 lst2$0 null$0)))
  t_150$0))

(assert (=
  (ep$0 next$0 FP_6$0
    (witness$0 data$0 (read$0 data$0 sk_l2_3$0)
      (sorted_set_c$0 data$0 next$0 lst1$0 null$0)))
  t_149$0))

(assert (=
  (ep$0 next$0 FP_6$0
    (witness$0 data$0 (read$0 data$0 sk_l2_3$0)
      (sorted_set_c$0 data$0 next$0 (read$1 next$0 lst1$0) null$0)))
  t_148$0))

(assert (=
  (ep$0 next$0 FP_6$0
    (witness$0 data$0 (read$0 data$0 sk_l1_3$0)
      (sorted_set_c$0 data$0 next_5$0 res_4$0 null$0)))
  t_147$0))

(assert (=
  (ep$0 next$0 FP_6$0
    (witness$0 data$0 (read$0 data$0 sk_l1_3$0)
      (sorted_set_c$0 data$0 next_4$0 tmp_3$0 null$0)))
  t_146$0))

(assert (=
  (ep$0 next$0 FP_6$0
    (witness$0 data$0 (read$0 data$0 sk_l1_3$0)
      (sorted_set_c$0 data$0 next$0 lst2$0 null$0)))
  t_145$0))

(assert (=
  (ep$0 next$0 FP_6$0
    (witness$0 data$0 (read$0 data$0 sk_l1_3$0)
      (sorted_set_c$0 data$0 next$0 lst1$0 null$0)))
  t_144$0))

(assert (=
  (ep$0 next$0 FP_6$0
    (witness$0 data$0 (read$0 data$0 sk_l1_3$0)
      (sorted_set_c$0 data$0 next$0 (read$1 next$0 lst1$0) null$0)))
  t_143$0))

(assert (=
  (ep$0 next$0 FP_6$0
    (witness$0 data$0 (read$0 data$0 lst2$0)
      (sorted_set_c$0 data$0 next_5$0 res_4$0 null$0)))
  t_142$0))

(assert (=
  (ep$0 next$0 FP_6$0
    (witness$0 data$0 (read$0 data$0 lst2$0)
      (sorted_set_c$0 data$0 next_4$0 tmp_3$0 null$0)))
  t_141$0))

(assert (=
  (ep$0 next$0 FP_6$0
    (witness$0 data$0 (read$0 data$0 lst2$0)
      (sorted_set_c$0 data$0 next$0 lst2$0 null$0)))
  t_140$0))

(assert (=
  (ep$0 next$0 FP_6$0
    (witness$0 data$0 (read$0 data$0 lst2$0)
      (sorted_set_c$0 data$0 next$0 lst1$0 null$0)))
  t_139$0))

(assert (=
  (ep$0 next$0 FP_6$0
    (witness$0 data$0 (read$0 data$0 lst2$0)
      (sorted_set_c$0 data$0 next$0 (read$1 next$0 lst1$0) null$0)))
  t_138$0))

(assert (=
  (ep$0 next$0 FP_6$0
    (witness$0 data$0 (read$0 data$0 lst1$0)
      (sorted_set_c$0 data$0 next_5$0 res_4$0 null$0)))
  t_137$0))

(assert (=
  (ep$0 next$0 FP_6$0
    (witness$0 data$0 (read$0 data$0 lst1$0)
      (sorted_set_c$0 data$0 next_4$0 tmp_3$0 null$0)))
  t_136$0))

(assert (=
  (ep$0 next$0 FP_6$0
    (witness$0 data$0 (read$0 data$0 lst1$0)
      (sorted_set_c$0 data$0 next$0 lst2$0 null$0)))
  t_135$0))

(assert (=
  (ep$0 next$0 FP_6$0
    (witness$0 data$0 (read$0 data$0 lst1$0)
      (sorted_set_c$0 data$0 next$0 lst1$0 null$0)))
  t_134$0))

(assert (=
  (ep$0 next$0 FP_6$0
    (witness$0 data$0 (read$0 data$0 lst1$0)
      (sorted_set_c$0 data$0 next$0 (read$1 next$0 lst1$0) null$0)))
  t_133$0))

(assert (= (ep$0 next$0 FP_6$0 tmp_3$0) t_132$0))

(assert (= (ep$0 next$0 FP_6$0 sk_l2_3$0) t_131$0))

(assert (= (ep$0 next$0 FP_6$0 sk_l1_3$0) t_130$0))

(assert (= (ep$0 next$0 FP_6$0 res_4$0) t_129$0))

(assert (= (ep$0 next$0 FP_6$0 lst2$0) t_128$0))

(assert (= (ep$0 next$0 FP_6$0 lst1$0) t_127$0))

(assert (= (ep$0 next$0 FP_6$0 (read$1 next$0 lst1$0)) t_126$0))

(assert (= (ep$0 next$0 FP_6$0 null$0) t_125$0))

(assert (= (read$1 next_4$0 lst1$0) t_124$0))

(assert (=
  (read$0 data$0
    (witness$0 data$0 sk_?e_2$0
      (sorted_set_c$0 data$0 next_5$0 res_4$0 null$0)))
  t_123$0))

(assert (=
  (read$0 data$0
    (witness$0 data$0 sk_?e_2$0
      (sorted_set_c$0 data$0 next_4$0 tmp_3$0 null$0)))
  t_122$0))

(assert (=
  (read$0 data$0
    (witness$0 data$0 sk_?e_2$0 (sorted_set_c$0 data$0 next$0 lst2$0 null$0)))
  t_121$0))

(assert (=
  (read$0 data$0
    (witness$0 data$0 sk_?e_2$0 (sorted_set_c$0 data$0 next$0 lst1$0 null$0)))
  t_120$0))

(assert (=
  (read$0 data$0
    (witness$0 data$0 sk_?e_2$0
      (sorted_set_c$0 data$0 next$0 (read$1 next$0 lst1$0) null$0)))
  t_119$0))

(assert (=
  (read$0 data$0
    (witness$0 data$0 (read$0 data$0 sk_l2_3$0)
      (sorted_set_c$0 data$0 next_5$0 res_4$0 null$0)))
  t_118$0))

(assert (=
  (read$0 data$0
    (witness$0 data$0 (read$0 data$0 sk_l2_3$0)
      (sorted_set_c$0 data$0 next_4$0 tmp_3$0 null$0)))
  t_117$0))

(assert (=
  (read$0 data$0
    (witness$0 data$0 (read$0 data$0 sk_l2_3$0)
      (sorted_set_c$0 data$0 next$0 lst2$0 null$0)))
  t_116$0))

(assert (=
  (read$0 data$0
    (witness$0 data$0 (read$0 data$0 sk_l2_3$0)
      (sorted_set_c$0 data$0 next$0 lst1$0 null$0)))
  t_115$0))

(assert (=
  (read$0 data$0
    (witness$0 data$0 (read$0 data$0 sk_l2_3$0)
      (sorted_set_c$0 data$0 next$0 (read$1 next$0 lst1$0) null$0)))
  t_114$0))

(assert (=
  (read$0 data$0
    (witness$0 data$0 (read$0 data$0 sk_l1_3$0)
      (sorted_set_c$0 data$0 next_5$0 res_4$0 null$0)))
  t_113$0))

(assert (=
  (read$0 data$0
    (witness$0 data$0 (read$0 data$0 sk_l1_3$0)
      (sorted_set_c$0 data$0 next_4$0 tmp_3$0 null$0)))
  t_112$0))

(assert (=
  (read$0 data$0
    (witness$0 data$0 (read$0 data$0 sk_l1_3$0)
      (sorted_set_c$0 data$0 next$0 lst2$0 null$0)))
  t_111$0))

(assert (=
  (read$0 data$0
    (witness$0 data$0 (read$0 data$0 sk_l1_3$0)
      (sorted_set_c$0 data$0 next$0 lst1$0 null$0)))
  t_110$0))

(assert (=
  (read$0 data$0
    (witness$0 data$0 (read$0 data$0 sk_l1_3$0)
      (sorted_set_c$0 data$0 next$0 (read$1 next$0 lst1$0) null$0)))
  t_109$0))

(assert (=
  (read$0 data$0
    (witness$0 data$0 (read$0 data$0 lst2$0)
      (sorted_set_c$0 data$0 next_5$0 res_4$0 null$0)))
  t_108$0))

(assert (=
  (read$0 data$0
    (witness$0 data$0 (read$0 data$0 lst2$0)
      (sorted_set_c$0 data$0 next_4$0 tmp_3$0 null$0)))
  t_107$0))

(assert (=
  (read$0 data$0
    (witness$0 data$0 (read$0 data$0 lst2$0)
      (sorted_set_c$0 data$0 next$0 lst2$0 null$0)))
  t_106$0))

(assert (=
  (read$0 data$0
    (witness$0 data$0 (read$0 data$0 lst2$0)
      (sorted_set_c$0 data$0 next$0 lst1$0 null$0)))
  t_105$0))

(assert (=
  (read$0 data$0
    (witness$0 data$0 (read$0 data$0 lst2$0)
      (sorted_set_c$0 data$0 next$0 (read$1 next$0 lst1$0) null$0)))
  t_104$0))

(assert (=
  (read$0 data$0
    (witness$0 data$0 (read$0 data$0 lst1$0)
      (sorted_set_c$0 data$0 next_5$0 res_4$0 null$0)))
  t_103$0))

(assert (=
  (read$0 data$0
    (witness$0 data$0 (read$0 data$0 lst1$0)
      (sorted_set_c$0 data$0 next_4$0 tmp_3$0 null$0)))
  t_102$0))

(assert (=
  (read$0 data$0
    (witness$0 data$0 (read$0 data$0 lst1$0)
      (sorted_set_c$0 data$0 next$0 lst2$0 null$0)))
  t_101$0))

(assert (=
  (read$0 data$0
    (witness$0 data$0 (read$0 data$0 lst1$0)
      (sorted_set_c$0 data$0 next$0 lst1$0 null$0)))
  t_100$0))

(assert (=
  (read$0 data$0
    (witness$0 data$0 (read$0 data$0 lst1$0)
      (sorted_set_c$0 data$0 next$0 (read$1 next$0 lst1$0) null$0)))
  t_99$0))

(assert (= (read$1 (write$0 next_4$0 lst1$0 tmp_3$0) lst1$0) t_98$0))

(assert (forall ((?d_12 Loc) (?x Loc) (?y Loc))
        (or (= ?y ?x)
            (= (read$1 next_4$0 ?y) (read$1 (write$0 next_4$0 ?x ?d_12) ?y)))))

(assert (forall ((?d_12 Loc) (?x Loc))
        (= (read$1 (write$0 next_4$0 ?x ?d_12) ?x) ?d_12)))

(assert (forall ((?f FldLoc)) (= (read$1 ?f null$0) null$0)))

(assert (forall ((x Loc) (y Loc))
        (or (and (= x y) (in$1 x (setenum$1 y)))
            (and (not (= x y)) (not (in$1 x (setenum$1 y)))))))

(assert (forall ((X SetLoc) (Y SetLoc) (x Loc))
        (or (and (in$1 x X) (in$1 x (setminus$1 X Y)) (not (in$1 x Y)))
            (and (or (in$1 x Y) (not (in$1 x X)))
                 (not (in$1 x (setminus$1 X Y)))))))

(assert (forall ((X SetLoc) (Y SetLoc) (x Loc))
        (or (and (in$1 x X) (in$1 x Y) (in$1 x (intersection$1 X Y)))
            (and (or (not (in$1 x X)) (not (in$1 x Y)))
                 (not (in$1 x (intersection$1 X Y)))))))

(assert (forall ((X SetLoc) (Y SetLoc) (x Loc))
        (or (and (in$1 x (union$1 X Y)) (or (in$1 x X) (in$1 x Y)))
            (and (not (in$1 x X)) (not (in$1 x Y))
                 (not (in$1 x (union$1 X Y)))))))

(assert (forall ((x Loc)) (not (in$1 x emptyset$1))))

(assert (forall ((x Int) (y Int))
        (or (and (= x y) (in$0 x (setenum$0 y)))
            (and (not (= x y)) (not (in$0 x (setenum$0 y)))))))

(assert (forall ((X SetInt) (Y SetInt) (x Int))
        (or (and (in$0 x X) (in$0 x (setminus$0 X Y)) (not (in$0 x Y)))
            (and (or (in$0 x Y) (not (in$0 x X)))
                 (not (in$0 x (setminus$0 X Y)))))))

(assert (forall ((X SetInt) (Y SetInt) (x Int))
        (or (and (in$0 x X) (in$0 x Y) (in$0 x (intersection$0 X Y)))
            (and (or (not (in$0 x X)) (not (in$0 x Y)))
                 (not (in$0 x (intersection$0 X Y)))))))

(assert (forall ((X SetInt) (Y SetInt) (x Int))
        (or (and (in$0 x (union$0 X Y)) (or (in$0 x X) (in$0 x Y)))
            (and (not (in$0 x X)) (not (in$0 x Y))
                 (not (in$0 x (union$0 X Y)))))))

(assert (forall ((x Int)) (not (in$0 x emptyset$0))))

(assert (or (and (Btwn$0 next$0 (read$1 next$0 lst1$0) null$0 null$0) Axiom_20$0)
    (not
         (sorted_set_struct$0 sk_?X_30$0 data$0 next$0 (read$1 next$0 lst1$0)
           null$0 content1_3$0))))

(assert (or (not Axiom_21$0)
    (forall ((l1 Loc) (l2 Loc))
            (or (= l1 l2) (< (read$0 data$0 l1) (read$0 data$0 l2))
                (not (Btwn$0 next$0 l1 l2 null$0)) (not (in$1 l1 sk_?X_27$0))
                (not (in$1 l2 sk_?X_27$0))))))

(assert (or (and (Btwn$0 next$0 lst2$0 null$0 null$0) Axiom_22$0)
    (not
         (sorted_set_struct$0 sk_?X_26$0 data$0 next$0 lst2$0 null$0
           content2$0))))

(assert (or (not Axiom_23$0)
    (forall ((l1 Loc) (l2 Loc))
            (or (= l1 l2) (< (read$0 data$0 l1) (read$0 data$0 l2))
                (not (Btwn$0 next$0 l1 l2 null$0)) (not (in$1 l1 sk_?X_29$0))
                (not (in$1 l2 sk_?X_29$0))))))

(assert (or (and (Btwn$0 next_4$0 tmp_3$0 null$0 null$0) Axiom_24$0)
    (not
         (sorted_set_struct$0 sk_?X_24$0 data$0 next_4$0 tmp_3$0 null$0
           (union$0 content1_3$0 content2_3$0)))))

(assert (or (not Axiom_25$0)
    (forall ((l1 Loc) (l2 Loc))
            (or (= l1 l2) (< (read$0 data$0 l1) (read$0 data$0 l2))
                (not (Btwn$0 next_5$0 l1 l2 null$0))
                (not (in$1 l1 sk_?X_31$0)) (not (in$1 l2 sk_?X_31$0))))))

(assert (= FP_7$0
  (union$1 (setminus$1 FP$0 FP_6$0)
    (union$1 (intersection$1 Alloc_4$0 FP_6$0)
      (setminus$1 Alloc_4$0 Alloc$0)))))

(assert (= FP_Caller_final_3$0 (union$1 FP_Caller_1$0 FP_7$0)))

(assert (= res_4$0 lst1$0))

(assert (Frame$1 FP_6$0 Alloc$0 data$0 data$0))

(assert (= Alloc_4$0 (union$1 FP_7$0 Alloc_4$0)))

(assert (= emptyset$1 (intersection$1 sk_?X_27$0 sk_?X_26$0)))

(assert (= content2$0 (sorted_set_c$0 data$0 next$0 lst2$0 null$0)))

(assert (= sk_?X_25$0 FP$0))

(assert (= sk_?X_27$0 (sorted_set_domain$0 data$0 next$0 lst1$0 null$0)))

(assert (sorted_set_struct$0 sk_?X_26$0 data$0 next$0 lst2$0 null$0 content2$0))

(assert (= emptyset$1 (intersection$1 sk_?X_30$0 sk_?X_29$0)))

(assert (= content2_3$0 (sorted_set_c$0 data$0 next$0 lst2$0 null$0)))

(assert (= sk_?X_28$0 FP_6$0))

(assert (= sk_?X_30$0
  (sorted_set_domain$0 data$0 next$0 (read$1 next$0 lst1$0) null$0)))

(assert (sorted_set_struct$0 sk_?X_29$0 data$0 next$0 lst2$0 null$0 content2_3$0))

(assert (= (union$0 content1_3$0 content2_3$0)
  (sorted_set_c$0 data$0 next_4$0 tmp_3$0 null$0)))

(assert (= sk_?X_24$0 (sorted_set_domain$0 data$0 next_4$0 tmp_3$0 null$0)))

(assert (= sk_?X_31$0
  (union$1 (intersection$1 Alloc_4$0 FP$0) (setminus$1 Alloc_4$0 Alloc$0))))

(assert (not (= lst1$0 null$0)))

(assert (not (in$1 null$0 Alloc$0)))

(assert (forall ((l1 Loc))
        (or
            (= l1
              (witness$0 data$0 (read$0 data$0 l1)
                (sorted_set_c$0 data$0 next$0 (read$1 next$0 lst1$0) null$0)))
            (not
                 (in$1 l1
                   (sorted_set_domain$0 data$0 next$0 (read$1 next$0 lst1$0)
                     null$0))))))

(assert (forall ((l1 Loc))
        (or
            (= l1
              (witness$0 data$0 (read$0 data$0 l1)
                (sorted_set_c$0 data$0 next$0 lst2$0 null$0)))
            (not (in$1 l1 (sorted_set_domain$0 data$0 next$0 lst2$0 null$0))))))

(assert (forall ((l1 Loc))
        (or
            (= l1
              (witness$0 data$0 (read$0 data$0 l1)
                (sorted_set_c$0 data$0 next_5$0 res_4$0 null$0)))
            (not
                 (in$1 l1
                   (sorted_set_domain$0 data$0 next_5$0 res_4$0 null$0))))))

(assert (forall ((l1 Loc))
        (or
            (in$0 (read$0 data$0 l1)
              (sorted_set_c$0 data$0 next$0 lst1$0 null$0))
            (not (in$1 l1 (sorted_set_domain$0 data$0 next$0 lst1$0 null$0))))))

(assert (forall ((l1 Loc))
        (or
            (in$0 (read$0 data$0 l1)
              (sorted_set_c$0 data$0 next_4$0 tmp_3$0 null$0))
            (not
                 (in$1 l1
                   (sorted_set_domain$0 data$0 next_4$0 tmp_3$0 null$0))))))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 (read$1 next$0 lst1$0) l1 null$0)
                 (in$1 l1
                   (sorted_set_domain$0 data$0 next$0 (read$1 next$0 lst1$0)
                     null$0))
                 (not (= l1 null$0)))
            (and
                 (or (= l1 null$0)
                     (not (Btwn$0 next$0 (read$1 next$0 lst1$0) l1 null$0)))
                 (not
                      (in$1 l1
                        (sorted_set_domain$0 data$0 next$0
                          (read$1 next$0 lst1$0) null$0)))))))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 lst2$0 l1 null$0)
                 (in$1 l1 (sorted_set_domain$0 data$0 next$0 lst2$0 null$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 lst2$0 l1 null$0)))
                 (not
                      (in$1 l1
                        (sorted_set_domain$0 data$0 next$0 lst2$0 null$0)))))))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next_5$0 res_4$0 l1 null$0)
                 (in$1 l1
                   (sorted_set_domain$0 data$0 next_5$0 res_4$0 null$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next_5$0 res_4$0 l1 null$0)))
                 (not
                      (in$1 l1
                        (sorted_set_domain$0 data$0 next_5$0 res_4$0 null$0)))))))

(assert (forall ((v Int))
        (or
            (= v
              (read$0 data$0
                (witness$0 data$0 v
                  (sorted_set_c$0 data$0 next$0 lst1$0 null$0))))
            (not (in$0 v (sorted_set_c$0 data$0 next$0 lst1$0 null$0))))))

(assert (forall ((v Int))
        (or
            (= v
              (read$0 data$0
                (witness$0 data$0 v
                  (sorted_set_c$0 data$0 next_4$0 tmp_3$0 null$0))))
            (not (in$0 v (sorted_set_c$0 data$0 next_4$0 tmp_3$0 null$0))))))

(assert (forall ((v Int))
        (or
            (=
              (witness$0 data$0 v
                (sorted_set_c$0 data$0 next$0 (read$1 next$0 lst1$0) null$0))
              null$0)
            (in$0 v
              (sorted_set_c$0 data$0 next$0 (read$1 next$0 lst1$0) null$0)))))

(assert (forall ((v Int))
        (or
            (=
              (witness$0 data$0 v
                (sorted_set_c$0 data$0 next$0 lst2$0 null$0))
              null$0)
            (in$0 v (sorted_set_c$0 data$0 next$0 lst2$0 null$0)))))

(assert (forall ((v Int))
        (or
            (=
              (witness$0 data$0 v
                (sorted_set_c$0 data$0 next_5$0 res_4$0 null$0))
              null$0)
            (in$0 v (sorted_set_c$0 data$0 next_5$0 res_4$0 null$0)))))

(assert (forall ((v Int))
        (or
            (in$1
              (witness$0 data$0 v
                (sorted_set_c$0 data$0 next$0 lst1$0 null$0))
              (sorted_set_domain$0 data$0 next$0 lst1$0 null$0))
            (not (in$0 v (sorted_set_c$0 data$0 next$0 lst1$0 null$0))))))

(assert (forall ((v Int))
        (or
            (in$1
              (witness$0 data$0 v
                (sorted_set_c$0 data$0 next_4$0 tmp_3$0 null$0))
              (sorted_set_domain$0 data$0 next_4$0 tmp_3$0 null$0))
            (not (in$0 v (sorted_set_c$0 data$0 next_4$0 tmp_3$0 null$0))))))

(assert (forall ((?X SetLoc) (?f FldLoc) (?x Loc) (?y Loc))
        (or (Btwn$0 ?f ?x (ep$0 ?f ?X ?x) ?y) (not (Btwn$0 ?f ?x ?y ?y))
            (not (in$1 ?y ?X)))))

(assert (forall ((?X SetLoc) (?f FldLoc) (?x Loc) (?y Loc))
        (or (not (Btwn$0 ?f ?x ?y ?y)) (not (in$1 ?y ?X))
            (in$1 (ep$0 ?f ?X ?x) ?X))))

(assert (or (and Axiom_28$0 Axiom_27$0 Axiom_26$0)
    (not (Frame$0 FP_6$0 Alloc$0 next$0 next_4$0))))

(assert (or (not Axiom_20$0)
    (forall ((l1 Loc) (l2 Loc))
            (or (= l1 l2) (< (read$0 data$0 l1) (read$0 data$0 l2))
                (not (Btwn$0 next$0 l1 l2 null$0)) (not (in$1 l1 sk_?X_30$0))
                (not (in$1 l2 sk_?X_30$0))))))

(assert (or (and (Btwn$0 next$0 lst1$0 null$0 null$0) Axiom_21$0)
    (not
         (sorted_set_struct$0 sk_?X_27$0 data$0 next$0 lst1$0 null$0
           content1$0))))

(assert (or (not Axiom_22$0)
    (forall ((l1 Loc) (l2 Loc))
            (or (= l1 l2) (< (read$0 data$0 l1) (read$0 data$0 l2))
                (not (Btwn$0 next$0 l1 l2 null$0)) (not (in$1 l1 sk_?X_26$0))
                (not (in$1 l2 sk_?X_26$0))))))

(assert (or (and (Btwn$0 next$0 lst2$0 null$0 null$0) Axiom_23$0)
    (not
         (sorted_set_struct$0 sk_?X_29$0 data$0 next$0 lst2$0 null$0
           content2_3$0))))

(assert (or (not Axiom_24$0)
    (forall ((l1 Loc) (l2 Loc))
            (or (= l1 l2) (< (read$0 data$0 l1) (read$0 data$0 l2))
                (not (Btwn$0 next_4$0 l1 l2 null$0))
                (not (in$1 l1 sk_?X_24$0)) (not (in$1 l2 sk_?X_24$0))))))

(assert (or (and (Btwn$0 next_5$0 res_4$0 null$0 null$0) Axiom_25$0)
    (not
         (sorted_set_struct$0 sk_?X_31$0 data$0 next_5$0 res_4$0 null$0
           (union$0 content1$0 content2$0)))))

(assert (= FP_Caller_1$0 (setminus$1 FP_Caller$0 FP$0)))

(assert (= next_5$0 (write$0 next_4$0 lst1$0 tmp_3$0)))

(assert (< (read$0 data$0 lst1$0) (read$0 data$0 lst2$0)))

(assert (Frame$0 FP_6$0 Alloc$0 next$0 next_4$0))

(assert (= Alloc$0 (union$1 FP_Caller$0 Alloc$0)))

(assert (= content1$0 (sorted_set_c$0 data$0 next$0 lst1$0 null$0)))

(assert (= sk_?X_25$0 (union$1 sk_?X_27$0 sk_?X_26$0)))

(assert (= sk_?X_26$0 (sorted_set_domain$0 data$0 next$0 lst2$0 null$0)))

(assert (= FP_Caller$0 (union$1 FP$0 FP_Caller$0)))

(assert (sorted_set_struct$0 sk_?X_27$0 data$0 next$0 lst1$0 null$0 content1$0))

(assert (= content1_3$0 (sorted_set_c$0 data$0 next$0 (read$1 next$0 lst1$0) null$0)))

(assert (= sk_?X_28$0 (union$1 sk_?X_30$0 sk_?X_29$0)))

(assert (= sk_?X_29$0 (sorted_set_domain$0 data$0 next$0 lst2$0 null$0)))

(assert (= FP$0 (union$1 FP_6$0 FP$0)))

(assert (sorted_set_struct$0 sk_?X_30$0 data$0 next$0 (read$1 next$0 lst1$0) null$0
  content1_3$0))

(assert (= sk_?X_24$0
  (union$1 (intersection$1 Alloc_4$0 FP_6$0) (setminus$1 Alloc_4$0 Alloc$0))))

(assert (sorted_set_struct$0 sk_?X_24$0 data$0 next_4$0 tmp_3$0 null$0
  (union$0 content1_3$0 content2_3$0)))

(assert (or
    (and (in$0 sk_?e_2$0 (union$0 content1$0 content2$0))
         (not
              (in$0 sk_?e_2$0
                (sorted_set_c$0 data$0 next_5$0 res_4$0 null$0))))
    (and (in$0 sk_?e_2$0 (sorted_set_c$0 data$0 next_5$0 res_4$0 null$0))
         (not (in$0 sk_?e_2$0 (union$0 content1$0 content2$0))))
    (and (in$1 sk_l2_3$0 sk_?X_31$0)
         (not
              (in$1 sk_l2_3$0
                (sorted_set_domain$0 data$0 next_5$0 res_4$0 null$0))))
    (and
         (in$1 sk_l2_3$0
           (sorted_set_domain$0 data$0 next_5$0 res_4$0 null$0))
         (not (in$1 sk_l2_3$0 sk_?X_31$0)))
    (not (Btwn$0 next_5$0 res_4$0 null$0 null$0))
    (and (Btwn$0 next_5$0 sk_l1_3$0 sk_l2_3$0 null$0)
         (in$1 sk_l1_3$0 sk_?X_31$0) (in$1 sk_l2_3$0 sk_?X_31$0)
         (not (= sk_l1_3$0 sk_l2_3$0))
         (not (< (read$0 data$0 sk_l1_3$0) (read$0 data$0 sk_l2_3$0))))))

(assert (not (= lst2$0 null$0)))

(assert (not (in$1 null$0 Alloc_4$0)))

(assert (forall ((l1 Loc))
        (or
            (= l1
              (witness$0 data$0 (read$0 data$0 l1)
                (sorted_set_c$0 data$0 next$0 lst1$0 null$0)))
            (not (in$1 l1 (sorted_set_domain$0 data$0 next$0 lst1$0 null$0))))))

(assert (forall ((l1 Loc))
        (or
            (= l1
              (witness$0 data$0 (read$0 data$0 l1)
                (sorted_set_c$0 data$0 next_4$0 tmp_3$0 null$0)))
            (not
                 (in$1 l1
                   (sorted_set_domain$0 data$0 next_4$0 tmp_3$0 null$0))))))

(assert (forall ((l1 Loc))
        (or
            (in$0 (read$0 data$0 l1)
              (sorted_set_c$0 data$0 next$0 (read$1 next$0 lst1$0) null$0))
            (not
                 (in$1 l1
                   (sorted_set_domain$0 data$0 next$0 (read$1 next$0 lst1$0)
                     null$0))))))

(assert (forall ((l1 Loc))
        (or
            (in$0 (read$0 data$0 l1)
              (sorted_set_c$0 data$0 next$0 lst2$0 null$0))
            (not (in$1 l1 (sorted_set_domain$0 data$0 next$0 lst2$0 null$0))))))

(assert (forall ((l1 Loc))
        (or
            (in$0 (read$0 data$0 l1)
              (sorted_set_c$0 data$0 next_5$0 res_4$0 null$0))
            (not
                 (in$1 l1
                   (sorted_set_domain$0 data$0 next_5$0 res_4$0 null$0))))))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 lst1$0 l1 null$0)
                 (in$1 l1 (sorted_set_domain$0 data$0 next$0 lst1$0 null$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 lst1$0 l1 null$0)))
                 (not
                      (in$1 l1
                        (sorted_set_domain$0 data$0 next$0 lst1$0 null$0)))))))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next_4$0 tmp_3$0 l1 null$0)
                 (in$1 l1
                   (sorted_set_domain$0 data$0 next_4$0 tmp_3$0 null$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next_4$0 tmp_3$0 l1 null$0)))
                 (not
                      (in$1 l1
                        (sorted_set_domain$0 data$0 next_4$0 tmp_3$0 null$0)))))))

(assert (forall ((v Int))
        (or
            (= v
              (read$0 data$0
                (witness$0 data$0 v
                  (sorted_set_c$0 data$0 next$0 (read$1 next$0 lst1$0)
                    null$0))))
            (not
                 (in$0 v
                   (sorted_set_c$0 data$0 next$0 (read$1 next$0 lst1$0)
                     null$0))))))

(assert (forall ((v Int))
        (or
            (= v
              (read$0 data$0
                (witness$0 data$0 v
                  (sorted_set_c$0 data$0 next$0 lst2$0 null$0))))
            (not (in$0 v (sorted_set_c$0 data$0 next$0 lst2$0 null$0))))))

(assert (forall ((v Int))
        (or
            (= v
              (read$0 data$0
                (witness$0 data$0 v
                  (sorted_set_c$0 data$0 next_5$0 res_4$0 null$0))))
            (not (in$0 v (sorted_set_c$0 data$0 next_5$0 res_4$0 null$0))))))

(assert (forall ((v Int))
        (or
            (=
              (witness$0 data$0 v
                (sorted_set_c$0 data$0 next$0 lst1$0 null$0))
              null$0)
            (in$0 v (sorted_set_c$0 data$0 next$0 lst1$0 null$0)))))

(assert (forall ((v Int))
        (or
            (=
              (witness$0 data$0 v
                (sorted_set_c$0 data$0 next_4$0 tmp_3$0 null$0))
              null$0)
            (in$0 v (sorted_set_c$0 data$0 next_4$0 tmp_3$0 null$0)))))

(assert (forall ((v Int))
        (or
            (in$1
              (witness$0 data$0 v
                (sorted_set_c$0 data$0 next$0 (read$1 next$0 lst1$0) null$0))
              (sorted_set_domain$0 data$0 next$0 (read$1 next$0 lst1$0)
                null$0))
            (not
                 (in$0 v
                   (sorted_set_c$0 data$0 next$0 (read$1 next$0 lst1$0)
                     null$0))))))

(assert (forall ((v Int))
        (or
            (in$1
              (witness$0 data$0 v
                (sorted_set_c$0 data$0 next$0 lst2$0 null$0))
              (sorted_set_domain$0 data$0 next$0 lst2$0 null$0))
            (not (in$0 v (sorted_set_c$0 data$0 next$0 lst2$0 null$0))))))

(assert (forall ((v Int))
        (or
            (in$1
              (witness$0 data$0 v
                (sorted_set_c$0 data$0 next_5$0 res_4$0 null$0))
              (sorted_set_domain$0 data$0 next_5$0 res_4$0 null$0))
            (not (in$0 v (sorted_set_c$0 data$0 next_5$0 res_4$0 null$0))))))

(assert (forall ((?X SetLoc) (?f FldLoc) (?x Loc))
        (or (in$1 (ep$0 ?f ?X ?x) ?X) (= ?x (ep$0 ?f ?X ?x)))))

(assert (forall ((?X SetLoc) (?f FldLoc) (?x Loc))
        (Btwn$0 ?f ?x (ep$0 ?f ?X ?x) (ep$0 ?f ?X ?x))))

(assert (or (not Axiom_26$0)
    (forall ((?x Loc) (?y Loc) (?z Loc))
            (or (in$1 ?x FP_6$0)
                (and (Btwn$0 next$0 ?x ?z ?y) (Btwn$0 next_4$0 ?x ?z ?y))
                (and (not (Btwn$0 next$0 ?x ?z ?y))
                     (not (Btwn$0 next_4$0 ?x ?z ?y)))
                (not (= ?x (ep$0 next$0 FP_6$0 ?x)))))))

(assert (or (not Axiom_27$0)
    (forall ((?x Loc) (?y Loc) (?z Loc))
            (or (and (Btwn$0 next$0 ?x ?z ?y) (Btwn$0 next_4$0 ?x ?z ?y))
                (and (not (Btwn$0 next$0 ?x ?z ?y))
                     (not (Btwn$0 next_4$0 ?x ?z ?y)))
                (not
                     (or (Btwn$0 next$0 ?x ?y (ep$0 next$0 FP_6$0 ?x))
                         (and (Btwn$0 next$0 ?x ?y ?y)
                              (not
                                   (Btwn$0 next$0 ?x (ep$0 next$0 FP_6$0 ?x)
                                     (ep$0 next$0 FP_6$0 ?x))))))))))

(assert (or (not Axiom_28$0)
    (forall ((?x Loc))
            (or (= (read$1 next$0 ?x) (read$1 next_4$0 ?x))
                (not (in$1 ?x (setminus$1 Alloc$0 FP_6$0)))))))

(assert (forall ((?u Loc) (?v Loc) (?z Loc))
        (and
             (or (Btwn$0 (write$0 next_4$0 lst1$0 tmp_3$0) ?z ?u ?v)
                 (not
                      (or
                          (and (Btwn$0 next_4$0 ?z ?u ?v)
                               (or (Btwn$0 next_4$0 ?z ?v lst1$0)
                                   (and (Btwn$0 next_4$0 ?z ?v ?v)
                                        (not
                                             (Btwn$0 next_4$0 ?z lst1$0
                                               lst1$0)))))
                          (and (not (= lst1$0 ?v))
                               (or (Btwn$0 next_4$0 ?z lst1$0 ?v)
                                   (and (Btwn$0 next_4$0 ?z lst1$0 lst1$0)
                                        (not (Btwn$0 next_4$0 ?z ?v ?v))))
                               (Btwn$0 next_4$0 ?z ?u lst1$0)
                               (or (Btwn$0 next_4$0 tmp_3$0 ?v lst1$0)
                                   (and (Btwn$0 next_4$0 tmp_3$0 ?v ?v)
                                        (not
                                             (Btwn$0 next_4$0 tmp_3$0 lst1$0
                                               lst1$0)))))
                          (and (not (= lst1$0 ?v))
                               (or (Btwn$0 next_4$0 ?z lst1$0 ?v)
                                   (and (Btwn$0 next_4$0 ?z lst1$0 lst1$0)
                                        (not (Btwn$0 next_4$0 ?z ?v ?v))))
                               (Btwn$0 next_4$0 tmp_3$0 ?u ?v)
                               (or (Btwn$0 next_4$0 tmp_3$0 ?v lst1$0)
                                   (and (Btwn$0 next_4$0 tmp_3$0 ?v ?v)
                                        (not
                                             (Btwn$0 next_4$0 tmp_3$0 lst1$0
                                               lst1$0))))))))
             (or
                 (and (Btwn$0 next_4$0 ?z ?u ?v)
                      (or (Btwn$0 next_4$0 ?z ?v lst1$0)
                          (and (Btwn$0 next_4$0 ?z ?v ?v)
                               (not (Btwn$0 next_4$0 ?z lst1$0 lst1$0)))))
                 (and (not (= lst1$0 ?v))
                      (or (Btwn$0 next_4$0 ?z lst1$0 ?v)
                          (and (Btwn$0 next_4$0 ?z lst1$0 lst1$0)
                               (not (Btwn$0 next_4$0 ?z ?v ?v))))
                      (Btwn$0 next_4$0 ?z ?u lst1$0)
                      (or (Btwn$0 next_4$0 tmp_3$0 ?v lst1$0)
                          (and (Btwn$0 next_4$0 tmp_3$0 ?v ?v)
                               (not (Btwn$0 next_4$0 tmp_3$0 lst1$0 lst1$0)))))
                 (and (not (= lst1$0 ?v))
                      (or (Btwn$0 next_4$0 ?z lst1$0 ?v)
                          (and (Btwn$0 next_4$0 ?z lst1$0 lst1$0)
                               (not (Btwn$0 next_4$0 ?z ?v ?v))))
                      (Btwn$0 next_4$0 tmp_3$0 ?u ?v)
                      (or (Btwn$0 next_4$0 tmp_3$0 ?v lst1$0)
                          (and (Btwn$0 next_4$0 tmp_3$0 ?v ?v)
                               (not (Btwn$0 next_4$0 tmp_3$0 lst1$0 lst1$0)))))
                 (not (Btwn$0 (write$0 next_4$0 lst1$0 tmp_3$0) ?z ?u ?v))))))

(assert (forall ((?f FldLoc) (?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 ?f ?x ?y ?z)) (not (Btwn$0 ?f ?x ?u ?y))
            (and (Btwn$0 ?f ?x ?u ?z) (Btwn$0 ?f ?u ?y ?z)))))

(assert (forall ((?f FldLoc) (?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 ?f ?x ?y ?z)) (not (Btwn$0 ?f ?y ?u ?z))
            (and (Btwn$0 ?f ?x ?y ?u) (Btwn$0 ?f ?x ?u ?z)))))

(assert (forall ((?f FldLoc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 ?f ?x ?y ?y)) (not (Btwn$0 ?f ?y ?z ?z))
            (Btwn$0 ?f ?x ?z ?z))))

(assert (forall ((?f FldLoc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 ?f ?x ?y ?z))
            (and (Btwn$0 ?f ?x ?y ?y) (Btwn$0 ?f ?y ?z ?z)))))

(assert (forall ((?f FldLoc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 ?f ?x ?y ?y)) (not (Btwn$0 ?f ?x ?z ?z))
            (Btwn$0 ?f ?x ?y ?z) (Btwn$0 ?f ?x ?z ?y))))

(assert (forall ((?f FldLoc) (?x Loc) (?y Loc))
        (or (not (Btwn$0 ?f ?x ?y ?x)) (= ?x ?y))))

(assert (forall ((?f FldLoc) (?x Loc) (?y Loc))
        (or (not (Btwn$0 ?f ?x ?y ?y)) (= ?x ?y)
            (Btwn$0 ?f ?x (read$1 ?f ?x) ?y))))

(assert (forall ((?f FldLoc) (?x Loc) (?y Loc))
        (or (not (= (read$1 ?f ?x) ?x)) (not (Btwn$0 ?f ?x ?y ?y)) (= ?x ?y))))

(assert (forall ((?f FldLoc) (?x Loc)) (Btwn$0 ?f ?x (read$1 ?f ?x) (read$1 ?f ?x))))

(assert (forall ((?f FldLoc) (?x Loc)) (Btwn$0 ?f ?x ?x ?x)))

(check-sat)
(exit)
