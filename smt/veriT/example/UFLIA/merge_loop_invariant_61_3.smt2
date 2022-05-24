(set-info :smt-lib-version 2.6)
(set-logic UFLIA)
(set-info :source |
  GRASShopper benchmarks.
  Authors: Ruzica Piskac, Thomas Wies, and Damien Zufferey
  URL: http://cs.nyu.edu/wies/software/grasshopper
  See also: GRASShopper - Complete Heap Verification with Mixed Specifications. In TACAS 2014, pages 124-139.

  If this benchmark is satisfiable, GRASShopper reports the following error message:
  tests/spl/sls/sls_merge_sort.spl:61:3-4:An invariant might not be maintained by a loop in procedure merge
  tests/spl/sls/sls_merge_sort.spl:47:15:Related location: This is the loop invariant that might not be maintained
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
(declare-fun emptyset$0 () SetLoc)
(declare-fun setenum$0 (Loc) SetLoc)
(declare-fun union$0 (SetLoc SetLoc) SetLoc)
(declare-fun intersection$0 (SetLoc SetLoc) SetLoc)
(declare-fun setminus$0 (SetLoc SetLoc) SetLoc)
(declare-fun Btwn$0 (FldLoc Loc Loc Loc) Bool)
(declare-fun in$0 (Loc SetLoc) Bool)
(declare-fun Alloc$0 () SetLoc)
(declare-fun Axiom_60$0 () Bool)
(declare-fun Axiom_61$0 () Bool)
(declare-fun Axiom_62$0 () Bool)
(declare-fun Axiom_63$0 () Bool)
(declare-fun Axiom_64$0 () Bool)
(declare-fun Axiom_65$0 () Bool)
(declare-fun Axiom_66$0 () Bool)
(declare-fun Axiom_67$0 () Bool)
(declare-fun Axiom_68$0 () Bool)
(declare-fun Axiom_69$0 () Bool)
(declare-fun Axiom_70$0 () Bool)
(declare-fun Axiom_71$0 () Bool)
(declare-fun FP$0 () SetLoc)
(declare-fun FP_Caller$0 () SetLoc)
(declare-fun FP_Caller_2$0 () SetLoc)
(declare-fun a_3$0 () Loc)
(declare-fun a_4$0 () Loc)
(declare-fun a_init$0 () Loc)
(declare-fun b_3$0 () Loc)
(declare-fun b_4$0 () Loc)
(declare-fun b_init$0 () Loc)
(declare-fun data$0 () FldInt)
(declare-fun last_4$0 () Loc)
(declare-fun last_5$0 () Loc)
(declare-fun last_6$0 () Loc)
(declare-fun last_init$0 () Loc)
(declare-fun lslseg_domain$0 (FldInt FldLoc Loc Loc Int) SetLoc)
(declare-fun lslseg_struct$0 (SetLoc FldInt FldLoc Loc Loc Int) Bool)
(declare-fun next$0 () FldLoc)
(declare-fun next_2$0 () FldLoc)
(declare-fun next_3$0 () FldLoc)
(declare-fun res_9$0 () Loc)
(declare-fun res_init$0 () Loc)
(declare-fun sk_?X_142$0 () SetLoc)
(declare-fun sk_?X_143$0 () SetLoc)
(declare-fun sk_?X_144$0 () SetLoc)
(declare-fun sk_?X_145$0 () SetLoc)
(declare-fun sk_?X_146$0 () SetLoc)
(declare-fun sk_?X_147$0 () SetLoc)
(declare-fun sk_?X_148$0 () SetLoc)
(declare-fun sk_?X_149$0 () SetLoc)
(declare-fun sk_?X_150$0 () SetLoc)
(declare-fun sk_?X_151$0 () SetLoc)
(declare-fun sk_?X_152$0 () SetLoc)
(declare-fun sk_?X_153$0 () SetLoc)
(declare-fun sk_?X_154$0 () SetLoc)
(declare-fun sk_?X_155$0 () SetLoc)
(declare-fun sk_?X_156$0 () SetLoc)
(declare-fun sk_?X_157$0 () SetLoc)
(declare-fun sk_?X_158$0 () SetLoc)
(declare-fun sk_?X_159$0 () SetLoc)
(declare-fun sk_?X_160$0 () SetLoc)
(declare-fun sk_?X_161$0 () SetLoc)
(declare-fun sk_?X_162$0 () SetLoc)
(declare-fun sk_?X_163$0 () SetLoc)
(declare-fun sk_?X_164$0 () SetLoc)
(declare-fun sk_?X_165$0 () SetLoc)
(declare-fun sk_?X_166$0 () SetLoc)
(declare-fun sk_?X_167$0 () SetLoc)
(declare-fun sk_FP_2$0 () SetLoc)
(declare-fun sk_FP_3$0 () SetLoc)
(declare-fun sk_l1_5$0 () Loc)
(declare-fun sk_l1_6$0 () Loc)
(declare-fun sk_l2_5$0 () Loc)
(declare-fun sk_l2_6$0 () Loc)
(declare-fun uslseg_domain$0 (FldInt FldLoc Loc Loc Int) SetLoc)
(declare-fun uslseg_struct$0 (SetLoc FldInt FldLoc Loc Loc Int) Bool)

(assert (forall ((?y Loc))
        (or (not (Btwn$0 next$0 null$0 ?y ?y)) (= null$0 ?y)
            (Btwn$0 next$0 null$0 (read$1 next$0 null$0) ?y))))

(assert (forall ((?y Loc))
        (or (not (Btwn$0 next$0 a_3$0 ?y ?y)) (= a_3$0 ?y)
            (Btwn$0 next$0 a_3$0 (read$1 next$0 a_3$0) ?y))))

(assert (forall ((?y Loc))
        (or (not (Btwn$0 next$0 b_3$0 ?y ?y)) (= b_3$0 ?y)
            (Btwn$0 next$0 b_3$0 (read$1 next$0 b_3$0) ?y))))

(assert (forall ((?y Loc))
        (or (not (Btwn$0 next$0 last_init$0 ?y ?y)) (= last_init$0 ?y)
            (Btwn$0 next$0 last_init$0 (read$1 next$0 last_init$0) ?y))))

(assert (forall ((?y Loc))
        (or (not (Btwn$0 next$0 last_6$0 ?y ?y)) (= last_6$0 ?y)
            (Btwn$0 next$0 last_6$0 (read$1 next$0 last_6$0) ?y))))

(assert (forall ((?y Loc))
        (or (not (Btwn$0 next_2$0 null$0 ?y ?y)) (= null$0 ?y)
            (Btwn$0 next_2$0 null$0 (read$1 next_2$0 null$0) ?y))))

(assert (forall ((?y Loc))
        (or (not (Btwn$0 next_2$0 a_3$0 ?y ?y)) (= a_3$0 ?y)
            (Btwn$0 next_2$0 a_3$0 (read$1 next_2$0 a_3$0) ?y))))

(assert (forall ((?y Loc))
        (or (not (Btwn$0 next_2$0 b_3$0 ?y ?y)) (= b_3$0 ?y)
            (Btwn$0 next_2$0 b_3$0 (read$1 next_2$0 b_3$0) ?y))))

(assert (forall ((?y Loc))
        (or (not (Btwn$0 next_2$0 last_6$0 ?y ?y)) (= last_6$0 ?y)
            (Btwn$0 next_2$0 last_6$0 (read$1 next_2$0 last_6$0) ?y))))

(assert (forall ((?y Loc))
        (or (not (Btwn$0 next_3$0 null$0 ?y ?y)) (= null$0 ?y)
            (Btwn$0 next_3$0 null$0 (read$1 next_3$0 null$0) ?y))))

(assert (forall ((?y Loc))
        (or (not (Btwn$0 next_3$0 b_3$0 ?y ?y)) (= b_3$0 ?y)
            (Btwn$0 next_3$0 b_3$0 (read$1 next_3$0 b_3$0) ?y))))

(assert (forall ((?y Loc))
        (or (not (Btwn$0 next_3$0 last_6$0 ?y ?y)) (= last_6$0 ?y)
            (Btwn$0 next_3$0 last_6$0 (read$1 next_3$0 last_6$0) ?y))))

(assert (forall ((?y Loc))
        (or (not (= (read$1 next$0 null$0) null$0))
            (not (Btwn$0 next$0 null$0 ?y ?y)) (= null$0 ?y))))

(assert (forall ((?y Loc))
        (or (not (= (read$1 next$0 a_3$0) a_3$0))
            (not (Btwn$0 next$0 a_3$0 ?y ?y)) (= a_3$0 ?y))))

(assert (forall ((?y Loc))
        (or (not (= (read$1 next$0 b_3$0) b_3$0))
            (not (Btwn$0 next$0 b_3$0 ?y ?y)) (= b_3$0 ?y))))

(assert (forall ((?y Loc))
        (or (not (= (read$1 next$0 last_init$0) last_init$0))
            (not (Btwn$0 next$0 last_init$0 ?y ?y)) (= last_init$0 ?y))))

(assert (forall ((?y Loc))
        (or (not (= (read$1 next$0 last_6$0) last_6$0))
            (not (Btwn$0 next$0 last_6$0 ?y ?y)) (= last_6$0 ?y))))

(assert (forall ((?y Loc))
        (or (not (= (read$1 next_2$0 null$0) null$0))
            (not (Btwn$0 next_2$0 null$0 ?y ?y)) (= null$0 ?y))))

(assert (forall ((?y Loc))
        (or (not (= (read$1 next_2$0 a_3$0) a_3$0))
            (not (Btwn$0 next_2$0 a_3$0 ?y ?y)) (= a_3$0 ?y))))

(assert (forall ((?y Loc))
        (or (not (= (read$1 next_2$0 b_3$0) b_3$0))
            (not (Btwn$0 next_2$0 b_3$0 ?y ?y)) (= b_3$0 ?y))))

(assert (forall ((?y Loc))
        (or (not (= (read$1 next_2$0 last_6$0) last_6$0))
            (not (Btwn$0 next_2$0 last_6$0 ?y ?y)) (= last_6$0 ?y))))

(assert (forall ((?y Loc))
        (or (not (= (read$1 next_3$0 null$0) null$0))
            (not (Btwn$0 next_3$0 null$0 ?y ?y)) (= null$0 ?y))))

(assert (forall ((?y Loc))
        (or (not (= (read$1 next_3$0 b_3$0) b_3$0))
            (not (Btwn$0 next_3$0 b_3$0 ?y ?y)) (= b_3$0 ?y))))

(assert (forall ((?y Loc))
        (or (not (= (read$1 next_3$0 last_6$0) last_6$0))
            (not (Btwn$0 next_3$0 last_6$0 ?y ?y)) (= last_6$0 ?y))))

(assert (Btwn$0 next$0 null$0 (read$1 next$0 null$0) (read$1 next$0 null$0)))

(assert (Btwn$0 next$0 a_3$0 (read$1 next$0 a_3$0) (read$1 next$0 a_3$0)))

(assert (Btwn$0 next$0 b_3$0 (read$1 next$0 b_3$0) (read$1 next$0 b_3$0)))

(assert (Btwn$0 next$0 last_init$0 (read$1 next$0 last_init$0)
  (read$1 next$0 last_init$0)))

(assert (Btwn$0 next$0 last_6$0 (read$1 next$0 last_6$0) (read$1 next$0 last_6$0)))

(assert (Btwn$0 next_2$0 null$0 (read$1 next_2$0 null$0) (read$1 next_2$0 null$0)))

(assert (Btwn$0 next_2$0 a_3$0 (read$1 next_2$0 a_3$0) (read$1 next_2$0 a_3$0)))

(assert (Btwn$0 next_2$0 b_3$0 (read$1 next_2$0 b_3$0) (read$1 next_2$0 b_3$0)))

(assert (Btwn$0 next_2$0 last_6$0 (read$1 next_2$0 last_6$0)
  (read$1 next_2$0 last_6$0)))

(assert (Btwn$0 next_3$0 null$0 (read$1 next_3$0 null$0) (read$1 next_3$0 null$0)))

(assert (Btwn$0 next_3$0 b_3$0 (read$1 next_3$0 b_3$0) (read$1 next_3$0 b_3$0)))

(assert (Btwn$0 next_3$0 last_6$0 (read$1 next_3$0 last_6$0)
  (read$1 next_3$0 last_6$0)))

(assert (forall ((l1 Loc))
        (or (not Axiom_71$0)
            (or (<= (read$0 data$0 l1) (read$0 data$0 last_6$0))
                (not (in$0 l1 sk_?X_163$0))))))

(assert (forall ((l1 Loc) (l2 Loc))
        (or (not Axiom_70$0)
            (or (<= (read$0 data$0 l1) (read$0 data$0 l2))
                (not (Btwn$0 next_3$0 l1 l2 last_6$0))
                (not (in$0 l1 sk_?X_163$0)) (not (in$0 l2 sk_?X_163$0))))))

(assert (forall ((l1 Loc))
        (or (not Axiom_67$0)
            (or (<= (read$0 data$0 last_6$0) (read$0 data$0 l1))
                (not (in$0 l1 sk_?X_160$0))))))

(assert (forall ((l1 Loc) (l2 Loc))
        (or (not Axiom_66$0)
            (or (<= (read$0 data$0 l1) (read$0 data$0 l2))
                (not (Btwn$0 next_3$0 l1 l2 null$0))
                (not (in$0 l1 sk_?X_160$0)) (not (in$0 l2 sk_?X_160$0))))))

(assert (forall ((l1 Loc))
        (or (not Axiom_63$0)
            (or (<= (read$0 data$0 last_init$0) (read$0 data$0 l1))
                (not (in$0 l1 sk_?X_144$0))))))

(assert (forall ((l1 Loc) (l2 Loc))
        (or (not Axiom_62$0)
            (or (<= (read$0 data$0 l1) (read$0 data$0 l2))
                (not (Btwn$0 next$0 l1 l2 null$0))
                (not (in$0 l1 sk_?X_144$0)) (not (in$0 l2 sk_?X_144$0))))))

(assert (forall ((l1 Loc))
        (or (not Axiom_69$0)
            (or (<= (read$0 data$0 last_6$0) (read$0 data$0 l1))
                (not (in$0 l1 sk_?X_157$0))))))

(assert (forall ((l1 Loc) (l2 Loc))
        (or (not Axiom_68$0)
            (or (<= (read$0 data$0 l1) (read$0 data$0 l2))
                (not (Btwn$0 next_3$0 l1 l2 null$0))
                (not (in$0 l1 sk_?X_157$0)) (not (in$0 l2 sk_?X_157$0))))))

(assert (forall ((l1 Loc))
        (or (not Axiom_65$0)
            (or (<= (read$0 data$0 l1) (read$0 data$0 last_init$0))
                (not (in$0 l1 sk_?X_150$0))))))

(assert (forall ((l1 Loc) (l2 Loc))
        (or (not Axiom_64$0)
            (or (<= (read$0 data$0 l1) (read$0 data$0 l2))
                (not (Btwn$0 next$0 l1 l2 last_init$0))
                (not (in$0 l1 sk_?X_150$0)) (not (in$0 l2 sk_?X_150$0))))))

(assert (forall ((l1 Loc))
        (or (not Axiom_61$0)
            (or (<= (read$0 data$0 last_init$0) (read$0 data$0 l1))
                (not (in$0 l1 sk_?X_147$0))))))

(assert (forall ((l1 Loc) (l2 Loc))
        (or (not Axiom_60$0)
            (or (<= (read$0 data$0 l1) (read$0 data$0 l2))
                (not (Btwn$0 next$0 l1 l2 null$0))
                (not (in$0 l1 sk_?X_147$0)) (not (in$0 l2 sk_?X_147$0))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_Caller$0 Alloc$0))
                 (or (in$0 x FP_Caller$0) (in$0 x Alloc$0)))
            (and (not (in$0 x FP_Caller$0)) (not (in$0 x Alloc$0))
                 (not (in$0 x (union$0 FP_Caller$0 Alloc$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP$0 FP_Caller$0))
                 (or (in$0 x FP$0) (in$0 x FP_Caller$0)))
            (and (not (in$0 x FP$0)) (not (in$0 x FP_Caller$0))
                 (not (in$0 x (union$0 FP$0 FP_Caller$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_146$0 sk_?X_144$0))
                 (or (in$0 x sk_?X_146$0) (in$0 x sk_?X_144$0)))
            (and (not (in$0 x sk_?X_146$0)) (not (in$0 x sk_?X_144$0))
                 (not (in$0 x (union$0 sk_?X_146$0 sk_?X_144$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_149$0 sk_?X_147$0))
                 (or (in$0 x sk_?X_149$0) (in$0 x sk_?X_147$0)))
            (and (not (in$0 x sk_?X_149$0)) (not (in$0 x sk_?X_147$0))
                 (not (in$0 x (union$0 sk_?X_149$0 sk_?X_147$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_154$0 sk_?X_150$0))
                 (or (in$0 x sk_?X_154$0) (in$0 x sk_?X_150$0)))
            (and (not (in$0 x sk_?X_154$0)) (not (in$0 x sk_?X_150$0))
                 (not (in$0 x (union$0 sk_?X_154$0 sk_?X_150$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_162$0 sk_?X_160$0))
                 (or (in$0 x sk_?X_162$0) (in$0 x sk_?X_160$0)))
            (and (not (in$0 x sk_?X_162$0)) (not (in$0 x sk_?X_160$0))
                 (not (in$0 x (union$0 sk_?X_162$0 sk_?X_160$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_165$0 sk_?X_163$0))
                 (or (in$0 x sk_?X_165$0) (in$0 x sk_?X_163$0)))
            (and (not (in$0 x sk_?X_165$0)) (not (in$0 x sk_?X_163$0))
                 (not (in$0 x (union$0 sk_?X_165$0 sk_?X_163$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_158$0 sk_?X_157$0))
                 (or (in$0 x sk_?X_158$0) (in$0 x sk_?X_157$0)))
            (and (not (in$0 x sk_?X_158$0)) (not (in$0 x sk_?X_157$0))
                 (not (in$0 x (union$0 sk_?X_158$0 sk_?X_157$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_146$0) (in$0 x sk_?X_144$0)
                 (in$0 x (intersection$0 sk_?X_146$0 sk_?X_144$0)))
            (and (or (not (in$0 x sk_?X_146$0)) (not (in$0 x sk_?X_144$0)))
                 (not (in$0 x (intersection$0 sk_?X_146$0 sk_?X_144$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_149$0) (in$0 x sk_?X_147$0)
                 (in$0 x (intersection$0 sk_?X_149$0 sk_?X_147$0)))
            (and (or (not (in$0 x sk_?X_149$0)) (not (in$0 x sk_?X_147$0)))
                 (not (in$0 x (intersection$0 sk_?X_149$0 sk_?X_147$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_154$0) (in$0 x sk_?X_150$0)
                 (in$0 x (intersection$0 sk_?X_154$0 sk_?X_150$0)))
            (and (or (not (in$0 x sk_?X_154$0)) (not (in$0 x sk_?X_150$0)))
                 (not (in$0 x (intersection$0 sk_?X_154$0 sk_?X_150$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_158$0) (in$0 x sk_?X_157$0)
                 (in$0 x (intersection$0 sk_?X_158$0 sk_?X_157$0)))
            (and (or (not (in$0 x sk_?X_158$0)) (not (in$0 x sk_?X_157$0)))
                 (not (in$0 x (intersection$0 sk_?X_158$0 sk_?X_157$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_162$0) (in$0 x sk_?X_160$0)
                 (in$0 x (intersection$0 sk_?X_162$0 sk_?X_160$0)))
            (and (or (not (in$0 x sk_?X_162$0)) (not (in$0 x sk_?X_160$0)))
                 (not (in$0 x (intersection$0 sk_?X_162$0 sk_?X_160$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_165$0) (in$0 x sk_?X_163$0)
                 (in$0 x (intersection$0 sk_?X_165$0 sk_?X_163$0)))
            (and (or (not (in$0 x sk_?X_165$0)) (not (in$0 x sk_?X_163$0)))
                 (not (in$0 x (intersection$0 sk_?X_165$0 sk_?X_163$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x FP_Caller$0) (in$0 x (setminus$0 FP_Caller$0 FP$0))
                 (not (in$0 x FP$0)))
            (and (or (in$0 x FP$0) (not (in$0 x FP_Caller$0)))
                 (not (in$0 x (setminus$0 FP_Caller$0 FP$0)))))))

(assert (forall ((y Loc) (x Loc))
        (or (and (= x y) (in$0 x (setenum$0 y)))
            (and (not (= x y)) (not (in$0 x (setenum$0 y)))))))

(assert (= (read$1 (write$0 next$0 last_init$0 a_3$0) last_init$0) a_3$0))

(assert (= (read$1 (write$0 next$0 last_init$0 b_3$0) last_init$0) b_3$0))

(assert (or (= null$0 last_init$0)
    (= (read$1 next$0 null$0)
      (read$1 (write$0 next$0 last_init$0 a_3$0) null$0))))

(assert (or (= null$0 last_init$0)
    (= (read$1 next$0 null$0)
      (read$1 (write$0 next$0 last_init$0 b_3$0) null$0))))

(assert (or (= a_3$0 last_init$0)
    (= (read$1 next$0 a_3$0)
      (read$1 (write$0 next$0 last_init$0 a_3$0) a_3$0))))

(assert (or (= a_3$0 last_init$0)
    (= (read$1 next$0 a_3$0)
      (read$1 (write$0 next$0 last_init$0 b_3$0) a_3$0))))

(assert (or (= b_3$0 last_init$0)
    (= (read$1 next$0 b_3$0)
      (read$1 (write$0 next$0 last_init$0 a_3$0) b_3$0))))

(assert (or (= b_3$0 last_init$0)
    (= (read$1 next$0 b_3$0)
      (read$1 (write$0 next$0 last_init$0 b_3$0) b_3$0))))

(assert (or (= last_init$0 last_init$0)
    (= (read$1 next$0 last_init$0)
      (read$1 (write$0 next$0 last_init$0 a_3$0) last_init$0))))

(assert (or (= last_init$0 last_init$0)
    (= (read$1 next$0 last_init$0)
      (read$1 (write$0 next$0 last_init$0 b_3$0) last_init$0))))

(assert (or (= last_6$0 last_init$0)
    (= (read$1 next$0 last_6$0)
      (read$1 (write$0 next$0 last_init$0 a_3$0) last_6$0))))

(assert (or (= last_6$0 last_init$0)
    (= (read$1 next$0 last_6$0)
      (read$1 (write$0 next$0 last_init$0 b_3$0) last_6$0))))

(assert (= (read$1 (write$0 next$0 last_init$0 a_3$0) last_init$0) a_3$0))

(assert (= (read$1 (write$0 next$0 last_init$0 b_3$0) last_init$0) b_3$0))

(assert (or (= null$0 last_init$0)
    (= (read$1 next$0 null$0)
      (read$1 (write$0 next$0 last_init$0 a_3$0) null$0))))

(assert (or (= null$0 last_init$0)
    (= (read$1 next$0 null$0)
      (read$1 (write$0 next$0 last_init$0 b_3$0) null$0))))

(assert (or (= a_3$0 last_init$0)
    (= (read$1 next$0 a_3$0)
      (read$1 (write$0 next$0 last_init$0 a_3$0) a_3$0))))

(assert (or (= a_3$0 last_init$0)
    (= (read$1 next$0 a_3$0)
      (read$1 (write$0 next$0 last_init$0 b_3$0) a_3$0))))

(assert (or (= b_3$0 last_init$0)
    (= (read$1 next$0 b_3$0)
      (read$1 (write$0 next$0 last_init$0 a_3$0) b_3$0))))

(assert (or (= b_3$0 last_init$0)
    (= (read$1 next$0 b_3$0)
      (read$1 (write$0 next$0 last_init$0 b_3$0) b_3$0))))

(assert (or (= last_init$0 last_init$0)
    (= (read$1 next$0 last_init$0)
      (read$1 (write$0 next$0 last_init$0 a_3$0) last_init$0))))

(assert (or (= last_init$0 last_init$0)
    (= (read$1 next$0 last_init$0)
      (read$1 (write$0 next$0 last_init$0 b_3$0) last_init$0))))

(assert (or (= last_6$0 last_init$0)
    (= (read$1 next$0 last_6$0)
      (read$1 (write$0 next$0 last_init$0 a_3$0) last_6$0))))

(assert (or (= last_6$0 last_init$0)
    (= (read$1 next$0 last_6$0)
      (read$1 (write$0 next$0 last_init$0 b_3$0) last_6$0))))

(assert (= (read$1 next$0 null$0) null$0))

(assert (= (read$1 next_2$0 null$0) null$0))

(assert (= (read$1 next_3$0 null$0) null$0))

(assert (forall ((x Loc)) (not (in$0 x emptyset$0))))

(assert (or (and (Btwn$0 next$0 b_init$0 null$0 null$0) Axiom_63$0 Axiom_62$0)
    (not
         (uslseg_struct$0 sk_?X_144$0 data$0 next$0 b_init$0 null$0
           (read$0 data$0 last_init$0)))))

(assert (or (and (Btwn$0 next_3$0 a_3$0 null$0 null$0) Axiom_67$0 Axiom_66$0)
    (not
         (uslseg_struct$0 sk_?X_160$0 data$0 next_3$0 a_3$0 null$0
           (read$0 data$0 last_6$0)))))

(assert (or (and (Btwn$0 next_3$0 res_9$0 last_6$0 last_6$0) Axiom_71$0 Axiom_70$0)
    (not
         (lslseg_struct$0 sk_?X_163$0 data$0 next_3$0 res_9$0 last_6$0
           (read$0 data$0 last_6$0)))))

(assert (or (not (= a_3$0 null$0)) (not (= b_3$0 null$0))))

(assert (= a_3$0 a_init$0))

(assert (= last_4$0 last_init$0))

(assert (= Alloc$0 (union$0 FP_Caller$0 Alloc$0)))

(assert (= sk_?X_143$0 (union$0 sk_?X_146$0 sk_?X_144$0)))

(assert (= sk_?X_145$0 (union$0 sk_?X_148$0 sk_?X_147$0)))

(assert (= sk_?X_147$0
  (uslseg_domain$0 data$0 next$0 a_init$0 null$0 (read$0 data$0 last_init$0))))

(assert (= sk_?X_149$0 (union$0 sk_?X_151$0 sk_?X_150$0)))

(assert (= sk_?X_151$0 sk_?X_152$0))

(assert (= sk_?X_153$0 sk_?X_154$0))

(assert (= FP_Caller$0 (union$0 FP$0 FP_Caller$0)))

(assert (= sk_?X_155$0 (union$0 sk_?X_158$0 sk_?X_157$0)))

(assert (= sk_?X_157$0
  (uslseg_domain$0 data$0 next_3$0 b_4$0 null$0 (read$0 data$0 last_6$0))))

(assert (= sk_?X_159$0 (union$0 sk_?X_162$0 sk_?X_160$0)))

(assert (= sk_?X_161$0 (union$0 sk_?X_166$0 sk_?X_163$0)))

(assert (= sk_?X_163$0
  (lslseg_domain$0 data$0 next_3$0 res_9$0 last_6$0 (read$0 data$0 last_6$0))))

(assert (= sk_?X_165$0 (setenum$0 last_6$0)))

(assert (= sk_?X_167$0 (setenum$0 last_6$0)))

(assert (= sk_FP_3$0 sk_?X_155$0))

(assert (or (in$0 sk_l1_6$0 (intersection$0 sk_?X_162$0 sk_?X_160$0))
    (in$0 sk_l2_6$0 (intersection$0 sk_?X_159$0 sk_?X_157$0))
    (in$0 sk_l2_6$0 (intersection$0 sk_?X_164$0 sk_?X_163$0))
    (and (in$0 sk_l1_6$0 sk_?X_160$0)
         (not (<= (read$0 data$0 last_6$0) (read$0 data$0 sk_l1_6$0))))
    (and (in$0 sk_l1_6$0 sk_FP_2$0) (not (in$0 sk_l1_6$0 FP$0)))
    (and (in$0 sk_l2_6$0 sk_?X_157$0)
         (not (<= (read$0 data$0 last_6$0) (read$0 data$0 sk_l2_6$0))))
    (and (in$0 sk_l2_6$0 sk_?X_163$0)
         (not (<= (read$0 data$0 sk_l2_6$0) (read$0 data$0 last_6$0))))
    (not (= (read$1 next_3$0 last_6$0) b_4$0))
    (not (Btwn$0 next_3$0 a_3$0 null$0 null$0))
    (not (Btwn$0 next_3$0 b_4$0 null$0 null$0))
    (not (Btwn$0 next_3$0 res_9$0 last_6$0 last_6$0))
    (and (Btwn$0 next_3$0 sk_l1_6$0 sk_l2_6$0 null$0)
         (in$0 sk_l1_6$0 sk_?X_160$0) (in$0 sk_l2_6$0 sk_?X_160$0)
         (not (<= (read$0 data$0 sk_l1_6$0) (read$0 data$0 sk_l2_6$0))))
    (and (Btwn$0 next_3$0 sk_l1_6$0 sk_l2_6$0 last_6$0)
         (in$0 sk_l1_6$0 sk_?X_163$0) (in$0 sk_l2_6$0 sk_?X_163$0)
         (not (<= (read$0 data$0 sk_l1_6$0) (read$0 data$0 sk_l2_6$0))))
    (and (Btwn$0 next_3$0 sk_l2_6$0 sk_l1_6$0 null$0)
         (in$0 sk_l1_6$0 sk_?X_157$0) (in$0 sk_l2_6$0 sk_?X_157$0)
         (not (<= (read$0 data$0 sk_l2_6$0) (read$0 data$0 sk_l1_6$0))))))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 a_init$0 l1 null$0)
                 (in$0 l1
                   (uslseg_domain$0 data$0 next$0 a_init$0 null$0
                     (read$0 data$0 last_init$0)))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 a_init$0 l1 null$0)))
                 (not
                      (in$0 l1
                        (uslseg_domain$0 data$0 next$0 a_init$0 null$0
                          (read$0 data$0 last_init$0))))))))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 res_init$0 l1 last_init$0)
                 (in$0 l1
                   (lslseg_domain$0 data$0 next$0 res_init$0 last_init$0
                     (read$0 data$0 last_init$0)))
                 (not (= l1 last_init$0)))
            (and
                 (or (= l1 last_init$0)
                     (not (Btwn$0 next$0 res_init$0 l1 last_init$0)))
                 (not
                      (in$0 l1
                        (lslseg_domain$0 data$0 next$0 res_init$0 last_init$0
                          (read$0 data$0 last_init$0))))))))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next_3$0 b_4$0 l1 null$0)
                 (in$0 l1
                   (uslseg_domain$0 data$0 next_3$0 b_4$0 null$0
                     (read$0 data$0 last_6$0)))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next_3$0 b_4$0 l1 null$0)))
                 (not
                      (in$0 l1
                        (uslseg_domain$0 data$0 next_3$0 b_4$0 null$0
                          (read$0 data$0 last_6$0))))))))

(assert (or (and (Btwn$0 next$0 a_init$0 null$0 null$0) Axiom_61$0 Axiom_60$0)
    (not
         (uslseg_struct$0 sk_?X_147$0 data$0 next$0 a_init$0 null$0
           (read$0 data$0 last_init$0)))))

(assert (or
    (and (Btwn$0 next$0 res_init$0 last_init$0 last_init$0) Axiom_65$0
         Axiom_64$0)
    (not
         (lslseg_struct$0 sk_?X_150$0 data$0 next$0 res_init$0 last_init$0
           (read$0 data$0 last_init$0)))))

(assert (or (and (Btwn$0 next_3$0 b_4$0 null$0 null$0) Axiom_69$0 Axiom_68$0)
    (not
         (uslseg_struct$0 sk_?X_157$0 data$0 next_3$0 b_4$0 null$0
           (read$0 data$0 last_6$0)))))

(assert (or
    (and
         (or (= a_3$0 null$0)
             (> (read$0 data$0 a_3$0) (read$0 data$0 b_3$0)))
         (or (= a_3$0 null$0) (not (= b_3$0 null$0)))
         (= b_4$0 (read$1 next_3$0 b_3$0)) (= last_6$0 b_3$0)
         (= next_3$0 (write$0 next$0 last_4$0 b_3$0)))
    (and
         (or (= b_3$0 null$0)
             (not (> (read$0 data$0 a_3$0) (read$0 data$0 b_3$0))))
         (= a_3$0 a_4$0) (= a_4$0 (read$1 next_2$0 a_3$0)) (= b_4$0 b_3$0)
         (= last_5$0 a_3$0) (= last_6$0 last_5$0)
         (= next_2$0 (write$0 next$0 last_4$0 a_3$0)) (= next_3$0 next_2$0)
         (not (= a_3$0 null$0)))))

(assert (= FP_Caller_2$0 (setminus$0 FP_Caller$0 FP$0)))

(assert (= b_3$0 b_init$0))

(assert (= res_9$0 res_init$0))

(assert (= sk_?X_142$0 (union$0 sk_?X_145$0 sk_?X_144$0)))

(assert (= sk_?X_144$0
  (uslseg_domain$0 data$0 next$0 b_init$0 null$0 (read$0 data$0 last_init$0))))

(assert (= sk_?X_146$0 (union$0 sk_?X_149$0 sk_?X_147$0)))

(assert (= sk_?X_148$0 (union$0 sk_?X_153$0 sk_?X_150$0)))

(assert (= sk_?X_150$0
  (lslseg_domain$0 data$0 next$0 res_init$0 last_init$0
    (read$0 data$0 last_init$0))))

(assert (= sk_?X_152$0 (setenum$0 last_init$0)))

(assert (= sk_?X_154$0 (setenum$0 last_init$0)))

(assert (or
    (and (= (read$1 next$0 last_init$0) a_init$0) (= emptyset$0 emptyset$0)
         (= emptyset$0 (intersection$0 sk_?X_145$0 sk_?X_144$0))
         (= emptyset$0 (intersection$0 sk_?X_148$0 sk_?X_147$0))
         (= emptyset$0 (intersection$0 sk_?X_153$0 sk_?X_150$0))
         (= sk_?X_142$0 FP$0)
         (lslseg_struct$0 sk_?X_150$0 data$0 next$0 res_init$0 last_init$0
           (read$0 data$0 last_init$0))
         (uslseg_struct$0 sk_?X_144$0 data$0 next$0 b_init$0 null$0
           (read$0 data$0 last_init$0))
         (uslseg_struct$0 sk_?X_147$0 data$0 next$0 a_init$0 null$0
           (read$0 data$0 last_init$0)))
    (and (= (read$1 next$0 last_init$0) b_init$0) (= emptyset$0 emptyset$0)
         (= emptyset$0 (intersection$0 sk_?X_146$0 sk_?X_144$0))
         (= emptyset$0 (intersection$0 sk_?X_149$0 sk_?X_147$0))
         (= emptyset$0 (intersection$0 sk_?X_151$0 sk_?X_150$0))
         (= sk_?X_143$0 FP$0)
         (lslseg_struct$0 sk_?X_150$0 data$0 next$0 res_init$0 last_init$0
           (read$0 data$0 last_init$0))
         (uslseg_struct$0 sk_?X_144$0 data$0 next$0 b_init$0 null$0
           (read$0 data$0 last_init$0))
         (uslseg_struct$0 sk_?X_147$0 data$0 next$0 a_init$0 null$0
           (read$0 data$0 last_init$0)))))

(assert (= sk_?X_156$0 (union$0 sk_?X_159$0 sk_?X_157$0)))

(assert (= sk_?X_158$0 (union$0 sk_?X_161$0 sk_?X_160$0)))

(assert (= sk_?X_160$0
  (uslseg_domain$0 data$0 next_3$0 a_3$0 null$0 (read$0 data$0 last_6$0))))

(assert (= sk_?X_162$0 (union$0 sk_?X_164$0 sk_?X_163$0)))

(assert (= sk_?X_164$0 sk_?X_165$0))

(assert (= sk_?X_166$0 sk_?X_167$0))

(assert (= sk_FP_2$0 sk_?X_156$0))

(assert (or (in$0 sk_l1_5$0 (intersection$0 sk_?X_161$0 sk_?X_160$0))
    (in$0 sk_l2_5$0 (intersection$0 sk_?X_158$0 sk_?X_157$0))
    (in$0 sk_l2_5$0 (intersection$0 sk_?X_166$0 sk_?X_163$0))
    (and (in$0 sk_l1_5$0 sk_?X_160$0)
         (not (<= (read$0 data$0 last_6$0) (read$0 data$0 sk_l1_5$0))))
    (and (in$0 sk_l1_5$0 sk_FP_3$0) (not (in$0 sk_l1_5$0 FP$0)))
    (and (in$0 sk_l2_5$0 sk_?X_157$0)
         (not (<= (read$0 data$0 last_6$0) (read$0 data$0 sk_l2_5$0))))
    (and (in$0 sk_l2_5$0 sk_?X_163$0)
         (not (<= (read$0 data$0 sk_l2_5$0) (read$0 data$0 last_6$0))))
    (not (= (read$1 next_3$0 last_6$0) a_3$0))
    (not (Btwn$0 next_3$0 a_3$0 null$0 null$0))
    (not (Btwn$0 next_3$0 b_4$0 null$0 null$0))
    (not (Btwn$0 next_3$0 res_9$0 last_6$0 last_6$0))
    (and (Btwn$0 next_3$0 sk_l1_5$0 sk_l2_5$0 null$0)
         (in$0 sk_l1_5$0 sk_?X_160$0) (in$0 sk_l2_5$0 sk_?X_160$0)
         (not (<= (read$0 data$0 sk_l1_5$0) (read$0 data$0 sk_l2_5$0))))
    (and (Btwn$0 next_3$0 sk_l1_5$0 sk_l2_5$0 last_6$0)
         (in$0 sk_l1_5$0 sk_?X_163$0) (in$0 sk_l2_5$0 sk_?X_163$0)
         (not (<= (read$0 data$0 sk_l1_5$0) (read$0 data$0 sk_l2_5$0))))
    (and (Btwn$0 next_3$0 sk_l2_5$0 sk_l1_5$0 null$0)
         (in$0 sk_l1_5$0 sk_?X_157$0) (in$0 sk_l2_5$0 sk_?X_157$0)
         (not (<= (read$0 data$0 sk_l2_5$0) (read$0 data$0 sk_l1_5$0))))))

(assert (not (in$0 null$0 Alloc$0)))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 b_init$0 l1 null$0)
                 (in$0 l1
                   (uslseg_domain$0 data$0 next$0 b_init$0 null$0
                     (read$0 data$0 last_init$0)))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 b_init$0 l1 null$0)))
                 (not
                      (in$0 l1
                        (uslseg_domain$0 data$0 next$0 b_init$0 null$0
                          (read$0 data$0 last_init$0))))))))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next_3$0 a_3$0 l1 null$0)
                 (in$0 l1
                   (uslseg_domain$0 data$0 next_3$0 a_3$0 null$0
                     (read$0 data$0 last_6$0)))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next_3$0 a_3$0 l1 null$0)))
                 (not
                      (in$0 l1
                        (uslseg_domain$0 data$0 next_3$0 a_3$0 null$0
                          (read$0 data$0 last_6$0))))))))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next_3$0 res_9$0 l1 last_6$0)
                 (in$0 l1
                   (lslseg_domain$0 data$0 next_3$0 res_9$0 last_6$0
                     (read$0 data$0 last_6$0)))
                 (not (= l1 last_6$0)))
            (and
                 (or (= l1 last_6$0)
                     (not (Btwn$0 next_3$0 res_9$0 l1 last_6$0)))
                 (not
                      (in$0 l1
                        (lslseg_domain$0 data$0 next_3$0 res_9$0 last_6$0
                          (read$0 data$0 last_6$0))))))))

(assert (forall ((?u Loc) (?v Loc) (?z Loc))
        (and
             (or (Btwn$0 (write$0 next$0 last_4$0 a_3$0) ?z ?u ?v)
                 (not
                      (or
                          (and (Btwn$0 next$0 ?z ?u ?v)
                               (or (Btwn$0 next$0 ?z ?v last_4$0)
                                   (and (Btwn$0 next$0 ?z ?v ?v)
                                        (not
                                             (Btwn$0 next$0 ?z last_4$0
                                               last_4$0)))))
                          (and (not (= last_4$0 ?v))
                               (or (Btwn$0 next$0 ?z last_4$0 ?v)
                                   (and (Btwn$0 next$0 ?z last_4$0 last_4$0)
                                        (not (Btwn$0 next$0 ?z ?v ?v))))
                               (Btwn$0 next$0 ?z ?u last_4$0)
                               (or (Btwn$0 next$0 a_3$0 ?v last_4$0)
                                   (and (Btwn$0 next$0 a_3$0 ?v ?v)
                                        (not
                                             (Btwn$0 next$0 a_3$0 last_4$0
                                               last_4$0)))))
                          (and (not (= last_4$0 ?v))
                               (or (Btwn$0 next$0 ?z last_4$0 ?v)
                                   (and (Btwn$0 next$0 ?z last_4$0 last_4$0)
                                        (not (Btwn$0 next$0 ?z ?v ?v))))
                               (Btwn$0 next$0 a_3$0 ?u ?v)
                               (or (Btwn$0 next$0 a_3$0 ?v last_4$0)
                                   (and (Btwn$0 next$0 a_3$0 ?v ?v)
                                        (not
                                             (Btwn$0 next$0 a_3$0 last_4$0
                                               last_4$0))))))))
             (or
                 (and (Btwn$0 next$0 ?z ?u ?v)
                      (or (Btwn$0 next$0 ?z ?v last_4$0)
                          (and (Btwn$0 next$0 ?z ?v ?v)
                               (not (Btwn$0 next$0 ?z last_4$0 last_4$0)))))
                 (and (not (= last_4$0 ?v))
                      (or (Btwn$0 next$0 ?z last_4$0 ?v)
                          (and (Btwn$0 next$0 ?z last_4$0 last_4$0)
                               (not (Btwn$0 next$0 ?z ?v ?v))))
                      (Btwn$0 next$0 ?z ?u last_4$0)
                      (or (Btwn$0 next$0 a_3$0 ?v last_4$0)
                          (and (Btwn$0 next$0 a_3$0 ?v ?v)
                               (not (Btwn$0 next$0 a_3$0 last_4$0 last_4$0)))))
                 (and (not (= last_4$0 ?v))
                      (or (Btwn$0 next$0 ?z last_4$0 ?v)
                          (and (Btwn$0 next$0 ?z last_4$0 last_4$0)
                               (not (Btwn$0 next$0 ?z ?v ?v))))
                      (Btwn$0 next$0 a_3$0 ?u ?v)
                      (or (Btwn$0 next$0 a_3$0 ?v last_4$0)
                          (and (Btwn$0 next$0 a_3$0 ?v ?v)
                               (not (Btwn$0 next$0 a_3$0 last_4$0 last_4$0)))))
                 (not (Btwn$0 (write$0 next$0 last_4$0 a_3$0) ?z ?u ?v))))))

(assert (forall ((?u Loc) (?v Loc) (?z Loc))
        (and
             (or (Btwn$0 (write$0 next$0 last_4$0 b_3$0) ?z ?u ?v)
                 (not
                      (or
                          (and (Btwn$0 next$0 ?z ?u ?v)
                               (or (Btwn$0 next$0 ?z ?v last_4$0)
                                   (and (Btwn$0 next$0 ?z ?v ?v)
                                        (not
                                             (Btwn$0 next$0 ?z last_4$0
                                               last_4$0)))))
                          (and (not (= last_4$0 ?v))
                               (or (Btwn$0 next$0 ?z last_4$0 ?v)
                                   (and (Btwn$0 next$0 ?z last_4$0 last_4$0)
                                        (not (Btwn$0 next$0 ?z ?v ?v))))
                               (Btwn$0 next$0 ?z ?u last_4$0)
                               (or (Btwn$0 next$0 b_3$0 ?v last_4$0)
                                   (and (Btwn$0 next$0 b_3$0 ?v ?v)
                                        (not
                                             (Btwn$0 next$0 b_3$0 last_4$0
                                               last_4$0)))))
                          (and (not (= last_4$0 ?v))
                               (or (Btwn$0 next$0 ?z last_4$0 ?v)
                                   (and (Btwn$0 next$0 ?z last_4$0 last_4$0)
                                        (not (Btwn$0 next$0 ?z ?v ?v))))
                               (Btwn$0 next$0 b_3$0 ?u ?v)
                               (or (Btwn$0 next$0 b_3$0 ?v last_4$0)
                                   (and (Btwn$0 next$0 b_3$0 ?v ?v)
                                        (not
                                             (Btwn$0 next$0 b_3$0 last_4$0
                                               last_4$0))))))))
             (or
                 (and (Btwn$0 next$0 ?z ?u ?v)
                      (or (Btwn$0 next$0 ?z ?v last_4$0)
                          (and (Btwn$0 next$0 ?z ?v ?v)
                               (not (Btwn$0 next$0 ?z last_4$0 last_4$0)))))
                 (and (not (= last_4$0 ?v))
                      (or (Btwn$0 next$0 ?z last_4$0 ?v)
                          (and (Btwn$0 next$0 ?z last_4$0 last_4$0)
                               (not (Btwn$0 next$0 ?z ?v ?v))))
                      (Btwn$0 next$0 ?z ?u last_4$0)
                      (or (Btwn$0 next$0 b_3$0 ?v last_4$0)
                          (and (Btwn$0 next$0 b_3$0 ?v ?v)
                               (not (Btwn$0 next$0 b_3$0 last_4$0 last_4$0)))))
                 (and (not (= last_4$0 ?v))
                      (or (Btwn$0 next$0 ?z last_4$0 ?v)
                          (and (Btwn$0 next$0 ?z last_4$0 last_4$0)
                               (not (Btwn$0 next$0 ?z ?v ?v))))
                      (Btwn$0 next$0 b_3$0 ?u ?v)
                      (or (Btwn$0 next$0 b_3$0 ?v last_4$0)
                          (and (Btwn$0 next$0 b_3$0 ?v ?v)
                               (not (Btwn$0 next$0 b_3$0 last_4$0 last_4$0)))))
                 (not (Btwn$0 (write$0 next$0 last_4$0 b_3$0) ?z ?u ?v))))))

(assert (forall ((?x Loc)) (Btwn$0 next_3$0 ?x ?x ?x)))

(assert (forall ((?x Loc)) (Btwn$0 next_2$0 ?x ?x ?x)))

(assert (forall ((?x Loc)) (Btwn$0 next$0 ?x ?x ?x)))

(assert (forall ((?x Loc) (?y Loc)) (or (not (Btwn$0 next_3$0 ?x ?y ?x)) (= ?x ?y))))

(assert (forall ((?x Loc) (?y Loc)) (or (not (Btwn$0 next_2$0 ?x ?y ?x)) (= ?x ?y))))

(assert (forall ((?x Loc) (?y Loc)) (or (not (Btwn$0 next$0 ?x ?y ?x)) (= ?x ?y))))

(assert (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_3$0 ?x ?y ?y)) (not (Btwn$0 next_3$0 ?x ?z ?z))
            (Btwn$0 next_3$0 ?x ?y ?z) (Btwn$0 next_3$0 ?x ?z ?y))))

(assert (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_2$0 ?x ?y ?y)) (not (Btwn$0 next_2$0 ?x ?z ?z))
            (Btwn$0 next_2$0 ?x ?y ?z) (Btwn$0 next_2$0 ?x ?z ?y))))

(assert (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?x ?z ?z))
            (Btwn$0 next$0 ?x ?y ?z) (Btwn$0 next$0 ?x ?z ?y))))

(assert (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_3$0 ?x ?y ?z))
            (and (Btwn$0 next_3$0 ?x ?y ?y) (Btwn$0 next_3$0 ?y ?z ?z)))))

(assert (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_2$0 ?x ?y ?z))
            (and (Btwn$0 next_2$0 ?x ?y ?y) (Btwn$0 next_2$0 ?y ?z ?z)))))

(assert (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z))
            (and (Btwn$0 next$0 ?x ?y ?y) (Btwn$0 next$0 ?y ?z ?z)))))

(assert (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_3$0 ?x ?y ?y)) (not (Btwn$0 next_3$0 ?y ?z ?z))
            (Btwn$0 next_3$0 ?x ?z ?z))))

(assert (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_2$0 ?x ?y ?y)) (not (Btwn$0 next_2$0 ?y ?z ?z))
            (Btwn$0 next_2$0 ?x ?z ?z))))

(assert (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?y ?z ?z))
            (Btwn$0 next$0 ?x ?z ?z))))

(assert (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_3$0 ?x ?y ?z)) (not (Btwn$0 next_3$0 ?y ?u ?z))
            (and (Btwn$0 next_3$0 ?x ?y ?u) (Btwn$0 next_3$0 ?x ?u ?z)))))

(assert (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_2$0 ?x ?y ?z)) (not (Btwn$0 next_2$0 ?y ?u ?z))
            (and (Btwn$0 next_2$0 ?x ?y ?u) (Btwn$0 next_2$0 ?x ?u ?z)))))

(assert (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?y ?u ?z))
            (and (Btwn$0 next$0 ?x ?y ?u) (Btwn$0 next$0 ?x ?u ?z)))))

(assert (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_3$0 ?x ?y ?z)) (not (Btwn$0 next_3$0 ?x ?u ?y))
            (and (Btwn$0 next_3$0 ?x ?u ?z) (Btwn$0 next_3$0 ?u ?y ?z)))))

(assert (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_2$0 ?x ?y ?z)) (not (Btwn$0 next_2$0 ?x ?u ?y))
            (and (Btwn$0 next_2$0 ?x ?u ?z) (Btwn$0 next_2$0 ?u ?y ?z)))))

(assert (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?x ?u ?y))
            (and (Btwn$0 next$0 ?x ?u ?z) (Btwn$0 next$0 ?u ?y ?z)))))

(check-sat)
(exit)
