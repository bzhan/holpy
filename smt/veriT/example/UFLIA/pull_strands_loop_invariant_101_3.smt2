(set-info :smt-lib-version 2.6)
(set-logic UFLIA)
(set-info :source |
  GRASShopper benchmarks.
  Authors: Ruzica Piskac, Thomas Wies, and Damien Zufferey
  URL: http://cs.nyu.edu/wies/software/grasshopper
  See also: GRASShopper - Complete Heap Verification with Mixed Specifications. In TACAS 2014, pages 124-139.

  If this benchmark is satisfiable, GRASShopper reports the following error message:
  tests/spl/sls/sls_strand_sort.spl:101:3-4:An invariant might not be maintained by a loop in procedure pull_strands
  tests/spl/sls/sls_strand_sort.spl:79:14:Related location: This is the loop invariant that might not be maintained
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
(declare-fun Axiom_92$0 () Bool)
(declare-fun Axiom_93$0 () Bool)
(declare-fun Axiom_94$0 () Bool)
(declare-fun Axiom_95$0 () Bool)
(declare-fun FP$0 () SetLoc)
(declare-fun FP_Caller$0 () SetLoc)
(declare-fun FP_Caller_4$0 () SetLoc)
(declare-fun curr_4$0 () Loc)
(declare-fun curr_5$0 () Loc)
(declare-fun curr_6$0 () Loc)
(declare-fun curr_init$0 () Loc)
(declare-fun data$0 () FldInt)
(declare-fun lseg_domain$0 (FldLoc Loc Loc) SetLoc)
(declare-fun lseg_struct$0 (SetLoc FldLoc Loc Loc) Bool)
(declare-fun lslseg_domain$0 (FldInt FldLoc Loc Loc Int) SetLoc)
(declare-fun lslseg_struct$0 (SetLoc FldInt FldLoc Loc Loc Int) Bool)
(declare-fun next$0 () FldLoc)
(declare-fun next_7$0 () FldLoc)
(declare-fun next_8$0 () FldLoc)
(declare-fun next_9$0 () FldLoc)
(declare-fun old_curr_2$0 () Loc)
(declare-fun old_curr_4$0 () Loc)
(declare-fun old_curr_init$0 () Loc)
(declare-fun prv_4$0 () Loc)
(declare-fun prv_5$0 () Loc)
(declare-fun prv_init$0 () Loc)
(declare-fun rest_6$0 () Loc)
(declare-fun rest_7$0 () Loc)
(declare-fun rest_init$0 () Loc)
(declare-fun sk_?X_312$0 () SetLoc)
(declare-fun sk_?X_313$0 () SetLoc)
(declare-fun sk_?X_314$0 () SetLoc)
(declare-fun sk_?X_315$0 () SetLoc)
(declare-fun sk_?X_316$0 () SetLoc)
(declare-fun sk_?X_317$0 () SetLoc)
(declare-fun sk_?X_318$0 () SetLoc)
(declare-fun sk_?X_319$0 () SetLoc)
(declare-fun sk_?X_320$0 () SetLoc)
(declare-fun sk_?X_321$0 () SetLoc)
(declare-fun sk_?X_322$0 () SetLoc)
(declare-fun sk_?X_323$0 () SetLoc)
(declare-fun sk_?X_324$0 () SetLoc)
(declare-fun sk_?X_325$0 () SetLoc)
(declare-fun sk_?X_326$0 () SetLoc)
(declare-fun sk_?X_327$0 () SetLoc)
(declare-fun sk_?X_328$0 () SetLoc)
(declare-fun sk_?X_329$0 () SetLoc)
(declare-fun sk_?X_330$0 () SetLoc)
(declare-fun sk_?X_331$0 () SetLoc)
(declare-fun sk_?X_332$0 () SetLoc)
(declare-fun sk_?X_333$0 () SetLoc)
(declare-fun sk_?X_334$0 () SetLoc)
(declare-fun sk_?X_335$0 () SetLoc)
(declare-fun sk_?X_336$0 () SetLoc)
(declare-fun sk_?X_337$0 () SetLoc)
(declare-fun sk_?X_338$0 () SetLoc)
(declare-fun sk_?X_339$0 () SetLoc)
(declare-fun sk_?X_340$0 () SetLoc)
(declare-fun sk_?X_341$0 () SetLoc)
(declare-fun sk_FP_6$0 () SetLoc)
(declare-fun sk_FP_7$0 () SetLoc)
(declare-fun sk_l1_10$0 () Loc)
(declare-fun sk_l1_11$0 () Loc)
(declare-fun sk_l2_10$0 () Loc)
(declare-fun sk_l2_11$0 () Loc)
(declare-fun sorted_7$0 () Loc)
(declare-fun sorted_init$0 () Loc)
(declare-fun sorted_tail_4$0 () Loc)
(declare-fun sorted_tail_5$0 () Loc)
(declare-fun sorted_tail_init$0 () Loc)

(assert (forall ((?y Loc))
        (or (not (Btwn$0 next$0 null$0 ?y ?y)) (= null$0 ?y)
            (Btwn$0 next$0 null$0 (read$1 next$0 null$0) ?y))))

(assert (forall ((?y Loc))
        (or (not (Btwn$0 next$0 curr_init$0 ?y ?y)) (= curr_init$0 ?y)
            (Btwn$0 next$0 curr_init$0 (read$1 next$0 curr_init$0) ?y))))

(assert (forall ((?y Loc))
        (or (not (Btwn$0 next$0 old_curr_4$0 ?y ?y)) (= old_curr_4$0 ?y)
            (Btwn$0 next$0 old_curr_4$0 (read$1 next$0 old_curr_4$0) ?y))))

(assert (forall ((?y Loc))
        (or (not (Btwn$0 next$0 prv_init$0 ?y ?y)) (= prv_init$0 ?y)
            (Btwn$0 next$0 prv_init$0 (read$1 next$0 prv_init$0) ?y))))

(assert (forall ((?y Loc))
        (or (not (Btwn$0 next$0 sorted_tail_5$0 ?y ?y))
            (= sorted_tail_5$0 ?y)
            (Btwn$0 next$0 sorted_tail_5$0 (read$1 next$0 sorted_tail_5$0)
              ?y))))

(assert (forall ((?y Loc))
        (or (not (Btwn$0 next$0 sorted_tail_4$0 ?y ?y))
            (= sorted_tail_4$0 ?y)
            (Btwn$0 next$0 sorted_tail_4$0 (read$1 next$0 sorted_tail_4$0)
              ?y))))

(assert (forall ((?y Loc))
        (or (not (Btwn$0 next_7$0 null$0 ?y ?y)) (= null$0 ?y)
            (Btwn$0 next_7$0 null$0 (read$1 next_7$0 null$0) ?y))))

(assert (forall ((?y Loc))
        (or (not (Btwn$0 next_7$0 old_curr_4$0 ?y ?y)) (= old_curr_4$0 ?y)
            (Btwn$0 next_7$0 old_curr_4$0 (read$1 next_7$0 old_curr_4$0) ?y))))

(assert (forall ((?y Loc))
        (or (not (Btwn$0 next_7$0 prv_init$0 ?y ?y)) (= prv_init$0 ?y)
            (Btwn$0 next_7$0 prv_init$0 (read$1 next_7$0 prv_init$0) ?y))))

(assert (forall ((?y Loc))
        (or (not (Btwn$0 next_7$0 sorted_tail_5$0 ?y ?y))
            (= sorted_tail_5$0 ?y)
            (Btwn$0 next_7$0 sorted_tail_5$0
              (read$1 next_7$0 sorted_tail_5$0) ?y))))

(assert (forall ((?y Loc))
        (or (not (Btwn$0 next_8$0 null$0 ?y ?y)) (= null$0 ?y)
            (Btwn$0 next_8$0 null$0 (read$1 next_8$0 null$0) ?y))))

(assert (forall ((?y Loc))
        (or (not (Btwn$0 next_8$0 prv_init$0 ?y ?y)) (= prv_init$0 ?y)
            (Btwn$0 next_8$0 prv_init$0 (read$1 next_8$0 prv_init$0) ?y))))

(assert (forall ((?y Loc))
        (or (not (Btwn$0 next_8$0 sorted_tail_5$0 ?y ?y))
            (= sorted_tail_5$0 ?y)
            (Btwn$0 next_8$0 sorted_tail_5$0
              (read$1 next_8$0 sorted_tail_5$0) ?y))))

(assert (forall ((?y Loc))
        (or (not (Btwn$0 next_9$0 null$0 ?y ?y)) (= null$0 ?y)
            (Btwn$0 next_9$0 null$0 (read$1 next_9$0 null$0) ?y))))

(assert (forall ((?y Loc))
        (or (not (Btwn$0 next_9$0 prv_init$0 ?y ?y)) (= prv_init$0 ?y)
            (Btwn$0 next_9$0 prv_init$0 (read$1 next_9$0 prv_init$0) ?y))))

(assert (forall ((?y Loc))
        (or (not (Btwn$0 next_9$0 sorted_tail_5$0 ?y ?y))
            (= sorted_tail_5$0 ?y)
            (Btwn$0 next_9$0 sorted_tail_5$0
              (read$1 next_9$0 sorted_tail_5$0) ?y))))

(assert (forall ((?y Loc))
        (or (not (= (read$1 next$0 null$0) null$0))
            (not (Btwn$0 next$0 null$0 ?y ?y)) (= null$0 ?y))))

(assert (forall ((?y Loc))
        (or (not (= (read$1 next$0 curr_init$0) curr_init$0))
            (not (Btwn$0 next$0 curr_init$0 ?y ?y)) (= curr_init$0 ?y))))

(assert (forall ((?y Loc))
        (or (not (= (read$1 next$0 old_curr_4$0) old_curr_4$0))
            (not (Btwn$0 next$0 old_curr_4$0 ?y ?y)) (= old_curr_4$0 ?y))))

(assert (forall ((?y Loc))
        (or (not (= (read$1 next$0 prv_init$0) prv_init$0))
            (not (Btwn$0 next$0 prv_init$0 ?y ?y)) (= prv_init$0 ?y))))

(assert (forall ((?y Loc))
        (or (not (= (read$1 next$0 sorted_tail_5$0) sorted_tail_5$0))
            (not (Btwn$0 next$0 sorted_tail_5$0 ?y ?y))
            (= sorted_tail_5$0 ?y))))

(assert (forall ((?y Loc))
        (or (not (= (read$1 next$0 sorted_tail_4$0) sorted_tail_4$0))
            (not (Btwn$0 next$0 sorted_tail_4$0 ?y ?y))
            (= sorted_tail_4$0 ?y))))

(assert (forall ((?y Loc))
        (or (not (= (read$1 next_7$0 null$0) null$0))
            (not (Btwn$0 next_7$0 null$0 ?y ?y)) (= null$0 ?y))))

(assert (forall ((?y Loc))
        (or (not (= (read$1 next_7$0 old_curr_4$0) old_curr_4$0))
            (not (Btwn$0 next_7$0 old_curr_4$0 ?y ?y)) (= old_curr_4$0 ?y))))

(assert (forall ((?y Loc))
        (or (not (= (read$1 next_7$0 prv_init$0) prv_init$0))
            (not (Btwn$0 next_7$0 prv_init$0 ?y ?y)) (= prv_init$0 ?y))))

(assert (forall ((?y Loc))
        (or (not (= (read$1 next_7$0 sorted_tail_5$0) sorted_tail_5$0))
            (not (Btwn$0 next_7$0 sorted_tail_5$0 ?y ?y))
            (= sorted_tail_5$0 ?y))))

(assert (forall ((?y Loc))
        (or (not (= (read$1 next_8$0 null$0) null$0))
            (not (Btwn$0 next_8$0 null$0 ?y ?y)) (= null$0 ?y))))

(assert (forall ((?y Loc))
        (or (not (= (read$1 next_8$0 prv_init$0) prv_init$0))
            (not (Btwn$0 next_8$0 prv_init$0 ?y ?y)) (= prv_init$0 ?y))))

(assert (forall ((?y Loc))
        (or (not (= (read$1 next_8$0 sorted_tail_5$0) sorted_tail_5$0))
            (not (Btwn$0 next_8$0 sorted_tail_5$0 ?y ?y))
            (= sorted_tail_5$0 ?y))))

(assert (forall ((?y Loc))
        (or (not (= (read$1 next_9$0 null$0) null$0))
            (not (Btwn$0 next_9$0 null$0 ?y ?y)) (= null$0 ?y))))

(assert (forall ((?y Loc))
        (or (not (= (read$1 next_9$0 prv_init$0) prv_init$0))
            (not (Btwn$0 next_9$0 prv_init$0 ?y ?y)) (= prv_init$0 ?y))))

(assert (forall ((?y Loc))
        (or (not (= (read$1 next_9$0 sorted_tail_5$0) sorted_tail_5$0))
            (not (Btwn$0 next_9$0 sorted_tail_5$0 ?y ?y))
            (= sorted_tail_5$0 ?y))))

(assert (Btwn$0 next$0 null$0 (read$1 next$0 null$0) (read$1 next$0 null$0)))

(assert (Btwn$0 next$0 curr_init$0 (read$1 next$0 curr_init$0)
  (read$1 next$0 curr_init$0)))

(assert (Btwn$0 next$0 old_curr_4$0 (read$1 next$0 old_curr_4$0)
  (read$1 next$0 old_curr_4$0)))

(assert (Btwn$0 next$0 prv_init$0 (read$1 next$0 prv_init$0)
  (read$1 next$0 prv_init$0)))

(assert (Btwn$0 next$0 sorted_tail_5$0 (read$1 next$0 sorted_tail_5$0)
  (read$1 next$0 sorted_tail_5$0)))

(assert (Btwn$0 next$0 sorted_tail_4$0 (read$1 next$0 sorted_tail_4$0)
  (read$1 next$0 sorted_tail_4$0)))

(assert (Btwn$0 next_7$0 null$0 (read$1 next_7$0 null$0) (read$1 next_7$0 null$0)))

(assert (Btwn$0 next_7$0 old_curr_4$0 (read$1 next_7$0 old_curr_4$0)
  (read$1 next_7$0 old_curr_4$0)))

(assert (Btwn$0 next_7$0 prv_init$0 (read$1 next_7$0 prv_init$0)
  (read$1 next_7$0 prv_init$0)))

(assert (Btwn$0 next_7$0 sorted_tail_5$0 (read$1 next_7$0 sorted_tail_5$0)
  (read$1 next_7$0 sorted_tail_5$0)))

(assert (Btwn$0 next_8$0 null$0 (read$1 next_8$0 null$0) (read$1 next_8$0 null$0)))

(assert (Btwn$0 next_8$0 prv_init$0 (read$1 next_8$0 prv_init$0)
  (read$1 next_8$0 prv_init$0)))

(assert (Btwn$0 next_8$0 sorted_tail_5$0 (read$1 next_8$0 sorted_tail_5$0)
  (read$1 next_8$0 sorted_tail_5$0)))

(assert (Btwn$0 next_9$0 null$0 (read$1 next_9$0 null$0) (read$1 next_9$0 null$0)))

(assert (Btwn$0 next_9$0 prv_init$0 (read$1 next_9$0 prv_init$0)
  (read$1 next_9$0 prv_init$0)))

(assert (Btwn$0 next_9$0 sorted_tail_5$0 (read$1 next_9$0 sorted_tail_5$0)
  (read$1 next_9$0 sorted_tail_5$0)))

(assert (forall ((l1 Loc))
        (or (not Axiom_95$0)
            (or (<= (read$0 data$0 l1) (read$0 data$0 sorted_tail_5$0))
                (not (in$0 l1 sk_?X_333$0))))))

(assert (forall ((l1 Loc) (l2 Loc))
        (or (not Axiom_94$0)
            (or (<= (read$0 data$0 l1) (read$0 data$0 l2))
                (not (Btwn$0 next_9$0 l1 l2 sorted_tail_5$0))
                (not (in$0 l1 sk_?X_333$0)) (not (in$0 l2 sk_?X_333$0))))))

(assert (forall ((l1 Loc))
        (or (not Axiom_93$0)
            (or (<= (read$0 data$0 l1) (read$0 data$0 sorted_tail_init$0))
                (not (in$0 l1 sk_?X_318$0))))))

(assert (forall ((l1 Loc) (l2 Loc))
        (or (not Axiom_92$0)
            (or (<= (read$0 data$0 l1) (read$0 data$0 l2))
                (not (Btwn$0 next$0 l1 l2 sorted_tail_init$0))
                (not (in$0 l1 sk_?X_318$0)) (not (in$0 l2 sk_?X_318$0))))))

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
            (and (in$0 x (union$0 sk_?X_316$0 sk_?X_315$0))
                 (or (in$0 x sk_?X_316$0) (in$0 x sk_?X_315$0)))
            (and (not (in$0 x sk_?X_316$0)) (not (in$0 x sk_?X_315$0))
                 (not (in$0 x (union$0 sk_?X_316$0 sk_?X_315$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_317$0 sk_?X_315$0))
                 (or (in$0 x sk_?X_317$0) (in$0 x sk_?X_315$0)))
            (and (not (in$0 x sk_?X_317$0)) (not (in$0 x sk_?X_315$0))
                 (not (in$0 x (union$0 sk_?X_317$0 sk_?X_315$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_319$0 sk_?X_318$0))
                 (or (in$0 x sk_?X_319$0) (in$0 x sk_?X_318$0)))
            (and (not (in$0 x sk_?X_319$0)) (not (in$0 x sk_?X_318$0))
                 (not (in$0 x (union$0 sk_?X_319$0 sk_?X_318$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_320$0 sk_?X_318$0))
                 (or (in$0 x sk_?X_320$0) (in$0 x sk_?X_318$0)))
            (and (not (in$0 x sk_?X_320$0)) (not (in$0 x sk_?X_318$0))
                 (not (in$0 x (union$0 sk_?X_320$0 sk_?X_318$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_326$0 emptyset$0))
                 (or (in$0 x sk_?X_326$0) (in$0 x emptyset$0)))
            (and (not (in$0 x sk_?X_326$0)) (not (in$0 x emptyset$0))
                 (not (in$0 x (union$0 sk_?X_326$0 emptyset$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_326$0 sk_?X_322$0))
                 (or (in$0 x sk_?X_326$0) (in$0 x sk_?X_322$0)))
            (and (not (in$0 x sk_?X_326$0)) (not (in$0 x sk_?X_322$0))
                 (not (in$0 x (union$0 sk_?X_326$0 sk_?X_322$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_325$0 sk_?X_323$0))
                 (or (in$0 x sk_?X_325$0) (in$0 x sk_?X_323$0)))
            (and (not (in$0 x sk_?X_325$0)) (not (in$0 x sk_?X_323$0))
                 (not (in$0 x (union$0 sk_?X_325$0 sk_?X_323$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_334$0 sk_?X_333$0))
                 (or (in$0 x sk_?X_334$0) (in$0 x sk_?X_333$0)))
            (and (not (in$0 x sk_?X_334$0)) (not (in$0 x sk_?X_333$0))
                 (not (in$0 x (union$0 sk_?X_334$0 sk_?X_333$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_335$0 sk_?X_333$0))
                 (or (in$0 x sk_?X_335$0) (in$0 x sk_?X_333$0)))
            (and (not (in$0 x sk_?X_335$0)) (not (in$0 x sk_?X_333$0))
                 (not (in$0 x (union$0 sk_?X_335$0 sk_?X_333$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_341$0 emptyset$0))
                 (or (in$0 x sk_?X_341$0) (in$0 x emptyset$0)))
            (and (not (in$0 x sk_?X_341$0)) (not (in$0 x emptyset$0))
                 (not (in$0 x (union$0 sk_?X_341$0 emptyset$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_341$0 sk_?X_337$0))
                 (or (in$0 x sk_?X_341$0) (in$0 x sk_?X_337$0)))
            (and (not (in$0 x sk_?X_341$0)) (not (in$0 x sk_?X_337$0))
                 (not (in$0 x (union$0 sk_?X_341$0 sk_?X_337$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_340$0 sk_?X_323$0))
                 (or (in$0 x sk_?X_340$0) (in$0 x sk_?X_323$0)))
            (and (not (in$0 x sk_?X_340$0)) (not (in$0 x sk_?X_323$0))
                 (not (in$0 x (union$0 sk_?X_340$0 sk_?X_323$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_332$0 sk_?X_330$0))
                 (or (in$0 x sk_?X_332$0) (in$0 x sk_?X_330$0)))
            (and (not (in$0 x sk_?X_332$0)) (not (in$0 x sk_?X_330$0))
                 (not (in$0 x (union$0 sk_?X_332$0 sk_?X_330$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_331$0 sk_?X_330$0))
                 (or (in$0 x sk_?X_331$0) (in$0 x sk_?X_330$0)))
            (and (not (in$0 x sk_?X_331$0)) (not (in$0 x sk_?X_330$0))
                 (not (in$0 x (union$0 sk_?X_331$0 sk_?X_330$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_316$0) (in$0 x sk_?X_315$0)
                 (in$0 x (intersection$0 sk_?X_316$0 sk_?X_315$0)))
            (and (or (not (in$0 x sk_?X_316$0)) (not (in$0 x sk_?X_315$0)))
                 (not (in$0 x (intersection$0 sk_?X_316$0 sk_?X_315$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_317$0) (in$0 x sk_?X_315$0)
                 (in$0 x (intersection$0 sk_?X_317$0 sk_?X_315$0)))
            (and (or (not (in$0 x sk_?X_317$0)) (not (in$0 x sk_?X_315$0)))
                 (not (in$0 x (intersection$0 sk_?X_317$0 sk_?X_315$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_319$0) (in$0 x sk_?X_318$0)
                 (in$0 x (intersection$0 sk_?X_319$0 sk_?X_318$0)))
            (and (or (not (in$0 x sk_?X_319$0)) (not (in$0 x sk_?X_318$0)))
                 (not (in$0 x (intersection$0 sk_?X_319$0 sk_?X_318$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_320$0) (in$0 x sk_?X_318$0)
                 (in$0 x (intersection$0 sk_?X_320$0 sk_?X_318$0)))
            (and (or (not (in$0 x sk_?X_320$0)) (not (in$0 x sk_?X_318$0)))
                 (not (in$0 x (intersection$0 sk_?X_320$0 sk_?X_318$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_325$0) (in$0 x sk_?X_323$0)
                 (in$0 x (intersection$0 sk_?X_325$0 sk_?X_323$0)))
            (and (or (not (in$0 x sk_?X_325$0)) (not (in$0 x sk_?X_323$0)))
                 (not (in$0 x (intersection$0 sk_?X_325$0 sk_?X_323$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_326$0) (in$0 x emptyset$0)
                 (in$0 x (intersection$0 sk_?X_326$0 emptyset$0)))
            (and (or (not (in$0 x sk_?X_326$0)) (not (in$0 x emptyset$0)))
                 (not (in$0 x (intersection$0 sk_?X_326$0 emptyset$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_326$0) (in$0 x sk_?X_322$0)
                 (in$0 x (intersection$0 sk_?X_326$0 sk_?X_322$0)))
            (and (or (not (in$0 x sk_?X_326$0)) (not (in$0 x sk_?X_322$0)))
                 (not (in$0 x (intersection$0 sk_?X_326$0 sk_?X_322$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_331$0) (in$0 x sk_?X_330$0)
                 (in$0 x (intersection$0 sk_?X_331$0 sk_?X_330$0)))
            (and (or (not (in$0 x sk_?X_331$0)) (not (in$0 x sk_?X_330$0)))
                 (not (in$0 x (intersection$0 sk_?X_331$0 sk_?X_330$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_332$0) (in$0 x sk_?X_330$0)
                 (in$0 x (intersection$0 sk_?X_332$0 sk_?X_330$0)))
            (and (or (not (in$0 x sk_?X_332$0)) (not (in$0 x sk_?X_330$0)))
                 (not (in$0 x (intersection$0 sk_?X_332$0 sk_?X_330$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_334$0) (in$0 x sk_?X_333$0)
                 (in$0 x (intersection$0 sk_?X_334$0 sk_?X_333$0)))
            (and (or (not (in$0 x sk_?X_334$0)) (not (in$0 x sk_?X_333$0)))
                 (not (in$0 x (intersection$0 sk_?X_334$0 sk_?X_333$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_335$0) (in$0 x sk_?X_333$0)
                 (in$0 x (intersection$0 sk_?X_335$0 sk_?X_333$0)))
            (and (or (not (in$0 x sk_?X_335$0)) (not (in$0 x sk_?X_333$0)))
                 (not (in$0 x (intersection$0 sk_?X_335$0 sk_?X_333$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_340$0) (in$0 x sk_?X_323$0)
                 (in$0 x (intersection$0 sk_?X_340$0 sk_?X_323$0)))
            (and (or (not (in$0 x sk_?X_340$0)) (not (in$0 x sk_?X_323$0)))
                 (not (in$0 x (intersection$0 sk_?X_340$0 sk_?X_323$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_341$0) (in$0 x emptyset$0)
                 (in$0 x (intersection$0 sk_?X_341$0 emptyset$0)))
            (and (or (not (in$0 x sk_?X_341$0)) (not (in$0 x emptyset$0)))
                 (not (in$0 x (intersection$0 sk_?X_341$0 emptyset$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_341$0) (in$0 x sk_?X_337$0)
                 (in$0 x (intersection$0 sk_?X_341$0 sk_?X_337$0)))
            (and (or (not (in$0 x sk_?X_341$0)) (not (in$0 x sk_?X_337$0)))
                 (not (in$0 x (intersection$0 sk_?X_341$0 sk_?X_337$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x FP_Caller$0) (in$0 x (setminus$0 FP_Caller$0 FP$0))
                 (not (in$0 x FP$0)))
            (and (or (in$0 x FP$0) (not (in$0 x FP_Caller$0)))
                 (not (in$0 x (setminus$0 FP_Caller$0 FP$0)))))))

(assert (forall ((y Loc) (x Loc))
        (or (and (= x y) (in$0 x (setenum$0 y)))
            (and (not (= x y)) (not (in$0 x (setenum$0 y)))))))

(assert (= (read$1 (write$0 next$0 sorted_tail_4$0 old_curr_4$0) sorted_tail_4$0)
  old_curr_4$0))

(assert (or (= null$0 sorted_tail_4$0)
    (= (read$1 next$0 null$0)
      (read$1 (write$0 next$0 sorted_tail_4$0 old_curr_4$0) null$0))))

(assert (or (= curr_init$0 sorted_tail_4$0)
    (= (read$1 next$0 curr_init$0)
      (read$1 (write$0 next$0 sorted_tail_4$0 old_curr_4$0) curr_init$0))))

(assert (or (= old_curr_4$0 sorted_tail_4$0)
    (= (read$1 next$0 old_curr_4$0)
      (read$1 (write$0 next$0 sorted_tail_4$0 old_curr_4$0) old_curr_4$0))))

(assert (or (= prv_init$0 sorted_tail_4$0)
    (= (read$1 next$0 prv_init$0)
      (read$1 (write$0 next$0 sorted_tail_4$0 old_curr_4$0) prv_init$0))))

(assert (or (= sorted_tail_5$0 sorted_tail_4$0)
    (= (read$1 next$0 sorted_tail_5$0)
      (read$1 (write$0 next$0 sorted_tail_4$0 old_curr_4$0) sorted_tail_5$0))))

(assert (or (= sorted_tail_4$0 sorted_tail_4$0)
    (= (read$1 next$0 sorted_tail_4$0)
      (read$1 (write$0 next$0 sorted_tail_4$0 old_curr_4$0) sorted_tail_4$0))))

(assert (= (read$1 (write$0 next_7$0 old_curr_4$0 null$0) old_curr_4$0) null$0))

(assert (or (= null$0 old_curr_4$0)
    (= (read$1 next_7$0 null$0)
      (read$1 (write$0 next_7$0 old_curr_4$0 null$0) null$0))))

(assert (or (= old_curr_4$0 old_curr_4$0)
    (= (read$1 next_7$0 old_curr_4$0)
      (read$1 (write$0 next_7$0 old_curr_4$0 null$0) old_curr_4$0))))

(assert (or (= prv_init$0 old_curr_4$0)
    (= (read$1 next_7$0 prv_init$0)
      (read$1 (write$0 next_7$0 old_curr_4$0 null$0) prv_init$0))))

(assert (or (= sorted_tail_5$0 old_curr_4$0)
    (= (read$1 next_7$0 sorted_tail_5$0)
      (read$1 (write$0 next_7$0 old_curr_4$0 null$0) sorted_tail_5$0))))

(assert (= (read$1 (write$0 next_8$0 prv_init$0 curr_6$0) prv_init$0) curr_6$0))

(assert (or (= null$0 prv_init$0)
    (= (read$1 next_8$0 null$0)
      (read$1 (write$0 next_8$0 prv_init$0 curr_6$0) null$0))))

(assert (or (= prv_init$0 prv_init$0)
    (= (read$1 next_8$0 prv_init$0)
      (read$1 (write$0 next_8$0 prv_init$0 curr_6$0) prv_init$0))))

(assert (or (= sorted_tail_5$0 prv_init$0)
    (= (read$1 next_8$0 sorted_tail_5$0)
      (read$1 (write$0 next_8$0 prv_init$0 curr_6$0) sorted_tail_5$0))))

(assert (= (read$1 next$0 null$0) null$0))

(assert (= (read$1 next_7$0 null$0) null$0))

(assert (= (read$1 next_8$0 null$0) null$0))

(assert (= (read$1 next_9$0 null$0) null$0))

(assert (forall ((x Loc)) (not (in$0 x emptyset$0))))

(assert (or (Btwn$0 next$0 rest_init$0 prv_init$0 prv_init$0)
    (not (lseg_struct$0 sk_?X_325$0 next$0 rest_init$0 prv_init$0))))

(assert (or (Btwn$0 next_9$0 rest_7$0 prv_4$0 prv_4$0)
    (not (lseg_struct$0 sk_?X_340$0 next_9$0 rest_7$0 prv_4$0))))

(assert (or
    (and (Btwn$0 next_9$0 sorted_7$0 sorted_tail_5$0 sorted_tail_5$0)
         Axiom_95$0 Axiom_94$0)
    (not
         (lslseg_struct$0 sk_?X_333$0 data$0 next_9$0 sorted_7$0
           sorted_tail_5$0 (read$0 data$0 sorted_tail_5$0)))))

(assert (= FP_Caller_4$0 (setminus$0 FP_Caller$0 FP$0)))

(assert (= old_curr_2$0 old_curr_init$0))

(assert (= rest_6$0 rest_init$0))

(assert (= sorted_tail_4$0 sorted_tail_init$0))

(assert (= sk_?X_312$0 (union$0 sk_?X_316$0 sk_?X_314$0)))

(assert (= sk_?X_314$0 sk_?X_315$0))

(assert (= sk_?X_316$0 (union$0 sk_?X_319$0 sk_?X_318$0)))

(assert (= sk_?X_318$0
  (lslseg_domain$0 data$0 next$0 sorted_init$0 sorted_tail_init$0
    (read$0 data$0 sorted_tail_init$0))))

(assert (= sk_?X_320$0 (union$0 sk_?X_326$0 sk_?X_322$0)))

(assert (= sk_?X_322$0 (union$0 sk_?X_325$0 sk_?X_323$0)))

(assert (= sk_?X_324$0 (setenum$0 prv_init$0)))

(assert (= sk_?X_326$0 (lseg_domain$0 next$0 curr_init$0 null$0)))

(assert (or
    (and (= (read$1 next$0 prv_init$0) curr_init$0)
         (= (read$1 next$0 sorted_tail_init$0) null$0)
         (= emptyset$0 emptyset$0)
         (= emptyset$0 (intersection$0 sk_?X_317$0 sk_?X_314$0))
         (= emptyset$0 (intersection$0 sk_?X_320$0 sk_?X_318$0))
         (= emptyset$0 (intersection$0 sk_?X_325$0 sk_?X_323$0))
         (= emptyset$0 (intersection$0 sk_?X_326$0 sk_?X_322$0))
         (= sk_?X_313$0 FP$0)
         (lseg_struct$0 sk_?X_325$0 next$0 rest_init$0 prv_init$0)
         (lseg_struct$0 sk_?X_326$0 next$0 curr_init$0 null$0)
         (lslseg_struct$0 sk_?X_318$0 data$0 next$0 sorted_init$0
           sorted_tail_init$0 (read$0 data$0 sorted_tail_init$0)))
    (and (= (read$1 next$0 sorted_tail_init$0) null$0)
         (= emptyset$0 emptyset$0)
         (= emptyset$0 (intersection$0 sk_?X_316$0 sk_?X_314$0))
         (= emptyset$0 (intersection$0 sk_?X_319$0 sk_?X_318$0))
         (= emptyset$0 (intersection$0 sk_?X_326$0 sk_?X_321$0))
         (= prv_init$0 null$0) (= rest_init$0 curr_init$0)
         (= sk_?X_312$0 FP$0)
         (lseg_struct$0 sk_?X_326$0 next$0 curr_init$0 null$0)
         (lslseg_struct$0 sk_?X_318$0 data$0 next$0 sorted_init$0
           sorted_tail_init$0 (read$0 data$0 sorted_tail_init$0)))))

(assert (= sk_?X_328$0 (union$0 sk_?X_332$0 sk_?X_329$0)))

(assert (= sk_?X_330$0 (setenum$0 sorted_tail_5$0)))

(assert (= sk_?X_332$0 (union$0 sk_?X_335$0 sk_?X_333$0)))

(assert (= sk_?X_334$0 (union$0 sk_?X_341$0 sk_?X_336$0)))

(assert (= sk_?X_336$0 emptyset$0))

(assert (= sk_?X_338$0 sk_?X_339$0))

(assert (= sk_?X_340$0 (lseg_domain$0 next_9$0 rest_7$0 prv_4$0)))

(assert (= sk_FP_6$0 sk_?X_328$0))

(assert (or (in$0 sk_l1_10$0 (intersection$0 sk_?X_332$0 sk_?X_329$0))
    (in$0 sk_l1_10$0 (intersection$0 sk_?X_340$0 sk_?X_338$0))
    (in$0 sk_l2_10$0 (intersection$0 sk_?X_335$0 sk_?X_333$0))
    (in$0 sk_l2_10$0 (intersection$0 sk_?X_341$0 sk_?X_337$0))
    (and (in$0 sk_l1_10$0 sk_FP_6$0) (not (in$0 sk_l1_10$0 FP$0)))
    (and (in$0 sk_l2_10$0 sk_?X_333$0)
         (not
              (<= (read$0 data$0 sk_l2_10$0) (read$0 data$0 sorted_tail_5$0))))
    (not (= (read$1 next_9$0 prv_4$0) curr_6$0))
    (not (= (read$1 next_9$0 sorted_tail_5$0) null$0))
    (not (Btwn$0 next_9$0 curr_6$0 null$0 null$0))
    (not (Btwn$0 next_9$0 rest_7$0 prv_4$0 prv_4$0))
    (not (Btwn$0 next_9$0 sorted_7$0 sorted_tail_5$0 sorted_tail_5$0))
    (and (Btwn$0 next_9$0 sk_l1_10$0 sk_l2_10$0 sorted_tail_5$0)
         (in$0 sk_l1_10$0 sk_?X_333$0) (in$0 sk_l2_10$0 sk_?X_333$0)
         (not (<= (read$0 data$0 sk_l1_10$0) (read$0 data$0 sk_l2_10$0))))))

(assert (not (= curr_4$0 null$0)))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 curr_init$0 l1 null$0)
                 (in$0 l1 (lseg_domain$0 next$0 curr_init$0 null$0))
                 (not (= l1 null$0)))
            (and
                 (or (= l1 null$0)
                     (not (Btwn$0 next$0 curr_init$0 l1 null$0)))
                 (not (in$0 l1 (lseg_domain$0 next$0 curr_init$0 null$0)))))))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 sorted_init$0 l1 sorted_tail_init$0)
                 (in$0 l1
                   (lslseg_domain$0 data$0 next$0 sorted_init$0
                     sorted_tail_init$0 (read$0 data$0 sorted_tail_init$0)))
                 (not (= l1 sorted_tail_init$0)))
            (and
                 (or (= l1 sorted_tail_init$0)
                     (not
                          (Btwn$0 next$0 sorted_init$0 l1 sorted_tail_init$0)))
                 (not
                      (in$0 l1
                        (lslseg_domain$0 data$0 next$0 sorted_init$0
                          sorted_tail_init$0
                          (read$0 data$0 sorted_tail_init$0))))))))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next_9$0 rest_7$0 l1 prv_4$0)
                 (in$0 l1 (lseg_domain$0 next_9$0 rest_7$0 prv_4$0))
                 (not (= l1 prv_4$0)))
            (and
                 (or (= l1 prv_4$0)
                     (not (Btwn$0 next_9$0 rest_7$0 l1 prv_4$0)))
                 (not (in$0 l1 (lseg_domain$0 next_9$0 rest_7$0 prv_4$0)))))))

(assert (or (Btwn$0 next$0 curr_init$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_326$0 next$0 curr_init$0 null$0))))

(assert (or (Btwn$0 next_9$0 curr_6$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_341$0 next_9$0 curr_6$0 null$0))))

(assert (or
    (and (Btwn$0 next$0 sorted_init$0 sorted_tail_init$0 sorted_tail_init$0)
         Axiom_93$0 Axiom_92$0)
    (not
         (lslseg_struct$0 sk_?X_318$0 data$0 next$0 sorted_init$0
           sorted_tail_init$0 (read$0 data$0 sorted_tail_init$0)))))

(assert (or
    (and
         (or
             (and (= next_9$0 (write$0 next_8$0 prv_4$0 curr_6$0))
                  (not (= prv_4$0 null$0)))
             (and (= next_9$0 next_8$0) (= prv_4$0 null$0)))
         (or (and (= rest_6$0 old_curr_4$0) (= rest_7$0 curr_6$0))
             (and (= rest_7$0 rest_6$0) (not (= rest_6$0 old_curr_4$0))))
         (= curr_6$0 (read$1 next$0 curr_4$0))
         (= next_7$0 (write$0 next$0 sorted_tail_4$0 old_curr_4$0))
         (= next_8$0 (write$0 next_7$0 old_curr_4$0 null$0))
         (= old_curr_4$0 curr_4$0) (= sorted_tail_5$0 old_curr_4$0)
         (>= (read$0 data$0 curr_4$0) (read$0 data$0 sorted_tail_4$0)))
    (and (= curr_5$0 (read$1 next$0 curr_4$0)) (= curr_6$0 curr_5$0)
         (= next_9$0 next$0) (= old_curr_4$0 old_curr_2$0)
         (= prv_4$0 prv_5$0) (= prv_5$0 curr_4$0) (= rest_7$0 rest_6$0)
         (= sorted_tail_5$0 sorted_tail_4$0)
         (not (>= (read$0 data$0 curr_4$0) (read$0 data$0 sorted_tail_4$0))))))

(assert (= curr_4$0 curr_init$0))

(assert (= prv_4$0 prv_init$0))

(assert (= sorted_7$0 sorted_init$0))

(assert (= Alloc$0 (union$0 FP_Caller$0 Alloc$0)))

(assert (= sk_?X_313$0 (union$0 sk_?X_317$0 sk_?X_314$0)))

(assert (= sk_?X_315$0 (setenum$0 sorted_tail_init$0)))

(assert (= sk_?X_317$0 (union$0 sk_?X_320$0 sk_?X_318$0)))

(assert (= sk_?X_319$0 (union$0 sk_?X_326$0 sk_?X_321$0)))

(assert (= sk_?X_321$0 emptyset$0))

(assert (= sk_?X_323$0 sk_?X_324$0))

(assert (= sk_?X_325$0 (lseg_domain$0 next$0 rest_init$0 prv_init$0)))

(assert (= FP_Caller$0 (union$0 FP$0 FP_Caller$0)))

(assert (= sk_?X_327$0 (union$0 sk_?X_331$0 sk_?X_329$0)))

(assert (= sk_?X_329$0 sk_?X_330$0))

(assert (= sk_?X_331$0 (union$0 sk_?X_334$0 sk_?X_333$0)))

(assert (= sk_?X_333$0
  (lslseg_domain$0 data$0 next_9$0 sorted_7$0 sorted_tail_5$0
    (read$0 data$0 sorted_tail_5$0))))

(assert (= sk_?X_335$0 (union$0 sk_?X_341$0 sk_?X_337$0)))

(assert (= sk_?X_337$0 (union$0 sk_?X_340$0 sk_?X_338$0)))

(assert (= sk_?X_339$0 (setenum$0 prv_4$0)))

(assert (= sk_?X_341$0 (lseg_domain$0 next_9$0 curr_6$0 null$0)))

(assert (= sk_FP_7$0 sk_?X_327$0))

(assert (or (in$0 sk_l1_11$0 (intersection$0 sk_?X_334$0 sk_?X_333$0))
    (in$0 sk_l2_11$0 (intersection$0 sk_?X_331$0 sk_?X_329$0))
    (in$0 sk_l2_11$0 (intersection$0 sk_?X_341$0 sk_?X_336$0))
    (and (in$0 sk_l1_11$0 sk_FP_7$0) (not (in$0 sk_l1_11$0 FP$0)))
    (and (in$0 sk_l2_11$0 sk_?X_333$0)
         (not
              (<= (read$0 data$0 sk_l2_11$0) (read$0 data$0 sorted_tail_5$0))))
    (not (= (read$1 next_9$0 sorted_tail_5$0) null$0))
    (not (= prv_4$0 null$0)) (not (= rest_7$0 curr_6$0))
    (not (Btwn$0 next_9$0 curr_6$0 null$0 null$0))
    (not (Btwn$0 next_9$0 sorted_7$0 sorted_tail_5$0 sorted_tail_5$0))
    (and (Btwn$0 next_9$0 sk_l1_11$0 sk_l2_11$0 sorted_tail_5$0)
         (in$0 sk_l1_11$0 sk_?X_333$0) (in$0 sk_l2_11$0 sk_?X_333$0)
         (not (<= (read$0 data$0 sk_l1_11$0) (read$0 data$0 sk_l2_11$0))))))

(assert (not (in$0 null$0 Alloc$0)))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 rest_init$0 l1 prv_init$0)
                 (in$0 l1 (lseg_domain$0 next$0 rest_init$0 prv_init$0))
                 (not (= l1 prv_init$0)))
            (and
                 (or (= l1 prv_init$0)
                     (not (Btwn$0 next$0 rest_init$0 l1 prv_init$0)))
                 (not
                      (in$0 l1 (lseg_domain$0 next$0 rest_init$0 prv_init$0)))))))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next_9$0 curr_6$0 l1 null$0)
                 (in$0 l1 (lseg_domain$0 next_9$0 curr_6$0 null$0))
                 (not (= l1 null$0)))
            (and
                 (or (= l1 null$0)
                     (not (Btwn$0 next_9$0 curr_6$0 l1 null$0)))
                 (not (in$0 l1 (lseg_domain$0 next_9$0 curr_6$0 null$0)))))))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next_9$0 sorted_7$0 l1 sorted_tail_5$0)
                 (in$0 l1
                   (lslseg_domain$0 data$0 next_9$0 sorted_7$0
                     sorted_tail_5$0 (read$0 data$0 sorted_tail_5$0)))
                 (not (= l1 sorted_tail_5$0)))
            (and
                 (or (= l1 sorted_tail_5$0)
                     (not (Btwn$0 next_9$0 sorted_7$0 l1 sorted_tail_5$0)))
                 (not
                      (in$0 l1
                        (lslseg_domain$0 data$0 next_9$0 sorted_7$0
                          sorted_tail_5$0 (read$0 data$0 sorted_tail_5$0))))))))

(assert (forall ((?u Loc) (?v Loc) (?z Loc))
        (and
             (or
                 (Btwn$0 (write$0 next$0 sorted_tail_4$0 old_curr_4$0) ?z ?u
                   ?v)
                 (not
                      (or
                          (and (Btwn$0 next$0 ?z ?u ?v)
                               (or (Btwn$0 next$0 ?z ?v sorted_tail_4$0)
                                   (and (Btwn$0 next$0 ?z ?v ?v)
                                        (not
                                             (Btwn$0 next$0 ?z
                                               sorted_tail_4$0
                                               sorted_tail_4$0)))))
                          (and (not (= sorted_tail_4$0 ?v))
                               (or (Btwn$0 next$0 ?z sorted_tail_4$0 ?v)
                                   (and
                                        (Btwn$0 next$0 ?z sorted_tail_4$0
                                          sorted_tail_4$0)
                                        (not (Btwn$0 next$0 ?z ?v ?v))))
                               (Btwn$0 next$0 ?z ?u sorted_tail_4$0)
                               (or
                                   (Btwn$0 next$0 old_curr_4$0 ?v
                                     sorted_tail_4$0)
                                   (and (Btwn$0 next$0 old_curr_4$0 ?v ?v)
                                        (not
                                             (Btwn$0 next$0 old_curr_4$0
                                               sorted_tail_4$0
                                               sorted_tail_4$0)))))
                          (and (not (= sorted_tail_4$0 ?v))
                               (or (Btwn$0 next$0 ?z sorted_tail_4$0 ?v)
                                   (and
                                        (Btwn$0 next$0 ?z sorted_tail_4$0
                                          sorted_tail_4$0)
                                        (not (Btwn$0 next$0 ?z ?v ?v))))
                               (Btwn$0 next$0 old_curr_4$0 ?u ?v)
                               (or
                                   (Btwn$0 next$0 old_curr_4$0 ?v
                                     sorted_tail_4$0)
                                   (and (Btwn$0 next$0 old_curr_4$0 ?v ?v)
                                        (not
                                             (Btwn$0 next$0 old_curr_4$0
                                               sorted_tail_4$0
                                               sorted_tail_4$0))))))))
             (or
                 (and (Btwn$0 next$0 ?z ?u ?v)
                      (or (Btwn$0 next$0 ?z ?v sorted_tail_4$0)
                          (and (Btwn$0 next$0 ?z ?v ?v)
                               (not
                                    (Btwn$0 next$0 ?z sorted_tail_4$0
                                      sorted_tail_4$0)))))
                 (and (not (= sorted_tail_4$0 ?v))
                      (or (Btwn$0 next$0 ?z sorted_tail_4$0 ?v)
                          (and
                               (Btwn$0 next$0 ?z sorted_tail_4$0
                                 sorted_tail_4$0)
                               (not (Btwn$0 next$0 ?z ?v ?v))))
                      (Btwn$0 next$0 ?z ?u sorted_tail_4$0)
                      (or (Btwn$0 next$0 old_curr_4$0 ?v sorted_tail_4$0)
                          (and (Btwn$0 next$0 old_curr_4$0 ?v ?v)
                               (not
                                    (Btwn$0 next$0 old_curr_4$0
                                      sorted_tail_4$0 sorted_tail_4$0)))))
                 (and (not (= sorted_tail_4$0 ?v))
                      (or (Btwn$0 next$0 ?z sorted_tail_4$0 ?v)
                          (and
                               (Btwn$0 next$0 ?z sorted_tail_4$0
                                 sorted_tail_4$0)
                               (not (Btwn$0 next$0 ?z ?v ?v))))
                      (Btwn$0 next$0 old_curr_4$0 ?u ?v)
                      (or (Btwn$0 next$0 old_curr_4$0 ?v sorted_tail_4$0)
                          (and (Btwn$0 next$0 old_curr_4$0 ?v ?v)
                               (not
                                    (Btwn$0 next$0 old_curr_4$0
                                      sorted_tail_4$0 sorted_tail_4$0)))))
                 (not
                      (Btwn$0 (write$0 next$0 sorted_tail_4$0 old_curr_4$0)
                        ?z ?u ?v))))))

(assert (forall ((?u Loc) (?v Loc) (?z Loc))
        (and
             (or (Btwn$0 (write$0 next_7$0 old_curr_4$0 null$0) ?z ?u ?v)
                 (not
                      (or
                          (and (Btwn$0 next_7$0 ?z ?u ?v)
                               (or (Btwn$0 next_7$0 ?z ?v old_curr_4$0)
                                   (and (Btwn$0 next_7$0 ?z ?v ?v)
                                        (not
                                             (Btwn$0 next_7$0 ?z old_curr_4$0
                                               old_curr_4$0)))))
                          (and (not (= old_curr_4$0 ?v))
                               (or (Btwn$0 next_7$0 ?z old_curr_4$0 ?v)
                                   (and
                                        (Btwn$0 next_7$0 ?z old_curr_4$0
                                          old_curr_4$0)
                                        (not (Btwn$0 next_7$0 ?z ?v ?v))))
                               (Btwn$0 next_7$0 ?z ?u old_curr_4$0)
                               (or (Btwn$0 next_7$0 null$0 ?v old_curr_4$0)
                                   (and (Btwn$0 next_7$0 null$0 ?v ?v)
                                        (not
                                             (Btwn$0 next_7$0 null$0
                                               old_curr_4$0 old_curr_4$0)))))
                          (and (not (= old_curr_4$0 ?v))
                               (or (Btwn$0 next_7$0 ?z old_curr_4$0 ?v)
                                   (and
                                        (Btwn$0 next_7$0 ?z old_curr_4$0
                                          old_curr_4$0)
                                        (not (Btwn$0 next_7$0 ?z ?v ?v))))
                               (Btwn$0 next_7$0 null$0 ?u ?v)
                               (or (Btwn$0 next_7$0 null$0 ?v old_curr_4$0)
                                   (and (Btwn$0 next_7$0 null$0 ?v ?v)
                                        (not
                                             (Btwn$0 next_7$0 null$0
                                               old_curr_4$0 old_curr_4$0))))))))
             (or
                 (and (Btwn$0 next_7$0 ?z ?u ?v)
                      (or (Btwn$0 next_7$0 ?z ?v old_curr_4$0)
                          (and (Btwn$0 next_7$0 ?z ?v ?v)
                               (not
                                    (Btwn$0 next_7$0 ?z old_curr_4$0
                                      old_curr_4$0)))))
                 (and (not (= old_curr_4$0 ?v))
                      (or (Btwn$0 next_7$0 ?z old_curr_4$0 ?v)
                          (and (Btwn$0 next_7$0 ?z old_curr_4$0 old_curr_4$0)
                               (not (Btwn$0 next_7$0 ?z ?v ?v))))
                      (Btwn$0 next_7$0 ?z ?u old_curr_4$0)
                      (or (Btwn$0 next_7$0 null$0 ?v old_curr_4$0)
                          (and (Btwn$0 next_7$0 null$0 ?v ?v)
                               (not
                                    (Btwn$0 next_7$0 null$0 old_curr_4$0
                                      old_curr_4$0)))))
                 (and (not (= old_curr_4$0 ?v))
                      (or (Btwn$0 next_7$0 ?z old_curr_4$0 ?v)
                          (and (Btwn$0 next_7$0 ?z old_curr_4$0 old_curr_4$0)
                               (not (Btwn$0 next_7$0 ?z ?v ?v))))
                      (Btwn$0 next_7$0 null$0 ?u ?v)
                      (or (Btwn$0 next_7$0 null$0 ?v old_curr_4$0)
                          (and (Btwn$0 next_7$0 null$0 ?v ?v)
                               (not
                                    (Btwn$0 next_7$0 null$0 old_curr_4$0
                                      old_curr_4$0)))))
                 (not
                      (Btwn$0 (write$0 next_7$0 old_curr_4$0 null$0) ?z ?u
                        ?v))))))

(assert (forall ((?u Loc) (?v Loc) (?z Loc))
        (and
             (or (Btwn$0 (write$0 next_8$0 prv_4$0 curr_6$0) ?z ?u ?v)
                 (not
                      (or
                          (and (Btwn$0 next_8$0 ?z ?u ?v)
                               (or (Btwn$0 next_8$0 ?z ?v prv_4$0)
                                   (and (Btwn$0 next_8$0 ?z ?v ?v)
                                        (not
                                             (Btwn$0 next_8$0 ?z prv_4$0
                                               prv_4$0)))))
                          (and (not (= prv_4$0 ?v))
                               (or (Btwn$0 next_8$0 ?z prv_4$0 ?v)
                                   (and (Btwn$0 next_8$0 ?z prv_4$0 prv_4$0)
                                        (not (Btwn$0 next_8$0 ?z ?v ?v))))
                               (Btwn$0 next_8$0 ?z ?u prv_4$0)
                               (or (Btwn$0 next_8$0 curr_6$0 ?v prv_4$0)
                                   (and (Btwn$0 next_8$0 curr_6$0 ?v ?v)
                                        (not
                                             (Btwn$0 next_8$0 curr_6$0
                                               prv_4$0 prv_4$0)))))
                          (and (not (= prv_4$0 ?v))
                               (or (Btwn$0 next_8$0 ?z prv_4$0 ?v)
                                   (and (Btwn$0 next_8$0 ?z prv_4$0 prv_4$0)
                                        (not (Btwn$0 next_8$0 ?z ?v ?v))))
                               (Btwn$0 next_8$0 curr_6$0 ?u ?v)
                               (or (Btwn$0 next_8$0 curr_6$0 ?v prv_4$0)
                                   (and (Btwn$0 next_8$0 curr_6$0 ?v ?v)
                                        (not
                                             (Btwn$0 next_8$0 curr_6$0
                                               prv_4$0 prv_4$0))))))))
             (or
                 (and (Btwn$0 next_8$0 ?z ?u ?v)
                      (or (Btwn$0 next_8$0 ?z ?v prv_4$0)
                          (and (Btwn$0 next_8$0 ?z ?v ?v)
                               (not (Btwn$0 next_8$0 ?z prv_4$0 prv_4$0)))))
                 (and (not (= prv_4$0 ?v))
                      (or (Btwn$0 next_8$0 ?z prv_4$0 ?v)
                          (and (Btwn$0 next_8$0 ?z prv_4$0 prv_4$0)
                               (not (Btwn$0 next_8$0 ?z ?v ?v))))
                      (Btwn$0 next_8$0 ?z ?u prv_4$0)
                      (or (Btwn$0 next_8$0 curr_6$0 ?v prv_4$0)
                          (and (Btwn$0 next_8$0 curr_6$0 ?v ?v)
                               (not
                                    (Btwn$0 next_8$0 curr_6$0 prv_4$0
                                      prv_4$0)))))
                 (and (not (= prv_4$0 ?v))
                      (or (Btwn$0 next_8$0 ?z prv_4$0 ?v)
                          (and (Btwn$0 next_8$0 ?z prv_4$0 prv_4$0)
                               (not (Btwn$0 next_8$0 ?z ?v ?v))))
                      (Btwn$0 next_8$0 curr_6$0 ?u ?v)
                      (or (Btwn$0 next_8$0 curr_6$0 ?v prv_4$0)
                          (and (Btwn$0 next_8$0 curr_6$0 ?v ?v)
                               (not
                                    (Btwn$0 next_8$0 curr_6$0 prv_4$0
                                      prv_4$0)))))
                 (not (Btwn$0 (write$0 next_8$0 prv_4$0 curr_6$0) ?z ?u ?v))))))

(assert (forall ((?x Loc)) (Btwn$0 next_9$0 ?x ?x ?x)))

(assert (forall ((?x Loc)) (Btwn$0 next_8$0 ?x ?x ?x)))

(assert (forall ((?x Loc)) (Btwn$0 next_7$0 ?x ?x ?x)))

(assert (forall ((?x Loc)) (Btwn$0 next$0 ?x ?x ?x)))

(assert (forall ((?x Loc) (?y Loc)) (or (not (Btwn$0 next_9$0 ?x ?y ?x)) (= ?x ?y))))

(assert (forall ((?x Loc) (?y Loc)) (or (not (Btwn$0 next_8$0 ?x ?y ?x)) (= ?x ?y))))

(assert (forall ((?x Loc) (?y Loc)) (or (not (Btwn$0 next_7$0 ?x ?y ?x)) (= ?x ?y))))

(assert (forall ((?x Loc) (?y Loc)) (or (not (Btwn$0 next$0 ?x ?y ?x)) (= ?x ?y))))

(assert (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_9$0 ?x ?y ?y)) (not (Btwn$0 next_9$0 ?x ?z ?z))
            (Btwn$0 next_9$0 ?x ?y ?z) (Btwn$0 next_9$0 ?x ?z ?y))))

(assert (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_8$0 ?x ?y ?y)) (not (Btwn$0 next_8$0 ?x ?z ?z))
            (Btwn$0 next_8$0 ?x ?y ?z) (Btwn$0 next_8$0 ?x ?z ?y))))

(assert (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_7$0 ?x ?y ?y)) (not (Btwn$0 next_7$0 ?x ?z ?z))
            (Btwn$0 next_7$0 ?x ?y ?z) (Btwn$0 next_7$0 ?x ?z ?y))))

(assert (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?x ?z ?z))
            (Btwn$0 next$0 ?x ?y ?z) (Btwn$0 next$0 ?x ?z ?y))))

(assert (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_9$0 ?x ?y ?z))
            (and (Btwn$0 next_9$0 ?x ?y ?y) (Btwn$0 next_9$0 ?y ?z ?z)))))

(assert (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_8$0 ?x ?y ?z))
            (and (Btwn$0 next_8$0 ?x ?y ?y) (Btwn$0 next_8$0 ?y ?z ?z)))))

(assert (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_7$0 ?x ?y ?z))
            (and (Btwn$0 next_7$0 ?x ?y ?y) (Btwn$0 next_7$0 ?y ?z ?z)))))

(assert (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z))
            (and (Btwn$0 next$0 ?x ?y ?y) (Btwn$0 next$0 ?y ?z ?z)))))

(assert (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_9$0 ?x ?y ?y)) (not (Btwn$0 next_9$0 ?y ?z ?z))
            (Btwn$0 next_9$0 ?x ?z ?z))))

(assert (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_8$0 ?x ?y ?y)) (not (Btwn$0 next_8$0 ?y ?z ?z))
            (Btwn$0 next_8$0 ?x ?z ?z))))

(assert (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_7$0 ?x ?y ?y)) (not (Btwn$0 next_7$0 ?y ?z ?z))
            (Btwn$0 next_7$0 ?x ?z ?z))))

(assert (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?y ?z ?z))
            (Btwn$0 next$0 ?x ?z ?z))))

(assert (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_9$0 ?x ?y ?z)) (not (Btwn$0 next_9$0 ?y ?u ?z))
            (and (Btwn$0 next_9$0 ?x ?y ?u) (Btwn$0 next_9$0 ?x ?u ?z)))))

(assert (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_8$0 ?x ?y ?z)) (not (Btwn$0 next_8$0 ?y ?u ?z))
            (and (Btwn$0 next_8$0 ?x ?y ?u) (Btwn$0 next_8$0 ?x ?u ?z)))))

(assert (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_7$0 ?x ?y ?z)) (not (Btwn$0 next_7$0 ?y ?u ?z))
            (and (Btwn$0 next_7$0 ?x ?y ?u) (Btwn$0 next_7$0 ?x ?u ?z)))))

(assert (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?y ?u ?z))
            (and (Btwn$0 next$0 ?x ?y ?u) (Btwn$0 next$0 ?x ?u ?z)))))

(assert (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_9$0 ?x ?y ?z)) (not (Btwn$0 next_9$0 ?x ?u ?y))
            (and (Btwn$0 next_9$0 ?x ?u ?z) (Btwn$0 next_9$0 ?u ?y ?z)))))

(assert (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_8$0 ?x ?y ?z)) (not (Btwn$0 next_8$0 ?x ?u ?y))
            (and (Btwn$0 next_8$0 ?x ?u ?z) (Btwn$0 next_8$0 ?u ?y ?z)))))

(assert (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_7$0 ?x ?y ?z)) (not (Btwn$0 next_7$0 ?x ?u ?y))
            (and (Btwn$0 next_7$0 ?x ?u ?z) (Btwn$0 next_7$0 ?u ?y ?z)))))

(assert (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?x ?u ?y))
            (and (Btwn$0 next$0 ?x ?u ?z) (Btwn$0 next$0 ?u ?y ?z)))))

(check-sat)
(exit)
