(set-info :smt-lib-version 2.6)
(set-logic UFLIA)
(set-info :source |
  GRASShopper benchmarks.
  Authors: Ruzica Piskac, Thomas Wies, and Damien Zufferey
  URL: http://cs.nyu.edu/wies/software/grasshopper
  See also: GRASShopper - Complete Heap Verification with Mixed Specifications. In TACAS 2014, pages 124-139.

  If this benchmark is satisfiable, GRASShopper reports the following error message:
  tests/spl/sls/sls_merge_sort.spl:88:1-2:A postcondition of procedure split might not hold at this return point
  tests/spl/sls/sls_merge_sort.spl:67:10-41:Related location: This is the postcondition that might not hold
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
(declare-fun read$0 (FldLoc Loc) Loc)
(declare-fun write$0 (FldLoc Loc Loc) FldLoc)
(declare-fun ep$0 (FldLoc SetLoc Loc) Loc)
(declare-fun emptyset$0 () SetLoc)
(declare-fun setenum$0 (Loc) SetLoc)
(declare-fun union$0 (SetLoc SetLoc) SetLoc)
(declare-fun intersection$0 (SetLoc SetLoc) SetLoc)
(declare-fun setminus$0 (SetLoc SetLoc) SetLoc)
(declare-fun Btwn$0 (FldLoc Loc Loc Loc) Bool)
(declare-fun Frame$0 (SetLoc SetLoc FldLoc FldLoc) Bool)
(declare-fun Frame$1 (SetLoc SetLoc FldInt FldInt) Bool)
(declare-fun in$0 (Loc SetLoc) Bool)
(declare-fun Alloc$0 () SetLoc)
(declare-fun FP$0 () SetLoc)
(declare-fun FP_13$0 () SetLoc)
(declare-fun FP_14$0 () SetLoc)
(declare-fun FP_Caller$0 () SetLoc)
(declare-fun FP_Caller_4$0 () SetLoc)
(declare-fun FP_Caller_final_8$0 () SetLoc)
(declare-fun curr_2$0 () Loc)
(declare-fun curr_3$0 () Loc)
(declare-fun data$0 () FldInt)
(declare-fun lseg_domain$0 (FldLoc Loc Loc) SetLoc)
(declare-fun lseg_struct$0 (SetLoc FldLoc Loc Loc) Bool)
(declare-fun next$0 () FldLoc)
(declare-fun next_9$0 () FldLoc)
(declare-fun sk_?X_252$0 () SetLoc)
(declare-fun sk_?X_253$0 () SetLoc)
(declare-fun sk_?X_254$0 () SetLoc)
(declare-fun sk_?X_255$0 () SetLoc)
(declare-fun sk_?X_256$0 () SetLoc)
(declare-fun sk_?X_257$0 () SetLoc)
(declare-fun sk_?X_258$0 () SetLoc)
(declare-fun sk_?X_259$0 () SetLoc)
(declare-fun sk_?X_260$0 () SetLoc)
(declare-fun sk_?X_261$0 () SetLoc)
(declare-fun sk_?X_262$0 () SetLoc)
(declare-fun sk_?X_263$0 () SetLoc)
(declare-fun sk_?X_264$0 () SetLoc)
(declare-fun sk_?X_265$0 () SetLoc)
(declare-fun sk_?e_4$0 () Loc)
(declare-fun tmp$0 () Loc)
(declare-fun tmp_2$0 () Loc)
(declare-fun x_1$0 () Loc)
(declare-fun y_6$0 () Loc)
(declare-fun y_7$0 () Loc)
(declare-fun z_1$0 () Loc)
(declare-fun z_2$0 () Loc)
(declare-fun z_3$0 () Loc)

(assert (forall ((?y Loc))
        (or (not (Btwn$0 next$0 tmp_2$0 ?y ?y)) (= tmp_2$0 ?y)
            (Btwn$0 next$0 tmp_2$0 (read$0 next$0 tmp_2$0) ?y))))

(assert (forall ((?y Loc))
        (or (not (Btwn$0 next$0 z_2$0 ?y ?y)) (= z_2$0 ?y)
            (Btwn$0 next$0 z_2$0 (read$0 next$0 z_2$0) ?y))))

(assert (forall ((?y Loc))
        (or (not (Btwn$0 next$0 curr_3$0 ?y ?y)) (= curr_3$0 ?y)
            (Btwn$0 next$0 curr_3$0 (read$0 next$0 curr_3$0) ?y))))

(assert (forall ((?y Loc))
        (or (not (Btwn$0 next_9$0 curr_3$0 ?y ?y)) (= curr_3$0 ?y)
            (Btwn$0 next_9$0 curr_3$0 (read$0 next_9$0 curr_3$0) ?y))))

(assert (forall ((?y Loc))
        (or (not (= (read$0 next$0 tmp_2$0) tmp_2$0))
            (not (Btwn$0 next$0 tmp_2$0 ?y ?y)) (= tmp_2$0 ?y))))

(assert (forall ((?y Loc))
        (or (not (= (read$0 next$0 z_2$0) z_2$0))
            (not (Btwn$0 next$0 z_2$0 ?y ?y)) (= z_2$0 ?y))))

(assert (forall ((?y Loc))
        (or (not (= (read$0 next$0 curr_3$0) curr_3$0))
            (not (Btwn$0 next$0 curr_3$0 ?y ?y)) (= curr_3$0 ?y))))

(assert (forall ((?y Loc))
        (or (not (= (read$0 next_9$0 curr_3$0) curr_3$0))
            (not (Btwn$0 next_9$0 curr_3$0 ?y ?y)) (= curr_3$0 ?y))))

(assert (Btwn$0 next$0 tmp_2$0 (read$0 next$0 tmp_2$0) (read$0 next$0 tmp_2$0)))

(assert (Btwn$0 next$0 z_2$0 (read$0 next$0 z_2$0) (read$0 next$0 z_2$0)))

(assert (Btwn$0 next$0 curr_3$0 (read$0 next$0 curr_3$0) (read$0 next$0 curr_3$0)))

(assert (Btwn$0 next_9$0 curr_3$0 (read$0 next_9$0 curr_3$0)
  (read$0 next_9$0 curr_3$0)))

(assert (forall ((?y Loc))
        (or (Btwn$0 next$0 y_7$0 (ep$0 next$0 FP_13$0 y_7$0) ?y)
            (not (Btwn$0 next$0 y_7$0 ?y ?y)) (not (in$0 ?y FP_13$0)))))

(assert (forall ((?y Loc))
        (or (Btwn$0 next$0 curr_3$0 (ep$0 next$0 FP_13$0 curr_3$0) ?y)
            (not (Btwn$0 next$0 curr_3$0 ?y ?y)) (not (in$0 ?y FP_13$0)))))

(assert (forall ((?y Loc))
        (or (Btwn$0 next$0 sk_?e_4$0 (ep$0 next$0 FP_13$0 sk_?e_4$0) ?y)
            (not (Btwn$0 next$0 sk_?e_4$0 ?y ?y)) (not (in$0 ?y FP_13$0)))))

(assert (forall ((?y Loc))
        (or (Btwn$0 next$0 z_2$0 (ep$0 next$0 FP_13$0 z_2$0) ?y)
            (not (Btwn$0 next$0 z_2$0 ?y ?y)) (not (in$0 ?y FP_13$0)))))

(assert (forall ((?y Loc))
        (or (Btwn$0 next$0 z_3$0 (ep$0 next$0 FP_13$0 z_3$0) ?y)
            (not (Btwn$0 next$0 z_3$0 ?y ?y)) (not (in$0 ?y FP_13$0)))))

(assert (Btwn$0 next$0 y_7$0 (ep$0 next$0 FP_13$0 y_7$0) (ep$0 next$0 FP_13$0 y_7$0)))

(assert (Btwn$0 next$0 curr_3$0 (ep$0 next$0 FP_13$0 curr_3$0)
  (ep$0 next$0 FP_13$0 curr_3$0)))

(assert (Btwn$0 next$0 sk_?e_4$0 (ep$0 next$0 FP_13$0 sk_?e_4$0)
  (ep$0 next$0 FP_13$0 sk_?e_4$0)))

(assert (Btwn$0 next$0 z_2$0 (ep$0 next$0 FP_13$0 z_2$0) (ep$0 next$0 FP_13$0 z_2$0)))

(assert (Btwn$0 next$0 z_3$0 (ep$0 next$0 FP_13$0 z_3$0) (ep$0 next$0 FP_13$0 z_3$0)))

(assert (or (in$0 (ep$0 next$0 FP_13$0 y_7$0) FP_13$0)
    (= y_7$0 (ep$0 next$0 FP_13$0 y_7$0))))

(assert (or (in$0 (ep$0 next$0 FP_13$0 curr_3$0) FP_13$0)
    (= curr_3$0 (ep$0 next$0 FP_13$0 curr_3$0))))

(assert (or (in$0 (ep$0 next$0 FP_13$0 sk_?e_4$0) FP_13$0)
    (= sk_?e_4$0 (ep$0 next$0 FP_13$0 sk_?e_4$0))))

(assert (or (in$0 (ep$0 next$0 FP_13$0 z_2$0) FP_13$0)
    (= z_2$0 (ep$0 next$0 FP_13$0 z_2$0))))

(assert (or (in$0 (ep$0 next$0 FP_13$0 z_3$0) FP_13$0)
    (= z_3$0 (ep$0 next$0 FP_13$0 z_3$0))))

(assert (forall ((x Loc))
        (or
            (and
                 (in$0 x
                   (union$0 (intersection$0 Alloc$0 FP$0)
                     (setminus$0 Alloc$0 Alloc$0)))
                 (or (in$0 x (intersection$0 Alloc$0 FP$0))
                     (in$0 x (setminus$0 Alloc$0 Alloc$0))))
            (and (not (in$0 x (intersection$0 Alloc$0 FP$0)))
                 (not (in$0 x (setminus$0 Alloc$0 Alloc$0)))
                 (not
                      (in$0 x
                        (union$0 (intersection$0 Alloc$0 FP$0)
                          (setminus$0 Alloc$0 Alloc$0))))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_Caller$0 Alloc$0))
                 (or (in$0 x FP_Caller$0) (in$0 x Alloc$0)))
            (and (not (in$0 x FP_Caller$0)) (not (in$0 x Alloc$0))
                 (not (in$0 x (union$0 FP_Caller$0 Alloc$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_14$0 Alloc$0))
                 (or (in$0 x FP_14$0) (in$0 x Alloc$0)))
            (and (not (in$0 x FP_14$0)) (not (in$0 x Alloc$0))
                 (not (in$0 x (union$0 FP_14$0 Alloc$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_259$0 sk_?X_262$0))
                 (or (in$0 x sk_?X_259$0) (in$0 x sk_?X_262$0)))
            (and (not (in$0 x sk_?X_259$0)) (not (in$0 x sk_?X_262$0))
                 (not (in$0 x (union$0 sk_?X_259$0 sk_?X_262$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 (setminus$0 FP$0 FP_13$0) sk_?X_256$0))
                 (or (in$0 x (setminus$0 FP$0 FP_13$0)) (in$0 x sk_?X_256$0)))
            (and (not (in$0 x (setminus$0 FP$0 FP_13$0)))
                 (not (in$0 x sk_?X_256$0))
                 (not
                      (in$0 x
                        (union$0 (setminus$0 FP$0 FP_13$0) sk_?X_256$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_262$0 FP_Caller$0))
                 (or (in$0 x sk_?X_262$0) (in$0 x FP_Caller$0)))
            (and (not (in$0 x sk_?X_262$0)) (not (in$0 x FP_Caller$0))
                 (not (in$0 x (union$0 sk_?X_262$0 FP_Caller$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_Caller_4$0 FP_14$0))
                 (or (in$0 x FP_Caller_4$0) (in$0 x FP_14$0)))
            (and (not (in$0 x FP_Caller_4$0)) (not (in$0 x FP_14$0))
                 (not (in$0 x (union$0 FP_Caller_4$0 FP_14$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_252$0 sk_?X_253$0))
                 (or (in$0 x sk_?X_252$0) (in$0 x sk_?X_253$0)))
            (and (not (in$0 x sk_?X_252$0)) (not (in$0 x sk_?X_253$0))
                 (not (in$0 x (union$0 sk_?X_252$0 sk_?X_253$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_254$0 sk_?X_255$0))
                 (or (in$0 x sk_?X_254$0) (in$0 x sk_?X_255$0)))
            (and (not (in$0 x sk_?X_254$0)) (not (in$0 x sk_?X_255$0))
                 (not (in$0 x (union$0 sk_?X_254$0 sk_?X_255$0)))))))

(assert (forall ((x Loc))
        (or
            (and
                 (in$0 x
                   (union$0 (intersection$0 Alloc$0 FP_13$0)
                     (setminus$0 Alloc$0 Alloc$0)))
                 (or (in$0 x (intersection$0 Alloc$0 FP_13$0))
                     (in$0 x (setminus$0 Alloc$0 Alloc$0))))
            (and (not (in$0 x (intersection$0 Alloc$0 FP_13$0)))
                 (not (in$0 x (setminus$0 Alloc$0 Alloc$0)))
                 (not
                      (in$0 x
                        (union$0 (intersection$0 Alloc$0 FP_13$0)
                          (setminus$0 Alloc$0 Alloc$0))))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_260$0 sk_?X_260$0))
                 (or (in$0 x sk_?X_260$0) (in$0 x sk_?X_260$0)))
            (and (not (in$0 x sk_?X_260$0)) (not (in$0 x sk_?X_260$0))
                 (not (in$0 x (union$0 sk_?X_260$0 sk_?X_260$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_13$0 sk_?X_262$0))
                 (or (in$0 x FP_13$0) (in$0 x sk_?X_262$0)))
            (and (not (in$0 x FP_13$0)) (not (in$0 x sk_?X_262$0))
                 (not (in$0 x (union$0 FP_13$0 sk_?X_262$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_263$0 sk_?X_264$0))
                 (or (in$0 x sk_?X_263$0) (in$0 x sk_?X_264$0)))
            (and (not (in$0 x sk_?X_263$0)) (not (in$0 x sk_?X_264$0))
                 (not (in$0 x (union$0 sk_?X_263$0 sk_?X_264$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_260$0) (in$0 x sk_?X_260$0)
                 (in$0 x (intersection$0 sk_?X_260$0 sk_?X_260$0)))
            (and (or (not (in$0 x sk_?X_260$0)) (not (in$0 x sk_?X_260$0)))
                 (not (in$0 x (intersection$0 sk_?X_260$0 sk_?X_260$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_259$0) (in$0 x sk_?X_262$0)
                 (in$0 x (intersection$0 sk_?X_259$0 sk_?X_262$0)))
            (and (or (not (in$0 x sk_?X_259$0)) (not (in$0 x sk_?X_262$0)))
                 (not (in$0 x (intersection$0 sk_?X_259$0 sk_?X_262$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_254$0) (in$0 x sk_?X_255$0)
                 (in$0 x (intersection$0 sk_?X_254$0 sk_?X_255$0)))
            (and (or (not (in$0 x sk_?X_254$0)) (not (in$0 x sk_?X_255$0)))
                 (not (in$0 x (intersection$0 sk_?X_254$0 sk_?X_255$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_252$0) (in$0 x sk_?X_253$0)
                 (in$0 x (intersection$0 sk_?X_252$0 sk_?X_253$0)))
            (and (or (not (in$0 x sk_?X_252$0)) (not (in$0 x sk_?X_253$0)))
                 (not (in$0 x (intersection$0 sk_?X_252$0 sk_?X_253$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x Alloc$0) (in$0 x sk_?X_262$0)
                 (in$0 x (intersection$0 Alloc$0 sk_?X_262$0)))
            (and (or (not (in$0 x Alloc$0)) (not (in$0 x sk_?X_262$0)))
                 (not (in$0 x (intersection$0 Alloc$0 sk_?X_262$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x Alloc$0) (in$0 x FP_13$0)
                 (in$0 x (intersection$0 Alloc$0 FP_13$0)))
            (and (or (not (in$0 x Alloc$0)) (not (in$0 x FP_13$0)))
                 (not (in$0 x (intersection$0 Alloc$0 FP_13$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_263$0) (in$0 x sk_?X_264$0)
                 (in$0 x (intersection$0 sk_?X_263$0 sk_?X_264$0)))
            (and (or (not (in$0 x sk_?X_263$0)) (not (in$0 x sk_?X_264$0)))
                 (not (in$0 x (intersection$0 sk_?X_263$0 sk_?X_264$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x Alloc$0) (in$0 x (setminus$0 Alloc$0 Alloc$0))
                 (not (in$0 x Alloc$0)))
            (and (or (in$0 x Alloc$0) (not (in$0 x Alloc$0)))
                 (not (in$0 x (setminus$0 Alloc$0 Alloc$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_262$0)
                 (in$0 x (setminus$0 sk_?X_262$0 FP_13$0))
                 (not (in$0 x FP_13$0)))
            (and (or (in$0 x FP_13$0) (not (in$0 x sk_?X_262$0)))
                 (not (in$0 x (setminus$0 sk_?X_262$0 FP_13$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x FP_Caller$0)
                 (in$0 x (setminus$0 FP_Caller$0 sk_?X_262$0))
                 (not (in$0 x sk_?X_262$0)))
            (and (or (in$0 x sk_?X_262$0) (not (in$0 x FP_Caller$0)))
                 (not (in$0 x (setminus$0 FP_Caller$0 sk_?X_262$0)))))))

(assert (forall ((y Loc) (x Loc))
        (or (and (= x y) (in$0 x (setenum$0 y)))
            (and (not (= x y)) (not (in$0 x (setenum$0 y)))))))

(assert (= (read$0 (write$0 next$0 tmp_2$0 curr_3$0) tmp_2$0) curr_3$0))

(assert (or (= tmp_2$0 tmp_2$0)
    (= (read$0 next$0 tmp_2$0)
      (read$0 (write$0 next$0 tmp_2$0 curr_3$0) tmp_2$0))))

(assert (or (= z_2$0 tmp_2$0)
    (= (read$0 next$0 z_2$0)
      (read$0 (write$0 next$0 tmp_2$0 curr_3$0) z_2$0))))

(assert (or (= curr_3$0 tmp_2$0)
    (= (read$0 next$0 curr_3$0)
      (read$0 (write$0 next$0 tmp_2$0 curr_3$0) curr_3$0))))

(assert (= (read$0 next$0 null$0) null$0))

(assert (= (read$0 next_9$0 null$0) null$0))

(assert (forall ((x Loc)) (not (in$0 x emptyset$0))))

(assert (or (Btwn$0 next$0 curr_2$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_258$0 next$0 curr_2$0 null$0))))

(assert (or (Btwn$0 next$0 x_1$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_262$0 next$0 x_1$0 null$0))))

(assert (or (Btwn$0 next$0 y_7$0 z_2$0 z_2$0)
    (not (lseg_struct$0 sk_?X_252$0 next$0 y_7$0 z_2$0))))

(assert (or (Btwn$0 next$0 z_2$0 curr_3$0 curr_3$0)
    (not (lseg_struct$0 sk_?X_253$0 next$0 z_2$0 curr_3$0))))

(assert (or (Btwn$0 next_9$0 z_3$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_264$0 next_9$0 z_3$0 null$0))))

(assert (= FP_14$0
  (union$0 (setminus$0 FP$0 FP_13$0)
    (union$0 (intersection$0 Alloc$0 FP_13$0) (setminus$0 Alloc$0 Alloc$0)))))

(assert (= FP_Caller_final_8$0 (union$0 FP_Caller_4$0 FP_14$0)))

(assert (= curr_3$0 null$0))

(assert (= y_7$0 y_6$0))

(assert (Frame$1 FP_13$0 Alloc$0 data$0 data$0))

(assert (= Alloc$0 (union$0 FP_14$0 Alloc$0)))

(assert (= emptyset$0 (intersection$0 sk_?X_252$0 sk_?X_253$0)))

(assert (= sk_?X_252$0 (lseg_domain$0 next$0 y_7$0 z_2$0)))

(assert (= sk_?X_254$0 (union$0 sk_?X_252$0 sk_?X_253$0)))

(assert (= sk_?X_256$0
  (union$0 (intersection$0 Alloc$0 FP_13$0) (setminus$0 Alloc$0 Alloc$0))))

(assert (lseg_struct$0 sk_?X_252$0 next$0 y_7$0 z_2$0))

(assert (lseg_struct$0 sk_?X_255$0 next$0 curr_3$0 null$0))

(assert (= emptyset$0 (intersection$0 sk_?X_261$0 sk_?X_260$0)))

(assert (= sk_?X_257$0 FP_13$0))

(assert (= sk_?X_259$0 (union$0 sk_?X_261$0 sk_?X_260$0)))

(assert (= sk_?X_261$0 (lseg_domain$0 next$0 y_6$0 z_1$0)))

(assert (lseg_struct$0 sk_?X_258$0 next$0 curr_2$0 null$0))

(assert (lseg_struct$0 sk_?X_261$0 next$0 y_6$0 z_1$0))

(assert (= sk_?X_262$0 (lseg_domain$0 next$0 x_1$0 null$0)))

(assert (lseg_struct$0 sk_?X_262$0 next$0 x_1$0 null$0))

(assert (= sk_?X_264$0 (lseg_domain$0 next_9$0 z_3$0 null$0)))

(assert (or (in$0 sk_?e_4$0 (intersection$0 sk_?X_263$0 sk_?X_264$0))
    (and
         (in$0 sk_?e_4$0
           (union$0 (intersection$0 Alloc$0 FP$0)
             (setminus$0 Alloc$0 Alloc$0)))
         (not (in$0 sk_?e_4$0 sk_?X_265$0)))
    (and (in$0 sk_?e_4$0 sk_?X_265$0)
         (not
              (in$0 sk_?e_4$0
                (union$0 (intersection$0 Alloc$0 FP$0)
                  (setminus$0 Alloc$0 Alloc$0)))))
    (not (Btwn$0 next_9$0 y_7$0 null$0 null$0))
    (not (Btwn$0 next_9$0 z_3$0 null$0 null$0))))

(assert (not (in$0 null$0 Alloc$0)))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 curr_3$0 l1 null$0)
                 (in$0 l1 (lseg_domain$0 next$0 curr_3$0 null$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 curr_3$0 l1 null$0)))
                 (not (in$0 l1 (lseg_domain$0 next$0 curr_3$0 null$0)))))))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 y_6$0 l1 z_1$0)
                 (in$0 l1 (lseg_domain$0 next$0 y_6$0 z_1$0))
                 (not (= l1 z_1$0)))
            (and (or (= l1 z_1$0) (not (Btwn$0 next$0 y_6$0 l1 z_1$0)))
                 (not (in$0 l1 (lseg_domain$0 next$0 y_6$0 z_1$0)))))))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 z_1$0 l1 curr_2$0)
                 (in$0 l1 (lseg_domain$0 next$0 z_1$0 curr_2$0))
                 (not (= l1 curr_2$0)))
            (and (or (= l1 curr_2$0) (not (Btwn$0 next$0 z_1$0 l1 curr_2$0)))
                 (not (in$0 l1 (lseg_domain$0 next$0 z_1$0 curr_2$0)))))))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next_9$0 y_7$0 l1 null$0)
                 (in$0 l1 (lseg_domain$0 next_9$0 y_7$0 null$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next_9$0 y_7$0 l1 null$0)))
                 (not (in$0 l1 (lseg_domain$0 next_9$0 y_7$0 null$0)))))))

(assert (or (Btwn$0 next$0 curr_3$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_255$0 next$0 curr_3$0 null$0))))

(assert (or (Btwn$0 next$0 y_6$0 z_1$0 z_1$0)
    (not (lseg_struct$0 sk_?X_261$0 next$0 y_6$0 z_1$0))))

(assert (or (Btwn$0 next$0 z_1$0 curr_2$0 curr_2$0)
    (not (lseg_struct$0 sk_?X_260$0 next$0 z_1$0 curr_2$0))))

(assert (or (Btwn$0 next_9$0 y_7$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_263$0 next_9$0 y_7$0 null$0))))

(assert (or
    (and (= next_9$0 (write$0 next$0 tmp_2$0 null$0)) (= tmp_2$0 z_2$0)
         (= z_3$0 (read$0 next$0 z_2$0)) (not (= z_2$0 null$0)))
    (and (= next_9$0 next$0) (= tmp_2$0 tmp$0) (= z_2$0 null$0)
         (= z_3$0 z_2$0))))

(assert (= FP_Caller_4$0 (setminus$0 FP_Caller$0 FP$0)))

(assert (= curr_2$0 x_1$0))

(assert (= y_6$0 x_1$0))

(assert (= z_1$0 x_1$0))

(assert (Frame$0 FP_13$0 Alloc$0 next$0 next$0))

(assert (= Alloc$0 (union$0 FP_Caller$0 Alloc$0)))

(assert (= emptyset$0 (intersection$0 sk_?X_254$0 sk_?X_255$0)))

(assert (= sk_?X_253$0 (lseg_domain$0 next$0 z_2$0 curr_3$0)))

(assert (= sk_?X_255$0 (lseg_domain$0 next$0 curr_3$0 null$0)))

(assert (= sk_?X_256$0 (union$0 sk_?X_254$0 sk_?X_255$0)))

(assert (lseg_struct$0 sk_?X_253$0 next$0 z_2$0 curr_3$0))

(assert (= emptyset$0 (intersection$0 sk_?X_259$0 sk_?X_258$0)))

(assert (= sk_?X_257$0 (union$0 sk_?X_259$0 sk_?X_258$0)))

(assert (= sk_?X_258$0 (lseg_domain$0 next$0 curr_2$0 null$0)))

(assert (= sk_?X_260$0 (lseg_domain$0 next$0 z_1$0 curr_2$0)))

(assert (= FP$0 (union$0 FP_13$0 FP$0)))

(assert (lseg_struct$0 sk_?X_260$0 next$0 z_1$0 curr_2$0))

(assert (= sk_?X_262$0 FP$0))

(assert (= FP_Caller$0 (union$0 FP$0 FP_Caller$0)))

(assert (= sk_?X_263$0 (lseg_domain$0 next_9$0 y_7$0 null$0)))

(assert (= sk_?X_265$0 (union$0 sk_?X_263$0 sk_?X_264$0)))

(assert (not (in$0 null$0 Alloc$0)))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 curr_2$0 l1 null$0)
                 (in$0 l1 (lseg_domain$0 next$0 curr_2$0 null$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 curr_2$0 l1 null$0)))
                 (not (in$0 l1 (lseg_domain$0 next$0 curr_2$0 null$0)))))))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 x_1$0 l1 null$0)
                 (in$0 l1 (lseg_domain$0 next$0 x_1$0 null$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 x_1$0 l1 null$0)))
                 (not (in$0 l1 (lseg_domain$0 next$0 x_1$0 null$0)))))))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 y_7$0 l1 z_2$0)
                 (in$0 l1 (lseg_domain$0 next$0 y_7$0 z_2$0))
                 (not (= l1 z_2$0)))
            (and (or (= l1 z_2$0) (not (Btwn$0 next$0 y_7$0 l1 z_2$0)))
                 (not (in$0 l1 (lseg_domain$0 next$0 y_7$0 z_2$0)))))))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 z_2$0 l1 curr_3$0)
                 (in$0 l1 (lseg_domain$0 next$0 z_2$0 curr_3$0))
                 (not (= l1 curr_3$0)))
            (and (or (= l1 curr_3$0) (not (Btwn$0 next$0 z_2$0 l1 curr_3$0)))
                 (not (in$0 l1 (lseg_domain$0 next$0 z_2$0 curr_3$0)))))))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next_9$0 z_3$0 l1 null$0)
                 (in$0 l1 (lseg_domain$0 next_9$0 z_3$0 null$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next_9$0 z_3$0 l1 null$0)))
                 (not (in$0 l1 (lseg_domain$0 next_9$0 z_3$0 null$0)))))))

(assert (forall ((?u Loc) (?v Loc) (?z Loc))
        (and
             (or (Btwn$0 (write$0 next$0 tmp_2$0 null$0) ?z ?u ?v)
                 (not
                      (or
                          (and (Btwn$0 next$0 ?z ?u ?v)
                               (or (Btwn$0 next$0 ?z ?v tmp_2$0)
                                   (and (Btwn$0 next$0 ?z ?v ?v)
                                        (not
                                             (Btwn$0 next$0 ?z tmp_2$0
                                               tmp_2$0)))))
                          (and (not (= tmp_2$0 ?v))
                               (or (Btwn$0 next$0 ?z tmp_2$0 ?v)
                                   (and (Btwn$0 next$0 ?z tmp_2$0 tmp_2$0)
                                        (not (Btwn$0 next$0 ?z ?v ?v))))
                               (Btwn$0 next$0 ?z ?u tmp_2$0)
                               (or (Btwn$0 next$0 null$0 ?v tmp_2$0)
                                   (and (Btwn$0 next$0 null$0 ?v ?v)
                                        (not
                                             (Btwn$0 next$0 null$0 tmp_2$0
                                               tmp_2$0)))))
                          (and (not (= tmp_2$0 ?v))
                               (or (Btwn$0 next$0 ?z tmp_2$0 ?v)
                                   (and (Btwn$0 next$0 ?z tmp_2$0 tmp_2$0)
                                        (not (Btwn$0 next$0 ?z ?v ?v))))
                               (Btwn$0 next$0 null$0 ?u ?v)
                               (or (Btwn$0 next$0 null$0 ?v tmp_2$0)
                                   (and (Btwn$0 next$0 null$0 ?v ?v)
                                        (not
                                             (Btwn$0 next$0 null$0 tmp_2$0
                                               tmp_2$0))))))))
             (or
                 (and (Btwn$0 next$0 ?z ?u ?v)
                      (or (Btwn$0 next$0 ?z ?v tmp_2$0)
                          (and (Btwn$0 next$0 ?z ?v ?v)
                               (not (Btwn$0 next$0 ?z tmp_2$0 tmp_2$0)))))
                 (and (not (= tmp_2$0 ?v))
                      (or (Btwn$0 next$0 ?z tmp_2$0 ?v)
                          (and (Btwn$0 next$0 ?z tmp_2$0 tmp_2$0)
                               (not (Btwn$0 next$0 ?z ?v ?v))))
                      (Btwn$0 next$0 ?z ?u tmp_2$0)
                      (or (Btwn$0 next$0 null$0 ?v tmp_2$0)
                          (and (Btwn$0 next$0 null$0 ?v ?v)
                               (not (Btwn$0 next$0 null$0 tmp_2$0 tmp_2$0)))))
                 (and (not (= tmp_2$0 ?v))
                      (or (Btwn$0 next$0 ?z tmp_2$0 ?v)
                          (and (Btwn$0 next$0 ?z tmp_2$0 tmp_2$0)
                               (not (Btwn$0 next$0 ?z ?v ?v))))
                      (Btwn$0 next$0 null$0 ?u ?v)
                      (or (Btwn$0 next$0 null$0 ?v tmp_2$0)
                          (and (Btwn$0 next$0 null$0 ?v ?v)
                               (not (Btwn$0 next$0 null$0 tmp_2$0 tmp_2$0)))))
                 (not (Btwn$0 (write$0 next$0 tmp_2$0 null$0) ?z ?u ?v))))))

(assert (forall ((?x Loc)) (Btwn$0 next_9$0 ?x ?x ?x)))

(assert (forall ((?x Loc)) (Btwn$0 next$0 ?x ?x ?x)))

(assert (forall ((?x Loc) (?y Loc)) (or (not (Btwn$0 next_9$0 ?x ?y ?x)) (= ?x ?y))))

(assert (forall ((?x Loc) (?y Loc)) (or (not (Btwn$0 next$0 ?x ?y ?x)) (= ?x ?y))))

(assert (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_9$0 ?x ?y ?y)) (not (Btwn$0 next_9$0 ?x ?z ?z))
            (Btwn$0 next_9$0 ?x ?y ?z) (Btwn$0 next_9$0 ?x ?z ?y))))

(assert (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?x ?z ?z))
            (Btwn$0 next$0 ?x ?y ?z) (Btwn$0 next$0 ?x ?z ?y))))

(assert (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_9$0 ?x ?y ?z))
            (and (Btwn$0 next_9$0 ?x ?y ?y) (Btwn$0 next_9$0 ?y ?z ?z)))))

(assert (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z))
            (and (Btwn$0 next$0 ?x ?y ?y) (Btwn$0 next$0 ?y ?z ?z)))))

(assert (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_9$0 ?x ?y ?y)) (not (Btwn$0 next_9$0 ?y ?z ?z))
            (Btwn$0 next_9$0 ?x ?z ?z))))

(assert (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?y ?z ?z))
            (Btwn$0 next$0 ?x ?z ?z))))

(assert (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_9$0 ?x ?y ?z)) (not (Btwn$0 next_9$0 ?y ?u ?z))
            (and (Btwn$0 next_9$0 ?x ?y ?u) (Btwn$0 next_9$0 ?x ?u ?z)))))

(assert (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?y ?u ?z))
            (and (Btwn$0 next$0 ?x ?y ?u) (Btwn$0 next$0 ?x ?u ?z)))))

(assert (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_9$0 ?x ?y ?z)) (not (Btwn$0 next_9$0 ?x ?u ?y))
            (and (Btwn$0 next_9$0 ?x ?u ?z) (Btwn$0 next_9$0 ?u ?y ?z)))))

(assert (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?x ?u ?y))
            (and (Btwn$0 next$0 ?x ?u ?z) (Btwn$0 next$0 ?u ?y ?z)))))

(check-sat)
(exit)
