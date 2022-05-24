(set-info :smt-lib-version 2.6)
(set-logic UF)
(set-info :source |
  GRASShopper benchmarks.
  Authors: Ruzica Piskac, Thomas Wies, and Damien Zufferey
  URL: http://cs.nyu.edu/wies/software/grasshopper
  See also: GRASShopper - Complete Heap Verification with Mixed Specifications. In TACAS 2014, pages 124-139.

  If this benchmark is satisfiable, GRASShopper reports the following error message:
  tests/spl/dl/dl_filter.spl:41:1-2:A postcondition of procedure dl_filter might not hold at this return point
  tests/spl/dl/dl_filter.spl:13:12-35:Related location: This is the postcondition that might not hold
  |)
(set-info :category "crafted")
(set-info :status unsat)

(declare-sort Loc 0)
(declare-sort SetLoc 0)
(declare-sort FldBool 0)
(declare-sort FldLoc 0)
(declare-fun null$0 () Loc)
(declare-fun read$0 (FldLoc Loc) Loc)
(declare-fun ep$0 (FldLoc SetLoc Loc) Loc)
(declare-fun emptyset$0 () SetLoc)
(declare-fun setenum$0 (Loc) SetLoc)
(declare-fun union$0 (SetLoc SetLoc) SetLoc)
(declare-fun intersection$0 (SetLoc SetLoc) SetLoc)
(declare-fun setminus$0 (SetLoc SetLoc) SetLoc)
(declare-fun Btwn$0 (FldLoc Loc Loc Loc) Bool)
(declare-fun Frame$0 (SetLoc SetLoc FldLoc FldLoc) Bool)
(declare-fun in$0 (Loc SetLoc) Bool)
(declare-fun Alloc$0 () SetLoc)
(declare-fun Alloc_1$0 () SetLoc)
(declare-fun Axiom_3$0 () Bool)
(declare-fun Axiom_4$0 () Bool)
(declare-fun Axiom_5$0 () Bool)
(declare-fun Axiom_6$0 () Bool)
(declare-fun Axiom_7$0 () Bool)
(declare-fun Axiom_8$0 () Bool)
(declare-fun Axiom_9$0 () Bool)
(declare-fun Axiom_10$0 () Bool)
(declare-fun Axiom_11$0 () Bool)
(declare-fun Axiom_12$0 () Bool)
(declare-fun FP$0 () SetLoc)
(declare-fun FP_1$0 () SetLoc)
(declare-fun FP_2$0 () SetLoc)
(declare-fun FP_Caller$0 () SetLoc)
(declare-fun FP_Caller_1$0 () SetLoc)
(declare-fun FP_Caller_final_1$0 () SetLoc)
(declare-fun a$0 () Loc)
(declare-fun b$0 () Loc)
(declare-fun c_1$0 () Loc)
(declare-fun c_2$0 () Loc)
(declare-fun curr_2$0 () Loc)
(declare-fun curr_3$0 () Loc)
(declare-fun d_1$0 () Loc)
(declare-fun d_2$0 () Loc)
(declare-fun dlseg_domain$0 (FldLoc FldLoc Loc Loc Loc Loc) SetLoc)
(declare-fun dlseg_struct$0 (SetLoc FldLoc FldLoc Loc Loc Loc Loc) Bool)
(declare-fun next$0 () FldLoc)
(declare-fun next_1$0 () FldLoc)
(declare-fun prev$0 () FldLoc)
(declare-fun prev_1$0 () FldLoc)
(declare-fun prv_2$0 () Loc)
(declare-fun prv_3$0 () Loc)
(declare-fun sk_?X_4$0 () SetLoc)
(declare-fun sk_?X_5$0 () SetLoc)
(declare-fun sk_?X_6$0 () SetLoc)
(declare-fun sk_?X_7$0 () SetLoc)
(declare-fun sk_?X_8$0 () SetLoc)
(declare-fun sk_?X_9$0 () SetLoc)
(declare-fun sk_?X_10$0 () SetLoc)
(declare-fun sk_?X_11$0 () SetLoc)
(declare-fun sk_l1_1$0 () Loc)
(declare-fun sk_l2_1$0 () Loc)
(declare-fun t$0 () Loc)
(declare-fun t_1$0 () Loc)
(declare-fun t_2$0 () Loc)
(declare-fun t_3$0 () Loc)
(declare-fun t_4$0 () Loc)
(declare-fun t_5$0 () Loc)
(declare-fun t_6$0 () Loc)
(declare-fun t_7$0 () Loc)
(declare-fun t_8$0 () Loc)
(declare-fun t_9$0 () Loc)
(declare-fun t_10$0 () Loc)
(declare-fun t_11$0 () Loc)
(declare-fun t_12$0 () Loc)
(declare-fun t_13$0 () Loc)
(declare-fun t_14$0 () Loc)
(declare-fun t_15$0 () Loc)
(declare-fun t_16$0 () Loc)
(declare-fun t_17$0 () Loc)
(declare-fun t_18$0 () Loc)
(declare-fun t_19$0 () Loc)
(declare-fun t_20$0 () Loc)
(declare-fun t_21$0 () Loc)
(declare-fun t_22$0 () Loc)
(declare-fun t_23$0 () Loc)
(declare-fun t_24$0 () Loc)
(declare-fun t_25$0 () Loc)
(declare-fun t_26$0 () Loc)
(declare-fun t_27$0 () Loc)
(declare-fun t_28$0 () Loc)
(declare-fun t_29$0 () Loc)
(declare-fun t_30$0 () Loc)
(declare-fun t_31$0 () Loc)
(declare-fun t_32$0 () Loc)
(declare-fun t_33$0 () Loc)
(declare-fun t_34$0 () Loc)
(declare-fun t_35$0 () Loc)
(declare-fun t_36$0 () Loc)
(declare-fun t_37$0 () Loc)

(assert (= (ep$0 prev$0 FP_1$0 sk_l2_1$0) t_37$0))

(assert (= (ep$0 prev$0 FP_1$0 sk_l1_1$0) t_36$0))

(assert (= (ep$0 prev$0 FP_1$0 prv_3$0) t_35$0))

(assert (= (ep$0 prev$0 FP_1$0 prv_2$0) t_34$0))

(assert (= (ep$0 prev$0 FP_1$0 d_2$0) t_33$0))

(assert (= (ep$0 prev$0 FP_1$0 d_1$0) t_32$0))

(assert (= (ep$0 prev$0 FP_1$0 curr_3$0) t_31$0))

(assert (= (ep$0 prev$0 FP_1$0 curr_2$0) t_30$0))

(assert (= (ep$0 prev$0 FP_1$0 c_2$0) t_29$0))

(assert (= (ep$0 prev$0 FP_1$0 c_1$0) t_28$0))

(assert (= (ep$0 prev$0 FP_1$0 b$0) t_27$0))

(assert (= (ep$0 prev$0 FP_1$0 a$0) t_26$0))

(assert (= (ep$0 prev$0 FP_1$0 null$0) t_25$0))

(assert (= (ep$0 next$0 FP_1$0 sk_l2_1$0) t_24$0))

(assert (= (ep$0 next$0 FP_1$0 sk_l1_1$0) t_23$0))

(assert (= (ep$0 next$0 FP_1$0 prv_3$0) t_22$0))

(assert (= (ep$0 next$0 FP_1$0 prv_2$0) t_21$0))

(assert (= (ep$0 next$0 FP_1$0 d_2$0) t_20$0))

(assert (= (ep$0 next$0 FP_1$0 d_1$0) t_19$0))

(assert (= (ep$0 next$0 FP_1$0 curr_3$0) t_18$0))

(assert (= (ep$0 next$0 FP_1$0 curr_2$0) t_17$0))

(assert (= (ep$0 next$0 FP_1$0 c_2$0) t_16$0))

(assert (= (ep$0 next$0 FP_1$0 c_1$0) t_15$0))

(assert (= (ep$0 next$0 FP_1$0 b$0) t_14$0))

(assert (= (ep$0 next$0 FP_1$0 a$0) t_13$0))

(assert (= (ep$0 next$0 FP_1$0 null$0) t_12$0))

(assert (= (read$0 prev_1$0 curr_2$0) t_11$0))

(assert (= (read$0 prev_1$0 c_1$0) t_10$0))

(assert (= (read$0 prev_1$0 a$0) t_9$0))

(assert (= (read$0 prev$0 sk_l2_1$0) t_8$0))

(assert (= (read$0 prev$0 curr_3$0) t_7$0))

(assert (= (read$0 prev$0 c_2$0) t_6$0))

(assert (= (read$0 next_1$0 prv_2$0) t_5$0))

(assert (= (read$0 next_1$0 d_1$0) t_4$0))

(assert (= (read$0 next_1$0 b$0) t_3$0))

(assert (= (read$0 next$0 sk_l1_1$0) t_2$0))

(assert (= (read$0 next$0 prv_3$0) t_1$0))

(assert (= (read$0 next$0 d_2$0) t$0))

(assert (forall ((?f FldLoc)) (= (read$0 ?f null$0) null$0)))

(assert (forall ((x Loc) (y Loc))
        (or (and (= x y) (in$0 x (setenum$0 y)))
            (and (not (= x y)) (not (in$0 x (setenum$0 y)))))))

(assert (forall ((X SetLoc) (Y SetLoc) (x Loc))
        (or (and (in$0 x X) (in$0 x (setminus$0 X Y)) (not (in$0 x Y)))
            (and (or (in$0 x Y) (not (in$0 x X)))
                 (not (in$0 x (setminus$0 X Y)))))))

(assert (forall ((X SetLoc) (Y SetLoc) (x Loc))
        (or (and (in$0 x X) (in$0 x Y) (in$0 x (intersection$0 X Y)))
            (and (or (not (in$0 x X)) (not (in$0 x Y)))
                 (not (in$0 x (intersection$0 X Y)))))))

(assert (forall ((X SetLoc) (Y SetLoc) (x Loc))
        (or (and (in$0 x (union$0 X Y)) (or (in$0 x X) (in$0 x Y)))
            (and (not (in$0 x X)) (not (in$0 x Y))
                 (not (in$0 x (union$0 X Y)))))))

(assert (forall ((x Loc)) (not (in$0 x emptyset$0))))

(assert (or
    (and (Btwn$0 next$0 a$0 null$0 null$0)
         (or (and (= null$0 b$0) (= a$0 null$0))
             (and (= (read$0 next$0 b$0) null$0)
                  (= (read$0 prev$0 a$0) null$0) (in$0 b$0 sk_?X_10$0)))
         Axiom_3$0)
    (not (dlseg_struct$0 sk_?X_10$0 next$0 prev$0 a$0 null$0 null$0 b$0))))

(assert (or (not Axiom_4$0)
    (forall ((l1 Loc) (l2 Loc))
            (or (= (read$0 prev$0 l2) l1) (not (= (read$0 next$0 l1) l2))
                (not (in$0 l1 sk_?X_9$0)) (not (in$0 l2 sk_?X_9$0))))))

(assert (or
    (and (Btwn$0 next$0 curr_2$0 null$0 null$0)
         (or
             (and (= (read$0 next$0 d_1$0) null$0)
                  (= (read$0 prev$0 curr_2$0) prv_2$0)
                  (in$0 d_1$0 sk_?X_8$0))
             (and (= curr_2$0 null$0) (= prv_2$0 d_1$0)))
         Axiom_5$0)
    (not
         (dlseg_struct$0 sk_?X_8$0 next$0 prev$0 curr_2$0 prv_2$0 null$0
           d_1$0))))

(assert (or (not Axiom_6$0)
    (forall ((l1 Loc) (l2 Loc))
            (or (= (read$0 prev_1$0 l2) l1) (not (= (read$0 next_1$0 l1) l2))
                (not (in$0 l1 sk_?X_11$0)) (not (in$0 l2 sk_?X_11$0))))))

(assert (or
    (and (Btwn$0 next_1$0 c_2$0 curr_3$0 curr_3$0)
         (or (and (= null$0 prv_3$0) (= c_2$0 curr_3$0))
             (and (= (read$0 next_1$0 prv_3$0) curr_3$0)
                  (= (read$0 prev_1$0 c_2$0) null$0)
                  (in$0 prv_3$0 sk_?X_4$0)))
         Axiom_7$0)
    (not
         (dlseg_struct$0 sk_?X_4$0 next_1$0 prev_1$0 c_2$0 null$0 curr_3$0
           prv_3$0))))

(assert (or (not Axiom_8$0)
    (forall ((l1 Loc) (l2 Loc))
            (or (= (read$0 prev_1$0 l2) l1) (not (= (read$0 next_1$0 l1) l2))
                (not (in$0 l1 sk_?X_5$0)) (not (in$0 l2 sk_?X_5$0))))))

(assert (= FP_2$0
  (union$0 (setminus$0 FP$0 FP_1$0)
    (union$0 (intersection$0 Alloc_1$0 FP_1$0)
      (setminus$0 Alloc_1$0 Alloc$0)))))

(assert (= FP_Caller_final_1$0 (union$0 FP_Caller_1$0 FP_2$0)))

(assert (= curr_2$0 c_1$0))

(assert (= d_1$0 b$0))

(assert (Frame$0 FP_1$0 Alloc$0 next$0 next_1$0))

(assert (= Alloc_1$0 (union$0 FP_2$0 Alloc_1$0)))

(assert (= emptyset$0 (intersection$0 sk_?X_4$0 sk_?X_5$0)))

(assert (= sk_?X_5$0
  (dlseg_domain$0 next_1$0 prev_1$0 curr_3$0 prv_3$0 null$0 d_2$0)))

(assert (= sk_?X_6$0 (union$0 sk_?X_4$0 sk_?X_5$0)))

(assert (dlseg_struct$0 sk_?X_5$0 next_1$0 prev_1$0 curr_3$0 prv_3$0 null$0 d_2$0))

(assert (= sk_?X_7$0 (union$0 sk_?X_9$0 sk_?X_8$0)))

(assert (= sk_?X_8$0 (dlseg_domain$0 next$0 prev$0 curr_2$0 prv_2$0 null$0 d_1$0)))

(assert (= FP$0 (union$0 FP_1$0 FP$0)))

(assert (dlseg_struct$0 sk_?X_9$0 next$0 prev$0 c_1$0 null$0 curr_2$0 prv_2$0))

(assert (= sk_?X_10$0 (dlseg_domain$0 next$0 prev$0 a$0 null$0 null$0 b$0)))

(assert (dlseg_struct$0 sk_?X_10$0 next$0 prev$0 a$0 null$0 null$0 b$0))

(assert (or
    (and (= (read$0 next_1$0 sk_l1_1$0) sk_l2_1$0)
         (in$0 sk_l1_1$0 sk_?X_11$0) (in$0 sk_l2_1$0 sk_?X_11$0)
         (not (= (read$0 prev_1$0 sk_l2_1$0) sk_l1_1$0)))
    (and
         (in$0 sk_l2_1$0
           (dlseg_domain$0 next_1$0 prev_1$0 c_2$0 null$0 null$0 d_2$0))
         (not (in$0 sk_l2_1$0 sk_?X_11$0)))
    (and (in$0 sk_l2_1$0 sk_?X_11$0)
         (not
              (in$0 sk_l2_1$0
                (dlseg_domain$0 next_1$0 prev_1$0 c_2$0 null$0 null$0 d_2$0))))
    (and (or (not (= null$0 d_2$0)) (not (= c_2$0 null$0)))
         (or (not (= (read$0 next_1$0 d_2$0) null$0))
             (not (= (read$0 prev_1$0 c_2$0) null$0))
             (not (in$0 d_2$0 sk_?X_11$0))))
    (not (Btwn$0 next_1$0 c_2$0 null$0 null$0))))

(assert (not (in$0 null$0 Alloc_1$0)))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 c_1$0 l1 curr_2$0)
                 (in$0 l1
                   (dlseg_domain$0 next$0 prev$0 c_1$0 null$0 curr_2$0
                     prv_2$0))
                 (not (= l1 curr_2$0)))
            (and (or (= l1 curr_2$0) (not (Btwn$0 next$0 c_1$0 l1 curr_2$0)))
                 (not
                      (in$0 l1
                        (dlseg_domain$0 next$0 prev$0 c_1$0 null$0 curr_2$0
                          prv_2$0)))))))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next_1$0 c_2$0 l1 null$0)
                 (in$0 l1
                   (dlseg_domain$0 next_1$0 prev_1$0 c_2$0 null$0 null$0
                     d_2$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next_1$0 c_2$0 l1 null$0)))
                 (not
                      (in$0 l1
                        (dlseg_domain$0 next_1$0 prev_1$0 c_2$0 null$0 null$0
                          d_2$0)))))))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next_1$0 curr_3$0 l1 null$0)
                 (in$0 l1
                   (dlseg_domain$0 next_1$0 prev_1$0 curr_3$0 prv_3$0 null$0
                     d_2$0))
                 (not (= l1 null$0)))
            (and
                 (or (= l1 null$0)
                     (not (Btwn$0 next_1$0 curr_3$0 l1 null$0)))
                 (not
                      (in$0 l1
                        (dlseg_domain$0 next_1$0 prev_1$0 curr_3$0 prv_3$0
                          null$0 d_2$0)))))))

(assert (forall ((?X SetLoc) (?f FldLoc) (?x Loc))
        (or (in$0 (ep$0 ?f ?X ?x) ?X) (= ?x (ep$0 ?f ?X ?x)))))

(assert (forall ((?X SetLoc) (?f FldLoc) (?x Loc))
        (Btwn$0 ?f ?x (ep$0 ?f ?X ?x) (ep$0 ?f ?X ?x))))

(assert (or (not Axiom_9$0)
    (forall ((?x Loc))
            (or (= (read$0 prev$0 ?x) (read$0 prev_1$0 ?x))
                (not (in$0 ?x (setminus$0 Alloc$0 FP_1$0)))))))

(assert (or (and Axiom_12$0 Axiom_11$0 Axiom_10$0)
    (not (Frame$0 FP_1$0 Alloc$0 next$0 next_1$0))))

(assert (or (not Axiom_3$0)
    (forall ((l1 Loc) (l2 Loc))
            (or (= (read$0 prev$0 l2) l1) (not (= (read$0 next$0 l1) l2))
                (not (in$0 l1 sk_?X_10$0)) (not (in$0 l2 sk_?X_10$0))))))

(assert (or
    (and (Btwn$0 next$0 c_1$0 curr_2$0 curr_2$0)
         (or (and (= null$0 prv_2$0) (= c_1$0 curr_2$0))
             (and (= (read$0 next$0 prv_2$0) curr_2$0)
                  (= (read$0 prev$0 c_1$0) null$0) (in$0 prv_2$0 sk_?X_9$0)))
         Axiom_4$0)
    (not
         (dlseg_struct$0 sk_?X_9$0 next$0 prev$0 c_1$0 null$0 curr_2$0
           prv_2$0))))

(assert (or (not Axiom_5$0)
    (forall ((l1 Loc) (l2 Loc))
            (or (= (read$0 prev$0 l2) l1) (not (= (read$0 next$0 l1) l2))
                (not (in$0 l1 sk_?X_8$0)) (not (in$0 l2 sk_?X_8$0))))))

(assert (or
    (and (Btwn$0 next_1$0 c_2$0 null$0 null$0)
         (or (and (= null$0 d_2$0) (= c_2$0 null$0))
             (and (= (read$0 next_1$0 d_2$0) null$0)
                  (= (read$0 prev_1$0 c_2$0) null$0) (in$0 d_2$0 sk_?X_11$0)))
         Axiom_6$0)
    (not
         (dlseg_struct$0 sk_?X_11$0 next_1$0 prev_1$0 c_2$0 null$0 null$0
           d_2$0))))

(assert (or (not Axiom_7$0)
    (forall ((l1 Loc) (l2 Loc))
            (or (= (read$0 prev_1$0 l2) l1) (not (= (read$0 next_1$0 l1) l2))
                (not (in$0 l1 sk_?X_4$0)) (not (in$0 l2 sk_?X_4$0))))))

(assert (or
    (and (Btwn$0 next_1$0 curr_3$0 null$0 null$0)
         (or
             (and (= (read$0 next_1$0 d_2$0) null$0)
                  (= (read$0 prev_1$0 curr_3$0) prv_3$0)
                  (in$0 d_2$0 sk_?X_5$0))
             (and (= curr_3$0 null$0) (= prv_3$0 d_2$0)))
         Axiom_8$0)
    (not
         (dlseg_struct$0 sk_?X_5$0 next_1$0 prev_1$0 curr_3$0 prv_3$0 null$0
           d_2$0))))

(assert (= FP_Caller_1$0 (setminus$0 FP_Caller$0 FP$0)))

(assert (= c_1$0 a$0))

(assert (= curr_3$0 null$0))

(assert (= prv_2$0 null$0))

(assert (Frame$0 FP_1$0 Alloc$0 prev$0 prev_1$0))

(assert (= Alloc$0 (union$0 FP_Caller$0 Alloc$0)))

(assert (= sk_?X_4$0
  (dlseg_domain$0 next_1$0 prev_1$0 c_2$0 null$0 curr_3$0 prv_3$0)))

(assert (= sk_?X_6$0
  (union$0 (intersection$0 Alloc_1$0 FP_1$0) (setminus$0 Alloc_1$0 Alloc$0))))

(assert (dlseg_struct$0 sk_?X_4$0 next_1$0 prev_1$0 c_2$0 null$0 curr_3$0 prv_3$0))

(assert (= emptyset$0 (intersection$0 sk_?X_9$0 sk_?X_8$0)))

(assert (= sk_?X_7$0 FP_1$0))

(assert (= sk_?X_9$0 (dlseg_domain$0 next$0 prev$0 c_1$0 null$0 curr_2$0 prv_2$0)))

(assert (dlseg_struct$0 sk_?X_8$0 next$0 prev$0 curr_2$0 prv_2$0 null$0 d_1$0))

(assert (= sk_?X_10$0 FP$0))

(assert (= FP_Caller$0 (union$0 FP$0 FP_Caller$0)))

(assert (= sk_?X_11$0
  (union$0 (intersection$0 Alloc_1$0 FP$0) (setminus$0 Alloc_1$0 Alloc$0))))

(assert (not (in$0 null$0 Alloc$0)))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 a$0 l1 null$0)
                 (in$0 l1
                   (dlseg_domain$0 next$0 prev$0 a$0 null$0 null$0 b$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 a$0 l1 null$0)))
                 (not
                      (in$0 l1
                        (dlseg_domain$0 next$0 prev$0 a$0 null$0 null$0 b$0)))))))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 curr_2$0 l1 null$0)
                 (in$0 l1
                   (dlseg_domain$0 next$0 prev$0 curr_2$0 prv_2$0 null$0
                     d_1$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 curr_2$0 l1 null$0)))
                 (not
                      (in$0 l1
                        (dlseg_domain$0 next$0 prev$0 curr_2$0 prv_2$0 null$0
                          d_1$0)))))))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next_1$0 c_2$0 l1 curr_3$0)
                 (in$0 l1
                   (dlseg_domain$0 next_1$0 prev_1$0 c_2$0 null$0 curr_3$0
                     prv_3$0))
                 (not (= l1 curr_3$0)))
            (and
                 (or (= l1 curr_3$0)
                     (not (Btwn$0 next_1$0 c_2$0 l1 curr_3$0)))
                 (not
                      (in$0 l1
                        (dlseg_domain$0 next_1$0 prev_1$0 c_2$0 null$0
                          curr_3$0 prv_3$0)))))))

(assert (forall ((?X SetLoc) (?f FldLoc) (?x Loc) (?y Loc))
        (or (Btwn$0 ?f ?x (ep$0 ?f ?X ?x) ?y) (not (Btwn$0 ?f ?x ?y ?y))
            (not (in$0 ?y ?X)))))

(assert (forall ((?X SetLoc) (?f FldLoc) (?x Loc) (?y Loc))
        (or (not (Btwn$0 ?f ?x ?y ?y)) (not (in$0 ?y ?X))
            (in$0 (ep$0 ?f ?X ?x) ?X))))

(assert (or (not (Frame$0 FP_1$0 Alloc$0 prev$0 prev_1$0)) Axiom_9$0))

(assert (or (not Axiom_10$0)
    (forall ((?x Loc) (?y Loc) (?z Loc))
            (or (in$0 ?x FP_1$0)
                (and (Btwn$0 next$0 ?x ?z ?y) (Btwn$0 next_1$0 ?x ?z ?y))
                (and (not (Btwn$0 next$0 ?x ?z ?y))
                     (not (Btwn$0 next_1$0 ?x ?z ?y)))
                (not (= ?x (ep$0 next$0 FP_1$0 ?x)))))))

(assert (or (not Axiom_11$0)
    (forall ((?x Loc) (?y Loc) (?z Loc))
            (or (and (Btwn$0 next$0 ?x ?z ?y) (Btwn$0 next_1$0 ?x ?z ?y))
                (and (not (Btwn$0 next$0 ?x ?z ?y))
                     (not (Btwn$0 next_1$0 ?x ?z ?y)))
                (not
                     (or (Btwn$0 next$0 ?x ?y (ep$0 next$0 FP_1$0 ?x))
                         (and (Btwn$0 next$0 ?x ?y ?y)
                              (not
                                   (Btwn$0 next$0 ?x (ep$0 next$0 FP_1$0 ?x)
                                     (ep$0 next$0 FP_1$0 ?x))))))))))

(assert (or (not Axiom_12$0)
    (forall ((?x Loc))
            (or (= (read$0 next$0 ?x) (read$0 next_1$0 ?x))
                (not (in$0 ?x (setminus$0 Alloc$0 FP_1$0)))))))

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
            (Btwn$0 ?f ?x (read$0 ?f ?x) ?y))))

(assert (forall ((?f FldLoc) (?x Loc) (?y Loc))
        (or (not (= (read$0 ?f ?x) ?x)) (not (Btwn$0 ?f ?x ?y ?y)) (= ?x ?y))))

(assert (forall ((?f FldLoc) (?x Loc)) (Btwn$0 ?f ?x (read$0 ?f ?x) (read$0 ?f ?x))))

(assert (forall ((?f FldLoc) (?x Loc)) (Btwn$0 ?f ?x ?x ?x)))

(check-sat)
(exit)
