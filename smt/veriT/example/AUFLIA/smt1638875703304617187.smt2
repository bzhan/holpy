(set-info :smt-lib-version 2.6)
(set-logic AUFLIA)
(set-info :source |Generator: Rodin SMT Plug-in|)
(set-info :license "https://creativecommons.org/licenses/by-nc/4.0/")
(set-info :category "industrial")
(set-info :status unsat)

(declare-sort PZ 0)
(declare-fun MS (Int PZ) Bool)
(declare-fun i (Int Int PZ) Bool)
(declare-fun n (Int Int) Bool)
(declare-fun N () PZ)
(declare-fun x () Int)

; Elementary Sets axiom (Singleton part)
(assert (forall ((x35 Int)) 
            (exists ((X PZ)) 
                (and 
                    (MS x35 X) 
                    (forall ((y0 Int)) 
                        (=> 
                            (MS y0 X) 
                            (= y0 x35)))))))
(assert (! (and 
               (forall ((x0 Int) (x1 Int)) 
                   (=> 
                       (n x0 x1) 
                       (and 
                           (MS x0 N) 
                           (MS x1 N)))) 
               (forall ((x2 Int) (x3 Int) (x4 Int)) 
                   (=> 
                       (and 
                           (n x2 x3) 
                           (n x2 x4)) 
                       (= x3 x4))) 
               (forall ((x5 Int)) 
                   (=> 
                       (MS x5 N) 
                       (exists ((x6 Int)) 
                           (n x5 x6)))) 
               (forall ((x7 Int)) 
                   (=> 
                       (MS x7 N) 
                       (exists ((x8 Int)) 
                           (n x8 x7)))) 
               (forall ((x9 Int) (x10 Int) (x11 Int)) 
                   (=> 
                       (and 
                           (n x10 x9) 
                           (n x11 x9)) 
                       (= x10 x11))))
         :named hyp1))
(assert (! (and 
               (forall ((x12 Int) (x13 Int) (x14 PZ)) 
                   (=> 
                       (i x12 x13 x14) 
                       (and 
                           (MS x12 N) 
                           (MS x13 N) 
                           (forall ((x15 Int)) 
                               (=> 
                                   (MS x15 x14) 
                                   (MS x15 N)))))) 
               (forall ((x16 Int) (x17 Int) (x18 PZ) (x19 PZ)) 
                   (=> 
                       (and 
                           (i x16 x17 x18) 
                           (i x16 x17 x19)) 
                       (forall ((x20 Int)) 
                           (= 
                               (MS x20 x18) 
                               (MS x20 x19))))) 
               (forall ((x21 Int) (x22 Int)) 
                   (=> 
                       (and 
                           (MS x21 N) 
                           (MS x22 N)) 
                       (exists ((x23 PZ)) 
                           (i x21 x22 x23)))))
         :named hyp2))
(assert (! (forall ((x24 Int)) 
               (=> 
                   (MS x24 N) 
                   (exists ((x25 PZ)) 
                       (and 
                           (forall ((x26 Int)) 
                               (= 
                                   (MS x26 x25) 
                                   (= x26 x24))) 
                           (i x24 x24 x25)))))
         :named hyp3))
(assert (! (forall ((x27 Int) (y Int)) 
               (=> 
                   (and 
                       (MS x27 N) 
                       (MS y N) 
                       (not 
                           (= x27 y))) 
                   (exists ((x28 PZ)) 
                       (and 
                           (forall ((x29 Int)) 
                               (= 
                                   (MS x29 x28) 
                                   (or 
                                       (= x29 y) 
                                       (exists ((x30 PZ)) 
                                           (and 
                                               (exists ((x31 Int)) 
                                                   (and 
                                                       (n x31 y) 
                                                       (i x27 x31 x30))) 
                                               (MS x29 x30)))))) 
                           (i x27 y x28)))))
         :named hyp4))
(assert (! (MS x N)
         :named hyp5))
(assert (! (not 
               (forall ((x32 Int) (x33 Int) (x34 Int)) 
                   (=> 
                       (and 
                           (n x33 x32) 
                           (n x34 x32)) 
                       (= x33 x34))))
         :named goal))
(check-sat)
(exit)

