(set-info :smt-lib-version 2.6)
(set-logic AUFLIA)
(set-info :source |Generator: Rodin SMT Plug-in|)
(set-info :license "https://creativecommons.org/licenses/by-nc/4.0/")
(set-info :category "industrial")
(set-info :status unsat)

(declare-sort N 0)
(declare-sort PN 0)
(declare-sort PNN 0)
(declare-sort PNZ 0)
(declare-fun MS (N N PNN) Bool)
(declare-fun MS0 (N PN) Bool)
(declare-fun MS1 (N Int PNZ) Bool)
(declare-fun M () PNN)
(declare-fun bm () PN)
(declare-fun c () PNN)
(declare-fun g () PNN)
(declare-fun n () PN)
(declare-fun x () N)
(declare-fun x0 () N)
(declare-fun y () N)
(declare-fun y0 () N)

; Elementary Sets axiom (Singleton part)
(assert (forall ((x55 N) (x56 N)) 
            (exists ((X PNN)) 
                (and 
                    (MS x55 x56 X) 
                    (forall ((y3 N) (y4 N)) 
                        (=> 
                            (MS y3 y4 X) 
                            (and 
                                (= y3 x55) 
                                (= y4 x56))))))))
; Elementary Sets axiom (Singleton part)
(assert (forall ((x57 N) (x58 Int)) 
            (exists ((X0 PNZ)) 
                (and 
                    (MS1 x57 x58 X0) 
                    (forall ((y5 N) (y6 Int)) 
                        (=> 
                            (MS1 y5 y6 X0) 
                            (and 
                                (= y5 x57) 
                                (= y6 x58))))))))
; Elementary Sets axiom (Singleton part)
(assert (forall ((x59 N)) 
            (exists ((X1 PN)) 
                (and 
                    (MS0 x59 X1) 
                    (forall ((y7 N)) 
                        (=> 
                            (MS0 y7 X1) 
                            (= y7 x59)))))))
(assert (! (forall ((x1 N) (y1 N)) 
               (=> 
                   (MS x1 y1 M) 
                   (forall ((x2 N)) 
                       (= 
                           (and 
                               (exists ((x3 N)) 
                                   (and 
                                       (= x3 x1) 
                                       (MS x3 x2 g))) 
                               (MS0 x2 n)) 
                           (= x2 y1)))))
         :named hyp1))
(assert (! (MS x y M)
         :named hyp2))
(assert (! (not 
               (MS0 y bm))
         :named hyp3))
(assert (! (and 
               (MS x0 y0 M) 
               (not 
                   (and 
                       (= x0 x) 
                       (= y0 y))))
         :named hyp4))
(assert (! (forall ((x4 N) (x5 N)) 
               (= 
                   (MS x4 x5 g) 
                   (MS x5 x4 g)))
         :named hyp5))
(assert (! (forall ((a Int)) 
               (exists ((b Int) (f PNZ)) 
                   (and 
                       (forall ((x6 N) (x7 Int)) 
                           (=> 
                               (MS1 x6 x7 f) 
                               (and 
                                   (<= a x7) 
                                   (<= x7 b)))) 
                       (forall ((x8 N) (x9 Int) (x10 Int)) 
                           (=> 
                               (and 
                                   (MS1 x8 x9 f) 
                                   (MS1 x8 x10 f)) 
                               (= x9 x10))) 
                       (forall ((x11 N)) 
                           (exists ((x12 Int)) 
                               (MS1 x11 x12 f))) 
                       (forall ((x13 Int) (x14 N) (x15 N)) 
                           (=> 
                               (and 
                                   (MS1 x14 x13 f) 
                                   (MS1 x15 x13 f)) 
                               (= x14 x15))))))
         :named hyp6))
(assert (! (forall ((x16 N) (x17 N)) 
               (=> 
                   (MS x16 x17 M) 
                   (MS x16 x17 g)))
         :named hyp7))
(assert (! (forall ((x18 N) (x19 N)) 
               (=> 
                   (MS x18 x19 c) 
                   (MS x18 x19 g)))
         :named hyp8))
(assert (! (forall ((x20 N)) 
               (= 
                   (MS0 x20 bm) 
                   (or 
                       (exists ((x21 N)) 
                           (MS x20 x21 M)) 
                       (exists ((x22 N)) 
                           (MS x20 x22 c)))))
         :named hyp9))
(assert (! (forall ((x23 N)) 
               (not 
                   (and 
                       (exists ((x24 N)) 
                           (MS x23 x24 M)) 
                       (exists ((x25 N)) 
                           (MS x23 x25 c)))))
         :named hyp10))
(assert (! (forall ((x26 N) (x27 N) (x28 N)) 
               (=> 
                   (and 
                       (MS x26 x27 M) 
                       (MS x26 x28 M)) 
                   (= x27 x28)))
         :named hyp11))
(assert (! (forall ((x29 N) (x30 N) (x31 N)) 
               (=> 
                   (and 
                       (MS x29 x30 c) 
                       (MS x29 x31 c)) 
                   (= x30 x31)))
         :named hyp12))
(assert (! (forall ((x32 N) (y2 N)) 
               (=> 
                   (MS x32 y2 M) 
                   (MS0 x32 n)))
         :named hyp13))
(assert (! (forall ((x33 N) (x34 N)) 
               (not 
                   (and 
                       (= x33 x34) 
                       (MS x33 x34 g))))
         :named hyp14))
(assert (! (forall ((S PN)) 
               (=> 
                   (and 
                       (not 
                           (forall ((x35 N)) 
                               (not 
                                   (MS0 x35 S)))) 
                       (forall ((x36 N)) 
                           (=> 
                               (exists ((x37 N)) 
                                   (and 
                                       (MS0 x37 S) 
                                       (MS x37 x36 g))) 
                               (MS0 x36 S)))) 
                   (forall ((x38 N)) 
                       (MS0 x38 S))))
         :named hyp15))
(assert (! (forall ((h PNN) (S0 PN)) 
               (=> 
                   (and 
                       (forall ((x39 N) (x40 N)) 
                           (=> 
                               (MS x39 x40 h) 
                               (MS x39 x40 g))) 
                       (forall ((x41 N) (x42 N)) 
                           (=> 
                               (MS x42 x41 h) 
                               (MS x41 x42 g))) 
                       (forall ((x43 N) (x44 N)) 
                           (not 
                               (and 
                                   (MS x43 x44 h) 
                                   (MS x44 x43 h)))) 
                       (forall ((x45 N)) 
                           (=> 
                               (MS0 x45 S0) 
                               (exists ((x46 N)) 
                                   (and 
                                       (MS0 x46 S0) 
                                       (MS x46 x45 h)))))) 
                   (forall ((x47 N)) 
                       (not 
                           (MS0 x47 S0)))))
         :named hyp16))
(assert (! (forall ((S1 PN)) 
               (=> 
                   (and 
                       (forall ((x48 N)) 
                           (=> 
                               (MS0 x48 S1) 
                               (MS0 x48 n))) 
                       (not 
                           (forall ((x49 N)) 
                               (not 
                                   (MS0 x49 S1)))) 
                       (forall ((x50 N)) 
                           (=> 
                               (exists ((x51 N)) 
                                   (and 
                                       (MS0 x51 S1) 
                                       (MS x51 x50 g) 
                                       (MS0 x51 n) 
                                       (MS0 x50 n))) 
                               (MS0 x50 S1)))) 
                   (forall ((x52 N)) 
                       (=> 
                           (MS0 x52 n) 
                           (MS0 x52 S1)))))
         :named hyp17))
(assert (! (not 
               (forall ((x53 N)) 
                   (= 
                       (and 
                           (exists ((x54 N)) 
                               (and 
                                   (= x54 x0) 
                                   (MS x54 x53 g))) 
                           (MS0 x53 n) 
                           (not 
                               (= x53 x))) 
                       (= x53 y0))))
         :named goal))
(check-sat)
(exit)

