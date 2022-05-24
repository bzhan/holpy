(set-info :smt-lib-version 2.6)
(set-logic AUFLIA)
(set-info :source |Generator: Rodin SMT Plug-in|)
(set-info :license "https://creativecommons.org/licenses/by-nc/4.0/")
(set-info :category "industrial")
(set-info :status unsat)

(declare-sort D 0)
(declare-sort PZD 0)
(declare-fun Data (Int PZD) Bool)
(declare-fun MS (Int D PZD) Bool)
(declare-fun data (Int PZD) Bool)
(declare-fun slot (Int Int) Bool)
(declare-fun adr_w () Int)
(declare-fun d () D)
(declare-fun latest () Int)
(declare-fun pair_w () Int)
(declare-fun reading () Int)
(declare-fun w () Int)
(declare-fun wtp () PZD)

; Elementary Sets axiom (Singleton part)
(assert (forall ((x32 Int) (x33 D)) 
            (exists ((X PZD)) 
                (and 
                    (MS x32 x33 X) 
                    (forall ((y Int) (y0 D)) 
                        (=> 
                            (MS y y0 X) 
                            (and 
                                (= y x32) 
                                (= y0 x33))))))))
(assert (! (= adr_w 1)
         :named hyp1))
(assert (! (forall ((x Int)) 
               (= 
                   (exists ((x0 D)) 
                       (MS x x0 wtp)) 
                   (and 
                       (<= 1 x) 
                       (<= x w))))
         :named hyp2))
(assert (! (= pair_w latest)
         :named hyp3))
(assert (! (or 
               (= 2 1) 
               (= 2 4) 
               (= 2 5))
         :named hyp4))
(assert (! (forall ((x1 Int) (x2 PZD)) 
               (= 
                   (Data x1 x2) 
                   (data x1 x2)))
         :named hyp5))
(assert (! (exists ((x3 PZD) (x4 Int)) 
               (and 
                   (= x4 (- 1 reading)) 
                   (data x4 x3)))
         :named hyp6))
(assert (! (forall ((x5 Int) (x6 PZD) (x7 PZD)) 
               (=> 
                   (and 
                       (data x5 x6) 
                       (data x5 x7)) 
                   (forall ((x8 Int) (x9 D)) 
                       (= 
                           (MS x8 x9 x6) 
                           (MS x8 x9 x7)))))
         :named hyp7))
(assert (! (=> 
               (or 
                   (= 1 2) 
                   (= 1 3)) 
               (exists ((x10 PZD)) 
                   (data latest x10)))
         :named hyp8))
(assert (! (not 
               (forall ((x11 Int) (x12 PZD)) 
                   (= 
                       (or 
                           (and 
                               (data x11 x12) 
                               (not 
                                   (exists ((x13 PZD)) 
                                       (and 
                                           (= x11 (- 1 reading)) 
                                           (forall ((x14 Int) (x15 D)) 
                                               (= 
                                                   (MS x14 x15 x13) 
                                                   (or 
                                                       (and 
                                                           (exists ((x16 PZD)) 
                                                               (and 
                                                                   (exists ((x17 Int)) 
                                                                       (and 
                                                                           (= x17 (- 1 reading)) 
                                                                           (data x17 x16))) 
                                                                   (MS x14 x15 x16))) 
                                                           (not 
                                                               (exists ((x18 D)) 
                                                                   (and 
                                                                       (forall ((x19 Int)) 
                                                                           (=> 
                                                                               (exists ((x20 Int)) 
                                                                                   (and 
                                                                                       (= x20 (- 1 reading)) 
                                                                                       (slot x20 x19))) 
                                                                               (= x14 (- 1 x19)))) 
                                                                       (= x18 d))))) 
                                                       (and 
                                                           (forall ((x21 Int)) 
                                                               (=> 
                                                                   (exists ((x22 Int)) 
                                                                       (and 
                                                                           (= x22 (- 1 reading)) 
                                                                           (slot x22 x21))) 
                                                                   (= x14 (- 1 x21)))) 
                                                           (= x15 d))))))))) 
                           (and 
                               (= x11 (- 1 reading)) 
                               (forall ((x23 Int) (x24 D)) 
                                   (= 
                                       (MS x23 x24 x12) 
                                       (or 
                                           (and 
                                               (exists ((x25 PZD)) 
                                                   (and 
                                                       (exists ((x26 Int)) 
                                                           (and 
                                                               (= x26 (- 1 reading)) 
                                                               (data x26 x25))) 
                                                       (MS x23 x24 x25))) 
                                               (not 
                                                   (exists ((x27 D)) 
                                                       (and 
                                                           (forall ((x28 Int)) 
                                                               (=> 
                                                                   (exists ((x29 Int)) 
                                                                       (and 
                                                                           (= x29 (- 1 reading)) 
                                                                           (slot x29 x28))) 
                                                                   (= x23 (- 1 x28)))) 
                                                           (= x27 d))))) 
                                           (and 
                                               (forall ((x30 Int)) 
                                                   (=> 
                                                       (exists ((x31 Int)) 
                                                           (and 
                                                               (= x31 (- 1 reading)) 
                                                               (slot x31 x30))) 
                                                       (= x23 (- 1 x30)))) 
                                               (= x24 d))))))) 
                       (data x11 x12))))
         :named goal))
(check-sat)
(exit)

