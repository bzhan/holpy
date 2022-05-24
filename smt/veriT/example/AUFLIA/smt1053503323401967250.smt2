(set-info :smt-lib-version 2.6)
(set-logic AUFLIA)
(set-info :source |Generator: Rodin SMT Plug-in|)
(set-info :license "https://creativecommons.org/licenses/by-nc/4.0/")
(set-info :category "industrial")
(set-info :status unsat)

(declare-sort L 0)
(declare-sort P 0)
(declare-sort PL0 0)
(declare-fun MS (L PL0) Bool)
(declare-fun aut (P L) Bool)
(declare-fun com (L L) Bool)
(declare-fun np (L L) Bool)
(declare-fun sit (P L) Bool)
(declare-fun l () L)
(declare-fun outside () L)
(declare-fun p () P)

; Elementary Sets axiom (Singleton part)
(assert (forall ((x34 L)) 
            (exists ((X PL0)) 
                (and 
                    (MS x34 X) 
                    (forall ((y L)) 
                        (=> 
                            (MS y X) 
                            (= y x34)))))))
(assert (! (forall ((x P) (x0 L)) 
               (=> 
                   (= x0 outside) 
                   (aut x x0)))
         :named hyp1))
(assert (! (exists ((l0 L)) 
               (and 
                   (not 
                       (= l0 outside)) 
                   (forall ((x1 P) (x2 L)) 
                       (=> 
                           (= x2 l0) 
                           (aut x1 x2)))))
         :named hyp2))
(assert (! (and 
               (forall ((x3 L) (x4 L)) 
                   (=> 
                       (np x3 x4) 
                       (not 
                           (= x3 outside)))) 
               (forall ((x5 L) (x6 L) (x7 L)) 
                   (=> 
                       (and 
                           (np x5 x6) 
                           (np x5 x7)) 
                       (= x6 x7))) 
               (forall ((x8 L)) 
                   (=> 
                       (not 
                           (= x8 outside)) 
                       (exists ((x9 L)) 
                           (np x8 x9)))))
         :named hyp3))
(assert (! (forall ((x10 L) (x11 L)) 
               (=> 
                   (np x10 x11) 
                   (com x10 x11)))
         :named hyp4))
(assert (! (forall ((s PL0)) 
               (=> 
                   (forall ((x12 L)) 
                       (=> 
                           (MS x12 s) 
                           (exists ((x13 L)) 
                               (and 
                                   (MS x13 s) 
                                   (np x12 x13))))) 
                   (forall ((x14 L)) 
                       (not 
                           (MS x14 s)))))
         :named hyp5))
(assert (! (forall ((x15 P) (x16 L)) 
               (=> 
                   (and 
                       (aut x15 x16) 
                       (not 
                           (= x16 outside))) 
                   (exists ((x17 L)) 
                       (and 
                           (aut x15 x17) 
                           (np x16 x17)))))
         :named hyp6))
(assert (! (exists ((l1 L)) 
               (and 
                   (not 
                       (= l1 outside)) 
                   (com outside l1) 
                   (forall ((x18 P) (x19 L)) 
                       (=> 
                           (= x19 l1) 
                           (aut x18 x19)))))
         :named hyp7))
(assert (! (and 
               (forall ((x20 P) (x21 L) (x22 L)) 
                   (=> 
                       (and 
                           (sit x20 x21) 
                           (sit x20 x22)) 
                       (= x21 x22))) 
               (forall ((x23 P)) 
                   (exists ((x24 L)) 
                       (sit x23 x24))))
         :named hyp8))
(assert (! (forall ((x25 P) (x26 L)) 
               (=> 
                   (sit x25 x26) 
                   (aut x25 x26)))
         :named hyp9))
(assert (! (aut p l)
         :named hyp10))
(assert (! (exists ((x27 L)) 
               (and 
                   (sit p x27) 
                   (com x27 l)))
         :named hyp11))
(assert (! (exists ((x28 L)) 
               (sit p x28))
         :named hyp12))
(assert (! (forall ((x29 P) (x30 L) (x31 L)) 
               (=> 
                   (and 
                       (sit x29 x30) 
                       (sit x29 x31)) 
                   (= x30 x31)))
         :named hyp13))
(assert (! (forall ((x32 L) (x33 L)) 
               (not 
                   (and 
                       (com x32 x33) 
                       (= x32 x33))))
         :named hyp14))
(assert (! (not 
               (not 
                   (sit p l)))
         :named goal))
(check-sat)
(exit)

