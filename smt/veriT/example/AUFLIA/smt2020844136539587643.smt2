(set-info :smt-lib-version 2.6)
(set-logic AUFLIA)
(set-info :source |Generator: Rodin SMT Plug-in|)
(set-info :license "https://creativecommons.org/licenses/by-nc/4.0/")
(set-info :category "industrial")
(set-info :status unsat)

(declare-sort PSZ 0)
(declare-sort S 0)
(declare-fun MS (S Int PSZ) Bool)

; Elementary Sets axiom (Singleton part)
(assert (forall ((x12 S) (x13 Int)) 
            (exists ((X PSZ)) 
                (and 
                    (MS x12 x13 X) 
                    (forall ((y S) (y0 Int)) 
                        (=> 
                            (MS y y0 X) 
                            (and 
                                (= y x12) 
                                (= y0 x13))))))))
(assert (! (forall ((a Int)) 
               (exists ((b Int) (f PSZ)) 
                   (and 
                       (forall ((x S) (x0 Int)) 
                           (=> 
                               (MS x x0 f) 
                               (and 
                                   (<= a x0) 
                                   (<= x0 b)))) 
                       (forall ((x1 S) (x2 Int) (x3 Int)) 
                           (=> 
                               (and 
                                   (MS x1 x2 f) 
                                   (MS x1 x3 f)) 
                               (= x2 x3))) 
                       (forall ((x4 S)) 
                           (exists ((x5 Int)) 
                               (MS x4 x5 f))) 
                       (forall ((x6 Int) (x7 S) (x8 S)) 
                           (=> 
                               (and 
                                   (MS x7 x6 f) 
                                   (MS x8 x6 f)) 
                               (= x7 x8))))))
         :named hyp1))
(assert (! (not 
               (and 
                   (forall ((x9 Bool) (x10 Bool)) 
                       (=> 
                           (and 
                               (not 
                                   x9) 
                               (not 
                                   x10)) 
                           (= 
                               x9 
                               x10))) 
                   (exists ((x11 Bool)) 
                       (not 
                           x11))))
         :named goal))
(check-sat)
(exit)

