(set-info :smt-lib-version 2.6)
(set-logic AUFLIA)
(set-info :source |Generator: Rodin SMT Plug-in|)
(set-info :license "https://creativecommons.org/licenses/by-nc/4.0/")
(set-info :category "industrial")
(set-info :status unsat)

(declare-sort B 0)
(declare-sort R 0)
(declare-fun resbl (B) Bool)
(declare-fun resrt (R) Bool)
(declare-fun rsrtbl (B R) Bool)
(declare-fun rtbl (B R) Bool)
(declare-fun r () R)

(assert (! (and 
               (forall ((x B) (x0 R)) 
                   (=> 
                       (rsrtbl x x0) 
                       (and 
                           (resbl x) 
                           (resrt x0)))) 
               (forall ((x1 B) (x2 R) (x3 R)) 
                   (=> 
                       (and 
                           (rsrtbl x1 x2) 
                           (rsrtbl x1 x3)) 
                       (= x2 x3))) 
               (forall ((x4 B)) 
                   (=> 
                       (resbl x4) 
                       (exists ((x5 R)) 
                           (rsrtbl x4 x5)))))
         :named hyp1))
(assert (! (forall ((x6 B)) 
               (not 
                   (and 
                       (exists ((x7 R)) 
                           (and 
                               (= x7 r) 
                               (rtbl x6 x7))) 
                       (resbl x6))))
         :named hyp2))
(assert (! (not 
               (resrt r))
         :named hyp3))
(assert (! (not 
               (and 
                   (forall ((x8 B) (x9 R)) 
                       (=> 
                           (or 
                               (rsrtbl x8 x9) 
                               (and 
                                   (rtbl x8 x9) 
                                   (= x9 r))) 
                           (and 
                               (or 
                                   (resbl x8) 
                                   (exists ((x10 R)) 
                                       (and 
                                           (= x10 r) 
                                           (rtbl x8 x10)))) 
                               (or 
                                   (resrt x9) 
                                   (= x9 r))))) 
                   (forall ((x11 B) (x12 R) (x13 R)) 
                       (=> 
                           (and 
                               (or 
                                   (rsrtbl x11 x12) 
                                   (and 
                                       (rtbl x11 x12) 
                                       (= x12 r))) 
                               (or 
                                   (rsrtbl x11 x13) 
                                   (and 
                                       (rtbl x11 x13) 
                                       (= x13 r)))) 
                           (= x12 x13))) 
                   (forall ((x14 B)) 
                       (=> 
                           (or 
                               (resbl x14) 
                               (exists ((x15 R)) 
                                   (and 
                                       (= x15 r) 
                                       (rtbl x14 x15)))) 
                           (or 
                               (exists ((x16 R)) 
                                   (rsrtbl x14 x16)) 
                               (exists ((x17 R)) 
                                   (and 
                                       (rtbl x14 x17) 
                                       (= x17 r))))))))
         :named goal))
(check-sat)
(exit)

