(set-info :smt-lib-version 2.6)
(set-logic AUFLIA)
(set-info :source |Generator: Rodin SMT Plug-in|)
(set-info :license "https://creativecommons.org/licenses/by-nc/4.0/")
(set-info :category "industrial")
(set-info :status unsat)

(declare-fun r (Int Int Int Int) Bool)

(assert (! (forall ((x Int) (x0 Int) (x1 Int) (x2 Int)) 
               (=> 
                   (r x1 x x0 x2) 
                   (and 
                       (<= 0 x) 
                       (<= 0 x0) 
                       (<= 0 x1) 
                       (<= 0 x2))))
         :named hyp1))
(assert (! (forall ((x3 Int) (x4 Int) (x5 Int) (x6 Int)) 
               (= 
                   (r x5 x3 x4 x6) 
                   (exists ((x10 Int) (y1 Int) (x20 Int) (y2 Int)) 
                       (and 
                           (<= 0 x10) 
                           (<= 0 y1) 
                           (<= 0 x20) 
                           (<= 0 y2) 
                           (or 
                               (< x10 x20) 
                               (and 
                                   (= x10 x20) 
                                   (< y1 y2))) 
                           (= x3 x10) 
                           (= x4 y1) 
                           (= x5 x20) 
                           (= x6 y2)))))
         :named hyp2))
(assert (! (forall ((x7 Int) (x8 Int) (x9 Int) (x11 Int)) 
               (=> 
                   (exists ((x12 Int) (y10 Int) (x21 Int) (y20 Int)) 
                       (and 
                           (<= 0 x12) 
                           (<= 0 y10) 
                           (<= 0 x21) 
                           (<= 0 y20) 
                           (or 
                               (< x12 x21) 
                               (and 
                                   (= x12 x21) 
                                   (< y10 y20))) 
                           (= x7 x12) 
                           (= x8 y10) 
                           (= x9 x21) 
                           (= x11 y20))) 
                   (and 
                       (<= 0 x7) 
                       (<= 0 x8) 
                       (<= 0 x9) 
                       (<= 0 x11))))
         :named hyp3))
(assert (! (not 
               (forall ((x13 Int) (x14 Int) (x15 Int) (x16 Int)) 
                   (not 
                       (and 
                           (exists ((x17 Int) (y11 Int) (x22 Int) (y21 Int)) 
                               (and 
                                   (<= 0 x17) 
                                   (<= 0 y11) 
                                   (<= 0 x22) 
                                   (<= 0 y21) 
                                   (or 
                                       (< x17 x22) 
                                       (and 
                                           (= x17 x22) 
                                           (< y11 y21))) 
                                   (= x13 x17) 
                                   (= x14 y11) 
                                   (= x15 x22) 
                                   (= x16 y21))) 
                           (= x13 x15) 
                           (= x14 x16)))))
         :named goal))
(check-sat)
(exit)

