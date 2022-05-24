(set-info :smt-lib-version 2.6)
(set-logic AUFLIA)
(set-info :source |Generator: Rodin SMT Plug-in|)
(set-info :license "https://creativecommons.org/licenses/by-nc/4.0/")
(set-info :category "industrial")
(set-info :status unsat)

(declare-sort D 0)
(declare-fun f (Int D) Bool)
(declare-fun g (Int D) Bool)
(declare-fun d () D)
(declare-fun n () Int)
(declare-fun r () Int)
(declare-fun s () Int)

(assert (! (= s (+ r 1))
         :named hyp1))
(assert (! (f r d)
         :named hyp2))
(assert (! (exists ((x D)) 
               (f r x))
         :named hyp3))
(assert (! (forall ((x0 Int) (x1 D) (x2 D)) 
               (=> 
                   (and 
                       (f x0 x1) 
                       (f x0 x2)) 
                   (= x1 x2)))
         :named hyp4))
(assert (! (and 
               (<= r (+ r 1)) 
               (<= (+ r 1) (+ r 1)))
         :named hyp5))
(assert (! (and 
               (forall ((x3 Int) (x4 D)) 
                   (=> 
                       (f x3 x4) 
                       (and 
                           (<= 1 x3) 
                           (<= x3 n)))) 
               (forall ((x5 Int) (x6 D) (x7 D)) 
                   (=> 
                       (and 
                           (f x5 x6) 
                           (f x5 x7)) 
                       (= x6 x7))) 
               (forall ((x8 Int)) 
                   (=> 
                       (and 
                           (<= 1 x8) 
                           (<= x8 n)) 
                       (exists ((x9 D)) 
                           (f x8 x9)))))
         :named hyp6))
(assert (! (and 
               (forall ((x10 Int) (x11 D)) 
                   (=> 
                       (g x10 x11) 
                       (and 
                           (<= 1 x10) 
                           (<= x10 n)))) 
               (forall ((x12 Int) (x13 D) (x14 D)) 
                   (=> 
                       (and 
                           (g x12 x13) 
                           (g x12 x14)) 
                       (= x13 x14))))
         :named hyp7))
(assert (! (and 
               (<= 1 r) 
               (<= r (+ n 1)))
         :named hyp8))
(assert (! (forall ((x15 Int) (x16 D)) 
               (= 
                   (g x15 x16) 
                   (and 
                       (f x15 x16) 
                       (<= 1 x15) 
                       (<= x15 (- r 1)))))
         :named hyp9))
(assert (! (<= s (+ n 1))
         :named hyp10))
(assert (! (and 
               (<= r s) 
               (<= s (+ r 1)))
         :named hyp11))
(assert (! (not 
               (and 
                   (<= (+ r 1) (+ r 1)) 
                   (<= (+ r 1) (+ r 1 1))))
         :named goal))
(check-sat)
(exit)

