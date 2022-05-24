(set-info :smt-lib-version 2.6)
(set-logic AUFLIA)
(set-info :source |Generator: Rodin SMT Plug-in|)
(set-info :license "https://creativecommons.org/licenses/by-nc/4.0/")
(set-info :category "industrial")
(set-info :status unsat)

(declare-sort D 0)
(declare-fun f (Int D) Bool)
(declare-fun parity (Int Int) Bool)
(declare-fun n () Int)

(assert (! (< 0 n)
         :named hyp1))
(assert (! (and 
               (forall ((x Int) (x0 D)) 
                   (=> 
                       (f x x0) 
                       (and 
                           (<= 1 x) 
                           (<= x n)))) 
               (forall ((x1 Int) (x2 D) (x3 D)) 
                   (=> 
                       (and 
                           (f x1 x2) 
                           (f x1 x3)) 
                       (= x2 x3))) 
               (forall ((x4 Int)) 
                   (=> 
                       (and 
                           (<= 1 x4) 
                           (<= x4 n)) 
                       (exists ((x5 D)) 
                           (f x4 x5)))))
         :named hyp2))
(assert (! (and 
               (forall ((x6 Int) (x7 Int)) 
                   (=> 
                       (parity x6 x7) 
                       (and 
                           (<= 0 x6) 
                           (or 
                               (= x7 0) 
                               (= x7 1))))) 
               (forall ((x8 Int) (x9 Int) (x10 Int)) 
                   (=> 
                       (and 
                           (parity x8 x9) 
                           (parity x8 x10)) 
                       (= x9 x10))) 
               (forall ((x11 Int)) 
                   (=> 
                       (<= 0 x11) 
                       (exists ((x12 Int)) 
                           (parity x11 x12)))))
         :named hyp3))
(assert (! (exists ((x13 Int) (x14 Int)) 
               (and 
                   (= x13 0) 
                   (= x14 0) 
                   (parity x13 x14)))
         :named hyp4))
(assert (! (exists ((x15 Int) (x16 Int)) 
               (and 
                   (= x16 0) 
                   (parity x16 x15)))
         :named hyp5))
(assert (! (forall ((x17 Int) (x18 Int) (x19 Int)) 
               (=> 
                   (and 
                       (parity x17 x18) 
                       (parity x17 x19)) 
                   (= x18 x19)))
         :named hyp6))
(assert (! (forall ((x20 Int)) 
               (=> 
                   (<= 0 x20) 
                   (exists ((x21 Int) (x22 Int)) 
                       (and 
                           (= x21 (+ x20 1)) 
                           (forall ((x23 Int)) 
                               (=> 
                                   (parity x20 x23) 
                                   (= x22 (- 1 x23)))) 
                           (parity x21 x22)))))
         :named hyp7))
(assert (! (forall ((x24 Int) (y Int)) 
               (=> 
                   (and 
                       (<= 0 y) 
                       (<= y x24) 
                       (<= x24 (+ y 1)) 
                       (exists ((x25 Int)) 
                           (and 
                               (parity y x25) 
                               (parity x24 x25)))) 
                   (= x24 y)))
         :named hyp8))
(assert (! (exists ((x26 Int) (x27 Int)) 
               (and 
                   (= x27 1) 
                   (parity x27 x26)))
         :named hyp9))
(assert (! (not 
               (exists ((x28 Int) (x29 Int)) 
                   (and 
                       (= x28 1) 
                       (= x29 1) 
                       (parity x28 x29))))
         :named goal))
(check-sat)
(exit)

