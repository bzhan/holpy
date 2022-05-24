(set-info :smt-lib-version 2.6)
(set-logic AUFLIA)
(set-info :source |Generator: Rodin SMT Plug-in|)
(set-info :license "https://creativecommons.org/licenses/by-nc/4.0/")
(set-info :category "industrial")
(set-info :status unsat)

(declare-sort MODE 0)
(declare-fun b_2_01 (Bool Int) Bool)
(declare-fun a1 () Int)
(declare-fun a2 () Int)
(declare-fun b1 () Int)
(declare-fun b2 () Int)
(declare-fun cir () MODE)
(declare-fun env () MODE)
(declare-fun mode () MODE)
(declare-fun o1 () Bool)
(declare-fun o2 () Bool)
(declare-fun p1 () Bool)
(declare-fun p2 () Bool)
(declare-fun r1 () Int)
(declare-fun r2 () Int)

(assert (! (and 
               (forall ((x Bool) (x0 Int) (x1 Int)) 
                   (=> 
                       (and 
                           (b_2_01 x x0) 
                           (b_2_01 x x1)) 
                       (= x0 x1))) 
               (forall ((x2 Bool)) 
                   (exists ((x3 Int)) 
                       (b_2_01 x2 x3))))
         :named hyp1))
(assert (! (exists ((x4 Bool) (x5 Int)) 
               (and 
                   x4 
                   (= x5 1) 
                   (b_2_01 x4 x5)))
         :named hyp2))
(assert (! (exists ((x6 Int) (x7 Bool)) 
               (and 
                   x7 
                   (b_2_01 x7 x6)))
         :named hyp3))
(assert (! (forall ((x8 Bool) (x9 Int) (x10 Int)) 
               (=> 
                   (and 
                       (b_2_01 x8 x9) 
                       (b_2_01 x8 x10)) 
                   (= x9 x10)))
         :named hyp4))
(assert (! (exists ((x11 Bool) (x12 Int)) 
               (and 
                   (not 
                       x11) 
                   (= x12 0) 
                   (b_2_01 x11 x12)))
         :named hyp5))
(assert (! (exists ((x13 Int) (x14 Bool)) 
               (and 
                   (not 
                       x14) 
                   (b_2_01 x14 x13)))
         :named hyp6))
(assert (! (<= a1 r1)
         :named hyp7))
(assert (! (<= r1 (+ a1 1))
         :named hyp8))
(assert (! (<= a2 r2)
         :named hyp9))
(assert (! (<= r2 (+ a2 1))
         :named hyp10))
(assert (! (=> 
               (= mode env) 
               (= 
                   (= r2 a2) 
                   (not 
                       p2)))
         :named hyp11))
(assert (! (=> 
               (= mode env) 
               (forall ((x15 Int)) 
                   (=> 
                       (b_2_01 o1 x15) 
                       (= a1 (+ b1 x15)))))
         :named hyp12))
(assert (! (=> 
               (= mode env) 
               (forall ((x16 Int)) 
                   (=> 
                       (b_2_01 o2 x16) 
                       (= a2 (+ b2 x16)))))
         :named hyp13))
(assert (! (= mode cir)
         :named hyp14))
(assert (! (not 
               p1)
         :named hyp15))
(assert (! (not 
               (= env cir))
         :named hyp16))
(assert (! (not 
               (= r2 b2))
         :named hyp17))
(assert (! (=> 
               (= mode env) 
               (= r1 a1))
         :named hyp18))
(assert (! (=> 
               (= r2 a2) 
               (not 
                   p2))
         :named hyp19))
(assert (! (or 
               (and 
                   (not 
                       (= r1 a1)) 
                   (not 
                       p2)) 
               (not 
                   (= r2 a2)) 
               (and 
                   (= r1 a1) 
                   (= r2 a2)))
         :named hyp20))
(assert (! (= a1 b1)
         :named hyp21))
(assert (! (= a2 b2)
         :named hyp22))
(assert (! (=> 
               (= mode env) 
               (exists ((x17 Int)) 
                   (b_2_01 o1 x17)))
         :named hyp23))
(assert (! (=> 
               (= mode env) 
               (exists ((x18 Int)) 
                   (b_2_01 o2 x18)))
         :named hyp24))
(assert (! (or 
               (and 
                   (not 
                       (= r1 b1)) 
                   (not 
                       p2)) 
               (not 
                   (= r2 a2)) 
               (and 
                   (= r1 b1) 
                   (= r2 a2)))
         :named hyp25))
(assert (! (not 
               (forall ((x19 Int)) 
                   (=> 
                       (exists ((x20 Bool)) 
                           (and 
                               (not 
                                   x20) 
                               (b_2_01 x20 x19))) 
                       (= b1 (+ b1 x19)))))
         :named goal))
(check-sat)
(exit)

