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
(declare-fun i1 () Bool)
(declare-fun i2 () Bool)
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
               (and 
                   (= mode cir) 
                   (= r1 a1)) 
               (not 
                   p1))
         :named hyp11))
(assert (! (=> 
               (= mode cir) 
               (= a1 b1))
         :named hyp12))
(assert (! (=> 
               (= mode cir) 
               (= a2 b2))
         :named hyp13))
(assert (! (=> 
               (= mode cir) 
               (= 
                   (not 
                       i1) 
                   (= r1 b1)))
         :named hyp14))
(assert (! (=> 
               (= mode cir) 
               (= 
                   (not 
                       i2) 
                   (= r2 b2)))
         :named hyp15))
(assert (! (= mode env)
         :named hyp16))
(assert (! (forall ((x15 Int)) 
               (=> 
                   (b_2_01 o2 x15) 
                   (= r2 (+ b2 x15))))
         :named hyp17))
(assert (! (exists ((x16 Int)) 
               (b_2_01 o2 x16))
         :named hyp18))
(assert (! (not 
               (= env cir))
         :named hyp19))
(assert (! (= 
               (= r1 a1) 
               (not 
                   p1))
         :named hyp20))
(assert (! (forall ((x17 Int)) 
               (=> 
                   (b_2_01 o1 x17) 
                   (= a1 (+ b1 x17))))
         :named hyp21))
(assert (! (exists ((x18 Int)) 
               (b_2_01 o1 x18))
         :named hyp22))
(assert (! (forall ((x19 Int)) 
               (=> 
                   (b_2_01 o2 x19) 
                   (= a2 (+ b2 x19))))
         :named hyp23))
(assert (! (not 
               p2)
         :named hyp24))
(assert (! (= r2 a2)
         :named hyp25))
(assert (! (= 
               (forall ((x20 Int)) 
                   (=> 
                       (b_2_01 o1 x20) 
                       (= r1 (+ b1 x20)))) 
               (not 
                   p1))
         :named hyp26))
(assert (! (not 
               (not 
                   (forall ((x21 Int) (x22 Int)) 
                       (=> 
                           (and 
                               (b_2_01 o2 x22) 
                               (b_2_01 o2 x21)) 
                           (= (+ b2 x22 1) (+ b2 x21))))))
         :named goal))
(check-sat)
(exit)

