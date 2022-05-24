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

(assert (! (= mode env)
         :named hyp1))
(assert (! (forall ((x Int)) 
               (=> 
                   (b_2_01 o1 x) 
                   (= r1 (+ b1 x))))
         :named hyp2))
(assert (! (forall ((x0 Int)) 
               (=> 
                   (b_2_01 o1 x0) 
                   (= a1 (+ b1 x0))))
         :named hyp3))
(assert (! (forall ((x1 Int)) 
               (=> 
                   (b_2_01 o2 x1) 
                   (= a2 (+ b2 x1))))
         :named hyp4))
(assert (! (exists ((x2 Int)) 
               (b_2_01 o2 x2))
         :named hyp5))
(assert (! (not 
               p1)
         :named hyp6))
(assert (! (= 
               (forall ((x3 Int)) 
                   (=> 
                       (b_2_01 o2 x3) 
                       (= r2 (+ b2 x3)))) 
               (not 
                   p2))
         :named hyp7))
(assert (! (and 
               (forall ((x4 Bool) (x5 Int) (x6 Int)) 
                   (=> 
                       (and 
                           (b_2_01 x4 x5) 
                           (b_2_01 x4 x6)) 
                       (= x5 x6))) 
               (forall ((x7 Bool)) 
                   (exists ((x8 Int)) 
                       (b_2_01 x7 x8))))
         :named hyp8))
(assert (! (exists ((x9 Bool) (x10 Int)) 
               (and 
                   x9 
                   (= x10 1) 
                   (b_2_01 x9 x10)))
         :named hyp9))
(assert (! (exists ((x11 Int) (x12 Bool)) 
               (and 
                   x12 
                   (b_2_01 x12 x11)))
         :named hyp10))
(assert (! (forall ((x13 Bool) (x14 Int) (x15 Int)) 
               (=> 
                   (and 
                       (b_2_01 x13 x14) 
                       (b_2_01 x13 x15)) 
                   (= x14 x15)))
         :named hyp11))
(assert (! (exists ((x16 Bool) (x17 Int)) 
               (and 
                   (not 
                       x16) 
                   (= x17 0) 
                   (b_2_01 x16 x17)))
         :named hyp12))
(assert (! (exists ((x18 Int) (x19 Bool)) 
               (and 
                   (not 
                       x19) 
                   (b_2_01 x19 x18)))
         :named hyp13))
(assert (! (<= a1 r1)
         :named hyp14))
(assert (! (<= r1 (+ a1 1))
         :named hyp15))
(assert (! (<= a2 r2)
         :named hyp16))
(assert (! (<= r2 (+ a2 1))
         :named hyp17))
(assert (! (=> 
               (and 
                   (= mode cir) 
                   (= r2 a2)) 
               (not 
                   p2))
         :named hyp18))
(assert (! (=> 
               (= mode cir) 
               (= a1 b1))
         :named hyp19))
(assert (! (=> 
               (= mode cir) 
               (= a2 b2))
         :named hyp20))
(assert (! (=> 
               (= mode cir) 
               (= 
                   (not 
                       i1) 
                   (= r1 b1)))
         :named hyp21))
(assert (! (=> 
               (= mode cir) 
               (= 
                   (not 
                       i2) 
                   (= r2 b2)))
         :named hyp22))
(assert (! (exists ((x20 Int)) 
               (b_2_01 o1 x20))
         :named hyp23))
(assert (! (not 
               (= env cir))
         :named hyp24))
(assert (! (= 
               (= r2 a2) 
               (not 
                   p2))
         :named hyp25))
(assert (! (= r1 a1)
         :named hyp26))
(assert (! (not 
               (not 
                   (forall ((x21 Int) (x22 Int)) 
                       (=> 
                           (and 
                               (b_2_01 o1 x22) 
                               (b_2_01 o1 x21)) 
                           (= (+ b1 x22 1) (+ b1 x21))))))
         :named goal))
(check-sat)
(exit)

