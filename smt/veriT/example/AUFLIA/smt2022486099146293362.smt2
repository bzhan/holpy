(set-info :smt-lib-version 2.6)
(set-logic AUFLIA)
(set-info :source |Generator: Rodin SMT Plug-in|)
(set-info :license "https://creativecommons.org/licenses/by-nc/4.0/")
(set-info :category "industrial")
(set-info :status unsat)

(declare-sort Color 0)
(declare-sort Sensor 0)
(declare-fun il_in_10 () Bool)
(declare-fun il_out_10 () Bool)
(declare-fun ml_in_10 () Bool)
(declare-fun ml_out_10 () Bool)
(declare-fun A () Int)
(declare-fun B () Int)
(declare-fun C () Int)
(declare-fun IL_IN_SR () Sensor)
(declare-fun IL_OUT_SR () Sensor)
(declare-fun ML_IN_SR () Sensor)
(declare-fun ML_OUT_SR () Sensor)
(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun c () Int)
(declare-fun d () Int)
(declare-fun green () Color)
(declare-fun il_pass () Int)
(declare-fun il_tl () Color)
(declare-fun ml_pass () Int)
(declare-fun ml_tl () Color)
(declare-fun n () Int)
(declare-fun off () Sensor)
(declare-fun on () Sensor)
(declare-fun red () Color)

(assert (! (<= 0 A)
         :named hyp1))
(assert (! (= ML_OUT_SR on)
         :named hyp2))
(assert (! (= ml_tl green)
         :named hyp3))
(assert (! (= c 0)
         :named hyp4))
(assert (! (not 
               ml_out_10)
         :named hyp5))
(assert (! (=> 
               il_in_10 
               (= A (- a 1)))
         :named hyp6))
(assert (! (=> 
               (not 
                   il_in_10) 
               (= A a))
         :named hyp7))
(assert (! (or 
               (< (+ a b 1) d) 
               (= (+ a b 1) d) 
               (and 
                   (= il_tl green) 
                   (< 1 b)) 
               (and 
                   (= il_tl green) 
                   (= b 1)) 
               (and 
                   (= il_tl red) 
                   (< 0 b) 
                   (= a 0) 
                   (= ml_pass 1)) 
               (< 0 a))
         :named hyp8))
(assert (! (< (+ a b) d)
         :named hyp9))
(assert (! (<= 0 d)
         :named hyp10))
(assert (! (< 0 d)
         :named hyp11))
(assert (! (forall ((x Color)) 
               (or 
                   (= x green) 
                   (= x red)))
         :named hyp12))
(assert (! (forall ((x0 Sensor)) 
               (or 
                   (= x0 on) 
                   (= x0 off)))
         :named hyp13))
(assert (! (not 
               (= on off))
         :named hyp14))
(assert (! (<= n d)
         :named hyp15))
(assert (! (or 
               (< 0 n) 
               (< n d))
         :named hyp16))
(assert (! (<= 0 a)
         :named hyp17))
(assert (! (<= 0 b)
         :named hyp18))
(assert (! (<= 0 c)
         :named hyp19))
(assert (! (= n (+ a b c))
         :named hyp20))
(assert (! (<= 0 (+ a b c))
         :named hyp21))
(assert (! (or 
               (= ml_tl red) 
               (= ml_tl green))
         :named hyp22))
(assert (! (or 
               (= il_tl red) 
               (= il_tl green))
         :named hyp23))
(assert (! (=> 
               (= il_tl green) 
               (= a 0))
         :named hyp24))
(assert (! (=> 
               (= il_tl green) 
               (< 0 b))
         :named hyp25))
(assert (! (or 
               (= ml_pass 0) 
               (= ml_pass 1))
         :named hyp26))
(assert (! (=> 
               (= ml_tl red) 
               (= ml_pass 1))
         :named hyp27))
(assert (! (=> 
               (= il_tl red) 
               (= il_pass 1))
         :named hyp28))
(assert (! (or 
               (= il_tl red) 
               (= ml_tl red))
         :named hyp29))
(assert (! (=> 
               (<= a 0) 
               (= a 0))
         :named hyp30))
(assert (! (=> 
               (<= b 0) 
               (= b 0))
         :named hyp31))
(assert (! (=> 
               (= IL_IN_SR on) 
               (< 0 A))
         :named hyp32))
(assert (! (=> 
               (= IL_OUT_SR on) 
               (< 0 B))
         :named hyp33))
(assert (! (=> 
               (= ML_IN_SR on) 
               (< 0 C))
         :named hyp34))
(assert (! (=> 
               il_out_10 
               (= il_tl green))
         :named hyp35))
(assert (! (=> 
               (= IL_IN_SR on) 
               (not 
                   il_in_10))
         :named hyp36))
(assert (! (=> 
               (= IL_OUT_SR on) 
               (not 
                   il_out_10))
         :named hyp37))
(assert (! (=> 
               (= ML_IN_SR on) 
               (not 
                   ml_in_10))
         :named hyp38))
(assert (! (=> 
               (and 
                   il_in_10 
                   ml_out_10) 
               (= A a))
         :named hyp39))
(assert (! (=> 
               (and 
                   (not 
                       il_in_10) 
                   ml_out_10) 
               (= A (+ a 1)))
         :named hyp40))
(assert (! (=> 
               (and 
                   il_in_10 
                   il_out_10) 
               (= B b))
         :named hyp41))
(assert (! (=> 
               (and 
                   il_in_10 
                   (not 
                       il_out_10)) 
               (= B (+ b 1)))
         :named hyp42))
(assert (! (=> 
               (and 
                   (not 
                       il_in_10) 
                   il_out_10) 
               (= B (- b 1)))
         :named hyp43))
(assert (! (=> 
               (and 
                   (not 
                       il_in_10) 
                   (not 
                       il_out_10)) 
               (= B b))
         :named hyp44))
(assert (! (=> 
               (and 
                   il_out_10 
                   ml_in_10) 
               (= C c))
         :named hyp45))
(assert (! (=> 
               (and 
                   il_out_10 
                   (not 
                       ml_in_10)) 
               (= C (+ c 1)))
         :named hyp46))
(assert (! (=> 
               (and 
                   (not 
                       il_out_10) 
                   ml_in_10) 
               (= C (- c 1)))
         :named hyp47))
(assert (! (=> 
               (and 
                   (not 
                       il_out_10) 
                   (not 
                       ml_in_10)) 
               (= C c))
         :named hyp48))
(assert (! (or 
               (= A 0) 
               (= C 0))
         :named hyp49))
(assert (! (<= (+ A B C) d)
         :named hyp50))
(assert (! (not 
               (= green red))
         :named hyp51))
(assert (! (=> 
               (and 
                   (<= d (+ b 1)) 
                   (not 
                       (= (+ b 1) d))) 
               (<= d b))
         :named hyp52))
(assert (! (=> 
               (and 
                   (<= b 1) 
                   (not 
                       (= b 1))) 
               (<= b 0))
         :named hyp53))
(assert (! (< (+ a b c) d)
         :named hyp54))
(assert (! (or 
               (< (+ a b 1) d) 
               (= (+ a b 1) d) 
               (and 
                   (= il_tl green) 
                   (< 1 b)) 
               (and 
                   (= il_tl green) 
                   (= b 1)) 
               (and 
                   (= ml_tl red) 
                   (= il_pass 1)) 
               (and 
                   (= il_tl red) 
                   (< 0 b) 
                   (= a 0) 
                   (= ml_pass 1)) 
               (< 0 a))
         :named hyp55))
(assert (! (not 
               (<= 0 (+ A 1)))
         :named goal))
(check-sat)
(exit)

