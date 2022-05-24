(set-info :smt-lib-version 2.6)
(set-logic AUFLIA)
(set-info :source |Generator: Rodin SMT Plug-in|)
(set-info :license "https://creativecommons.org/licenses/by-nc/4.0/")
(set-info :category "industrial")
(set-info :status unsat)

(declare-sort K 0)
(declare-sort N 0)
(declare-sort PN 0)
(declare-sort PNN 0)
(declare-sort PNZ 0)
(declare-fun MS (N Int PNZ) Bool)
(declare-fun MS0 (N N PNN) Bool)
(declare-fun MS1 (N PN) Bool)
(declare-fun b () PN)
(declare-fun c () PNN)
(declare-fun f () PNN)
(declare-fun g () PNN)
(declare-fun ko () K)
(declare-fun n () K)
(declare-fun ok () K)
(declare-fun p () N)
(declare-fun t () N)

; Elementary Sets axiom (Singleton part)
(assert (forall ((x79 N) (x80 N)) 
            (exists ((X PNN)) 
                (and 
                    (MS0 x79 x80 X) 
                    (forall ((y0 N) (y1 N)) 
                        (=> 
                            (MS0 y0 y1 X) 
                            (and 
                                (= y0 x79) 
                                (= y1 x80))))))))
; Elementary Sets axiom (Singleton part)
(assert (forall ((x81 N) (x82 Int)) 
            (exists ((X0 PNZ)) 
                (and 
                    (MS x81 x82 X0) 
                    (forall ((y2 N) (y3 Int)) 
                        (=> 
                            (MS y2 y3 X0) 
                            (and 
                                (= y2 x81) 
                                (= y3 x82))))))))
; Elementary Sets axiom (Singleton part)
(assert (forall ((x83 N)) 
            (exists ((X1 PN)) 
                (and 
                    (MS1 x83 X1) 
                    (forall ((y4 N)) 
                        (=> 
                            (MS1 y4 X1) 
                            (= y4 x83)))))))
(assert (! (forall ((a Int)) 
               (exists ((b0 Int) (f0 PNZ)) 
                   (and 
                       (forall ((x N) (x0 Int)) 
                           (=> 
                               (MS x x0 f0) 
                               (and 
                                   (<= a x0) 
                                   (<= x0 b0)))) 
                       (forall ((x1 N) (x2 Int) (x3 Int)) 
                           (=> 
                               (and 
                                   (MS x1 x2 f0) 
                                   (MS x1 x3 f0)) 
                               (= x2 x3))) 
                       (forall ((x4 N)) 
                           (exists ((x5 Int)) 
                               (MS x4 x5 f0))) 
                       (forall ((x6 Int) (x7 N) (x8 N)) 
                           (=> 
                               (and 
                                   (MS x7 x6 f0) 
                                   (MS x8 x6 f0)) 
                               (= x7 x8))))))
         :named hyp1))
(assert (! (forall ((x9 N) (x10 N)) 
               (=> 
                   (= x9 x10) 
                   (MS0 x9 x10 c)))
         :named hyp2))
(assert (! (forall ((x11 N) (x12 N)) 
               (=> 
                   (exists ((x13 N)) 
                       (and 
                           (MS0 x11 x13 c) 
                           (MS0 x13 x12 g))) 
                   (MS0 x11 x12 c)))
         :named hyp3))
(assert (! (forall ((r PNN)) 
               (=> 
                   (and 
                       (forall ((x14 N) (x15 N)) 
                           (=> 
                               (= x14 x15) 
                               (MS0 x14 x15 r))) 
                       (forall ((x16 N) (x17 N)) 
                           (=> 
                               (exists ((x18 N)) 
                                   (and 
                                       (MS0 x16 x18 r) 
                                       (MS0 x18 x17 g))) 
                               (MS0 x16 x17 r)))) 
                   (forall ((x19 N) (x20 N)) 
                       (=> 
                           (MS0 x19 x20 c) 
                           (MS0 x19 x20 r)))))
         :named hyp4))
(assert (! (MS1 t b)
         :named hyp5))
(assert (! (=> 
               (forall ((x21 N)) 
                   (=> 
                       (exists ((x22 N)) 
                           (and 
                               (MS1 x22 b) 
                               (MS0 x22 x21 g))) 
                       (MS1 x21 b))) 
               (forall ((x23 N)) 
                   (=> 
                       (exists ((x24 N)) 
                           (and 
                               (MS1 x24 b) 
                               (MS0 x24 x23 c))) 
                       (MS1 x23 b))))
         :named hyp6))
(assert (! (forall ((x25 N)) 
               (=> 
                   (MS1 x25 b) 
                   (exists ((x26 N)) 
                       (and 
                           (= x26 t) 
                           (MS0 x26 x25 c)))))
         :named hyp7))
(assert (! (MS1 p b)
         :named hyp8))
(assert (! (and 
               (forall ((x27 N) (x28 N)) 
                   (=> 
                       (MS0 x27 x28 f) 
                       (and 
                           (MS1 x27 b) 
                           (not 
                               (= x27 t)) 
                           (MS1 x28 b) 
                           (not 
                               (= x28 p))))) 
               (forall ((x29 N) (x30 N) (x31 N)) 
                   (=> 
                       (and 
                           (MS0 x29 x30 f) 
                           (MS0 x29 x31 f)) 
                       (= x30 x31))) 
               (forall ((x32 N) (x33 N) (x34 N)) 
                   (=> 
                       (and 
                           (MS0 x33 x32 f) 
                           (MS0 x34 x32 f)) 
                       (= x33 x34))))
         :named hyp9))
(assert (! (forall ((x35 N)) 
               (= 
                   (or 
                       (exists ((x36 N)) 
                           (MS0 x35 x36 f)) 
                       (= x35 t)) 
                   (or 
                       (exists ((x37 N)) 
                           (MS0 x37 x35 f)) 
                       (= x35 p))))
         :named hyp10))
(assert (! (forall ((s PN)) 
               (=> 
                   (and 
                       (forall ((x38 N)) 
                           (=> 
                               (MS1 x38 s) 
                               (or 
                                   (exists ((x39 N)) 
                                       (MS0 x38 x39 f)) 
                                   (= x38 t)))) 
                       (forall ((x40 N)) 
                           (=> 
                               (MS1 x40 s) 
                               (exists ((x41 N)) 
                                   (and 
                                       (MS1 x41 s) 
                                       (MS0 x40 x41 f)))))) 
                   (forall ((x42 N)) 
                       (not 
                           (MS1 x42 s)))))
         :named hyp11))
(assert (! (forall ((x43 N) (x44 N)) 
               (=> 
                   (MS0 x44 x43 f) 
                   (MS0 x43 x44 g)))
         :named hyp12))
(assert (! (forall ((x45 N)) 
               (=> 
                   (exists ((x46 N)) 
                       (and 
                           (MS1 x46 b) 
                           (not 
                               (or 
                                   (exists ((x47 N)) 
                                       (MS0 x46 x47 f)) 
                                   (= x46 t))) 
                           (MS0 x46 x45 g))) 
                   (MS1 x45 b)))
         :named hyp13))
(assert (! (= n ko)
         :named hyp14))
(assert (! (forall ((x48 N)) 
               (=> 
                   (exists ((x49 N)) 
                       (and 
                           (= x49 p) 
                           (MS0 x49 x48 g))) 
                   (MS1 x48 b)))
         :named hyp15))
(assert (! (exists ((x50 N)) 
               (MS0 p x50 f))
         :named hyp16))
(assert (! (forall ((x51 N) (x52 N) (x53 N)) 
               (=> 
                   (and 
                       (MS0 x51 x52 f) 
                       (MS0 x51 x53 f)) 
                   (= x52 x53)))
         :named hyp17))
(assert (! (forall ((x54 K)) 
               (or 
                   (= x54 ok) 
                   (= x54 ko)))
         :named hyp18))
(assert (! (not 
               (= ok ko))
         :named hyp19))
(assert (! (or 
               (forall ((x55 N)) 
                   (=> 
                       (exists ((x56 N)) 
                           (and 
                               (MS1 x56 b) 
                               (MS0 x56 x55 g))) 
                       (MS1 x55 b))) 
               (and 
                   (not 
                       (forall ((x57 N)) 
                           (=> 
                               (exists ((x58 N)) 
                                   (and 
                                       (MS1 x58 b) 
                                       (MS0 x58 x57 g))) 
                               (MS1 x57 b)))) 
                   (exists ((x59 N) (y N)) 
                       (and 
                           (MS0 x59 y g) 
                           (MS1 x59 b) 
                           (not 
                               (MS1 y b))))))
         :named hyp20))
(assert (! (not 
               (= p t))
         :named hyp21))
(assert (! (not 
               (= n ok))
         :named hyp22))
(assert (! (not 
               (forall ((x60 N) (x61 N)) 
                   (not 
                       (MS0 x60 x61 f))))
         :named hyp23))
(assert (! (MS0 p t f)
         :named hyp24))
(assert (! (forall ((x62 N) (x63 N)) 
               (= 
                   (MS0 x62 x63 f) 
                   (and 
                       (= x62 p) 
                       (= x63 t))))
         :named hyp25))
(assert (! (forall ((x64 N)) 
               (= 
                   (or 
                       (exists ((x65 N)) 
                           (MS0 x64 x65 f)) 
                       (MS0 p x64 f)) 
                   (or 
                       (exists ((x66 N)) 
                           (MS0 x66 x64 f)) 
                       (= x64 p))))
         :named hyp26))
(assert (! (and 
               (forall ((x67 N) (x68 N)) 
                   (=> 
                       (MS0 x67 x68 f) 
                       (and 
                           (MS1 x67 b) 
                           (not 
                               (MS0 p x67 f)) 
                           (MS1 x68 b) 
                           (not 
                               (= x68 p))))) 
               (forall ((x69 N) (x70 N) (x71 N)) 
                   (=> 
                       (and 
                           (MS0 x69 x70 f) 
                           (MS0 x69 x71 f)) 
                       (= x70 x71))) 
               (forall ((x72 N) (x73 N) (x74 N)) 
                   (=> 
                       (and 
                           (MS0 x73 x72 f) 
                           (MS0 x74 x72 f)) 
                       (= x73 x74))))
         :named hyp27))
(assert (! (not 
               (MS0 p p f))
         :named hyp28))
(assert (! (forall ((x75 N) (x76 N)) 
               (= 
                   (MS0 x75 x76 f) 
                   (and 
                       (= x75 p) 
                       (MS0 p x76 f))))
         :named hyp29))
(assert (! (not 
               (forall ((x77 N)) 
                   (=> 
                       (exists ((x78 N)) 
                           (MS0 x77 x78 f)) 
                       (= x77 p))))
         :named goal))
(check-sat)
(exit)

