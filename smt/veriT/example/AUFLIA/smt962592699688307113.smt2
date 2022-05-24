(set-info :smt-lib-version 2.6)
(set-logic AUFLIA)
(set-info :source |Generator: Rodin SMT Plug-in|)
(set-info :license "https://creativecommons.org/licenses/by-nc/4.0/")
(set-info :category "industrial")
(set-info :status unsat)

(declare-sort M 0)
(declare-sort PS 0)
(declare-sort PSSZ 0)
(declare-sort PSZ 0)
(declare-sort PZS 0)
(declare-sort S 0)
(declare-fun DA (S Bool) Bool)
(declare-fun MS0 (S Int PSZ) Bool)
(declare-fun MS1 (S PS) Bool)
(declare-fun MS2 (S S Int PSSZ) Bool)
(declare-fun MS3 (Int S PZS) Bool)
(declare-fun a0 (S S) Bool)
(declare-fun b1 (S PZS) Bool)
(declare-fun c (S S) Bool)
(declare-fun d (S S) Bool)
(declare-fun p (M S) Bool)
(declare-fun da () PS)
(declare-fun k () Int)
(declare-fun l () S)
(declare-fun r () PSZ)

; Elementary Sets axiom (Singleton part)
(assert (forall ((x139 S) (x140 Int)) 
            (exists ((X PSZ)) 
                (and 
                    (MS0 x139 x140 X) 
                    (forall ((y S) (y0 Int)) 
                        (=> 
                            (MS0 y y0 X) 
                            (and 
                                (= y x139) 
                                (= y0 x140))))))))
; Elementary Sets axiom (Singleton part)
(assert (forall ((x141 S)) 
            (exists ((X0 PS)) 
                (and 
                    (MS1 x141 X0) 
                    (forall ((y1 S)) 
                        (=> 
                            (MS1 y1 X0) 
                            (= y1 x141)))))))
; Elementary Sets axiom (Singleton part)
(assert (forall ((x142 Int) (x143 S)) 
            (exists ((X1 PZS)) 
                (and 
                    (MS3 x142 x143 X1) 
                    (forall ((y2 Int) (y3 S)) 
                        (=> 
                            (MS3 y2 y3 X1) 
                            (and 
                                (= y2 x142) 
                                (= y3 x143))))))))
; Elementary Sets axiom (Singleton part)
(assert (forall ((x144 S) (x145 S) (x146 Int)) 
            (exists ((X2 PSSZ)) 
                (and 
                    (MS2 x144 x145 x146 X2) 
                    (forall ((y4 S) (y5 S) (y6 Int)) 
                        (=> 
                            (MS2 y4 y5 y6 X2) 
                            (and 
                                (= y4 x144) 
                                (= y5 x145) 
                                (= y6 x146))))))))
(assert (! (not 
               (exists ((x Bool)) 
                   (and 
                       x 
                       (DA l x))))
         :named hyp1))
(assert (! (forall ((a Int)) 
               (exists ((b Int) (f PSZ)) 
                   (and 
                       (forall ((x0 S) (x1 Int)) 
                           (=> 
                               (MS0 x0 x1 f) 
                               (and 
                                   (<= a x1) 
                                   (<= x1 b)))) 
                       (forall ((x2 S) (x3 Int) (x4 Int)) 
                           (=> 
                               (and 
                                   (MS0 x2 x3 f) 
                                   (MS0 x2 x4 f)) 
                               (= x3 x4))) 
                       (forall ((x5 S)) 
                           (exists ((x6 Int)) 
                               (MS0 x5 x6 f))) 
                       (forall ((x7 Int) (x8 S) (x9 S)) 
                           (=> 
                               (and 
                                   (MS0 x8 x7 f) 
                                   (MS0 x9 x7 f)) 
                               (= x8 x9))))))
         :named hyp2))
(assert (! (and 
               (forall ((x10 S) (x11 S)) 
                   (=> 
                       (c x10 x11) 
                       (not 
                           (= x10 l)))) 
               (forall ((x12 S) (x13 S) (x14 S)) 
                   (=> 
                       (and 
                           (c x12 x13) 
                           (c x12 x14)) 
                       (= x13 x14))) 
               (forall ((x15 S)) 
                   (=> 
                       (not 
                           (= x15 l)) 
                       (exists ((x16 S)) 
                           (c x15 x16)))))
         :named hyp3))
(assert (! (forall ((x17 M) (x18 S) (x19 S)) 
               (=> 
                   (and 
                       (p x17 x18) 
                       (p x17 x19)) 
                   (= x18 x19)))
         :named hyp4))
(assert (! (and 
               (forall ((x20 S) (x21 S)) 
                   (=> 
                       (d x20 x21) 
                       (not 
                           (= x20 l)))) 
               (forall ((x22 S) (x23 S) (x24 S)) 
                   (=> 
                       (and 
                           (d x22 x23) 
                           (d x22 x24)) 
                       (= x23 x24))))
         :named hyp5))
(assert (! (and 
               (forall ((x25 S) (x26 S)) 
                   (=> 
                       (a0 x25 x26) 
                       (not 
                           (= x25 l)))) 
               (forall ((x27 S) (x28 S) (x29 S)) 
                   (=> 
                       (and 
                           (a0 x27 x28) 
                           (a0 x27 x29)) 
                       (= x28 x29))))
         :named hyp6))
(assert (! (forall ((x30 S) (x31 S)) 
               (= 
                   (c x30 x31) 
                   (or 
                       (and 
                           (d x30 x31) 
                           (not 
                               (exists ((x32 S)) 
                                   (a0 x30 x32)))) 
                       (a0 x30 x31))))
         :named hyp7))
(assert (! (forall ((x33 S)) 
               (= 
                   (exists ((x34 S)) 
                       (a0 x33 x34)) 
                   (and 
                       (MS1 x33 da) 
                       (not 
                           (= x33 l)))))
         :named hyp8))
(assert (! (forall ((a1 Int)) 
               (exists ((b0 Int) (f0 PSSZ)) 
                   (and 
                       (forall ((x35 S) (x36 S) (x37 Int)) 
                           (=> 
                               (MS2 x35 x36 x37 f0) 
                               (and 
                                   (a0 x35 x36) 
                                   (<= a1 x37) 
                                   (<= x37 b0)))) 
                       (forall ((x38 S) (x39 S) (x40 Int) (x41 Int)) 
                           (=> 
                               (and 
                                   (MS2 x38 x39 x40 f0) 
                                   (MS2 x38 x39 x41 f0)) 
                               (= x40 x41))) 
                       (forall ((x42 S) (x43 S)) 
                           (=> 
                               (a0 x42 x43) 
                               (exists ((x44 Int)) 
                                   (MS2 x42 x43 x44 f0)))) 
                       (forall ((x45 Int) (x46 S) (x47 S) (x48 S) (x49 S)) 
                           (=> 
                               (and 
                                   (MS2 x46 x47 x45 f0) 
                                   (MS2 x48 x49 x45 f0)) 
                               (and 
                                   (= x46 x48) 
                                   (= x47 x49)))))))
         :named hyp9))
(assert (! (and 
               (forall ((x50 S) (x51 Int)) 
                   (=> 
                       (MS0 x50 x51 r) 
                       (<= 0 x51))) 
               (forall ((x52 S) (x53 Int) (x54 Int)) 
                   (=> 
                       (and 
                           (MS0 x52 x53 r) 
                           (MS0 x52 x54 r)) 
                       (= x53 x54))) 
               (forall ((x55 S)) 
                   (exists ((x56 Int)) 
                       (MS0 x55 x56 r))))
         :named hyp10))
(assert (! (and 
               (forall ((x57 S) (x58 PZS)) 
                   (=> 
                       (b1 x57 x58) 
                       (and 
                           (forall ((x59 Int) (x60 S)) 
                               (=> 
                                   (MS3 x59 x60 x58) 
                                   (<= 0 x59))) 
                           (forall ((x61 Int) (x62 S) (x63 S)) 
                               (=> 
                                   (and 
                                       (MS3 x61 x62 x58) 
                                       (MS3 x61 x63 x58)) 
                                   (= x62 x63)))))) 
               (forall ((x64 S) (x65 PZS) (x66 PZS)) 
                   (=> 
                       (and 
                           (b1 x64 x65) 
                           (b1 x64 x66)) 
                       (forall ((x67 Int) (x68 S)) 
                           (= 
                               (MS3 x67 x68 x65) 
                               (MS3 x67 x68 x66))))) 
               (forall ((x69 S)) 
                   (exists ((x70 PZS)) 
                       (b1 x69 x70))))
         :named hyp11))
(assert (! (forall ((s S)) 
               (=> 
                   (exists ((x71 S)) 
                       (a0 s x71)) 
                   (exists ((x72 S)) 
                       (and 
                           (exists ((x73 PZS)) 
                               (and 
                                   (b1 s x73) 
                                   (exists ((x74 Int)) 
                                       (and 
                                           (exists ((x75 S) (x76 PZS)) 
                                               (and 
                                                   (b1 s x76) 
                                                   (MS3 x74 x75 x76))) 
                                           (forall ((x77 Int)) 
                                               (=> 
                                                   (exists ((x78 S) (x79 PZS)) 
                                                       (and 
                                                           (b1 s x79) 
                                                           (MS3 x77 x78 x79))) 
                                                   (<= x77 x74))) 
                                           (MS3 x74 x72 x73))))) 
                           (a0 s x72)))))
         :named hyp12))
(assert (! (MS0 l k r)
         :named hyp13))
(assert (! (exists ((x80 Int)) 
               (MS0 l x80 r))
         :named hyp14))
(assert (! (forall ((x81 S) (x82 Int) (x83 Int)) 
               (=> 
                   (and 
                       (MS0 x81 x82 r) 
                       (MS0 x81 x83 r)) 
                   (= x82 x83)))
         :named hyp15))
(assert (! (forall ((s0 S)) 
               (=> 
                   (exists ((x84 S)) 
                       (a0 s0 x84)) 
                   (exists ((x85 Int)) 
                       (and 
                           (exists ((x86 S) (x87 PZS)) 
                               (and 
                                   (b1 s0 x87) 
                                   (MS3 x85 x86 x87))) 
                           (forall ((x88 Int)) 
                               (=> 
                                   (MS0 s0 x88 r) 
                                   (< x88 x85)))))))
         :named hyp16))
(assert (! (forall ((s1 S) (x89 Int)) 
               (=> 
                   (MS0 s1 x89 r) 
                   (<= x89 k)))
         :named hyp17))
(assert (! (and 
               (forall ((x90 S) (x91 Bool) (x92 Bool)) 
                   (=> 
                       (and 
                           (DA x90 x91) 
                           (DA x90 x92)) 
                       (= 
                           x91 
                           x92))) 
               (forall ((x93 S)) 
                   (exists ((x94 Bool)) 
                       (DA x93 x94))))
         :named hyp18))
(assert (! (exists ((x95 Bool)) 
               (DA l x95))
         :named hyp19))
(assert (! (forall ((x96 S) (x97 Bool) (x98 Bool)) 
               (=> 
                   (and 
                       (DA x96 x97) 
                       (DA x96 x98)) 
                   (= 
                       x97 
                       x98)))
         :named hyp20))
(assert (! (forall ((s2 S)) 
               (=> 
                   (exists ((x99 S)) 
                       (a0 s2 x99)) 
                   (not 
                       (exists ((x100 PZS)) 
                           (and 
                               (forall ((x101 Int) (x102 S)) 
                                   (not 
                                       (MS3 x101 x102 x100))) 
                               (b1 s2 x100))))))
         :named hyp21))
(assert (! (forall ((s3 S)) 
               (not 
                   (exists ((x103 S) (x104 PZS)) 
                       (and 
                           (b1 s3 x104) 
                           (exists ((x105 Int)) 
                               (and 
                                   (MS0 s3 x105 r) 
                                   (MS3 x105 x103 x104)))))))
         :named hyp22))
(assert (! (forall ((U PS)) 
               (=> 
                   (forall ((x106 S)) 
                       (=> 
                           (MS1 x106 U) 
                           (exists ((x107 S)) 
                               (and 
                                   (MS1 x107 U) 
                                   (c x106 x107))))) 
                   (forall ((x108 S)) 
                       (not 
                           (MS1 x108 U)))))
         :named hyp23))
(assert (! (forall ((s4 S) (x109 Int)) 
               (=> 
                   (exists ((x110 S) (x111 PZS)) 
                       (and 
                           (b1 s4 x111) 
                           (MS3 x109 x110 x111))) 
                   (and 
                       (<= 0 x109) 
                       (<= x109 k))))
         :named hyp24))
(assert (! (forall ((s5 S) (n Int)) 
               (=> 
                   (and 
                       (exists ((x112 S) (x113 PZS)) 
                           (and 
                               (b1 s5 x113) 
                               (MS3 n x112 x113))) 
                       (forall ((x114 Int)) 
                           (=> 
                               (MS0 s5 x114 r) 
                               (< x114 n)))) 
                   (and 
                       (exists ((x115 S) (x116 PZS)) 
                           (and 
                               (b1 s5 x116) 
                               (MS3 n x115 x116))) 
                       (forall ((x117 Int)) 
                           (=> 
                               (exists ((x118 S) (x119 PZS)) 
                                   (and 
                                       (b1 s5 x119) 
                                       (MS3 x117 x118 x119))) 
                               (<= x117 n))))))
         :named hyp25))
(assert (! (forall ((x120 S)) 
               (=> 
                   (MS1 x120 da) 
                   (exists ((x121 Bool)) 
                       (and 
                           x121 
                           (DA x120 x121)))))
         :named hyp26))
(assert (! (forall ((x122 S)) 
               (=> 
                   (exists ((x123 Bool)) 
                       (and 
                           x123 
                           (DA x122 x123))) 
                   (MS1 x122 da)))
         :named hyp27))
(assert (! (forall ((s6 S)) 
               (=> 
                   (and 
                       (not 
                           (exists ((x124 PZS)) 
                               (and 
                                   (forall ((x125 Int) (x126 S)) 
                                       (not 
                                           (MS3 x125 x126 x124))) 
                                   (b1 s6 x124)))) 
                       (exists ((x127 Int)) 
                           (and 
                               (exists ((x128 S) (x129 PZS)) 
                                   (and 
                                       (b1 s6 x129) 
                                       (MS3 x127 x128 x129))) 
                               (forall ((x130 Int)) 
                                   (=> 
                                       (MS0 s6 x130 r) 
                                       (< x130 x127)))))) 
                   (exists ((x131 S)) 
                       (a0 s6 x131))))
         :named hyp28))
(assert (! (forall ((s7 S)) 
               (=> 
                   (not 
                       (= s7 l)) 
                   (forall ((x132 Int)) 
                       (=> 
                           (MS0 s7 x132 r) 
                           (<= x132 k)))))
         :named hyp29))
(assert (! (forall ((s8 S)) 
               (=> 
                   (not 
                       (exists ((x133 PZS)) 
                           (and 
                               (forall ((x134 Int) (x135 S)) 
                                   (not 
                                       (MS3 x134 x135 x133))) 
                               (b1 s8 x133)))) 
                   (forall ((x136 Int)) 
                       (=> 
                           (exists ((x137 S) (x138 PZS)) 
                               (and 
                                   (b1 s8 x138) 
                                   (MS3 x136 x137 x138))) 
                           (<= x136 k)))))
         :named hyp30))
(assert (! (not 
               (not 
                   (MS1 l da)))
         :named goal))
(check-sat)
(exit)

