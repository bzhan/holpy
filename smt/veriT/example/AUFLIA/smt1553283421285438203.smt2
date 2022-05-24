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
(declare-fun MS0 (Int S PZS) Bool)
(declare-fun MS1 (S Int PSZ) Bool)
(declare-fun MS2 (S PS) Bool)
(declare-fun MS3 (S S Int PSSZ) Bool)
(declare-fun a0 (S S) Bool)
(declare-fun b (S PZS) Bool)
(declare-fun c (S S) Bool)
(declare-fun d (S S) Bool)
(declare-fun p (M S) Bool)
(declare-fun da () PS)
(declare-fun k () Int)
(declare-fun l () S)
(declare-fun n () Int)
(declare-fun n0 () Int)
(declare-fun r () PSZ)
(declare-fun s () S)
(declare-fun s0 () S)

; Elementary Sets axiom (Singleton part)
(assert (forall ((x143 S) (x144 Int)) 
            (exists ((X PSZ)) 
                (and 
                    (MS1 x143 x144 X) 
                    (forall ((y S) (y0 Int)) 
                        (=> 
                            (MS1 y y0 X) 
                            (and 
                                (= y x143) 
                                (= y0 x144))))))))
; Elementary Sets axiom (Singleton part)
(assert (forall ((x145 S)) 
            (exists ((X0 PS)) 
                (and 
                    (MS2 x145 X0) 
                    (forall ((y1 S)) 
                        (=> 
                            (MS2 y1 X0) 
                            (= y1 x145)))))))
; Elementary Sets axiom (Singleton part)
(assert (forall ((x146 Int) (x147 S)) 
            (exists ((X1 PZS)) 
                (and 
                    (MS0 x146 x147 X1) 
                    (forall ((y2 Int) (y3 S)) 
                        (=> 
                            (MS0 y2 y3 X1) 
                            (and 
                                (= y2 x146) 
                                (= y3 x147))))))))
; Elementary Sets axiom (Singleton part)
(assert (forall ((x148 S) (x149 S) (x150 Int)) 
            (exists ((X2 PSSZ)) 
                (and 
                    (MS3 x148 x149 x150 X2) 
                    (forall ((y4 S) (y5 S) (y6 Int)) 
                        (=> 
                            (MS3 y4 y5 y6 X2) 
                            (and 
                                (= y4 x148) 
                                (= y5 x149) 
                                (= y6 x150))))))))
(assert (! (exists ((x S) (x0 PZS)) 
               (and 
                   (b s x0) 
                   (MS0 n x x0)))
         :named hyp1))
(assert (! (forall ((x1 Int)) 
               (=> 
                   (MS1 s x1 r) 
                   (< x1 n)))
         :named hyp2))
(assert (! (forall ((s1 S) (n1 Int)) 
               (=> 
                   (and 
                       (exists ((x2 S) (x3 PZS)) 
                           (and 
                               (b s1 x3) 
                               (MS0 n1 x2 x3))) 
                       (forall ((x4 Int)) 
                           (=> 
                               (MS1 s1 x4 r) 
                               (< x4 n1)))) 
                   (and 
                       (exists ((x5 S) (x6 PZS)) 
                           (and 
                               (b s1 x6) 
                               (MS0 n1 x5 x6))) 
                       (forall ((x7 Int)) 
                           (=> 
                               (exists ((x8 S) (x9 PZS)) 
                                   (and 
                                       (b s1 x9) 
                                       (MS0 x7 x8 x9))) 
                               (<= x7 n1))))))
         :named hyp3))
(assert (! (not 
               (= s0 s))
         :named hyp4))
(assert (! (exists ((x10 S) (x11 PZS)) 
               (and 
                   (b s0 x11) 
                   (MS0 n0 x10 x11)))
         :named hyp5))
(assert (! (forall ((x12 Int)) 
               (=> 
                   (MS1 s0 x12 r) 
                   (< x12 n0)))
         :named hyp6))
(assert (! (forall ((a Int)) 
               (exists ((b0 Int) (f PSZ)) 
                   (and 
                       (forall ((x13 S) (x14 Int)) 
                           (=> 
                               (MS1 x13 x14 f) 
                               (and 
                                   (<= a x14) 
                                   (<= x14 b0)))) 
                       (forall ((x15 S) (x16 Int) (x17 Int)) 
                           (=> 
                               (and 
                                   (MS1 x15 x16 f) 
                                   (MS1 x15 x17 f)) 
                               (= x16 x17))) 
                       (forall ((x18 S)) 
                           (exists ((x19 Int)) 
                               (MS1 x18 x19 f))) 
                       (forall ((x20 Int) (x21 S) (x22 S)) 
                           (=> 
                               (and 
                                   (MS1 x21 x20 f) 
                                   (MS1 x22 x20 f)) 
                               (= x21 x22))))))
         :named hyp7))
(assert (! (and 
               (forall ((x23 S) (x24 S)) 
                   (=> 
                       (c x23 x24) 
                       (not 
                           (= x23 l)))) 
               (forall ((x25 S) (x26 S) (x27 S)) 
                   (=> 
                       (and 
                           (c x25 x26) 
                           (c x25 x27)) 
                       (= x26 x27))) 
               (forall ((x28 S)) 
                   (=> 
                       (not 
                           (= x28 l)) 
                       (exists ((x29 S)) 
                           (c x28 x29)))))
         :named hyp8))
(assert (! (forall ((x30 M) (x31 S) (x32 S)) 
               (=> 
                   (and 
                       (p x30 x31) 
                       (p x30 x32)) 
                   (= x31 x32)))
         :named hyp9))
(assert (! (and 
               (forall ((x33 S) (x34 S)) 
                   (=> 
                       (d x33 x34) 
                       (not 
                           (= x33 l)))) 
               (forall ((x35 S) (x36 S) (x37 S)) 
                   (=> 
                       (and 
                           (d x35 x36) 
                           (d x35 x37)) 
                       (= x36 x37))))
         :named hyp10))
(assert (! (and 
               (forall ((x38 S) (x39 S)) 
                   (=> 
                       (a0 x38 x39) 
                       (not 
                           (= x38 l)))) 
               (forall ((x40 S) (x41 S) (x42 S)) 
                   (=> 
                       (and 
                           (a0 x40 x41) 
                           (a0 x40 x42)) 
                       (= x41 x42))))
         :named hyp11))
(assert (! (forall ((x43 S) (x44 S)) 
               (= 
                   (c x43 x44) 
                   (or 
                       (and 
                           (d x43 x44) 
                           (not 
                               (exists ((x45 S)) 
                                   (a0 x43 x45)))) 
                       (a0 x43 x44))))
         :named hyp12))
(assert (! (forall ((x46 S)) 
               (= 
                   (exists ((x47 S)) 
                       (a0 x46 x47)) 
                   (and 
                       (MS2 x46 da) 
                       (not 
                           (= x46 l)))))
         :named hyp13))
(assert (! (forall ((a1 Int)) 
               (exists ((b1 Int) (f0 PSSZ)) 
                   (and 
                       (forall ((x48 S) (x49 S) (x50 Int)) 
                           (=> 
                               (MS3 x48 x49 x50 f0) 
                               (and 
                                   (a0 x48 x49) 
                                   (<= a1 x50) 
                                   (<= x50 b1)))) 
                       (forall ((x51 S) (x52 S) (x53 Int) (x54 Int)) 
                           (=> 
                               (and 
                                   (MS3 x51 x52 x53 f0) 
                                   (MS3 x51 x52 x54 f0)) 
                               (= x53 x54))) 
                       (forall ((x55 S) (x56 S)) 
                           (=> 
                               (a0 x55 x56) 
                               (exists ((x57 Int)) 
                                   (MS3 x55 x56 x57 f0)))) 
                       (forall ((x58 Int) (x59 S) (x60 S) (x61 S) (x62 S)) 
                           (=> 
                               (and 
                                   (MS3 x59 x60 x58 f0) 
                                   (MS3 x61 x62 x58 f0)) 
                               (and 
                                   (= x59 x61) 
                                   (= x60 x62)))))))
         :named hyp14))
(assert (! (and 
               (forall ((x63 S) (x64 Int)) 
                   (=> 
                       (MS1 x63 x64 r) 
                       (<= 0 x64))) 
               (forall ((x65 S) (x66 Int) (x67 Int)) 
                   (=> 
                       (and 
                           (MS1 x65 x66 r) 
                           (MS1 x65 x67 r)) 
                       (= x66 x67))) 
               (forall ((x68 S)) 
                   (exists ((x69 Int)) 
                       (MS1 x68 x69 r))))
         :named hyp15))
(assert (! (and 
               (forall ((x70 S) (x71 PZS)) 
                   (=> 
                       (b x70 x71) 
                       (and 
                           (forall ((x72 Int) (x73 S)) 
                               (=> 
                                   (MS0 x72 x73 x71) 
                                   (<= 0 x72))) 
                           (forall ((x74 Int) (x75 S) (x76 S)) 
                               (=> 
                                   (and 
                                       (MS0 x74 x75 x71) 
                                       (MS0 x74 x76 x71)) 
                                   (= x75 x76)))))) 
               (forall ((x77 S) (x78 PZS) (x79 PZS)) 
                   (=> 
                       (and 
                           (b x77 x78) 
                           (b x77 x79)) 
                       (forall ((x80 Int) (x81 S)) 
                           (= 
                               (MS0 x80 x81 x78) 
                               (MS0 x80 x81 x79))))) 
               (forall ((x82 S)) 
                   (exists ((x83 PZS)) 
                       (b x82 x83))))
         :named hyp16))
(assert (! (forall ((s2 S)) 
               (=> 
                   (exists ((x84 S)) 
                       (a0 s2 x84)) 
                   (exists ((x85 S)) 
                       (and 
                           (exists ((x86 PZS)) 
                               (and 
                                   (b s2 x86) 
                                   (exists ((x87 Int)) 
                                       (and 
                                           (exists ((x88 S) (x89 PZS)) 
                                               (and 
                                                   (b s2 x89) 
                                                   (MS0 x87 x88 x89))) 
                                           (forall ((x90 Int)) 
                                               (=> 
                                                   (exists ((x91 S) (x92 PZS)) 
                                                       (and 
                                                           (b s2 x92) 
                                                           (MS0 x90 x91 x92))) 
                                                   (<= x90 x87))) 
                                           (MS0 x87 x85 x86))))) 
                           (a0 s2 x85)))))
         :named hyp17))
(assert (! (MS1 l k r)
         :named hyp18))
(assert (! (exists ((x93 Int)) 
               (MS1 l x93 r))
         :named hyp19))
(assert (! (forall ((x94 S) (x95 Int) (x96 Int)) 
               (=> 
                   (and 
                       (MS1 x94 x95 r) 
                       (MS1 x94 x96 r)) 
                   (= x95 x96)))
         :named hyp20))
(assert (! (forall ((s3 S)) 
               (=> 
                   (exists ((x97 S)) 
                       (a0 s3 x97)) 
                   (exists ((x98 Int)) 
                       (and 
                           (exists ((x99 S) (x100 PZS)) 
                               (and 
                                   (b s3 x100) 
                                   (MS0 x98 x99 x100))) 
                           (forall ((x101 Int)) 
                               (=> 
                                   (MS1 s3 x101 r) 
                                   (< x101 x98)))))))
         :named hyp21))
(assert (! (forall ((s4 S) (x102 Int)) 
               (=> 
                   (MS1 s4 x102 r) 
                   (<= x102 k)))
         :named hyp22))
(assert (! (exists ((x103 PZS)) 
               (b s x103))
         :named hyp23))
(assert (! (forall ((x104 S) (x105 PZS) (x106 PZS)) 
               (=> 
                   (and 
                       (b x104 x105) 
                       (b x104 x106)) 
                   (forall ((x107 Int) (x108 S)) 
                       (= 
                           (MS0 x107 x108 x105) 
                           (MS0 x107 x108 x106)))))
         :named hyp24))
(assert (! (exists ((x109 Int)) 
               (MS1 s x109 r))
         :named hyp25))
(assert (! (forall ((s5 S)) 
               (=> 
                   (exists ((x110 S)) 
                       (a0 s5 x110)) 
                   (not 
                       (exists ((x111 PZS)) 
                           (and 
                               (forall ((x112 Int) (x113 S)) 
                                   (not 
                                       (MS0 x112 x113 x111))) 
                               (b s5 x111))))))
         :named hyp26))
(assert (! (forall ((s6 S)) 
               (not 
                   (exists ((x114 S) (x115 PZS)) 
                       (and 
                           (b s6 x115) 
                           (exists ((x116 Int)) 
                               (and 
                                   (MS1 s6 x116 r) 
                                   (MS0 x116 x114 x115)))))))
         :named hyp27))
(assert (! (forall ((U PS)) 
               (=> 
                   (forall ((x117 S)) 
                       (=> 
                           (MS2 x117 U) 
                           (exists ((x118 S)) 
                               (and 
                                   (MS2 x118 U) 
                                   (c x117 x118))))) 
                   (forall ((x119 S)) 
                       (not 
                           (MS2 x119 U)))))
         :named hyp28))
(assert (! (forall ((s7 S) (x120 Int)) 
               (=> 
                   (exists ((x121 S) (x122 PZS)) 
                       (and 
                           (b s7 x122) 
                           (MS0 x120 x121 x122))) 
                   (and 
                       (<= 0 x120) 
                       (<= x120 k))))
         :named hyp29))
(assert (! (forall ((s8 S)) 
               (=> 
                   (and 
                       (not 
                           (exists ((x123 PZS)) 
                               (and 
                                   (forall ((x124 Int) (x125 S)) 
                                       (not 
                                           (MS0 x124 x125 x123))) 
                                   (b s8 x123)))) 
                       (exists ((x126 Int)) 
                           (and 
                               (exists ((x127 S) (x128 PZS)) 
                                   (and 
                                       (b s8 x128) 
                                       (MS0 x126 x127 x128))) 
                               (forall ((x129 Int)) 
                                   (=> 
                                       (MS1 s8 x129 r) 
                                       (< x129 x126)))))) 
                   (exists ((x130 S)) 
                       (a0 s8 x130))))
         :named hyp30))
(assert (! (forall ((s9 S)) 
               (=> 
                   (not 
                       (= s9 l)) 
                   (forall ((x131 Int)) 
                       (=> 
                           (MS1 s9 x131 r) 
                           (<= x131 k)))))
         :named hyp31))
(assert (! (forall ((s10 S)) 
               (=> 
                   (not 
                       (exists ((x132 PZS)) 
                           (and 
                               (forall ((x133 Int) (x134 S)) 
                                   (not 
                                       (MS0 x133 x134 x132))) 
                               (b s10 x132)))) 
                   (forall ((x135 Int)) 
                       (=> 
                           (exists ((x136 S) (x137 PZS)) 
                               (and 
                                   (b s10 x137) 
                                   (MS0 x135 x136 x137))) 
                           (<= x135 k)))))
         :named hyp32))
(assert (! (not 
               (and 
                   (exists ((x138 S) (x139 PZS)) 
                       (and 
                           (b s0 x139) 
                           (MS0 n0 x138 x139))) 
                   (forall ((x140 Int)) 
                       (=> 
                           (exists ((x141 S) (x142 PZS)) 
                               (and 
                                   (b s0 x142) 
                                   (MS0 x140 x141 x142))) 
                           (<= x140 n0)))))
         :named goal))
(check-sat)
(exit)

