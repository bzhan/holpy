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
(declare-fun n () Int)
(declare-fun r () PSZ)
(declare-fun s () S)

; Elementary Sets axiom (Singleton part)
(assert (forall ((x153 S) (x154 Int)) 
            (exists ((X PSZ)) 
                (and 
                    (MS0 x153 x154 X) 
                    (forall ((y S) (y0 Int)) 
                        (=> 
                            (MS0 y y0 X) 
                            (and 
                                (= y x153) 
                                (= y0 x154))))))))
; Elementary Sets axiom (Singleton part)
(assert (forall ((x155 S)) 
            (exists ((X0 PS)) 
                (and 
                    (MS1 x155 X0) 
                    (forall ((y1 S)) 
                        (=> 
                            (MS1 y1 X0) 
                            (= y1 x155)))))))
; Elementary Sets axiom (Singleton part)
(assert (forall ((x156 Int) (x157 S)) 
            (exists ((X1 PZS)) 
                (and 
                    (MS3 x156 x157 X1) 
                    (forall ((y2 Int) (y3 S)) 
                        (=> 
                            (MS3 y2 y3 X1) 
                            (and 
                                (= y2 x156) 
                                (= y3 x157))))))))
; Elementary Sets axiom (Singleton part)
(assert (forall ((x158 S) (x159 S) (x160 Int)) 
            (exists ((X2 PSSZ)) 
                (and 
                    (MS2 x158 x159 x160 X2) 
                    (forall ((y4 S) (y5 S) (y6 Int)) 
                        (=> 
                            (MS2 y4 y5 y6 X2) 
                            (and 
                                (= y4 x158) 
                                (= y5 x159) 
                                (= y6 x160))))))))
(assert (! (forall ((a Int)) 
               (exists ((b Int) (f PSZ)) 
                   (and 
                       (forall ((x S) (x0 Int)) 
                           (=> 
                               (MS0 x x0 f) 
                               (and 
                                   (<= a x0) 
                                   (<= x0 b)))) 
                       (forall ((x1 S) (x2 Int) (x3 Int)) 
                           (=> 
                               (and 
                                   (MS0 x1 x2 f) 
                                   (MS0 x1 x3 f)) 
                               (= x2 x3))) 
                       (forall ((x4 S)) 
                           (exists ((x5 Int)) 
                               (MS0 x4 x5 f))) 
                       (forall ((x6 Int) (x7 S) (x8 S)) 
                           (=> 
                               (and 
                                   (MS0 x7 x6 f) 
                                   (MS0 x8 x6 f)) 
                               (= x7 x8))))))
         :named hyp1))
(assert (! (and 
               (forall ((x9 S) (x10 S)) 
                   (=> 
                       (c x9 x10) 
                       (not 
                           (= x9 l)))) 
               (forall ((x11 S) (x12 S) (x13 S)) 
                   (=> 
                       (and 
                           (c x11 x12) 
                           (c x11 x13)) 
                       (= x12 x13))) 
               (forall ((x14 S)) 
                   (=> 
                       (not 
                           (= x14 l)) 
                       (exists ((x15 S)) 
                           (c x14 x15)))))
         :named hyp2))
(assert (! (forall ((x16 M) (x17 S) (x18 S)) 
               (=> 
                   (and 
                       (p x16 x17) 
                       (p x16 x18)) 
                   (= x17 x18)))
         :named hyp3))
(assert (! (and 
               (forall ((x19 S) (x20 S)) 
                   (=> 
                       (d x19 x20) 
                       (not 
                           (= x19 l)))) 
               (forall ((x21 S) (x22 S) (x23 S)) 
                   (=> 
                       (and 
                           (d x21 x22) 
                           (d x21 x23)) 
                       (= x22 x23))))
         :named hyp4))
(assert (! (and 
               (forall ((x24 S) (x25 S)) 
                   (=> 
                       (a0 x24 x25) 
                       (not 
                           (= x24 l)))) 
               (forall ((x26 S) (x27 S) (x28 S)) 
                   (=> 
                       (and 
                           (a0 x26 x27) 
                           (a0 x26 x28)) 
                       (= x27 x28))))
         :named hyp5))
(assert (! (forall ((x29 S) (x30 S)) 
               (= 
                   (c x29 x30) 
                   (or 
                       (and 
                           (d x29 x30) 
                           (not 
                               (exists ((x31 S)) 
                                   (a0 x29 x31)))) 
                       (a0 x29 x30))))
         :named hyp6))
(assert (! (forall ((x32 S)) 
               (= 
                   (exists ((x33 S)) 
                       (a0 x32 x33)) 
                   (and 
                       (MS1 x32 da) 
                       (not 
                           (= x32 l)))))
         :named hyp7))
(assert (! (forall ((a1 Int)) 
               (exists ((b0 Int) (f0 PSSZ)) 
                   (and 
                       (forall ((x34 S) (x35 S) (x36 Int)) 
                           (=> 
                               (MS2 x34 x35 x36 f0) 
                               (and 
                                   (a0 x34 x35) 
                                   (<= a1 x36) 
                                   (<= x36 b0)))) 
                       (forall ((x37 S) (x38 S) (x39 Int) (x40 Int)) 
                           (=> 
                               (and 
                                   (MS2 x37 x38 x39 f0) 
                                   (MS2 x37 x38 x40 f0)) 
                               (= x39 x40))) 
                       (forall ((x41 S) (x42 S)) 
                           (=> 
                               (a0 x41 x42) 
                               (exists ((x43 Int)) 
                                   (MS2 x41 x42 x43 f0)))) 
                       (forall ((x44 Int) (x45 S) (x46 S) (x47 S) (x48 S)) 
                           (=> 
                               (and 
                                   (MS2 x45 x46 x44 f0) 
                                   (MS2 x47 x48 x44 f0)) 
                               (and 
                                   (= x45 x47) 
                                   (= x46 x48)))))))
         :named hyp8))
(assert (! (<= 0 k)
         :named hyp9))
(assert (! (and 
               (forall ((x49 S) (x50 Int)) 
                   (=> 
                       (MS0 x49 x50 r) 
                       (<= 0 x50))) 
               (forall ((x51 S) (x52 Int) (x53 Int)) 
                   (=> 
                       (and 
                           (MS0 x51 x52 r) 
                           (MS0 x51 x53 r)) 
                       (= x52 x53))) 
               (forall ((x54 S)) 
                   (exists ((x55 Int)) 
                       (MS0 x54 x55 r))))
         :named hyp10))
(assert (! (and 
               (forall ((x56 S) (x57 PZS)) 
                   (=> 
                       (b1 x56 x57) 
                       (and 
                           (forall ((x58 Int) (x59 S)) 
                               (=> 
                                   (MS3 x58 x59 x57) 
                                   (<= 0 x58))) 
                           (forall ((x60 Int) (x61 S) (x62 S)) 
                               (=> 
                                   (and 
                                       (MS3 x60 x61 x57) 
                                       (MS3 x60 x62 x57)) 
                                   (= x61 x62)))))) 
               (forall ((x63 S) (x64 PZS) (x65 PZS)) 
                   (=> 
                       (and 
                           (b1 x63 x64) 
                           (b1 x63 x65)) 
                       (forall ((x66 Int) (x67 S)) 
                           (= 
                               (MS3 x66 x67 x64) 
                               (MS3 x66 x67 x65))))) 
               (forall ((x68 S)) 
                   (exists ((x69 PZS)) 
                       (b1 x68 x69))))
         :named hyp11))
(assert (! (forall ((s0 S)) 
               (=> 
                   (exists ((x70 S)) 
                       (a0 s0 x70)) 
                   (exists ((x71 S)) 
                       (and 
                           (exists ((x72 PZS)) 
                               (and 
                                   (b1 s0 x72) 
                                   (exists ((x73 Int)) 
                                       (and 
                                           (exists ((x74 S) (x75 PZS)) 
                                               (and 
                                                   (b1 s0 x75) 
                                                   (MS3 x73 x74 x75))) 
                                           (forall ((x76 Int)) 
                                               (=> 
                                                   (exists ((x77 S) (x78 PZS)) 
                                                       (and 
                                                           (b1 s0 x78) 
                                                           (MS3 x76 x77 x78))) 
                                                   (<= x76 x73))) 
                                           (MS3 x73 x71 x72))))) 
                           (a0 s0 x71)))))
         :named hyp12))
(assert (! (MS0 l k r)
         :named hyp13))
(assert (! (exists ((x79 Int)) 
               (MS0 l x79 r))
         :named hyp14))
(assert (! (forall ((x80 S) (x81 Int) (x82 Int)) 
               (=> 
                   (and 
                       (MS0 x80 x81 r) 
                       (MS0 x80 x82 r)) 
                   (= x81 x82)))
         :named hyp15))
(assert (! (forall ((s1 S)) 
               (=> 
                   (exists ((x83 S)) 
                       (a0 s1 x83)) 
                   (exists ((x84 Int)) 
                       (and 
                           (exists ((x85 S) (x86 PZS)) 
                               (and 
                                   (b1 s1 x86) 
                                   (MS3 x84 x85 x86))) 
                           (forall ((x87 Int)) 
                               (=> 
                                   (MS0 s1 x87 r) 
                                   (< x87 x84)))))))
         :named hyp16))
(assert (! (forall ((s2 S) (x88 Int)) 
               (=> 
                   (MS0 s2 x88 r) 
                   (<= x88 k)))
         :named hyp17))
(assert (! (and 
               (forall ((x89 S) (x90 Bool) (x91 Bool)) 
                   (=> 
                       (and 
                           (DA x89 x90) 
                           (DA x89 x91)) 
                       (= 
                           x90 
                           x91))) 
               (forall ((x92 S)) 
                   (exists ((x93 Bool)) 
                       (DA x92 x93))))
         :named hyp18))
(assert (! (exists ((x94 S) (x95 PZS)) 
               (and 
                   (b1 s x95) 
                   (MS3 n x94 x95)))
         :named hyp19))
(assert (! (exists ((x96 PZS)) 
               (b1 s x96))
         :named hyp20))
(assert (! (forall ((x97 S) (x98 PZS) (x99 PZS)) 
               (=> 
                   (and 
                       (b1 x97 x98) 
                       (b1 x97 x99)) 
                   (forall ((x100 Int) (x101 S)) 
                       (= 
                           (MS3 x100 x101 x98) 
                           (MS3 x100 x101 x99)))))
         :named hyp21))
(assert (! (forall ((x102 Int)) 
               (=> 
                   (MS0 s x102 r) 
                   (< x102 n)))
         :named hyp22))
(assert (! (exists ((x103 Int)) 
               (MS0 s x103 r))
         :named hyp23))
(assert (! (forall ((s3 S)) 
               (=> 
                   (exists ((x104 S)) 
                       (a0 s3 x104)) 
                   (not 
                       (exists ((x105 PZS)) 
                           (and 
                               (forall ((x106 Int) (x107 S)) 
                                   (not 
                                       (MS3 x106 x107 x105))) 
                               (b1 s3 x105))))))
         :named hyp24))
(assert (! (forall ((s4 S)) 
               (not 
                   (exists ((x108 S) (x109 PZS)) 
                       (and 
                           (b1 s4 x109) 
                           (exists ((x110 Int)) 
                               (and 
                                   (MS0 s4 x110 r) 
                                   (MS3 x110 x108 x109)))))))
         :named hyp25))
(assert (! (forall ((U PS)) 
               (=> 
                   (forall ((x111 S)) 
                       (=> 
                           (MS1 x111 U) 
                           (exists ((x112 S)) 
                               (and 
                                   (MS1 x112 U) 
                                   (c x111 x112))))) 
                   (forall ((x113 S)) 
                       (not 
                           (MS1 x113 U)))))
         :named hyp26))
(assert (! (forall ((s5 S) (x114 Int)) 
               (=> 
                   (exists ((x115 S) (x116 PZS)) 
                       (and 
                           (b1 s5 x116) 
                           (MS3 x114 x115 x116))) 
                   (and 
                       (<= 0 x114) 
                       (<= x114 k))))
         :named hyp27))
(assert (! (forall ((s6 S) (n0 Int)) 
               (=> 
                   (and 
                       (exists ((x117 S) (x118 PZS)) 
                           (and 
                               (b1 s6 x118) 
                               (MS3 n0 x117 x118))) 
                       (forall ((x119 Int)) 
                           (=> 
                               (MS0 s6 x119 r) 
                               (< x119 n0)))) 
                   (and 
                       (exists ((x120 S) (x121 PZS)) 
                           (and 
                               (b1 s6 x121) 
                               (MS3 n0 x120 x121))) 
                       (forall ((x122 Int)) 
                           (=> 
                               (exists ((x123 S) (x124 PZS)) 
                                   (and 
                                       (b1 s6 x124) 
                                       (MS3 x122 x123 x124))) 
                               (<= x122 n0))))))
         :named hyp28))
(assert (! (forall ((x125 S)) 
               (=> 
                   (MS1 x125 da) 
                   (exists ((x126 Bool)) 
                       (and 
                           x126 
                           (DA x125 x126)))))
         :named hyp29))
(assert (! (forall ((x127 S)) 
               (=> 
                   (exists ((x128 Bool)) 
                       (and 
                           x128 
                           (DA x127 x128))) 
                   (MS1 x127 da)))
         :named hyp30))
(assert (! (forall ((s7 S)) 
               (=> 
                   (and 
                       (not 
                           (exists ((x129 PZS)) 
                               (and 
                                   (forall ((x130 Int) (x131 S)) 
                                       (not 
                                           (MS3 x130 x131 x129))) 
                                   (b1 s7 x129)))) 
                       (exists ((x132 Int)) 
                           (and 
                               (exists ((x133 S) (x134 PZS)) 
                                   (and 
                                       (b1 s7 x134) 
                                       (MS3 x132 x133 x134))) 
                               (forall ((x135 Int)) 
                                   (=> 
                                       (MS0 s7 x135 r) 
                                       (< x135 x132)))))) 
                   (exists ((x136 S)) 
                       (a0 s7 x136))))
         :named hyp31))
(assert (! (forall ((s8 S)) 
               (=> 
                   (not 
                       (= s8 l)) 
                   (forall ((x137 Int)) 
                       (=> 
                           (MS0 s8 x137 r) 
                           (<= x137 k)))))
         :named hyp32))
(assert (! (forall ((s9 S)) 
               (=> 
                   (not 
                       (exists ((x138 PZS)) 
                           (and 
                               (forall ((x139 Int) (x140 S)) 
                                   (not 
                                       (MS3 x139 x140 x138))) 
                               (b1 s9 x138)))) 
                   (forall ((x141 Int)) 
                       (=> 
                           (exists ((x142 S) (x143 PZS)) 
                               (and 
                                   (b1 s9 x143) 
                                   (MS3 x141 x142 x143))) 
                           (<= x141 k)))))
         :named hyp33))
(assert (! (not 
               (and 
                   (forall ((x144 S) (x145 Bool) (x146 Bool)) 
                       (=> 
                           (and 
                               (or 
                                   (and 
                                       (DA x144 x145) 
                                       (not 
                                           (exists ((x147 Bool)) 
                                               (and 
                                                   (= x144 s) 
                                                   (not 
                                                       x147))))) 
                                   (and 
                                       (= x144 s) 
                                       (not 
                                           x145))) 
                               (or 
                                   (and 
                                       (DA x144 x146) 
                                       (not 
                                           (exists ((x148 Bool)) 
                                               (and 
                                                   (= x144 s) 
                                                   (not 
                                                       x148))))) 
                                   (and 
                                       (= x144 s) 
                                       (not 
                                           x146)))) 
                           (= 
                               x145 
                               x146))) 
                   (forall ((x149 S)) 
                       (or 
                           (exists ((x150 Bool)) 
                               (and 
                                   (DA x149 x150) 
                                   (not 
                                       (exists ((x151 Bool)) 
                                           (and 
                                               (= x149 s) 
                                               (not 
                                                   x151)))))) 
                           (exists ((x152 Bool)) 
                               (and 
                                   (= x149 s) 
                                   (not 
                                       x152)))))))
         :named goal))
(check-sat)
(exit)

