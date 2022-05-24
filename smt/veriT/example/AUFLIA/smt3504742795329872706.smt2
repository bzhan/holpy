(set-info :smt-lib-version 2.6)
(set-logic AUFLIA)
(set-info :source |Generator: Rodin SMT Plug-in|)
(set-info :license "https://creativecommons.org/licenses/by-nc/4.0/")
(set-info :category "industrial")
(set-info :status unsat)

(declare-sort A 0)
(declare-sort PA 0)
(declare-sort PAA 0)
(declare-sort PZ 0)
(declare-sort PZA 0)
(declare-fun MS (A A PAA) Bool)
(declare-fun MS0 (A PA) Bool)
(declare-fun MS1 (Int A PZA) Bool)
(declare-fun MS2 (Int PZ) Bool)
(declare-fun cnc (PZA PZA PZA) Bool)
(declare-fun dist (A A Int) Bool)
(declare-fun length (PZA Int) Bool)
(declare-fun path (A A PZA) Bool)
(declare-fun reverse (PZA PZA) Bool)
(declare-fun seq (PZA) Bool)
(declare-fun shpath (A A PZA) Bool)
(declare-fun a () PA)
(declare-fun c () PAA)
(declare-fun candidate () PA)
(declare-fun p () PZA)
(declare-fun q () PZA)
(declare-fun r () PAA)
(declare-fun x () A)
(declare-fun x1 () A)
(declare-fun y1 () A)
(declare-fun y2 () A)

; Elementary Sets axiom (Singleton part)
(assert (forall ((x1750 A) (x1751 A)) 
            (exists ((X PAA)) 
                (and 
                    (MS x1750 x1751 X) 
                    (forall ((y41 A) (y42 A)) 
                        (=> 
                            (MS y41 y42 X) 
                            (and 
                                (= y41 x1750) 
                                (= y42 x1751))))))))
; Elementary Sets axiom (Singleton part)
(assert (forall ((x1752 A)) 
            (exists ((X0 PA)) 
                (and 
                    (MS0 x1752 X0) 
                    (forall ((y43 A)) 
                        (=> 
                            (MS0 y43 X0) 
                            (= y43 x1752)))))))
; Elementary Sets axiom (Singleton part)
(assert (forall ((x1753 Int)) 
            (exists ((X1 PZ)) 
                (and 
                    (MS2 x1753 X1) 
                    (forall ((y44 Int)) 
                        (=> 
                            (MS2 y44 X1) 
                            (= y44 x1753)))))))
; Elementary Sets axiom (Singleton part)
(assert (forall ((x1754 Int) (x1755 A)) 
            (exists ((X2 PZA)) 
                (and 
                    (MS1 x1754 x1755 X2) 
                    (forall ((y45 Int) (y46 A)) 
                        (=> 
                            (MS1 y45 y46 X2) 
                            (and 
                                (= y45 x1754) 
                                (= y46 x1755))))))))
(assert (! (forall ((x0 A) (x2 A)) 
               (=> 
                   (MS x0 x2 r) 
                   (and 
                       (MS0 x0 a) 
                       (MS0 x2 a))))
         :named hyp1))
(assert (! (not 
               (forall ((x3 A) (x4 A)) 
                   (not 
                       (MS x3 x4 r))))
         :named hyp2))
(assert (! (forall ((x5 A) (x6 A)) 
               (=> 
                   (MS x5 x6 c) 
                   (and 
                       (MS0 x5 a) 
                       (MS0 x6 a))))
         :named hyp3))
(assert (! (forall ((x7 A) (x8 A)) 
               (=> 
                   (MS x7 x8 r) 
                   (MS x7 x8 c)))
         :named hyp4))
(assert (! (forall ((x9 A) (x10 A)) 
               (=> 
                   (exists ((x11 A)) 
                       (and 
                           (MS x9 x11 c) 
                           (MS x11 x10 r))) 
                   (MS x9 x10 c)))
         :named hyp5))
(assert (! (forall ((s PAA)) 
               (=> 
                   (and 
                       (forall ((x12 A) (x13 A)) 
                           (=> 
                               (MS x12 x13 s) 
                               (and 
                                   (MS0 x12 a) 
                                   (MS0 x13 a)))) 
                       (forall ((x14 A) (x15 A)) 
                           (=> 
                               (MS x14 x15 r) 
                               (MS x14 x15 s))) 
                       (forall ((x16 A) (x17 A)) 
                           (=> 
                               (exists ((x18 A)) 
                                   (and 
                                       (MS x16 x18 s) 
                                       (MS x18 x17 r))) 
                               (MS x16 x17 s)))) 
                   (forall ((x19 A) (x20 A)) 
                       (=> 
                           (MS x19 x20 c) 
                           (MS x19 x20 s)))))
         :named hyp6))
(assert (! (forall ((x21 A)) 
               (= 
                   (exists ((x22 A)) 
                       (MS x21 x22 r)) 
                   (MS0 x21 a)))
         :named hyp7))
(assert (! (forall ((x23 A)) 
               (= 
                   (exists ((x24 A)) 
                       (MS x23 x24 c)) 
                   (MS0 x23 a)))
         :named hyp8))
(assert (! (forall ((x25 A)) 
               (=> 
                   (exists ((x26 A)) 
                       (MS x25 x26 r)) 
                   (exists ((x27 A)) 
                       (MS x25 x27 c))))
         :named hyp9))
(assert (! (forall ((x28 A) (x29 A)) 
               (= 
                   (MS x28 x29 c) 
                   (or 
                       (MS x28 x29 r) 
                       (exists ((x30 A)) 
                           (and 
                               (MS x28 x30 c) 
                               (MS x30 x29 r))))))
         :named hyp10))
(assert (! (forall ((x31 A) (y A)) 
               (=> 
                   (and 
                       (MS0 x31 a) 
                       (MS0 y a)) 
                   (forall ((s0 PZA) (n Int)) 
                       (=> 
                           (and 
                               (<= 0 n) 
                               (< 1 n) 
                               (forall ((x32 Int) (x33 A)) 
                                   (=> 
                                       (MS1 x32 x33 s0) 
                                       (and 
                                           (<= 1 x32) 
                                           (<= x32 n) 
                                           (MS0 x33 a)))) 
                               (forall ((x34 Int) (x35 A) (x36 A)) 
                                   (=> 
                                       (and 
                                           (MS1 x34 x35 s0) 
                                           (MS1 x34 x36 s0)) 
                                       (= x35 x36))) 
                               (forall ((x37 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x37) 
                                           (<= x37 n)) 
                                       (exists ((x38 A)) 
                                           (MS1 x37 x38 s0))))) 
                           (and 
                               (exists ((x39 A) (x40 Int)) 
                                   (and 
                                       (= x40 1) 
                                       (MS1 x40 x39 s0))) 
                               (forall ((x41 Int) (x42 A) (x43 A)) 
                                   (=> 
                                       (and 
                                           (MS1 x41 x42 s0) 
                                           (MS1 x41 x43 s0)) 
                                       (= x42 x43))) 
                               (=> 
                                   (exists ((x44 Int)) 
                                       (and 
                                           (= x44 1) 
                                           (MS1 x44 x31 s0))) 
                                   (and 
                                       (exists ((x45 A)) 
                                           (MS1 n x45 s0)) 
                                       (=> 
                                           (MS1 n y s0) 
                                           (forall ((i Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 i) 
                                                       (<= i (- n 1))) 
                                                   (and 
                                                       (exists ((x46 A)) 
                                                           (MS1 i x46 s0)) 
                                                       (exists ((x47 A) (x48 Int)) 
                                                           (and 
                                                               (= x48 (+ i 1)) 
                                                               (MS1 x48 x47 s0))))))))))))))
         :named hyp11))
(assert (! (forall ((s1 PZ) (n0 Int)) 
               (=> 
                   (and 
                       (< 1 n0) 
                       (forall ((x49 Int)) 
                           (=> 
                               (MS2 x49 s1) 
                               (and 
                                   (<= 2 x49) 
                                   (<= x49 n0)))) 
                       (exists ((x50 Int)) 
                           (and 
                               (= x50 2) 
                               (MS2 x50 s1))) 
                       (forall ((i0 Int)) 
                           (=> 
                               (and 
                                   (<= 2 i0) 
                                   (<= i0 (- n0 1)) 
                                   (MS2 i0 s1)) 
                               (exists ((x51 Int)) 
                                   (and 
                                       (= x51 (+ i0 1)) 
                                       (MS2 x51 s1)))))) 
                   (forall ((x52 Int)) 
                       (=> 
                           (and 
                               (<= 2 x52) 
                               (<= x52 n0)) 
                           (MS2 x52 s1)))))
         :named hyp12))
(assert (! (forall ((x53 A) (x54 A)) 
               (=> 
                   (exists ((x55 PZA)) 
                       (path x53 x54 x55)) 
                   (MS x53 x54 c)))
         :named hyp13))
(assert (! (forall ((x56 A) (x57 A)) 
               (=> 
                   (MS x56 x57 c) 
                   (exists ((x58 PZA)) 
                       (path x56 x57 x58))))
         :named hyp14))
(assert (! (forall ((x59 A) (x60 A)) 
               (=> 
                   (and 
                       (MS0 x59 a) 
                       (MS0 x60 a)) 
                   (exists ((x61 PZA)) 
                       (path x59 x60 x61))))
         :named hyp15))
(assert (! (forall ((x62 PZA)) 
               (= 
                   (seq x62) 
                   (exists ((s2 PZA)) 
                       (and 
                           (exists ((n1 Int)) 
                               (and 
                                   (<= 0 n1) 
                                   (forall ((x63 Int) (x64 A)) 
                                       (=> 
                                           (MS1 x63 x64 s2) 
                                           (and 
                                               (<= 1 x63) 
                                               (<= x63 n1)))) 
                                   (forall ((x65 Int) (x66 A) (x67 A)) 
                                       (=> 
                                           (and 
                                               (MS1 x65 x66 s2) 
                                               (MS1 x65 x67 s2)) 
                                           (= x66 x67))) 
                                   (forall ((x68 Int)) 
                                       (=> 
                                           (and 
                                               (<= 1 x68) 
                                               (<= x68 n1)) 
                                           (exists ((x69 A)) 
                                               (MS1 x68 x69 s2)))))) 
                           (forall ((x70 Int) (x71 A)) 
                               (= 
                                   (MS1 x70 x71 x62) 
                                   (MS1 x70 x71 s2)))))))
         :named hyp16))
(assert (! (forall ((n2 Int) (s3 PZA)) 
               (=> 
                   (and 
                       (<= 0 n2) 
                       (forall ((x72 Int) (x73 A)) 
                           (=> 
                               (MS1 x72 x73 s3) 
                               (and 
                                   (<= 1 x72) 
                                   (<= x72 n2)))) 
                       (forall ((x74 Int) (x75 A) (x76 A)) 
                           (=> 
                               (and 
                                   (MS1 x74 x75 s3) 
                                   (MS1 x74 x76 s3)) 
                               (= x75 x76))) 
                       (forall ((x77 Int)) 
                           (=> 
                               (and 
                                   (<= 1 x77) 
                                   (<= x77 n2)) 
                               (exists ((x78 A)) 
                                   (MS1 x77 x78 s3))))) 
                   (seq s3)))
         :named hyp17))
(assert (! (and 
               (forall ((x79 PZA) (x80 Int)) 
                   (=> 
                       (length x79 x80) 
                       (and 
                           (seq x79) 
                           (<= 0 x80)))) 
               (forall ((x81 PZA) (x82 Int) (x83 Int)) 
                   (=> 
                       (and 
                           (length x81 x82) 
                           (length x81 x83)) 
                       (= x82 x83))) 
               (forall ((x84 PZA)) 
                   (=> 
                       (seq x84) 
                       (exists ((x85 Int)) 
                           (length x84 x85)))))
         :named hyp18))
(assert (! (forall ((n3 Int) (s4 PZA)) 
               (=> 
                   (and 
                       (<= 0 n3) 
                       (forall ((x86 Int) (x87 A)) 
                           (=> 
                               (MS1 x86 x87 s4) 
                               (and 
                                   (<= 1 x86) 
                                   (<= x86 n3)))) 
                       (forall ((x88 Int) (x89 A) (x90 A)) 
                           (=> 
                               (and 
                                   (MS1 x88 x89 s4) 
                                   (MS1 x88 x90 s4)) 
                               (= x89 x90))) 
                       (forall ((x91 Int)) 
                           (=> 
                               (and 
                                   (<= 1 x91) 
                                   (<= x91 n3)) 
                               (exists ((x92 A)) 
                                   (MS1 x91 x92 s4))))) 
                   (length s4 n3)))
         :named hyp19))
(assert (! (forall ((s5 PZA)) 
               (=> 
                   (seq s5) 
                   (and 
                       (forall ((x93 Int) (x94 A)) 
                           (=> 
                               (MS1 x93 x94 s5) 
                               (and 
                                   (<= 1 x93) 
                                   (forall ((x95 Int)) 
                                       (=> 
                                           (length s5 x95) 
                                           (<= x93 x95)))))) 
                       (forall ((x96 Int) (x97 A) (x98 A)) 
                           (=> 
                               (and 
                                   (MS1 x96 x97 s5) 
                                   (MS1 x96 x98 s5)) 
                               (= x97 x98))) 
                       (forall ((x99 Int)) 
                           (=> 
                               (and 
                                   (<= 1 x99) 
                                   (forall ((x100 Int)) 
                                       (=> 
                                           (length s5 x100) 
                                           (<= x99 x100)))) 
                               (exists ((x101 A)) 
                                   (MS1 x99 x101 s5)))))))
         :named hyp20))
(assert (! (forall ((x102 PZA) (x103 PZA) (x104 PZA)) 
               (= 
                   (cnc x102 x103 x104) 
                   (exists ((s10 PZA) (s20 PZA)) 
                       (and 
                           (seq s10) 
                           (seq s20) 
                           (forall ((x105 Int) (x106 A)) 
                               (= 
                                   (MS1 x105 x106 x102) 
                                   (MS1 x105 x106 s10))) 
                           (forall ((x107 Int) (x108 A)) 
                               (= 
                                   (MS1 x107 x108 x103) 
                                   (MS1 x107 x108 s20))) 
                           (forall ((x109 Int) (x110 A)) 
                               (= 
                                   (MS1 x109 x110 x104) 
                                   (or 
                                       (exists ((i1 Int)) 
                                           (and 
                                               (<= 1 i1) 
                                               (forall ((x111 Int)) 
                                                   (=> 
                                                       (length s10 x111) 
                                                       (<= i1 x111))) 
                                               (= x109 i1) 
                                               (MS1 i1 x110 s10))) 
                                       (exists ((i2 Int)) 
                                           (and 
                                               (forall ((x112 Int)) 
                                                   (=> 
                                                       (length s10 x112) 
                                                       (<= (+ x112 1) i2))) 
                                               (forall ((x113 Int) (x114 Int)) 
                                                   (=> 
                                                       (and 
                                                           (length s10 x114) 
                                                           (length s20 x113)) 
                                                       (<= i2 (+ x114 x113)))) 
                                               (= x109 i2) 
                                               (exists ((x115 Int)) 
                                                   (and 
                                                       (forall ((x116 Int)) 
                                                           (=> 
                                                               (length s10 x116) 
                                                               (= x115 (- i2 x116)))) 
                                                       (MS1 x115 x110 s20))))))))))))
         :named hyp21))
(assert (! (and 
               (forall ((x117 PZA) (x118 PZA) (x119 PZA)) 
                   (=> 
                       (cnc x117 x118 x119) 
                       (and 
                           (seq x117) 
                           (seq x118) 
                           (seq x119)))) 
               (forall ((x120 PZA) (x121 PZA) (x122 PZA) (x123 PZA)) 
                   (=> 
                       (and 
                           (cnc x120 x121 x122) 
                           (cnc x120 x121 x123)) 
                       (forall ((x124 Int) (x125 A)) 
                           (= 
                               (MS1 x124 x125 x122) 
                               (MS1 x124 x125 x123))))) 
               (forall ((x126 PZA) (x127 PZA)) 
                   (=> 
                       (and 
                           (seq x126) 
                           (seq x127)) 
                       (exists ((x128 PZA)) 
                           (cnc x126 x127 x128)))))
         :named hyp22))
(assert (! (forall ((s11 PZA) (s21 PZA)) 
               (=> 
                   (and 
                       (seq s11) 
                       (seq s21)) 
                   (exists ((x129 PZA) (x130 Int)) 
                       (and 
                           (cnc s11 s21 x129) 
                           (forall ((x131 Int) (x132 Int)) 
                               (=> 
                                   (and 
                                       (length s11 x132) 
                                       (length s21 x131)) 
                                   (= x130 (+ x132 x131)))) 
                           (length x129 x130)))))
         :named hyp23))
(assert (! (forall ((s12 PZA) (s22 PZA)) 
               (=> 
                   (and 
                       (seq s12) 
                       (seq s22)) 
                   (forall ((x133 Int)) 
                       (= 
                           (exists ((x134 A) (x135 PZA)) 
                               (and 
                                   (cnc s12 s22 x135) 
                                   (MS1 x133 x134 x135))) 
                           (and 
                               (<= 1 x133) 
                               (forall ((x136 Int) (x137 Int)) 
                                   (=> 
                                       (and 
                                           (length s12 x137) 
                                           (length s22 x136)) 
                                       (<= x133 (+ x137 x136)))))))))
         :named hyp24))
(assert (! (forall ((s13 PZA) (s23 PZA)) 
               (=> 
                   (and 
                       (seq s13) 
                       (seq s23)) 
                   (forall ((x138 A)) 
                       (= 
                           (exists ((x139 Int) (x140 PZA)) 
                               (and 
                                   (cnc s13 s23 x140) 
                                   (MS1 x139 x138 x140))) 
                           (or 
                               (exists ((x141 Int)) 
                                   (MS1 x141 x138 s13)) 
                               (exists ((x142 Int)) 
                                   (MS1 x142 x138 s23)))))))
         :named hyp25))
(assert (! (forall ((s14 PZA) (s24 PZA) (i3 Int)) 
               (=> 
                   (and 
                       (seq s14) 
                       (seq s24) 
                       (<= 1 i3) 
                       (forall ((x143 Int)) 
                           (=> 
                               (length s14 x143) 
                               (<= i3 x143)))) 
                   (exists ((x144 PZA)) 
                       (and 
                           (cnc s14 s24 x144) 
                           (exists ((x145 A)) 
                               (and 
                                   (MS1 i3 x145 s14) 
                                   (MS1 i3 x145 x144)))))))
         :named hyp26))
(assert (! (forall ((s15 PZA) (s25 PZA) (i4 Int)) 
               (=> 
                   (and 
                       (seq s15) 
                       (seq s25) 
                       (forall ((x146 Int)) 
                           (=> 
                               (length s15 x146) 
                               (<= (+ x146 1) i4))) 
                       (forall ((x147 Int) (x148 Int)) 
                           (=> 
                               (and 
                                   (length s15 x148) 
                                   (length s25 x147)) 
                               (<= i4 (+ x148 x147))))) 
                   (exists ((x149 PZA)) 
                       (and 
                           (cnc s15 s25 x149) 
                           (exists ((x150 A)) 
                               (and 
                                   (exists ((x151 Int)) 
                                       (and 
                                           (forall ((x152 Int)) 
                                               (=> 
                                                   (length s15 x152) 
                                                   (= x151 (- i4 x152)))) 
                                           (MS1 x151 x150 s25))) 
                                   (MS1 i4 x150 x149)))))))
         :named hyp27))
(assert (! (forall ((x153 A) (x154 A)) 
               (not 
                   (and 
                       (MS x153 x154 r) 
                       (= x153 x154))))
         :named hyp28))
(assert (! (and 
               (forall ((x155 A) (x156 A) (x157 Int)) 
                   (=> 
                       (dist x155 x156 x157) 
                       (and 
                           (MS0 x155 a) 
                           (MS0 x156 a) 
                           (<= 0 x157)))) 
               (forall ((x158 A) (x159 A) (x160 Int) (x161 Int)) 
                   (=> 
                       (and 
                           (dist x158 x159 x160) 
                           (dist x158 x159 x161)) 
                       (= x160 x161))) 
               (forall ((x162 A) (x163 A)) 
                   (=> 
                       (and 
                           (MS0 x162 a) 
                           (MS0 x163 a)) 
                       (exists ((x164 Int)) 
                           (dist x162 x163 x164)))))
         :named hyp29))
(assert (! (forall ((x165 A) (y0 A)) 
               (=> 
                   (and 
                       (MS0 x165 a) 
                       (MS0 y0 a)) 
                   (exists ((x166 Int)) 
                       (and 
                           (exists ((x167 PZA)) 
                               (and 
                                   (exists ((x168 A) (x169 A)) 
                                       (and 
                                           (= x168 x165) 
                                           (= x169 y0) 
                                           (path x168 x169 x167))) 
                                   (length x167 x166))) 
                           (forall ((x170 Int)) 
                               (=> 
                                   (exists ((x171 PZA)) 
                                       (and 
                                           (exists ((x172 A) (x173 A)) 
                                               (and 
                                                   (= x172 x165) 
                                                   (= x173 y0) 
                                                   (path x172 x173 x171))) 
                                           (length x171 x170))) 
                                   (<= x166 x170))) 
                           (dist x165 y0 x166)))))
         :named hyp30))
(assert (! (forall ((x174 PZA) (x175 PZA)) 
               (= 
                   (reverse x174 x175) 
                   (exists ((s6 PZA)) 
                       (and 
                           (seq s6) 
                           (forall ((x176 Int) (x177 A)) 
                               (= 
                                   (MS1 x176 x177 x174) 
                                   (MS1 x176 x177 s6))) 
                           (forall ((x178 Int) (x179 A)) 
                               (= 
                                   (MS1 x178 x179 x175) 
                                   (exists ((i5 Int)) 
                                       (and 
                                           (<= 1 i5) 
                                           (forall ((x180 Int)) 
                                               (=> 
                                                   (length s6 x180) 
                                                   (<= i5 x180))) 
                                           (= x178 i5) 
                                           (exists ((x181 Int)) 
                                               (and 
                                                   (forall ((x182 Int)) 
                                                       (=> 
                                                           (length s6 x182) 
                                                           (= x181 (+ (- x182 i5) 1)))) 
                                                   (MS1 x181 x179 s6)))))))))))
         :named hyp31))
(assert (! (and 
               (forall ((x183 PZA) (x184 PZA)) 
                   (=> 
                       (reverse x183 x184) 
                       (and 
                           (seq x183) 
                           (seq x184)))) 
               (forall ((x185 PZA) (x186 PZA) (x187 PZA)) 
                   (=> 
                       (and 
                           (reverse x185 x186) 
                           (reverse x185 x187)) 
                       (forall ((x188 Int) (x189 A)) 
                           (= 
                               (MS1 x188 x189 x186) 
                               (MS1 x188 x189 x187))))) 
               (forall ((x190 PZA)) 
                   (=> 
                       (seq x190) 
                       (exists ((x191 PZA)) 
                           (reverse x190 x191)))))
         :named hyp32))
(assert (! (forall ((s7 PZA)) 
               (=> 
                   (seq s7) 
                   (exists ((x192 PZA) (x193 Int)) 
                       (and 
                           (reverse s7 x192) 
                           (length s7 x193) 
                           (length x192 x193)))))
         :named hyp33))
(assert (! (forall ((s8 PZA)) 
               (=> 
                   (seq s8) 
                   (forall ((x194 A)) 
                       (= 
                           (exists ((x195 Int) (x196 PZA)) 
                               (and 
                                   (reverse s8 x196) 
                                   (MS1 x195 x194 x196))) 
                           (exists ((x197 Int)) 
                               (MS1 x197 x194 s8))))))
         :named hyp34))
(assert (! (forall ((s9 PZA)) 
               (=> 
                   (seq s9) 
                   (exists ((x198 PZA)) 
                       (and 
                           (reverse s9 x198) 
                           (reverse x198 s9)))))
         :named hyp35))
(assert (! (forall ((x199 A) (x200 A)) 
               (=> 
                   (MS x199 x200 r) 
                   (MS x200 x199 r)))
         :named hyp36))
(assert (! (forall ((x201 A) (y3 A) (p0 PZA)) 
               (=> 
                   (path x201 y3 p0) 
                   (exists ((x202 PZA)) 
                       (and 
                           (reverse p0 x202) 
                           (path y3 x201 x202)))))
         :named hyp37))
(assert (! (forall ((x203 A) (y4 A)) 
               (=> 
                   (and 
                       (MS0 x203 a) 
                       (MS0 y4 a)) 
                   (forall ((x204 PZA)) 
                       (= 
                           (exists ((x205 A) (x206 A)) 
                               (and 
                                   (= x205 y4) 
                                   (= x206 x203) 
                                   (path x205 x206 x204))) 
                           (exists ((x207 PZA)) 
                               (and 
                                   (exists ((x208 A) (x209 A)) 
                                       (and 
                                           (= x208 x203) 
                                           (= x209 y4) 
                                           (path x208 x209 x207))) 
                                   (reverse x207 x204)))))))
         :named hyp38))
(assert (! (forall ((x210 A) (y5 A)) 
               (=> 
                   (and 
                       (MS0 x210 a) 
                       (MS0 y5 a)) 
                   (exists ((x211 Int)) 
                       (and 
                           (dist y5 x210 x211) 
                           (dist x210 y5 x211)))))
         :named hyp39))
(assert (! (forall ((x212 A) (x213 A) (x214 PZA)) 
               (= 
                   (shpath x212 x213 x214) 
                   (exists ((x215 A) (y6 A) (p1 PZA)) 
                       (and 
                           (path x215 y6 p1) 
                           (exists ((x216 Int)) 
                               (and 
                                   (length p1 x216) 
                                   (dist x215 y6 x216))) 
                           (= x212 x215) 
                           (= x213 y6) 
                           (forall ((x217 Int) (x218 A)) 
                               (= 
                                   (MS1 x217 x218 x214) 
                                   (MS1 x217 x218 p1)))))))
         :named hyp40))
(assert (! (forall ((x219 A) (y7 A) (p2 PZA)) 
               (=> 
                   (path x219 y7 p2) 
                   (and 
                       (exists ((x220 Int)) 
                           (dist x219 y7 x220)) 
                       (forall ((x221 A) (x222 A) (x223 Int) (x224 Int)) 
                           (=> 
                               (and 
                                   (dist x221 x222 x223) 
                                   (dist x221 x222 x224)) 
                               (= x223 x224))) 
                       (exists ((x225 Int)) 
                           (length p2 x225)) 
                       (forall ((x226 PZA) (x227 Int) (x228 Int)) 
                           (=> 
                               (and 
                                   (length x226 x227) 
                                   (length x226 x228)) 
                               (= x227 x228))))))
         :named hyp41))
(assert (! (forall ((x229 A) (y8 A)) 
               (=> 
                   (and 
                       (MS0 x229 a) 
                       (MS0 y8 a)) 
                   (exists ((x230 PZA)) 
                       (shpath x229 y8 x230))))
         :named hyp42))
(assert (! (forall ((x231 A) (x232 A) (x233 PZA)) 
               (= 
                   (path x231 x232 x233) 
                   (exists ((x234 A) (y9 A) (p3 PZA)) 
                       (and 
                           (MS0 x234 a) 
                           (MS0 y9 a) 
                           (exists ((n4 Int)) 
                               (and 
                                   (<= 0 n4) 
                                   (< 1 n4) 
                                   (forall ((x235 Int) (x236 A)) 
                                       (=> 
                                           (MS1 x235 x236 p3) 
                                           (and 
                                               (<= 1 x235) 
                                               (<= x235 n4) 
                                               (MS0 x236 a)))) 
                                   (forall ((x237 Int) (x238 A) (x239 A)) 
                                       (=> 
                                           (and 
                                               (MS1 x237 x238 p3) 
                                               (MS1 x237 x239 p3)) 
                                           (= x238 x239))) 
                                   (forall ((x240 Int)) 
                                       (=> 
                                           (and 
                                               (<= 1 x240) 
                                               (<= x240 n4)) 
                                           (exists ((x241 A)) 
                                               (MS1 x240 x241 p3)))) 
                                   (exists ((x242 Int)) 
                                       (and 
                                           (= x242 1) 
                                           (MS1 x242 x234 p3))) 
                                   (MS1 n4 y9 p3) 
                                   (forall ((i6 Int)) 
                                       (=> 
                                           (and 
                                               (<= 1 i6) 
                                               (<= i6 (- n4 1))) 
                                           (exists ((x243 A) (x244 A)) 
                                               (and 
                                                   (MS1 i6 x243 p3) 
                                                   (exists ((x245 Int)) 
                                                       (and 
                                                           (= x245 (+ i6 1)) 
                                                           (MS1 x245 x244 p3))) 
                                                   (MS x243 x244 r))))))) 
                           (= x231 x234) 
                           (= x232 y9) 
                           (forall ((x246 Int) (x247 A)) 
                               (= 
                                   (MS1 x246 x247 x233) 
                                   (MS1 x246 x247 p3)))))))
         :named hyp43))
(assert (! (forall ((x248 A)) 
               (= 
                   (MS0 x248 candidate) 
                   (exists ((z A)) 
                       (and 
                           (MS0 z a) 
                           (forall ((x249 A) (y10 A)) 
                               (=> 
                                   (and 
                                       (MS0 x249 a) 
                                       (not 
                                           (= x249 z)) 
                                       (MS0 y10 a) 
                                       (not 
                                           (= y10 z)) 
                                       (not 
                                           (= x249 y10))) 
                                   (exists ((p4 PZA)) 
                                       (and 
                                           (exists ((x250 A) (x251 A)) 
                                               (and 
                                                   (= x250 x249) 
                                                   (= x251 y10) 
                                                   (path x250 x251 p4))) 
                                           (not 
                                               (exists ((x252 Int)) 
                                                   (MS1 x252 z p4))))))) 
                           (= x248 z)))))
         :named hyp44))
(assert (! (forall ((u A)) 
               (=> 
                   (MS0 u candidate) 
                   (forall ((x253 A) (x254 A)) 
                       (=> 
                           (and 
                               (MS0 x253 a) 
                               (not 
                                   (= x253 u)) 
                               (MS0 x254 a) 
                               (not 
                                   (= x254 u)) 
                               (not 
                                   (= x253 x254))) 
                           (exists ((x255 A) (y11 A) (p5 PZA)) 
                               (and 
                                   (MS0 x255 a) 
                                   (not 
                                       (= x255 u)) 
                                   (MS0 y11 a) 
                                   (not 
                                       (= y11 u)) 
                                   (not 
                                       (= x255 y11)) 
                                   (exists ((n5 Int)) 
                                       (and 
                                           (<= 0 n5) 
                                           (< 1 n5) 
                                           (forall ((x256 Int) (x257 A)) 
                                               (=> 
                                                   (MS1 x256 x257 p5) 
                                                   (and 
                                                       (<= 1 x256) 
                                                       (<= x256 n5) 
                                                       (MS0 x257 a) 
                                                       (not 
                                                           (= x257 u))))) 
                                           (forall ((x258 Int) (x259 A) (x260 A)) 
                                               (=> 
                                                   (and 
                                                       (MS1 x258 x259 p5) 
                                                       (MS1 x258 x260 p5)) 
                                                   (= x259 x260))) 
                                           (forall ((x261 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x261) 
                                                       (<= x261 n5)) 
                                                   (exists ((x262 A)) 
                                                       (MS1 x261 x262 p5)))) 
                                           (exists ((x263 Int)) 
                                               (and 
                                                   (= x263 1) 
                                                   (MS1 x263 x255 p5))) 
                                           (MS1 n5 y11 p5) 
                                           (forall ((i7 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 i7) 
                                                       (<= i7 (- n5 1))) 
                                                   (exists ((x264 A) (x265 A)) 
                                                       (and 
                                                           (MS1 i7 x264 p5) 
                                                           (exists ((x266 Int)) 
                                                               (and 
                                                                   (= x266 (+ i7 1)) 
                                                                   (MS1 x266 x265 p5))) 
                                                           (MS x264 x265 r))))))) 
                                   (= x253 x255) 
                                   (= x254 y11)))))))
         :named hyp45))
(assert (! (forall ((s16 PZA) (s26 PZA)) 
               (=> 
                   (and 
                       (seq s16) 
                       (seq s26)) 
                   (and 
                       (exists ((x267 Int)) 
                           (length s16 x267)) 
                       (forall ((x268 PZA) (x269 Int) (x270 Int)) 
                           (=> 
                               (and 
                                   (length x268 x269) 
                                   (length x268 x270)) 
                               (= x269 x270))) 
                       (forall ((i8 Int)) 
                           (=> 
                               (and 
                                   (<= 1 i8) 
                                   (forall ((x271 Int)) 
                                       (=> 
                                           (length s16 x271) 
                                           (<= i8 x271)))) 
                               (and 
                                   (exists ((x272 A)) 
                                       (MS1 i8 x272 s16)) 
                                   (forall ((x273 Int) (x274 A) (x275 A)) 
                                       (=> 
                                           (and 
                                               (MS1 x273 x274 s16) 
                                               (MS1 x273 x275 s16)) 
                                           (= x274 x275)))))) 
                       (exists ((x276 Int)) 
                           (length s26 x276)) 
                       (forall ((i9 Int)) 
                           (=> 
                               (and 
                                   (forall ((x277 Int)) 
                                       (=> 
                                           (length s16 x277) 
                                           (<= (+ x277 1) i9))) 
                                   (forall ((x278 Int) (x279 Int)) 
                                       (=> 
                                           (and 
                                               (length s16 x279) 
                                               (length s26 x278)) 
                                           (<= i9 (+ x279 x278))))) 
                               (and 
                                   (exists ((x280 A) (x281 Int)) 
                                       (and 
                                           (forall ((x282 Int)) 
                                               (=> 
                                                   (length s16 x282) 
                                                   (= x281 (- i9 x282)))) 
                                           (MS1 x281 x280 s26))) 
                                   (forall ((x283 Int) (x284 A) (x285 A)) 
                                       (=> 
                                           (and 
                                               (MS1 x283 x284 s26) 
                                               (MS1 x283 x285 s26)) 
                                           (= x284 x285)))))))))
         :named hyp46))
(assert (! (forall ((s17 PZA)) 
               (=> 
                   (seq s17) 
                   (and 
                       (exists ((x286 Int)) 
                           (length s17 x286)) 
                       (forall ((x287 PZA) (x288 Int) (x289 Int)) 
                           (=> 
                               (and 
                                   (length x287 x288) 
                                   (length x287 x289)) 
                               (= x288 x289))) 
                       (forall ((i10 Int)) 
                           (=> 
                               (and 
                                   (<= 1 i10) 
                                   (forall ((x290 Int)) 
                                       (=> 
                                           (length s17 x290) 
                                           (<= i10 x290)))) 
                               (and 
                                   (exists ((x291 A) (x292 Int)) 
                                       (and 
                                           (forall ((x293 Int)) 
                                               (=> 
                                                   (length s17 x293) 
                                                   (= x292 (+ (- x293 i10) 1)))) 
                                           (MS1 x292 x291 s17))) 
                                   (forall ((x294 Int) (x295 A) (x296 A)) 
                                       (=> 
                                           (and 
                                               (MS1 x294 x295 s17) 
                                               (MS1 x294 x296 s17)) 
                                           (= x295 x296)))))))))
         :named hyp47))
(assert (! (forall ((x297 A) (y12 A) (p6 PZA) (i11 Int)) 
               (=> 
                   (and 
                       (MS0 x297 a) 
                       (MS0 y12 a) 
                       (seq p6) 
                       (shpath x297 y12 p6) 
                       (exists ((x298 A)) 
                           (MS1 i11 x298 p6)) 
                       (not 
                           (= i11 1)) 
                       (not 
                           (length p6 i11))) 
                   (exists ((x299 A) (x300 PZA)) 
                       (and 
                           (MS1 i11 x299 p6) 
                           (forall ((x301 Int) (x302 A)) 
                               (= 
                                   (MS1 x301 x302 x300) 
                                   (and 
                                       (MS1 x301 x302 p6) 
                                       (<= 1 x301) 
                                       (<= x301 i11)))) 
                           (shpath x297 x299 x300)))))
         :named hyp48))
(assert (! (forall ((x303 A) (y13 A) (p7 PZA) (i12 Int)) 
               (=> 
                   (and 
                       (MS0 x303 a) 
                       (MS0 y13 a) 
                       (seq p7) 
                       (shpath x303 y13 p7) 
                       (exists ((x304 A)) 
                           (MS1 i12 x304 p7)) 
                       (not 
                           (= i12 1)) 
                       (not 
                           (length p7 i12))) 
                   (and 
                       (exists ((x305 A)) 
                           (and 
                               (MS1 i12 x305 p7) 
                               (dist x303 x305 i12))) 
                       (exists ((x306 A) (x307 Int)) 
                           (and 
                               (exists ((x308 Int)) 
                                   (and 
                                       (= x308 (+ i12 1)) 
                                       (MS1 x308 x306 p7))) 
                               (= x307 (+ i12 1)) 
                               (dist x303 x306 x307))) 
                       (exists ((x309 A) (x310 A)) 
                           (and 
                               (MS1 i12 x309 p7) 
                               (exists ((x311 Int)) 
                                   (and 
                                       (= x311 (+ i12 1)) 
                                       (MS1 x311 x310 p7))) 
                               (MS x309 x310 r))))))
         :named hyp49))
(assert (! (forall ((x312 A) (y14 A) (p8 PZA) (z0 A)) 
               (=> 
                   (and 
                       (MS0 x312 a) 
                       (MS0 y14 a) 
                       (seq p8) 
                       (shpath x312 y14 p8) 
                       (exists ((x313 Int)) 
                           (MS1 x313 z0 p8)) 
                       (not 
                           (= z0 x312)) 
                       (not 
                           (= z0 y14))) 
                   (exists ((t A)) 
                       (and 
                           (MS0 t a) 
                           (forall ((x314 Int) (x315 Int)) 
                               (=> 
                                   (and 
                                       (dist x312 z0 x315) 
                                       (dist x312 t x314)) 
                                   (< x315 x314))) 
                           (MS z0 t r)))))
         :named hyp50))
(assert (! (forall ((x316 A) (y15 A) (z1 A)) 
               (=> 
                   (and 
                       (MS0 x316 a) 
                       (MS0 y15 a) 
                       (MS0 z1 a) 
                       (not 
                           (= z1 x316)) 
                       (not 
                           (= z1 y15)) 
                       (forall ((t0 A)) 
                           (=> 
                               (and 
                                   (MS0 t0 a) 
                                   (MS z1 t0 r)) 
                               (forall ((x317 Int) (x318 Int)) 
                                   (=> 
                                       (and 
                                           (dist x316 t0 x318) 
                                           (dist x316 z1 x317)) 
                                       (<= x318 x317)))))) 
                   (exists ((q0 PZA)) 
                       (and 
                           (path x316 y15 q0) 
                           (not 
                               (exists ((x319 Int)) 
                                   (MS1 x319 z1 q0)))))))
         :named hyp51))
(assert (! (forall ((x320 A) (x321 A)) 
               (=> 
                   (and 
                       (MS0 x320 a) 
                       (MS0 x321 a)) 
                   (MS x320 x321 c)))
         :named hyp52))
(assert (! (not 
               (forall ((x322 A)) 
                   (MS0 x322 a)))
         :named hyp53))
(assert (! (forall ((s18 PZA) (s27 PZA) (b PA)) 
               (=> 
                   (and 
                       (seq s18) 
                       (seq s27) 
                       (forall ((x323 A)) 
                           (=> 
                               (exists ((x324 Int)) 
                                   (MS1 x324 x323 s18)) 
                               (MS0 x323 b))) 
                       (forall ((x325 A)) 
                           (=> 
                               (exists ((x326 Int)) 
                                   (MS1 x326 x325 s27)) 
                               (MS0 x325 b)))) 
                   (and 
                       (forall ((x327 Int) (x328 A)) 
                           (=> 
                               (exists ((x329 PZA)) 
                                   (and 
                                       (cnc s18 s27 x329) 
                                       (MS1 x327 x328 x329))) 
                               (and 
                                   (<= 1 x327) 
                                   (forall ((x330 Int) (x331 Int)) 
                                       (=> 
                                           (and 
                                               (length s18 x331) 
                                               (length s27 x330)) 
                                           (<= x327 (+ x331 x330)))) 
                                   (MS0 x328 b)))) 
                       (forall ((x332 Int) (x333 A) (x334 A)) 
                           (=> 
                               (and 
                                   (exists ((x335 PZA)) 
                                       (and 
                                           (cnc s18 s27 x335) 
                                           (MS1 x332 x333 x335))) 
                                   (exists ((x336 PZA)) 
                                       (and 
                                           (cnc s18 s27 x336) 
                                           (MS1 x332 x334 x336)))) 
                               (= x333 x334))) 
                       (forall ((x337 Int)) 
                           (=> 
                               (and 
                                   (<= 1 x337) 
                                   (forall ((x338 Int) (x339 Int)) 
                                       (=> 
                                           (and 
                                               (length s18 x339) 
                                               (length s27 x338)) 
                                           (<= x337 (+ x339 x338))))) 
                               (exists ((x340 A) (x341 PZA)) 
                                   (and 
                                       (cnc s18 s27 x341) 
                                       (MS1 x337 x340 x341))))))))
         :named hyp54))
(assert (! (forall ((x342 A) (x343 A) (x344 PZA)) 
               (= 
                   (path x342 x343 x344) 
                   (exists ((x345 A) (y16 A) (p9 PZA)) 
                       (and 
                           (seq p9) 
                           (forall ((x346 A)) 
                               (=> 
                                   (exists ((x347 Int)) 
                                       (MS1 x347 x346 p9)) 
                                   (MS0 x346 a))) 
                           (forall ((x348 Int)) 
                               (=> 
                                   (length p9 x348) 
                                   (< 1 x348))) 
                           (exists ((x349 Int)) 
                               (and 
                                   (= x349 1) 
                                   (MS1 x349 x345 p9))) 
                           (exists ((x350 Int)) 
                               (and 
                                   (length p9 x350) 
                                   (MS1 x350 y16 p9))) 
                           (forall ((i13 Int)) 
                               (=> 
                                   (and 
                                       (<= 1 i13) 
                                       (forall ((x351 Int)) 
                                           (=> 
                                               (length p9 x351) 
                                               (<= i13 (- x351 1))))) 
                                   (exists ((x352 A) (x353 A)) 
                                       (and 
                                           (MS1 i13 x352 p9) 
                                           (exists ((x354 Int)) 
                                               (and 
                                                   (= x354 (+ i13 1)) 
                                                   (MS1 x354 x353 p9))) 
                                           (MS x352 x353 r))))) 
                           (= x342 x345) 
                           (= x343 y16) 
                           (forall ((x355 Int) (x356 A)) 
                               (= 
                                   (MS1 x355 x356 x344) 
                                   (MS1 x355 x356 p9)))))))
         :named hyp55))
(assert (! (forall ((x357 A) (y17 A) (p10 PZA)) 
               (=> 
                   (and 
                       (seq p10) 
                       (forall ((x358 A)) 
                           (=> 
                               (exists ((x359 Int)) 
                                   (MS1 x359 x358 p10)) 
                               (MS0 x358 a)))) 
                   (and 
                       (exists ((x360 Int)) 
                           (length p10 x360)) 
                       (forall ((x361 PZA) (x362 Int) (x363 Int)) 
                           (=> 
                               (and 
                                   (length x361 x362) 
                                   (length x361 x363)) 
                               (= x362 x363))) 
                       (=> 
                           (forall ((x364 Int)) 
                               (=> 
                                   (length p10 x364) 
                                   (< 1 x364))) 
                           (and 
                               (exists ((x365 A) (x366 Int)) 
                                   (and 
                                       (= x366 1) 
                                       (MS1 x366 x365 p10))) 
                               (forall ((x367 Int) (x368 A) (x369 A)) 
                                   (=> 
                                       (and 
                                           (MS1 x367 x368 p10) 
                                           (MS1 x367 x369 p10)) 
                                       (= x368 x369))) 
                               (=> 
                                   (exists ((x370 Int)) 
                                       (and 
                                           (= x370 1) 
                                           (MS1 x370 x357 p10))) 
                                   (and 
                                       (exists ((x371 A) (x372 Int)) 
                                           (and 
                                               (length p10 x372) 
                                               (MS1 x372 x371 p10))) 
                                       (=> 
                                           (exists ((x373 Int)) 
                                               (and 
                                                   (length p10 x373) 
                                                   (MS1 x373 y17 p10))) 
                                           (forall ((i14 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 i14) 
                                                       (forall ((x374 Int)) 
                                                           (=> 
                                                               (length p10 x374) 
                                                               (<= i14 (- x374 1))))) 
                                                   (and 
                                                       (exists ((x375 A)) 
                                                           (MS1 i14 x375 p10)) 
                                                       (exists ((x376 A) (x377 Int)) 
                                                           (and 
                                                               (= x377 (+ i14 1)) 
                                                               (MS1 x377 x376 p10))))))))))))))
         :named hyp56))
(assert (! (MS0 y1 a)
         :named hyp57))
(assert (! (MS0 y2 a)
         :named hyp58))
(assert (! (MS0 x a)
         :named hyp59))
(assert (! (MS0 x1 a)
         :named hyp60))
(assert (! (path x y1 q)
         :named hyp61))
(assert (! (path y2 x1 p)
         :named hyp62))
(assert (! (MS x1 x r)
         :named hyp63))
(assert (! (and 
               (forall ((x378 PZA) (x379 Int)) 
                   (=> 
                       (length x378 x379) 
                       (and 
                           (exists ((s19 PZA)) 
                               (and 
                                   (exists ((n6 Int)) 
                                       (and 
                                           (<= 0 n6) 
                                           (forall ((x380 Int) (x381 A)) 
                                               (=> 
                                                   (MS1 x380 x381 s19) 
                                                   (and 
                                                       (<= 1 x380) 
                                                       (<= x380 n6)))) 
                                           (forall ((x382 Int) (x383 A) (x384 A)) 
                                               (=> 
                                                   (and 
                                                       (MS1 x382 x383 s19) 
                                                       (MS1 x382 x384 s19)) 
                                                   (= x383 x384))) 
                                           (forall ((x385 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x385) 
                                                       (<= x385 n6)) 
                                                   (exists ((x386 A)) 
                                                       (MS1 x385 x386 s19)))))) 
                                   (forall ((x387 Int) (x388 A)) 
                                       (= 
                                           (MS1 x387 x388 x378) 
                                           (MS1 x387 x388 s19))))) 
                           (<= 0 x379)))) 
               (forall ((x389 PZA) (x390 Int) (x391 Int)) 
                   (=> 
                       (and 
                           (length x389 x390) 
                           (length x389 x391)) 
                       (= x390 x391))) 
               (forall ((x392 PZA)) 
                   (=> 
                       (exists ((s28 PZA)) 
                           (and 
                               (exists ((n7 Int)) 
                                   (and 
                                       (<= 0 n7) 
                                       (forall ((x393 Int) (x394 A)) 
                                           (=> 
                                               (MS1 x393 x394 s28) 
                                               (and 
                                                   (<= 1 x393) 
                                                   (<= x393 n7)))) 
                                       (forall ((x395 Int) (x396 A) (x397 A)) 
                                           (=> 
                                               (and 
                                                   (MS1 x395 x396 s28) 
                                                   (MS1 x395 x397 s28)) 
                                               (= x396 x397))) 
                                       (forall ((x398 Int)) 
                                           (=> 
                                               (and 
                                                   (<= 1 x398) 
                                                   (<= x398 n7)) 
                                               (exists ((x399 A)) 
                                                   (MS1 x398 x399 s28)))))) 
                               (forall ((x400 Int) (x401 A)) 
                                   (= 
                                       (MS1 x400 x401 x392) 
                                       (MS1 x400 x401 s28))))) 
                       (exists ((x402 Int)) 
                           (length x392 x402)))))
         :named hyp64))
(assert (! (and 
               (forall ((x403 PZA) (x404 PZA) (x405 PZA)) 
                   (=> 
                       (cnc x403 x404 x405) 
                       (and 
                           (exists ((s29 PZA)) 
                               (and 
                                   (exists ((n8 Int)) 
                                       (and 
                                           (<= 0 n8) 
                                           (forall ((x406 Int) (x407 A)) 
                                               (=> 
                                                   (MS1 x406 x407 s29) 
                                                   (and 
                                                       (<= 1 x406) 
                                                       (<= x406 n8)))) 
                                           (forall ((x408 Int) (x409 A) (x410 A)) 
                                               (=> 
                                                   (and 
                                                       (MS1 x408 x409 s29) 
                                                       (MS1 x408 x410 s29)) 
                                                   (= x409 x410))) 
                                           (forall ((x411 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x411) 
                                                       (<= x411 n8)) 
                                                   (exists ((x412 A)) 
                                                       (MS1 x411 x412 s29)))))) 
                                   (forall ((x413 Int) (x414 A)) 
                                       (= 
                                           (MS1 x413 x414 x403) 
                                           (MS1 x413 x414 s29))))) 
                           (exists ((s30 PZA)) 
                               (and 
                                   (exists ((n9 Int)) 
                                       (and 
                                           (<= 0 n9) 
                                           (forall ((x415 Int) (x416 A)) 
                                               (=> 
                                                   (MS1 x415 x416 s30) 
                                                   (and 
                                                       (<= 1 x415) 
                                                       (<= x415 n9)))) 
                                           (forall ((x417 Int) (x418 A) (x419 A)) 
                                               (=> 
                                                   (and 
                                                       (MS1 x417 x418 s30) 
                                                       (MS1 x417 x419 s30)) 
                                                   (= x418 x419))) 
                                           (forall ((x420 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x420) 
                                                       (<= x420 n9)) 
                                                   (exists ((x421 A)) 
                                                       (MS1 x420 x421 s30)))))) 
                                   (forall ((x422 Int) (x423 A)) 
                                       (= 
                                           (MS1 x422 x423 x404) 
                                           (MS1 x422 x423 s30))))) 
                           (exists ((s31 PZA)) 
                               (and 
                                   (exists ((n10 Int)) 
                                       (and 
                                           (<= 0 n10) 
                                           (forall ((x424 Int) (x425 A)) 
                                               (=> 
                                                   (MS1 x424 x425 s31) 
                                                   (and 
                                                       (<= 1 x424) 
                                                       (<= x424 n10)))) 
                                           (forall ((x426 Int) (x427 A) (x428 A)) 
                                               (=> 
                                                   (and 
                                                       (MS1 x426 x427 s31) 
                                                       (MS1 x426 x428 s31)) 
                                                   (= x427 x428))) 
                                           (forall ((x429 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x429) 
                                                       (<= x429 n10)) 
                                                   (exists ((x430 A)) 
                                                       (MS1 x429 x430 s31)))))) 
                                   (forall ((x431 Int) (x432 A)) 
                                       (= 
                                           (MS1 x431 x432 x405) 
                                           (MS1 x431 x432 s31)))))))) 
               (forall ((x433 PZA) (x434 PZA) (x435 PZA) (x436 PZA)) 
                   (=> 
                       (and 
                           (cnc x433 x434 x435) 
                           (cnc x433 x434 x436)) 
                       (forall ((x437 Int) (x438 A)) 
                           (= 
                               (MS1 x437 x438 x435) 
                               (MS1 x437 x438 x436))))) 
               (forall ((x439 PZA) (x440 PZA)) 
                   (=> 
                       (and 
                           (exists ((s32 PZA)) 
                               (and 
                                   (exists ((n11 Int)) 
                                       (and 
                                           (<= 0 n11) 
                                           (forall ((x441 Int) (x442 A)) 
                                               (=> 
                                                   (MS1 x441 x442 s32) 
                                                   (and 
                                                       (<= 1 x441) 
                                                       (<= x441 n11)))) 
                                           (forall ((x443 Int) (x444 A) (x445 A)) 
                                               (=> 
                                                   (and 
                                                       (MS1 x443 x444 s32) 
                                                       (MS1 x443 x445 s32)) 
                                                   (= x444 x445))) 
                                           (forall ((x446 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x446) 
                                                       (<= x446 n11)) 
                                                   (exists ((x447 A)) 
                                                       (MS1 x446 x447 s32)))))) 
                                   (forall ((x448 Int) (x449 A)) 
                                       (= 
                                           (MS1 x448 x449 x439) 
                                           (MS1 x448 x449 s32))))) 
                           (exists ((s33 PZA)) 
                               (and 
                                   (exists ((n12 Int)) 
                                       (and 
                                           (<= 0 n12) 
                                           (forall ((x450 Int) (x451 A)) 
                                               (=> 
                                                   (MS1 x450 x451 s33) 
                                                   (and 
                                                       (<= 1 x450) 
                                                       (<= x450 n12)))) 
                                           (forall ((x452 Int) (x453 A) (x454 A)) 
                                               (=> 
                                                   (and 
                                                       (MS1 x452 x453 s33) 
                                                       (MS1 x452 x454 s33)) 
                                                   (= x453 x454))) 
                                           (forall ((x455 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x455) 
                                                       (<= x455 n12)) 
                                                   (exists ((x456 A)) 
                                                       (MS1 x455 x456 s33)))))) 
                                   (forall ((x457 Int) (x458 A)) 
                                       (= 
                                           (MS1 x457 x458 x440) 
                                           (MS1 x457 x458 s33)))))) 
                       (exists ((x459 PZA)) 
                           (cnc x439 x440 x459)))))
         :named hyp65))
(assert (! (and 
               (forall ((x460 PZA) (x461 PZA)) 
                   (=> 
                       (reverse x460 x461) 
                       (and 
                           (exists ((s34 PZA)) 
                               (and 
                                   (exists ((n13 Int)) 
                                       (and 
                                           (<= 0 n13) 
                                           (forall ((x462 Int) (x463 A)) 
                                               (=> 
                                                   (MS1 x462 x463 s34) 
                                                   (and 
                                                       (<= 1 x462) 
                                                       (<= x462 n13)))) 
                                           (forall ((x464 Int) (x465 A) (x466 A)) 
                                               (=> 
                                                   (and 
                                                       (MS1 x464 x465 s34) 
                                                       (MS1 x464 x466 s34)) 
                                                   (= x465 x466))) 
                                           (forall ((x467 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x467) 
                                                       (<= x467 n13)) 
                                                   (exists ((x468 A)) 
                                                       (MS1 x467 x468 s34)))))) 
                                   (forall ((x469 Int) (x470 A)) 
                                       (= 
                                           (MS1 x469 x470 x460) 
                                           (MS1 x469 x470 s34))))) 
                           (exists ((s35 PZA)) 
                               (and 
                                   (exists ((n14 Int)) 
                                       (and 
                                           (<= 0 n14) 
                                           (forall ((x471 Int) (x472 A)) 
                                               (=> 
                                                   (MS1 x471 x472 s35) 
                                                   (and 
                                                       (<= 1 x471) 
                                                       (<= x471 n14)))) 
                                           (forall ((x473 Int) (x474 A) (x475 A)) 
                                               (=> 
                                                   (and 
                                                       (MS1 x473 x474 s35) 
                                                       (MS1 x473 x475 s35)) 
                                                   (= x474 x475))) 
                                           (forall ((x476 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x476) 
                                                       (<= x476 n14)) 
                                                   (exists ((x477 A)) 
                                                       (MS1 x476 x477 s35)))))) 
                                   (forall ((x478 Int) (x479 A)) 
                                       (= 
                                           (MS1 x478 x479 x461) 
                                           (MS1 x478 x479 s35)))))))) 
               (forall ((x480 PZA) (x481 PZA) (x482 PZA)) 
                   (=> 
                       (and 
                           (reverse x480 x481) 
                           (reverse x480 x482)) 
                       (forall ((x483 Int) (x484 A)) 
                           (= 
                               (MS1 x483 x484 x481) 
                               (MS1 x483 x484 x482))))) 
               (forall ((x485 PZA)) 
                   (=> 
                       (exists ((s36 PZA)) 
                           (and 
                               (exists ((n15 Int)) 
                                   (and 
                                       (<= 0 n15) 
                                       (forall ((x486 Int) (x487 A)) 
                                           (=> 
                                               (MS1 x486 x487 s36) 
                                               (and 
                                                   (<= 1 x486) 
                                                   (<= x486 n15)))) 
                                       (forall ((x488 Int) (x489 A) (x490 A)) 
                                           (=> 
                                               (and 
                                                   (MS1 x488 x489 s36) 
                                                   (MS1 x488 x490 s36)) 
                                               (= x489 x490))) 
                                       (forall ((x491 Int)) 
                                           (=> 
                                               (and 
                                                   (<= 1 x491) 
                                                   (<= x491 n15)) 
                                               (exists ((x492 A)) 
                                                   (MS1 x491 x492 s36)))))) 
                               (forall ((x493 Int) (x494 A)) 
                                   (= 
                                       (MS1 x493 x494 x485) 
                                       (MS1 x493 x494 s36))))) 
                       (exists ((x495 PZA)) 
                           (reverse x485 x495)))))
         :named hyp66))
(assert (! (forall ((n16 Int) (s37 PZA)) 
               (=> 
                   (and 
                       (<= 0 n16) 
                       (forall ((x496 Int) (x497 A)) 
                           (=> 
                               (MS1 x496 x497 s37) 
                               (and 
                                   (<= 1 x496) 
                                   (<= x496 n16)))) 
                       (forall ((x498 Int) (x499 A) (x500 A)) 
                           (=> 
                               (and 
                                   (MS1 x498 x499 s37) 
                                   (MS1 x498 x500 s37)) 
                               (= x499 x500))) 
                       (forall ((x501 Int)) 
                           (=> 
                               (and 
                                   (<= 1 x501) 
                                   (<= x501 n16)) 
                               (exists ((x502 A)) 
                                   (MS1 x501 x502 s37))))) 
                   (exists ((n17 Int)) 
                       (and 
                           (<= 0 n17) 
                           (forall ((x503 Int) (x504 A)) 
                               (=> 
                                   (MS1 x503 x504 s37) 
                                   (and 
                                       (<= 1 x503) 
                                       (<= x503 n17)))) 
                           (forall ((x505 Int) (x506 A) (x507 A)) 
                               (=> 
                                   (and 
                                       (MS1 x505 x506 s37) 
                                       (MS1 x505 x507 s37)) 
                                   (= x506 x507))) 
                           (forall ((x508 Int)) 
                               (=> 
                                   (and 
                                       (<= 1 x508) 
                                       (<= x508 n17)) 
                                   (exists ((x509 A)) 
                                       (MS1 x508 x509 s37))))))))
         :named hyp67))
(assert (! (forall ((s38 PZA)) 
               (=> 
                   (exists ((n18 Int)) 
                       (and 
                           (<= 0 n18) 
                           (forall ((x510 Int) (x511 A)) 
                               (=> 
                                   (MS1 x510 x511 s38) 
                                   (and 
                                       (<= 1 x510) 
                                       (<= x510 n18)))) 
                           (forall ((x512 Int) (x513 A) (x514 A)) 
                               (=> 
                                   (and 
                                       (MS1 x512 x513 s38) 
                                       (MS1 x512 x514 s38)) 
                                   (= x513 x514))) 
                           (forall ((x515 Int)) 
                               (=> 
                                   (and 
                                       (<= 1 x515) 
                                       (<= x515 n18)) 
                                   (exists ((x516 A)) 
                                       (MS1 x515 x516 s38)))))) 
                   (and 
                       (forall ((x517 Int) (x518 A)) 
                           (=> 
                               (MS1 x517 x518 s38) 
                               (and 
                                   (<= 1 x517) 
                                   (forall ((x519 Int)) 
                                       (=> 
                                           (length s38 x519) 
                                           (<= x517 x519)))))) 
                       (forall ((x520 Int) (x521 A) (x522 A)) 
                           (=> 
                               (and 
                                   (MS1 x520 x521 s38) 
                                   (MS1 x520 x522 s38)) 
                               (= x521 x522))) 
                       (forall ((x523 Int)) 
                           (=> 
                               (and 
                                   (<= 1 x523) 
                                   (forall ((x524 Int)) 
                                       (=> 
                                           (length s38 x524) 
                                           (<= x523 x524)))) 
                               (exists ((x525 A)) 
                                   (MS1 x523 x525 s38)))))))
         :named hyp68))
(assert (! (forall ((x526 PZA) (x527 PZA) (x528 PZA)) 
               (= 
                   (cnc x526 x527 x528) 
                   (exists ((s110 PZA) (s210 PZA)) 
                       (and 
                           (exists ((n19 Int)) 
                               (and 
                                   (<= 0 n19) 
                                   (forall ((x529 Int) (x530 A)) 
                                       (=> 
                                           (MS1 x529 x530 s110) 
                                           (and 
                                               (<= 1 x529) 
                                               (<= x529 n19)))) 
                                   (forall ((x531 Int) (x532 A) (x533 A)) 
                                       (=> 
                                           (and 
                                               (MS1 x531 x532 s110) 
                                               (MS1 x531 x533 s110)) 
                                           (= x532 x533))) 
                                   (forall ((x534 Int)) 
                                       (=> 
                                           (and 
                                               (<= 1 x534) 
                                               (<= x534 n19)) 
                                           (exists ((x535 A)) 
                                               (MS1 x534 x535 s110)))))) 
                           (exists ((n20 Int)) 
                               (and 
                                   (<= 0 n20) 
                                   (forall ((x536 Int) (x537 A)) 
                                       (=> 
                                           (MS1 x536 x537 s210) 
                                           (and 
                                               (<= 1 x536) 
                                               (<= x536 n20)))) 
                                   (forall ((x538 Int) (x539 A) (x540 A)) 
                                       (=> 
                                           (and 
                                               (MS1 x538 x539 s210) 
                                               (MS1 x538 x540 s210)) 
                                           (= x539 x540))) 
                                   (forall ((x541 Int)) 
                                       (=> 
                                           (and 
                                               (<= 1 x541) 
                                               (<= x541 n20)) 
                                           (exists ((x542 A)) 
                                               (MS1 x541 x542 s210)))))) 
                           (forall ((x543 Int) (x544 A)) 
                               (= 
                                   (MS1 x543 x544 x526) 
                                   (MS1 x543 x544 s110))) 
                           (forall ((x545 Int) (x546 A)) 
                               (= 
                                   (MS1 x545 x546 x527) 
                                   (MS1 x545 x546 s210))) 
                           (forall ((x547 Int) (x548 A)) 
                               (= 
                                   (MS1 x547 x548 x528) 
                                   (or 
                                       (exists ((i15 Int)) 
                                           (and 
                                               (<= 1 i15) 
                                               (forall ((x549 Int)) 
                                                   (=> 
                                                       (length s110 x549) 
                                                       (<= i15 x549))) 
                                               (= x547 i15) 
                                               (MS1 i15 x548 s110))) 
                                       (exists ((i16 Int)) 
                                           (and 
                                               (forall ((x550 Int)) 
                                                   (=> 
                                                       (length s110 x550) 
                                                       (<= (+ x550 1) i16))) 
                                               (forall ((x551 Int) (x552 Int)) 
                                                   (=> 
                                                       (and 
                                                           (length s110 x552) 
                                                           (length s210 x551)) 
                                                       (<= i16 (+ x552 x551)))) 
                                               (= x547 i16) 
                                               (exists ((x553 Int)) 
                                                   (and 
                                                       (forall ((x554 Int)) 
                                                           (=> 
                                                               (length s110 x554) 
                                                               (= x553 (- i16 x554)))) 
                                                       (MS1 x553 x548 s210))))))))))))
         :named hyp69))
(assert (! (forall ((s111 PZA) (s211 PZA)) 
               (=> 
                   (and 
                       (exists ((n21 Int)) 
                           (and 
                               (<= 0 n21) 
                               (forall ((x555 Int) (x556 A)) 
                                   (=> 
                                       (MS1 x555 x556 s111) 
                                       (and 
                                           (<= 1 x555) 
                                           (<= x555 n21)))) 
                               (forall ((x557 Int) (x558 A) (x559 A)) 
                                   (=> 
                                       (and 
                                           (MS1 x557 x558 s111) 
                                           (MS1 x557 x559 s111)) 
                                       (= x558 x559))) 
                               (forall ((x560 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x560) 
                                           (<= x560 n21)) 
                                       (exists ((x561 A)) 
                                           (MS1 x560 x561 s111)))))) 
                       (exists ((n22 Int)) 
                           (and 
                               (<= 0 n22) 
                               (forall ((x562 Int) (x563 A)) 
                                   (=> 
                                       (MS1 x562 x563 s211) 
                                       (and 
                                           (<= 1 x562) 
                                           (<= x562 n22)))) 
                               (forall ((x564 Int) (x565 A) (x566 A)) 
                                   (=> 
                                       (and 
                                           (MS1 x564 x565 s211) 
                                           (MS1 x564 x566 s211)) 
                                       (= x565 x566))) 
                               (forall ((x567 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x567) 
                                           (<= x567 n22)) 
                                       (exists ((x568 A)) 
                                           (MS1 x567 x568 s211))))))) 
                   (exists ((x569 PZA) (x570 Int)) 
                       (and 
                           (cnc s111 s211 x569) 
                           (forall ((x571 Int) (x572 Int)) 
                               (=> 
                                   (and 
                                       (length s111 x572) 
                                       (length s211 x571)) 
                                   (= x570 (+ x572 x571)))) 
                           (length x569 x570)))))
         :named hyp70))
(assert (! (forall ((s112 PZA) (s212 PZA)) 
               (=> 
                   (and 
                       (exists ((n23 Int)) 
                           (and 
                               (<= 0 n23) 
                               (forall ((x573 Int) (x574 A)) 
                                   (=> 
                                       (MS1 x573 x574 s112) 
                                       (and 
                                           (<= 1 x573) 
                                           (<= x573 n23)))) 
                               (forall ((x575 Int) (x576 A) (x577 A)) 
                                   (=> 
                                       (and 
                                           (MS1 x575 x576 s112) 
                                           (MS1 x575 x577 s112)) 
                                       (= x576 x577))) 
                               (forall ((x578 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x578) 
                                           (<= x578 n23)) 
                                       (exists ((x579 A)) 
                                           (MS1 x578 x579 s112)))))) 
                       (exists ((n24 Int)) 
                           (and 
                               (<= 0 n24) 
                               (forall ((x580 Int) (x581 A)) 
                                   (=> 
                                       (MS1 x580 x581 s212) 
                                       (and 
                                           (<= 1 x580) 
                                           (<= x580 n24)))) 
                               (forall ((x582 Int) (x583 A) (x584 A)) 
                                   (=> 
                                       (and 
                                           (MS1 x582 x583 s212) 
                                           (MS1 x582 x584 s212)) 
                                       (= x583 x584))) 
                               (forall ((x585 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x585) 
                                           (<= x585 n24)) 
                                       (exists ((x586 A)) 
                                           (MS1 x585 x586 s212))))))) 
                   (forall ((x587 Int)) 
                       (= 
                           (exists ((x588 A) (x589 PZA)) 
                               (and 
                                   (cnc s112 s212 x589) 
                                   (MS1 x587 x588 x589))) 
                           (and 
                               (<= 1 x587) 
                               (forall ((x590 Int) (x591 Int)) 
                                   (=> 
                                       (and 
                                           (length s112 x591) 
                                           (length s212 x590)) 
                                       (<= x587 (+ x591 x590)))))))))
         :named hyp71))
(assert (! (forall ((s113 PZA) (s213 PZA)) 
               (=> 
                   (and 
                       (exists ((n25 Int)) 
                           (and 
                               (<= 0 n25) 
                               (forall ((x592 Int) (x593 A)) 
                                   (=> 
                                       (MS1 x592 x593 s113) 
                                       (and 
                                           (<= 1 x592) 
                                           (<= x592 n25)))) 
                               (forall ((x594 Int) (x595 A) (x596 A)) 
                                   (=> 
                                       (and 
                                           (MS1 x594 x595 s113) 
                                           (MS1 x594 x596 s113)) 
                                       (= x595 x596))) 
                               (forall ((x597 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x597) 
                                           (<= x597 n25)) 
                                       (exists ((x598 A)) 
                                           (MS1 x597 x598 s113)))))) 
                       (exists ((n26 Int)) 
                           (and 
                               (<= 0 n26) 
                               (forall ((x599 Int) (x600 A)) 
                                   (=> 
                                       (MS1 x599 x600 s213) 
                                       (and 
                                           (<= 1 x599) 
                                           (<= x599 n26)))) 
                               (forall ((x601 Int) (x602 A) (x603 A)) 
                                   (=> 
                                       (and 
                                           (MS1 x601 x602 s213) 
                                           (MS1 x601 x603 s213)) 
                                       (= x602 x603))) 
                               (forall ((x604 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x604) 
                                           (<= x604 n26)) 
                                       (exists ((x605 A)) 
                                           (MS1 x604 x605 s213))))))) 
                   (forall ((x606 A)) 
                       (= 
                           (exists ((x607 Int) (x608 PZA)) 
                               (and 
                                   (cnc s113 s213 x608) 
                                   (MS1 x607 x606 x608))) 
                           (or 
                               (exists ((x609 Int)) 
                                   (MS1 x609 x606 s113)) 
                               (exists ((x610 Int)) 
                                   (MS1 x610 x606 s213)))))))
         :named hyp72))
(assert (! (forall ((s114 PZA) (s214 PZA) (i17 Int)) 
               (=> 
                   (and 
                       (exists ((n27 Int)) 
                           (and 
                               (<= 0 n27) 
                               (forall ((x611 Int) (x612 A)) 
                                   (=> 
                                       (MS1 x611 x612 s114) 
                                       (and 
                                           (<= 1 x611) 
                                           (<= x611 n27)))) 
                               (forall ((x613 Int) (x614 A) (x615 A)) 
                                   (=> 
                                       (and 
                                           (MS1 x613 x614 s114) 
                                           (MS1 x613 x615 s114)) 
                                       (= x614 x615))) 
                               (forall ((x616 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x616) 
                                           (<= x616 n27)) 
                                       (exists ((x617 A)) 
                                           (MS1 x616 x617 s114)))))) 
                       (exists ((n28 Int)) 
                           (and 
                               (<= 0 n28) 
                               (forall ((x618 Int) (x619 A)) 
                                   (=> 
                                       (MS1 x618 x619 s214) 
                                       (and 
                                           (<= 1 x618) 
                                           (<= x618 n28)))) 
                               (forall ((x620 Int) (x621 A) (x622 A)) 
                                   (=> 
                                       (and 
                                           (MS1 x620 x621 s214) 
                                           (MS1 x620 x622 s214)) 
                                       (= x621 x622))) 
                               (forall ((x623 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x623) 
                                           (<= x623 n28)) 
                                       (exists ((x624 A)) 
                                           (MS1 x623 x624 s214)))))) 
                       (<= 1 i17) 
                       (forall ((x625 Int)) 
                           (=> 
                               (length s114 x625) 
                               (<= i17 x625)))) 
                   (exists ((x626 PZA)) 
                       (and 
                           (cnc s114 s214 x626) 
                           (exists ((x627 A)) 
                               (and 
                                   (MS1 i17 x627 s114) 
                                   (MS1 i17 x627 x626)))))))
         :named hyp73))
(assert (! (forall ((s115 PZA) (s215 PZA) (i18 Int)) 
               (=> 
                   (and 
                       (exists ((n29 Int)) 
                           (and 
                               (<= 0 n29) 
                               (forall ((x628 Int) (x629 A)) 
                                   (=> 
                                       (MS1 x628 x629 s115) 
                                       (and 
                                           (<= 1 x628) 
                                           (<= x628 n29)))) 
                               (forall ((x630 Int) (x631 A) (x632 A)) 
                                   (=> 
                                       (and 
                                           (MS1 x630 x631 s115) 
                                           (MS1 x630 x632 s115)) 
                                       (= x631 x632))) 
                               (forall ((x633 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x633) 
                                           (<= x633 n29)) 
                                       (exists ((x634 A)) 
                                           (MS1 x633 x634 s115)))))) 
                       (exists ((n30 Int)) 
                           (and 
                               (<= 0 n30) 
                               (forall ((x635 Int) (x636 A)) 
                                   (=> 
                                       (MS1 x635 x636 s215) 
                                       (and 
                                           (<= 1 x635) 
                                           (<= x635 n30)))) 
                               (forall ((x637 Int) (x638 A) (x639 A)) 
                                   (=> 
                                       (and 
                                           (MS1 x637 x638 s215) 
                                           (MS1 x637 x639 s215)) 
                                       (= x638 x639))) 
                               (forall ((x640 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x640) 
                                           (<= x640 n30)) 
                                       (exists ((x641 A)) 
                                           (MS1 x640 x641 s215)))))) 
                       (forall ((x642 Int)) 
                           (=> 
                               (length s115 x642) 
                               (<= (+ x642 1) i18))) 
                       (forall ((x643 Int) (x644 Int)) 
                           (=> 
                               (and 
                                   (length s115 x644) 
                                   (length s215 x643)) 
                               (<= i18 (+ x644 x643))))) 
                   (exists ((x645 PZA)) 
                       (and 
                           (cnc s115 s215 x645) 
                           (exists ((x646 A)) 
                               (and 
                                   (exists ((x647 Int)) 
                                       (and 
                                           (forall ((x648 Int)) 
                                               (=> 
                                                   (length s115 x648) 
                                                   (= x647 (- i18 x648)))) 
                                           (MS1 x647 x646 s215))) 
                                   (MS1 i18 x646 x645)))))))
         :named hyp74))
(assert (! (forall ((x649 PZA) (x650 PZA)) 
               (= 
                   (reverse x649 x650) 
                   (exists ((s39 PZA)) 
                       (and 
                           (exists ((n31 Int)) 
                               (and 
                                   (<= 0 n31) 
                                   (forall ((x651 Int) (x652 A)) 
                                       (=> 
                                           (MS1 x651 x652 s39) 
                                           (and 
                                               (<= 1 x651) 
                                               (<= x651 n31)))) 
                                   (forall ((x653 Int) (x654 A) (x655 A)) 
                                       (=> 
                                           (and 
                                               (MS1 x653 x654 s39) 
                                               (MS1 x653 x655 s39)) 
                                           (= x654 x655))) 
                                   (forall ((x656 Int)) 
                                       (=> 
                                           (and 
                                               (<= 1 x656) 
                                               (<= x656 n31)) 
                                           (exists ((x657 A)) 
                                               (MS1 x656 x657 s39)))))) 
                           (forall ((x658 Int) (x659 A)) 
                               (= 
                                   (MS1 x658 x659 x649) 
                                   (MS1 x658 x659 s39))) 
                           (forall ((x660 Int) (x661 A)) 
                               (= 
                                   (MS1 x660 x661 x650) 
                                   (exists ((i19 Int)) 
                                       (and 
                                           (<= 1 i19) 
                                           (forall ((x662 Int)) 
                                               (=> 
                                                   (length s39 x662) 
                                                   (<= i19 x662))) 
                                           (= x660 i19) 
                                           (exists ((x663 Int)) 
                                               (and 
                                                   (forall ((x664 Int)) 
                                                       (=> 
                                                           (length s39 x664) 
                                                           (= x663 (+ (- x664 i19) 1)))) 
                                                   (MS1 x663 x661 s39)))))))))))
         :named hyp75))
(assert (! (forall ((s40 PZA)) 
               (=> 
                   (exists ((n32 Int)) 
                       (and 
                           (<= 0 n32) 
                           (forall ((x665 Int) (x666 A)) 
                               (=> 
                                   (MS1 x665 x666 s40) 
                                   (and 
                                       (<= 1 x665) 
                                       (<= x665 n32)))) 
                           (forall ((x667 Int) (x668 A) (x669 A)) 
                               (=> 
                                   (and 
                                       (MS1 x667 x668 s40) 
                                       (MS1 x667 x669 s40)) 
                                   (= x668 x669))) 
                           (forall ((x670 Int)) 
                               (=> 
                                   (and 
                                       (<= 1 x670) 
                                       (<= x670 n32)) 
                                   (exists ((x671 A)) 
                                       (MS1 x670 x671 s40)))))) 
                   (exists ((x672 PZA) (x673 Int)) 
                       (and 
                           (reverse s40 x672) 
                           (length s40 x673) 
                           (length x672 x673)))))
         :named hyp76))
(assert (! (forall ((s41 PZA)) 
               (=> 
                   (exists ((n33 Int)) 
                       (and 
                           (<= 0 n33) 
                           (forall ((x674 Int) (x675 A)) 
                               (=> 
                                   (MS1 x674 x675 s41) 
                                   (and 
                                       (<= 1 x674) 
                                       (<= x674 n33)))) 
                           (forall ((x676 Int) (x677 A) (x678 A)) 
                               (=> 
                                   (and 
                                       (MS1 x676 x677 s41) 
                                       (MS1 x676 x678 s41)) 
                                   (= x677 x678))) 
                           (forall ((x679 Int)) 
                               (=> 
                                   (and 
                                       (<= 1 x679) 
                                       (<= x679 n33)) 
                                   (exists ((x680 A)) 
                                       (MS1 x679 x680 s41)))))) 
                   (forall ((x681 A)) 
                       (= 
                           (exists ((x682 Int) (x683 PZA)) 
                               (and 
                                   (reverse s41 x683) 
                                   (MS1 x682 x681 x683))) 
                           (exists ((x684 Int)) 
                               (MS1 x684 x681 s41))))))
         :named hyp77))
(assert (! (forall ((s42 PZA)) 
               (=> 
                   (exists ((n34 Int)) 
                       (and 
                           (<= 0 n34) 
                           (forall ((x685 Int) (x686 A)) 
                               (=> 
                                   (MS1 x685 x686 s42) 
                                   (and 
                                       (<= 1 x685) 
                                       (<= x685 n34)))) 
                           (forall ((x687 Int) (x688 A) (x689 A)) 
                               (=> 
                                   (and 
                                       (MS1 x687 x688 s42) 
                                       (MS1 x687 x689 s42)) 
                                   (= x688 x689))) 
                           (forall ((x690 Int)) 
                               (=> 
                                   (and 
                                       (<= 1 x690) 
                                       (<= x690 n34)) 
                                   (exists ((x691 A)) 
                                       (MS1 x690 x691 s42)))))) 
                   (exists ((x692 PZA)) 
                       (and 
                           (reverse s42 x692) 
                           (reverse x692 s42)))))
         :named hyp78))
(assert (! (forall ((x693 A) (y18 A) (p11 PZA) (i20 Int)) 
               (=> 
                   (and 
                       (MS0 x693 a) 
                       (MS0 y18 a) 
                       (exists ((n35 Int)) 
                           (and 
                               (<= 0 n35) 
                               (forall ((x694 Int) (x695 A)) 
                                   (=> 
                                       (MS1 x694 x695 p11) 
                                       (and 
                                           (<= 1 x694) 
                                           (<= x694 n35)))) 
                               (forall ((x696 Int) (x697 A) (x698 A)) 
                                   (=> 
                                       (and 
                                           (MS1 x696 x697 p11) 
                                           (MS1 x696 x698 p11)) 
                                       (= x697 x698))) 
                               (forall ((x699 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x699) 
                                           (<= x699 n35)) 
                                       (exists ((x700 A)) 
                                           (MS1 x699 x700 p11)))))) 
                       (shpath x693 y18 p11) 
                       (exists ((x701 A)) 
                           (MS1 i20 x701 p11)) 
                       (not 
                           (= i20 1)) 
                       (not 
                           (length p11 i20))) 
                   (exists ((x702 A) (x703 PZA)) 
                       (and 
                           (MS1 i20 x702 p11) 
                           (forall ((x704 Int) (x705 A)) 
                               (= 
                                   (MS1 x704 x705 x703) 
                                   (and 
                                       (MS1 x704 x705 p11) 
                                       (<= 1 x704) 
                                       (<= x704 i20)))) 
                           (shpath x693 x702 x703)))))
         :named hyp79))
(assert (! (forall ((x706 A) (y19 A) (p12 PZA) (i21 Int)) 
               (=> 
                   (and 
                       (MS0 x706 a) 
                       (MS0 y19 a) 
                       (exists ((n36 Int)) 
                           (and 
                               (<= 0 n36) 
                               (forall ((x707 Int) (x708 A)) 
                                   (=> 
                                       (MS1 x707 x708 p12) 
                                       (and 
                                           (<= 1 x707) 
                                           (<= x707 n36)))) 
                               (forall ((x709 Int) (x710 A) (x711 A)) 
                                   (=> 
                                       (and 
                                           (MS1 x709 x710 p12) 
                                           (MS1 x709 x711 p12)) 
                                       (= x710 x711))) 
                               (forall ((x712 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x712) 
                                           (<= x712 n36)) 
                                       (exists ((x713 A)) 
                                           (MS1 x712 x713 p12)))))) 
                       (shpath x706 y19 p12) 
                       (exists ((x714 A)) 
                           (MS1 i21 x714 p12)) 
                       (not 
                           (= i21 1)) 
                       (not 
                           (length p12 i21))) 
                   (and 
                       (exists ((x715 A)) 
                           (and 
                               (MS1 i21 x715 p12) 
                               (dist x706 x715 i21))) 
                       (exists ((x716 A) (x717 Int)) 
                           (and 
                               (exists ((x718 Int)) 
                                   (and 
                                       (= x718 (+ i21 1)) 
                                       (MS1 x718 x716 p12))) 
                               (= x717 (+ i21 1)) 
                               (dist x706 x716 x717))) 
                       (exists ((x719 A) (x720 A)) 
                           (and 
                               (MS1 i21 x719 p12) 
                               (exists ((x721 Int)) 
                                   (and 
                                       (= x721 (+ i21 1)) 
                                       (MS1 x721 x720 p12))) 
                               (MS x719 x720 r))))))
         :named hyp80))
(assert (! (forall ((x722 A) (y20 A) (p13 PZA) (z2 A)) 
               (=> 
                   (and 
                       (MS0 x722 a) 
                       (MS0 y20 a) 
                       (exists ((n37 Int)) 
                           (and 
                               (<= 0 n37) 
                               (forall ((x723 Int) (x724 A)) 
                                   (=> 
                                       (MS1 x723 x724 p13) 
                                       (and 
                                           (<= 1 x723) 
                                           (<= x723 n37)))) 
                               (forall ((x725 Int) (x726 A) (x727 A)) 
                                   (=> 
                                       (and 
                                           (MS1 x725 x726 p13) 
                                           (MS1 x725 x727 p13)) 
                                       (= x726 x727))) 
                               (forall ((x728 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x728) 
                                           (<= x728 n37)) 
                                       (exists ((x729 A)) 
                                           (MS1 x728 x729 p13)))))) 
                       (shpath x722 y20 p13) 
                       (exists ((x730 Int)) 
                           (MS1 x730 z2 p13)) 
                       (not 
                           (= z2 x722)) 
                       (not 
                           (= z2 y20))) 
                   (exists ((t1 A)) 
                       (and 
                           (MS0 t1 a) 
                           (forall ((x731 Int) (x732 Int)) 
                               (=> 
                                   (and 
                                       (dist x722 z2 x732) 
                                       (dist x722 t1 x731)) 
                                   (< x732 x731))) 
                           (MS z2 t1 r)))))
         :named hyp81))
(assert (! (forall ((s116 PZA) (s216 PZA) (b0 PA)) 
               (=> 
                   (and 
                       (exists ((n38 Int)) 
                           (and 
                               (<= 0 n38) 
                               (forall ((x733 Int) (x734 A)) 
                                   (=> 
                                       (MS1 x733 x734 s116) 
                                       (and 
                                           (<= 1 x733) 
                                           (<= x733 n38)))) 
                               (forall ((x735 Int) (x736 A) (x737 A)) 
                                   (=> 
                                       (and 
                                           (MS1 x735 x736 s116) 
                                           (MS1 x735 x737 s116)) 
                                       (= x736 x737))) 
                               (forall ((x738 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x738) 
                                           (<= x738 n38)) 
                                       (exists ((x739 A)) 
                                           (MS1 x738 x739 s116)))))) 
                       (exists ((n39 Int)) 
                           (and 
                               (<= 0 n39) 
                               (forall ((x740 Int) (x741 A)) 
                                   (=> 
                                       (MS1 x740 x741 s216) 
                                       (and 
                                           (<= 1 x740) 
                                           (<= x740 n39)))) 
                               (forall ((x742 Int) (x743 A) (x744 A)) 
                                   (=> 
                                       (and 
                                           (MS1 x742 x743 s216) 
                                           (MS1 x742 x744 s216)) 
                                       (= x743 x744))) 
                               (forall ((x745 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x745) 
                                           (<= x745 n39)) 
                                       (exists ((x746 A)) 
                                           (MS1 x745 x746 s216)))))) 
                       (forall ((x747 A)) 
                           (=> 
                               (exists ((x748 Int)) 
                                   (MS1 x748 x747 s116)) 
                               (MS0 x747 b0))) 
                       (forall ((x749 A)) 
                           (=> 
                               (exists ((x750 Int)) 
                                   (MS1 x750 x749 s216)) 
                               (MS0 x749 b0)))) 
                   (and 
                       (forall ((x751 Int) (x752 A)) 
                           (=> 
                               (exists ((x753 PZA)) 
                                   (and 
                                       (cnc s116 s216 x753) 
                                       (MS1 x751 x752 x753))) 
                               (and 
                                   (<= 1 x751) 
                                   (forall ((x754 Int) (x755 Int)) 
                                       (=> 
                                           (and 
                                               (length s116 x755) 
                                               (length s216 x754)) 
                                           (<= x751 (+ x755 x754)))) 
                                   (MS0 x752 b0)))) 
                       (forall ((x756 Int) (x757 A) (x758 A)) 
                           (=> 
                               (and 
                                   (exists ((x759 PZA)) 
                                       (and 
                                           (cnc s116 s216 x759) 
                                           (MS1 x756 x757 x759))) 
                                   (exists ((x760 PZA)) 
                                       (and 
                                           (cnc s116 s216 x760) 
                                           (MS1 x756 x758 x760)))) 
                               (= x757 x758))) 
                       (forall ((x761 Int)) 
                           (=> 
                               (and 
                                   (<= 1 x761) 
                                   (forall ((x762 Int) (x763 Int)) 
                                       (=> 
                                           (and 
                                               (length s116 x763) 
                                               (length s216 x762)) 
                                           (<= x761 (+ x763 x762))))) 
                               (exists ((x764 A) (x765 PZA)) 
                                   (and 
                                       (cnc s116 s216 x765) 
                                       (MS1 x761 x764 x765))))))))
         :named hyp82))
(assert (! (forall ((x766 A) (x767 A) (x768 PZA)) 
               (= 
                   (path x766 x767 x768) 
                   (exists ((x769 A) (y21 A) (p14 PZA)) 
                       (and 
                           (exists ((n40 Int)) 
                               (and 
                                   (<= 0 n40) 
                                   (forall ((x770 Int) (x771 A)) 
                                       (=> 
                                           (MS1 x770 x771 p14) 
                                           (and 
                                               (<= 1 x770) 
                                               (<= x770 n40)))) 
                                   (forall ((x772 Int) (x773 A) (x774 A)) 
                                       (=> 
                                           (and 
                                               (MS1 x772 x773 p14) 
                                               (MS1 x772 x774 p14)) 
                                           (= x773 x774))) 
                                   (forall ((x775 Int)) 
                                       (=> 
                                           (and 
                                               (<= 1 x775) 
                                               (<= x775 n40)) 
                                           (exists ((x776 A)) 
                                               (MS1 x775 x776 p14)))))) 
                           (forall ((x777 A)) 
                               (=> 
                                   (exists ((x778 Int)) 
                                       (MS1 x778 x777 p14)) 
                                   (MS0 x777 a))) 
                           (forall ((x779 Int)) 
                               (=> 
                                   (length p14 x779) 
                                   (< 1 x779))) 
                           (exists ((x780 Int)) 
                               (and 
                                   (= x780 1) 
                                   (MS1 x780 x769 p14))) 
                           (exists ((x781 Int)) 
                               (and 
                                   (length p14 x781) 
                                   (MS1 x781 y21 p14))) 
                           (forall ((i22 Int)) 
                               (=> 
                                   (and 
                                       (<= 1 i22) 
                                       (forall ((x782 Int)) 
                                           (=> 
                                               (length p14 x782) 
                                               (<= i22 (- x782 1))))) 
                                   (exists ((x783 A) (x784 A)) 
                                       (and 
                                           (MS1 i22 x783 p14) 
                                           (exists ((x785 Int)) 
                                               (and 
                                                   (= x785 (+ i22 1)) 
                                                   (MS1 x785 x784 p14))) 
                                           (MS x783 x784 r))))) 
                           (= x766 x769) 
                           (= x767 y21) 
                           (forall ((x786 Int) (x787 A)) 
                               (= 
                                   (MS1 x786 x787 x768) 
                                   (MS1 x786 x787 p14)))))))
         :named hyp83))
(assert (! (forall ((x788 A) (y22 A)) 
               (=> 
                   (and 
                       (MS0 x788 a) 
                       (MS0 y22 a)) 
                   (exists ((p15 PZA)) 
                       (and 
                           (path x788 y22 p15) 
                           (exists ((x789 Int)) 
                               (and 
                                   (length p15 x789) 
                                   (dist x788 y22 x789)))))))
         :named hyp84))
(assert (! (forall ((x790 A) (y23 A) (p16 PZA) (i23 Int)) 
               (=> 
                   (and 
                       (MS0 x790 a) 
                       (MS0 y23 a) 
                       (exists ((n41 Int)) 
                           (and 
                               (<= 0 n41) 
                               (forall ((x791 Int) (x792 A)) 
                                   (=> 
                                       (MS1 x791 x792 p16) 
                                       (and 
                                           (<= 1 x791) 
                                           (<= x791 n41)))) 
                               (forall ((x793 Int) (x794 A) (x795 A)) 
                                   (=> 
                                       (and 
                                           (MS1 x793 x794 p16) 
                                           (MS1 x793 x795 p16)) 
                                       (= x794 x795))) 
                               (forall ((x796 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x796) 
                                           (<= x796 n41)) 
                                       (exists ((x797 A)) 
                                           (MS1 x796 x797 p16)))))) 
                       (path x790 y23 p16) 
                       (exists ((x798 Int)) 
                           (and 
                               (length p16 x798) 
                               (dist x790 y23 x798))) 
                       (exists ((x799 A)) 
                           (MS1 i23 x799 p16)) 
                       (not 
                           (= i23 1)) 
                       (not 
                           (length p16 i23))) 
                   (and 
                       (exists ((x800 A) (x801 PZA)) 
                           (and 
                               (MS1 i23 x800 p16) 
                               (forall ((x802 Int) (x803 A)) 
                                   (= 
                                       (MS1 x802 x803 x801) 
                                       (and 
                                           (MS1 x802 x803 p16) 
                                           (<= 1 x802) 
                                           (<= x802 i23)))) 
                               (path x790 x800 x801))) 
                       (exists ((x804 A) (x805 Int)) 
                           (and 
                               (MS1 i23 x804 p16) 
                               (exists ((x806 PZA)) 
                                   (and 
                                       (forall ((x807 Int) (x808 A)) 
                                           (= 
                                               (MS1 x807 x808 x806) 
                                               (and 
                                                   (MS1 x807 x808 p16) 
                                                   (<= 1 x807) 
                                                   (<= x807 i23)))) 
                                       (length x806 x805))) 
                               (dist x790 x804 x805))))))
         :named hyp85))
(assert (! (forall ((x809 A) (y24 A) (p17 PZA) (i24 Int)) 
               (=> 
                   (and 
                       (MS0 x809 a) 
                       (MS0 y24 a) 
                       (exists ((n42 Int)) 
                           (and 
                               (<= 0 n42) 
                               (forall ((x810 Int) (x811 A)) 
                                   (=> 
                                       (MS1 x810 x811 p17) 
                                       (and 
                                           (<= 1 x810) 
                                           (<= x810 n42)))) 
                               (forall ((x812 Int) (x813 A) (x814 A)) 
                                   (=> 
                                       (and 
                                           (MS1 x812 x813 p17) 
                                           (MS1 x812 x814 p17)) 
                                       (= x813 x814))) 
                               (forall ((x815 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x815) 
                                           (<= x815 n42)) 
                                       (exists ((x816 A)) 
                                           (MS1 x815 x816 p17)))))) 
                       (path x809 y24 p17) 
                       (exists ((x817 Int)) 
                           (and 
                               (length p17 x817) 
                               (dist x809 y24 x817))) 
                       (exists ((x818 A)) 
                           (MS1 i24 x818 p17)) 
                       (not 
                           (= i24 1)) 
                       (not 
                           (length p17 i24))) 
                   (and 
                       (exists ((x819 A)) 
                           (and 
                               (MS1 i24 x819 p17) 
                               (dist x809 x819 i24))) 
                       (exists ((x820 A) (x821 Int)) 
                           (and 
                               (exists ((x822 Int)) 
                                   (and 
                                       (= x822 (+ i24 1)) 
                                       (MS1 x822 x820 p17))) 
                               (= x821 (+ i24 1)) 
                               (dist x809 x820 x821))) 
                       (exists ((x823 A) (x824 A)) 
                           (and 
                               (MS1 i24 x823 p17) 
                               (exists ((x825 Int)) 
                                   (and 
                                       (= x825 (+ i24 1)) 
                                       (MS1 x825 x824 p17))) 
                               (MS x823 x824 r))))))
         :named hyp86))
(assert (! (forall ((x826 A) (y25 A) (p18 PZA) (z3 A)) 
               (=> 
                   (and 
                       (MS0 x826 a) 
                       (MS0 y25 a) 
                       (exists ((n43 Int)) 
                           (and 
                               (<= 0 n43) 
                               (forall ((x827 Int) (x828 A)) 
                                   (=> 
                                       (MS1 x827 x828 p18) 
                                       (and 
                                           (<= 1 x827) 
                                           (<= x827 n43)))) 
                               (forall ((x829 Int) (x830 A) (x831 A)) 
                                   (=> 
                                       (and 
                                           (MS1 x829 x830 p18) 
                                           (MS1 x829 x831 p18)) 
                                       (= x830 x831))) 
                               (forall ((x832 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x832) 
                                           (<= x832 n43)) 
                                       (exists ((x833 A)) 
                                           (MS1 x832 x833 p18)))))) 
                       (path x826 y25 p18) 
                       (exists ((x834 Int)) 
                           (and 
                               (length p18 x834) 
                               (dist x826 y25 x834))) 
                       (exists ((x835 Int)) 
                           (MS1 x835 z3 p18)) 
                       (not 
                           (= z3 x826)) 
                       (not 
                           (= z3 y25))) 
                   (exists ((t2 A)) 
                       (and 
                           (MS0 t2 a) 
                           (forall ((x836 Int) (x837 Int)) 
                               (=> 
                                   (and 
                                       (dist x826 z3 x837) 
                                       (dist x826 t2 x836)) 
                                   (< x837 x836))) 
                           (MS z3 t2 r)))))
         :named hyp87))
(assert (! (and 
               (forall ((x838 PZA) (x839 PZA) (x840 PZA)) 
                   (=> 
                       (exists ((s117 PZA) (s217 PZA)) 
                           (and 
                               (exists ((n44 Int)) 
                                   (and 
                                       (<= 0 n44) 
                                       (forall ((x841 Int) (x842 A)) 
                                           (=> 
                                               (MS1 x841 x842 s117) 
                                               (and 
                                                   (<= 1 x841) 
                                                   (<= x841 n44)))) 
                                       (forall ((x843 Int) (x844 A) (x845 A)) 
                                           (=> 
                                               (and 
                                                   (MS1 x843 x844 s117) 
                                                   (MS1 x843 x845 s117)) 
                                               (= x844 x845))) 
                                       (forall ((x846 Int)) 
                                           (=> 
                                               (and 
                                                   (<= 1 x846) 
                                                   (<= x846 n44)) 
                                               (exists ((x847 A)) 
                                                   (MS1 x846 x847 s117)))))) 
                               (exists ((n45 Int)) 
                                   (and 
                                       (<= 0 n45) 
                                       (forall ((x848 Int) (x849 A)) 
                                           (=> 
                                               (MS1 x848 x849 s217) 
                                               (and 
                                                   (<= 1 x848) 
                                                   (<= x848 n45)))) 
                                       (forall ((x850 Int) (x851 A) (x852 A)) 
                                           (=> 
                                               (and 
                                                   (MS1 x850 x851 s217) 
                                                   (MS1 x850 x852 s217)) 
                                               (= x851 x852))) 
                                       (forall ((x853 Int)) 
                                           (=> 
                                               (and 
                                                   (<= 1 x853) 
                                                   (<= x853 n45)) 
                                               (exists ((x854 A)) 
                                                   (MS1 x853 x854 s217)))))) 
                               (forall ((x855 Int) (x856 A)) 
                                   (= 
                                       (MS1 x855 x856 x838) 
                                       (MS1 x855 x856 s117))) 
                               (forall ((x857 Int) (x858 A)) 
                                   (= 
                                       (MS1 x857 x858 x839) 
                                       (MS1 x857 x858 s217))) 
                               (forall ((x859 Int) (x860 A)) 
                                   (= 
                                       (MS1 x859 x860 x840) 
                                       (or 
                                           (exists ((i25 Int)) 
                                               (and 
                                                   (<= 1 i25) 
                                                   (forall ((x861 Int)) 
                                                       (=> 
                                                           (length s117 x861) 
                                                           (<= i25 x861))) 
                                                   (= x859 i25) 
                                                   (MS1 i25 x860 s117))) 
                                           (exists ((i26 Int)) 
                                               (and 
                                                   (forall ((x862 Int)) 
                                                       (=> 
                                                           (length s117 x862) 
                                                           (<= (+ x862 1) i26))) 
                                                   (forall ((x863 Int) (x864 Int)) 
                                                       (=> 
                                                           (and 
                                                               (length s117 x864) 
                                                               (length s217 x863)) 
                                                           (<= i26 (+ x864 x863)))) 
                                                   (= x859 i26) 
                                                   (exists ((x865 Int)) 
                                                       (and 
                                                           (forall ((x866 Int)) 
                                                               (=> 
                                                                   (length s117 x866) 
                                                                   (= x865 (- i26 x866)))) 
                                                           (MS1 x865 x860 s217)))))))))) 
                       (and 
                           (exists ((s43 PZA)) 
                               (and 
                                   (exists ((n46 Int)) 
                                       (and 
                                           (<= 0 n46) 
                                           (forall ((x867 Int) (x868 A)) 
                                               (=> 
                                                   (MS1 x867 x868 s43) 
                                                   (and 
                                                       (<= 1 x867) 
                                                       (<= x867 n46)))) 
                                           (forall ((x869 Int) (x870 A) (x871 A)) 
                                               (=> 
                                                   (and 
                                                       (MS1 x869 x870 s43) 
                                                       (MS1 x869 x871 s43)) 
                                                   (= x870 x871))) 
                                           (forall ((x872 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x872) 
                                                       (<= x872 n46)) 
                                                   (exists ((x873 A)) 
                                                       (MS1 x872 x873 s43)))))) 
                                   (forall ((x874 Int) (x875 A)) 
                                       (= 
                                           (MS1 x874 x875 x838) 
                                           (MS1 x874 x875 s43))))) 
                           (exists ((s44 PZA)) 
                               (and 
                                   (exists ((n47 Int)) 
                                       (and 
                                           (<= 0 n47) 
                                           (forall ((x876 Int) (x877 A)) 
                                               (=> 
                                                   (MS1 x876 x877 s44) 
                                                   (and 
                                                       (<= 1 x876) 
                                                       (<= x876 n47)))) 
                                           (forall ((x878 Int) (x879 A) (x880 A)) 
                                               (=> 
                                                   (and 
                                                       (MS1 x878 x879 s44) 
                                                       (MS1 x878 x880 s44)) 
                                                   (= x879 x880))) 
                                           (forall ((x881 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x881) 
                                                       (<= x881 n47)) 
                                                   (exists ((x882 A)) 
                                                       (MS1 x881 x882 s44)))))) 
                                   (forall ((x883 Int) (x884 A)) 
                                       (= 
                                           (MS1 x883 x884 x839) 
                                           (MS1 x883 x884 s44))))) 
                           (exists ((s45 PZA)) 
                               (and 
                                   (exists ((n48 Int)) 
                                       (and 
                                           (<= 0 n48) 
                                           (forall ((x885 Int) (x886 A)) 
                                               (=> 
                                                   (MS1 x885 x886 s45) 
                                                   (and 
                                                       (<= 1 x885) 
                                                       (<= x885 n48)))) 
                                           (forall ((x887 Int) (x888 A) (x889 A)) 
                                               (=> 
                                                   (and 
                                                       (MS1 x887 x888 s45) 
                                                       (MS1 x887 x889 s45)) 
                                                   (= x888 x889))) 
                                           (forall ((x890 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x890) 
                                                       (<= x890 n48)) 
                                                   (exists ((x891 A)) 
                                                       (MS1 x890 x891 s45)))))) 
                                   (forall ((x892 Int) (x893 A)) 
                                       (= 
                                           (MS1 x892 x893 x840) 
                                           (MS1 x892 x893 s45)))))))) 
               (forall ((x894 PZA) (x895 PZA) (x896 PZA) (x897 PZA)) 
                   (=> 
                       (and 
                           (exists ((s118 PZA) (s218 PZA)) 
                               (and 
                                   (exists ((n49 Int)) 
                                       (and 
                                           (<= 0 n49) 
                                           (forall ((x898 Int) (x899 A)) 
                                               (=> 
                                                   (MS1 x898 x899 s118) 
                                                   (and 
                                                       (<= 1 x898) 
                                                       (<= x898 n49)))) 
                                           (forall ((x900 Int) (x901 A) (x902 A)) 
                                               (=> 
                                                   (and 
                                                       (MS1 x900 x901 s118) 
                                                       (MS1 x900 x902 s118)) 
                                                   (= x901 x902))) 
                                           (forall ((x903 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x903) 
                                                       (<= x903 n49)) 
                                                   (exists ((x904 A)) 
                                                       (MS1 x903 x904 s118)))))) 
                                   (exists ((n50 Int)) 
                                       (and 
                                           (<= 0 n50) 
                                           (forall ((x905 Int) (x906 A)) 
                                               (=> 
                                                   (MS1 x905 x906 s218) 
                                                   (and 
                                                       (<= 1 x905) 
                                                       (<= x905 n50)))) 
                                           (forall ((x907 Int) (x908 A) (x909 A)) 
                                               (=> 
                                                   (and 
                                                       (MS1 x907 x908 s218) 
                                                       (MS1 x907 x909 s218)) 
                                                   (= x908 x909))) 
                                           (forall ((x910 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x910) 
                                                       (<= x910 n50)) 
                                                   (exists ((x911 A)) 
                                                       (MS1 x910 x911 s218)))))) 
                                   (forall ((x912 Int) (x913 A)) 
                                       (= 
                                           (MS1 x912 x913 x894) 
                                           (MS1 x912 x913 s118))) 
                                   (forall ((x914 Int) (x915 A)) 
                                       (= 
                                           (MS1 x914 x915 x895) 
                                           (MS1 x914 x915 s218))) 
                                   (forall ((x916 Int) (x917 A)) 
                                       (= 
                                           (MS1 x916 x917 x896) 
                                           (or 
                                               (exists ((i27 Int)) 
                                                   (and 
                                                       (<= 1 i27) 
                                                       (forall ((x918 Int)) 
                                                           (=> 
                                                               (length s118 x918) 
                                                               (<= i27 x918))) 
                                                       (= x916 i27) 
                                                       (MS1 i27 x917 s118))) 
                                               (exists ((i28 Int)) 
                                                   (and 
                                                       (forall ((x919 Int)) 
                                                           (=> 
                                                               (length s118 x919) 
                                                               (<= (+ x919 1) i28))) 
                                                       (forall ((x920 Int) (x921 Int)) 
                                                           (=> 
                                                               (and 
                                                                   (length s118 x921) 
                                                                   (length s218 x920)) 
                                                               (<= i28 (+ x921 x920)))) 
                                                       (= x916 i28) 
                                                       (exists ((x922 Int)) 
                                                           (and 
                                                               (forall ((x923 Int)) 
                                                                   (=> 
                                                                       (length s118 x923) 
                                                                       (= x922 (- i28 x923)))) 
                                                               (MS1 x922 x917 s218)))))))))) 
                           (exists ((s119 PZA) (s219 PZA)) 
                               (and 
                                   (exists ((n51 Int)) 
                                       (and 
                                           (<= 0 n51) 
                                           (forall ((x924 Int) (x925 A)) 
                                               (=> 
                                                   (MS1 x924 x925 s119) 
                                                   (and 
                                                       (<= 1 x924) 
                                                       (<= x924 n51)))) 
                                           (forall ((x926 Int) (x927 A) (x928 A)) 
                                               (=> 
                                                   (and 
                                                       (MS1 x926 x927 s119) 
                                                       (MS1 x926 x928 s119)) 
                                                   (= x927 x928))) 
                                           (forall ((x929 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x929) 
                                                       (<= x929 n51)) 
                                                   (exists ((x930 A)) 
                                                       (MS1 x929 x930 s119)))))) 
                                   (exists ((n52 Int)) 
                                       (and 
                                           (<= 0 n52) 
                                           (forall ((x931 Int) (x932 A)) 
                                               (=> 
                                                   (MS1 x931 x932 s219) 
                                                   (and 
                                                       (<= 1 x931) 
                                                       (<= x931 n52)))) 
                                           (forall ((x933 Int) (x934 A) (x935 A)) 
                                               (=> 
                                                   (and 
                                                       (MS1 x933 x934 s219) 
                                                       (MS1 x933 x935 s219)) 
                                                   (= x934 x935))) 
                                           (forall ((x936 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x936) 
                                                       (<= x936 n52)) 
                                                   (exists ((x937 A)) 
                                                       (MS1 x936 x937 s219)))))) 
                                   (forall ((x938 Int) (x939 A)) 
                                       (= 
                                           (MS1 x938 x939 x894) 
                                           (MS1 x938 x939 s119))) 
                                   (forall ((x940 Int) (x941 A)) 
                                       (= 
                                           (MS1 x940 x941 x895) 
                                           (MS1 x940 x941 s219))) 
                                   (forall ((x942 Int) (x943 A)) 
                                       (= 
                                           (MS1 x942 x943 x897) 
                                           (or 
                                               (exists ((i29 Int)) 
                                                   (and 
                                                       (<= 1 i29) 
                                                       (forall ((x944 Int)) 
                                                           (=> 
                                                               (length s119 x944) 
                                                               (<= i29 x944))) 
                                                       (= x942 i29) 
                                                       (MS1 i29 x943 s119))) 
                                               (exists ((i30 Int)) 
                                                   (and 
                                                       (forall ((x945 Int)) 
                                                           (=> 
                                                               (length s119 x945) 
                                                               (<= (+ x945 1) i30))) 
                                                       (forall ((x946 Int) (x947 Int)) 
                                                           (=> 
                                                               (and 
                                                                   (length s119 x947) 
                                                                   (length s219 x946)) 
                                                               (<= i30 (+ x947 x946)))) 
                                                       (= x942 i30) 
                                                       (exists ((x948 Int)) 
                                                           (and 
                                                               (forall ((x949 Int)) 
                                                                   (=> 
                                                                       (length s119 x949) 
                                                                       (= x948 (- i30 x949)))) 
                                                               (MS1 x948 x943 s219))))))))))) 
                       (forall ((x950 Int) (x951 A)) 
                           (= 
                               (MS1 x950 x951 x896) 
                               (MS1 x950 x951 x897))))) 
               (forall ((x952 PZA) (x953 PZA)) 
                   (=> 
                       (and 
                           (exists ((s46 PZA)) 
                               (and 
                                   (exists ((n53 Int)) 
                                       (and 
                                           (<= 0 n53) 
                                           (forall ((x954 Int) (x955 A)) 
                                               (=> 
                                                   (MS1 x954 x955 s46) 
                                                   (and 
                                                       (<= 1 x954) 
                                                       (<= x954 n53)))) 
                                           (forall ((x956 Int) (x957 A) (x958 A)) 
                                               (=> 
                                                   (and 
                                                       (MS1 x956 x957 s46) 
                                                       (MS1 x956 x958 s46)) 
                                                   (= x957 x958))) 
                                           (forall ((x959 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x959) 
                                                       (<= x959 n53)) 
                                                   (exists ((x960 A)) 
                                                       (MS1 x959 x960 s46)))))) 
                                   (forall ((x961 Int) (x962 A)) 
                                       (= 
                                           (MS1 x961 x962 x952) 
                                           (MS1 x961 x962 s46))))) 
                           (exists ((s47 PZA)) 
                               (and 
                                   (exists ((n54 Int)) 
                                       (and 
                                           (<= 0 n54) 
                                           (forall ((x963 Int) (x964 A)) 
                                               (=> 
                                                   (MS1 x963 x964 s47) 
                                                   (and 
                                                       (<= 1 x963) 
                                                       (<= x963 n54)))) 
                                           (forall ((x965 Int) (x966 A) (x967 A)) 
                                               (=> 
                                                   (and 
                                                       (MS1 x965 x966 s47) 
                                                       (MS1 x965 x967 s47)) 
                                                   (= x966 x967))) 
                                           (forall ((x968 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x968) 
                                                       (<= x968 n54)) 
                                                   (exists ((x969 A)) 
                                                       (MS1 x968 x969 s47)))))) 
                                   (forall ((x970 Int) (x971 A)) 
                                       (= 
                                           (MS1 x970 x971 x953) 
                                           (MS1 x970 x971 s47)))))) 
                       (exists ((x972 PZA) (s120 PZA) (s220 PZA)) 
                           (and 
                               (exists ((n55 Int)) 
                                   (and 
                                       (<= 0 n55) 
                                       (forall ((x973 Int) (x974 A)) 
                                           (=> 
                                               (MS1 x973 x974 s120) 
                                               (and 
                                                   (<= 1 x973) 
                                                   (<= x973 n55)))) 
                                       (forall ((x975 Int) (x976 A) (x977 A)) 
                                           (=> 
                                               (and 
                                                   (MS1 x975 x976 s120) 
                                                   (MS1 x975 x977 s120)) 
                                               (= x976 x977))) 
                                       (forall ((x978 Int)) 
                                           (=> 
                                               (and 
                                                   (<= 1 x978) 
                                                   (<= x978 n55)) 
                                               (exists ((x979 A)) 
                                                   (MS1 x978 x979 s120)))))) 
                               (exists ((n56 Int)) 
                                   (and 
                                       (<= 0 n56) 
                                       (forall ((x980 Int) (x981 A)) 
                                           (=> 
                                               (MS1 x980 x981 s220) 
                                               (and 
                                                   (<= 1 x980) 
                                                   (<= x980 n56)))) 
                                       (forall ((x982 Int) (x983 A) (x984 A)) 
                                           (=> 
                                               (and 
                                                   (MS1 x982 x983 s220) 
                                                   (MS1 x982 x984 s220)) 
                                               (= x983 x984))) 
                                       (forall ((x985 Int)) 
                                           (=> 
                                               (and 
                                                   (<= 1 x985) 
                                                   (<= x985 n56)) 
                                               (exists ((x986 A)) 
                                                   (MS1 x985 x986 s220)))))) 
                               (forall ((x987 Int) (x988 A)) 
                                   (= 
                                       (MS1 x987 x988 x952) 
                                       (MS1 x987 x988 s120))) 
                               (forall ((x989 Int) (x990 A)) 
                                   (= 
                                       (MS1 x989 x990 x953) 
                                       (MS1 x989 x990 s220))) 
                               (forall ((x991 Int) (x992 A)) 
                                   (= 
                                       (MS1 x991 x992 x972) 
                                       (or 
                                           (exists ((i31 Int)) 
                                               (and 
                                                   (<= 1 i31) 
                                                   (forall ((x993 Int)) 
                                                       (=> 
                                                           (length s120 x993) 
                                                           (<= i31 x993))) 
                                                   (= x991 i31) 
                                                   (MS1 i31 x992 s120))) 
                                           (exists ((i32 Int)) 
                                               (and 
                                                   (forall ((x994 Int)) 
                                                       (=> 
                                                           (length s120 x994) 
                                                           (<= (+ x994 1) i32))) 
                                                   (forall ((x995 Int) (x996 Int)) 
                                                       (=> 
                                                           (and 
                                                               (length s120 x996) 
                                                               (length s220 x995)) 
                                                           (<= i32 (+ x996 x995)))) 
                                                   (= x991 i32) 
                                                   (exists ((x997 Int)) 
                                                       (and 
                                                           (forall ((x998 Int)) 
                                                               (=> 
                                                                   (length s120 x998) 
                                                                   (= x997 (- i32 x998)))) 
                                                           (MS1 x997 x992 s220)))))))))))))
         :named hyp88))
(assert (! (forall ((s121 PZA) (s221 PZA)) 
               (=> 
                   (and 
                       (exists ((n57 Int)) 
                           (and 
                               (<= 0 n57) 
                               (forall ((x999 Int) (x1000 A)) 
                                   (=> 
                                       (MS1 x999 x1000 s121) 
                                       (and 
                                           (<= 1 x999) 
                                           (<= x999 n57)))) 
                               (forall ((x1001 Int) (x1002 A) (x1003 A)) 
                                   (=> 
                                       (and 
                                           (MS1 x1001 x1002 s121) 
                                           (MS1 x1001 x1003 s121)) 
                                       (= x1002 x1003))) 
                               (forall ((x1004 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x1004) 
                                           (<= x1004 n57)) 
                                       (exists ((x1005 A)) 
                                           (MS1 x1004 x1005 s121)))))) 
                       (exists ((n58 Int)) 
                           (and 
                               (<= 0 n58) 
                               (forall ((x1006 Int) (x1007 A)) 
                                   (=> 
                                       (MS1 x1006 x1007 s221) 
                                       (and 
                                           (<= 1 x1006) 
                                           (<= x1006 n58)))) 
                               (forall ((x1008 Int) (x1009 A) (x1010 A)) 
                                   (=> 
                                       (and 
                                           (MS1 x1008 x1009 s221) 
                                           (MS1 x1008 x1010 s221)) 
                                       (= x1009 x1010))) 
                               (forall ((x1011 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x1011) 
                                           (<= x1011 n58)) 
                                       (exists ((x1012 A)) 
                                           (MS1 x1011 x1012 s221))))))) 
                   (exists ((x1013 PZA) (x1014 Int)) 
                       (and 
                           (forall ((x1015 Int) (x1016 A)) 
                               (= 
                                   (MS1 x1015 x1016 x1013) 
                                   (or 
                                       (exists ((i33 Int)) 
                                           (and 
                                               (<= 1 i33) 
                                               (forall ((x1017 Int)) 
                                                   (=> 
                                                       (length s121 x1017) 
                                                       (<= i33 x1017))) 
                                               (= x1015 i33) 
                                               (MS1 i33 x1016 s121))) 
                                       (exists ((i34 Int)) 
                                           (and 
                                               (forall ((x1018 Int)) 
                                                   (=> 
                                                       (length s121 x1018) 
                                                       (<= (+ x1018 1) i34))) 
                                               (forall ((x1019 Int) (x1020 Int)) 
                                                   (=> 
                                                       (and 
                                                           (length s121 x1020) 
                                                           (length s221 x1019)) 
                                                       (<= i34 (+ x1020 x1019)))) 
                                               (= x1015 i34) 
                                               (exists ((x1021 Int)) 
                                                   (and 
                                                       (forall ((x1022 Int)) 
                                                           (=> 
                                                               (length s121 x1022) 
                                                               (= x1021 (- i34 x1022)))) 
                                                       (MS1 x1021 x1016 s221)))))))) 
                           (forall ((x1023 Int) (x1024 Int)) 
                               (=> 
                                   (and 
                                       (length s121 x1024) 
                                       (length s221 x1023)) 
                                   (= x1014 (+ x1024 x1023)))) 
                           (length x1013 x1014)))))
         :named hyp89))
(assert (! (forall ((s122 PZA) (s222 PZA)) 
               (=> 
                   (and 
                       (exists ((n59 Int)) 
                           (and 
                               (<= 0 n59) 
                               (forall ((x1025 Int) (x1026 A)) 
                                   (=> 
                                       (MS1 x1025 x1026 s122) 
                                       (and 
                                           (<= 1 x1025) 
                                           (<= x1025 n59)))) 
                               (forall ((x1027 Int) (x1028 A) (x1029 A)) 
                                   (=> 
                                       (and 
                                           (MS1 x1027 x1028 s122) 
                                           (MS1 x1027 x1029 s122)) 
                                       (= x1028 x1029))) 
                               (forall ((x1030 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x1030) 
                                           (<= x1030 n59)) 
                                       (exists ((x1031 A)) 
                                           (MS1 x1030 x1031 s122)))))) 
                       (exists ((n60 Int)) 
                           (and 
                               (<= 0 n60) 
                               (forall ((x1032 Int) (x1033 A)) 
                                   (=> 
                                       (MS1 x1032 x1033 s222) 
                                       (and 
                                           (<= 1 x1032) 
                                           (<= x1032 n60)))) 
                               (forall ((x1034 Int) (x1035 A) (x1036 A)) 
                                   (=> 
                                       (and 
                                           (MS1 x1034 x1035 s222) 
                                           (MS1 x1034 x1036 s222)) 
                                       (= x1035 x1036))) 
                               (forall ((x1037 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x1037) 
                                           (<= x1037 n60)) 
                                       (exists ((x1038 A)) 
                                           (MS1 x1037 x1038 s222))))))) 
                   (forall ((x1039 Int)) 
                       (= 
                           (or 
                               (exists ((x1040 A)) 
                                   (exists ((i35 Int)) 
                                       (and 
                                           (<= 1 i35) 
                                           (forall ((x1041 Int)) 
                                               (=> 
                                                   (length s122 x1041) 
                                                   (<= i35 x1041))) 
                                           (= x1039 i35) 
                                           (MS1 i35 x1040 s122)))) 
                               (exists ((x1042 A)) 
                                   (exists ((i36 Int)) 
                                       (and 
                                           (forall ((x1043 Int)) 
                                               (=> 
                                                   (length s122 x1043) 
                                                   (<= (+ x1043 1) i36))) 
                                           (forall ((x1044 Int) (x1045 Int)) 
                                               (=> 
                                                   (and 
                                                       (length s122 x1045) 
                                                       (length s222 x1044)) 
                                                   (<= i36 (+ x1045 x1044)))) 
                                           (= x1039 i36) 
                                           (exists ((x1046 Int)) 
                                               (and 
                                                   (forall ((x1047 Int)) 
                                                       (=> 
                                                           (length s122 x1047) 
                                                           (= x1046 (- i36 x1047)))) 
                                                   (MS1 x1046 x1042 s222))))))) 
                           (and 
                               (<= 1 x1039) 
                               (forall ((x1048 Int) (x1049 Int)) 
                                   (=> 
                                       (and 
                                           (length s122 x1049) 
                                           (length s222 x1048)) 
                                       (<= x1039 (+ x1049 x1048)))))))))
         :named hyp90))
(assert (! (forall ((s123 PZA) (s223 PZA)) 
               (=> 
                   (and 
                       (exists ((n61 Int)) 
                           (and 
                               (<= 0 n61) 
                               (forall ((x1050 Int) (x1051 A)) 
                                   (=> 
                                       (MS1 x1050 x1051 s123) 
                                       (and 
                                           (<= 1 x1050) 
                                           (<= x1050 n61)))) 
                               (forall ((x1052 Int) (x1053 A) (x1054 A)) 
                                   (=> 
                                       (and 
                                           (MS1 x1052 x1053 s123) 
                                           (MS1 x1052 x1054 s123)) 
                                       (= x1053 x1054))) 
                               (forall ((x1055 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x1055) 
                                           (<= x1055 n61)) 
                                       (exists ((x1056 A)) 
                                           (MS1 x1055 x1056 s123)))))) 
                       (exists ((n62 Int)) 
                           (and 
                               (<= 0 n62) 
                               (forall ((x1057 Int) (x1058 A)) 
                                   (=> 
                                       (MS1 x1057 x1058 s223) 
                                       (and 
                                           (<= 1 x1057) 
                                           (<= x1057 n62)))) 
                               (forall ((x1059 Int) (x1060 A) (x1061 A)) 
                                   (=> 
                                       (and 
                                           (MS1 x1059 x1060 s223) 
                                           (MS1 x1059 x1061 s223)) 
                                       (= x1060 x1061))) 
                               (forall ((x1062 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x1062) 
                                           (<= x1062 n62)) 
                                       (exists ((x1063 A)) 
                                           (MS1 x1062 x1063 s223))))))) 
                   (forall ((x1064 A)) 
                       (= 
                           (or 
                               (exists ((x1065 Int)) 
                                   (exists ((i37 Int)) 
                                       (and 
                                           (<= 1 i37) 
                                           (forall ((x1066 Int)) 
                                               (=> 
                                                   (length s123 x1066) 
                                                   (<= i37 x1066))) 
                                           (= x1065 i37) 
                                           (MS1 i37 x1064 s123)))) 
                               (exists ((x1067 Int)) 
                                   (exists ((i38 Int)) 
                                       (and 
                                           (forall ((x1068 Int)) 
                                               (=> 
                                                   (length s123 x1068) 
                                                   (<= (+ x1068 1) i38))) 
                                           (forall ((x1069 Int) (x1070 Int)) 
                                               (=> 
                                                   (and 
                                                       (length s123 x1070) 
                                                       (length s223 x1069)) 
                                                   (<= i38 (+ x1070 x1069)))) 
                                           (= x1067 i38) 
                                           (exists ((x1071 Int)) 
                                               (and 
                                                   (forall ((x1072 Int)) 
                                                       (=> 
                                                           (length s123 x1072) 
                                                           (= x1071 (- i38 x1072)))) 
                                                   (MS1 x1071 x1064 s223))))))) 
                           (or 
                               (exists ((x1073 Int)) 
                                   (MS1 x1073 x1064 s123)) 
                               (exists ((x1074 Int)) 
                                   (MS1 x1074 x1064 s223)))))))
         :named hyp91))
(assert (! (forall ((s124 PZA) (s224 PZA) (i39 Int)) 
               (=> 
                   (and 
                       (exists ((n63 Int)) 
                           (and 
                               (<= 0 n63) 
                               (forall ((x1075 Int) (x1076 A)) 
                                   (=> 
                                       (MS1 x1075 x1076 s124) 
                                       (and 
                                           (<= 1 x1075) 
                                           (<= x1075 n63)))) 
                               (forall ((x1077 Int) (x1078 A) (x1079 A)) 
                                   (=> 
                                       (and 
                                           (MS1 x1077 x1078 s124) 
                                           (MS1 x1077 x1079 s124)) 
                                       (= x1078 x1079))) 
                               (forall ((x1080 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x1080) 
                                           (<= x1080 n63)) 
                                       (exists ((x1081 A)) 
                                           (MS1 x1080 x1081 s124)))))) 
                       (exists ((n64 Int)) 
                           (and 
                               (<= 0 n64) 
                               (forall ((x1082 Int) (x1083 A)) 
                                   (=> 
                                       (MS1 x1082 x1083 s224) 
                                       (and 
                                           (<= 1 x1082) 
                                           (<= x1082 n64)))) 
                               (forall ((x1084 Int) (x1085 A) (x1086 A)) 
                                   (=> 
                                       (and 
                                           (MS1 x1084 x1085 s224) 
                                           (MS1 x1084 x1086 s224)) 
                                       (= x1085 x1086))) 
                               (forall ((x1087 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x1087) 
                                           (<= x1087 n64)) 
                                       (exists ((x1088 A)) 
                                           (MS1 x1087 x1088 s224)))))) 
                       (<= 1 i39) 
                       (forall ((x1089 Int)) 
                           (=> 
                               (length s124 x1089) 
                               (<= i39 x1089)))) 
                   (or 
                       (exists ((i40 Int)) 
                           (and 
                               (<= 1 i40) 
                               (forall ((x1090 Int)) 
                                   (=> 
                                       (length s124 x1090) 
                                       (<= i40 x1090))) 
                               (= i39 i40) 
                               (exists ((x1091 A)) 
                                   (and 
                                       (MS1 i40 x1091 s124) 
                                       (MS1 i39 x1091 s124))))) 
                       (exists ((i41 Int)) 
                           (and 
                               (forall ((x1092 Int)) 
                                   (=> 
                                       (length s124 x1092) 
                                       (<= (+ x1092 1) i41))) 
                               (forall ((x1093 Int) (x1094 Int)) 
                                   (=> 
                                       (and 
                                           (length s124 x1094) 
                                           (length s224 x1093)) 
                                       (<= i41 (+ x1094 x1093)))) 
                               (= i39 i41) 
                               (exists ((x1095 A)) 
                                   (and 
                                       (exists ((x1096 Int)) 
                                           (and 
                                               (forall ((x1097 Int)) 
                                                   (=> 
                                                       (length s124 x1097) 
                                                       (= x1096 (- i41 x1097)))) 
                                               (MS1 x1096 x1095 s224))) 
                                       (MS1 i39 x1095 s124))))))))
         :named hyp92))
(assert (! (forall ((s125 PZA) (s225 PZA) (i42 Int)) 
               (=> 
                   (and 
                       (exists ((n65 Int)) 
                           (and 
                               (<= 0 n65) 
                               (forall ((x1098 Int) (x1099 A)) 
                                   (=> 
                                       (MS1 x1098 x1099 s125) 
                                       (and 
                                           (<= 1 x1098) 
                                           (<= x1098 n65)))) 
                               (forall ((x1100 Int) (x1101 A) (x1102 A)) 
                                   (=> 
                                       (and 
                                           (MS1 x1100 x1101 s125) 
                                           (MS1 x1100 x1102 s125)) 
                                       (= x1101 x1102))) 
                               (forall ((x1103 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x1103) 
                                           (<= x1103 n65)) 
                                       (exists ((x1104 A)) 
                                           (MS1 x1103 x1104 s125)))))) 
                       (exists ((n66 Int)) 
                           (and 
                               (<= 0 n66) 
                               (forall ((x1105 Int) (x1106 A)) 
                                   (=> 
                                       (MS1 x1105 x1106 s225) 
                                       (and 
                                           (<= 1 x1105) 
                                           (<= x1105 n66)))) 
                               (forall ((x1107 Int) (x1108 A) (x1109 A)) 
                                   (=> 
                                       (and 
                                           (MS1 x1107 x1108 s225) 
                                           (MS1 x1107 x1109 s225)) 
                                       (= x1108 x1109))) 
                               (forall ((x1110 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x1110) 
                                           (<= x1110 n66)) 
                                       (exists ((x1111 A)) 
                                           (MS1 x1110 x1111 s225)))))) 
                       (forall ((x1112 Int)) 
                           (=> 
                               (length s125 x1112) 
                               (<= (+ x1112 1) i42))) 
                       (forall ((x1113 Int) (x1114 Int)) 
                           (=> 
                               (and 
                                   (length s125 x1114) 
                                   (length s225 x1113)) 
                               (<= i42 (+ x1114 x1113))))) 
                   (or 
                       (exists ((i43 Int)) 
                           (and 
                               (<= 1 i43) 
                               (forall ((x1115 Int)) 
                                   (=> 
                                       (length s125 x1115) 
                                       (<= i43 x1115))) 
                               (= i42 i43) 
                               (exists ((x1116 Int) (x1117 A)) 
                                   (and 
                                       (forall ((x1118 Int)) 
                                           (=> 
                                               (length s125 x1118) 
                                               (= x1116 (- i42 x1118)))) 
                                       (MS1 i43 x1117 s125) 
                                       (MS1 x1116 x1117 s225))))) 
                       (exists ((i44 Int)) 
                           (and 
                               (forall ((x1119 Int)) 
                                   (=> 
                                       (length s125 x1119) 
                                       (<= (+ x1119 1) i44))) 
                               (forall ((x1120 Int) (x1121 Int)) 
                                   (=> 
                                       (and 
                                           (length s125 x1121) 
                                           (length s225 x1120)) 
                                       (<= i44 (+ x1121 x1120)))) 
                               (= i42 i44) 
                               (exists ((x1122 Int) (x1123 A)) 
                                   (and 
                                       (forall ((x1124 Int)) 
                                           (=> 
                                               (length s125 x1124) 
                                               (= x1122 (- i42 x1124)))) 
                                       (exists ((x1125 Int)) 
                                           (and 
                                               (forall ((x1126 Int)) 
                                                   (=> 
                                                       (length s125 x1126) 
                                                       (= x1125 (- i44 x1126)))) 
                                               (MS1 x1125 x1123 s225))) 
                                       (MS1 x1122 x1123 s225))))))))
         :named hyp93))
(assert (! (forall ((s126 PZA) (s226 PZA) (b1 PA)) 
               (=> 
                   (and 
                       (exists ((n67 Int)) 
                           (and 
                               (<= 0 n67) 
                               (forall ((x1127 Int) (x1128 A)) 
                                   (=> 
                                       (MS1 x1127 x1128 s126) 
                                       (and 
                                           (<= 1 x1127) 
                                           (<= x1127 n67)))) 
                               (forall ((x1129 Int) (x1130 A) (x1131 A)) 
                                   (=> 
                                       (and 
                                           (MS1 x1129 x1130 s126) 
                                           (MS1 x1129 x1131 s126)) 
                                       (= x1130 x1131))) 
                               (forall ((x1132 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x1132) 
                                           (<= x1132 n67)) 
                                       (exists ((x1133 A)) 
                                           (MS1 x1132 x1133 s126)))))) 
                       (exists ((n68 Int)) 
                           (and 
                               (<= 0 n68) 
                               (forall ((x1134 Int) (x1135 A)) 
                                   (=> 
                                       (MS1 x1134 x1135 s226) 
                                       (and 
                                           (<= 1 x1134) 
                                           (<= x1134 n68)))) 
                               (forall ((x1136 Int) (x1137 A) (x1138 A)) 
                                   (=> 
                                       (and 
                                           (MS1 x1136 x1137 s226) 
                                           (MS1 x1136 x1138 s226)) 
                                       (= x1137 x1138))) 
                               (forall ((x1139 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x1139) 
                                           (<= x1139 n68)) 
                                       (exists ((x1140 A)) 
                                           (MS1 x1139 x1140 s226)))))) 
                       (forall ((x1141 A)) 
                           (=> 
                               (exists ((x1142 Int)) 
                                   (MS1 x1142 x1141 s126)) 
                               (MS0 x1141 b1))) 
                       (forall ((x1143 A)) 
                           (=> 
                               (exists ((x1144 Int)) 
                                   (MS1 x1144 x1143 s226)) 
                               (MS0 x1143 b1)))) 
                   (and 
                       (forall ((x1145 Int) (x1146 A)) 
                           (=> 
                               (or 
                                   (exists ((i45 Int)) 
                                       (and 
                                           (<= 1 i45) 
                                           (forall ((x1147 Int)) 
                                               (=> 
                                                   (length s126 x1147) 
                                                   (<= i45 x1147))) 
                                           (= x1145 i45) 
                                           (MS1 i45 x1146 s126))) 
                                   (exists ((i46 Int)) 
                                       (and 
                                           (forall ((x1148 Int)) 
                                               (=> 
                                                   (length s126 x1148) 
                                                   (<= (+ x1148 1) i46))) 
                                           (forall ((x1149 Int) (x1150 Int)) 
                                               (=> 
                                                   (and 
                                                       (length s126 x1150) 
                                                       (length s226 x1149)) 
                                                   (<= i46 (+ x1150 x1149)))) 
                                           (= x1145 i46) 
                                           (exists ((x1151 Int)) 
                                               (and 
                                                   (forall ((x1152 Int)) 
                                                       (=> 
                                                           (length s126 x1152) 
                                                           (= x1151 (- i46 x1152)))) 
                                                   (MS1 x1151 x1146 s226)))))) 
                               (and 
                                   (<= 1 x1145) 
                                   (forall ((x1153 Int) (x1154 Int)) 
                                       (=> 
                                           (and 
                                               (length s126 x1154) 
                                               (length s226 x1153)) 
                                           (<= x1145 (+ x1154 x1153)))) 
                                   (MS0 x1146 b1)))) 
                       (forall ((x1155 Int) (x1156 A) (x1157 A)) 
                           (=> 
                               (and 
                                   (or 
                                       (exists ((i47 Int)) 
                                           (and 
                                               (<= 1 i47) 
                                               (forall ((x1158 Int)) 
                                                   (=> 
                                                       (length s126 x1158) 
                                                       (<= i47 x1158))) 
                                               (= x1155 i47) 
                                               (MS1 i47 x1156 s126))) 
                                       (exists ((i48 Int)) 
                                           (and 
                                               (forall ((x1159 Int)) 
                                                   (=> 
                                                       (length s126 x1159) 
                                                       (<= (+ x1159 1) i48))) 
                                               (forall ((x1160 Int) (x1161 Int)) 
                                                   (=> 
                                                       (and 
                                                           (length s126 x1161) 
                                                           (length s226 x1160)) 
                                                       (<= i48 (+ x1161 x1160)))) 
                                               (= x1155 i48) 
                                               (exists ((x1162 Int)) 
                                                   (and 
                                                       (forall ((x1163 Int)) 
                                                           (=> 
                                                               (length s126 x1163) 
                                                               (= x1162 (- i48 x1163)))) 
                                                       (MS1 x1162 x1156 s226)))))) 
                                   (or 
                                       (exists ((i49 Int)) 
                                           (and 
                                               (<= 1 i49) 
                                               (forall ((x1164 Int)) 
                                                   (=> 
                                                       (length s126 x1164) 
                                                       (<= i49 x1164))) 
                                               (= x1155 i49) 
                                               (MS1 i49 x1157 s126))) 
                                       (exists ((i50 Int)) 
                                           (and 
                                               (forall ((x1165 Int)) 
                                                   (=> 
                                                       (length s126 x1165) 
                                                       (<= (+ x1165 1) i50))) 
                                               (forall ((x1166 Int) (x1167 Int)) 
                                                   (=> 
                                                       (and 
                                                           (length s126 x1167) 
                                                           (length s226 x1166)) 
                                                       (<= i50 (+ x1167 x1166)))) 
                                               (= x1155 i50) 
                                               (exists ((x1168 Int)) 
                                                   (and 
                                                       (forall ((x1169 Int)) 
                                                           (=> 
                                                               (length s126 x1169) 
                                                               (= x1168 (- i50 x1169)))) 
                                                       (MS1 x1168 x1157 s226))))))) 
                               (= x1156 x1157))) 
                       (forall ((x1170 Int)) 
                           (=> 
                               (and 
                                   (<= 1 x1170) 
                                   (forall ((x1171 Int) (x1172 Int)) 
                                       (=> 
                                           (and 
                                               (length s126 x1172) 
                                               (length s226 x1171)) 
                                           (<= x1170 (+ x1172 x1171))))) 
                               (or 
                                   (exists ((x1173 A)) 
                                       (exists ((i51 Int)) 
                                           (and 
                                               (<= 1 i51) 
                                               (forall ((x1174 Int)) 
                                                   (=> 
                                                       (length s126 x1174) 
                                                       (<= i51 x1174))) 
                                               (= x1170 i51) 
                                               (MS1 i51 x1173 s126)))) 
                                   (exists ((x1175 A)) 
                                       (exists ((i52 Int)) 
                                           (and 
                                               (forall ((x1176 Int)) 
                                                   (=> 
                                                       (length s126 x1176) 
                                                       (<= (+ x1176 1) i52))) 
                                               (forall ((x1177 Int) (x1178 Int)) 
                                                   (=> 
                                                       (and 
                                                           (length s126 x1178) 
                                                           (length s226 x1177)) 
                                                       (<= i52 (+ x1178 x1177)))) 
                                               (= x1170 i52) 
                                               (exists ((x1179 Int)) 
                                                   (and 
                                                       (forall ((x1180 Int)) 
                                                           (=> 
                                                               (length s126 x1180) 
                                                               (= x1179 (- i52 x1180)))) 
                                                       (MS1 x1179 x1175 s226))))))))))))
         :named hyp94))
(assert (! (forall ((x1181 A) (y26 A)) 
               (=> 
                   (and 
                       (MS0 x1181 a) 
                       (MS0 y26 a)) 
                   (forall ((x1182 PZA)) 
                       (= 
                           (exists ((x1183 A) (x1184 A)) 
                               (and 
                                   (= x1183 y26) 
                                   (= x1184 x1181) 
                                   (path x1183 x1184 x1182))) 
                           (exists ((x1185 PZA)) 
                               (and 
                                   (exists ((x1186 A) (x1187 A)) 
                                       (and 
                                           (= x1186 x1181) 
                                           (= x1187 y26) 
                                           (path x1186 x1187 x1185))) 
                                   (exists ((s48 PZA)) 
                                       (and 
                                           (exists ((n69 Int)) 
                                               (and 
                                                   (<= 0 n69) 
                                                   (forall ((x1188 Int) (x1189 A)) 
                                                       (=> 
                                                           (MS1 x1188 x1189 s48) 
                                                           (and 
                                                               (<= 1 x1188) 
                                                               (<= x1188 n69)))) 
                                                   (forall ((x1190 Int) (x1191 A) (x1192 A)) 
                                                       (=> 
                                                           (and 
                                                               (MS1 x1190 x1191 s48) 
                                                               (MS1 x1190 x1192 s48)) 
                                                           (= x1191 x1192))) 
                                                   (forall ((x1193 Int)) 
                                                       (=> 
                                                           (and 
                                                               (<= 1 x1193) 
                                                               (<= x1193 n69)) 
                                                           (exists ((x1194 A)) 
                                                               (MS1 x1193 x1194 s48)))))) 
                                           (forall ((x1195 Int) (x1196 A)) 
                                               (= 
                                                   (MS1 x1195 x1196 x1185) 
                                                   (MS1 x1195 x1196 s48))) 
                                           (forall ((x1197 Int) (x1198 A)) 
                                               (= 
                                                   (MS1 x1197 x1198 x1182) 
                                                   (exists ((i53 Int)) 
                                                       (and 
                                                           (<= 1 i53) 
                                                           (forall ((x1199 Int)) 
                                                               (=> 
                                                                   (length s48 x1199) 
                                                                   (<= i53 x1199))) 
                                                           (= x1197 i53) 
                                                           (exists ((x1200 Int)) 
                                                               (and 
                                                                   (forall ((x1201 Int)) 
                                                                       (=> 
                                                                           (length s48 x1201) 
                                                                           (= x1200 (+ (- x1201 i53) 1)))) 
                                                                   (MS1 x1200 x1198 s48)))))))))))))))
         :named hyp95))
(assert (! (and 
               (forall ((x1202 PZA) (x1203 PZA)) 
                   (=> 
                       (exists ((s49 PZA)) 
                           (and 
                               (exists ((n70 Int)) 
                                   (and 
                                       (<= 0 n70) 
                                       (forall ((x1204 Int) (x1205 A)) 
                                           (=> 
                                               (MS1 x1204 x1205 s49) 
                                               (and 
                                                   (<= 1 x1204) 
                                                   (<= x1204 n70)))) 
                                       (forall ((x1206 Int) (x1207 A) (x1208 A)) 
                                           (=> 
                                               (and 
                                                   (MS1 x1206 x1207 s49) 
                                                   (MS1 x1206 x1208 s49)) 
                                               (= x1207 x1208))) 
                                       (forall ((x1209 Int)) 
                                           (=> 
                                               (and 
                                                   (<= 1 x1209) 
                                                   (<= x1209 n70)) 
                                               (exists ((x1210 A)) 
                                                   (MS1 x1209 x1210 s49)))))) 
                               (forall ((x1211 Int) (x1212 A)) 
                                   (= 
                                       (MS1 x1211 x1212 x1202) 
                                       (MS1 x1211 x1212 s49))) 
                               (forall ((x1213 Int) (x1214 A)) 
                                   (= 
                                       (MS1 x1213 x1214 x1203) 
                                       (exists ((i54 Int)) 
                                           (and 
                                               (<= 1 i54) 
                                               (forall ((x1215 Int)) 
                                                   (=> 
                                                       (length s49 x1215) 
                                                       (<= i54 x1215))) 
                                               (= x1213 i54) 
                                               (exists ((x1216 Int)) 
                                                   (and 
                                                       (forall ((x1217 Int)) 
                                                           (=> 
                                                               (length s49 x1217) 
                                                               (= x1216 (+ (- x1217 i54) 1)))) 
                                                       (MS1 x1216 x1214 s49))))))))) 
                       (and 
                           (exists ((s50 PZA)) 
                               (and 
                                   (exists ((n71 Int)) 
                                       (and 
                                           (<= 0 n71) 
                                           (forall ((x1218 Int) (x1219 A)) 
                                               (=> 
                                                   (MS1 x1218 x1219 s50) 
                                                   (and 
                                                       (<= 1 x1218) 
                                                       (<= x1218 n71)))) 
                                           (forall ((x1220 Int) (x1221 A) (x1222 A)) 
                                               (=> 
                                                   (and 
                                                       (MS1 x1220 x1221 s50) 
                                                       (MS1 x1220 x1222 s50)) 
                                                   (= x1221 x1222))) 
                                           (forall ((x1223 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x1223) 
                                                       (<= x1223 n71)) 
                                                   (exists ((x1224 A)) 
                                                       (MS1 x1223 x1224 s50)))))) 
                                   (forall ((x1225 Int) (x1226 A)) 
                                       (= 
                                           (MS1 x1225 x1226 x1202) 
                                           (MS1 x1225 x1226 s50))))) 
                           (exists ((s51 PZA)) 
                               (and 
                                   (exists ((n72 Int)) 
                                       (and 
                                           (<= 0 n72) 
                                           (forall ((x1227 Int) (x1228 A)) 
                                               (=> 
                                                   (MS1 x1227 x1228 s51) 
                                                   (and 
                                                       (<= 1 x1227) 
                                                       (<= x1227 n72)))) 
                                           (forall ((x1229 Int) (x1230 A) (x1231 A)) 
                                               (=> 
                                                   (and 
                                                       (MS1 x1229 x1230 s51) 
                                                       (MS1 x1229 x1231 s51)) 
                                                   (= x1230 x1231))) 
                                           (forall ((x1232 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x1232) 
                                                       (<= x1232 n72)) 
                                                   (exists ((x1233 A)) 
                                                       (MS1 x1232 x1233 s51)))))) 
                                   (forall ((x1234 Int) (x1235 A)) 
                                       (= 
                                           (MS1 x1234 x1235 x1203) 
                                           (MS1 x1234 x1235 s51)))))))) 
               (forall ((x1236 PZA) (x1237 PZA) (x1238 PZA)) 
                   (=> 
                       (and 
                           (exists ((s52 PZA)) 
                               (and 
                                   (exists ((n73 Int)) 
                                       (and 
                                           (<= 0 n73) 
                                           (forall ((x1239 Int) (x1240 A)) 
                                               (=> 
                                                   (MS1 x1239 x1240 s52) 
                                                   (and 
                                                       (<= 1 x1239) 
                                                       (<= x1239 n73)))) 
                                           (forall ((x1241 Int) (x1242 A) (x1243 A)) 
                                               (=> 
                                                   (and 
                                                       (MS1 x1241 x1242 s52) 
                                                       (MS1 x1241 x1243 s52)) 
                                                   (= x1242 x1243))) 
                                           (forall ((x1244 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x1244) 
                                                       (<= x1244 n73)) 
                                                   (exists ((x1245 A)) 
                                                       (MS1 x1244 x1245 s52)))))) 
                                   (forall ((x1246 Int) (x1247 A)) 
                                       (= 
                                           (MS1 x1246 x1247 x1236) 
                                           (MS1 x1246 x1247 s52))) 
                                   (forall ((x1248 Int) (x1249 A)) 
                                       (= 
                                           (MS1 x1248 x1249 x1237) 
                                           (exists ((i55 Int)) 
                                               (and 
                                                   (<= 1 i55) 
                                                   (forall ((x1250 Int)) 
                                                       (=> 
                                                           (length s52 x1250) 
                                                           (<= i55 x1250))) 
                                                   (= x1248 i55) 
                                                   (exists ((x1251 Int)) 
                                                       (and 
                                                           (forall ((x1252 Int)) 
                                                               (=> 
                                                                   (length s52 x1252) 
                                                                   (= x1251 (+ (- x1252 i55) 1)))) 
                                                           (MS1 x1251 x1249 s52))))))))) 
                           (exists ((s53 PZA)) 
                               (and 
                                   (exists ((n74 Int)) 
                                       (and 
                                           (<= 0 n74) 
                                           (forall ((x1253 Int) (x1254 A)) 
                                               (=> 
                                                   (MS1 x1253 x1254 s53) 
                                                   (and 
                                                       (<= 1 x1253) 
                                                       (<= x1253 n74)))) 
                                           (forall ((x1255 Int) (x1256 A) (x1257 A)) 
                                               (=> 
                                                   (and 
                                                       (MS1 x1255 x1256 s53) 
                                                       (MS1 x1255 x1257 s53)) 
                                                   (= x1256 x1257))) 
                                           (forall ((x1258 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x1258) 
                                                       (<= x1258 n74)) 
                                                   (exists ((x1259 A)) 
                                                       (MS1 x1258 x1259 s53)))))) 
                                   (forall ((x1260 Int) (x1261 A)) 
                                       (= 
                                           (MS1 x1260 x1261 x1236) 
                                           (MS1 x1260 x1261 s53))) 
                                   (forall ((x1262 Int) (x1263 A)) 
                                       (= 
                                           (MS1 x1262 x1263 x1238) 
                                           (exists ((i56 Int)) 
                                               (and 
                                                   (<= 1 i56) 
                                                   (forall ((x1264 Int)) 
                                                       (=> 
                                                           (length s53 x1264) 
                                                           (<= i56 x1264))) 
                                                   (= x1262 i56) 
                                                   (exists ((x1265 Int)) 
                                                       (and 
                                                           (forall ((x1266 Int)) 
                                                               (=> 
                                                                   (length s53 x1266) 
                                                                   (= x1265 (+ (- x1266 i56) 1)))) 
                                                           (MS1 x1265 x1263 s53)))))))))) 
                       (forall ((x1267 Int) (x1268 A)) 
                           (= 
                               (MS1 x1267 x1268 x1237) 
                               (MS1 x1267 x1268 x1238))))) 
               (forall ((x1269 PZA)) 
                   (=> 
                       (exists ((s54 PZA)) 
                           (and 
                               (exists ((n75 Int)) 
                                   (and 
                                       (<= 0 n75) 
                                       (forall ((x1270 Int) (x1271 A)) 
                                           (=> 
                                               (MS1 x1270 x1271 s54) 
                                               (and 
                                                   (<= 1 x1270) 
                                                   (<= x1270 n75)))) 
                                       (forall ((x1272 Int) (x1273 A) (x1274 A)) 
                                           (=> 
                                               (and 
                                                   (MS1 x1272 x1273 s54) 
                                                   (MS1 x1272 x1274 s54)) 
                                               (= x1273 x1274))) 
                                       (forall ((x1275 Int)) 
                                           (=> 
                                               (and 
                                                   (<= 1 x1275) 
                                                   (<= x1275 n75)) 
                                               (exists ((x1276 A)) 
                                                   (MS1 x1275 x1276 s54)))))) 
                               (forall ((x1277 Int) (x1278 A)) 
                                   (= 
                                       (MS1 x1277 x1278 x1269) 
                                       (MS1 x1277 x1278 s54))))) 
                       (exists ((x1279 PZA) (s55 PZA)) 
                           (and 
                               (exists ((n76 Int)) 
                                   (and 
                                       (<= 0 n76) 
                                       (forall ((x1280 Int) (x1281 A)) 
                                           (=> 
                                               (MS1 x1280 x1281 s55) 
                                               (and 
                                                   (<= 1 x1280) 
                                                   (<= x1280 n76)))) 
                                       (forall ((x1282 Int) (x1283 A) (x1284 A)) 
                                           (=> 
                                               (and 
                                                   (MS1 x1282 x1283 s55) 
                                                   (MS1 x1282 x1284 s55)) 
                                               (= x1283 x1284))) 
                                       (forall ((x1285 Int)) 
                                           (=> 
                                               (and 
                                                   (<= 1 x1285) 
                                                   (<= x1285 n76)) 
                                               (exists ((x1286 A)) 
                                                   (MS1 x1285 x1286 s55)))))) 
                               (forall ((x1287 Int) (x1288 A)) 
                                   (= 
                                       (MS1 x1287 x1288 x1269) 
                                       (MS1 x1287 x1288 s55))) 
                               (forall ((x1289 Int) (x1290 A)) 
                                   (= 
                                       (MS1 x1289 x1290 x1279) 
                                       (exists ((i57 Int)) 
                                           (and 
                                               (<= 1 i57) 
                                               (forall ((x1291 Int)) 
                                                   (=> 
                                                       (length s55 x1291) 
                                                       (<= i57 x1291))) 
                                               (= x1289 i57) 
                                               (exists ((x1292 Int)) 
                                                   (and 
                                                       (forall ((x1293 Int)) 
                                                           (=> 
                                                               (length s55 x1293) 
                                                               (= x1292 (+ (- x1293 i57) 1)))) 
                                                       (MS1 x1292 x1290 s55))))))))))))
         :named hyp96))
(assert (! (forall ((x1294 A) (y27 A) (p19 PZA)) 
               (=> 
                   (path x1294 y27 p19) 
                   (exists ((x1295 PZA)) 
                       (and 
                           (forall ((x1296 Int) (x1297 A)) 
                               (= 
                                   (MS1 x1296 x1297 x1295) 
                                   (exists ((i58 Int)) 
                                       (and 
                                           (<= 1 i58) 
                                           (forall ((x1298 Int)) 
                                               (=> 
                                                   (length p19 x1298) 
                                                   (<= i58 x1298))) 
                                           (= x1296 i58) 
                                           (exists ((x1299 Int)) 
                                               (and 
                                                   (forall ((x1300 Int)) 
                                                       (=> 
                                                           (length p19 x1300) 
                                                           (= x1299 (+ (- x1300 i58) 1)))) 
                                                   (MS1 x1299 x1297 p19))))))) 
                           (path y27 x1294 x1295)))))
         :named hyp97))
(assert (! (forall ((s56 PZA)) 
               (=> 
                   (exists ((n77 Int)) 
                       (and 
                           (<= 0 n77) 
                           (forall ((x1301 Int) (x1302 A)) 
                               (=> 
                                   (MS1 x1301 x1302 s56) 
                                   (and 
                                       (<= 1 x1301) 
                                       (<= x1301 n77)))) 
                           (forall ((x1303 Int) (x1304 A) (x1305 A)) 
                               (=> 
                                   (and 
                                       (MS1 x1303 x1304 s56) 
                                       (MS1 x1303 x1305 s56)) 
                                   (= x1304 x1305))) 
                           (forall ((x1306 Int)) 
                               (=> 
                                   (and 
                                       (<= 1 x1306) 
                                       (<= x1306 n77)) 
                                   (exists ((x1307 A)) 
                                       (MS1 x1306 x1307 s56)))))) 
                   (exists ((x1308 PZA) (x1309 Int)) 
                       (and 
                           (forall ((x1310 Int) (x1311 A)) 
                               (= 
                                   (MS1 x1310 x1311 x1308) 
                                   (exists ((i59 Int)) 
                                       (and 
                                           (<= 1 i59) 
                                           (forall ((x1312 Int)) 
                                               (=> 
                                                   (length s56 x1312) 
                                                   (<= i59 x1312))) 
                                           (= x1310 i59) 
                                           (exists ((x1313 Int)) 
                                               (and 
                                                   (forall ((x1314 Int)) 
                                                       (=> 
                                                           (length s56 x1314) 
                                                           (= x1313 (+ (- x1314 i59) 1)))) 
                                                   (MS1 x1313 x1311 s56))))))) 
                           (length s56 x1309) 
                           (length x1308 x1309)))))
         :named hyp98))
(assert (! (forall ((s57 PZA)) 
               (=> 
                   (exists ((n78 Int)) 
                       (and 
                           (<= 0 n78) 
                           (forall ((x1315 Int) (x1316 A)) 
                               (=> 
                                   (MS1 x1315 x1316 s57) 
                                   (and 
                                       (<= 1 x1315) 
                                       (<= x1315 n78)))) 
                           (forall ((x1317 Int) (x1318 A) (x1319 A)) 
                               (=> 
                                   (and 
                                       (MS1 x1317 x1318 s57) 
                                       (MS1 x1317 x1319 s57)) 
                                   (= x1318 x1319))) 
                           (forall ((x1320 Int)) 
                               (=> 
                                   (and 
                                       (<= 1 x1320) 
                                       (<= x1320 n78)) 
                                   (exists ((x1321 A)) 
                                       (MS1 x1320 x1321 s57)))))) 
                   (forall ((x1322 A)) 
                       (= 
                           (exists ((i60 Int)) 
                               (and 
                                   (<= 1 i60) 
                                   (forall ((x1323 Int)) 
                                       (=> 
                                           (length s57 x1323) 
                                           (<= i60 x1323))) 
                                   (exists ((x1324 Int)) 
                                       (and 
                                           (forall ((x1325 Int)) 
                                               (=> 
                                                   (length s57 x1325) 
                                                   (= x1324 (+ (- x1325 i60) 1)))) 
                                           (MS1 x1324 x1322 s57))))) 
                           (exists ((x1326 Int)) 
                               (MS1 x1326 x1322 s57))))))
         :named hyp99))
(assert (! (forall ((s58 PZA)) 
               (=> 
                   (exists ((n79 Int)) 
                       (and 
                           (<= 0 n79) 
                           (forall ((x1327 Int) (x1328 A)) 
                               (=> 
                                   (MS1 x1327 x1328 s58) 
                                   (and 
                                       (<= 1 x1327) 
                                       (<= x1327 n79)))) 
                           (forall ((x1329 Int) (x1330 A) (x1331 A)) 
                               (=> 
                                   (and 
                                       (MS1 x1329 x1330 s58) 
                                       (MS1 x1329 x1331 s58)) 
                                   (= x1330 x1331))) 
                           (forall ((x1332 Int)) 
                               (=> 
                                   (and 
                                       (<= 1 x1332) 
                                       (<= x1332 n79)) 
                                   (exists ((x1333 A)) 
                                       (MS1 x1332 x1333 s58)))))) 
                   (forall ((x1334 Int) (x1335 A)) 
                       (= 
                           (exists ((i61 Int)) 
                               (and 
                                   (<= 1 i61) 
                                   (forall ((x1336 Int)) 
                                       (=> 
                                           (exists ((x1337 PZA)) 
                                               (and 
                                                   (forall ((x1338 Int) (x1339 A)) 
                                                       (= 
                                                           (MS1 x1338 x1339 x1337) 
                                                           (exists ((i62 Int)) 
                                                               (and 
                                                                   (<= 1 i62) 
                                                                   (forall ((x1340 Int)) 
                                                                       (=> 
                                                                           (length s58 x1340) 
                                                                           (<= i62 x1340))) 
                                                                   (= x1338 i62) 
                                                                   (exists ((x1341 Int)) 
                                                                       (and 
                                                                           (forall ((x1342 Int)) 
                                                                               (=> 
                                                                                   (length s58 x1342) 
                                                                                   (= x1341 (+ (- x1342 i62) 1)))) 
                                                                           (MS1 x1341 x1339 s58))))))) 
                                                   (length x1337 x1336))) 
                                           (<= i61 x1336))) 
                                   (= x1334 i61) 
                                   (exists ((x1343 Int)) 
                                       (and 
                                           (forall ((x1344 Int) (x1345 Int)) 
                                               (=> 
                                                   (and 
                                                       (length s58 x1345) 
                                                       (exists ((x1346 PZA)) 
                                                           (and 
                                                               (forall ((x1347 Int) (x1348 A)) 
                                                                   (= 
                                                                       (MS1 x1347 x1348 x1346) 
                                                                       (exists ((i63 Int)) 
                                                                           (and 
                                                                               (<= 1 i63) 
                                                                               (forall ((x1349 Int)) 
                                                                                   (=> 
                                                                                       (length s58 x1349) 
                                                                                       (<= i63 x1349))) 
                                                                               (= x1347 i63) 
                                                                               (exists ((x1350 Int)) 
                                                                                   (and 
                                                                                       (forall ((x1351 Int)) 
                                                                                           (=> 
                                                                                               (length s58 x1351) 
                                                                                               (= x1350 (+ (- x1351 i63) 1)))) 
                                                                                       (MS1 x1350 x1348 s58))))))) 
                                                               (length x1346 x1344)))) 
                                                   (= x1343 (+ (- x1345 (+ (- x1344 i61) 1)) 1)))) 
                                           (MS1 x1343 x1335 s58))))) 
                           (MS1 x1334 x1335 s58)))))
         :named hyp100))
(assert (! (forall ((x1352 A) (y28 A)) 
               (=> 
                   (and 
                       (MS0 x1352 a) 
                       (MS0 y28 a)) 
                   (exists ((x1353 Int)) 
                       (and 
                           (exists ((x1354 PZA)) 
                               (and 
                                   (exists ((x1355 A) (x1356 A)) 
                                       (and 
                                           (= x1355 x1352) 
                                           (= x1356 y28) 
                                           (exists ((x1357 A) (y29 A) (p20 PZA)) 
                                               (and 
                                                   (exists ((n80 Int)) 
                                                       (and 
                                                           (<= 0 n80) 
                                                           (forall ((x1358 Int) (x1359 A)) 
                                                               (=> 
                                                                   (MS1 x1358 x1359 p20) 
                                                                   (and 
                                                                       (<= 1 x1358) 
                                                                       (<= x1358 n80)))) 
                                                           (forall ((x1360 Int) (x1361 A) (x1362 A)) 
                                                               (=> 
                                                                   (and 
                                                                       (MS1 x1360 x1361 p20) 
                                                                       (MS1 x1360 x1362 p20)) 
                                                                   (= x1361 x1362))) 
                                                           (forall ((x1363 Int)) 
                                                               (=> 
                                                                   (and 
                                                                       (<= 1 x1363) 
                                                                       (<= x1363 n80)) 
                                                                   (exists ((x1364 A)) 
                                                                       (MS1 x1363 x1364 p20)))))) 
                                                   (forall ((x1365 A)) 
                                                       (=> 
                                                           (exists ((x1366 Int)) 
                                                               (MS1 x1366 x1365 p20)) 
                                                           (MS0 x1365 a))) 
                                                   (forall ((x1367 Int)) 
                                                       (=> 
                                                           (length p20 x1367) 
                                                           (< 1 x1367))) 
                                                   (exists ((x1368 Int)) 
                                                       (and 
                                                           (= x1368 1) 
                                                           (MS1 x1368 x1357 p20))) 
                                                   (exists ((x1369 Int)) 
                                                       (and 
                                                           (length p20 x1369) 
                                                           (MS1 x1369 y29 p20))) 
                                                   (forall ((i64 Int)) 
                                                       (=> 
                                                           (and 
                                                               (<= 1 i64) 
                                                               (forall ((x1370 Int)) 
                                                                   (=> 
                                                                       (length p20 x1370) 
                                                                       (<= i64 (- x1370 1))))) 
                                                           (exists ((x1371 A) (x1372 A)) 
                                                               (and 
                                                                   (MS1 i64 x1371 p20) 
                                                                   (exists ((x1373 Int)) 
                                                                       (and 
                                                                           (= x1373 (+ i64 1)) 
                                                                           (MS1 x1373 x1372 p20))) 
                                                                   (MS x1371 x1372 r))))) 
                                                   (= x1355 x1357) 
                                                   (= x1356 y29) 
                                                   (forall ((x1374 Int) (x1375 A)) 
                                                       (= 
                                                           (MS1 x1374 x1375 x1354) 
                                                           (MS1 x1374 x1375 p20))))))) 
                                   (length x1354 x1353))) 
                           (forall ((x1376 Int)) 
                               (=> 
                                   (exists ((x1377 PZA)) 
                                       (and 
                                           (exists ((x1378 A) (x1379 A)) 
                                               (and 
                                                   (= x1378 x1352) 
                                                   (= x1379 y28) 
                                                   (exists ((x1380 A) (y30 A) (p21 PZA)) 
                                                       (and 
                                                           (exists ((n81 Int)) 
                                                               (and 
                                                                   (<= 0 n81) 
                                                                   (forall ((x1381 Int) (x1382 A)) 
                                                                       (=> 
                                                                           (MS1 x1381 x1382 p21) 
                                                                           (and 
                                                                               (<= 1 x1381) 
                                                                               (<= x1381 n81)))) 
                                                                   (forall ((x1383 Int) (x1384 A) (x1385 A)) 
                                                                       (=> 
                                                                           (and 
                                                                               (MS1 x1383 x1384 p21) 
                                                                               (MS1 x1383 x1385 p21)) 
                                                                           (= x1384 x1385))) 
                                                                   (forall ((x1386 Int)) 
                                                                       (=> 
                                                                           (and 
                                                                               (<= 1 x1386) 
                                                                               (<= x1386 n81)) 
                                                                           (exists ((x1387 A)) 
                                                                               (MS1 x1386 x1387 p21)))))) 
                                                           (forall ((x1388 A)) 
                                                               (=> 
                                                                   (exists ((x1389 Int)) 
                                                                       (MS1 x1389 x1388 p21)) 
                                                                   (MS0 x1388 a))) 
                                                           (forall ((x1390 Int)) 
                                                               (=> 
                                                                   (length p21 x1390) 
                                                                   (< 1 x1390))) 
                                                           (exists ((x1391 Int)) 
                                                               (and 
                                                                   (= x1391 1) 
                                                                   (MS1 x1391 x1380 p21))) 
                                                           (exists ((x1392 Int)) 
                                                               (and 
                                                                   (length p21 x1392) 
                                                                   (MS1 x1392 y30 p21))) 
                                                           (forall ((i65 Int)) 
                                                               (=> 
                                                                   (and 
                                                                       (<= 1 i65) 
                                                                       (forall ((x1393 Int)) 
                                                                           (=> 
                                                                               (length p21 x1393) 
                                                                               (<= i65 (- x1393 1))))) 
                                                                   (exists ((x1394 A) (x1395 A)) 
                                                                       (and 
                                                                           (MS1 i65 x1394 p21) 
                                                                           (exists ((x1396 Int)) 
                                                                               (and 
                                                                                   (= x1396 (+ i65 1)) 
                                                                                   (MS1 x1396 x1395 p21))) 
                                                                           (MS x1394 x1395 r))))) 
                                                           (= x1378 x1380) 
                                                           (= x1379 y30) 
                                                           (forall ((x1397 Int) (x1398 A)) 
                                                               (= 
                                                                   (MS1 x1397 x1398 x1377) 
                                                                   (MS1 x1397 x1398 p21))))))) 
                                           (length x1377 x1376))) 
                                   (<= x1353 x1376))) 
                           (dist x1352 y28 x1353)))))
         :named hyp101))
(assert (! (forall ((x1399 A) (y31 A)) 
               (=> 
                   (and 
                       (MS0 x1399 a) 
                       (MS0 y31 a)) 
                   (forall ((x1400 PZA)) 
                       (= 
                           (exists ((x1401 A) (x1402 A)) 
                               (and 
                                   (= x1401 y31) 
                                   (= x1402 x1399) 
                                   (exists ((x1403 A) (y32 A) (p22 PZA)) 
                                       (and 
                                           (exists ((n82 Int)) 
                                               (and 
                                                   (<= 0 n82) 
                                                   (forall ((x1404 Int) (x1405 A)) 
                                                       (=> 
                                                           (MS1 x1404 x1405 p22) 
                                                           (and 
                                                               (<= 1 x1404) 
                                                               (<= x1404 n82)))) 
                                                   (forall ((x1406 Int) (x1407 A) (x1408 A)) 
                                                       (=> 
                                                           (and 
                                                               (MS1 x1406 x1407 p22) 
                                                               (MS1 x1406 x1408 p22)) 
                                                           (= x1407 x1408))) 
                                                   (forall ((x1409 Int)) 
                                                       (=> 
                                                           (and 
                                                               (<= 1 x1409) 
                                                               (<= x1409 n82)) 
                                                           (exists ((x1410 A)) 
                                                               (MS1 x1409 x1410 p22)))))) 
                                           (forall ((x1411 A)) 
                                               (=> 
                                                   (exists ((x1412 Int)) 
                                                       (MS1 x1412 x1411 p22)) 
                                                   (MS0 x1411 a))) 
                                           (forall ((x1413 Int)) 
                                               (=> 
                                                   (length p22 x1413) 
                                                   (< 1 x1413))) 
                                           (exists ((x1414 Int)) 
                                               (and 
                                                   (= x1414 1) 
                                                   (MS1 x1414 x1403 p22))) 
                                           (exists ((x1415 Int)) 
                                               (and 
                                                   (length p22 x1415) 
                                                   (MS1 x1415 y32 p22))) 
                                           (forall ((i66 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 i66) 
                                                       (forall ((x1416 Int)) 
                                                           (=> 
                                                               (length p22 x1416) 
                                                               (<= i66 (- x1416 1))))) 
                                                   (exists ((x1417 A) (x1418 A)) 
                                                       (and 
                                                           (MS1 i66 x1417 p22) 
                                                           (exists ((x1419 Int)) 
                                                               (and 
                                                                   (= x1419 (+ i66 1)) 
                                                                   (MS1 x1419 x1418 p22))) 
                                                           (MS x1417 x1418 r))))) 
                                           (= x1401 x1403) 
                                           (= x1402 y32) 
                                           (forall ((x1420 Int) (x1421 A)) 
                                               (= 
                                                   (MS1 x1420 x1421 x1400) 
                                                   (MS1 x1420 x1421 p22))))))) 
                           (exists ((x1422 PZA)) 
                               (and 
                                   (exists ((x1423 A) (x1424 A)) 
                                       (and 
                                           (= x1423 x1399) 
                                           (= x1424 y31) 
                                           (exists ((x1425 A) (y33 A) (p23 PZA)) 
                                               (and 
                                                   (exists ((n83 Int)) 
                                                       (and 
                                                           (<= 0 n83) 
                                                           (forall ((x1426 Int) (x1427 A)) 
                                                               (=> 
                                                                   (MS1 x1426 x1427 p23) 
                                                                   (and 
                                                                       (<= 1 x1426) 
                                                                       (<= x1426 n83)))) 
                                                           (forall ((x1428 Int) (x1429 A) (x1430 A)) 
                                                               (=> 
                                                                   (and 
                                                                       (MS1 x1428 x1429 p23) 
                                                                       (MS1 x1428 x1430 p23)) 
                                                                   (= x1429 x1430))) 
                                                           (forall ((x1431 Int)) 
                                                               (=> 
                                                                   (and 
                                                                       (<= 1 x1431) 
                                                                       (<= x1431 n83)) 
                                                                   (exists ((x1432 A)) 
                                                                       (MS1 x1431 x1432 p23)))))) 
                                                   (forall ((x1433 A)) 
                                                       (=> 
                                                           (exists ((x1434 Int)) 
                                                               (MS1 x1434 x1433 p23)) 
                                                           (MS0 x1433 a))) 
                                                   (forall ((x1435 Int)) 
                                                       (=> 
                                                           (length p23 x1435) 
                                                           (< 1 x1435))) 
                                                   (exists ((x1436 Int)) 
                                                       (and 
                                                           (= x1436 1) 
                                                           (MS1 x1436 x1425 p23))) 
                                                   (exists ((x1437 Int)) 
                                                       (and 
                                                           (length p23 x1437) 
                                                           (MS1 x1437 y33 p23))) 
                                                   (forall ((i67 Int)) 
                                                       (=> 
                                                           (and 
                                                               (<= 1 i67) 
                                                               (forall ((x1438 Int)) 
                                                                   (=> 
                                                                       (length p23 x1438) 
                                                                       (<= i67 (- x1438 1))))) 
                                                           (exists ((x1439 A) (x1440 A)) 
                                                               (and 
                                                                   (MS1 i67 x1439 p23) 
                                                                   (exists ((x1441 Int)) 
                                                                       (and 
                                                                           (= x1441 (+ i67 1)) 
                                                                           (MS1 x1441 x1440 p23))) 
                                                                   (MS x1439 x1440 r))))) 
                                                   (= x1423 x1425) 
                                                   (= x1424 y33) 
                                                   (forall ((x1442 Int) (x1443 A)) 
                                                       (= 
                                                           (MS1 x1442 x1443 x1422) 
                                                           (MS1 x1442 x1443 p23))))))) 
                                   (exists ((s59 PZA)) 
                                       (and 
                                           (exists ((n84 Int)) 
                                               (and 
                                                   (<= 0 n84) 
                                                   (forall ((x1444 Int) (x1445 A)) 
                                                       (=> 
                                                           (MS1 x1444 x1445 s59) 
                                                           (and 
                                                               (<= 1 x1444) 
                                                               (<= x1444 n84)))) 
                                                   (forall ((x1446 Int) (x1447 A) (x1448 A)) 
                                                       (=> 
                                                           (and 
                                                               (MS1 x1446 x1447 s59) 
                                                               (MS1 x1446 x1448 s59)) 
                                                           (= x1447 x1448))) 
                                                   (forall ((x1449 Int)) 
                                                       (=> 
                                                           (and 
                                                               (<= 1 x1449) 
                                                               (<= x1449 n84)) 
                                                           (exists ((x1450 A)) 
                                                               (MS1 x1449 x1450 s59)))))) 
                                           (forall ((x1451 Int) (x1452 A)) 
                                               (= 
                                                   (MS1 x1451 x1452 x1422) 
                                                   (MS1 x1451 x1452 s59))) 
                                           (forall ((x1453 Int) (x1454 A)) 
                                               (= 
                                                   (MS1 x1453 x1454 x1400) 
                                                   (exists ((i68 Int)) 
                                                       (and 
                                                           (<= 1 i68) 
                                                           (forall ((x1455 Int)) 
                                                               (=> 
                                                                   (length s59 x1455) 
                                                                   (<= i68 x1455))) 
                                                           (= x1453 i68) 
                                                           (exists ((x1456 Int)) 
                                                               (and 
                                                                   (forall ((x1457 Int)) 
                                                                       (=> 
                                                                           (length s59 x1457) 
                                                                           (= x1456 (+ (- x1457 i68) 1)))) 
                                                                   (MS1 x1456 x1454 s59)))))))))))))))
         :named hyp102))
(assert (! (forall ((x1458 A) (x1459 A) (x1460 PZA)) 
               (= 
                   (shpath x1458 x1459 x1460) 
                   (exists ((x1461 A) (y34 A) (p24 PZA)) 
                       (and 
                           (exists ((n85 Int)) 
                               (and 
                                   (<= 0 n85) 
                                   (forall ((x1462 Int) (x1463 A)) 
                                       (=> 
                                           (MS1 x1462 x1463 p24) 
                                           (and 
                                               (<= 1 x1462) 
                                               (<= x1462 n85)))) 
                                   (forall ((x1464 Int) (x1465 A) (x1466 A)) 
                                       (=> 
                                           (and 
                                               (MS1 x1464 x1465 p24) 
                                               (MS1 x1464 x1466 p24)) 
                                           (= x1465 x1466))) 
                                   (forall ((x1467 Int)) 
                                       (=> 
                                           (and 
                                               (<= 1 x1467) 
                                               (<= x1467 n85)) 
                                           (exists ((x1468 A)) 
                                               (MS1 x1467 x1468 p24)))))) 
                           (forall ((x1469 A)) 
                               (=> 
                                   (exists ((x1470 Int)) 
                                       (MS1 x1470 x1469 p24)) 
                                   (MS0 x1469 a))) 
                           (forall ((x1471 Int)) 
                               (=> 
                                   (length p24 x1471) 
                                   (< 1 x1471))) 
                           (exists ((x1472 Int)) 
                               (and 
                                   (= x1472 1) 
                                   (MS1 x1472 x1461 p24))) 
                           (exists ((x1473 Int)) 
                               (and 
                                   (length p24 x1473) 
                                   (MS1 x1473 y34 p24))) 
                           (forall ((i69 Int)) 
                               (=> 
                                   (and 
                                       (<= 1 i69) 
                                       (forall ((x1474 Int)) 
                                           (=> 
                                               (length p24 x1474) 
                                               (<= i69 (- x1474 1))))) 
                                   (exists ((x1475 A) (x1476 A)) 
                                       (and 
                                           (MS1 i69 x1475 p24) 
                                           (exists ((x1477 Int)) 
                                               (and 
                                                   (= x1477 (+ i69 1)) 
                                                   (MS1 x1477 x1476 p24))) 
                                           (MS x1475 x1476 r))))) 
                           (exists ((x1478 Int)) 
                               (and 
                                   (length p24 x1478) 
                                   (dist x1461 y34 x1478))) 
                           (= x1458 x1461) 
                           (= x1459 y34) 
                           (forall ((x1479 Int) (x1480 A)) 
                               (= 
                                   (MS1 x1479 x1480 x1460) 
                                   (MS1 x1479 x1480 p24)))))))
         :named hyp103))
(assert (! (forall ((x1481 A) (y35 A) (z4 A)) 
               (=> 
                   (and 
                       (MS0 x1481 a) 
                       (MS0 y35 a) 
                       (MS0 z4 a) 
                       (not 
                           (= z4 x1481)) 
                       (not 
                           (= z4 y35)) 
                       (forall ((t3 A)) 
                           (=> 
                               (and 
                                   (MS0 t3 a) 
                                   (MS z4 t3 r)) 
                               (forall ((x1482 Int) (x1483 Int)) 
                                   (=> 
                                       (and 
                                           (dist x1481 t3 x1483) 
                                           (dist x1481 z4 x1482)) 
                                       (<= x1483 x1482)))))) 
                   (exists ((q1 PZA)) 
                       (and 
                           (exists ((n86 Int)) 
                               (and 
                                   (<= 0 n86) 
                                   (forall ((x1484 Int) (x1485 A)) 
                                       (=> 
                                           (MS1 x1484 x1485 q1) 
                                           (and 
                                               (<= 1 x1484) 
                                               (<= x1484 n86)))) 
                                   (forall ((x1486 Int) (x1487 A) (x1488 A)) 
                                       (=> 
                                           (and 
                                               (MS1 x1486 x1487 q1) 
                                               (MS1 x1486 x1488 q1)) 
                                           (= x1487 x1488))) 
                                   (forall ((x1489 Int)) 
                                       (=> 
                                           (and 
                                               (<= 1 x1489) 
                                               (<= x1489 n86)) 
                                           (exists ((x1490 A)) 
                                               (MS1 x1489 x1490 q1)))))) 
                           (forall ((x1491 A)) 
                               (=> 
                                   (exists ((x1492 Int)) 
                                       (MS1 x1492 x1491 q1)) 
                                   (MS0 x1491 a))) 
                           (forall ((x1493 Int)) 
                               (=> 
                                   (length q1 x1493) 
                                   (< 1 x1493))) 
                           (exists ((x1494 Int)) 
                               (and 
                                   (= x1494 1) 
                                   (MS1 x1494 x1481 q1))) 
                           (exists ((x1495 Int)) 
                               (and 
                                   (length q1 x1495) 
                                   (MS1 x1495 y35 q1))) 
                           (forall ((i70 Int)) 
                               (=> 
                                   (and 
                                       (<= 1 i70) 
                                       (forall ((x1496 Int)) 
                                           (=> 
                                               (length q1 x1496) 
                                               (<= i70 (- x1496 1))))) 
                                   (exists ((x1497 A) (x1498 A)) 
                                       (and 
                                           (MS1 i70 x1497 q1) 
                                           (exists ((x1499 Int)) 
                                               (and 
                                                   (= x1499 (+ i70 1)) 
                                                   (MS1 x1499 x1498 q1))) 
                                           (MS x1497 x1498 r))))) 
                           (not 
                               (exists ((x1500 Int)) 
                                   (MS1 x1500 z4 q1)))))))
         :named hyp104))
(assert (! (exists ((n87 Int)) 
               (and 
                   (<= 0 n87) 
                   (forall ((x1501 Int) (x1502 A)) 
                       (=> 
                           (MS1 x1501 x1502 q) 
                           (and 
                               (<= 1 x1501) 
                               (<= x1501 n87)))) 
                   (forall ((x1503 Int) (x1504 A) (x1505 A)) 
                       (=> 
                           (and 
                               (MS1 x1503 x1504 q) 
                               (MS1 x1503 x1505 q)) 
                           (= x1504 x1505))) 
                   (forall ((x1506 Int)) 
                       (=> 
                           (and 
                               (<= 1 x1506) 
                               (<= x1506 n87)) 
                           (exists ((x1507 A)) 
                               (MS1 x1506 x1507 q))))))
         :named hyp105))
(assert (! (forall ((x1508 A)) 
               (=> 
                   (exists ((x1509 Int)) 
                       (MS1 x1509 x1508 q)) 
                   (MS0 x1508 a)))
         :named hyp106))
(assert (! (forall ((x1510 Int)) 
               (=> 
                   (length q x1510) 
                   (< 1 x1510)))
         :named hyp107))
(assert (! (exists ((x1511 Int)) 
               (and 
                   (= x1511 1) 
                   (MS1 x1511 x q)))
         :named hyp108))
(assert (! (exists ((x1512 Int)) 
               (and 
                   (length q x1512) 
                   (MS1 x1512 y1 q)))
         :named hyp109))
(assert (! (forall ((i71 Int)) 
               (=> 
                   (and 
                       (<= 1 i71) 
                       (forall ((x1513 Int)) 
                           (=> 
                               (length q x1513) 
                               (<= i71 (- x1513 1))))) 
                   (exists ((x1514 A) (x1515 A)) 
                       (and 
                           (MS1 i71 x1514 q) 
                           (exists ((x1516 Int)) 
                               (and 
                                   (= x1516 (+ i71 1)) 
                                   (MS1 x1516 x1515 q))) 
                           (MS x1514 x1515 r)))))
         :named hyp110))
(assert (! (exists ((n88 Int)) 
               (and 
                   (<= 0 n88) 
                   (forall ((x1517 Int) (x1518 A)) 
                       (=> 
                           (MS1 x1517 x1518 p) 
                           (and 
                               (<= 1 x1517) 
                               (<= x1517 n88)))) 
                   (forall ((x1519 Int) (x1520 A) (x1521 A)) 
                       (=> 
                           (and 
                               (MS1 x1519 x1520 p) 
                               (MS1 x1519 x1521 p)) 
                           (= x1520 x1521))) 
                   (forall ((x1522 Int)) 
                       (=> 
                           (and 
                               (<= 1 x1522) 
                               (<= x1522 n88)) 
                           (exists ((x1523 A)) 
                               (MS1 x1522 x1523 p))))))
         :named hyp111))
(assert (! (forall ((x1524 A)) 
               (=> 
                   (exists ((x1525 Int)) 
                       (MS1 x1525 x1524 p)) 
                   (MS0 x1524 a)))
         :named hyp112))
(assert (! (forall ((x1526 Int)) 
               (=> 
                   (length p x1526) 
                   (< 1 x1526)))
         :named hyp113))
(assert (! (exists ((x1527 Int)) 
               (and 
                   (= x1527 1) 
                   (MS1 x1527 y2 p)))
         :named hyp114))
(assert (! (exists ((x1528 Int)) 
               (and 
                   (length p x1528) 
                   (MS1 x1528 x1 p)))
         :named hyp115))
(assert (! (forall ((i72 Int)) 
               (=> 
                   (and 
                       (<= 1 i72) 
                       (forall ((x1529 Int)) 
                           (=> 
                               (length p x1529) 
                               (<= i72 (- x1529 1))))) 
                   (exists ((x1530 A) (x1531 A)) 
                       (and 
                           (MS1 i72 x1530 p) 
                           (exists ((x1532 Int)) 
                               (and 
                                   (= x1532 (+ i72 1)) 
                                   (MS1 x1532 x1531 p))) 
                           (MS x1530 x1531 r)))))
         :named hyp116))
(assert (! (forall ((x1533 A) (y36 A)) 
               (=> 
                   (and 
                       (MS0 x1533 a) 
                       (MS0 y36 a)) 
                   (exists ((p25 PZA)) 
                       (and 
                           (exists ((n89 Int)) 
                               (and 
                                   (<= 0 n89) 
                                   (forall ((x1534 Int) (x1535 A)) 
                                       (=> 
                                           (MS1 x1534 x1535 p25) 
                                           (and 
                                               (<= 1 x1534) 
                                               (<= x1534 n89)))) 
                                   (forall ((x1536 Int) (x1537 A) (x1538 A)) 
                                       (=> 
                                           (and 
                                               (MS1 x1536 x1537 p25) 
                                               (MS1 x1536 x1538 p25)) 
                                           (= x1537 x1538))) 
                                   (forall ((x1539 Int)) 
                                       (=> 
                                           (and 
                                               (<= 1 x1539) 
                                               (<= x1539 n89)) 
                                           (exists ((x1540 A)) 
                                               (MS1 x1539 x1540 p25)))))) 
                           (forall ((x1541 A)) 
                               (=> 
                                   (exists ((x1542 Int)) 
                                       (MS1 x1542 x1541 p25)) 
                                   (MS0 x1541 a))) 
                           (forall ((x1543 Int)) 
                               (=> 
                                   (length p25 x1543) 
                                   (< 1 x1543))) 
                           (exists ((x1544 Int)) 
                               (and 
                                   (= x1544 1) 
                                   (MS1 x1544 x1533 p25))) 
                           (exists ((x1545 Int)) 
                               (and 
                                   (length p25 x1545) 
                                   (MS1 x1545 y36 p25))) 
                           (forall ((i73 Int)) 
                               (=> 
                                   (and 
                                       (<= 1 i73) 
                                       (forall ((x1546 Int)) 
                                           (=> 
                                               (length p25 x1546) 
                                               (<= i73 (- x1546 1))))) 
                                   (exists ((x1547 A) (x1548 A)) 
                                       (and 
                                           (MS1 i73 x1547 p25) 
                                           (exists ((x1549 Int)) 
                                               (and 
                                                   (= x1549 (+ i73 1)) 
                                                   (MS1 x1549 x1548 p25))) 
                                           (MS x1547 x1548 r))))) 
                           (exists ((x1550 Int)) 
                               (and 
                                   (length p25 x1550) 
                                   (dist x1533 y36 x1550)))))))
         :named hyp117))
(assert (! (forall ((x1551 A) (y37 A) (p26 PZA) (i74 Int)) 
               (=> 
                   (and 
                       (MS0 x1551 a) 
                       (MS0 y37 a) 
                       (exists ((n90 Int)) 
                           (and 
                               (<= 0 n90) 
                               (forall ((x1552 Int) (x1553 A)) 
                                   (=> 
                                       (MS1 x1552 x1553 p26) 
                                       (and 
                                           (<= 1 x1552) 
                                           (<= x1552 n90)))) 
                               (forall ((x1554 Int) (x1555 A) (x1556 A)) 
                                   (=> 
                                       (and 
                                           (MS1 x1554 x1555 p26) 
                                           (MS1 x1554 x1556 p26)) 
                                       (= x1555 x1556))) 
                               (forall ((x1557 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x1557) 
                                           (<= x1557 n90)) 
                                       (exists ((x1558 A)) 
                                           (MS1 x1557 x1558 p26)))))) 
                       (forall ((x1559 A)) 
                           (=> 
                               (exists ((x1560 Int)) 
                                   (MS1 x1560 x1559 p26)) 
                               (MS0 x1559 a))) 
                       (forall ((x1561 Int)) 
                           (=> 
                               (length p26 x1561) 
                               (< 1 x1561))) 
                       (exists ((x1562 Int)) 
                           (and 
                               (= x1562 1) 
                               (MS1 x1562 x1551 p26))) 
                       (exists ((x1563 Int)) 
                           (and 
                               (length p26 x1563) 
                               (MS1 x1563 y37 p26))) 
                       (forall ((i75 Int)) 
                           (=> 
                               (and 
                                   (<= 1 i75) 
                                   (forall ((x1564 Int)) 
                                       (=> 
                                           (length p26 x1564) 
                                           (<= i75 (- x1564 1))))) 
                               (exists ((x1565 A) (x1566 A)) 
                                   (and 
                                       (MS1 i75 x1565 p26) 
                                       (exists ((x1567 Int)) 
                                           (and 
                                               (= x1567 (+ i75 1)) 
                                               (MS1 x1567 x1566 p26))) 
                                       (MS x1565 x1566 r))))) 
                       (exists ((x1568 Int)) 
                           (and 
                               (length p26 x1568) 
                               (dist x1551 y37 x1568))) 
                       (exists ((x1569 A)) 
                           (MS1 i74 x1569 p26)) 
                       (not 
                           (= i74 1)) 
                       (not 
                           (length p26 i74))) 
                   (and 
                       (exists ((n91 Int)) 
                           (and 
                               (<= 0 n91) 
                               (forall ((x1570 Int) (x1571 A)) 
                                   (=> 
                                       (and 
                                           (MS1 x1570 x1571 p26) 
                                           (<= 1 x1570) 
                                           (<= x1570 i74)) 
                                       (and 
                                           (<= 1 x1570) 
                                           (<= x1570 n91)))) 
                               (forall ((x1572 Int) (x1573 A) (x1574 A)) 
                                   (=> 
                                       (and 
                                           (MS1 x1572 x1573 p26) 
                                           (<= 1 x1572) 
                                           (<= x1572 i74) 
                                           (MS1 x1572 x1574 p26)) 
                                       (= x1573 x1574))) 
                               (forall ((x1575 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x1575) 
                                           (<= x1575 n91)) 
                                       (exists ((x1576 A)) 
                                           (and 
                                               (MS1 x1575 x1576 p26) 
                                               (<= 1 x1575) 
                                               (<= x1575 i74))))))) 
                       (forall ((x1577 A)) 
                           (=> 
                               (exists ((x1578 Int)) 
                                   (and 
                                       (MS1 x1578 x1577 p26) 
                                       (<= 1 x1578) 
                                       (<= x1578 i74))) 
                               (MS0 x1577 a))) 
                       (forall ((x1579 Int)) 
                           (=> 
                               (exists ((x1580 PZA)) 
                                   (and 
                                       (forall ((x1581 Int) (x1582 A)) 
                                           (= 
                                               (MS1 x1581 x1582 x1580) 
                                               (and 
                                                   (MS1 x1581 x1582 p26) 
                                                   (<= 1 x1581) 
                                                   (<= x1581 i74)))) 
                                       (length x1580 x1579))) 
                               (< 1 x1579))) 
                       (exists ((x1583 Int)) 
                           (and 
                               (= x1583 1) 
                               (MS1 x1583 x1551 p26))) 
                       (<= 1 1) 
                       (<= 1 i74) 
                       (exists ((x1584 Int) (x1585 A)) 
                           (and 
                               (exists ((x1586 PZA)) 
                                   (and 
                                       (forall ((x1587 Int) (x1588 A)) 
                                           (= 
                                               (MS1 x1587 x1588 x1586) 
                                               (and 
                                                   (MS1 x1587 x1588 p26) 
                                                   (<= 1 x1587) 
                                                   (<= x1587 i74)))) 
                                       (length x1586 x1584))) 
                               (MS1 i74 x1585 p26) 
                               (MS1 x1584 x1585 p26))) 
                       (forall ((x1589 Int)) 
                           (=> 
                               (exists ((x1590 PZA)) 
                                   (and 
                                       (forall ((x1591 Int) (x1592 A)) 
                                           (= 
                                               (MS1 x1591 x1592 x1590) 
                                               (and 
                                                   (MS1 x1591 x1592 p26) 
                                                   (<= 1 x1591) 
                                                   (<= x1591 i74)))) 
                                       (length x1590 x1589))) 
                               (<= 1 x1589))) 
                       (forall ((x1593 Int)) 
                           (=> 
                               (exists ((x1594 PZA)) 
                                   (and 
                                       (forall ((x1595 Int) (x1596 A)) 
                                           (= 
                                               (MS1 x1595 x1596 x1594) 
                                               (and 
                                                   (MS1 x1595 x1596 p26) 
                                                   (<= 1 x1595) 
                                                   (<= x1595 i74)))) 
                                       (length x1594 x1593))) 
                               (<= x1593 i74))) 
                       (forall ((i76 Int)) 
                           (=> 
                               (and 
                                   (<= 1 i76) 
                                   (forall ((x1597 Int)) 
                                       (=> 
                                           (exists ((x1598 PZA)) 
                                               (and 
                                                   (forall ((x1599 Int) (x1600 A)) 
                                                       (= 
                                                           (MS1 x1599 x1600 x1598) 
                                                           (and 
                                                               (MS1 x1599 x1600 p26) 
                                                               (<= 1 x1599) 
                                                               (<= x1599 i74)))) 
                                                   (length x1598 x1597))) 
                                           (<= i76 (- x1597 1))))) 
                               (exists ((x1601 A) (x1602 A)) 
                                   (and 
                                       (MS1 i76 x1601 p26) 
                                       (<= 1 i76) 
                                       (<= i76 i74) 
                                       (exists ((x1603 Int)) 
                                           (and 
                                               (= x1603 (+ i76 1)) 
                                               (MS1 x1603 x1602 p26))) 
                                       (<= 1 (+ i76 1)) 
                                       (<= (+ i76 1) i74) 
                                       (MS x1601 x1602 r))))) 
                       (exists ((x1604 A) (x1605 Int)) 
                           (and 
                               (MS1 i74 x1604 p26) 
                               (exists ((x1606 PZA)) 
                                   (and 
                                       (forall ((x1607 Int) (x1608 A)) 
                                           (= 
                                               (MS1 x1607 x1608 x1606) 
                                               (and 
                                                   (MS1 x1607 x1608 p26) 
                                                   (<= 1 x1607) 
                                                   (<= x1607 i74)))) 
                                       (length x1606 x1605))) 
                               (dist x1551 x1604 x1605))))))
         :named hyp118))
(assert (! (forall ((x1609 A) (y38 A) (p27 PZA) (i77 Int)) 
               (=> 
                   (and 
                       (MS0 x1609 a) 
                       (MS0 y38 a) 
                       (exists ((n92 Int)) 
                           (and 
                               (<= 0 n92) 
                               (forall ((x1610 Int) (x1611 A)) 
                                   (=> 
                                       (MS1 x1610 x1611 p27) 
                                       (and 
                                           (<= 1 x1610) 
                                           (<= x1610 n92)))) 
                               (forall ((x1612 Int) (x1613 A) (x1614 A)) 
                                   (=> 
                                       (and 
                                           (MS1 x1612 x1613 p27) 
                                           (MS1 x1612 x1614 p27)) 
                                       (= x1613 x1614))) 
                               (forall ((x1615 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x1615) 
                                           (<= x1615 n92)) 
                                       (exists ((x1616 A)) 
                                           (MS1 x1615 x1616 p27)))))) 
                       (forall ((x1617 A)) 
                           (=> 
                               (exists ((x1618 Int)) 
                                   (MS1 x1618 x1617 p27)) 
                               (MS0 x1617 a))) 
                       (forall ((x1619 Int)) 
                           (=> 
                               (length p27 x1619) 
                               (< 1 x1619))) 
                       (exists ((x1620 Int)) 
                           (and 
                               (= x1620 1) 
                               (MS1 x1620 x1609 p27))) 
                       (exists ((x1621 Int)) 
                           (and 
                               (length p27 x1621) 
                               (MS1 x1621 y38 p27))) 
                       (forall ((i78 Int)) 
                           (=> 
                               (and 
                                   (<= 1 i78) 
                                   (forall ((x1622 Int)) 
                                       (=> 
                                           (length p27 x1622) 
                                           (<= i78 (- x1622 1))))) 
                               (exists ((x1623 A) (x1624 A)) 
                                   (and 
                                       (MS1 i78 x1623 p27) 
                                       (exists ((x1625 Int)) 
                                           (and 
                                               (= x1625 (+ i78 1)) 
                                               (MS1 x1625 x1624 p27))) 
                                       (MS x1623 x1624 r))))) 
                       (exists ((x1626 Int)) 
                           (and 
                               (length p27 x1626) 
                               (dist x1609 y38 x1626))) 
                       (exists ((x1627 A)) 
                           (MS1 i77 x1627 p27)) 
                       (not 
                           (= i77 1)) 
                       (not 
                           (length p27 i77))) 
                   (and 
                       (exists ((x1628 A)) 
                           (and 
                               (MS1 i77 x1628 p27) 
                               (dist x1609 x1628 i77))) 
                       (exists ((x1629 A) (x1630 Int)) 
                           (and 
                               (exists ((x1631 Int)) 
                                   (and 
                                       (= x1631 (+ i77 1)) 
                                       (MS1 x1631 x1629 p27))) 
                               (= x1630 (+ i77 1)) 
                               (dist x1609 x1629 x1630))) 
                       (exists ((x1632 A) (x1633 A)) 
                           (and 
                               (MS1 i77 x1632 p27) 
                               (exists ((x1634 Int)) 
                                   (and 
                                       (= x1634 (+ i77 1)) 
                                       (MS1 x1634 x1633 p27))) 
                               (MS x1632 x1633 r))))))
         :named hyp119))
(assert (! (forall ((x1635 A) (y39 A) (p28 PZA) (z5 A)) 
               (=> 
                   (and 
                       (MS0 x1635 a) 
                       (MS0 y39 a) 
                       (exists ((n93 Int)) 
                           (and 
                               (<= 0 n93) 
                               (forall ((x1636 Int) (x1637 A)) 
                                   (=> 
                                       (MS1 x1636 x1637 p28) 
                                       (and 
                                           (<= 1 x1636) 
                                           (<= x1636 n93)))) 
                               (forall ((x1638 Int) (x1639 A) (x1640 A)) 
                                   (=> 
                                       (and 
                                           (MS1 x1638 x1639 p28) 
                                           (MS1 x1638 x1640 p28)) 
                                       (= x1639 x1640))) 
                               (forall ((x1641 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x1641) 
                                           (<= x1641 n93)) 
                                       (exists ((x1642 A)) 
                                           (MS1 x1641 x1642 p28)))))) 
                       (forall ((x1643 A)) 
                           (=> 
                               (exists ((x1644 Int)) 
                                   (MS1 x1644 x1643 p28)) 
                               (MS0 x1643 a))) 
                       (forall ((x1645 Int)) 
                           (=> 
                               (length p28 x1645) 
                               (< 1 x1645))) 
                       (exists ((x1646 Int)) 
                           (and 
                               (= x1646 1) 
                               (MS1 x1646 x1635 p28))) 
                       (exists ((x1647 Int)) 
                           (and 
                               (length p28 x1647) 
                               (MS1 x1647 y39 p28))) 
                       (forall ((i79 Int)) 
                           (=> 
                               (and 
                                   (<= 1 i79) 
                                   (forall ((x1648 Int)) 
                                       (=> 
                                           (length p28 x1648) 
                                           (<= i79 (- x1648 1))))) 
                               (exists ((x1649 A) (x1650 A)) 
                                   (and 
                                       (MS1 i79 x1649 p28) 
                                       (exists ((x1651 Int)) 
                                           (and 
                                               (= x1651 (+ i79 1)) 
                                               (MS1 x1651 x1650 p28))) 
                                       (MS x1649 x1650 r))))) 
                       (exists ((x1652 Int)) 
                           (and 
                               (length p28 x1652) 
                               (dist x1635 y39 x1652))) 
                       (exists ((x1653 Int)) 
                           (MS1 x1653 z5 p28)) 
                       (not 
                           (= z5 x1635)) 
                       (not 
                           (= z5 y39))) 
                   (exists ((t4 A)) 
                       (and 
                           (MS0 t4 a) 
                           (forall ((x1654 Int) (x1655 Int)) 
                               (=> 
                                   (and 
                                       (dist x1635 z5 x1655) 
                                       (dist x1635 t4 x1654)) 
                                   (< x1655 x1654))) 
                           (MS z5 t4 r)))))
         :named hyp120))
(assert (! (forall ((x1656 A) (y40 A) (p29 PZA)) 
               (=> 
                   (and 
                       (exists ((n94 Int)) 
                           (and 
                               (<= 0 n94) 
                               (forall ((x1657 Int) (x1658 A)) 
                                   (=> 
                                       (MS1 x1657 x1658 p29) 
                                       (and 
                                           (<= 1 x1657) 
                                           (<= x1657 n94)))) 
                               (forall ((x1659 Int) (x1660 A) (x1661 A)) 
                                   (=> 
                                       (and 
                                           (MS1 x1659 x1660 p29) 
                                           (MS1 x1659 x1661 p29)) 
                                       (= x1660 x1661))) 
                               (forall ((x1662 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x1662) 
                                           (<= x1662 n94)) 
                                       (exists ((x1663 A)) 
                                           (MS1 x1662 x1663 p29)))))) 
                       (forall ((x1664 A)) 
                           (=> 
                               (exists ((x1665 Int)) 
                                   (MS1 x1665 x1664 p29)) 
                               (MS0 x1664 a))) 
                       (forall ((x1666 Int)) 
                           (=> 
                               (length p29 x1666) 
                               (< 1 x1666))) 
                       (exists ((x1667 Int)) 
                           (and 
                               (= x1667 1) 
                               (MS1 x1667 x1656 p29))) 
                       (exists ((x1668 Int)) 
                           (and 
                               (length p29 x1668) 
                               (MS1 x1668 y40 p29))) 
                       (forall ((i80 Int)) 
                           (=> 
                               (and 
                                   (<= 1 i80) 
                                   (forall ((x1669 Int)) 
                                       (=> 
                                           (length p29 x1669) 
                                           (<= i80 (- x1669 1))))) 
                               (exists ((x1670 A) (x1671 A)) 
                                   (and 
                                       (MS1 i80 x1670 p29) 
                                       (exists ((x1672 Int)) 
                                           (and 
                                               (= x1672 (+ i80 1)) 
                                               (MS1 x1672 x1671 p29))) 
                                       (MS x1670 x1671 r)))))) 
                   (and 
                       (exists ((n95 Int)) 
                           (and 
                               (<= 0 n95) 
                               (forall ((x1673 Int) (x1674 A)) 
                                   (=> 
                                       (exists ((i81 Int)) 
                                           (and 
                                               (<= 1 i81) 
                                               (forall ((x1675 Int)) 
                                                   (=> 
                                                       (length p29 x1675) 
                                                       (<= i81 x1675))) 
                                               (= x1673 i81) 
                                               (exists ((x1676 Int)) 
                                                   (and 
                                                       (forall ((x1677 Int)) 
                                                           (=> 
                                                               (length p29 x1677) 
                                                               (= x1676 (+ (- x1677 i81) 1)))) 
                                                       (MS1 x1676 x1674 p29))))) 
                                       (and 
                                           (<= 1 x1673) 
                                           (<= x1673 n95)))) 
                               (forall ((x1678 Int) (x1679 A) (x1680 A)) 
                                   (=> 
                                       (and 
                                           (exists ((i82 Int)) 
                                               (and 
                                                   (<= 1 i82) 
                                                   (forall ((x1681 Int)) 
                                                       (=> 
                                                           (length p29 x1681) 
                                                           (<= i82 x1681))) 
                                                   (= x1678 i82) 
                                                   (exists ((x1682 Int)) 
                                                       (and 
                                                           (forall ((x1683 Int)) 
                                                               (=> 
                                                                   (length p29 x1683) 
                                                                   (= x1682 (+ (- x1683 i82) 1)))) 
                                                           (MS1 x1682 x1679 p29))))) 
                                           (exists ((i83 Int)) 
                                               (and 
                                                   (<= 1 i83) 
                                                   (forall ((x1684 Int)) 
                                                       (=> 
                                                           (length p29 x1684) 
                                                           (<= i83 x1684))) 
                                                   (= x1678 i83) 
                                                   (exists ((x1685 Int)) 
                                                       (and 
                                                           (forall ((x1686 Int)) 
                                                               (=> 
                                                                   (length p29 x1686) 
                                                                   (= x1685 (+ (- x1686 i83) 1)))) 
                                                           (MS1 x1685 x1680 p29)))))) 
                                       (= x1679 x1680))) 
                               (forall ((x1687 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x1687) 
                                           (<= x1687 n95)) 
                                       (exists ((x1688 A) (i84 Int)) 
                                           (and 
                                               (<= 1 i84) 
                                               (forall ((x1689 Int)) 
                                                   (=> 
                                                       (length p29 x1689) 
                                                       (<= i84 x1689))) 
                                               (= x1687 i84) 
                                               (exists ((x1690 Int)) 
                                                   (and 
                                                       (forall ((x1691 Int)) 
                                                           (=> 
                                                               (length p29 x1691) 
                                                               (= x1690 (+ (- x1691 i84) 1)))) 
                                                       (MS1 x1690 x1688 p29))))))))) 
                       (forall ((i85 Int)) 
                           (=> 
                               (and 
                                   (<= 1 i85) 
                                   (forall ((x1692 Int)) 
                                       (=> 
                                           (length p29 x1692) 
                                           (<= i85 x1692)))) 
                               (exists ((x1693 A)) 
                                   (and 
                                       (exists ((x1694 Int)) 
                                           (and 
                                               (forall ((x1695 Int)) 
                                                   (=> 
                                                       (length p29 x1695) 
                                                       (= x1694 (+ (- x1695 i85) 1)))) 
                                               (MS1 x1694 x1693 p29))) 
                                       (MS0 x1693 a))))) 
                       (forall ((x1696 Int)) 
                           (=> 
                               (exists ((x1697 PZA)) 
                                   (and 
                                       (forall ((x1698 Int) (x1699 A)) 
                                           (= 
                                               (MS1 x1698 x1699 x1697) 
                                               (exists ((i86 Int)) 
                                                   (and 
                                                       (<= 1 i86) 
                                                       (forall ((x1700 Int)) 
                                                           (=> 
                                                               (length p29 x1700) 
                                                               (<= i86 x1700))) 
                                                       (= x1698 i86) 
                                                       (exists ((x1701 Int)) 
                                                           (and 
                                                               (forall ((x1702 Int)) 
                                                                   (=> 
                                                                       (length p29 x1702) 
                                                                       (= x1701 (+ (- x1702 i86) 1)))) 
                                                               (MS1 x1701 x1699 p29))))))) 
                                       (length x1697 x1696))) 
                               (< 1 x1696))) 
                       (exists ((x1703 Int)) 
                           (and 
                               (forall ((x1704 Int)) 
                                   (=> 
                                       (length p29 x1704) 
                                       (= x1703 (+ (- x1704 1) 1)))) 
                               (MS1 x1703 y40 p29))) 
                       (exists ((x1705 Int)) 
                           (and 
                               (forall ((x1706 Int) (x1707 Int)) 
                                   (=> 
                                       (and 
                                           (length p29 x1707) 
                                           (exists ((x1708 PZA)) 
                                               (and 
                                                   (forall ((x1709 Int) (x1710 A)) 
                                                       (= 
                                                           (MS1 x1709 x1710 x1708) 
                                                           (exists ((i87 Int)) 
                                                               (and 
                                                                   (<= 1 i87) 
                                                                   (forall ((x1711 Int)) 
                                                                       (=> 
                                                                           (length p29 x1711) 
                                                                           (<= i87 x1711))) 
                                                                   (= x1709 i87) 
                                                                   (exists ((x1712 Int)) 
                                                                       (and 
                                                                           (forall ((x1713 Int)) 
                                                                               (=> 
                                                                                   (length p29 x1713) 
                                                                                   (= x1712 (+ (- x1713 i87) 1)))) 
                                                                           (MS1 x1712 x1710 p29))))))) 
                                                   (length x1708 x1706)))) 
                                       (= x1705 (+ (- x1707 x1706) 1)))) 
                               (MS1 x1705 x1656 p29))) 
                       (forall ((i88 Int)) 
                           (=> 
                               (and 
                                   (<= 1 i88) 
                                   (forall ((x1714 Int)) 
                                       (=> 
                                           (exists ((x1715 PZA)) 
                                               (and 
                                                   (forall ((x1716 Int) (x1717 A)) 
                                                       (= 
                                                           (MS1 x1716 x1717 x1715) 
                                                           (exists ((i89 Int)) 
                                                               (and 
                                                                   (<= 1 i89) 
                                                                   (forall ((x1718 Int)) 
                                                                       (=> 
                                                                           (length p29 x1718) 
                                                                           (<= i89 x1718))) 
                                                                   (= x1716 i89) 
                                                                   (exists ((x1719 Int)) 
                                                                       (and 
                                                                           (forall ((x1720 Int)) 
                                                                               (=> 
                                                                                   (length p29 x1720) 
                                                                                   (= x1719 (+ (- x1720 i89) 1)))) 
                                                                           (MS1 x1719 x1717 p29))))))) 
                                                   (length x1715 x1714))) 
                                           (<= i88 (- x1714 1))))) 
                               (exists ((x1721 A) (x1722 A)) 
                                   (and 
                                       (exists ((x1723 Int)) 
                                           (and 
                                               (forall ((x1724 Int)) 
                                                   (=> 
                                                       (length p29 x1724) 
                                                       (= x1723 (+ (- x1724 i88) 1)))) 
                                               (MS1 x1723 x1721 p29))) 
                                       (exists ((x1725 Int)) 
                                           (and 
                                               (forall ((x1726 Int)) 
                                                   (=> 
                                                       (length p29 x1726) 
                                                       (= x1725 (+ (- x1726 (+ i88 1)) 1)))) 
                                               (MS1 x1725 x1722 p29))) 
                                       (MS x1721 x1722 r))))))))
         :named hyp121))
(assert (! (exists ((x1727 A)) 
               (and 
                   (exists ((x1728 Int)) 
                       (and 
                           (= x1728 1) 
                           (MS1 x1728 x1727 q))) 
                   (MS0 x1727 a)))
         :named hyp122))
(assert (! (exists ((x1729 A)) 
               (and 
                   (exists ((x1730 Int)) 
                       (and 
                           (= x1730 1) 
                           (MS1 x1730 x1729 q))) 
                   (MS x1 x1729 r)))
         :named hyp123))
(assert (! (exists ((x1731 A)) 
               (and 
                   (exists ((x1732 Int)) 
                       (and 
                           (length q x1732) 
                           (MS1 x1732 x1731 q))) 
                   (MS0 x1731 a)))
         :named hyp124))
(assert (! (exists ((x1733 A)) 
               (and 
                   (exists ((x1734 Int)) 
                       (and 
                           (= x1734 1) 
                           (MS1 x1734 x1733 p))) 
                   (MS0 x1733 a)))
         :named hyp125))
(assert (! (exists ((x1735 A)) 
               (and 
                   (exists ((x1736 Int)) 
                       (and 
                           (length p x1736) 
                           (MS1 x1736 x1735 p))) 
                   (MS0 x1735 a)))
         :named hyp126))
(assert (! (exists ((x1737 A) (x1738 A)) 
               (and 
                   (exists ((x1739 Int)) 
                       (and 
                           (length p x1739) 
                           (MS1 x1739 x1737 p))) 
                   (exists ((x1740 Int)) 
                       (and 
                           (= x1740 1) 
                           (MS1 x1740 x1738 q))) 
                   (MS x1737 x1738 r)))
         :named hyp127))
(assert (! (not 
               (forall ((x1741 A)) 
                   (=> 
                       (or 
                           (exists ((x1742 Int)) 
                               (exists ((i90 Int)) 
                                   (and 
                                       (<= 1 i90) 
                                       (forall ((x1743 Int)) 
                                           (=> 
                                               (length p x1743) 
                                               (<= i90 x1743))) 
                                       (= x1742 i90) 
                                       (MS1 i90 x1741 p)))) 
                           (exists ((x1744 Int)) 
                               (exists ((i91 Int)) 
                                   (and 
                                       (forall ((x1745 Int)) 
                                           (=> 
                                               (length p x1745) 
                                               (<= (+ x1745 1) i91))) 
                                       (forall ((x1746 Int) (x1747 Int)) 
                                           (=> 
                                               (and 
                                                   (length p x1747) 
                                                   (length q x1746)) 
                                               (<= i91 (+ x1747 x1746)))) 
                                       (= x1744 i91) 
                                       (exists ((x1748 Int)) 
                                           (and 
                                               (forall ((x1749 Int)) 
                                                   (=> 
                                                       (length p x1749) 
                                                       (= x1748 (- i91 x1749)))) 
                                               (MS1 x1748 x1741 q))))))) 
                       (MS0 x1741 a))))
         :named goal))
(check-sat)
(exit)

