(set-info :smt-lib-version 2.6)
(set-logic AUFLIA)
(set-info :source |Generator: Rodin SMT Plug-in|)
(set-info :license "https://creativecommons.org/licenses/by-nc/4.0/")
(set-info :category "industrial")
(set-info :status unsat)

(declare-sort A 0)
(declare-sort PA 0)
(declare-sort PAA 0)
(declare-sort PZA 0)
(declare-fun MS (Int A PZA) Bool)
(declare-fun MS0 (A A PAA) Bool)
(declare-fun MS1 (A PA) Bool)
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
(assert (forall ((x1746 A) (x1747 A)) 
            (exists ((X PAA)) 
                (and 
                    (MS0 x1746 x1747 X) 
                    (forall ((y41 A) (y42 A)) 
                        (=> 
                            (MS0 y41 y42 X) 
                            (and 
                                (= y41 x1746) 
                                (= y42 x1747))))))))
; Elementary Sets axiom (Singleton part)
(assert (forall ((x1748 A)) 
            (exists ((X0 PA)) 
                (and 
                    (MS1 x1748 X0) 
                    (forall ((y43 A)) 
                        (=> 
                            (MS1 y43 X0) 
                            (= y43 x1748)))))))
; Elementary Sets axiom (Singleton part)
(assert (forall ((x1749 Int) (x1750 A)) 
            (exists ((X1 PZA)) 
                (and 
                    (MS x1749 x1750 X1) 
                    (forall ((y44 Int) (y45 A)) 
                        (=> 
                            (MS y44 y45 X1) 
                            (and 
                                (= y44 x1749) 
                                (= y45 x1750))))))))
(assert (! (forall ((x0 PZA)) 
               (= 
                   (seq x0) 
                   (exists ((s PZA)) 
                       (and 
                           (exists ((n Int)) 
                               (and 
                                   (<= 0 n) 
                                   (forall ((x2 Int) (x3 A)) 
                                       (=> 
                                           (MS x2 x3 s) 
                                           (and 
                                               (<= 1 x2) 
                                               (<= x2 n)))) 
                                   (forall ((x4 Int) (x5 A) (x6 A)) 
                                       (=> 
                                           (and 
                                               (MS x4 x5 s) 
                                               (MS x4 x6 s)) 
                                           (= x5 x6))) 
                                   (forall ((x7 Int)) 
                                       (=> 
                                           (and 
                                               (<= 1 x7) 
                                               (<= x7 n)) 
                                           (exists ((x8 A)) 
                                               (MS x7 x8 s)))))) 
                           (forall ((x9 Int) (x10 A)) 
                               (= 
                                   (MS x9 x10 x0) 
                                   (MS x9 x10 s)))))))
         :named hyp1))
(assert (! (forall ((n0 Int) (s0 PZA)) 
               (=> 
                   (and 
                       (<= 0 n0) 
                       (forall ((x11 Int) (x12 A)) 
                           (=> 
                               (MS x11 x12 s0) 
                               (and 
                                   (<= 1 x11) 
                                   (<= x11 n0)))) 
                       (forall ((x13 Int) (x14 A) (x15 A)) 
                           (=> 
                               (and 
                                   (MS x13 x14 s0) 
                                   (MS x13 x15 s0)) 
                               (= x14 x15))) 
                       (forall ((x16 Int)) 
                           (=> 
                               (and 
                                   (<= 1 x16) 
                                   (<= x16 n0)) 
                               (exists ((x17 A)) 
                                   (MS x16 x17 s0))))) 
                   (length s0 n0)))
         :named hyp2))
(assert (! (forall ((x18 A) (x19 A)) 
               (not 
                   (and 
                       (MS0 x18 x19 r) 
                       (= x18 x19))))
         :named hyp3))
(assert (! (and 
               (forall ((x20 A) (x21 A) (x22 Int)) 
                   (=> 
                       (dist x20 x21 x22) 
                       (and 
                           (MS1 x20 a) 
                           (MS1 x21 a) 
                           (<= 0 x22)))) 
               (forall ((x23 A) (x24 A) (x25 Int) (x26 Int)) 
                   (=> 
                       (and 
                           (dist x23 x24 x25) 
                           (dist x23 x24 x26)) 
                       (= x25 x26))) 
               (forall ((x27 A) (x28 A)) 
                   (=> 
                       (and 
                           (MS1 x27 a) 
                           (MS1 x28 a)) 
                       (exists ((x29 Int)) 
                           (dist x27 x28 x29)))))
         :named hyp4))
(assert (! (forall ((x30 A) (x31 A)) 
               (=> 
                   (MS0 x30 x31 r) 
                   (MS0 x31 x30 r)))
         :named hyp5))
(assert (! (forall ((x32 A) (y A)) 
               (=> 
                   (and 
                       (MS1 x32 a) 
                       (MS1 y a)) 
                   (exists ((x33 Int)) 
                       (and 
                           (dist y x32 x33) 
                           (dist x32 y x33)))))
         :named hyp6))
(assert (! (and 
               (forall ((x34 PZA) (x35 Int)) 
                   (=> 
                       (length x34 x35) 
                       (and 
                           (exists ((s1 PZA)) 
                               (and 
                                   (exists ((n1 Int)) 
                                       (and 
                                           (<= 0 n1) 
                                           (forall ((x36 Int) (x37 A)) 
                                               (=> 
                                                   (MS x36 x37 s1) 
                                                   (and 
                                                       (<= 1 x36) 
                                                       (<= x36 n1)))) 
                                           (forall ((x38 Int) (x39 A) (x40 A)) 
                                               (=> 
                                                   (and 
                                                       (MS x38 x39 s1) 
                                                       (MS x38 x40 s1)) 
                                                   (= x39 x40))) 
                                           (forall ((x41 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x41) 
                                                       (<= x41 n1)) 
                                                   (exists ((x42 A)) 
                                                       (MS x41 x42 s1)))))) 
                                   (forall ((x43 Int) (x44 A)) 
                                       (= 
                                           (MS x43 x44 x34) 
                                           (MS x43 x44 s1))))) 
                           (<= 0 x35)))) 
               (forall ((x45 PZA) (x46 Int) (x47 Int)) 
                   (=> 
                       (and 
                           (length x45 x46) 
                           (length x45 x47)) 
                       (= x46 x47))) 
               (forall ((x48 PZA)) 
                   (=> 
                       (exists ((s2 PZA)) 
                           (and 
                               (exists ((n2 Int)) 
                                   (and 
                                       (<= 0 n2) 
                                       (forall ((x49 Int) (x50 A)) 
                                           (=> 
                                               (MS x49 x50 s2) 
                                               (and 
                                                   (<= 1 x49) 
                                                   (<= x49 n2)))) 
                                       (forall ((x51 Int) (x52 A) (x53 A)) 
                                           (=> 
                                               (and 
                                                   (MS x51 x52 s2) 
                                                   (MS x51 x53 s2)) 
                                               (= x52 x53))) 
                                       (forall ((x54 Int)) 
                                           (=> 
                                               (and 
                                                   (<= 1 x54) 
                                                   (<= x54 n2)) 
                                               (exists ((x55 A)) 
                                                   (MS x54 x55 s2)))))) 
                               (forall ((x56 Int) (x57 A)) 
                                   (= 
                                       (MS x56 x57 x48) 
                                       (MS x56 x57 s2))))) 
                       (exists ((x58 Int)) 
                           (length x48 x58)))))
         :named hyp7))
(assert (! (forall ((n3 Int) (s3 PZA)) 
               (=> 
                   (and 
                       (<= 0 n3) 
                       (forall ((x59 Int) (x60 A)) 
                           (=> 
                               (MS x59 x60 s3) 
                               (and 
                                   (<= 1 x59) 
                                   (<= x59 n3)))) 
                       (forall ((x61 Int) (x62 A) (x63 A)) 
                           (=> 
                               (and 
                                   (MS x61 x62 s3) 
                                   (MS x61 x63 s3)) 
                               (= x62 x63))) 
                       (forall ((x64 Int)) 
                           (=> 
                               (and 
                                   (<= 1 x64) 
                                   (<= x64 n3)) 
                               (exists ((x65 A)) 
                                   (MS x64 x65 s3))))) 
                   (exists ((n4 Int)) 
                       (and 
                           (<= 0 n4) 
                           (forall ((x66 Int) (x67 A)) 
                               (=> 
                                   (MS x66 x67 s3) 
                                   (and 
                                       (<= 1 x66) 
                                       (<= x66 n4)))) 
                           (forall ((x68 Int) (x69 A) (x70 A)) 
                               (=> 
                                   (and 
                                       (MS x68 x69 s3) 
                                       (MS x68 x70 s3)) 
                                   (= x69 x70))) 
                           (forall ((x71 Int)) 
                               (=> 
                                   (and 
                                       (<= 1 x71) 
                                       (<= x71 n4)) 
                                   (exists ((x72 A)) 
                                       (MS x71 x72 s3))))))))
         :named hyp8))
(assert (! (forall ((s4 PZA)) 
               (=> 
                   (exists ((n5 Int)) 
                       (and 
                           (<= 0 n5) 
                           (forall ((x73 Int) (x74 A)) 
                               (=> 
                                   (MS x73 x74 s4) 
                                   (and 
                                       (<= 1 x73) 
                                       (<= x73 n5)))) 
                           (forall ((x75 Int) (x76 A) (x77 A)) 
                               (=> 
                                   (and 
                                       (MS x75 x76 s4) 
                                       (MS x75 x77 s4)) 
                                   (= x76 x77))) 
                           (forall ((x78 Int)) 
                               (=> 
                                   (and 
                                       (<= 1 x78) 
                                       (<= x78 n5)) 
                                   (exists ((x79 A)) 
                                       (MS x78 x79 s4)))))) 
                   (and 
                       (forall ((x80 Int) (x81 A)) 
                           (=> 
                               (MS x80 x81 s4) 
                               (and 
                                   (<= 1 x80) 
                                   (forall ((x82 Int)) 
                                       (=> 
                                           (length s4 x82) 
                                           (<= x80 x82)))))) 
                       (forall ((x83 Int) (x84 A) (x85 A)) 
                           (=> 
                               (and 
                                   (MS x83 x84 s4) 
                                   (MS x83 x85 s4)) 
                               (= x84 x85))) 
                       (forall ((x86 Int)) 
                           (=> 
                               (and 
                                   (<= 1 x86) 
                                   (forall ((x87 Int)) 
                                       (=> 
                                           (length s4 x87) 
                                           (<= x86 x87)))) 
                               (exists ((x88 A)) 
                                   (MS x86 x88 s4)))))))
         :named hyp9))
(assert (! (forall ((x89 PZA) (x90 PZA) (x91 PZA)) 
               (= 
                   (cnc x89 x90 x91) 
                   (exists ((s10 PZA) (s20 PZA)) 
                       (and 
                           (exists ((n6 Int)) 
                               (and 
                                   (<= 0 n6) 
                                   (forall ((x92 Int) (x93 A)) 
                                       (=> 
                                           (MS x92 x93 s10) 
                                           (and 
                                               (<= 1 x92) 
                                               (<= x92 n6)))) 
                                   (forall ((x94 Int) (x95 A) (x96 A)) 
                                       (=> 
                                           (and 
                                               (MS x94 x95 s10) 
                                               (MS x94 x96 s10)) 
                                           (= x95 x96))) 
                                   (forall ((x97 Int)) 
                                       (=> 
                                           (and 
                                               (<= 1 x97) 
                                               (<= x97 n6)) 
                                           (exists ((x98 A)) 
                                               (MS x97 x98 s10)))))) 
                           (exists ((n7 Int)) 
                               (and 
                                   (<= 0 n7) 
                                   (forall ((x99 Int) (x100 A)) 
                                       (=> 
                                           (MS x99 x100 s20) 
                                           (and 
                                               (<= 1 x99) 
                                               (<= x99 n7)))) 
                                   (forall ((x101 Int) (x102 A) (x103 A)) 
                                       (=> 
                                           (and 
                                               (MS x101 x102 s20) 
                                               (MS x101 x103 s20)) 
                                           (= x102 x103))) 
                                   (forall ((x104 Int)) 
                                       (=> 
                                           (and 
                                               (<= 1 x104) 
                                               (<= x104 n7)) 
                                           (exists ((x105 A)) 
                                               (MS x104 x105 s20)))))) 
                           (forall ((x106 Int) (x107 A)) 
                               (= 
                                   (MS x106 x107 x89) 
                                   (MS x106 x107 s10))) 
                           (forall ((x108 Int) (x109 A)) 
                               (= 
                                   (MS x108 x109 x90) 
                                   (MS x108 x109 s20))) 
                           (forall ((x110 Int) (x111 A)) 
                               (= 
                                   (MS x110 x111 x91) 
                                   (or 
                                       (exists ((i Int)) 
                                           (and 
                                               (<= 1 i) 
                                               (forall ((x112 Int)) 
                                                   (=> 
                                                       (length s10 x112) 
                                                       (<= i x112))) 
                                               (= x110 i) 
                                               (MS i x111 s10))) 
                                       (exists ((i0 Int)) 
                                           (and 
                                               (forall ((x113 Int)) 
                                                   (=> 
                                                       (length s10 x113) 
                                                       (<= (+ x113 1) i0))) 
                                               (forall ((x114 Int) (x115 Int)) 
                                                   (=> 
                                                       (and 
                                                           (length s10 x115) 
                                                           (length s20 x114)) 
                                                       (<= i0 (+ x115 x114)))) 
                                               (= x110 i0) 
                                               (exists ((x116 Int)) 
                                                   (and 
                                                       (forall ((x117 Int)) 
                                                           (=> 
                                                               (length s10 x117) 
                                                               (= x116 (- i0 x117)))) 
                                                       (MS x116 x111 s20))))))))))))
         :named hyp10))
(assert (! (forall ((x118 PZA) (x119 PZA)) 
               (= 
                   (reverse x118 x119) 
                   (exists ((s5 PZA)) 
                       (and 
                           (exists ((n8 Int)) 
                               (and 
                                   (<= 0 n8) 
                                   (forall ((x120 Int) (x121 A)) 
                                       (=> 
                                           (MS x120 x121 s5) 
                                           (and 
                                               (<= 1 x120) 
                                               (<= x120 n8)))) 
                                   (forall ((x122 Int) (x123 A) (x124 A)) 
                                       (=> 
                                           (and 
                                               (MS x122 x123 s5) 
                                               (MS x122 x124 s5)) 
                                           (= x123 x124))) 
                                   (forall ((x125 Int)) 
                                       (=> 
                                           (and 
                                               (<= 1 x125) 
                                               (<= x125 n8)) 
                                           (exists ((x126 A)) 
                                               (MS x125 x126 s5)))))) 
                           (forall ((x127 Int) (x128 A)) 
                               (= 
                                   (MS x127 x128 x118) 
                                   (MS x127 x128 s5))) 
                           (forall ((x129 Int) (x130 A)) 
                               (= 
                                   (MS x129 x130 x119) 
                                   (exists ((i1 Int)) 
                                       (and 
                                           (<= 1 i1) 
                                           (forall ((x131 Int)) 
                                               (=> 
                                                   (length s5 x131) 
                                                   (<= i1 x131))) 
                                           (= x129 i1) 
                                           (exists ((x132 Int)) 
                                               (and 
                                                   (forall ((x133 Int)) 
                                                       (=> 
                                                           (length s5 x133) 
                                                           (= x132 (+ (- x133 i1) 1)))) 
                                                   (MS x132 x130 s5)))))))))))
         :named hyp11))
(assert (! (forall ((x134 A) (x135 A) (x136 PZA)) 
               (= 
                   (path x134 x135 x136) 
                   (exists ((x137 A) (y0 A) (p0 PZA)) 
                       (and 
                           (exists ((n9 Int)) 
                               (and 
                                   (<= 0 n9) 
                                   (forall ((x138 Int) (x139 A)) 
                                       (=> 
                                           (MS x138 x139 p0) 
                                           (and 
                                               (<= 1 x138) 
                                               (<= x138 n9)))) 
                                   (forall ((x140 Int) (x141 A) (x142 A)) 
                                       (=> 
                                           (and 
                                               (MS x140 x141 p0) 
                                               (MS x140 x142 p0)) 
                                           (= x141 x142))) 
                                   (forall ((x143 Int)) 
                                       (=> 
                                           (and 
                                               (<= 1 x143) 
                                               (<= x143 n9)) 
                                           (exists ((x144 A)) 
                                               (MS x143 x144 p0)))))) 
                           (forall ((x145 A)) 
                               (=> 
                                   (exists ((x146 Int)) 
                                       (MS x146 x145 p0)) 
                                   (MS1 x145 a))) 
                           (forall ((x147 Int)) 
                               (=> 
                                   (length p0 x147) 
                                   (< 1 x147))) 
                           (exists ((x148 Int)) 
                               (and 
                                   (= x148 1) 
                                   (MS x148 x137 p0))) 
                           (exists ((x149 Int)) 
                               (and 
                                   (length p0 x149) 
                                   (MS x149 y0 p0))) 
                           (forall ((i2 Int)) 
                               (=> 
                                   (and 
                                       (<= 1 i2) 
                                       (forall ((x150 Int)) 
                                           (=> 
                                               (length p0 x150) 
                                               (<= i2 (- x150 1))))) 
                                   (exists ((x151 A) (x152 A)) 
                                       (and 
                                           (MS i2 x151 p0) 
                                           (exists ((x153 Int)) 
                                               (and 
                                                   (= x153 (+ i2 1)) 
                                                   (MS x153 x152 p0))) 
                                           (MS0 x151 x152 r))))) 
                           (= x134 x137) 
                           (= x135 y0) 
                           (forall ((x154 Int) (x155 A)) 
                               (= 
                                   (MS x154 x155 x136) 
                                   (MS x154 x155 p0)))))))
         :named hyp12))
(assert (! (and 
               (forall ((x156 PZA) (x157 PZA) (x158 PZA)) 
                   (=> 
                       (exists ((s11 PZA) (s21 PZA)) 
                           (and 
                               (exists ((n10 Int)) 
                                   (and 
                                       (<= 0 n10) 
                                       (forall ((x159 Int) (x160 A)) 
                                           (=> 
                                               (MS x159 x160 s11) 
                                               (and 
                                                   (<= 1 x159) 
                                                   (<= x159 n10)))) 
                                       (forall ((x161 Int) (x162 A) (x163 A)) 
                                           (=> 
                                               (and 
                                                   (MS x161 x162 s11) 
                                                   (MS x161 x163 s11)) 
                                               (= x162 x163))) 
                                       (forall ((x164 Int)) 
                                           (=> 
                                               (and 
                                                   (<= 1 x164) 
                                                   (<= x164 n10)) 
                                               (exists ((x165 A)) 
                                                   (MS x164 x165 s11)))))) 
                               (exists ((n11 Int)) 
                                   (and 
                                       (<= 0 n11) 
                                       (forall ((x166 Int) (x167 A)) 
                                           (=> 
                                               (MS x166 x167 s21) 
                                               (and 
                                                   (<= 1 x166) 
                                                   (<= x166 n11)))) 
                                       (forall ((x168 Int) (x169 A) (x170 A)) 
                                           (=> 
                                               (and 
                                                   (MS x168 x169 s21) 
                                                   (MS x168 x170 s21)) 
                                               (= x169 x170))) 
                                       (forall ((x171 Int)) 
                                           (=> 
                                               (and 
                                                   (<= 1 x171) 
                                                   (<= x171 n11)) 
                                               (exists ((x172 A)) 
                                                   (MS x171 x172 s21)))))) 
                               (forall ((x173 Int) (x174 A)) 
                                   (= 
                                       (MS x173 x174 x156) 
                                       (MS x173 x174 s11))) 
                               (forall ((x175 Int) (x176 A)) 
                                   (= 
                                       (MS x175 x176 x157) 
                                       (MS x175 x176 s21))) 
                               (forall ((x177 Int) (x178 A)) 
                                   (= 
                                       (MS x177 x178 x158) 
                                       (or 
                                           (exists ((i3 Int)) 
                                               (and 
                                                   (<= 1 i3) 
                                                   (forall ((x179 Int)) 
                                                       (=> 
                                                           (length s11 x179) 
                                                           (<= i3 x179))) 
                                                   (= x177 i3) 
                                                   (MS i3 x178 s11))) 
                                           (exists ((i4 Int)) 
                                               (and 
                                                   (forall ((x180 Int)) 
                                                       (=> 
                                                           (length s11 x180) 
                                                           (<= (+ x180 1) i4))) 
                                                   (forall ((x181 Int) (x182 Int)) 
                                                       (=> 
                                                           (and 
                                                               (length s11 x182) 
                                                               (length s21 x181)) 
                                                           (<= i4 (+ x182 x181)))) 
                                                   (= x177 i4) 
                                                   (exists ((x183 Int)) 
                                                       (and 
                                                           (forall ((x184 Int)) 
                                                               (=> 
                                                                   (length s11 x184) 
                                                                   (= x183 (- i4 x184)))) 
                                                           (MS x183 x178 s21)))))))))) 
                       (and 
                           (exists ((s6 PZA)) 
                               (and 
                                   (exists ((n12 Int)) 
                                       (and 
                                           (<= 0 n12) 
                                           (forall ((x185 Int) (x186 A)) 
                                               (=> 
                                                   (MS x185 x186 s6) 
                                                   (and 
                                                       (<= 1 x185) 
                                                       (<= x185 n12)))) 
                                           (forall ((x187 Int) (x188 A) (x189 A)) 
                                               (=> 
                                                   (and 
                                                       (MS x187 x188 s6) 
                                                       (MS x187 x189 s6)) 
                                                   (= x188 x189))) 
                                           (forall ((x190 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x190) 
                                                       (<= x190 n12)) 
                                                   (exists ((x191 A)) 
                                                       (MS x190 x191 s6)))))) 
                                   (forall ((x192 Int) (x193 A)) 
                                       (= 
                                           (MS x192 x193 x156) 
                                           (MS x192 x193 s6))))) 
                           (exists ((s7 PZA)) 
                               (and 
                                   (exists ((n13 Int)) 
                                       (and 
                                           (<= 0 n13) 
                                           (forall ((x194 Int) (x195 A)) 
                                               (=> 
                                                   (MS x194 x195 s7) 
                                                   (and 
                                                       (<= 1 x194) 
                                                       (<= x194 n13)))) 
                                           (forall ((x196 Int) (x197 A) (x198 A)) 
                                               (=> 
                                                   (and 
                                                       (MS x196 x197 s7) 
                                                       (MS x196 x198 s7)) 
                                                   (= x197 x198))) 
                                           (forall ((x199 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x199) 
                                                       (<= x199 n13)) 
                                                   (exists ((x200 A)) 
                                                       (MS x199 x200 s7)))))) 
                                   (forall ((x201 Int) (x202 A)) 
                                       (= 
                                           (MS x201 x202 x157) 
                                           (MS x201 x202 s7))))) 
                           (exists ((s8 PZA)) 
                               (and 
                                   (exists ((n14 Int)) 
                                       (and 
                                           (<= 0 n14) 
                                           (forall ((x203 Int) (x204 A)) 
                                               (=> 
                                                   (MS x203 x204 s8) 
                                                   (and 
                                                       (<= 1 x203) 
                                                       (<= x203 n14)))) 
                                           (forall ((x205 Int) (x206 A) (x207 A)) 
                                               (=> 
                                                   (and 
                                                       (MS x205 x206 s8) 
                                                       (MS x205 x207 s8)) 
                                                   (= x206 x207))) 
                                           (forall ((x208 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x208) 
                                                       (<= x208 n14)) 
                                                   (exists ((x209 A)) 
                                                       (MS x208 x209 s8)))))) 
                                   (forall ((x210 Int) (x211 A)) 
                                       (= 
                                           (MS x210 x211 x158) 
                                           (MS x210 x211 s8)))))))) 
               (forall ((x212 PZA) (x213 PZA) (x214 PZA) (x215 PZA)) 
                   (=> 
                       (and 
                           (exists ((s12 PZA) (s22 PZA)) 
                               (and 
                                   (exists ((n15 Int)) 
                                       (and 
                                           (<= 0 n15) 
                                           (forall ((x216 Int) (x217 A)) 
                                               (=> 
                                                   (MS x216 x217 s12) 
                                                   (and 
                                                       (<= 1 x216) 
                                                       (<= x216 n15)))) 
                                           (forall ((x218 Int) (x219 A) (x220 A)) 
                                               (=> 
                                                   (and 
                                                       (MS x218 x219 s12) 
                                                       (MS x218 x220 s12)) 
                                                   (= x219 x220))) 
                                           (forall ((x221 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x221) 
                                                       (<= x221 n15)) 
                                                   (exists ((x222 A)) 
                                                       (MS x221 x222 s12)))))) 
                                   (exists ((n16 Int)) 
                                       (and 
                                           (<= 0 n16) 
                                           (forall ((x223 Int) (x224 A)) 
                                               (=> 
                                                   (MS x223 x224 s22) 
                                                   (and 
                                                       (<= 1 x223) 
                                                       (<= x223 n16)))) 
                                           (forall ((x225 Int) (x226 A) (x227 A)) 
                                               (=> 
                                                   (and 
                                                       (MS x225 x226 s22) 
                                                       (MS x225 x227 s22)) 
                                                   (= x226 x227))) 
                                           (forall ((x228 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x228) 
                                                       (<= x228 n16)) 
                                                   (exists ((x229 A)) 
                                                       (MS x228 x229 s22)))))) 
                                   (forall ((x230 Int) (x231 A)) 
                                       (= 
                                           (MS x230 x231 x212) 
                                           (MS x230 x231 s12))) 
                                   (forall ((x232 Int) (x233 A)) 
                                       (= 
                                           (MS x232 x233 x213) 
                                           (MS x232 x233 s22))) 
                                   (forall ((x234 Int) (x235 A)) 
                                       (= 
                                           (MS x234 x235 x214) 
                                           (or 
                                               (exists ((i5 Int)) 
                                                   (and 
                                                       (<= 1 i5) 
                                                       (forall ((x236 Int)) 
                                                           (=> 
                                                               (length s12 x236) 
                                                               (<= i5 x236))) 
                                                       (= x234 i5) 
                                                       (MS i5 x235 s12))) 
                                               (exists ((i6 Int)) 
                                                   (and 
                                                       (forall ((x237 Int)) 
                                                           (=> 
                                                               (length s12 x237) 
                                                               (<= (+ x237 1) i6))) 
                                                       (forall ((x238 Int) (x239 Int)) 
                                                           (=> 
                                                               (and 
                                                                   (length s12 x239) 
                                                                   (length s22 x238)) 
                                                               (<= i6 (+ x239 x238)))) 
                                                       (= x234 i6) 
                                                       (exists ((x240 Int)) 
                                                           (and 
                                                               (forall ((x241 Int)) 
                                                                   (=> 
                                                                       (length s12 x241) 
                                                                       (= x240 (- i6 x241)))) 
                                                               (MS x240 x235 s22)))))))))) 
                           (exists ((s13 PZA) (s23 PZA)) 
                               (and 
                                   (exists ((n17 Int)) 
                                       (and 
                                           (<= 0 n17) 
                                           (forall ((x242 Int) (x243 A)) 
                                               (=> 
                                                   (MS x242 x243 s13) 
                                                   (and 
                                                       (<= 1 x242) 
                                                       (<= x242 n17)))) 
                                           (forall ((x244 Int) (x245 A) (x246 A)) 
                                               (=> 
                                                   (and 
                                                       (MS x244 x245 s13) 
                                                       (MS x244 x246 s13)) 
                                                   (= x245 x246))) 
                                           (forall ((x247 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x247) 
                                                       (<= x247 n17)) 
                                                   (exists ((x248 A)) 
                                                       (MS x247 x248 s13)))))) 
                                   (exists ((n18 Int)) 
                                       (and 
                                           (<= 0 n18) 
                                           (forall ((x249 Int) (x250 A)) 
                                               (=> 
                                                   (MS x249 x250 s23) 
                                                   (and 
                                                       (<= 1 x249) 
                                                       (<= x249 n18)))) 
                                           (forall ((x251 Int) (x252 A) (x253 A)) 
                                               (=> 
                                                   (and 
                                                       (MS x251 x252 s23) 
                                                       (MS x251 x253 s23)) 
                                                   (= x252 x253))) 
                                           (forall ((x254 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x254) 
                                                       (<= x254 n18)) 
                                                   (exists ((x255 A)) 
                                                       (MS x254 x255 s23)))))) 
                                   (forall ((x256 Int) (x257 A)) 
                                       (= 
                                           (MS x256 x257 x212) 
                                           (MS x256 x257 s13))) 
                                   (forall ((x258 Int) (x259 A)) 
                                       (= 
                                           (MS x258 x259 x213) 
                                           (MS x258 x259 s23))) 
                                   (forall ((x260 Int) (x261 A)) 
                                       (= 
                                           (MS x260 x261 x215) 
                                           (or 
                                               (exists ((i7 Int)) 
                                                   (and 
                                                       (<= 1 i7) 
                                                       (forall ((x262 Int)) 
                                                           (=> 
                                                               (length s13 x262) 
                                                               (<= i7 x262))) 
                                                       (= x260 i7) 
                                                       (MS i7 x261 s13))) 
                                               (exists ((i8 Int)) 
                                                   (and 
                                                       (forall ((x263 Int)) 
                                                           (=> 
                                                               (length s13 x263) 
                                                               (<= (+ x263 1) i8))) 
                                                       (forall ((x264 Int) (x265 Int)) 
                                                           (=> 
                                                               (and 
                                                                   (length s13 x265) 
                                                                   (length s23 x264)) 
                                                               (<= i8 (+ x265 x264)))) 
                                                       (= x260 i8) 
                                                       (exists ((x266 Int)) 
                                                           (and 
                                                               (forall ((x267 Int)) 
                                                                   (=> 
                                                                       (length s13 x267) 
                                                                       (= x266 (- i8 x267)))) 
                                                               (MS x266 x261 s23))))))))))) 
                       (forall ((x268 Int) (x269 A)) 
                           (= 
                               (MS x268 x269 x214) 
                               (MS x268 x269 x215))))) 
               (forall ((x270 PZA) (x271 PZA)) 
                   (=> 
                       (and 
                           (exists ((s9 PZA)) 
                               (and 
                                   (exists ((n19 Int)) 
                                       (and 
                                           (<= 0 n19) 
                                           (forall ((x272 Int) (x273 A)) 
                                               (=> 
                                                   (MS x272 x273 s9) 
                                                   (and 
                                                       (<= 1 x272) 
                                                       (<= x272 n19)))) 
                                           (forall ((x274 Int) (x275 A) (x276 A)) 
                                               (=> 
                                                   (and 
                                                       (MS x274 x275 s9) 
                                                       (MS x274 x276 s9)) 
                                                   (= x275 x276))) 
                                           (forall ((x277 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x277) 
                                                       (<= x277 n19)) 
                                                   (exists ((x278 A)) 
                                                       (MS x277 x278 s9)))))) 
                                   (forall ((x279 Int) (x280 A)) 
                                       (= 
                                           (MS x279 x280 x270) 
                                           (MS x279 x280 s9))))) 
                           (exists ((s14 PZA)) 
                               (and 
                                   (exists ((n20 Int)) 
                                       (and 
                                           (<= 0 n20) 
                                           (forall ((x281 Int) (x282 A)) 
                                               (=> 
                                                   (MS x281 x282 s14) 
                                                   (and 
                                                       (<= 1 x281) 
                                                       (<= x281 n20)))) 
                                           (forall ((x283 Int) (x284 A) (x285 A)) 
                                               (=> 
                                                   (and 
                                                       (MS x283 x284 s14) 
                                                       (MS x283 x285 s14)) 
                                                   (= x284 x285))) 
                                           (forall ((x286 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x286) 
                                                       (<= x286 n20)) 
                                                   (exists ((x287 A)) 
                                                       (MS x286 x287 s14)))))) 
                                   (forall ((x288 Int) (x289 A)) 
                                       (= 
                                           (MS x288 x289 x271) 
                                           (MS x288 x289 s14)))))) 
                       (exists ((x290 PZA) (s15 PZA) (s24 PZA)) 
                           (and 
                               (exists ((n21 Int)) 
                                   (and 
                                       (<= 0 n21) 
                                       (forall ((x291 Int) (x292 A)) 
                                           (=> 
                                               (MS x291 x292 s15) 
                                               (and 
                                                   (<= 1 x291) 
                                                   (<= x291 n21)))) 
                                       (forall ((x293 Int) (x294 A) (x295 A)) 
                                           (=> 
                                               (and 
                                                   (MS x293 x294 s15) 
                                                   (MS x293 x295 s15)) 
                                               (= x294 x295))) 
                                       (forall ((x296 Int)) 
                                           (=> 
                                               (and 
                                                   (<= 1 x296) 
                                                   (<= x296 n21)) 
                                               (exists ((x297 A)) 
                                                   (MS x296 x297 s15)))))) 
                               (exists ((n22 Int)) 
                                   (and 
                                       (<= 0 n22) 
                                       (forall ((x298 Int) (x299 A)) 
                                           (=> 
                                               (MS x298 x299 s24) 
                                               (and 
                                                   (<= 1 x298) 
                                                   (<= x298 n22)))) 
                                       (forall ((x300 Int) (x301 A) (x302 A)) 
                                           (=> 
                                               (and 
                                                   (MS x300 x301 s24) 
                                                   (MS x300 x302 s24)) 
                                               (= x301 x302))) 
                                       (forall ((x303 Int)) 
                                           (=> 
                                               (and 
                                                   (<= 1 x303) 
                                                   (<= x303 n22)) 
                                               (exists ((x304 A)) 
                                                   (MS x303 x304 s24)))))) 
                               (forall ((x305 Int) (x306 A)) 
                                   (= 
                                       (MS x305 x306 x270) 
                                       (MS x305 x306 s15))) 
                               (forall ((x307 Int) (x308 A)) 
                                   (= 
                                       (MS x307 x308 x271) 
                                       (MS x307 x308 s24))) 
                               (forall ((x309 Int) (x310 A)) 
                                   (= 
                                       (MS x309 x310 x290) 
                                       (or 
                                           (exists ((i9 Int)) 
                                               (and 
                                                   (<= 1 i9) 
                                                   (forall ((x311 Int)) 
                                                       (=> 
                                                           (length s15 x311) 
                                                           (<= i9 x311))) 
                                                   (= x309 i9) 
                                                   (MS i9 x310 s15))) 
                                           (exists ((i10 Int)) 
                                               (and 
                                                   (forall ((x312 Int)) 
                                                       (=> 
                                                           (length s15 x312) 
                                                           (<= (+ x312 1) i10))) 
                                                   (forall ((x313 Int) (x314 Int)) 
                                                       (=> 
                                                           (and 
                                                               (length s15 x314) 
                                                               (length s24 x313)) 
                                                           (<= i10 (+ x314 x313)))) 
                                                   (= x309 i10) 
                                                   (exists ((x315 Int)) 
                                                       (and 
                                                           (forall ((x316 Int)) 
                                                               (=> 
                                                                   (length s15 x316) 
                                                                   (= x315 (- i10 x316)))) 
                                                           (MS x315 x310 s24)))))))))))))
         :named hyp13))
(assert (! (forall ((s16 PZA) (s25 PZA)) 
               (=> 
                   (and 
                       (exists ((n23 Int)) 
                           (and 
                               (<= 0 n23) 
                               (forall ((x317 Int) (x318 A)) 
                                   (=> 
                                       (MS x317 x318 s16) 
                                       (and 
                                           (<= 1 x317) 
                                           (<= x317 n23)))) 
                               (forall ((x319 Int) (x320 A) (x321 A)) 
                                   (=> 
                                       (and 
                                           (MS x319 x320 s16) 
                                           (MS x319 x321 s16)) 
                                       (= x320 x321))) 
                               (forall ((x322 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x322) 
                                           (<= x322 n23)) 
                                       (exists ((x323 A)) 
                                           (MS x322 x323 s16)))))) 
                       (exists ((n24 Int)) 
                           (and 
                               (<= 0 n24) 
                               (forall ((x324 Int) (x325 A)) 
                                   (=> 
                                       (MS x324 x325 s25) 
                                       (and 
                                           (<= 1 x324) 
                                           (<= x324 n24)))) 
                               (forall ((x326 Int) (x327 A) (x328 A)) 
                                   (=> 
                                       (and 
                                           (MS x326 x327 s25) 
                                           (MS x326 x328 s25)) 
                                       (= x327 x328))) 
                               (forall ((x329 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x329) 
                                           (<= x329 n24)) 
                                       (exists ((x330 A)) 
                                           (MS x329 x330 s25))))))) 
                   (exists ((x331 PZA) (x332 Int)) 
                       (and 
                           (forall ((x333 Int) (x334 A)) 
                               (= 
                                   (MS x333 x334 x331) 
                                   (or 
                                       (exists ((i11 Int)) 
                                           (and 
                                               (<= 1 i11) 
                                               (forall ((x335 Int)) 
                                                   (=> 
                                                       (length s16 x335) 
                                                       (<= i11 x335))) 
                                               (= x333 i11) 
                                               (MS i11 x334 s16))) 
                                       (exists ((i12 Int)) 
                                           (and 
                                               (forall ((x336 Int)) 
                                                   (=> 
                                                       (length s16 x336) 
                                                       (<= (+ x336 1) i12))) 
                                               (forall ((x337 Int) (x338 Int)) 
                                                   (=> 
                                                       (and 
                                                           (length s16 x338) 
                                                           (length s25 x337)) 
                                                       (<= i12 (+ x338 x337)))) 
                                               (= x333 i12) 
                                               (exists ((x339 Int)) 
                                                   (and 
                                                       (forall ((x340 Int)) 
                                                           (=> 
                                                               (length s16 x340) 
                                                               (= x339 (- i12 x340)))) 
                                                       (MS x339 x334 s25)))))))) 
                           (forall ((x341 Int) (x342 Int)) 
                               (=> 
                                   (and 
                                       (length s16 x342) 
                                       (length s25 x341)) 
                                   (= x332 (+ x342 x341)))) 
                           (length x331 x332)))))
         :named hyp14))
(assert (! (forall ((s17 PZA) (s26 PZA)) 
               (=> 
                   (and 
                       (exists ((n25 Int)) 
                           (and 
                               (<= 0 n25) 
                               (forall ((x343 Int) (x344 A)) 
                                   (=> 
                                       (MS x343 x344 s17) 
                                       (and 
                                           (<= 1 x343) 
                                           (<= x343 n25)))) 
                               (forall ((x345 Int) (x346 A) (x347 A)) 
                                   (=> 
                                       (and 
                                           (MS x345 x346 s17) 
                                           (MS x345 x347 s17)) 
                                       (= x346 x347))) 
                               (forall ((x348 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x348) 
                                           (<= x348 n25)) 
                                       (exists ((x349 A)) 
                                           (MS x348 x349 s17)))))) 
                       (exists ((n26 Int)) 
                           (and 
                               (<= 0 n26) 
                               (forall ((x350 Int) (x351 A)) 
                                   (=> 
                                       (MS x350 x351 s26) 
                                       (and 
                                           (<= 1 x350) 
                                           (<= x350 n26)))) 
                               (forall ((x352 Int) (x353 A) (x354 A)) 
                                   (=> 
                                       (and 
                                           (MS x352 x353 s26) 
                                           (MS x352 x354 s26)) 
                                       (= x353 x354))) 
                               (forall ((x355 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x355) 
                                           (<= x355 n26)) 
                                       (exists ((x356 A)) 
                                           (MS x355 x356 s26))))))) 
                   (forall ((x357 Int)) 
                       (= 
                           (or 
                               (exists ((x358 A)) 
                                   (exists ((i13 Int)) 
                                       (and 
                                           (<= 1 i13) 
                                           (forall ((x359 Int)) 
                                               (=> 
                                                   (length s17 x359) 
                                                   (<= i13 x359))) 
                                           (= x357 i13) 
                                           (MS i13 x358 s17)))) 
                               (exists ((x360 A)) 
                                   (exists ((i14 Int)) 
                                       (and 
                                           (forall ((x361 Int)) 
                                               (=> 
                                                   (length s17 x361) 
                                                   (<= (+ x361 1) i14))) 
                                           (forall ((x362 Int) (x363 Int)) 
                                               (=> 
                                                   (and 
                                                       (length s17 x363) 
                                                       (length s26 x362)) 
                                                   (<= i14 (+ x363 x362)))) 
                                           (= x357 i14) 
                                           (exists ((x364 Int)) 
                                               (and 
                                                   (forall ((x365 Int)) 
                                                       (=> 
                                                           (length s17 x365) 
                                                           (= x364 (- i14 x365)))) 
                                                   (MS x364 x360 s26))))))) 
                           (and 
                               (<= 1 x357) 
                               (forall ((x366 Int) (x367 Int)) 
                                   (=> 
                                       (and 
                                           (length s17 x367) 
                                           (length s26 x366)) 
                                       (<= x357 (+ x367 x366)))))))))
         :named hyp15))
(assert (! (forall ((s18 PZA) (s27 PZA)) 
               (=> 
                   (and 
                       (exists ((n27 Int)) 
                           (and 
                               (<= 0 n27) 
                               (forall ((x368 Int) (x369 A)) 
                                   (=> 
                                       (MS x368 x369 s18) 
                                       (and 
                                           (<= 1 x368) 
                                           (<= x368 n27)))) 
                               (forall ((x370 Int) (x371 A) (x372 A)) 
                                   (=> 
                                       (and 
                                           (MS x370 x371 s18) 
                                           (MS x370 x372 s18)) 
                                       (= x371 x372))) 
                               (forall ((x373 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x373) 
                                           (<= x373 n27)) 
                                       (exists ((x374 A)) 
                                           (MS x373 x374 s18)))))) 
                       (exists ((n28 Int)) 
                           (and 
                               (<= 0 n28) 
                               (forall ((x375 Int) (x376 A)) 
                                   (=> 
                                       (MS x375 x376 s27) 
                                       (and 
                                           (<= 1 x375) 
                                           (<= x375 n28)))) 
                               (forall ((x377 Int) (x378 A) (x379 A)) 
                                   (=> 
                                       (and 
                                           (MS x377 x378 s27) 
                                           (MS x377 x379 s27)) 
                                       (= x378 x379))) 
                               (forall ((x380 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x380) 
                                           (<= x380 n28)) 
                                       (exists ((x381 A)) 
                                           (MS x380 x381 s27))))))) 
                   (forall ((x382 A)) 
                       (= 
                           (or 
                               (exists ((x383 Int)) 
                                   (exists ((i15 Int)) 
                                       (and 
                                           (<= 1 i15) 
                                           (forall ((x384 Int)) 
                                               (=> 
                                                   (length s18 x384) 
                                                   (<= i15 x384))) 
                                           (= x383 i15) 
                                           (MS i15 x382 s18)))) 
                               (exists ((x385 Int)) 
                                   (exists ((i16 Int)) 
                                       (and 
                                           (forall ((x386 Int)) 
                                               (=> 
                                                   (length s18 x386) 
                                                   (<= (+ x386 1) i16))) 
                                           (forall ((x387 Int) (x388 Int)) 
                                               (=> 
                                                   (and 
                                                       (length s18 x388) 
                                                       (length s27 x387)) 
                                                   (<= i16 (+ x388 x387)))) 
                                           (= x385 i16) 
                                           (exists ((x389 Int)) 
                                               (and 
                                                   (forall ((x390 Int)) 
                                                       (=> 
                                                           (length s18 x390) 
                                                           (= x389 (- i16 x390)))) 
                                                   (MS x389 x382 s27))))))) 
                           (or 
                               (exists ((x391 Int)) 
                                   (MS x391 x382 s18)) 
                               (exists ((x392 Int)) 
                                   (MS x392 x382 s27)))))))
         :named hyp16))
(assert (! (forall ((s19 PZA) (s28 PZA) (i17 Int)) 
               (=> 
                   (and 
                       (exists ((n29 Int)) 
                           (and 
                               (<= 0 n29) 
                               (forall ((x393 Int) (x394 A)) 
                                   (=> 
                                       (MS x393 x394 s19) 
                                       (and 
                                           (<= 1 x393) 
                                           (<= x393 n29)))) 
                               (forall ((x395 Int) (x396 A) (x397 A)) 
                                   (=> 
                                       (and 
                                           (MS x395 x396 s19) 
                                           (MS x395 x397 s19)) 
                                       (= x396 x397))) 
                               (forall ((x398 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x398) 
                                           (<= x398 n29)) 
                                       (exists ((x399 A)) 
                                           (MS x398 x399 s19)))))) 
                       (exists ((n30 Int)) 
                           (and 
                               (<= 0 n30) 
                               (forall ((x400 Int) (x401 A)) 
                                   (=> 
                                       (MS x400 x401 s28) 
                                       (and 
                                           (<= 1 x400) 
                                           (<= x400 n30)))) 
                               (forall ((x402 Int) (x403 A) (x404 A)) 
                                   (=> 
                                       (and 
                                           (MS x402 x403 s28) 
                                           (MS x402 x404 s28)) 
                                       (= x403 x404))) 
                               (forall ((x405 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x405) 
                                           (<= x405 n30)) 
                                       (exists ((x406 A)) 
                                           (MS x405 x406 s28)))))) 
                       (<= 1 i17) 
                       (forall ((x407 Int)) 
                           (=> 
                               (length s19 x407) 
                               (<= i17 x407)))) 
                   (or 
                       (exists ((i18 Int)) 
                           (and 
                               (<= 1 i18) 
                               (forall ((x408 Int)) 
                                   (=> 
                                       (length s19 x408) 
                                       (<= i18 x408))) 
                               (= i17 i18) 
                               (exists ((x409 A)) 
                                   (and 
                                       (MS i18 x409 s19) 
                                       (MS i17 x409 s19))))) 
                       (exists ((i19 Int)) 
                           (and 
                               (forall ((x410 Int)) 
                                   (=> 
                                       (length s19 x410) 
                                       (<= (+ x410 1) i19))) 
                               (forall ((x411 Int) (x412 Int)) 
                                   (=> 
                                       (and 
                                           (length s19 x412) 
                                           (length s28 x411)) 
                                       (<= i19 (+ x412 x411)))) 
                               (= i17 i19) 
                               (exists ((x413 A)) 
                                   (and 
                                       (exists ((x414 Int)) 
                                           (and 
                                               (forall ((x415 Int)) 
                                                   (=> 
                                                       (length s19 x415) 
                                                       (= x414 (- i19 x415)))) 
                                               (MS x414 x413 s28))) 
                                       (MS i17 x413 s19))))))))
         :named hyp17))
(assert (! (forall ((s110 PZA) (s29 PZA) (i20 Int)) 
               (=> 
                   (and 
                       (exists ((n31 Int)) 
                           (and 
                               (<= 0 n31) 
                               (forall ((x416 Int) (x417 A)) 
                                   (=> 
                                       (MS x416 x417 s110) 
                                       (and 
                                           (<= 1 x416) 
                                           (<= x416 n31)))) 
                               (forall ((x418 Int) (x419 A) (x420 A)) 
                                   (=> 
                                       (and 
                                           (MS x418 x419 s110) 
                                           (MS x418 x420 s110)) 
                                       (= x419 x420))) 
                               (forall ((x421 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x421) 
                                           (<= x421 n31)) 
                                       (exists ((x422 A)) 
                                           (MS x421 x422 s110)))))) 
                       (exists ((n32 Int)) 
                           (and 
                               (<= 0 n32) 
                               (forall ((x423 Int) (x424 A)) 
                                   (=> 
                                       (MS x423 x424 s29) 
                                       (and 
                                           (<= 1 x423) 
                                           (<= x423 n32)))) 
                               (forall ((x425 Int) (x426 A) (x427 A)) 
                                   (=> 
                                       (and 
                                           (MS x425 x426 s29) 
                                           (MS x425 x427 s29)) 
                                       (= x426 x427))) 
                               (forall ((x428 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x428) 
                                           (<= x428 n32)) 
                                       (exists ((x429 A)) 
                                           (MS x428 x429 s29)))))) 
                       (forall ((x430 Int)) 
                           (=> 
                               (length s110 x430) 
                               (<= (+ x430 1) i20))) 
                       (forall ((x431 Int) (x432 Int)) 
                           (=> 
                               (and 
                                   (length s110 x432) 
                                   (length s29 x431)) 
                               (<= i20 (+ x432 x431))))) 
                   (or 
                       (exists ((i21 Int)) 
                           (and 
                               (<= 1 i21) 
                               (forall ((x433 Int)) 
                                   (=> 
                                       (length s110 x433) 
                                       (<= i21 x433))) 
                               (= i20 i21) 
                               (exists ((x434 Int) (x435 A)) 
                                   (and 
                                       (forall ((x436 Int)) 
                                           (=> 
                                               (length s110 x436) 
                                               (= x434 (- i20 x436)))) 
                                       (MS i21 x435 s110) 
                                       (MS x434 x435 s29))))) 
                       (exists ((i22 Int)) 
                           (and 
                               (forall ((x437 Int)) 
                                   (=> 
                                       (length s110 x437) 
                                       (<= (+ x437 1) i22))) 
                               (forall ((x438 Int) (x439 Int)) 
                                   (=> 
                                       (and 
                                           (length s110 x439) 
                                           (length s29 x438)) 
                                       (<= i22 (+ x439 x438)))) 
                               (= i20 i22) 
                               (exists ((x440 Int) (x441 A)) 
                                   (and 
                                       (forall ((x442 Int)) 
                                           (=> 
                                               (length s110 x442) 
                                               (= x440 (- i20 x442)))) 
                                       (exists ((x443 Int)) 
                                           (and 
                                               (forall ((x444 Int)) 
                                                   (=> 
                                                       (length s110 x444) 
                                                       (= x443 (- i22 x444)))) 
                                               (MS x443 x441 s29))) 
                                       (MS x440 x441 s29))))))))
         :named hyp18))
(assert (! (forall ((s111 PZA) (s210 PZA) (b PA)) 
               (=> 
                   (and 
                       (exists ((n33 Int)) 
                           (and 
                               (<= 0 n33) 
                               (forall ((x445 Int) (x446 A)) 
                                   (=> 
                                       (MS x445 x446 s111) 
                                       (and 
                                           (<= 1 x445) 
                                           (<= x445 n33)))) 
                               (forall ((x447 Int) (x448 A) (x449 A)) 
                                   (=> 
                                       (and 
                                           (MS x447 x448 s111) 
                                           (MS x447 x449 s111)) 
                                       (= x448 x449))) 
                               (forall ((x450 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x450) 
                                           (<= x450 n33)) 
                                       (exists ((x451 A)) 
                                           (MS x450 x451 s111)))))) 
                       (exists ((n34 Int)) 
                           (and 
                               (<= 0 n34) 
                               (forall ((x452 Int) (x453 A)) 
                                   (=> 
                                       (MS x452 x453 s210) 
                                       (and 
                                           (<= 1 x452) 
                                           (<= x452 n34)))) 
                               (forall ((x454 Int) (x455 A) (x456 A)) 
                                   (=> 
                                       (and 
                                           (MS x454 x455 s210) 
                                           (MS x454 x456 s210)) 
                                       (= x455 x456))) 
                               (forall ((x457 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x457) 
                                           (<= x457 n34)) 
                                       (exists ((x458 A)) 
                                           (MS x457 x458 s210)))))) 
                       (forall ((x459 A)) 
                           (=> 
                               (exists ((x460 Int)) 
                                   (MS x460 x459 s111)) 
                               (MS1 x459 b))) 
                       (forall ((x461 A)) 
                           (=> 
                               (exists ((x462 Int)) 
                                   (MS x462 x461 s210)) 
                               (MS1 x461 b)))) 
                   (and 
                       (forall ((x463 Int) (x464 A)) 
                           (=> 
                               (or 
                                   (exists ((i23 Int)) 
                                       (and 
                                           (<= 1 i23) 
                                           (forall ((x465 Int)) 
                                               (=> 
                                                   (length s111 x465) 
                                                   (<= i23 x465))) 
                                           (= x463 i23) 
                                           (MS i23 x464 s111))) 
                                   (exists ((i24 Int)) 
                                       (and 
                                           (forall ((x466 Int)) 
                                               (=> 
                                                   (length s111 x466) 
                                                   (<= (+ x466 1) i24))) 
                                           (forall ((x467 Int) (x468 Int)) 
                                               (=> 
                                                   (and 
                                                       (length s111 x468) 
                                                       (length s210 x467)) 
                                                   (<= i24 (+ x468 x467)))) 
                                           (= x463 i24) 
                                           (exists ((x469 Int)) 
                                               (and 
                                                   (forall ((x470 Int)) 
                                                       (=> 
                                                           (length s111 x470) 
                                                           (= x469 (- i24 x470)))) 
                                                   (MS x469 x464 s210)))))) 
                               (and 
                                   (<= 1 x463) 
                                   (forall ((x471 Int) (x472 Int)) 
                                       (=> 
                                           (and 
                                               (length s111 x472) 
                                               (length s210 x471)) 
                                           (<= x463 (+ x472 x471)))) 
                                   (MS1 x464 b)))) 
                       (forall ((x473 Int) (x474 A) (x475 A)) 
                           (=> 
                               (and 
                                   (or 
                                       (exists ((i25 Int)) 
                                           (and 
                                               (<= 1 i25) 
                                               (forall ((x476 Int)) 
                                                   (=> 
                                                       (length s111 x476) 
                                                       (<= i25 x476))) 
                                               (= x473 i25) 
                                               (MS i25 x474 s111))) 
                                       (exists ((i26 Int)) 
                                           (and 
                                               (forall ((x477 Int)) 
                                                   (=> 
                                                       (length s111 x477) 
                                                       (<= (+ x477 1) i26))) 
                                               (forall ((x478 Int) (x479 Int)) 
                                                   (=> 
                                                       (and 
                                                           (length s111 x479) 
                                                           (length s210 x478)) 
                                                       (<= i26 (+ x479 x478)))) 
                                               (= x473 i26) 
                                               (exists ((x480 Int)) 
                                                   (and 
                                                       (forall ((x481 Int)) 
                                                           (=> 
                                                               (length s111 x481) 
                                                               (= x480 (- i26 x481)))) 
                                                       (MS x480 x474 s210)))))) 
                                   (or 
                                       (exists ((i27 Int)) 
                                           (and 
                                               (<= 1 i27) 
                                               (forall ((x482 Int)) 
                                                   (=> 
                                                       (length s111 x482) 
                                                       (<= i27 x482))) 
                                               (= x473 i27) 
                                               (MS i27 x475 s111))) 
                                       (exists ((i28 Int)) 
                                           (and 
                                               (forall ((x483 Int)) 
                                                   (=> 
                                                       (length s111 x483) 
                                                       (<= (+ x483 1) i28))) 
                                               (forall ((x484 Int) (x485 Int)) 
                                                   (=> 
                                                       (and 
                                                           (length s111 x485) 
                                                           (length s210 x484)) 
                                                       (<= i28 (+ x485 x484)))) 
                                               (= x473 i28) 
                                               (exists ((x486 Int)) 
                                                   (and 
                                                       (forall ((x487 Int)) 
                                                           (=> 
                                                               (length s111 x487) 
                                                               (= x486 (- i28 x487)))) 
                                                       (MS x486 x475 s210))))))) 
                               (= x474 x475))) 
                       (forall ((x488 Int)) 
                           (=> 
                               (and 
                                   (<= 1 x488) 
                                   (forall ((x489 Int) (x490 Int)) 
                                       (=> 
                                           (and 
                                               (length s111 x490) 
                                               (length s210 x489)) 
                                           (<= x488 (+ x490 x489))))) 
                               (or 
                                   (exists ((x491 A)) 
                                       (exists ((i29 Int)) 
                                           (and 
                                               (<= 1 i29) 
                                               (forall ((x492 Int)) 
                                                   (=> 
                                                       (length s111 x492) 
                                                       (<= i29 x492))) 
                                               (= x488 i29) 
                                               (MS i29 x491 s111)))) 
                                   (exists ((x493 A)) 
                                       (exists ((i30 Int)) 
                                           (and 
                                               (forall ((x494 Int)) 
                                                   (=> 
                                                       (length s111 x494) 
                                                       (<= (+ x494 1) i30))) 
                                               (forall ((x495 Int) (x496 Int)) 
                                                   (=> 
                                                       (and 
                                                           (length s111 x496) 
                                                           (length s210 x495)) 
                                                       (<= i30 (+ x496 x495)))) 
                                               (= x488 i30) 
                                               (exists ((x497 Int)) 
                                                   (and 
                                                       (forall ((x498 Int)) 
                                                           (=> 
                                                               (length s111 x498) 
                                                               (= x497 (- i30 x498)))) 
                                                       (MS x497 x493 s210))))))))))))
         :named hyp19))
(assert (! (and 
               (forall ((x499 PZA) (x500 PZA)) 
                   (=> 
                       (exists ((s30 PZA)) 
                           (and 
                               (exists ((n35 Int)) 
                                   (and 
                                       (<= 0 n35) 
                                       (forall ((x501 Int) (x502 A)) 
                                           (=> 
                                               (MS x501 x502 s30) 
                                               (and 
                                                   (<= 1 x501) 
                                                   (<= x501 n35)))) 
                                       (forall ((x503 Int) (x504 A) (x505 A)) 
                                           (=> 
                                               (and 
                                                   (MS x503 x504 s30) 
                                                   (MS x503 x505 s30)) 
                                               (= x504 x505))) 
                                       (forall ((x506 Int)) 
                                           (=> 
                                               (and 
                                                   (<= 1 x506) 
                                                   (<= x506 n35)) 
                                               (exists ((x507 A)) 
                                                   (MS x506 x507 s30)))))) 
                               (forall ((x508 Int) (x509 A)) 
                                   (= 
                                       (MS x508 x509 x499) 
                                       (MS x508 x509 s30))) 
                               (forall ((x510 Int) (x511 A)) 
                                   (= 
                                       (MS x510 x511 x500) 
                                       (exists ((i31 Int)) 
                                           (and 
                                               (<= 1 i31) 
                                               (forall ((x512 Int)) 
                                                   (=> 
                                                       (length s30 x512) 
                                                       (<= i31 x512))) 
                                               (= x510 i31) 
                                               (exists ((x513 Int)) 
                                                   (and 
                                                       (forall ((x514 Int)) 
                                                           (=> 
                                                               (length s30 x514) 
                                                               (= x513 (+ (- x514 i31) 1)))) 
                                                       (MS x513 x511 s30))))))))) 
                       (and 
                           (exists ((s31 PZA)) 
                               (and 
                                   (exists ((n36 Int)) 
                                       (and 
                                           (<= 0 n36) 
                                           (forall ((x515 Int) (x516 A)) 
                                               (=> 
                                                   (MS x515 x516 s31) 
                                                   (and 
                                                       (<= 1 x515) 
                                                       (<= x515 n36)))) 
                                           (forall ((x517 Int) (x518 A) (x519 A)) 
                                               (=> 
                                                   (and 
                                                       (MS x517 x518 s31) 
                                                       (MS x517 x519 s31)) 
                                                   (= x518 x519))) 
                                           (forall ((x520 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x520) 
                                                       (<= x520 n36)) 
                                                   (exists ((x521 A)) 
                                                       (MS x520 x521 s31)))))) 
                                   (forall ((x522 Int) (x523 A)) 
                                       (= 
                                           (MS x522 x523 x499) 
                                           (MS x522 x523 s31))))) 
                           (exists ((s32 PZA)) 
                               (and 
                                   (exists ((n37 Int)) 
                                       (and 
                                           (<= 0 n37) 
                                           (forall ((x524 Int) (x525 A)) 
                                               (=> 
                                                   (MS x524 x525 s32) 
                                                   (and 
                                                       (<= 1 x524) 
                                                       (<= x524 n37)))) 
                                           (forall ((x526 Int) (x527 A) (x528 A)) 
                                               (=> 
                                                   (and 
                                                       (MS x526 x527 s32) 
                                                       (MS x526 x528 s32)) 
                                                   (= x527 x528))) 
                                           (forall ((x529 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x529) 
                                                       (<= x529 n37)) 
                                                   (exists ((x530 A)) 
                                                       (MS x529 x530 s32)))))) 
                                   (forall ((x531 Int) (x532 A)) 
                                       (= 
                                           (MS x531 x532 x500) 
                                           (MS x531 x532 s32)))))))) 
               (forall ((x533 PZA) (x534 PZA) (x535 PZA)) 
                   (=> 
                       (and 
                           (exists ((s33 PZA)) 
                               (and 
                                   (exists ((n38 Int)) 
                                       (and 
                                           (<= 0 n38) 
                                           (forall ((x536 Int) (x537 A)) 
                                               (=> 
                                                   (MS x536 x537 s33) 
                                                   (and 
                                                       (<= 1 x536) 
                                                       (<= x536 n38)))) 
                                           (forall ((x538 Int) (x539 A) (x540 A)) 
                                               (=> 
                                                   (and 
                                                       (MS x538 x539 s33) 
                                                       (MS x538 x540 s33)) 
                                                   (= x539 x540))) 
                                           (forall ((x541 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x541) 
                                                       (<= x541 n38)) 
                                                   (exists ((x542 A)) 
                                                       (MS x541 x542 s33)))))) 
                                   (forall ((x543 Int) (x544 A)) 
                                       (= 
                                           (MS x543 x544 x533) 
                                           (MS x543 x544 s33))) 
                                   (forall ((x545 Int) (x546 A)) 
                                       (= 
                                           (MS x545 x546 x534) 
                                           (exists ((i32 Int)) 
                                               (and 
                                                   (<= 1 i32) 
                                                   (forall ((x547 Int)) 
                                                       (=> 
                                                           (length s33 x547) 
                                                           (<= i32 x547))) 
                                                   (= x545 i32) 
                                                   (exists ((x548 Int)) 
                                                       (and 
                                                           (forall ((x549 Int)) 
                                                               (=> 
                                                                   (length s33 x549) 
                                                                   (= x548 (+ (- x549 i32) 1)))) 
                                                           (MS x548 x546 s33))))))))) 
                           (exists ((s34 PZA)) 
                               (and 
                                   (exists ((n39 Int)) 
                                       (and 
                                           (<= 0 n39) 
                                           (forall ((x550 Int) (x551 A)) 
                                               (=> 
                                                   (MS x550 x551 s34) 
                                                   (and 
                                                       (<= 1 x550) 
                                                       (<= x550 n39)))) 
                                           (forall ((x552 Int) (x553 A) (x554 A)) 
                                               (=> 
                                                   (and 
                                                       (MS x552 x553 s34) 
                                                       (MS x552 x554 s34)) 
                                                   (= x553 x554))) 
                                           (forall ((x555 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x555) 
                                                       (<= x555 n39)) 
                                                   (exists ((x556 A)) 
                                                       (MS x555 x556 s34)))))) 
                                   (forall ((x557 Int) (x558 A)) 
                                       (= 
                                           (MS x557 x558 x533) 
                                           (MS x557 x558 s34))) 
                                   (forall ((x559 Int) (x560 A)) 
                                       (= 
                                           (MS x559 x560 x535) 
                                           (exists ((i33 Int)) 
                                               (and 
                                                   (<= 1 i33) 
                                                   (forall ((x561 Int)) 
                                                       (=> 
                                                           (length s34 x561) 
                                                           (<= i33 x561))) 
                                                   (= x559 i33) 
                                                   (exists ((x562 Int)) 
                                                       (and 
                                                           (forall ((x563 Int)) 
                                                               (=> 
                                                                   (length s34 x563) 
                                                                   (= x562 (+ (- x563 i33) 1)))) 
                                                           (MS x562 x560 s34)))))))))) 
                       (forall ((x564 Int) (x565 A)) 
                           (= 
                               (MS x564 x565 x534) 
                               (MS x564 x565 x535))))) 
               (forall ((x566 PZA)) 
                   (=> 
                       (exists ((s35 PZA)) 
                           (and 
                               (exists ((n40 Int)) 
                                   (and 
                                       (<= 0 n40) 
                                       (forall ((x567 Int) (x568 A)) 
                                           (=> 
                                               (MS x567 x568 s35) 
                                               (and 
                                                   (<= 1 x567) 
                                                   (<= x567 n40)))) 
                                       (forall ((x569 Int) (x570 A) (x571 A)) 
                                           (=> 
                                               (and 
                                                   (MS x569 x570 s35) 
                                                   (MS x569 x571 s35)) 
                                               (= x570 x571))) 
                                       (forall ((x572 Int)) 
                                           (=> 
                                               (and 
                                                   (<= 1 x572) 
                                                   (<= x572 n40)) 
                                               (exists ((x573 A)) 
                                                   (MS x572 x573 s35)))))) 
                               (forall ((x574 Int) (x575 A)) 
                                   (= 
                                       (MS x574 x575 x566) 
                                       (MS x574 x575 s35))))) 
                       (exists ((x576 PZA) (s36 PZA)) 
                           (and 
                               (exists ((n41 Int)) 
                                   (and 
                                       (<= 0 n41) 
                                       (forall ((x577 Int) (x578 A)) 
                                           (=> 
                                               (MS x577 x578 s36) 
                                               (and 
                                                   (<= 1 x577) 
                                                   (<= x577 n41)))) 
                                       (forall ((x579 Int) (x580 A) (x581 A)) 
                                           (=> 
                                               (and 
                                                   (MS x579 x580 s36) 
                                                   (MS x579 x581 s36)) 
                                               (= x580 x581))) 
                                       (forall ((x582 Int)) 
                                           (=> 
                                               (and 
                                                   (<= 1 x582) 
                                                   (<= x582 n41)) 
                                               (exists ((x583 A)) 
                                                   (MS x582 x583 s36)))))) 
                               (forall ((x584 Int) (x585 A)) 
                                   (= 
                                       (MS x584 x585 x566) 
                                       (MS x584 x585 s36))) 
                               (forall ((x586 Int) (x587 A)) 
                                   (= 
                                       (MS x586 x587 x576) 
                                       (exists ((i34 Int)) 
                                           (and 
                                               (<= 1 i34) 
                                               (forall ((x588 Int)) 
                                                   (=> 
                                                       (length s36 x588) 
                                                       (<= i34 x588))) 
                                               (= x586 i34) 
                                               (exists ((x589 Int)) 
                                                   (and 
                                                       (forall ((x590 Int)) 
                                                           (=> 
                                                               (length s36 x590) 
                                                               (= x589 (+ (- x590 i34) 1)))) 
                                                       (MS x589 x587 s36))))))))))))
         :named hyp20))
(assert (! (forall ((s37 PZA)) 
               (=> 
                   (exists ((n42 Int)) 
                       (and 
                           (<= 0 n42) 
                           (forall ((x591 Int) (x592 A)) 
                               (=> 
                                   (MS x591 x592 s37) 
                                   (and 
                                       (<= 1 x591) 
                                       (<= x591 n42)))) 
                           (forall ((x593 Int) (x594 A) (x595 A)) 
                               (=> 
                                   (and 
                                       (MS x593 x594 s37) 
                                       (MS x593 x595 s37)) 
                                   (= x594 x595))) 
                           (forall ((x596 Int)) 
                               (=> 
                                   (and 
                                       (<= 1 x596) 
                                       (<= x596 n42)) 
                                   (exists ((x597 A)) 
                                       (MS x596 x597 s37)))))) 
                   (exists ((x598 PZA) (x599 Int)) 
                       (and 
                           (forall ((x600 Int) (x601 A)) 
                               (= 
                                   (MS x600 x601 x598) 
                                   (exists ((i35 Int)) 
                                       (and 
                                           (<= 1 i35) 
                                           (forall ((x602 Int)) 
                                               (=> 
                                                   (length s37 x602) 
                                                   (<= i35 x602))) 
                                           (= x600 i35) 
                                           (exists ((x603 Int)) 
                                               (and 
                                                   (forall ((x604 Int)) 
                                                       (=> 
                                                           (length s37 x604) 
                                                           (= x603 (+ (- x604 i35) 1)))) 
                                                   (MS x603 x601 s37))))))) 
                           (length s37 x599) 
                           (length x598 x599)))))
         :named hyp21))
(assert (! (forall ((s38 PZA)) 
               (=> 
                   (exists ((n43 Int)) 
                       (and 
                           (<= 0 n43) 
                           (forall ((x605 Int) (x606 A)) 
                               (=> 
                                   (MS x605 x606 s38) 
                                   (and 
                                       (<= 1 x605) 
                                       (<= x605 n43)))) 
                           (forall ((x607 Int) (x608 A) (x609 A)) 
                               (=> 
                                   (and 
                                       (MS x607 x608 s38) 
                                       (MS x607 x609 s38)) 
                                   (= x608 x609))) 
                           (forall ((x610 Int)) 
                               (=> 
                                   (and 
                                       (<= 1 x610) 
                                       (<= x610 n43)) 
                                   (exists ((x611 A)) 
                                       (MS x610 x611 s38)))))) 
                   (forall ((x612 A)) 
                       (= 
                           (exists ((i36 Int)) 
                               (and 
                                   (<= 1 i36) 
                                   (forall ((x613 Int)) 
                                       (=> 
                                           (length s38 x613) 
                                           (<= i36 x613))) 
                                   (exists ((x614 Int)) 
                                       (and 
                                           (forall ((x615 Int)) 
                                               (=> 
                                                   (length s38 x615) 
                                                   (= x614 (+ (- x615 i36) 1)))) 
                                           (MS x614 x612 s38))))) 
                           (exists ((x616 Int)) 
                               (MS x616 x612 s38))))))
         :named hyp22))
(assert (! (forall ((s39 PZA)) 
               (=> 
                   (exists ((n44 Int)) 
                       (and 
                           (<= 0 n44) 
                           (forall ((x617 Int) (x618 A)) 
                               (=> 
                                   (MS x617 x618 s39) 
                                   (and 
                                       (<= 1 x617) 
                                       (<= x617 n44)))) 
                           (forall ((x619 Int) (x620 A) (x621 A)) 
                               (=> 
                                   (and 
                                       (MS x619 x620 s39) 
                                       (MS x619 x621 s39)) 
                                   (= x620 x621))) 
                           (forall ((x622 Int)) 
                               (=> 
                                   (and 
                                       (<= 1 x622) 
                                       (<= x622 n44)) 
                                   (exists ((x623 A)) 
                                       (MS x622 x623 s39)))))) 
                   (forall ((x624 Int) (x625 A)) 
                       (= 
                           (exists ((i37 Int)) 
                               (and 
                                   (<= 1 i37) 
                                   (forall ((x626 Int)) 
                                       (=> 
                                           (exists ((x627 PZA)) 
                                               (and 
                                                   (forall ((x628 Int) (x629 A)) 
                                                       (= 
                                                           (MS x628 x629 x627) 
                                                           (exists ((i38 Int)) 
                                                               (and 
                                                                   (<= 1 i38) 
                                                                   (forall ((x630 Int)) 
                                                                       (=> 
                                                                           (length s39 x630) 
                                                                           (<= i38 x630))) 
                                                                   (= x628 i38) 
                                                                   (exists ((x631 Int)) 
                                                                       (and 
                                                                           (forall ((x632 Int)) 
                                                                               (=> 
                                                                                   (length s39 x632) 
                                                                                   (= x631 (+ (- x632 i38) 1)))) 
                                                                           (MS x631 x629 s39))))))) 
                                                   (length x627 x626))) 
                                           (<= i37 x626))) 
                                   (= x624 i37) 
                                   (exists ((x633 Int)) 
                                       (and 
                                           (forall ((x634 Int) (x635 Int)) 
                                               (=> 
                                                   (and 
                                                       (length s39 x635) 
                                                       (exists ((x636 PZA)) 
                                                           (and 
                                                               (forall ((x637 Int) (x638 A)) 
                                                                   (= 
                                                                       (MS x637 x638 x636) 
                                                                       (exists ((i39 Int)) 
                                                                           (and 
                                                                               (<= 1 i39) 
                                                                               (forall ((x639 Int)) 
                                                                                   (=> 
                                                                                       (length s39 x639) 
                                                                                       (<= i39 x639))) 
                                                                               (= x637 i39) 
                                                                               (exists ((x640 Int)) 
                                                                                   (and 
                                                                                       (forall ((x641 Int)) 
                                                                                           (=> 
                                                                                               (length s39 x641) 
                                                                                               (= x640 (+ (- x641 i39) 1)))) 
                                                                                       (MS x640 x638 s39))))))) 
                                                               (length x636 x634)))) 
                                                   (= x633 (+ (- x635 (+ (- x634 i37) 1)) 1)))) 
                                           (MS x633 x625 s39))))) 
                           (MS x624 x625 s39)))))
         :named hyp23))
(assert (! (forall ((x642 A) (y3 A)) 
               (=> 
                   (and 
                       (MS1 x642 a) 
                       (MS1 y3 a)) 
                   (exists ((x643 Int)) 
                       (and 
                           (exists ((x644 PZA)) 
                               (and 
                                   (exists ((x645 A) (x646 A)) 
                                       (and 
                                           (= x645 x642) 
                                           (= x646 y3) 
                                           (exists ((x647 A) (y4 A) (p1 PZA)) 
                                               (and 
                                                   (exists ((n45 Int)) 
                                                       (and 
                                                           (<= 0 n45) 
                                                           (forall ((x648 Int) (x649 A)) 
                                                               (=> 
                                                                   (MS x648 x649 p1) 
                                                                   (and 
                                                                       (<= 1 x648) 
                                                                       (<= x648 n45)))) 
                                                           (forall ((x650 Int) (x651 A) (x652 A)) 
                                                               (=> 
                                                                   (and 
                                                                       (MS x650 x651 p1) 
                                                                       (MS x650 x652 p1)) 
                                                                   (= x651 x652))) 
                                                           (forall ((x653 Int)) 
                                                               (=> 
                                                                   (and 
                                                                       (<= 1 x653) 
                                                                       (<= x653 n45)) 
                                                                   (exists ((x654 A)) 
                                                                       (MS x653 x654 p1)))))) 
                                                   (forall ((x655 A)) 
                                                       (=> 
                                                           (exists ((x656 Int)) 
                                                               (MS x656 x655 p1)) 
                                                           (MS1 x655 a))) 
                                                   (forall ((x657 Int)) 
                                                       (=> 
                                                           (length p1 x657) 
                                                           (< 1 x657))) 
                                                   (exists ((x658 Int)) 
                                                       (and 
                                                           (= x658 1) 
                                                           (MS x658 x647 p1))) 
                                                   (exists ((x659 Int)) 
                                                       (and 
                                                           (length p1 x659) 
                                                           (MS x659 y4 p1))) 
                                                   (forall ((i40 Int)) 
                                                       (=> 
                                                           (and 
                                                               (<= 1 i40) 
                                                               (forall ((x660 Int)) 
                                                                   (=> 
                                                                       (length p1 x660) 
                                                                       (<= i40 (- x660 1))))) 
                                                           (exists ((x661 A) (x662 A)) 
                                                               (and 
                                                                   (MS i40 x661 p1) 
                                                                   (exists ((x663 Int)) 
                                                                       (and 
                                                                           (= x663 (+ i40 1)) 
                                                                           (MS x663 x662 p1))) 
                                                                   (MS0 x661 x662 r))))) 
                                                   (= x645 x647) 
                                                   (= x646 y4) 
                                                   (forall ((x664 Int) (x665 A)) 
                                                       (= 
                                                           (MS x664 x665 x644) 
                                                           (MS x664 x665 p1))))))) 
                                   (length x644 x643))) 
                           (forall ((x666 Int)) 
                               (=> 
                                   (exists ((x667 PZA)) 
                                       (and 
                                           (exists ((x668 A) (x669 A)) 
                                               (and 
                                                   (= x668 x642) 
                                                   (= x669 y3) 
                                                   (exists ((x670 A) (y5 A) (p2 PZA)) 
                                                       (and 
                                                           (exists ((n46 Int)) 
                                                               (and 
                                                                   (<= 0 n46) 
                                                                   (forall ((x671 Int) (x672 A)) 
                                                                       (=> 
                                                                           (MS x671 x672 p2) 
                                                                           (and 
                                                                               (<= 1 x671) 
                                                                               (<= x671 n46)))) 
                                                                   (forall ((x673 Int) (x674 A) (x675 A)) 
                                                                       (=> 
                                                                           (and 
                                                                               (MS x673 x674 p2) 
                                                                               (MS x673 x675 p2)) 
                                                                           (= x674 x675))) 
                                                                   (forall ((x676 Int)) 
                                                                       (=> 
                                                                           (and 
                                                                               (<= 1 x676) 
                                                                               (<= x676 n46)) 
                                                                           (exists ((x677 A)) 
                                                                               (MS x676 x677 p2)))))) 
                                                           (forall ((x678 A)) 
                                                               (=> 
                                                                   (exists ((x679 Int)) 
                                                                       (MS x679 x678 p2)) 
                                                                   (MS1 x678 a))) 
                                                           (forall ((x680 Int)) 
                                                               (=> 
                                                                   (length p2 x680) 
                                                                   (< 1 x680))) 
                                                           (exists ((x681 Int)) 
                                                               (and 
                                                                   (= x681 1) 
                                                                   (MS x681 x670 p2))) 
                                                           (exists ((x682 Int)) 
                                                               (and 
                                                                   (length p2 x682) 
                                                                   (MS x682 y5 p2))) 
                                                           (forall ((i41 Int)) 
                                                               (=> 
                                                                   (and 
                                                                       (<= 1 i41) 
                                                                       (forall ((x683 Int)) 
                                                                           (=> 
                                                                               (length p2 x683) 
                                                                               (<= i41 (- x683 1))))) 
                                                                   (exists ((x684 A) (x685 A)) 
                                                                       (and 
                                                                           (MS i41 x684 p2) 
                                                                           (exists ((x686 Int)) 
                                                                               (and 
                                                                                   (= x686 (+ i41 1)) 
                                                                                   (MS x686 x685 p2))) 
                                                                           (MS0 x684 x685 r))))) 
                                                           (= x668 x670) 
                                                           (= x669 y5) 
                                                           (forall ((x687 Int) (x688 A)) 
                                                               (= 
                                                                   (MS x687 x688 x667) 
                                                                   (MS x687 x688 p2))))))) 
                                           (length x667 x666))) 
                                   (<= x643 x666))) 
                           (dist x642 y3 x643)))))
         :named hyp24))
(assert (! (forall ((x689 A) (y6 A)) 
               (=> 
                   (and 
                       (MS1 x689 a) 
                       (MS1 y6 a)) 
                   (forall ((x690 PZA)) 
                       (= 
                           (exists ((x691 A) (x692 A)) 
                               (and 
                                   (= x691 y6) 
                                   (= x692 x689) 
                                   (exists ((x693 A) (y7 A) (p3 PZA)) 
                                       (and 
                                           (exists ((n47 Int)) 
                                               (and 
                                                   (<= 0 n47) 
                                                   (forall ((x694 Int) (x695 A)) 
                                                       (=> 
                                                           (MS x694 x695 p3) 
                                                           (and 
                                                               (<= 1 x694) 
                                                               (<= x694 n47)))) 
                                                   (forall ((x696 Int) (x697 A) (x698 A)) 
                                                       (=> 
                                                           (and 
                                                               (MS x696 x697 p3) 
                                                               (MS x696 x698 p3)) 
                                                           (= x697 x698))) 
                                                   (forall ((x699 Int)) 
                                                       (=> 
                                                           (and 
                                                               (<= 1 x699) 
                                                               (<= x699 n47)) 
                                                           (exists ((x700 A)) 
                                                               (MS x699 x700 p3)))))) 
                                           (forall ((x701 A)) 
                                               (=> 
                                                   (exists ((x702 Int)) 
                                                       (MS x702 x701 p3)) 
                                                   (MS1 x701 a))) 
                                           (forall ((x703 Int)) 
                                               (=> 
                                                   (length p3 x703) 
                                                   (< 1 x703))) 
                                           (exists ((x704 Int)) 
                                               (and 
                                                   (= x704 1) 
                                                   (MS x704 x693 p3))) 
                                           (exists ((x705 Int)) 
                                               (and 
                                                   (length p3 x705) 
                                                   (MS x705 y7 p3))) 
                                           (forall ((i42 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 i42) 
                                                       (forall ((x706 Int)) 
                                                           (=> 
                                                               (length p3 x706) 
                                                               (<= i42 (- x706 1))))) 
                                                   (exists ((x707 A) (x708 A)) 
                                                       (and 
                                                           (MS i42 x707 p3) 
                                                           (exists ((x709 Int)) 
                                                               (and 
                                                                   (= x709 (+ i42 1)) 
                                                                   (MS x709 x708 p3))) 
                                                           (MS0 x707 x708 r))))) 
                                           (= x691 x693) 
                                           (= x692 y7) 
                                           (forall ((x710 Int) (x711 A)) 
                                               (= 
                                                   (MS x710 x711 x690) 
                                                   (MS x710 x711 p3))))))) 
                           (exists ((x712 PZA)) 
                               (and 
                                   (exists ((x713 A) (x714 A)) 
                                       (and 
                                           (= x713 x689) 
                                           (= x714 y6) 
                                           (exists ((x715 A) (y8 A) (p4 PZA)) 
                                               (and 
                                                   (exists ((n48 Int)) 
                                                       (and 
                                                           (<= 0 n48) 
                                                           (forall ((x716 Int) (x717 A)) 
                                                               (=> 
                                                                   (MS x716 x717 p4) 
                                                                   (and 
                                                                       (<= 1 x716) 
                                                                       (<= x716 n48)))) 
                                                           (forall ((x718 Int) (x719 A) (x720 A)) 
                                                               (=> 
                                                                   (and 
                                                                       (MS x718 x719 p4) 
                                                                       (MS x718 x720 p4)) 
                                                                   (= x719 x720))) 
                                                           (forall ((x721 Int)) 
                                                               (=> 
                                                                   (and 
                                                                       (<= 1 x721) 
                                                                       (<= x721 n48)) 
                                                                   (exists ((x722 A)) 
                                                                       (MS x721 x722 p4)))))) 
                                                   (forall ((x723 A)) 
                                                       (=> 
                                                           (exists ((x724 Int)) 
                                                               (MS x724 x723 p4)) 
                                                           (MS1 x723 a))) 
                                                   (forall ((x725 Int)) 
                                                       (=> 
                                                           (length p4 x725) 
                                                           (< 1 x725))) 
                                                   (exists ((x726 Int)) 
                                                       (and 
                                                           (= x726 1) 
                                                           (MS x726 x715 p4))) 
                                                   (exists ((x727 Int)) 
                                                       (and 
                                                           (length p4 x727) 
                                                           (MS x727 y8 p4))) 
                                                   (forall ((i43 Int)) 
                                                       (=> 
                                                           (and 
                                                               (<= 1 i43) 
                                                               (forall ((x728 Int)) 
                                                                   (=> 
                                                                       (length p4 x728) 
                                                                       (<= i43 (- x728 1))))) 
                                                           (exists ((x729 A) (x730 A)) 
                                                               (and 
                                                                   (MS i43 x729 p4) 
                                                                   (exists ((x731 Int)) 
                                                                       (and 
                                                                           (= x731 (+ i43 1)) 
                                                                           (MS x731 x730 p4))) 
                                                                   (MS0 x729 x730 r))))) 
                                                   (= x713 x715) 
                                                   (= x714 y8) 
                                                   (forall ((x732 Int) (x733 A)) 
                                                       (= 
                                                           (MS x732 x733 x712) 
                                                           (MS x732 x733 p4))))))) 
                                   (exists ((s40 PZA)) 
                                       (and 
                                           (exists ((n49 Int)) 
                                               (and 
                                                   (<= 0 n49) 
                                                   (forall ((x734 Int) (x735 A)) 
                                                       (=> 
                                                           (MS x734 x735 s40) 
                                                           (and 
                                                               (<= 1 x734) 
                                                               (<= x734 n49)))) 
                                                   (forall ((x736 Int) (x737 A) (x738 A)) 
                                                       (=> 
                                                           (and 
                                                               (MS x736 x737 s40) 
                                                               (MS x736 x738 s40)) 
                                                           (= x737 x738))) 
                                                   (forall ((x739 Int)) 
                                                       (=> 
                                                           (and 
                                                               (<= 1 x739) 
                                                               (<= x739 n49)) 
                                                           (exists ((x740 A)) 
                                                               (MS x739 x740 s40)))))) 
                                           (forall ((x741 Int) (x742 A)) 
                                               (= 
                                                   (MS x741 x742 x712) 
                                                   (MS x741 x742 s40))) 
                                           (forall ((x743 Int) (x744 A)) 
                                               (= 
                                                   (MS x743 x744 x690) 
                                                   (exists ((i44 Int)) 
                                                       (and 
                                                           (<= 1 i44) 
                                                           (forall ((x745 Int)) 
                                                               (=> 
                                                                   (length s40 x745) 
                                                                   (<= i44 x745))) 
                                                           (= x743 i44) 
                                                           (exists ((x746 Int)) 
                                                               (and 
                                                                   (forall ((x747 Int)) 
                                                                       (=> 
                                                                           (length s40 x747) 
                                                                           (= x746 (+ (- x747 i44) 1)))) 
                                                                   (MS x746 x744 s40)))))))))))))))
         :named hyp25))
(assert (! (forall ((x748 A) (x749 A) (x750 PZA)) 
               (= 
                   (shpath x748 x749 x750) 
                   (exists ((x751 A) (y9 A) (p5 PZA)) 
                       (and 
                           (exists ((n50 Int)) 
                               (and 
                                   (<= 0 n50) 
                                   (forall ((x752 Int) (x753 A)) 
                                       (=> 
                                           (MS x752 x753 p5) 
                                           (and 
                                               (<= 1 x752) 
                                               (<= x752 n50)))) 
                                   (forall ((x754 Int) (x755 A) (x756 A)) 
                                       (=> 
                                           (and 
                                               (MS x754 x755 p5) 
                                               (MS x754 x756 p5)) 
                                           (= x755 x756))) 
                                   (forall ((x757 Int)) 
                                       (=> 
                                           (and 
                                               (<= 1 x757) 
                                               (<= x757 n50)) 
                                           (exists ((x758 A)) 
                                               (MS x757 x758 p5)))))) 
                           (forall ((x759 A)) 
                               (=> 
                                   (exists ((x760 Int)) 
                                       (MS x760 x759 p5)) 
                                   (MS1 x759 a))) 
                           (forall ((x761 Int)) 
                               (=> 
                                   (length p5 x761) 
                                   (< 1 x761))) 
                           (exists ((x762 Int)) 
                               (and 
                                   (= x762 1) 
                                   (MS x762 x751 p5))) 
                           (exists ((x763 Int)) 
                               (and 
                                   (length p5 x763) 
                                   (MS x763 y9 p5))) 
                           (forall ((i45 Int)) 
                               (=> 
                                   (and 
                                       (<= 1 i45) 
                                       (forall ((x764 Int)) 
                                           (=> 
                                               (length p5 x764) 
                                               (<= i45 (- x764 1))))) 
                                   (exists ((x765 A) (x766 A)) 
                                       (and 
                                           (MS i45 x765 p5) 
                                           (exists ((x767 Int)) 
                                               (and 
                                                   (= x767 (+ i45 1)) 
                                                   (MS x767 x766 p5))) 
                                           (MS0 x765 x766 r))))) 
                           (exists ((x768 Int)) 
                               (and 
                                   (length p5 x768) 
                                   (dist x751 y9 x768))) 
                           (= x748 x751) 
                           (= x749 y9) 
                           (forall ((x769 Int) (x770 A)) 
                               (= 
                                   (MS x769 x770 x750) 
                                   (MS x769 x770 p5)))))))
         :named hyp26))
(assert (! (forall ((x771 A) (y10 A) (z A)) 
               (=> 
                   (and 
                       (MS1 x771 a) 
                       (MS1 y10 a) 
                       (MS1 z a) 
                       (not 
                           (= z x771)) 
                       (not 
                           (= z y10)) 
                       (forall ((t A)) 
                           (=> 
                               (and 
                                   (MS1 t a) 
                                   (MS0 z t r)) 
                               (forall ((x772 Int) (x773 Int)) 
                                   (=> 
                                       (and 
                                           (dist x771 t x773) 
                                           (dist x771 z x772)) 
                                       (<= x773 x772)))))) 
                   (exists ((q0 PZA)) 
                       (and 
                           (exists ((n51 Int)) 
                               (and 
                                   (<= 0 n51) 
                                   (forall ((x774 Int) (x775 A)) 
                                       (=> 
                                           (MS x774 x775 q0) 
                                           (and 
                                               (<= 1 x774) 
                                               (<= x774 n51)))) 
                                   (forall ((x776 Int) (x777 A) (x778 A)) 
                                       (=> 
                                           (and 
                                               (MS x776 x777 q0) 
                                               (MS x776 x778 q0)) 
                                           (= x777 x778))) 
                                   (forall ((x779 Int)) 
                                       (=> 
                                           (and 
                                               (<= 1 x779) 
                                               (<= x779 n51)) 
                                           (exists ((x780 A)) 
                                               (MS x779 x780 q0)))))) 
                           (forall ((x781 A)) 
                               (=> 
                                   (exists ((x782 Int)) 
                                       (MS x782 x781 q0)) 
                                   (MS1 x781 a))) 
                           (forall ((x783 Int)) 
                               (=> 
                                   (length q0 x783) 
                                   (< 1 x783))) 
                           (exists ((x784 Int)) 
                               (and 
                                   (= x784 1) 
                                   (MS x784 x771 q0))) 
                           (exists ((x785 Int)) 
                               (and 
                                   (length q0 x785) 
                                   (MS x785 y10 q0))) 
                           (forall ((i46 Int)) 
                               (=> 
                                   (and 
                                       (<= 1 i46) 
                                       (forall ((x786 Int)) 
                                           (=> 
                                               (length q0 x786) 
                                               (<= i46 (- x786 1))))) 
                                   (exists ((x787 A) (x788 A)) 
                                       (and 
                                           (MS i46 x787 q0) 
                                           (exists ((x789 Int)) 
                                               (and 
                                                   (= x789 (+ i46 1)) 
                                                   (MS x789 x788 q0))) 
                                           (MS0 x787 x788 r))))) 
                           (not 
                               (exists ((x790 Int)) 
                                   (MS x790 z q0)))))))
         :named hyp27))
(assert (! (exists ((n52 Int)) 
               (and 
                   (<= 0 n52) 
                   (forall ((x791 Int) (x792 A)) 
                       (=> 
                           (MS x791 x792 q) 
                           (and 
                               (<= 1 x791) 
                               (<= x791 n52)))) 
                   (forall ((x793 Int) (x794 A) (x795 A)) 
                       (=> 
                           (and 
                               (MS x793 x794 q) 
                               (MS x793 x795 q)) 
                           (= x794 x795))) 
                   (forall ((x796 Int)) 
                       (=> 
                           (and 
                               (<= 1 x796) 
                               (<= x796 n52)) 
                           (exists ((x797 A)) 
                               (MS x796 x797 q))))))
         :named hyp28))
(assert (! (forall ((x798 A)) 
               (=> 
                   (exists ((x799 Int)) 
                       (MS x799 x798 q)) 
                   (MS1 x798 a)))
         :named hyp29))
(assert (! (forall ((x800 Int)) 
               (=> 
                   (length q x800) 
                   (< 1 x800)))
         :named hyp30))
(assert (! (exists ((x801 Int)) 
               (and 
                   (= x801 1) 
                   (MS x801 x q)))
         :named hyp31))
(assert (! (exists ((x802 Int)) 
               (and 
                   (length q x802) 
                   (MS x802 y1 q)))
         :named hyp32))
(assert (! (forall ((i47 Int)) 
               (=> 
                   (and 
                       (<= 1 i47) 
                       (forall ((x803 Int)) 
                           (=> 
                               (length q x803) 
                               (<= i47 (- x803 1))))) 
                   (exists ((x804 A) (x805 A)) 
                       (and 
                           (MS i47 x804 q) 
                           (exists ((x806 Int)) 
                               (and 
                                   (= x806 (+ i47 1)) 
                                   (MS x806 x805 q))) 
                           (MS0 x804 x805 r)))))
         :named hyp33))
(assert (! (exists ((n53 Int)) 
               (and 
                   (<= 0 n53) 
                   (forall ((x807 Int) (x808 A)) 
                       (=> 
                           (MS x807 x808 p) 
                           (and 
                               (<= 1 x807) 
                               (<= x807 n53)))) 
                   (forall ((x809 Int) (x810 A) (x811 A)) 
                       (=> 
                           (and 
                               (MS x809 x810 p) 
                               (MS x809 x811 p)) 
                           (= x810 x811))) 
                   (forall ((x812 Int)) 
                       (=> 
                           (and 
                               (<= 1 x812) 
                               (<= x812 n53)) 
                           (exists ((x813 A)) 
                               (MS x812 x813 p))))))
         :named hyp34))
(assert (! (forall ((x814 A)) 
               (=> 
                   (exists ((x815 Int)) 
                       (MS x815 x814 p)) 
                   (MS1 x814 a)))
         :named hyp35))
(assert (! (forall ((x816 Int)) 
               (=> 
                   (length p x816) 
                   (< 1 x816)))
         :named hyp36))
(assert (! (exists ((x817 Int)) 
               (and 
                   (= x817 1) 
                   (MS x817 y2 p)))
         :named hyp37))
(assert (! (exists ((x818 Int)) 
               (and 
                   (length p x818) 
                   (MS x818 x1 p)))
         :named hyp38))
(assert (! (forall ((i48 Int)) 
               (=> 
                   (and 
                       (<= 1 i48) 
                       (forall ((x819 Int)) 
                           (=> 
                               (length p x819) 
                               (<= i48 (- x819 1))))) 
                   (exists ((x820 A) (x821 A)) 
                       (and 
                           (MS i48 x820 p) 
                           (exists ((x822 Int)) 
                               (and 
                                   (= x822 (+ i48 1)) 
                                   (MS x822 x821 p))) 
                           (MS0 x820 x821 r)))))
         :named hyp39))
(assert (! (forall ((x823 A) (y11 A)) 
               (=> 
                   (and 
                       (MS1 x823 a) 
                       (MS1 y11 a)) 
                   (exists ((p6 PZA)) 
                       (and 
                           (exists ((n54 Int)) 
                               (and 
                                   (<= 0 n54) 
                                   (forall ((x824 Int) (x825 A)) 
                                       (=> 
                                           (MS x824 x825 p6) 
                                           (and 
                                               (<= 1 x824) 
                                               (<= x824 n54)))) 
                                   (forall ((x826 Int) (x827 A) (x828 A)) 
                                       (=> 
                                           (and 
                                               (MS x826 x827 p6) 
                                               (MS x826 x828 p6)) 
                                           (= x827 x828))) 
                                   (forall ((x829 Int)) 
                                       (=> 
                                           (and 
                                               (<= 1 x829) 
                                               (<= x829 n54)) 
                                           (exists ((x830 A)) 
                                               (MS x829 x830 p6)))))) 
                           (forall ((x831 A)) 
                               (=> 
                                   (exists ((x832 Int)) 
                                       (MS x832 x831 p6)) 
                                   (MS1 x831 a))) 
                           (forall ((x833 Int)) 
                               (=> 
                                   (length p6 x833) 
                                   (< 1 x833))) 
                           (exists ((x834 Int)) 
                               (and 
                                   (= x834 1) 
                                   (MS x834 x823 p6))) 
                           (exists ((x835 Int)) 
                               (and 
                                   (length p6 x835) 
                                   (MS x835 y11 p6))) 
                           (forall ((i49 Int)) 
                               (=> 
                                   (and 
                                       (<= 1 i49) 
                                       (forall ((x836 Int)) 
                                           (=> 
                                               (length p6 x836) 
                                               (<= i49 (- x836 1))))) 
                                   (exists ((x837 A) (x838 A)) 
                                       (and 
                                           (MS i49 x837 p6) 
                                           (exists ((x839 Int)) 
                                               (and 
                                                   (= x839 (+ i49 1)) 
                                                   (MS x839 x838 p6))) 
                                           (MS0 x837 x838 r))))) 
                           (exists ((x840 Int)) 
                               (and 
                                   (length p6 x840) 
                                   (dist x823 y11 x840)))))))
         :named hyp40))
(assert (! (forall ((x841 A) (y12 A) (p7 PZA) (i50 Int)) 
               (=> 
                   (and 
                       (MS1 x841 a) 
                       (MS1 y12 a) 
                       (exists ((n55 Int)) 
                           (and 
                               (<= 0 n55) 
                               (forall ((x842 Int) (x843 A)) 
                                   (=> 
                                       (MS x842 x843 p7) 
                                       (and 
                                           (<= 1 x842) 
                                           (<= x842 n55)))) 
                               (forall ((x844 Int) (x845 A) (x846 A)) 
                                   (=> 
                                       (and 
                                           (MS x844 x845 p7) 
                                           (MS x844 x846 p7)) 
                                       (= x845 x846))) 
                               (forall ((x847 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x847) 
                                           (<= x847 n55)) 
                                       (exists ((x848 A)) 
                                           (MS x847 x848 p7)))))) 
                       (forall ((x849 A)) 
                           (=> 
                               (exists ((x850 Int)) 
                                   (MS x850 x849 p7)) 
                               (MS1 x849 a))) 
                       (forall ((x851 Int)) 
                           (=> 
                               (length p7 x851) 
                               (< 1 x851))) 
                       (exists ((x852 Int)) 
                           (and 
                               (= x852 1) 
                               (MS x852 x841 p7))) 
                       (exists ((x853 Int)) 
                           (and 
                               (length p7 x853) 
                               (MS x853 y12 p7))) 
                       (forall ((i51 Int)) 
                           (=> 
                               (and 
                                   (<= 1 i51) 
                                   (forall ((x854 Int)) 
                                       (=> 
                                           (length p7 x854) 
                                           (<= i51 (- x854 1))))) 
                               (exists ((x855 A) (x856 A)) 
                                   (and 
                                       (MS i51 x855 p7) 
                                       (exists ((x857 Int)) 
                                           (and 
                                               (= x857 (+ i51 1)) 
                                               (MS x857 x856 p7))) 
                                       (MS0 x855 x856 r))))) 
                       (exists ((x858 Int)) 
                           (and 
                               (length p7 x858) 
                               (dist x841 y12 x858))) 
                       (exists ((x859 A)) 
                           (MS i50 x859 p7)) 
                       (not 
                           (= i50 1)) 
                       (not 
                           (length p7 i50))) 
                   (and 
                       (exists ((n56 Int)) 
                           (and 
                               (<= 0 n56) 
                               (forall ((x860 Int) (x861 A)) 
                                   (=> 
                                       (and 
                                           (MS x860 x861 p7) 
                                           (<= 1 x860) 
                                           (<= x860 i50)) 
                                       (and 
                                           (<= 1 x860) 
                                           (<= x860 n56)))) 
                               (forall ((x862 Int) (x863 A) (x864 A)) 
                                   (=> 
                                       (and 
                                           (MS x862 x863 p7) 
                                           (<= 1 x862) 
                                           (<= x862 i50) 
                                           (MS x862 x864 p7)) 
                                       (= x863 x864))) 
                               (forall ((x865 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x865) 
                                           (<= x865 n56)) 
                                       (exists ((x866 A)) 
                                           (and 
                                               (MS x865 x866 p7) 
                                               (<= 1 x865) 
                                               (<= x865 i50))))))) 
                       (forall ((x867 A)) 
                           (=> 
                               (exists ((x868 Int)) 
                                   (and 
                                       (MS x868 x867 p7) 
                                       (<= 1 x868) 
                                       (<= x868 i50))) 
                               (MS1 x867 a))) 
                       (forall ((x869 Int)) 
                           (=> 
                               (exists ((x870 PZA)) 
                                   (and 
                                       (forall ((x871 Int) (x872 A)) 
                                           (= 
                                               (MS x871 x872 x870) 
                                               (and 
                                                   (MS x871 x872 p7) 
                                                   (<= 1 x871) 
                                                   (<= x871 i50)))) 
                                       (length x870 x869))) 
                               (< 1 x869))) 
                       (exists ((x873 Int)) 
                           (and 
                               (= x873 1) 
                               (MS x873 x841 p7))) 
                       (<= 1 1) 
                       (<= 1 i50) 
                       (exists ((x874 Int) (x875 A)) 
                           (and 
                               (exists ((x876 PZA)) 
                                   (and 
                                       (forall ((x877 Int) (x878 A)) 
                                           (= 
                                               (MS x877 x878 x876) 
                                               (and 
                                                   (MS x877 x878 p7) 
                                                   (<= 1 x877) 
                                                   (<= x877 i50)))) 
                                       (length x876 x874))) 
                               (MS i50 x875 p7) 
                               (MS x874 x875 p7))) 
                       (forall ((x879 Int)) 
                           (=> 
                               (exists ((x880 PZA)) 
                                   (and 
                                       (forall ((x881 Int) (x882 A)) 
                                           (= 
                                               (MS x881 x882 x880) 
                                               (and 
                                                   (MS x881 x882 p7) 
                                                   (<= 1 x881) 
                                                   (<= x881 i50)))) 
                                       (length x880 x879))) 
                               (<= 1 x879))) 
                       (forall ((x883 Int)) 
                           (=> 
                               (exists ((x884 PZA)) 
                                   (and 
                                       (forall ((x885 Int) (x886 A)) 
                                           (= 
                                               (MS x885 x886 x884) 
                                               (and 
                                                   (MS x885 x886 p7) 
                                                   (<= 1 x885) 
                                                   (<= x885 i50)))) 
                                       (length x884 x883))) 
                               (<= x883 i50))) 
                       (forall ((i52 Int)) 
                           (=> 
                               (and 
                                   (<= 1 i52) 
                                   (forall ((x887 Int)) 
                                       (=> 
                                           (exists ((x888 PZA)) 
                                               (and 
                                                   (forall ((x889 Int) (x890 A)) 
                                                       (= 
                                                           (MS x889 x890 x888) 
                                                           (and 
                                                               (MS x889 x890 p7) 
                                                               (<= 1 x889) 
                                                               (<= x889 i50)))) 
                                                   (length x888 x887))) 
                                           (<= i52 (- x887 1))))) 
                               (exists ((x891 A) (x892 A)) 
                                   (and 
                                       (MS i52 x891 p7) 
                                       (<= 1 i52) 
                                       (<= i52 i50) 
                                       (exists ((x893 Int)) 
                                           (and 
                                               (= x893 (+ i52 1)) 
                                               (MS x893 x892 p7))) 
                                       (<= 1 (+ i52 1)) 
                                       (<= (+ i52 1) i50) 
                                       (MS0 x891 x892 r))))) 
                       (exists ((x894 A) (x895 Int)) 
                           (and 
                               (MS i50 x894 p7) 
                               (exists ((x896 PZA)) 
                                   (and 
                                       (forall ((x897 Int) (x898 A)) 
                                           (= 
                                               (MS x897 x898 x896) 
                                               (and 
                                                   (MS x897 x898 p7) 
                                                   (<= 1 x897) 
                                                   (<= x897 i50)))) 
                                       (length x896 x895))) 
                               (dist x841 x894 x895))))))
         :named hyp41))
(assert (! (forall ((x899 A) (y13 A) (p8 PZA) (i53 Int)) 
               (=> 
                   (and 
                       (MS1 x899 a) 
                       (MS1 y13 a) 
                       (exists ((n57 Int)) 
                           (and 
                               (<= 0 n57) 
                               (forall ((x900 Int) (x901 A)) 
                                   (=> 
                                       (MS x900 x901 p8) 
                                       (and 
                                           (<= 1 x900) 
                                           (<= x900 n57)))) 
                               (forall ((x902 Int) (x903 A) (x904 A)) 
                                   (=> 
                                       (and 
                                           (MS x902 x903 p8) 
                                           (MS x902 x904 p8)) 
                                       (= x903 x904))) 
                               (forall ((x905 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x905) 
                                           (<= x905 n57)) 
                                       (exists ((x906 A)) 
                                           (MS x905 x906 p8)))))) 
                       (forall ((x907 A)) 
                           (=> 
                               (exists ((x908 Int)) 
                                   (MS x908 x907 p8)) 
                               (MS1 x907 a))) 
                       (forall ((x909 Int)) 
                           (=> 
                               (length p8 x909) 
                               (< 1 x909))) 
                       (exists ((x910 Int)) 
                           (and 
                               (= x910 1) 
                               (MS x910 x899 p8))) 
                       (exists ((x911 Int)) 
                           (and 
                               (length p8 x911) 
                               (MS x911 y13 p8))) 
                       (forall ((i54 Int)) 
                           (=> 
                               (and 
                                   (<= 1 i54) 
                                   (forall ((x912 Int)) 
                                       (=> 
                                           (length p8 x912) 
                                           (<= i54 (- x912 1))))) 
                               (exists ((x913 A) (x914 A)) 
                                   (and 
                                       (MS i54 x913 p8) 
                                       (exists ((x915 Int)) 
                                           (and 
                                               (= x915 (+ i54 1)) 
                                               (MS x915 x914 p8))) 
                                       (MS0 x913 x914 r))))) 
                       (exists ((x916 Int)) 
                           (and 
                               (length p8 x916) 
                               (dist x899 y13 x916))) 
                       (exists ((x917 A)) 
                           (MS i53 x917 p8)) 
                       (not 
                           (= i53 1)) 
                       (not 
                           (length p8 i53))) 
                   (and 
                       (exists ((x918 A)) 
                           (and 
                               (MS i53 x918 p8) 
                               (dist x899 x918 i53))) 
                       (exists ((x919 A) (x920 Int)) 
                           (and 
                               (exists ((x921 Int)) 
                                   (and 
                                       (= x921 (+ i53 1)) 
                                       (MS x921 x919 p8))) 
                               (= x920 (+ i53 1)) 
                               (dist x899 x919 x920))) 
                       (exists ((x922 A) (x923 A)) 
                           (and 
                               (MS i53 x922 p8) 
                               (exists ((x924 Int)) 
                                   (and 
                                       (= x924 (+ i53 1)) 
                                       (MS x924 x923 p8))) 
                               (MS0 x922 x923 r))))))
         :named hyp42))
(assert (! (forall ((x925 A) (y14 A) (p9 PZA) (z0 A)) 
               (=> 
                   (and 
                       (MS1 x925 a) 
                       (MS1 y14 a) 
                       (exists ((n58 Int)) 
                           (and 
                               (<= 0 n58) 
                               (forall ((x926 Int) (x927 A)) 
                                   (=> 
                                       (MS x926 x927 p9) 
                                       (and 
                                           (<= 1 x926) 
                                           (<= x926 n58)))) 
                               (forall ((x928 Int) (x929 A) (x930 A)) 
                                   (=> 
                                       (and 
                                           (MS x928 x929 p9) 
                                           (MS x928 x930 p9)) 
                                       (= x929 x930))) 
                               (forall ((x931 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x931) 
                                           (<= x931 n58)) 
                                       (exists ((x932 A)) 
                                           (MS x931 x932 p9)))))) 
                       (forall ((x933 A)) 
                           (=> 
                               (exists ((x934 Int)) 
                                   (MS x934 x933 p9)) 
                               (MS1 x933 a))) 
                       (forall ((x935 Int)) 
                           (=> 
                               (length p9 x935) 
                               (< 1 x935))) 
                       (exists ((x936 Int)) 
                           (and 
                               (= x936 1) 
                               (MS x936 x925 p9))) 
                       (exists ((x937 Int)) 
                           (and 
                               (length p9 x937) 
                               (MS x937 y14 p9))) 
                       (forall ((i55 Int)) 
                           (=> 
                               (and 
                                   (<= 1 i55) 
                                   (forall ((x938 Int)) 
                                       (=> 
                                           (length p9 x938) 
                                           (<= i55 (- x938 1))))) 
                               (exists ((x939 A) (x940 A)) 
                                   (and 
                                       (MS i55 x939 p9) 
                                       (exists ((x941 Int)) 
                                           (and 
                                               (= x941 (+ i55 1)) 
                                               (MS x941 x940 p9))) 
                                       (MS0 x939 x940 r))))) 
                       (exists ((x942 Int)) 
                           (and 
                               (length p9 x942) 
                               (dist x925 y14 x942))) 
                       (exists ((x943 Int)) 
                           (MS x943 z0 p9)) 
                       (not 
                           (= z0 x925)) 
                       (not 
                           (= z0 y14))) 
                   (exists ((t0 A)) 
                       (and 
                           (MS1 t0 a) 
                           (forall ((x944 Int) (x945 Int)) 
                               (=> 
                                   (and 
                                       (dist x925 z0 x945) 
                                       (dist x925 t0 x944)) 
                                   (< x945 x944))) 
                           (MS0 z0 t0 r)))))
         :named hyp43))
(assert (! (forall ((x946 A) (y15 A) (p10 PZA)) 
               (=> 
                   (and 
                       (exists ((n59 Int)) 
                           (and 
                               (<= 0 n59) 
                               (forall ((x947 Int) (x948 A)) 
                                   (=> 
                                       (MS x947 x948 p10) 
                                       (and 
                                           (<= 1 x947) 
                                           (<= x947 n59)))) 
                               (forall ((x949 Int) (x950 A) (x951 A)) 
                                   (=> 
                                       (and 
                                           (MS x949 x950 p10) 
                                           (MS x949 x951 p10)) 
                                       (= x950 x951))) 
                               (forall ((x952 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x952) 
                                           (<= x952 n59)) 
                                       (exists ((x953 A)) 
                                           (MS x952 x953 p10)))))) 
                       (forall ((x954 A)) 
                           (=> 
                               (exists ((x955 Int)) 
                                   (MS x955 x954 p10)) 
                               (MS1 x954 a))) 
                       (forall ((x956 Int)) 
                           (=> 
                               (length p10 x956) 
                               (< 1 x956))) 
                       (exists ((x957 Int)) 
                           (and 
                               (= x957 1) 
                               (MS x957 x946 p10))) 
                       (exists ((x958 Int)) 
                           (and 
                               (length p10 x958) 
                               (MS x958 y15 p10))) 
                       (forall ((i56 Int)) 
                           (=> 
                               (and 
                                   (<= 1 i56) 
                                   (forall ((x959 Int)) 
                                       (=> 
                                           (length p10 x959) 
                                           (<= i56 (- x959 1))))) 
                               (exists ((x960 A) (x961 A)) 
                                   (and 
                                       (MS i56 x960 p10) 
                                       (exists ((x962 Int)) 
                                           (and 
                                               (= x962 (+ i56 1)) 
                                               (MS x962 x961 p10))) 
                                       (MS0 x960 x961 r)))))) 
                   (and 
                       (exists ((n60 Int)) 
                           (and 
                               (<= 0 n60) 
                               (forall ((x963 Int) (x964 A)) 
                                   (=> 
                                       (exists ((i57 Int)) 
                                           (and 
                                               (<= 1 i57) 
                                               (forall ((x965 Int)) 
                                                   (=> 
                                                       (length p10 x965) 
                                                       (<= i57 x965))) 
                                               (= x963 i57) 
                                               (exists ((x966 Int)) 
                                                   (and 
                                                       (forall ((x967 Int)) 
                                                           (=> 
                                                               (length p10 x967) 
                                                               (= x966 (+ (- x967 i57) 1)))) 
                                                       (MS x966 x964 p10))))) 
                                       (and 
                                           (<= 1 x963) 
                                           (<= x963 n60)))) 
                               (forall ((x968 Int) (x969 A) (x970 A)) 
                                   (=> 
                                       (and 
                                           (exists ((i58 Int)) 
                                               (and 
                                                   (<= 1 i58) 
                                                   (forall ((x971 Int)) 
                                                       (=> 
                                                           (length p10 x971) 
                                                           (<= i58 x971))) 
                                                   (= x968 i58) 
                                                   (exists ((x972 Int)) 
                                                       (and 
                                                           (forall ((x973 Int)) 
                                                               (=> 
                                                                   (length p10 x973) 
                                                                   (= x972 (+ (- x973 i58) 1)))) 
                                                           (MS x972 x969 p10))))) 
                                           (exists ((i59 Int)) 
                                               (and 
                                                   (<= 1 i59) 
                                                   (forall ((x974 Int)) 
                                                       (=> 
                                                           (length p10 x974) 
                                                           (<= i59 x974))) 
                                                   (= x968 i59) 
                                                   (exists ((x975 Int)) 
                                                       (and 
                                                           (forall ((x976 Int)) 
                                                               (=> 
                                                                   (length p10 x976) 
                                                                   (= x975 (+ (- x976 i59) 1)))) 
                                                           (MS x975 x970 p10)))))) 
                                       (= x969 x970))) 
                               (forall ((x977 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x977) 
                                           (<= x977 n60)) 
                                       (exists ((x978 A) (i60 Int)) 
                                           (and 
                                               (<= 1 i60) 
                                               (forall ((x979 Int)) 
                                                   (=> 
                                                       (length p10 x979) 
                                                       (<= i60 x979))) 
                                               (= x977 i60) 
                                               (exists ((x980 Int)) 
                                                   (and 
                                                       (forall ((x981 Int)) 
                                                           (=> 
                                                               (length p10 x981) 
                                                               (= x980 (+ (- x981 i60) 1)))) 
                                                       (MS x980 x978 p10))))))))) 
                       (forall ((i61 Int)) 
                           (=> 
                               (and 
                                   (<= 1 i61) 
                                   (forall ((x982 Int)) 
                                       (=> 
                                           (length p10 x982) 
                                           (<= i61 x982)))) 
                               (exists ((x983 A)) 
                                   (and 
                                       (exists ((x984 Int)) 
                                           (and 
                                               (forall ((x985 Int)) 
                                                   (=> 
                                                       (length p10 x985) 
                                                       (= x984 (+ (- x985 i61) 1)))) 
                                               (MS x984 x983 p10))) 
                                       (MS1 x983 a))))) 
                       (forall ((x986 Int)) 
                           (=> 
                               (exists ((x987 PZA)) 
                                   (and 
                                       (forall ((x988 Int) (x989 A)) 
                                           (= 
                                               (MS x988 x989 x987) 
                                               (exists ((i62 Int)) 
                                                   (and 
                                                       (<= 1 i62) 
                                                       (forall ((x990 Int)) 
                                                           (=> 
                                                               (length p10 x990) 
                                                               (<= i62 x990))) 
                                                       (= x988 i62) 
                                                       (exists ((x991 Int)) 
                                                           (and 
                                                               (forall ((x992 Int)) 
                                                                   (=> 
                                                                       (length p10 x992) 
                                                                       (= x991 (+ (- x992 i62) 1)))) 
                                                               (MS x991 x989 p10))))))) 
                                       (length x987 x986))) 
                               (< 1 x986))) 
                       (exists ((x993 Int)) 
                           (and 
                               (forall ((x994 Int)) 
                                   (=> 
                                       (length p10 x994) 
                                       (= x993 (+ (- x994 1) 1)))) 
                               (MS x993 y15 p10))) 
                       (exists ((x995 Int)) 
                           (and 
                               (forall ((x996 Int) (x997 Int)) 
                                   (=> 
                                       (and 
                                           (length p10 x997) 
                                           (exists ((x998 PZA)) 
                                               (and 
                                                   (forall ((x999 Int) (x1000 A)) 
                                                       (= 
                                                           (MS x999 x1000 x998) 
                                                           (exists ((i63 Int)) 
                                                               (and 
                                                                   (<= 1 i63) 
                                                                   (forall ((x1001 Int)) 
                                                                       (=> 
                                                                           (length p10 x1001) 
                                                                           (<= i63 x1001))) 
                                                                   (= x999 i63) 
                                                                   (exists ((x1002 Int)) 
                                                                       (and 
                                                                           (forall ((x1003 Int)) 
                                                                               (=> 
                                                                                   (length p10 x1003) 
                                                                                   (= x1002 (+ (- x1003 i63) 1)))) 
                                                                           (MS x1002 x1000 p10))))))) 
                                                   (length x998 x996)))) 
                                       (= x995 (+ (- x997 x996) 1)))) 
                               (MS x995 x946 p10))) 
                       (forall ((i64 Int)) 
                           (=> 
                               (and 
                                   (<= 1 i64) 
                                   (forall ((x1004 Int)) 
                                       (=> 
                                           (exists ((x1005 PZA)) 
                                               (and 
                                                   (forall ((x1006 Int) (x1007 A)) 
                                                       (= 
                                                           (MS x1006 x1007 x1005) 
                                                           (exists ((i65 Int)) 
                                                               (and 
                                                                   (<= 1 i65) 
                                                                   (forall ((x1008 Int)) 
                                                                       (=> 
                                                                           (length p10 x1008) 
                                                                           (<= i65 x1008))) 
                                                                   (= x1006 i65) 
                                                                   (exists ((x1009 Int)) 
                                                                       (and 
                                                                           (forall ((x1010 Int)) 
                                                                               (=> 
                                                                                   (length p10 x1010) 
                                                                                   (= x1009 (+ (- x1010 i65) 1)))) 
                                                                           (MS x1009 x1007 p10))))))) 
                                                   (length x1005 x1004))) 
                                           (<= i64 (- x1004 1))))) 
                               (exists ((x1011 A) (x1012 A)) 
                                   (and 
                                       (exists ((x1013 Int)) 
                                           (and 
                                               (forall ((x1014 Int)) 
                                                   (=> 
                                                       (length p10 x1014) 
                                                       (= x1013 (+ (- x1014 i64) 1)))) 
                                               (MS x1013 x1011 p10))) 
                                       (exists ((x1015 Int)) 
                                           (and 
                                               (forall ((x1016 Int)) 
                                                   (=> 
                                                       (length p10 x1016) 
                                                       (= x1015 (+ (- x1016 (+ i64 1)) 1)))) 
                                               (MS x1015 x1012 p10))) 
                                       (MS0 x1011 x1012 r))))))))
         :named hyp44))
(assert (! (exists ((x1017 A)) 
               (and 
                   (exists ((x1018 Int)) 
                       (and 
                           (= x1018 1) 
                           (MS x1018 x1017 q))) 
                   (MS1 x1017 a)))
         :named hyp45))
(assert (! (exists ((x1019 A)) 
               (and 
                   (exists ((x1020 Int)) 
                       (and 
                           (length q x1020) 
                           (MS x1020 x1019 q))) 
                   (MS1 x1019 a)))
         :named hyp46))
(assert (! (exists ((x1021 A)) 
               (and 
                   (exists ((x1022 Int)) 
                       (and 
                           (= x1022 1) 
                           (MS x1022 x1021 p))) 
                   (MS1 x1021 a)))
         :named hyp47))
(assert (! (exists ((x1023 A)) 
               (and 
                   (exists ((x1024 Int)) 
                       (and 
                           (length p x1024) 
                           (MS x1024 x1023 p))) 
                   (MS1 x1023 a)))
         :named hyp48))
(assert (! (exists ((x1025 A) (x1026 A)) 
               (and 
                   (exists ((x1027 Int)) 
                       (and 
                           (length p x1027) 
                           (MS x1027 x1025 p))) 
                   (exists ((x1028 Int)) 
                       (and 
                           (= x1028 1) 
                           (MS x1028 x1026 q))) 
                   (MS0 x1025 x1026 r)))
         :named hyp49))
(assert (! (forall ((x1029 A) (x1030 A)) 
               (=> 
                   (MS0 x1029 x1030 r) 
                   (and 
                       (MS1 x1029 a) 
                       (MS1 x1030 a))))
         :named hyp50))
(assert (! (not 
               (forall ((x1031 A) (x1032 A)) 
                   (not 
                       (MS0 x1031 x1032 r))))
         :named hyp51))
(assert (! (forall ((x1033 A) (x1034 A)) 
               (=> 
                   (MS0 x1033 x1034 c) 
                   (and 
                       (MS1 x1033 a) 
                       (MS1 x1034 a))))
         :named hyp52))
(assert (! (forall ((x1035 A) (x1036 A)) 
               (=> 
                   (MS0 x1035 x1036 r) 
                   (MS0 x1035 x1036 c)))
         :named hyp53))
(assert (! (forall ((x1037 A) (x1038 A)) 
               (=> 
                   (exists ((x1039 A)) 
                       (and 
                           (MS0 x1037 x1039 c) 
                           (MS0 x1039 x1038 r))) 
                   (MS0 x1037 x1038 c)))
         :named hyp54))
(assert (! (forall ((s41 PAA)) 
               (=> 
                   (and 
                       (forall ((x1040 A) (x1041 A)) 
                           (=> 
                               (MS0 x1040 x1041 s41) 
                               (and 
                                   (MS1 x1040 a) 
                                   (MS1 x1041 a)))) 
                       (forall ((x1042 A) (x1043 A)) 
                           (=> 
                               (MS0 x1042 x1043 r) 
                               (MS0 x1042 x1043 s41))) 
                       (forall ((x1044 A) (x1045 A)) 
                           (=> 
                               (exists ((x1046 A)) 
                                   (and 
                                       (MS0 x1044 x1046 s41) 
                                       (MS0 x1046 x1045 r))) 
                               (MS0 x1044 x1045 s41)))) 
                   (forall ((x1047 A) (x1048 A)) 
                       (=> 
                           (MS0 x1047 x1048 c) 
                           (MS0 x1047 x1048 s41)))))
         :named hyp55))
(assert (! (forall ((x1049 A)) 
               (= 
                   (exists ((x1050 A)) 
                       (MS0 x1049 x1050 r)) 
                   (MS1 x1049 a)))
         :named hyp56))
(assert (! (forall ((x1051 A)) 
               (= 
                   (exists ((x1052 A)) 
                       (MS0 x1051 x1052 c)) 
                   (MS1 x1051 a)))
         :named hyp57))
(assert (! (forall ((x1053 A)) 
               (=> 
                   (exists ((x1054 A)) 
                       (MS0 x1053 x1054 r)) 
                   (exists ((x1055 A)) 
                       (MS0 x1053 x1055 c))))
         :named hyp58))
(assert (! (forall ((x1056 A) (x1057 A)) 
               (= 
                   (MS0 x1056 x1057 c) 
                   (or 
                       (MS0 x1056 x1057 r) 
                       (exists ((x1058 A)) 
                           (and 
                               (MS0 x1056 x1058 c) 
                               (MS0 x1058 x1057 r))))))
         :named hyp59))
(assert (! (forall ((x1059 A) (y16 A)) 
               (=> 
                   (and 
                       (MS1 x1059 a) 
                       (MS1 y16 a)) 
                   (forall ((s42 PZA) (n61 Int)) 
                       (=> 
                           (and 
                               (<= 0 n61) 
                               (< 1 n61) 
                               (forall ((x1060 Int) (x1061 A)) 
                                   (=> 
                                       (MS x1060 x1061 s42) 
                                       (and 
                                           (<= 1 x1060) 
                                           (<= x1060 n61) 
                                           (MS1 x1061 a)))) 
                               (forall ((x1062 Int) (x1063 A) (x1064 A)) 
                                   (=> 
                                       (and 
                                           (MS x1062 x1063 s42) 
                                           (MS x1062 x1064 s42)) 
                                       (= x1063 x1064))) 
                               (forall ((x1065 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x1065) 
                                           (<= x1065 n61)) 
                                       (exists ((x1066 A)) 
                                           (MS x1065 x1066 s42))))) 
                           (and 
                               (exists ((x1067 A) (x1068 Int)) 
                                   (and 
                                       (= x1068 1) 
                                       (MS x1068 x1067 s42))) 
                               (forall ((x1069 Int) (x1070 A) (x1071 A)) 
                                   (=> 
                                       (and 
                                           (MS x1069 x1070 s42) 
                                           (MS x1069 x1071 s42)) 
                                       (= x1070 x1071))) 
                               (=> 
                                   (exists ((x1072 Int)) 
                                       (and 
                                           (= x1072 1) 
                                           (MS x1072 x1059 s42))) 
                                   (and 
                                       (exists ((x1073 A)) 
                                           (MS n61 x1073 s42)) 
                                       (=> 
                                           (MS n61 y16 s42) 
                                           (forall ((i66 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 i66) 
                                                       (<= i66 (- n61 1))) 
                                                   (and 
                                                       (exists ((x1074 A)) 
                                                           (MS i66 x1074 s42)) 
                                                       (exists ((x1075 A) (x1076 Int)) 
                                                           (and 
                                                               (= x1076 (+ i66 1)) 
                                                               (MS x1076 x1075 s42))))))))))))))
         :named hyp60))
(assert (! (forall ((x1077 A) (x1078 A)) 
               (=> 
                   (exists ((x1079 PZA)) 
                       (path x1077 x1078 x1079)) 
                   (MS0 x1077 x1078 c)))
         :named hyp61))
(assert (! (forall ((x1080 A) (x1081 A)) 
               (=> 
                   (MS0 x1080 x1081 c) 
                   (exists ((x1082 PZA)) 
                       (path x1080 x1081 x1082))))
         :named hyp62))
(assert (! (forall ((x1083 A) (x1084 A)) 
               (=> 
                   (and 
                       (MS1 x1083 a) 
                       (MS1 x1084 a)) 
                   (exists ((x1085 PZA)) 
                       (path x1083 x1084 x1085))))
         :named hyp63))
(assert (! (forall ((n62 Int) (s43 PZA)) 
               (=> 
                   (and 
                       (<= 0 n62) 
                       (forall ((x1086 Int) (x1087 A)) 
                           (=> 
                               (MS x1086 x1087 s43) 
                               (and 
                                   (<= 1 x1086) 
                                   (<= x1086 n62)))) 
                       (forall ((x1088 Int) (x1089 A) (x1090 A)) 
                           (=> 
                               (and 
                                   (MS x1088 x1089 s43) 
                                   (MS x1088 x1090 s43)) 
                               (= x1089 x1090))) 
                       (forall ((x1091 Int)) 
                           (=> 
                               (and 
                                   (<= 1 x1091) 
                                   (<= x1091 n62)) 
                               (exists ((x1092 A)) 
                                   (MS x1091 x1092 s43))))) 
                   (seq s43)))
         :named hyp64))
(assert (! (and 
               (forall ((x1093 PZA) (x1094 Int)) 
                   (=> 
                       (length x1093 x1094) 
                       (and 
                           (seq x1093) 
                           (<= 0 x1094)))) 
               (forall ((x1095 PZA) (x1096 Int) (x1097 Int)) 
                   (=> 
                       (and 
                           (length x1095 x1096) 
                           (length x1095 x1097)) 
                       (= x1096 x1097))) 
               (forall ((x1098 PZA)) 
                   (=> 
                       (seq x1098) 
                       (exists ((x1099 Int)) 
                           (length x1098 x1099)))))
         :named hyp65))
(assert (! (forall ((s44 PZA)) 
               (=> 
                   (seq s44) 
                   (and 
                       (forall ((x1100 Int) (x1101 A)) 
                           (=> 
                               (MS x1100 x1101 s44) 
                               (and 
                                   (<= 1 x1100) 
                                   (forall ((x1102 Int)) 
                                       (=> 
                                           (length s44 x1102) 
                                           (<= x1100 x1102)))))) 
                       (forall ((x1103 Int) (x1104 A) (x1105 A)) 
                           (=> 
                               (and 
                                   (MS x1103 x1104 s44) 
                                   (MS x1103 x1105 s44)) 
                               (= x1104 x1105))) 
                       (forall ((x1106 Int)) 
                           (=> 
                               (and 
                                   (<= 1 x1106) 
                                   (forall ((x1107 Int)) 
                                       (=> 
                                           (length s44 x1107) 
                                           (<= x1106 x1107)))) 
                               (exists ((x1108 A)) 
                                   (MS x1106 x1108 s44)))))))
         :named hyp66))
(assert (! (forall ((x1109 PZA) (x1110 PZA) (x1111 PZA)) 
               (= 
                   (cnc x1109 x1110 x1111) 
                   (exists ((s112 PZA) (s211 PZA)) 
                       (and 
                           (seq s112) 
                           (seq s211) 
                           (forall ((x1112 Int) (x1113 A)) 
                               (= 
                                   (MS x1112 x1113 x1109) 
                                   (MS x1112 x1113 s112))) 
                           (forall ((x1114 Int) (x1115 A)) 
                               (= 
                                   (MS x1114 x1115 x1110) 
                                   (MS x1114 x1115 s211))) 
                           (forall ((x1116 Int) (x1117 A)) 
                               (= 
                                   (MS x1116 x1117 x1111) 
                                   (or 
                                       (exists ((i67 Int)) 
                                           (and 
                                               (<= 1 i67) 
                                               (forall ((x1118 Int)) 
                                                   (=> 
                                                       (length s112 x1118) 
                                                       (<= i67 x1118))) 
                                               (= x1116 i67) 
                                               (MS i67 x1117 s112))) 
                                       (exists ((i68 Int)) 
                                           (and 
                                               (forall ((x1119 Int)) 
                                                   (=> 
                                                       (length s112 x1119) 
                                                       (<= (+ x1119 1) i68))) 
                                               (forall ((x1120 Int) (x1121 Int)) 
                                                   (=> 
                                                       (and 
                                                           (length s112 x1121) 
                                                           (length s211 x1120)) 
                                                       (<= i68 (+ x1121 x1120)))) 
                                               (= x1116 i68) 
                                               (exists ((x1122 Int)) 
                                                   (and 
                                                       (forall ((x1123 Int)) 
                                                           (=> 
                                                               (length s112 x1123) 
                                                               (= x1122 (- i68 x1123)))) 
                                                       (MS x1122 x1117 s211))))))))))))
         :named hyp67))
(assert (! (and 
               (forall ((x1124 PZA) (x1125 PZA) (x1126 PZA)) 
                   (=> 
                       (cnc x1124 x1125 x1126) 
                       (and 
                           (seq x1124) 
                           (seq x1125) 
                           (seq x1126)))) 
               (forall ((x1127 PZA) (x1128 PZA) (x1129 PZA) (x1130 PZA)) 
                   (=> 
                       (and 
                           (cnc x1127 x1128 x1129) 
                           (cnc x1127 x1128 x1130)) 
                       (forall ((x1131 Int) (x1132 A)) 
                           (= 
                               (MS x1131 x1132 x1129) 
                               (MS x1131 x1132 x1130))))) 
               (forall ((x1133 PZA) (x1134 PZA)) 
                   (=> 
                       (and 
                           (seq x1133) 
                           (seq x1134)) 
                       (exists ((x1135 PZA)) 
                           (cnc x1133 x1134 x1135)))))
         :named hyp68))
(assert (! (forall ((s113 PZA) (s212 PZA)) 
               (=> 
                   (and 
                       (seq s113) 
                       (seq s212)) 
                   (exists ((x1136 PZA) (x1137 Int)) 
                       (and 
                           (cnc s113 s212 x1136) 
                           (forall ((x1138 Int) (x1139 Int)) 
                               (=> 
                                   (and 
                                       (length s113 x1139) 
                                       (length s212 x1138)) 
                                   (= x1137 (+ x1139 x1138)))) 
                           (length x1136 x1137)))))
         :named hyp69))
(assert (! (forall ((s114 PZA) (s213 PZA)) 
               (=> 
                   (and 
                       (seq s114) 
                       (seq s213)) 
                   (forall ((x1140 Int)) 
                       (= 
                           (exists ((x1141 A) (x1142 PZA)) 
                               (and 
                                   (cnc s114 s213 x1142) 
                                   (MS x1140 x1141 x1142))) 
                           (and 
                               (<= 1 x1140) 
                               (forall ((x1143 Int) (x1144 Int)) 
                                   (=> 
                                       (and 
                                           (length s114 x1144) 
                                           (length s213 x1143)) 
                                       (<= x1140 (+ x1144 x1143)))))))))
         :named hyp70))
(assert (! (forall ((s115 PZA) (s214 PZA)) 
               (=> 
                   (and 
                       (seq s115) 
                       (seq s214)) 
                   (forall ((x1145 A)) 
                       (= 
                           (exists ((x1146 Int) (x1147 PZA)) 
                               (and 
                                   (cnc s115 s214 x1147) 
                                   (MS x1146 x1145 x1147))) 
                           (or 
                               (exists ((x1148 Int)) 
                                   (MS x1148 x1145 s115)) 
                               (exists ((x1149 Int)) 
                                   (MS x1149 x1145 s214)))))))
         :named hyp71))
(assert (! (forall ((s116 PZA) (s215 PZA) (i69 Int)) 
               (=> 
                   (and 
                       (seq s116) 
                       (seq s215) 
                       (<= 1 i69) 
                       (forall ((x1150 Int)) 
                           (=> 
                               (length s116 x1150) 
                               (<= i69 x1150)))) 
                   (exists ((x1151 PZA)) 
                       (and 
                           (cnc s116 s215 x1151) 
                           (exists ((x1152 A)) 
                               (and 
                                   (MS i69 x1152 s116) 
                                   (MS i69 x1152 x1151)))))))
         :named hyp72))
(assert (! (forall ((s117 PZA) (s216 PZA) (i70 Int)) 
               (=> 
                   (and 
                       (seq s117) 
                       (seq s216) 
                       (forall ((x1153 Int)) 
                           (=> 
                               (length s117 x1153) 
                               (<= (+ x1153 1) i70))) 
                       (forall ((x1154 Int) (x1155 Int)) 
                           (=> 
                               (and 
                                   (length s117 x1155) 
                                   (length s216 x1154)) 
                               (<= i70 (+ x1155 x1154))))) 
                   (exists ((x1156 PZA)) 
                       (and 
                           (cnc s117 s216 x1156) 
                           (exists ((x1157 A)) 
                               (and 
                                   (exists ((x1158 Int)) 
                                       (and 
                                           (forall ((x1159 Int)) 
                                               (=> 
                                                   (length s117 x1159) 
                                                   (= x1158 (- i70 x1159)))) 
                                           (MS x1158 x1157 s216))) 
                                   (MS i70 x1157 x1156)))))))
         :named hyp73))
(assert (! (forall ((x1160 A) (y17 A)) 
               (=> 
                   (and 
                       (MS1 x1160 a) 
                       (MS1 y17 a)) 
                   (exists ((x1161 Int)) 
                       (and 
                           (exists ((x1162 PZA)) 
                               (and 
                                   (exists ((x1163 A) (x1164 A)) 
                                       (and 
                                           (= x1163 x1160) 
                                           (= x1164 y17) 
                                           (path x1163 x1164 x1162))) 
                                   (length x1162 x1161))) 
                           (forall ((x1165 Int)) 
                               (=> 
                                   (exists ((x1166 PZA)) 
                                       (and 
                                           (exists ((x1167 A) (x1168 A)) 
                                               (and 
                                                   (= x1167 x1160) 
                                                   (= x1168 y17) 
                                                   (path x1167 x1168 x1166))) 
                                           (length x1166 x1165))) 
                                   (<= x1161 x1165))) 
                           (dist x1160 y17 x1161)))))
         :named hyp74))
(assert (! (forall ((x1169 PZA) (x1170 PZA)) 
               (= 
                   (reverse x1169 x1170) 
                   (exists ((s45 PZA)) 
                       (and 
                           (seq s45) 
                           (forall ((x1171 Int) (x1172 A)) 
                               (= 
                                   (MS x1171 x1172 x1169) 
                                   (MS x1171 x1172 s45))) 
                           (forall ((x1173 Int) (x1174 A)) 
                               (= 
                                   (MS x1173 x1174 x1170) 
                                   (exists ((i71 Int)) 
                                       (and 
                                           (<= 1 i71) 
                                           (forall ((x1175 Int)) 
                                               (=> 
                                                   (length s45 x1175) 
                                                   (<= i71 x1175))) 
                                           (= x1173 i71) 
                                           (exists ((x1176 Int)) 
                                               (and 
                                                   (forall ((x1177 Int)) 
                                                       (=> 
                                                           (length s45 x1177) 
                                                           (= x1176 (+ (- x1177 i71) 1)))) 
                                                   (MS x1176 x1174 s45)))))))))))
         :named hyp75))
(assert (! (and 
               (forall ((x1178 PZA) (x1179 PZA)) 
                   (=> 
                       (reverse x1178 x1179) 
                       (and 
                           (seq x1178) 
                           (seq x1179)))) 
               (forall ((x1180 PZA) (x1181 PZA) (x1182 PZA)) 
                   (=> 
                       (and 
                           (reverse x1180 x1181) 
                           (reverse x1180 x1182)) 
                       (forall ((x1183 Int) (x1184 A)) 
                           (= 
                               (MS x1183 x1184 x1181) 
                               (MS x1183 x1184 x1182))))) 
               (forall ((x1185 PZA)) 
                   (=> 
                       (seq x1185) 
                       (exists ((x1186 PZA)) 
                           (reverse x1185 x1186)))))
         :named hyp76))
(assert (! (forall ((s46 PZA)) 
               (=> 
                   (seq s46) 
                   (exists ((x1187 PZA) (x1188 Int)) 
                       (and 
                           (reverse s46 x1187) 
                           (length s46 x1188) 
                           (length x1187 x1188)))))
         :named hyp77))
(assert (! (forall ((s47 PZA)) 
               (=> 
                   (seq s47) 
                   (forall ((x1189 A)) 
                       (= 
                           (exists ((x1190 Int) (x1191 PZA)) 
                               (and 
                                   (reverse s47 x1191) 
                                   (MS x1190 x1189 x1191))) 
                           (exists ((x1192 Int)) 
                               (MS x1192 x1189 s47))))))
         :named hyp78))
(assert (! (forall ((s48 PZA)) 
               (=> 
                   (seq s48) 
                   (exists ((x1193 PZA)) 
                       (and 
                           (reverse s48 x1193) 
                           (reverse x1193 s48)))))
         :named hyp79))
(assert (! (forall ((x1194 A) (y18 A) (p11 PZA)) 
               (=> 
                   (path x1194 y18 p11) 
                   (exists ((x1195 PZA)) 
                       (and 
                           (reverse p11 x1195) 
                           (path y18 x1194 x1195)))))
         :named hyp80))
(assert (! (forall ((x1196 A) (y19 A)) 
               (=> 
                   (and 
                       (MS1 x1196 a) 
                       (MS1 y19 a)) 
                   (forall ((x1197 PZA)) 
                       (= 
                           (exists ((x1198 A) (x1199 A)) 
                               (and 
                                   (= x1198 y19) 
                                   (= x1199 x1196) 
                                   (path x1198 x1199 x1197))) 
                           (exists ((x1200 PZA)) 
                               (and 
                                   (exists ((x1201 A) (x1202 A)) 
                                       (and 
                                           (= x1201 x1196) 
                                           (= x1202 y19) 
                                           (path x1201 x1202 x1200))) 
                                   (reverse x1200 x1197)))))))
         :named hyp81))
(assert (! (forall ((x1203 A) (x1204 A) (x1205 PZA)) 
               (= 
                   (shpath x1203 x1204 x1205) 
                   (exists ((x1206 A) (y20 A) (p12 PZA)) 
                       (and 
                           (path x1206 y20 p12) 
                           (exists ((x1207 Int)) 
                               (and 
                                   (length p12 x1207) 
                                   (dist x1206 y20 x1207))) 
                           (= x1203 x1206) 
                           (= x1204 y20) 
                           (forall ((x1208 Int) (x1209 A)) 
                               (= 
                                   (MS x1208 x1209 x1205) 
                                   (MS x1208 x1209 p12)))))))
         :named hyp82))
(assert (! (forall ((x1210 A) (y21 A) (p13 PZA)) 
               (=> 
                   (path x1210 y21 p13) 
                   (and 
                       (exists ((x1211 Int)) 
                           (dist x1210 y21 x1211)) 
                       (forall ((x1212 A) (x1213 A) (x1214 Int) (x1215 Int)) 
                           (=> 
                               (and 
                                   (dist x1212 x1213 x1214) 
                                   (dist x1212 x1213 x1215)) 
                               (= x1214 x1215))) 
                       (exists ((x1216 Int)) 
                           (length p13 x1216)) 
                       (forall ((x1217 PZA) (x1218 Int) (x1219 Int)) 
                           (=> 
                               (and 
                                   (length x1217 x1218) 
                                   (length x1217 x1219)) 
                               (= x1218 x1219))))))
         :named hyp83))
(assert (! (forall ((x1220 A) (y22 A)) 
               (=> 
                   (and 
                       (MS1 x1220 a) 
                       (MS1 y22 a)) 
                   (exists ((x1221 PZA)) 
                       (shpath x1220 y22 x1221))))
         :named hyp84))
(assert (! (forall ((x1222 A) (x1223 A) (x1224 PZA)) 
               (= 
                   (path x1222 x1223 x1224) 
                   (exists ((x1225 A) (y23 A) (p14 PZA)) 
                       (and 
                           (MS1 x1225 a) 
                           (MS1 y23 a) 
                           (exists ((n63 Int)) 
                               (and 
                                   (<= 0 n63) 
                                   (< 1 n63) 
                                   (forall ((x1226 Int) (x1227 A)) 
                                       (=> 
                                           (MS x1226 x1227 p14) 
                                           (and 
                                               (<= 1 x1226) 
                                               (<= x1226 n63) 
                                               (MS1 x1227 a)))) 
                                   (forall ((x1228 Int) (x1229 A) (x1230 A)) 
                                       (=> 
                                           (and 
                                               (MS x1228 x1229 p14) 
                                               (MS x1228 x1230 p14)) 
                                           (= x1229 x1230))) 
                                   (forall ((x1231 Int)) 
                                       (=> 
                                           (and 
                                               (<= 1 x1231) 
                                               (<= x1231 n63)) 
                                           (exists ((x1232 A)) 
                                               (MS x1231 x1232 p14)))) 
                                   (exists ((x1233 Int)) 
                                       (and 
                                           (= x1233 1) 
                                           (MS x1233 x1225 p14))) 
                                   (MS n63 y23 p14) 
                                   (forall ((i72 Int)) 
                                       (=> 
                                           (and 
                                               (<= 1 i72) 
                                               (<= i72 (- n63 1))) 
                                           (exists ((x1234 A) (x1235 A)) 
                                               (and 
                                                   (MS i72 x1234 p14) 
                                                   (exists ((x1236 Int)) 
                                                       (and 
                                                           (= x1236 (+ i72 1)) 
                                                           (MS x1236 x1235 p14))) 
                                                   (MS0 x1234 x1235 r))))))) 
                           (= x1222 x1225) 
                           (= x1223 y23) 
                           (forall ((x1237 Int) (x1238 A)) 
                               (= 
                                   (MS x1237 x1238 x1224) 
                                   (MS x1237 x1238 p14)))))))
         :named hyp85))
(assert (! (forall ((x1239 A)) 
               (= 
                   (MS1 x1239 candidate) 
                   (exists ((z1 A)) 
                       (and 
                           (MS1 z1 a) 
                           (forall ((x1240 A) (y24 A)) 
                               (=> 
                                   (and 
                                       (MS1 x1240 a) 
                                       (not 
                                           (= x1240 z1)) 
                                       (MS1 y24 a) 
                                       (not 
                                           (= y24 z1)) 
                                       (not 
                                           (= x1240 y24))) 
                                   (exists ((p15 PZA)) 
                                       (and 
                                           (exists ((x1241 A) (x1242 A)) 
                                               (and 
                                                   (= x1241 x1240) 
                                                   (= x1242 y24) 
                                                   (path x1241 x1242 p15))) 
                                           (not 
                                               (exists ((x1243 Int)) 
                                                   (MS x1243 z1 p15))))))) 
                           (= x1239 z1)))))
         :named hyp86))
(assert (! (forall ((u A)) 
               (=> 
                   (MS1 u candidate) 
                   (forall ((x1244 A) (x1245 A)) 
                       (=> 
                           (and 
                               (MS1 x1244 a) 
                               (not 
                                   (= x1244 u)) 
                               (MS1 x1245 a) 
                               (not 
                                   (= x1245 u)) 
                               (not 
                                   (= x1244 x1245))) 
                           (exists ((x1246 A) (y25 A) (p16 PZA)) 
                               (and 
                                   (MS1 x1246 a) 
                                   (not 
                                       (= x1246 u)) 
                                   (MS1 y25 a) 
                                   (not 
                                       (= y25 u)) 
                                   (not 
                                       (= x1246 y25)) 
                                   (exists ((n64 Int)) 
                                       (and 
                                           (<= 0 n64) 
                                           (< 1 n64) 
                                           (forall ((x1247 Int) (x1248 A)) 
                                               (=> 
                                                   (MS x1247 x1248 p16) 
                                                   (and 
                                                       (<= 1 x1247) 
                                                       (<= x1247 n64) 
                                                       (MS1 x1248 a) 
                                                       (not 
                                                           (= x1248 u))))) 
                                           (forall ((x1249 Int) (x1250 A) (x1251 A)) 
                                               (=> 
                                                   (and 
                                                       (MS x1249 x1250 p16) 
                                                       (MS x1249 x1251 p16)) 
                                                   (= x1250 x1251))) 
                                           (forall ((x1252 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x1252) 
                                                       (<= x1252 n64)) 
                                                   (exists ((x1253 A)) 
                                                       (MS x1252 x1253 p16)))) 
                                           (exists ((x1254 Int)) 
                                               (and 
                                                   (= x1254 1) 
                                                   (MS x1254 x1246 p16))) 
                                           (MS n64 y25 p16) 
                                           (forall ((i73 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 i73) 
                                                       (<= i73 (- n64 1))) 
                                                   (exists ((x1255 A) (x1256 A)) 
                                                       (and 
                                                           (MS i73 x1255 p16) 
                                                           (exists ((x1257 Int)) 
                                                               (and 
                                                                   (= x1257 (+ i73 1)) 
                                                                   (MS x1257 x1256 p16))) 
                                                           (MS0 x1255 x1256 r))))))) 
                                   (= x1244 x1246) 
                                   (= x1245 y25)))))))
         :named hyp87))
(assert (! (forall ((s118 PZA) (s217 PZA)) 
               (=> 
                   (and 
                       (seq s118) 
                       (seq s217)) 
                   (and 
                       (exists ((x1258 Int)) 
                           (length s118 x1258)) 
                       (forall ((x1259 PZA) (x1260 Int) (x1261 Int)) 
                           (=> 
                               (and 
                                   (length x1259 x1260) 
                                   (length x1259 x1261)) 
                               (= x1260 x1261))) 
                       (forall ((i74 Int)) 
                           (=> 
                               (and 
                                   (<= 1 i74) 
                                   (forall ((x1262 Int)) 
                                       (=> 
                                           (length s118 x1262) 
                                           (<= i74 x1262)))) 
                               (and 
                                   (exists ((x1263 A)) 
                                       (MS i74 x1263 s118)) 
                                   (forall ((x1264 Int) (x1265 A) (x1266 A)) 
                                       (=> 
                                           (and 
                                               (MS x1264 x1265 s118) 
                                               (MS x1264 x1266 s118)) 
                                           (= x1265 x1266)))))) 
                       (exists ((x1267 Int)) 
                           (length s217 x1267)) 
                       (forall ((i75 Int)) 
                           (=> 
                               (and 
                                   (forall ((x1268 Int)) 
                                       (=> 
                                           (length s118 x1268) 
                                           (<= (+ x1268 1) i75))) 
                                   (forall ((x1269 Int) (x1270 Int)) 
                                       (=> 
                                           (and 
                                               (length s118 x1270) 
                                               (length s217 x1269)) 
                                           (<= i75 (+ x1270 x1269))))) 
                               (and 
                                   (exists ((x1271 A) (x1272 Int)) 
                                       (and 
                                           (forall ((x1273 Int)) 
                                               (=> 
                                                   (length s118 x1273) 
                                                   (= x1272 (- i75 x1273)))) 
                                           (MS x1272 x1271 s217))) 
                                   (forall ((x1274 Int) (x1275 A) (x1276 A)) 
                                       (=> 
                                           (and 
                                               (MS x1274 x1275 s217) 
                                               (MS x1274 x1276 s217)) 
                                           (= x1275 x1276)))))))))
         :named hyp88))
(assert (! (forall ((s49 PZA)) 
               (=> 
                   (seq s49) 
                   (and 
                       (exists ((x1277 Int)) 
                           (length s49 x1277)) 
                       (forall ((x1278 PZA) (x1279 Int) (x1280 Int)) 
                           (=> 
                               (and 
                                   (length x1278 x1279) 
                                   (length x1278 x1280)) 
                               (= x1279 x1280))) 
                       (forall ((i76 Int)) 
                           (=> 
                               (and 
                                   (<= 1 i76) 
                                   (forall ((x1281 Int)) 
                                       (=> 
                                           (length s49 x1281) 
                                           (<= i76 x1281)))) 
                               (and 
                                   (exists ((x1282 A) (x1283 Int)) 
                                       (and 
                                           (forall ((x1284 Int)) 
                                               (=> 
                                                   (length s49 x1284) 
                                                   (= x1283 (+ (- x1284 i76) 1)))) 
                                           (MS x1283 x1282 s49))) 
                                   (forall ((x1285 Int) (x1286 A) (x1287 A)) 
                                       (=> 
                                           (and 
                                               (MS x1285 x1286 s49) 
                                               (MS x1285 x1287 s49)) 
                                           (= x1286 x1287)))))))))
         :named hyp89))
(assert (! (forall ((x1288 A) (y26 A) (p17 PZA) (i77 Int)) 
               (=> 
                   (and 
                       (MS1 x1288 a) 
                       (MS1 y26 a) 
                       (seq p17) 
                       (shpath x1288 y26 p17) 
                       (exists ((x1289 A)) 
                           (MS i77 x1289 p17)) 
                       (not 
                           (= i77 1)) 
                       (not 
                           (length p17 i77))) 
                   (exists ((x1290 A) (x1291 PZA)) 
                       (and 
                           (MS i77 x1290 p17) 
                           (forall ((x1292 Int) (x1293 A)) 
                               (= 
                                   (MS x1292 x1293 x1291) 
                                   (and 
                                       (MS x1292 x1293 p17) 
                                       (<= 1 x1292) 
                                       (<= x1292 i77)))) 
                           (shpath x1288 x1290 x1291)))))
         :named hyp90))
(assert (! (forall ((x1294 A) (y27 A) (p18 PZA) (i78 Int)) 
               (=> 
                   (and 
                       (MS1 x1294 a) 
                       (MS1 y27 a) 
                       (seq p18) 
                       (shpath x1294 y27 p18) 
                       (exists ((x1295 A)) 
                           (MS i78 x1295 p18)) 
                       (not 
                           (= i78 1)) 
                       (not 
                           (length p18 i78))) 
                   (and 
                       (exists ((x1296 A)) 
                           (and 
                               (MS i78 x1296 p18) 
                               (dist x1294 x1296 i78))) 
                       (exists ((x1297 A) (x1298 Int)) 
                           (and 
                               (exists ((x1299 Int)) 
                                   (and 
                                       (= x1299 (+ i78 1)) 
                                       (MS x1299 x1297 p18))) 
                               (= x1298 (+ i78 1)) 
                               (dist x1294 x1297 x1298))) 
                       (exists ((x1300 A) (x1301 A)) 
                           (and 
                               (MS i78 x1300 p18) 
                               (exists ((x1302 Int)) 
                                   (and 
                                       (= x1302 (+ i78 1)) 
                                       (MS x1302 x1301 p18))) 
                               (MS0 x1300 x1301 r))))))
         :named hyp91))
(assert (! (forall ((x1303 A) (y28 A) (p19 PZA) (z2 A)) 
               (=> 
                   (and 
                       (MS1 x1303 a) 
                       (MS1 y28 a) 
                       (seq p19) 
                       (shpath x1303 y28 p19) 
                       (exists ((x1304 Int)) 
                           (MS x1304 z2 p19)) 
                       (not 
                           (= z2 x1303)) 
                       (not 
                           (= z2 y28))) 
                   (exists ((t1 A)) 
                       (and 
                           (MS1 t1 a) 
                           (forall ((x1305 Int) (x1306 Int)) 
                               (=> 
                                   (and 
                                       (dist x1303 z2 x1306) 
                                       (dist x1303 t1 x1305)) 
                                   (< x1306 x1305))) 
                           (MS0 z2 t1 r)))))
         :named hyp92))
(assert (! (forall ((x1307 A) (y29 A) (z3 A)) 
               (=> 
                   (and 
                       (MS1 x1307 a) 
                       (MS1 y29 a) 
                       (MS1 z3 a) 
                       (not 
                           (= z3 x1307)) 
                       (not 
                           (= z3 y29)) 
                       (forall ((t2 A)) 
                           (=> 
                               (and 
                                   (MS1 t2 a) 
                                   (MS0 z3 t2 r)) 
                               (forall ((x1308 Int) (x1309 Int)) 
                                   (=> 
                                       (and 
                                           (dist x1307 t2 x1309) 
                                           (dist x1307 z3 x1308)) 
                                       (<= x1309 x1308)))))) 
                   (exists ((q1 PZA)) 
                       (and 
                           (path x1307 y29 q1) 
                           (not 
                               (exists ((x1310 Int)) 
                                   (MS x1310 z3 q1)))))))
         :named hyp93))
(assert (! (forall ((x1311 A) (x1312 A)) 
               (=> 
                   (and 
                       (MS1 x1311 a) 
                       (MS1 x1312 a)) 
                   (MS0 x1311 x1312 c)))
         :named hyp94))
(assert (! (not 
               (forall ((x1313 A)) 
                   (MS1 x1313 a)))
         :named hyp95))
(assert (! (forall ((s119 PZA) (s218 PZA) (b0 PA)) 
               (=> 
                   (and 
                       (seq s119) 
                       (seq s218) 
                       (forall ((x1314 A)) 
                           (=> 
                               (exists ((x1315 Int)) 
                                   (MS x1315 x1314 s119)) 
                               (MS1 x1314 b0))) 
                       (forall ((x1316 A)) 
                           (=> 
                               (exists ((x1317 Int)) 
                                   (MS x1317 x1316 s218)) 
                               (MS1 x1316 b0)))) 
                   (and 
                       (forall ((x1318 Int) (x1319 A)) 
                           (=> 
                               (exists ((x1320 PZA)) 
                                   (and 
                                       (cnc s119 s218 x1320) 
                                       (MS x1318 x1319 x1320))) 
                               (and 
                                   (<= 1 x1318) 
                                   (forall ((x1321 Int) (x1322 Int)) 
                                       (=> 
                                           (and 
                                               (length s119 x1322) 
                                               (length s218 x1321)) 
                                           (<= x1318 (+ x1322 x1321)))) 
                                   (MS1 x1319 b0)))) 
                       (forall ((x1323 Int) (x1324 A) (x1325 A)) 
                           (=> 
                               (and 
                                   (exists ((x1326 PZA)) 
                                       (and 
                                           (cnc s119 s218 x1326) 
                                           (MS x1323 x1324 x1326))) 
                                   (exists ((x1327 PZA)) 
                                       (and 
                                           (cnc s119 s218 x1327) 
                                           (MS x1323 x1325 x1327)))) 
                               (= x1324 x1325))) 
                       (forall ((x1328 Int)) 
                           (=> 
                               (and 
                                   (<= 1 x1328) 
                                   (forall ((x1329 Int) (x1330 Int)) 
                                       (=> 
                                           (and 
                                               (length s119 x1330) 
                                               (length s218 x1329)) 
                                           (<= x1328 (+ x1330 x1329))))) 
                               (exists ((x1331 A) (x1332 PZA)) 
                                   (and 
                                       (cnc s119 s218 x1332) 
                                       (MS x1328 x1331 x1332))))))))
         :named hyp96))
(assert (! (forall ((x1333 A) (x1334 A) (x1335 PZA)) 
               (= 
                   (path x1333 x1334 x1335) 
                   (exists ((x1336 A) (y30 A) (p20 PZA)) 
                       (and 
                           (seq p20) 
                           (forall ((x1337 A)) 
                               (=> 
                                   (exists ((x1338 Int)) 
                                       (MS x1338 x1337 p20)) 
                                   (MS1 x1337 a))) 
                           (forall ((x1339 Int)) 
                               (=> 
                                   (length p20 x1339) 
                                   (< 1 x1339))) 
                           (exists ((x1340 Int)) 
                               (and 
                                   (= x1340 1) 
                                   (MS x1340 x1336 p20))) 
                           (exists ((x1341 Int)) 
                               (and 
                                   (length p20 x1341) 
                                   (MS x1341 y30 p20))) 
                           (forall ((i79 Int)) 
                               (=> 
                                   (and 
                                       (<= 1 i79) 
                                       (forall ((x1342 Int)) 
                                           (=> 
                                               (length p20 x1342) 
                                               (<= i79 (- x1342 1))))) 
                                   (exists ((x1343 A) (x1344 A)) 
                                       (and 
                                           (MS i79 x1343 p20) 
                                           (exists ((x1345 Int)) 
                                               (and 
                                                   (= x1345 (+ i79 1)) 
                                                   (MS x1345 x1344 p20))) 
                                           (MS0 x1343 x1344 r))))) 
                           (= x1333 x1336) 
                           (= x1334 y30) 
                           (forall ((x1346 Int) (x1347 A)) 
                               (= 
                                   (MS x1346 x1347 x1335) 
                                   (MS x1346 x1347 p20)))))))
         :named hyp97))
(assert (! (forall ((x1348 A) (y31 A) (p21 PZA)) 
               (=> 
                   (and 
                       (seq p21) 
                       (forall ((x1349 A)) 
                           (=> 
                               (exists ((x1350 Int)) 
                                   (MS x1350 x1349 p21)) 
                               (MS1 x1349 a)))) 
                   (and 
                       (exists ((x1351 Int)) 
                           (length p21 x1351)) 
                       (forall ((x1352 PZA) (x1353 Int) (x1354 Int)) 
                           (=> 
                               (and 
                                   (length x1352 x1353) 
                                   (length x1352 x1354)) 
                               (= x1353 x1354))) 
                       (=> 
                           (forall ((x1355 Int)) 
                               (=> 
                                   (length p21 x1355) 
                                   (< 1 x1355))) 
                           (and 
                               (exists ((x1356 A) (x1357 Int)) 
                                   (and 
                                       (= x1357 1) 
                                       (MS x1357 x1356 p21))) 
                               (forall ((x1358 Int) (x1359 A) (x1360 A)) 
                                   (=> 
                                       (and 
                                           (MS x1358 x1359 p21) 
                                           (MS x1358 x1360 p21)) 
                                       (= x1359 x1360))) 
                               (=> 
                                   (exists ((x1361 Int)) 
                                       (and 
                                           (= x1361 1) 
                                           (MS x1361 x1348 p21))) 
                                   (and 
                                       (exists ((x1362 A) (x1363 Int)) 
                                           (and 
                                               (length p21 x1363) 
                                               (MS x1363 x1362 p21))) 
                                       (=> 
                                           (exists ((x1364 Int)) 
                                               (and 
                                                   (length p21 x1364) 
                                                   (MS x1364 y31 p21))) 
                                           (forall ((i80 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 i80) 
                                                       (forall ((x1365 Int)) 
                                                           (=> 
                                                               (length p21 x1365) 
                                                               (<= i80 (- x1365 1))))) 
                                                   (and 
                                                       (exists ((x1366 A)) 
                                                           (MS i80 x1366 p21)) 
                                                       (exists ((x1367 A) (x1368 Int)) 
                                                           (and 
                                                               (= x1368 (+ i80 1)) 
                                                               (MS x1368 x1367 p21))))))))))))))
         :named hyp98))
(assert (! (MS1 y1 a)
         :named hyp99))
(assert (! (MS1 y2 a)
         :named hyp100))
(assert (! (MS1 x a)
         :named hyp101))
(assert (! (MS1 x1 a)
         :named hyp102))
(assert (! (path x y1 q)
         :named hyp103))
(assert (! (path y2 x1 p)
         :named hyp104))
(assert (! (MS0 x1 x r)
         :named hyp105))
(assert (! (and 
               (forall ((x1369 PZA) (x1370 PZA) (x1371 PZA)) 
                   (=> 
                       (cnc x1369 x1370 x1371) 
                       (and 
                           (exists ((s50 PZA)) 
                               (and 
                                   (exists ((n65 Int)) 
                                       (and 
                                           (<= 0 n65) 
                                           (forall ((x1372 Int) (x1373 A)) 
                                               (=> 
                                                   (MS x1372 x1373 s50) 
                                                   (and 
                                                       (<= 1 x1372) 
                                                       (<= x1372 n65)))) 
                                           (forall ((x1374 Int) (x1375 A) (x1376 A)) 
                                               (=> 
                                                   (and 
                                                       (MS x1374 x1375 s50) 
                                                       (MS x1374 x1376 s50)) 
                                                   (= x1375 x1376))) 
                                           (forall ((x1377 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x1377) 
                                                       (<= x1377 n65)) 
                                                   (exists ((x1378 A)) 
                                                       (MS x1377 x1378 s50)))))) 
                                   (forall ((x1379 Int) (x1380 A)) 
                                       (= 
                                           (MS x1379 x1380 x1369) 
                                           (MS x1379 x1380 s50))))) 
                           (exists ((s51 PZA)) 
                               (and 
                                   (exists ((n66 Int)) 
                                       (and 
                                           (<= 0 n66) 
                                           (forall ((x1381 Int) (x1382 A)) 
                                               (=> 
                                                   (MS x1381 x1382 s51) 
                                                   (and 
                                                       (<= 1 x1381) 
                                                       (<= x1381 n66)))) 
                                           (forall ((x1383 Int) (x1384 A) (x1385 A)) 
                                               (=> 
                                                   (and 
                                                       (MS x1383 x1384 s51) 
                                                       (MS x1383 x1385 s51)) 
                                                   (= x1384 x1385))) 
                                           (forall ((x1386 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x1386) 
                                                       (<= x1386 n66)) 
                                                   (exists ((x1387 A)) 
                                                       (MS x1386 x1387 s51)))))) 
                                   (forall ((x1388 Int) (x1389 A)) 
                                       (= 
                                           (MS x1388 x1389 x1370) 
                                           (MS x1388 x1389 s51))))) 
                           (exists ((s52 PZA)) 
                               (and 
                                   (exists ((n67 Int)) 
                                       (and 
                                           (<= 0 n67) 
                                           (forall ((x1390 Int) (x1391 A)) 
                                               (=> 
                                                   (MS x1390 x1391 s52) 
                                                   (and 
                                                       (<= 1 x1390) 
                                                       (<= x1390 n67)))) 
                                           (forall ((x1392 Int) (x1393 A) (x1394 A)) 
                                               (=> 
                                                   (and 
                                                       (MS x1392 x1393 s52) 
                                                       (MS x1392 x1394 s52)) 
                                                   (= x1393 x1394))) 
                                           (forall ((x1395 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x1395) 
                                                       (<= x1395 n67)) 
                                                   (exists ((x1396 A)) 
                                                       (MS x1395 x1396 s52)))))) 
                                   (forall ((x1397 Int) (x1398 A)) 
                                       (= 
                                           (MS x1397 x1398 x1371) 
                                           (MS x1397 x1398 s52)))))))) 
               (forall ((x1399 PZA) (x1400 PZA) (x1401 PZA) (x1402 PZA)) 
                   (=> 
                       (and 
                           (cnc x1399 x1400 x1401) 
                           (cnc x1399 x1400 x1402)) 
                       (forall ((x1403 Int) (x1404 A)) 
                           (= 
                               (MS x1403 x1404 x1401) 
                               (MS x1403 x1404 x1402))))) 
               (forall ((x1405 PZA) (x1406 PZA)) 
                   (=> 
                       (and 
                           (exists ((s53 PZA)) 
                               (and 
                                   (exists ((n68 Int)) 
                                       (and 
                                           (<= 0 n68) 
                                           (forall ((x1407 Int) (x1408 A)) 
                                               (=> 
                                                   (MS x1407 x1408 s53) 
                                                   (and 
                                                       (<= 1 x1407) 
                                                       (<= x1407 n68)))) 
                                           (forall ((x1409 Int) (x1410 A) (x1411 A)) 
                                               (=> 
                                                   (and 
                                                       (MS x1409 x1410 s53) 
                                                       (MS x1409 x1411 s53)) 
                                                   (= x1410 x1411))) 
                                           (forall ((x1412 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x1412) 
                                                       (<= x1412 n68)) 
                                                   (exists ((x1413 A)) 
                                                       (MS x1412 x1413 s53)))))) 
                                   (forall ((x1414 Int) (x1415 A)) 
                                       (= 
                                           (MS x1414 x1415 x1405) 
                                           (MS x1414 x1415 s53))))) 
                           (exists ((s54 PZA)) 
                               (and 
                                   (exists ((n69 Int)) 
                                       (and 
                                           (<= 0 n69) 
                                           (forall ((x1416 Int) (x1417 A)) 
                                               (=> 
                                                   (MS x1416 x1417 s54) 
                                                   (and 
                                                       (<= 1 x1416) 
                                                       (<= x1416 n69)))) 
                                           (forall ((x1418 Int) (x1419 A) (x1420 A)) 
                                               (=> 
                                                   (and 
                                                       (MS x1418 x1419 s54) 
                                                       (MS x1418 x1420 s54)) 
                                                   (= x1419 x1420))) 
                                           (forall ((x1421 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x1421) 
                                                       (<= x1421 n69)) 
                                                   (exists ((x1422 A)) 
                                                       (MS x1421 x1422 s54)))))) 
                                   (forall ((x1423 Int) (x1424 A)) 
                                       (= 
                                           (MS x1423 x1424 x1406) 
                                           (MS x1423 x1424 s54)))))) 
                       (exists ((x1425 PZA)) 
                           (cnc x1405 x1406 x1425)))))
         :named hyp106))
(assert (! (and 
               (forall ((x1426 PZA) (x1427 PZA)) 
                   (=> 
                       (reverse x1426 x1427) 
                       (and 
                           (exists ((s55 PZA)) 
                               (and 
                                   (exists ((n70 Int)) 
                                       (and 
                                           (<= 0 n70) 
                                           (forall ((x1428 Int) (x1429 A)) 
                                               (=> 
                                                   (MS x1428 x1429 s55) 
                                                   (and 
                                                       (<= 1 x1428) 
                                                       (<= x1428 n70)))) 
                                           (forall ((x1430 Int) (x1431 A) (x1432 A)) 
                                               (=> 
                                                   (and 
                                                       (MS x1430 x1431 s55) 
                                                       (MS x1430 x1432 s55)) 
                                                   (= x1431 x1432))) 
                                           (forall ((x1433 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x1433) 
                                                       (<= x1433 n70)) 
                                                   (exists ((x1434 A)) 
                                                       (MS x1433 x1434 s55)))))) 
                                   (forall ((x1435 Int) (x1436 A)) 
                                       (= 
                                           (MS x1435 x1436 x1426) 
                                           (MS x1435 x1436 s55))))) 
                           (exists ((s56 PZA)) 
                               (and 
                                   (exists ((n71 Int)) 
                                       (and 
                                           (<= 0 n71) 
                                           (forall ((x1437 Int) (x1438 A)) 
                                               (=> 
                                                   (MS x1437 x1438 s56) 
                                                   (and 
                                                       (<= 1 x1437) 
                                                       (<= x1437 n71)))) 
                                           (forall ((x1439 Int) (x1440 A) (x1441 A)) 
                                               (=> 
                                                   (and 
                                                       (MS x1439 x1440 s56) 
                                                       (MS x1439 x1441 s56)) 
                                                   (= x1440 x1441))) 
                                           (forall ((x1442 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x1442) 
                                                       (<= x1442 n71)) 
                                                   (exists ((x1443 A)) 
                                                       (MS x1442 x1443 s56)))))) 
                                   (forall ((x1444 Int) (x1445 A)) 
                                       (= 
                                           (MS x1444 x1445 x1427) 
                                           (MS x1444 x1445 s56)))))))) 
               (forall ((x1446 PZA) (x1447 PZA) (x1448 PZA)) 
                   (=> 
                       (and 
                           (reverse x1446 x1447) 
                           (reverse x1446 x1448)) 
                       (forall ((x1449 Int) (x1450 A)) 
                           (= 
                               (MS x1449 x1450 x1447) 
                               (MS x1449 x1450 x1448))))) 
               (forall ((x1451 PZA)) 
                   (=> 
                       (exists ((s57 PZA)) 
                           (and 
                               (exists ((n72 Int)) 
                                   (and 
                                       (<= 0 n72) 
                                       (forall ((x1452 Int) (x1453 A)) 
                                           (=> 
                                               (MS x1452 x1453 s57) 
                                               (and 
                                                   (<= 1 x1452) 
                                                   (<= x1452 n72)))) 
                                       (forall ((x1454 Int) (x1455 A) (x1456 A)) 
                                           (=> 
                                               (and 
                                                   (MS x1454 x1455 s57) 
                                                   (MS x1454 x1456 s57)) 
                                               (= x1455 x1456))) 
                                       (forall ((x1457 Int)) 
                                           (=> 
                                               (and 
                                                   (<= 1 x1457) 
                                                   (<= x1457 n72)) 
                                               (exists ((x1458 A)) 
                                                   (MS x1457 x1458 s57)))))) 
                               (forall ((x1459 Int) (x1460 A)) 
                                   (= 
                                       (MS x1459 x1460 x1451) 
                                       (MS x1459 x1460 s57))))) 
                       (exists ((x1461 PZA)) 
                           (reverse x1451 x1461)))))
         :named hyp107))
(assert (! (forall ((s120 PZA) (s219 PZA)) 
               (=> 
                   (and 
                       (exists ((n73 Int)) 
                           (and 
                               (<= 0 n73) 
                               (forall ((x1462 Int) (x1463 A)) 
                                   (=> 
                                       (MS x1462 x1463 s120) 
                                       (and 
                                           (<= 1 x1462) 
                                           (<= x1462 n73)))) 
                               (forall ((x1464 Int) (x1465 A) (x1466 A)) 
                                   (=> 
                                       (and 
                                           (MS x1464 x1465 s120) 
                                           (MS x1464 x1466 s120)) 
                                       (= x1465 x1466))) 
                               (forall ((x1467 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x1467) 
                                           (<= x1467 n73)) 
                                       (exists ((x1468 A)) 
                                           (MS x1467 x1468 s120)))))) 
                       (exists ((n74 Int)) 
                           (and 
                               (<= 0 n74) 
                               (forall ((x1469 Int) (x1470 A)) 
                                   (=> 
                                       (MS x1469 x1470 s219) 
                                       (and 
                                           (<= 1 x1469) 
                                           (<= x1469 n74)))) 
                               (forall ((x1471 Int) (x1472 A) (x1473 A)) 
                                   (=> 
                                       (and 
                                           (MS x1471 x1472 s219) 
                                           (MS x1471 x1473 s219)) 
                                       (= x1472 x1473))) 
                               (forall ((x1474 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x1474) 
                                           (<= x1474 n74)) 
                                       (exists ((x1475 A)) 
                                           (MS x1474 x1475 s219))))))) 
                   (exists ((x1476 PZA) (x1477 Int)) 
                       (and 
                           (cnc s120 s219 x1476) 
                           (forall ((x1478 Int) (x1479 Int)) 
                               (=> 
                                   (and 
                                       (length s120 x1479) 
                                       (length s219 x1478)) 
                                   (= x1477 (+ x1479 x1478)))) 
                           (length x1476 x1477)))))
         :named hyp108))
(assert (! (forall ((s121 PZA) (s220 PZA)) 
               (=> 
                   (and 
                       (exists ((n75 Int)) 
                           (and 
                               (<= 0 n75) 
                               (forall ((x1480 Int) (x1481 A)) 
                                   (=> 
                                       (MS x1480 x1481 s121) 
                                       (and 
                                           (<= 1 x1480) 
                                           (<= x1480 n75)))) 
                               (forall ((x1482 Int) (x1483 A) (x1484 A)) 
                                   (=> 
                                       (and 
                                           (MS x1482 x1483 s121) 
                                           (MS x1482 x1484 s121)) 
                                       (= x1483 x1484))) 
                               (forall ((x1485 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x1485) 
                                           (<= x1485 n75)) 
                                       (exists ((x1486 A)) 
                                           (MS x1485 x1486 s121)))))) 
                       (exists ((n76 Int)) 
                           (and 
                               (<= 0 n76) 
                               (forall ((x1487 Int) (x1488 A)) 
                                   (=> 
                                       (MS x1487 x1488 s220) 
                                       (and 
                                           (<= 1 x1487) 
                                           (<= x1487 n76)))) 
                               (forall ((x1489 Int) (x1490 A) (x1491 A)) 
                                   (=> 
                                       (and 
                                           (MS x1489 x1490 s220) 
                                           (MS x1489 x1491 s220)) 
                                       (= x1490 x1491))) 
                               (forall ((x1492 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x1492) 
                                           (<= x1492 n76)) 
                                       (exists ((x1493 A)) 
                                           (MS x1492 x1493 s220))))))) 
                   (forall ((x1494 Int)) 
                       (= 
                           (exists ((x1495 A) (x1496 PZA)) 
                               (and 
                                   (cnc s121 s220 x1496) 
                                   (MS x1494 x1495 x1496))) 
                           (and 
                               (<= 1 x1494) 
                               (forall ((x1497 Int) (x1498 Int)) 
                                   (=> 
                                       (and 
                                           (length s121 x1498) 
                                           (length s220 x1497)) 
                                       (<= x1494 (+ x1498 x1497)))))))))
         :named hyp109))
(assert (! (forall ((s122 PZA) (s221 PZA)) 
               (=> 
                   (and 
                       (exists ((n77 Int)) 
                           (and 
                               (<= 0 n77) 
                               (forall ((x1499 Int) (x1500 A)) 
                                   (=> 
                                       (MS x1499 x1500 s122) 
                                       (and 
                                           (<= 1 x1499) 
                                           (<= x1499 n77)))) 
                               (forall ((x1501 Int) (x1502 A) (x1503 A)) 
                                   (=> 
                                       (and 
                                           (MS x1501 x1502 s122) 
                                           (MS x1501 x1503 s122)) 
                                       (= x1502 x1503))) 
                               (forall ((x1504 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x1504) 
                                           (<= x1504 n77)) 
                                       (exists ((x1505 A)) 
                                           (MS x1504 x1505 s122)))))) 
                       (exists ((n78 Int)) 
                           (and 
                               (<= 0 n78) 
                               (forall ((x1506 Int) (x1507 A)) 
                                   (=> 
                                       (MS x1506 x1507 s221) 
                                       (and 
                                           (<= 1 x1506) 
                                           (<= x1506 n78)))) 
                               (forall ((x1508 Int) (x1509 A) (x1510 A)) 
                                   (=> 
                                       (and 
                                           (MS x1508 x1509 s221) 
                                           (MS x1508 x1510 s221)) 
                                       (= x1509 x1510))) 
                               (forall ((x1511 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x1511) 
                                           (<= x1511 n78)) 
                                       (exists ((x1512 A)) 
                                           (MS x1511 x1512 s221))))))) 
                   (forall ((x1513 A)) 
                       (= 
                           (exists ((x1514 Int) (x1515 PZA)) 
                               (and 
                                   (cnc s122 s221 x1515) 
                                   (MS x1514 x1513 x1515))) 
                           (or 
                               (exists ((x1516 Int)) 
                                   (MS x1516 x1513 s122)) 
                               (exists ((x1517 Int)) 
                                   (MS x1517 x1513 s221)))))))
         :named hyp110))
(assert (! (forall ((s123 PZA) (s222 PZA) (i81 Int)) 
               (=> 
                   (and 
                       (exists ((n79 Int)) 
                           (and 
                               (<= 0 n79) 
                               (forall ((x1518 Int) (x1519 A)) 
                                   (=> 
                                       (MS x1518 x1519 s123) 
                                       (and 
                                           (<= 1 x1518) 
                                           (<= x1518 n79)))) 
                               (forall ((x1520 Int) (x1521 A) (x1522 A)) 
                                   (=> 
                                       (and 
                                           (MS x1520 x1521 s123) 
                                           (MS x1520 x1522 s123)) 
                                       (= x1521 x1522))) 
                               (forall ((x1523 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x1523) 
                                           (<= x1523 n79)) 
                                       (exists ((x1524 A)) 
                                           (MS x1523 x1524 s123)))))) 
                       (exists ((n80 Int)) 
                           (and 
                               (<= 0 n80) 
                               (forall ((x1525 Int) (x1526 A)) 
                                   (=> 
                                       (MS x1525 x1526 s222) 
                                       (and 
                                           (<= 1 x1525) 
                                           (<= x1525 n80)))) 
                               (forall ((x1527 Int) (x1528 A) (x1529 A)) 
                                   (=> 
                                       (and 
                                           (MS x1527 x1528 s222) 
                                           (MS x1527 x1529 s222)) 
                                       (= x1528 x1529))) 
                               (forall ((x1530 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x1530) 
                                           (<= x1530 n80)) 
                                       (exists ((x1531 A)) 
                                           (MS x1530 x1531 s222)))))) 
                       (<= 1 i81) 
                       (forall ((x1532 Int)) 
                           (=> 
                               (length s123 x1532) 
                               (<= i81 x1532)))) 
                   (exists ((x1533 PZA)) 
                       (and 
                           (cnc s123 s222 x1533) 
                           (exists ((x1534 A)) 
                               (and 
                                   (MS i81 x1534 s123) 
                                   (MS i81 x1534 x1533)))))))
         :named hyp111))
(assert (! (forall ((s124 PZA) (s223 PZA) (i82 Int)) 
               (=> 
                   (and 
                       (exists ((n81 Int)) 
                           (and 
                               (<= 0 n81) 
                               (forall ((x1535 Int) (x1536 A)) 
                                   (=> 
                                       (MS x1535 x1536 s124) 
                                       (and 
                                           (<= 1 x1535) 
                                           (<= x1535 n81)))) 
                               (forall ((x1537 Int) (x1538 A) (x1539 A)) 
                                   (=> 
                                       (and 
                                           (MS x1537 x1538 s124) 
                                           (MS x1537 x1539 s124)) 
                                       (= x1538 x1539))) 
                               (forall ((x1540 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x1540) 
                                           (<= x1540 n81)) 
                                       (exists ((x1541 A)) 
                                           (MS x1540 x1541 s124)))))) 
                       (exists ((n82 Int)) 
                           (and 
                               (<= 0 n82) 
                               (forall ((x1542 Int) (x1543 A)) 
                                   (=> 
                                       (MS x1542 x1543 s223) 
                                       (and 
                                           (<= 1 x1542) 
                                           (<= x1542 n82)))) 
                               (forall ((x1544 Int) (x1545 A) (x1546 A)) 
                                   (=> 
                                       (and 
                                           (MS x1544 x1545 s223) 
                                           (MS x1544 x1546 s223)) 
                                       (= x1545 x1546))) 
                               (forall ((x1547 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x1547) 
                                           (<= x1547 n82)) 
                                       (exists ((x1548 A)) 
                                           (MS x1547 x1548 s223)))))) 
                       (forall ((x1549 Int)) 
                           (=> 
                               (length s124 x1549) 
                               (<= (+ x1549 1) i82))) 
                       (forall ((x1550 Int) (x1551 Int)) 
                           (=> 
                               (and 
                                   (length s124 x1551) 
                                   (length s223 x1550)) 
                               (<= i82 (+ x1551 x1550))))) 
                   (exists ((x1552 PZA)) 
                       (and 
                           (cnc s124 s223 x1552) 
                           (exists ((x1553 A)) 
                               (and 
                                   (exists ((x1554 Int)) 
                                       (and 
                                           (forall ((x1555 Int)) 
                                               (=> 
                                                   (length s124 x1555) 
                                                   (= x1554 (- i82 x1555)))) 
                                           (MS x1554 x1553 s223))) 
                                   (MS i82 x1553 x1552)))))))
         :named hyp112))
(assert (! (forall ((s58 PZA)) 
               (=> 
                   (exists ((n83 Int)) 
                       (and 
                           (<= 0 n83) 
                           (forall ((x1556 Int) (x1557 A)) 
                               (=> 
                                   (MS x1556 x1557 s58) 
                                   (and 
                                       (<= 1 x1556) 
                                       (<= x1556 n83)))) 
                           (forall ((x1558 Int) (x1559 A) (x1560 A)) 
                               (=> 
                                   (and 
                                       (MS x1558 x1559 s58) 
                                       (MS x1558 x1560 s58)) 
                                   (= x1559 x1560))) 
                           (forall ((x1561 Int)) 
                               (=> 
                                   (and 
                                       (<= 1 x1561) 
                                       (<= x1561 n83)) 
                                   (exists ((x1562 A)) 
                                       (MS x1561 x1562 s58)))))) 
                   (exists ((x1563 PZA) (x1564 Int)) 
                       (and 
                           (reverse s58 x1563) 
                           (length s58 x1564) 
                           (length x1563 x1564)))))
         :named hyp113))
(assert (! (forall ((s59 PZA)) 
               (=> 
                   (exists ((n84 Int)) 
                       (and 
                           (<= 0 n84) 
                           (forall ((x1565 Int) (x1566 A)) 
                               (=> 
                                   (MS x1565 x1566 s59) 
                                   (and 
                                       (<= 1 x1565) 
                                       (<= x1565 n84)))) 
                           (forall ((x1567 Int) (x1568 A) (x1569 A)) 
                               (=> 
                                   (and 
                                       (MS x1567 x1568 s59) 
                                       (MS x1567 x1569 s59)) 
                                   (= x1568 x1569))) 
                           (forall ((x1570 Int)) 
                               (=> 
                                   (and 
                                       (<= 1 x1570) 
                                       (<= x1570 n84)) 
                                   (exists ((x1571 A)) 
                                       (MS x1570 x1571 s59)))))) 
                   (forall ((x1572 A)) 
                       (= 
                           (exists ((x1573 Int) (x1574 PZA)) 
                               (and 
                                   (reverse s59 x1574) 
                                   (MS x1573 x1572 x1574))) 
                           (exists ((x1575 Int)) 
                               (MS x1575 x1572 s59))))))
         :named hyp114))
(assert (! (forall ((s60 PZA)) 
               (=> 
                   (exists ((n85 Int)) 
                       (and 
                           (<= 0 n85) 
                           (forall ((x1576 Int) (x1577 A)) 
                               (=> 
                                   (MS x1576 x1577 s60) 
                                   (and 
                                       (<= 1 x1576) 
                                       (<= x1576 n85)))) 
                           (forall ((x1578 Int) (x1579 A) (x1580 A)) 
                               (=> 
                                   (and 
                                       (MS x1578 x1579 s60) 
                                       (MS x1578 x1580 s60)) 
                                   (= x1579 x1580))) 
                           (forall ((x1581 Int)) 
                               (=> 
                                   (and 
                                       (<= 1 x1581) 
                                       (<= x1581 n85)) 
                                   (exists ((x1582 A)) 
                                       (MS x1581 x1582 s60)))))) 
                   (exists ((x1583 PZA)) 
                       (and 
                           (reverse s60 x1583) 
                           (reverse x1583 s60)))))
         :named hyp115))
(assert (! (forall ((x1584 A) (y32 A) (p22 PZA) (i83 Int)) 
               (=> 
                   (and 
                       (MS1 x1584 a) 
                       (MS1 y32 a) 
                       (exists ((n86 Int)) 
                           (and 
                               (<= 0 n86) 
                               (forall ((x1585 Int) (x1586 A)) 
                                   (=> 
                                       (MS x1585 x1586 p22) 
                                       (and 
                                           (<= 1 x1585) 
                                           (<= x1585 n86)))) 
                               (forall ((x1587 Int) (x1588 A) (x1589 A)) 
                                   (=> 
                                       (and 
                                           (MS x1587 x1588 p22) 
                                           (MS x1587 x1589 p22)) 
                                       (= x1588 x1589))) 
                               (forall ((x1590 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x1590) 
                                           (<= x1590 n86)) 
                                       (exists ((x1591 A)) 
                                           (MS x1590 x1591 p22)))))) 
                       (shpath x1584 y32 p22) 
                       (exists ((x1592 A)) 
                           (MS i83 x1592 p22)) 
                       (not 
                           (= i83 1)) 
                       (not 
                           (length p22 i83))) 
                   (exists ((x1593 A) (x1594 PZA)) 
                       (and 
                           (MS i83 x1593 p22) 
                           (forall ((x1595 Int) (x1596 A)) 
                               (= 
                                   (MS x1595 x1596 x1594) 
                                   (and 
                                       (MS x1595 x1596 p22) 
                                       (<= 1 x1595) 
                                       (<= x1595 i83)))) 
                           (shpath x1584 x1593 x1594)))))
         :named hyp116))
(assert (! (forall ((x1597 A) (y33 A) (p23 PZA) (i84 Int)) 
               (=> 
                   (and 
                       (MS1 x1597 a) 
                       (MS1 y33 a) 
                       (exists ((n87 Int)) 
                           (and 
                               (<= 0 n87) 
                               (forall ((x1598 Int) (x1599 A)) 
                                   (=> 
                                       (MS x1598 x1599 p23) 
                                       (and 
                                           (<= 1 x1598) 
                                           (<= x1598 n87)))) 
                               (forall ((x1600 Int) (x1601 A) (x1602 A)) 
                                   (=> 
                                       (and 
                                           (MS x1600 x1601 p23) 
                                           (MS x1600 x1602 p23)) 
                                       (= x1601 x1602))) 
                               (forall ((x1603 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x1603) 
                                           (<= x1603 n87)) 
                                       (exists ((x1604 A)) 
                                           (MS x1603 x1604 p23)))))) 
                       (shpath x1597 y33 p23) 
                       (exists ((x1605 A)) 
                           (MS i84 x1605 p23)) 
                       (not 
                           (= i84 1)) 
                       (not 
                           (length p23 i84))) 
                   (and 
                       (exists ((x1606 A)) 
                           (and 
                               (MS i84 x1606 p23) 
                               (dist x1597 x1606 i84))) 
                       (exists ((x1607 A) (x1608 Int)) 
                           (and 
                               (exists ((x1609 Int)) 
                                   (and 
                                       (= x1609 (+ i84 1)) 
                                       (MS x1609 x1607 p23))) 
                               (= x1608 (+ i84 1)) 
                               (dist x1597 x1607 x1608))) 
                       (exists ((x1610 A) (x1611 A)) 
                           (and 
                               (MS i84 x1610 p23) 
                               (exists ((x1612 Int)) 
                                   (and 
                                       (= x1612 (+ i84 1)) 
                                       (MS x1612 x1611 p23))) 
                               (MS0 x1610 x1611 r))))))
         :named hyp117))
(assert (! (forall ((x1613 A) (y34 A) (p24 PZA) (z4 A)) 
               (=> 
                   (and 
                       (MS1 x1613 a) 
                       (MS1 y34 a) 
                       (exists ((n88 Int)) 
                           (and 
                               (<= 0 n88) 
                               (forall ((x1614 Int) (x1615 A)) 
                                   (=> 
                                       (MS x1614 x1615 p24) 
                                       (and 
                                           (<= 1 x1614) 
                                           (<= x1614 n88)))) 
                               (forall ((x1616 Int) (x1617 A) (x1618 A)) 
                                   (=> 
                                       (and 
                                           (MS x1616 x1617 p24) 
                                           (MS x1616 x1618 p24)) 
                                       (= x1617 x1618))) 
                               (forall ((x1619 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x1619) 
                                           (<= x1619 n88)) 
                                       (exists ((x1620 A)) 
                                           (MS x1619 x1620 p24)))))) 
                       (shpath x1613 y34 p24) 
                       (exists ((x1621 Int)) 
                           (MS x1621 z4 p24)) 
                       (not 
                           (= z4 x1613)) 
                       (not 
                           (= z4 y34))) 
                   (exists ((t3 A)) 
                       (and 
                           (MS1 t3 a) 
                           (forall ((x1622 Int) (x1623 Int)) 
                               (=> 
                                   (and 
                                       (dist x1613 z4 x1623) 
                                       (dist x1613 t3 x1622)) 
                                   (< x1623 x1622))) 
                           (MS0 z4 t3 r)))))
         :named hyp118))
(assert (! (forall ((s125 PZA) (s224 PZA) (b1 PA)) 
               (=> 
                   (and 
                       (exists ((n89 Int)) 
                           (and 
                               (<= 0 n89) 
                               (forall ((x1624 Int) (x1625 A)) 
                                   (=> 
                                       (MS x1624 x1625 s125) 
                                       (and 
                                           (<= 1 x1624) 
                                           (<= x1624 n89)))) 
                               (forall ((x1626 Int) (x1627 A) (x1628 A)) 
                                   (=> 
                                       (and 
                                           (MS x1626 x1627 s125) 
                                           (MS x1626 x1628 s125)) 
                                       (= x1627 x1628))) 
                               (forall ((x1629 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x1629) 
                                           (<= x1629 n89)) 
                                       (exists ((x1630 A)) 
                                           (MS x1629 x1630 s125)))))) 
                       (exists ((n90 Int)) 
                           (and 
                               (<= 0 n90) 
                               (forall ((x1631 Int) (x1632 A)) 
                                   (=> 
                                       (MS x1631 x1632 s224) 
                                       (and 
                                           (<= 1 x1631) 
                                           (<= x1631 n90)))) 
                               (forall ((x1633 Int) (x1634 A) (x1635 A)) 
                                   (=> 
                                       (and 
                                           (MS x1633 x1634 s224) 
                                           (MS x1633 x1635 s224)) 
                                       (= x1634 x1635))) 
                               (forall ((x1636 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x1636) 
                                           (<= x1636 n90)) 
                                       (exists ((x1637 A)) 
                                           (MS x1636 x1637 s224)))))) 
                       (forall ((x1638 A)) 
                           (=> 
                               (exists ((x1639 Int)) 
                                   (MS x1639 x1638 s125)) 
                               (MS1 x1638 b1))) 
                       (forall ((x1640 A)) 
                           (=> 
                               (exists ((x1641 Int)) 
                                   (MS x1641 x1640 s224)) 
                               (MS1 x1640 b1)))) 
                   (and 
                       (forall ((x1642 Int) (x1643 A)) 
                           (=> 
                               (exists ((x1644 PZA)) 
                                   (and 
                                       (cnc s125 s224 x1644) 
                                       (MS x1642 x1643 x1644))) 
                               (and 
                                   (<= 1 x1642) 
                                   (forall ((x1645 Int) (x1646 Int)) 
                                       (=> 
                                           (and 
                                               (length s125 x1646) 
                                               (length s224 x1645)) 
                                           (<= x1642 (+ x1646 x1645)))) 
                                   (MS1 x1643 b1)))) 
                       (forall ((x1647 Int) (x1648 A) (x1649 A)) 
                           (=> 
                               (and 
                                   (exists ((x1650 PZA)) 
                                       (and 
                                           (cnc s125 s224 x1650) 
                                           (MS x1647 x1648 x1650))) 
                                   (exists ((x1651 PZA)) 
                                       (and 
                                           (cnc s125 s224 x1651) 
                                           (MS x1647 x1649 x1651)))) 
                               (= x1648 x1649))) 
                       (forall ((x1652 Int)) 
                           (=> 
                               (and 
                                   (<= 1 x1652) 
                                   (forall ((x1653 Int) (x1654 Int)) 
                                       (=> 
                                           (and 
                                               (length s125 x1654) 
                                               (length s224 x1653)) 
                                           (<= x1652 (+ x1654 x1653))))) 
                               (exists ((x1655 A) (x1656 PZA)) 
                                   (and 
                                       (cnc s125 s224 x1656) 
                                       (MS x1652 x1655 x1656))))))))
         :named hyp119))
(assert (! (forall ((x1657 A) (y35 A)) 
               (=> 
                   (and 
                       (MS1 x1657 a) 
                       (MS1 y35 a)) 
                   (exists ((p25 PZA)) 
                       (and 
                           (path x1657 y35 p25) 
                           (exists ((x1658 Int)) 
                               (and 
                                   (length p25 x1658) 
                                   (dist x1657 y35 x1658)))))))
         :named hyp120))
(assert (! (forall ((x1659 A) (y36 A) (p26 PZA) (i85 Int)) 
               (=> 
                   (and 
                       (MS1 x1659 a) 
                       (MS1 y36 a) 
                       (exists ((n91 Int)) 
                           (and 
                               (<= 0 n91) 
                               (forall ((x1660 Int) (x1661 A)) 
                                   (=> 
                                       (MS x1660 x1661 p26) 
                                       (and 
                                           (<= 1 x1660) 
                                           (<= x1660 n91)))) 
                               (forall ((x1662 Int) (x1663 A) (x1664 A)) 
                                   (=> 
                                       (and 
                                           (MS x1662 x1663 p26) 
                                           (MS x1662 x1664 p26)) 
                                       (= x1663 x1664))) 
                               (forall ((x1665 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x1665) 
                                           (<= x1665 n91)) 
                                       (exists ((x1666 A)) 
                                           (MS x1665 x1666 p26)))))) 
                       (path x1659 y36 p26) 
                       (exists ((x1667 Int)) 
                           (and 
                               (length p26 x1667) 
                               (dist x1659 y36 x1667))) 
                       (exists ((x1668 A)) 
                           (MS i85 x1668 p26)) 
                       (not 
                           (= i85 1)) 
                       (not 
                           (length p26 i85))) 
                   (and 
                       (exists ((x1669 A) (x1670 PZA)) 
                           (and 
                               (MS i85 x1669 p26) 
                               (forall ((x1671 Int) (x1672 A)) 
                                   (= 
                                       (MS x1671 x1672 x1670) 
                                       (and 
                                           (MS x1671 x1672 p26) 
                                           (<= 1 x1671) 
                                           (<= x1671 i85)))) 
                               (path x1659 x1669 x1670))) 
                       (exists ((x1673 A) (x1674 Int)) 
                           (and 
                               (MS i85 x1673 p26) 
                               (exists ((x1675 PZA)) 
                                   (and 
                                       (forall ((x1676 Int) (x1677 A)) 
                                           (= 
                                               (MS x1676 x1677 x1675) 
                                               (and 
                                                   (MS x1676 x1677 p26) 
                                                   (<= 1 x1676) 
                                                   (<= x1676 i85)))) 
                                       (length x1675 x1674))) 
                               (dist x1659 x1673 x1674))))))
         :named hyp121))
(assert (! (forall ((x1678 A) (y37 A) (p27 PZA) (i86 Int)) 
               (=> 
                   (and 
                       (MS1 x1678 a) 
                       (MS1 y37 a) 
                       (exists ((n92 Int)) 
                           (and 
                               (<= 0 n92) 
                               (forall ((x1679 Int) (x1680 A)) 
                                   (=> 
                                       (MS x1679 x1680 p27) 
                                       (and 
                                           (<= 1 x1679) 
                                           (<= x1679 n92)))) 
                               (forall ((x1681 Int) (x1682 A) (x1683 A)) 
                                   (=> 
                                       (and 
                                           (MS x1681 x1682 p27) 
                                           (MS x1681 x1683 p27)) 
                                       (= x1682 x1683))) 
                               (forall ((x1684 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x1684) 
                                           (<= x1684 n92)) 
                                       (exists ((x1685 A)) 
                                           (MS x1684 x1685 p27)))))) 
                       (path x1678 y37 p27) 
                       (exists ((x1686 Int)) 
                           (and 
                               (length p27 x1686) 
                               (dist x1678 y37 x1686))) 
                       (exists ((x1687 A)) 
                           (MS i86 x1687 p27)) 
                       (not 
                           (= i86 1)) 
                       (not 
                           (length p27 i86))) 
                   (and 
                       (exists ((x1688 A)) 
                           (and 
                               (MS i86 x1688 p27) 
                               (dist x1678 x1688 i86))) 
                       (exists ((x1689 A) (x1690 Int)) 
                           (and 
                               (exists ((x1691 Int)) 
                                   (and 
                                       (= x1691 (+ i86 1)) 
                                       (MS x1691 x1689 p27))) 
                               (= x1690 (+ i86 1)) 
                               (dist x1678 x1689 x1690))) 
                       (exists ((x1692 A) (x1693 A)) 
                           (and 
                               (MS i86 x1692 p27) 
                               (exists ((x1694 Int)) 
                                   (and 
                                       (= x1694 (+ i86 1)) 
                                       (MS x1694 x1693 p27))) 
                               (MS0 x1692 x1693 r))))))
         :named hyp122))
(assert (! (forall ((x1695 A) (y38 A) (p28 PZA) (z5 A)) 
               (=> 
                   (and 
                       (MS1 x1695 a) 
                       (MS1 y38 a) 
                       (exists ((n93 Int)) 
                           (and 
                               (<= 0 n93) 
                               (forall ((x1696 Int) (x1697 A)) 
                                   (=> 
                                       (MS x1696 x1697 p28) 
                                       (and 
                                           (<= 1 x1696) 
                                           (<= x1696 n93)))) 
                               (forall ((x1698 Int) (x1699 A) (x1700 A)) 
                                   (=> 
                                       (and 
                                           (MS x1698 x1699 p28) 
                                           (MS x1698 x1700 p28)) 
                                       (= x1699 x1700))) 
                               (forall ((x1701 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x1701) 
                                           (<= x1701 n93)) 
                                       (exists ((x1702 A)) 
                                           (MS x1701 x1702 p28)))))) 
                       (path x1695 y38 p28) 
                       (exists ((x1703 Int)) 
                           (and 
                               (length p28 x1703) 
                               (dist x1695 y38 x1703))) 
                       (exists ((x1704 Int)) 
                           (MS x1704 z5 p28)) 
                       (not 
                           (= z5 x1695)) 
                       (not 
                           (= z5 y38))) 
                   (exists ((t4 A)) 
                       (and 
                           (MS1 t4 a) 
                           (forall ((x1705 Int) (x1706 Int)) 
                               (=> 
                                   (and 
                                       (dist x1695 z5 x1706) 
                                       (dist x1695 t4 x1705)) 
                                   (< x1706 x1705))) 
                           (MS0 z5 t4 r)))))
         :named hyp123))
(assert (! (forall ((x1707 A) (y39 A)) 
               (=> 
                   (and 
                       (MS1 x1707 a) 
                       (MS1 y39 a)) 
                   (forall ((x1708 PZA)) 
                       (= 
                           (exists ((x1709 A) (x1710 A)) 
                               (and 
                                   (= x1709 y39) 
                                   (= x1710 x1707) 
                                   (path x1709 x1710 x1708))) 
                           (exists ((x1711 PZA)) 
                               (and 
                                   (exists ((x1712 A) (x1713 A)) 
                                       (and 
                                           (= x1712 x1707) 
                                           (= x1713 y39) 
                                           (path x1712 x1713 x1711))) 
                                   (exists ((s61 PZA)) 
                                       (and 
                                           (exists ((n94 Int)) 
                                               (and 
                                                   (<= 0 n94) 
                                                   (forall ((x1714 Int) (x1715 A)) 
                                                       (=> 
                                                           (MS x1714 x1715 s61) 
                                                           (and 
                                                               (<= 1 x1714) 
                                                               (<= x1714 n94)))) 
                                                   (forall ((x1716 Int) (x1717 A) (x1718 A)) 
                                                       (=> 
                                                           (and 
                                                               (MS x1716 x1717 s61) 
                                                               (MS x1716 x1718 s61)) 
                                                           (= x1717 x1718))) 
                                                   (forall ((x1719 Int)) 
                                                       (=> 
                                                           (and 
                                                               (<= 1 x1719) 
                                                               (<= x1719 n94)) 
                                                           (exists ((x1720 A)) 
                                                               (MS x1719 x1720 s61)))))) 
                                           (forall ((x1721 Int) (x1722 A)) 
                                               (= 
                                                   (MS x1721 x1722 x1711) 
                                                   (MS x1721 x1722 s61))) 
                                           (forall ((x1723 Int) (x1724 A)) 
                                               (= 
                                                   (MS x1723 x1724 x1708) 
                                                   (exists ((i87 Int)) 
                                                       (and 
                                                           (<= 1 i87) 
                                                           (forall ((x1725 Int)) 
                                                               (=> 
                                                                   (length s61 x1725) 
                                                                   (<= i87 x1725))) 
                                                           (= x1723 i87) 
                                                           (exists ((x1726 Int)) 
                                                               (and 
                                                                   (forall ((x1727 Int)) 
                                                                       (=> 
                                                                           (length s61 x1727) 
                                                                           (= x1726 (+ (- x1727 i87) 1)))) 
                                                                   (MS x1726 x1724 s61)))))))))))))))
         :named hyp124))
(assert (! (forall ((x1728 A) (y40 A) (p29 PZA)) 
               (=> 
                   (path x1728 y40 p29) 
                   (exists ((x1729 PZA)) 
                       (and 
                           (forall ((x1730 Int) (x1731 A)) 
                               (= 
                                   (MS x1730 x1731 x1729) 
                                   (exists ((i88 Int)) 
                                       (and 
                                           (<= 1 i88) 
                                           (forall ((x1732 Int)) 
                                               (=> 
                                                   (length p29 x1732) 
                                                   (<= i88 x1732))) 
                                           (= x1730 i88) 
                                           (exists ((x1733 Int)) 
                                               (and 
                                                   (forall ((x1734 Int)) 
                                                       (=> 
                                                           (length p29 x1734) 
                                                           (= x1733 (+ (- x1734 i88) 1)))) 
                                                   (MS x1733 x1731 p29))))))) 
                           (path y40 x1728 x1729)))))
         :named hyp125))
(assert (! (exists ((x1735 A)) 
               (and 
                   (exists ((x1736 Int)) 
                       (and 
                           (= x1736 1) 
                           (MS x1736 x1735 q))) 
                   (MS0 x1 x1735 r)))
         :named hyp126))
(assert (! (not 
               (forall ((x1737 A)) 
                   (=> 
                       (or 
                           (exists ((x1738 Int)) 
                               (exists ((i89 Int)) 
                                   (and 
                                       (<= 1 i89) 
                                       (forall ((x1739 Int)) 
                                           (=> 
                                               (length p x1739) 
                                               (<= i89 x1739))) 
                                       (= x1738 i89) 
                                       (MS i89 x1737 p)))) 
                           (exists ((x1740 Int)) 
                               (exists ((i90 Int)) 
                                   (and 
                                       (forall ((x1741 Int)) 
                                           (=> 
                                               (length p x1741) 
                                               (<= (+ x1741 1) i90))) 
                                       (forall ((x1742 Int) (x1743 Int)) 
                                           (=> 
                                               (and 
                                                   (length p x1743) 
                                                   (length q x1742)) 
                                               (<= i90 (+ x1743 x1742)))) 
                                       (= x1740 i90) 
                                       (exists ((x1744 Int)) 
                                           (and 
                                               (forall ((x1745 Int)) 
                                                   (=> 
                                                       (length p x1745) 
                                                       (= x1744 (- i90 x1745)))) 
                                               (MS x1744 x1737 q))))))) 
                       (MS1 x1737 a))))
         :named goal))
(check-sat)
(exit)

