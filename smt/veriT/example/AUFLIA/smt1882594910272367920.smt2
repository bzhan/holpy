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
(declare-fun r () PAA)
(declare-fun x () A)
(declare-fun y2 () A)

; Elementary Sets axiom (Singleton part)
(assert (forall ((x1928 A) (x1929 A)) 
            (exists ((X PAA)) 
                (and 
                    (MS0 x1928 x1929 X) 
                    (forall ((y45 A) (y46 A)) 
                        (=> 
                            (MS0 y45 y46 X) 
                            (and 
                                (= y45 x1928) 
                                (= y46 x1929))))))))
; Elementary Sets axiom (Singleton part)
(assert (forall ((x1930 A)) 
            (exists ((X0 PA)) 
                (and 
                    (MS1 x1930 X0) 
                    (forall ((y47 A)) 
                        (=> 
                            (MS1 y47 X0) 
                            (= y47 x1930)))))))
; Elementary Sets axiom (Singleton part)
(assert (forall ((x1931 Int) (x1932 A)) 
            (exists ((X1 PZA)) 
                (and 
                    (MS x1931 x1932 X1) 
                    (forall ((y48 Int) (y49 A)) 
                        (=> 
                            (MS y48 y49 X1) 
                            (and 
                                (= y48 x1931) 
                                (= y49 x1932))))))))
(assert (! (forall ((x0 PZA)) 
               (= 
                   (seq x0) 
                   (exists ((s PZA)) 
                       (and 
                           (exists ((n Int)) 
                               (and 
                                   (<= 0 n) 
                                   (forall ((x1 Int) (x2 A)) 
                                       (=> 
                                           (MS x1 x2 s) 
                                           (and 
                                               (<= 1 x1) 
                                               (<= x1 n)))) 
                                   (forall ((x3 Int) (x4 A) (x5 A)) 
                                       (=> 
                                           (and 
                                               (MS x3 x4 s) 
                                               (MS x3 x5 s)) 
                                           (= x4 x5))) 
                                   (forall ((x6 Int)) 
                                       (=> 
                                           (and 
                                               (<= 1 x6) 
                                               (<= x6 n)) 
                                           (exists ((x7 A)) 
                                               (MS x6 x7 s)))))) 
                           (forall ((x8 Int) (x9 A)) 
                               (= 
                                   (MS x8 x9 x0) 
                                   (MS x8 x9 s)))))))
         :named hyp1))
(assert (! (forall ((n0 Int) (s0 PZA)) 
               (=> 
                   (and 
                       (<= 0 n0) 
                       (forall ((x10 Int) (x11 A)) 
                           (=> 
                               (MS x10 x11 s0) 
                               (and 
                                   (<= 1 x10) 
                                   (<= x10 n0)))) 
                       (forall ((x12 Int) (x13 A) (x14 A)) 
                           (=> 
                               (and 
                                   (MS x12 x13 s0) 
                                   (MS x12 x14 s0)) 
                               (= x13 x14))) 
                       (forall ((x15 Int)) 
                           (=> 
                               (and 
                                   (<= 1 x15) 
                                   (<= x15 n0)) 
                               (exists ((x16 A)) 
                                   (MS x15 x16 s0))))) 
                   (length s0 n0)))
         :named hyp2))
(assert (! (forall ((x17 A) (x18 A)) 
               (not 
                   (and 
                       (MS0 x17 x18 r) 
                       (= x17 x18))))
         :named hyp3))
(assert (! (and 
               (forall ((x19 A) (x20 A) (x21 Int)) 
                   (=> 
                       (dist x19 x20 x21) 
                       (and 
                           (MS1 x19 a) 
                           (MS1 x20 a) 
                           (<= 0 x21)))) 
               (forall ((x22 A) (x23 A) (x24 Int) (x25 Int)) 
                   (=> 
                       (and 
                           (dist x22 x23 x24) 
                           (dist x22 x23 x25)) 
                       (= x24 x25))) 
               (forall ((x26 A) (x27 A)) 
                   (=> 
                       (and 
                           (MS1 x26 a) 
                           (MS1 x27 a)) 
                       (exists ((x28 Int)) 
                           (dist x26 x27 x28)))))
         :named hyp4))
(assert (! (forall ((x29 A) (x30 A)) 
               (=> 
                   (MS0 x29 x30 r) 
                   (MS0 x30 x29 r)))
         :named hyp5))
(assert (! (forall ((x31 A) (y A)) 
               (=> 
                   (and 
                       (MS1 x31 a) 
                       (MS1 y a)) 
                   (exists ((x32 Int)) 
                       (and 
                           (dist y x31 x32) 
                           (dist x31 y x32)))))
         :named hyp6))
(assert (! (forall ((x33 Int)) 
               (=> 
                   (length p x33) 
                   (<= 3 x33)))
         :named hyp7))
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
         :named hyp8))
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
         :named hyp9))
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
         :named hyp10))
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
         :named hyp11))
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
         :named hyp12))
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
         :named hyp13))
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
         :named hyp14))
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
         :named hyp15))
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
         :named hyp16))
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
         :named hyp17))
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
         :named hyp18))
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
         :named hyp19))
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
         :named hyp20))
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
         :named hyp21))
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
         :named hyp22))
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
         :named hyp23))
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
         :named hyp24))
(assert (! (forall ((x642 A) (y1 A)) 
               (=> 
                   (and 
                       (MS1 x642 a) 
                       (MS1 y1 a)) 
                   (exists ((x643 Int)) 
                       (and 
                           (exists ((x644 PZA)) 
                               (and 
                                   (exists ((x645 A) (x646 A)) 
                                       (and 
                                           (= x645 x642) 
                                           (= x646 y1) 
                                           (exists ((x647 A) (y3 A) (p1 PZA)) 
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
                                                           (MS x659 y3 p1))) 
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
                                                   (= x646 y3) 
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
                                                   (= x669 y1) 
                                                   (exists ((x670 A) (y4 A) (p2 PZA)) 
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
                                                                   (MS x682 y4 p2))) 
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
                                                           (= x669 y4) 
                                                           (forall ((x687 Int) (x688 A)) 
                                                               (= 
                                                                   (MS x687 x688 x667) 
                                                                   (MS x687 x688 p2))))))) 
                                           (length x667 x666))) 
                                   (<= x643 x666))) 
                           (dist x642 y1 x643)))))
         :named hyp25))
(assert (! (forall ((x689 A) (y5 A)) 
               (=> 
                   (and 
                       (MS1 x689 a) 
                       (MS1 y5 a)) 
                   (forall ((x690 PZA)) 
                       (= 
                           (exists ((x691 A) (x692 A)) 
                               (and 
                                   (= x691 y5) 
                                   (= x692 x689) 
                                   (exists ((x693 A) (y6 A) (p3 PZA)) 
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
                                                   (MS x705 y6 p3))) 
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
                                           (= x692 y6) 
                                           (forall ((x710 Int) (x711 A)) 
                                               (= 
                                                   (MS x710 x711 x690) 
                                                   (MS x710 x711 p3))))))) 
                           (exists ((x712 PZA)) 
                               (and 
                                   (exists ((x713 A) (x714 A)) 
                                       (and 
                                           (= x713 x689) 
                                           (= x714 y5) 
                                           (exists ((x715 A) (y7 A) (p4 PZA)) 
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
                                                           (MS x727 y7 p4))) 
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
                                                   (= x714 y7) 
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
         :named hyp26))
(assert (! (forall ((x748 A) (x749 A) (x750 PZA)) 
               (= 
                   (shpath x748 x749 x750) 
                   (exists ((x751 A) (y8 A) (p5 PZA)) 
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
                                   (MS x763 y8 p5))) 
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
                                   (dist x751 y8 x768))) 
                           (= x748 x751) 
                           (= x749 y8) 
                           (forall ((x769 Int) (x770 A)) 
                               (= 
                                   (MS x769 x770 x750) 
                                   (MS x769 x770 p5)))))))
         :named hyp27))
(assert (! (forall ((x771 A) (y9 A) (p6 PZA) (i46 Int)) 
               (=> 
                   (and 
                       (MS1 x771 a) 
                       (MS1 y9 a) 
                       (exists ((n51 Int)) 
                           (and 
                               (<= 0 n51) 
                               (forall ((x772 Int) (x773 A)) 
                                   (=> 
                                       (MS x772 x773 p6) 
                                       (and 
                                           (<= 1 x772) 
                                           (<= x772 n51)))) 
                               (forall ((x774 Int) (x775 A) (x776 A)) 
                                   (=> 
                                       (and 
                                           (MS x774 x775 p6) 
                                           (MS x774 x776 p6)) 
                                       (= x775 x776))) 
                               (forall ((x777 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x777) 
                                           (<= x777 n51)) 
                                       (exists ((x778 A)) 
                                           (MS x777 x778 p6)))))) 
                       (forall ((x779 A)) 
                           (=> 
                               (exists ((x780 Int)) 
                                   (MS x780 x779 p6)) 
                               (MS1 x779 a))) 
                       (forall ((x781 Int)) 
                           (=> 
                               (length p6 x781) 
                               (< 1 x781))) 
                       (exists ((x782 Int)) 
                           (and 
                               (= x782 1) 
                               (MS x782 x771 p6))) 
                       (exists ((x783 Int)) 
                           (and 
                               (length p6 x783) 
                               (MS x783 y9 p6))) 
                       (forall ((i47 Int)) 
                           (=> 
                               (and 
                                   (<= 1 i47) 
                                   (forall ((x784 Int)) 
                                       (=> 
                                           (length p6 x784) 
                                           (<= i47 (- x784 1))))) 
                               (exists ((x785 A) (x786 A)) 
                                   (and 
                                       (MS i47 x785 p6) 
                                       (exists ((x787 Int)) 
                                           (and 
                                               (= x787 (+ i47 1)) 
                                               (MS x787 x786 p6))) 
                                       (MS0 x785 x786 r))))) 
                       (<= 2 i46) 
                       (forall ((x788 Int)) 
                           (=> 
                               (length p6 x788) 
                               (<= i46 (- x788 1))))) 
                   (and 
                       (exists ((n52 Int)) 
                           (and 
                               (<= 0 n52) 
                               (forall ((x789 Int) (x790 A)) 
                                   (=> 
                                       (and 
                                           (MS x789 x790 p6) 
                                           (<= 1 x789) 
                                           (<= x789 i46)) 
                                       (and 
                                           (<= 1 x789) 
                                           (<= x789 n52)))) 
                               (forall ((x791 Int) (x792 A) (x793 A)) 
                                   (=> 
                                       (and 
                                           (MS x791 x792 p6) 
                                           (<= 1 x791) 
                                           (<= x791 i46) 
                                           (MS x791 x793 p6)) 
                                       (= x792 x793))) 
                               (forall ((x794 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x794) 
                                           (<= x794 n52)) 
                                       (exists ((x795 A)) 
                                           (and 
                                               (MS x794 x795 p6) 
                                               (<= 1 x794) 
                                               (<= x794 i46))))))) 
                       (forall ((x796 A)) 
                           (=> 
                               (exists ((x797 Int)) 
                                   (and 
                                       (MS x797 x796 p6) 
                                       (<= 1 x797) 
                                       (<= x797 i46))) 
                               (MS1 x796 a))) 
                       (forall ((x798 Int)) 
                           (=> 
                               (exists ((x799 PZA)) 
                                   (and 
                                       (forall ((x800 Int) (x801 A)) 
                                           (= 
                                               (MS x800 x801 x799) 
                                               (and 
                                                   (MS x800 x801 p6) 
                                                   (<= 1 x800) 
                                                   (<= x800 i46)))) 
                                       (length x799 x798))) 
                               (< 1 x798))) 
                       (exists ((x802 Int)) 
                           (and 
                               (= x802 1) 
                               (MS x802 x771 p6))) 
                       (<= 1 1) 
                       (<= 1 i46) 
                       (exists ((x803 Int) (x804 A)) 
                           (and 
                               (exists ((x805 PZA)) 
                                   (and 
                                       (forall ((x806 Int) (x807 A)) 
                                           (= 
                                               (MS x806 x807 x805) 
                                               (and 
                                                   (MS x806 x807 p6) 
                                                   (<= 1 x806) 
                                                   (<= x806 i46)))) 
                                       (length x805 x803))) 
                               (MS i46 x804 p6) 
                               (MS x803 x804 p6))) 
                       (forall ((x808 Int)) 
                           (=> 
                               (exists ((x809 PZA)) 
                                   (and 
                                       (forall ((x810 Int) (x811 A)) 
                                           (= 
                                               (MS x810 x811 x809) 
                                               (and 
                                                   (MS x810 x811 p6) 
                                                   (<= 1 x810) 
                                                   (<= x810 i46)))) 
                                       (length x809 x808))) 
                               (<= 1 x808))) 
                       (forall ((x812 Int)) 
                           (=> 
                               (exists ((x813 PZA)) 
                                   (and 
                                       (forall ((x814 Int) (x815 A)) 
                                           (= 
                                               (MS x814 x815 x813) 
                                               (and 
                                                   (MS x814 x815 p6) 
                                                   (<= 1 x814) 
                                                   (<= x814 i46)))) 
                                       (length x813 x812))) 
                               (<= x812 i46))) 
                       (forall ((i48 Int)) 
                           (=> 
                               (and 
                                   (<= 1 i48) 
                                   (forall ((x816 Int)) 
                                       (=> 
                                           (exists ((x817 PZA)) 
                                               (and 
                                                   (forall ((x818 Int) (x819 A)) 
                                                       (= 
                                                           (MS x818 x819 x817) 
                                                           (and 
                                                               (MS x818 x819 p6) 
                                                               (<= 1 x818) 
                                                               (<= x818 i46)))) 
                                                   (length x817 x816))) 
                                           (<= i48 (- x816 1))))) 
                               (exists ((x820 A) (x821 A)) 
                                   (and 
                                       (MS i48 x820 p6) 
                                       (<= 1 i48) 
                                       (<= i48 i46) 
                                       (exists ((x822 Int)) 
                                           (and 
                                               (= x822 (+ i48 1)) 
                                               (MS x822 x821 p6))) 
                                       (<= 1 (+ i48 1)) 
                                       (<= (+ i48 1) i46) 
                                       (MS0 x820 x821 r))))))))
         :named hyp28))
(assert (! (forall ((x823 A) (y10 A) (z A)) 
               (=> 
                   (and 
                       (MS1 x823 a) 
                       (MS1 y10 a) 
                       (MS1 z a) 
                       (not 
                           (= z x823)) 
                       (not 
                           (= z y10)) 
                       (forall ((t A)) 
                           (=> 
                               (and 
                                   (MS1 t a) 
                                   (MS0 z t r)) 
                               (forall ((x824 Int) (x825 Int)) 
                                   (=> 
                                       (and 
                                           (dist x823 t x825) 
                                           (dist x823 z x824)) 
                                       (<= x825 x824)))))) 
                   (exists ((q PZA)) 
                       (and 
                           (exists ((n53 Int)) 
                               (and 
                                   (<= 0 n53) 
                                   (forall ((x826 Int) (x827 A)) 
                                       (=> 
                                           (MS x826 x827 q) 
                                           (and 
                                               (<= 1 x826) 
                                               (<= x826 n53)))) 
                                   (forall ((x828 Int) (x829 A) (x830 A)) 
                                       (=> 
                                           (and 
                                               (MS x828 x829 q) 
                                               (MS x828 x830 q)) 
                                           (= x829 x830))) 
                                   (forall ((x831 Int)) 
                                       (=> 
                                           (and 
                                               (<= 1 x831) 
                                               (<= x831 n53)) 
                                           (exists ((x832 A)) 
                                               (MS x831 x832 q)))))) 
                           (forall ((x833 A)) 
                               (=> 
                                   (exists ((x834 Int)) 
                                       (MS x834 x833 q)) 
                                   (MS1 x833 a))) 
                           (forall ((x835 Int)) 
                               (=> 
                                   (length q x835) 
                                   (< 1 x835))) 
                           (exists ((x836 Int)) 
                               (and 
                                   (= x836 1) 
                                   (MS x836 x823 q))) 
                           (exists ((x837 Int)) 
                               (and 
                                   (length q x837) 
                                   (MS x837 y10 q))) 
                           (forall ((i49 Int)) 
                               (=> 
                                   (and 
                                       (<= 1 i49) 
                                       (forall ((x838 Int)) 
                                           (=> 
                                               (length q x838) 
                                               (<= i49 (- x838 1))))) 
                                   (exists ((x839 A) (x840 A)) 
                                       (and 
                                           (MS i49 x839 q) 
                                           (exists ((x841 Int)) 
                                               (and 
                                                   (= x841 (+ i49 1)) 
                                                   (MS x841 x840 q))) 
                                           (MS0 x839 x840 r))))) 
                           (not 
                               (exists ((x842 Int)) 
                                   (MS x842 z q)))))))
         :named hyp29))
(assert (! (exists ((n54 Int)) 
               (and 
                   (<= 0 n54) 
                   (forall ((x843 Int) (x844 A)) 
                       (=> 
                           (MS x843 x844 p) 
                           (and 
                               (<= 1 x843) 
                               (<= x843 n54)))) 
                   (forall ((x845 Int) (x846 A) (x847 A)) 
                       (=> 
                           (and 
                               (MS x845 x846 p) 
                               (MS x845 x847 p)) 
                           (= x846 x847))) 
                   (forall ((x848 Int)) 
                       (=> 
                           (and 
                               (<= 1 x848) 
                               (<= x848 n54)) 
                           (exists ((x849 A)) 
                               (MS x848 x849 p))))))
         :named hyp30))
(assert (! (forall ((x850 A)) 
               (=> 
                   (exists ((x851 Int)) 
                       (MS x851 x850 p)) 
                   (MS1 x850 a)))
         :named hyp31))
(assert (! (forall ((x852 Int)) 
               (=> 
                   (length p x852) 
                   (< 1 x852)))
         :named hyp32))
(assert (! (exists ((x853 Int)) 
               (and 
                   (= x853 1) 
                   (MS x853 x p)))
         :named hyp33))
(assert (! (exists ((x854 Int)) 
               (and 
                   (length p x854) 
                   (MS x854 y2 p)))
         :named hyp34))
(assert (! (forall ((i50 Int)) 
               (=> 
                   (and 
                       (<= 1 i50) 
                       (forall ((x855 Int)) 
                           (=> 
                               (length p x855) 
                               (<= i50 (- x855 1))))) 
                   (exists ((x856 A) (x857 A)) 
                       (and 
                           (MS i50 x856 p) 
                           (exists ((x858 Int)) 
                               (and 
                                   (= x858 (+ i50 1)) 
                                   (MS x858 x857 p))) 
                           (MS0 x856 x857 r)))))
         :named hyp35))
(assert (! (forall ((x859 A) (y11 A)) 
               (=> 
                   (and 
                       (MS1 x859 a) 
                       (MS1 y11 a)) 
                   (exists ((p7 PZA)) 
                       (and 
                           (exists ((n55 Int)) 
                               (and 
                                   (<= 0 n55) 
                                   (forall ((x860 Int) (x861 A)) 
                                       (=> 
                                           (MS x860 x861 p7) 
                                           (and 
                                               (<= 1 x860) 
                                               (<= x860 n55)))) 
                                   (forall ((x862 Int) (x863 A) (x864 A)) 
                                       (=> 
                                           (and 
                                               (MS x862 x863 p7) 
                                               (MS x862 x864 p7)) 
                                           (= x863 x864))) 
                                   (forall ((x865 Int)) 
                                       (=> 
                                           (and 
                                               (<= 1 x865) 
                                               (<= x865 n55)) 
                                           (exists ((x866 A)) 
                                               (MS x865 x866 p7)))))) 
                           (forall ((x867 A)) 
                               (=> 
                                   (exists ((x868 Int)) 
                                       (MS x868 x867 p7)) 
                                   (MS1 x867 a))) 
                           (forall ((x869 Int)) 
                               (=> 
                                   (length p7 x869) 
                                   (< 1 x869))) 
                           (exists ((x870 Int)) 
                               (and 
                                   (= x870 1) 
                                   (MS x870 x859 p7))) 
                           (exists ((x871 Int)) 
                               (and 
                                   (length p7 x871) 
                                   (MS x871 y11 p7))) 
                           (forall ((i51 Int)) 
                               (=> 
                                   (and 
                                       (<= 1 i51) 
                                       (forall ((x872 Int)) 
                                           (=> 
                                               (length p7 x872) 
                                               (<= i51 (- x872 1))))) 
                                   (exists ((x873 A) (x874 A)) 
                                       (and 
                                           (MS i51 x873 p7) 
                                           (exists ((x875 Int)) 
                                               (and 
                                                   (= x875 (+ i51 1)) 
                                                   (MS x875 x874 p7))) 
                                           (MS0 x873 x874 r))))) 
                           (exists ((x876 Int)) 
                               (and 
                                   (length p7 x876) 
                                   (dist x859 y11 x876)))))))
         :named hyp36))
(assert (! (forall ((x877 A) (y12 A) (p8 PZA) (i52 Int)) 
               (=> 
                   (and 
                       (MS1 x877 a) 
                       (MS1 y12 a) 
                       (exists ((n56 Int)) 
                           (and 
                               (<= 0 n56) 
                               (forall ((x878 Int) (x879 A)) 
                                   (=> 
                                       (MS x878 x879 p8) 
                                       (and 
                                           (<= 1 x878) 
                                           (<= x878 n56)))) 
                               (forall ((x880 Int) (x881 A) (x882 A)) 
                                   (=> 
                                       (and 
                                           (MS x880 x881 p8) 
                                           (MS x880 x882 p8)) 
                                       (= x881 x882))) 
                               (forall ((x883 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x883) 
                                           (<= x883 n56)) 
                                       (exists ((x884 A)) 
                                           (MS x883 x884 p8)))))) 
                       (forall ((x885 A)) 
                           (=> 
                               (exists ((x886 Int)) 
                                   (MS x886 x885 p8)) 
                               (MS1 x885 a))) 
                       (forall ((x887 Int)) 
                           (=> 
                               (length p8 x887) 
                               (< 1 x887))) 
                       (exists ((x888 Int)) 
                           (and 
                               (= x888 1) 
                               (MS x888 x877 p8))) 
                       (exists ((x889 Int)) 
                           (and 
                               (length p8 x889) 
                               (MS x889 y12 p8))) 
                       (forall ((i53 Int)) 
                           (=> 
                               (and 
                                   (<= 1 i53) 
                                   (forall ((x890 Int)) 
                                       (=> 
                                           (length p8 x890) 
                                           (<= i53 (- x890 1))))) 
                               (exists ((x891 A) (x892 A)) 
                                   (and 
                                       (MS i53 x891 p8) 
                                       (exists ((x893 Int)) 
                                           (and 
                                               (= x893 (+ i53 1)) 
                                               (MS x893 x892 p8))) 
                                       (MS0 x891 x892 r))))) 
                       (exists ((x894 Int)) 
                           (and 
                               (length p8 x894) 
                               (dist x877 y12 x894))) 
                       (exists ((x895 A)) 
                           (MS i52 x895 p8)) 
                       (not 
                           (= i52 1)) 
                       (not 
                           (length p8 i52))) 
                   (and 
                       (exists ((n57 Int)) 
                           (and 
                               (<= 0 n57) 
                               (forall ((x896 Int) (x897 A)) 
                                   (=> 
                                       (and 
                                           (MS x896 x897 p8) 
                                           (<= 1 x896) 
                                           (<= x896 i52)) 
                                       (and 
                                           (<= 1 x896) 
                                           (<= x896 n57)))) 
                               (forall ((x898 Int) (x899 A) (x900 A)) 
                                   (=> 
                                       (and 
                                           (MS x898 x899 p8) 
                                           (<= 1 x898) 
                                           (<= x898 i52) 
                                           (MS x898 x900 p8)) 
                                       (= x899 x900))) 
                               (forall ((x901 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x901) 
                                           (<= x901 n57)) 
                                       (exists ((x902 A)) 
                                           (and 
                                               (MS x901 x902 p8) 
                                               (<= 1 x901) 
                                               (<= x901 i52))))))) 
                       (forall ((x903 A)) 
                           (=> 
                               (exists ((x904 Int)) 
                                   (and 
                                       (MS x904 x903 p8) 
                                       (<= 1 x904) 
                                       (<= x904 i52))) 
                               (MS1 x903 a))) 
                       (forall ((x905 Int)) 
                           (=> 
                               (exists ((x906 PZA)) 
                                   (and 
                                       (forall ((x907 Int) (x908 A)) 
                                           (= 
                                               (MS x907 x908 x906) 
                                               (and 
                                                   (MS x907 x908 p8) 
                                                   (<= 1 x907) 
                                                   (<= x907 i52)))) 
                                       (length x906 x905))) 
                               (< 1 x905))) 
                       (exists ((x909 Int)) 
                           (and 
                               (= x909 1) 
                               (MS x909 x877 p8))) 
                       (<= 1 1) 
                       (<= 1 i52) 
                       (exists ((x910 Int) (x911 A)) 
                           (and 
                               (exists ((x912 PZA)) 
                                   (and 
                                       (forall ((x913 Int) (x914 A)) 
                                           (= 
                                               (MS x913 x914 x912) 
                                               (and 
                                                   (MS x913 x914 p8) 
                                                   (<= 1 x913) 
                                                   (<= x913 i52)))) 
                                       (length x912 x910))) 
                               (MS i52 x911 p8) 
                               (MS x910 x911 p8))) 
                       (forall ((x915 Int)) 
                           (=> 
                               (exists ((x916 PZA)) 
                                   (and 
                                       (forall ((x917 Int) (x918 A)) 
                                           (= 
                                               (MS x917 x918 x916) 
                                               (and 
                                                   (MS x917 x918 p8) 
                                                   (<= 1 x917) 
                                                   (<= x917 i52)))) 
                                       (length x916 x915))) 
                               (<= 1 x915))) 
                       (forall ((x919 Int)) 
                           (=> 
                               (exists ((x920 PZA)) 
                                   (and 
                                       (forall ((x921 Int) (x922 A)) 
                                           (= 
                                               (MS x921 x922 x920) 
                                               (and 
                                                   (MS x921 x922 p8) 
                                                   (<= 1 x921) 
                                                   (<= x921 i52)))) 
                                       (length x920 x919))) 
                               (<= x919 i52))) 
                       (forall ((i54 Int)) 
                           (=> 
                               (and 
                                   (<= 1 i54) 
                                   (forall ((x923 Int)) 
                                       (=> 
                                           (exists ((x924 PZA)) 
                                               (and 
                                                   (forall ((x925 Int) (x926 A)) 
                                                       (= 
                                                           (MS x925 x926 x924) 
                                                           (and 
                                                               (MS x925 x926 p8) 
                                                               (<= 1 x925) 
                                                               (<= x925 i52)))) 
                                                   (length x924 x923))) 
                                           (<= i54 (- x923 1))))) 
                               (exists ((x927 A) (x928 A)) 
                                   (and 
                                       (MS i54 x927 p8) 
                                       (<= 1 i54) 
                                       (<= i54 i52) 
                                       (exists ((x929 Int)) 
                                           (and 
                                               (= x929 (+ i54 1)) 
                                               (MS x929 x928 p8))) 
                                       (<= 1 (+ i54 1)) 
                                       (<= (+ i54 1) i52) 
                                       (MS0 x927 x928 r))))) 
                       (exists ((x930 A) (x931 Int)) 
                           (and 
                               (MS i52 x930 p8) 
                               (exists ((x932 PZA)) 
                                   (and 
                                       (forall ((x933 Int) (x934 A)) 
                                           (= 
                                               (MS x933 x934 x932) 
                                               (and 
                                                   (MS x933 x934 p8) 
                                                   (<= 1 x933) 
                                                   (<= x933 i52)))) 
                                       (length x932 x931))) 
                               (dist x877 x930 x931))))))
         :named hyp37))
(assert (! (forall ((x935 A) (y13 A) (p9 PZA) (i55 Int)) 
               (=> 
                   (and 
                       (MS1 x935 a) 
                       (MS1 y13 a) 
                       (exists ((n58 Int)) 
                           (and 
                               (<= 0 n58) 
                               (forall ((x936 Int) (x937 A)) 
                                   (=> 
                                       (MS x936 x937 p9) 
                                       (and 
                                           (<= 1 x936) 
                                           (<= x936 n58)))) 
                               (forall ((x938 Int) (x939 A) (x940 A)) 
                                   (=> 
                                       (and 
                                           (MS x938 x939 p9) 
                                           (MS x938 x940 p9)) 
                                       (= x939 x940))) 
                               (forall ((x941 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x941) 
                                           (<= x941 n58)) 
                                       (exists ((x942 A)) 
                                           (MS x941 x942 p9)))))) 
                       (forall ((x943 A)) 
                           (=> 
                               (exists ((x944 Int)) 
                                   (MS x944 x943 p9)) 
                               (MS1 x943 a))) 
                       (forall ((x945 Int)) 
                           (=> 
                               (length p9 x945) 
                               (< 1 x945))) 
                       (exists ((x946 Int)) 
                           (and 
                               (= x946 1) 
                               (MS x946 x935 p9))) 
                       (exists ((x947 Int)) 
                           (and 
                               (length p9 x947) 
                               (MS x947 y13 p9))) 
                       (forall ((i56 Int)) 
                           (=> 
                               (and 
                                   (<= 1 i56) 
                                   (forall ((x948 Int)) 
                                       (=> 
                                           (length p9 x948) 
                                           (<= i56 (- x948 1))))) 
                               (exists ((x949 A) (x950 A)) 
                                   (and 
                                       (MS i56 x949 p9) 
                                       (exists ((x951 Int)) 
                                           (and 
                                               (= x951 (+ i56 1)) 
                                               (MS x951 x950 p9))) 
                                       (MS0 x949 x950 r))))) 
                       (exists ((x952 Int)) 
                           (and 
                               (length p9 x952) 
                               (dist x935 y13 x952))) 
                       (exists ((x953 A)) 
                           (MS i55 x953 p9)) 
                       (not 
                           (= i55 1)) 
                       (not 
                           (length p9 i55))) 
                   (and 
                       (exists ((x954 A)) 
                           (and 
                               (MS i55 x954 p9) 
                               (dist x935 x954 i55))) 
                       (exists ((x955 A) (x956 Int)) 
                           (and 
                               (exists ((x957 Int)) 
                                   (and 
                                       (= x957 (+ i55 1)) 
                                       (MS x957 x955 p9))) 
                               (= x956 (+ i55 1)) 
                               (dist x935 x955 x956))) 
                       (exists ((x958 A) (x959 A)) 
                           (and 
                               (MS i55 x958 p9) 
                               (exists ((x960 Int)) 
                                   (and 
                                       (= x960 (+ i55 1)) 
                                       (MS x960 x959 p9))) 
                               (MS0 x958 x959 r))))))
         :named hyp38))
(assert (! (forall ((x961 A) (y14 A) (p10 PZA) (z0 A)) 
               (=> 
                   (and 
                       (MS1 x961 a) 
                       (MS1 y14 a) 
                       (exists ((n59 Int)) 
                           (and 
                               (<= 0 n59) 
                               (forall ((x962 Int) (x963 A)) 
                                   (=> 
                                       (MS x962 x963 p10) 
                                       (and 
                                           (<= 1 x962) 
                                           (<= x962 n59)))) 
                               (forall ((x964 Int) (x965 A) (x966 A)) 
                                   (=> 
                                       (and 
                                           (MS x964 x965 p10) 
                                           (MS x964 x966 p10)) 
                                       (= x965 x966))) 
                               (forall ((x967 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x967) 
                                           (<= x967 n59)) 
                                       (exists ((x968 A)) 
                                           (MS x967 x968 p10)))))) 
                       (forall ((x969 A)) 
                           (=> 
                               (exists ((x970 Int)) 
                                   (MS x970 x969 p10)) 
                               (MS1 x969 a))) 
                       (forall ((x971 Int)) 
                           (=> 
                               (length p10 x971) 
                               (< 1 x971))) 
                       (exists ((x972 Int)) 
                           (and 
                               (= x972 1) 
                               (MS x972 x961 p10))) 
                       (exists ((x973 Int)) 
                           (and 
                               (length p10 x973) 
                               (MS x973 y14 p10))) 
                       (forall ((i57 Int)) 
                           (=> 
                               (and 
                                   (<= 1 i57) 
                                   (forall ((x974 Int)) 
                                       (=> 
                                           (length p10 x974) 
                                           (<= i57 (- x974 1))))) 
                               (exists ((x975 A) (x976 A)) 
                                   (and 
                                       (MS i57 x975 p10) 
                                       (exists ((x977 Int)) 
                                           (and 
                                               (= x977 (+ i57 1)) 
                                               (MS x977 x976 p10))) 
                                       (MS0 x975 x976 r))))) 
                       (exists ((x978 Int)) 
                           (and 
                               (length p10 x978) 
                               (dist x961 y14 x978))) 
                       (exists ((x979 Int)) 
                           (MS x979 z0 p10)) 
                       (not 
                           (= z0 x961)) 
                       (not 
                           (= z0 y14))) 
                   (exists ((t0 A)) 
                       (and 
                           (MS1 t0 a) 
                           (forall ((x980 Int) (x981 Int)) 
                               (=> 
                                   (and 
                                       (dist x961 z0 x981) 
                                       (dist x961 t0 x980)) 
                                   (< x981 x980))) 
                           (MS0 z0 t0 r)))))
         :named hyp39))
(assert (! (forall ((y15 A) (y20 A) (x982 A) (x1100 A) (p11 PZA) (q0 PZA)) 
               (=> 
                   (and 
                       (MS1 y15 a) 
                       (MS1 y20 a) 
                       (MS1 x982 a) 
                       (MS1 x1100 a) 
                       (exists ((n60 Int)) 
                           (and 
                               (<= 0 n60) 
                               (forall ((x983 Int) (x984 A)) 
                                   (=> 
                                       (MS x983 x984 q0) 
                                       (and 
                                           (<= 1 x983) 
                                           (<= x983 n60)))) 
                               (forall ((x985 Int) (x986 A) (x987 A)) 
                                   (=> 
                                       (and 
                                           (MS x985 x986 q0) 
                                           (MS x985 x987 q0)) 
                                       (= x986 x987))) 
                               (forall ((x988 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x988) 
                                           (<= x988 n60)) 
                                       (exists ((x989 A)) 
                                           (MS x988 x989 q0)))))) 
                       (forall ((x990 A)) 
                           (=> 
                               (exists ((x991 Int)) 
                                   (MS x991 x990 q0)) 
                               (MS1 x990 a))) 
                       (forall ((x992 Int)) 
                           (=> 
                               (length q0 x992) 
                               (< 1 x992))) 
                       (exists ((x993 Int)) 
                           (and 
                               (= x993 1) 
                               (MS x993 x982 q0))) 
                       (exists ((x994 Int)) 
                           (and 
                               (length q0 x994) 
                               (MS x994 y15 q0))) 
                       (forall ((i58 Int)) 
                           (=> 
                               (and 
                                   (<= 1 i58) 
                                   (forall ((x995 Int)) 
                                       (=> 
                                           (length q0 x995) 
                                           (<= i58 (- x995 1))))) 
                               (exists ((x996 A) (x997 A)) 
                                   (and 
                                       (MS i58 x996 q0) 
                                       (exists ((x998 Int)) 
                                           (and 
                                               (= x998 (+ i58 1)) 
                                               (MS x998 x997 q0))) 
                                       (MS0 x996 x997 r))))) 
                       (exists ((n61 Int)) 
                           (and 
                               (<= 0 n61) 
                               (forall ((x999 Int) (x1000 A)) 
                                   (=> 
                                       (MS x999 x1000 p11) 
                                       (and 
                                           (<= 1 x999) 
                                           (<= x999 n61)))) 
                               (forall ((x1001 Int) (x1002 A) (x1003 A)) 
                                   (=> 
                                       (and 
                                           (MS x1001 x1002 p11) 
                                           (MS x1001 x1003 p11)) 
                                       (= x1002 x1003))) 
                               (forall ((x1004 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x1004) 
                                           (<= x1004 n61)) 
                                       (exists ((x1005 A)) 
                                           (MS x1004 x1005 p11)))))) 
                       (forall ((x1006 A)) 
                           (=> 
                               (exists ((x1007 Int)) 
                                   (MS x1007 x1006 p11)) 
                               (MS1 x1006 a))) 
                       (forall ((x1008 Int)) 
                           (=> 
                               (length p11 x1008) 
                               (< 1 x1008))) 
                       (exists ((x1009 Int)) 
                           (and 
                               (= x1009 1) 
                               (MS x1009 y20 p11))) 
                       (exists ((x1010 Int)) 
                           (and 
                               (length p11 x1010) 
                               (MS x1010 x1100 p11))) 
                       (forall ((i59 Int)) 
                           (=> 
                               (and 
                                   (<= 1 i59) 
                                   (forall ((x1011 Int)) 
                                       (=> 
                                           (length p11 x1011) 
                                           (<= i59 (- x1011 1))))) 
                               (exists ((x1012 A) (x1013 A)) 
                                   (and 
                                       (MS i59 x1012 p11) 
                                       (exists ((x1014 Int)) 
                                           (and 
                                               (= x1014 (+ i59 1)) 
                                               (MS x1014 x1013 p11))) 
                                       (MS0 x1012 x1013 r))))) 
                       (MS0 x1100 x982 r)) 
                   (and 
                       (exists ((n62 Int)) 
                           (and 
                               (<= 0 n62) 
                               (forall ((x1015 Int) (x1016 A)) 
                                   (=> 
                                       (or 
                                           (exists ((i60 Int)) 
                                               (and 
                                                   (<= 1 i60) 
                                                   (forall ((x1017 Int)) 
                                                       (=> 
                                                           (length p11 x1017) 
                                                           (<= i60 x1017))) 
                                                   (= x1015 i60) 
                                                   (MS i60 x1016 p11))) 
                                           (exists ((i61 Int)) 
                                               (and 
                                                   (forall ((x1018 Int)) 
                                                       (=> 
                                                           (length p11 x1018) 
                                                           (<= (+ x1018 1) i61))) 
                                                   (forall ((x1019 Int) (x1020 Int)) 
                                                       (=> 
                                                           (and 
                                                               (length p11 x1020) 
                                                               (length q0 x1019)) 
                                                           (<= i61 (+ x1020 x1019)))) 
                                                   (= x1015 i61) 
                                                   (exists ((x1021 Int)) 
                                                       (and 
                                                           (forall ((x1022 Int)) 
                                                               (=> 
                                                                   (length p11 x1022) 
                                                                   (= x1021 (- i61 x1022)))) 
                                                           (MS x1021 x1016 q0)))))) 
                                       (and 
                                           (<= 1 x1015) 
                                           (<= x1015 n62)))) 
                               (forall ((x1023 Int) (x1024 A) (x1025 A)) 
                                   (=> 
                                       (and 
                                           (or 
                                               (exists ((i62 Int)) 
                                                   (and 
                                                       (<= 1 i62) 
                                                       (forall ((x1026 Int)) 
                                                           (=> 
                                                               (length p11 x1026) 
                                                               (<= i62 x1026))) 
                                                       (= x1023 i62) 
                                                       (MS i62 x1024 p11))) 
                                               (exists ((i63 Int)) 
                                                   (and 
                                                       (forall ((x1027 Int)) 
                                                           (=> 
                                                               (length p11 x1027) 
                                                               (<= (+ x1027 1) i63))) 
                                                       (forall ((x1028 Int) (x1029 Int)) 
                                                           (=> 
                                                               (and 
                                                                   (length p11 x1029) 
                                                                   (length q0 x1028)) 
                                                               (<= i63 (+ x1029 x1028)))) 
                                                       (= x1023 i63) 
                                                       (exists ((x1030 Int)) 
                                                           (and 
                                                               (forall ((x1031 Int)) 
                                                                   (=> 
                                                                       (length p11 x1031) 
                                                                       (= x1030 (- i63 x1031)))) 
                                                               (MS x1030 x1024 q0)))))) 
                                           (or 
                                               (exists ((i64 Int)) 
                                                   (and 
                                                       (<= 1 i64) 
                                                       (forall ((x1032 Int)) 
                                                           (=> 
                                                               (length p11 x1032) 
                                                               (<= i64 x1032))) 
                                                       (= x1023 i64) 
                                                       (MS i64 x1025 p11))) 
                                               (exists ((i65 Int)) 
                                                   (and 
                                                       (forall ((x1033 Int)) 
                                                           (=> 
                                                               (length p11 x1033) 
                                                               (<= (+ x1033 1) i65))) 
                                                       (forall ((x1034 Int) (x1035 Int)) 
                                                           (=> 
                                                               (and 
                                                                   (length p11 x1035) 
                                                                   (length q0 x1034)) 
                                                               (<= i65 (+ x1035 x1034)))) 
                                                       (= x1023 i65) 
                                                       (exists ((x1036 Int)) 
                                                           (and 
                                                               (forall ((x1037 Int)) 
                                                                   (=> 
                                                                       (length p11 x1037) 
                                                                       (= x1036 (- i65 x1037)))) 
                                                               (MS x1036 x1025 q0))))))) 
                                       (= x1024 x1025))) 
                               (forall ((x1038 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x1038) 
                                           (<= x1038 n62)) 
                                       (or 
                                           (exists ((x1039 A)) 
                                               (exists ((i66 Int)) 
                                                   (and 
                                                       (<= 1 i66) 
                                                       (forall ((x1040 Int)) 
                                                           (=> 
                                                               (length p11 x1040) 
                                                               (<= i66 x1040))) 
                                                       (= x1038 i66) 
                                                       (MS i66 x1039 p11)))) 
                                           (exists ((x1041 A)) 
                                               (exists ((i67 Int)) 
                                                   (and 
                                                       (forall ((x1042 Int)) 
                                                           (=> 
                                                               (length p11 x1042) 
                                                               (<= (+ x1042 1) i67))) 
                                                       (forall ((x1043 Int) (x1044 Int)) 
                                                           (=> 
                                                               (and 
                                                                   (length p11 x1044) 
                                                                   (length q0 x1043)) 
                                                               (<= i67 (+ x1044 x1043)))) 
                                                       (= x1038 i67) 
                                                       (exists ((x1045 Int)) 
                                                           (and 
                                                               (forall ((x1046 Int)) 
                                                                   (=> 
                                                                       (length p11 x1046) 
                                                                       (= x1045 (- i67 x1046)))) 
                                                               (MS x1045 x1041 q0))))))))))) 
                       (forall ((x1047 A)) 
                           (=> 
                               (or 
                                   (exists ((x1048 Int)) 
                                       (exists ((i68 Int)) 
                                           (and 
                                               (<= 1 i68) 
                                               (forall ((x1049 Int)) 
                                                   (=> 
                                                       (length p11 x1049) 
                                                       (<= i68 x1049))) 
                                               (= x1048 i68) 
                                               (MS i68 x1047 p11)))) 
                                   (exists ((x1050 Int)) 
                                       (exists ((i69 Int)) 
                                           (and 
                                               (forall ((x1051 Int)) 
                                                   (=> 
                                                       (length p11 x1051) 
                                                       (<= (+ x1051 1) i69))) 
                                               (forall ((x1052 Int) (x1053 Int)) 
                                                   (=> 
                                                       (and 
                                                           (length p11 x1053) 
                                                           (length q0 x1052)) 
                                                       (<= i69 (+ x1053 x1052)))) 
                                               (= x1050 i69) 
                                               (exists ((x1054 Int)) 
                                                   (and 
                                                       (forall ((x1055 Int)) 
                                                           (=> 
                                                               (length p11 x1055) 
                                                               (= x1054 (- i69 x1055)))) 
                                                       (MS x1054 x1047 q0))))))) 
                               (MS1 x1047 a))) 
                       (forall ((x1056 Int)) 
                           (=> 
                               (exists ((x1057 PZA)) 
                                   (and 
                                       (forall ((x1058 Int) (x1059 A)) 
                                           (= 
                                               (MS x1058 x1059 x1057) 
                                               (or 
                                                   (exists ((i70 Int)) 
                                                       (and 
                                                           (<= 1 i70) 
                                                           (forall ((x1060 Int)) 
                                                               (=> 
                                                                   (length p11 x1060) 
                                                                   (<= i70 x1060))) 
                                                           (= x1058 i70) 
                                                           (MS i70 x1059 p11))) 
                                                   (exists ((i71 Int)) 
                                                       (and 
                                                           (forall ((x1061 Int)) 
                                                               (=> 
                                                                   (length p11 x1061) 
                                                                   (<= (+ x1061 1) i71))) 
                                                           (forall ((x1062 Int) (x1063 Int)) 
                                                               (=> 
                                                                   (and 
                                                                       (length p11 x1063) 
                                                                       (length q0 x1062)) 
                                                                   (<= i71 (+ x1063 x1062)))) 
                                                           (= x1058 i71) 
                                                           (exists ((x1064 Int)) 
                                                               (and 
                                                                   (forall ((x1065 Int)) 
                                                                       (=> 
                                                                           (length p11 x1065) 
                                                                           (= x1064 (- i71 x1065)))) 
                                                                   (MS x1064 x1059 q0)))))))) 
                                       (length x1057 x1056))) 
                               (< 1 x1056))) 
                       (or 
                           (exists ((i72 Int)) 
                               (and 
                                   (<= 1 i72) 
                                   (forall ((x1066 Int)) 
                                       (=> 
                                           (length p11 x1066) 
                                           (<= i72 x1066))) 
                                   (= 1 i72) 
                                   (MS i72 y20 p11))) 
                           (exists ((i73 Int)) 
                               (and 
                                   (forall ((x1067 Int)) 
                                       (=> 
                                           (length p11 x1067) 
                                           (<= (+ x1067 1) i73))) 
                                   (forall ((x1068 Int) (x1069 Int)) 
                                       (=> 
                                           (and 
                                               (length p11 x1069) 
                                               (length q0 x1068)) 
                                           (<= i73 (+ x1069 x1068)))) 
                                   (= 1 i73) 
                                   (exists ((x1070 Int)) 
                                       (and 
                                           (forall ((x1071 Int)) 
                                               (=> 
                                                   (length p11 x1071) 
                                                   (= x1070 (- i73 x1071)))) 
                                           (MS x1070 y20 q0)))))) 
                       (or 
                           (exists ((i74 Int)) 
                               (and 
                                   (<= 1 i74) 
                                   (forall ((x1072 Int)) 
                                       (=> 
                                           (length p11 x1072) 
                                           (<= i74 x1072))) 
                                   (exists ((x1073 PZA)) 
                                       (and 
                                           (forall ((x1074 Int) (x1075 A)) 
                                               (= 
                                                   (MS x1074 x1075 x1073) 
                                                   (or 
                                                       (exists ((i75 Int)) 
                                                           (and 
                                                               (<= 1 i75) 
                                                               (forall ((x1076 Int)) 
                                                                   (=> 
                                                                       (length p11 x1076) 
                                                                       (<= i75 x1076))) 
                                                               (= x1074 i75) 
                                                               (MS i75 x1075 p11))) 
                                                       (exists ((i76 Int)) 
                                                           (and 
                                                               (forall ((x1077 Int)) 
                                                                   (=> 
                                                                       (length p11 x1077) 
                                                                       (<= (+ x1077 1) i76))) 
                                                               (forall ((x1078 Int) (x1079 Int)) 
                                                                   (=> 
                                                                       (and 
                                                                           (length p11 x1079) 
                                                                           (length q0 x1078)) 
                                                                       (<= i76 (+ x1079 x1078)))) 
                                                               (= x1074 i76) 
                                                               (exists ((x1080 Int)) 
                                                                   (and 
                                                                       (forall ((x1081 Int)) 
                                                                           (=> 
                                                                               (length p11 x1081) 
                                                                               (= x1080 (- i76 x1081)))) 
                                                                       (MS x1080 x1075 q0)))))))) 
                                           (length x1073 i74))) 
                                   (MS i74 y15 p11))) 
                           (exists ((i77 Int)) 
                               (and 
                                   (forall ((x1082 Int)) 
                                       (=> 
                                           (length p11 x1082) 
                                           (<= (+ x1082 1) i77))) 
                                   (forall ((x1083 Int) (x1084 Int)) 
                                       (=> 
                                           (and 
                                               (length p11 x1084) 
                                               (length q0 x1083)) 
                                           (<= i77 (+ x1084 x1083)))) 
                                   (exists ((x1085 PZA)) 
                                       (and 
                                           (forall ((x1086 Int) (x1087 A)) 
                                               (= 
                                                   (MS x1086 x1087 x1085) 
                                                   (or 
                                                       (exists ((i78 Int)) 
                                                           (and 
                                                               (<= 1 i78) 
                                                               (forall ((x1088 Int)) 
                                                                   (=> 
                                                                       (length p11 x1088) 
                                                                       (<= i78 x1088))) 
                                                               (= x1086 i78) 
                                                               (MS i78 x1087 p11))) 
                                                       (exists ((i79 Int)) 
                                                           (and 
                                                               (forall ((x1089 Int)) 
                                                                   (=> 
                                                                       (length p11 x1089) 
                                                                       (<= (+ x1089 1) i79))) 
                                                               (forall ((x1090 Int) (x1091 Int)) 
                                                                   (=> 
                                                                       (and 
                                                                           (length p11 x1091) 
                                                                           (length q0 x1090)) 
                                                                       (<= i79 (+ x1091 x1090)))) 
                                                               (= x1086 i79) 
                                                               (exists ((x1092 Int)) 
                                                                   (and 
                                                                       (forall ((x1093 Int)) 
                                                                           (=> 
                                                                               (length p11 x1093) 
                                                                               (= x1092 (- i79 x1093)))) 
                                                                       (MS x1092 x1087 q0)))))))) 
                                           (length x1085 i77))) 
                                   (exists ((x1094 Int)) 
                                       (and 
                                           (forall ((x1095 Int)) 
                                               (=> 
                                                   (length p11 x1095) 
                                                   (= x1094 (- i77 x1095)))) 
                                           (MS x1094 y15 q0)))))) 
                       (forall ((i80 Int)) 
                           (=> 
                               (and 
                                   (<= 1 i80) 
                                   (forall ((x1096 Int)) 
                                       (=> 
                                           (exists ((x1097 PZA)) 
                                               (and 
                                                   (forall ((x1098 Int) (x1099 A)) 
                                                       (= 
                                                           (MS x1098 x1099 x1097) 
                                                           (or 
                                                               (exists ((i81 Int)) 
                                                                   (and 
                                                                       (<= 1 i81) 
                                                                       (forall ((x1101 Int)) 
                                                                           (=> 
                                                                               (length p11 x1101) 
                                                                               (<= i81 x1101))) 
                                                                       (= x1098 i81) 
                                                                       (MS i81 x1099 p11))) 
                                                               (exists ((i82 Int)) 
                                                                   (and 
                                                                       (forall ((x1102 Int)) 
                                                                           (=> 
                                                                               (length p11 x1102) 
                                                                               (<= (+ x1102 1) i82))) 
                                                                       (forall ((x1103 Int) (x1104 Int)) 
                                                                           (=> 
                                                                               (and 
                                                                                   (length p11 x1104) 
                                                                                   (length q0 x1103)) 
                                                                               (<= i82 (+ x1104 x1103)))) 
                                                                       (= x1098 i82) 
                                                                       (exists ((x1105 Int)) 
                                                                           (and 
                                                                               (forall ((x1106 Int)) 
                                                                                   (=> 
                                                                                       (length p11 x1106) 
                                                                                       (= x1105 (- i82 x1106)))) 
                                                                               (MS x1105 x1099 q0)))))))) 
                                                   (length x1097 x1096))) 
                                           (<= i80 (- x1096 1))))) 
                               (exists ((x1107 A) (x1108 A)) 
                                   (and 
                                       (or 
                                           (exists ((i83 Int)) 
                                               (and 
                                                   (<= 1 i83) 
                                                   (forall ((x1109 Int)) 
                                                       (=> 
                                                           (length p11 x1109) 
                                                           (<= i83 x1109))) 
                                                   (= i80 i83) 
                                                   (MS i83 x1107 p11))) 
                                           (exists ((i84 Int)) 
                                               (and 
                                                   (forall ((x1110 Int)) 
                                                       (=> 
                                                           (length p11 x1110) 
                                                           (<= (+ x1110 1) i84))) 
                                                   (forall ((x1111 Int) (x1112 Int)) 
                                                       (=> 
                                                           (and 
                                                               (length p11 x1112) 
                                                               (length q0 x1111)) 
                                                           (<= i84 (+ x1112 x1111)))) 
                                                   (= i80 i84) 
                                                   (exists ((x1113 Int)) 
                                                       (and 
                                                           (forall ((x1114 Int)) 
                                                               (=> 
                                                                   (length p11 x1114) 
                                                                   (= x1113 (- i84 x1114)))) 
                                                           (MS x1113 x1107 q0)))))) 
                                       (or 
                                           (exists ((i85 Int)) 
                                               (and 
                                                   (<= 1 i85) 
                                                   (forall ((x1115 Int)) 
                                                       (=> 
                                                           (length p11 x1115) 
                                                           (<= i85 x1115))) 
                                                   (= (+ i80 1) i85) 
                                                   (MS i85 x1108 p11))) 
                                           (exists ((i86 Int)) 
                                               (and 
                                                   (forall ((x1116 Int)) 
                                                       (=> 
                                                           (length p11 x1116) 
                                                           (<= (+ x1116 1) i86))) 
                                                   (forall ((x1117 Int) (x1118 Int)) 
                                                       (=> 
                                                           (and 
                                                               (length p11 x1118) 
                                                               (length q0 x1117)) 
                                                           (<= i86 (+ x1118 x1117)))) 
                                                   (= (+ i80 1) i86) 
                                                   (exists ((x1119 Int)) 
                                                       (and 
                                                           (forall ((x1120 Int)) 
                                                               (=> 
                                                                   (length p11 x1120) 
                                                                   (= x1119 (- i86 x1120)))) 
                                                           (MS x1119 x1108 q0)))))) 
                                       (MS0 x1107 x1108 r))))))))
         :named hyp40))
(assert (! (forall ((x1121 A) (y16 A) (p12 PZA)) 
               (=> 
                   (and 
                       (exists ((n63 Int)) 
                           (and 
                               (<= 0 n63) 
                               (forall ((x1122 Int) (x1123 A)) 
                                   (=> 
                                       (MS x1122 x1123 p12) 
                                       (and 
                                           (<= 1 x1122) 
                                           (<= x1122 n63)))) 
                               (forall ((x1124 Int) (x1125 A) (x1126 A)) 
                                   (=> 
                                       (and 
                                           (MS x1124 x1125 p12) 
                                           (MS x1124 x1126 p12)) 
                                       (= x1125 x1126))) 
                               (forall ((x1127 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x1127) 
                                           (<= x1127 n63)) 
                                       (exists ((x1128 A)) 
                                           (MS x1127 x1128 p12)))))) 
                       (forall ((x1129 A)) 
                           (=> 
                               (exists ((x1130 Int)) 
                                   (MS x1130 x1129 p12)) 
                               (MS1 x1129 a))) 
                       (forall ((x1131 Int)) 
                           (=> 
                               (length p12 x1131) 
                               (< 1 x1131))) 
                       (exists ((x1132 Int)) 
                           (and 
                               (= x1132 1) 
                               (MS x1132 x1121 p12))) 
                       (exists ((x1133 Int)) 
                           (and 
                               (length p12 x1133) 
                               (MS x1133 y16 p12))) 
                       (forall ((i87 Int)) 
                           (=> 
                               (and 
                                   (<= 1 i87) 
                                   (forall ((x1134 Int)) 
                                       (=> 
                                           (length p12 x1134) 
                                           (<= i87 (- x1134 1))))) 
                               (exists ((x1135 A) (x1136 A)) 
                                   (and 
                                       (MS i87 x1135 p12) 
                                       (exists ((x1137 Int)) 
                                           (and 
                                               (= x1137 (+ i87 1)) 
                                               (MS x1137 x1136 p12))) 
                                       (MS0 x1135 x1136 r)))))) 
                   (and 
                       (exists ((n64 Int)) 
                           (and 
                               (<= 0 n64) 
                               (forall ((x1138 Int) (x1139 A)) 
                                   (=> 
                                       (exists ((i88 Int)) 
                                           (and 
                                               (<= 1 i88) 
                                               (forall ((x1140 Int)) 
                                                   (=> 
                                                       (length p12 x1140) 
                                                       (<= i88 x1140))) 
                                               (= x1138 i88) 
                                               (exists ((x1141 Int)) 
                                                   (and 
                                                       (forall ((x1142 Int)) 
                                                           (=> 
                                                               (length p12 x1142) 
                                                               (= x1141 (+ (- x1142 i88) 1)))) 
                                                       (MS x1141 x1139 p12))))) 
                                       (and 
                                           (<= 1 x1138) 
                                           (<= x1138 n64)))) 
                               (forall ((x1143 Int) (x1144 A) (x1145 A)) 
                                   (=> 
                                       (and 
                                           (exists ((i89 Int)) 
                                               (and 
                                                   (<= 1 i89) 
                                                   (forall ((x1146 Int)) 
                                                       (=> 
                                                           (length p12 x1146) 
                                                           (<= i89 x1146))) 
                                                   (= x1143 i89) 
                                                   (exists ((x1147 Int)) 
                                                       (and 
                                                           (forall ((x1148 Int)) 
                                                               (=> 
                                                                   (length p12 x1148) 
                                                                   (= x1147 (+ (- x1148 i89) 1)))) 
                                                           (MS x1147 x1144 p12))))) 
                                           (exists ((i90 Int)) 
                                               (and 
                                                   (<= 1 i90) 
                                                   (forall ((x1149 Int)) 
                                                       (=> 
                                                           (length p12 x1149) 
                                                           (<= i90 x1149))) 
                                                   (= x1143 i90) 
                                                   (exists ((x1150 Int)) 
                                                       (and 
                                                           (forall ((x1151 Int)) 
                                                               (=> 
                                                                   (length p12 x1151) 
                                                                   (= x1150 (+ (- x1151 i90) 1)))) 
                                                           (MS x1150 x1145 p12)))))) 
                                       (= x1144 x1145))) 
                               (forall ((x1152 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x1152) 
                                           (<= x1152 n64)) 
                                       (exists ((x1153 A) (i91 Int)) 
                                           (and 
                                               (<= 1 i91) 
                                               (forall ((x1154 Int)) 
                                                   (=> 
                                                       (length p12 x1154) 
                                                       (<= i91 x1154))) 
                                               (= x1152 i91) 
                                               (exists ((x1155 Int)) 
                                                   (and 
                                                       (forall ((x1156 Int)) 
                                                           (=> 
                                                               (length p12 x1156) 
                                                               (= x1155 (+ (- x1156 i91) 1)))) 
                                                       (MS x1155 x1153 p12))))))))) 
                       (forall ((i92 Int)) 
                           (=> 
                               (and 
                                   (<= 1 i92) 
                                   (forall ((x1157 Int)) 
                                       (=> 
                                           (length p12 x1157) 
                                           (<= i92 x1157)))) 
                               (exists ((x1158 A)) 
                                   (and 
                                       (exists ((x1159 Int)) 
                                           (and 
                                               (forall ((x1160 Int)) 
                                                   (=> 
                                                       (length p12 x1160) 
                                                       (= x1159 (+ (- x1160 i92) 1)))) 
                                               (MS x1159 x1158 p12))) 
                                       (MS1 x1158 a))))) 
                       (forall ((x1161 Int)) 
                           (=> 
                               (exists ((x1162 PZA)) 
                                   (and 
                                       (forall ((x1163 Int) (x1164 A)) 
                                           (= 
                                               (MS x1163 x1164 x1162) 
                                               (exists ((i93 Int)) 
                                                   (and 
                                                       (<= 1 i93) 
                                                       (forall ((x1165 Int)) 
                                                           (=> 
                                                               (length p12 x1165) 
                                                               (<= i93 x1165))) 
                                                       (= x1163 i93) 
                                                       (exists ((x1166 Int)) 
                                                           (and 
                                                               (forall ((x1167 Int)) 
                                                                   (=> 
                                                                       (length p12 x1167) 
                                                                       (= x1166 (+ (- x1167 i93) 1)))) 
                                                               (MS x1166 x1164 p12))))))) 
                                       (length x1162 x1161))) 
                               (< 1 x1161))) 
                       (exists ((x1168 Int)) 
                           (and 
                               (forall ((x1169 Int)) 
                                   (=> 
                                       (length p12 x1169) 
                                       (= x1168 (+ (- x1169 1) 1)))) 
                               (MS x1168 y16 p12))) 
                       (exists ((x1170 Int)) 
                           (and 
                               (forall ((x1171 Int) (x1172 Int)) 
                                   (=> 
                                       (and 
                                           (length p12 x1172) 
                                           (exists ((x1173 PZA)) 
                                               (and 
                                                   (forall ((x1174 Int) (x1175 A)) 
                                                       (= 
                                                           (MS x1174 x1175 x1173) 
                                                           (exists ((i94 Int)) 
                                                               (and 
                                                                   (<= 1 i94) 
                                                                   (forall ((x1176 Int)) 
                                                                       (=> 
                                                                           (length p12 x1176) 
                                                                           (<= i94 x1176))) 
                                                                   (= x1174 i94) 
                                                                   (exists ((x1177 Int)) 
                                                                       (and 
                                                                           (forall ((x1178 Int)) 
                                                                               (=> 
                                                                                   (length p12 x1178) 
                                                                                   (= x1177 (+ (- x1178 i94) 1)))) 
                                                                           (MS x1177 x1175 p12))))))) 
                                                   (length x1173 x1171)))) 
                                       (= x1170 (+ (- x1172 x1171) 1)))) 
                               (MS x1170 x1121 p12))) 
                       (forall ((i95 Int)) 
                           (=> 
                               (and 
                                   (<= 1 i95) 
                                   (forall ((x1179 Int)) 
                                       (=> 
                                           (exists ((x1180 PZA)) 
                                               (and 
                                                   (forall ((x1181 Int) (x1182 A)) 
                                                       (= 
                                                           (MS x1181 x1182 x1180) 
                                                           (exists ((i96 Int)) 
                                                               (and 
                                                                   (<= 1 i96) 
                                                                   (forall ((x1183 Int)) 
                                                                       (=> 
                                                                           (length p12 x1183) 
                                                                           (<= i96 x1183))) 
                                                                   (= x1181 i96) 
                                                                   (exists ((x1184 Int)) 
                                                                       (and 
                                                                           (forall ((x1185 Int)) 
                                                                               (=> 
                                                                                   (length p12 x1185) 
                                                                                   (= x1184 (+ (- x1185 i96) 1)))) 
                                                                           (MS x1184 x1182 p12))))))) 
                                                   (length x1180 x1179))) 
                                           (<= i95 (- x1179 1))))) 
                               (exists ((x1186 A) (x1187 A)) 
                                   (and 
                                       (exists ((x1188 Int)) 
                                           (and 
                                               (forall ((x1189 Int)) 
                                                   (=> 
                                                       (length p12 x1189) 
                                                       (= x1188 (+ (- x1189 i95) 1)))) 
                                               (MS x1188 x1186 p12))) 
                                       (exists ((x1190 Int)) 
                                           (and 
                                               (forall ((x1191 Int)) 
                                                   (=> 
                                                       (length p12 x1191) 
                                                       (= x1190 (+ (- x1191 (+ i95 1)) 1)))) 
                                               (MS x1190 x1187 p12))) 
                                       (MS0 x1186 x1187 r))))))))
         :named hyp41))
(assert (! (exists ((x1192 A)) 
               (and 
                   (exists ((x1193 Int)) 
                       (and 
                           (= x1193 1) 
                           (MS x1193 x1192 p))) 
                   (MS1 x1192 a)))
         :named hyp42))
(assert (! (exists ((x1194 A)) 
               (and 
                   (exists ((x1195 Int)) 
                       (and 
                           (length p x1195) 
                           (MS x1195 x1194 p))) 
                   (MS1 x1194 a)))
         :named hyp43))
(assert (! (forall ((x1196 A) (x1197 A)) 
               (=> 
                   (MS0 x1196 x1197 r) 
                   (and 
                       (MS1 x1196 a) 
                       (MS1 x1197 a))))
         :named hyp44))
(assert (! (not 
               (forall ((x1198 A) (x1199 A)) 
                   (not 
                       (MS0 x1198 x1199 r))))
         :named hyp45))
(assert (! (forall ((x1200 A) (x1201 A)) 
               (=> 
                   (MS0 x1200 x1201 c) 
                   (and 
                       (MS1 x1200 a) 
                       (MS1 x1201 a))))
         :named hyp46))
(assert (! (forall ((x1202 A) (x1203 A)) 
               (=> 
                   (MS0 x1202 x1203 r) 
                   (MS0 x1202 x1203 c)))
         :named hyp47))
(assert (! (forall ((x1204 A) (x1205 A)) 
               (=> 
                   (exists ((x1206 A)) 
                       (and 
                           (MS0 x1204 x1206 c) 
                           (MS0 x1206 x1205 r))) 
                   (MS0 x1204 x1205 c)))
         :named hyp48))
(assert (! (forall ((s41 PAA)) 
               (=> 
                   (and 
                       (forall ((x1207 A) (x1208 A)) 
                           (=> 
                               (MS0 x1207 x1208 s41) 
                               (and 
                                   (MS1 x1207 a) 
                                   (MS1 x1208 a)))) 
                       (forall ((x1209 A) (x1210 A)) 
                           (=> 
                               (MS0 x1209 x1210 r) 
                               (MS0 x1209 x1210 s41))) 
                       (forall ((x1211 A) (x1212 A)) 
                           (=> 
                               (exists ((x1213 A)) 
                                   (and 
                                       (MS0 x1211 x1213 s41) 
                                       (MS0 x1213 x1212 r))) 
                               (MS0 x1211 x1212 s41)))) 
                   (forall ((x1214 A) (x1215 A)) 
                       (=> 
                           (MS0 x1214 x1215 c) 
                           (MS0 x1214 x1215 s41)))))
         :named hyp49))
(assert (! (forall ((x1216 A)) 
               (= 
                   (exists ((x1217 A)) 
                       (MS0 x1216 x1217 r)) 
                   (MS1 x1216 a)))
         :named hyp50))
(assert (! (forall ((x1218 A)) 
               (= 
                   (exists ((x1219 A)) 
                       (MS0 x1218 x1219 c)) 
                   (MS1 x1218 a)))
         :named hyp51))
(assert (! (forall ((x1220 A)) 
               (=> 
                   (exists ((x1221 A)) 
                       (MS0 x1220 x1221 r)) 
                   (exists ((x1222 A)) 
                       (MS0 x1220 x1222 c))))
         :named hyp52))
(assert (! (forall ((x1223 A) (x1224 A)) 
               (= 
                   (MS0 x1223 x1224 c) 
                   (or 
                       (MS0 x1223 x1224 r) 
                       (exists ((x1225 A)) 
                           (and 
                               (MS0 x1223 x1225 c) 
                               (MS0 x1225 x1224 r))))))
         :named hyp53))
(assert (! (forall ((x1226 A) (y17 A)) 
               (=> 
                   (and 
                       (MS1 x1226 a) 
                       (MS1 y17 a)) 
                   (forall ((s42 PZA) (n65 Int)) 
                       (=> 
                           (and 
                               (<= 0 n65) 
                               (< 1 n65) 
                               (forall ((x1227 Int) (x1228 A)) 
                                   (=> 
                                       (MS x1227 x1228 s42) 
                                       (and 
                                           (<= 1 x1227) 
                                           (<= x1227 n65) 
                                           (MS1 x1228 a)))) 
                               (forall ((x1229 Int) (x1230 A) (x1231 A)) 
                                   (=> 
                                       (and 
                                           (MS x1229 x1230 s42) 
                                           (MS x1229 x1231 s42)) 
                                       (= x1230 x1231))) 
                               (forall ((x1232 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x1232) 
                                           (<= x1232 n65)) 
                                       (exists ((x1233 A)) 
                                           (MS x1232 x1233 s42))))) 
                           (and 
                               (exists ((x1234 A) (x1235 Int)) 
                                   (and 
                                       (= x1235 1) 
                                       (MS x1235 x1234 s42))) 
                               (forall ((x1236 Int) (x1237 A) (x1238 A)) 
                                   (=> 
                                       (and 
                                           (MS x1236 x1237 s42) 
                                           (MS x1236 x1238 s42)) 
                                       (= x1237 x1238))) 
                               (=> 
                                   (exists ((x1239 Int)) 
                                       (and 
                                           (= x1239 1) 
                                           (MS x1239 x1226 s42))) 
                                   (and 
                                       (exists ((x1240 A)) 
                                           (MS n65 x1240 s42)) 
                                       (=> 
                                           (MS n65 y17 s42) 
                                           (forall ((i97 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 i97) 
                                                       (<= i97 (- n65 1))) 
                                                   (and 
                                                       (exists ((x1241 A)) 
                                                           (MS i97 x1241 s42)) 
                                                       (exists ((x1242 A) (x1243 Int)) 
                                                           (and 
                                                               (= x1243 (+ i97 1)) 
                                                               (MS x1243 x1242 s42))))))))))))))
         :named hyp54))
(assert (! (forall ((x1244 A) (x1245 A)) 
               (=> 
                   (exists ((x1246 PZA)) 
                       (path x1244 x1245 x1246)) 
                   (MS0 x1244 x1245 c)))
         :named hyp55))
(assert (! (forall ((x1247 A) (x1248 A)) 
               (=> 
                   (MS0 x1247 x1248 c) 
                   (exists ((x1249 PZA)) 
                       (path x1247 x1248 x1249))))
         :named hyp56))
(assert (! (forall ((x1250 A) (x1251 A)) 
               (=> 
                   (and 
                       (MS1 x1250 a) 
                       (MS1 x1251 a)) 
                   (exists ((x1252 PZA)) 
                       (path x1250 x1251 x1252))))
         :named hyp57))
(assert (! (forall ((n66 Int) (s43 PZA)) 
               (=> 
                   (and 
                       (<= 0 n66) 
                       (forall ((x1253 Int) (x1254 A)) 
                           (=> 
                               (MS x1253 x1254 s43) 
                               (and 
                                   (<= 1 x1253) 
                                   (<= x1253 n66)))) 
                       (forall ((x1255 Int) (x1256 A) (x1257 A)) 
                           (=> 
                               (and 
                                   (MS x1255 x1256 s43) 
                                   (MS x1255 x1257 s43)) 
                               (= x1256 x1257))) 
                       (forall ((x1258 Int)) 
                           (=> 
                               (and 
                                   (<= 1 x1258) 
                                   (<= x1258 n66)) 
                               (exists ((x1259 A)) 
                                   (MS x1258 x1259 s43))))) 
                   (seq s43)))
         :named hyp58))
(assert (! (and 
               (forall ((x1260 PZA) (x1261 Int)) 
                   (=> 
                       (length x1260 x1261) 
                       (and 
                           (seq x1260) 
                           (<= 0 x1261)))) 
               (forall ((x1262 PZA) (x1263 Int) (x1264 Int)) 
                   (=> 
                       (and 
                           (length x1262 x1263) 
                           (length x1262 x1264)) 
                       (= x1263 x1264))) 
               (forall ((x1265 PZA)) 
                   (=> 
                       (seq x1265) 
                       (exists ((x1266 Int)) 
                           (length x1265 x1266)))))
         :named hyp59))
(assert (! (forall ((s44 PZA)) 
               (=> 
                   (seq s44) 
                   (and 
                       (forall ((x1267 Int) (x1268 A)) 
                           (=> 
                               (MS x1267 x1268 s44) 
                               (and 
                                   (<= 1 x1267) 
                                   (forall ((x1269 Int)) 
                                       (=> 
                                           (length s44 x1269) 
                                           (<= x1267 x1269)))))) 
                       (forall ((x1270 Int) (x1271 A) (x1272 A)) 
                           (=> 
                               (and 
                                   (MS x1270 x1271 s44) 
                                   (MS x1270 x1272 s44)) 
                               (= x1271 x1272))) 
                       (forall ((x1273 Int)) 
                           (=> 
                               (and 
                                   (<= 1 x1273) 
                                   (forall ((x1274 Int)) 
                                       (=> 
                                           (length s44 x1274) 
                                           (<= x1273 x1274)))) 
                               (exists ((x1275 A)) 
                                   (MS x1273 x1275 s44)))))))
         :named hyp60))
(assert (! (forall ((x1276 PZA) (x1277 PZA) (x1278 PZA)) 
               (= 
                   (cnc x1276 x1277 x1278) 
                   (exists ((s112 PZA) (s211 PZA)) 
                       (and 
                           (seq s112) 
                           (seq s211) 
                           (forall ((x1279 Int) (x1280 A)) 
                               (= 
                                   (MS x1279 x1280 x1276) 
                                   (MS x1279 x1280 s112))) 
                           (forall ((x1281 Int) (x1282 A)) 
                               (= 
                                   (MS x1281 x1282 x1277) 
                                   (MS x1281 x1282 s211))) 
                           (forall ((x1283 Int) (x1284 A)) 
                               (= 
                                   (MS x1283 x1284 x1278) 
                                   (or 
                                       (exists ((i98 Int)) 
                                           (and 
                                               (<= 1 i98) 
                                               (forall ((x1285 Int)) 
                                                   (=> 
                                                       (length s112 x1285) 
                                                       (<= i98 x1285))) 
                                               (= x1283 i98) 
                                               (MS i98 x1284 s112))) 
                                       (exists ((i99 Int)) 
                                           (and 
                                               (forall ((x1286 Int)) 
                                                   (=> 
                                                       (length s112 x1286) 
                                                       (<= (+ x1286 1) i99))) 
                                               (forall ((x1287 Int) (x1288 Int)) 
                                                   (=> 
                                                       (and 
                                                           (length s112 x1288) 
                                                           (length s211 x1287)) 
                                                       (<= i99 (+ x1288 x1287)))) 
                                               (= x1283 i99) 
                                               (exists ((x1289 Int)) 
                                                   (and 
                                                       (forall ((x1290 Int)) 
                                                           (=> 
                                                               (length s112 x1290) 
                                                               (= x1289 (- i99 x1290)))) 
                                                       (MS x1289 x1284 s211))))))))))))
         :named hyp61))
(assert (! (and 
               (forall ((x1291 PZA) (x1292 PZA) (x1293 PZA)) 
                   (=> 
                       (cnc x1291 x1292 x1293) 
                       (and 
                           (seq x1291) 
                           (seq x1292) 
                           (seq x1293)))) 
               (forall ((x1294 PZA) (x1295 PZA) (x1296 PZA) (x1297 PZA)) 
                   (=> 
                       (and 
                           (cnc x1294 x1295 x1296) 
                           (cnc x1294 x1295 x1297)) 
                       (forall ((x1298 Int) (x1299 A)) 
                           (= 
                               (MS x1298 x1299 x1296) 
                               (MS x1298 x1299 x1297))))) 
               (forall ((x1300 PZA) (x1301 PZA)) 
                   (=> 
                       (and 
                           (seq x1300) 
                           (seq x1301)) 
                       (exists ((x1302 PZA)) 
                           (cnc x1300 x1301 x1302)))))
         :named hyp62))
(assert (! (forall ((s113 PZA) (s212 PZA)) 
               (=> 
                   (and 
                       (seq s113) 
                       (seq s212)) 
                   (exists ((x1303 PZA) (x1304 Int)) 
                       (and 
                           (cnc s113 s212 x1303) 
                           (forall ((x1305 Int) (x1306 Int)) 
                               (=> 
                                   (and 
                                       (length s113 x1306) 
                                       (length s212 x1305)) 
                                   (= x1304 (+ x1306 x1305)))) 
                           (length x1303 x1304)))))
         :named hyp63))
(assert (! (forall ((s114 PZA) (s213 PZA)) 
               (=> 
                   (and 
                       (seq s114) 
                       (seq s213)) 
                   (forall ((x1307 Int)) 
                       (= 
                           (exists ((x1308 A) (x1309 PZA)) 
                               (and 
                                   (cnc s114 s213 x1309) 
                                   (MS x1307 x1308 x1309))) 
                           (and 
                               (<= 1 x1307) 
                               (forall ((x1310 Int) (x1311 Int)) 
                                   (=> 
                                       (and 
                                           (length s114 x1311) 
                                           (length s213 x1310)) 
                                       (<= x1307 (+ x1311 x1310)))))))))
         :named hyp64))
(assert (! (forall ((s115 PZA) (s214 PZA)) 
               (=> 
                   (and 
                       (seq s115) 
                       (seq s214)) 
                   (forall ((x1312 A)) 
                       (= 
                           (exists ((x1313 Int) (x1314 PZA)) 
                               (and 
                                   (cnc s115 s214 x1314) 
                                   (MS x1313 x1312 x1314))) 
                           (or 
                               (exists ((x1315 Int)) 
                                   (MS x1315 x1312 s115)) 
                               (exists ((x1316 Int)) 
                                   (MS x1316 x1312 s214)))))))
         :named hyp65))
(assert (! (forall ((s116 PZA) (s215 PZA) (i100 Int)) 
               (=> 
                   (and 
                       (seq s116) 
                       (seq s215) 
                       (<= 1 i100) 
                       (forall ((x1317 Int)) 
                           (=> 
                               (length s116 x1317) 
                               (<= i100 x1317)))) 
                   (exists ((x1318 PZA)) 
                       (and 
                           (cnc s116 s215 x1318) 
                           (exists ((x1319 A)) 
                               (and 
                                   (MS i100 x1319 s116) 
                                   (MS i100 x1319 x1318)))))))
         :named hyp66))
(assert (! (forall ((s117 PZA) (s216 PZA) (i101 Int)) 
               (=> 
                   (and 
                       (seq s117) 
                       (seq s216) 
                       (forall ((x1320 Int)) 
                           (=> 
                               (length s117 x1320) 
                               (<= (+ x1320 1) i101))) 
                       (forall ((x1321 Int) (x1322 Int)) 
                           (=> 
                               (and 
                                   (length s117 x1322) 
                                   (length s216 x1321)) 
                               (<= i101 (+ x1322 x1321))))) 
                   (exists ((x1323 PZA)) 
                       (and 
                           (cnc s117 s216 x1323) 
                           (exists ((x1324 A)) 
                               (and 
                                   (exists ((x1325 Int)) 
                                       (and 
                                           (forall ((x1326 Int)) 
                                               (=> 
                                                   (length s117 x1326) 
                                                   (= x1325 (- i101 x1326)))) 
                                           (MS x1325 x1324 s216))) 
                                   (MS i101 x1324 x1323)))))))
         :named hyp67))
(assert (! (forall ((x1327 A) (y18 A)) 
               (=> 
                   (and 
                       (MS1 x1327 a) 
                       (MS1 y18 a)) 
                   (exists ((x1328 Int)) 
                       (and 
                           (exists ((x1329 PZA)) 
                               (and 
                                   (exists ((x1330 A) (x1331 A)) 
                                       (and 
                                           (= x1330 x1327) 
                                           (= x1331 y18) 
                                           (path x1330 x1331 x1329))) 
                                   (length x1329 x1328))) 
                           (forall ((x1332 Int)) 
                               (=> 
                                   (exists ((x1333 PZA)) 
                                       (and 
                                           (exists ((x1334 A) (x1335 A)) 
                                               (and 
                                                   (= x1334 x1327) 
                                                   (= x1335 y18) 
                                                   (path x1334 x1335 x1333))) 
                                           (length x1333 x1332))) 
                                   (<= x1328 x1332))) 
                           (dist x1327 y18 x1328)))))
         :named hyp68))
(assert (! (forall ((x1336 PZA) (x1337 PZA)) 
               (= 
                   (reverse x1336 x1337) 
                   (exists ((s45 PZA)) 
                       (and 
                           (seq s45) 
                           (forall ((x1338 Int) (x1339 A)) 
                               (= 
                                   (MS x1338 x1339 x1336) 
                                   (MS x1338 x1339 s45))) 
                           (forall ((x1340 Int) (x1341 A)) 
                               (= 
                                   (MS x1340 x1341 x1337) 
                                   (exists ((i102 Int)) 
                                       (and 
                                           (<= 1 i102) 
                                           (forall ((x1342 Int)) 
                                               (=> 
                                                   (length s45 x1342) 
                                                   (<= i102 x1342))) 
                                           (= x1340 i102) 
                                           (exists ((x1343 Int)) 
                                               (and 
                                                   (forall ((x1344 Int)) 
                                                       (=> 
                                                           (length s45 x1344) 
                                                           (= x1343 (+ (- x1344 i102) 1)))) 
                                                   (MS x1343 x1341 s45)))))))))))
         :named hyp69))
(assert (! (and 
               (forall ((x1345 PZA) (x1346 PZA)) 
                   (=> 
                       (reverse x1345 x1346) 
                       (and 
                           (seq x1345) 
                           (seq x1346)))) 
               (forall ((x1347 PZA) (x1348 PZA) (x1349 PZA)) 
                   (=> 
                       (and 
                           (reverse x1347 x1348) 
                           (reverse x1347 x1349)) 
                       (forall ((x1350 Int) (x1351 A)) 
                           (= 
                               (MS x1350 x1351 x1348) 
                               (MS x1350 x1351 x1349))))) 
               (forall ((x1352 PZA)) 
                   (=> 
                       (seq x1352) 
                       (exists ((x1353 PZA)) 
                           (reverse x1352 x1353)))))
         :named hyp70))
(assert (! (forall ((s46 PZA)) 
               (=> 
                   (seq s46) 
                   (exists ((x1354 PZA) (x1355 Int)) 
                       (and 
                           (reverse s46 x1354) 
                           (length s46 x1355) 
                           (length x1354 x1355)))))
         :named hyp71))
(assert (! (forall ((s47 PZA)) 
               (=> 
                   (seq s47) 
                   (forall ((x1356 A)) 
                       (= 
                           (exists ((x1357 Int) (x1358 PZA)) 
                               (and 
                                   (reverse s47 x1358) 
                                   (MS x1357 x1356 x1358))) 
                           (exists ((x1359 Int)) 
                               (MS x1359 x1356 s47))))))
         :named hyp72))
(assert (! (forall ((s48 PZA)) 
               (=> 
                   (seq s48) 
                   (exists ((x1360 PZA)) 
                       (and 
                           (reverse s48 x1360) 
                           (reverse x1360 s48)))))
         :named hyp73))
(assert (! (forall ((x1361 A) (y19 A) (p13 PZA)) 
               (=> 
                   (path x1361 y19 p13) 
                   (exists ((x1362 PZA)) 
                       (and 
                           (reverse p13 x1362) 
                           (path y19 x1361 x1362)))))
         :named hyp74))
(assert (! (forall ((x1363 A) (y21 A)) 
               (=> 
                   (and 
                       (MS1 x1363 a) 
                       (MS1 y21 a)) 
                   (forall ((x1364 PZA)) 
                       (= 
                           (exists ((x1365 A) (x1366 A)) 
                               (and 
                                   (= x1365 y21) 
                                   (= x1366 x1363) 
                                   (path x1365 x1366 x1364))) 
                           (exists ((x1367 PZA)) 
                               (and 
                                   (exists ((x1368 A) (x1369 A)) 
                                       (and 
                                           (= x1368 x1363) 
                                           (= x1369 y21) 
                                           (path x1368 x1369 x1367))) 
                                   (reverse x1367 x1364)))))))
         :named hyp75))
(assert (! (forall ((x1370 A) (x1371 A) (x1372 PZA)) 
               (= 
                   (shpath x1370 x1371 x1372) 
                   (exists ((x1373 A) (y22 A) (p14 PZA)) 
                       (and 
                           (path x1373 y22 p14) 
                           (exists ((x1374 Int)) 
                               (and 
                                   (length p14 x1374) 
                                   (dist x1373 y22 x1374))) 
                           (= x1370 x1373) 
                           (= x1371 y22) 
                           (forall ((x1375 Int) (x1376 A)) 
                               (= 
                                   (MS x1375 x1376 x1372) 
                                   (MS x1375 x1376 p14)))))))
         :named hyp76))
(assert (! (forall ((x1377 A) (y23 A) (p15 PZA)) 
               (=> 
                   (path x1377 y23 p15) 
                   (and 
                       (exists ((x1378 Int)) 
                           (dist x1377 y23 x1378)) 
                       (forall ((x1379 A) (x1380 A) (x1381 Int) (x1382 Int)) 
                           (=> 
                               (and 
                                   (dist x1379 x1380 x1381) 
                                   (dist x1379 x1380 x1382)) 
                               (= x1381 x1382))) 
                       (exists ((x1383 Int)) 
                           (length p15 x1383)) 
                       (forall ((x1384 PZA) (x1385 Int) (x1386 Int)) 
                           (=> 
                               (and 
                                   (length x1384 x1385) 
                                   (length x1384 x1386)) 
                               (= x1385 x1386))))))
         :named hyp77))
(assert (! (forall ((x1387 A) (y24 A)) 
               (=> 
                   (and 
                       (MS1 x1387 a) 
                       (MS1 y24 a)) 
                   (exists ((x1388 PZA)) 
                       (shpath x1387 y24 x1388))))
         :named hyp78))
(assert (! (forall ((y110 A) (y25 A) (x1389 A) (x1390 A) (p16 PZA) (q1 PZA)) 
               (=> 
                   (and 
                       (MS1 y110 a) 
                       (MS1 y25 a) 
                       (MS1 x1389 a) 
                       (MS1 x1390 a) 
                       (path x1389 y110 q1) 
                       (path y25 x1390 p16) 
                       (MS0 x1390 x1389 r)) 
                   (exists ((x1391 PZA)) 
                       (and 
                           (cnc p16 q1 x1391) 
                           (path y25 y110 x1391)))))
         :named hyp79))
(assert (! (forall ((x1392 A) (y26 A) (p17 PZA) (i103 Int)) 
               (=> 
                   (and 
                       (MS1 x1392 a) 
                       (MS1 y26 a) 
                       (path x1392 y26 p17) 
                       (<= 2 i103) 
                       (forall ((x1393 Int)) 
                           (=> 
                               (length p17 x1393) 
                               (<= i103 (- x1393 1))))) 
                   (exists ((x1394 A) (x1395 PZA)) 
                       (and 
                           (MS i103 x1394 p17) 
                           (forall ((x1396 Int) (x1397 A)) 
                               (= 
                                   (MS x1396 x1397 x1395) 
                                   (and 
                                       (MS x1396 x1397 p17) 
                                       (<= 1 x1396) 
                                       (<= x1396 i103)))) 
                           (path x1392 x1394 x1395)))))
         :named hyp80))
(assert (! (forall ((x1398 A) (x1399 A) (x1400 PZA)) 
               (= 
                   (path x1398 x1399 x1400) 
                   (exists ((x1401 A) (y27 A) (p18 PZA)) 
                       (and 
                           (MS1 x1401 a) 
                           (MS1 y27 a) 
                           (exists ((n67 Int)) 
                               (and 
                                   (<= 0 n67) 
                                   (< 1 n67) 
                                   (forall ((x1402 Int) (x1403 A)) 
                                       (=> 
                                           (MS x1402 x1403 p18) 
                                           (and 
                                               (<= 1 x1402) 
                                               (<= x1402 n67) 
                                               (MS1 x1403 a)))) 
                                   (forall ((x1404 Int) (x1405 A) (x1406 A)) 
                                       (=> 
                                           (and 
                                               (MS x1404 x1405 p18) 
                                               (MS x1404 x1406 p18)) 
                                           (= x1405 x1406))) 
                                   (forall ((x1407 Int)) 
                                       (=> 
                                           (and 
                                               (<= 1 x1407) 
                                               (<= x1407 n67)) 
                                           (exists ((x1408 A)) 
                                               (MS x1407 x1408 p18)))) 
                                   (exists ((x1409 Int)) 
                                       (and 
                                           (= x1409 1) 
                                           (MS x1409 x1401 p18))) 
                                   (MS n67 y27 p18) 
                                   (forall ((i104 Int)) 
                                       (=> 
                                           (and 
                                               (<= 1 i104) 
                                               (<= i104 (- n67 1))) 
                                           (exists ((x1410 A) (x1411 A)) 
                                               (and 
                                                   (MS i104 x1410 p18) 
                                                   (exists ((x1412 Int)) 
                                                       (and 
                                                           (= x1412 (+ i104 1)) 
                                                           (MS x1412 x1411 p18))) 
                                                   (MS0 x1410 x1411 r))))))) 
                           (= x1398 x1401) 
                           (= x1399 y27) 
                           (forall ((x1413 Int) (x1414 A)) 
                               (= 
                                   (MS x1413 x1414 x1400) 
                                   (MS x1413 x1414 p18)))))))
         :named hyp81))
(assert (! (forall ((x1415 A)) 
               (= 
                   (MS1 x1415 candidate) 
                   (exists ((z1 A)) 
                       (and 
                           (MS1 z1 a) 
                           (forall ((x1416 A) (y28 A)) 
                               (=> 
                                   (and 
                                       (MS1 x1416 a) 
                                       (not 
                                           (= x1416 z1)) 
                                       (MS1 y28 a) 
                                       (not 
                                           (= y28 z1)) 
                                       (not 
                                           (= x1416 y28))) 
                                   (exists ((p19 PZA)) 
                                       (and 
                                           (exists ((x1417 A) (x1418 A)) 
                                               (and 
                                                   (= x1417 x1416) 
                                                   (= x1418 y28) 
                                                   (path x1417 x1418 p19))) 
                                           (not 
                                               (exists ((x1419 Int)) 
                                                   (MS x1419 z1 p19))))))) 
                           (= x1415 z1)))))
         :named hyp82))
(assert (! (forall ((u A)) 
               (=> 
                   (MS1 u candidate) 
                   (forall ((x1420 A) (x1421 A)) 
                       (=> 
                           (and 
                               (MS1 x1420 a) 
                               (not 
                                   (= x1420 u)) 
                               (MS1 x1421 a) 
                               (not 
                                   (= x1421 u)) 
                               (not 
                                   (= x1420 x1421))) 
                           (exists ((x1422 A) (y29 A) (p20 PZA)) 
                               (and 
                                   (MS1 x1422 a) 
                                   (not 
                                       (= x1422 u)) 
                                   (MS1 y29 a) 
                                   (not 
                                       (= y29 u)) 
                                   (not 
                                       (= x1422 y29)) 
                                   (exists ((n68 Int)) 
                                       (and 
                                           (<= 0 n68) 
                                           (< 1 n68) 
                                           (forall ((x1423 Int) (x1424 A)) 
                                               (=> 
                                                   (MS x1423 x1424 p20) 
                                                   (and 
                                                       (<= 1 x1423) 
                                                       (<= x1423 n68) 
                                                       (MS1 x1424 a) 
                                                       (not 
                                                           (= x1424 u))))) 
                                           (forall ((x1425 Int) (x1426 A) (x1427 A)) 
                                               (=> 
                                                   (and 
                                                       (MS x1425 x1426 p20) 
                                                       (MS x1425 x1427 p20)) 
                                                   (= x1426 x1427))) 
                                           (forall ((x1428 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x1428) 
                                                       (<= x1428 n68)) 
                                                   (exists ((x1429 A)) 
                                                       (MS x1428 x1429 p20)))) 
                                           (exists ((x1430 Int)) 
                                               (and 
                                                   (= x1430 1) 
                                                   (MS x1430 x1422 p20))) 
                                           (MS n68 y29 p20) 
                                           (forall ((i105 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 i105) 
                                                       (<= i105 (- n68 1))) 
                                                   (exists ((x1431 A) (x1432 A)) 
                                                       (and 
                                                           (MS i105 x1431 p20) 
                                                           (exists ((x1433 Int)) 
                                                               (and 
                                                                   (= x1433 (+ i105 1)) 
                                                                   (MS x1433 x1432 p20))) 
                                                           (MS0 x1431 x1432 r))))))) 
                                   (= x1420 x1422) 
                                   (= x1421 y29)))))))
         :named hyp83))
(assert (! (forall ((s118 PZA) (s217 PZA)) 
               (=> 
                   (and 
                       (seq s118) 
                       (seq s217)) 
                   (and 
                       (exists ((x1434 Int)) 
                           (length s118 x1434)) 
                       (forall ((x1435 PZA) (x1436 Int) (x1437 Int)) 
                           (=> 
                               (and 
                                   (length x1435 x1436) 
                                   (length x1435 x1437)) 
                               (= x1436 x1437))) 
                       (forall ((i106 Int)) 
                           (=> 
                               (and 
                                   (<= 1 i106) 
                                   (forall ((x1438 Int)) 
                                       (=> 
                                           (length s118 x1438) 
                                           (<= i106 x1438)))) 
                               (and 
                                   (exists ((x1439 A)) 
                                       (MS i106 x1439 s118)) 
                                   (forall ((x1440 Int) (x1441 A) (x1442 A)) 
                                       (=> 
                                           (and 
                                               (MS x1440 x1441 s118) 
                                               (MS x1440 x1442 s118)) 
                                           (= x1441 x1442)))))) 
                       (exists ((x1443 Int)) 
                           (length s217 x1443)) 
                       (forall ((i107 Int)) 
                           (=> 
                               (and 
                                   (forall ((x1444 Int)) 
                                       (=> 
                                           (length s118 x1444) 
                                           (<= (+ x1444 1) i107))) 
                                   (forall ((x1445 Int) (x1446 Int)) 
                                       (=> 
                                           (and 
                                               (length s118 x1446) 
                                               (length s217 x1445)) 
                                           (<= i107 (+ x1446 x1445))))) 
                               (and 
                                   (exists ((x1447 A) (x1448 Int)) 
                                       (and 
                                           (forall ((x1449 Int)) 
                                               (=> 
                                                   (length s118 x1449) 
                                                   (= x1448 (- i107 x1449)))) 
                                           (MS x1448 x1447 s217))) 
                                   (forall ((x1450 Int) (x1451 A) (x1452 A)) 
                                       (=> 
                                           (and 
                                               (MS x1450 x1451 s217) 
                                               (MS x1450 x1452 s217)) 
                                           (= x1451 x1452)))))))))
         :named hyp84))
(assert (! (forall ((s49 PZA)) 
               (=> 
                   (seq s49) 
                   (and 
                       (exists ((x1453 Int)) 
                           (length s49 x1453)) 
                       (forall ((x1454 PZA) (x1455 Int) (x1456 Int)) 
                           (=> 
                               (and 
                                   (length x1454 x1455) 
                                   (length x1454 x1456)) 
                               (= x1455 x1456))) 
                       (forall ((i108 Int)) 
                           (=> 
                               (and 
                                   (<= 1 i108) 
                                   (forall ((x1457 Int)) 
                                       (=> 
                                           (length s49 x1457) 
                                           (<= i108 x1457)))) 
                               (and 
                                   (exists ((x1458 A) (x1459 Int)) 
                                       (and 
                                           (forall ((x1460 Int)) 
                                               (=> 
                                                   (length s49 x1460) 
                                                   (= x1459 (+ (- x1460 i108) 1)))) 
                                           (MS x1459 x1458 s49))) 
                                   (forall ((x1461 Int) (x1462 A) (x1463 A)) 
                                       (=> 
                                           (and 
                                               (MS x1461 x1462 s49) 
                                               (MS x1461 x1463 s49)) 
                                           (= x1462 x1463)))))))))
         :named hyp85))
(assert (! (forall ((x1464 A) (y30 A) (p21 PZA) (i109 Int)) 
               (=> 
                   (and 
                       (MS1 x1464 a) 
                       (MS1 y30 a) 
                       (seq p21) 
                       (shpath x1464 y30 p21) 
                       (exists ((x1465 A)) 
                           (MS i109 x1465 p21)) 
                       (not 
                           (= i109 1)) 
                       (not 
                           (length p21 i109))) 
                   (exists ((x1466 A) (x1467 PZA)) 
                       (and 
                           (MS i109 x1466 p21) 
                           (forall ((x1468 Int) (x1469 A)) 
                               (= 
                                   (MS x1468 x1469 x1467) 
                                   (and 
                                       (MS x1468 x1469 p21) 
                                       (<= 1 x1468) 
                                       (<= x1468 i109)))) 
                           (shpath x1464 x1466 x1467)))))
         :named hyp86))
(assert (! (forall ((x1470 A) (y31 A) (p22 PZA) (i110 Int)) 
               (=> 
                   (and 
                       (MS1 x1470 a) 
                       (MS1 y31 a) 
                       (seq p22) 
                       (shpath x1470 y31 p22) 
                       (exists ((x1471 A)) 
                           (MS i110 x1471 p22)) 
                       (not 
                           (= i110 1)) 
                       (not 
                           (length p22 i110))) 
                   (and 
                       (exists ((x1472 A)) 
                           (and 
                               (MS i110 x1472 p22) 
                               (dist x1470 x1472 i110))) 
                       (exists ((x1473 A) (x1474 Int)) 
                           (and 
                               (exists ((x1475 Int)) 
                                   (and 
                                       (= x1475 (+ i110 1)) 
                                       (MS x1475 x1473 p22))) 
                               (= x1474 (+ i110 1)) 
                               (dist x1470 x1473 x1474))) 
                       (exists ((x1476 A) (x1477 A)) 
                           (and 
                               (MS i110 x1476 p22) 
                               (exists ((x1478 Int)) 
                                   (and 
                                       (= x1478 (+ i110 1)) 
                                       (MS x1478 x1477 p22))) 
                               (MS0 x1476 x1477 r))))))
         :named hyp87))
(assert (! (forall ((x1479 A) (y32 A) (p23 PZA) (z2 A)) 
               (=> 
                   (and 
                       (MS1 x1479 a) 
                       (MS1 y32 a) 
                       (seq p23) 
                       (shpath x1479 y32 p23) 
                       (exists ((x1480 Int)) 
                           (MS x1480 z2 p23)) 
                       (not 
                           (= z2 x1479)) 
                       (not 
                           (= z2 y32))) 
                   (exists ((t1 A)) 
                       (and 
                           (MS1 t1 a) 
                           (forall ((x1481 Int) (x1482 Int)) 
                               (=> 
                                   (and 
                                       (dist x1479 z2 x1482) 
                                       (dist x1479 t1 x1481)) 
                                   (< x1482 x1481))) 
                           (MS0 z2 t1 r)))))
         :named hyp88))
(assert (! (forall ((x1483 A) (y33 A) (z3 A)) 
               (=> 
                   (and 
                       (MS1 x1483 a) 
                       (MS1 y33 a) 
                       (MS1 z3 a) 
                       (not 
                           (= z3 x1483)) 
                       (not 
                           (= z3 y33)) 
                       (forall ((t2 A)) 
                           (=> 
                               (and 
                                   (MS1 t2 a) 
                                   (MS0 z3 t2 r)) 
                               (forall ((x1484 Int) (x1485 Int)) 
                                   (=> 
                                       (and 
                                           (dist x1483 t2 x1485) 
                                           (dist x1483 z3 x1484)) 
                                       (<= x1485 x1484)))))) 
                   (exists ((q2 PZA)) 
                       (and 
                           (path x1483 y33 q2) 
                           (not 
                               (exists ((x1486 Int)) 
                                   (MS x1486 z3 q2)))))))
         :named hyp89))
(assert (! (forall ((x1487 A) (x1488 A)) 
               (=> 
                   (and 
                       (MS1 x1487 a) 
                       (MS1 x1488 a)) 
                   (MS0 x1487 x1488 c)))
         :named hyp90))
(assert (! (not 
               (forall ((x1489 A)) 
                   (MS1 x1489 a)))
         :named hyp91))
(assert (! (forall ((s119 PZA) (s218 PZA) (b0 PA)) 
               (=> 
                   (and 
                       (seq s119) 
                       (seq s218) 
                       (forall ((x1490 A)) 
                           (=> 
                               (exists ((x1491 Int)) 
                                   (MS x1491 x1490 s119)) 
                               (MS1 x1490 b0))) 
                       (forall ((x1492 A)) 
                           (=> 
                               (exists ((x1493 Int)) 
                                   (MS x1493 x1492 s218)) 
                               (MS1 x1492 b0)))) 
                   (and 
                       (forall ((x1494 Int) (x1495 A)) 
                           (=> 
                               (exists ((x1496 PZA)) 
                                   (and 
                                       (cnc s119 s218 x1496) 
                                       (MS x1494 x1495 x1496))) 
                               (and 
                                   (<= 1 x1494) 
                                   (forall ((x1497 Int) (x1498 Int)) 
                                       (=> 
                                           (and 
                                               (length s119 x1498) 
                                               (length s218 x1497)) 
                                           (<= x1494 (+ x1498 x1497)))) 
                                   (MS1 x1495 b0)))) 
                       (forall ((x1499 Int) (x1500 A) (x1501 A)) 
                           (=> 
                               (and 
                                   (exists ((x1502 PZA)) 
                                       (and 
                                           (cnc s119 s218 x1502) 
                                           (MS x1499 x1500 x1502))) 
                                   (exists ((x1503 PZA)) 
                                       (and 
                                           (cnc s119 s218 x1503) 
                                           (MS x1499 x1501 x1503)))) 
                               (= x1500 x1501))) 
                       (forall ((x1504 Int)) 
                           (=> 
                               (and 
                                   (<= 1 x1504) 
                                   (forall ((x1505 Int) (x1506 Int)) 
                                       (=> 
                                           (and 
                                               (length s119 x1506) 
                                               (length s218 x1505)) 
                                           (<= x1504 (+ x1506 x1505))))) 
                               (exists ((x1507 A) (x1508 PZA)) 
                                   (and 
                                       (cnc s119 s218 x1508) 
                                       (MS x1504 x1507 x1508))))))))
         :named hyp92))
(assert (! (forall ((x1509 A) (x1510 A) (x1511 PZA)) 
               (= 
                   (path x1509 x1510 x1511) 
                   (exists ((x1512 A) (y34 A) (p24 PZA)) 
                       (and 
                           (seq p24) 
                           (forall ((x1513 A)) 
                               (=> 
                                   (exists ((x1514 Int)) 
                                       (MS x1514 x1513 p24)) 
                                   (MS1 x1513 a))) 
                           (forall ((x1515 Int)) 
                               (=> 
                                   (length p24 x1515) 
                                   (< 1 x1515))) 
                           (exists ((x1516 Int)) 
                               (and 
                                   (= x1516 1) 
                                   (MS x1516 x1512 p24))) 
                           (exists ((x1517 Int)) 
                               (and 
                                   (length p24 x1517) 
                                   (MS x1517 y34 p24))) 
                           (forall ((i111 Int)) 
                               (=> 
                                   (and 
                                       (<= 1 i111) 
                                       (forall ((x1518 Int)) 
                                           (=> 
                                               (length p24 x1518) 
                                               (<= i111 (- x1518 1))))) 
                                   (exists ((x1519 A) (x1520 A)) 
                                       (and 
                                           (MS i111 x1519 p24) 
                                           (exists ((x1521 Int)) 
                                               (and 
                                                   (= x1521 (+ i111 1)) 
                                                   (MS x1521 x1520 p24))) 
                                           (MS0 x1519 x1520 r))))) 
                           (= x1509 x1512) 
                           (= x1510 y34) 
                           (forall ((x1522 Int) (x1523 A)) 
                               (= 
                                   (MS x1522 x1523 x1511) 
                                   (MS x1522 x1523 p24)))))))
         :named hyp93))
(assert (! (forall ((x1524 A) (y35 A) (p25 PZA)) 
               (=> 
                   (and 
                       (seq p25) 
                       (forall ((x1525 A)) 
                           (=> 
                               (exists ((x1526 Int)) 
                                   (MS x1526 x1525 p25)) 
                               (MS1 x1525 a)))) 
                   (and 
                       (exists ((x1527 Int)) 
                           (length p25 x1527)) 
                       (forall ((x1528 PZA) (x1529 Int) (x1530 Int)) 
                           (=> 
                               (and 
                                   (length x1528 x1529) 
                                   (length x1528 x1530)) 
                               (= x1529 x1530))) 
                       (=> 
                           (forall ((x1531 Int)) 
                               (=> 
                                   (length p25 x1531) 
                                   (< 1 x1531))) 
                           (and 
                               (exists ((x1532 A) (x1533 Int)) 
                                   (and 
                                       (= x1533 1) 
                                       (MS x1533 x1532 p25))) 
                               (forall ((x1534 Int) (x1535 A) (x1536 A)) 
                                   (=> 
                                       (and 
                                           (MS x1534 x1535 p25) 
                                           (MS x1534 x1536 p25)) 
                                       (= x1535 x1536))) 
                               (=> 
                                   (exists ((x1537 Int)) 
                                       (and 
                                           (= x1537 1) 
                                           (MS x1537 x1524 p25))) 
                                   (and 
                                       (exists ((x1538 A) (x1539 Int)) 
                                           (and 
                                               (length p25 x1539) 
                                               (MS x1539 x1538 p25))) 
                                       (=> 
                                           (exists ((x1540 Int)) 
                                               (and 
                                                   (length p25 x1540) 
                                                   (MS x1540 y35 p25))) 
                                           (forall ((i112 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 i112) 
                                                       (forall ((x1541 Int)) 
                                                           (=> 
                                                               (length p25 x1541) 
                                                               (<= i112 (- x1541 1))))) 
                                                   (and 
                                                       (exists ((x1542 A)) 
                                                           (MS i112 x1542 p25)) 
                                                       (exists ((x1543 A) (x1544 Int)) 
                                                           (and 
                                                               (= x1544 (+ i112 1)) 
                                                               (MS x1544 x1543 p25))))))))))))))
         :named hyp94))
(assert (! (MS1 x a)
         :named hyp95))
(assert (! (MS1 y2 a)
         :named hyp96))
(assert (! (path x y2 p)
         :named hyp97))
(assert (! (and 
               (forall ((x1545 PZA) (x1546 PZA) (x1547 PZA)) 
                   (=> 
                       (cnc x1545 x1546 x1547) 
                       (and 
                           (exists ((s50 PZA)) 
                               (and 
                                   (exists ((n69 Int)) 
                                       (and 
                                           (<= 0 n69) 
                                           (forall ((x1548 Int) (x1549 A)) 
                                               (=> 
                                                   (MS x1548 x1549 s50) 
                                                   (and 
                                                       (<= 1 x1548) 
                                                       (<= x1548 n69)))) 
                                           (forall ((x1550 Int) (x1551 A) (x1552 A)) 
                                               (=> 
                                                   (and 
                                                       (MS x1550 x1551 s50) 
                                                       (MS x1550 x1552 s50)) 
                                                   (= x1551 x1552))) 
                                           (forall ((x1553 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x1553) 
                                                       (<= x1553 n69)) 
                                                   (exists ((x1554 A)) 
                                                       (MS x1553 x1554 s50)))))) 
                                   (forall ((x1555 Int) (x1556 A)) 
                                       (= 
                                           (MS x1555 x1556 x1545) 
                                           (MS x1555 x1556 s50))))) 
                           (exists ((s51 PZA)) 
                               (and 
                                   (exists ((n70 Int)) 
                                       (and 
                                           (<= 0 n70) 
                                           (forall ((x1557 Int) (x1558 A)) 
                                               (=> 
                                                   (MS x1557 x1558 s51) 
                                                   (and 
                                                       (<= 1 x1557) 
                                                       (<= x1557 n70)))) 
                                           (forall ((x1559 Int) (x1560 A) (x1561 A)) 
                                               (=> 
                                                   (and 
                                                       (MS x1559 x1560 s51) 
                                                       (MS x1559 x1561 s51)) 
                                                   (= x1560 x1561))) 
                                           (forall ((x1562 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x1562) 
                                                       (<= x1562 n70)) 
                                                   (exists ((x1563 A)) 
                                                       (MS x1562 x1563 s51)))))) 
                                   (forall ((x1564 Int) (x1565 A)) 
                                       (= 
                                           (MS x1564 x1565 x1546) 
                                           (MS x1564 x1565 s51))))) 
                           (exists ((s52 PZA)) 
                               (and 
                                   (exists ((n71 Int)) 
                                       (and 
                                           (<= 0 n71) 
                                           (forall ((x1566 Int) (x1567 A)) 
                                               (=> 
                                                   (MS x1566 x1567 s52) 
                                                   (and 
                                                       (<= 1 x1566) 
                                                       (<= x1566 n71)))) 
                                           (forall ((x1568 Int) (x1569 A) (x1570 A)) 
                                               (=> 
                                                   (and 
                                                       (MS x1568 x1569 s52) 
                                                       (MS x1568 x1570 s52)) 
                                                   (= x1569 x1570))) 
                                           (forall ((x1571 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x1571) 
                                                       (<= x1571 n71)) 
                                                   (exists ((x1572 A)) 
                                                       (MS x1571 x1572 s52)))))) 
                                   (forall ((x1573 Int) (x1574 A)) 
                                       (= 
                                           (MS x1573 x1574 x1547) 
                                           (MS x1573 x1574 s52)))))))) 
               (forall ((x1575 PZA) (x1576 PZA) (x1577 PZA) (x1578 PZA)) 
                   (=> 
                       (and 
                           (cnc x1575 x1576 x1577) 
                           (cnc x1575 x1576 x1578)) 
                       (forall ((x1579 Int) (x1580 A)) 
                           (= 
                               (MS x1579 x1580 x1577) 
                               (MS x1579 x1580 x1578))))) 
               (forall ((x1581 PZA) (x1582 PZA)) 
                   (=> 
                       (and 
                           (exists ((s53 PZA)) 
                               (and 
                                   (exists ((n72 Int)) 
                                       (and 
                                           (<= 0 n72) 
                                           (forall ((x1583 Int) (x1584 A)) 
                                               (=> 
                                                   (MS x1583 x1584 s53) 
                                                   (and 
                                                       (<= 1 x1583) 
                                                       (<= x1583 n72)))) 
                                           (forall ((x1585 Int) (x1586 A) (x1587 A)) 
                                               (=> 
                                                   (and 
                                                       (MS x1585 x1586 s53) 
                                                       (MS x1585 x1587 s53)) 
                                                   (= x1586 x1587))) 
                                           (forall ((x1588 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x1588) 
                                                       (<= x1588 n72)) 
                                                   (exists ((x1589 A)) 
                                                       (MS x1588 x1589 s53)))))) 
                                   (forall ((x1590 Int) (x1591 A)) 
                                       (= 
                                           (MS x1590 x1591 x1581) 
                                           (MS x1590 x1591 s53))))) 
                           (exists ((s54 PZA)) 
                               (and 
                                   (exists ((n73 Int)) 
                                       (and 
                                           (<= 0 n73) 
                                           (forall ((x1592 Int) (x1593 A)) 
                                               (=> 
                                                   (MS x1592 x1593 s54) 
                                                   (and 
                                                       (<= 1 x1592) 
                                                       (<= x1592 n73)))) 
                                           (forall ((x1594 Int) (x1595 A) (x1596 A)) 
                                               (=> 
                                                   (and 
                                                       (MS x1594 x1595 s54) 
                                                       (MS x1594 x1596 s54)) 
                                                   (= x1595 x1596))) 
                                           (forall ((x1597 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x1597) 
                                                       (<= x1597 n73)) 
                                                   (exists ((x1598 A)) 
                                                       (MS x1597 x1598 s54)))))) 
                                   (forall ((x1599 Int) (x1600 A)) 
                                       (= 
                                           (MS x1599 x1600 x1582) 
                                           (MS x1599 x1600 s54)))))) 
                       (exists ((x1601 PZA)) 
                           (cnc x1581 x1582 x1601)))))
         :named hyp98))
(assert (! (and 
               (forall ((x1602 PZA) (x1603 PZA)) 
                   (=> 
                       (reverse x1602 x1603) 
                       (and 
                           (exists ((s55 PZA)) 
                               (and 
                                   (exists ((n74 Int)) 
                                       (and 
                                           (<= 0 n74) 
                                           (forall ((x1604 Int) (x1605 A)) 
                                               (=> 
                                                   (MS x1604 x1605 s55) 
                                                   (and 
                                                       (<= 1 x1604) 
                                                       (<= x1604 n74)))) 
                                           (forall ((x1606 Int) (x1607 A) (x1608 A)) 
                                               (=> 
                                                   (and 
                                                       (MS x1606 x1607 s55) 
                                                       (MS x1606 x1608 s55)) 
                                                   (= x1607 x1608))) 
                                           (forall ((x1609 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x1609) 
                                                       (<= x1609 n74)) 
                                                   (exists ((x1610 A)) 
                                                       (MS x1609 x1610 s55)))))) 
                                   (forall ((x1611 Int) (x1612 A)) 
                                       (= 
                                           (MS x1611 x1612 x1602) 
                                           (MS x1611 x1612 s55))))) 
                           (exists ((s56 PZA)) 
                               (and 
                                   (exists ((n75 Int)) 
                                       (and 
                                           (<= 0 n75) 
                                           (forall ((x1613 Int) (x1614 A)) 
                                               (=> 
                                                   (MS x1613 x1614 s56) 
                                                   (and 
                                                       (<= 1 x1613) 
                                                       (<= x1613 n75)))) 
                                           (forall ((x1615 Int) (x1616 A) (x1617 A)) 
                                               (=> 
                                                   (and 
                                                       (MS x1615 x1616 s56) 
                                                       (MS x1615 x1617 s56)) 
                                                   (= x1616 x1617))) 
                                           (forall ((x1618 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x1618) 
                                                       (<= x1618 n75)) 
                                                   (exists ((x1619 A)) 
                                                       (MS x1618 x1619 s56)))))) 
                                   (forall ((x1620 Int) (x1621 A)) 
                                       (= 
                                           (MS x1620 x1621 x1603) 
                                           (MS x1620 x1621 s56)))))))) 
               (forall ((x1622 PZA) (x1623 PZA) (x1624 PZA)) 
                   (=> 
                       (and 
                           (reverse x1622 x1623) 
                           (reverse x1622 x1624)) 
                       (forall ((x1625 Int) (x1626 A)) 
                           (= 
                               (MS x1625 x1626 x1623) 
                               (MS x1625 x1626 x1624))))) 
               (forall ((x1627 PZA)) 
                   (=> 
                       (exists ((s57 PZA)) 
                           (and 
                               (exists ((n76 Int)) 
                                   (and 
                                       (<= 0 n76) 
                                       (forall ((x1628 Int) (x1629 A)) 
                                           (=> 
                                               (MS x1628 x1629 s57) 
                                               (and 
                                                   (<= 1 x1628) 
                                                   (<= x1628 n76)))) 
                                       (forall ((x1630 Int) (x1631 A) (x1632 A)) 
                                           (=> 
                                               (and 
                                                   (MS x1630 x1631 s57) 
                                                   (MS x1630 x1632 s57)) 
                                               (= x1631 x1632))) 
                                       (forall ((x1633 Int)) 
                                           (=> 
                                               (and 
                                                   (<= 1 x1633) 
                                                   (<= x1633 n76)) 
                                               (exists ((x1634 A)) 
                                                   (MS x1633 x1634 s57)))))) 
                               (forall ((x1635 Int) (x1636 A)) 
                                   (= 
                                       (MS x1635 x1636 x1627) 
                                       (MS x1635 x1636 s57))))) 
                       (exists ((x1637 PZA)) 
                           (reverse x1627 x1637)))))
         :named hyp99))
(assert (! (forall ((s120 PZA) (s219 PZA)) 
               (=> 
                   (and 
                       (exists ((n77 Int)) 
                           (and 
                               (<= 0 n77) 
                               (forall ((x1638 Int) (x1639 A)) 
                                   (=> 
                                       (MS x1638 x1639 s120) 
                                       (and 
                                           (<= 1 x1638) 
                                           (<= x1638 n77)))) 
                               (forall ((x1640 Int) (x1641 A) (x1642 A)) 
                                   (=> 
                                       (and 
                                           (MS x1640 x1641 s120) 
                                           (MS x1640 x1642 s120)) 
                                       (= x1641 x1642))) 
                               (forall ((x1643 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x1643) 
                                           (<= x1643 n77)) 
                                       (exists ((x1644 A)) 
                                           (MS x1643 x1644 s120)))))) 
                       (exists ((n78 Int)) 
                           (and 
                               (<= 0 n78) 
                               (forall ((x1645 Int) (x1646 A)) 
                                   (=> 
                                       (MS x1645 x1646 s219) 
                                       (and 
                                           (<= 1 x1645) 
                                           (<= x1645 n78)))) 
                               (forall ((x1647 Int) (x1648 A) (x1649 A)) 
                                   (=> 
                                       (and 
                                           (MS x1647 x1648 s219) 
                                           (MS x1647 x1649 s219)) 
                                       (= x1648 x1649))) 
                               (forall ((x1650 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x1650) 
                                           (<= x1650 n78)) 
                                       (exists ((x1651 A)) 
                                           (MS x1650 x1651 s219))))))) 
                   (exists ((x1652 PZA) (x1653 Int)) 
                       (and 
                           (cnc s120 s219 x1652) 
                           (forall ((x1654 Int) (x1655 Int)) 
                               (=> 
                                   (and 
                                       (length s120 x1655) 
                                       (length s219 x1654)) 
                                   (= x1653 (+ x1655 x1654)))) 
                           (length x1652 x1653)))))
         :named hyp100))
(assert (! (forall ((s121 PZA) (s220 PZA)) 
               (=> 
                   (and 
                       (exists ((n79 Int)) 
                           (and 
                               (<= 0 n79) 
                               (forall ((x1656 Int) (x1657 A)) 
                                   (=> 
                                       (MS x1656 x1657 s121) 
                                       (and 
                                           (<= 1 x1656) 
                                           (<= x1656 n79)))) 
                               (forall ((x1658 Int) (x1659 A) (x1660 A)) 
                                   (=> 
                                       (and 
                                           (MS x1658 x1659 s121) 
                                           (MS x1658 x1660 s121)) 
                                       (= x1659 x1660))) 
                               (forall ((x1661 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x1661) 
                                           (<= x1661 n79)) 
                                       (exists ((x1662 A)) 
                                           (MS x1661 x1662 s121)))))) 
                       (exists ((n80 Int)) 
                           (and 
                               (<= 0 n80) 
                               (forall ((x1663 Int) (x1664 A)) 
                                   (=> 
                                       (MS x1663 x1664 s220) 
                                       (and 
                                           (<= 1 x1663) 
                                           (<= x1663 n80)))) 
                               (forall ((x1665 Int) (x1666 A) (x1667 A)) 
                                   (=> 
                                       (and 
                                           (MS x1665 x1666 s220) 
                                           (MS x1665 x1667 s220)) 
                                       (= x1666 x1667))) 
                               (forall ((x1668 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x1668) 
                                           (<= x1668 n80)) 
                                       (exists ((x1669 A)) 
                                           (MS x1668 x1669 s220))))))) 
                   (forall ((x1670 Int)) 
                       (= 
                           (exists ((x1671 A) (x1672 PZA)) 
                               (and 
                                   (cnc s121 s220 x1672) 
                                   (MS x1670 x1671 x1672))) 
                           (and 
                               (<= 1 x1670) 
                               (forall ((x1673 Int) (x1674 Int)) 
                                   (=> 
                                       (and 
                                           (length s121 x1674) 
                                           (length s220 x1673)) 
                                       (<= x1670 (+ x1674 x1673)))))))))
         :named hyp101))
(assert (! (forall ((s122 PZA) (s221 PZA)) 
               (=> 
                   (and 
                       (exists ((n81 Int)) 
                           (and 
                               (<= 0 n81) 
                               (forall ((x1675 Int) (x1676 A)) 
                                   (=> 
                                       (MS x1675 x1676 s122) 
                                       (and 
                                           (<= 1 x1675) 
                                           (<= x1675 n81)))) 
                               (forall ((x1677 Int) (x1678 A) (x1679 A)) 
                                   (=> 
                                       (and 
                                           (MS x1677 x1678 s122) 
                                           (MS x1677 x1679 s122)) 
                                       (= x1678 x1679))) 
                               (forall ((x1680 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x1680) 
                                           (<= x1680 n81)) 
                                       (exists ((x1681 A)) 
                                           (MS x1680 x1681 s122)))))) 
                       (exists ((n82 Int)) 
                           (and 
                               (<= 0 n82) 
                               (forall ((x1682 Int) (x1683 A)) 
                                   (=> 
                                       (MS x1682 x1683 s221) 
                                       (and 
                                           (<= 1 x1682) 
                                           (<= x1682 n82)))) 
                               (forall ((x1684 Int) (x1685 A) (x1686 A)) 
                                   (=> 
                                       (and 
                                           (MS x1684 x1685 s221) 
                                           (MS x1684 x1686 s221)) 
                                       (= x1685 x1686))) 
                               (forall ((x1687 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x1687) 
                                           (<= x1687 n82)) 
                                       (exists ((x1688 A)) 
                                           (MS x1687 x1688 s221))))))) 
                   (forall ((x1689 A)) 
                       (= 
                           (exists ((x1690 Int) (x1691 PZA)) 
                               (and 
                                   (cnc s122 s221 x1691) 
                                   (MS x1690 x1689 x1691))) 
                           (or 
                               (exists ((x1692 Int)) 
                                   (MS x1692 x1689 s122)) 
                               (exists ((x1693 Int)) 
                                   (MS x1693 x1689 s221)))))))
         :named hyp102))
(assert (! (forall ((s123 PZA) (s222 PZA) (i113 Int)) 
               (=> 
                   (and 
                       (exists ((n83 Int)) 
                           (and 
                               (<= 0 n83) 
                               (forall ((x1694 Int) (x1695 A)) 
                                   (=> 
                                       (MS x1694 x1695 s123) 
                                       (and 
                                           (<= 1 x1694) 
                                           (<= x1694 n83)))) 
                               (forall ((x1696 Int) (x1697 A) (x1698 A)) 
                                   (=> 
                                       (and 
                                           (MS x1696 x1697 s123) 
                                           (MS x1696 x1698 s123)) 
                                       (= x1697 x1698))) 
                               (forall ((x1699 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x1699) 
                                           (<= x1699 n83)) 
                                       (exists ((x1700 A)) 
                                           (MS x1699 x1700 s123)))))) 
                       (exists ((n84 Int)) 
                           (and 
                               (<= 0 n84) 
                               (forall ((x1701 Int) (x1702 A)) 
                                   (=> 
                                       (MS x1701 x1702 s222) 
                                       (and 
                                           (<= 1 x1701) 
                                           (<= x1701 n84)))) 
                               (forall ((x1703 Int) (x1704 A) (x1705 A)) 
                                   (=> 
                                       (and 
                                           (MS x1703 x1704 s222) 
                                           (MS x1703 x1705 s222)) 
                                       (= x1704 x1705))) 
                               (forall ((x1706 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x1706) 
                                           (<= x1706 n84)) 
                                       (exists ((x1707 A)) 
                                           (MS x1706 x1707 s222)))))) 
                       (<= 1 i113) 
                       (forall ((x1708 Int)) 
                           (=> 
                               (length s123 x1708) 
                               (<= i113 x1708)))) 
                   (exists ((x1709 PZA)) 
                       (and 
                           (cnc s123 s222 x1709) 
                           (exists ((x1710 A)) 
                               (and 
                                   (MS i113 x1710 s123) 
                                   (MS i113 x1710 x1709)))))))
         :named hyp103))
(assert (! (forall ((s124 PZA) (s223 PZA) (i114 Int)) 
               (=> 
                   (and 
                       (exists ((n85 Int)) 
                           (and 
                               (<= 0 n85) 
                               (forall ((x1711 Int) (x1712 A)) 
                                   (=> 
                                       (MS x1711 x1712 s124) 
                                       (and 
                                           (<= 1 x1711) 
                                           (<= x1711 n85)))) 
                               (forall ((x1713 Int) (x1714 A) (x1715 A)) 
                                   (=> 
                                       (and 
                                           (MS x1713 x1714 s124) 
                                           (MS x1713 x1715 s124)) 
                                       (= x1714 x1715))) 
                               (forall ((x1716 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x1716) 
                                           (<= x1716 n85)) 
                                       (exists ((x1717 A)) 
                                           (MS x1716 x1717 s124)))))) 
                       (exists ((n86 Int)) 
                           (and 
                               (<= 0 n86) 
                               (forall ((x1718 Int) (x1719 A)) 
                                   (=> 
                                       (MS x1718 x1719 s223) 
                                       (and 
                                           (<= 1 x1718) 
                                           (<= x1718 n86)))) 
                               (forall ((x1720 Int) (x1721 A) (x1722 A)) 
                                   (=> 
                                       (and 
                                           (MS x1720 x1721 s223) 
                                           (MS x1720 x1722 s223)) 
                                       (= x1721 x1722))) 
                               (forall ((x1723 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x1723) 
                                           (<= x1723 n86)) 
                                       (exists ((x1724 A)) 
                                           (MS x1723 x1724 s223)))))) 
                       (forall ((x1725 Int)) 
                           (=> 
                               (length s124 x1725) 
                               (<= (+ x1725 1) i114))) 
                       (forall ((x1726 Int) (x1727 Int)) 
                           (=> 
                               (and 
                                   (length s124 x1727) 
                                   (length s223 x1726)) 
                               (<= i114 (+ x1727 x1726))))) 
                   (exists ((x1728 PZA)) 
                       (and 
                           (cnc s124 s223 x1728) 
                           (exists ((x1729 A)) 
                               (and 
                                   (exists ((x1730 Int)) 
                                       (and 
                                           (forall ((x1731 Int)) 
                                               (=> 
                                                   (length s124 x1731) 
                                                   (= x1730 (- i114 x1731)))) 
                                           (MS x1730 x1729 s223))) 
                                   (MS i114 x1729 x1728)))))))
         :named hyp104))
(assert (! (forall ((s58 PZA)) 
               (=> 
                   (exists ((n87 Int)) 
                       (and 
                           (<= 0 n87) 
                           (forall ((x1732 Int) (x1733 A)) 
                               (=> 
                                   (MS x1732 x1733 s58) 
                                   (and 
                                       (<= 1 x1732) 
                                       (<= x1732 n87)))) 
                           (forall ((x1734 Int) (x1735 A) (x1736 A)) 
                               (=> 
                                   (and 
                                       (MS x1734 x1735 s58) 
                                       (MS x1734 x1736 s58)) 
                                   (= x1735 x1736))) 
                           (forall ((x1737 Int)) 
                               (=> 
                                   (and 
                                       (<= 1 x1737) 
                                       (<= x1737 n87)) 
                                   (exists ((x1738 A)) 
                                       (MS x1737 x1738 s58)))))) 
                   (exists ((x1739 PZA) (x1740 Int)) 
                       (and 
                           (reverse s58 x1739) 
                           (length s58 x1740) 
                           (length x1739 x1740)))))
         :named hyp105))
(assert (! (forall ((s59 PZA)) 
               (=> 
                   (exists ((n88 Int)) 
                       (and 
                           (<= 0 n88) 
                           (forall ((x1741 Int) (x1742 A)) 
                               (=> 
                                   (MS x1741 x1742 s59) 
                                   (and 
                                       (<= 1 x1741) 
                                       (<= x1741 n88)))) 
                           (forall ((x1743 Int) (x1744 A) (x1745 A)) 
                               (=> 
                                   (and 
                                       (MS x1743 x1744 s59) 
                                       (MS x1743 x1745 s59)) 
                                   (= x1744 x1745))) 
                           (forall ((x1746 Int)) 
                               (=> 
                                   (and 
                                       (<= 1 x1746) 
                                       (<= x1746 n88)) 
                                   (exists ((x1747 A)) 
                                       (MS x1746 x1747 s59)))))) 
                   (forall ((x1748 A)) 
                       (= 
                           (exists ((x1749 Int) (x1750 PZA)) 
                               (and 
                                   (reverse s59 x1750) 
                                   (MS x1749 x1748 x1750))) 
                           (exists ((x1751 Int)) 
                               (MS x1751 x1748 s59))))))
         :named hyp106))
(assert (! (forall ((s60 PZA)) 
               (=> 
                   (exists ((n89 Int)) 
                       (and 
                           (<= 0 n89) 
                           (forall ((x1752 Int) (x1753 A)) 
                               (=> 
                                   (MS x1752 x1753 s60) 
                                   (and 
                                       (<= 1 x1752) 
                                       (<= x1752 n89)))) 
                           (forall ((x1754 Int) (x1755 A) (x1756 A)) 
                               (=> 
                                   (and 
                                       (MS x1754 x1755 s60) 
                                       (MS x1754 x1756 s60)) 
                                   (= x1755 x1756))) 
                           (forall ((x1757 Int)) 
                               (=> 
                                   (and 
                                       (<= 1 x1757) 
                                       (<= x1757 n89)) 
                                   (exists ((x1758 A)) 
                                       (MS x1757 x1758 s60)))))) 
                   (exists ((x1759 PZA)) 
                       (and 
                           (reverse s60 x1759) 
                           (reverse x1759 s60)))))
         :named hyp107))
(assert (! (forall ((x1760 A) (y36 A) (p26 PZA) (i115 Int)) 
               (=> 
                   (and 
                       (MS1 x1760 a) 
                       (MS1 y36 a) 
                       (exists ((n90 Int)) 
                           (and 
                               (<= 0 n90) 
                               (forall ((x1761 Int) (x1762 A)) 
                                   (=> 
                                       (MS x1761 x1762 p26) 
                                       (and 
                                           (<= 1 x1761) 
                                           (<= x1761 n90)))) 
                               (forall ((x1763 Int) (x1764 A) (x1765 A)) 
                                   (=> 
                                       (and 
                                           (MS x1763 x1764 p26) 
                                           (MS x1763 x1765 p26)) 
                                       (= x1764 x1765))) 
                               (forall ((x1766 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x1766) 
                                           (<= x1766 n90)) 
                                       (exists ((x1767 A)) 
                                           (MS x1766 x1767 p26)))))) 
                       (shpath x1760 y36 p26) 
                       (exists ((x1768 A)) 
                           (MS i115 x1768 p26)) 
                       (not 
                           (= i115 1)) 
                       (not 
                           (length p26 i115))) 
                   (exists ((x1769 A) (x1770 PZA)) 
                       (and 
                           (MS i115 x1769 p26) 
                           (forall ((x1771 Int) (x1772 A)) 
                               (= 
                                   (MS x1771 x1772 x1770) 
                                   (and 
                                       (MS x1771 x1772 p26) 
                                       (<= 1 x1771) 
                                       (<= x1771 i115)))) 
                           (shpath x1760 x1769 x1770)))))
         :named hyp108))
(assert (! (forall ((x1773 A) (y37 A) (p27 PZA) (i116 Int)) 
               (=> 
                   (and 
                       (MS1 x1773 a) 
                       (MS1 y37 a) 
                       (exists ((n91 Int)) 
                           (and 
                               (<= 0 n91) 
                               (forall ((x1774 Int) (x1775 A)) 
                                   (=> 
                                       (MS x1774 x1775 p27) 
                                       (and 
                                           (<= 1 x1774) 
                                           (<= x1774 n91)))) 
                               (forall ((x1776 Int) (x1777 A) (x1778 A)) 
                                   (=> 
                                       (and 
                                           (MS x1776 x1777 p27) 
                                           (MS x1776 x1778 p27)) 
                                       (= x1777 x1778))) 
                               (forall ((x1779 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x1779) 
                                           (<= x1779 n91)) 
                                       (exists ((x1780 A)) 
                                           (MS x1779 x1780 p27)))))) 
                       (shpath x1773 y37 p27) 
                       (exists ((x1781 A)) 
                           (MS i116 x1781 p27)) 
                       (not 
                           (= i116 1)) 
                       (not 
                           (length p27 i116))) 
                   (and 
                       (exists ((x1782 A)) 
                           (and 
                               (MS i116 x1782 p27) 
                               (dist x1773 x1782 i116))) 
                       (exists ((x1783 A) (x1784 Int)) 
                           (and 
                               (exists ((x1785 Int)) 
                                   (and 
                                       (= x1785 (+ i116 1)) 
                                       (MS x1785 x1783 p27))) 
                               (= x1784 (+ i116 1)) 
                               (dist x1773 x1783 x1784))) 
                       (exists ((x1786 A) (x1787 A)) 
                           (and 
                               (MS i116 x1786 p27) 
                               (exists ((x1788 Int)) 
                                   (and 
                                       (= x1788 (+ i116 1)) 
                                       (MS x1788 x1787 p27))) 
                               (MS0 x1786 x1787 r))))))
         :named hyp109))
(assert (! (forall ((x1789 A) (y38 A) (p28 PZA) (z4 A)) 
               (=> 
                   (and 
                       (MS1 x1789 a) 
                       (MS1 y38 a) 
                       (exists ((n92 Int)) 
                           (and 
                               (<= 0 n92) 
                               (forall ((x1790 Int) (x1791 A)) 
                                   (=> 
                                       (MS x1790 x1791 p28) 
                                       (and 
                                           (<= 1 x1790) 
                                           (<= x1790 n92)))) 
                               (forall ((x1792 Int) (x1793 A) (x1794 A)) 
                                   (=> 
                                       (and 
                                           (MS x1792 x1793 p28) 
                                           (MS x1792 x1794 p28)) 
                                       (= x1793 x1794))) 
                               (forall ((x1795 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x1795) 
                                           (<= x1795 n92)) 
                                       (exists ((x1796 A)) 
                                           (MS x1795 x1796 p28)))))) 
                       (shpath x1789 y38 p28) 
                       (exists ((x1797 Int)) 
                           (MS x1797 z4 p28)) 
                       (not 
                           (= z4 x1789)) 
                       (not 
                           (= z4 y38))) 
                   (exists ((t3 A)) 
                       (and 
                           (MS1 t3 a) 
                           (forall ((x1798 Int) (x1799 Int)) 
                               (=> 
                                   (and 
                                       (dist x1789 z4 x1799) 
                                       (dist x1789 t3 x1798)) 
                                   (< x1799 x1798))) 
                           (MS0 z4 t3 r)))))
         :named hyp110))
(assert (! (forall ((s125 PZA) (s224 PZA) (b1 PA)) 
               (=> 
                   (and 
                       (exists ((n93 Int)) 
                           (and 
                               (<= 0 n93) 
                               (forall ((x1800 Int) (x1801 A)) 
                                   (=> 
                                       (MS x1800 x1801 s125) 
                                       (and 
                                           (<= 1 x1800) 
                                           (<= x1800 n93)))) 
                               (forall ((x1802 Int) (x1803 A) (x1804 A)) 
                                   (=> 
                                       (and 
                                           (MS x1802 x1803 s125) 
                                           (MS x1802 x1804 s125)) 
                                       (= x1803 x1804))) 
                               (forall ((x1805 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x1805) 
                                           (<= x1805 n93)) 
                                       (exists ((x1806 A)) 
                                           (MS x1805 x1806 s125)))))) 
                       (exists ((n94 Int)) 
                           (and 
                               (<= 0 n94) 
                               (forall ((x1807 Int) (x1808 A)) 
                                   (=> 
                                       (MS x1807 x1808 s224) 
                                       (and 
                                           (<= 1 x1807) 
                                           (<= x1807 n94)))) 
                               (forall ((x1809 Int) (x1810 A) (x1811 A)) 
                                   (=> 
                                       (and 
                                           (MS x1809 x1810 s224) 
                                           (MS x1809 x1811 s224)) 
                                       (= x1810 x1811))) 
                               (forall ((x1812 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x1812) 
                                           (<= x1812 n94)) 
                                       (exists ((x1813 A)) 
                                           (MS x1812 x1813 s224)))))) 
                       (forall ((x1814 A)) 
                           (=> 
                               (exists ((x1815 Int)) 
                                   (MS x1815 x1814 s125)) 
                               (MS1 x1814 b1))) 
                       (forall ((x1816 A)) 
                           (=> 
                               (exists ((x1817 Int)) 
                                   (MS x1817 x1816 s224)) 
                               (MS1 x1816 b1)))) 
                   (and 
                       (forall ((x1818 Int) (x1819 A)) 
                           (=> 
                               (exists ((x1820 PZA)) 
                                   (and 
                                       (cnc s125 s224 x1820) 
                                       (MS x1818 x1819 x1820))) 
                               (and 
                                   (<= 1 x1818) 
                                   (forall ((x1821 Int) (x1822 Int)) 
                                       (=> 
                                           (and 
                                               (length s125 x1822) 
                                               (length s224 x1821)) 
                                           (<= x1818 (+ x1822 x1821)))) 
                                   (MS1 x1819 b1)))) 
                       (forall ((x1823 Int) (x1824 A) (x1825 A)) 
                           (=> 
                               (and 
                                   (exists ((x1826 PZA)) 
                                       (and 
                                           (cnc s125 s224 x1826) 
                                           (MS x1823 x1824 x1826))) 
                                   (exists ((x1827 PZA)) 
                                       (and 
                                           (cnc s125 s224 x1827) 
                                           (MS x1823 x1825 x1827)))) 
                               (= x1824 x1825))) 
                       (forall ((x1828 Int)) 
                           (=> 
                               (and 
                                   (<= 1 x1828) 
                                   (forall ((x1829 Int) (x1830 Int)) 
                                       (=> 
                                           (and 
                                               (length s125 x1830) 
                                               (length s224 x1829)) 
                                           (<= x1828 (+ x1830 x1829))))) 
                               (exists ((x1831 A) (x1832 PZA)) 
                                   (and 
                                       (cnc s125 s224 x1832) 
                                       (MS x1828 x1831 x1832))))))))
         :named hyp111))
(assert (! (forall ((x1833 A) (y39 A)) 
               (=> 
                   (and 
                       (MS1 x1833 a) 
                       (MS1 y39 a)) 
                   (exists ((p29 PZA)) 
                       (and 
                           (path x1833 y39 p29) 
                           (exists ((x1834 Int)) 
                               (and 
                                   (length p29 x1834) 
                                   (dist x1833 y39 x1834)))))))
         :named hyp112))
(assert (! (forall ((x1835 A) (y40 A) (p30 PZA) (i117 Int)) 
               (=> 
                   (and 
                       (MS1 x1835 a) 
                       (MS1 y40 a) 
                       (exists ((n95 Int)) 
                           (and 
                               (<= 0 n95) 
                               (forall ((x1836 Int) (x1837 A)) 
                                   (=> 
                                       (MS x1836 x1837 p30) 
                                       (and 
                                           (<= 1 x1836) 
                                           (<= x1836 n95)))) 
                               (forall ((x1838 Int) (x1839 A) (x1840 A)) 
                                   (=> 
                                       (and 
                                           (MS x1838 x1839 p30) 
                                           (MS x1838 x1840 p30)) 
                                       (= x1839 x1840))) 
                               (forall ((x1841 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x1841) 
                                           (<= x1841 n95)) 
                                       (exists ((x1842 A)) 
                                           (MS x1841 x1842 p30)))))) 
                       (path x1835 y40 p30) 
                       (exists ((x1843 Int)) 
                           (and 
                               (length p30 x1843) 
                               (dist x1835 y40 x1843))) 
                       (exists ((x1844 A)) 
                           (MS i117 x1844 p30)) 
                       (not 
                           (= i117 1)) 
                       (not 
                           (length p30 i117))) 
                   (and 
                       (exists ((x1845 A) (x1846 PZA)) 
                           (and 
                               (MS i117 x1845 p30) 
                               (forall ((x1847 Int) (x1848 A)) 
                                   (= 
                                       (MS x1847 x1848 x1846) 
                                       (and 
                                           (MS x1847 x1848 p30) 
                                           (<= 1 x1847) 
                                           (<= x1847 i117)))) 
                               (path x1835 x1845 x1846))) 
                       (exists ((x1849 A) (x1850 Int)) 
                           (and 
                               (MS i117 x1849 p30) 
                               (exists ((x1851 PZA)) 
                                   (and 
                                       (forall ((x1852 Int) (x1853 A)) 
                                           (= 
                                               (MS x1852 x1853 x1851) 
                                               (and 
                                                   (MS x1852 x1853 p30) 
                                                   (<= 1 x1852) 
                                                   (<= x1852 i117)))) 
                                       (length x1851 x1850))) 
                               (dist x1835 x1849 x1850))))))
         :named hyp113))
(assert (! (forall ((x1854 A) (y41 A) (p31 PZA) (i118 Int)) 
               (=> 
                   (and 
                       (MS1 x1854 a) 
                       (MS1 y41 a) 
                       (exists ((n96 Int)) 
                           (and 
                               (<= 0 n96) 
                               (forall ((x1855 Int) (x1856 A)) 
                                   (=> 
                                       (MS x1855 x1856 p31) 
                                       (and 
                                           (<= 1 x1855) 
                                           (<= x1855 n96)))) 
                               (forall ((x1857 Int) (x1858 A) (x1859 A)) 
                                   (=> 
                                       (and 
                                           (MS x1857 x1858 p31) 
                                           (MS x1857 x1859 p31)) 
                                       (= x1858 x1859))) 
                               (forall ((x1860 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x1860) 
                                           (<= x1860 n96)) 
                                       (exists ((x1861 A)) 
                                           (MS x1860 x1861 p31)))))) 
                       (path x1854 y41 p31) 
                       (exists ((x1862 Int)) 
                           (and 
                               (length p31 x1862) 
                               (dist x1854 y41 x1862))) 
                       (exists ((x1863 A)) 
                           (MS i118 x1863 p31)) 
                       (not 
                           (= i118 1)) 
                       (not 
                           (length p31 i118))) 
                   (and 
                       (exists ((x1864 A)) 
                           (and 
                               (MS i118 x1864 p31) 
                               (dist x1854 x1864 i118))) 
                       (exists ((x1865 A) (x1866 Int)) 
                           (and 
                               (exists ((x1867 Int)) 
                                   (and 
                                       (= x1867 (+ i118 1)) 
                                       (MS x1867 x1865 p31))) 
                               (= x1866 (+ i118 1)) 
                               (dist x1854 x1865 x1866))) 
                       (exists ((x1868 A) (x1869 A)) 
                           (and 
                               (MS i118 x1868 p31) 
                               (exists ((x1870 Int)) 
                                   (and 
                                       (= x1870 (+ i118 1)) 
                                       (MS x1870 x1869 p31))) 
                               (MS0 x1868 x1869 r))))))
         :named hyp114))
(assert (! (forall ((x1871 A) (y42 A) (p32 PZA) (z5 A)) 
               (=> 
                   (and 
                       (MS1 x1871 a) 
                       (MS1 y42 a) 
                       (exists ((n97 Int)) 
                           (and 
                               (<= 0 n97) 
                               (forall ((x1872 Int) (x1873 A)) 
                                   (=> 
                                       (MS x1872 x1873 p32) 
                                       (and 
                                           (<= 1 x1872) 
                                           (<= x1872 n97)))) 
                               (forall ((x1874 Int) (x1875 A) (x1876 A)) 
                                   (=> 
                                       (and 
                                           (MS x1874 x1875 p32) 
                                           (MS x1874 x1876 p32)) 
                                       (= x1875 x1876))) 
                               (forall ((x1877 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x1877) 
                                           (<= x1877 n97)) 
                                       (exists ((x1878 A)) 
                                           (MS x1877 x1878 p32)))))) 
                       (path x1871 y42 p32) 
                       (exists ((x1879 Int)) 
                           (and 
                               (length p32 x1879) 
                               (dist x1871 y42 x1879))) 
                       (exists ((x1880 Int)) 
                           (MS x1880 z5 p32)) 
                       (not 
                           (= z5 x1871)) 
                       (not 
                           (= z5 y42))) 
                   (exists ((t4 A)) 
                       (and 
                           (MS1 t4 a) 
                           (forall ((x1881 Int) (x1882 Int)) 
                               (=> 
                                   (and 
                                       (dist x1871 z5 x1882) 
                                       (dist x1871 t4 x1881)) 
                                   (< x1882 x1881))) 
                           (MS0 z5 t4 r)))))
         :named hyp115))
(assert (! (forall ((y111 A) (y210 A) (x1883 A) (x1884 A) (p33 PZA) (q3 PZA)) 
               (=> 
                   (and 
                       (MS1 y111 a) 
                       (MS1 y210 a) 
                       (MS1 x1883 a) 
                       (MS1 x1884 a) 
                       (path x1883 y111 q3) 
                       (path y210 x1884 p33) 
                       (MS0 x1884 x1883 r)) 
                   (exists ((x1885 PZA)) 
                       (and 
                           (forall ((x1886 Int) (x1887 A)) 
                               (= 
                                   (MS x1886 x1887 x1885) 
                                   (or 
                                       (exists ((i119 Int)) 
                                           (and 
                                               (<= 1 i119) 
                                               (forall ((x1888 Int)) 
                                                   (=> 
                                                       (length p33 x1888) 
                                                       (<= i119 x1888))) 
                                               (= x1886 i119) 
                                               (MS i119 x1887 p33))) 
                                       (exists ((i120 Int)) 
                                           (and 
                                               (forall ((x1889 Int)) 
                                                   (=> 
                                                       (length p33 x1889) 
                                                       (<= (+ x1889 1) i120))) 
                                               (forall ((x1890 Int) (x1891 Int)) 
                                                   (=> 
                                                       (and 
                                                           (length p33 x1891) 
                                                           (length q3 x1890)) 
                                                       (<= i120 (+ x1891 x1890)))) 
                                               (= x1886 i120) 
                                               (exists ((x1892 Int)) 
                                                   (and 
                                                       (forall ((x1893 Int)) 
                                                           (=> 
                                                               (length p33 x1893) 
                                                               (= x1892 (- i120 x1893)))) 
                                                       (MS x1892 x1887 q3)))))))) 
                           (path y210 y111 x1885)))))
         :named hyp116))
(assert (! (forall ((x1894 A) (y43 A)) 
               (=> 
                   (and 
                       (MS1 x1894 a) 
                       (MS1 y43 a)) 
                   (forall ((x1895 PZA)) 
                       (= 
                           (exists ((x1896 A) (x1897 A)) 
                               (and 
                                   (= x1896 y43) 
                                   (= x1897 x1894) 
                                   (path x1896 x1897 x1895))) 
                           (exists ((x1898 PZA)) 
                               (and 
                                   (exists ((x1899 A) (x1900 A)) 
                                       (and 
                                           (= x1899 x1894) 
                                           (= x1900 y43) 
                                           (path x1899 x1900 x1898))) 
                                   (exists ((s61 PZA)) 
                                       (and 
                                           (exists ((n98 Int)) 
                                               (and 
                                                   (<= 0 n98) 
                                                   (forall ((x1901 Int) (x1902 A)) 
                                                       (=> 
                                                           (MS x1901 x1902 s61) 
                                                           (and 
                                                               (<= 1 x1901) 
                                                               (<= x1901 n98)))) 
                                                   (forall ((x1903 Int) (x1904 A) (x1905 A)) 
                                                       (=> 
                                                           (and 
                                                               (MS x1903 x1904 s61) 
                                                               (MS x1903 x1905 s61)) 
                                                           (= x1904 x1905))) 
                                                   (forall ((x1906 Int)) 
                                                       (=> 
                                                           (and 
                                                               (<= 1 x1906) 
                                                               (<= x1906 n98)) 
                                                           (exists ((x1907 A)) 
                                                               (MS x1906 x1907 s61)))))) 
                                           (forall ((x1908 Int) (x1909 A)) 
                                               (= 
                                                   (MS x1908 x1909 x1898) 
                                                   (MS x1908 x1909 s61))) 
                                           (forall ((x1910 Int) (x1911 A)) 
                                               (= 
                                                   (MS x1910 x1911 x1895) 
                                                   (exists ((i121 Int)) 
                                                       (and 
                                                           (<= 1 i121) 
                                                           (forall ((x1912 Int)) 
                                                               (=> 
                                                                   (length s61 x1912) 
                                                                   (<= i121 x1912))) 
                                                           (= x1910 i121) 
                                                           (exists ((x1913 Int)) 
                                                               (and 
                                                                   (forall ((x1914 Int)) 
                                                                       (=> 
                                                                           (length s61 x1914) 
                                                                           (= x1913 (+ (- x1914 i121) 1)))) 
                                                                   (MS x1913 x1911 s61)))))))))))))))
         :named hyp117))
(assert (! (forall ((x1915 A) (y44 A) (p34 PZA)) 
               (=> 
                   (path x1915 y44 p34) 
                   (exists ((x1916 PZA)) 
                       (and 
                           (forall ((x1917 Int) (x1918 A)) 
                               (= 
                                   (MS x1917 x1918 x1916) 
                                   (exists ((i122 Int)) 
                                       (and 
                                           (<= 1 i122) 
                                           (forall ((x1919 Int)) 
                                               (=> 
                                                   (length p34 x1919) 
                                                   (<= i122 x1919))) 
                                           (= x1917 i122) 
                                           (exists ((x1920 Int)) 
                                               (and 
                                                   (forall ((x1921 Int)) 
                                                       (=> 
                                                           (length p34 x1921) 
                                                           (= x1920 (+ (- x1921 i122) 1)))) 
                                                   (MS x1920 x1918 p34))))))) 
                           (path y44 x1915 x1916)))))
         :named hyp118))
(assert (! (not 
               (forall ((x1922 A)) 
                   (=> 
                       (exists ((x1923 Int)) 
                           (and 
                               (exists ((i123 Int)) 
                                   (and 
                                       (<= 1 i123) 
                                       (forall ((x1924 Int)) 
                                           (=> 
                                               (length p x1924) 
                                               (<= i123 x1924))) 
                                       (= x1923 i123) 
                                       (exists ((x1925 Int)) 
                                           (and 
                                               (forall ((x1926 Int)) 
                                                   (=> 
                                                       (length p x1926) 
                                                       (= x1925 (+ (- x1926 i123) 1)))) 
                                               (MS x1925 x1922 p))))) 
                               (<= 1 x1923) 
                               (forall ((x1927 Int)) 
                                   (=> 
                                       (length p x1927) 
                                       (<= x1923 (- x1927 1)))))) 
                       (MS1 x1922 a))))
         :named goal))
(check-sat)
(exit)

