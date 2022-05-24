(set-info :smt-lib-version 2.6)
(set-logic AUFLIA)
(set-info :source |Generator: Rodin SMT Plug-in|)
(set-info :license "https://creativecommons.org/licenses/by-nc/4.0/")
(set-info :category "industrial")
(set-info :status unsat)

(declare-sort A 0)
(declare-sort PA 0)
(declare-sort PZA 0)
(declare-fun MS (Int A PZA) Bool)
(declare-fun MS0 (A PA) Bool)
(declare-fun cnc (PZA PZA PZA) Bool)
(declare-fun dist (A A Int) Bool)
(declare-fun length (PZA Int) Bool)
(declare-fun path (A A PZA) Bool)
(declare-fun r (A A) Bool)
(declare-fun reverse (PZA PZA) Bool)
(declare-fun seq (PZA) Bool)
(declare-fun shpath (A A PZA) Bool)
(declare-fun a () PA)
(declare-fun p () PZA)
(declare-fun x () A)
(declare-fun y () A)

; Elementary Sets axiom (Singleton part)
(assert (forall ((x1307 A)) 
            (exists ((X PA)) 
                (and 
                    (MS0 x1307 X) 
                    (forall ((y17 A)) 
                        (=> 
                            (MS0 y17 X) 
                            (= y17 x1307)))))))
; Elementary Sets axiom (Singleton part)
(assert (forall ((x1308 Int) (x1309 A)) 
            (exists ((X0 PZA)) 
                (and 
                    (MS x1308 x1309 X0) 
                    (forall ((y18 Int) (y19 A)) 
                        (=> 
                            (MS y18 y19 X0) 
                            (and 
                                (= y18 x1308) 
                                (= y19 x1309))))))))
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
                       (r x17 x18) 
                       (= x17 x18))))
         :named hyp3))
(assert (! (and 
               (forall ((x19 A) (x20 A) (x21 Int)) 
                   (=> 
                       (dist x19 x20 x21) 
                       (and 
                           (MS0 x19 a) 
                           (MS0 x20 a) 
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
                           (MS0 x26 a) 
                           (MS0 x27 a)) 
                       (exists ((x28 Int)) 
                           (dist x26 x27 x28)))))
         :named hyp4))
(assert (! (forall ((x29 A) (x30 A)) 
               (=> 
                   (r x29 x30) 
                   (r x30 x29)))
         :named hyp5))
(assert (! (forall ((x31 A) (y0 A)) 
               (=> 
                   (and 
                       (MS0 x31 a) 
                       (MS0 y0 a)) 
                   (exists ((x32 Int)) 
                       (and 
                           (dist y0 x31 x32) 
                           (dist x31 y0 x32)))))
         :named hyp6))
(assert (! (and 
               (forall ((x33 PZA) (x34 Int)) 
                   (=> 
                       (length x33 x34) 
                       (and 
                           (exists ((s1 PZA)) 
                               (and 
                                   (exists ((n1 Int)) 
                                       (and 
                                           (<= 0 n1) 
                                           (forall ((x35 Int) (x36 A)) 
                                               (=> 
                                                   (MS x35 x36 s1) 
                                                   (and 
                                                       (<= 1 x35) 
                                                       (<= x35 n1)))) 
                                           (forall ((x37 Int) (x38 A) (x39 A)) 
                                               (=> 
                                                   (and 
                                                       (MS x37 x38 s1) 
                                                       (MS x37 x39 s1)) 
                                                   (= x38 x39))) 
                                           (forall ((x40 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x40) 
                                                       (<= x40 n1)) 
                                                   (exists ((x41 A)) 
                                                       (MS x40 x41 s1)))))) 
                                   (forall ((x42 Int) (x43 A)) 
                                       (= 
                                           (MS x42 x43 x33) 
                                           (MS x42 x43 s1))))) 
                           (<= 0 x34)))) 
               (forall ((x44 PZA) (x45 Int) (x46 Int)) 
                   (=> 
                       (and 
                           (length x44 x45) 
                           (length x44 x46)) 
                       (= x45 x46))) 
               (forall ((x47 PZA)) 
                   (=> 
                       (exists ((s2 PZA)) 
                           (and 
                               (exists ((n2 Int)) 
                                   (and 
                                       (<= 0 n2) 
                                       (forall ((x48 Int) (x49 A)) 
                                           (=> 
                                               (MS x48 x49 s2) 
                                               (and 
                                                   (<= 1 x48) 
                                                   (<= x48 n2)))) 
                                       (forall ((x50 Int) (x51 A) (x52 A)) 
                                           (=> 
                                               (and 
                                                   (MS x50 x51 s2) 
                                                   (MS x50 x52 s2)) 
                                               (= x51 x52))) 
                                       (forall ((x53 Int)) 
                                           (=> 
                                               (and 
                                                   (<= 1 x53) 
                                                   (<= x53 n2)) 
                                               (exists ((x54 A)) 
                                                   (MS x53 x54 s2)))))) 
                               (forall ((x55 Int) (x56 A)) 
                                   (= 
                                       (MS x55 x56 x47) 
                                       (MS x55 x56 s2))))) 
                       (exists ((x57 Int)) 
                           (length x47 x57)))))
         :named hyp7))
(assert (! (forall ((n3 Int) (s3 PZA)) 
               (=> 
                   (and 
                       (<= 0 n3) 
                       (forall ((x58 Int) (x59 A)) 
                           (=> 
                               (MS x58 x59 s3) 
                               (and 
                                   (<= 1 x58) 
                                   (<= x58 n3)))) 
                       (forall ((x60 Int) (x61 A) (x62 A)) 
                           (=> 
                               (and 
                                   (MS x60 x61 s3) 
                                   (MS x60 x62 s3)) 
                               (= x61 x62))) 
                       (forall ((x63 Int)) 
                           (=> 
                               (and 
                                   (<= 1 x63) 
                                   (<= x63 n3)) 
                               (exists ((x64 A)) 
                                   (MS x63 x64 s3))))) 
                   (exists ((n4 Int)) 
                       (and 
                           (<= 0 n4) 
                           (forall ((x65 Int) (x66 A)) 
                               (=> 
                                   (MS x65 x66 s3) 
                                   (and 
                                       (<= 1 x65) 
                                       (<= x65 n4)))) 
                           (forall ((x67 Int) (x68 A) (x69 A)) 
                               (=> 
                                   (and 
                                       (MS x67 x68 s3) 
                                       (MS x67 x69 s3)) 
                                   (= x68 x69))) 
                           (forall ((x70 Int)) 
                               (=> 
                                   (and 
                                       (<= 1 x70) 
                                       (<= x70 n4)) 
                                   (exists ((x71 A)) 
                                       (MS x70 x71 s3))))))))
         :named hyp8))
(assert (! (forall ((s4 PZA)) 
               (=> 
                   (exists ((n5 Int)) 
                       (and 
                           (<= 0 n5) 
                           (forall ((x72 Int) (x73 A)) 
                               (=> 
                                   (MS x72 x73 s4) 
                                   (and 
                                       (<= 1 x72) 
                                       (<= x72 n5)))) 
                           (forall ((x74 Int) (x75 A) (x76 A)) 
                               (=> 
                                   (and 
                                       (MS x74 x75 s4) 
                                       (MS x74 x76 s4)) 
                                   (= x75 x76))) 
                           (forall ((x77 Int)) 
                               (=> 
                                   (and 
                                       (<= 1 x77) 
                                       (<= x77 n5)) 
                                   (exists ((x78 A)) 
                                       (MS x77 x78 s4)))))) 
                   (and 
                       (forall ((x79 Int) (x80 A)) 
                           (=> 
                               (MS x79 x80 s4) 
                               (and 
                                   (<= 1 x79) 
                                   (forall ((x81 Int)) 
                                       (=> 
                                           (length s4 x81) 
                                           (<= x79 x81)))))) 
                       (forall ((x82 Int) (x83 A) (x84 A)) 
                           (=> 
                               (and 
                                   (MS x82 x83 s4) 
                                   (MS x82 x84 s4)) 
                               (= x83 x84))) 
                       (forall ((x85 Int)) 
                           (=> 
                               (and 
                                   (<= 1 x85) 
                                   (forall ((x86 Int)) 
                                       (=> 
                                           (length s4 x86) 
                                           (<= x85 x86)))) 
                               (exists ((x87 A)) 
                                   (MS x85 x87 s4)))))))
         :named hyp9))
(assert (! (forall ((x88 PZA) (x89 PZA) (x90 PZA)) 
               (= 
                   (cnc x88 x89 x90) 
                   (exists ((s10 PZA) (s20 PZA)) 
                       (and 
                           (exists ((n6 Int)) 
                               (and 
                                   (<= 0 n6) 
                                   (forall ((x91 Int) (x92 A)) 
                                       (=> 
                                           (MS x91 x92 s10) 
                                           (and 
                                               (<= 1 x91) 
                                               (<= x91 n6)))) 
                                   (forall ((x93 Int) (x94 A) (x95 A)) 
                                       (=> 
                                           (and 
                                               (MS x93 x94 s10) 
                                               (MS x93 x95 s10)) 
                                           (= x94 x95))) 
                                   (forall ((x96 Int)) 
                                       (=> 
                                           (and 
                                               (<= 1 x96) 
                                               (<= x96 n6)) 
                                           (exists ((x97 A)) 
                                               (MS x96 x97 s10)))))) 
                           (exists ((n7 Int)) 
                               (and 
                                   (<= 0 n7) 
                                   (forall ((x98 Int) (x99 A)) 
                                       (=> 
                                           (MS x98 x99 s20) 
                                           (and 
                                               (<= 1 x98) 
                                               (<= x98 n7)))) 
                                   (forall ((x100 Int) (x101 A) (x102 A)) 
                                       (=> 
                                           (and 
                                               (MS x100 x101 s20) 
                                               (MS x100 x102 s20)) 
                                           (= x101 x102))) 
                                   (forall ((x103 Int)) 
                                       (=> 
                                           (and 
                                               (<= 1 x103) 
                                               (<= x103 n7)) 
                                           (exists ((x104 A)) 
                                               (MS x103 x104 s20)))))) 
                           (forall ((x105 Int) (x106 A)) 
                               (= 
                                   (MS x105 x106 x88) 
                                   (MS x105 x106 s10))) 
                           (forall ((x107 Int) (x108 A)) 
                               (= 
                                   (MS x107 x108 x89) 
                                   (MS x107 x108 s20))) 
                           (forall ((x109 Int) (x110 A)) 
                               (= 
                                   (MS x109 x110 x90) 
                                   (or 
                                       (exists ((i Int)) 
                                           (and 
                                               (<= 1 i) 
                                               (forall ((x111 Int)) 
                                                   (=> 
                                                       (length s10 x111) 
                                                       (<= i x111))) 
                                               (= x109 i) 
                                               (MS i x110 s10))) 
                                       (exists ((i0 Int)) 
                                           (and 
                                               (forall ((x112 Int)) 
                                                   (=> 
                                                       (length s10 x112) 
                                                       (<= (+ x112 1) i0))) 
                                               (forall ((x113 Int) (x114 Int)) 
                                                   (=> 
                                                       (and 
                                                           (length s10 x114) 
                                                           (length s20 x113)) 
                                                       (<= i0 (+ x114 x113)))) 
                                               (= x109 i0) 
                                               (exists ((x115 Int)) 
                                                   (and 
                                                       (forall ((x116 Int)) 
                                                           (=> 
                                                               (length s10 x116) 
                                                               (= x115 (- i0 x116)))) 
                                                       (MS x115 x110 s20))))))))))))
         :named hyp10))
(assert (! (forall ((x117 PZA) (x118 PZA)) 
               (= 
                   (reverse x117 x118) 
                   (exists ((s5 PZA)) 
                       (and 
                           (exists ((n8 Int)) 
                               (and 
                                   (<= 0 n8) 
                                   (forall ((x119 Int) (x120 A)) 
                                       (=> 
                                           (MS x119 x120 s5) 
                                           (and 
                                               (<= 1 x119) 
                                               (<= x119 n8)))) 
                                   (forall ((x121 Int) (x122 A) (x123 A)) 
                                       (=> 
                                           (and 
                                               (MS x121 x122 s5) 
                                               (MS x121 x123 s5)) 
                                           (= x122 x123))) 
                                   (forall ((x124 Int)) 
                                       (=> 
                                           (and 
                                               (<= 1 x124) 
                                               (<= x124 n8)) 
                                           (exists ((x125 A)) 
                                               (MS x124 x125 s5)))))) 
                           (forall ((x126 Int) (x127 A)) 
                               (= 
                                   (MS x126 x127 x117) 
                                   (MS x126 x127 s5))) 
                           (forall ((x128 Int) (x129 A)) 
                               (= 
                                   (MS x128 x129 x118) 
                                   (exists ((i1 Int)) 
                                       (and 
                                           (<= 1 i1) 
                                           (forall ((x130 Int)) 
                                               (=> 
                                                   (length s5 x130) 
                                                   (<= i1 x130))) 
                                           (= x128 i1) 
                                           (exists ((x131 Int)) 
                                               (and 
                                                   (forall ((x132 Int)) 
                                                       (=> 
                                                           (length s5 x132) 
                                                           (= x131 (+ (- x132 i1) 1)))) 
                                                   (MS x131 x129 s5)))))))))))
         :named hyp11))
(assert (! (forall ((x133 A) (x134 A) (x135 PZA)) 
               (= 
                   (path x133 x134 x135) 
                   (exists ((x136 A) (y1 A) (p0 PZA)) 
                       (and 
                           (exists ((n9 Int)) 
                               (and 
                                   (<= 0 n9) 
                                   (forall ((x137 Int) (x138 A)) 
                                       (=> 
                                           (MS x137 x138 p0) 
                                           (and 
                                               (<= 1 x137) 
                                               (<= x137 n9)))) 
                                   (forall ((x139 Int) (x140 A) (x141 A)) 
                                       (=> 
                                           (and 
                                               (MS x139 x140 p0) 
                                               (MS x139 x141 p0)) 
                                           (= x140 x141))) 
                                   (forall ((x142 Int)) 
                                       (=> 
                                           (and 
                                               (<= 1 x142) 
                                               (<= x142 n9)) 
                                           (exists ((x143 A)) 
                                               (MS x142 x143 p0)))))) 
                           (forall ((x144 A)) 
                               (=> 
                                   (exists ((x145 Int)) 
                                       (MS x145 x144 p0)) 
                                   (MS0 x144 a))) 
                           (forall ((x146 Int)) 
                               (=> 
                                   (length p0 x146) 
                                   (< 1 x146))) 
                           (exists ((x147 Int)) 
                               (and 
                                   (= x147 1) 
                                   (MS x147 x136 p0))) 
                           (exists ((x148 Int)) 
                               (and 
                                   (length p0 x148) 
                                   (MS x148 y1 p0))) 
                           (forall ((i2 Int)) 
                               (=> 
                                   (and 
                                       (<= 1 i2) 
                                       (forall ((x149 Int)) 
                                           (=> 
                                               (length p0 x149) 
                                               (<= i2 (- x149 1))))) 
                                   (exists ((x150 A) (x151 A)) 
                                       (and 
                                           (MS i2 x150 p0) 
                                           (exists ((x152 Int)) 
                                               (and 
                                                   (= x152 (+ i2 1)) 
                                                   (MS x152 x151 p0))) 
                                           (r x150 x151))))) 
                           (= x133 x136) 
                           (= x134 y1) 
                           (forall ((x153 Int) (x154 A)) 
                               (= 
                                   (MS x153 x154 x135) 
                                   (MS x153 x154 p0)))))))
         :named hyp12))
(assert (! (and 
               (forall ((x155 PZA) (x156 PZA) (x157 PZA)) 
                   (=> 
                       (exists ((s11 PZA) (s21 PZA)) 
                           (and 
                               (exists ((n10 Int)) 
                                   (and 
                                       (<= 0 n10) 
                                       (forall ((x158 Int) (x159 A)) 
                                           (=> 
                                               (MS x158 x159 s11) 
                                               (and 
                                                   (<= 1 x158) 
                                                   (<= x158 n10)))) 
                                       (forall ((x160 Int) (x161 A) (x162 A)) 
                                           (=> 
                                               (and 
                                                   (MS x160 x161 s11) 
                                                   (MS x160 x162 s11)) 
                                               (= x161 x162))) 
                                       (forall ((x163 Int)) 
                                           (=> 
                                               (and 
                                                   (<= 1 x163) 
                                                   (<= x163 n10)) 
                                               (exists ((x164 A)) 
                                                   (MS x163 x164 s11)))))) 
                               (exists ((n11 Int)) 
                                   (and 
                                       (<= 0 n11) 
                                       (forall ((x165 Int) (x166 A)) 
                                           (=> 
                                               (MS x165 x166 s21) 
                                               (and 
                                                   (<= 1 x165) 
                                                   (<= x165 n11)))) 
                                       (forall ((x167 Int) (x168 A) (x169 A)) 
                                           (=> 
                                               (and 
                                                   (MS x167 x168 s21) 
                                                   (MS x167 x169 s21)) 
                                               (= x168 x169))) 
                                       (forall ((x170 Int)) 
                                           (=> 
                                               (and 
                                                   (<= 1 x170) 
                                                   (<= x170 n11)) 
                                               (exists ((x171 A)) 
                                                   (MS x170 x171 s21)))))) 
                               (forall ((x172 Int) (x173 A)) 
                                   (= 
                                       (MS x172 x173 x155) 
                                       (MS x172 x173 s11))) 
                               (forall ((x174 Int) (x175 A)) 
                                   (= 
                                       (MS x174 x175 x156) 
                                       (MS x174 x175 s21))) 
                               (forall ((x176 Int) (x177 A)) 
                                   (= 
                                       (MS x176 x177 x157) 
                                       (or 
                                           (exists ((i3 Int)) 
                                               (and 
                                                   (<= 1 i3) 
                                                   (forall ((x178 Int)) 
                                                       (=> 
                                                           (length s11 x178) 
                                                           (<= i3 x178))) 
                                                   (= x176 i3) 
                                                   (MS i3 x177 s11))) 
                                           (exists ((i4 Int)) 
                                               (and 
                                                   (forall ((x179 Int)) 
                                                       (=> 
                                                           (length s11 x179) 
                                                           (<= (+ x179 1) i4))) 
                                                   (forall ((x180 Int) (x181 Int)) 
                                                       (=> 
                                                           (and 
                                                               (length s11 x181) 
                                                               (length s21 x180)) 
                                                           (<= i4 (+ x181 x180)))) 
                                                   (= x176 i4) 
                                                   (exists ((x182 Int)) 
                                                       (and 
                                                           (forall ((x183 Int)) 
                                                               (=> 
                                                                   (length s11 x183) 
                                                                   (= x182 (- i4 x183)))) 
                                                           (MS x182 x177 s21)))))))))) 
                       (and 
                           (exists ((s6 PZA)) 
                               (and 
                                   (exists ((n12 Int)) 
                                       (and 
                                           (<= 0 n12) 
                                           (forall ((x184 Int) (x185 A)) 
                                               (=> 
                                                   (MS x184 x185 s6) 
                                                   (and 
                                                       (<= 1 x184) 
                                                       (<= x184 n12)))) 
                                           (forall ((x186 Int) (x187 A) (x188 A)) 
                                               (=> 
                                                   (and 
                                                       (MS x186 x187 s6) 
                                                       (MS x186 x188 s6)) 
                                                   (= x187 x188))) 
                                           (forall ((x189 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x189) 
                                                       (<= x189 n12)) 
                                                   (exists ((x190 A)) 
                                                       (MS x189 x190 s6)))))) 
                                   (forall ((x191 Int) (x192 A)) 
                                       (= 
                                           (MS x191 x192 x155) 
                                           (MS x191 x192 s6))))) 
                           (exists ((s7 PZA)) 
                               (and 
                                   (exists ((n13 Int)) 
                                       (and 
                                           (<= 0 n13) 
                                           (forall ((x193 Int) (x194 A)) 
                                               (=> 
                                                   (MS x193 x194 s7) 
                                                   (and 
                                                       (<= 1 x193) 
                                                       (<= x193 n13)))) 
                                           (forall ((x195 Int) (x196 A) (x197 A)) 
                                               (=> 
                                                   (and 
                                                       (MS x195 x196 s7) 
                                                       (MS x195 x197 s7)) 
                                                   (= x196 x197))) 
                                           (forall ((x198 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x198) 
                                                       (<= x198 n13)) 
                                                   (exists ((x199 A)) 
                                                       (MS x198 x199 s7)))))) 
                                   (forall ((x200 Int) (x201 A)) 
                                       (= 
                                           (MS x200 x201 x156) 
                                           (MS x200 x201 s7))))) 
                           (exists ((s8 PZA)) 
                               (and 
                                   (exists ((n14 Int)) 
                                       (and 
                                           (<= 0 n14) 
                                           (forall ((x202 Int) (x203 A)) 
                                               (=> 
                                                   (MS x202 x203 s8) 
                                                   (and 
                                                       (<= 1 x202) 
                                                       (<= x202 n14)))) 
                                           (forall ((x204 Int) (x205 A) (x206 A)) 
                                               (=> 
                                                   (and 
                                                       (MS x204 x205 s8) 
                                                       (MS x204 x206 s8)) 
                                                   (= x205 x206))) 
                                           (forall ((x207 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x207) 
                                                       (<= x207 n14)) 
                                                   (exists ((x208 A)) 
                                                       (MS x207 x208 s8)))))) 
                                   (forall ((x209 Int) (x210 A)) 
                                       (= 
                                           (MS x209 x210 x157) 
                                           (MS x209 x210 s8)))))))) 
               (forall ((x211 PZA) (x212 PZA) (x213 PZA) (x214 PZA)) 
                   (=> 
                       (and 
                           (exists ((s12 PZA) (s22 PZA)) 
                               (and 
                                   (exists ((n15 Int)) 
                                       (and 
                                           (<= 0 n15) 
                                           (forall ((x215 Int) (x216 A)) 
                                               (=> 
                                                   (MS x215 x216 s12) 
                                                   (and 
                                                       (<= 1 x215) 
                                                       (<= x215 n15)))) 
                                           (forall ((x217 Int) (x218 A) (x219 A)) 
                                               (=> 
                                                   (and 
                                                       (MS x217 x218 s12) 
                                                       (MS x217 x219 s12)) 
                                                   (= x218 x219))) 
                                           (forall ((x220 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x220) 
                                                       (<= x220 n15)) 
                                                   (exists ((x221 A)) 
                                                       (MS x220 x221 s12)))))) 
                                   (exists ((n16 Int)) 
                                       (and 
                                           (<= 0 n16) 
                                           (forall ((x222 Int) (x223 A)) 
                                               (=> 
                                                   (MS x222 x223 s22) 
                                                   (and 
                                                       (<= 1 x222) 
                                                       (<= x222 n16)))) 
                                           (forall ((x224 Int) (x225 A) (x226 A)) 
                                               (=> 
                                                   (and 
                                                       (MS x224 x225 s22) 
                                                       (MS x224 x226 s22)) 
                                                   (= x225 x226))) 
                                           (forall ((x227 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x227) 
                                                       (<= x227 n16)) 
                                                   (exists ((x228 A)) 
                                                       (MS x227 x228 s22)))))) 
                                   (forall ((x229 Int) (x230 A)) 
                                       (= 
                                           (MS x229 x230 x211) 
                                           (MS x229 x230 s12))) 
                                   (forall ((x231 Int) (x232 A)) 
                                       (= 
                                           (MS x231 x232 x212) 
                                           (MS x231 x232 s22))) 
                                   (forall ((x233 Int) (x234 A)) 
                                       (= 
                                           (MS x233 x234 x213) 
                                           (or 
                                               (exists ((i5 Int)) 
                                                   (and 
                                                       (<= 1 i5) 
                                                       (forall ((x235 Int)) 
                                                           (=> 
                                                               (length s12 x235) 
                                                               (<= i5 x235))) 
                                                       (= x233 i5) 
                                                       (MS i5 x234 s12))) 
                                               (exists ((i6 Int)) 
                                                   (and 
                                                       (forall ((x236 Int)) 
                                                           (=> 
                                                               (length s12 x236) 
                                                               (<= (+ x236 1) i6))) 
                                                       (forall ((x237 Int) (x238 Int)) 
                                                           (=> 
                                                               (and 
                                                                   (length s12 x238) 
                                                                   (length s22 x237)) 
                                                               (<= i6 (+ x238 x237)))) 
                                                       (= x233 i6) 
                                                       (exists ((x239 Int)) 
                                                           (and 
                                                               (forall ((x240 Int)) 
                                                                   (=> 
                                                                       (length s12 x240) 
                                                                       (= x239 (- i6 x240)))) 
                                                               (MS x239 x234 s22)))))))))) 
                           (exists ((s13 PZA) (s23 PZA)) 
                               (and 
                                   (exists ((n17 Int)) 
                                       (and 
                                           (<= 0 n17) 
                                           (forall ((x241 Int) (x242 A)) 
                                               (=> 
                                                   (MS x241 x242 s13) 
                                                   (and 
                                                       (<= 1 x241) 
                                                       (<= x241 n17)))) 
                                           (forall ((x243 Int) (x244 A) (x245 A)) 
                                               (=> 
                                                   (and 
                                                       (MS x243 x244 s13) 
                                                       (MS x243 x245 s13)) 
                                                   (= x244 x245))) 
                                           (forall ((x246 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x246) 
                                                       (<= x246 n17)) 
                                                   (exists ((x247 A)) 
                                                       (MS x246 x247 s13)))))) 
                                   (exists ((n18 Int)) 
                                       (and 
                                           (<= 0 n18) 
                                           (forall ((x248 Int) (x249 A)) 
                                               (=> 
                                                   (MS x248 x249 s23) 
                                                   (and 
                                                       (<= 1 x248) 
                                                       (<= x248 n18)))) 
                                           (forall ((x250 Int) (x251 A) (x252 A)) 
                                               (=> 
                                                   (and 
                                                       (MS x250 x251 s23) 
                                                       (MS x250 x252 s23)) 
                                                   (= x251 x252))) 
                                           (forall ((x253 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x253) 
                                                       (<= x253 n18)) 
                                                   (exists ((x254 A)) 
                                                       (MS x253 x254 s23)))))) 
                                   (forall ((x255 Int) (x256 A)) 
                                       (= 
                                           (MS x255 x256 x211) 
                                           (MS x255 x256 s13))) 
                                   (forall ((x257 Int) (x258 A)) 
                                       (= 
                                           (MS x257 x258 x212) 
                                           (MS x257 x258 s23))) 
                                   (forall ((x259 Int) (x260 A)) 
                                       (= 
                                           (MS x259 x260 x214) 
                                           (or 
                                               (exists ((i7 Int)) 
                                                   (and 
                                                       (<= 1 i7) 
                                                       (forall ((x261 Int)) 
                                                           (=> 
                                                               (length s13 x261) 
                                                               (<= i7 x261))) 
                                                       (= x259 i7) 
                                                       (MS i7 x260 s13))) 
                                               (exists ((i8 Int)) 
                                                   (and 
                                                       (forall ((x262 Int)) 
                                                           (=> 
                                                               (length s13 x262) 
                                                               (<= (+ x262 1) i8))) 
                                                       (forall ((x263 Int) (x264 Int)) 
                                                           (=> 
                                                               (and 
                                                                   (length s13 x264) 
                                                                   (length s23 x263)) 
                                                               (<= i8 (+ x264 x263)))) 
                                                       (= x259 i8) 
                                                       (exists ((x265 Int)) 
                                                           (and 
                                                               (forall ((x266 Int)) 
                                                                   (=> 
                                                                       (length s13 x266) 
                                                                       (= x265 (- i8 x266)))) 
                                                               (MS x265 x260 s23))))))))))) 
                       (forall ((x267 Int) (x268 A)) 
                           (= 
                               (MS x267 x268 x213) 
                               (MS x267 x268 x214))))) 
               (forall ((x269 PZA) (x270 PZA)) 
                   (=> 
                       (and 
                           (exists ((s9 PZA)) 
                               (and 
                                   (exists ((n19 Int)) 
                                       (and 
                                           (<= 0 n19) 
                                           (forall ((x271 Int) (x272 A)) 
                                               (=> 
                                                   (MS x271 x272 s9) 
                                                   (and 
                                                       (<= 1 x271) 
                                                       (<= x271 n19)))) 
                                           (forall ((x273 Int) (x274 A) (x275 A)) 
                                               (=> 
                                                   (and 
                                                       (MS x273 x274 s9) 
                                                       (MS x273 x275 s9)) 
                                                   (= x274 x275))) 
                                           (forall ((x276 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x276) 
                                                       (<= x276 n19)) 
                                                   (exists ((x277 A)) 
                                                       (MS x276 x277 s9)))))) 
                                   (forall ((x278 Int) (x279 A)) 
                                       (= 
                                           (MS x278 x279 x269) 
                                           (MS x278 x279 s9))))) 
                           (exists ((s14 PZA)) 
                               (and 
                                   (exists ((n20 Int)) 
                                       (and 
                                           (<= 0 n20) 
                                           (forall ((x280 Int) (x281 A)) 
                                               (=> 
                                                   (MS x280 x281 s14) 
                                                   (and 
                                                       (<= 1 x280) 
                                                       (<= x280 n20)))) 
                                           (forall ((x282 Int) (x283 A) (x284 A)) 
                                               (=> 
                                                   (and 
                                                       (MS x282 x283 s14) 
                                                       (MS x282 x284 s14)) 
                                                   (= x283 x284))) 
                                           (forall ((x285 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x285) 
                                                       (<= x285 n20)) 
                                                   (exists ((x286 A)) 
                                                       (MS x285 x286 s14)))))) 
                                   (forall ((x287 Int) (x288 A)) 
                                       (= 
                                           (MS x287 x288 x270) 
                                           (MS x287 x288 s14)))))) 
                       (exists ((x289 PZA) (s15 PZA) (s24 PZA)) 
                           (and 
                               (exists ((n21 Int)) 
                                   (and 
                                       (<= 0 n21) 
                                       (forall ((x290 Int) (x291 A)) 
                                           (=> 
                                               (MS x290 x291 s15) 
                                               (and 
                                                   (<= 1 x290) 
                                                   (<= x290 n21)))) 
                                       (forall ((x292 Int) (x293 A) (x294 A)) 
                                           (=> 
                                               (and 
                                                   (MS x292 x293 s15) 
                                                   (MS x292 x294 s15)) 
                                               (= x293 x294))) 
                                       (forall ((x295 Int)) 
                                           (=> 
                                               (and 
                                                   (<= 1 x295) 
                                                   (<= x295 n21)) 
                                               (exists ((x296 A)) 
                                                   (MS x295 x296 s15)))))) 
                               (exists ((n22 Int)) 
                                   (and 
                                       (<= 0 n22) 
                                       (forall ((x297 Int) (x298 A)) 
                                           (=> 
                                               (MS x297 x298 s24) 
                                               (and 
                                                   (<= 1 x297) 
                                                   (<= x297 n22)))) 
                                       (forall ((x299 Int) (x300 A) (x301 A)) 
                                           (=> 
                                               (and 
                                                   (MS x299 x300 s24) 
                                                   (MS x299 x301 s24)) 
                                               (= x300 x301))) 
                                       (forall ((x302 Int)) 
                                           (=> 
                                               (and 
                                                   (<= 1 x302) 
                                                   (<= x302 n22)) 
                                               (exists ((x303 A)) 
                                                   (MS x302 x303 s24)))))) 
                               (forall ((x304 Int) (x305 A)) 
                                   (= 
                                       (MS x304 x305 x269) 
                                       (MS x304 x305 s15))) 
                               (forall ((x306 Int) (x307 A)) 
                                   (= 
                                       (MS x306 x307 x270) 
                                       (MS x306 x307 s24))) 
                               (forall ((x308 Int) (x309 A)) 
                                   (= 
                                       (MS x308 x309 x289) 
                                       (or 
                                           (exists ((i9 Int)) 
                                               (and 
                                                   (<= 1 i9) 
                                                   (forall ((x310 Int)) 
                                                       (=> 
                                                           (length s15 x310) 
                                                           (<= i9 x310))) 
                                                   (= x308 i9) 
                                                   (MS i9 x309 s15))) 
                                           (exists ((i10 Int)) 
                                               (and 
                                                   (forall ((x311 Int)) 
                                                       (=> 
                                                           (length s15 x311) 
                                                           (<= (+ x311 1) i10))) 
                                                   (forall ((x312 Int) (x313 Int)) 
                                                       (=> 
                                                           (and 
                                                               (length s15 x313) 
                                                               (length s24 x312)) 
                                                           (<= i10 (+ x313 x312)))) 
                                                   (= x308 i10) 
                                                   (exists ((x314 Int)) 
                                                       (and 
                                                           (forall ((x315 Int)) 
                                                               (=> 
                                                                   (length s15 x315) 
                                                                   (= x314 (- i10 x315)))) 
                                                           (MS x314 x309 s24)))))))))))))
         :named hyp13))
(assert (! (forall ((s16 PZA) (s25 PZA)) 
               (=> 
                   (and 
                       (exists ((n23 Int)) 
                           (and 
                               (<= 0 n23) 
                               (forall ((x316 Int) (x317 A)) 
                                   (=> 
                                       (MS x316 x317 s16) 
                                       (and 
                                           (<= 1 x316) 
                                           (<= x316 n23)))) 
                               (forall ((x318 Int) (x319 A) (x320 A)) 
                                   (=> 
                                       (and 
                                           (MS x318 x319 s16) 
                                           (MS x318 x320 s16)) 
                                       (= x319 x320))) 
                               (forall ((x321 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x321) 
                                           (<= x321 n23)) 
                                       (exists ((x322 A)) 
                                           (MS x321 x322 s16)))))) 
                       (exists ((n24 Int)) 
                           (and 
                               (<= 0 n24) 
                               (forall ((x323 Int) (x324 A)) 
                                   (=> 
                                       (MS x323 x324 s25) 
                                       (and 
                                           (<= 1 x323) 
                                           (<= x323 n24)))) 
                               (forall ((x325 Int) (x326 A) (x327 A)) 
                                   (=> 
                                       (and 
                                           (MS x325 x326 s25) 
                                           (MS x325 x327 s25)) 
                                       (= x326 x327))) 
                               (forall ((x328 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x328) 
                                           (<= x328 n24)) 
                                       (exists ((x329 A)) 
                                           (MS x328 x329 s25))))))) 
                   (exists ((x330 PZA) (x331 Int)) 
                       (and 
                           (forall ((x332 Int) (x333 A)) 
                               (= 
                                   (MS x332 x333 x330) 
                                   (or 
                                       (exists ((i11 Int)) 
                                           (and 
                                               (<= 1 i11) 
                                               (forall ((x334 Int)) 
                                                   (=> 
                                                       (length s16 x334) 
                                                       (<= i11 x334))) 
                                               (= x332 i11) 
                                               (MS i11 x333 s16))) 
                                       (exists ((i12 Int)) 
                                           (and 
                                               (forall ((x335 Int)) 
                                                   (=> 
                                                       (length s16 x335) 
                                                       (<= (+ x335 1) i12))) 
                                               (forall ((x336 Int) (x337 Int)) 
                                                   (=> 
                                                       (and 
                                                           (length s16 x337) 
                                                           (length s25 x336)) 
                                                       (<= i12 (+ x337 x336)))) 
                                               (= x332 i12) 
                                               (exists ((x338 Int)) 
                                                   (and 
                                                       (forall ((x339 Int)) 
                                                           (=> 
                                                               (length s16 x339) 
                                                               (= x338 (- i12 x339)))) 
                                                       (MS x338 x333 s25)))))))) 
                           (forall ((x340 Int) (x341 Int)) 
                               (=> 
                                   (and 
                                       (length s16 x341) 
                                       (length s25 x340)) 
                                   (= x331 (+ x341 x340)))) 
                           (length x330 x331)))))
         :named hyp14))
(assert (! (forall ((s17 PZA) (s26 PZA)) 
               (=> 
                   (and 
                       (exists ((n25 Int)) 
                           (and 
                               (<= 0 n25) 
                               (forall ((x342 Int) (x343 A)) 
                                   (=> 
                                       (MS x342 x343 s17) 
                                       (and 
                                           (<= 1 x342) 
                                           (<= x342 n25)))) 
                               (forall ((x344 Int) (x345 A) (x346 A)) 
                                   (=> 
                                       (and 
                                           (MS x344 x345 s17) 
                                           (MS x344 x346 s17)) 
                                       (= x345 x346))) 
                               (forall ((x347 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x347) 
                                           (<= x347 n25)) 
                                       (exists ((x348 A)) 
                                           (MS x347 x348 s17)))))) 
                       (exists ((n26 Int)) 
                           (and 
                               (<= 0 n26) 
                               (forall ((x349 Int) (x350 A)) 
                                   (=> 
                                       (MS x349 x350 s26) 
                                       (and 
                                           (<= 1 x349) 
                                           (<= x349 n26)))) 
                               (forall ((x351 Int) (x352 A) (x353 A)) 
                                   (=> 
                                       (and 
                                           (MS x351 x352 s26) 
                                           (MS x351 x353 s26)) 
                                       (= x352 x353))) 
                               (forall ((x354 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x354) 
                                           (<= x354 n26)) 
                                       (exists ((x355 A)) 
                                           (MS x354 x355 s26))))))) 
                   (forall ((x356 Int)) 
                       (= 
                           (or 
                               (exists ((x357 A)) 
                                   (exists ((i13 Int)) 
                                       (and 
                                           (<= 1 i13) 
                                           (forall ((x358 Int)) 
                                               (=> 
                                                   (length s17 x358) 
                                                   (<= i13 x358))) 
                                           (= x356 i13) 
                                           (MS i13 x357 s17)))) 
                               (exists ((x359 A)) 
                                   (exists ((i14 Int)) 
                                       (and 
                                           (forall ((x360 Int)) 
                                               (=> 
                                                   (length s17 x360) 
                                                   (<= (+ x360 1) i14))) 
                                           (forall ((x361 Int) (x362 Int)) 
                                               (=> 
                                                   (and 
                                                       (length s17 x362) 
                                                       (length s26 x361)) 
                                                   (<= i14 (+ x362 x361)))) 
                                           (= x356 i14) 
                                           (exists ((x363 Int)) 
                                               (and 
                                                   (forall ((x364 Int)) 
                                                       (=> 
                                                           (length s17 x364) 
                                                           (= x363 (- i14 x364)))) 
                                                   (MS x363 x359 s26))))))) 
                           (and 
                               (<= 1 x356) 
                               (forall ((x365 Int) (x366 Int)) 
                                   (=> 
                                       (and 
                                           (length s17 x366) 
                                           (length s26 x365)) 
                                       (<= x356 (+ x366 x365)))))))))
         :named hyp15))
(assert (! (forall ((s18 PZA) (s27 PZA)) 
               (=> 
                   (and 
                       (exists ((n27 Int)) 
                           (and 
                               (<= 0 n27) 
                               (forall ((x367 Int) (x368 A)) 
                                   (=> 
                                       (MS x367 x368 s18) 
                                       (and 
                                           (<= 1 x367) 
                                           (<= x367 n27)))) 
                               (forall ((x369 Int) (x370 A) (x371 A)) 
                                   (=> 
                                       (and 
                                           (MS x369 x370 s18) 
                                           (MS x369 x371 s18)) 
                                       (= x370 x371))) 
                               (forall ((x372 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x372) 
                                           (<= x372 n27)) 
                                       (exists ((x373 A)) 
                                           (MS x372 x373 s18)))))) 
                       (exists ((n28 Int)) 
                           (and 
                               (<= 0 n28) 
                               (forall ((x374 Int) (x375 A)) 
                                   (=> 
                                       (MS x374 x375 s27) 
                                       (and 
                                           (<= 1 x374) 
                                           (<= x374 n28)))) 
                               (forall ((x376 Int) (x377 A) (x378 A)) 
                                   (=> 
                                       (and 
                                           (MS x376 x377 s27) 
                                           (MS x376 x378 s27)) 
                                       (= x377 x378))) 
                               (forall ((x379 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x379) 
                                           (<= x379 n28)) 
                                       (exists ((x380 A)) 
                                           (MS x379 x380 s27))))))) 
                   (forall ((x381 A)) 
                       (= 
                           (or 
                               (exists ((x382 Int)) 
                                   (exists ((i15 Int)) 
                                       (and 
                                           (<= 1 i15) 
                                           (forall ((x383 Int)) 
                                               (=> 
                                                   (length s18 x383) 
                                                   (<= i15 x383))) 
                                           (= x382 i15) 
                                           (MS i15 x381 s18)))) 
                               (exists ((x384 Int)) 
                                   (exists ((i16 Int)) 
                                       (and 
                                           (forall ((x385 Int)) 
                                               (=> 
                                                   (length s18 x385) 
                                                   (<= (+ x385 1) i16))) 
                                           (forall ((x386 Int) (x387 Int)) 
                                               (=> 
                                                   (and 
                                                       (length s18 x387) 
                                                       (length s27 x386)) 
                                                   (<= i16 (+ x387 x386)))) 
                                           (= x384 i16) 
                                           (exists ((x388 Int)) 
                                               (and 
                                                   (forall ((x389 Int)) 
                                                       (=> 
                                                           (length s18 x389) 
                                                           (= x388 (- i16 x389)))) 
                                                   (MS x388 x381 s27))))))) 
                           (or 
                               (exists ((x390 Int)) 
                                   (MS x390 x381 s18)) 
                               (exists ((x391 Int)) 
                                   (MS x391 x381 s27)))))))
         :named hyp16))
(assert (! (forall ((s19 PZA) (s28 PZA) (i17 Int)) 
               (=> 
                   (and 
                       (exists ((n29 Int)) 
                           (and 
                               (<= 0 n29) 
                               (forall ((x392 Int) (x393 A)) 
                                   (=> 
                                       (MS x392 x393 s19) 
                                       (and 
                                           (<= 1 x392) 
                                           (<= x392 n29)))) 
                               (forall ((x394 Int) (x395 A) (x396 A)) 
                                   (=> 
                                       (and 
                                           (MS x394 x395 s19) 
                                           (MS x394 x396 s19)) 
                                       (= x395 x396))) 
                               (forall ((x397 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x397) 
                                           (<= x397 n29)) 
                                       (exists ((x398 A)) 
                                           (MS x397 x398 s19)))))) 
                       (exists ((n30 Int)) 
                           (and 
                               (<= 0 n30) 
                               (forall ((x399 Int) (x400 A)) 
                                   (=> 
                                       (MS x399 x400 s28) 
                                       (and 
                                           (<= 1 x399) 
                                           (<= x399 n30)))) 
                               (forall ((x401 Int) (x402 A) (x403 A)) 
                                   (=> 
                                       (and 
                                           (MS x401 x402 s28) 
                                           (MS x401 x403 s28)) 
                                       (= x402 x403))) 
                               (forall ((x404 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x404) 
                                           (<= x404 n30)) 
                                       (exists ((x405 A)) 
                                           (MS x404 x405 s28)))))) 
                       (<= 1 i17) 
                       (forall ((x406 Int)) 
                           (=> 
                               (length s19 x406) 
                               (<= i17 x406)))) 
                   (or 
                       (exists ((i18 Int)) 
                           (and 
                               (<= 1 i18) 
                               (forall ((x407 Int)) 
                                   (=> 
                                       (length s19 x407) 
                                       (<= i18 x407))) 
                               (= i17 i18) 
                               (exists ((x408 A)) 
                                   (and 
                                       (MS i18 x408 s19) 
                                       (MS i17 x408 s19))))) 
                       (exists ((i19 Int)) 
                           (and 
                               (forall ((x409 Int)) 
                                   (=> 
                                       (length s19 x409) 
                                       (<= (+ x409 1) i19))) 
                               (forall ((x410 Int) (x411 Int)) 
                                   (=> 
                                       (and 
                                           (length s19 x411) 
                                           (length s28 x410)) 
                                       (<= i19 (+ x411 x410)))) 
                               (= i17 i19) 
                               (exists ((x412 A)) 
                                   (and 
                                       (exists ((x413 Int)) 
                                           (and 
                                               (forall ((x414 Int)) 
                                                   (=> 
                                                       (length s19 x414) 
                                                       (= x413 (- i19 x414)))) 
                                               (MS x413 x412 s28))) 
                                       (MS i17 x412 s19))))))))
         :named hyp17))
(assert (! (forall ((s110 PZA) (s29 PZA) (i20 Int)) 
               (=> 
                   (and 
                       (exists ((n31 Int)) 
                           (and 
                               (<= 0 n31) 
                               (forall ((x415 Int) (x416 A)) 
                                   (=> 
                                       (MS x415 x416 s110) 
                                       (and 
                                           (<= 1 x415) 
                                           (<= x415 n31)))) 
                               (forall ((x417 Int) (x418 A) (x419 A)) 
                                   (=> 
                                       (and 
                                           (MS x417 x418 s110) 
                                           (MS x417 x419 s110)) 
                                       (= x418 x419))) 
                               (forall ((x420 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x420) 
                                           (<= x420 n31)) 
                                       (exists ((x421 A)) 
                                           (MS x420 x421 s110)))))) 
                       (exists ((n32 Int)) 
                           (and 
                               (<= 0 n32) 
                               (forall ((x422 Int) (x423 A)) 
                                   (=> 
                                       (MS x422 x423 s29) 
                                       (and 
                                           (<= 1 x422) 
                                           (<= x422 n32)))) 
                               (forall ((x424 Int) (x425 A) (x426 A)) 
                                   (=> 
                                       (and 
                                           (MS x424 x425 s29) 
                                           (MS x424 x426 s29)) 
                                       (= x425 x426))) 
                               (forall ((x427 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x427) 
                                           (<= x427 n32)) 
                                       (exists ((x428 A)) 
                                           (MS x427 x428 s29)))))) 
                       (forall ((x429 Int)) 
                           (=> 
                               (length s110 x429) 
                               (<= (+ x429 1) i20))) 
                       (forall ((x430 Int) (x431 Int)) 
                           (=> 
                               (and 
                                   (length s110 x431) 
                                   (length s29 x430)) 
                               (<= i20 (+ x431 x430))))) 
                   (or 
                       (exists ((i21 Int)) 
                           (and 
                               (<= 1 i21) 
                               (forall ((x432 Int)) 
                                   (=> 
                                       (length s110 x432) 
                                       (<= i21 x432))) 
                               (= i20 i21) 
                               (exists ((x433 Int) (x434 A)) 
                                   (and 
                                       (forall ((x435 Int)) 
                                           (=> 
                                               (length s110 x435) 
                                               (= x433 (- i20 x435)))) 
                                       (MS i21 x434 s110) 
                                       (MS x433 x434 s29))))) 
                       (exists ((i22 Int)) 
                           (and 
                               (forall ((x436 Int)) 
                                   (=> 
                                       (length s110 x436) 
                                       (<= (+ x436 1) i22))) 
                               (forall ((x437 Int) (x438 Int)) 
                                   (=> 
                                       (and 
                                           (length s110 x438) 
                                           (length s29 x437)) 
                                       (<= i22 (+ x438 x437)))) 
                               (= i20 i22) 
                               (exists ((x439 Int) (x440 A)) 
                                   (and 
                                       (forall ((x441 Int)) 
                                           (=> 
                                               (length s110 x441) 
                                               (= x439 (- i20 x441)))) 
                                       (exists ((x442 Int)) 
                                           (and 
                                               (forall ((x443 Int)) 
                                                   (=> 
                                                       (length s110 x443) 
                                                       (= x442 (- i22 x443)))) 
                                               (MS x442 x440 s29))) 
                                       (MS x439 x440 s29))))))))
         :named hyp18))
(assert (! (forall ((s111 PZA) (s210 PZA) (b PA)) 
               (=> 
                   (and 
                       (exists ((n33 Int)) 
                           (and 
                               (<= 0 n33) 
                               (forall ((x444 Int) (x445 A)) 
                                   (=> 
                                       (MS x444 x445 s111) 
                                       (and 
                                           (<= 1 x444) 
                                           (<= x444 n33)))) 
                               (forall ((x446 Int) (x447 A) (x448 A)) 
                                   (=> 
                                       (and 
                                           (MS x446 x447 s111) 
                                           (MS x446 x448 s111)) 
                                       (= x447 x448))) 
                               (forall ((x449 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x449) 
                                           (<= x449 n33)) 
                                       (exists ((x450 A)) 
                                           (MS x449 x450 s111)))))) 
                       (exists ((n34 Int)) 
                           (and 
                               (<= 0 n34) 
                               (forall ((x451 Int) (x452 A)) 
                                   (=> 
                                       (MS x451 x452 s210) 
                                       (and 
                                           (<= 1 x451) 
                                           (<= x451 n34)))) 
                               (forall ((x453 Int) (x454 A) (x455 A)) 
                                   (=> 
                                       (and 
                                           (MS x453 x454 s210) 
                                           (MS x453 x455 s210)) 
                                       (= x454 x455))) 
                               (forall ((x456 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x456) 
                                           (<= x456 n34)) 
                                       (exists ((x457 A)) 
                                           (MS x456 x457 s210)))))) 
                       (forall ((x458 A)) 
                           (=> 
                               (exists ((x459 Int)) 
                                   (MS x459 x458 s111)) 
                               (MS0 x458 b))) 
                       (forall ((x460 A)) 
                           (=> 
                               (exists ((x461 Int)) 
                                   (MS x461 x460 s210)) 
                               (MS0 x460 b)))) 
                   (and 
                       (forall ((x462 Int) (x463 A)) 
                           (=> 
                               (or 
                                   (exists ((i23 Int)) 
                                       (and 
                                           (<= 1 i23) 
                                           (forall ((x464 Int)) 
                                               (=> 
                                                   (length s111 x464) 
                                                   (<= i23 x464))) 
                                           (= x462 i23) 
                                           (MS i23 x463 s111))) 
                                   (exists ((i24 Int)) 
                                       (and 
                                           (forall ((x465 Int)) 
                                               (=> 
                                                   (length s111 x465) 
                                                   (<= (+ x465 1) i24))) 
                                           (forall ((x466 Int) (x467 Int)) 
                                               (=> 
                                                   (and 
                                                       (length s111 x467) 
                                                       (length s210 x466)) 
                                                   (<= i24 (+ x467 x466)))) 
                                           (= x462 i24) 
                                           (exists ((x468 Int)) 
                                               (and 
                                                   (forall ((x469 Int)) 
                                                       (=> 
                                                           (length s111 x469) 
                                                           (= x468 (- i24 x469)))) 
                                                   (MS x468 x463 s210)))))) 
                               (and 
                                   (<= 1 x462) 
                                   (forall ((x470 Int) (x471 Int)) 
                                       (=> 
                                           (and 
                                               (length s111 x471) 
                                               (length s210 x470)) 
                                           (<= x462 (+ x471 x470)))) 
                                   (MS0 x463 b)))) 
                       (forall ((x472 Int) (x473 A) (x474 A)) 
                           (=> 
                               (and 
                                   (or 
                                       (exists ((i25 Int)) 
                                           (and 
                                               (<= 1 i25) 
                                               (forall ((x475 Int)) 
                                                   (=> 
                                                       (length s111 x475) 
                                                       (<= i25 x475))) 
                                               (= x472 i25) 
                                               (MS i25 x473 s111))) 
                                       (exists ((i26 Int)) 
                                           (and 
                                               (forall ((x476 Int)) 
                                                   (=> 
                                                       (length s111 x476) 
                                                       (<= (+ x476 1) i26))) 
                                               (forall ((x477 Int) (x478 Int)) 
                                                   (=> 
                                                       (and 
                                                           (length s111 x478) 
                                                           (length s210 x477)) 
                                                       (<= i26 (+ x478 x477)))) 
                                               (= x472 i26) 
                                               (exists ((x479 Int)) 
                                                   (and 
                                                       (forall ((x480 Int)) 
                                                           (=> 
                                                               (length s111 x480) 
                                                               (= x479 (- i26 x480)))) 
                                                       (MS x479 x473 s210)))))) 
                                   (or 
                                       (exists ((i27 Int)) 
                                           (and 
                                               (<= 1 i27) 
                                               (forall ((x481 Int)) 
                                                   (=> 
                                                       (length s111 x481) 
                                                       (<= i27 x481))) 
                                               (= x472 i27) 
                                               (MS i27 x474 s111))) 
                                       (exists ((i28 Int)) 
                                           (and 
                                               (forall ((x482 Int)) 
                                                   (=> 
                                                       (length s111 x482) 
                                                       (<= (+ x482 1) i28))) 
                                               (forall ((x483 Int) (x484 Int)) 
                                                   (=> 
                                                       (and 
                                                           (length s111 x484) 
                                                           (length s210 x483)) 
                                                       (<= i28 (+ x484 x483)))) 
                                               (= x472 i28) 
                                               (exists ((x485 Int)) 
                                                   (and 
                                                       (forall ((x486 Int)) 
                                                           (=> 
                                                               (length s111 x486) 
                                                               (= x485 (- i28 x486)))) 
                                                       (MS x485 x474 s210))))))) 
                               (= x473 x474))) 
                       (forall ((x487 Int)) 
                           (=> 
                               (and 
                                   (<= 1 x487) 
                                   (forall ((x488 Int) (x489 Int)) 
                                       (=> 
                                           (and 
                                               (length s111 x489) 
                                               (length s210 x488)) 
                                           (<= x487 (+ x489 x488))))) 
                               (or 
                                   (exists ((x490 A)) 
                                       (exists ((i29 Int)) 
                                           (and 
                                               (<= 1 i29) 
                                               (forall ((x491 Int)) 
                                                   (=> 
                                                       (length s111 x491) 
                                                       (<= i29 x491))) 
                                               (= x487 i29) 
                                               (MS i29 x490 s111)))) 
                                   (exists ((x492 A)) 
                                       (exists ((i30 Int)) 
                                           (and 
                                               (forall ((x493 Int)) 
                                                   (=> 
                                                       (length s111 x493) 
                                                       (<= (+ x493 1) i30))) 
                                               (forall ((x494 Int) (x495 Int)) 
                                                   (=> 
                                                       (and 
                                                           (length s111 x495) 
                                                           (length s210 x494)) 
                                                       (<= i30 (+ x495 x494)))) 
                                               (= x487 i30) 
                                               (exists ((x496 Int)) 
                                                   (and 
                                                       (forall ((x497 Int)) 
                                                           (=> 
                                                               (length s111 x497) 
                                                               (= x496 (- i30 x497)))) 
                                                       (MS x496 x492 s210))))))))))))
         :named hyp19))
(assert (! (and 
               (forall ((x498 PZA) (x499 PZA)) 
                   (=> 
                       (exists ((s30 PZA)) 
                           (and 
                               (exists ((n35 Int)) 
                                   (and 
                                       (<= 0 n35) 
                                       (forall ((x500 Int) (x501 A)) 
                                           (=> 
                                               (MS x500 x501 s30) 
                                               (and 
                                                   (<= 1 x500) 
                                                   (<= x500 n35)))) 
                                       (forall ((x502 Int) (x503 A) (x504 A)) 
                                           (=> 
                                               (and 
                                                   (MS x502 x503 s30) 
                                                   (MS x502 x504 s30)) 
                                               (= x503 x504))) 
                                       (forall ((x505 Int)) 
                                           (=> 
                                               (and 
                                                   (<= 1 x505) 
                                                   (<= x505 n35)) 
                                               (exists ((x506 A)) 
                                                   (MS x505 x506 s30)))))) 
                               (forall ((x507 Int) (x508 A)) 
                                   (= 
                                       (MS x507 x508 x498) 
                                       (MS x507 x508 s30))) 
                               (forall ((x509 Int) (x510 A)) 
                                   (= 
                                       (MS x509 x510 x499) 
                                       (exists ((i31 Int)) 
                                           (and 
                                               (<= 1 i31) 
                                               (forall ((x511 Int)) 
                                                   (=> 
                                                       (length s30 x511) 
                                                       (<= i31 x511))) 
                                               (= x509 i31) 
                                               (exists ((x512 Int)) 
                                                   (and 
                                                       (forall ((x513 Int)) 
                                                           (=> 
                                                               (length s30 x513) 
                                                               (= x512 (+ (- x513 i31) 1)))) 
                                                       (MS x512 x510 s30))))))))) 
                       (and 
                           (exists ((s31 PZA)) 
                               (and 
                                   (exists ((n36 Int)) 
                                       (and 
                                           (<= 0 n36) 
                                           (forall ((x514 Int) (x515 A)) 
                                               (=> 
                                                   (MS x514 x515 s31) 
                                                   (and 
                                                       (<= 1 x514) 
                                                       (<= x514 n36)))) 
                                           (forall ((x516 Int) (x517 A) (x518 A)) 
                                               (=> 
                                                   (and 
                                                       (MS x516 x517 s31) 
                                                       (MS x516 x518 s31)) 
                                                   (= x517 x518))) 
                                           (forall ((x519 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x519) 
                                                       (<= x519 n36)) 
                                                   (exists ((x520 A)) 
                                                       (MS x519 x520 s31)))))) 
                                   (forall ((x521 Int) (x522 A)) 
                                       (= 
                                           (MS x521 x522 x498) 
                                           (MS x521 x522 s31))))) 
                           (exists ((s32 PZA)) 
                               (and 
                                   (exists ((n37 Int)) 
                                       (and 
                                           (<= 0 n37) 
                                           (forall ((x523 Int) (x524 A)) 
                                               (=> 
                                                   (MS x523 x524 s32) 
                                                   (and 
                                                       (<= 1 x523) 
                                                       (<= x523 n37)))) 
                                           (forall ((x525 Int) (x526 A) (x527 A)) 
                                               (=> 
                                                   (and 
                                                       (MS x525 x526 s32) 
                                                       (MS x525 x527 s32)) 
                                                   (= x526 x527))) 
                                           (forall ((x528 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x528) 
                                                       (<= x528 n37)) 
                                                   (exists ((x529 A)) 
                                                       (MS x528 x529 s32)))))) 
                                   (forall ((x530 Int) (x531 A)) 
                                       (= 
                                           (MS x530 x531 x499) 
                                           (MS x530 x531 s32)))))))) 
               (forall ((x532 PZA) (x533 PZA) (x534 PZA)) 
                   (=> 
                       (and 
                           (exists ((s33 PZA)) 
                               (and 
                                   (exists ((n38 Int)) 
                                       (and 
                                           (<= 0 n38) 
                                           (forall ((x535 Int) (x536 A)) 
                                               (=> 
                                                   (MS x535 x536 s33) 
                                                   (and 
                                                       (<= 1 x535) 
                                                       (<= x535 n38)))) 
                                           (forall ((x537 Int) (x538 A) (x539 A)) 
                                               (=> 
                                                   (and 
                                                       (MS x537 x538 s33) 
                                                       (MS x537 x539 s33)) 
                                                   (= x538 x539))) 
                                           (forall ((x540 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x540) 
                                                       (<= x540 n38)) 
                                                   (exists ((x541 A)) 
                                                       (MS x540 x541 s33)))))) 
                                   (forall ((x542 Int) (x543 A)) 
                                       (= 
                                           (MS x542 x543 x532) 
                                           (MS x542 x543 s33))) 
                                   (forall ((x544 Int) (x545 A)) 
                                       (= 
                                           (MS x544 x545 x533) 
                                           (exists ((i32 Int)) 
                                               (and 
                                                   (<= 1 i32) 
                                                   (forall ((x546 Int)) 
                                                       (=> 
                                                           (length s33 x546) 
                                                           (<= i32 x546))) 
                                                   (= x544 i32) 
                                                   (exists ((x547 Int)) 
                                                       (and 
                                                           (forall ((x548 Int)) 
                                                               (=> 
                                                                   (length s33 x548) 
                                                                   (= x547 (+ (- x548 i32) 1)))) 
                                                           (MS x547 x545 s33))))))))) 
                           (exists ((s34 PZA)) 
                               (and 
                                   (exists ((n39 Int)) 
                                       (and 
                                           (<= 0 n39) 
                                           (forall ((x549 Int) (x550 A)) 
                                               (=> 
                                                   (MS x549 x550 s34) 
                                                   (and 
                                                       (<= 1 x549) 
                                                       (<= x549 n39)))) 
                                           (forall ((x551 Int) (x552 A) (x553 A)) 
                                               (=> 
                                                   (and 
                                                       (MS x551 x552 s34) 
                                                       (MS x551 x553 s34)) 
                                                   (= x552 x553))) 
                                           (forall ((x554 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x554) 
                                                       (<= x554 n39)) 
                                                   (exists ((x555 A)) 
                                                       (MS x554 x555 s34)))))) 
                                   (forall ((x556 Int) (x557 A)) 
                                       (= 
                                           (MS x556 x557 x532) 
                                           (MS x556 x557 s34))) 
                                   (forall ((x558 Int) (x559 A)) 
                                       (= 
                                           (MS x558 x559 x534) 
                                           (exists ((i33 Int)) 
                                               (and 
                                                   (<= 1 i33) 
                                                   (forall ((x560 Int)) 
                                                       (=> 
                                                           (length s34 x560) 
                                                           (<= i33 x560))) 
                                                   (= x558 i33) 
                                                   (exists ((x561 Int)) 
                                                       (and 
                                                           (forall ((x562 Int)) 
                                                               (=> 
                                                                   (length s34 x562) 
                                                                   (= x561 (+ (- x562 i33) 1)))) 
                                                           (MS x561 x559 s34)))))))))) 
                       (forall ((x563 Int) (x564 A)) 
                           (= 
                               (MS x563 x564 x533) 
                               (MS x563 x564 x534))))) 
               (forall ((x565 PZA)) 
                   (=> 
                       (exists ((s35 PZA)) 
                           (and 
                               (exists ((n40 Int)) 
                                   (and 
                                       (<= 0 n40) 
                                       (forall ((x566 Int) (x567 A)) 
                                           (=> 
                                               (MS x566 x567 s35) 
                                               (and 
                                                   (<= 1 x566) 
                                                   (<= x566 n40)))) 
                                       (forall ((x568 Int) (x569 A) (x570 A)) 
                                           (=> 
                                               (and 
                                                   (MS x568 x569 s35) 
                                                   (MS x568 x570 s35)) 
                                               (= x569 x570))) 
                                       (forall ((x571 Int)) 
                                           (=> 
                                               (and 
                                                   (<= 1 x571) 
                                                   (<= x571 n40)) 
                                               (exists ((x572 A)) 
                                                   (MS x571 x572 s35)))))) 
                               (forall ((x573 Int) (x574 A)) 
                                   (= 
                                       (MS x573 x574 x565) 
                                       (MS x573 x574 s35))))) 
                       (exists ((x575 PZA) (s36 PZA)) 
                           (and 
                               (exists ((n41 Int)) 
                                   (and 
                                       (<= 0 n41) 
                                       (forall ((x576 Int) (x577 A)) 
                                           (=> 
                                               (MS x576 x577 s36) 
                                               (and 
                                                   (<= 1 x576) 
                                                   (<= x576 n41)))) 
                                       (forall ((x578 Int) (x579 A) (x580 A)) 
                                           (=> 
                                               (and 
                                                   (MS x578 x579 s36) 
                                                   (MS x578 x580 s36)) 
                                               (= x579 x580))) 
                                       (forall ((x581 Int)) 
                                           (=> 
                                               (and 
                                                   (<= 1 x581) 
                                                   (<= x581 n41)) 
                                               (exists ((x582 A)) 
                                                   (MS x581 x582 s36)))))) 
                               (forall ((x583 Int) (x584 A)) 
                                   (= 
                                       (MS x583 x584 x565) 
                                       (MS x583 x584 s36))) 
                               (forall ((x585 Int) (x586 A)) 
                                   (= 
                                       (MS x585 x586 x575) 
                                       (exists ((i34 Int)) 
                                           (and 
                                               (<= 1 i34) 
                                               (forall ((x587 Int)) 
                                                   (=> 
                                                       (length s36 x587) 
                                                       (<= i34 x587))) 
                                               (= x585 i34) 
                                               (exists ((x588 Int)) 
                                                   (and 
                                                       (forall ((x589 Int)) 
                                                           (=> 
                                                               (length s36 x589) 
                                                               (= x588 (+ (- x589 i34) 1)))) 
                                                       (MS x588 x586 s36))))))))))))
         :named hyp20))
(assert (! (forall ((s37 PZA)) 
               (=> 
                   (exists ((n42 Int)) 
                       (and 
                           (<= 0 n42) 
                           (forall ((x590 Int) (x591 A)) 
                               (=> 
                                   (MS x590 x591 s37) 
                                   (and 
                                       (<= 1 x590) 
                                       (<= x590 n42)))) 
                           (forall ((x592 Int) (x593 A) (x594 A)) 
                               (=> 
                                   (and 
                                       (MS x592 x593 s37) 
                                       (MS x592 x594 s37)) 
                                   (= x593 x594))) 
                           (forall ((x595 Int)) 
                               (=> 
                                   (and 
                                       (<= 1 x595) 
                                       (<= x595 n42)) 
                                   (exists ((x596 A)) 
                                       (MS x595 x596 s37)))))) 
                   (exists ((x597 PZA) (x598 Int)) 
                       (and 
                           (forall ((x599 Int) (x600 A)) 
                               (= 
                                   (MS x599 x600 x597) 
                                   (exists ((i35 Int)) 
                                       (and 
                                           (<= 1 i35) 
                                           (forall ((x601 Int)) 
                                               (=> 
                                                   (length s37 x601) 
                                                   (<= i35 x601))) 
                                           (= x599 i35) 
                                           (exists ((x602 Int)) 
                                               (and 
                                                   (forall ((x603 Int)) 
                                                       (=> 
                                                           (length s37 x603) 
                                                           (= x602 (+ (- x603 i35) 1)))) 
                                                   (MS x602 x600 s37))))))) 
                           (length s37 x598) 
                           (length x597 x598)))))
         :named hyp21))
(assert (! (forall ((s38 PZA)) 
               (=> 
                   (exists ((n43 Int)) 
                       (and 
                           (<= 0 n43) 
                           (forall ((x604 Int) (x605 A)) 
                               (=> 
                                   (MS x604 x605 s38) 
                                   (and 
                                       (<= 1 x604) 
                                       (<= x604 n43)))) 
                           (forall ((x606 Int) (x607 A) (x608 A)) 
                               (=> 
                                   (and 
                                       (MS x606 x607 s38) 
                                       (MS x606 x608 s38)) 
                                   (= x607 x608))) 
                           (forall ((x609 Int)) 
                               (=> 
                                   (and 
                                       (<= 1 x609) 
                                       (<= x609 n43)) 
                                   (exists ((x610 A)) 
                                       (MS x609 x610 s38)))))) 
                   (forall ((x611 A)) 
                       (= 
                           (exists ((i36 Int)) 
                               (and 
                                   (<= 1 i36) 
                                   (forall ((x612 Int)) 
                                       (=> 
                                           (length s38 x612) 
                                           (<= i36 x612))) 
                                   (exists ((x613 Int)) 
                                       (and 
                                           (forall ((x614 Int)) 
                                               (=> 
                                                   (length s38 x614) 
                                                   (= x613 (+ (- x614 i36) 1)))) 
                                           (MS x613 x611 s38))))) 
                           (exists ((x615 Int)) 
                               (MS x615 x611 s38))))))
         :named hyp22))
(assert (! (forall ((s39 PZA)) 
               (=> 
                   (exists ((n44 Int)) 
                       (and 
                           (<= 0 n44) 
                           (forall ((x616 Int) (x617 A)) 
                               (=> 
                                   (MS x616 x617 s39) 
                                   (and 
                                       (<= 1 x616) 
                                       (<= x616 n44)))) 
                           (forall ((x618 Int) (x619 A) (x620 A)) 
                               (=> 
                                   (and 
                                       (MS x618 x619 s39) 
                                       (MS x618 x620 s39)) 
                                   (= x619 x620))) 
                           (forall ((x621 Int)) 
                               (=> 
                                   (and 
                                       (<= 1 x621) 
                                       (<= x621 n44)) 
                                   (exists ((x622 A)) 
                                       (MS x621 x622 s39)))))) 
                   (forall ((x623 Int) (x624 A)) 
                       (= 
                           (exists ((i37 Int)) 
                               (and 
                                   (<= 1 i37) 
                                   (forall ((x625 Int)) 
                                       (=> 
                                           (exists ((x626 PZA)) 
                                               (and 
                                                   (forall ((x627 Int) (x628 A)) 
                                                       (= 
                                                           (MS x627 x628 x626) 
                                                           (exists ((i38 Int)) 
                                                               (and 
                                                                   (<= 1 i38) 
                                                                   (forall ((x629 Int)) 
                                                                       (=> 
                                                                           (length s39 x629) 
                                                                           (<= i38 x629))) 
                                                                   (= x627 i38) 
                                                                   (exists ((x630 Int)) 
                                                                       (and 
                                                                           (forall ((x631 Int)) 
                                                                               (=> 
                                                                                   (length s39 x631) 
                                                                                   (= x630 (+ (- x631 i38) 1)))) 
                                                                           (MS x630 x628 s39))))))) 
                                                   (length x626 x625))) 
                                           (<= i37 x625))) 
                                   (= x623 i37) 
                                   (exists ((x632 Int)) 
                                       (and 
                                           (forall ((x633 Int) (x634 Int)) 
                                               (=> 
                                                   (and 
                                                       (length s39 x634) 
                                                       (exists ((x635 PZA)) 
                                                           (and 
                                                               (forall ((x636 Int) (x637 A)) 
                                                                   (= 
                                                                       (MS x636 x637 x635) 
                                                                       (exists ((i39 Int)) 
                                                                           (and 
                                                                               (<= 1 i39) 
                                                                               (forall ((x638 Int)) 
                                                                                   (=> 
                                                                                       (length s39 x638) 
                                                                                       (<= i39 x638))) 
                                                                               (= x636 i39) 
                                                                               (exists ((x639 Int)) 
                                                                                   (and 
                                                                                       (forall ((x640 Int)) 
                                                                                           (=> 
                                                                                               (length s39 x640) 
                                                                                               (= x639 (+ (- x640 i39) 1)))) 
                                                                                       (MS x639 x637 s39))))))) 
                                                               (length x635 x633)))) 
                                                   (= x632 (+ (- x634 (+ (- x633 i37) 1)) 1)))) 
                                           (MS x632 x624 s39))))) 
                           (MS x623 x624 s39)))))
         :named hyp23))
(assert (! (forall ((x641 A) (y2 A)) 
               (=> 
                   (and 
                       (MS0 x641 a) 
                       (MS0 y2 a)) 
                   (exists ((x642 Int)) 
                       (and 
                           (exists ((x643 PZA)) 
                               (and 
                                   (exists ((x644 A) (x645 A)) 
                                       (and 
                                           (= x644 x641) 
                                           (= x645 y2) 
                                           (exists ((x646 A) (y3 A) (p1 PZA)) 
                                               (and 
                                                   (exists ((n45 Int)) 
                                                       (and 
                                                           (<= 0 n45) 
                                                           (forall ((x647 Int) (x648 A)) 
                                                               (=> 
                                                                   (MS x647 x648 p1) 
                                                                   (and 
                                                                       (<= 1 x647) 
                                                                       (<= x647 n45)))) 
                                                           (forall ((x649 Int) (x650 A) (x651 A)) 
                                                               (=> 
                                                                   (and 
                                                                       (MS x649 x650 p1) 
                                                                       (MS x649 x651 p1)) 
                                                                   (= x650 x651))) 
                                                           (forall ((x652 Int)) 
                                                               (=> 
                                                                   (and 
                                                                       (<= 1 x652) 
                                                                       (<= x652 n45)) 
                                                                   (exists ((x653 A)) 
                                                                       (MS x652 x653 p1)))))) 
                                                   (forall ((x654 A)) 
                                                       (=> 
                                                           (exists ((x655 Int)) 
                                                               (MS x655 x654 p1)) 
                                                           (MS0 x654 a))) 
                                                   (forall ((x656 Int)) 
                                                       (=> 
                                                           (length p1 x656) 
                                                           (< 1 x656))) 
                                                   (exists ((x657 Int)) 
                                                       (and 
                                                           (= x657 1) 
                                                           (MS x657 x646 p1))) 
                                                   (exists ((x658 Int)) 
                                                       (and 
                                                           (length p1 x658) 
                                                           (MS x658 y3 p1))) 
                                                   (forall ((i40 Int)) 
                                                       (=> 
                                                           (and 
                                                               (<= 1 i40) 
                                                               (forall ((x659 Int)) 
                                                                   (=> 
                                                                       (length p1 x659) 
                                                                       (<= i40 (- x659 1))))) 
                                                           (exists ((x660 A) (x661 A)) 
                                                               (and 
                                                                   (MS i40 x660 p1) 
                                                                   (exists ((x662 Int)) 
                                                                       (and 
                                                                           (= x662 (+ i40 1)) 
                                                                           (MS x662 x661 p1))) 
                                                                   (r x660 x661))))) 
                                                   (= x644 x646) 
                                                   (= x645 y3) 
                                                   (forall ((x663 Int) (x664 A)) 
                                                       (= 
                                                           (MS x663 x664 x643) 
                                                           (MS x663 x664 p1))))))) 
                                   (length x643 x642))) 
                           (forall ((x665 Int)) 
                               (=> 
                                   (exists ((x666 PZA)) 
                                       (and 
                                           (exists ((x667 A) (x668 A)) 
                                               (and 
                                                   (= x667 x641) 
                                                   (= x668 y2) 
                                                   (exists ((x669 A) (y4 A) (p2 PZA)) 
                                                       (and 
                                                           (exists ((n46 Int)) 
                                                               (and 
                                                                   (<= 0 n46) 
                                                                   (forall ((x670 Int) (x671 A)) 
                                                                       (=> 
                                                                           (MS x670 x671 p2) 
                                                                           (and 
                                                                               (<= 1 x670) 
                                                                               (<= x670 n46)))) 
                                                                   (forall ((x672 Int) (x673 A) (x674 A)) 
                                                                       (=> 
                                                                           (and 
                                                                               (MS x672 x673 p2) 
                                                                               (MS x672 x674 p2)) 
                                                                           (= x673 x674))) 
                                                                   (forall ((x675 Int)) 
                                                                       (=> 
                                                                           (and 
                                                                               (<= 1 x675) 
                                                                               (<= x675 n46)) 
                                                                           (exists ((x676 A)) 
                                                                               (MS x675 x676 p2)))))) 
                                                           (forall ((x677 A)) 
                                                               (=> 
                                                                   (exists ((x678 Int)) 
                                                                       (MS x678 x677 p2)) 
                                                                   (MS0 x677 a))) 
                                                           (forall ((x679 Int)) 
                                                               (=> 
                                                                   (length p2 x679) 
                                                                   (< 1 x679))) 
                                                           (exists ((x680 Int)) 
                                                               (and 
                                                                   (= x680 1) 
                                                                   (MS x680 x669 p2))) 
                                                           (exists ((x681 Int)) 
                                                               (and 
                                                                   (length p2 x681) 
                                                                   (MS x681 y4 p2))) 
                                                           (forall ((i41 Int)) 
                                                               (=> 
                                                                   (and 
                                                                       (<= 1 i41) 
                                                                       (forall ((x682 Int)) 
                                                                           (=> 
                                                                               (length p2 x682) 
                                                                               (<= i41 (- x682 1))))) 
                                                                   (exists ((x683 A) (x684 A)) 
                                                                       (and 
                                                                           (MS i41 x683 p2) 
                                                                           (exists ((x685 Int)) 
                                                                               (and 
                                                                                   (= x685 (+ i41 1)) 
                                                                                   (MS x685 x684 p2))) 
                                                                           (r x683 x684))))) 
                                                           (= x667 x669) 
                                                           (= x668 y4) 
                                                           (forall ((x686 Int) (x687 A)) 
                                                               (= 
                                                                   (MS x686 x687 x666) 
                                                                   (MS x686 x687 p2))))))) 
                                           (length x666 x665))) 
                                   (<= x642 x665))) 
                           (dist x641 y2 x642)))))
         :named hyp24))
(assert (! (forall ((x688 A) (y5 A)) 
               (=> 
                   (and 
                       (MS0 x688 a) 
                       (MS0 y5 a)) 
                   (forall ((x689 PZA)) 
                       (= 
                           (exists ((x690 A) (x691 A)) 
                               (and 
                                   (= x690 y5) 
                                   (= x691 x688) 
                                   (exists ((x692 A) (y6 A) (p3 PZA)) 
                                       (and 
                                           (exists ((n47 Int)) 
                                               (and 
                                                   (<= 0 n47) 
                                                   (forall ((x693 Int) (x694 A)) 
                                                       (=> 
                                                           (MS x693 x694 p3) 
                                                           (and 
                                                               (<= 1 x693) 
                                                               (<= x693 n47)))) 
                                                   (forall ((x695 Int) (x696 A) (x697 A)) 
                                                       (=> 
                                                           (and 
                                                               (MS x695 x696 p3) 
                                                               (MS x695 x697 p3)) 
                                                           (= x696 x697))) 
                                                   (forall ((x698 Int)) 
                                                       (=> 
                                                           (and 
                                                               (<= 1 x698) 
                                                               (<= x698 n47)) 
                                                           (exists ((x699 A)) 
                                                               (MS x698 x699 p3)))))) 
                                           (forall ((x700 A)) 
                                               (=> 
                                                   (exists ((x701 Int)) 
                                                       (MS x701 x700 p3)) 
                                                   (MS0 x700 a))) 
                                           (forall ((x702 Int)) 
                                               (=> 
                                                   (length p3 x702) 
                                                   (< 1 x702))) 
                                           (exists ((x703 Int)) 
                                               (and 
                                                   (= x703 1) 
                                                   (MS x703 x692 p3))) 
                                           (exists ((x704 Int)) 
                                               (and 
                                                   (length p3 x704) 
                                                   (MS x704 y6 p3))) 
                                           (forall ((i42 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 i42) 
                                                       (forall ((x705 Int)) 
                                                           (=> 
                                                               (length p3 x705) 
                                                               (<= i42 (- x705 1))))) 
                                                   (exists ((x706 A) (x707 A)) 
                                                       (and 
                                                           (MS i42 x706 p3) 
                                                           (exists ((x708 Int)) 
                                                               (and 
                                                                   (= x708 (+ i42 1)) 
                                                                   (MS x708 x707 p3))) 
                                                           (r x706 x707))))) 
                                           (= x690 x692) 
                                           (= x691 y6) 
                                           (forall ((x709 Int) (x710 A)) 
                                               (= 
                                                   (MS x709 x710 x689) 
                                                   (MS x709 x710 p3))))))) 
                           (exists ((x711 PZA)) 
                               (and 
                                   (exists ((x712 A) (x713 A)) 
                                       (and 
                                           (= x712 x688) 
                                           (= x713 y5) 
                                           (exists ((x714 A) (y7 A) (p4 PZA)) 
                                               (and 
                                                   (exists ((n48 Int)) 
                                                       (and 
                                                           (<= 0 n48) 
                                                           (forall ((x715 Int) (x716 A)) 
                                                               (=> 
                                                                   (MS x715 x716 p4) 
                                                                   (and 
                                                                       (<= 1 x715) 
                                                                       (<= x715 n48)))) 
                                                           (forall ((x717 Int) (x718 A) (x719 A)) 
                                                               (=> 
                                                                   (and 
                                                                       (MS x717 x718 p4) 
                                                                       (MS x717 x719 p4)) 
                                                                   (= x718 x719))) 
                                                           (forall ((x720 Int)) 
                                                               (=> 
                                                                   (and 
                                                                       (<= 1 x720) 
                                                                       (<= x720 n48)) 
                                                                   (exists ((x721 A)) 
                                                                       (MS x720 x721 p4)))))) 
                                                   (forall ((x722 A)) 
                                                       (=> 
                                                           (exists ((x723 Int)) 
                                                               (MS x723 x722 p4)) 
                                                           (MS0 x722 a))) 
                                                   (forall ((x724 Int)) 
                                                       (=> 
                                                           (length p4 x724) 
                                                           (< 1 x724))) 
                                                   (exists ((x725 Int)) 
                                                       (and 
                                                           (= x725 1) 
                                                           (MS x725 x714 p4))) 
                                                   (exists ((x726 Int)) 
                                                       (and 
                                                           (length p4 x726) 
                                                           (MS x726 y7 p4))) 
                                                   (forall ((i43 Int)) 
                                                       (=> 
                                                           (and 
                                                               (<= 1 i43) 
                                                               (forall ((x727 Int)) 
                                                                   (=> 
                                                                       (length p4 x727) 
                                                                       (<= i43 (- x727 1))))) 
                                                           (exists ((x728 A) (x729 A)) 
                                                               (and 
                                                                   (MS i43 x728 p4) 
                                                                   (exists ((x730 Int)) 
                                                                       (and 
                                                                           (= x730 (+ i43 1)) 
                                                                           (MS x730 x729 p4))) 
                                                                   (r x728 x729))))) 
                                                   (= x712 x714) 
                                                   (= x713 y7) 
                                                   (forall ((x731 Int) (x732 A)) 
                                                       (= 
                                                           (MS x731 x732 x711) 
                                                           (MS x731 x732 p4))))))) 
                                   (exists ((s40 PZA)) 
                                       (and 
                                           (exists ((n49 Int)) 
                                               (and 
                                                   (<= 0 n49) 
                                                   (forall ((x733 Int) (x734 A)) 
                                                       (=> 
                                                           (MS x733 x734 s40) 
                                                           (and 
                                                               (<= 1 x733) 
                                                               (<= x733 n49)))) 
                                                   (forall ((x735 Int) (x736 A) (x737 A)) 
                                                       (=> 
                                                           (and 
                                                               (MS x735 x736 s40) 
                                                               (MS x735 x737 s40)) 
                                                           (= x736 x737))) 
                                                   (forall ((x738 Int)) 
                                                       (=> 
                                                           (and 
                                                               (<= 1 x738) 
                                                               (<= x738 n49)) 
                                                           (exists ((x739 A)) 
                                                               (MS x738 x739 s40)))))) 
                                           (forall ((x740 Int) (x741 A)) 
                                               (= 
                                                   (MS x740 x741 x711) 
                                                   (MS x740 x741 s40))) 
                                           (forall ((x742 Int) (x743 A)) 
                                               (= 
                                                   (MS x742 x743 x689) 
                                                   (exists ((i44 Int)) 
                                                       (and 
                                                           (<= 1 i44) 
                                                           (forall ((x744 Int)) 
                                                               (=> 
                                                                   (length s40 x744) 
                                                                   (<= i44 x744))) 
                                                           (= x742 i44) 
                                                           (exists ((x745 Int)) 
                                                               (and 
                                                                   (forall ((x746 Int)) 
                                                                       (=> 
                                                                           (length s40 x746) 
                                                                           (= x745 (+ (- x746 i44) 1)))) 
                                                                   (MS x745 x743 s40)))))))))))))))
         :named hyp25))
(assert (! (forall ((x747 A) (x748 A) (x749 PZA)) 
               (= 
                   (shpath x747 x748 x749) 
                   (exists ((x750 A) (y8 A) (p5 PZA)) 
                       (and 
                           (exists ((n50 Int)) 
                               (and 
                                   (<= 0 n50) 
                                   (forall ((x751 Int) (x752 A)) 
                                       (=> 
                                           (MS x751 x752 p5) 
                                           (and 
                                               (<= 1 x751) 
                                               (<= x751 n50)))) 
                                   (forall ((x753 Int) (x754 A) (x755 A)) 
                                       (=> 
                                           (and 
                                               (MS x753 x754 p5) 
                                               (MS x753 x755 p5)) 
                                           (= x754 x755))) 
                                   (forall ((x756 Int)) 
                                       (=> 
                                           (and 
                                               (<= 1 x756) 
                                               (<= x756 n50)) 
                                           (exists ((x757 A)) 
                                               (MS x756 x757 p5)))))) 
                           (forall ((x758 A)) 
                               (=> 
                                   (exists ((x759 Int)) 
                                       (MS x759 x758 p5)) 
                                   (MS0 x758 a))) 
                           (forall ((x760 Int)) 
                               (=> 
                                   (length p5 x760) 
                                   (< 1 x760))) 
                           (exists ((x761 Int)) 
                               (and 
                                   (= x761 1) 
                                   (MS x761 x750 p5))) 
                           (exists ((x762 Int)) 
                               (and 
                                   (length p5 x762) 
                                   (MS x762 y8 p5))) 
                           (forall ((i45 Int)) 
                               (=> 
                                   (and 
                                       (<= 1 i45) 
                                       (forall ((x763 Int)) 
                                           (=> 
                                               (length p5 x763) 
                                               (<= i45 (- x763 1))))) 
                                   (exists ((x764 A) (x765 A)) 
                                       (and 
                                           (MS i45 x764 p5) 
                                           (exists ((x766 Int)) 
                                               (and 
                                                   (= x766 (+ i45 1)) 
                                                   (MS x766 x765 p5))) 
                                           (r x764 x765))))) 
                           (exists ((x767 Int)) 
                               (and 
                                   (length p5 x767) 
                                   (dist x750 y8 x767))) 
                           (= x747 x750) 
                           (= x748 y8) 
                           (forall ((x768 Int) (x769 A)) 
                               (= 
                                   (MS x768 x769 x749) 
                                   (MS x768 x769 p5)))))))
         :named hyp26))
(assert (! (forall ((x770 A) (y9 A) (p6 PZA) (i46 Int)) 
               (=> 
                   (and 
                       (MS0 x770 a) 
                       (MS0 y9 a) 
                       (exists ((n51 Int)) 
                           (and 
                               (<= 0 n51) 
                               (forall ((x771 Int) (x772 A)) 
                                   (=> 
                                       (MS x771 x772 p6) 
                                       (and 
                                           (<= 1 x771) 
                                           (<= x771 n51)))) 
                               (forall ((x773 Int) (x774 A) (x775 A)) 
                                   (=> 
                                       (and 
                                           (MS x773 x774 p6) 
                                           (MS x773 x775 p6)) 
                                       (= x774 x775))) 
                               (forall ((x776 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x776) 
                                           (<= x776 n51)) 
                                       (exists ((x777 A)) 
                                           (MS x776 x777 p6)))))) 
                       (forall ((x778 A)) 
                           (=> 
                               (exists ((x779 Int)) 
                                   (MS x779 x778 p6)) 
                               (MS0 x778 a))) 
                       (forall ((x780 Int)) 
                           (=> 
                               (length p6 x780) 
                               (< 1 x780))) 
                       (exists ((x781 Int)) 
                           (and 
                               (= x781 1) 
                               (MS x781 x770 p6))) 
                       (exists ((x782 Int)) 
                           (and 
                               (length p6 x782) 
                               (MS x782 y9 p6))) 
                       (forall ((i47 Int)) 
                           (=> 
                               (and 
                                   (<= 1 i47) 
                                   (forall ((x783 Int)) 
                                       (=> 
                                           (length p6 x783) 
                                           (<= i47 (- x783 1))))) 
                               (exists ((x784 A) (x785 A)) 
                                   (and 
                                       (MS i47 x784 p6) 
                                       (exists ((x786 Int)) 
                                           (and 
                                               (= x786 (+ i47 1)) 
                                               (MS x786 x785 p6))) 
                                       (r x784 x785))))) 
                       (<= 2 i46) 
                       (forall ((x787 Int)) 
                           (=> 
                               (length p6 x787) 
                               (<= i46 (- x787 1))))) 
                   (and 
                       (exists ((n52 Int)) 
                           (and 
                               (<= 0 n52) 
                               (forall ((x788 Int) (x789 A)) 
                                   (=> 
                                       (and 
                                           (MS x788 x789 p6) 
                                           (<= 1 x788) 
                                           (<= x788 i46)) 
                                       (and 
                                           (<= 1 x788) 
                                           (<= x788 n52)))) 
                               (forall ((x790 Int) (x791 A) (x792 A)) 
                                   (=> 
                                       (and 
                                           (MS x790 x791 p6) 
                                           (<= 1 x790) 
                                           (<= x790 i46) 
                                           (MS x790 x792 p6)) 
                                       (= x791 x792))) 
                               (forall ((x793 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x793) 
                                           (<= x793 n52)) 
                                       (exists ((x794 A)) 
                                           (and 
                                               (MS x793 x794 p6) 
                                               (<= 1 x793) 
                                               (<= x793 i46))))))) 
                       (forall ((x795 A)) 
                           (=> 
                               (exists ((x796 Int)) 
                                   (and 
                                       (MS x796 x795 p6) 
                                       (<= 1 x796) 
                                       (<= x796 i46))) 
                               (MS0 x795 a))) 
                       (forall ((x797 Int)) 
                           (=> 
                               (exists ((x798 PZA)) 
                                   (and 
                                       (forall ((x799 Int) (x800 A)) 
                                           (= 
                                               (MS x799 x800 x798) 
                                               (and 
                                                   (MS x799 x800 p6) 
                                                   (<= 1 x799) 
                                                   (<= x799 i46)))) 
                                       (length x798 x797))) 
                               (< 1 x797))) 
                       (exists ((x801 Int)) 
                           (and 
                               (= x801 1) 
                               (MS x801 x770 p6))) 
                       (<= 1 1) 
                       (<= 1 i46) 
                       (exists ((x802 Int) (x803 A)) 
                           (and 
                               (exists ((x804 PZA)) 
                                   (and 
                                       (forall ((x805 Int) (x806 A)) 
                                           (= 
                                               (MS x805 x806 x804) 
                                               (and 
                                                   (MS x805 x806 p6) 
                                                   (<= 1 x805) 
                                                   (<= x805 i46)))) 
                                       (length x804 x802))) 
                               (MS i46 x803 p6) 
                               (MS x802 x803 p6))) 
                       (forall ((x807 Int)) 
                           (=> 
                               (exists ((x808 PZA)) 
                                   (and 
                                       (forall ((x809 Int) (x810 A)) 
                                           (= 
                                               (MS x809 x810 x808) 
                                               (and 
                                                   (MS x809 x810 p6) 
                                                   (<= 1 x809) 
                                                   (<= x809 i46)))) 
                                       (length x808 x807))) 
                               (<= 1 x807))) 
                       (forall ((x811 Int)) 
                           (=> 
                               (exists ((x812 PZA)) 
                                   (and 
                                       (forall ((x813 Int) (x814 A)) 
                                           (= 
                                               (MS x813 x814 x812) 
                                               (and 
                                                   (MS x813 x814 p6) 
                                                   (<= 1 x813) 
                                                   (<= x813 i46)))) 
                                       (length x812 x811))) 
                               (<= x811 i46))) 
                       (forall ((i48 Int)) 
                           (=> 
                               (and 
                                   (<= 1 i48) 
                                   (forall ((x815 Int)) 
                                       (=> 
                                           (exists ((x816 PZA)) 
                                               (and 
                                                   (forall ((x817 Int) (x818 A)) 
                                                       (= 
                                                           (MS x817 x818 x816) 
                                                           (and 
                                                               (MS x817 x818 p6) 
                                                               (<= 1 x817) 
                                                               (<= x817 i46)))) 
                                                   (length x816 x815))) 
                                           (<= i48 (- x815 1))))) 
                               (exists ((x819 A) (x820 A)) 
                                   (and 
                                       (MS i48 x819 p6) 
                                       (<= 1 i48) 
                                       (<= i48 i46) 
                                       (exists ((x821 Int)) 
                                           (and 
                                               (= x821 (+ i48 1)) 
                                               (MS x821 x820 p6))) 
                                       (<= 1 (+ i48 1)) 
                                       (<= (+ i48 1) i46) 
                                       (r x819 x820))))))))
         :named hyp27))
(assert (! (forall ((x822 A) (y10 A) (z A)) 
               (=> 
                   (and 
                       (MS0 x822 a) 
                       (MS0 y10 a) 
                       (MS0 z a) 
                       (not 
                           (= z x822)) 
                       (not 
                           (= z y10)) 
                       (forall ((t A)) 
                           (=> 
                               (and 
                                   (MS0 t a) 
                                   (r z t)) 
                               (forall ((x823 Int) (x824 Int)) 
                                   (=> 
                                       (and 
                                           (dist x822 t x824) 
                                           (dist x822 z x823)) 
                                       (<= x824 x823)))))) 
                   (exists ((q PZA)) 
                       (and 
                           (exists ((n53 Int)) 
                               (and 
                                   (<= 0 n53) 
                                   (forall ((x825 Int) (x826 A)) 
                                       (=> 
                                           (MS x825 x826 q) 
                                           (and 
                                               (<= 1 x825) 
                                               (<= x825 n53)))) 
                                   (forall ((x827 Int) (x828 A) (x829 A)) 
                                       (=> 
                                           (and 
                                               (MS x827 x828 q) 
                                               (MS x827 x829 q)) 
                                           (= x828 x829))) 
                                   (forall ((x830 Int)) 
                                       (=> 
                                           (and 
                                               (<= 1 x830) 
                                               (<= x830 n53)) 
                                           (exists ((x831 A)) 
                                               (MS x830 x831 q)))))) 
                           (forall ((x832 A)) 
                               (=> 
                                   (exists ((x833 Int)) 
                                       (MS x833 x832 q)) 
                                   (MS0 x832 a))) 
                           (forall ((x834 Int)) 
                               (=> 
                                   (length q x834) 
                                   (< 1 x834))) 
                           (exists ((x835 Int)) 
                               (and 
                                   (= x835 1) 
                                   (MS x835 x822 q))) 
                           (exists ((x836 Int)) 
                               (and 
                                   (length q x836) 
                                   (MS x836 y10 q))) 
                           (forall ((i49 Int)) 
                               (=> 
                                   (and 
                                       (<= 1 i49) 
                                       (forall ((x837 Int)) 
                                           (=> 
                                               (length q x837) 
                                               (<= i49 (- x837 1))))) 
                                   (exists ((x838 A) (x839 A)) 
                                       (and 
                                           (MS i49 x838 q) 
                                           (exists ((x840 Int)) 
                                               (and 
                                                   (= x840 (+ i49 1)) 
                                                   (MS x840 x839 q))) 
                                           (r x838 x839))))) 
                           (not 
                               (exists ((x841 Int)) 
                                   (MS x841 z q)))))))
         :named hyp28))
(assert (! (forall ((x842 A) (y11 A)) 
               (=> 
                   (and 
                       (MS0 x842 a) 
                       (MS0 y11 a)) 
                   (exists ((p7 PZA)) 
                       (and 
                           (exists ((n54 Int)) 
                               (and 
                                   (<= 0 n54) 
                                   (forall ((x843 Int) (x844 A)) 
                                       (=> 
                                           (MS x843 x844 p7) 
                                           (and 
                                               (<= 1 x843) 
                                               (<= x843 n54)))) 
                                   (forall ((x845 Int) (x846 A) (x847 A)) 
                                       (=> 
                                           (and 
                                               (MS x845 x846 p7) 
                                               (MS x845 x847 p7)) 
                                           (= x846 x847))) 
                                   (forall ((x848 Int)) 
                                       (=> 
                                           (and 
                                               (<= 1 x848) 
                                               (<= x848 n54)) 
                                           (exists ((x849 A)) 
                                               (MS x848 x849 p7)))))) 
                           (forall ((x850 A)) 
                               (=> 
                                   (exists ((x851 Int)) 
                                       (MS x851 x850 p7)) 
                                   (MS0 x850 a))) 
                           (forall ((x852 Int)) 
                               (=> 
                                   (length p7 x852) 
                                   (< 1 x852))) 
                           (exists ((x853 Int)) 
                               (and 
                                   (= x853 1) 
                                   (MS x853 x842 p7))) 
                           (exists ((x854 Int)) 
                               (and 
                                   (length p7 x854) 
                                   (MS x854 y11 p7))) 
                           (forall ((i50 Int)) 
                               (=> 
                                   (and 
                                       (<= 1 i50) 
                                       (forall ((x855 Int)) 
                                           (=> 
                                               (length p7 x855) 
                                               (<= i50 (- x855 1))))) 
                                   (exists ((x856 A) (x857 A)) 
                                       (and 
                                           (MS i50 x856 p7) 
                                           (exists ((x858 Int)) 
                                               (and 
                                                   (= x858 (+ i50 1)) 
                                                   (MS x858 x857 p7))) 
                                           (r x856 x857))))) 
                           (exists ((x859 Int)) 
                               (and 
                                   (length p7 x859) 
                                   (dist x842 y11 x859)))))))
         :named hyp29))
(assert (! (exists ((n55 Int)) 
               (and 
                   (<= 0 n55) 
                   (forall ((x860 Int) (x861 A)) 
                       (=> 
                           (MS x860 x861 p) 
                           (and 
                               (<= 1 x860) 
                               (<= x860 n55)))) 
                   (forall ((x862 Int) (x863 A) (x864 A)) 
                       (=> 
                           (and 
                               (MS x862 x863 p) 
                               (MS x862 x864 p)) 
                           (= x863 x864))) 
                   (forall ((x865 Int)) 
                       (=> 
                           (and 
                               (<= 1 x865) 
                               (<= x865 n55)) 
                           (exists ((x866 A)) 
                               (MS x865 x866 p))))))
         :named hyp30))
(assert (! (forall ((x867 A)) 
               (=> 
                   (exists ((x868 Int)) 
                       (MS x868 x867 p)) 
                   (MS0 x867 a)))
         :named hyp31))
(assert (! (forall ((x869 Int)) 
               (=> 
                   (length p x869) 
                   (< 1 x869)))
         :named hyp32))
(assert (! (exists ((x870 Int)) 
               (and 
                   (= x870 1) 
                   (MS x870 x p)))
         :named hyp33))
(assert (! (exists ((x871 Int)) 
               (and 
                   (length p x871) 
                   (MS x871 y p)))
         :named hyp34))
(assert (! (forall ((i51 Int)) 
               (=> 
                   (and 
                       (<= 1 i51) 
                       (forall ((x872 Int)) 
                           (=> 
                               (length p x872) 
                               (<= i51 (- x872 1))))) 
                   (exists ((x873 A) (x874 A)) 
                       (and 
                           (MS i51 x873 p) 
                           (exists ((x875 Int)) 
                               (and 
                                   (= x875 (+ i51 1)) 
                                   (MS x875 x874 p))) 
                           (r x873 x874)))))
         :named hyp35))
(assert (! (forall ((x876 A) (y12 A) (p8 PZA) (i52 Int)) 
               (=> 
                   (and 
                       (MS0 x876 a) 
                       (MS0 y12 a) 
                       (exists ((n56 Int)) 
                           (and 
                               (<= 0 n56) 
                               (forall ((x877 Int) (x878 A)) 
                                   (=> 
                                       (MS x877 x878 p8) 
                                       (and 
                                           (<= 1 x877) 
                                           (<= x877 n56)))) 
                               (forall ((x879 Int) (x880 A) (x881 A)) 
                                   (=> 
                                       (and 
                                           (MS x879 x880 p8) 
                                           (MS x879 x881 p8)) 
                                       (= x880 x881))) 
                               (forall ((x882 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x882) 
                                           (<= x882 n56)) 
                                       (exists ((x883 A)) 
                                           (MS x882 x883 p8)))))) 
                       (forall ((x884 A)) 
                           (=> 
                               (exists ((x885 Int)) 
                                   (MS x885 x884 p8)) 
                               (MS0 x884 a))) 
                       (forall ((x886 Int)) 
                           (=> 
                               (length p8 x886) 
                               (< 1 x886))) 
                       (exists ((x887 Int)) 
                           (and 
                               (= x887 1) 
                               (MS x887 x876 p8))) 
                       (exists ((x888 Int)) 
                           (and 
                               (length p8 x888) 
                               (MS x888 y12 p8))) 
                       (forall ((i53 Int)) 
                           (=> 
                               (and 
                                   (<= 1 i53) 
                                   (forall ((x889 Int)) 
                                       (=> 
                                           (length p8 x889) 
                                           (<= i53 (- x889 1))))) 
                               (exists ((x890 A) (x891 A)) 
                                   (and 
                                       (MS i53 x890 p8) 
                                       (exists ((x892 Int)) 
                                           (and 
                                               (= x892 (+ i53 1)) 
                                               (MS x892 x891 p8))) 
                                       (r x890 x891))))) 
                       (exists ((x893 Int)) 
                           (and 
                               (length p8 x893) 
                               (dist x876 y12 x893))) 
                       (exists ((x894 A)) 
                           (MS i52 x894 p8)) 
                       (not 
                           (= i52 1)) 
                       (not 
                           (length p8 i52))) 
                   (and 
                       (exists ((n57 Int)) 
                           (and 
                               (<= 0 n57) 
                               (forall ((x895 Int) (x896 A)) 
                                   (=> 
                                       (and 
                                           (MS x895 x896 p8) 
                                           (<= 1 x895) 
                                           (<= x895 i52)) 
                                       (and 
                                           (<= 1 x895) 
                                           (<= x895 n57)))) 
                               (forall ((x897 Int) (x898 A) (x899 A)) 
                                   (=> 
                                       (and 
                                           (MS x897 x898 p8) 
                                           (<= 1 x897) 
                                           (<= x897 i52) 
                                           (MS x897 x899 p8)) 
                                       (= x898 x899))) 
                               (forall ((x900 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x900) 
                                           (<= x900 n57)) 
                                       (exists ((x901 A)) 
                                           (and 
                                               (MS x900 x901 p8) 
                                               (<= 1 x900) 
                                               (<= x900 i52))))))) 
                       (forall ((x902 A)) 
                           (=> 
                               (exists ((x903 Int)) 
                                   (and 
                                       (MS x903 x902 p8) 
                                       (<= 1 x903) 
                                       (<= x903 i52))) 
                               (MS0 x902 a))) 
                       (forall ((x904 Int)) 
                           (=> 
                               (exists ((x905 PZA)) 
                                   (and 
                                       (forall ((x906 Int) (x907 A)) 
                                           (= 
                                               (MS x906 x907 x905) 
                                               (and 
                                                   (MS x906 x907 p8) 
                                                   (<= 1 x906) 
                                                   (<= x906 i52)))) 
                                       (length x905 x904))) 
                               (< 1 x904))) 
                       (exists ((x908 Int)) 
                           (and 
                               (= x908 1) 
                               (MS x908 x876 p8))) 
                       (<= 1 1) 
                       (<= 1 i52) 
                       (exists ((x909 Int) (x910 A)) 
                           (and 
                               (exists ((x911 PZA)) 
                                   (and 
                                       (forall ((x912 Int) (x913 A)) 
                                           (= 
                                               (MS x912 x913 x911) 
                                               (and 
                                                   (MS x912 x913 p8) 
                                                   (<= 1 x912) 
                                                   (<= x912 i52)))) 
                                       (length x911 x909))) 
                               (MS i52 x910 p8) 
                               (MS x909 x910 p8))) 
                       (forall ((x914 Int)) 
                           (=> 
                               (exists ((x915 PZA)) 
                                   (and 
                                       (forall ((x916 Int) (x917 A)) 
                                           (= 
                                               (MS x916 x917 x915) 
                                               (and 
                                                   (MS x916 x917 p8) 
                                                   (<= 1 x916) 
                                                   (<= x916 i52)))) 
                                       (length x915 x914))) 
                               (<= 1 x914))) 
                       (forall ((x918 Int)) 
                           (=> 
                               (exists ((x919 PZA)) 
                                   (and 
                                       (forall ((x920 Int) (x921 A)) 
                                           (= 
                                               (MS x920 x921 x919) 
                                               (and 
                                                   (MS x920 x921 p8) 
                                                   (<= 1 x920) 
                                                   (<= x920 i52)))) 
                                       (length x919 x918))) 
                               (<= x918 i52))) 
                       (forall ((i54 Int)) 
                           (=> 
                               (and 
                                   (<= 1 i54) 
                                   (forall ((x922 Int)) 
                                       (=> 
                                           (exists ((x923 PZA)) 
                                               (and 
                                                   (forall ((x924 Int) (x925 A)) 
                                                       (= 
                                                           (MS x924 x925 x923) 
                                                           (and 
                                                               (MS x924 x925 p8) 
                                                               (<= 1 x924) 
                                                               (<= x924 i52)))) 
                                                   (length x923 x922))) 
                                           (<= i54 (- x922 1))))) 
                               (exists ((x926 A) (x927 A)) 
                                   (and 
                                       (MS i54 x926 p8) 
                                       (<= 1 i54) 
                                       (<= i54 i52) 
                                       (exists ((x928 Int)) 
                                           (and 
                                               (= x928 (+ i54 1)) 
                                               (MS x928 x927 p8))) 
                                       (<= 1 (+ i54 1)) 
                                       (<= (+ i54 1) i52) 
                                       (r x926 x927))))) 
                       (exists ((x929 A) (x930 Int)) 
                           (and 
                               (MS i52 x929 p8) 
                               (exists ((x931 PZA)) 
                                   (and 
                                       (forall ((x932 Int) (x933 A)) 
                                           (= 
                                               (MS x932 x933 x931) 
                                               (and 
                                                   (MS x932 x933 p8) 
                                                   (<= 1 x932) 
                                                   (<= x932 i52)))) 
                                       (length x931 x930))) 
                               (dist x876 x929 x930))))))
         :named hyp36))
(assert (! (forall ((x934 A) (y13 A) (p9 PZA) (i55 Int)) 
               (=> 
                   (and 
                       (MS0 x934 a) 
                       (MS0 y13 a) 
                       (exists ((n58 Int)) 
                           (and 
                               (<= 0 n58) 
                               (forall ((x935 Int) (x936 A)) 
                                   (=> 
                                       (MS x935 x936 p9) 
                                       (and 
                                           (<= 1 x935) 
                                           (<= x935 n58)))) 
                               (forall ((x937 Int) (x938 A) (x939 A)) 
                                   (=> 
                                       (and 
                                           (MS x937 x938 p9) 
                                           (MS x937 x939 p9)) 
                                       (= x938 x939))) 
                               (forall ((x940 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x940) 
                                           (<= x940 n58)) 
                                       (exists ((x941 A)) 
                                           (MS x940 x941 p9)))))) 
                       (forall ((x942 A)) 
                           (=> 
                               (exists ((x943 Int)) 
                                   (MS x943 x942 p9)) 
                               (MS0 x942 a))) 
                       (forall ((x944 Int)) 
                           (=> 
                               (length p9 x944) 
                               (< 1 x944))) 
                       (exists ((x945 Int)) 
                           (and 
                               (= x945 1) 
                               (MS x945 x934 p9))) 
                       (exists ((x946 Int)) 
                           (and 
                               (length p9 x946) 
                               (MS x946 y13 p9))) 
                       (forall ((i56 Int)) 
                           (=> 
                               (and 
                                   (<= 1 i56) 
                                   (forall ((x947 Int)) 
                                       (=> 
                                           (length p9 x947) 
                                           (<= i56 (- x947 1))))) 
                               (exists ((x948 A) (x949 A)) 
                                   (and 
                                       (MS i56 x948 p9) 
                                       (exists ((x950 Int)) 
                                           (and 
                                               (= x950 (+ i56 1)) 
                                               (MS x950 x949 p9))) 
                                       (r x948 x949))))) 
                       (exists ((x951 Int)) 
                           (and 
                               (length p9 x951) 
                               (dist x934 y13 x951))) 
                       (exists ((x952 A)) 
                           (MS i55 x952 p9)) 
                       (not 
                           (= i55 1)) 
                       (not 
                           (length p9 i55))) 
                   (and 
                       (exists ((x953 A)) 
                           (and 
                               (MS i55 x953 p9) 
                               (dist x934 x953 i55))) 
                       (exists ((x954 A) (x955 Int)) 
                           (and 
                               (exists ((x956 Int)) 
                                   (and 
                                       (= x956 (+ i55 1)) 
                                       (MS x956 x954 p9))) 
                               (= x955 (+ i55 1)) 
                               (dist x934 x954 x955))) 
                       (exists ((x957 A) (x958 A)) 
                           (and 
                               (MS i55 x957 p9) 
                               (exists ((x959 Int)) 
                                   (and 
                                       (= x959 (+ i55 1)) 
                                       (MS x959 x958 p9))) 
                               (r x957 x958))))))
         :named hyp37))
(assert (! (forall ((x960 A) (y14 A) (p10 PZA) (z0 A)) 
               (=> 
                   (and 
                       (MS0 x960 a) 
                       (MS0 y14 a) 
                       (exists ((n59 Int)) 
                           (and 
                               (<= 0 n59) 
                               (forall ((x961 Int) (x962 A)) 
                                   (=> 
                                       (MS x961 x962 p10) 
                                       (and 
                                           (<= 1 x961) 
                                           (<= x961 n59)))) 
                               (forall ((x963 Int) (x964 A) (x965 A)) 
                                   (=> 
                                       (and 
                                           (MS x963 x964 p10) 
                                           (MS x963 x965 p10)) 
                                       (= x964 x965))) 
                               (forall ((x966 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x966) 
                                           (<= x966 n59)) 
                                       (exists ((x967 A)) 
                                           (MS x966 x967 p10)))))) 
                       (forall ((x968 A)) 
                           (=> 
                               (exists ((x969 Int)) 
                                   (MS x969 x968 p10)) 
                               (MS0 x968 a))) 
                       (forall ((x970 Int)) 
                           (=> 
                               (length p10 x970) 
                               (< 1 x970))) 
                       (exists ((x971 Int)) 
                           (and 
                               (= x971 1) 
                               (MS x971 x960 p10))) 
                       (exists ((x972 Int)) 
                           (and 
                               (length p10 x972) 
                               (MS x972 y14 p10))) 
                       (forall ((i57 Int)) 
                           (=> 
                               (and 
                                   (<= 1 i57) 
                                   (forall ((x973 Int)) 
                                       (=> 
                                           (length p10 x973) 
                                           (<= i57 (- x973 1))))) 
                               (exists ((x974 A) (x975 A)) 
                                   (and 
                                       (MS i57 x974 p10) 
                                       (exists ((x976 Int)) 
                                           (and 
                                               (= x976 (+ i57 1)) 
                                               (MS x976 x975 p10))) 
                                       (r x974 x975))))) 
                       (exists ((x977 Int)) 
                           (and 
                               (length p10 x977) 
                               (dist x960 y14 x977))) 
                       (exists ((x978 Int)) 
                           (MS x978 z0 p10)) 
                       (not 
                           (= z0 x960)) 
                       (not 
                           (= z0 y14))) 
                   (exists ((t0 A)) 
                       (and 
                           (MS0 t0 a) 
                           (forall ((x979 Int) (x980 Int)) 
                               (=> 
                                   (and 
                                       (dist x960 z0 x980) 
                                       (dist x960 t0 x979)) 
                                   (< x980 x979))) 
                           (r z0 t0)))))
         :named hyp38))
(assert (! (forall ((y15 A) (y20 A) (x981 A) (x1100 A) (p11 PZA) (q0 PZA)) 
               (=> 
                   (and 
                       (MS0 y15 a) 
                       (MS0 y20 a) 
                       (MS0 x981 a) 
                       (MS0 x1100 a) 
                       (exists ((n60 Int)) 
                           (and 
                               (<= 0 n60) 
                               (forall ((x982 Int) (x983 A)) 
                                   (=> 
                                       (MS x982 x983 q0) 
                                       (and 
                                           (<= 1 x982) 
                                           (<= x982 n60)))) 
                               (forall ((x984 Int) (x985 A) (x986 A)) 
                                   (=> 
                                       (and 
                                           (MS x984 x985 q0) 
                                           (MS x984 x986 q0)) 
                                       (= x985 x986))) 
                               (forall ((x987 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x987) 
                                           (<= x987 n60)) 
                                       (exists ((x988 A)) 
                                           (MS x987 x988 q0)))))) 
                       (forall ((x989 A)) 
                           (=> 
                               (exists ((x990 Int)) 
                                   (MS x990 x989 q0)) 
                               (MS0 x989 a))) 
                       (forall ((x991 Int)) 
                           (=> 
                               (length q0 x991) 
                               (< 1 x991))) 
                       (exists ((x992 Int)) 
                           (and 
                               (= x992 1) 
                               (MS x992 x981 q0))) 
                       (exists ((x993 Int)) 
                           (and 
                               (length q0 x993) 
                               (MS x993 y15 q0))) 
                       (forall ((i58 Int)) 
                           (=> 
                               (and 
                                   (<= 1 i58) 
                                   (forall ((x994 Int)) 
                                       (=> 
                                           (length q0 x994) 
                                           (<= i58 (- x994 1))))) 
                               (exists ((x995 A) (x996 A)) 
                                   (and 
                                       (MS i58 x995 q0) 
                                       (exists ((x997 Int)) 
                                           (and 
                                               (= x997 (+ i58 1)) 
                                               (MS x997 x996 q0))) 
                                       (r x995 x996))))) 
                       (exists ((n61 Int)) 
                           (and 
                               (<= 0 n61) 
                               (forall ((x998 Int) (x999 A)) 
                                   (=> 
                                       (MS x998 x999 p11) 
                                       (and 
                                           (<= 1 x998) 
                                           (<= x998 n61)))) 
                               (forall ((x1000 Int) (x1001 A) (x1002 A)) 
                                   (=> 
                                       (and 
                                           (MS x1000 x1001 p11) 
                                           (MS x1000 x1002 p11)) 
                                       (= x1001 x1002))) 
                               (forall ((x1003 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x1003) 
                                           (<= x1003 n61)) 
                                       (exists ((x1004 A)) 
                                           (MS x1003 x1004 p11)))))) 
                       (forall ((x1005 A)) 
                           (=> 
                               (exists ((x1006 Int)) 
                                   (MS x1006 x1005 p11)) 
                               (MS0 x1005 a))) 
                       (forall ((x1007 Int)) 
                           (=> 
                               (length p11 x1007) 
                               (< 1 x1007))) 
                       (exists ((x1008 Int)) 
                           (and 
                               (= x1008 1) 
                               (MS x1008 y20 p11))) 
                       (exists ((x1009 Int)) 
                           (and 
                               (length p11 x1009) 
                               (MS x1009 x1100 p11))) 
                       (forall ((i59 Int)) 
                           (=> 
                               (and 
                                   (<= 1 i59) 
                                   (forall ((x1010 Int)) 
                                       (=> 
                                           (length p11 x1010) 
                                           (<= i59 (- x1010 1))))) 
                               (exists ((x1011 A) (x1012 A)) 
                                   (and 
                                       (MS i59 x1011 p11) 
                                       (exists ((x1013 Int)) 
                                           (and 
                                               (= x1013 (+ i59 1)) 
                                               (MS x1013 x1012 p11))) 
                                       (r x1011 x1012))))) 
                       (r x1100 x981)) 
                   (and 
                       (exists ((n62 Int)) 
                           (and 
                               (<= 0 n62) 
                               (forall ((x1014 Int) (x1015 A)) 
                                   (=> 
                                       (or 
                                           (exists ((i60 Int)) 
                                               (and 
                                                   (<= 1 i60) 
                                                   (forall ((x1016 Int)) 
                                                       (=> 
                                                           (length p11 x1016) 
                                                           (<= i60 x1016))) 
                                                   (= x1014 i60) 
                                                   (MS i60 x1015 p11))) 
                                           (exists ((i61 Int)) 
                                               (and 
                                                   (forall ((x1017 Int)) 
                                                       (=> 
                                                           (length p11 x1017) 
                                                           (<= (+ x1017 1) i61))) 
                                                   (forall ((x1018 Int) (x1019 Int)) 
                                                       (=> 
                                                           (and 
                                                               (length p11 x1019) 
                                                               (length q0 x1018)) 
                                                           (<= i61 (+ x1019 x1018)))) 
                                                   (= x1014 i61) 
                                                   (exists ((x1020 Int)) 
                                                       (and 
                                                           (forall ((x1021 Int)) 
                                                               (=> 
                                                                   (length p11 x1021) 
                                                                   (= x1020 (- i61 x1021)))) 
                                                           (MS x1020 x1015 q0)))))) 
                                       (and 
                                           (<= 1 x1014) 
                                           (<= x1014 n62)))) 
                               (forall ((x1022 Int) (x1023 A) (x1024 A)) 
                                   (=> 
                                       (and 
                                           (or 
                                               (exists ((i62 Int)) 
                                                   (and 
                                                       (<= 1 i62) 
                                                       (forall ((x1025 Int)) 
                                                           (=> 
                                                               (length p11 x1025) 
                                                               (<= i62 x1025))) 
                                                       (= x1022 i62) 
                                                       (MS i62 x1023 p11))) 
                                               (exists ((i63 Int)) 
                                                   (and 
                                                       (forall ((x1026 Int)) 
                                                           (=> 
                                                               (length p11 x1026) 
                                                               (<= (+ x1026 1) i63))) 
                                                       (forall ((x1027 Int) (x1028 Int)) 
                                                           (=> 
                                                               (and 
                                                                   (length p11 x1028) 
                                                                   (length q0 x1027)) 
                                                               (<= i63 (+ x1028 x1027)))) 
                                                       (= x1022 i63) 
                                                       (exists ((x1029 Int)) 
                                                           (and 
                                                               (forall ((x1030 Int)) 
                                                                   (=> 
                                                                       (length p11 x1030) 
                                                                       (= x1029 (- i63 x1030)))) 
                                                               (MS x1029 x1023 q0)))))) 
                                           (or 
                                               (exists ((i64 Int)) 
                                                   (and 
                                                       (<= 1 i64) 
                                                       (forall ((x1031 Int)) 
                                                           (=> 
                                                               (length p11 x1031) 
                                                               (<= i64 x1031))) 
                                                       (= x1022 i64) 
                                                       (MS i64 x1024 p11))) 
                                               (exists ((i65 Int)) 
                                                   (and 
                                                       (forall ((x1032 Int)) 
                                                           (=> 
                                                               (length p11 x1032) 
                                                               (<= (+ x1032 1) i65))) 
                                                       (forall ((x1033 Int) (x1034 Int)) 
                                                           (=> 
                                                               (and 
                                                                   (length p11 x1034) 
                                                                   (length q0 x1033)) 
                                                               (<= i65 (+ x1034 x1033)))) 
                                                       (= x1022 i65) 
                                                       (exists ((x1035 Int)) 
                                                           (and 
                                                               (forall ((x1036 Int)) 
                                                                   (=> 
                                                                       (length p11 x1036) 
                                                                       (= x1035 (- i65 x1036)))) 
                                                               (MS x1035 x1024 q0))))))) 
                                       (= x1023 x1024))) 
                               (forall ((x1037 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x1037) 
                                           (<= x1037 n62)) 
                                       (or 
                                           (exists ((x1038 A)) 
                                               (exists ((i66 Int)) 
                                                   (and 
                                                       (<= 1 i66) 
                                                       (forall ((x1039 Int)) 
                                                           (=> 
                                                               (length p11 x1039) 
                                                               (<= i66 x1039))) 
                                                       (= x1037 i66) 
                                                       (MS i66 x1038 p11)))) 
                                           (exists ((x1040 A)) 
                                               (exists ((i67 Int)) 
                                                   (and 
                                                       (forall ((x1041 Int)) 
                                                           (=> 
                                                               (length p11 x1041) 
                                                               (<= (+ x1041 1) i67))) 
                                                       (forall ((x1042 Int) (x1043 Int)) 
                                                           (=> 
                                                               (and 
                                                                   (length p11 x1043) 
                                                                   (length q0 x1042)) 
                                                               (<= i67 (+ x1043 x1042)))) 
                                                       (= x1037 i67) 
                                                       (exists ((x1044 Int)) 
                                                           (and 
                                                               (forall ((x1045 Int)) 
                                                                   (=> 
                                                                       (length p11 x1045) 
                                                                       (= x1044 (- i67 x1045)))) 
                                                               (MS x1044 x1040 q0))))))))))) 
                       (forall ((x1046 A)) 
                           (=> 
                               (or 
                                   (exists ((x1047 Int)) 
                                       (exists ((i68 Int)) 
                                           (and 
                                               (<= 1 i68) 
                                               (forall ((x1048 Int)) 
                                                   (=> 
                                                       (length p11 x1048) 
                                                       (<= i68 x1048))) 
                                               (= x1047 i68) 
                                               (MS i68 x1046 p11)))) 
                                   (exists ((x1049 Int)) 
                                       (exists ((i69 Int)) 
                                           (and 
                                               (forall ((x1050 Int)) 
                                                   (=> 
                                                       (length p11 x1050) 
                                                       (<= (+ x1050 1) i69))) 
                                               (forall ((x1051 Int) (x1052 Int)) 
                                                   (=> 
                                                       (and 
                                                           (length p11 x1052) 
                                                           (length q0 x1051)) 
                                                       (<= i69 (+ x1052 x1051)))) 
                                               (= x1049 i69) 
                                               (exists ((x1053 Int)) 
                                                   (and 
                                                       (forall ((x1054 Int)) 
                                                           (=> 
                                                               (length p11 x1054) 
                                                               (= x1053 (- i69 x1054)))) 
                                                       (MS x1053 x1046 q0))))))) 
                               (MS0 x1046 a))) 
                       (forall ((x1055 Int)) 
                           (=> 
                               (exists ((x1056 PZA)) 
                                   (and 
                                       (forall ((x1057 Int) (x1058 A)) 
                                           (= 
                                               (MS x1057 x1058 x1056) 
                                               (or 
                                                   (exists ((i70 Int)) 
                                                       (and 
                                                           (<= 1 i70) 
                                                           (forall ((x1059 Int)) 
                                                               (=> 
                                                                   (length p11 x1059) 
                                                                   (<= i70 x1059))) 
                                                           (= x1057 i70) 
                                                           (MS i70 x1058 p11))) 
                                                   (exists ((i71 Int)) 
                                                       (and 
                                                           (forall ((x1060 Int)) 
                                                               (=> 
                                                                   (length p11 x1060) 
                                                                   (<= (+ x1060 1) i71))) 
                                                           (forall ((x1061 Int) (x1062 Int)) 
                                                               (=> 
                                                                   (and 
                                                                       (length p11 x1062) 
                                                                       (length q0 x1061)) 
                                                                   (<= i71 (+ x1062 x1061)))) 
                                                           (= x1057 i71) 
                                                           (exists ((x1063 Int)) 
                                                               (and 
                                                                   (forall ((x1064 Int)) 
                                                                       (=> 
                                                                           (length p11 x1064) 
                                                                           (= x1063 (- i71 x1064)))) 
                                                                   (MS x1063 x1058 q0)))))))) 
                                       (length x1056 x1055))) 
                               (< 1 x1055))) 
                       (or 
                           (exists ((i72 Int)) 
                               (and 
                                   (<= 1 i72) 
                                   (forall ((x1065 Int)) 
                                       (=> 
                                           (length p11 x1065) 
                                           (<= i72 x1065))) 
                                   (= 1 i72) 
                                   (MS i72 y20 p11))) 
                           (exists ((i73 Int)) 
                               (and 
                                   (forall ((x1066 Int)) 
                                       (=> 
                                           (length p11 x1066) 
                                           (<= (+ x1066 1) i73))) 
                                   (forall ((x1067 Int) (x1068 Int)) 
                                       (=> 
                                           (and 
                                               (length p11 x1068) 
                                               (length q0 x1067)) 
                                           (<= i73 (+ x1068 x1067)))) 
                                   (= 1 i73) 
                                   (exists ((x1069 Int)) 
                                       (and 
                                           (forall ((x1070 Int)) 
                                               (=> 
                                                   (length p11 x1070) 
                                                   (= x1069 (- i73 x1070)))) 
                                           (MS x1069 y20 q0)))))) 
                       (or 
                           (exists ((i74 Int)) 
                               (and 
                                   (<= 1 i74) 
                                   (forall ((x1071 Int)) 
                                       (=> 
                                           (length p11 x1071) 
                                           (<= i74 x1071))) 
                                   (exists ((x1072 PZA)) 
                                       (and 
                                           (forall ((x1073 Int) (x1074 A)) 
                                               (= 
                                                   (MS x1073 x1074 x1072) 
                                                   (or 
                                                       (exists ((i75 Int)) 
                                                           (and 
                                                               (<= 1 i75) 
                                                               (forall ((x1075 Int)) 
                                                                   (=> 
                                                                       (length p11 x1075) 
                                                                       (<= i75 x1075))) 
                                                               (= x1073 i75) 
                                                               (MS i75 x1074 p11))) 
                                                       (exists ((i76 Int)) 
                                                           (and 
                                                               (forall ((x1076 Int)) 
                                                                   (=> 
                                                                       (length p11 x1076) 
                                                                       (<= (+ x1076 1) i76))) 
                                                               (forall ((x1077 Int) (x1078 Int)) 
                                                                   (=> 
                                                                       (and 
                                                                           (length p11 x1078) 
                                                                           (length q0 x1077)) 
                                                                       (<= i76 (+ x1078 x1077)))) 
                                                               (= x1073 i76) 
                                                               (exists ((x1079 Int)) 
                                                                   (and 
                                                                       (forall ((x1080 Int)) 
                                                                           (=> 
                                                                               (length p11 x1080) 
                                                                               (= x1079 (- i76 x1080)))) 
                                                                       (MS x1079 x1074 q0)))))))) 
                                           (length x1072 i74))) 
                                   (MS i74 y15 p11))) 
                           (exists ((i77 Int)) 
                               (and 
                                   (forall ((x1081 Int)) 
                                       (=> 
                                           (length p11 x1081) 
                                           (<= (+ x1081 1) i77))) 
                                   (forall ((x1082 Int) (x1083 Int)) 
                                       (=> 
                                           (and 
                                               (length p11 x1083) 
                                               (length q0 x1082)) 
                                           (<= i77 (+ x1083 x1082)))) 
                                   (exists ((x1084 PZA)) 
                                       (and 
                                           (forall ((x1085 Int) (x1086 A)) 
                                               (= 
                                                   (MS x1085 x1086 x1084) 
                                                   (or 
                                                       (exists ((i78 Int)) 
                                                           (and 
                                                               (<= 1 i78) 
                                                               (forall ((x1087 Int)) 
                                                                   (=> 
                                                                       (length p11 x1087) 
                                                                       (<= i78 x1087))) 
                                                               (= x1085 i78) 
                                                               (MS i78 x1086 p11))) 
                                                       (exists ((i79 Int)) 
                                                           (and 
                                                               (forall ((x1088 Int)) 
                                                                   (=> 
                                                                       (length p11 x1088) 
                                                                       (<= (+ x1088 1) i79))) 
                                                               (forall ((x1089 Int) (x1090 Int)) 
                                                                   (=> 
                                                                       (and 
                                                                           (length p11 x1090) 
                                                                           (length q0 x1089)) 
                                                                       (<= i79 (+ x1090 x1089)))) 
                                                               (= x1085 i79) 
                                                               (exists ((x1091 Int)) 
                                                                   (and 
                                                                       (forall ((x1092 Int)) 
                                                                           (=> 
                                                                               (length p11 x1092) 
                                                                               (= x1091 (- i79 x1092)))) 
                                                                       (MS x1091 x1086 q0)))))))) 
                                           (length x1084 i77))) 
                                   (exists ((x1093 Int)) 
                                       (and 
                                           (forall ((x1094 Int)) 
                                               (=> 
                                                   (length p11 x1094) 
                                                   (= x1093 (- i77 x1094)))) 
                                           (MS x1093 y15 q0)))))) 
                       (forall ((i80 Int)) 
                           (=> 
                               (and 
                                   (<= 1 i80) 
                                   (forall ((x1095 Int)) 
                                       (=> 
                                           (exists ((x1096 PZA)) 
                                               (and 
                                                   (forall ((x1097 Int) (x1098 A)) 
                                                       (= 
                                                           (MS x1097 x1098 x1096) 
                                                           (or 
                                                               (exists ((i81 Int)) 
                                                                   (and 
                                                                       (<= 1 i81) 
                                                                       (forall ((x1099 Int)) 
                                                                           (=> 
                                                                               (length p11 x1099) 
                                                                               (<= i81 x1099))) 
                                                                       (= x1097 i81) 
                                                                       (MS i81 x1098 p11))) 
                                                               (exists ((i82 Int)) 
                                                                   (and 
                                                                       (forall ((x1101 Int)) 
                                                                           (=> 
                                                                               (length p11 x1101) 
                                                                               (<= (+ x1101 1) i82))) 
                                                                       (forall ((x1102 Int) (x1103 Int)) 
                                                                           (=> 
                                                                               (and 
                                                                                   (length p11 x1103) 
                                                                                   (length q0 x1102)) 
                                                                               (<= i82 (+ x1103 x1102)))) 
                                                                       (= x1097 i82) 
                                                                       (exists ((x1104 Int)) 
                                                                           (and 
                                                                               (forall ((x1105 Int)) 
                                                                                   (=> 
                                                                                       (length p11 x1105) 
                                                                                       (= x1104 (- i82 x1105)))) 
                                                                               (MS x1104 x1098 q0)))))))) 
                                                   (length x1096 x1095))) 
                                           (<= i80 (- x1095 1))))) 
                               (exists ((x1106 A) (x1107 A)) 
                                   (and 
                                       (or 
                                           (exists ((i83 Int)) 
                                               (and 
                                                   (<= 1 i83) 
                                                   (forall ((x1108 Int)) 
                                                       (=> 
                                                           (length p11 x1108) 
                                                           (<= i83 x1108))) 
                                                   (= i80 i83) 
                                                   (MS i83 x1106 p11))) 
                                           (exists ((i84 Int)) 
                                               (and 
                                                   (forall ((x1109 Int)) 
                                                       (=> 
                                                           (length p11 x1109) 
                                                           (<= (+ x1109 1) i84))) 
                                                   (forall ((x1110 Int) (x1111 Int)) 
                                                       (=> 
                                                           (and 
                                                               (length p11 x1111) 
                                                               (length q0 x1110)) 
                                                           (<= i84 (+ x1111 x1110)))) 
                                                   (= i80 i84) 
                                                   (exists ((x1112 Int)) 
                                                       (and 
                                                           (forall ((x1113 Int)) 
                                                               (=> 
                                                                   (length p11 x1113) 
                                                                   (= x1112 (- i84 x1113)))) 
                                                           (MS x1112 x1106 q0)))))) 
                                       (or 
                                           (exists ((i85 Int)) 
                                               (and 
                                                   (<= 1 i85) 
                                                   (forall ((x1114 Int)) 
                                                       (=> 
                                                           (length p11 x1114) 
                                                           (<= i85 x1114))) 
                                                   (= (+ i80 1) i85) 
                                                   (MS i85 x1107 p11))) 
                                           (exists ((i86 Int)) 
                                               (and 
                                                   (forall ((x1115 Int)) 
                                                       (=> 
                                                           (length p11 x1115) 
                                                           (<= (+ x1115 1) i86))) 
                                                   (forall ((x1116 Int) (x1117 Int)) 
                                                       (=> 
                                                           (and 
                                                               (length p11 x1117) 
                                                               (length q0 x1116)) 
                                                           (<= i86 (+ x1117 x1116)))) 
                                                   (= (+ i80 1) i86) 
                                                   (exists ((x1118 Int)) 
                                                       (and 
                                                           (forall ((x1119 Int)) 
                                                               (=> 
                                                                   (length p11 x1119) 
                                                                   (= x1118 (- i86 x1119)))) 
                                                           (MS x1118 x1107 q0)))))) 
                                       (r x1106 x1107))))))))
         :named hyp39))
(assert (! (forall ((x1120 A) (y16 A) (p12 PZA)) 
               (=> 
                   (and 
                       (exists ((n63 Int)) 
                           (and 
                               (<= 0 n63) 
                               (forall ((x1121 Int) (x1122 A)) 
                                   (=> 
                                       (MS x1121 x1122 p12) 
                                       (and 
                                           (<= 1 x1121) 
                                           (<= x1121 n63)))) 
                               (forall ((x1123 Int) (x1124 A) (x1125 A)) 
                                   (=> 
                                       (and 
                                           (MS x1123 x1124 p12) 
                                           (MS x1123 x1125 p12)) 
                                       (= x1124 x1125))) 
                               (forall ((x1126 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x1126) 
                                           (<= x1126 n63)) 
                                       (exists ((x1127 A)) 
                                           (MS x1126 x1127 p12)))))) 
                       (forall ((x1128 A)) 
                           (=> 
                               (exists ((x1129 Int)) 
                                   (MS x1129 x1128 p12)) 
                               (MS0 x1128 a))) 
                       (forall ((x1130 Int)) 
                           (=> 
                               (length p12 x1130) 
                               (< 1 x1130))) 
                       (exists ((x1131 Int)) 
                           (and 
                               (= x1131 1) 
                               (MS x1131 x1120 p12))) 
                       (exists ((x1132 Int)) 
                           (and 
                               (length p12 x1132) 
                               (MS x1132 y16 p12))) 
                       (forall ((i87 Int)) 
                           (=> 
                               (and 
                                   (<= 1 i87) 
                                   (forall ((x1133 Int)) 
                                       (=> 
                                           (length p12 x1133) 
                                           (<= i87 (- x1133 1))))) 
                               (exists ((x1134 A) (x1135 A)) 
                                   (and 
                                       (MS i87 x1134 p12) 
                                       (exists ((x1136 Int)) 
                                           (and 
                                               (= x1136 (+ i87 1)) 
                                               (MS x1136 x1135 p12))) 
                                       (r x1134 x1135)))))) 
                   (and 
                       (exists ((n64 Int)) 
                           (and 
                               (<= 0 n64) 
                               (forall ((x1137 Int) (x1138 A)) 
                                   (=> 
                                       (exists ((i88 Int)) 
                                           (and 
                                               (<= 1 i88) 
                                               (forall ((x1139 Int)) 
                                                   (=> 
                                                       (length p12 x1139) 
                                                       (<= i88 x1139))) 
                                               (= x1137 i88) 
                                               (exists ((x1140 Int)) 
                                                   (and 
                                                       (forall ((x1141 Int)) 
                                                           (=> 
                                                               (length p12 x1141) 
                                                               (= x1140 (+ (- x1141 i88) 1)))) 
                                                       (MS x1140 x1138 p12))))) 
                                       (and 
                                           (<= 1 x1137) 
                                           (<= x1137 n64)))) 
                               (forall ((x1142 Int) (x1143 A) (x1144 A)) 
                                   (=> 
                                       (and 
                                           (exists ((i89 Int)) 
                                               (and 
                                                   (<= 1 i89) 
                                                   (forall ((x1145 Int)) 
                                                       (=> 
                                                           (length p12 x1145) 
                                                           (<= i89 x1145))) 
                                                   (= x1142 i89) 
                                                   (exists ((x1146 Int)) 
                                                       (and 
                                                           (forall ((x1147 Int)) 
                                                               (=> 
                                                                   (length p12 x1147) 
                                                                   (= x1146 (+ (- x1147 i89) 1)))) 
                                                           (MS x1146 x1143 p12))))) 
                                           (exists ((i90 Int)) 
                                               (and 
                                                   (<= 1 i90) 
                                                   (forall ((x1148 Int)) 
                                                       (=> 
                                                           (length p12 x1148) 
                                                           (<= i90 x1148))) 
                                                   (= x1142 i90) 
                                                   (exists ((x1149 Int)) 
                                                       (and 
                                                           (forall ((x1150 Int)) 
                                                               (=> 
                                                                   (length p12 x1150) 
                                                                   (= x1149 (+ (- x1150 i90) 1)))) 
                                                           (MS x1149 x1144 p12)))))) 
                                       (= x1143 x1144))) 
                               (forall ((x1151 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x1151) 
                                           (<= x1151 n64)) 
                                       (exists ((x1152 A) (i91 Int)) 
                                           (and 
                                               (<= 1 i91) 
                                               (forall ((x1153 Int)) 
                                                   (=> 
                                                       (length p12 x1153) 
                                                       (<= i91 x1153))) 
                                               (= x1151 i91) 
                                               (exists ((x1154 Int)) 
                                                   (and 
                                                       (forall ((x1155 Int)) 
                                                           (=> 
                                                               (length p12 x1155) 
                                                               (= x1154 (+ (- x1155 i91) 1)))) 
                                                       (MS x1154 x1152 p12))))))))) 
                       (forall ((i92 Int)) 
                           (=> 
                               (and 
                                   (<= 1 i92) 
                                   (forall ((x1156 Int)) 
                                       (=> 
                                           (length p12 x1156) 
                                           (<= i92 x1156)))) 
                               (exists ((x1157 A)) 
                                   (and 
                                       (exists ((x1158 Int)) 
                                           (and 
                                               (forall ((x1159 Int)) 
                                                   (=> 
                                                       (length p12 x1159) 
                                                       (= x1158 (+ (- x1159 i92) 1)))) 
                                               (MS x1158 x1157 p12))) 
                                       (MS0 x1157 a))))) 
                       (forall ((x1160 Int)) 
                           (=> 
                               (exists ((x1161 PZA)) 
                                   (and 
                                       (forall ((x1162 Int) (x1163 A)) 
                                           (= 
                                               (MS x1162 x1163 x1161) 
                                               (exists ((i93 Int)) 
                                                   (and 
                                                       (<= 1 i93) 
                                                       (forall ((x1164 Int)) 
                                                           (=> 
                                                               (length p12 x1164) 
                                                               (<= i93 x1164))) 
                                                       (= x1162 i93) 
                                                       (exists ((x1165 Int)) 
                                                           (and 
                                                               (forall ((x1166 Int)) 
                                                                   (=> 
                                                                       (length p12 x1166) 
                                                                       (= x1165 (+ (- x1166 i93) 1)))) 
                                                               (MS x1165 x1163 p12))))))) 
                                       (length x1161 x1160))) 
                               (< 1 x1160))) 
                       (exists ((x1167 Int)) 
                           (and 
                               (forall ((x1168 Int)) 
                                   (=> 
                                       (length p12 x1168) 
                                       (= x1167 (+ (- x1168 1) 1)))) 
                               (MS x1167 y16 p12))) 
                       (exists ((x1169 Int)) 
                           (and 
                               (forall ((x1170 Int) (x1171 Int)) 
                                   (=> 
                                       (and 
                                           (length p12 x1171) 
                                           (exists ((x1172 PZA)) 
                                               (and 
                                                   (forall ((x1173 Int) (x1174 A)) 
                                                       (= 
                                                           (MS x1173 x1174 x1172) 
                                                           (exists ((i94 Int)) 
                                                               (and 
                                                                   (<= 1 i94) 
                                                                   (forall ((x1175 Int)) 
                                                                       (=> 
                                                                           (length p12 x1175) 
                                                                           (<= i94 x1175))) 
                                                                   (= x1173 i94) 
                                                                   (exists ((x1176 Int)) 
                                                                       (and 
                                                                           (forall ((x1177 Int)) 
                                                                               (=> 
                                                                                   (length p12 x1177) 
                                                                                   (= x1176 (+ (- x1177 i94) 1)))) 
                                                                           (MS x1176 x1174 p12))))))) 
                                                   (length x1172 x1170)))) 
                                       (= x1169 (+ (- x1171 x1170) 1)))) 
                               (MS x1169 x1120 p12))) 
                       (forall ((i95 Int)) 
                           (=> 
                               (and 
                                   (<= 1 i95) 
                                   (forall ((x1178 Int)) 
                                       (=> 
                                           (exists ((x1179 PZA)) 
                                               (and 
                                                   (forall ((x1180 Int) (x1181 A)) 
                                                       (= 
                                                           (MS x1180 x1181 x1179) 
                                                           (exists ((i96 Int)) 
                                                               (and 
                                                                   (<= 1 i96) 
                                                                   (forall ((x1182 Int)) 
                                                                       (=> 
                                                                           (length p12 x1182) 
                                                                           (<= i96 x1182))) 
                                                                   (= x1180 i96) 
                                                                   (exists ((x1183 Int)) 
                                                                       (and 
                                                                           (forall ((x1184 Int)) 
                                                                               (=> 
                                                                                   (length p12 x1184) 
                                                                                   (= x1183 (+ (- x1184 i96) 1)))) 
                                                                           (MS x1183 x1181 p12))))))) 
                                                   (length x1179 x1178))) 
                                           (<= i95 (- x1178 1))))) 
                               (exists ((x1185 A) (x1186 A)) 
                                   (and 
                                       (exists ((x1187 Int)) 
                                           (and 
                                               (forall ((x1188 Int)) 
                                                   (=> 
                                                       (length p12 x1188) 
                                                       (= x1187 (+ (- x1188 i95) 1)))) 
                                               (MS x1187 x1185 p12))) 
                                       (exists ((x1189 Int)) 
                                           (and 
                                               (forall ((x1190 Int)) 
                                                   (=> 
                                                       (length p12 x1190) 
                                                       (= x1189 (+ (- x1190 (+ i95 1)) 1)))) 
                                               (MS x1189 x1186 p12))) 
                                       (r x1185 x1186))))))))
         :named hyp40))
(assert (! (forall ((x1191 A) (y21 A) (p13 PZA)) 
               (=> 
                   (and 
                       (MS0 x1191 a) 
                       (MS0 y21 a) 
                       (exists ((n65 Int)) 
                           (and 
                               (<= 0 n65) 
                               (forall ((x1192 Int) (x1193 A)) 
                                   (=> 
                                       (MS x1192 x1193 p13) 
                                       (and 
                                           (<= 1 x1192) 
                                           (<= x1192 n65)))) 
                               (forall ((x1194 Int) (x1195 A) (x1196 A)) 
                                   (=> 
                                       (and 
                                           (MS x1194 x1195 p13) 
                                           (MS x1194 x1196 p13)) 
                                       (= x1195 x1196))) 
                               (forall ((x1197 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x1197) 
                                           (<= x1197 n65)) 
                                       (exists ((x1198 A)) 
                                           (MS x1197 x1198 p13)))))) 
                       (forall ((x1199 A)) 
                           (=> 
                               (exists ((x1200 Int)) 
                                   (MS x1200 x1199 p13)) 
                               (MS0 x1199 a))) 
                       (forall ((x1201 Int)) 
                           (=> 
                               (length p13 x1201) 
                               (< 1 x1201))) 
                       (exists ((x1202 Int)) 
                           (and 
                               (= x1202 1) 
                               (MS x1202 x1191 p13))) 
                       (exists ((x1203 Int)) 
                           (and 
                               (length p13 x1203) 
                               (MS x1203 y21 p13))) 
                       (forall ((i97 Int)) 
                           (=> 
                               (and 
                                   (<= 1 i97) 
                                   (forall ((x1204 Int)) 
                                       (=> 
                                           (length p13 x1204) 
                                           (<= i97 (- x1204 1))))) 
                               (exists ((x1205 A) (x1206 A)) 
                                   (and 
                                       (MS i97 x1205 p13) 
                                       (exists ((x1207 Int)) 
                                           (and 
                                               (= x1207 (+ i97 1)) 
                                               (MS x1207 x1206 p13))) 
                                       (r x1205 x1206))))) 
                       (forall ((x1208 Int)) 
                           (=> 
                               (length p13 x1208) 
                               (<= 3 x1208)))) 
                   (and 
                       (exists ((n66 Int)) 
                           (and 
                               (<= 0 n66) 
                               (forall ((x1209 Int) (x1210 A)) 
                                   (=> 
                                       (and 
                                           (exists ((i98 Int)) 
                                               (and 
                                                   (<= 1 i98) 
                                                   (forall ((x1211 Int)) 
                                                       (=> 
                                                           (length p13 x1211) 
                                                           (<= i98 x1211))) 
                                                   (= x1209 i98) 
                                                   (exists ((x1212 Int)) 
                                                       (and 
                                                           (forall ((x1213 Int)) 
                                                               (=> 
                                                                   (length p13 x1213) 
                                                                   (= x1212 (+ (- x1213 i98) 1)))) 
                                                           (MS x1212 x1210 p13))))) 
                                           (<= 1 x1209) 
                                           (forall ((x1214 Int)) 
                                               (=> 
                                                   (length p13 x1214) 
                                                   (<= x1209 (- x1214 1))))) 
                                       (and 
                                           (<= 1 x1209) 
                                           (<= x1209 n66)))) 
                               (forall ((x1215 Int) (x1216 A) (x1217 A)) 
                                   (=> 
                                       (and 
                                           (exists ((i99 Int)) 
                                               (and 
                                                   (<= 1 i99) 
                                                   (forall ((x1218 Int)) 
                                                       (=> 
                                                           (length p13 x1218) 
                                                           (<= i99 x1218))) 
                                                   (= x1215 i99) 
                                                   (exists ((x1219 Int)) 
                                                       (and 
                                                           (forall ((x1220 Int)) 
                                                               (=> 
                                                                   (length p13 x1220) 
                                                                   (= x1219 (+ (- x1220 i99) 1)))) 
                                                           (MS x1219 x1216 p13))))) 
                                           (<= 1 x1215) 
                                           (forall ((x1221 Int)) 
                                               (=> 
                                                   (length p13 x1221) 
                                                   (<= x1215 (- x1221 1)))) 
                                           (exists ((i100 Int)) 
                                               (and 
                                                   (<= 1 i100) 
                                                   (forall ((x1222 Int)) 
                                                       (=> 
                                                           (length p13 x1222) 
                                                           (<= i100 x1222))) 
                                                   (= x1215 i100) 
                                                   (exists ((x1223 Int)) 
                                                       (and 
                                                           (forall ((x1224 Int)) 
                                                               (=> 
                                                                   (length p13 x1224) 
                                                                   (= x1223 (+ (- x1224 i100) 1)))) 
                                                           (MS x1223 x1217 p13)))))) 
                                       (= x1216 x1217))) 
                               (forall ((x1225 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x1225) 
                                           (<= x1225 n66)) 
                                       (exists ((x1226 A)) 
                                           (and 
                                               (exists ((i101 Int)) 
                                                   (and 
                                                       (<= 1 i101) 
                                                       (forall ((x1227 Int)) 
                                                           (=> 
                                                               (length p13 x1227) 
                                                               (<= i101 x1227))) 
                                                       (= x1225 i101) 
                                                       (exists ((x1228 Int)) 
                                                           (and 
                                                               (forall ((x1229 Int)) 
                                                                   (=> 
                                                                       (length p13 x1229) 
                                                                       (= x1228 (+ (- x1229 i101) 1)))) 
                                                               (MS x1228 x1226 p13))))) 
                                               (<= 1 x1225) 
                                               (forall ((x1230 Int)) 
                                                   (=> 
                                                       (length p13 x1230) 
                                                       (<= x1225 (- x1230 1)))))))))) 
                       (forall ((x1231 A)) 
                           (=> 
                               (exists ((x1232 Int)) 
                                   (and 
                                       (exists ((i102 Int)) 
                                           (and 
                                               (<= 1 i102) 
                                               (forall ((x1233 Int)) 
                                                   (=> 
                                                       (length p13 x1233) 
                                                       (<= i102 x1233))) 
                                               (= x1232 i102) 
                                               (exists ((x1234 Int)) 
                                                   (and 
                                                       (forall ((x1235 Int)) 
                                                           (=> 
                                                               (length p13 x1235) 
                                                               (= x1234 (+ (- x1235 i102) 1)))) 
                                                       (MS x1234 x1231 p13))))) 
                                       (<= 1 x1232) 
                                       (forall ((x1236 Int)) 
                                           (=> 
                                               (length p13 x1236) 
                                               (<= x1232 (- x1236 1)))))) 
                               (MS0 x1231 a))) 
                       (forall ((x1237 Int)) 
                           (=> 
                               (exists ((x1238 PZA)) 
                                   (and 
                                       (forall ((x1239 Int) (x1240 A)) 
                                           (= 
                                               (MS x1239 x1240 x1238) 
                                               (and 
                                                   (exists ((i103 Int)) 
                                                       (and 
                                                           (<= 1 i103) 
                                                           (forall ((x1241 Int)) 
                                                               (=> 
                                                                   (length p13 x1241) 
                                                                   (<= i103 x1241))) 
                                                           (= x1239 i103) 
                                                           (exists ((x1242 Int)) 
                                                               (and 
                                                                   (forall ((x1243 Int)) 
                                                                       (=> 
                                                                           (length p13 x1243) 
                                                                           (= x1242 (+ (- x1243 i103) 1)))) 
                                                                   (MS x1242 x1240 p13))))) 
                                                   (<= 1 x1239) 
                                                   (forall ((x1244 Int)) 
                                                       (=> 
                                                           (length p13 x1244) 
                                                           (<= x1239 (- x1244 1))))))) 
                                       (length x1238 x1237))) 
                               (< 1 x1237))) 
                       (exists ((i104 Int)) 
                           (and 
                               (<= 1 i104) 
                               (forall ((x1245 Int)) 
                                   (=> 
                                       (length p13 x1245) 
                                       (<= i104 x1245))) 
                               (= 1 i104) 
                               (exists ((x1246 Int)) 
                                   (and 
                                       (forall ((x1247 Int)) 
                                           (=> 
                                               (length p13 x1247) 
                                               (= x1246 (+ (- x1247 i104) 1)))) 
                                       (MS x1246 y21 p13))))) 
                       (<= 1 1) 
                       (forall ((x1248 Int)) 
                           (=> 
                               (length p13 x1248) 
                               (<= 1 (- x1248 1)))) 
                       (exists ((i105 Int)) 
                           (and 
                               (<= 1 i105) 
                               (forall ((x1249 Int)) 
                                   (=> 
                                       (length p13 x1249) 
                                       (<= i105 x1249))) 
                               (exists ((x1250 PZA)) 
                                   (and 
                                       (forall ((x1251 Int) (x1252 A)) 
                                           (= 
                                               (MS x1251 x1252 x1250) 
                                               (and 
                                                   (exists ((i106 Int)) 
                                                       (and 
                                                           (<= 1 i106) 
                                                           (forall ((x1253 Int)) 
                                                               (=> 
                                                                   (length p13 x1253) 
                                                                   (<= i106 x1253))) 
                                                           (= x1251 i106) 
                                                           (exists ((x1254 Int)) 
                                                               (and 
                                                                   (forall ((x1255 Int)) 
                                                                       (=> 
                                                                           (length p13 x1255) 
                                                                           (= x1254 (+ (- x1255 i106) 1)))) 
                                                                   (MS x1254 x1252 p13))))) 
                                                   (<= 1 x1251) 
                                                   (forall ((x1256 Int)) 
                                                       (=> 
                                                           (length p13 x1256) 
                                                           (<= x1251 (- x1256 1))))))) 
                                       (length x1250 i105))) 
                               (exists ((x1257 Int) (x1258 A)) 
                                   (and 
                                       (forall ((x1259 Int) (x1260 Int)) 
                                           (=> 
                                               (and 
                                                   (length p13 x1260) 
                                                   (length p13 x1259)) 
                                               (= x1257 (+ (- x1260 (- x1259 1)) 1)))) 
                                       (exists ((x1261 Int)) 
                                           (and 
                                               (forall ((x1262 Int)) 
                                                   (=> 
                                                       (length p13 x1262) 
                                                       (= x1261 (+ (- x1262 i105) 1)))) 
                                               (MS x1261 x1258 p13))) 
                                       (MS x1257 x1258 p13))))) 
                       (forall ((x1263 Int)) 
                           (=> 
                               (exists ((x1264 PZA)) 
                                   (and 
                                       (forall ((x1265 Int) (x1266 A)) 
                                           (= 
                                               (MS x1265 x1266 x1264) 
                                               (and 
                                                   (exists ((i107 Int)) 
                                                       (and 
                                                           (<= 1 i107) 
                                                           (forall ((x1267 Int)) 
                                                               (=> 
                                                                   (length p13 x1267) 
                                                                   (<= i107 x1267))) 
                                                           (= x1265 i107) 
                                                           (exists ((x1268 Int)) 
                                                               (and 
                                                                   (forall ((x1269 Int)) 
                                                                       (=> 
                                                                           (length p13 x1269) 
                                                                           (= x1268 (+ (- x1269 i107) 1)))) 
                                                                   (MS x1268 x1266 p13))))) 
                                                   (<= 1 x1265) 
                                                   (forall ((x1270 Int)) 
                                                       (=> 
                                                           (length p13 x1270) 
                                                           (<= x1265 (- x1270 1))))))) 
                                       (length x1264 x1263))) 
                               (<= 1 x1263))) 
                       (forall ((x1271 Int) (x1272 Int)) 
                           (=> 
                               (and 
                                   (exists ((x1273 PZA)) 
                                       (and 
                                           (forall ((x1274 Int) (x1275 A)) 
                                               (= 
                                                   (MS x1274 x1275 x1273) 
                                                   (and 
                                                       (exists ((i108 Int)) 
                                                           (and 
                                                               (<= 1 i108) 
                                                               (forall ((x1276 Int)) 
                                                                   (=> 
                                                                       (length p13 x1276) 
                                                                       (<= i108 x1276))) 
                                                               (= x1274 i108) 
                                                               (exists ((x1277 Int)) 
                                                                   (and 
                                                                       (forall ((x1278 Int)) 
                                                                           (=> 
                                                                               (length p13 x1278) 
                                                                               (= x1277 (+ (- x1278 i108) 1)))) 
                                                                       (MS x1277 x1275 p13))))) 
                                                       (<= 1 x1274) 
                                                       (forall ((x1279 Int)) 
                                                           (=> 
                                                               (length p13 x1279) 
                                                               (<= x1274 (- x1279 1))))))) 
                                           (length x1273 x1272))) 
                                   (length p13 x1271)) 
                               (<= x1272 (- x1271 1)))) 
                       (forall ((i109 Int)) 
                           (=> 
                               (and 
                                   (<= 1 i109) 
                                   (forall ((x1280 Int)) 
                                       (=> 
                                           (exists ((x1281 PZA)) 
                                               (and 
                                                   (forall ((x1282 Int) (x1283 A)) 
                                                       (= 
                                                           (MS x1282 x1283 x1281) 
                                                           (and 
                                                               (exists ((i110 Int)) 
                                                                   (and 
                                                                       (<= 1 i110) 
                                                                       (forall ((x1284 Int)) 
                                                                           (=> 
                                                                               (length p13 x1284) 
                                                                               (<= i110 x1284))) 
                                                                       (= x1282 i110) 
                                                                       (exists ((x1285 Int)) 
                                                                           (and 
                                                                               (forall ((x1286 Int)) 
                                                                                   (=> 
                                                                                       (length p13 x1286) 
                                                                                       (= x1285 (+ (- x1286 i110) 1)))) 
                                                                               (MS x1285 x1283 p13))))) 
                                                               (<= 1 x1282) 
                                                               (forall ((x1287 Int)) 
                                                                   (=> 
                                                                       (length p13 x1287) 
                                                                       (<= x1282 (- x1287 1))))))) 
                                                   (length x1281 x1280))) 
                                           (<= i109 (- x1280 1))))) 
                               (exists ((x1288 A) (x1289 A)) 
                                   (and 
                                       (exists ((i111 Int)) 
                                           (and 
                                               (<= 1 i111) 
                                               (forall ((x1290 Int)) 
                                                   (=> 
                                                       (length p13 x1290) 
                                                       (<= i111 x1290))) 
                                               (= i109 i111) 
                                               (exists ((x1291 Int)) 
                                                   (and 
                                                       (forall ((x1292 Int)) 
                                                           (=> 
                                                               (length p13 x1292) 
                                                               (= x1291 (+ (- x1292 i111) 1)))) 
                                                       (MS x1291 x1288 p13))))) 
                                       (<= 1 i109) 
                                       (forall ((x1293 Int)) 
                                           (=> 
                                               (length p13 x1293) 
                                               (<= i109 (- x1293 1)))) 
                                       (exists ((i112 Int)) 
                                           (and 
                                               (<= 1 i112) 
                                               (forall ((x1294 Int)) 
                                                   (=> 
                                                       (length p13 x1294) 
                                                       (<= i112 x1294))) 
                                               (= (+ i109 1) i112) 
                                               (exists ((x1295 Int)) 
                                                   (and 
                                                       (forall ((x1296 Int)) 
                                                           (=> 
                                                               (length p13 x1296) 
                                                               (= x1295 (+ (- x1296 i112) 1)))) 
                                                       (MS x1295 x1289 p13))))) 
                                       (<= 1 (+ i109 1)) 
                                       (forall ((x1297 Int)) 
                                           (=> 
                                               (length p13 x1297) 
                                               (<= (+ i109 1) (- x1297 1)))) 
                                       (r x1288 x1289))))))))
         :named hyp41))
(assert (! (exists ((x1298 A) (x1299 A) (x1300 Int)) 
               (and 
                   (exists ((x1301 Int)) 
                       (and 
                           (= x1301 1) 
                           (MS x1301 x1298 p))) 
                   (exists ((x1302 Int)) 
                       (and 
                           (length p x1302) 
                           (MS x1302 x1299 p))) 
                   (length p x1300) 
                   (dist x1298 x1299 x1300)))
         :named hyp42))
(assert (! (not 
               (exists ((x1303 Int) (x1304 A)) 
                   (and 
                       (forall ((x1305 Int)) 
                           (=> 
                               (length p x1305) 
                               (= x1303 (+ (- x1305 1) 1)))) 
                       (exists ((x1306 Int)) 
                           (and 
                               (length p x1306) 
                               (MS x1306 x1304 p))) 
                       (MS x1303 x1304 p))))
         :named goal))
(check-sat)
(exit)

