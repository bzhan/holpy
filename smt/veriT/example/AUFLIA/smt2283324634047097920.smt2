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
(declare-fun seq (PZA) Bool)
(declare-fun a () PA)
(declare-fun x () A)
(declare-fun y () A)

; Elementary Sets axiom (Singleton part)
(assert (forall ((x500 A)) 
            (exists ((X PA)) 
                (and 
                    (MS0 x500 X) 
                    (forall ((y2 A)) 
                        (=> 
                            (MS0 y2 X) 
                            (= y2 x500)))))))
; Elementary Sets axiom (Singleton part)
(assert (forall ((x501 Int) (x502 A)) 
            (exists ((X0 PZA)) 
                (and 
                    (MS x501 x502 X0) 
                    (forall ((y3 Int) (y4 A)) 
                        (=> 
                            (MS y3 y4 X0) 
                            (and 
                                (= y3 x501) 
                                (= y4 x502))))))))
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
(assert (! (MS0 x a)
         :named hyp5))
(assert (! (MS0 y a)
         :named hyp6))
(assert (! (and 
               (forall ((x29 PZA) (x30 Int)) 
                   (=> 
                       (length x29 x30) 
                       (and 
                           (exists ((s1 PZA)) 
                               (and 
                                   (exists ((n1 Int)) 
                                       (and 
                                           (<= 0 n1) 
                                           (forall ((x31 Int) (x32 A)) 
                                               (=> 
                                                   (MS x31 x32 s1) 
                                                   (and 
                                                       (<= 1 x31) 
                                                       (<= x31 n1)))) 
                                           (forall ((x33 Int) (x34 A) (x35 A)) 
                                               (=> 
                                                   (and 
                                                       (MS x33 x34 s1) 
                                                       (MS x33 x35 s1)) 
                                                   (= x34 x35))) 
                                           (forall ((x36 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x36) 
                                                       (<= x36 n1)) 
                                                   (exists ((x37 A)) 
                                                       (MS x36 x37 s1)))))) 
                                   (forall ((x38 Int) (x39 A)) 
                                       (= 
                                           (MS x38 x39 x29) 
                                           (MS x38 x39 s1))))) 
                           (<= 0 x30)))) 
               (forall ((x40 PZA) (x41 Int) (x42 Int)) 
                   (=> 
                       (and 
                           (length x40 x41) 
                           (length x40 x42)) 
                       (= x41 x42))) 
               (forall ((x43 PZA)) 
                   (=> 
                       (exists ((s2 PZA)) 
                           (and 
                               (exists ((n2 Int)) 
                                   (and 
                                       (<= 0 n2) 
                                       (forall ((x44 Int) (x45 A)) 
                                           (=> 
                                               (MS x44 x45 s2) 
                                               (and 
                                                   (<= 1 x44) 
                                                   (<= x44 n2)))) 
                                       (forall ((x46 Int) (x47 A) (x48 A)) 
                                           (=> 
                                               (and 
                                                   (MS x46 x47 s2) 
                                                   (MS x46 x48 s2)) 
                                               (= x47 x48))) 
                                       (forall ((x49 Int)) 
                                           (=> 
                                               (and 
                                                   (<= 1 x49) 
                                                   (<= x49 n2)) 
                                               (exists ((x50 A)) 
                                                   (MS x49 x50 s2)))))) 
                               (forall ((x51 Int) (x52 A)) 
                                   (= 
                                       (MS x51 x52 x43) 
                                       (MS x51 x52 s2))))) 
                       (exists ((x53 Int)) 
                           (length x43 x53)))))
         :named hyp7))
(assert (! (forall ((n3 Int) (s3 PZA)) 
               (=> 
                   (and 
                       (<= 0 n3) 
                       (forall ((x54 Int) (x55 A)) 
                           (=> 
                               (MS x54 x55 s3) 
                               (and 
                                   (<= 1 x54) 
                                   (<= x54 n3)))) 
                       (forall ((x56 Int) (x57 A) (x58 A)) 
                           (=> 
                               (and 
                                   (MS x56 x57 s3) 
                                   (MS x56 x58 s3)) 
                               (= x57 x58))) 
                       (forall ((x59 Int)) 
                           (=> 
                               (and 
                                   (<= 1 x59) 
                                   (<= x59 n3)) 
                               (exists ((x60 A)) 
                                   (MS x59 x60 s3))))) 
                   (exists ((n4 Int)) 
                       (and 
                           (<= 0 n4) 
                           (forall ((x61 Int) (x62 A)) 
                               (=> 
                                   (MS x61 x62 s3) 
                                   (and 
                                       (<= 1 x61) 
                                       (<= x61 n4)))) 
                           (forall ((x63 Int) (x64 A) (x65 A)) 
                               (=> 
                                   (and 
                                       (MS x63 x64 s3) 
                                       (MS x63 x65 s3)) 
                                   (= x64 x65))) 
                           (forall ((x66 Int)) 
                               (=> 
                                   (and 
                                       (<= 1 x66) 
                                       (<= x66 n4)) 
                                   (exists ((x67 A)) 
                                       (MS x66 x67 s3))))))))
         :named hyp8))
(assert (! (forall ((s4 PZA)) 
               (=> 
                   (exists ((n5 Int)) 
                       (and 
                           (<= 0 n5) 
                           (forall ((x68 Int) (x69 A)) 
                               (=> 
                                   (MS x68 x69 s4) 
                                   (and 
                                       (<= 1 x68) 
                                       (<= x68 n5)))) 
                           (forall ((x70 Int) (x71 A) (x72 A)) 
                               (=> 
                                   (and 
                                       (MS x70 x71 s4) 
                                       (MS x70 x72 s4)) 
                                   (= x71 x72))) 
                           (forall ((x73 Int)) 
                               (=> 
                                   (and 
                                       (<= 1 x73) 
                                       (<= x73 n5)) 
                                   (exists ((x74 A)) 
                                       (MS x73 x74 s4)))))) 
                   (and 
                       (forall ((x75 Int) (x76 A)) 
                           (=> 
                               (MS x75 x76 s4) 
                               (and 
                                   (<= 1 x75) 
                                   (forall ((x77 Int)) 
                                       (=> 
                                           (length s4 x77) 
                                           (<= x75 x77)))))) 
                       (forall ((x78 Int) (x79 A) (x80 A)) 
                           (=> 
                               (and 
                                   (MS x78 x79 s4) 
                                   (MS x78 x80 s4)) 
                               (= x79 x80))) 
                       (forall ((x81 Int)) 
                           (=> 
                               (and 
                                   (<= 1 x81) 
                                   (forall ((x82 Int)) 
                                       (=> 
                                           (length s4 x82) 
                                           (<= x81 x82)))) 
                               (exists ((x83 A)) 
                                   (MS x81 x83 s4)))))))
         :named hyp9))
(assert (! (forall ((x84 PZA) (x85 PZA) (x86 PZA)) 
               (= 
                   (cnc x84 x85 x86) 
                   (exists ((s10 PZA) (s20 PZA)) 
                       (and 
                           (exists ((n6 Int)) 
                               (and 
                                   (<= 0 n6) 
                                   (forall ((x87 Int) (x88 A)) 
                                       (=> 
                                           (MS x87 x88 s10) 
                                           (and 
                                               (<= 1 x87) 
                                               (<= x87 n6)))) 
                                   (forall ((x89 Int) (x90 A) (x91 A)) 
                                       (=> 
                                           (and 
                                               (MS x89 x90 s10) 
                                               (MS x89 x91 s10)) 
                                           (= x90 x91))) 
                                   (forall ((x92 Int)) 
                                       (=> 
                                           (and 
                                               (<= 1 x92) 
                                               (<= x92 n6)) 
                                           (exists ((x93 A)) 
                                               (MS x92 x93 s10)))))) 
                           (exists ((n7 Int)) 
                               (and 
                                   (<= 0 n7) 
                                   (forall ((x94 Int) (x95 A)) 
                                       (=> 
                                           (MS x94 x95 s20) 
                                           (and 
                                               (<= 1 x94) 
                                               (<= x94 n7)))) 
                                   (forall ((x96 Int) (x97 A) (x98 A)) 
                                       (=> 
                                           (and 
                                               (MS x96 x97 s20) 
                                               (MS x96 x98 s20)) 
                                           (= x97 x98))) 
                                   (forall ((x99 Int)) 
                                       (=> 
                                           (and 
                                               (<= 1 x99) 
                                               (<= x99 n7)) 
                                           (exists ((x100 A)) 
                                               (MS x99 x100 s20)))))) 
                           (forall ((x101 Int) (x102 A)) 
                               (= 
                                   (MS x101 x102 x84) 
                                   (MS x101 x102 s10))) 
                           (forall ((x103 Int) (x104 A)) 
                               (= 
                                   (MS x103 x104 x85) 
                                   (MS x103 x104 s20))) 
                           (forall ((x105 Int) (x106 A)) 
                               (= 
                                   (MS x105 x106 x86) 
                                   (or 
                                       (exists ((i Int)) 
                                           (and 
                                               (<= 1 i) 
                                               (forall ((x107 Int)) 
                                                   (=> 
                                                       (length s10 x107) 
                                                       (<= i x107))) 
                                               (= x105 i) 
                                               (MS i x106 s10))) 
                                       (exists ((i0 Int)) 
                                           (and 
                                               (forall ((x108 Int)) 
                                                   (=> 
                                                       (length s10 x108) 
                                                       (<= (+ x108 1) i0))) 
                                               (forall ((x109 Int) (x110 Int)) 
                                                   (=> 
                                                       (and 
                                                           (length s10 x110) 
                                                           (length s20 x109)) 
                                                       (<= i0 (+ x110 x109)))) 
                                               (= x105 i0) 
                                               (exists ((x111 Int)) 
                                                   (and 
                                                       (forall ((x112 Int)) 
                                                           (=> 
                                                               (length s10 x112) 
                                                               (= x111 (- i0 x112)))) 
                                                       (MS x111 x106 s20))))))))))))
         :named hyp10))
(assert (! (forall ((x113 A) (x114 A) (x115 PZA)) 
               (= 
                   (path x113 x114 x115) 
                   (exists ((x116 A) (y0 A) (p PZA)) 
                       (and 
                           (exists ((n8 Int)) 
                               (and 
                                   (<= 0 n8) 
                                   (forall ((x117 Int) (x118 A)) 
                                       (=> 
                                           (MS x117 x118 p) 
                                           (and 
                                               (<= 1 x117) 
                                               (<= x117 n8)))) 
                                   (forall ((x119 Int) (x120 A) (x121 A)) 
                                       (=> 
                                           (and 
                                               (MS x119 x120 p) 
                                               (MS x119 x121 p)) 
                                           (= x120 x121))) 
                                   (forall ((x122 Int)) 
                                       (=> 
                                           (and 
                                               (<= 1 x122) 
                                               (<= x122 n8)) 
                                           (exists ((x123 A)) 
                                               (MS x122 x123 p)))))) 
                           (forall ((x124 A)) 
                               (=> 
                                   (exists ((x125 Int)) 
                                       (MS x125 x124 p)) 
                                   (MS0 x124 a))) 
                           (forall ((x126 Int)) 
                               (=> 
                                   (length p x126) 
                                   (< 1 x126))) 
                           (exists ((x127 Int)) 
                               (and 
                                   (= x127 1) 
                                   (MS x127 x116 p))) 
                           (exists ((x128 Int)) 
                               (and 
                                   (length p x128) 
                                   (MS x128 y0 p))) 
                           (forall ((i1 Int)) 
                               (=> 
                                   (and 
                                       (<= 1 i1) 
                                       (forall ((x129 Int)) 
                                           (=> 
                                               (length p x129) 
                                               (<= i1 (- x129 1))))) 
                                   (exists ((x130 A) (x131 A)) 
                                       (and 
                                           (MS i1 x130 p) 
                                           (exists ((x132 Int)) 
                                               (and 
                                                   (= x132 (+ i1 1)) 
                                                   (MS x132 x131 p))) 
                                           (r x130 x131))))) 
                           (= x113 x116) 
                           (= x114 y0) 
                           (forall ((x133 Int) (x134 A)) 
                               (= 
                                   (MS x133 x134 x115) 
                                   (MS x133 x134 p)))))))
         :named hyp11))
(assert (! (and 
               (forall ((x135 PZA) (x136 PZA) (x137 PZA)) 
                   (=> 
                       (exists ((s11 PZA) (s21 PZA)) 
                           (and 
                               (exists ((n9 Int)) 
                                   (and 
                                       (<= 0 n9) 
                                       (forall ((x138 Int) (x139 A)) 
                                           (=> 
                                               (MS x138 x139 s11) 
                                               (and 
                                                   (<= 1 x138) 
                                                   (<= x138 n9)))) 
                                       (forall ((x140 Int) (x141 A) (x142 A)) 
                                           (=> 
                                               (and 
                                                   (MS x140 x141 s11) 
                                                   (MS x140 x142 s11)) 
                                               (= x141 x142))) 
                                       (forall ((x143 Int)) 
                                           (=> 
                                               (and 
                                                   (<= 1 x143) 
                                                   (<= x143 n9)) 
                                               (exists ((x144 A)) 
                                                   (MS x143 x144 s11)))))) 
                               (exists ((n10 Int)) 
                                   (and 
                                       (<= 0 n10) 
                                       (forall ((x145 Int) (x146 A)) 
                                           (=> 
                                               (MS x145 x146 s21) 
                                               (and 
                                                   (<= 1 x145) 
                                                   (<= x145 n10)))) 
                                       (forall ((x147 Int) (x148 A) (x149 A)) 
                                           (=> 
                                               (and 
                                                   (MS x147 x148 s21) 
                                                   (MS x147 x149 s21)) 
                                               (= x148 x149))) 
                                       (forall ((x150 Int)) 
                                           (=> 
                                               (and 
                                                   (<= 1 x150) 
                                                   (<= x150 n10)) 
                                               (exists ((x151 A)) 
                                                   (MS x150 x151 s21)))))) 
                               (forall ((x152 Int) (x153 A)) 
                                   (= 
                                       (MS x152 x153 x135) 
                                       (MS x152 x153 s11))) 
                               (forall ((x154 Int) (x155 A)) 
                                   (= 
                                       (MS x154 x155 x136) 
                                       (MS x154 x155 s21))) 
                               (forall ((x156 Int) (x157 A)) 
                                   (= 
                                       (MS x156 x157 x137) 
                                       (or 
                                           (exists ((i2 Int)) 
                                               (and 
                                                   (<= 1 i2) 
                                                   (forall ((x158 Int)) 
                                                       (=> 
                                                           (length s11 x158) 
                                                           (<= i2 x158))) 
                                                   (= x156 i2) 
                                                   (MS i2 x157 s11))) 
                                           (exists ((i3 Int)) 
                                               (and 
                                                   (forall ((x159 Int)) 
                                                       (=> 
                                                           (length s11 x159) 
                                                           (<= (+ x159 1) i3))) 
                                                   (forall ((x160 Int) (x161 Int)) 
                                                       (=> 
                                                           (and 
                                                               (length s11 x161) 
                                                               (length s21 x160)) 
                                                           (<= i3 (+ x161 x160)))) 
                                                   (= x156 i3) 
                                                   (exists ((x162 Int)) 
                                                       (and 
                                                           (forall ((x163 Int)) 
                                                               (=> 
                                                                   (length s11 x163) 
                                                                   (= x162 (- i3 x163)))) 
                                                           (MS x162 x157 s21)))))))))) 
                       (and 
                           (exists ((s5 PZA)) 
                               (and 
                                   (exists ((n11 Int)) 
                                       (and 
                                           (<= 0 n11) 
                                           (forall ((x164 Int) (x165 A)) 
                                               (=> 
                                                   (MS x164 x165 s5) 
                                                   (and 
                                                       (<= 1 x164) 
                                                       (<= x164 n11)))) 
                                           (forall ((x166 Int) (x167 A) (x168 A)) 
                                               (=> 
                                                   (and 
                                                       (MS x166 x167 s5) 
                                                       (MS x166 x168 s5)) 
                                                   (= x167 x168))) 
                                           (forall ((x169 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x169) 
                                                       (<= x169 n11)) 
                                                   (exists ((x170 A)) 
                                                       (MS x169 x170 s5)))))) 
                                   (forall ((x171 Int) (x172 A)) 
                                       (= 
                                           (MS x171 x172 x135) 
                                           (MS x171 x172 s5))))) 
                           (exists ((s6 PZA)) 
                               (and 
                                   (exists ((n12 Int)) 
                                       (and 
                                           (<= 0 n12) 
                                           (forall ((x173 Int) (x174 A)) 
                                               (=> 
                                                   (MS x173 x174 s6) 
                                                   (and 
                                                       (<= 1 x173) 
                                                       (<= x173 n12)))) 
                                           (forall ((x175 Int) (x176 A) (x177 A)) 
                                               (=> 
                                                   (and 
                                                       (MS x175 x176 s6) 
                                                       (MS x175 x177 s6)) 
                                                   (= x176 x177))) 
                                           (forall ((x178 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x178) 
                                                       (<= x178 n12)) 
                                                   (exists ((x179 A)) 
                                                       (MS x178 x179 s6)))))) 
                                   (forall ((x180 Int) (x181 A)) 
                                       (= 
                                           (MS x180 x181 x136) 
                                           (MS x180 x181 s6))))) 
                           (exists ((s7 PZA)) 
                               (and 
                                   (exists ((n13 Int)) 
                                       (and 
                                           (<= 0 n13) 
                                           (forall ((x182 Int) (x183 A)) 
                                               (=> 
                                                   (MS x182 x183 s7) 
                                                   (and 
                                                       (<= 1 x182) 
                                                       (<= x182 n13)))) 
                                           (forall ((x184 Int) (x185 A) (x186 A)) 
                                               (=> 
                                                   (and 
                                                       (MS x184 x185 s7) 
                                                       (MS x184 x186 s7)) 
                                                   (= x185 x186))) 
                                           (forall ((x187 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x187) 
                                                       (<= x187 n13)) 
                                                   (exists ((x188 A)) 
                                                       (MS x187 x188 s7)))))) 
                                   (forall ((x189 Int) (x190 A)) 
                                       (= 
                                           (MS x189 x190 x137) 
                                           (MS x189 x190 s7)))))))) 
               (forall ((x191 PZA) (x192 PZA) (x193 PZA) (x194 PZA)) 
                   (=> 
                       (and 
                           (exists ((s12 PZA) (s22 PZA)) 
                               (and 
                                   (exists ((n14 Int)) 
                                       (and 
                                           (<= 0 n14) 
                                           (forall ((x195 Int) (x196 A)) 
                                               (=> 
                                                   (MS x195 x196 s12) 
                                                   (and 
                                                       (<= 1 x195) 
                                                       (<= x195 n14)))) 
                                           (forall ((x197 Int) (x198 A) (x199 A)) 
                                               (=> 
                                                   (and 
                                                       (MS x197 x198 s12) 
                                                       (MS x197 x199 s12)) 
                                                   (= x198 x199))) 
                                           (forall ((x200 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x200) 
                                                       (<= x200 n14)) 
                                                   (exists ((x201 A)) 
                                                       (MS x200 x201 s12)))))) 
                                   (exists ((n15 Int)) 
                                       (and 
                                           (<= 0 n15) 
                                           (forall ((x202 Int) (x203 A)) 
                                               (=> 
                                                   (MS x202 x203 s22) 
                                                   (and 
                                                       (<= 1 x202) 
                                                       (<= x202 n15)))) 
                                           (forall ((x204 Int) (x205 A) (x206 A)) 
                                               (=> 
                                                   (and 
                                                       (MS x204 x205 s22) 
                                                       (MS x204 x206 s22)) 
                                                   (= x205 x206))) 
                                           (forall ((x207 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x207) 
                                                       (<= x207 n15)) 
                                                   (exists ((x208 A)) 
                                                       (MS x207 x208 s22)))))) 
                                   (forall ((x209 Int) (x210 A)) 
                                       (= 
                                           (MS x209 x210 x191) 
                                           (MS x209 x210 s12))) 
                                   (forall ((x211 Int) (x212 A)) 
                                       (= 
                                           (MS x211 x212 x192) 
                                           (MS x211 x212 s22))) 
                                   (forall ((x213 Int) (x214 A)) 
                                       (= 
                                           (MS x213 x214 x193) 
                                           (or 
                                               (exists ((i4 Int)) 
                                                   (and 
                                                       (<= 1 i4) 
                                                       (forall ((x215 Int)) 
                                                           (=> 
                                                               (length s12 x215) 
                                                               (<= i4 x215))) 
                                                       (= x213 i4) 
                                                       (MS i4 x214 s12))) 
                                               (exists ((i5 Int)) 
                                                   (and 
                                                       (forall ((x216 Int)) 
                                                           (=> 
                                                               (length s12 x216) 
                                                               (<= (+ x216 1) i5))) 
                                                       (forall ((x217 Int) (x218 Int)) 
                                                           (=> 
                                                               (and 
                                                                   (length s12 x218) 
                                                                   (length s22 x217)) 
                                                               (<= i5 (+ x218 x217)))) 
                                                       (= x213 i5) 
                                                       (exists ((x219 Int)) 
                                                           (and 
                                                               (forall ((x220 Int)) 
                                                                   (=> 
                                                                       (length s12 x220) 
                                                                       (= x219 (- i5 x220)))) 
                                                               (MS x219 x214 s22)))))))))) 
                           (exists ((s13 PZA) (s23 PZA)) 
                               (and 
                                   (exists ((n16 Int)) 
                                       (and 
                                           (<= 0 n16) 
                                           (forall ((x221 Int) (x222 A)) 
                                               (=> 
                                                   (MS x221 x222 s13) 
                                                   (and 
                                                       (<= 1 x221) 
                                                       (<= x221 n16)))) 
                                           (forall ((x223 Int) (x224 A) (x225 A)) 
                                               (=> 
                                                   (and 
                                                       (MS x223 x224 s13) 
                                                       (MS x223 x225 s13)) 
                                                   (= x224 x225))) 
                                           (forall ((x226 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x226) 
                                                       (<= x226 n16)) 
                                                   (exists ((x227 A)) 
                                                       (MS x226 x227 s13)))))) 
                                   (exists ((n17 Int)) 
                                       (and 
                                           (<= 0 n17) 
                                           (forall ((x228 Int) (x229 A)) 
                                               (=> 
                                                   (MS x228 x229 s23) 
                                                   (and 
                                                       (<= 1 x228) 
                                                       (<= x228 n17)))) 
                                           (forall ((x230 Int) (x231 A) (x232 A)) 
                                               (=> 
                                                   (and 
                                                       (MS x230 x231 s23) 
                                                       (MS x230 x232 s23)) 
                                                   (= x231 x232))) 
                                           (forall ((x233 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x233) 
                                                       (<= x233 n17)) 
                                                   (exists ((x234 A)) 
                                                       (MS x233 x234 s23)))))) 
                                   (forall ((x235 Int) (x236 A)) 
                                       (= 
                                           (MS x235 x236 x191) 
                                           (MS x235 x236 s13))) 
                                   (forall ((x237 Int) (x238 A)) 
                                       (= 
                                           (MS x237 x238 x192) 
                                           (MS x237 x238 s23))) 
                                   (forall ((x239 Int) (x240 A)) 
                                       (= 
                                           (MS x239 x240 x194) 
                                           (or 
                                               (exists ((i6 Int)) 
                                                   (and 
                                                       (<= 1 i6) 
                                                       (forall ((x241 Int)) 
                                                           (=> 
                                                               (length s13 x241) 
                                                               (<= i6 x241))) 
                                                       (= x239 i6) 
                                                       (MS i6 x240 s13))) 
                                               (exists ((i7 Int)) 
                                                   (and 
                                                       (forall ((x242 Int)) 
                                                           (=> 
                                                               (length s13 x242) 
                                                               (<= (+ x242 1) i7))) 
                                                       (forall ((x243 Int) (x244 Int)) 
                                                           (=> 
                                                               (and 
                                                                   (length s13 x244) 
                                                                   (length s23 x243)) 
                                                               (<= i7 (+ x244 x243)))) 
                                                       (= x239 i7) 
                                                       (exists ((x245 Int)) 
                                                           (and 
                                                               (forall ((x246 Int)) 
                                                                   (=> 
                                                                       (length s13 x246) 
                                                                       (= x245 (- i7 x246)))) 
                                                               (MS x245 x240 s23))))))))))) 
                       (forall ((x247 Int) (x248 A)) 
                           (= 
                               (MS x247 x248 x193) 
                               (MS x247 x248 x194))))) 
               (forall ((x249 PZA) (x250 PZA)) 
                   (=> 
                       (and 
                           (exists ((s8 PZA)) 
                               (and 
                                   (exists ((n18 Int)) 
                                       (and 
                                           (<= 0 n18) 
                                           (forall ((x251 Int) (x252 A)) 
                                               (=> 
                                                   (MS x251 x252 s8) 
                                                   (and 
                                                       (<= 1 x251) 
                                                       (<= x251 n18)))) 
                                           (forall ((x253 Int) (x254 A) (x255 A)) 
                                               (=> 
                                                   (and 
                                                       (MS x253 x254 s8) 
                                                       (MS x253 x255 s8)) 
                                                   (= x254 x255))) 
                                           (forall ((x256 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x256) 
                                                       (<= x256 n18)) 
                                                   (exists ((x257 A)) 
                                                       (MS x256 x257 s8)))))) 
                                   (forall ((x258 Int) (x259 A)) 
                                       (= 
                                           (MS x258 x259 x249) 
                                           (MS x258 x259 s8))))) 
                           (exists ((s9 PZA)) 
                               (and 
                                   (exists ((n19 Int)) 
                                       (and 
                                           (<= 0 n19) 
                                           (forall ((x260 Int) (x261 A)) 
                                               (=> 
                                                   (MS x260 x261 s9) 
                                                   (and 
                                                       (<= 1 x260) 
                                                       (<= x260 n19)))) 
                                           (forall ((x262 Int) (x263 A) (x264 A)) 
                                               (=> 
                                                   (and 
                                                       (MS x262 x263 s9) 
                                                       (MS x262 x264 s9)) 
                                                   (= x263 x264))) 
                                           (forall ((x265 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x265) 
                                                       (<= x265 n19)) 
                                                   (exists ((x266 A)) 
                                                       (MS x265 x266 s9)))))) 
                                   (forall ((x267 Int) (x268 A)) 
                                       (= 
                                           (MS x267 x268 x250) 
                                           (MS x267 x268 s9)))))) 
                       (exists ((x269 PZA) (s14 PZA) (s24 PZA)) 
                           (and 
                               (exists ((n20 Int)) 
                                   (and 
                                       (<= 0 n20) 
                                       (forall ((x270 Int) (x271 A)) 
                                           (=> 
                                               (MS x270 x271 s14) 
                                               (and 
                                                   (<= 1 x270) 
                                                   (<= x270 n20)))) 
                                       (forall ((x272 Int) (x273 A) (x274 A)) 
                                           (=> 
                                               (and 
                                                   (MS x272 x273 s14) 
                                                   (MS x272 x274 s14)) 
                                               (= x273 x274))) 
                                       (forall ((x275 Int)) 
                                           (=> 
                                               (and 
                                                   (<= 1 x275) 
                                                   (<= x275 n20)) 
                                               (exists ((x276 A)) 
                                                   (MS x275 x276 s14)))))) 
                               (exists ((n21 Int)) 
                                   (and 
                                       (<= 0 n21) 
                                       (forall ((x277 Int) (x278 A)) 
                                           (=> 
                                               (MS x277 x278 s24) 
                                               (and 
                                                   (<= 1 x277) 
                                                   (<= x277 n21)))) 
                                       (forall ((x279 Int) (x280 A) (x281 A)) 
                                           (=> 
                                               (and 
                                                   (MS x279 x280 s24) 
                                                   (MS x279 x281 s24)) 
                                               (= x280 x281))) 
                                       (forall ((x282 Int)) 
                                           (=> 
                                               (and 
                                                   (<= 1 x282) 
                                                   (<= x282 n21)) 
                                               (exists ((x283 A)) 
                                                   (MS x282 x283 s24)))))) 
                               (forall ((x284 Int) (x285 A)) 
                                   (= 
                                       (MS x284 x285 x249) 
                                       (MS x284 x285 s14))) 
                               (forall ((x286 Int) (x287 A)) 
                                   (= 
                                       (MS x286 x287 x250) 
                                       (MS x286 x287 s24))) 
                               (forall ((x288 Int) (x289 A)) 
                                   (= 
                                       (MS x288 x289 x269) 
                                       (or 
                                           (exists ((i8 Int)) 
                                               (and 
                                                   (<= 1 i8) 
                                                   (forall ((x290 Int)) 
                                                       (=> 
                                                           (length s14 x290) 
                                                           (<= i8 x290))) 
                                                   (= x288 i8) 
                                                   (MS i8 x289 s14))) 
                                           (exists ((i9 Int)) 
                                               (and 
                                                   (forall ((x291 Int)) 
                                                       (=> 
                                                           (length s14 x291) 
                                                           (<= (+ x291 1) i9))) 
                                                   (forall ((x292 Int) (x293 Int)) 
                                                       (=> 
                                                           (and 
                                                               (length s14 x293) 
                                                               (length s24 x292)) 
                                                           (<= i9 (+ x293 x292)))) 
                                                   (= x288 i9) 
                                                   (exists ((x294 Int)) 
                                                       (and 
                                                           (forall ((x295 Int)) 
                                                               (=> 
                                                                   (length s14 x295) 
                                                                   (= x294 (- i9 x295)))) 
                                                           (MS x294 x289 s24)))))))))))))
         :named hyp12))
(assert (! (forall ((s15 PZA) (s25 PZA)) 
               (=> 
                   (and 
                       (exists ((n22 Int)) 
                           (and 
                               (<= 0 n22) 
                               (forall ((x296 Int) (x297 A)) 
                                   (=> 
                                       (MS x296 x297 s15) 
                                       (and 
                                           (<= 1 x296) 
                                           (<= x296 n22)))) 
                               (forall ((x298 Int) (x299 A) (x300 A)) 
                                   (=> 
                                       (and 
                                           (MS x298 x299 s15) 
                                           (MS x298 x300 s15)) 
                                       (= x299 x300))) 
                               (forall ((x301 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x301) 
                                           (<= x301 n22)) 
                                       (exists ((x302 A)) 
                                           (MS x301 x302 s15)))))) 
                       (exists ((n23 Int)) 
                           (and 
                               (<= 0 n23) 
                               (forall ((x303 Int) (x304 A)) 
                                   (=> 
                                       (MS x303 x304 s25) 
                                       (and 
                                           (<= 1 x303) 
                                           (<= x303 n23)))) 
                               (forall ((x305 Int) (x306 A) (x307 A)) 
                                   (=> 
                                       (and 
                                           (MS x305 x306 s25) 
                                           (MS x305 x307 s25)) 
                                       (= x306 x307))) 
                               (forall ((x308 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x308) 
                                           (<= x308 n23)) 
                                       (exists ((x309 A)) 
                                           (MS x308 x309 s25))))))) 
                   (exists ((x310 PZA) (x311 Int)) 
                       (and 
                           (forall ((x312 Int) (x313 A)) 
                               (= 
                                   (MS x312 x313 x310) 
                                   (or 
                                       (exists ((i10 Int)) 
                                           (and 
                                               (<= 1 i10) 
                                               (forall ((x314 Int)) 
                                                   (=> 
                                                       (length s15 x314) 
                                                       (<= i10 x314))) 
                                               (= x312 i10) 
                                               (MS i10 x313 s15))) 
                                       (exists ((i11 Int)) 
                                           (and 
                                               (forall ((x315 Int)) 
                                                   (=> 
                                                       (length s15 x315) 
                                                       (<= (+ x315 1) i11))) 
                                               (forall ((x316 Int) (x317 Int)) 
                                                   (=> 
                                                       (and 
                                                           (length s15 x317) 
                                                           (length s25 x316)) 
                                                       (<= i11 (+ x317 x316)))) 
                                               (= x312 i11) 
                                               (exists ((x318 Int)) 
                                                   (and 
                                                       (forall ((x319 Int)) 
                                                           (=> 
                                                               (length s15 x319) 
                                                               (= x318 (- i11 x319)))) 
                                                       (MS x318 x313 s25)))))))) 
                           (forall ((x320 Int) (x321 Int)) 
                               (=> 
                                   (and 
                                       (length s15 x321) 
                                       (length s25 x320)) 
                                   (= x311 (+ x321 x320)))) 
                           (length x310 x311)))))
         :named hyp13))
(assert (! (forall ((s16 PZA) (s26 PZA)) 
               (=> 
                   (and 
                       (exists ((n24 Int)) 
                           (and 
                               (<= 0 n24) 
                               (forall ((x322 Int) (x323 A)) 
                                   (=> 
                                       (MS x322 x323 s16) 
                                       (and 
                                           (<= 1 x322) 
                                           (<= x322 n24)))) 
                               (forall ((x324 Int) (x325 A) (x326 A)) 
                                   (=> 
                                       (and 
                                           (MS x324 x325 s16) 
                                           (MS x324 x326 s16)) 
                                       (= x325 x326))) 
                               (forall ((x327 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x327) 
                                           (<= x327 n24)) 
                                       (exists ((x328 A)) 
                                           (MS x327 x328 s16)))))) 
                       (exists ((n25 Int)) 
                           (and 
                               (<= 0 n25) 
                               (forall ((x329 Int) (x330 A)) 
                                   (=> 
                                       (MS x329 x330 s26) 
                                       (and 
                                           (<= 1 x329) 
                                           (<= x329 n25)))) 
                               (forall ((x331 Int) (x332 A) (x333 A)) 
                                   (=> 
                                       (and 
                                           (MS x331 x332 s26) 
                                           (MS x331 x333 s26)) 
                                       (= x332 x333))) 
                               (forall ((x334 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x334) 
                                           (<= x334 n25)) 
                                       (exists ((x335 A)) 
                                           (MS x334 x335 s26))))))) 
                   (forall ((x336 Int)) 
                       (= 
                           (or 
                               (exists ((x337 A)) 
                                   (exists ((i12 Int)) 
                                       (and 
                                           (<= 1 i12) 
                                           (forall ((x338 Int)) 
                                               (=> 
                                                   (length s16 x338) 
                                                   (<= i12 x338))) 
                                           (= x336 i12) 
                                           (MS i12 x337 s16)))) 
                               (exists ((x339 A)) 
                                   (exists ((i13 Int)) 
                                       (and 
                                           (forall ((x340 Int)) 
                                               (=> 
                                                   (length s16 x340) 
                                                   (<= (+ x340 1) i13))) 
                                           (forall ((x341 Int) (x342 Int)) 
                                               (=> 
                                                   (and 
                                                       (length s16 x342) 
                                                       (length s26 x341)) 
                                                   (<= i13 (+ x342 x341)))) 
                                           (= x336 i13) 
                                           (exists ((x343 Int)) 
                                               (and 
                                                   (forall ((x344 Int)) 
                                                       (=> 
                                                           (length s16 x344) 
                                                           (= x343 (- i13 x344)))) 
                                                   (MS x343 x339 s26))))))) 
                           (and 
                               (<= 1 x336) 
                               (forall ((x345 Int) (x346 Int)) 
                                   (=> 
                                       (and 
                                           (length s16 x346) 
                                           (length s26 x345)) 
                                       (<= x336 (+ x346 x345)))))))))
         :named hyp14))
(assert (! (forall ((s17 PZA) (s27 PZA)) 
               (=> 
                   (and 
                       (exists ((n26 Int)) 
                           (and 
                               (<= 0 n26) 
                               (forall ((x347 Int) (x348 A)) 
                                   (=> 
                                       (MS x347 x348 s17) 
                                       (and 
                                           (<= 1 x347) 
                                           (<= x347 n26)))) 
                               (forall ((x349 Int) (x350 A) (x351 A)) 
                                   (=> 
                                       (and 
                                           (MS x349 x350 s17) 
                                           (MS x349 x351 s17)) 
                                       (= x350 x351))) 
                               (forall ((x352 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x352) 
                                           (<= x352 n26)) 
                                       (exists ((x353 A)) 
                                           (MS x352 x353 s17)))))) 
                       (exists ((n27 Int)) 
                           (and 
                               (<= 0 n27) 
                               (forall ((x354 Int) (x355 A)) 
                                   (=> 
                                       (MS x354 x355 s27) 
                                       (and 
                                           (<= 1 x354) 
                                           (<= x354 n27)))) 
                               (forall ((x356 Int) (x357 A) (x358 A)) 
                                   (=> 
                                       (and 
                                           (MS x356 x357 s27) 
                                           (MS x356 x358 s27)) 
                                       (= x357 x358))) 
                               (forall ((x359 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x359) 
                                           (<= x359 n27)) 
                                       (exists ((x360 A)) 
                                           (MS x359 x360 s27))))))) 
                   (forall ((x361 A)) 
                       (= 
                           (or 
                               (exists ((x362 Int)) 
                                   (exists ((i14 Int)) 
                                       (and 
                                           (<= 1 i14) 
                                           (forall ((x363 Int)) 
                                               (=> 
                                                   (length s17 x363) 
                                                   (<= i14 x363))) 
                                           (= x362 i14) 
                                           (MS i14 x361 s17)))) 
                               (exists ((x364 Int)) 
                                   (exists ((i15 Int)) 
                                       (and 
                                           (forall ((x365 Int)) 
                                               (=> 
                                                   (length s17 x365) 
                                                   (<= (+ x365 1) i15))) 
                                           (forall ((x366 Int) (x367 Int)) 
                                               (=> 
                                                   (and 
                                                       (length s17 x367) 
                                                       (length s27 x366)) 
                                                   (<= i15 (+ x367 x366)))) 
                                           (= x364 i15) 
                                           (exists ((x368 Int)) 
                                               (and 
                                                   (forall ((x369 Int)) 
                                                       (=> 
                                                           (length s17 x369) 
                                                           (= x368 (- i15 x369)))) 
                                                   (MS x368 x361 s27))))))) 
                           (or 
                               (exists ((x370 Int)) 
                                   (MS x370 x361 s17)) 
                               (exists ((x371 Int)) 
                                   (MS x371 x361 s27)))))))
         :named hyp15))
(assert (! (forall ((s18 PZA) (s28 PZA) (i16 Int)) 
               (=> 
                   (and 
                       (exists ((n28 Int)) 
                           (and 
                               (<= 0 n28) 
                               (forall ((x372 Int) (x373 A)) 
                                   (=> 
                                       (MS x372 x373 s18) 
                                       (and 
                                           (<= 1 x372) 
                                           (<= x372 n28)))) 
                               (forall ((x374 Int) (x375 A) (x376 A)) 
                                   (=> 
                                       (and 
                                           (MS x374 x375 s18) 
                                           (MS x374 x376 s18)) 
                                       (= x375 x376))) 
                               (forall ((x377 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x377) 
                                           (<= x377 n28)) 
                                       (exists ((x378 A)) 
                                           (MS x377 x378 s18)))))) 
                       (exists ((n29 Int)) 
                           (and 
                               (<= 0 n29) 
                               (forall ((x379 Int) (x380 A)) 
                                   (=> 
                                       (MS x379 x380 s28) 
                                       (and 
                                           (<= 1 x379) 
                                           (<= x379 n29)))) 
                               (forall ((x381 Int) (x382 A) (x383 A)) 
                                   (=> 
                                       (and 
                                           (MS x381 x382 s28) 
                                           (MS x381 x383 s28)) 
                                       (= x382 x383))) 
                               (forall ((x384 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x384) 
                                           (<= x384 n29)) 
                                       (exists ((x385 A)) 
                                           (MS x384 x385 s28)))))) 
                       (<= 1 i16) 
                       (forall ((x386 Int)) 
                           (=> 
                               (length s18 x386) 
                               (<= i16 x386)))) 
                   (or 
                       (exists ((i17 Int)) 
                           (and 
                               (<= 1 i17) 
                               (forall ((x387 Int)) 
                                   (=> 
                                       (length s18 x387) 
                                       (<= i17 x387))) 
                               (= i16 i17) 
                               (exists ((x388 A)) 
                                   (and 
                                       (MS i17 x388 s18) 
                                       (MS i16 x388 s18))))) 
                       (exists ((i18 Int)) 
                           (and 
                               (forall ((x389 Int)) 
                                   (=> 
                                       (length s18 x389) 
                                       (<= (+ x389 1) i18))) 
                               (forall ((x390 Int) (x391 Int)) 
                                   (=> 
                                       (and 
                                           (length s18 x391) 
                                           (length s28 x390)) 
                                       (<= i18 (+ x391 x390)))) 
                               (= i16 i18) 
                               (exists ((x392 A)) 
                                   (and 
                                       (exists ((x393 Int)) 
                                           (and 
                                               (forall ((x394 Int)) 
                                                   (=> 
                                                       (length s18 x394) 
                                                       (= x393 (- i18 x394)))) 
                                               (MS x393 x392 s28))) 
                                       (MS i16 x392 s18))))))))
         :named hyp16))
(assert (! (forall ((s19 PZA) (s29 PZA) (i19 Int)) 
               (=> 
                   (and 
                       (exists ((n30 Int)) 
                           (and 
                               (<= 0 n30) 
                               (forall ((x395 Int) (x396 A)) 
                                   (=> 
                                       (MS x395 x396 s19) 
                                       (and 
                                           (<= 1 x395) 
                                           (<= x395 n30)))) 
                               (forall ((x397 Int) (x398 A) (x399 A)) 
                                   (=> 
                                       (and 
                                           (MS x397 x398 s19) 
                                           (MS x397 x399 s19)) 
                                       (= x398 x399))) 
                               (forall ((x400 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x400) 
                                           (<= x400 n30)) 
                                       (exists ((x401 A)) 
                                           (MS x400 x401 s19)))))) 
                       (exists ((n31 Int)) 
                           (and 
                               (<= 0 n31) 
                               (forall ((x402 Int) (x403 A)) 
                                   (=> 
                                       (MS x402 x403 s29) 
                                       (and 
                                           (<= 1 x402) 
                                           (<= x402 n31)))) 
                               (forall ((x404 Int) (x405 A) (x406 A)) 
                                   (=> 
                                       (and 
                                           (MS x404 x405 s29) 
                                           (MS x404 x406 s29)) 
                                       (= x405 x406))) 
                               (forall ((x407 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x407) 
                                           (<= x407 n31)) 
                                       (exists ((x408 A)) 
                                           (MS x407 x408 s29)))))) 
                       (forall ((x409 Int)) 
                           (=> 
                               (length s19 x409) 
                               (<= (+ x409 1) i19))) 
                       (forall ((x410 Int) (x411 Int)) 
                           (=> 
                               (and 
                                   (length s19 x411) 
                                   (length s29 x410)) 
                               (<= i19 (+ x411 x410))))) 
                   (or 
                       (exists ((i20 Int)) 
                           (and 
                               (<= 1 i20) 
                               (forall ((x412 Int)) 
                                   (=> 
                                       (length s19 x412) 
                                       (<= i20 x412))) 
                               (= i19 i20) 
                               (exists ((x413 Int) (x414 A)) 
                                   (and 
                                       (forall ((x415 Int)) 
                                           (=> 
                                               (length s19 x415) 
                                               (= x413 (- i19 x415)))) 
                                       (MS i20 x414 s19) 
                                       (MS x413 x414 s29))))) 
                       (exists ((i21 Int)) 
                           (and 
                               (forall ((x416 Int)) 
                                   (=> 
                                       (length s19 x416) 
                                       (<= (+ x416 1) i21))) 
                               (forall ((x417 Int) (x418 Int)) 
                                   (=> 
                                       (and 
                                           (length s19 x418) 
                                           (length s29 x417)) 
                                       (<= i21 (+ x418 x417)))) 
                               (= i19 i21) 
                               (exists ((x419 Int) (x420 A)) 
                                   (and 
                                       (forall ((x421 Int)) 
                                           (=> 
                                               (length s19 x421) 
                                               (= x419 (- i19 x421)))) 
                                       (exists ((x422 Int)) 
                                           (and 
                                               (forall ((x423 Int)) 
                                                   (=> 
                                                       (length s19 x423) 
                                                       (= x422 (- i21 x423)))) 
                                               (MS x422 x420 s29))) 
                                       (MS x419 x420 s29))))))))
         :named hyp17))
(assert (! (forall ((s110 PZA) (s210 PZA) (b PA)) 
               (=> 
                   (and 
                       (exists ((n32 Int)) 
                           (and 
                               (<= 0 n32) 
                               (forall ((x424 Int) (x425 A)) 
                                   (=> 
                                       (MS x424 x425 s110) 
                                       (and 
                                           (<= 1 x424) 
                                           (<= x424 n32)))) 
                               (forall ((x426 Int) (x427 A) (x428 A)) 
                                   (=> 
                                       (and 
                                           (MS x426 x427 s110) 
                                           (MS x426 x428 s110)) 
                                       (= x427 x428))) 
                               (forall ((x429 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x429) 
                                           (<= x429 n32)) 
                                       (exists ((x430 A)) 
                                           (MS x429 x430 s110)))))) 
                       (exists ((n33 Int)) 
                           (and 
                               (<= 0 n33) 
                               (forall ((x431 Int) (x432 A)) 
                                   (=> 
                                       (MS x431 x432 s210) 
                                       (and 
                                           (<= 1 x431) 
                                           (<= x431 n33)))) 
                               (forall ((x433 Int) (x434 A) (x435 A)) 
                                   (=> 
                                       (and 
                                           (MS x433 x434 s210) 
                                           (MS x433 x435 s210)) 
                                       (= x434 x435))) 
                               (forall ((x436 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x436) 
                                           (<= x436 n33)) 
                                       (exists ((x437 A)) 
                                           (MS x436 x437 s210)))))) 
                       (forall ((x438 A)) 
                           (=> 
                               (exists ((x439 Int)) 
                                   (MS x439 x438 s110)) 
                               (MS0 x438 b))) 
                       (forall ((x440 A)) 
                           (=> 
                               (exists ((x441 Int)) 
                                   (MS x441 x440 s210)) 
                               (MS0 x440 b)))) 
                   (and 
                       (forall ((x442 Int) (x443 A)) 
                           (=> 
                               (or 
                                   (exists ((i22 Int)) 
                                       (and 
                                           (<= 1 i22) 
                                           (forall ((x444 Int)) 
                                               (=> 
                                                   (length s110 x444) 
                                                   (<= i22 x444))) 
                                           (= x442 i22) 
                                           (MS i22 x443 s110))) 
                                   (exists ((i23 Int)) 
                                       (and 
                                           (forall ((x445 Int)) 
                                               (=> 
                                                   (length s110 x445) 
                                                   (<= (+ x445 1) i23))) 
                                           (forall ((x446 Int) (x447 Int)) 
                                               (=> 
                                                   (and 
                                                       (length s110 x447) 
                                                       (length s210 x446)) 
                                                   (<= i23 (+ x447 x446)))) 
                                           (= x442 i23) 
                                           (exists ((x448 Int)) 
                                               (and 
                                                   (forall ((x449 Int)) 
                                                       (=> 
                                                           (length s110 x449) 
                                                           (= x448 (- i23 x449)))) 
                                                   (MS x448 x443 s210)))))) 
                               (and 
                                   (<= 1 x442) 
                                   (forall ((x450 Int) (x451 Int)) 
                                       (=> 
                                           (and 
                                               (length s110 x451) 
                                               (length s210 x450)) 
                                           (<= x442 (+ x451 x450)))) 
                                   (MS0 x443 b)))) 
                       (forall ((x452 Int) (x453 A) (x454 A)) 
                           (=> 
                               (and 
                                   (or 
                                       (exists ((i24 Int)) 
                                           (and 
                                               (<= 1 i24) 
                                               (forall ((x455 Int)) 
                                                   (=> 
                                                       (length s110 x455) 
                                                       (<= i24 x455))) 
                                               (= x452 i24) 
                                               (MS i24 x453 s110))) 
                                       (exists ((i25 Int)) 
                                           (and 
                                               (forall ((x456 Int)) 
                                                   (=> 
                                                       (length s110 x456) 
                                                       (<= (+ x456 1) i25))) 
                                               (forall ((x457 Int) (x458 Int)) 
                                                   (=> 
                                                       (and 
                                                           (length s110 x458) 
                                                           (length s210 x457)) 
                                                       (<= i25 (+ x458 x457)))) 
                                               (= x452 i25) 
                                               (exists ((x459 Int)) 
                                                   (and 
                                                       (forall ((x460 Int)) 
                                                           (=> 
                                                               (length s110 x460) 
                                                               (= x459 (- i25 x460)))) 
                                                       (MS x459 x453 s210)))))) 
                                   (or 
                                       (exists ((i26 Int)) 
                                           (and 
                                               (<= 1 i26) 
                                               (forall ((x461 Int)) 
                                                   (=> 
                                                       (length s110 x461) 
                                                       (<= i26 x461))) 
                                               (= x452 i26) 
                                               (MS i26 x454 s110))) 
                                       (exists ((i27 Int)) 
                                           (and 
                                               (forall ((x462 Int)) 
                                                   (=> 
                                                       (length s110 x462) 
                                                       (<= (+ x462 1) i27))) 
                                               (forall ((x463 Int) (x464 Int)) 
                                                   (=> 
                                                       (and 
                                                           (length s110 x464) 
                                                           (length s210 x463)) 
                                                       (<= i27 (+ x464 x463)))) 
                                               (= x452 i27) 
                                               (exists ((x465 Int)) 
                                                   (and 
                                                       (forall ((x466 Int)) 
                                                           (=> 
                                                               (length s110 x466) 
                                                               (= x465 (- i27 x466)))) 
                                                       (MS x465 x454 s210))))))) 
                               (= x453 x454))) 
                       (forall ((x467 Int)) 
                           (=> 
                               (and 
                                   (<= 1 x467) 
                                   (forall ((x468 Int) (x469 Int)) 
                                       (=> 
                                           (and 
                                               (length s110 x469) 
                                               (length s210 x468)) 
                                           (<= x467 (+ x469 x468))))) 
                               (or 
                                   (exists ((x470 A)) 
                                       (exists ((i28 Int)) 
                                           (and 
                                               (<= 1 i28) 
                                               (forall ((x471 Int)) 
                                                   (=> 
                                                       (length s110 x471) 
                                                       (<= i28 x471))) 
                                               (= x467 i28) 
                                               (MS i28 x470 s110)))) 
                                   (exists ((x472 A)) 
                                       (exists ((i29 Int)) 
                                           (and 
                                               (forall ((x473 Int)) 
                                                   (=> 
                                                       (length s110 x473) 
                                                       (<= (+ x473 1) i29))) 
                                               (forall ((x474 Int) (x475 Int)) 
                                                   (=> 
                                                       (and 
                                                           (length s110 x475) 
                                                           (length s210 x474)) 
                                                       (<= i29 (+ x475 x474)))) 
                                               (= x467 i29) 
                                               (exists ((x476 Int)) 
                                                   (and 
                                                       (forall ((x477 Int)) 
                                                           (=> 
                                                               (length s110 x477) 
                                                               (= x476 (- i29 x477)))) 
                                                       (MS x476 x472 s210))))))))))))
         :named hyp18))
(assert (! (not 
               (exists ((b0 Int)) 
                   (forall ((x00 Int)) 
                       (=> 
                           (exists ((x478 PZA)) 
                               (and 
                                   (exists ((x479 A) (x480 A)) 
                                       (and 
                                           (= x479 x) 
                                           (= x480 y) 
                                           (exists ((x481 A) (y1 A) (p0 PZA)) 
                                               (and 
                                                   (exists ((n34 Int)) 
                                                       (and 
                                                           (<= 0 n34) 
                                                           (forall ((x482 Int) (x483 A)) 
                                                               (=> 
                                                                   (MS x482 x483 p0) 
                                                                   (and 
                                                                       (<= 1 x482) 
                                                                       (<= x482 n34)))) 
                                                           (forall ((x484 Int) (x485 A) (x486 A)) 
                                                               (=> 
                                                                   (and 
                                                                       (MS x484 x485 p0) 
                                                                       (MS x484 x486 p0)) 
                                                                   (= x485 x486))) 
                                                           (forall ((x487 Int)) 
                                                               (=> 
                                                                   (and 
                                                                       (<= 1 x487) 
                                                                       (<= x487 n34)) 
                                                                   (exists ((x488 A)) 
                                                                       (MS x487 x488 p0)))))) 
                                                   (forall ((x489 A)) 
                                                       (=> 
                                                           (exists ((x490 Int)) 
                                                               (MS x490 x489 p0)) 
                                                           (MS0 x489 a))) 
                                                   (forall ((x491 Int)) 
                                                       (=> 
                                                           (length p0 x491) 
                                                           (< 1 x491))) 
                                                   (exists ((x492 Int)) 
                                                       (and 
                                                           (= x492 1) 
                                                           (MS x492 x481 p0))) 
                                                   (exists ((x493 Int)) 
                                                       (and 
                                                           (length p0 x493) 
                                                           (MS x493 y1 p0))) 
                                                   (forall ((i30 Int)) 
                                                       (=> 
                                                           (and 
                                                               (<= 1 i30) 
                                                               (forall ((x494 Int)) 
                                                                   (=> 
                                                                       (length p0 x494) 
                                                                       (<= i30 (- x494 1))))) 
                                                           (exists ((x495 A) (x496 A)) 
                                                               (and 
                                                                   (MS i30 x495 p0) 
                                                                   (exists ((x497 Int)) 
                                                                       (and 
                                                                           (= x497 (+ i30 1)) 
                                                                           (MS x497 x496 p0))) 
                                                                   (r x495 x496))))) 
                                                   (= x479 x481) 
                                                   (= x480 y1) 
                                                   (forall ((x498 Int) (x499 A)) 
                                                       (= 
                                                           (MS x498 x499 x478) 
                                                           (MS x498 x499 p0))))))) 
                                   (length x478 x00))) 
                           (<= b0 x00)))))
         :named goal))
(check-sat)
(exit)

