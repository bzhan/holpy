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
(declare-fun MS0 (A PA) Bool)
(declare-fun MS1 (A A PAA) Bool)
(declare-fun cnc (PZA PZA PZA) Bool)
(declare-fun length (PZA Int) Bool)
(declare-fun path (A A PZA) Bool)
(declare-fun seq (PZA) Bool)
(declare-fun a () PA)
(declare-fun c () PAA)
(declare-fun candidate () PA)
(declare-fun i () Int)
(declare-fun r () PAA)
(declare-fun s1 () PZA)
(declare-fun s2 () PZA)

; Elementary Sets axiom (Singleton part)
(assert (forall ((x798 A) (x799 A)) 
            (exists ((X PAA)) 
                (and 
                    (MS1 x798 x799 X) 
                    (forall ((y3 A) (y4 A)) 
                        (=> 
                            (MS1 y3 y4 X) 
                            (and 
                                (= y3 x798) 
                                (= y4 x799))))))))
; Elementary Sets axiom (Singleton part)
(assert (forall ((x800 A)) 
            (exists ((X0 PA)) 
                (and 
                    (MS0 x800 X0) 
                    (forall ((y5 A)) 
                        (=> 
                            (MS0 y5 X0) 
                            (= y5 x800)))))))
; Elementary Sets axiom (Singleton part)
(assert (forall ((x801 Int) (x802 A)) 
            (exists ((X1 PZA)) 
                (and 
                    (MS x801 x802 X1) 
                    (forall ((y6 Int) (y7 A)) 
                        (=> 
                            (MS y6 y7 X1) 
                            (and 
                                (= y6 x801) 
                                (= y7 x802))))))))
(assert (! (forall ((x PZA)) 
               (= 
                   (seq x) 
                   (exists ((s PZA)) 
                       (and 
                           (exists ((n Int)) 
                               (and 
                                   (<= 0 n) 
                                   (forall ((x0 Int) (x1 A)) 
                                       (=> 
                                           (MS x0 x1 s) 
                                           (and 
                                               (<= 1 x0) 
                                               (<= x0 n)))) 
                                   (forall ((x2 Int) (x3 A) (x4 A)) 
                                       (=> 
                                           (and 
                                               (MS x2 x3 s) 
                                               (MS x2 x4 s)) 
                                           (= x3 x4))) 
                                   (forall ((x5 Int)) 
                                       (=> 
                                           (and 
                                               (<= 1 x5) 
                                               (<= x5 n)) 
                                           (exists ((x6 A)) 
                                               (MS x5 x6 s)))))) 
                           (forall ((x7 Int) (x8 A)) 
                               (= 
                                   (MS x7 x8 x) 
                                   (MS x7 x8 s)))))))
         :named hyp1))
(assert (! (forall ((n0 Int) (s0 PZA)) 
               (=> 
                   (and 
                       (<= 0 n0) 
                       (forall ((x9 Int) (x10 A)) 
                           (=> 
                               (MS x9 x10 s0) 
                               (and 
                                   (<= 1 x9) 
                                   (<= x9 n0)))) 
                       (forall ((x11 Int) (x12 A) (x13 A)) 
                           (=> 
                               (and 
                                   (MS x11 x12 s0) 
                                   (MS x11 x13 s0)) 
                               (= x12 x13))) 
                       (forall ((x14 Int)) 
                           (=> 
                               (and 
                                   (<= 1 x14) 
                                   (<= x14 n0)) 
                               (exists ((x15 A)) 
                                   (MS x14 x15 s0))))) 
                   (length s0 n0)))
         :named hyp2))
(assert (! (and 
               (forall ((x16 Int)) 
                   (=> 
                       (length s1 x16) 
                       (<= (+ x16 1) i))) 
               (forall ((x17 Int) (x18 Int)) 
                   (=> 
                       (and 
                           (length s1 x18) 
                           (length s2 x17)) 
                       (<= i (+ x18 x17)))))
         :named hyp3))
(assert (! (and 
               (forall ((x19 PZA) (x20 Int)) 
                   (=> 
                       (length x19 x20) 
                       (and 
                           (exists ((s3 PZA)) 
                               (and 
                                   (exists ((n1 Int)) 
                                       (and 
                                           (<= 0 n1) 
                                           (forall ((x21 Int) (x22 A)) 
                                               (=> 
                                                   (MS x21 x22 s3) 
                                                   (and 
                                                       (<= 1 x21) 
                                                       (<= x21 n1)))) 
                                           (forall ((x23 Int) (x24 A) (x25 A)) 
                                               (=> 
                                                   (and 
                                                       (MS x23 x24 s3) 
                                                       (MS x23 x25 s3)) 
                                                   (= x24 x25))) 
                                           (forall ((x26 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x26) 
                                                       (<= x26 n1)) 
                                                   (exists ((x27 A)) 
                                                       (MS x26 x27 s3)))))) 
                                   (forall ((x28 Int) (x29 A)) 
                                       (= 
                                           (MS x28 x29 x19) 
                                           (MS x28 x29 s3))))) 
                           (<= 0 x20)))) 
               (forall ((x30 PZA) (x31 Int) (x32 Int)) 
                   (=> 
                       (and 
                           (length x30 x31) 
                           (length x30 x32)) 
                       (= x31 x32))) 
               (forall ((x33 PZA)) 
                   (=> 
                       (exists ((s4 PZA)) 
                           (and 
                               (exists ((n2 Int)) 
                                   (and 
                                       (<= 0 n2) 
                                       (forall ((x34 Int) (x35 A)) 
                                           (=> 
                                               (MS x34 x35 s4) 
                                               (and 
                                                   (<= 1 x34) 
                                                   (<= x34 n2)))) 
                                       (forall ((x36 Int) (x37 A) (x38 A)) 
                                           (=> 
                                               (and 
                                                   (MS x36 x37 s4) 
                                                   (MS x36 x38 s4)) 
                                               (= x37 x38))) 
                                       (forall ((x39 Int)) 
                                           (=> 
                                               (and 
                                                   (<= 1 x39) 
                                                   (<= x39 n2)) 
                                               (exists ((x40 A)) 
                                                   (MS x39 x40 s4)))))) 
                               (forall ((x41 Int) (x42 A)) 
                                   (= 
                                       (MS x41 x42 x33) 
                                       (MS x41 x42 s4))))) 
                       (exists ((x43 Int)) 
                           (length x33 x43)))))
         :named hyp4))
(assert (! (forall ((n3 Int) (s5 PZA)) 
               (=> 
                   (and 
                       (<= 0 n3) 
                       (forall ((x44 Int) (x45 A)) 
                           (=> 
                               (MS x44 x45 s5) 
                               (and 
                                   (<= 1 x44) 
                                   (<= x44 n3)))) 
                       (forall ((x46 Int) (x47 A) (x48 A)) 
                           (=> 
                               (and 
                                   (MS x46 x47 s5) 
                                   (MS x46 x48 s5)) 
                               (= x47 x48))) 
                       (forall ((x49 Int)) 
                           (=> 
                               (and 
                                   (<= 1 x49) 
                                   (<= x49 n3)) 
                               (exists ((x50 A)) 
                                   (MS x49 x50 s5))))) 
                   (exists ((n4 Int)) 
                       (and 
                           (<= 0 n4) 
                           (forall ((x51 Int) (x52 A)) 
                               (=> 
                                   (MS x51 x52 s5) 
                                   (and 
                                       (<= 1 x51) 
                                       (<= x51 n4)))) 
                           (forall ((x53 Int) (x54 A) (x55 A)) 
                               (=> 
                                   (and 
                                       (MS x53 x54 s5) 
                                       (MS x53 x55 s5)) 
                                   (= x54 x55))) 
                           (forall ((x56 Int)) 
                               (=> 
                                   (and 
                                       (<= 1 x56) 
                                       (<= x56 n4)) 
                                   (exists ((x57 A)) 
                                       (MS x56 x57 s5))))))))
         :named hyp5))
(assert (! (forall ((s6 PZA)) 
               (=> 
                   (exists ((n5 Int)) 
                       (and 
                           (<= 0 n5) 
                           (forall ((x58 Int) (x59 A)) 
                               (=> 
                                   (MS x58 x59 s6) 
                                   (and 
                                       (<= 1 x58) 
                                       (<= x58 n5)))) 
                           (forall ((x60 Int) (x61 A) (x62 A)) 
                               (=> 
                                   (and 
                                       (MS x60 x61 s6) 
                                       (MS x60 x62 s6)) 
                                   (= x61 x62))) 
                           (forall ((x63 Int)) 
                               (=> 
                                   (and 
                                       (<= 1 x63) 
                                       (<= x63 n5)) 
                                   (exists ((x64 A)) 
                                       (MS x63 x64 s6)))))) 
                   (and 
                       (forall ((x65 Int) (x66 A)) 
                           (=> 
                               (MS x65 x66 s6) 
                               (and 
                                   (<= 1 x65) 
                                   (forall ((x67 Int)) 
                                       (=> 
                                           (length s6 x67) 
                                           (<= x65 x67)))))) 
                       (forall ((x68 Int) (x69 A) (x70 A)) 
                           (=> 
                               (and 
                                   (MS x68 x69 s6) 
                                   (MS x68 x70 s6)) 
                               (= x69 x70))) 
                       (forall ((x71 Int)) 
                           (=> 
                               (and 
                                   (<= 1 x71) 
                                   (forall ((x72 Int)) 
                                       (=> 
                                           (length s6 x72) 
                                           (<= x71 x72)))) 
                               (exists ((x73 A)) 
                                   (MS x71 x73 s6)))))))
         :named hyp6))
(assert (! (forall ((x74 PZA) (x75 PZA) (x76 PZA)) 
               (= 
                   (cnc x74 x75 x76) 
                   (exists ((s10 PZA) (s20 PZA)) 
                       (and 
                           (exists ((n6 Int)) 
                               (and 
                                   (<= 0 n6) 
                                   (forall ((x77 Int) (x78 A)) 
                                       (=> 
                                           (MS x77 x78 s10) 
                                           (and 
                                               (<= 1 x77) 
                                               (<= x77 n6)))) 
                                   (forall ((x79 Int) (x80 A) (x81 A)) 
                                       (=> 
                                           (and 
                                               (MS x79 x80 s10) 
                                               (MS x79 x81 s10)) 
                                           (= x80 x81))) 
                                   (forall ((x82 Int)) 
                                       (=> 
                                           (and 
                                               (<= 1 x82) 
                                               (<= x82 n6)) 
                                           (exists ((x83 A)) 
                                               (MS x82 x83 s10)))))) 
                           (exists ((n7 Int)) 
                               (and 
                                   (<= 0 n7) 
                                   (forall ((x84 Int) (x85 A)) 
                                       (=> 
                                           (MS x84 x85 s20) 
                                           (and 
                                               (<= 1 x84) 
                                               (<= x84 n7)))) 
                                   (forall ((x86 Int) (x87 A) (x88 A)) 
                                       (=> 
                                           (and 
                                               (MS x86 x87 s20) 
                                               (MS x86 x88 s20)) 
                                           (= x87 x88))) 
                                   (forall ((x89 Int)) 
                                       (=> 
                                           (and 
                                               (<= 1 x89) 
                                               (<= x89 n7)) 
                                           (exists ((x90 A)) 
                                               (MS x89 x90 s20)))))) 
                           (forall ((x91 Int) (x92 A)) 
                               (= 
                                   (MS x91 x92 x74) 
                                   (MS x91 x92 s10))) 
                           (forall ((x93 Int) (x94 A)) 
                               (= 
                                   (MS x93 x94 x75) 
                                   (MS x93 x94 s20))) 
                           (forall ((x95 Int) (x96 A)) 
                               (= 
                                   (MS x95 x96 x76) 
                                   (or 
                                       (exists ((i0 Int)) 
                                           (and 
                                               (<= 1 i0) 
                                               (forall ((x97 Int)) 
                                                   (=> 
                                                       (length s10 x97) 
                                                       (<= i0 x97))) 
                                               (= x95 i0) 
                                               (MS i0 x96 s10))) 
                                       (exists ((i1 Int)) 
                                           (and 
                                               (forall ((x98 Int)) 
                                                   (=> 
                                                       (length s10 x98) 
                                                       (<= (+ x98 1) i1))) 
                                               (forall ((x99 Int) (x100 Int)) 
                                                   (=> 
                                                       (and 
                                                           (length s10 x100) 
                                                           (length s20 x99)) 
                                                       (<= i1 (+ x100 x99)))) 
                                               (= x95 i1) 
                                               (exists ((x101 Int)) 
                                                   (and 
                                                       (forall ((x102 Int)) 
                                                           (=> 
                                                               (length s10 x102) 
                                                               (= x101 (- i1 x102)))) 
                                                       (MS x101 x96 s20))))))))))))
         :named hyp7))
(assert (! (exists ((n8 Int)) 
               (and 
                   (<= 0 n8) 
                   (forall ((x103 Int) (x104 A)) 
                       (=> 
                           (MS x103 x104 s1) 
                           (and 
                               (<= 1 x103) 
                               (<= x103 n8)))) 
                   (forall ((x105 Int) (x106 A) (x107 A)) 
                       (=> 
                           (and 
                               (MS x105 x106 s1) 
                               (MS x105 x107 s1)) 
                           (= x106 x107))) 
                   (forall ((x108 Int)) 
                       (=> 
                           (and 
                               (<= 1 x108) 
                               (<= x108 n8)) 
                           (exists ((x109 A)) 
                               (MS x108 x109 s1))))))
         :named hyp8))
(assert (! (exists ((n9 Int)) 
               (and 
                   (<= 0 n9) 
                   (forall ((x110 Int) (x111 A)) 
                       (=> 
                           (MS x110 x111 s2) 
                           (and 
                               (<= 1 x110) 
                               (<= x110 n9)))) 
                   (forall ((x112 Int) (x113 A) (x114 A)) 
                       (=> 
                           (and 
                               (MS x112 x113 s2) 
                               (MS x112 x114 s2)) 
                           (= x113 x114))) 
                   (forall ((x115 Int)) 
                       (=> 
                           (and 
                               (<= 1 x115) 
                               (<= x115 n9)) 
                           (exists ((x116 A)) 
                               (MS x115 x116 s2))))))
         :named hyp9))
(assert (! (and 
               (forall ((x117 PZA) (x118 PZA) (x119 PZA)) 
                   (=> 
                       (exists ((s11 PZA) (s21 PZA)) 
                           (and 
                               (exists ((n10 Int)) 
                                   (and 
                                       (<= 0 n10) 
                                       (forall ((x120 Int) (x121 A)) 
                                           (=> 
                                               (MS x120 x121 s11) 
                                               (and 
                                                   (<= 1 x120) 
                                                   (<= x120 n10)))) 
                                       (forall ((x122 Int) (x123 A) (x124 A)) 
                                           (=> 
                                               (and 
                                                   (MS x122 x123 s11) 
                                                   (MS x122 x124 s11)) 
                                               (= x123 x124))) 
                                       (forall ((x125 Int)) 
                                           (=> 
                                               (and 
                                                   (<= 1 x125) 
                                                   (<= x125 n10)) 
                                               (exists ((x126 A)) 
                                                   (MS x125 x126 s11)))))) 
                               (exists ((n11 Int)) 
                                   (and 
                                       (<= 0 n11) 
                                       (forall ((x127 Int) (x128 A)) 
                                           (=> 
                                               (MS x127 x128 s21) 
                                               (and 
                                                   (<= 1 x127) 
                                                   (<= x127 n11)))) 
                                       (forall ((x129 Int) (x130 A) (x131 A)) 
                                           (=> 
                                               (and 
                                                   (MS x129 x130 s21) 
                                                   (MS x129 x131 s21)) 
                                               (= x130 x131))) 
                                       (forall ((x132 Int)) 
                                           (=> 
                                               (and 
                                                   (<= 1 x132) 
                                                   (<= x132 n11)) 
                                               (exists ((x133 A)) 
                                                   (MS x132 x133 s21)))))) 
                               (forall ((x134 Int) (x135 A)) 
                                   (= 
                                       (MS x134 x135 x117) 
                                       (MS x134 x135 s11))) 
                               (forall ((x136 Int) (x137 A)) 
                                   (= 
                                       (MS x136 x137 x118) 
                                       (MS x136 x137 s21))) 
                               (forall ((x138 Int) (x139 A)) 
                                   (= 
                                       (MS x138 x139 x119) 
                                       (or 
                                           (exists ((i2 Int)) 
                                               (and 
                                                   (<= 1 i2) 
                                                   (forall ((x140 Int)) 
                                                       (=> 
                                                           (length s11 x140) 
                                                           (<= i2 x140))) 
                                                   (= x138 i2) 
                                                   (MS i2 x139 s11))) 
                                           (exists ((i3 Int)) 
                                               (and 
                                                   (forall ((x141 Int)) 
                                                       (=> 
                                                           (length s11 x141) 
                                                           (<= (+ x141 1) i3))) 
                                                   (forall ((x142 Int) (x143 Int)) 
                                                       (=> 
                                                           (and 
                                                               (length s11 x143) 
                                                               (length s21 x142)) 
                                                           (<= i3 (+ x143 x142)))) 
                                                   (= x138 i3) 
                                                   (exists ((x144 Int)) 
                                                       (and 
                                                           (forall ((x145 Int)) 
                                                               (=> 
                                                                   (length s11 x145) 
                                                                   (= x144 (- i3 x145)))) 
                                                           (MS x144 x139 s21)))))))))) 
                       (and 
                           (exists ((s7 PZA)) 
                               (and 
                                   (exists ((n12 Int)) 
                                       (and 
                                           (<= 0 n12) 
                                           (forall ((x146 Int) (x147 A)) 
                                               (=> 
                                                   (MS x146 x147 s7) 
                                                   (and 
                                                       (<= 1 x146) 
                                                       (<= x146 n12)))) 
                                           (forall ((x148 Int) (x149 A) (x150 A)) 
                                               (=> 
                                                   (and 
                                                       (MS x148 x149 s7) 
                                                       (MS x148 x150 s7)) 
                                                   (= x149 x150))) 
                                           (forall ((x151 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x151) 
                                                       (<= x151 n12)) 
                                                   (exists ((x152 A)) 
                                                       (MS x151 x152 s7)))))) 
                                   (forall ((x153 Int) (x154 A)) 
                                       (= 
                                           (MS x153 x154 x117) 
                                           (MS x153 x154 s7))))) 
                           (exists ((s8 PZA)) 
                               (and 
                                   (exists ((n13 Int)) 
                                       (and 
                                           (<= 0 n13) 
                                           (forall ((x155 Int) (x156 A)) 
                                               (=> 
                                                   (MS x155 x156 s8) 
                                                   (and 
                                                       (<= 1 x155) 
                                                       (<= x155 n13)))) 
                                           (forall ((x157 Int) (x158 A) (x159 A)) 
                                               (=> 
                                                   (and 
                                                       (MS x157 x158 s8) 
                                                       (MS x157 x159 s8)) 
                                                   (= x158 x159))) 
                                           (forall ((x160 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x160) 
                                                       (<= x160 n13)) 
                                                   (exists ((x161 A)) 
                                                       (MS x160 x161 s8)))))) 
                                   (forall ((x162 Int) (x163 A)) 
                                       (= 
                                           (MS x162 x163 x118) 
                                           (MS x162 x163 s8))))) 
                           (exists ((s9 PZA)) 
                               (and 
                                   (exists ((n14 Int)) 
                                       (and 
                                           (<= 0 n14) 
                                           (forall ((x164 Int) (x165 A)) 
                                               (=> 
                                                   (MS x164 x165 s9) 
                                                   (and 
                                                       (<= 1 x164) 
                                                       (<= x164 n14)))) 
                                           (forall ((x166 Int) (x167 A) (x168 A)) 
                                               (=> 
                                                   (and 
                                                       (MS x166 x167 s9) 
                                                       (MS x166 x168 s9)) 
                                                   (= x167 x168))) 
                                           (forall ((x169 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x169) 
                                                       (<= x169 n14)) 
                                                   (exists ((x170 A)) 
                                                       (MS x169 x170 s9)))))) 
                                   (forall ((x171 Int) (x172 A)) 
                                       (= 
                                           (MS x171 x172 x119) 
                                           (MS x171 x172 s9)))))))) 
               (forall ((x173 PZA) (x174 PZA) (x175 PZA) (x176 PZA)) 
                   (=> 
                       (and 
                           (exists ((s12 PZA) (s22 PZA)) 
                               (and 
                                   (exists ((n15 Int)) 
                                       (and 
                                           (<= 0 n15) 
                                           (forall ((x177 Int) (x178 A)) 
                                               (=> 
                                                   (MS x177 x178 s12) 
                                                   (and 
                                                       (<= 1 x177) 
                                                       (<= x177 n15)))) 
                                           (forall ((x179 Int) (x180 A) (x181 A)) 
                                               (=> 
                                                   (and 
                                                       (MS x179 x180 s12) 
                                                       (MS x179 x181 s12)) 
                                                   (= x180 x181))) 
                                           (forall ((x182 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x182) 
                                                       (<= x182 n15)) 
                                                   (exists ((x183 A)) 
                                                       (MS x182 x183 s12)))))) 
                                   (exists ((n16 Int)) 
                                       (and 
                                           (<= 0 n16) 
                                           (forall ((x184 Int) (x185 A)) 
                                               (=> 
                                                   (MS x184 x185 s22) 
                                                   (and 
                                                       (<= 1 x184) 
                                                       (<= x184 n16)))) 
                                           (forall ((x186 Int) (x187 A) (x188 A)) 
                                               (=> 
                                                   (and 
                                                       (MS x186 x187 s22) 
                                                       (MS x186 x188 s22)) 
                                                   (= x187 x188))) 
                                           (forall ((x189 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x189) 
                                                       (<= x189 n16)) 
                                                   (exists ((x190 A)) 
                                                       (MS x189 x190 s22)))))) 
                                   (forall ((x191 Int) (x192 A)) 
                                       (= 
                                           (MS x191 x192 x173) 
                                           (MS x191 x192 s12))) 
                                   (forall ((x193 Int) (x194 A)) 
                                       (= 
                                           (MS x193 x194 x174) 
                                           (MS x193 x194 s22))) 
                                   (forall ((x195 Int) (x196 A)) 
                                       (= 
                                           (MS x195 x196 x175) 
                                           (or 
                                               (exists ((i4 Int)) 
                                                   (and 
                                                       (<= 1 i4) 
                                                       (forall ((x197 Int)) 
                                                           (=> 
                                                               (length s12 x197) 
                                                               (<= i4 x197))) 
                                                       (= x195 i4) 
                                                       (MS i4 x196 s12))) 
                                               (exists ((i5 Int)) 
                                                   (and 
                                                       (forall ((x198 Int)) 
                                                           (=> 
                                                               (length s12 x198) 
                                                               (<= (+ x198 1) i5))) 
                                                       (forall ((x199 Int) (x200 Int)) 
                                                           (=> 
                                                               (and 
                                                                   (length s12 x200) 
                                                                   (length s22 x199)) 
                                                               (<= i5 (+ x200 x199)))) 
                                                       (= x195 i5) 
                                                       (exists ((x201 Int)) 
                                                           (and 
                                                               (forall ((x202 Int)) 
                                                                   (=> 
                                                                       (length s12 x202) 
                                                                       (= x201 (- i5 x202)))) 
                                                               (MS x201 x196 s22)))))))))) 
                           (exists ((s13 PZA) (s23 PZA)) 
                               (and 
                                   (exists ((n17 Int)) 
                                       (and 
                                           (<= 0 n17) 
                                           (forall ((x203 Int) (x204 A)) 
                                               (=> 
                                                   (MS x203 x204 s13) 
                                                   (and 
                                                       (<= 1 x203) 
                                                       (<= x203 n17)))) 
                                           (forall ((x205 Int) (x206 A) (x207 A)) 
                                               (=> 
                                                   (and 
                                                       (MS x205 x206 s13) 
                                                       (MS x205 x207 s13)) 
                                                   (= x206 x207))) 
                                           (forall ((x208 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x208) 
                                                       (<= x208 n17)) 
                                                   (exists ((x209 A)) 
                                                       (MS x208 x209 s13)))))) 
                                   (exists ((n18 Int)) 
                                       (and 
                                           (<= 0 n18) 
                                           (forall ((x210 Int) (x211 A)) 
                                               (=> 
                                                   (MS x210 x211 s23) 
                                                   (and 
                                                       (<= 1 x210) 
                                                       (<= x210 n18)))) 
                                           (forall ((x212 Int) (x213 A) (x214 A)) 
                                               (=> 
                                                   (and 
                                                       (MS x212 x213 s23) 
                                                       (MS x212 x214 s23)) 
                                                   (= x213 x214))) 
                                           (forall ((x215 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x215) 
                                                       (<= x215 n18)) 
                                                   (exists ((x216 A)) 
                                                       (MS x215 x216 s23)))))) 
                                   (forall ((x217 Int) (x218 A)) 
                                       (= 
                                           (MS x217 x218 x173) 
                                           (MS x217 x218 s13))) 
                                   (forall ((x219 Int) (x220 A)) 
                                       (= 
                                           (MS x219 x220 x174) 
                                           (MS x219 x220 s23))) 
                                   (forall ((x221 Int) (x222 A)) 
                                       (= 
                                           (MS x221 x222 x176) 
                                           (or 
                                               (exists ((i6 Int)) 
                                                   (and 
                                                       (<= 1 i6) 
                                                       (forall ((x223 Int)) 
                                                           (=> 
                                                               (length s13 x223) 
                                                               (<= i6 x223))) 
                                                       (= x221 i6) 
                                                       (MS i6 x222 s13))) 
                                               (exists ((i7 Int)) 
                                                   (and 
                                                       (forall ((x224 Int)) 
                                                           (=> 
                                                               (length s13 x224) 
                                                               (<= (+ x224 1) i7))) 
                                                       (forall ((x225 Int) (x226 Int)) 
                                                           (=> 
                                                               (and 
                                                                   (length s13 x226) 
                                                                   (length s23 x225)) 
                                                               (<= i7 (+ x226 x225)))) 
                                                       (= x221 i7) 
                                                       (exists ((x227 Int)) 
                                                           (and 
                                                               (forall ((x228 Int)) 
                                                                   (=> 
                                                                       (length s13 x228) 
                                                                       (= x227 (- i7 x228)))) 
                                                               (MS x227 x222 s23))))))))))) 
                       (forall ((x229 Int) (x230 A)) 
                           (= 
                               (MS x229 x230 x175) 
                               (MS x229 x230 x176))))) 
               (forall ((x231 PZA) (x232 PZA)) 
                   (=> 
                       (and 
                           (exists ((s14 PZA)) 
                               (and 
                                   (exists ((n19 Int)) 
                                       (and 
                                           (<= 0 n19) 
                                           (forall ((x233 Int) (x234 A)) 
                                               (=> 
                                                   (MS x233 x234 s14) 
                                                   (and 
                                                       (<= 1 x233) 
                                                       (<= x233 n19)))) 
                                           (forall ((x235 Int) (x236 A) (x237 A)) 
                                               (=> 
                                                   (and 
                                                       (MS x235 x236 s14) 
                                                       (MS x235 x237 s14)) 
                                                   (= x236 x237))) 
                                           (forall ((x238 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x238) 
                                                       (<= x238 n19)) 
                                                   (exists ((x239 A)) 
                                                       (MS x238 x239 s14)))))) 
                                   (forall ((x240 Int) (x241 A)) 
                                       (= 
                                           (MS x240 x241 x231) 
                                           (MS x240 x241 s14))))) 
                           (exists ((s15 PZA)) 
                               (and 
                                   (exists ((n20 Int)) 
                                       (and 
                                           (<= 0 n20) 
                                           (forall ((x242 Int) (x243 A)) 
                                               (=> 
                                                   (MS x242 x243 s15) 
                                                   (and 
                                                       (<= 1 x242) 
                                                       (<= x242 n20)))) 
                                           (forall ((x244 Int) (x245 A) (x246 A)) 
                                               (=> 
                                                   (and 
                                                       (MS x244 x245 s15) 
                                                       (MS x244 x246 s15)) 
                                                   (= x245 x246))) 
                                           (forall ((x247 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x247) 
                                                       (<= x247 n20)) 
                                                   (exists ((x248 A)) 
                                                       (MS x247 x248 s15)))))) 
                                   (forall ((x249 Int) (x250 A)) 
                                       (= 
                                           (MS x249 x250 x232) 
                                           (MS x249 x250 s15)))))) 
                       (exists ((x251 PZA) (s16 PZA) (s24 PZA)) 
                           (and 
                               (exists ((n21 Int)) 
                                   (and 
                                       (<= 0 n21) 
                                       (forall ((x252 Int) (x253 A)) 
                                           (=> 
                                               (MS x252 x253 s16) 
                                               (and 
                                                   (<= 1 x252) 
                                                   (<= x252 n21)))) 
                                       (forall ((x254 Int) (x255 A) (x256 A)) 
                                           (=> 
                                               (and 
                                                   (MS x254 x255 s16) 
                                                   (MS x254 x256 s16)) 
                                               (= x255 x256))) 
                                       (forall ((x257 Int)) 
                                           (=> 
                                               (and 
                                                   (<= 1 x257) 
                                                   (<= x257 n21)) 
                                               (exists ((x258 A)) 
                                                   (MS x257 x258 s16)))))) 
                               (exists ((n22 Int)) 
                                   (and 
                                       (<= 0 n22) 
                                       (forall ((x259 Int) (x260 A)) 
                                           (=> 
                                               (MS x259 x260 s24) 
                                               (and 
                                                   (<= 1 x259) 
                                                   (<= x259 n22)))) 
                                       (forall ((x261 Int) (x262 A) (x263 A)) 
                                           (=> 
                                               (and 
                                                   (MS x261 x262 s24) 
                                                   (MS x261 x263 s24)) 
                                               (= x262 x263))) 
                                       (forall ((x264 Int)) 
                                           (=> 
                                               (and 
                                                   (<= 1 x264) 
                                                   (<= x264 n22)) 
                                               (exists ((x265 A)) 
                                                   (MS x264 x265 s24)))))) 
                               (forall ((x266 Int) (x267 A)) 
                                   (= 
                                       (MS x266 x267 x231) 
                                       (MS x266 x267 s16))) 
                               (forall ((x268 Int) (x269 A)) 
                                   (= 
                                       (MS x268 x269 x232) 
                                       (MS x268 x269 s24))) 
                               (forall ((x270 Int) (x271 A)) 
                                   (= 
                                       (MS x270 x271 x251) 
                                       (or 
                                           (exists ((i8 Int)) 
                                               (and 
                                                   (<= 1 i8) 
                                                   (forall ((x272 Int)) 
                                                       (=> 
                                                           (length s16 x272) 
                                                           (<= i8 x272))) 
                                                   (= x270 i8) 
                                                   (MS i8 x271 s16))) 
                                           (exists ((i9 Int)) 
                                               (and 
                                                   (forall ((x273 Int)) 
                                                       (=> 
                                                           (length s16 x273) 
                                                           (<= (+ x273 1) i9))) 
                                                   (forall ((x274 Int) (x275 Int)) 
                                                       (=> 
                                                           (and 
                                                               (length s16 x275) 
                                                               (length s24 x274)) 
                                                           (<= i9 (+ x275 x274)))) 
                                                   (= x270 i9) 
                                                   (exists ((x276 Int)) 
                                                       (and 
                                                           (forall ((x277 Int)) 
                                                               (=> 
                                                                   (length s16 x277) 
                                                                   (= x276 (- i9 x277)))) 
                                                           (MS x276 x271 s24)))))))))))))
         :named hyp10))
(assert (! (forall ((s17 PZA) (s25 PZA)) 
               (=> 
                   (and 
                       (exists ((n23 Int)) 
                           (and 
                               (<= 0 n23) 
                               (forall ((x278 Int) (x279 A)) 
                                   (=> 
                                       (MS x278 x279 s17) 
                                       (and 
                                           (<= 1 x278) 
                                           (<= x278 n23)))) 
                               (forall ((x280 Int) (x281 A) (x282 A)) 
                                   (=> 
                                       (and 
                                           (MS x280 x281 s17) 
                                           (MS x280 x282 s17)) 
                                       (= x281 x282))) 
                               (forall ((x283 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x283) 
                                           (<= x283 n23)) 
                                       (exists ((x284 A)) 
                                           (MS x283 x284 s17)))))) 
                       (exists ((n24 Int)) 
                           (and 
                               (<= 0 n24) 
                               (forall ((x285 Int) (x286 A)) 
                                   (=> 
                                       (MS x285 x286 s25) 
                                       (and 
                                           (<= 1 x285) 
                                           (<= x285 n24)))) 
                               (forall ((x287 Int) (x288 A) (x289 A)) 
                                   (=> 
                                       (and 
                                           (MS x287 x288 s25) 
                                           (MS x287 x289 s25)) 
                                       (= x288 x289))) 
                               (forall ((x290 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x290) 
                                           (<= x290 n24)) 
                                       (exists ((x291 A)) 
                                           (MS x290 x291 s25))))))) 
                   (exists ((x292 PZA) (x293 Int)) 
                       (and 
                           (forall ((x294 Int) (x295 A)) 
                               (= 
                                   (MS x294 x295 x292) 
                                   (or 
                                       (exists ((i10 Int)) 
                                           (and 
                                               (<= 1 i10) 
                                               (forall ((x296 Int)) 
                                                   (=> 
                                                       (length s17 x296) 
                                                       (<= i10 x296))) 
                                               (= x294 i10) 
                                               (MS i10 x295 s17))) 
                                       (exists ((i11 Int)) 
                                           (and 
                                               (forall ((x297 Int)) 
                                                   (=> 
                                                       (length s17 x297) 
                                                       (<= (+ x297 1) i11))) 
                                               (forall ((x298 Int) (x299 Int)) 
                                                   (=> 
                                                       (and 
                                                           (length s17 x299) 
                                                           (length s25 x298)) 
                                                       (<= i11 (+ x299 x298)))) 
                                               (= x294 i11) 
                                               (exists ((x300 Int)) 
                                                   (and 
                                                       (forall ((x301 Int)) 
                                                           (=> 
                                                               (length s17 x301) 
                                                               (= x300 (- i11 x301)))) 
                                                       (MS x300 x295 s25)))))))) 
                           (forall ((x302 Int) (x303 Int)) 
                               (=> 
                                   (and 
                                       (length s17 x303) 
                                       (length s25 x302)) 
                                   (= x293 (+ x303 x302)))) 
                           (length x292 x293)))))
         :named hyp11))
(assert (! (forall ((s18 PZA) (s26 PZA)) 
               (=> 
                   (and 
                       (exists ((n25 Int)) 
                           (and 
                               (<= 0 n25) 
                               (forall ((x304 Int) (x305 A)) 
                                   (=> 
                                       (MS x304 x305 s18) 
                                       (and 
                                           (<= 1 x304) 
                                           (<= x304 n25)))) 
                               (forall ((x306 Int) (x307 A) (x308 A)) 
                                   (=> 
                                       (and 
                                           (MS x306 x307 s18) 
                                           (MS x306 x308 s18)) 
                                       (= x307 x308))) 
                               (forall ((x309 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x309) 
                                           (<= x309 n25)) 
                                       (exists ((x310 A)) 
                                           (MS x309 x310 s18)))))) 
                       (exists ((n26 Int)) 
                           (and 
                               (<= 0 n26) 
                               (forall ((x311 Int) (x312 A)) 
                                   (=> 
                                       (MS x311 x312 s26) 
                                       (and 
                                           (<= 1 x311) 
                                           (<= x311 n26)))) 
                               (forall ((x313 Int) (x314 A) (x315 A)) 
                                   (=> 
                                       (and 
                                           (MS x313 x314 s26) 
                                           (MS x313 x315 s26)) 
                                       (= x314 x315))) 
                               (forall ((x316 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x316) 
                                           (<= x316 n26)) 
                                       (exists ((x317 A)) 
                                           (MS x316 x317 s26))))))) 
                   (forall ((x318 Int)) 
                       (= 
                           (or 
                               (exists ((x319 A)) 
                                   (exists ((i12 Int)) 
                                       (and 
                                           (<= 1 i12) 
                                           (forall ((x320 Int)) 
                                               (=> 
                                                   (length s18 x320) 
                                                   (<= i12 x320))) 
                                           (= x318 i12) 
                                           (MS i12 x319 s18)))) 
                               (exists ((x321 A)) 
                                   (exists ((i13 Int)) 
                                       (and 
                                           (forall ((x322 Int)) 
                                               (=> 
                                                   (length s18 x322) 
                                                   (<= (+ x322 1) i13))) 
                                           (forall ((x323 Int) (x324 Int)) 
                                               (=> 
                                                   (and 
                                                       (length s18 x324) 
                                                       (length s26 x323)) 
                                                   (<= i13 (+ x324 x323)))) 
                                           (= x318 i13) 
                                           (exists ((x325 Int)) 
                                               (and 
                                                   (forall ((x326 Int)) 
                                                       (=> 
                                                           (length s18 x326) 
                                                           (= x325 (- i13 x326)))) 
                                                   (MS x325 x321 s26))))))) 
                           (and 
                               (<= 1 x318) 
                               (forall ((x327 Int) (x328 Int)) 
                                   (=> 
                                       (and 
                                           (length s18 x328) 
                                           (length s26 x327)) 
                                       (<= x318 (+ x328 x327)))))))))
         :named hyp12))
(assert (! (forall ((s19 PZA) (s27 PZA)) 
               (=> 
                   (and 
                       (exists ((n27 Int)) 
                           (and 
                               (<= 0 n27) 
                               (forall ((x329 Int) (x330 A)) 
                                   (=> 
                                       (MS x329 x330 s19) 
                                       (and 
                                           (<= 1 x329) 
                                           (<= x329 n27)))) 
                               (forall ((x331 Int) (x332 A) (x333 A)) 
                                   (=> 
                                       (and 
                                           (MS x331 x332 s19) 
                                           (MS x331 x333 s19)) 
                                       (= x332 x333))) 
                               (forall ((x334 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x334) 
                                           (<= x334 n27)) 
                                       (exists ((x335 A)) 
                                           (MS x334 x335 s19)))))) 
                       (exists ((n28 Int)) 
                           (and 
                               (<= 0 n28) 
                               (forall ((x336 Int) (x337 A)) 
                                   (=> 
                                       (MS x336 x337 s27) 
                                       (and 
                                           (<= 1 x336) 
                                           (<= x336 n28)))) 
                               (forall ((x338 Int) (x339 A) (x340 A)) 
                                   (=> 
                                       (and 
                                           (MS x338 x339 s27) 
                                           (MS x338 x340 s27)) 
                                       (= x339 x340))) 
                               (forall ((x341 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x341) 
                                           (<= x341 n28)) 
                                       (exists ((x342 A)) 
                                           (MS x341 x342 s27))))))) 
                   (forall ((x343 A)) 
                       (= 
                           (or 
                               (exists ((x344 Int)) 
                                   (exists ((i14 Int)) 
                                       (and 
                                           (<= 1 i14) 
                                           (forall ((x345 Int)) 
                                               (=> 
                                                   (length s19 x345) 
                                                   (<= i14 x345))) 
                                           (= x344 i14) 
                                           (MS i14 x343 s19)))) 
                               (exists ((x346 Int)) 
                                   (exists ((i15 Int)) 
                                       (and 
                                           (forall ((x347 Int)) 
                                               (=> 
                                                   (length s19 x347) 
                                                   (<= (+ x347 1) i15))) 
                                           (forall ((x348 Int) (x349 Int)) 
                                               (=> 
                                                   (and 
                                                       (length s19 x349) 
                                                       (length s27 x348)) 
                                                   (<= i15 (+ x349 x348)))) 
                                           (= x346 i15) 
                                           (exists ((x350 Int)) 
                                               (and 
                                                   (forall ((x351 Int)) 
                                                       (=> 
                                                           (length s19 x351) 
                                                           (= x350 (- i15 x351)))) 
                                                   (MS x350 x343 s27))))))) 
                           (or 
                               (exists ((x352 Int)) 
                                   (MS x352 x343 s19)) 
                               (exists ((x353 Int)) 
                                   (MS x353 x343 s27)))))))
         :named hyp13))
(assert (! (forall ((s110 PZA) (s28 PZA) (i16 Int)) 
               (=> 
                   (and 
                       (exists ((n29 Int)) 
                           (and 
                               (<= 0 n29) 
                               (forall ((x354 Int) (x355 A)) 
                                   (=> 
                                       (MS x354 x355 s110) 
                                       (and 
                                           (<= 1 x354) 
                                           (<= x354 n29)))) 
                               (forall ((x356 Int) (x357 A) (x358 A)) 
                                   (=> 
                                       (and 
                                           (MS x356 x357 s110) 
                                           (MS x356 x358 s110)) 
                                       (= x357 x358))) 
                               (forall ((x359 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x359) 
                                           (<= x359 n29)) 
                                       (exists ((x360 A)) 
                                           (MS x359 x360 s110)))))) 
                       (exists ((n30 Int)) 
                           (and 
                               (<= 0 n30) 
                               (forall ((x361 Int) (x362 A)) 
                                   (=> 
                                       (MS x361 x362 s28) 
                                       (and 
                                           (<= 1 x361) 
                                           (<= x361 n30)))) 
                               (forall ((x363 Int) (x364 A) (x365 A)) 
                                   (=> 
                                       (and 
                                           (MS x363 x364 s28) 
                                           (MS x363 x365 s28)) 
                                       (= x364 x365))) 
                               (forall ((x366 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x366) 
                                           (<= x366 n30)) 
                                       (exists ((x367 A)) 
                                           (MS x366 x367 s28)))))) 
                       (<= 1 i16) 
                       (forall ((x368 Int)) 
                           (=> 
                               (length s110 x368) 
                               (<= i16 x368)))) 
                   (or 
                       (exists ((i17 Int)) 
                           (and 
                               (<= 1 i17) 
                               (forall ((x369 Int)) 
                                   (=> 
                                       (length s110 x369) 
                                       (<= i17 x369))) 
                               (= i16 i17) 
                               (exists ((x370 A)) 
                                   (and 
                                       (MS i17 x370 s110) 
                                       (MS i16 x370 s110))))) 
                       (exists ((i18 Int)) 
                           (and 
                               (forall ((x371 Int)) 
                                   (=> 
                                       (length s110 x371) 
                                       (<= (+ x371 1) i18))) 
                               (forall ((x372 Int) (x373 Int)) 
                                   (=> 
                                       (and 
                                           (length s110 x373) 
                                           (length s28 x372)) 
                                       (<= i18 (+ x373 x372)))) 
                               (= i16 i18) 
                               (exists ((x374 A)) 
                                   (and 
                                       (exists ((x375 Int)) 
                                           (and 
                                               (forall ((x376 Int)) 
                                                   (=> 
                                                       (length s110 x376) 
                                                       (= x375 (- i18 x376)))) 
                                               (MS x375 x374 s28))) 
                                       (MS i16 x374 s110))))))))
         :named hyp14))
(assert (! (forall ((s111 PZA) (s29 PZA) (b PA)) 
               (=> 
                   (and 
                       (exists ((n31 Int)) 
                           (and 
                               (<= 0 n31) 
                               (forall ((x377 Int) (x378 A)) 
                                   (=> 
                                       (MS x377 x378 s111) 
                                       (and 
                                           (<= 1 x377) 
                                           (<= x377 n31)))) 
                               (forall ((x379 Int) (x380 A) (x381 A)) 
                                   (=> 
                                       (and 
                                           (MS x379 x380 s111) 
                                           (MS x379 x381 s111)) 
                                       (= x380 x381))) 
                               (forall ((x382 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x382) 
                                           (<= x382 n31)) 
                                       (exists ((x383 A)) 
                                           (MS x382 x383 s111)))))) 
                       (exists ((n32 Int)) 
                           (and 
                               (<= 0 n32) 
                               (forall ((x384 Int) (x385 A)) 
                                   (=> 
                                       (MS x384 x385 s29) 
                                       (and 
                                           (<= 1 x384) 
                                           (<= x384 n32)))) 
                               (forall ((x386 Int) (x387 A) (x388 A)) 
                                   (=> 
                                       (and 
                                           (MS x386 x387 s29) 
                                           (MS x386 x388 s29)) 
                                       (= x387 x388))) 
                               (forall ((x389 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x389) 
                                           (<= x389 n32)) 
                                       (exists ((x390 A)) 
                                           (MS x389 x390 s29)))))) 
                       (forall ((x391 A)) 
                           (=> 
                               (exists ((x392 Int)) 
                                   (MS x392 x391 s111)) 
                               (MS0 x391 b))) 
                       (forall ((x393 A)) 
                           (=> 
                               (exists ((x394 Int)) 
                                   (MS x394 x393 s29)) 
                               (MS0 x393 b)))) 
                   (and 
                       (forall ((x395 Int) (x396 A)) 
                           (=> 
                               (or 
                                   (exists ((i19 Int)) 
                                       (and 
                                           (<= 1 i19) 
                                           (forall ((x397 Int)) 
                                               (=> 
                                                   (length s111 x397) 
                                                   (<= i19 x397))) 
                                           (= x395 i19) 
                                           (MS i19 x396 s111))) 
                                   (exists ((i20 Int)) 
                                       (and 
                                           (forall ((x398 Int)) 
                                               (=> 
                                                   (length s111 x398) 
                                                   (<= (+ x398 1) i20))) 
                                           (forall ((x399 Int) (x400 Int)) 
                                               (=> 
                                                   (and 
                                                       (length s111 x400) 
                                                       (length s29 x399)) 
                                                   (<= i20 (+ x400 x399)))) 
                                           (= x395 i20) 
                                           (exists ((x401 Int)) 
                                               (and 
                                                   (forall ((x402 Int)) 
                                                       (=> 
                                                           (length s111 x402) 
                                                           (= x401 (- i20 x402)))) 
                                                   (MS x401 x396 s29)))))) 
                               (and 
                                   (<= 1 x395) 
                                   (forall ((x403 Int) (x404 Int)) 
                                       (=> 
                                           (and 
                                               (length s111 x404) 
                                               (length s29 x403)) 
                                           (<= x395 (+ x404 x403)))) 
                                   (MS0 x396 b)))) 
                       (forall ((x405 Int) (x406 A) (x407 A)) 
                           (=> 
                               (and 
                                   (or 
                                       (exists ((i21 Int)) 
                                           (and 
                                               (<= 1 i21) 
                                               (forall ((x408 Int)) 
                                                   (=> 
                                                       (length s111 x408) 
                                                       (<= i21 x408))) 
                                               (= x405 i21) 
                                               (MS i21 x406 s111))) 
                                       (exists ((i22 Int)) 
                                           (and 
                                               (forall ((x409 Int)) 
                                                   (=> 
                                                       (length s111 x409) 
                                                       (<= (+ x409 1) i22))) 
                                               (forall ((x410 Int) (x411 Int)) 
                                                   (=> 
                                                       (and 
                                                           (length s111 x411) 
                                                           (length s29 x410)) 
                                                       (<= i22 (+ x411 x410)))) 
                                               (= x405 i22) 
                                               (exists ((x412 Int)) 
                                                   (and 
                                                       (forall ((x413 Int)) 
                                                           (=> 
                                                               (length s111 x413) 
                                                               (= x412 (- i22 x413)))) 
                                                       (MS x412 x406 s29)))))) 
                                   (or 
                                       (exists ((i23 Int)) 
                                           (and 
                                               (<= 1 i23) 
                                               (forall ((x414 Int)) 
                                                   (=> 
                                                       (length s111 x414) 
                                                       (<= i23 x414))) 
                                               (= x405 i23) 
                                               (MS i23 x407 s111))) 
                                       (exists ((i24 Int)) 
                                           (and 
                                               (forall ((x415 Int)) 
                                                   (=> 
                                                       (length s111 x415) 
                                                       (<= (+ x415 1) i24))) 
                                               (forall ((x416 Int) (x417 Int)) 
                                                   (=> 
                                                       (and 
                                                           (length s111 x417) 
                                                           (length s29 x416)) 
                                                       (<= i24 (+ x417 x416)))) 
                                               (= x405 i24) 
                                               (exists ((x418 Int)) 
                                                   (and 
                                                       (forall ((x419 Int)) 
                                                           (=> 
                                                               (length s111 x419) 
                                                               (= x418 (- i24 x419)))) 
                                                       (MS x418 x407 s29))))))) 
                               (= x406 x407))) 
                       (forall ((x420 Int)) 
                           (=> 
                               (and 
                                   (<= 1 x420) 
                                   (forall ((x421 Int) (x422 Int)) 
                                       (=> 
                                           (and 
                                               (length s111 x422) 
                                               (length s29 x421)) 
                                           (<= x420 (+ x422 x421))))) 
                               (or 
                                   (exists ((x423 A)) 
                                       (exists ((i25 Int)) 
                                           (and 
                                               (<= 1 i25) 
                                               (forall ((x424 Int)) 
                                                   (=> 
                                                       (length s111 x424) 
                                                       (<= i25 x424))) 
                                               (= x420 i25) 
                                               (MS i25 x423 s111)))) 
                                   (exists ((x425 A)) 
                                       (exists ((i26 Int)) 
                                           (and 
                                               (forall ((x426 Int)) 
                                                   (=> 
                                                       (length s111 x426) 
                                                       (<= (+ x426 1) i26))) 
                                               (forall ((x427 Int) (x428 Int)) 
                                                   (=> 
                                                       (and 
                                                           (length s111 x428) 
                                                           (length s29 x427)) 
                                                       (<= i26 (+ x428 x427)))) 
                                               (= x420 i26) 
                                               (exists ((x429 Int)) 
                                                   (and 
                                                       (forall ((x430 Int)) 
                                                           (=> 
                                                               (length s111 x430) 
                                                               (= x429 (- i26 x430)))) 
                                                       (MS x429 x425 s29))))))))))))
         :named hyp15))
(assert (! (forall ((x431 A) (x432 A)) 
               (=> 
                   (MS1 x431 x432 r) 
                   (and 
                       (MS0 x431 a) 
                       (MS0 x432 a))))
         :named hyp16))
(assert (! (not 
               (forall ((x433 A) (x434 A)) 
                   (not 
                       (MS1 x433 x434 r))))
         :named hyp17))
(assert (! (forall ((x435 A) (x436 A)) 
               (=> 
                   (MS1 x435 x436 c) 
                   (and 
                       (MS0 x435 a) 
                       (MS0 x436 a))))
         :named hyp18))
(assert (! (forall ((x437 A) (x438 A)) 
               (=> 
                   (MS1 x437 x438 r) 
                   (MS1 x437 x438 c)))
         :named hyp19))
(assert (! (forall ((x439 A) (x440 A)) 
               (=> 
                   (exists ((x441 A)) 
                       (and 
                           (MS1 x439 x441 c) 
                           (MS1 x441 x440 r))) 
                   (MS1 x439 x440 c)))
         :named hyp20))
(assert (! (forall ((s30 PAA)) 
               (=> 
                   (and 
                       (forall ((x442 A) (x443 A)) 
                           (=> 
                               (MS1 x442 x443 s30) 
                               (and 
                                   (MS0 x442 a) 
                                   (MS0 x443 a)))) 
                       (forall ((x444 A) (x445 A)) 
                           (=> 
                               (MS1 x444 x445 r) 
                               (MS1 x444 x445 s30))) 
                       (forall ((x446 A) (x447 A)) 
                           (=> 
                               (exists ((x448 A)) 
                                   (and 
                                       (MS1 x446 x448 s30) 
                                       (MS1 x448 x447 r))) 
                               (MS1 x446 x447 s30)))) 
                   (forall ((x449 A) (x450 A)) 
                       (=> 
                           (MS1 x449 x450 c) 
                           (MS1 x449 x450 s30)))))
         :named hyp21))
(assert (! (forall ((x451 A)) 
               (= 
                   (exists ((x452 A)) 
                       (MS1 x451 x452 r)) 
                   (MS0 x451 a)))
         :named hyp22))
(assert (! (forall ((x453 A)) 
               (= 
                   (exists ((x454 A)) 
                       (MS1 x453 x454 c)) 
                   (MS0 x453 a)))
         :named hyp23))
(assert (! (forall ((x455 A)) 
               (=> 
                   (exists ((x456 A)) 
                       (MS1 x455 x456 r)) 
                   (exists ((x457 A)) 
                       (MS1 x455 x457 c))))
         :named hyp24))
(assert (! (forall ((x458 A) (x459 A)) 
               (= 
                   (MS1 x458 x459 c) 
                   (or 
                       (MS1 x458 x459 r) 
                       (exists ((x460 A)) 
                           (and 
                               (MS1 x458 x460 c) 
                               (MS1 x460 x459 r))))))
         :named hyp25))
(assert (! (forall ((x461 A) (y A)) 
               (=> 
                   (and 
                       (MS0 x461 a) 
                       (MS0 y a)) 
                   (forall ((s31 PZA) (n33 Int)) 
                       (=> 
                           (and 
                               (<= 0 n33) 
                               (< 1 n33) 
                               (forall ((x462 Int) (x463 A)) 
                                   (=> 
                                       (MS x462 x463 s31) 
                                       (and 
                                           (<= 1 x462) 
                                           (<= x462 n33) 
                                           (MS0 x463 a)))) 
                               (forall ((x464 Int) (x465 A) (x466 A)) 
                                   (=> 
                                       (and 
                                           (MS x464 x465 s31) 
                                           (MS x464 x466 s31)) 
                                       (= x465 x466))) 
                               (forall ((x467 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x467) 
                                           (<= x467 n33)) 
                                       (exists ((x468 A)) 
                                           (MS x467 x468 s31))))) 
                           (and 
                               (exists ((x469 A) (x470 Int)) 
                                   (and 
                                       (= x470 1) 
                                       (MS x470 x469 s31))) 
                               (forall ((x471 Int) (x472 A) (x473 A)) 
                                   (=> 
                                       (and 
                                           (MS x471 x472 s31) 
                                           (MS x471 x473 s31)) 
                                       (= x472 x473))) 
                               (=> 
                                   (exists ((x474 Int)) 
                                       (and 
                                           (= x474 1) 
                                           (MS x474 x461 s31))) 
                                   (and 
                                       (exists ((x475 A)) 
                                           (MS n33 x475 s31)) 
                                       (=> 
                                           (MS n33 y s31) 
                                           (forall ((i27 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 i27) 
                                                       (<= i27 (- n33 1))) 
                                                   (and 
                                                       (exists ((x476 A)) 
                                                           (MS i27 x476 s31)) 
                                                       (exists ((x477 A) (x478 Int)) 
                                                           (and 
                                                               (= x478 (+ i27 1)) 
                                                               (MS x478 x477 s31))))))))))))))
         :named hyp26))
(assert (! (forall ((x479 A) (x480 A)) 
               (=> 
                   (exists ((x481 PZA)) 
                       (path x479 x480 x481)) 
                   (MS1 x479 x480 c)))
         :named hyp27))
(assert (! (forall ((x482 A) (x483 A)) 
               (=> 
                   (MS1 x482 x483 c) 
                   (exists ((x484 PZA)) 
                       (path x482 x483 x484))))
         :named hyp28))
(assert (! (forall ((x485 A) (x486 A)) 
               (=> 
                   (and 
                       (MS0 x485 a) 
                       (MS0 x486 a)) 
                   (exists ((x487 PZA)) 
                       (path x485 x486 x487))))
         :named hyp29))
(assert (! (forall ((n34 Int) (s32 PZA)) 
               (=> 
                   (and 
                       (<= 0 n34) 
                       (forall ((x488 Int) (x489 A)) 
                           (=> 
                               (MS x488 x489 s32) 
                               (and 
                                   (<= 1 x488) 
                                   (<= x488 n34)))) 
                       (forall ((x490 Int) (x491 A) (x492 A)) 
                           (=> 
                               (and 
                                   (MS x490 x491 s32) 
                                   (MS x490 x492 s32)) 
                               (= x491 x492))) 
                       (forall ((x493 Int)) 
                           (=> 
                               (and 
                                   (<= 1 x493) 
                                   (<= x493 n34)) 
                               (exists ((x494 A)) 
                                   (MS x493 x494 s32))))) 
                   (seq s32)))
         :named hyp30))
(assert (! (and 
               (forall ((x495 PZA) (x496 Int)) 
                   (=> 
                       (length x495 x496) 
                       (and 
                           (seq x495) 
                           (<= 0 x496)))) 
               (forall ((x497 PZA) (x498 Int) (x499 Int)) 
                   (=> 
                       (and 
                           (length x497 x498) 
                           (length x497 x499)) 
                       (= x498 x499))) 
               (forall ((x500 PZA)) 
                   (=> 
                       (seq x500) 
                       (exists ((x501 Int)) 
                           (length x500 x501)))))
         :named hyp31))
(assert (! (forall ((s33 PZA)) 
               (=> 
                   (seq s33) 
                   (and 
                       (forall ((x502 Int) (x503 A)) 
                           (=> 
                               (MS x502 x503 s33) 
                               (and 
                                   (<= 1 x502) 
                                   (forall ((x504 Int)) 
                                       (=> 
                                           (length s33 x504) 
                                           (<= x502 x504)))))) 
                       (forall ((x505 Int) (x506 A) (x507 A)) 
                           (=> 
                               (and 
                                   (MS x505 x506 s33) 
                                   (MS x505 x507 s33)) 
                               (= x506 x507))) 
                       (forall ((x508 Int)) 
                           (=> 
                               (and 
                                   (<= 1 x508) 
                                   (forall ((x509 Int)) 
                                       (=> 
                                           (length s33 x509) 
                                           (<= x508 x509)))) 
                               (exists ((x510 A)) 
                                   (MS x508 x510 s33)))))))
         :named hyp32))
(assert (! (forall ((x511 PZA) (x512 PZA) (x513 PZA)) 
               (= 
                   (cnc x511 x512 x513) 
                   (exists ((s112 PZA) (s210 PZA)) 
                       (and 
                           (seq s112) 
                           (seq s210) 
                           (forall ((x514 Int) (x515 A)) 
                               (= 
                                   (MS x514 x515 x511) 
                                   (MS x514 x515 s112))) 
                           (forall ((x516 Int) (x517 A)) 
                               (= 
                                   (MS x516 x517 x512) 
                                   (MS x516 x517 s210))) 
                           (forall ((x518 Int) (x519 A)) 
                               (= 
                                   (MS x518 x519 x513) 
                                   (or 
                                       (exists ((i28 Int)) 
                                           (and 
                                               (<= 1 i28) 
                                               (forall ((x520 Int)) 
                                                   (=> 
                                                       (length s112 x520) 
                                                       (<= i28 x520))) 
                                               (= x518 i28) 
                                               (MS i28 x519 s112))) 
                                       (exists ((i29 Int)) 
                                           (and 
                                               (forall ((x521 Int)) 
                                                   (=> 
                                                       (length s112 x521) 
                                                       (<= (+ x521 1) i29))) 
                                               (forall ((x522 Int) (x523 Int)) 
                                                   (=> 
                                                       (and 
                                                           (length s112 x523) 
                                                           (length s210 x522)) 
                                                       (<= i29 (+ x523 x522)))) 
                                               (= x518 i29) 
                                               (exists ((x524 Int)) 
                                                   (and 
                                                       (forall ((x525 Int)) 
                                                           (=> 
                                                               (length s112 x525) 
                                                               (= x524 (- i29 x525)))) 
                                                       (MS x524 x519 s210))))))))))))
         :named hyp33))
(assert (! (and 
               (forall ((x526 PZA) (x527 PZA) (x528 PZA)) 
                   (=> 
                       (cnc x526 x527 x528) 
                       (and 
                           (seq x526) 
                           (seq x527) 
                           (seq x528)))) 
               (forall ((x529 PZA) (x530 PZA) (x531 PZA) (x532 PZA)) 
                   (=> 
                       (and 
                           (cnc x529 x530 x531) 
                           (cnc x529 x530 x532)) 
                       (forall ((x533 Int) (x534 A)) 
                           (= 
                               (MS x533 x534 x531) 
                               (MS x533 x534 x532))))) 
               (forall ((x535 PZA) (x536 PZA)) 
                   (=> 
                       (and 
                           (seq x535) 
                           (seq x536)) 
                       (exists ((x537 PZA)) 
                           (cnc x535 x536 x537)))))
         :named hyp34))
(assert (! (forall ((s113 PZA) (s211 PZA)) 
               (=> 
                   (and 
                       (seq s113) 
                       (seq s211)) 
                   (exists ((x538 PZA) (x539 Int)) 
                       (and 
                           (cnc s113 s211 x538) 
                           (forall ((x540 Int) (x541 Int)) 
                               (=> 
                                   (and 
                                       (length s113 x541) 
                                       (length s211 x540)) 
                                   (= x539 (+ x541 x540)))) 
                           (length x538 x539)))))
         :named hyp35))
(assert (! (forall ((s114 PZA) (s212 PZA)) 
               (=> 
                   (and 
                       (seq s114) 
                       (seq s212)) 
                   (forall ((x542 Int)) 
                       (= 
                           (exists ((x543 A) (x544 PZA)) 
                               (and 
                                   (cnc s114 s212 x544) 
                                   (MS x542 x543 x544))) 
                           (and 
                               (<= 1 x542) 
                               (forall ((x545 Int) (x546 Int)) 
                                   (=> 
                                       (and 
                                           (length s114 x546) 
                                           (length s212 x545)) 
                                       (<= x542 (+ x546 x545)))))))))
         :named hyp36))
(assert (! (forall ((s115 PZA) (s213 PZA)) 
               (=> 
                   (and 
                       (seq s115) 
                       (seq s213)) 
                   (forall ((x547 A)) 
                       (= 
                           (exists ((x548 Int) (x549 PZA)) 
                               (and 
                                   (cnc s115 s213 x549) 
                                   (MS x548 x547 x549))) 
                           (or 
                               (exists ((x550 Int)) 
                                   (MS x550 x547 s115)) 
                               (exists ((x551 Int)) 
                                   (MS x551 x547 s213)))))))
         :named hyp37))
(assert (! (forall ((s116 PZA) (s214 PZA) (i30 Int)) 
               (=> 
                   (and 
                       (seq s116) 
                       (seq s214) 
                       (<= 1 i30) 
                       (forall ((x552 Int)) 
                           (=> 
                               (length s116 x552) 
                               (<= i30 x552)))) 
                   (exists ((x553 PZA)) 
                       (and 
                           (cnc s116 s214 x553) 
                           (exists ((x554 A)) 
                               (and 
                                   (MS i30 x554 s116) 
                                   (MS i30 x554 x553)))))))
         :named hyp38))
(assert (! (forall ((x555 A) (x556 A) (x557 PZA)) 
               (= 
                   (path x555 x556 x557) 
                   (exists ((x558 A) (y0 A) (p PZA)) 
                       (and 
                           (MS0 x558 a) 
                           (MS0 y0 a) 
                           (exists ((n35 Int)) 
                               (and 
                                   (<= 0 n35) 
                                   (< 1 n35) 
                                   (forall ((x559 Int) (x560 A)) 
                                       (=> 
                                           (MS x559 x560 p) 
                                           (and 
                                               (<= 1 x559) 
                                               (<= x559 n35) 
                                               (MS0 x560 a)))) 
                                   (forall ((x561 Int) (x562 A) (x563 A)) 
                                       (=> 
                                           (and 
                                               (MS x561 x562 p) 
                                               (MS x561 x563 p)) 
                                           (= x562 x563))) 
                                   (forall ((x564 Int)) 
                                       (=> 
                                           (and 
                                               (<= 1 x564) 
                                               (<= x564 n35)) 
                                           (exists ((x565 A)) 
                                               (MS x564 x565 p)))) 
                                   (exists ((x566 Int)) 
                                       (and 
                                           (= x566 1) 
                                           (MS x566 x558 p))) 
                                   (MS n35 y0 p) 
                                   (forall ((i31 Int)) 
                                       (=> 
                                           (and 
                                               (<= 1 i31) 
                                               (<= i31 (- n35 1))) 
                                           (exists ((x567 A) (x568 A)) 
                                               (and 
                                                   (MS i31 x567 p) 
                                                   (exists ((x569 Int)) 
                                                       (and 
                                                           (= x569 (+ i31 1)) 
                                                           (MS x569 x568 p))) 
                                                   (MS1 x567 x568 r))))))) 
                           (= x555 x558) 
                           (= x556 y0) 
                           (forall ((x570 Int) (x571 A)) 
                               (= 
                                   (MS x570 x571 x557) 
                                   (MS x570 x571 p)))))))
         :named hyp39))
(assert (! (forall ((x572 A)) 
               (= 
                   (MS0 x572 candidate) 
                   (exists ((z A)) 
                       (and 
                           (MS0 z a) 
                           (forall ((x573 A) (y1 A)) 
                               (=> 
                                   (and 
                                       (MS0 x573 a) 
                                       (not 
                                           (= x573 z)) 
                                       (MS0 y1 a) 
                                       (not 
                                           (= y1 z)) 
                                       (not 
                                           (= x573 y1))) 
                                   (exists ((p0 PZA)) 
                                       (and 
                                           (exists ((x574 A) (x575 A)) 
                                               (and 
                                                   (= x574 x573) 
                                                   (= x575 y1) 
                                                   (path x574 x575 p0))) 
                                           (not 
                                               (exists ((x576 Int)) 
                                                   (MS x576 z p0))))))) 
                           (= x572 z)))))
         :named hyp40))
(assert (! (forall ((u A)) 
               (=> 
                   (MS0 u candidate) 
                   (forall ((x577 A) (x578 A)) 
                       (=> 
                           (and 
                               (MS0 x577 a) 
                               (not 
                                   (= x577 u)) 
                               (MS0 x578 a) 
                               (not 
                                   (= x578 u)) 
                               (not 
                                   (= x577 x578))) 
                           (exists ((x579 A) (y2 A) (p1 PZA)) 
                               (and 
                                   (MS0 x579 a) 
                                   (not 
                                       (= x579 u)) 
                                   (MS0 y2 a) 
                                   (not 
                                       (= y2 u)) 
                                   (not 
                                       (= x579 y2)) 
                                   (exists ((n36 Int)) 
                                       (and 
                                           (<= 0 n36) 
                                           (< 1 n36) 
                                           (forall ((x580 Int) (x581 A)) 
                                               (=> 
                                                   (MS x580 x581 p1) 
                                                   (and 
                                                       (<= 1 x580) 
                                                       (<= x580 n36) 
                                                       (MS0 x581 a) 
                                                       (not 
                                                           (= x581 u))))) 
                                           (forall ((x582 Int) (x583 A) (x584 A)) 
                                               (=> 
                                                   (and 
                                                       (MS x582 x583 p1) 
                                                       (MS x582 x584 p1)) 
                                                   (= x583 x584))) 
                                           (forall ((x585 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x585) 
                                                       (<= x585 n36)) 
                                                   (exists ((x586 A)) 
                                                       (MS x585 x586 p1)))) 
                                           (exists ((x587 Int)) 
                                               (and 
                                                   (= x587 1) 
                                                   (MS x587 x579 p1))) 
                                           (MS n36 y2 p1) 
                                           (forall ((i32 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 i32) 
                                                       (<= i32 (- n36 1))) 
                                                   (exists ((x588 A) (x589 A)) 
                                                       (and 
                                                           (MS i32 x588 p1) 
                                                           (exists ((x590 Int)) 
                                                               (and 
                                                                   (= x590 (+ i32 1)) 
                                                                   (MS x590 x589 p1))) 
                                                           (MS1 x588 x589 r))))))) 
                                   (= x577 x579) 
                                   (= x578 y2)))))))
         :named hyp41))
(assert (! (forall ((s117 PZA) (s215 PZA)) 
               (=> 
                   (and 
                       (seq s117) 
                       (seq s215)) 
                   (and 
                       (exists ((x591 Int)) 
                           (length s117 x591)) 
                       (forall ((x592 PZA) (x593 Int) (x594 Int)) 
                           (=> 
                               (and 
                                   (length x592 x593) 
                                   (length x592 x594)) 
                               (= x593 x594))) 
                       (forall ((i33 Int)) 
                           (=> 
                               (and 
                                   (<= 1 i33) 
                                   (forall ((x595 Int)) 
                                       (=> 
                                           (length s117 x595) 
                                           (<= i33 x595)))) 
                               (and 
                                   (exists ((x596 A)) 
                                       (MS i33 x596 s117)) 
                                   (forall ((x597 Int) (x598 A) (x599 A)) 
                                       (=> 
                                           (and 
                                               (MS x597 x598 s117) 
                                               (MS x597 x599 s117)) 
                                           (= x598 x599)))))) 
                       (exists ((x600 Int)) 
                           (length s215 x600)) 
                       (forall ((i34 Int)) 
                           (=> 
                               (and 
                                   (forall ((x601 Int)) 
                                       (=> 
                                           (length s117 x601) 
                                           (<= (+ x601 1) i34))) 
                                   (forall ((x602 Int) (x603 Int)) 
                                       (=> 
                                           (and 
                                               (length s117 x603) 
                                               (length s215 x602)) 
                                           (<= i34 (+ x603 x602))))) 
                               (and 
                                   (exists ((x604 A) (x605 Int)) 
                                       (and 
                                           (forall ((x606 Int)) 
                                               (=> 
                                                   (length s117 x606) 
                                                   (= x605 (- i34 x606)))) 
                                           (MS x605 x604 s215))) 
                                   (forall ((x607 Int) (x608 A) (x609 A)) 
                                       (=> 
                                           (and 
                                               (MS x607 x608 s215) 
                                               (MS x607 x609 s215)) 
                                           (= x608 x609)))))))))
         :named hyp42))
(assert (! (forall ((x610 A) (x611 A)) 
               (=> 
                   (and 
                       (MS0 x610 a) 
                       (MS0 x611 a)) 
                   (MS1 x610 x611 c)))
         :named hyp43))
(assert (! (not 
               (forall ((x612 A)) 
                   (MS0 x612 a)))
         :named hyp44))
(assert (! (forall ((s118 PZA) (s216 PZA) (b0 PA)) 
               (=> 
                   (and 
                       (seq s118) 
                       (seq s216) 
                       (forall ((x613 A)) 
                           (=> 
                               (exists ((x614 Int)) 
                                   (MS x614 x613 s118)) 
                               (MS0 x613 b0))) 
                       (forall ((x615 A)) 
                           (=> 
                               (exists ((x616 Int)) 
                                   (MS x616 x615 s216)) 
                               (MS0 x615 b0)))) 
                   (and 
                       (forall ((x617 Int) (x618 A)) 
                           (=> 
                               (exists ((x619 PZA)) 
                                   (and 
                                       (cnc s118 s216 x619) 
                                       (MS x617 x618 x619))) 
                               (and 
                                   (<= 1 x617) 
                                   (forall ((x620 Int) (x621 Int)) 
                                       (=> 
                                           (and 
                                               (length s118 x621) 
                                               (length s216 x620)) 
                                           (<= x617 (+ x621 x620)))) 
                                   (MS0 x618 b0)))) 
                       (forall ((x622 Int) (x623 A) (x624 A)) 
                           (=> 
                               (and 
                                   (exists ((x625 PZA)) 
                                       (and 
                                           (cnc s118 s216 x625) 
                                           (MS x622 x623 x625))) 
                                   (exists ((x626 PZA)) 
                                       (and 
                                           (cnc s118 s216 x626) 
                                           (MS x622 x624 x626)))) 
                               (= x623 x624))) 
                       (forall ((x627 Int)) 
                           (=> 
                               (and 
                                   (<= 1 x627) 
                                   (forall ((x628 Int) (x629 Int)) 
                                       (=> 
                                           (and 
                                               (length s118 x629) 
                                               (length s216 x628)) 
                                           (<= x627 (+ x629 x628))))) 
                               (exists ((x630 A) (x631 PZA)) 
                                   (and 
                                       (cnc s118 s216 x631) 
                                       (MS x627 x630 x631))))))))
         :named hyp45))
(assert (! (seq s1)
         :named hyp46))
(assert (! (seq s2)
         :named hyp47))
(assert (! (and 
               (forall ((x632 PZA) (x633 PZA) (x634 PZA)) 
                   (=> 
                       (cnc x632 x633 x634) 
                       (and 
                           (exists ((s34 PZA)) 
                               (and 
                                   (exists ((n37 Int)) 
                                       (and 
                                           (<= 0 n37) 
                                           (forall ((x635 Int) (x636 A)) 
                                               (=> 
                                                   (MS x635 x636 s34) 
                                                   (and 
                                                       (<= 1 x635) 
                                                       (<= x635 n37)))) 
                                           (forall ((x637 Int) (x638 A) (x639 A)) 
                                               (=> 
                                                   (and 
                                                       (MS x637 x638 s34) 
                                                       (MS x637 x639 s34)) 
                                                   (= x638 x639))) 
                                           (forall ((x640 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x640) 
                                                       (<= x640 n37)) 
                                                   (exists ((x641 A)) 
                                                       (MS x640 x641 s34)))))) 
                                   (forall ((x642 Int) (x643 A)) 
                                       (= 
                                           (MS x642 x643 x632) 
                                           (MS x642 x643 s34))))) 
                           (exists ((s35 PZA)) 
                               (and 
                                   (exists ((n38 Int)) 
                                       (and 
                                           (<= 0 n38) 
                                           (forall ((x644 Int) (x645 A)) 
                                               (=> 
                                                   (MS x644 x645 s35) 
                                                   (and 
                                                       (<= 1 x644) 
                                                       (<= x644 n38)))) 
                                           (forall ((x646 Int) (x647 A) (x648 A)) 
                                               (=> 
                                                   (and 
                                                       (MS x646 x647 s35) 
                                                       (MS x646 x648 s35)) 
                                                   (= x647 x648))) 
                                           (forall ((x649 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x649) 
                                                       (<= x649 n38)) 
                                                   (exists ((x650 A)) 
                                                       (MS x649 x650 s35)))))) 
                                   (forall ((x651 Int) (x652 A)) 
                                       (= 
                                           (MS x651 x652 x633) 
                                           (MS x651 x652 s35))))) 
                           (exists ((s36 PZA)) 
                               (and 
                                   (exists ((n39 Int)) 
                                       (and 
                                           (<= 0 n39) 
                                           (forall ((x653 Int) (x654 A)) 
                                               (=> 
                                                   (MS x653 x654 s36) 
                                                   (and 
                                                       (<= 1 x653) 
                                                       (<= x653 n39)))) 
                                           (forall ((x655 Int) (x656 A) (x657 A)) 
                                               (=> 
                                                   (and 
                                                       (MS x655 x656 s36) 
                                                       (MS x655 x657 s36)) 
                                                   (= x656 x657))) 
                                           (forall ((x658 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x658) 
                                                       (<= x658 n39)) 
                                                   (exists ((x659 A)) 
                                                       (MS x658 x659 s36)))))) 
                                   (forall ((x660 Int) (x661 A)) 
                                       (= 
                                           (MS x660 x661 x634) 
                                           (MS x660 x661 s36)))))))) 
               (forall ((x662 PZA) (x663 PZA) (x664 PZA) (x665 PZA)) 
                   (=> 
                       (and 
                           (cnc x662 x663 x664) 
                           (cnc x662 x663 x665)) 
                       (forall ((x666 Int) (x667 A)) 
                           (= 
                               (MS x666 x667 x664) 
                               (MS x666 x667 x665))))) 
               (forall ((x668 PZA) (x669 PZA)) 
                   (=> 
                       (and 
                           (exists ((s37 PZA)) 
                               (and 
                                   (exists ((n40 Int)) 
                                       (and 
                                           (<= 0 n40) 
                                           (forall ((x670 Int) (x671 A)) 
                                               (=> 
                                                   (MS x670 x671 s37) 
                                                   (and 
                                                       (<= 1 x670) 
                                                       (<= x670 n40)))) 
                                           (forall ((x672 Int) (x673 A) (x674 A)) 
                                               (=> 
                                                   (and 
                                                       (MS x672 x673 s37) 
                                                       (MS x672 x674 s37)) 
                                                   (= x673 x674))) 
                                           (forall ((x675 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x675) 
                                                       (<= x675 n40)) 
                                                   (exists ((x676 A)) 
                                                       (MS x675 x676 s37)))))) 
                                   (forall ((x677 Int) (x678 A)) 
                                       (= 
                                           (MS x677 x678 x668) 
                                           (MS x677 x678 s37))))) 
                           (exists ((s38 PZA)) 
                               (and 
                                   (exists ((n41 Int)) 
                                       (and 
                                           (<= 0 n41) 
                                           (forall ((x679 Int) (x680 A)) 
                                               (=> 
                                                   (MS x679 x680 s38) 
                                                   (and 
                                                       (<= 1 x679) 
                                                       (<= x679 n41)))) 
                                           (forall ((x681 Int) (x682 A) (x683 A)) 
                                               (=> 
                                                   (and 
                                                       (MS x681 x682 s38) 
                                                       (MS x681 x683 s38)) 
                                                   (= x682 x683))) 
                                           (forall ((x684 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x684) 
                                                       (<= x684 n41)) 
                                                   (exists ((x685 A)) 
                                                       (MS x684 x685 s38)))))) 
                                   (forall ((x686 Int) (x687 A)) 
                                       (= 
                                           (MS x686 x687 x669) 
                                           (MS x686 x687 s38)))))) 
                       (exists ((x688 PZA)) 
                           (cnc x668 x669 x688)))))
         :named hyp48))
(assert (! (forall ((s119 PZA) (s217 PZA)) 
               (=> 
                   (and 
                       (exists ((n42 Int)) 
                           (and 
                               (<= 0 n42) 
                               (forall ((x689 Int) (x690 A)) 
                                   (=> 
                                       (MS x689 x690 s119) 
                                       (and 
                                           (<= 1 x689) 
                                           (<= x689 n42)))) 
                               (forall ((x691 Int) (x692 A) (x693 A)) 
                                   (=> 
                                       (and 
                                           (MS x691 x692 s119) 
                                           (MS x691 x693 s119)) 
                                       (= x692 x693))) 
                               (forall ((x694 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x694) 
                                           (<= x694 n42)) 
                                       (exists ((x695 A)) 
                                           (MS x694 x695 s119)))))) 
                       (exists ((n43 Int)) 
                           (and 
                               (<= 0 n43) 
                               (forall ((x696 Int) (x697 A)) 
                                   (=> 
                                       (MS x696 x697 s217) 
                                       (and 
                                           (<= 1 x696) 
                                           (<= x696 n43)))) 
                               (forall ((x698 Int) (x699 A) (x700 A)) 
                                   (=> 
                                       (and 
                                           (MS x698 x699 s217) 
                                           (MS x698 x700 s217)) 
                                       (= x699 x700))) 
                               (forall ((x701 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x701) 
                                           (<= x701 n43)) 
                                       (exists ((x702 A)) 
                                           (MS x701 x702 s217))))))) 
                   (exists ((x703 PZA) (x704 Int)) 
                       (and 
                           (cnc s119 s217 x703) 
                           (forall ((x705 Int) (x706 Int)) 
                               (=> 
                                   (and 
                                       (length s119 x706) 
                                       (length s217 x705)) 
                                   (= x704 (+ x706 x705)))) 
                           (length x703 x704)))))
         :named hyp49))
(assert (! (forall ((s120 PZA) (s218 PZA)) 
               (=> 
                   (and 
                       (exists ((n44 Int)) 
                           (and 
                               (<= 0 n44) 
                               (forall ((x707 Int) (x708 A)) 
                                   (=> 
                                       (MS x707 x708 s120) 
                                       (and 
                                           (<= 1 x707) 
                                           (<= x707 n44)))) 
                               (forall ((x709 Int) (x710 A) (x711 A)) 
                                   (=> 
                                       (and 
                                           (MS x709 x710 s120) 
                                           (MS x709 x711 s120)) 
                                       (= x710 x711))) 
                               (forall ((x712 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x712) 
                                           (<= x712 n44)) 
                                       (exists ((x713 A)) 
                                           (MS x712 x713 s120)))))) 
                       (exists ((n45 Int)) 
                           (and 
                               (<= 0 n45) 
                               (forall ((x714 Int) (x715 A)) 
                                   (=> 
                                       (MS x714 x715 s218) 
                                       (and 
                                           (<= 1 x714) 
                                           (<= x714 n45)))) 
                               (forall ((x716 Int) (x717 A) (x718 A)) 
                                   (=> 
                                       (and 
                                           (MS x716 x717 s218) 
                                           (MS x716 x718 s218)) 
                                       (= x717 x718))) 
                               (forall ((x719 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x719) 
                                           (<= x719 n45)) 
                                       (exists ((x720 A)) 
                                           (MS x719 x720 s218))))))) 
                   (forall ((x721 Int)) 
                       (= 
                           (exists ((x722 A) (x723 PZA)) 
                               (and 
                                   (cnc s120 s218 x723) 
                                   (MS x721 x722 x723))) 
                           (and 
                               (<= 1 x721) 
                               (forall ((x724 Int) (x725 Int)) 
                                   (=> 
                                       (and 
                                           (length s120 x725) 
                                           (length s218 x724)) 
                                       (<= x721 (+ x725 x724)))))))))
         :named hyp50))
(assert (! (forall ((s121 PZA) (s219 PZA)) 
               (=> 
                   (and 
                       (exists ((n46 Int)) 
                           (and 
                               (<= 0 n46) 
                               (forall ((x726 Int) (x727 A)) 
                                   (=> 
                                       (MS x726 x727 s121) 
                                       (and 
                                           (<= 1 x726) 
                                           (<= x726 n46)))) 
                               (forall ((x728 Int) (x729 A) (x730 A)) 
                                   (=> 
                                       (and 
                                           (MS x728 x729 s121) 
                                           (MS x728 x730 s121)) 
                                       (= x729 x730))) 
                               (forall ((x731 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x731) 
                                           (<= x731 n46)) 
                                       (exists ((x732 A)) 
                                           (MS x731 x732 s121)))))) 
                       (exists ((n47 Int)) 
                           (and 
                               (<= 0 n47) 
                               (forall ((x733 Int) (x734 A)) 
                                   (=> 
                                       (MS x733 x734 s219) 
                                       (and 
                                           (<= 1 x733) 
                                           (<= x733 n47)))) 
                               (forall ((x735 Int) (x736 A) (x737 A)) 
                                   (=> 
                                       (and 
                                           (MS x735 x736 s219) 
                                           (MS x735 x737 s219)) 
                                       (= x736 x737))) 
                               (forall ((x738 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x738) 
                                           (<= x738 n47)) 
                                       (exists ((x739 A)) 
                                           (MS x738 x739 s219))))))) 
                   (forall ((x740 A)) 
                       (= 
                           (exists ((x741 Int) (x742 PZA)) 
                               (and 
                                   (cnc s121 s219 x742) 
                                   (MS x741 x740 x742))) 
                           (or 
                               (exists ((x743 Int)) 
                                   (MS x743 x740 s121)) 
                               (exists ((x744 Int)) 
                                   (MS x744 x740 s219)))))))
         :named hyp51))
(assert (! (forall ((s122 PZA) (s220 PZA) (i35 Int)) 
               (=> 
                   (and 
                       (exists ((n48 Int)) 
                           (and 
                               (<= 0 n48) 
                               (forall ((x745 Int) (x746 A)) 
                                   (=> 
                                       (MS x745 x746 s122) 
                                       (and 
                                           (<= 1 x745) 
                                           (<= x745 n48)))) 
                               (forall ((x747 Int) (x748 A) (x749 A)) 
                                   (=> 
                                       (and 
                                           (MS x747 x748 s122) 
                                           (MS x747 x749 s122)) 
                                       (= x748 x749))) 
                               (forall ((x750 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x750) 
                                           (<= x750 n48)) 
                                       (exists ((x751 A)) 
                                           (MS x750 x751 s122)))))) 
                       (exists ((n49 Int)) 
                           (and 
                               (<= 0 n49) 
                               (forall ((x752 Int) (x753 A)) 
                                   (=> 
                                       (MS x752 x753 s220) 
                                       (and 
                                           (<= 1 x752) 
                                           (<= x752 n49)))) 
                               (forall ((x754 Int) (x755 A) (x756 A)) 
                                   (=> 
                                       (and 
                                           (MS x754 x755 s220) 
                                           (MS x754 x756 s220)) 
                                       (= x755 x756))) 
                               (forall ((x757 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x757) 
                                           (<= x757 n49)) 
                                       (exists ((x758 A)) 
                                           (MS x757 x758 s220)))))) 
                       (<= 1 i35) 
                       (forall ((x759 Int)) 
                           (=> 
                               (length s122 x759) 
                               (<= i35 x759)))) 
                   (exists ((x760 PZA)) 
                       (and 
                           (cnc s122 s220 x760) 
                           (exists ((x761 A)) 
                               (and 
                                   (MS i35 x761 s122) 
                                   (MS i35 x761 x760)))))))
         :named hyp52))
(assert (! (forall ((s123 PZA) (s221 PZA) (b1 PA)) 
               (=> 
                   (and 
                       (exists ((n50 Int)) 
                           (and 
                               (<= 0 n50) 
                               (forall ((x762 Int) (x763 A)) 
                                   (=> 
                                       (MS x762 x763 s123) 
                                       (and 
                                           (<= 1 x762) 
                                           (<= x762 n50)))) 
                               (forall ((x764 Int) (x765 A) (x766 A)) 
                                   (=> 
                                       (and 
                                           (MS x764 x765 s123) 
                                           (MS x764 x766 s123)) 
                                       (= x765 x766))) 
                               (forall ((x767 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x767) 
                                           (<= x767 n50)) 
                                       (exists ((x768 A)) 
                                           (MS x767 x768 s123)))))) 
                       (exists ((n51 Int)) 
                           (and 
                               (<= 0 n51) 
                               (forall ((x769 Int) (x770 A)) 
                                   (=> 
                                       (MS x769 x770 s221) 
                                       (and 
                                           (<= 1 x769) 
                                           (<= x769 n51)))) 
                               (forall ((x771 Int) (x772 A) (x773 A)) 
                                   (=> 
                                       (and 
                                           (MS x771 x772 s221) 
                                           (MS x771 x773 s221)) 
                                       (= x772 x773))) 
                               (forall ((x774 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x774) 
                                           (<= x774 n51)) 
                                       (exists ((x775 A)) 
                                           (MS x774 x775 s221)))))) 
                       (forall ((x776 A)) 
                           (=> 
                               (exists ((x777 Int)) 
                                   (MS x777 x776 s123)) 
                               (MS0 x776 b1))) 
                       (forall ((x778 A)) 
                           (=> 
                               (exists ((x779 Int)) 
                                   (MS x779 x778 s221)) 
                               (MS0 x778 b1)))) 
                   (and 
                       (forall ((x780 Int) (x781 A)) 
                           (=> 
                               (exists ((x782 PZA)) 
                                   (and 
                                       (cnc s123 s221 x782) 
                                       (MS x780 x781 x782))) 
                               (and 
                                   (<= 1 x780) 
                                   (forall ((x783 Int) (x784 Int)) 
                                       (=> 
                                           (and 
                                               (length s123 x784) 
                                               (length s221 x783)) 
                                           (<= x780 (+ x784 x783)))) 
                                   (MS0 x781 b1)))) 
                       (forall ((x785 Int) (x786 A) (x787 A)) 
                           (=> 
                               (and 
                                   (exists ((x788 PZA)) 
                                       (and 
                                           (cnc s123 s221 x788) 
                                           (MS x785 x786 x788))) 
                                   (exists ((x789 PZA)) 
                                       (and 
                                           (cnc s123 s221 x789) 
                                           (MS x785 x787 x789)))) 
                               (= x786 x787))) 
                       (forall ((x790 Int)) 
                           (=> 
                               (and 
                                   (<= 1 x790) 
                                   (forall ((x791 Int) (x792 Int)) 
                                       (=> 
                                           (and 
                                               (length s123 x792) 
                                               (length s221 x791)) 
                                           (<= x790 (+ x792 x791))))) 
                               (exists ((x793 A) (x794 PZA)) 
                                   (and 
                                       (cnc s123 s221 x794) 
                                       (MS x790 x793 x794))))))))
         :named hyp53))
(assert (! (not 
               (forall ((x795 Int) (x796 A) (x797 A)) 
                   (=> 
                       (and 
                           (MS x795 x796 s2) 
                           (MS x795 x797 s2)) 
                       (= x796 x797))))
         :named goal))
(check-sat)
(exit)

