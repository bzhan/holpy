(set-info :smt-lib-version 2.6)
(set-logic AUFLIA)
(set-info :source |Generator: Rodin SMT Plug-in|)
(set-info :license "https://creativecommons.org/licenses/by-nc/4.0/")
(set-info :category "industrial")
(set-info :status unsat)

(declare-sort B 0)
(declare-sort PB0 0)
(declare-sort PBB 0)
(declare-sort R 0)
(declare-sort S 0)
(declare-fun GRN (S) Bool)
(declare-fun MS (B B PBB) Bool)
(declare-fun MS0 (B PB0) Bool)
(declare-fun SIG (B S) Bool)
(declare-fun frm (R) Bool)
(declare-fun fst (R B) Bool)
(declare-fun lst (R B) Bool)
(declare-fun nxt (R PBB) Bool)
(declare-fun rdy (R) Bool)
(declare-fun resrt (R) Bool)
(declare-fun rsrtbl (B R) Bool)
(declare-fun rtbl (B R) Bool)
(declare-fun LBT () PB0)
(declare-fun OCC () PB0)
(declare-fun TRK () PBB)
(declare-fun blpt () PB0)
(declare-fun lft () PBB)
(declare-fun r () R)
(declare-fun resbl () PB0)
(declare-fun rht () PBB)

; Elementary Sets axiom (Singleton part)
(assert (forall ((x231 B)) 
            (exists ((X PB0)) 
                (and 
                    (MS0 x231 X) 
                    (forall ((y0 B)) 
                        (=> 
                            (MS0 y0 X) 
                            (= y0 x231)))))))
; Elementary Sets axiom (Singleton part)
(assert (forall ((x232 B) (x233 B)) 
            (exists ((X0 PBB)) 
                (and 
                    (MS x232 x233 X0) 
                    (forall ((y1 B) (y2 B)) 
                        (=> 
                            (MS y1 y2 X0) 
                            (and 
                                (= y1 x232) 
                                (= y2 x233))))))))
(assert (! (forall ((x B)) 
               (exists ((x0 R)) 
                   (rtbl x x0)))
         :named hyp1))
(assert (! (forall ((x1 R)) 
               (exists ((x2 B)) 
                   (rtbl x2 x1)))
         :named hyp2))
(assert (! (and 
               (forall ((x3 R) (x4 PBB)) 
                   (=> 
                       (nxt x3 x4) 
                       (and 
                           (forall ((x5 B) (x6 B) (x7 B)) 
                               (=> 
                                   (and 
                                       (MS x5 x6 x4) 
                                       (MS x5 x7 x4)) 
                                   (= x6 x7))) 
                           (forall ((x8 B) (x9 B) (x10 B)) 
                               (=> 
                                   (and 
                                       (MS x9 x8 x4) 
                                       (MS x10 x8 x4)) 
                                   (= x9 x10)))))) 
               (forall ((x11 R) (x12 PBB) (x13 PBB)) 
                   (=> 
                       (and 
                           (nxt x11 x12) 
                           (nxt x11 x13)) 
                       (forall ((x14 B) (x15 B)) 
                           (= 
                               (MS x14 x15 x12) 
                               (MS x14 x15 x13))))) 
               (forall ((x16 R)) 
                   (exists ((x17 PBB)) 
                       (nxt x16 x17))))
         :named hyp3))
(assert (! (and 
               (forall ((x18 R) (x19 B) (x20 B)) 
                   (=> 
                       (and 
                           (fst x18 x19) 
                           (fst x18 x20)) 
                       (= x19 x20))) 
               (forall ((x21 R)) 
                   (exists ((x22 B)) 
                       (fst x21 x22))))
         :named hyp4))
(assert (! (and 
               (forall ((x23 R) (x24 B) (x25 B)) 
                   (=> 
                       (and 
                           (lst x23 x24) 
                           (lst x23 x25)) 
                       (= x24 x25))) 
               (forall ((x26 R)) 
                   (exists ((x27 B)) 
                       (lst x26 x27))))
         :named hyp5))
(assert (! (forall ((x28 B) (x29 R)) 
               (=> 
                   (fst x29 x28) 
                   (rtbl x28 x29)))
         :named hyp6))
(assert (! (forall ((x30 B) (x31 R)) 
               (=> 
                   (lst x31 x30) 
                   (rtbl x30 x31)))
         :named hyp7))
(assert (! (and 
               (forall ((x32 B) (x33 S)) 
                   (=> 
                       (SIG x32 x33) 
                       (exists ((x34 R)) 
                           (fst x34 x32)))) 
               (forall ((x35 B) (x36 S) (x37 S)) 
                   (=> 
                       (and 
                           (SIG x35 x36) 
                           (SIG x35 x37)) 
                       (= x36 x37))) 
               (forall ((x38 B)) 
                   (=> 
                       (exists ((x39 R)) 
                           (fst x39 x38)) 
                       (exists ((x40 S)) 
                           (SIG x38 x40)))) 
               (forall ((x41 S)) 
                   (exists ((x42 B)) 
                       (SIG x42 x41))) 
               (forall ((x43 S) (x44 B) (x45 B)) 
                   (=> 
                       (and 
                           (SIG x44 x43) 
                           (SIG x45 x43)) 
                       (= x44 x45))))
         :named hyp8))
(assert (! (and 
               (forall ((x46 B) (x47 B)) 
                   (=> 
                       (MS x46 x47 lft) 
                       (MS0 x46 blpt))) 
               (forall ((x48 B) (x49 B) (x50 B)) 
                   (=> 
                       (and 
                           (MS x48 x49 lft) 
                           (MS x48 x50 lft)) 
                       (= x49 x50))) 
               (forall ((x51 B)) 
                   (=> 
                       (MS0 x51 blpt) 
                       (exists ((x52 B)) 
                           (MS x51 x52 lft)))))
         :named hyp9))
(assert (! (and 
               (forall ((x53 B) (x54 B)) 
                   (=> 
                       (MS x53 x54 rht) 
                       (MS0 x53 blpt))) 
               (forall ((x55 B) (x56 B) (x57 B)) 
                   (=> 
                       (and 
                           (MS x55 x56 rht) 
                           (MS x55 x57 rht)) 
                       (= x56 x57))) 
               (forall ((x58 B)) 
                   (=> 
                       (MS0 x58 blpt) 
                       (exists ((x59 B)) 
                           (MS x58 x59 rht)))))
         :named hyp10))
(assert (! (forall ((x60 B) (x61 B)) 
               (not 
                   (and 
                       (MS x60 x61 lft) 
                       (MS x60 x61 rht))))
         :named hyp11))
(assert (! (forall ((x62 B)) 
               (not 
                   (and 
                       (MS0 x62 blpt) 
                       (exists ((x63 R)) 
                           (fst x63 x62)))))
         :named hyp12))
(assert (! (forall ((x64 B)) 
               (not 
                   (and 
                       (MS0 x64 blpt) 
                       (exists ((x65 R)) 
                           (lst x65 x64)))))
         :named hyp13))
(assert (! (and 
               (forall ((x66 B) (x67 R)) 
                   (=> 
                       (rsrtbl x66 x67) 
                       (and 
                           (MS0 x66 resbl) 
                           (resrt x67)))) 
               (forall ((x68 B) (x69 R) (x70 R)) 
                   (=> 
                       (and 
                           (rsrtbl x68 x69) 
                           (rsrtbl x68 x70)) 
                       (= x69 x70))) 
               (forall ((x71 B)) 
                   (=> 
                       (MS0 x71 resbl) 
                       (exists ((x72 R)) 
                           (rsrtbl x71 x72)))))
         :named hyp14))
(assert (! (forall ((x73 B) (x74 R)) 
               (=> 
                   (rsrtbl x73 x74) 
                   (rtbl x73 x74)))
         :named hyp15))
(assert (! (forall ((x75 B)) 
               (=> 
                   (MS0 x75 OCC) 
                   (MS0 x75 resbl)))
         :named hyp16))
(assert (! (and 
               (forall ((x76 B) (x77 B) (x78 B)) 
                   (=> 
                       (and 
                           (MS x76 x77 TRK) 
                           (MS x76 x78 TRK)) 
                       (= x77 x78))) 
               (forall ((x79 B) (x80 B) (x81 B)) 
                   (=> 
                       (and 
                           (MS x80 x79 TRK) 
                           (MS x81 x79 TRK)) 
                       (= x80 x81))))
         :named hyp17))
(assert (! (forall ((x82 R)) 
               (=> 
                   (frm x82) 
                   (resrt x82)))
         :named hyp18))
(assert (! (forall ((x83 R)) 
               (=> 
                   (exists ((x84 B)) 
                       (and 
                           (MS0 x84 OCC) 
                           (rsrtbl x84 x83))) 
                   (frm x83)))
         :named hyp19))
(assert (! (forall ((r0 R)) 
               (=> 
                   (and 
                       (resrt r0) 
                       (not 
                           (frm r0))) 
                   (forall ((x85 B) (x86 R)) 
                       (= 
                           (and 
                               (rtbl x85 x86) 
                               (= x86 r0)) 
                           (and 
                               (rsrtbl x85 x86) 
                               (= x86 r0))))))
         :named hyp20))
(assert (! (forall ((r1 R)) 
               (=> 
                   (frm r1) 
                   (forall ((x87 B) (x88 B)) 
                       (= 
                           (and 
                               (exists ((x89 PBB)) 
                                   (and 
                                       (nxt r1 x89) 
                                       (MS x87 x88 x89))) 
                               (exists ((x90 R)) 
                                   (and 
                                       (= x90 r1) 
                                       (rsrtbl x87 x90)))) 
                           (and 
                               (MS x87 x88 TRK) 
                               (exists ((x91 R)) 
                                   (and 
                                       (= x91 r1) 
                                       (rsrtbl x87 x91))))))))
         :named hyp21))
(assert (! (forall ((x92 B)) 
               (=> 
                   (MS0 x92 LBT) 
                   (MS0 x92 OCC)))
         :named hyp22))
(assert (! (forall ((b B)) 
               (=> 
                   (and 
                       (MS0 b OCC) 
                       (exists ((x93 B)) 
                           (MS b x93 TRK))) 
                   (exists ((x94 PBB)) 
                       (and 
                           (exists ((x95 R)) 
                               (and 
                                   (rsrtbl b x95) 
                                   (nxt x95 x94))) 
                           (exists ((x96 B)) 
                               (and 
                                   (MS b x96 TRK) 
                                   (MS b x96 x94)))))))
         :named hyp23))
(assert (! (forall ((x97 R)) 
               (=> 
                   (rdy x97) 
                   (frm x97)))
         :named hyp24))
(assert (! (forall ((r2 R)) 
               (=> 
                   (rdy r2) 
                   (forall ((x98 B) (x99 R)) 
                       (= 
                           (and 
                               (rtbl x98 x99) 
                               (= x99 r2)) 
                           (and 
                               (rsrtbl x98 x99) 
                               (= x99 r2))))))
         :named hyp25))
(assert (! (forall ((r3 R)) 
               (=> 
                   (rdy r3) 
                   (forall ((x100 B)) 
                       (not 
                           (and 
                               (exists ((x101 R)) 
                                   (and 
                                       (rtbl x100 x101) 
                                       (= x101 r3))) 
                               (MS0 x100 OCC))))))
         :named hyp26))
(assert (! (forall ((x102 S)) 
               (= 
                   (exists ((x103 B)) 
                       (and 
                           (exists ((x104 R)) 
                               (and 
                                   (rdy x104) 
                                   (fst x104 x103))) 
                           (SIG x103 x102))) 
                   (GRN x102)))
         :named hyp27))
(assert (! (and 
               (forall ((x105 R) (x106 B) (x107 B)) 
                   (=> 
                       (and 
                           (fst x105 x106) 
                           (rdy x105) 
                           (fst x105 x107)) 
                       (= x106 x107))) 
               (forall ((x108 R)) 
                   (=> 
                       (rdy x108) 
                       (exists ((x109 B)) 
                           (and 
                               (fst x108 x109) 
                               (rdy x108))))) 
               (forall ((x110 B) (x111 R) (x112 R)) 
                   (=> 
                       (and 
                           (fst x111 x110) 
                           (rdy x111) 
                           (fst x112 x110) 
                           (rdy x112)) 
                       (= x111 x112))))
         :named hyp28))
(assert (! (and 
               (forall ((x113 B) (x114 B)) 
                   (=> 
                       (and 
                           (or 
                               (MS x113 x114 lft) 
                               (MS x113 x114 rht)) 
                           (or 
                               (MS x113 x114 TRK) 
                               (MS x114 x113 TRK))) 
                       (MS0 x113 blpt))) 
               (forall ((x115 B) (x116 B) (x117 B)) 
                   (=> 
                       (and 
                           (or 
                               (MS x115 x116 lft) 
                               (MS x115 x116 rht)) 
                           (or 
                               (MS x115 x116 TRK) 
                               (MS x116 x115 TRK)) 
                           (or 
                               (MS x115 x117 lft) 
                               (MS x115 x117 rht)) 
                           (or 
                               (MS x115 x117 TRK) 
                               (MS x117 x115 TRK))) 
                       (= x116 x117))))
         :named hyp29))
(assert (! (and 
               (resrt r) 
               (not 
                   (frm r)))
         :named hyp30))
(assert (! (exists ((x118 PBB)) 
               (nxt r x118))
         :named hyp31))
(assert (! (forall ((x119 R) (x120 PBB) (x121 PBB)) 
               (=> 
                   (and 
                       (nxt x119 x120) 
                       (nxt x119 x121)) 
                   (forall ((x122 B) (x123 B)) 
                       (= 
                           (MS x122 x123 x120) 
                           (MS x122 x123 x121)))))
         :named hyp32))
(assert (! (forall ((a B) (b0 B)) 
               (=> 
                   (and 
                       (MS0 b0 LBT) 
                       (exists ((x124 B) (x125 PBB)) 
                           (and 
                               (exists ((x126 R)) 
                                   (and 
                                       (rsrtbl b0 x126) 
                                       (nxt x126 x125))) 
                               (MS x124 b0 x125))) 
                       (exists ((x127 PBB)) 
                           (and 
                               (exists ((x128 R)) 
                                   (and 
                                       (rsrtbl b0 x128) 
                                       (nxt x128 x127))) 
                               (MS a b0 x127))) 
                       (exists ((x129 R)) 
                           (rsrtbl a x129))) 
                   (not 
                       (exists ((x130 R)) 
                           (and 
                               (rsrtbl b0 x130) 
                               (rsrtbl a x130))))))
         :named hyp33))
(assert (! (forall ((r4 R) (S1 PB0)) 
               (=> 
                   (forall ((x131 B)) 
                       (=> 
                           (MS0 x131 S1) 
                           (exists ((x132 B)) 
                               (and 
                                   (MS0 x132 S1) 
                                   (exists ((x133 PBB)) 
                                       (and 
                                           (nxt r4 x133) 
                                           (MS x132 x131 x133))))))) 
                   (forall ((x134 B)) 
                       (not 
                           (MS0 x134 S1)))))
         :named hyp34))
(assert (! (and 
               (forall ((r5 R)) 
                   (forall ((x135 B) (x136 B)) 
                       (=> 
                           (exists ((x137 PBB)) 
                               (and 
                                   (nxt r5 x137) 
                                   (MS x135 x136 x137))) 
                           (and 
                               (exists ((x138 R)) 
                                   (and 
                                       (= x138 r5) 
                                       (rtbl x135 x138))) 
                               (not 
                                   (lst r5 x135)) 
                               (exists ((x139 R)) 
                                   (and 
                                       (= x139 r5) 
                                       (rtbl x136 x139))) 
                               (not 
                                   (fst r5 x136)))))) 
               (forall ((r6 R)) 
                   (forall ((x140 B) (x141 B) (x142 B)) 
                       (=> 
                           (and 
                               (exists ((x143 PBB)) 
                                   (and 
                                       (nxt r6 x143) 
                                       (MS x140 x141 x143))) 
                               (exists ((x144 PBB)) 
                                   (and 
                                       (nxt r6 x144) 
                                       (MS x140 x142 x144)))) 
                           (= x141 x142)))) 
               (forall ((r7 R)) 
                   (forall ((x145 B)) 
                       (=> 
                           (and 
                               (exists ((x146 R)) 
                                   (and 
                                       (= x146 r7) 
                                       (rtbl x145 x146))) 
                               (not 
                                   (lst r7 x145))) 
                           (exists ((x147 B) (x148 PBB)) 
                               (and 
                                   (nxt r7 x148) 
                                   (MS x145 x147 x148)))))) 
               (forall ((r8 R)) 
                   (forall ((x149 B)) 
                       (=> 
                           (and 
                               (exists ((x150 R)) 
                                   (and 
                                       (= x150 r8) 
                                       (rtbl x149 x150))) 
                               (not 
                                   (fst r8 x149))) 
                           (exists ((x151 B) (x152 PBB)) 
                               (and 
                                   (nxt r8 x152) 
                                   (MS x151 x149 x152)))))) 
               (forall ((r9 R)) 
                   (forall ((x153 B) (x154 B) (x155 B)) 
                       (=> 
                           (and 
                               (exists ((x156 PBB)) 
                                   (and 
                                       (nxt r9 x156) 
                                       (MS x154 x153 x156))) 
                               (exists ((x157 PBB)) 
                                   (and 
                                       (nxt r9 x157) 
                                       (MS x155 x153 x157)))) 
                           (= x154 x155)))))
         :named hyp35))
(assert (! (and 
               (forall ((r10 R)) 
                   (forall ((x158 B) (x159 B)) 
                       (=> 
                           (and 
                               (or 
                                   (MS x158 x159 lft) 
                                   (MS x158 x159 rht)) 
                               (or 
                                   (exists ((x160 PBB)) 
                                       (and 
                                           (nxt r10 x160) 
                                           (MS x158 x159 x160))) 
                                   (exists ((x161 PBB)) 
                                       (and 
                                           (nxt r10 x161) 
                                           (MS x159 x158 x161))))) 
                           (MS0 x158 blpt)))) 
               (forall ((r11 R)) 
                   (forall ((x162 B) (x163 B) (x164 B)) 
                       (=> 
                           (and 
                               (or 
                                   (MS x162 x163 lft) 
                                   (MS x162 x163 rht)) 
                               (or 
                                   (exists ((x165 PBB)) 
                                       (and 
                                           (nxt r11 x165) 
                                           (MS x162 x163 x165))) 
                                   (exists ((x166 PBB)) 
                                       (and 
                                           (nxt r11 x166) 
                                           (MS x163 x162 x166)))) 
                               (or 
                                   (MS x162 x164 lft) 
                                   (MS x162 x164 rht)) 
                               (or 
                                   (exists ((x167 PBB)) 
                                       (and 
                                           (nxt r11 x167) 
                                           (MS x162 x164 x167))) 
                                   (exists ((x168 PBB)) 
                                       (and 
                                           (nxt r11 x168) 
                                           (MS x164 x162 x168))))) 
                           (= x163 x164)))))
         :named hyp36))
(assert (! (forall ((r12 R) (x169 B)) 
               (=> 
                   (exists ((x170 B)) 
                       (and 
                           (exists ((x171 R)) 
                               (and 
                                   (= x171 r12) 
                                   (rsrtbl x170 x171))) 
                           (exists ((x172 PBB)) 
                               (and 
                                   (nxt r12 x172) 
                                   (MS x170 x169 x172))))) 
                   (exists ((x173 R)) 
                       (and 
                           (= x173 r12) 
                           (rsrtbl x169 x173)))))
         :named hyp37))
(assert (! (forall ((r13 R) (x174 B)) 
               (=> 
                   (exists ((x175 B)) 
                       (and 
                           (exists ((x176 R)) 
                               (and 
                                   (= x176 r13) 
                                   (rsrtbl x175 x176))) 
                           (not 
                               (MS0 x175 OCC)) 
                           (exists ((x177 PBB)) 
                               (and 
                                   (nxt r13 x177) 
                                   (MS x175 x174 x177))))) 
                   (and 
                       (exists ((x178 R)) 
                           (and 
                               (= x178 r13) 
                               (rsrtbl x174 x178))) 
                       (not 
                           (MS0 x174 OCC)))))
         :named hyp38))
(assert (! (forall ((x179 B) (y B)) 
               (=> 
                   (MS x179 y TRK) 
                   (exists ((r14 R) (x180 PBB)) 
                       (and 
                           (nxt r14 x180) 
                           (MS x179 y x180)))))
         :named hyp39))
(assert (! (forall ((r15 R)) 
               (not 
                   (exists ((x181 B)) 
                       (and 
                           (lst r15 x181) 
                           (fst r15 x181)))))
         :named hyp40))
(assert (! (forall ((r16 R) (s R)) 
               (=> 
                   (not 
                       (= r16 s)) 
                   (not 
                       (and 
                           (exists ((x182 R)) 
                               (and 
                                   (= x182 s) 
                                   (exists ((x183 B)) 
                                       (and 
                                           (fst r16 x183) 
                                           (rtbl x183 x182))))) 
                           (not 
                               (or 
                                   (exists ((x184 B)) 
                                       (and 
                                           (fst s x184) 
                                           (fst r16 x184))) 
                                   (exists ((x185 B)) 
                                       (and 
                                           (lst s x185) 
                                           (fst r16 x185)))))))))
         :named hyp41))
(assert (! (forall ((r17 R) (s0 R)) 
               (=> 
                   (not 
                       (= r17 s0)) 
                   (not 
                       (and 
                           (exists ((x186 R)) 
                               (and 
                                   (= x186 s0) 
                                   (exists ((x187 B)) 
                                       (and 
                                           (lst r17 x187) 
                                           (rtbl x187 x186))))) 
                           (not 
                               (or 
                                   (exists ((x188 B)) 
                                       (and 
                                           (fst s0 x188) 
                                           (lst r17 x188))) 
                                   (exists ((x189 B)) 
                                       (and 
                                           (lst s0 x189) 
                                           (lst r17 x189)))))))))
         :named hyp42))
(assert (! (forall ((r18 R) (x190 B)) 
               (=> 
                   (and 
                       (exists ((x191 B)) 
                           (and 
                               (exists ((x192 R)) 
                                   (and 
                                       (= x192 r18) 
                                       (rtbl x191 x192))) 
                               (not 
                                   (exists ((x193 R)) 
                                       (and 
                                           (= x193 r18) 
                                           (rsrtbl x191 x193)))) 
                               (exists ((x194 PBB)) 
                                   (and 
                                       (nxt r18 x194) 
                                       (MS x191 x190 x194))))) 
                       (exists ((x195 R)) 
                           (and 
                               (= x195 r18) 
                               (rsrtbl x190 x195)))) 
                   (MS0 x190 OCC)))
         :named hyp43))
(assert (! (not 
               (and 
                   (forall ((x196 B) (x197 B)) 
                       (=> 
                           (and 
                               (or 
                                   (MS x196 x197 lft) 
                                   (MS x196 x197 rht)) 
                               (or 
                                   (and 
                                       (MS x196 x197 TRK) 
                                       (not 
                                           (exists ((x198 B) (x199 PBB)) 
                                               (and 
                                                   (nxt r x199) 
                                                   (MS x196 x198 x199)))) 
                                       (not 
                                           (exists ((x200 B) (x201 PBB)) 
                                               (and 
                                                   (nxt r x201) 
                                                   (MS x200 x197 x201))))) 
                                   (exists ((x202 PBB)) 
                                       (and 
                                           (nxt r x202) 
                                           (MS x196 x197 x202))) 
                                   (and 
                                       (MS x197 x196 TRK) 
                                       (not 
                                           (exists ((x203 B) (x204 PBB)) 
                                               (and 
                                                   (nxt r x204) 
                                                   (MS x197 x203 x204)))) 
                                       (not 
                                           (exists ((x205 B) (x206 PBB)) 
                                               (and 
                                                   (nxt r x206) 
                                                   (MS x205 x196 x206))))) 
                                   (exists ((x207 PBB)) 
                                       (and 
                                           (nxt r x207) 
                                           (MS x197 x196 x207))))) 
                           (MS0 x196 blpt))) 
                   (forall ((x208 B) (x209 B) (x210 B)) 
                       (=> 
                           (and 
                               (or 
                                   (MS x208 x209 lft) 
                                   (MS x208 x209 rht)) 
                               (or 
                                   (and 
                                       (MS x208 x209 TRK) 
                                       (not 
                                           (exists ((x211 B) (x212 PBB)) 
                                               (and 
                                                   (nxt r x212) 
                                                   (MS x208 x211 x212)))) 
                                       (not 
                                           (exists ((x213 B) (x214 PBB)) 
                                               (and 
                                                   (nxt r x214) 
                                                   (MS x213 x209 x214))))) 
                                   (exists ((x215 PBB)) 
                                       (and 
                                           (nxt r x215) 
                                           (MS x208 x209 x215))) 
                                   (and 
                                       (MS x209 x208 TRK) 
                                       (not 
                                           (exists ((x216 B) (x217 PBB)) 
                                               (and 
                                                   (nxt r x217) 
                                                   (MS x209 x216 x217)))) 
                                       (not 
                                           (exists ((x218 B) (x219 PBB)) 
                                               (and 
                                                   (nxt r x219) 
                                                   (MS x218 x208 x219))))) 
                                   (exists ((x220 PBB)) 
                                       (and 
                                           (nxt r x220) 
                                           (MS x209 x208 x220)))) 
                               (or 
                                   (MS x208 x210 lft) 
                                   (MS x208 x210 rht)) 
                               (or 
                                   (and 
                                       (MS x208 x210 TRK) 
                                       (not 
                                           (exists ((x221 B) (x222 PBB)) 
                                               (and 
                                                   (nxt r x222) 
                                                   (MS x208 x221 x222)))) 
                                       (not 
                                           (exists ((x223 B) (x224 PBB)) 
                                               (and 
                                                   (nxt r x224) 
                                                   (MS x223 x210 x224))))) 
                                   (exists ((x225 PBB)) 
                                       (and 
                                           (nxt r x225) 
                                           (MS x208 x210 x225))) 
                                   (and 
                                       (MS x210 x208 TRK) 
                                       (not 
                                           (exists ((x226 B) (x227 PBB)) 
                                               (and 
                                                   (nxt r x227) 
                                                   (MS x210 x226 x227)))) 
                                       (not 
                                           (exists ((x228 B) (x229 PBB)) 
                                               (and 
                                                   (nxt r x229) 
                                                   (MS x228 x208 x229))))) 
                                   (exists ((x230 PBB)) 
                                       (and 
                                           (nxt r x230) 
                                           (MS x210 x208 x230))))) 
                           (= x209 x210)))))
         :named goal))
(check-sat)
(exit)

