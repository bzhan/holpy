(set-info :smt-lib-version 2.6)
(set-logic AUFLIA)
(set-info :source |Generator: Rodin SMT Plug-in|)
(set-info :license "https://creativecommons.org/licenses/by-nc/4.0/")
(set-info :category "industrial")
(set-info :status unsat)

(declare-sort D 0)
(declare-sort PZD 0)
(declare-sort PZZ 0)
(declare-fun Data (Int PZD) Bool)
(declare-fun MS (Int D PZD) Bool)
(declare-fun MS0 (Int Int PZZ) Bool)
(declare-fun data (Int PZD) Bool)
(declare-fun idata (Int PZZ) Bool)
(declare-fun adr_r () Int)
(declare-fun adr_w () Int)
(declare-fun f () PZZ)
(declare-fun g () PZZ)
(declare-fun indx_r () Int)
(declare-fun indx_w () Int)
(declare-fun indx_wp () Int)
(declare-fun latest () Int)
(declare-fun m () Int)
(declare-fun pair_w () Int)
(declare-fun r () Int)
(declare-fun rd () PZD)
(declare-fun reading () Int)
(declare-fun slot () PZZ)
(declare-fun u () Int)
(declare-fun w () Int)
(declare-fun wt () PZD)
(declare-fun wtp () PZD)
(declare-fun x () D)
(declare-fun y () D)

; Elementary Sets axiom (Singleton part)
(assert (forall ((x292 Int) (x293 D)) 
            (exists ((X PZD)) 
                (and 
                    (MS x292 x293 X) 
                    (forall ((y0 Int) (y1 D)) 
                        (=> 
                            (MS y0 y1 X) 
                            (and 
                                (= y0 x292) 
                                (= y1 x293))))))))
; Elementary Sets axiom (Singleton part)
(assert (forall ((x294 Int) (x295 Int)) 
            (exists ((X0 PZZ)) 
                (and 
                    (MS0 x294 x295 X0) 
                    (forall ((y2 Int) (y3 Int)) 
                        (=> 
                            (MS0 y2 y3 X0) 
                            (and 
                                (= y2 x294) 
                                (= y3 x295))))))))
(assert (! (< 0 w)
         :named hyp1))
(assert (! (< 0 r)
         :named hyp2))
(assert (! (and 
               (forall ((x0 Int) (x1 D)) 
                   (=> 
                       (MS x0 x1 wt) 
                       (and 
                           (<= 1 x0) 
                           (<= x0 w)))) 
               (forall ((x2 Int) (x3 D) (x4 D)) 
                   (=> 
                       (and 
                           (MS x2 x3 wt) 
                           (MS x2 x4 wt)) 
                       (= x3 x4))) 
               (forall ((x5 Int)) 
                   (=> 
                       (and 
                           (<= 1 x5) 
                           (<= x5 w)) 
                       (exists ((x6 D)) 
                           (MS x5 x6 wt)))))
         :named hyp3))
(assert (! (and 
               (forall ((x7 Int) (x8 D)) 
                   (=> 
                       (MS x7 x8 rd) 
                       (and 
                           (<= 1 x7) 
                           (<= x7 r)))) 
               (forall ((x9 Int) (x10 D) (x11 D)) 
                   (=> 
                       (and 
                           (MS x9 x10 rd) 
                           (MS x9 x11 rd)) 
                       (= x10 x11))) 
               (forall ((x12 Int)) 
                   (=> 
                       (and 
                           (<= 1 x12) 
                           (<= x12 r)) 
                       (exists ((x13 D)) 
                           (MS x12 x13 rd)))))
         :named hyp4))
(assert (! (and 
               (forall ((x14 Int) (x15 Int)) 
                   (=> 
                       (MS0 x14 x15 f) 
                       (and 
                           (<= 1 x14) 
                           (<= x14 r) 
                           (<= 1 x15) 
                           (<= x15 w)))) 
               (forall ((x16 Int) (x17 Int) (x18 Int)) 
                   (=> 
                       (and 
                           (MS0 x16 x17 f) 
                           (MS0 x16 x18 f)) 
                       (= x17 x18))) 
               (forall ((x19 Int)) 
                   (=> 
                       (and 
                           (<= 1 x19) 
                           (<= x19 r)) 
                       (exists ((x20 Int)) 
                           (MS0 x19 x20 f)))))
         :named hyp5))
(assert (! (and 
               (forall ((x21 Int) (x22 Int)) 
                   (=> 
                       (MS0 x21 x22 g) 
                       (and 
                           (<= 1 x21) 
                           (<= x21 r) 
                           (<= 1 x22) 
                           (<= x22 w)))) 
               (forall ((x23 Int) (x24 Int) (x25 Int)) 
                   (=> 
                       (and 
                           (MS0 x23 x24 g) 
                           (MS0 x23 x25 g)) 
                       (= x24 x25))) 
               (forall ((x26 Int)) 
                   (=> 
                       (and 
                           (<= 1 x26) 
                           (<= x26 r)) 
                       (exists ((x27 Int)) 
                           (MS0 x26 x27 g)))))
         :named hyp6))
(assert (! (forall ((x28 Int) (x29 D)) 
               (= 
                   (MS x28 x29 rd) 
                   (exists ((x30 Int)) 
                       (and 
                           (MS0 x28 x30 f) 
                           (MS x30 x29 wt)))))
         :named hyp7))
(assert (! (forall ((i Int)) 
               (=> 
                   (and 
                       (<= 1 i) 
                       (<= i r)) 
                   (forall ((x31 Int) (x32 Int)) 
                       (=> 
                           (and 
                               (MS0 i x32 f) 
                               (MS0 i x31 g)) 
                           (<= x32 x31)))))
         :named hyp8))
(assert (! (forall ((i0 Int)) 
               (=> 
                   (and 
                       (<= 1 i0) 
                       (<= i0 (- r 1))) 
                   (forall ((x33 Int) (x34 Int)) 
                       (=> 
                           (and 
                               (MS0 i0 x34 g) 
                               (exists ((x35 Int)) 
                                   (and 
                                       (= x35 (+ i0 1)) 
                                       (MS0 x35 x33 f)))) 
                           (<= x34 x33)))))
         :named hyp9))
(assert (! (or 
               (= adr_w 1) 
               (= adr_w 2) 
               (= adr_w 3) 
               (= adr_w 4) 
               (= adr_w 5))
         :named hyp10))
(assert (! (or 
               (= adr_r 1) 
               (= adr_r 2) 
               (= adr_r 3))
         :named hyp11))
(assert (! (MS0 r u g)
         :named hyp12))
(assert (! (exists ((x36 Int)) 
               (MS0 r x36 g))
         :named hyp13))
(assert (! (forall ((x37 Int) (x38 Int) (x39 Int)) 
               (=> 
                   (and 
                       (MS0 x37 x38 g) 
                       (MS0 x37 x39 g)) 
                   (= x38 x39)))
         :named hyp14))
(assert (! (MS0 r m f)
         :named hyp15))
(assert (! (exists ((x40 Int)) 
               (MS0 r x40 f))
         :named hyp16))
(assert (! (forall ((x41 Int) (x42 Int) (x43 Int)) 
               (=> 
                   (and 
                       (MS0 x41 x42 f) 
                       (MS0 x41 x43 f)) 
                   (= x42 x43)))
         :named hyp17))
(assert (! (and 
               (forall ((x44 Int) (x45 D)) 
                   (=> 
                       (MS x44 x45 wtp) 
                       (< 0 x44))) 
               (forall ((x46 Int) (x47 D) (x48 D)) 
                   (=> 
                       (and 
                           (MS x46 x47 wtp) 
                           (MS x46 x48 wtp)) 
                       (= x47 x48))))
         :named hyp18))
(assert (! (=> 
               (= adr_r 1) 
               (MS r y rd))
         :named hyp19))
(assert (! (=> 
               (= adr_r 1) 
               (and 
                   (exists ((x49 D)) 
                       (MS r x49 rd)) 
                   (forall ((x50 Int) (x51 D) (x52 D)) 
                       (=> 
                           (and 
                               (MS x50 x51 rd) 
                               (MS x50 x52 rd)) 
                           (= x51 x52)))))
         :named hyp20))
(assert (! (forall ((x53 Int) (x54 D)) 
               (=> 
                   (MS x53 x54 wt) 
                   (MS x53 x54 wtp)))
         :named hyp21))
(assert (! (=> 
               (= adr_w 1) 
               (forall ((x55 Int)) 
                   (= 
                       (exists ((x56 D)) 
                           (MS x55 x56 wtp)) 
                       (and 
                           (<= 1 x55) 
                           (<= x55 w)))))
         :named hyp22))
(assert (! (=> 
               (or 
                   (= adr_w 2) 
                   (= adr_w 3) 
                   (= adr_w 4)) 
               (forall ((x57 Int)) 
                   (= 
                       (exists ((x58 D)) 
                           (MS x57 x58 wtp)) 
                       (and 
                           (<= 1 x57) 
                           (<= x57 (+ w 1))))))
         :named hyp23))
(assert (! (=> 
               (= adr_w 5) 
               (or 
                   (forall ((x59 Int)) 
                       (= 
                           (exists ((x60 D)) 
                               (MS x59 x60 wtp)) 
                           (and 
                               (<= 1 x59) 
                               (<= x59 w)))) 
                   (forall ((x61 Int)) 
                       (= 
                           (exists ((x62 D)) 
                               (MS x61 x62 wtp)) 
                           (and 
                               (<= 1 x61) 
                               (<= x61 (+ w 1)))))))
         :named hyp24))
(assert (! (or 
               (= reading 0) 
               (= reading 1))
         :named hyp25))
(assert (! (or 
               (= pair_w 0) 
               (= pair_w 1))
         :named hyp26))
(assert (! (or 
               (= latest 0) 
               (= latest 1))
         :named hyp27))
(assert (! (or 
               (= indx_r 0) 
               (= indx_r 1))
         :named hyp28))
(assert (! (or 
               (= indx_wp 0) 
               (= indx_wp 1))
         :named hyp29))
(assert (! (and 
               (forall ((x63 Int) (x64 Int)) 
                   (=> 
                       (MS0 x63 x64 slot) 
                       (and 
                           (or 
                               (= x63 0) 
                               (= x63 1)) 
                           (or 
                               (= x64 0) 
                               (= x64 1))))) 
               (forall ((x65 Int) (x66 Int) (x67 Int)) 
                   (=> 
                       (and 
                           (MS0 x65 x66 slot) 
                           (MS0 x65 x67 slot)) 
                       (= x66 x67))) 
               (forall ((x68 Int)) 
                   (=> 
                       (or 
                           (= x68 0) 
                           (= x68 1)) 
                       (exists ((x69 Int)) 
                           (MS0 x68 x69 slot)))))
         :named hyp30))
(assert (! (and 
               (forall ((x70 Int) (x71 PZZ)) 
                   (=> 
                       (idata x70 x71) 
                       (and 
                           (or 
                               (= x70 0) 
                               (= x70 1)) 
                           (forall ((x72 Int) (x73 Int)) 
                               (=> 
                                   (MS0 x72 x73 x71) 
                                   (and 
                                       (or 
                                           (= x72 0) 
                                           (= x72 1)) 
                                       (exists ((x74 D)) 
                                           (MS x73 x74 wtp))))) 
                           (forall ((x75 Int) (x76 Int) (x77 Int)) 
                               (=> 
                                   (and 
                                       (MS0 x75 x76 x71) 
                                       (MS0 x75 x77 x71)) 
                                   (= x76 x77))) 
                           (forall ((x78 Int)) 
                               (=> 
                                   (or 
                                       (= x78 0) 
                                       (= x78 1)) 
                                   (exists ((x79 Int)) 
                                       (MS0 x78 x79 x71))))))) 
               (forall ((x80 Int) (x81 PZZ) (x82 PZZ)) 
                   (=> 
                       (and 
                           (idata x80 x81) 
                           (idata x80 x82)) 
                       (forall ((x83 Int) (x84 Int)) 
                           (= 
                               (MS0 x83 x84 x81) 
                               (MS0 x83 x84 x82))))) 
               (forall ((x85 Int)) 
                   (=> 
                       (or 
                           (= x85 0) 
                           (= x85 1)) 
                       (exists ((x86 PZZ)) 
                           (idata x85 x86)))))
         :named hyp31))
(assert (! (=> 
               (= adr_r 2) 
               (and 
                   (forall ((x87 Int)) 
                       (=> 
                           (exists ((x88 PZZ)) 
                               (and 
                                   (idata reading x88) 
                                   (exists ((x89 Int)) 
                                       (and 
                                           (MS0 reading x89 slot) 
                                           (MS0 x89 x87 x88))))) 
                           (<= u x87))) 
                   (forall ((x90 Int)) 
                       (=> 
                           (exists ((x91 PZZ)) 
                               (and 
                                   (idata reading x91) 
                                   (exists ((x92 Int)) 
                                       (and 
                                           (MS0 reading x92 slot) 
                                           (MS0 x92 x90 x91))))) 
                           (<= x90 w)))))
         :named hyp32))
(assert (! (=> 
               (= adr_r 3) 
               (exists ((x93 PZZ)) 
                   (and 
                       (idata reading x93) 
                       (MS0 indx_r m x93))))
         :named hyp33))
(assert (! (exists ((x94 PZZ)) 
               (and 
                   (idata latest x94) 
                   (exists ((x95 Int)) 
                       (and 
                           (MS0 latest x95 slot) 
                           (MS0 x95 w x94)))))
         :named hyp34))
(assert (! (exists ((x96 PZZ)) 
               (idata latest x96))
         :named hyp35))
(assert (! (forall ((x97 Int) (x98 PZZ) (x99 PZZ)) 
               (=> 
                   (and 
                       (idata x97 x98) 
                       (idata x97 x99)) 
                   (forall ((x100 Int) (x101 Int)) 
                       (= 
                           (MS0 x100 x101 x98) 
                           (MS0 x100 x101 x99)))))
         :named hyp36))
(assert (! (exists ((x102 Int)) 
               (MS0 latest x102 slot))
         :named hyp37))
(assert (! (forall ((x103 Int) (x104 Int) (x105 Int)) 
               (=> 
                   (and 
                       (MS0 x103 x104 slot) 
                       (MS0 x103 x105 slot)) 
                   (= x104 x105)))
         :named hyp38))
(assert (! (exists ((x106 Int) (x107 PZZ)) 
               (and 
                   (idata latest x107) 
                   (exists ((x108 Int)) 
                       (and 
                           (MS0 latest x108 slot) 
                           (MS0 x108 x106 x107)))))
         :named hyp39))
(assert (! (forall ((x109 Int) (x110 Int) (x111 Int)) 
               (=> 
                   (and 
                       (exists ((x112 PZZ)) 
                           (and 
                               (idata latest x112) 
                               (MS0 x109 x110 x112))) 
                       (exists ((x113 PZZ)) 
                           (and 
                               (idata latest x113) 
                               (MS0 x109 x111 x113)))) 
                   (= x110 x111)))
         :named hyp40))
(assert (! (=> 
               (= adr_w 1) 
               (= pair_w latest))
         :named hyp41))
(assert (! (=> 
               (= reading pair_w) 
               (= latest reading))
         :named hyp42))
(assert (! (=> 
               (or 
                   (= adr_w 1) 
                   (= adr_w 5)) 
               (MS0 pair_w indx_wp slot))
         :named hyp43))
(assert (! (=> 
               (or 
                   (= adr_w 2) 
                   (= adr_w 3) 
                   (= adr_w 4)) 
               (forall ((x114 Int)) 
                   (=> 
                       (MS0 pair_w x114 slot) 
                       (= indx_wp (- 1 x114)))))
         :named hyp44))
(assert (! (=> 
               (and 
                   (= adr_w 5) 
                   (= latest pair_w)) 
               (forall ((x115 Int)) 
                   (= 
                       (exists ((x116 D)) 
                           (MS x115 x116 wtp)) 
                       (and 
                           (<= 1 x115) 
                           (<= x115 w)))))
         :named hyp45))
(assert (! (=> 
               (and 
                   (= adr_w 5) 
                   (forall ((x117 Int)) 
                       (= 
                           (exists ((x118 D)) 
                               (MS x117 x118 wtp)) 
                           (and 
                               (<= 1 x117) 
                               (<= x117 w))))) 
               (= latest pair_w))
         :named hyp46))
(assert (! (exists ((x119 PZZ)) 
               (and 
                   (idata pair_w x119) 
                   (exists ((x120 Int)) 
                       (and 
                           (exists ((x121 D)) 
                               (MS x120 x121 wtp)) 
                           (forall ((x122 Int)) 
                               (=> 
                                   (exists ((x123 D)) 
                                       (MS x122 x123 wtp)) 
                                   (<= x122 x120))) 
                           (MS0 indx_wp x120 x119)))))
         :named hyp47))
(assert (! (exists ((x124 PZZ)) 
               (idata pair_w x124))
         :named hyp48))
(assert (! (exists ((x125 Int) (x126 PZZ)) 
               (and 
                   (idata pair_w x126) 
                   (MS0 indx_wp x125 x126)))
         :named hyp49))
(assert (! (forall ((x127 Int) (x128 Int) (x129 Int)) 
               (=> 
                   (and 
                       (exists ((x130 PZZ)) 
                           (and 
                               (idata pair_w x130) 
                               (MS0 x127 x128 x130))) 
                       (exists ((x131 PZZ)) 
                           (and 
                               (idata pair_w x131) 
                               (MS0 x127 x129 x131)))) 
                   (= x128 x129)))
         :named hyp50))
(assert (! (exists ((b Int)) 
               (forall ((x132 Int)) 
                   (=> 
                       (exists ((x133 D)) 
                           (MS x132 x133 wtp)) 
                       (<= x132 b))))
         :named hyp51))
(assert (! (not 
               (= reading (- 1 reading)))
         :named hyp52))
(assert (! (not 
               (exists ((x134 Int) (x135 Int)) 
                   (and 
                       (= x134 (- 1 reading)) 
                       (forall ((x136 Int)) 
                           (=> 
                               (exists ((x137 Int)) 
                                   (and 
                                       (= x137 (- 1 reading)) 
                                       (MS0 x137 x136 slot))) 
                               (= x135 (- 1 x136)))) 
                       (MS0 x134 x135 slot))))
         :named hyp53))
(assert (! (exists ((x138 Int) (x139 Int)) 
               (and 
                   (= x139 (- 1 reading)) 
                   (MS0 x139 x138 slot)))
         :named hyp54))
(assert (! (and 
               (forall ((x140 Int) (x141 PZD)) 
                   (=> 
                       (Data x140 x141) 
                       (and 
                           (or 
                               (= x140 0) 
                               (= x140 1)) 
                           (forall ((x142 Int) (x143 D)) 
                               (=> 
                                   (MS x142 x143 x141) 
                                   (or 
                                       (= x142 0) 
                                       (= x142 1)))) 
                           (forall ((x144 Int) (x145 D) (x146 D)) 
                               (=> 
                                   (and 
                                       (MS x144 x145 x141) 
                                       (MS x144 x146 x141)) 
                                   (= x145 x146))) 
                           (forall ((x147 Int)) 
                               (=> 
                                   (or 
                                       (= x147 0) 
                                       (= x147 1)) 
                                   (exists ((x148 D)) 
                                       (MS x147 x148 x141))))))) 
               (forall ((x149 Int) (x150 PZD) (x151 PZD)) 
                   (=> 
                       (and 
                           (Data x149 x150) 
                           (Data x149 x151)) 
                       (forall ((x152 Int) (x153 D)) 
                           (= 
                               (MS x152 x153 x150) 
                               (MS x152 x153 x151))))) 
               (forall ((x154 Int)) 
                   (=> 
                       (or 
                           (= x154 0) 
                           (= x154 1)) 
                       (exists ((x155 PZD)) 
                           (Data x154 x155)))))
         :named hyp55))
(assert (! (forall ((x156 Int) (z Int)) 
               (=> 
                   (and 
                       (or 
                           (= x156 0) 
                           (= x156 1)) 
                       (or 
                           (= z 0) 
                           (= z 1))) 
                   (exists ((x157 Int) (x158 D)) 
                       (and 
                           (exists ((x159 PZZ)) 
                               (and 
                                   (idata x156 x159) 
                                   (MS0 z x157 x159))) 
                           (exists ((x160 PZD)) 
                               (and 
                                   (Data x156 x160) 
                                   (MS z x158 x160))) 
                           (MS x157 x158 wtp)))))
         :named hyp56))
(assert (! (and 
               (forall ((x161 Int) (x162 PZD)) 
                   (=> 
                       (data x161 x162) 
                       (and 
                           (or 
                               (= x161 0) 
                               (= x161 1)) 
                           (forall ((x163 Int) (x164 D)) 
                               (=> 
                                   (MS x163 x164 x162) 
                                   (or 
                                       (= x163 0) 
                                       (= x163 1)))) 
                           (forall ((x165 Int) (x166 D) (x167 D)) 
                               (=> 
                                   (and 
                                       (MS x165 x166 x162) 
                                       (MS x165 x167 x162)) 
                                   (= x166 x167))) 
                           (forall ((x168 Int)) 
                               (=> 
                                   (or 
                                       (= x168 0) 
                                       (= x168 1)) 
                                   (exists ((x169 D)) 
                                       (MS x168 x169 x162))))))) 
               (forall ((x170 Int) (x171 PZD) (x172 PZD)) 
                   (=> 
                       (and 
                           (data x170 x171) 
                           (data x170 x172)) 
                       (forall ((x173 Int) (x174 D)) 
                           (= 
                               (MS x173 x174 x171) 
                               (MS x173 x174 x172))))) 
               (forall ((x175 Int)) 
                   (=> 
                       (or 
                           (= x175 0) 
                           (= x175 1)) 
                       (exists ((x176 PZD)) 
                           (data x175 x176)))))
         :named hyp57))
(assert (! (or 
               (= indx_w 0) 
               (= indx_w 1))
         :named hyp58))
(assert (! (=> 
               (or 
                   (= adr_w 1) 
                   (= adr_w 4) 
                   (= adr_w 5)) 
               (forall ((x177 Int) (x178 PZD)) 
                   (= 
                       (Data x177 x178) 
                       (data x177 x178))))
         :named hyp59))
(assert (! (=> 
               (or 
                   (= adr_w 1) 
                   (= adr_w 3) 
                   (= adr_w 4) 
                   (= adr_w 5)) 
               (= indx_w indx_wp))
         :named hyp60))
(assert (! (=> 
               (and 
                   (= adr_w 2) 
                   (= adr_r 3) 
                   (= pair_w reading)) 
               (not 
                   (= indx_r indx_wp)))
         :named hyp61))
(assert (! (= adr_w 3)
         :named hyp62))
(assert (! (not 
               (forall ((x179 Int) (x180 D)) 
                   (not 
                       (MS x179 x180 wtp))))
         :named hyp63))
(assert (! (=> 
               (= adr_r 2) 
               (and 
                   (exists ((x181 PZZ)) 
                       (idata reading x181)) 
                   (exists ((x182 Int)) 
                       (MS0 reading x182 slot)) 
                   (exists ((x183 Int) (x184 PZZ)) 
                       (and 
                           (idata reading x184) 
                           (exists ((x185 Int)) 
                               (and 
                                   (MS0 reading x185 slot) 
                                   (MS0 x185 x183 x184))))) 
                   (forall ((x186 Int) (x187 Int) (x188 Int)) 
                       (=> 
                           (and 
                               (exists ((x189 PZZ)) 
                                   (and 
                                       (idata reading x189) 
                                       (MS0 x186 x187 x189))) 
                               (exists ((x190 PZZ)) 
                                   (and 
                                       (idata reading x190) 
                                       (MS0 x186 x188 x190)))) 
                           (= x187 x188)))))
         :named hyp64))
(assert (! (=> 
               (= adr_r 3) 
               (and 
                   (exists ((x191 PZZ)) 
                       (idata reading x191)) 
                   (exists ((x192 Int) (x193 PZZ)) 
                       (and 
                           (idata reading x193) 
                           (MS0 indx_r x192 x193))) 
                   (forall ((x194 Int) (x195 Int) (x196 Int)) 
                       (=> 
                           (and 
                               (exists ((x197 PZZ)) 
                                   (and 
                                       (idata reading x197) 
                                       (MS0 x194 x195 x197))) 
                               (exists ((x198 PZZ)) 
                                   (and 
                                       (idata reading x198) 
                                       (MS0 x194 x196 x198)))) 
                           (= x195 x196)))))
         :named hyp65))
(assert (! (=> 
               (or 
                   (= adr_w 1) 
                   (= adr_w 5)) 
               (exists ((x199 Int)) 
                   (MS0 pair_w x199 slot)))
         :named hyp66))
(assert (! (=> 
               (or 
                   (= adr_w 2) 
                   (= adr_w 3) 
                   (= adr_w 4)) 
               (exists ((x200 Int)) 
                   (MS0 pair_w x200 slot)))
         :named hyp67))
(assert (! (=> 
               (and 
                   (= adr_r 3) 
                   (= pair_w reading)) 
               (not 
                   (= indx_r indx_wp)))
         :named hyp68))
(assert (! (or 
               (= 4 2) 
               (= 4 3))
         :named hyp69))
(assert (! (exists ((x201 PZD)) 
               (data pair_w x201))
         :named hyp70))
(assert (! (forall ((x202 Int) (x203 PZD) (x204 PZD)) 
               (=> 
                   (and 
                       (data x202 x203) 
                       (data x202 x204)) 
                   (forall ((x205 Int) (x206 D)) 
                       (= 
                           (MS x205 x206 x203) 
                           (MS x205 x206 x204)))))
         :named hyp71))
(assert (! (or 
               (exists ((x207 PZD)) 
                   (and 
                       (data pair_w x207) 
                       (not 
                           (exists ((x208 PZD)) 
                               (forall ((x209 Int) (x210 D)) 
                                   (= 
                                       (MS x209 x210 x208) 
                                       (or 
                                           (and 
                                               (exists ((x211 PZD)) 
                                                   (and 
                                                       (data pair_w x211) 
                                                       (MS x209 x210 x211))) 
                                               (not 
                                                   (exists ((x212 D)) 
                                                       (and 
                                                           (= x209 indx_w) 
                                                           (= x212 x))))) 
                                           (and 
                                               (= x209 indx_w) 
                                               (= x210 x))))))))) 
               (exists ((x213 PZD)) 
                   (forall ((x214 Int) (x215 D)) 
                       (= 
                           (MS x214 x215 x213) 
                           (or 
                               (and 
                                   (exists ((x216 PZD)) 
                                       (and 
                                           (data pair_w x216) 
                                           (MS x214 x215 x216))) 
                                   (not 
                                       (exists ((x217 D)) 
                                           (and 
                                               (= x214 indx_w) 
                                               (= x217 x))))) 
                               (and 
                                   (= x214 indx_w) 
                                   (= x215 x)))))))
         :named hyp72))
(assert (! (forall ((x218 Int) (x219 PZD) (x220 PZD)) 
               (=> 
                   (and 
                       (or 
                           (and 
                               (data x218 x219) 
                               (not 
                                   (exists ((x221 PZD)) 
                                       (and 
                                           (= x218 pair_w) 
                                           (forall ((x222 Int) (x223 D)) 
                                               (= 
                                                   (MS x222 x223 x221) 
                                                   (or 
                                                       (and 
                                                           (exists ((x224 PZD)) 
                                                               (and 
                                                                   (data pair_w x224) 
                                                                   (MS x222 x223 x224))) 
                                                           (not 
                                                               (exists ((x225 D)) 
                                                                   (and 
                                                                       (= x222 indx_w) 
                                                                       (= x225 x))))) 
                                                       (and 
                                                           (= x222 indx_w) 
                                                           (= x223 x))))))))) 
                           (and 
                               (= x218 pair_w) 
                               (forall ((x226 Int) (x227 D)) 
                                   (= 
                                       (MS x226 x227 x219) 
                                       (or 
                                           (and 
                                               (exists ((x228 PZD)) 
                                                   (and 
                                                       (data pair_w x228) 
                                                       (MS x226 x227 x228))) 
                                               (not 
                                                   (exists ((x229 D)) 
                                                       (and 
                                                           (= x226 indx_w) 
                                                           (= x229 x))))) 
                                           (and 
                                               (= x226 indx_w) 
                                               (= x227 x))))))) 
                       (or 
                           (and 
                               (data x218 x220) 
                               (not 
                                   (exists ((x230 PZD)) 
                                       (and 
                                           (= x218 pair_w) 
                                           (forall ((x231 Int) (x232 D)) 
                                               (= 
                                                   (MS x231 x232 x230) 
                                                   (or 
                                                       (and 
                                                           (exists ((x233 PZD)) 
                                                               (and 
                                                                   (data pair_w x233) 
                                                                   (MS x231 x232 x233))) 
                                                           (not 
                                                               (exists ((x234 D)) 
                                                                   (and 
                                                                       (= x231 indx_w) 
                                                                       (= x234 x))))) 
                                                       (and 
                                                           (= x231 indx_w) 
                                                           (= x232 x))))))))) 
                           (and 
                               (= x218 pair_w) 
                               (forall ((x235 Int) (x236 D)) 
                                   (= 
                                       (MS x235 x236 x220) 
                                       (or 
                                           (and 
                                               (exists ((x237 PZD)) 
                                                   (and 
                                                       (data pair_w x237) 
                                                       (MS x235 x236 x237))) 
                                               (not 
                                                   (exists ((x238 D)) 
                                                       (and 
                                                           (= x235 indx_w) 
                                                           (= x238 x))))) 
                                           (and 
                                               (= x235 indx_w) 
                                               (= x236 x)))))))) 
                   (forall ((x239 Int) (x240 D)) 
                       (= 
                           (MS x239 x240 x219) 
                           (MS x239 x240 x220)))))
         :named hyp73))
(assert (! (forall ((x241 Int) (x242 PZD)) 
               (= 
                   (Data x241 x242) 
                   (or 
                       (and 
                           (data x241 x242) 
                           (not 
                               (exists ((x243 PZD)) 
                                   (and 
                                       (= x241 pair_w) 
                                       (forall ((x244 Int) (x245 D)) 
                                           (= 
                                               (MS x244 x245 x243) 
                                               (or 
                                                   (and 
                                                       (exists ((x246 PZD)) 
                                                           (and 
                                                               (data pair_w x246) 
                                                               (MS x244 x245 x246))) 
                                                       (not 
                                                           (exists ((x247 D)) 
                                                               (and 
                                                                   (= x244 indx_wp) 
                                                                   (= x247 x))))) 
                                                   (and 
                                                       (= x244 indx_wp) 
                                                       (= x245 x))))))))) 
                       (and 
                           (= x241 pair_w) 
                           (forall ((x248 Int) (x249 D)) 
                               (= 
                                   (MS x248 x249 x242) 
                                   (or 
                                       (and 
                                           (exists ((x250 PZD)) 
                                               (and 
                                                   (data pair_w x250) 
                                                   (MS x248 x249 x250))) 
                                           (not 
                                               (exists ((x251 D)) 
                                                   (and 
                                                       (= x248 indx_wp) 
                                                       (= x251 x))))) 
                                       (and 
                                           (= x248 indx_wp) 
                                           (= x249 x)))))))))
         :named hyp74))
(assert (! (not 
               (forall ((x252 Int) (x253 PZD)) 
                   (= 
                       (or 
                           (and 
                               (data x252 x253) 
                               (not 
                                   (exists ((x254 PZD)) 
                                       (and 
                                           (= x252 pair_w) 
                                           (forall ((x255 Int) (x256 D)) 
                                               (= 
                                                   (MS x255 x256 x254) 
                                                   (or 
                                                       (and 
                                                           (exists ((x257 PZD)) 
                                                               (and 
                                                                   (data pair_w x257) 
                                                                   (MS x255 x256 x257))) 
                                                           (not 
                                                               (exists ((x258 D)) 
                                                                   (and 
                                                                       (= x255 indx_wp) 
                                                                       (= x258 x))))) 
                                                       (and 
                                                           (= x255 indx_wp) 
                                                           (= x256 x))))))))) 
                           (and 
                               (= x252 pair_w) 
                               (forall ((x259 Int) (x260 D)) 
                                   (= 
                                       (MS x259 x260 x253) 
                                       (or 
                                           (and 
                                               (exists ((x261 PZD)) 
                                                   (and 
                                                       (data pair_w x261) 
                                                       (MS x259 x260 x261))) 
                                               (not 
                                                   (exists ((x262 D)) 
                                                       (and 
                                                           (= x259 indx_wp) 
                                                           (= x262 x))))) 
                                           (and 
                                               (= x259 indx_wp) 
                                               (= x260 x))))))) 
                       (or 
                           (and 
                               (data x252 x253) 
                               (not 
                                   (or 
                                       (exists ((x263 PZD)) 
                                           (and 
                                               (= x252 pair_w) 
                                               (forall ((x264 Int) (x265 D)) 
                                                   (= 
                                                       (MS x264 x265 x263) 
                                                       (or 
                                                           (and 
                                                               (exists ((x266 PZD)) 
                                                                   (and 
                                                                       (data pair_w x266) 
                                                                       (MS x264 x265 x266))) 
                                                               (not 
                                                                   (exists ((x267 D)) 
                                                                       (and 
                                                                           (= x264 indx_w) 
                                                                           (= x267 x))))) 
                                                           (and 
                                                               (= x264 indx_w) 
                                                               (= x265 x))))))) 
                                       (exists ((x268 PZD)) 
                                           (and 
                                               (= x252 pair_w) 
                                               (forall ((x269 Int) (x270 D)) 
                                                   (= 
                                                       (MS x269 x270 x268) 
                                                       (or 
                                                           (and 
                                                               (exists ((x271 PZD)) 
                                                                   (and 
                                                                       (data pair_w x271) 
                                                                       (MS x269 x270 x271))) 
                                                               (not 
                                                                   (or 
                                                                       (exists ((x272 D)) 
                                                                           (and 
                                                                               (= x269 indx_w) 
                                                                               (= x272 x))) 
                                                                       (exists ((x273 D)) 
                                                                           (and 
                                                                               (= x269 indx_wp) 
                                                                               (= x273 x)))))) 
                                                           (and 
                                                               (= x269 indx_w) 
                                                               (= x270 x) 
                                                               (not 
                                                                   (exists ((x274 D)) 
                                                                       (and 
                                                                           (= x269 indx_wp) 
                                                                           (= x274 x))))) 
                                                           (and 
                                                               (= x269 indx_wp) 
                                                               (= x270 x)))))))))) 
                           (and 
                               (= x252 pair_w) 
                               (forall ((x275 Int) (x276 D)) 
                                   (= 
                                       (MS x275 x276 x253) 
                                       (or 
                                           (and 
                                               (exists ((x277 PZD)) 
                                                   (and 
                                                       (data pair_w x277) 
                                                       (MS x275 x276 x277))) 
                                               (not 
                                                   (exists ((x278 D)) 
                                                       (and 
                                                           (= x275 indx_w) 
                                                           (= x278 x))))) 
                                           (and 
                                               (= x275 indx_w) 
                                               (= x276 x))))) 
                               (not 
                                   (exists ((x279 PZD)) 
                                       (and 
                                           (= x252 pair_w) 
                                           (forall ((x280 Int) (x281 D)) 
                                               (= 
                                                   (MS x280 x281 x279) 
                                                   (or 
                                                       (and 
                                                           (exists ((x282 PZD)) 
                                                               (and 
                                                                   (data pair_w x282) 
                                                                   (MS x280 x281 x282))) 
                                                           (not 
                                                               (or 
                                                                   (exists ((x283 D)) 
                                                                       (and 
                                                                           (= x280 indx_w) 
                                                                           (= x283 x))) 
                                                                   (exists ((x284 D)) 
                                                                       (and 
                                                                           (= x280 indx_wp) 
                                                                           (= x284 x)))))) 
                                                       (and 
                                                           (= x280 indx_w) 
                                                           (= x281 x) 
                                                           (not 
                                                               (exists ((x285 D)) 
                                                                   (and 
                                                                       (= x280 indx_wp) 
                                                                       (= x285 x))))) 
                                                       (and 
                                                           (= x280 indx_wp) 
                                                           (= x281 x))))))))) 
                           (and 
                               (= x252 pair_w) 
                               (forall ((x286 Int) (x287 D)) 
                                   (= 
                                       (MS x286 x287 x253) 
                                       (or 
                                           (and 
                                               (exists ((x288 PZD)) 
                                                   (and 
                                                       (data pair_w x288) 
                                                       (MS x286 x287 x288))) 
                                               (not 
                                                   (or 
                                                       (exists ((x289 D)) 
                                                           (and 
                                                               (= x286 indx_w) 
                                                               (= x289 x))) 
                                                       (exists ((x290 D)) 
                                                           (and 
                                                               (= x286 indx_wp) 
                                                               (= x290 x)))))) 
                                           (and 
                                               (= x286 indx_w) 
                                               (= x287 x) 
                                               (not 
                                                   (exists ((x291 D)) 
                                                       (and 
                                                           (= x286 indx_wp) 
                                                           (= x291 x))))) 
                                           (and 
                                               (= x286 indx_wp) 
                                               (= x287 x))))))))))
         :named goal))
(check-sat)
(exit)

