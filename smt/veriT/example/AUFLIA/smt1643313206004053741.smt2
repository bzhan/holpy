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
(declare-fun d () D)
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
(assert (forall ((x228 Int) (x229 D)) 
            (exists ((X PZD)) 
                (and 
                    (MS x228 x229 X) 
                    (forall ((y0 Int) (y1 D)) 
                        (=> 
                            (MS y0 y1 X) 
                            (and 
                                (= y0 x228) 
                                (= y1 x229))))))))
; Elementary Sets axiom (Singleton part)
(assert (forall ((x230 Int) (x231 Int)) 
            (exists ((X0 PZZ)) 
                (and 
                    (MS0 x230 x231 X0) 
                    (forall ((y2 Int) (y3 Int)) 
                        (=> 
                            (MS0 y2 y3 X0) 
                            (and 
                                (= y2 x230) 
                                (= y3 x231))))))))
(assert (! (= adr_w 1)
         :named hyp1))
(assert (! (forall ((x0 Int)) 
               (= 
                   (exists ((x1 D)) 
                       (MS x0 x1 wtp)) 
                   (and 
                       (<= 1 x0) 
                       (<= x0 w))))
         :named hyp2))
(assert (! (= pair_w latest)
         :named hyp3))
(assert (! (or 
               (= 2 1) 
               (= 2 4) 
               (= 2 5))
         :named hyp4))
(assert (! (forall ((x2 Int) (x3 PZD)) 
               (= 
                   (Data x2 x3) 
                   (data x2 x3)))
         :named hyp5))
(assert (! (exists ((x4 PZD) (x5 Int)) 
               (and 
                   (= x5 (- 1 reading)) 
                   (data x5 x4)))
         :named hyp6))
(assert (! (forall ((x6 Int) (x7 PZD) (x8 PZD)) 
               (=> 
                   (and 
                       (data x6 x7) 
                       (data x6 x8)) 
                   (forall ((x9 Int) (x10 D)) 
                       (= 
                           (MS x9 x10 x7) 
                           (MS x9 x10 x8)))))
         :named hyp7))
(assert (! (=> 
               (or 
                   (= 1 2) 
                   (= 1 3)) 
               (exists ((x11 PZD)) 
                   (data latest x11)))
         :named hyp8))
(assert (! (< 0 w)
         :named hyp9))
(assert (! (and 
               (forall ((x12 Int) (x13 D)) 
                   (=> 
                       (MS x12 x13 wt) 
                       (and 
                           (<= 1 x12) 
                           (<= x12 w)))) 
               (forall ((x14 Int) (x15 D) (x16 D)) 
                   (=> 
                       (and 
                           (MS x14 x15 wt) 
                           (MS x14 x16 wt)) 
                       (= x15 x16))) 
               (forall ((x17 Int)) 
                   (=> 
                       (and 
                           (<= 1 x17) 
                           (<= x17 w)) 
                       (exists ((x18 D)) 
                           (MS x17 x18 wt)))))
         :named hyp10))
(assert (! (and 
               (forall ((x19 Int) (x20 D)) 
                   (=> 
                       (MS x19 x20 rd) 
                       (and 
                           (<= 1 x19) 
                           (<= x19 r)))) 
               (forall ((x21 Int) (x22 D) (x23 D)) 
                   (=> 
                       (and 
                           (MS x21 x22 rd) 
                           (MS x21 x23 rd)) 
                       (= x22 x23))) 
               (forall ((x24 Int)) 
                   (=> 
                       (and 
                           (<= 1 x24) 
                           (<= x24 r)) 
                       (exists ((x25 D)) 
                           (MS x24 x25 rd)))))
         :named hyp11))
(assert (! (and 
               (forall ((x26 Int) (x27 Int)) 
                   (=> 
                       (MS0 x26 x27 f) 
                       (and 
                           (<= 1 x26) 
                           (<= x26 r) 
                           (<= 1 x27) 
                           (<= x27 w)))) 
               (forall ((x28 Int) (x29 Int) (x30 Int)) 
                   (=> 
                       (and 
                           (MS0 x28 x29 f) 
                           (MS0 x28 x30 f)) 
                       (= x29 x30))) 
               (forall ((x31 Int)) 
                   (=> 
                       (and 
                           (<= 1 x31) 
                           (<= x31 r)) 
                       (exists ((x32 Int)) 
                           (MS0 x31 x32 f)))))
         :named hyp12))
(assert (! (and 
               (forall ((x33 Int) (x34 Int)) 
                   (=> 
                       (MS0 x33 x34 g) 
                       (and 
                           (<= 1 x33) 
                           (<= x33 r) 
                           (<= 1 x34) 
                           (<= x34 w)))) 
               (forall ((x35 Int) (x36 Int) (x37 Int)) 
                   (=> 
                       (and 
                           (MS0 x35 x36 g) 
                           (MS0 x35 x37 g)) 
                       (= x36 x37))) 
               (forall ((x38 Int)) 
                   (=> 
                       (and 
                           (<= 1 x38) 
                           (<= x38 r)) 
                       (exists ((x39 Int)) 
                           (MS0 x38 x39 g)))))
         :named hyp13))
(assert (! (forall ((x40 Int) (x41 D)) 
               (= 
                   (MS x40 x41 rd) 
                   (exists ((x42 Int)) 
                       (and 
                           (MS0 x40 x42 f) 
                           (MS x42 x41 wt)))))
         :named hyp14))
(assert (! (or 
               (= adr_w 1) 
               (= adr_w 2) 
               (= adr_w 3) 
               (= adr_w 4) 
               (= adr_w 5))
         :named hyp15))
(assert (! (and 
               (forall ((x43 Int) (x44 D)) 
                   (=> 
                       (MS x43 x44 wtp) 
                       (< 0 x43))) 
               (forall ((x45 Int) (x46 D) (x47 D)) 
                   (=> 
                       (and 
                           (MS x45 x46 wtp) 
                           (MS x45 x47 wtp)) 
                       (= x46 x47))))
         :named hyp16))
(assert (! (=> 
               (= adr_r 1) 
               (MS r y rd))
         :named hyp17))
(assert (! (=> 
               (= adr_r 1) 
               (and 
                   (exists ((x48 D)) 
                       (MS r x48 rd)) 
                   (forall ((x49 Int) (x50 D) (x51 D)) 
                       (=> 
                           (and 
                               (MS x49 x50 rd) 
                               (MS x49 x51 rd)) 
                           (= x50 x51)))))
         :named hyp18))
(assert (! (forall ((x52 Int) (x53 D)) 
               (=> 
                   (MS x52 x53 wt) 
                   (MS x52 x53 wtp)))
         :named hyp19))
(assert (! (=> 
               (or 
                   (= adr_w 2) 
                   (= adr_w 3) 
                   (= adr_w 4)) 
               (forall ((x54 Int)) 
                   (= 
                       (exists ((x55 D)) 
                           (MS x54 x55 wtp)) 
                       (and 
                           (<= 1 x54) 
                           (<= x54 (+ w 1))))))
         :named hyp20))
(assert (! (=> 
               (= adr_w 5) 
               (or 
                   (forall ((x56 Int)) 
                       (= 
                           (exists ((x57 D)) 
                               (MS x56 x57 wtp)) 
                           (and 
                               (<= 1 x56) 
                               (<= x56 w)))) 
                   (forall ((x58 Int)) 
                       (= 
                           (exists ((x59 D)) 
                               (MS x58 x59 wtp)) 
                           (and 
                               (<= 1 x58) 
                               (<= x58 (+ w 1)))))))
         :named hyp21))
(assert (! (or 
               (= reading 0) 
               (= reading 1))
         :named hyp22))
(assert (! (or 
               (= pair_w 0) 
               (= pair_w 1))
         :named hyp23))
(assert (! (or 
               (= latest 0) 
               (= latest 1))
         :named hyp24))
(assert (! (and 
               (forall ((x60 Int) (x61 Int)) 
                   (=> 
                       (MS0 x60 x61 slot) 
                       (and 
                           (or 
                               (= x60 0) 
                               (= x60 1)) 
                           (or 
                               (= x61 0) 
                               (= x61 1))))) 
               (forall ((x62 Int) (x63 Int) (x64 Int)) 
                   (=> 
                       (and 
                           (MS0 x62 x63 slot) 
                           (MS0 x62 x64 slot)) 
                       (= x63 x64))) 
               (forall ((x65 Int)) 
                   (=> 
                       (or 
                           (= x65 0) 
                           (= x65 1)) 
                       (exists ((x66 Int)) 
                           (MS0 x65 x66 slot)))))
         :named hyp25))
(assert (! (and 
               (forall ((x67 Int) (x68 PZZ)) 
                   (=> 
                       (idata x67 x68) 
                       (and 
                           (or 
                               (= x67 0) 
                               (= x67 1)) 
                           (forall ((x69 Int) (x70 Int)) 
                               (=> 
                                   (MS0 x69 x70 x68) 
                                   (and 
                                       (or 
                                           (= x69 0) 
                                           (= x69 1)) 
                                       (exists ((x71 D)) 
                                           (MS x70 x71 wtp))))) 
                           (forall ((x72 Int) (x73 Int) (x74 Int)) 
                               (=> 
                                   (and 
                                       (MS0 x72 x73 x68) 
                                       (MS0 x72 x74 x68)) 
                                   (= x73 x74))) 
                           (forall ((x75 Int)) 
                               (=> 
                                   (or 
                                       (= x75 0) 
                                       (= x75 1)) 
                                   (exists ((x76 Int)) 
                                       (MS0 x75 x76 x68))))))) 
               (forall ((x77 Int) (x78 PZZ) (x79 PZZ)) 
                   (=> 
                       (and 
                           (idata x77 x78) 
                           (idata x77 x79)) 
                       (forall ((x80 Int) (x81 Int)) 
                           (= 
                               (MS0 x80 x81 x78) 
                               (MS0 x80 x81 x79))))) 
               (forall ((x82 Int)) 
                   (=> 
                       (or 
                           (= x82 0) 
                           (= x82 1)) 
                       (exists ((x83 PZZ)) 
                           (idata x82 x83)))))
         :named hyp26))
(assert (! (=> 
               (= adr_r 2) 
               (and 
                   (forall ((x84 Int)) 
                       (=> 
                           (exists ((x85 PZZ)) 
                               (and 
                                   (idata reading x85) 
                                   (exists ((x86 Int)) 
                                       (and 
                                           (MS0 reading x86 slot) 
                                           (MS0 x86 x84 x85))))) 
                           (<= u x84))) 
                   (forall ((x87 Int)) 
                       (=> 
                           (exists ((x88 PZZ)) 
                               (and 
                                   (idata reading x88) 
                                   (exists ((x89 Int)) 
                                       (and 
                                           (MS0 reading x89 slot) 
                                           (MS0 x89 x87 x88))))) 
                           (<= x87 w)))))
         :named hyp27))
(assert (! (=> 
               (= adr_r 3) 
               (exists ((x90 PZZ)) 
                   (and 
                       (idata reading x90) 
                       (MS0 indx_r m x90))))
         :named hyp28))
(assert (! (exists ((x91 PZZ)) 
               (and 
                   (idata latest x91) 
                   (exists ((x92 Int)) 
                       (and 
                           (MS0 latest x92 slot) 
                           (MS0 x92 w x91)))))
         :named hyp29))
(assert (! (exists ((x93 PZZ)) 
               (idata latest x93))
         :named hyp30))
(assert (! (exists ((x94 Int)) 
               (MS0 latest x94 slot))
         :named hyp31))
(assert (! (forall ((x95 Int) (x96 Int) (x97 Int)) 
               (=> 
                   (and 
                       (MS0 x95 x96 slot) 
                       (MS0 x95 x97 slot)) 
                   (= x96 x97)))
         :named hyp32))
(assert (! (exists ((x98 Int) (x99 PZZ)) 
               (and 
                   (idata latest x99) 
                   (exists ((x100 Int)) 
                       (and 
                           (MS0 latest x100 slot) 
                           (MS0 x100 x98 x99)))))
         :named hyp33))
(assert (! (forall ((x101 Int) (x102 Int) (x103 Int)) 
               (=> 
                   (and 
                       (exists ((x104 PZZ)) 
                           (and 
                               (idata latest x104) 
                               (MS0 x101 x102 x104))) 
                       (exists ((x105 PZZ)) 
                           (and 
                               (idata latest x105) 
                               (MS0 x101 x103 x105)))) 
                   (= x102 x103)))
         :named hyp34))
(assert (! (=> 
               (= reading pair_w) 
               (= latest reading))
         :named hyp35))
(assert (! (=> 
               (or 
                   (= adr_w 1) 
                   (= adr_w 5)) 
               (MS0 pair_w indx_wp slot))
         :named hyp36))
(assert (! (=> 
               (or 
                   (= adr_w 2) 
                   (= adr_w 3) 
                   (= adr_w 4)) 
               (forall ((x106 Int)) 
                   (=> 
                       (MS0 pair_w x106 slot) 
                       (= indx_wp (- 1 x106)))))
         :named hyp37))
(assert (! (exists ((x107 PZZ)) 
               (and 
                   (idata pair_w x107) 
                   (exists ((x108 Int)) 
                       (and 
                           (exists ((x109 D)) 
                               (MS x108 x109 wtp)) 
                           (forall ((x110 Int)) 
                               (=> 
                                   (exists ((x111 D)) 
                                       (MS x110 x111 wtp)) 
                                   (<= x110 x108))) 
                           (MS0 indx_wp x108 x107)))))
         :named hyp38))
(assert (! (exists ((x112 PZZ)) 
               (idata pair_w x112))
         :named hyp39))
(assert (! (exists ((x113 Int) (x114 PZZ)) 
               (and 
                   (idata pair_w x114) 
                   (MS0 indx_wp x113 x114)))
         :named hyp40))
(assert (! (forall ((x115 Int) (x116 Int) (x117 Int)) 
               (=> 
                   (and 
                       (exists ((x118 PZZ)) 
                           (and 
                               (idata pair_w x118) 
                               (MS0 x115 x116 x118))) 
                       (exists ((x119 PZZ)) 
                           (and 
                               (idata pair_w x119) 
                               (MS0 x115 x117 x119)))) 
                   (= x116 x117)))
         :named hyp41))
(assert (! (exists ((b Int)) 
               (forall ((x120 Int)) 
                   (=> 
                       (exists ((x121 D)) 
                           (MS x120 x121 wtp)) 
                       (<= x120 b))))
         :named hyp42))
(assert (! (not 
               (= reading (- 1 reading)))
         :named hyp43))
(assert (! (not 
               (exists ((x122 Int) (x123 Int)) 
                   (and 
                       (= x122 (- 1 reading)) 
                       (forall ((x124 Int)) 
                           (=> 
                               (exists ((x125 Int)) 
                                   (and 
                                       (= x125 (- 1 reading)) 
                                       (MS0 x125 x124 slot))) 
                               (= x123 (- 1 x124)))) 
                       (MS0 x122 x123 slot))))
         :named hyp44))
(assert (! (exists ((x126 Int) (x127 Int)) 
               (and 
                   (= x127 (- 1 reading)) 
                   (MS0 x127 x126 slot)))
         :named hyp45))
(assert (! (and 
               (forall ((x128 Int) (x129 PZD)) 
                   (=> 
                       (Data x128 x129) 
                       (and 
                           (or 
                               (= x128 0) 
                               (= x128 1)) 
                           (forall ((x130 Int) (x131 D)) 
                               (=> 
                                   (MS x130 x131 x129) 
                                   (or 
                                       (= x130 0) 
                                       (= x130 1)))) 
                           (forall ((x132 Int) (x133 D) (x134 D)) 
                               (=> 
                                   (and 
                                       (MS x132 x133 x129) 
                                       (MS x132 x134 x129)) 
                                   (= x133 x134))) 
                           (forall ((x135 Int)) 
                               (=> 
                                   (or 
                                       (= x135 0) 
                                       (= x135 1)) 
                                   (exists ((x136 D)) 
                                       (MS x135 x136 x129))))))) 
               (forall ((x137 Int) (x138 PZD) (x139 PZD)) 
                   (=> 
                       (and 
                           (Data x137 x138) 
                           (Data x137 x139)) 
                       (forall ((x140 Int) (x141 D)) 
                           (= 
                               (MS x140 x141 x138) 
                               (MS x140 x141 x139))))) 
               (forall ((x142 Int)) 
                   (=> 
                       (or 
                           (= x142 0) 
                           (= x142 1)) 
                       (exists ((x143 PZD)) 
                           (Data x142 x143)))))
         :named hyp46))
(assert (! (forall ((x144 Int) (z Int)) 
               (=> 
                   (and 
                       (or 
                           (= x144 0) 
                           (= x144 1)) 
                       (or 
                           (= z 0) 
                           (= z 1))) 
                   (exists ((x145 Int) (x146 D)) 
                       (and 
                           (exists ((x147 PZZ)) 
                               (and 
                                   (idata x144 x147) 
                                   (MS0 z x145 x147))) 
                           (exists ((x148 PZD)) 
                               (and 
                                   (Data x144 x148) 
                                   (MS z x146 x148))) 
                           (MS x145 x146 wtp)))))
         :named hyp47))
(assert (! (and 
               (forall ((x149 Int) (x150 PZD)) 
                   (=> 
                       (data x149 x150) 
                       (and 
                           (or 
                               (= x149 0) 
                               (= x149 1)) 
                           (forall ((x151 Int) (x152 D)) 
                               (=> 
                                   (MS x151 x152 x150) 
                                   (or 
                                       (= x151 0) 
                                       (= x151 1)))) 
                           (forall ((x153 Int) (x154 D) (x155 D)) 
                               (=> 
                                   (and 
                                       (MS x153 x154 x150) 
                                       (MS x153 x155 x150)) 
                                   (= x154 x155))) 
                           (forall ((x156 Int)) 
                               (=> 
                                   (or 
                                       (= x156 0) 
                                       (= x156 1)) 
                                   (exists ((x157 D)) 
                                       (MS x156 x157 x150))))))) 
               (forall ((x158 Int) (x159 PZD) (x160 PZD)) 
                   (=> 
                       (and 
                           (data x158 x159) 
                           (data x158 x160)) 
                       (forall ((x161 Int) (x162 D)) 
                           (= 
                               (MS x161 x162 x159) 
                               (MS x161 x162 x160))))) 
               (forall ((x163 Int)) 
                   (=> 
                       (or 
                           (= x163 0) 
                           (= x163 1)) 
                       (exists ((x164 PZD)) 
                           (data x163 x164)))))
         :named hyp48))
(assert (! (=> 
               (or 
                   (= adr_w 2) 
                   (= adr_w 3)) 
               (forall ((x165 Int) (x166 PZD)) 
                   (= 
                       (Data x165 x166) 
                       (or 
                           (and 
                               (data x165 x166) 
                               (not 
                                   (exists ((x167 PZD)) 
                                       (and 
                                           (= x165 pair_w) 
                                           (forall ((x168 Int) (x169 D)) 
                                               (= 
                                                   (MS x168 x169 x167) 
                                                   (or 
                                                       (and 
                                                           (exists ((x170 PZD)) 
                                                               (and 
                                                                   (data pair_w x170) 
                                                                   (MS x168 x169 x170))) 
                                                           (not 
                                                               (exists ((x171 D)) 
                                                                   (and 
                                                                       (= x168 indx_wp) 
                                                                       (= x171 x))))) 
                                                       (and 
                                                           (= x168 indx_wp) 
                                                           (= x169 x))))))))) 
                           (and 
                               (= x165 pair_w) 
                               (forall ((x172 Int) (x173 D)) 
                                   (= 
                                       (MS x172 x173 x166) 
                                       (or 
                                           (and 
                                               (exists ((x174 PZD)) 
                                                   (and 
                                                       (data pair_w x174) 
                                                       (MS x172 x173 x174))) 
                                               (not 
                                                   (exists ((x175 D)) 
                                                       (and 
                                                           (= x172 indx_wp) 
                                                           (= x175 x))))) 
                                           (and 
                                               (= x172 indx_wp) 
                                               (= x173 x))))))))))
         :named hyp49))
(assert (! (=> 
               (or 
                   (= adr_w 1) 
                   (= adr_w 3) 
                   (= adr_w 4) 
                   (= adr_w 5)) 
               (= indx_w indx_wp))
         :named hyp50))
(assert (! (=> 
               (and 
                   (= adr_w 3) 
                   (= adr_r 3) 
                   (= pair_w reading)) 
               (not 
                   (= indx_r indx_wp)))
         :named hyp51))
(assert (! (=> 
               (and 
                   (= adr_w 2) 
                   (= adr_r 3) 
                   (= pair_w reading)) 
               (not 
                   (= indx_r indx_wp)))
         :named hyp52))
(assert (! (not 
               (forall ((x176 Int) (x177 D)) 
                   (not 
                       (MS x176 x177 wtp))))
         :named hyp53))
(assert (! (=> 
               (= adr_r 2) 
               (and 
                   (exists ((x178 PZZ)) 
                       (idata reading x178)) 
                   (exists ((x179 Int)) 
                       (MS0 reading x179 slot)) 
                   (exists ((x180 Int) (x181 PZZ)) 
                       (and 
                           (idata reading x181) 
                           (exists ((x182 Int)) 
                               (and 
                                   (MS0 reading x182 slot) 
                                   (MS0 x182 x180 x181))))) 
                   (forall ((x183 Int) (x184 Int) (x185 Int)) 
                       (=> 
                           (and 
                               (exists ((x186 PZZ)) 
                                   (and 
                                       (idata reading x186) 
                                       (MS0 x183 x184 x186))) 
                               (exists ((x187 PZZ)) 
                                   (and 
                                       (idata reading x187) 
                                       (MS0 x183 x185 x187)))) 
                           (= x184 x185)))))
         :named hyp54))
(assert (! (=> 
               (= adr_r 3) 
               (and 
                   (exists ((x188 PZZ)) 
                       (idata reading x188)) 
                   (exists ((x189 Int) (x190 PZZ)) 
                       (and 
                           (idata reading x190) 
                           (MS0 indx_r x189 x190))) 
                   (forall ((x191 Int) (x192 Int) (x193 Int)) 
                       (=> 
                           (and 
                               (exists ((x194 PZZ)) 
                                   (and 
                                       (idata reading x194) 
                                       (MS0 x191 x192 x194))) 
                               (exists ((x195 PZZ)) 
                                   (and 
                                       (idata reading x195) 
                                       (MS0 x191 x193 x195)))) 
                           (= x192 x193)))))
         :named hyp55))
(assert (! (=> 
               (or 
                   (= adr_w 1) 
                   (= adr_w 5)) 
               (exists ((x196 Int)) 
                   (MS0 pair_w x196 slot)))
         :named hyp56))
(assert (! (=> 
               (or 
                   (= adr_w 2) 
                   (= adr_w 3) 
                   (= adr_w 4)) 
               (exists ((x197 Int)) 
                   (MS0 pair_w x197 slot)))
         :named hyp57))
(assert (! (exists ((x198 PZD) (x199 Int)) 
               (and 
                   (= x199 (- 1 reading)) 
                   (Data x199 x198)))
         :named hyp58))
(assert (! (forall ((x200 Int) (x201 PZD) (x202 PZD)) 
               (=> 
                   (and 
                       (Data x200 x201) 
                       (Data x200 x202)) 
                   (forall ((x203 Int) (x204 D)) 
                       (= 
                           (MS x203 x204 x201) 
                           (MS x203 x204 x202)))))
         :named hyp59))
(assert (! (=> 
               (or 
                   (= adr_w 2) 
                   (= adr_w 3)) 
               (exists ((x205 PZD)) 
                   (data pair_w x205)))
         :named hyp60))
(assert (! (=> 
               (or 
                   (= 1 2) 
                   (= 1 3)) 
               (exists ((x206 PZD)) 
                   (data pair_w x206)))
         :named hyp61))
(assert (! (not 
               (forall ((x207 Int) (x208 PZD)) 
                   (= 
                       (or 
                           (and 
                               (data x207 x208) 
                               (not 
                                   (exists ((x209 PZD)) 
                                       (and 
                                           (= x207 (- 1 reading)) 
                                           (forall ((x210 Int) (x211 D)) 
                                               (= 
                                                   (MS x210 x211 x209) 
                                                   (or 
                                                       (and 
                                                           (exists ((x212 PZD)) 
                                                               (and 
                                                                   (exists ((x213 Int)) 
                                                                       (and 
                                                                           (= x213 (- 1 reading)) 
                                                                           (data x213 x212))) 
                                                                   (MS x210 x211 x212))) 
                                                           (not 
                                                               (exists ((x214 D)) 
                                                                   (and 
                                                                       (forall ((x215 Int)) 
                                                                           (=> 
                                                                               (exists ((x216 Int)) 
                                                                                   (and 
                                                                                       (= x216 (- 1 reading)) 
                                                                                       (MS0 x216 x215 slot))) 
                                                                               (= x210 (- 1 x215)))) 
                                                                       (= x214 d))))) 
                                                       (and 
                                                           (forall ((x217 Int)) 
                                                               (=> 
                                                                   (exists ((x218 Int)) 
                                                                       (and 
                                                                           (= x218 (- 1 reading)) 
                                                                           (MS0 x218 x217 slot))) 
                                                                   (= x210 (- 1 x217)))) 
                                                           (= x211 d))))))))) 
                           (and 
                               (= x207 (- 1 reading)) 
                               (forall ((x219 Int) (x220 D)) 
                                   (= 
                                       (MS x219 x220 x208) 
                                       (or 
                                           (and 
                                               (exists ((x221 PZD)) 
                                                   (and 
                                                       (exists ((x222 Int)) 
                                                           (and 
                                                               (= x222 (- 1 reading)) 
                                                               (data x222 x221))) 
                                                       (MS x219 x220 x221))) 
                                               (not 
                                                   (exists ((x223 D)) 
                                                       (and 
                                                           (forall ((x224 Int)) 
                                                               (=> 
                                                                   (exists ((x225 Int)) 
                                                                       (and 
                                                                           (= x225 (- 1 reading)) 
                                                                           (MS0 x225 x224 slot))) 
                                                                   (= x219 (- 1 x224)))) 
                                                           (= x223 d))))) 
                                           (and 
                                               (forall ((x226 Int)) 
                                                   (=> 
                                                       (exists ((x227 Int)) 
                                                           (and 
                                                               (= x227 (- 1 reading)) 
                                                               (MS0 x227 x226 slot))) 
                                                       (= x219 (- 1 x226)))) 
                                               (= x220 d))))))) 
                       (data x207 x208))))
         :named goal))
(check-sat)
(exit)

