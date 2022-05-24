(set-info :smt-lib-version 2.6)
(set-logic AUFLIA)
(set-info :source |Generator: Rodin SMT Plug-in|)
(set-info :license "https://creativecommons.org/licenses/by-nc/4.0/")
(set-info :category "industrial")
(set-info :status unsat)

(declare-sort D 0)
(declare-sort PZZ 0)
(declare-fun MS (Int Int PZZ) Bool)
(declare-fun idata (Int PZZ) Bool)
(declare-fun rd (Int D) Bool)
(declare-fun wt (Int D) Bool)
(declare-fun wtp (Int D) Bool)
(declare-fun adr_r () Int)
(declare-fun adr_w () Int)
(declare-fun f () PZZ)
(declare-fun g () PZZ)
(declare-fun indx_r () Int)
(declare-fun indx_wp () Int)
(declare-fun latest () Int)
(declare-fun m () Int)
(declare-fun pair_w () Int)
(declare-fun r () Int)
(declare-fun reading () Int)
(declare-fun slot () PZZ)
(declare-fun u () Int)
(declare-fun w () Int)
(declare-fun y () D)

; Elementary Sets axiom (Singleton part)
(assert (forall ((x161 Int) (x162 Int)) 
            (exists ((X PZZ)) 
                (and 
                    (MS x161 x162 X) 
                    (forall ((y0 Int) (y1 Int)) 
                        (=> 
                            (MS y0 y1 X) 
                            (and 
                                (= y0 x161) 
                                (= y1 x162))))))))
(assert (! (< 0 w)
         :named hyp1))
(assert (! (< 0 r)
         :named hyp2))
(assert (! (and 
               (forall ((x Int) (x0 D)) 
                   (=> 
                       (wt x x0) 
                       (and 
                           (<= 1 x) 
                           (<= x w)))) 
               (forall ((x1 Int) (x2 D) (x3 D)) 
                   (=> 
                       (and 
                           (wt x1 x2) 
                           (wt x1 x3)) 
                       (= x2 x3))) 
               (forall ((x4 Int)) 
                   (=> 
                       (and 
                           (<= 1 x4) 
                           (<= x4 w)) 
                       (exists ((x5 D)) 
                           (wt x4 x5)))))
         :named hyp3))
(assert (! (and 
               (forall ((x6 Int) (x7 D)) 
                   (=> 
                       (rd x6 x7) 
                       (and 
                           (<= 1 x6) 
                           (<= x6 r)))) 
               (forall ((x8 Int) (x9 D) (x10 D)) 
                   (=> 
                       (and 
                           (rd x8 x9) 
                           (rd x8 x10)) 
                       (= x9 x10))) 
               (forall ((x11 Int)) 
                   (=> 
                       (and 
                           (<= 1 x11) 
                           (<= x11 r)) 
                       (exists ((x12 D)) 
                           (rd x11 x12)))))
         :named hyp4))
(assert (! (and 
               (forall ((x13 Int) (x14 Int)) 
                   (=> 
                       (MS x13 x14 f) 
                       (and 
                           (<= 1 x13) 
                           (<= x13 r) 
                           (<= 1 x14) 
                           (<= x14 w)))) 
               (forall ((x15 Int) (x16 Int) (x17 Int)) 
                   (=> 
                       (and 
                           (MS x15 x16 f) 
                           (MS x15 x17 f)) 
                       (= x16 x17))) 
               (forall ((x18 Int)) 
                   (=> 
                       (and 
                           (<= 1 x18) 
                           (<= x18 r)) 
                       (exists ((x19 Int)) 
                           (MS x18 x19 f)))))
         :named hyp5))
(assert (! (and 
               (forall ((x20 Int) (x21 Int)) 
                   (=> 
                       (MS x20 x21 g) 
                       (and 
                           (<= 1 x20) 
                           (<= x20 r) 
                           (<= 1 x21) 
                           (<= x21 w)))) 
               (forall ((x22 Int) (x23 Int) (x24 Int)) 
                   (=> 
                       (and 
                           (MS x22 x23 g) 
                           (MS x22 x24 g)) 
                       (= x23 x24))) 
               (forall ((x25 Int)) 
                   (=> 
                       (and 
                           (<= 1 x25) 
                           (<= x25 r)) 
                       (exists ((x26 Int)) 
                           (MS x25 x26 g)))))
         :named hyp6))
(assert (! (forall ((x27 Int) (x28 D)) 
               (= 
                   (rd x27 x28) 
                   (exists ((x29 Int)) 
                       (and 
                           (MS x27 x29 f) 
                           (wt x29 x28)))))
         :named hyp7))
(assert (! (forall ((i Int)) 
               (=> 
                   (and 
                       (<= 1 i) 
                       (<= i r)) 
                   (forall ((x30 Int) (x31 Int)) 
                       (=> 
                           (and 
                               (MS i x31 f) 
                               (MS i x30 g)) 
                           (<= x31 x30)))))
         :named hyp8))
(assert (! (forall ((i0 Int)) 
               (=> 
                   (and 
                       (<= 1 i0) 
                       (<= i0 (- r 1))) 
                   (forall ((x32 Int) (x33 Int)) 
                       (=> 
                           (and 
                               (MS i0 x33 g) 
                               (exists ((x34 Int)) 
                                   (and 
                                       (= x34 (+ i0 1)) 
                                       (MS x34 x32 f)))) 
                           (<= x33 x32)))))
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
(assert (! (MS r u g)
         :named hyp12))
(assert (! (exists ((x35 Int)) 
               (MS r x35 g))
         :named hyp13))
(assert (! (forall ((x36 Int) (x37 Int) (x38 Int)) 
               (=> 
                   (and 
                       (MS x36 x37 g) 
                       (MS x36 x38 g)) 
                   (= x37 x38)))
         :named hyp14))
(assert (! (MS r m f)
         :named hyp15))
(assert (! (exists ((x39 Int)) 
               (MS r x39 f))
         :named hyp16))
(assert (! (forall ((x40 Int) (x41 Int) (x42 Int)) 
               (=> 
                   (and 
                       (MS x40 x41 f) 
                       (MS x40 x42 f)) 
                   (= x41 x42)))
         :named hyp17))
(assert (! (and 
               (forall ((x43 Int) (x44 D)) 
                   (=> 
                       (wtp x43 x44) 
                       (< 0 x43))) 
               (forall ((x45 Int) (x46 D) (x47 D)) 
                   (=> 
                       (and 
                           (wtp x45 x46) 
                           (wtp x45 x47)) 
                       (= x46 x47))))
         :named hyp18))
(assert (! (=> 
               (= adr_r 1) 
               (rd r y))
         :named hyp19))
(assert (! (=> 
               (= adr_r 1) 
               (and 
                   (exists ((x48 D)) 
                       (rd r x48)) 
                   (forall ((x49 Int) (x50 D) (x51 D)) 
                       (=> 
                           (and 
                               (rd x49 x50) 
                               (rd x49 x51)) 
                           (= x50 x51)))))
         :named hyp20))
(assert (! (forall ((x52 Int) (x53 D)) 
               (=> 
                   (wt x52 x53) 
                   (wtp x52 x53)))
         :named hyp21))
(assert (! (=> 
               (or 
                   (= adr_w 2) 
                   (= adr_w 3) 
                   (= adr_w 4)) 
               (forall ((x54 Int)) 
                   (= 
                       (exists ((x55 D)) 
                           (wtp x54 x55)) 
                       (and 
                           (<= 1 x54) 
                           (<= x54 (+ w 1))))))
         :named hyp22))
(assert (! (=> 
               (= adr_w 5) 
               (or 
                   (forall ((x56 Int)) 
                       (= 
                           (exists ((x57 D)) 
                               (wtp x56 x57)) 
                           (and 
                               (<= 1 x56) 
                               (<= x56 w)))) 
                   (forall ((x58 Int)) 
                       (= 
                           (exists ((x59 D)) 
                               (wtp x58 x59)) 
                           (and 
                               (<= 1 x58) 
                               (<= x58 (+ w 1)))))))
         :named hyp23))
(assert (! (or 
               (= reading 0) 
               (= reading 1))
         :named hyp24))
(assert (! (or 
               (= pair_w 0) 
               (= pair_w 1))
         :named hyp25))
(assert (! (or 
               (= latest 0) 
               (= latest 1))
         :named hyp26))
(assert (! (or 
               (= indx_r 0) 
               (= indx_r 1))
         :named hyp27))
(assert (! (or 
               (= indx_wp 0) 
               (= indx_wp 1))
         :named hyp28))
(assert (! (and 
               (forall ((x60 Int) (x61 Int)) 
                   (=> 
                       (MS x60 x61 slot) 
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
                           (MS x62 x63 slot) 
                           (MS x62 x64 slot)) 
                       (= x63 x64))) 
               (forall ((x65 Int)) 
                   (=> 
                       (or 
                           (= x65 0) 
                           (= x65 1)) 
                       (exists ((x66 Int)) 
                           (MS x65 x66 slot)))))
         :named hyp29))
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
                                   (MS x69 x70 x68) 
                                   (and 
                                       (or 
                                           (= x69 0) 
                                           (= x69 1)) 
                                       (exists ((x71 D)) 
                                           (wtp x70 x71))))) 
                           (forall ((x72 Int) (x73 Int) (x74 Int)) 
                               (=> 
                                   (and 
                                       (MS x72 x73 x68) 
                                       (MS x72 x74 x68)) 
                                   (= x73 x74))) 
                           (forall ((x75 Int)) 
                               (=> 
                                   (or 
                                       (= x75 0) 
                                       (= x75 1)) 
                                   (exists ((x76 Int)) 
                                       (MS x75 x76 x68))))))) 
               (forall ((x77 Int) (x78 PZZ) (x79 PZZ)) 
                   (=> 
                       (and 
                           (idata x77 x78) 
                           (idata x77 x79)) 
                       (forall ((x80 Int) (x81 Int)) 
                           (= 
                               (MS x80 x81 x78) 
                               (MS x80 x81 x79))))) 
               (forall ((x82 Int)) 
                   (=> 
                       (or 
                           (= x82 0) 
                           (= x82 1)) 
                       (exists ((x83 PZZ)) 
                           (idata x82 x83)))))
         :named hyp30))
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
                                           (MS reading x86 slot) 
                                           (MS x86 x84 x85))))) 
                           (<= u x84))) 
                   (forall ((x87 Int)) 
                       (=> 
                           (exists ((x88 PZZ)) 
                               (and 
                                   (idata reading x88) 
                                   (exists ((x89 Int)) 
                                       (and 
                                           (MS reading x89 slot) 
                                           (MS x89 x87 x88))))) 
                           (<= x87 w)))))
         :named hyp31))
(assert (! (=> 
               (= adr_r 3) 
               (exists ((x90 PZZ)) 
                   (and 
                       (idata reading x90) 
                       (MS indx_r m x90))))
         :named hyp32))
(assert (! (exists ((x91 PZZ)) 
               (and 
                   (idata latest x91) 
                   (exists ((x92 Int)) 
                       (and 
                           (MS latest x92 slot) 
                           (MS x92 w x91)))))
         :named hyp33))
(assert (! (exists ((x93 PZZ)) 
               (idata latest x93))
         :named hyp34))
(assert (! (forall ((x94 Int) (x95 PZZ) (x96 PZZ)) 
               (=> 
                   (and 
                       (idata x94 x95) 
                       (idata x94 x96)) 
                   (forall ((x97 Int) (x98 Int)) 
                       (= 
                           (MS x97 x98 x95) 
                           (MS x97 x98 x96)))))
         :named hyp35))
(assert (! (exists ((x99 Int)) 
               (MS latest x99 slot))
         :named hyp36))
(assert (! (forall ((x100 Int) (x101 Int) (x102 Int)) 
               (=> 
                   (and 
                       (MS x100 x101 slot) 
                       (MS x100 x102 slot)) 
                   (= x101 x102)))
         :named hyp37))
(assert (! (exists ((x103 Int) (x104 PZZ)) 
               (and 
                   (idata latest x104) 
                   (exists ((x105 Int)) 
                       (and 
                           (MS latest x105 slot) 
                           (MS x105 x103 x104)))))
         :named hyp38))
(assert (! (forall ((x106 Int) (x107 Int) (x108 Int)) 
               (=> 
                   (and 
                       (exists ((x109 PZZ)) 
                           (and 
                               (idata latest x109) 
                               (MS x106 x107 x109))) 
                       (exists ((x110 PZZ)) 
                           (and 
                               (idata latest x110) 
                               (MS x106 x108 x110)))) 
                   (= x107 x108)))
         :named hyp39))
(assert (! (=> 
               (= reading pair_w) 
               (= latest reading))
         :named hyp40))
(assert (! (=> 
               (or 
                   (= adr_w 1) 
                   (= adr_w 5)) 
               (MS pair_w indx_wp slot))
         :named hyp41))
(assert (! (=> 
               (or 
                   (= adr_w 2) 
                   (= adr_w 3) 
                   (= adr_w 4)) 
               (forall ((x111 Int)) 
                   (=> 
                       (MS pair_w x111 slot) 
                       (= indx_wp (- 1 x111)))))
         :named hyp42))
(assert (! (exists ((x112 PZZ)) 
               (and 
                   (idata pair_w x112) 
                   (exists ((x113 Int)) 
                       (and 
                           (exists ((x114 D)) 
                               (wtp x113 x114)) 
                           (forall ((x115 Int)) 
                               (=> 
                                   (exists ((x116 D)) 
                                       (wtp x115 x116)) 
                                   (<= x115 x113))) 
                           (MS indx_wp x113 x112)))))
         :named hyp43))
(assert (! (exists ((x117 PZZ)) 
               (idata pair_w x117))
         :named hyp44))
(assert (! (exists ((x118 Int) (x119 PZZ)) 
               (and 
                   (idata pair_w x119) 
                   (MS indx_wp x118 x119)))
         :named hyp45))
(assert (! (forall ((x120 Int) (x121 Int) (x122 Int)) 
               (=> 
                   (and 
                       (exists ((x123 PZZ)) 
                           (and 
                               (idata pair_w x123) 
                               (MS x120 x121 x123))) 
                       (exists ((x124 PZZ)) 
                           (and 
                               (idata pair_w x124) 
                               (MS x120 x122 x124)))) 
                   (= x121 x122)))
         :named hyp46))
(assert (! (exists ((b Int)) 
               (forall ((x125 Int)) 
                   (=> 
                       (exists ((x126 D)) 
                           (wtp x125 x126)) 
                       (<= x125 b))))
         :named hyp47))
(assert (! (not 
               (= reading (- 1 reading)))
         :named hyp48))
(assert (! (not 
               (exists ((x127 Int) (x128 Int)) 
                   (and 
                       (= x127 (- 1 reading)) 
                       (forall ((x129 Int)) 
                           (=> 
                               (exists ((x130 Int)) 
                                   (and 
                                       (= x130 (- 1 reading)) 
                                       (MS x130 x129 slot))) 
                               (= x128 (- 1 x129)))) 
                       (MS x127 x128 slot))))
         :named hyp49))
(assert (! (exists ((x131 Int) (x132 Int)) 
               (and 
                   (= x132 (- 1 reading)) 
                   (MS x132 x131 slot)))
         :named hyp50))
(assert (! (= adr_w 1)
         :named hyp51))
(assert (! (not 
               (forall ((x133 Int) (x134 D)) 
                   (not 
                       (wtp x133 x134))))
         :named hyp52))
(assert (! (forall ((x135 Int)) 
               (= 
                   (exists ((x136 D)) 
                       (wtp x135 x136)) 
                   (and 
                       (<= 1 x135) 
                       (<= x135 w))))
         :named hyp53))
(assert (! (=> 
               (= adr_r 2) 
               (and 
                   (exists ((x137 PZZ)) 
                       (idata reading x137)) 
                   (exists ((x138 Int)) 
                       (MS reading x138 slot)) 
                   (exists ((x139 Int) (x140 PZZ)) 
                       (and 
                           (idata reading x140) 
                           (exists ((x141 Int)) 
                               (and 
                                   (MS reading x141 slot) 
                                   (MS x141 x139 x140))))) 
                   (forall ((x142 Int) (x143 Int) (x144 Int)) 
                       (=> 
                           (and 
                               (exists ((x145 PZZ)) 
                                   (and 
                                       (idata reading x145) 
                                       (MS x142 x143 x145))) 
                               (exists ((x146 PZZ)) 
                                   (and 
                                       (idata reading x146) 
                                       (MS x142 x144 x146)))) 
                           (= x143 x144)))))
         :named hyp54))
(assert (! (=> 
               (= adr_r 3) 
               (and 
                   (exists ((x147 PZZ)) 
                       (idata reading x147)) 
                   (exists ((x148 Int) (x149 PZZ)) 
                       (and 
                           (idata reading x149) 
                           (MS indx_r x148 x149))) 
                   (forall ((x150 Int) (x151 Int) (x152 Int)) 
                       (=> 
                           (and 
                               (exists ((x153 PZZ)) 
                                   (and 
                                       (idata reading x153) 
                                       (MS x150 x151 x153))) 
                               (exists ((x154 PZZ)) 
                                   (and 
                                       (idata reading x154) 
                                       (MS x150 x152 x154)))) 
                           (= x151 x152)))))
         :named hyp55))
(assert (! (= pair_w latest)
         :named hyp56))
(assert (! (=> 
               (or 
                   (= adr_w 1) 
                   (= adr_w 5)) 
               (exists ((x155 Int)) 
                   (MS pair_w x155 slot)))
         :named hyp57))
(assert (! (=> 
               (or 
                   (= adr_w 2) 
                   (= adr_w 3) 
                   (= adr_w 4)) 
               (exists ((x156 Int)) 
                   (MS pair_w x156 slot)))
         :named hyp58))
(assert (! (not 
               (or 
                   (forall ((x157 Int)) 
                       (=> 
                           (exists ((x158 Int)) 
                               (and 
                                   (= x158 (- 1 reading)) 
                                   (MS x158 x157 slot))) 
                           (= (- 1 x157) 0))) 
                   (forall ((x159 Int)) 
                       (=> 
                           (exists ((x160 Int)) 
                               (and 
                                   (= x160 (- 1 reading)) 
                                   (MS x160 x159 slot))) 
                           (= (- 1 x159) 1)))))
         :named goal))
(check-sat)
(exit)

