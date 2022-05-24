(set-info :smt-lib-version 2.6)
(set-logic AUFLIA)
(set-info :source |Generator: Rodin SMT Plug-in|)
(set-info :license "https://creativecommons.org/licenses/by-nc/4.0/")
(set-info :category "industrial")
(set-info :status unsat)

(declare-sort CLR 0)
(declare-sort DIR 0)
(declare-sort K 0)
(declare-sort N 0)
(declare-sort PN 0)
(declare-sort PNN 0)
(declare-sort PNZ 0)
(declare-fun MS (N PN) Bool)
(declare-fun MS0 (N N PNN) Bool)
(declare-fun MS1 (N Int PNZ) Bool)
(declare-fun clr (N CLR) Bool)
(declare-fun dirp (N DIR) Bool)
(declare-fun b () PN)
(declare-fun black () CLR)
(declare-fun c () PNN)
(declare-fun f () PNN)
(declare-fun g () PNN)
(declare-fun h () PNN)
(declare-fun ko () K)
(declare-fun left () DIR)
(declare-fun lft () PN)
(declare-fun lt () PNN)
(declare-fun ltp () PNN)
(declare-fun n () K)
(declare-fun nil () N)
(declare-fun ok () K)
(declare-fun p () N)
(declare-fun q () N)
(declare-fun rht () PN)
(declare-fun right () DIR)
(declare-fun rt () PNN)
(declare-fun rtp () PNN)
(declare-fun t () N)
(declare-fun ult () PNN)
(declare-fun urt () PNN)
(declare-fun vlt () PNN)
(declare-fun vrt () PNN)
(declare-fun white () CLR)
(declare-fun wlt () PNN)
(declare-fun wrt () PNN)

; Elementary Sets axiom (Singleton part)
(assert (forall ((x744 N) (x745 N)) 
            (exists ((X PNN)) 
                (and 
                    (MS0 x744 x745 X) 
                    (forall ((y3 N) (y4 N)) 
                        (=> 
                            (MS0 y3 y4 X) 
                            (and 
                                (= y3 x744) 
                                (= y4 x745))))))))
; Elementary Sets axiom (Singleton part)
(assert (forall ((x746 N) (x747 Int)) 
            (exists ((X0 PNZ)) 
                (and 
                    (MS1 x746 x747 X0) 
                    (forall ((y5 N) (y6 Int)) 
                        (=> 
                            (MS1 y5 y6 X0) 
                            (and 
                                (= y5 x746) 
                                (= y6 x747))))))))
; Elementary Sets axiom (Singleton part)
(assert (forall ((x748 N)) 
            (exists ((X1 PN)) 
                (and 
                    (MS x748 X1) 
                    (forall ((y7 N)) 
                        (=> 
                            (MS y7 X1) 
                            (= y7 x748)))))))
(assert (! (forall ((x N)) 
               (= 
                   (MS x b) 
                   (exists ((x0 CLR)) 
                       (and 
                           (= x0 black) 
                           (clr x x0)))))
         :named hyp1))
(assert (! (exists ((x1 N)) 
               (and 
                   (MS0 p x1 wrt) 
                   (clr x1 white)))
         :named hyp2))
(assert (! (= n ko)
         :named hyp3))
(assert (! (forall ((x2 K)) 
               (or 
                   (= x2 ok) 
                   (= x2 ko)))
         :named hyp4))
(assert (! (not 
               (= ok ko))
         :named hyp5))
(assert (! (forall ((x3 DIR)) 
               (or 
                   (= x3 left) 
                   (= x3 right)))
         :named hyp6))
(assert (! (not 
               (= left right))
         :named hyp7))
(assert (! (not 
               (MS0 p nil wrt))
         :named hyp8))
(assert (! (=> 
               (not 
                   (MS0 p nil wlt)) 
               (exists ((x4 N)) 
                   (and 
                       (MS0 p x4 wlt) 
                       (clr x4 black))))
         :named hyp9))
(assert (! (or 
               (not 
                   (forall ((x5 N)) 
                       (=> 
                           (exists ((x6 N)) 
                               (and 
                                   (= x6 p) 
                                   (MS0 x6 x5 lt))) 
                           (exists ((x7 CLR)) 
                               (and 
                                   (= x7 black) 
                                   (clr x5 x7)))))) 
               (and 
                   (forall ((x8 N)) 
                       (=> 
                           (exists ((x9 N)) 
                               (and 
                                   (= x9 p) 
                                   (MS0 x9 x8 lt))) 
                           (exists ((x10 CLR)) 
                               (and 
                                   (= x10 black) 
                                   (clr x8 x10))))) 
                   (not 
                       (forall ((x11 N)) 
                           (=> 
                               (exists ((x12 N)) 
                                   (and 
                                       (= x12 p) 
                                       (MS0 x12 x11 rt))) 
                               (exists ((x13 CLR)) 
                                   (and 
                                       (= x13 black) 
                                       (clr x11 x13))))))) 
               (and 
                   (=> 
                       (and 
                           (forall ((x14 N)) 
                               (=> 
                                   (exists ((x15 N)) 
                                       (and 
                                           (= x15 p) 
                                           (MS0 x15 x14 lt))) 
                                   (exists ((x16 CLR)) 
                                       (and 
                                           (= x16 black) 
                                           (clr x14 x16))))) 
                           (forall ((x17 N)) 
                               (=> 
                                   (exists ((x18 N)) 
                                       (and 
                                           (= x18 p) 
                                           (MS0 x18 x17 rt))) 
                                   (exists ((x19 CLR)) 
                                       (and 
                                           (= x19 black) 
                                           (clr x17 x19))))) 
                           (not 
                               (= p t))) 
                       (and 
                           (exists ((x20 N)) 
                               (MS0 p x20 f)) 
                           (forall ((x21 N) (x22 N) (x23 N)) 
                               (=> 
                                   (and 
                                       (MS0 x21 x22 f) 
                                       (MS0 x21 x23 f)) 
                                   (= x22 x23))))) 
                   (or 
                       (and 
                           (forall ((x24 N)) 
                               (=> 
                                   (exists ((x25 N)) 
                                       (and 
                                           (= x25 p) 
                                           (MS0 x25 x24 lt))) 
                                   (exists ((x26 CLR)) 
                                       (and 
                                           (= x26 black) 
                                           (clr x24 x26))))) 
                           (forall ((x27 N)) 
                               (=> 
                                   (exists ((x28 N)) 
                                       (and 
                                           (= x28 p) 
                                           (MS0 x28 x27 rt))) 
                                   (exists ((x29 CLR)) 
                                       (and 
                                           (= x29 black) 
                                           (clr x27 x29))))) 
                           (not 
                               (= p t)) 
                           (exists ((x30 N)) 
                               (and 
                                   (MS0 p x30 f) 
                                   (MS x30 lft)))) 
                       (=> 
                           (and 
                               (forall ((x31 N)) 
                                   (=> 
                                       (exists ((x32 N)) 
                                           (and 
                                               (= x32 p) 
                                               (MS0 x32 x31 lt))) 
                                       (exists ((x33 CLR)) 
                                           (and 
                                               (= x33 black) 
                                               (clr x31 x33))))) 
                               (forall ((x34 N)) 
                                   (=> 
                                       (exists ((x35 N)) 
                                           (and 
                                               (= x35 p) 
                                               (MS0 x35 x34 rt))) 
                                       (exists ((x36 CLR)) 
                                           (and 
                                               (= x36 black) 
                                               (clr x34 x36))))) 
                               (not 
                                   (= p t))) 
                           (and 
                               (exists ((x37 N)) 
                                   (MS0 p x37 f)) 
                               (forall ((x38 N) (x39 N) (x40 N)) 
                                   (=> 
                                       (and 
                                           (MS0 x38 x39 f) 
                                           (MS0 x38 x40 f)) 
                                       (= x39 x40))))))))
         :named hyp10))
(assert (! (or 
               (not 
                   (forall ((x41 N)) 
                       (=> 
                           (exists ((x42 N)) 
                               (and 
                                   (= x42 p) 
                                   (MS0 x42 x41 ult))) 
                           (exists ((x43 CLR)) 
                               (and 
                                   (= x43 black) 
                                   (clr x41 x43)))))) 
               (and 
                   (forall ((x44 N)) 
                       (=> 
                           (exists ((x45 N)) 
                               (and 
                                   (= x45 p) 
                                   (MS0 x45 x44 ult))) 
                           (exists ((x46 CLR)) 
                               (and 
                                   (= x46 black) 
                                   (clr x44 x46))))) 
                   (not 
                       (forall ((x47 N)) 
                           (=> 
                               (exists ((x48 N)) 
                                   (and 
                                       (= x48 p) 
                                       (MS0 x48 x47 urt))) 
                               (exists ((x49 CLR)) 
                                   (and 
                                       (= x49 black) 
                                       (clr x47 x49))))))) 
               (and 
                   (=> 
                       (and 
                           (forall ((x50 N)) 
                               (=> 
                                   (exists ((x51 N)) 
                                       (and 
                                           (= x51 p) 
                                           (MS0 x51 x50 ult))) 
                                   (exists ((x52 CLR)) 
                                       (and 
                                           (= x52 black) 
                                           (clr x50 x52))))) 
                           (forall ((x53 N)) 
                               (=> 
                                   (exists ((x54 N)) 
                                       (and 
                                           (= x54 p) 
                                           (MS0 x54 x53 urt))) 
                                   (exists ((x55 CLR)) 
                                       (and 
                                           (= x55 black) 
                                           (clr x53 x55))))) 
                           (not 
                               (= p t))) 
                       (and 
                           (exists ((x56 N)) 
                               (MS0 p x56 f)) 
                           (forall ((x57 N) (x58 N) (x59 N)) 
                               (=> 
                                   (and 
                                       (MS0 x57 x58 f) 
                                       (MS0 x57 x59 f)) 
                                   (= x58 x59))))) 
                   (or 
                       (and 
                           (forall ((x60 N)) 
                               (=> 
                                   (exists ((x61 N)) 
                                       (and 
                                           (= x61 p) 
                                           (MS0 x61 x60 ult))) 
                                   (exists ((x62 CLR)) 
                                       (and 
                                           (= x62 black) 
                                           (clr x60 x62))))) 
                           (forall ((x63 N)) 
                               (=> 
                                   (exists ((x64 N)) 
                                       (and 
                                           (= x64 p) 
                                           (MS0 x64 x63 urt))) 
                                   (exists ((x65 CLR)) 
                                       (and 
                                           (= x65 black) 
                                           (clr x63 x65))))) 
                           (not 
                               (= p t)) 
                           (exists ((x66 N)) 
                               (and 
                                   (MS0 p x66 f) 
                                   (MS x66 lft)))) 
                       (=> 
                           (and 
                               (forall ((x67 N)) 
                                   (=> 
                                       (exists ((x68 N)) 
                                           (and 
                                               (= x68 p) 
                                               (MS0 x68 x67 ult))) 
                                       (exists ((x69 CLR)) 
                                           (and 
                                               (= x69 black) 
                                               (clr x67 x69))))) 
                               (forall ((x70 N)) 
                                   (=> 
                                       (exists ((x71 N)) 
                                           (and 
                                               (= x71 p) 
                                               (MS0 x71 x70 urt))) 
                                       (exists ((x72 CLR)) 
                                           (and 
                                               (= x72 black) 
                                               (clr x70 x72))))) 
                               (not 
                                   (= p t))) 
                           (and 
                               (exists ((x73 N)) 
                                   (MS0 p x73 f)) 
                               (forall ((x74 N) (x75 N) (x76 N)) 
                                   (=> 
                                       (and 
                                           (MS0 x74 x75 f) 
                                           (MS0 x74 x76 f)) 
                                       (= x75 x76))))))))
         :named hyp11))
(assert (! (or 
               (not 
                   (forall ((x77 N)) 
                       (=> 
                           (exists ((x78 N)) 
                               (and 
                                   (= x78 p) 
                                   (MS0 x78 x77 vlt))) 
                           (exists ((x79 CLR)) 
                               (and 
                                   (= x79 black) 
                                   (clr x77 x79)))))) 
               (and 
                   (forall ((x80 N)) 
                       (=> 
                           (exists ((x81 N)) 
                               (and 
                                   (= x81 p) 
                                   (MS0 x81 x80 vlt))) 
                           (exists ((x82 CLR)) 
                               (and 
                                   (= x82 black) 
                                   (clr x80 x82))))) 
                   (not 
                       (forall ((x83 N)) 
                           (=> 
                               (exists ((x84 N)) 
                                   (and 
                                       (= x84 p) 
                                       (MS0 x84 x83 vrt))) 
                               (exists ((x85 CLR)) 
                                   (and 
                                       (= x85 black) 
                                       (clr x83 x85))))))) 
               (and 
                   (=> 
                       (and 
                           (forall ((x86 N)) 
                               (=> 
                                   (exists ((x87 N)) 
                                       (and 
                                           (= x87 p) 
                                           (MS0 x87 x86 vlt))) 
                                   (exists ((x88 CLR)) 
                                       (and 
                                           (= x88 black) 
                                           (clr x86 x88))))) 
                           (forall ((x89 N)) 
                               (=> 
                                   (exists ((x90 N)) 
                                       (and 
                                           (= x90 p) 
                                           (MS0 x90 x89 vrt))) 
                                   (exists ((x91 CLR)) 
                                       (and 
                                           (= x91 black) 
                                           (clr x89 x91))))) 
                           (not 
                               (= p t))) 
                       (and 
                           (exists ((x92 N)) 
                               (MS0 p x92 h)) 
                           (forall ((x93 N) (x94 N) (x95 N)) 
                               (=> 
                                   (and 
                                       (MS0 x93 x94 h) 
                                       (MS0 x93 x95 h)) 
                                   (= x94 x95))))) 
                   (or 
                       (and 
                           (forall ((x96 N)) 
                               (=> 
                                   (exists ((x97 N)) 
                                       (and 
                                           (= x97 p) 
                                           (MS0 x97 x96 vlt))) 
                                   (exists ((x98 CLR)) 
                                       (and 
                                           (= x98 black) 
                                           (clr x96 x98))))) 
                           (forall ((x99 N)) 
                               (=> 
                                   (exists ((x100 N)) 
                                       (and 
                                           (= x100 p) 
                                           (MS0 x100 x99 vrt))) 
                                   (exists ((x101 CLR)) 
                                       (and 
                                           (= x101 black) 
                                           (clr x99 x101))))) 
                           (not 
                               (= p t)) 
                           (exists ((x102 N)) 
                               (and 
                                   (MS0 p x102 h) 
                                   (MS x102 lft)))) 
                       (=> 
                           (and 
                               (forall ((x103 N)) 
                                   (=> 
                                       (exists ((x104 N)) 
                                           (and 
                                               (= x104 p) 
                                               (MS0 x104 x103 vlt))) 
                                       (exists ((x105 CLR)) 
                                           (and 
                                               (= x105 black) 
                                               (clr x103 x105))))) 
                               (forall ((x106 N)) 
                                   (=> 
                                       (exists ((x107 N)) 
                                           (and 
                                               (= x107 p) 
                                               (MS0 x107 x106 vrt))) 
                                       (exists ((x108 CLR)) 
                                           (and 
                                               (= x108 black) 
                                               (clr x106 x108))))) 
                               (not 
                                   (= p t))) 
                           (and 
                               (exists ((x109 N)) 
                                   (MS0 p x109 h)) 
                               (forall ((x110 N) (x111 N) (x112 N)) 
                                   (=> 
                                       (and 
                                           (MS0 x110 x111 h) 
                                           (MS0 x110 x112 h)) 
                                       (= x111 x112))))))))
         :named hyp12))
(assert (! (forall ((x113 CLR)) 
               (or 
                   (= x113 black) 
                   (exists ((x114 N)) 
                       (and 
                           (MS0 p x114 wrt) 
                           (clr x114 x113)))))
         :named hyp13))
(assert (! (not 
               (exists ((x115 N)) 
                   (and 
                       (MS0 p x115 wrt) 
                       (clr x115 black))))
         :named hyp14))
(assert (! (not 
               (exists ((x116 CLR)) 
                   (and 
                       (= x116 black) 
                       (exists ((x117 N)) 
                           (and 
                               (MS0 p x117 wrt) 
                               (clr x117 x116))))))
         :named hyp15))
(assert (! (or 
               (and 
                   (not 
                       (forall ((x118 N)) 
                           (=> 
                               (exists ((x119 N)) 
                                   (and 
                                       (= x119 p) 
                                       (MS0 x119 x118 g))) 
                               (exists ((x120 CLR)) 
                                   (and 
                                       (= x120 black) 
                                       (clr x118 x120)))))) 
                   (exists ((y N)) 
                       (and 
                           (MS0 p y g) 
                           (not 
                               (exists ((x121 CLR)) 
                                   (and 
                                       (= x121 black) 
                                       (clr y x121))))))) 
               (and 
                   (forall ((x122 N)) 
                       (=> 
                           (exists ((x123 N)) 
                               (and 
                                   (= x123 p) 
                                   (MS0 x123 x122 g))) 
                           (exists ((x124 CLR)) 
                               (and 
                                   (= x124 black) 
                                   (clr x122 x124))))) 
                   (not 
                       (= p t))) 
               (and 
                   (forall ((x125 N)) 
                       (=> 
                           (exists ((x126 N)) 
                               (and 
                                   (= x126 p) 
                                   (MS0 x126 x125 g))) 
                           (exists ((x127 CLR)) 
                               (and 
                                   (= x127 black) 
                                   (clr x125 x127))))) 
                   (= p t)))
         :named hyp16))
(assert (! (or 
               (not 
                   (forall ((x128 N)) 
                       (=> 
                           (exists ((x129 N)) 
                               (and 
                                   (= x129 p) 
                                   (MS0 x129 x128 lt))) 
                           (exists ((x130 CLR)) 
                               (and 
                                   (= x130 black) 
                                   (clr x128 x130)))))) 
               (and 
                   (forall ((x131 N)) 
                       (=> 
                           (exists ((x132 N)) 
                               (and 
                                   (= x132 p) 
                                   (MS0 x132 x131 lt))) 
                           (exists ((x133 CLR)) 
                               (and 
                                   (= x133 black) 
                                   (clr x131 x133))))) 
                   (not 
                       (forall ((x134 N)) 
                           (=> 
                               (exists ((x135 N)) 
                                   (and 
                                       (= x135 p) 
                                       (MS0 x135 x134 rt))) 
                               (exists ((x136 CLR)) 
                                   (and 
                                       (= x136 black) 
                                       (clr x134 x136))))))) 
               (and 
                   (forall ((x137 N)) 
                       (=> 
                           (exists ((x138 N)) 
                               (and 
                                   (= x138 p) 
                                   (MS0 x138 x137 lt))) 
                           (exists ((x139 CLR)) 
                               (and 
                                   (= x139 black) 
                                   (clr x137 x139))))) 
                   (forall ((x140 N)) 
                       (=> 
                           (exists ((x141 N)) 
                               (and 
                                   (= x141 p) 
                                   (MS0 x141 x140 rt))) 
                           (exists ((x142 CLR)) 
                               (and 
                                   (= x142 black) 
                                   (clr x140 x142))))) 
                   (not 
                       (= p t))) 
               (and 
                   (forall ((x143 N)) 
                       (=> 
                           (exists ((x144 N)) 
                               (and 
                                   (= x144 p) 
                                   (MS0 x144 x143 lt))) 
                           (exists ((x145 CLR)) 
                               (and 
                                   (= x145 black) 
                                   (clr x143 x145))))) 
                   (forall ((x146 N)) 
                       (=> 
                           (exists ((x147 N)) 
                               (and 
                                   (= x147 p) 
                                   (MS0 x147 x146 rt))) 
                           (exists ((x148 CLR)) 
                               (and 
                                   (= x148 black) 
                                   (clr x146 x148))))) 
                   (= p t)))
         :named hyp17))
(assert (! (or 
               (not 
                   (forall ((x149 N)) 
                       (=> 
                           (exists ((x150 N)) 
                               (and 
                                   (= x150 p) 
                                   (MS0 x150 x149 lt))) 
                           (exists ((x151 CLR)) 
                               (and 
                                   (= x151 black) 
                                   (clr x149 x151)))))) 
               (and 
                   (forall ((x152 N)) 
                       (=> 
                           (exists ((x153 N)) 
                               (and 
                                   (= x153 p) 
                                   (MS0 x153 x152 lt))) 
                           (exists ((x154 CLR)) 
                               (and 
                                   (= x154 black) 
                                   (clr x152 x154))))) 
                   (not 
                       (forall ((x155 N)) 
                           (=> 
                               (exists ((x156 N)) 
                                   (and 
                                       (= x156 p) 
                                       (MS0 x156 x155 rt))) 
                               (exists ((x157 CLR)) 
                                   (and 
                                       (= x157 black) 
                                       (clr x155 x157))))))) 
               (and 
                   (forall ((x158 N)) 
                       (=> 
                           (exists ((x159 N)) 
                               (and 
                                   (= x159 p) 
                                   (MS0 x159 x158 lt))) 
                           (exists ((x160 CLR)) 
                               (and 
                                   (= x160 black) 
                                   (clr x158 x160))))) 
                   (forall ((x161 N)) 
                       (=> 
                           (exists ((x162 N)) 
                               (and 
                                   (= x162 p) 
                                   (MS0 x162 x161 rt))) 
                           (exists ((x163 CLR)) 
                               (and 
                                   (= x163 black) 
                                   (clr x161 x163))))) 
                   (not 
                       (= p t)) 
                   (exists ((x164 N)) 
                       (and 
                           (MS0 p x164 f) 
                           (MS x164 lft)))) 
               (and 
                   (forall ((x165 N)) 
                       (=> 
                           (exists ((x166 N)) 
                               (and 
                                   (= x166 p) 
                                   (MS0 x166 x165 lt))) 
                           (exists ((x167 CLR)) 
                               (and 
                                   (= x167 black) 
                                   (clr x165 x167))))) 
                   (forall ((x168 N)) 
                       (=> 
                           (exists ((x169 N)) 
                               (and 
                                   (= x169 p) 
                                   (MS0 x169 x168 rt))) 
                           (exists ((x170 CLR)) 
                               (and 
                                   (= x170 black) 
                                   (clr x168 x170))))) 
                   (not 
                       (= p t)) 
                   (exists ((x171 N)) 
                       (and 
                           (MS0 p x171 f) 
                           (MS x171 rht)))) 
               (and 
                   (forall ((x172 N)) 
                       (=> 
                           (exists ((x173 N)) 
                               (and 
                                   (= x173 p) 
                                   (MS0 x173 x172 lt))) 
                           (exists ((x174 CLR)) 
                               (and 
                                   (= x174 black) 
                                   (clr x172 x174))))) 
                   (forall ((x175 N)) 
                       (=> 
                           (exists ((x176 N)) 
                               (and 
                                   (= x176 p) 
                                   (MS0 x176 x175 rt))) 
                           (exists ((x177 CLR)) 
                               (and 
                                   (= x177 black) 
                                   (clr x175 x177))))) 
                   (= p t)))
         :named hyp18))
(assert (! (or 
               (not 
                   (forall ((x178 N)) 
                       (=> 
                           (exists ((x179 N)) 
                               (and 
                                   (= x179 p) 
                                   (MS0 x179 x178 ult))) 
                           (exists ((x180 CLR)) 
                               (and 
                                   (= x180 black) 
                                   (clr x178 x180)))))) 
               (and 
                   (forall ((x181 N)) 
                       (=> 
                           (exists ((x182 N)) 
                               (and 
                                   (= x182 p) 
                                   (MS0 x182 x181 ult))) 
                           (exists ((x183 CLR)) 
                               (and 
                                   (= x183 black) 
                                   (clr x181 x183))))) 
                   (not 
                       (forall ((x184 N)) 
                           (=> 
                               (exists ((x185 N)) 
                                   (and 
                                       (= x185 p) 
                                       (MS0 x185 x184 urt))) 
                               (exists ((x186 CLR)) 
                                   (and 
                                       (= x186 black) 
                                       (clr x184 x186))))))) 
               (and 
                   (forall ((x187 N)) 
                       (=> 
                           (exists ((x188 N)) 
                               (and 
                                   (= x188 p) 
                                   (MS0 x188 x187 ult))) 
                           (exists ((x189 CLR)) 
                               (and 
                                   (= x189 black) 
                                   (clr x187 x189))))) 
                   (forall ((x190 N)) 
                       (=> 
                           (exists ((x191 N)) 
                               (and 
                                   (= x191 p) 
                                   (MS0 x191 x190 urt))) 
                           (exists ((x192 CLR)) 
                               (and 
                                   (= x192 black) 
                                   (clr x190 x192))))) 
                   (not 
                       (= p t)) 
                   (exists ((x193 N)) 
                       (and 
                           (MS0 p x193 f) 
                           (MS x193 lft)))) 
               (and 
                   (forall ((x194 N)) 
                       (=> 
                           (exists ((x195 N)) 
                               (and 
                                   (= x195 p) 
                                   (MS0 x195 x194 ult))) 
                           (exists ((x196 CLR)) 
                               (and 
                                   (= x196 black) 
                                   (clr x194 x196))))) 
                   (forall ((x197 N)) 
                       (=> 
                           (exists ((x198 N)) 
                               (and 
                                   (= x198 p) 
                                   (MS0 x198 x197 urt))) 
                           (exists ((x199 CLR)) 
                               (and 
                                   (= x199 black) 
                                   (clr x197 x199))))) 
                   (not 
                       (= p t)) 
                   (exists ((x200 N)) 
                       (and 
                           (MS0 p x200 f) 
                           (MS x200 rht)))) 
               (and 
                   (forall ((x201 N)) 
                       (=> 
                           (exists ((x202 N)) 
                               (and 
                                   (= x202 p) 
                                   (MS0 x202 x201 ult))) 
                           (exists ((x203 CLR)) 
                               (and 
                                   (= x203 black) 
                                   (clr x201 x203))))) 
                   (forall ((x204 N)) 
                       (=> 
                           (exists ((x205 N)) 
                               (and 
                                   (= x205 p) 
                                   (MS0 x205 x204 urt))) 
                           (exists ((x206 CLR)) 
                               (and 
                                   (= x206 black) 
                                   (clr x204 x206))))) 
                   (= p t)))
         :named hyp19))
(assert (! (or 
               (not 
                   (forall ((x207 N)) 
                       (=> 
                           (exists ((x208 N)) 
                               (and 
                                   (= x208 p) 
                                   (MS0 x208 x207 vlt))) 
                           (exists ((x209 CLR)) 
                               (and 
                                   (= x209 black) 
                                   (clr x207 x209)))))) 
               (and 
                   (forall ((x210 N)) 
                       (=> 
                           (exists ((x211 N)) 
                               (and 
                                   (= x211 p) 
                                   (MS0 x211 x210 vlt))) 
                           (exists ((x212 CLR)) 
                               (and 
                                   (= x212 black) 
                                   (clr x210 x212))))) 
                   (not 
                       (forall ((x213 N)) 
                           (=> 
                               (exists ((x214 N)) 
                                   (and 
                                       (= x214 p) 
                                       (MS0 x214 x213 vrt))) 
                               (exists ((x215 CLR)) 
                                   (and 
                                       (= x215 black) 
                                       (clr x213 x215))))))) 
               (and 
                   (forall ((x216 N)) 
                       (=> 
                           (exists ((x217 N)) 
                               (and 
                                   (= x217 p) 
                                   (MS0 x217 x216 vlt))) 
                           (exists ((x218 CLR)) 
                               (and 
                                   (= x218 black) 
                                   (clr x216 x218))))) 
                   (forall ((x219 N)) 
                       (=> 
                           (exists ((x220 N)) 
                               (and 
                                   (= x220 p) 
                                   (MS0 x220 x219 vrt))) 
                           (exists ((x221 CLR)) 
                               (and 
                                   (= x221 black) 
                                   (clr x219 x221))))) 
                   (not 
                       (= p t)) 
                   (exists ((x222 N)) 
                       (and 
                           (MS0 p x222 h) 
                           (MS x222 lft)))) 
               (and 
                   (forall ((x223 N)) 
                       (=> 
                           (exists ((x224 N)) 
                               (and 
                                   (= x224 p) 
                                   (MS0 x224 x223 vlt))) 
                           (exists ((x225 CLR)) 
                               (and 
                                   (= x225 black) 
                                   (clr x223 x225))))) 
                   (forall ((x226 N)) 
                       (=> 
                           (exists ((x227 N)) 
                               (and 
                                   (= x227 p) 
                                   (MS0 x227 x226 vrt))) 
                           (exists ((x228 CLR)) 
                               (and 
                                   (= x228 black) 
                                   (clr x226 x228))))) 
                   (not 
                       (= p t)) 
                   (exists ((x229 N)) 
                       (and 
                           (MS0 p x229 h) 
                           (MS x229 rht)))) 
               (and 
                   (forall ((x230 N)) 
                       (=> 
                           (exists ((x231 N)) 
                               (and 
                                   (= x231 p) 
                                   (MS0 x231 x230 vlt))) 
                           (exists ((x232 CLR)) 
                               (and 
                                   (= x232 black) 
                                   (clr x230 x232))))) 
                   (forall ((x233 N)) 
                       (=> 
                           (exists ((x234 N)) 
                               (and 
                                   (= x234 p) 
                                   (MS0 x234 x233 vrt))) 
                           (exists ((x235 CLR)) 
                               (and 
                                   (= x235 black) 
                                   (clr x233 x235))))) 
                   (= p t)))
         :named hyp20))
(assert (! (or 
               (and 
                   (not 
                       (MS0 p nil wlt)) 
                   (not 
                       (exists ((x236 CLR)) 
                           (and 
                               (= x236 black) 
                               (exists ((x237 N)) 
                                   (and 
                                       (MS0 p x237 wlt) 
                                       (clr x237 x236))))))) 
               (=> 
                   (not 
                       (MS0 p nil wlt)) 
                   (exists ((x238 CLR)) 
                       (and 
                           (= x238 black) 
                           (exists ((x239 N)) 
                               (and 
                                   (MS0 p x239 wlt) 
                                   (clr x239 x238)))))))
         :named hyp21))
(assert (! (forall ((a Int)) 
               (exists ((b0 Int) (f0 PNZ)) 
                   (and 
                       (forall ((x240 N) (x241 Int)) 
                           (=> 
                               (MS1 x240 x241 f0) 
                               (and 
                                   (<= a x241) 
                                   (<= x241 b0)))) 
                       (forall ((x242 N) (x243 Int) (x244 Int)) 
                           (=> 
                               (and 
                                   (MS1 x242 x243 f0) 
                                   (MS1 x242 x244 f0)) 
                               (= x243 x244))) 
                       (forall ((x245 N)) 
                           (exists ((x246 Int)) 
                               (MS1 x245 x246 f0))) 
                       (forall ((x247 Int) (x248 N) (x249 N)) 
                           (=> 
                               (and 
                                   (MS1 x248 x247 f0) 
                                   (MS1 x249 x247 f0)) 
                               (= x248 x249))))))
         :named hyp22))
(assert (! (forall ((x250 N) (x251 N)) 
               (=> 
                   (= x250 x251) 
                   (MS0 x250 x251 c)))
         :named hyp23))
(assert (! (forall ((x252 N) (x253 N)) 
               (=> 
                   (exists ((x254 N)) 
                       (and 
                           (MS0 x252 x254 c) 
                           (MS0 x254 x253 g))) 
                   (MS0 x252 x253 c)))
         :named hyp24))
(assert (! (forall ((r PNN)) 
               (=> 
                   (and 
                       (forall ((x255 N) (x256 N)) 
                           (=> 
                               (= x255 x256) 
                               (MS0 x255 x256 r))) 
                       (forall ((x257 N) (x258 N)) 
                           (=> 
                               (exists ((x259 N)) 
                                   (and 
                                       (MS0 x257 x259 r) 
                                       (MS0 x259 x258 g))) 
                               (MS0 x257 x258 r)))) 
                   (forall ((x260 N) (x261 N)) 
                       (=> 
                           (MS0 x260 x261 c) 
                           (MS0 x260 x261 r)))))
         :named hyp25))
(assert (! (forall ((x262 N) (x263 N) (x264 N)) 
               (=> 
                   (and 
                       (MS0 x262 x263 lt) 
                       (MS0 x262 x264 lt)) 
                   (= x263 x264)))
         :named hyp26))
(assert (! (forall ((x265 N) (x266 N) (x267 N)) 
               (=> 
                   (and 
                       (MS0 x265 x266 rt) 
                       (MS0 x265 x267 rt)) 
                   (= x266 x267)))
         :named hyp27))
(assert (! (forall ((x268 N) (x269 N)) 
               (= 
                   (MS0 x268 x269 g) 
                   (or 
                       (MS0 x268 x269 lt) 
                       (MS0 x268 x269 rt))))
         :named hyp28))
(assert (! (and 
               (forall ((x270 N) (x271 N) (x272 N)) 
                   (=> 
                       (and 
                           (MS0 x270 x271 ltp) 
                           (MS0 x270 x272 ltp)) 
                       (= x271 x272))) 
               (forall ((x273 N)) 
                   (exists ((x274 N)) 
                       (MS0 x273 x274 ltp))))
         :named hyp29))
(assert (! (and 
               (forall ((x275 N) (x276 N) (x277 N)) 
                   (=> 
                       (and 
                           (MS0 x275 x276 rtp) 
                           (MS0 x275 x277 rtp)) 
                       (= x276 x277))) 
               (forall ((x278 N)) 
                   (exists ((x279 N)) 
                       (MS0 x278 x279 rtp))))
         :named hyp30))
(assert (! (forall ((x280 N) (x281 N)) 
               (= 
                   (MS0 x280 x281 ltp) 
                   (or 
                       (and 
                           (= x281 nil) 
                           (not 
                               (exists ((x282 N)) 
                                   (MS0 x280 x282 lt)))) 
                       (MS0 x280 x281 lt))))
         :named hyp31))
(assert (! (forall ((x283 N) (x284 N)) 
               (= 
                   (MS0 x283 x284 rtp) 
                   (or 
                       (and 
                           (= x284 nil) 
                           (not 
                               (exists ((x285 N)) 
                                   (MS0 x283 x285 rt)))) 
                       (MS0 x283 x284 rt))))
         :named hyp32))
(assert (! (MS t b)
         :named hyp33))
(assert (! (=> 
               (forall ((x286 N)) 
                   (=> 
                       (exists ((x287 N)) 
                           (and 
                               (MS x287 b) 
                               (MS0 x287 x286 g))) 
                       (MS x286 b))) 
               (forall ((x288 N)) 
                   (=> 
                       (exists ((x289 N)) 
                           (and 
                               (MS x289 b) 
                               (MS0 x289 x288 c))) 
                       (MS x288 b))))
         :named hyp34))
(assert (! (forall ((x290 N)) 
               (=> 
                   (MS x290 b) 
                   (exists ((x291 N)) 
                       (and 
                           (= x291 t) 
                           (MS0 x291 x290 c)))))
         :named hyp35))
(assert (! (MS p b)
         :named hyp36))
(assert (! (and 
               (forall ((x292 N) (x293 N)) 
                   (=> 
                       (MS0 x292 x293 f) 
                       (and 
                           (MS x292 b) 
                           (not 
                               (= x292 t)) 
                           (MS x293 b) 
                           (not 
                               (= x293 p))))) 
               (forall ((x294 N) (x295 N) (x296 N)) 
                   (=> 
                       (and 
                           (MS0 x294 x295 f) 
                           (MS0 x294 x296 f)) 
                       (= x295 x296))) 
               (forall ((x297 N) (x298 N) (x299 N)) 
                   (=> 
                       (and 
                           (MS0 x298 x297 f) 
                           (MS0 x299 x297 f)) 
                       (= x298 x299))))
         :named hyp37))
(assert (! (forall ((x300 N)) 
               (= 
                   (or 
                       (exists ((x301 N)) 
                           (MS0 x300 x301 f)) 
                       (= x300 t)) 
                   (or 
                       (exists ((x302 N)) 
                           (MS0 x302 x300 f)) 
                       (= x300 p))))
         :named hyp38))
(assert (! (forall ((s PN)) 
               (=> 
                   (and 
                       (forall ((x303 N)) 
                           (=> 
                               (MS x303 s) 
                               (or 
                                   (exists ((x304 N)) 
                                       (MS0 x303 x304 f)) 
                                   (= x303 t)))) 
                       (forall ((x305 N)) 
                           (=> 
                               (MS x305 s) 
                               (exists ((x306 N)) 
                                   (and 
                                       (MS x306 s) 
                                       (MS0 x305 x306 f)))))) 
                   (forall ((x307 N)) 
                       (not 
                           (MS x307 s)))))
         :named hyp39))
(assert (! (forall ((x308 N) (x309 N)) 
               (=> 
                   (MS0 x309 x308 f) 
                   (MS0 x308 x309 g)))
         :named hyp40))
(assert (! (forall ((x310 N)) 
               (=> 
                   (exists ((x311 N)) 
                       (and 
                           (MS x311 b) 
                           (not 
                               (or 
                                   (exists ((x312 N)) 
                                       (MS0 x311 x312 f)) 
                                   (= x311 t))) 
                           (MS0 x311 x310 g))) 
                   (MS x310 b)))
         :named hyp41))
(assert (! (=> 
               (= n ok) 
               (forall ((x313 N)) 
                   (=> 
                       (exists ((x314 N)) 
                           (and 
                               (MS x314 b) 
                               (MS0 x314 x313 g))) 
                       (MS x313 b))))
         :named hyp42))
(assert (! (=> 
               (= n ok) 
               (= p t))
         :named hyp43))
(assert (! (=> 
               (= p t) 
               (forall ((x315 N) (x316 N)) 
                   (not 
                       (MS0 x315 x316 f))))
         :named hyp44))
(assert (! (=> 
               (forall ((x317 N) (x318 N)) 
                   (not 
                       (MS0 x317 x318 f))) 
               (= p t))
         :named hyp45))
(assert (! (forall ((x319 N)) 
               (= 
                   (or 
                       (MS x319 lft) 
                       (MS x319 rht)) 
                   (exists ((x320 N)) 
                       (MS0 x320 x319 f))))
         :named hyp46))
(assert (! (forall ((x321 N)) 
               (not 
                   (and 
                       (MS x321 lft) 
                       (MS x321 rht))))
         :named hyp47))
(assert (! (forall ((x322 N) (x323 N)) 
               (=> 
                   (and 
                       (MS0 x323 x322 f) 
                       (MS x322 lft)) 
                   (MS0 x322 x323 lt)))
         :named hyp48))
(assert (! (forall ((x324 N) (x325 N)) 
               (=> 
                   (and 
                       (MS0 x325 x324 f) 
                       (MS x324 rht)) 
                   (MS0 x324 x325 rt)))
         :named hyp49))
(assert (! (=> 
               (forall ((x326 N) (x327 N)) 
                   (not 
                       (MS0 x326 x327 f))) 
               (and 
                   (forall ((x328 N)) 
                       (not 
                           (MS x328 lft))) 
                   (forall ((x329 N)) 
                       (not 
                           (MS x329 rht)))))
         :named hyp50))
(assert (! (=> 
               (= n ok) 
               (forall ((x330 N) (x331 N)) 
                   (not 
                       (MS0 x330 x331 f))))
         :named hyp51))
(assert (! (=> 
               (= n ok) 
               (and 
                   (forall ((x332 N)) 
                       (not 
                           (MS x332 lft))) 
                   (forall ((x333 N)) 
                       (not 
                           (MS x333 rht)))))
         :named hyp52))
(assert (! (forall ((x334 N) (x335 N)) 
               (= 
                   (MS0 x334 x335 ult) 
                   (or 
                       (and 
                           (MS0 x334 x335 lt) 
                           (not 
                               (MS x334 lft))) 
                       (and 
                           (MS0 x334 x335 f) 
                           (MS x334 lft)))))
         :named hyp53))
(assert (! (forall ((x336 N) (x337 N) (x338 N)) 
               (=> 
                   (and 
                       (MS0 x336 x337 ult) 
                       (MS0 x336 x338 ult)) 
                   (= x337 x338)))
         :named hyp54))
(assert (! (forall ((x339 N) (x340 N)) 
               (= 
                   (MS0 x339 x340 urt) 
                   (or 
                       (and 
                           (MS0 x339 x340 rt) 
                           (not 
                               (MS x339 rht))) 
                       (and 
                           (MS0 x339 x340 f) 
                           (MS x339 rht)))))
         :named hyp55))
(assert (! (forall ((x341 N) (x342 N) (x343 N)) 
               (=> 
                   (and 
                       (MS0 x341 x342 urt) 
                       (MS0 x341 x343 urt)) 
                   (= x342 x343)))
         :named hyp56))
(assert (! (forall ((x344 N) (x345 N)) 
               (= 
                   (MS0 x344 x345 h) 
                   (and 
                       (MS0 x344 x345 f) 
                       (= x344 p))))
         :named hyp57))
(assert (! (=> 
               (= n ok) 
               (forall ((x346 N) (x347 N)) 
                   (= 
                       (MS0 x346 x347 ult) 
                       (MS0 x346 x347 lt))))
         :named hyp58))
(assert (! (=> 
               (= n ok) 
               (forall ((x348 N) (x349 N)) 
                   (= 
                       (MS0 x348 x349 urt) 
                       (MS0 x348 x349 rt))))
         :named hyp59))
(assert (! (forall ((x350 N) (x351 N)) 
               (= 
                   (MS0 x350 x351 vlt) 
                   (or 
                       (and 
                           (MS0 x350 x351 ult) 
                           (not 
                               (exists ((x352 N)) 
                                   (and 
                                       (= x350 t) 
                                       (= x352 nil) 
                                       (MS x350 lft))))) 
                       (and 
                           (= x350 t) 
                           (= x351 nil) 
                           (MS x350 lft)))))
         :named hyp60))
(assert (! (forall ((x353 N) (x354 N) (x355 N)) 
               (=> 
                   (and 
                       (MS0 x353 x354 vlt) 
                       (MS0 x353 x355 vlt)) 
                   (= x354 x355)))
         :named hyp61))
(assert (! (forall ((x356 N) (x357 N)) 
               (= 
                   (MS0 x356 x357 vrt) 
                   (or 
                       (and 
                           (MS0 x356 x357 urt) 
                           (not 
                               (exists ((x358 N)) 
                                   (and 
                                       (= x356 t) 
                                       (= x358 nil) 
                                       (MS x356 rht))))) 
                       (and 
                           (= x356 t) 
                           (= x357 nil) 
                           (MS x356 rht)))))
         :named hyp62))
(assert (! (forall ((x359 N) (x360 N) (x361 N)) 
               (=> 
                   (and 
                       (MS0 x359 x360 vrt) 
                       (MS0 x359 x361 vrt)) 
                   (= x360 x361)))
         :named hyp63))
(assert (! (=> 
               (= p t) 
               (= q nil))
         :named hyp64))
(assert (! (=> 
               (= n ok) 
               (forall ((x362 N) (x363 N)) 
                   (= 
                       (MS0 x362 x363 vlt) 
                       (MS0 x362 x363 lt))))
         :named hyp65))
(assert (! (=> 
               (= n ok) 
               (forall ((x364 N) (x365 N)) 
                   (= 
                       (MS0 x364 x365 vrt) 
                       (MS0 x364 x365 rt))))
         :named hyp66))
(assert (! (and 
               (forall ((x366 N) (x367 N) (x368 N)) 
                   (=> 
                       (and 
                           (MS0 x366 x367 wlt) 
                           (MS0 x366 x368 wlt)) 
                       (= x367 x368))) 
               (forall ((x369 N)) 
                   (exists ((x370 N)) 
                       (MS0 x369 x370 wlt))))
         :named hyp67))
(assert (! (and 
               (forall ((x371 N) (x372 N) (x373 N)) 
                   (=> 
                       (and 
                           (MS0 x371 x372 wrt) 
                           (MS0 x371 x373 wrt)) 
                       (= x372 x373))) 
               (forall ((x374 N)) 
                   (exists ((x375 N)) 
                       (MS0 x374 x375 wrt))))
         :named hyp68))
(assert (! (forall ((x376 N) (x377 N)) 
               (= 
                   (MS0 x376 x377 wlt) 
                   (or 
                       (and 
                           (= x377 nil) 
                           (not 
                               (exists ((x378 N)) 
                                   (MS0 x376 x378 vlt)))) 
                       (MS0 x376 x377 vlt))))
         :named hyp69))
(assert (! (forall ((x379 N) (x380 N)) 
               (= 
                   (MS0 x379 x380 wrt) 
                   (or 
                       (and 
                           (= x380 nil) 
                           (not 
                               (exists ((x381 N)) 
                                   (MS0 x379 x381 vrt)))) 
                       (MS0 x379 x380 vrt))))
         :named hyp70))
(assert (! (=> 
               (= n ok) 
               (forall ((x382 N) (x383 N)) 
                   (= 
                       (MS0 x382 x383 wlt) 
                       (MS0 x382 x383 ltp))))
         :named hyp71))
(assert (! (=> 
               (= n ok) 
               (forall ((x384 N) (x385 N)) 
                   (= 
                       (MS0 x384 x385 wrt) 
                       (MS0 x384 x385 rtp))))
         :named hyp72))
(assert (! (and 
               (forall ((x386 N) (x387 CLR) (x388 CLR)) 
                   (=> 
                       (and 
                           (clr x386 x387) 
                           (clr x386 x388)) 
                       (= x387 x388))) 
               (forall ((x389 N)) 
                   (exists ((x390 CLR)) 
                       (clr x389 x390))))
         :named hyp73))
(assert (! (and 
               (forall ((x391 N) (x392 DIR)) 
                   (=> 
                       (dirp x391 x392) 
                       (and 
                           (or 
                               (MS x391 lft) 
                               (MS x391 rht)) 
                           (or 
                               (= x392 left) 
                               (= x392 right))))) 
               (forall ((x393 N) (x394 DIR) (x395 DIR)) 
                   (=> 
                       (and 
                           (dirp x393 x394) 
                           (dirp x393 x395)) 
                       (= x394 x395))) 
               (forall ((x396 N)) 
                   (=> 
                       (or 
                           (MS x396 lft) 
                           (MS x396 rht)) 
                       (exists ((x397 DIR)) 
                           (dirp x396 x397)))))
         :named hyp74))
(assert (! (forall ((x398 N)) 
               (= 
                   (MS x398 lft) 
                   (exists ((x399 DIR)) 
                       (and 
                           (= x399 left) 
                           (dirp x398 x399)))))
         :named hyp75))
(assert (! (forall ((x400 N)) 
               (= 
                   (MS x400 rht) 
                   (exists ((x401 DIR)) 
                       (and 
                           (= x401 right) 
                           (dirp x400 x401)))))
         :named hyp76))
(assert (! (forall ((x402 CLR)) 
               (or 
                   (= x402 black) 
                   (= x402 white)))
         :named hyp77))
(assert (! (exists ((x403 CLR) (x404 N)) 
               (and 
                   (MS0 p x404 wlt) 
                   (clr x404 x403)))
         :named hyp78))
(assert (! (exists ((x405 N)) 
               (MS0 p x405 wlt))
         :named hyp79))
(assert (! (forall ((x406 N) (x407 N) (x408 N)) 
               (=> 
                   (and 
                       (MS0 x406 x407 wlt) 
                       (MS0 x406 x408 wlt)) 
                   (= x407 x408)))
         :named hyp80))
(assert (! (= 
               (exists ((x409 N)) 
                   (and 
                       (MS0 p x409 wlt) 
                       (MS x409 b))) 
               (exists ((x410 N)) 
                   (and 
                       (MS0 p x410 wlt) 
                       (clr x410 black))))
         :named hyp81))
(assert (! (forall ((x411 N) (x412 CLR) (x413 CLR)) 
               (=> 
                   (and 
                       (clr x411 x412) 
                       (clr x411 x413)) 
                   (= x412 x413)))
         :named hyp82))
(assert (! (exists ((x414 CLR) (x415 N)) 
               (and 
                   (MS0 p x415 wrt) 
                   (clr x415 x414)))
         :named hyp83))
(assert (! (exists ((x416 N)) 
               (MS0 p x416 wrt))
         :named hyp84))
(assert (! (forall ((x417 N) (x418 N) (x419 N)) 
               (=> 
                   (and 
                       (MS0 x417 x418 wrt) 
                       (MS0 x417 x419 wrt)) 
                   (= x418 x419)))
         :named hyp85))
(assert (! (or 
               (exists ((x420 N)) 
                   (and 
                       (MS0 p x420 wlt) 
                       (clr x420 black))) 
               (exists ((x421 N)) 
                   (and 
                       (MS0 p x421 wlt) 
                       (clr x421 white))))
         :named hyp86))
(assert (! (or 
               (exists ((x422 N)) 
                   (and 
                       (MS0 p x422 wrt) 
                       (clr x422 black))) 
               (exists ((x423 N)) 
                   (and 
                       (MS0 p x423 wrt) 
                       (clr x423 white))))
         :named hyp87))
(assert (! (not 
               (= black white))
         :named hyp88))
(assert (! (not 
               (or 
                   (exists ((x424 N)) 
                       (MS0 nil x424 lt)) 
                   (exists ((x425 N)) 
                       (MS0 nil x425 rt))))
         :named hyp89))
(assert (! (not 
               (or 
                   (exists ((x426 N)) 
                       (MS0 x426 nil lt)) 
                   (exists ((x427 N)) 
                       (MS0 x427 nil rt))))
         :named hyp90))
(assert (! (or 
               (forall ((x428 N)) 
                   (=> 
                       (exists ((x429 N)) 
                           (and 
                               (MS x429 b) 
                               (MS0 x429 x428 g))) 
                       (MS x428 b))) 
               (and 
                   (not 
                       (forall ((x430 N)) 
                           (=> 
                               (exists ((x431 N)) 
                                   (and 
                                       (MS x431 b) 
                                       (MS0 x431 x430 g))) 
                               (MS x430 b)))) 
                   (exists ((x432 N) (y0 N)) 
                       (and 
                           (MS0 x432 y0 g) 
                           (MS x432 b) 
                           (not 
                               (MS y0 b))))))
         :named hyp91))
(assert (! (=> 
               (not 
                   (= p t)) 
               (exists ((x433 N)) 
                   (MS0 p x433 f)))
         :named hyp92))
(assert (! (=> 
               (and 
                   (not 
                       (= p t)) 
                   (MS0 p t f)) 
               (forall ((x434 N) (x435 N)) 
                   (= 
                       (MS0 x434 x435 f) 
                       (and 
                           (= x434 p) 
                           (= x435 t)))))
         :named hyp93))
(assert (! (=> 
               (not 
                   (= p t)) 
               (and 
                   (exists ((x436 N)) 
                       (MS0 p x436 f)) 
                   (forall ((x437 N) (x438 N) (x439 N)) 
                       (=> 
                           (and 
                               (MS0 x437 x438 f) 
                               (MS0 x437 x439 f)) 
                           (= x438 x439)))))
         :named hyp94))
(assert (! (not 
               (MS p lft))
         :named hyp95))
(assert (! (not 
               (MS p rht))
         :named hyp96))
(assert (! (=> 
               (not 
                   (= p t)) 
               (or 
                   (exists ((x440 N)) 
                       (and 
                           (MS0 p x440 h) 
                           (MS x440 lft))) 
                   (exists ((x441 N)) 
                       (and 
                           (MS0 p x441 h) 
                           (MS x441 rht)))))
         :named hyp97))
(assert (! (=> 
               (not 
                   (= p t)) 
               (and 
                   (exists ((x442 N)) 
                       (MS0 p x442 h)) 
                   (forall ((x443 N) (x444 N) (x445 N)) 
                       (=> 
                           (and 
                               (MS0 x443 x444 h) 
                               (MS0 x443 x445 h)) 
                           (= x444 x445)))))
         :named hyp98))
(assert (! (=> 
               (not 
                   (= p t)) 
               (MS0 p q h))
         :named hyp99))
(assert (! (=> 
               (not 
                   (= p t)) 
               (or 
                   (MS q lft) 
                   (MS q rht)))
         :named hyp100))
(assert (! (or 
               (and 
                   (not 
                       (forall ((x446 N)) 
                           (=> 
                               (exists ((x447 N)) 
                                   (and 
                                       (= x447 p) 
                                       (MS0 x447 x446 g))) 
                               (MS x446 b)))) 
                   (exists ((y1 N)) 
                       (and 
                           (MS0 p y1 g) 
                           (not 
                               (MS y1 b))))) 
               (and 
                   (forall ((x448 N)) 
                       (=> 
                           (exists ((x449 N)) 
                               (and 
                                   (= x449 p) 
                                   (MS0 x449 x448 g))) 
                           (MS x448 b))) 
                   (not 
                       (= p t))) 
               (and 
                   (forall ((x450 N)) 
                       (=> 
                           (exists ((x451 N)) 
                               (and 
                                   (= x451 p) 
                                   (MS0 x451 x450 g))) 
                           (MS x450 b))) 
                   (= p t)) 
               (= n ok))
         :named hyp101))
(assert (! (or 
               (not 
                   (forall ((x452 N)) 
                       (=> 
                           (exists ((x453 N)) 
                               (and 
                                   (= x453 p) 
                                   (MS0 x453 x452 lt))) 
                           (MS x452 b)))) 
               (and 
                   (forall ((x454 N)) 
                       (=> 
                           (exists ((x455 N)) 
                               (and 
                                   (= x455 p) 
                                   (MS0 x455 x454 lt))) 
                           (MS x454 b))) 
                   (not 
                       (forall ((x456 N)) 
                           (=> 
                               (exists ((x457 N)) 
                                   (and 
                                       (= x457 p) 
                                       (MS0 x457 x456 rt))) 
                               (MS x456 b))))) 
               (and 
                   (forall ((x458 N)) 
                       (=> 
                           (exists ((x459 N)) 
                               (and 
                                   (= x459 p) 
                                   (MS0 x459 x458 lt))) 
                           (MS x458 b))) 
                   (forall ((x460 N)) 
                       (=> 
                           (exists ((x461 N)) 
                               (and 
                                   (= x461 p) 
                                   (MS0 x461 x460 rt))) 
                           (MS x460 b))) 
                   (not 
                       (= p t))) 
               (and 
                   (forall ((x462 N)) 
                       (=> 
                           (exists ((x463 N)) 
                               (and 
                                   (= x463 p) 
                                   (MS0 x463 x462 lt))) 
                           (MS x462 b))) 
                   (forall ((x464 N)) 
                       (=> 
                           (exists ((x465 N)) 
                               (and 
                                   (= x465 p) 
                                   (MS0 x465 x464 rt))) 
                           (MS x464 b))) 
                   (= p t)) 
               (= n ok))
         :named hyp102))
(assert (! (or 
               (not 
                   (forall ((x466 N)) 
                       (=> 
                           (exists ((x467 N)) 
                               (and 
                                   (= x467 p) 
                                   (MS0 x467 x466 lt))) 
                           (MS x466 b)))) 
               (and 
                   (forall ((x468 N)) 
                       (=> 
                           (exists ((x469 N)) 
                               (and 
                                   (= x469 p) 
                                   (MS0 x469 x468 lt))) 
                           (MS x468 b))) 
                   (not 
                       (forall ((x470 N)) 
                           (=> 
                               (exists ((x471 N)) 
                                   (and 
                                       (= x471 p) 
                                       (MS0 x471 x470 rt))) 
                               (MS x470 b))))) 
               (and 
                   (forall ((x472 N)) 
                       (=> 
                           (exists ((x473 N)) 
                               (and 
                                   (= x473 p) 
                                   (MS0 x473 x472 lt))) 
                           (MS x472 b))) 
                   (forall ((x474 N)) 
                       (=> 
                           (exists ((x475 N)) 
                               (and 
                                   (= x475 p) 
                                   (MS0 x475 x474 rt))) 
                           (MS x474 b))) 
                   (not 
                       (= p t)) 
                   (exists ((x476 N)) 
                       (and 
                           (MS0 p x476 f) 
                           (MS x476 lft)))) 
               (and 
                   (forall ((x477 N)) 
                       (=> 
                           (exists ((x478 N)) 
                               (and 
                                   (= x478 p) 
                                   (MS0 x478 x477 lt))) 
                           (MS x477 b))) 
                   (forall ((x479 N)) 
                       (=> 
                           (exists ((x480 N)) 
                               (and 
                                   (= x480 p) 
                                   (MS0 x480 x479 rt))) 
                           (MS x479 b))) 
                   (not 
                       (= p t)) 
                   (exists ((x481 N)) 
                       (and 
                           (MS0 p x481 f) 
                           (MS x481 rht)))) 
               (and 
                   (forall ((x482 N)) 
                       (=> 
                           (exists ((x483 N)) 
                               (and 
                                   (= x483 p) 
                                   (MS0 x483 x482 lt))) 
                           (MS x482 b))) 
                   (forall ((x484 N)) 
                       (=> 
                           (exists ((x485 N)) 
                               (and 
                                   (= x485 p) 
                                   (MS0 x485 x484 rt))) 
                           (MS x484 b))) 
                   (= p t)) 
               (= n ok))
         :named hyp103))
(assert (! (or 
               (not 
                   (forall ((x486 N)) 
                       (=> 
                           (exists ((x487 N)) 
                               (and 
                                   (= x487 p) 
                                   (MS0 x487 x486 lt))) 
                           (MS x486 b)))) 
               (and 
                   (forall ((x488 N)) 
                       (=> 
                           (exists ((x489 N)) 
                               (and 
                                   (= x489 p) 
                                   (MS0 x489 x488 lt))) 
                           (MS x488 b))) 
                   (not 
                       (forall ((x490 N)) 
                           (=> 
                               (exists ((x491 N)) 
                                   (and 
                                       (= x491 p) 
                                       (MS0 x491 x490 rt))) 
                               (MS x490 b))))) 
               (and 
                   (=> 
                       (and 
                           (forall ((x492 N)) 
                               (=> 
                                   (exists ((x493 N)) 
                                       (and 
                                           (= x493 p) 
                                           (MS0 x493 x492 lt))) 
                                   (MS x492 b))) 
                           (forall ((x494 N)) 
                               (=> 
                                   (exists ((x495 N)) 
                                       (and 
                                           (= x495 p) 
                                           (MS0 x495 x494 rt))) 
                                   (MS x494 b))) 
                           (not 
                               (= p t))) 
                       (and 
                           (exists ((x496 N)) 
                               (MS0 p x496 f)) 
                           (forall ((x497 N) (x498 N) (x499 N)) 
                               (=> 
                                   (and 
                                       (MS0 x497 x498 f) 
                                       (MS0 x497 x499 f)) 
                                   (= x498 x499))))) 
                   (or 
                       (and 
                           (forall ((x500 N)) 
                               (=> 
                                   (exists ((x501 N)) 
                                       (and 
                                           (= x501 p) 
                                           (MS0 x501 x500 lt))) 
                                   (MS x500 b))) 
                           (forall ((x502 N)) 
                               (=> 
                                   (exists ((x503 N)) 
                                       (and 
                                           (= x503 p) 
                                           (MS0 x503 x502 rt))) 
                                   (MS x502 b))) 
                           (not 
                               (= p t)) 
                           (exists ((x504 N)) 
                               (and 
                                   (MS0 p x504 f) 
                                   (MS x504 lft)))) 
                       (=> 
                           (and 
                               (forall ((x505 N)) 
                                   (=> 
                                       (exists ((x506 N)) 
                                           (and 
                                               (= x506 p) 
                                               (MS0 x506 x505 lt))) 
                                       (MS x505 b))) 
                               (forall ((x507 N)) 
                                   (=> 
                                       (exists ((x508 N)) 
                                           (and 
                                               (= x508 p) 
                                               (MS0 x508 x507 rt))) 
                                       (MS x507 b))) 
                               (not 
                                   (= p t))) 
                           (and 
                               (exists ((x509 N)) 
                                   (MS0 p x509 f)) 
                               (forall ((x510 N) (x511 N) (x512 N)) 
                                   (=> 
                                       (and 
                                           (MS0 x510 x511 f) 
                                           (MS0 x510 x512 f)) 
                                       (= x511 x512))))))))
         :named hyp104))
(assert (! (or 
               (not 
                   (forall ((x513 N)) 
                       (=> 
                           (exists ((x514 N)) 
                               (and 
                                   (= x514 p) 
                                   (MS0 x514 x513 ult))) 
                           (MS x513 b)))) 
               (and 
                   (forall ((x515 N)) 
                       (=> 
                           (exists ((x516 N)) 
                               (and 
                                   (= x516 p) 
                                   (MS0 x516 x515 ult))) 
                           (MS x515 b))) 
                   (not 
                       (forall ((x517 N)) 
                           (=> 
                               (exists ((x518 N)) 
                                   (and 
                                       (= x518 p) 
                                       (MS0 x518 x517 urt))) 
                               (MS x517 b))))) 
               (and 
                   (forall ((x519 N)) 
                       (=> 
                           (exists ((x520 N)) 
                               (and 
                                   (= x520 p) 
                                   (MS0 x520 x519 ult))) 
                           (MS x519 b))) 
                   (forall ((x521 N)) 
                       (=> 
                           (exists ((x522 N)) 
                               (and 
                                   (= x522 p) 
                                   (MS0 x522 x521 urt))) 
                           (MS x521 b))) 
                   (not 
                       (= p t)) 
                   (exists ((x523 N)) 
                       (and 
                           (MS0 p x523 f) 
                           (MS x523 lft)))) 
               (and 
                   (forall ((x524 N)) 
                       (=> 
                           (exists ((x525 N)) 
                               (and 
                                   (= x525 p) 
                                   (MS0 x525 x524 ult))) 
                           (MS x524 b))) 
                   (forall ((x526 N)) 
                       (=> 
                           (exists ((x527 N)) 
                               (and 
                                   (= x527 p) 
                                   (MS0 x527 x526 urt))) 
                           (MS x526 b))) 
                   (not 
                       (= p t)) 
                   (exists ((x528 N)) 
                       (and 
                           (MS0 p x528 f) 
                           (MS x528 rht)))) 
               (and 
                   (forall ((x529 N)) 
                       (=> 
                           (exists ((x530 N)) 
                               (and 
                                   (= x530 p) 
                                   (MS0 x530 x529 ult))) 
                           (MS x529 b))) 
                   (forall ((x531 N)) 
                       (=> 
                           (exists ((x532 N)) 
                               (and 
                                   (= x532 p) 
                                   (MS0 x532 x531 urt))) 
                           (MS x531 b))) 
                   (= p t)) 
               (= n ok))
         :named hyp105))
(assert (! (or 
               (not 
                   (forall ((x533 N)) 
                       (=> 
                           (exists ((x534 N)) 
                               (and 
                                   (= x534 p) 
                                   (MS0 x534 x533 ult))) 
                           (MS x533 b)))) 
               (and 
                   (forall ((x535 N)) 
                       (=> 
                           (exists ((x536 N)) 
                               (and 
                                   (= x536 p) 
                                   (MS0 x536 x535 ult))) 
                           (MS x535 b))) 
                   (not 
                       (forall ((x537 N)) 
                           (=> 
                               (exists ((x538 N)) 
                                   (and 
                                       (= x538 p) 
                                       (MS0 x538 x537 urt))) 
                               (MS x537 b))))) 
               (and 
                   (=> 
                       (and 
                           (forall ((x539 N)) 
                               (=> 
                                   (exists ((x540 N)) 
                                       (and 
                                           (= x540 p) 
                                           (MS0 x540 x539 ult))) 
                                   (MS x539 b))) 
                           (forall ((x541 N)) 
                               (=> 
                                   (exists ((x542 N)) 
                                       (and 
                                           (= x542 p) 
                                           (MS0 x542 x541 urt))) 
                                   (MS x541 b))) 
                           (not 
                               (= p t))) 
                       (and 
                           (exists ((x543 N)) 
                               (MS0 p x543 f)) 
                           (forall ((x544 N) (x545 N) (x546 N)) 
                               (=> 
                                   (and 
                                       (MS0 x544 x545 f) 
                                       (MS0 x544 x546 f)) 
                                   (= x545 x546))))) 
                   (or 
                       (and 
                           (forall ((x547 N)) 
                               (=> 
                                   (exists ((x548 N)) 
                                       (and 
                                           (= x548 p) 
                                           (MS0 x548 x547 ult))) 
                                   (MS x547 b))) 
                           (forall ((x549 N)) 
                               (=> 
                                   (exists ((x550 N)) 
                                       (and 
                                           (= x550 p) 
                                           (MS0 x550 x549 urt))) 
                                   (MS x549 b))) 
                           (not 
                               (= p t)) 
                           (exists ((x551 N)) 
                               (and 
                                   (MS0 p x551 f) 
                                   (MS x551 lft)))) 
                       (=> 
                           (and 
                               (forall ((x552 N)) 
                                   (=> 
                                       (exists ((x553 N)) 
                                           (and 
                                               (= x553 p) 
                                               (MS0 x553 x552 ult))) 
                                       (MS x552 b))) 
                               (forall ((x554 N)) 
                                   (=> 
                                       (exists ((x555 N)) 
                                           (and 
                                               (= x555 p) 
                                               (MS0 x555 x554 urt))) 
                                       (MS x554 b))) 
                               (not 
                                   (= p t))) 
                           (and 
                               (exists ((x556 N)) 
                                   (MS0 p x556 f)) 
                               (forall ((x557 N) (x558 N) (x559 N)) 
                                   (=> 
                                       (and 
                                           (MS0 x557 x558 f) 
                                           (MS0 x557 x559 f)) 
                                       (= x558 x559))))))))
         :named hyp106))
(assert (! (or 
               (not 
                   (forall ((x560 N)) 
                       (=> 
                           (exists ((x561 N)) 
                               (and 
                                   (= x561 p) 
                                   (MS0 x561 x560 vlt))) 
                           (MS x560 b)))) 
               (and 
                   (forall ((x562 N)) 
                       (=> 
                           (exists ((x563 N)) 
                               (and 
                                   (= x563 p) 
                                   (MS0 x563 x562 vlt))) 
                           (MS x562 b))) 
                   (not 
                       (forall ((x564 N)) 
                           (=> 
                               (exists ((x565 N)) 
                                   (and 
                                       (= x565 p) 
                                       (MS0 x565 x564 vrt))) 
                               (MS x564 b))))) 
               (and 
                   (forall ((x566 N)) 
                       (=> 
                           (exists ((x567 N)) 
                               (and 
                                   (= x567 p) 
                                   (MS0 x567 x566 vlt))) 
                           (MS x566 b))) 
                   (forall ((x568 N)) 
                       (=> 
                           (exists ((x569 N)) 
                               (and 
                                   (= x569 p) 
                                   (MS0 x569 x568 vrt))) 
                           (MS x568 b))) 
                   (not 
                       (= p t)) 
                   (exists ((x570 N)) 
                       (and 
                           (MS0 p x570 h) 
                           (MS x570 lft)))) 
               (and 
                   (forall ((x571 N)) 
                       (=> 
                           (exists ((x572 N)) 
                               (and 
                                   (= x572 p) 
                                   (MS0 x572 x571 vlt))) 
                           (MS x571 b))) 
                   (forall ((x573 N)) 
                       (=> 
                           (exists ((x574 N)) 
                               (and 
                                   (= x574 p) 
                                   (MS0 x574 x573 vrt))) 
                           (MS x573 b))) 
                   (not 
                       (= p t)) 
                   (exists ((x575 N)) 
                       (and 
                           (MS0 p x575 h) 
                           (MS x575 rht)))) 
               (and 
                   (forall ((x576 N)) 
                       (=> 
                           (exists ((x577 N)) 
                               (and 
                                   (= x577 p) 
                                   (MS0 x577 x576 vlt))) 
                           (MS x576 b))) 
                   (forall ((x578 N)) 
                       (=> 
                           (exists ((x579 N)) 
                               (and 
                                   (= x579 p) 
                                   (MS0 x579 x578 vrt))) 
                           (MS x578 b))) 
                   (= p t)) 
               (= n ok))
         :named hyp107))
(assert (! (or 
               (not 
                   (forall ((x580 N)) 
                       (=> 
                           (exists ((x581 N)) 
                               (and 
                                   (= x581 p) 
                                   (MS0 x581 x580 vlt))) 
                           (MS x580 b)))) 
               (and 
                   (forall ((x582 N)) 
                       (=> 
                           (exists ((x583 N)) 
                               (and 
                                   (= x583 p) 
                                   (MS0 x583 x582 vlt))) 
                           (MS x582 b))) 
                   (not 
                       (forall ((x584 N)) 
                           (=> 
                               (exists ((x585 N)) 
                                   (and 
                                       (= x585 p) 
                                       (MS0 x585 x584 vrt))) 
                               (MS x584 b))))) 
               (and 
                   (=> 
                       (and 
                           (forall ((x586 N)) 
                               (=> 
                                   (exists ((x587 N)) 
                                       (and 
                                           (= x587 p) 
                                           (MS0 x587 x586 vlt))) 
                                   (MS x586 b))) 
                           (forall ((x588 N)) 
                               (=> 
                                   (exists ((x589 N)) 
                                       (and 
                                           (= x589 p) 
                                           (MS0 x589 x588 vrt))) 
                                   (MS x588 b))) 
                           (not 
                               (= p t))) 
                       (and 
                           (exists ((x590 N)) 
                               (MS0 p x590 h)) 
                           (forall ((x591 N) (x592 N) (x593 N)) 
                               (=> 
                                   (and 
                                       (MS0 x591 x592 h) 
                                       (MS0 x591 x593 h)) 
                                   (= x592 x593))))) 
                   (or 
                       (and 
                           (forall ((x594 N)) 
                               (=> 
                                   (exists ((x595 N)) 
                                       (and 
                                           (= x595 p) 
                                           (MS0 x595 x594 vlt))) 
                                   (MS x594 b))) 
                           (forall ((x596 N)) 
                               (=> 
                                   (exists ((x597 N)) 
                                       (and 
                                           (= x597 p) 
                                           (MS0 x597 x596 vrt))) 
                                   (MS x596 b))) 
                           (not 
                               (= p t)) 
                           (exists ((x598 N)) 
                               (and 
                                   (MS0 p x598 h) 
                                   (MS x598 lft)))) 
                       (=> 
                           (and 
                               (forall ((x599 N)) 
                                   (=> 
                                       (exists ((x600 N)) 
                                           (and 
                                               (= x600 p) 
                                               (MS0 x600 x599 vlt))) 
                                       (MS x599 b))) 
                               (forall ((x601 N)) 
                                   (=> 
                                       (exists ((x602 N)) 
                                           (and 
                                               (= x602 p) 
                                               (MS0 x602 x601 vrt))) 
                                       (MS x601 b))) 
                               (not 
                                   (= p t))) 
                           (and 
                               (exists ((x603 N)) 
                                   (MS0 p x603 h)) 
                               (forall ((x604 N) (x605 N) (x606 N)) 
                                   (=> 
                                       (and 
                                           (MS0 x604 x605 h) 
                                           (MS0 x604 x606 h)) 
                                       (= x605 x606))))))))
         :named hyp108))
(assert (! (forall ((x607 N)) 
               (=> 
                   (and 
                       (exists ((x608 N)) 
                           (MS0 x607 x608 vrt)) 
                       (not 
                           (= x607 t))) 
                   (not 
                       (MS0 x607 nil wrt))))
         :named hyp109))
(assert (! (forall ((x609 N)) 
               (=> 
                   (and 
                       (exists ((x610 N)) 
                           (MS0 x609 x610 vlt)) 
                       (not 
                           (= x609 t))) 
                   (not 
                       (MS0 x609 nil wlt))))
         :named hyp110))
(assert (! (forall ((x611 N)) 
               (=> 
                   (not 
                       (MS0 x611 nil wlt)) 
                   (exists ((x612 N)) 
                       (MS0 x611 x612 vlt))))
         :named hyp111))
(assert (! (forall ((x613 N)) 
               (=> 
                   (not 
                       (MS0 x613 nil wrt)) 
                   (exists ((x614 N)) 
                       (MS0 x613 x614 vrt))))
         :named hyp112))
(assert (! (or 
               (and 
                   (not 
                       (forall ((x615 N)) 
                           (=> 
                               (exists ((x616 N)) 
                                   (and 
                                       (= x616 p) 
                                       (MS0 x616 x615 g))) 
                               (exists ((x617 CLR)) 
                                   (and 
                                       (= x617 black) 
                                       (clr x615 x617)))))) 
                   (exists ((y2 N)) 
                       (and 
                           (MS0 p y2 g) 
                           (not 
                               (exists ((x618 CLR)) 
                                   (and 
                                       (= x618 black) 
                                       (clr y2 x618))))))) 
               (and 
                   (forall ((x619 N)) 
                       (=> 
                           (exists ((x620 N)) 
                               (and 
                                   (= x620 p) 
                                   (MS0 x620 x619 g))) 
                           (exists ((x621 CLR)) 
                               (and 
                                   (= x621 black) 
                                   (clr x619 x621))))) 
                   (not 
                       (= p t))) 
               (and 
                   (forall ((x622 N)) 
                       (=> 
                           (exists ((x623 N)) 
                               (and 
                                   (= x623 p) 
                                   (MS0 x623 x622 g))) 
                           (exists ((x624 CLR)) 
                               (and 
                                   (= x624 black) 
                                   (clr x622 x624))))) 
                   (= p t)) 
               (= n ok))
         :named hyp113))
(assert (! (or 
               (not 
                   (forall ((x625 N)) 
                       (=> 
                           (exists ((x626 N)) 
                               (and 
                                   (= x626 p) 
                                   (MS0 x626 x625 lt))) 
                           (exists ((x627 CLR)) 
                               (and 
                                   (= x627 black) 
                                   (clr x625 x627)))))) 
               (and 
                   (forall ((x628 N)) 
                       (=> 
                           (exists ((x629 N)) 
                               (and 
                                   (= x629 p) 
                                   (MS0 x629 x628 lt))) 
                           (exists ((x630 CLR)) 
                               (and 
                                   (= x630 black) 
                                   (clr x628 x630))))) 
                   (not 
                       (forall ((x631 N)) 
                           (=> 
                               (exists ((x632 N)) 
                                   (and 
                                       (= x632 p) 
                                       (MS0 x632 x631 rt))) 
                               (exists ((x633 CLR)) 
                                   (and 
                                       (= x633 black) 
                                       (clr x631 x633))))))) 
               (and 
                   (forall ((x634 N)) 
                       (=> 
                           (exists ((x635 N)) 
                               (and 
                                   (= x635 p) 
                                   (MS0 x635 x634 lt))) 
                           (exists ((x636 CLR)) 
                               (and 
                                   (= x636 black) 
                                   (clr x634 x636))))) 
                   (forall ((x637 N)) 
                       (=> 
                           (exists ((x638 N)) 
                               (and 
                                   (= x638 p) 
                                   (MS0 x638 x637 rt))) 
                           (exists ((x639 CLR)) 
                               (and 
                                   (= x639 black) 
                                   (clr x637 x639))))) 
                   (not 
                       (= p t))) 
               (and 
                   (forall ((x640 N)) 
                       (=> 
                           (exists ((x641 N)) 
                               (and 
                                   (= x641 p) 
                                   (MS0 x641 x640 lt))) 
                           (exists ((x642 CLR)) 
                               (and 
                                   (= x642 black) 
                                   (clr x640 x642))))) 
                   (forall ((x643 N)) 
                       (=> 
                           (exists ((x644 N)) 
                               (and 
                                   (= x644 p) 
                                   (MS0 x644 x643 rt))) 
                           (exists ((x645 CLR)) 
                               (and 
                                   (= x645 black) 
                                   (clr x643 x645))))) 
                   (= p t)) 
               (= n ok))
         :named hyp114))
(assert (! (or 
               (not 
                   (forall ((x646 N)) 
                       (=> 
                           (exists ((x647 N)) 
                               (and 
                                   (= x647 p) 
                                   (MS0 x647 x646 lt))) 
                           (exists ((x648 CLR)) 
                               (and 
                                   (= x648 black) 
                                   (clr x646 x648)))))) 
               (and 
                   (forall ((x649 N)) 
                       (=> 
                           (exists ((x650 N)) 
                               (and 
                                   (= x650 p) 
                                   (MS0 x650 x649 lt))) 
                           (exists ((x651 CLR)) 
                               (and 
                                   (= x651 black) 
                                   (clr x649 x651))))) 
                   (not 
                       (forall ((x652 N)) 
                           (=> 
                               (exists ((x653 N)) 
                                   (and 
                                       (= x653 p) 
                                       (MS0 x653 x652 rt))) 
                               (exists ((x654 CLR)) 
                                   (and 
                                       (= x654 black) 
                                       (clr x652 x654))))))) 
               (and 
                   (forall ((x655 N)) 
                       (=> 
                           (exists ((x656 N)) 
                               (and 
                                   (= x656 p) 
                                   (MS0 x656 x655 lt))) 
                           (exists ((x657 CLR)) 
                               (and 
                                   (= x657 black) 
                                   (clr x655 x657))))) 
                   (forall ((x658 N)) 
                       (=> 
                           (exists ((x659 N)) 
                               (and 
                                   (= x659 p) 
                                   (MS0 x659 x658 rt))) 
                           (exists ((x660 CLR)) 
                               (and 
                                   (= x660 black) 
                                   (clr x658 x660))))) 
                   (not 
                       (= p t)) 
                   (exists ((x661 N)) 
                       (and 
                           (MS0 p x661 f) 
                           (MS x661 lft)))) 
               (and 
                   (forall ((x662 N)) 
                       (=> 
                           (exists ((x663 N)) 
                               (and 
                                   (= x663 p) 
                                   (MS0 x663 x662 lt))) 
                           (exists ((x664 CLR)) 
                               (and 
                                   (= x664 black) 
                                   (clr x662 x664))))) 
                   (forall ((x665 N)) 
                       (=> 
                           (exists ((x666 N)) 
                               (and 
                                   (= x666 p) 
                                   (MS0 x666 x665 rt))) 
                           (exists ((x667 CLR)) 
                               (and 
                                   (= x667 black) 
                                   (clr x665 x667))))) 
                   (not 
                       (= p t)) 
                   (exists ((x668 N)) 
                       (and 
                           (MS0 p x668 f) 
                           (MS x668 rht)))) 
               (and 
                   (forall ((x669 N)) 
                       (=> 
                           (exists ((x670 N)) 
                               (and 
                                   (= x670 p) 
                                   (MS0 x670 x669 lt))) 
                           (exists ((x671 CLR)) 
                               (and 
                                   (= x671 black) 
                                   (clr x669 x671))))) 
                   (forall ((x672 N)) 
                       (=> 
                           (exists ((x673 N)) 
                               (and 
                                   (= x673 p) 
                                   (MS0 x673 x672 rt))) 
                           (exists ((x674 CLR)) 
                               (and 
                                   (= x674 black) 
                                   (clr x672 x674))))) 
                   (= p t)) 
               (= n ok))
         :named hyp115))
(assert (! (or 
               (not 
                   (forall ((x675 N)) 
                       (=> 
                           (exists ((x676 N)) 
                               (and 
                                   (= x676 p) 
                                   (MS0 x676 x675 ult))) 
                           (exists ((x677 CLR)) 
                               (and 
                                   (= x677 black) 
                                   (clr x675 x677)))))) 
               (and 
                   (forall ((x678 N)) 
                       (=> 
                           (exists ((x679 N)) 
                               (and 
                                   (= x679 p) 
                                   (MS0 x679 x678 ult))) 
                           (exists ((x680 CLR)) 
                               (and 
                                   (= x680 black) 
                                   (clr x678 x680))))) 
                   (not 
                       (forall ((x681 N)) 
                           (=> 
                               (exists ((x682 N)) 
                                   (and 
                                       (= x682 p) 
                                       (MS0 x682 x681 urt))) 
                               (exists ((x683 CLR)) 
                                   (and 
                                       (= x683 black) 
                                       (clr x681 x683))))))) 
               (and 
                   (forall ((x684 N)) 
                       (=> 
                           (exists ((x685 N)) 
                               (and 
                                   (= x685 p) 
                                   (MS0 x685 x684 ult))) 
                           (exists ((x686 CLR)) 
                               (and 
                                   (= x686 black) 
                                   (clr x684 x686))))) 
                   (forall ((x687 N)) 
                       (=> 
                           (exists ((x688 N)) 
                               (and 
                                   (= x688 p) 
                                   (MS0 x688 x687 urt))) 
                           (exists ((x689 CLR)) 
                               (and 
                                   (= x689 black) 
                                   (clr x687 x689))))) 
                   (not 
                       (= p t)) 
                   (exists ((x690 N)) 
                       (and 
                           (MS0 p x690 f) 
                           (MS x690 lft)))) 
               (and 
                   (forall ((x691 N)) 
                       (=> 
                           (exists ((x692 N)) 
                               (and 
                                   (= x692 p) 
                                   (MS0 x692 x691 ult))) 
                           (exists ((x693 CLR)) 
                               (and 
                                   (= x693 black) 
                                   (clr x691 x693))))) 
                   (forall ((x694 N)) 
                       (=> 
                           (exists ((x695 N)) 
                               (and 
                                   (= x695 p) 
                                   (MS0 x695 x694 urt))) 
                           (exists ((x696 CLR)) 
                               (and 
                                   (= x696 black) 
                                   (clr x694 x696))))) 
                   (not 
                       (= p t)) 
                   (exists ((x697 N)) 
                       (and 
                           (MS0 p x697 f) 
                           (MS x697 rht)))) 
               (and 
                   (forall ((x698 N)) 
                       (=> 
                           (exists ((x699 N)) 
                               (and 
                                   (= x699 p) 
                                   (MS0 x699 x698 ult))) 
                           (exists ((x700 CLR)) 
                               (and 
                                   (= x700 black) 
                                   (clr x698 x700))))) 
                   (forall ((x701 N)) 
                       (=> 
                           (exists ((x702 N)) 
                               (and 
                                   (= x702 p) 
                                   (MS0 x702 x701 urt))) 
                           (exists ((x703 CLR)) 
                               (and 
                                   (= x703 black) 
                                   (clr x701 x703))))) 
                   (= p t)) 
               (= n ok))
         :named hyp116))
(assert (! (or 
               (not 
                   (forall ((x704 N)) 
                       (=> 
                           (exists ((x705 N)) 
                               (and 
                                   (= x705 p) 
                                   (MS0 x705 x704 vlt))) 
                           (exists ((x706 CLR)) 
                               (and 
                                   (= x706 black) 
                                   (clr x704 x706)))))) 
               (and 
                   (forall ((x707 N)) 
                       (=> 
                           (exists ((x708 N)) 
                               (and 
                                   (= x708 p) 
                                   (MS0 x708 x707 vlt))) 
                           (exists ((x709 CLR)) 
                               (and 
                                   (= x709 black) 
                                   (clr x707 x709))))) 
                   (not 
                       (forall ((x710 N)) 
                           (=> 
                               (exists ((x711 N)) 
                                   (and 
                                       (= x711 p) 
                                       (MS0 x711 x710 vrt))) 
                               (exists ((x712 CLR)) 
                                   (and 
                                       (= x712 black) 
                                       (clr x710 x712))))))) 
               (and 
                   (forall ((x713 N)) 
                       (=> 
                           (exists ((x714 N)) 
                               (and 
                                   (= x714 p) 
                                   (MS0 x714 x713 vlt))) 
                           (exists ((x715 CLR)) 
                               (and 
                                   (= x715 black) 
                                   (clr x713 x715))))) 
                   (forall ((x716 N)) 
                       (=> 
                           (exists ((x717 N)) 
                               (and 
                                   (= x717 p) 
                                   (MS0 x717 x716 vrt))) 
                           (exists ((x718 CLR)) 
                               (and 
                                   (= x718 black) 
                                   (clr x716 x718))))) 
                   (not 
                       (= p t)) 
                   (exists ((x719 N)) 
                       (and 
                           (MS0 p x719 h) 
                           (MS x719 lft)))) 
               (and 
                   (forall ((x720 N)) 
                       (=> 
                           (exists ((x721 N)) 
                               (and 
                                   (= x721 p) 
                                   (MS0 x721 x720 vlt))) 
                           (exists ((x722 CLR)) 
                               (and 
                                   (= x722 black) 
                                   (clr x720 x722))))) 
                   (forall ((x723 N)) 
                       (=> 
                           (exists ((x724 N)) 
                               (and 
                                   (= x724 p) 
                                   (MS0 x724 x723 vrt))) 
                           (exists ((x725 CLR)) 
                               (and 
                                   (= x725 black) 
                                   (clr x723 x725))))) 
                   (not 
                       (= p t)) 
                   (exists ((x726 N)) 
                       (and 
                           (MS0 p x726 h) 
                           (MS x726 rht)))) 
               (and 
                   (forall ((x727 N)) 
                       (=> 
                           (exists ((x728 N)) 
                               (and 
                                   (= x728 p) 
                                   (MS0 x728 x727 vlt))) 
                           (exists ((x729 CLR)) 
                               (and 
                                   (= x729 black) 
                                   (clr x727 x729))))) 
                   (forall ((x730 N)) 
                       (=> 
                           (exists ((x731 N)) 
                               (and 
                                   (= x731 p) 
                                   (MS0 x731 x730 vrt))) 
                           (exists ((x732 CLR)) 
                               (and 
                                   (= x732 black) 
                                   (clr x730 x732))))) 
                   (= p t)) 
               (= n ok))
         :named hyp117))
(assert (! (not 
               (exists ((x733 N)) 
                   (and 
                       (MS0 p x733 wrt) 
                       (MS x733 b))))
         :named hyp118))
(assert (! (or 
               (and 
                   (not 
                       (MS0 p nil wlt)) 
                   (not 
                       (exists ((x734 N)) 
                           (and 
                               (MS0 p x734 wlt) 
                               (MS x734 b))))) 
               (=> 
                   (not 
                       (MS0 p nil wlt)) 
                   (exists ((x735 N)) 
                       (and 
                           (MS0 p x735 wlt) 
                           (MS x735 b)))) 
               (= n ok))
         :named hyp119))
(assert (! (or 
               (and 
                   (not 
                       (MS0 p nil wlt)) 
                   (not 
                       (exists ((x736 CLR)) 
                           (and 
                               (= x736 black) 
                               (exists ((x737 N)) 
                                   (and 
                                       (MS0 p x737 wlt) 
                                       (clr x737 x736))))))) 
               (=> 
                   (not 
                       (MS0 p nil wlt)) 
                   (exists ((x738 CLR)) 
                       (and 
                           (= x738 black) 
                           (exists ((x739 N)) 
                               (and 
                                   (MS0 p x739 wlt) 
                                   (clr x739 x738)))))) 
               (= n ok))
         :named hyp120))
(assert (! (not 
               (forall ((x740 N)) 
                   (= 
                       (or 
                           (exists ((x741 CLR)) 
                               (and 
                                   (= x741 black) 
                                   (clr x740 x741))) 
                           (MS0 p x740 wrt)) 
                       (exists ((x742 CLR)) 
                           (and 
                               (= x742 black) 
                               (or 
                                   (and 
                                       (clr x740 x742) 
                                       (not 
                                           (exists ((x743 CLR)) 
                                               (and 
                                                   (MS0 p x740 wrt) 
                                                   (= x743 black))))) 
                                   (and 
                                       (MS0 p x740 wrt) 
                                       (= x742 black))))))))
         :named goal))
(check-sat)
(exit)

