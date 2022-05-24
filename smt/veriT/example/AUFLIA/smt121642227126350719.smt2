(set-info :smt-lib-version 2.6)
(set-logic AUFLIA)
(set-info :source |Generator: Rodin SMT Plug-in|)
(set-info :license "https://creativecommons.org/licenses/by-nc/4.0/")
(set-info :category "industrial")
(set-info :status unsat)

(declare-sort K 0)
(declare-sort N 0)
(declare-sort PN 0)
(declare-sort PNN 0)
(declare-sort PNZ 0)
(declare-fun MS (N PN) Bool)
(declare-fun MS0 (N N PNN) Bool)
(declare-fun MS1 (N Int PNZ) Bool)
(declare-fun b () PN)
(declare-fun c () PNN)
(declare-fun f () PNN)
(declare-fun g () PNN)
(declare-fun ko () K)
(declare-fun lft () PN)
(declare-fun lt () PNN)
(declare-fun n () K)
(declare-fun nil () N)
(declare-fun ok () K)
(declare-fun p () N)
(declare-fun rht () PN)
(declare-fun rt () PNN)
(declare-fun t () N)

; Elementary Sets axiom (Singleton part)
(assert (forall ((x117 N) (x118 N)) 
            (exists ((X PNN)) 
                (and 
                    (MS0 x117 x118 X) 
                    (forall ((y2 N) (y3 N)) 
                        (=> 
                            (MS0 y2 y3 X) 
                            (and 
                                (= y2 x117) 
                                (= y3 x118))))))))
; Elementary Sets axiom (Singleton part)
(assert (forall ((x119 N) (x120 Int)) 
            (exists ((X0 PNZ)) 
                (and 
                    (MS1 x119 x120 X0) 
                    (forall ((y4 N) (y5 Int)) 
                        (=> 
                            (MS1 y4 y5 X0) 
                            (and 
                                (= y4 x119) 
                                (= y5 x120))))))))
; Elementary Sets axiom (Singleton part)
(assert (forall ((x121 N)) 
            (exists ((X1 PN)) 
                (and 
                    (MS x121 X1) 
                    (forall ((y6 N)) 
                        (=> 
                            (MS y6 X1) 
                            (= y6 x121)))))))
(assert (! (forall ((x N)) 
               (= 
                   (or 
                       (MS x lft) 
                       (MS x rht)) 
                   (exists ((x0 N)) 
                       (MS0 x0 x f))))
         :named hyp1))
(assert (! (= n ko)
         :named hyp2))
(assert (! (forall ((x1 N)) 
               (=> 
                   (exists ((x2 N)) 
                       (and 
                           (= x2 p) 
                           (MS0 x2 x1 lt))) 
                   (MS x1 b)))
         :named hyp3))
(assert (! (=> 
               (exists ((x3 N)) 
                   (MS0 p x3 lt)) 
               (exists ((x4 N)) 
                   (and 
                       (MS0 p x4 lt) 
                       (MS x4 b))))
         :named hyp4))
(assert (! (forall ((x5 N) (x6 N)) 
               (=> 
                   (and 
                       (MS0 x6 x5 f) 
                       (MS x5 lft)) 
                   (MS0 x5 x6 lt)))
         :named hyp5))
(assert (! (forall ((x7 N) (x8 N)) 
               (=> 
                   (and 
                       (MS0 x8 x7 f) 
                       (MS x7 rht)) 
                   (MS0 x7 x8 rt)))
         :named hyp6))
(assert (! (forall ((x9 K)) 
               (or 
                   (= x9 ok) 
                   (= x9 ko)))
         :named hyp7))
(assert (! (not 
               (= ok ko))
         :named hyp8))
(assert (! (not 
               (forall ((x10 N)) 
                   (=> 
                       (exists ((x11 N)) 
                           (and 
                               (= x11 p) 
                               (MS0 x11 x10 rt))) 
                       (MS x10 b))))
         :named hyp9))
(assert (! (or 
               (and 
                   (not 
                       (forall ((x12 N)) 
                           (=> 
                               (exists ((x13 N)) 
                                   (and 
                                       (= x13 p) 
                                       (MS0 x13 x12 g))) 
                               (MS x12 b)))) 
                   (exists ((y N)) 
                       (and 
                           (MS0 p y g) 
                           (not 
                               (MS y b))))) 
               (and 
                   (forall ((x14 N)) 
                       (=> 
                           (exists ((x15 N)) 
                               (and 
                                   (= x15 p) 
                                   (MS0 x15 x14 g))) 
                           (MS x14 b))) 
                   (not 
                       (= p t))) 
               (and 
                   (forall ((x16 N)) 
                       (=> 
                           (exists ((x17 N)) 
                               (and 
                                   (= x17 p) 
                                   (MS0 x17 x16 g))) 
                           (MS x16 b))) 
                   (= p t)))
         :named hyp10))
(assert (! (forall ((a Int)) 
               (exists ((b0 Int) (f0 PNZ)) 
                   (and 
                       (forall ((x18 N) (x19 Int)) 
                           (=> 
                               (MS1 x18 x19 f0) 
                               (and 
                                   (<= a x19) 
                                   (<= x19 b0)))) 
                       (forall ((x20 N) (x21 Int) (x22 Int)) 
                           (=> 
                               (and 
                                   (MS1 x20 x21 f0) 
                                   (MS1 x20 x22 f0)) 
                               (= x21 x22))) 
                       (forall ((x23 N)) 
                           (exists ((x24 Int)) 
                               (MS1 x23 x24 f0))) 
                       (forall ((x25 Int) (x26 N) (x27 N)) 
                           (=> 
                               (and 
                                   (MS1 x26 x25 f0) 
                                   (MS1 x27 x25 f0)) 
                               (= x26 x27))))))
         :named hyp11))
(assert (! (forall ((x28 N) (x29 N)) 
               (=> 
                   (= x28 x29) 
                   (MS0 x28 x29 c)))
         :named hyp12))
(assert (! (forall ((x30 N) (x31 N)) 
               (=> 
                   (exists ((x32 N)) 
                       (and 
                           (MS0 x30 x32 c) 
                           (MS0 x32 x31 g))) 
                   (MS0 x30 x31 c)))
         :named hyp13))
(assert (! (forall ((r PNN)) 
               (=> 
                   (and 
                       (forall ((x33 N) (x34 N)) 
                           (=> 
                               (= x33 x34) 
                               (MS0 x33 x34 r))) 
                       (forall ((x35 N) (x36 N)) 
                           (=> 
                               (exists ((x37 N)) 
                                   (and 
                                       (MS0 x35 x37 r) 
                                       (MS0 x37 x36 g))) 
                               (MS0 x35 x36 r)))) 
                   (forall ((x38 N) (x39 N)) 
                       (=> 
                           (MS0 x38 x39 c) 
                           (MS0 x38 x39 r)))))
         :named hyp14))
(assert (! (forall ((x40 N) (x41 N) (x42 N)) 
               (=> 
                   (and 
                       (MS0 x40 x41 lt) 
                       (MS0 x40 x42 lt)) 
                   (= x41 x42)))
         :named hyp15))
(assert (! (forall ((x43 N) (x44 N) (x45 N)) 
               (=> 
                   (and 
                       (MS0 x43 x44 rt) 
                       (MS0 x43 x45 rt)) 
                   (= x44 x45)))
         :named hyp16))
(assert (! (forall ((x46 N) (x47 N)) 
               (= 
                   (MS0 x46 x47 g) 
                   (or 
                       (MS0 x46 x47 lt) 
                       (MS0 x46 x47 rt))))
         :named hyp17))
(assert (! (MS t b)
         :named hyp18))
(assert (! (=> 
               (forall ((x48 N)) 
                   (=> 
                       (exists ((x49 N)) 
                           (and 
                               (MS x49 b) 
                               (MS0 x49 x48 g))) 
                       (MS x48 b))) 
               (forall ((x50 N)) 
                   (=> 
                       (exists ((x51 N)) 
                           (and 
                               (MS x51 b) 
                               (MS0 x51 x50 c))) 
                       (MS x50 b))))
         :named hyp19))
(assert (! (forall ((x52 N)) 
               (=> 
                   (MS x52 b) 
                   (exists ((x53 N)) 
                       (and 
                           (= x53 t) 
                           (MS0 x53 x52 c)))))
         :named hyp20))
(assert (! (MS p b)
         :named hyp21))
(assert (! (and 
               (forall ((x54 N) (x55 N)) 
                   (=> 
                       (MS0 x54 x55 f) 
                       (and 
                           (MS x54 b) 
                           (not 
                               (= x54 t)) 
                           (MS x55 b) 
                           (not 
                               (= x55 p))))) 
               (forall ((x56 N) (x57 N) (x58 N)) 
                   (=> 
                       (and 
                           (MS0 x56 x57 f) 
                           (MS0 x56 x58 f)) 
                       (= x57 x58))) 
               (forall ((x59 N) (x60 N) (x61 N)) 
                   (=> 
                       (and 
                           (MS0 x60 x59 f) 
                           (MS0 x61 x59 f)) 
                       (= x60 x61))))
         :named hyp22))
(assert (! (forall ((x62 N)) 
               (= 
                   (or 
                       (exists ((x63 N)) 
                           (MS0 x62 x63 f)) 
                       (= x62 t)) 
                   (or 
                       (exists ((x64 N)) 
                           (MS0 x64 x62 f)) 
                       (= x62 p))))
         :named hyp23))
(assert (! (forall ((s PN)) 
               (=> 
                   (and 
                       (forall ((x65 N)) 
                           (=> 
                               (MS x65 s) 
                               (or 
                                   (exists ((x66 N)) 
                                       (MS0 x65 x66 f)) 
                                   (= x65 t)))) 
                       (forall ((x67 N)) 
                           (=> 
                               (MS x67 s) 
                               (exists ((x68 N)) 
                                   (and 
                                       (MS x68 s) 
                                       (MS0 x67 x68 f)))))) 
                   (forall ((x69 N)) 
                       (not 
                           (MS x69 s)))))
         :named hyp24))
(assert (! (forall ((x70 N) (x71 N)) 
               (=> 
                   (MS0 x71 x70 f) 
                   (MS0 x70 x71 g)))
         :named hyp25))
(assert (! (forall ((x72 N)) 
               (=> 
                   (exists ((x73 N)) 
                       (and 
                           (MS x73 b) 
                           (not 
                               (or 
                                   (exists ((x74 N)) 
                                       (MS0 x73 x74 f)) 
                                   (= x73 t))) 
                           (MS0 x73 x72 g))) 
                   (MS x72 b)))
         :named hyp26))
(assert (! (=> 
               (= n ok) 
               (forall ((x75 N)) 
                   (=> 
                       (exists ((x76 N)) 
                           (and 
                               (MS x76 b) 
                               (MS0 x76 x75 g))) 
                       (MS x75 b))))
         :named hyp27))
(assert (! (=> 
               (= n ok) 
               (= p t))
         :named hyp28))
(assert (! (=> 
               (= p t) 
               (forall ((x77 N) (x78 N)) 
                   (not 
                       (MS0 x77 x78 f))))
         :named hyp29))
(assert (! (=> 
               (forall ((x79 N) (x80 N)) 
                   (not 
                       (MS0 x79 x80 f))) 
               (= p t))
         :named hyp30))
(assert (! (forall ((x81 N)) 
               (not 
                   (and 
                       (MS x81 lft) 
                       (MS x81 rht))))
         :named hyp31))
(assert (! (=> 
               (forall ((x82 N) (x83 N)) 
                   (not 
                       (MS0 x82 x83 f))) 
               (and 
                   (forall ((x84 N)) 
                       (not 
                           (MS x84 lft))) 
                   (forall ((x85 N)) 
                       (not 
                           (MS x85 rht)))))
         :named hyp32))
(assert (! (=> 
               (= n ok) 
               (forall ((x86 N) (x87 N)) 
                   (not 
                       (MS0 x86 x87 f))))
         :named hyp33))
(assert (! (=> 
               (= n ok) 
               (and 
                   (forall ((x88 N)) 
                       (not 
                           (MS x88 lft))) 
                   (forall ((x89 N)) 
                       (not 
                           (MS x89 rht)))))
         :named hyp34))
(assert (! (exists ((x90 N)) 
               (MS0 p x90 rt))
         :named hyp35))
(assert (! (not 
               (or 
                   (exists ((x91 N)) 
                       (MS0 nil x91 lt)) 
                   (exists ((x92 N)) 
                       (MS0 nil x92 rt))))
         :named hyp36))
(assert (! (not 
               (or 
                   (exists ((x93 N)) 
                       (MS0 x93 nil lt)) 
                   (exists ((x94 N)) 
                       (MS0 x94 nil rt))))
         :named hyp37))
(assert (! (or 
               (forall ((x95 N)) 
                   (=> 
                       (exists ((x96 N)) 
                           (and 
                               (MS x96 b) 
                               (MS0 x96 x95 g))) 
                       (MS x95 b))) 
               (and 
                   (not 
                       (forall ((x97 N)) 
                           (=> 
                               (exists ((x98 N)) 
                                   (and 
                                       (MS x98 b) 
                                       (MS0 x98 x97 g))) 
                               (MS x97 b)))) 
                   (exists ((x99 N) (y0 N)) 
                       (and 
                           (MS0 x99 y0 g) 
                           (MS x99 b) 
                           (not 
                               (MS y0 b))))))
         :named hyp38))
(assert (! (=> 
               (not 
                   (= p t)) 
               (exists ((x100 N)) 
                   (MS0 p x100 f)))
         :named hyp39))
(assert (! (=> 
               (and 
                   (not 
                       (= p t)) 
                   (MS0 p t f)) 
               (forall ((x101 N) (x102 N)) 
                   (= 
                       (MS0 x101 x102 f) 
                       (and 
                           (= x101 p) 
                           (= x102 t)))))
         :named hyp40))
(assert (! (=> 
               (not 
                   (= p t)) 
               (and 
                   (exists ((x103 N)) 
                       (MS0 p x103 f)) 
                   (forall ((x104 N) (x105 N) (x106 N)) 
                       (=> 
                           (and 
                               (MS0 x104 x105 f) 
                               (MS0 x104 x106 f)) 
                           (= x105 x106)))))
         :named hyp41))
(assert (! (not 
               (MS p lft))
         :named hyp42))
(assert (! (not 
               (MS p rht))
         :named hyp43))
(assert (! (or 
               (and 
                   (not 
                       (forall ((x107 N)) 
                           (=> 
                               (exists ((x108 N)) 
                                   (and 
                                       (= x108 p) 
                                       (MS0 x108 x107 g))) 
                               (MS x107 b)))) 
                   (exists ((y1 N)) 
                       (and 
                           (MS0 p y1 g) 
                           (not 
                               (MS y1 b))))) 
               (and 
                   (forall ((x109 N)) 
                       (=> 
                           (exists ((x110 N)) 
                               (and 
                                   (= x110 p) 
                                   (MS0 x110 x109 g))) 
                           (MS x109 b))) 
                   (not 
                       (= p t))) 
               (and 
                   (forall ((x111 N)) 
                       (=> 
                           (exists ((x112 N)) 
                               (and 
                                   (= x112 p) 
                                   (MS0 x112 x111 g))) 
                           (MS x111 b))) 
                   (= p t)) 
               (= n ok))
         :named hyp44))
(assert (! (not 
               (forall ((x113 N)) 
                   (= 
                       (or 
                           (MS x113 lft) 
                           (MS x113 rht) 
                           (= x113 p)) 
                       (or 
                           (exists ((x114 N)) 
                               (and 
                                   (MS0 x114 x113 f) 
                                   (not 
                                       (exists ((x115 N)) 
                                           (and 
                                               (MS0 p x114 rt) 
                                               (= x115 p)))))) 
                           (exists ((x116 N)) 
                               (and 
                                   (MS0 p x116 rt) 
                                   (= x113 p)))))))
         :named goal))
(check-sat)
(exit)

