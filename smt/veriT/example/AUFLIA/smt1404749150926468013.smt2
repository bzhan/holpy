(set-info :smt-lib-version 2.6)
(set-logic AUFLIA)
(set-info :source |Generator: Rodin SMT Plug-in|)
(set-info :license "https://creativecommons.org/licenses/by-nc/4.0/")
(set-info :category "industrial")
(set-info :status unsat)

(declare-sort N 0)
(declare-sort PN 0)
(declare-sort PNZ 0)
(declare-fun MS (N Int PNZ) Bool)
(declare-fun MS0 (N PN) Bool)
(declare-fun f0 (N N) Bool)
(declare-fun n () PN)
(declare-fun o () PNZ)
(declare-fun p () N)
(declare-fun s () PN)
(declare-fun t () N)
(declare-fun x () N)

; Elementary Sets axiom (Singleton part)
(assert (forall ((x125 N) (x126 Int)) 
            (exists ((X PNZ)) 
                (and 
                    (MS x125 x126 X) 
                    (forall ((y N) (y0 Int)) 
                        (=> 
                            (MS y y0 X) 
                            (and 
                                (= y x125) 
                                (= y0 x126))))))))
; Elementary Sets axiom (Singleton part)
(assert (forall ((x127 N)) 
            (exists ((X0 PN)) 
                (and 
                    (MS0 x127 X0) 
                    (forall ((y1 N)) 
                        (=> 
                            (MS0 y1 X0) 
                            (= y1 x127)))))))
(assert (! (forall ((a Int)) 
               (exists ((b Int) (f PNZ)) 
                   (and 
                       (forall ((x0 N) (x1 Int)) 
                           (=> 
                               (MS x0 x1 f) 
                               (and 
                                   (MS0 x0 n) 
                                   (<= a x1) 
                                   (<= x1 b)))) 
                       (forall ((x2 N) (x3 Int) (x4 Int)) 
                           (=> 
                               (and 
                                   (MS x2 x3 f) 
                                   (MS x2 x4 f)) 
                               (= x3 x4))) 
                       (forall ((x5 N)) 
                           (=> 
                               (MS0 x5 n) 
                               (exists ((x6 Int)) 
                                   (MS x5 x6 f)))) 
                       (forall ((x7 Int) (x8 N) (x9 N)) 
                           (=> 
                               (and 
                                   (MS x8 x7 f) 
                                   (MS x9 x7 f)) 
                               (= x8 x9))))))
         :named hyp1))
(assert (! (MS0 p n)
         :named hyp2))
(assert (! (MS0 t n)
         :named hyp3))
(assert (! (and 
               (forall ((x10 N) (x11 N)) 
                   (=> 
                       (f0 x10 x11) 
                       (and 
                           (MS0 x10 n) 
                           (not 
                               (= x10 t)) 
                           (MS0 x11 n) 
                           (not 
                               (= x11 p))))) 
               (forall ((x12 N) (x13 N) (x14 N)) 
                   (=> 
                       (and 
                           (f0 x12 x13) 
                           (f0 x12 x14)) 
                       (= x13 x14))) 
               (forall ((x15 N)) 
                   (=> 
                       (and 
                           (MS0 x15 n) 
                           (not 
                               (= x15 t))) 
                       (exists ((x16 N)) 
                           (f0 x15 x16)))) 
               (forall ((x17 N)) 
                   (=> 
                       (and 
                           (MS0 x17 n) 
                           (not 
                               (= x17 p))) 
                       (exists ((x18 N)) 
                           (f0 x18 x17)))) 
               (forall ((x19 N) (x20 N) (x21 N)) 
                   (=> 
                       (and 
                           (f0 x20 x19) 
                           (f0 x21 x19)) 
                       (= x20 x21))))
         :named hyp4))
(assert (! (forall ((s0 PN)) 
               (=> 
                   (and 
                       (forall ((x22 N)) 
                           (=> 
                               (MS0 x22 s0) 
                               (MS0 x22 n))) 
                       (forall ((x23 N)) 
                           (=> 
                               (MS0 x23 s0) 
                               (exists ((x24 N)) 
                                   (and 
                                       (MS0 x24 s0) 
                                       (f0 x24 x23)))))) 
                   (forall ((x25 N)) 
                       (not 
                           (MS0 x25 s0)))))
         :named hyp5))
(assert (! (and 
               (forall ((x26 N) (x27 Int)) 
                   (=> 
                       (MS x26 x27 o) 
                       (and 
                           (MS0 x26 n) 
                           (<= 1 x27) 
                           (forall ((x28 Int)) 
                               (=> 
                                   (and 
                                       (<= 0 x28) 
                                       (exists ((f1 PNZ)) 
                                           (and 
                                               (forall ((x29 N) (x30 Int)) 
                                                   (=> 
                                                       (MS x29 x30 f1) 
                                                       (and 
                                                           (MS0 x29 n) 
                                                           (<= 1 x30) 
                                                           (<= x30 x28)))) 
                                               (forall ((x31 N) (x32 Int) (x33 Int)) 
                                                   (=> 
                                                       (and 
                                                           (MS x31 x32 f1) 
                                                           (MS x31 x33 f1)) 
                                                       (= x32 x33))) 
                                               (forall ((x34 N)) 
                                                   (=> 
                                                       (MS0 x34 n) 
                                                       (exists ((x35 Int)) 
                                                           (MS x34 x35 f1)))) 
                                               (forall ((x36 Int)) 
                                                   (=> 
                                                       (and 
                                                           (<= 1 x36) 
                                                           (<= x36 x28)) 
                                                       (exists ((x37 N)) 
                                                           (MS x37 x36 f1)))) 
                                               (forall ((x38 Int) (x39 N) (x40 N)) 
                                                   (=> 
                                                       (and 
                                                           (MS x39 x38 f1) 
                                                           (MS x40 x38 f1)) 
                                                       (= x39 x40)))))) 
                                   (<= x27 x28)))))) 
               (forall ((x41 N) (x42 Int) (x43 Int)) 
                   (=> 
                       (and 
                           (MS x41 x42 o) 
                           (MS x41 x43 o)) 
                       (= x42 x43))) 
               (forall ((x44 N)) 
                   (=> 
                       (MS0 x44 n) 
                       (exists ((x45 Int)) 
                           (MS x44 x45 o)))) 
               (forall ((x46 Int)) 
                   (=> 
                       (and 
                           (<= 1 x46) 
                           (forall ((x47 Int)) 
                               (=> 
                                   (and 
                                       (<= 0 x47) 
                                       (exists ((f2 PNZ)) 
                                           (and 
                                               (forall ((x48 N) (x49 Int)) 
                                                   (=> 
                                                       (MS x48 x49 f2) 
                                                       (and 
                                                           (MS0 x48 n) 
                                                           (<= 1 x49) 
                                                           (<= x49 x47)))) 
                                               (forall ((x50 N) (x51 Int) (x52 Int)) 
                                                   (=> 
                                                       (and 
                                                           (MS x50 x51 f2) 
                                                           (MS x50 x52 f2)) 
                                                       (= x51 x52))) 
                                               (forall ((x53 N)) 
                                                   (=> 
                                                       (MS0 x53 n) 
                                                       (exists ((x54 Int)) 
                                                           (MS x53 x54 f2)))) 
                                               (forall ((x55 Int)) 
                                                   (=> 
                                                       (and 
                                                           (<= 1 x55) 
                                                           (<= x55 x47)) 
                                                       (exists ((x56 N)) 
                                                           (MS x56 x55 f2)))) 
                                               (forall ((x57 Int) (x58 N) (x59 N)) 
                                                   (=> 
                                                       (and 
                                                           (MS x58 x57 f2) 
                                                           (MS x59 x57 f2)) 
                                                       (= x58 x59)))))) 
                                   (<= x46 x47)))) 
                       (exists ((x60 N)) 
                           (MS x60 x46 o)))) 
               (forall ((x61 Int) (x62 N) (x63 N)) 
                   (=> 
                       (and 
                           (MS x62 x61 o) 
                           (MS x63 x61 o)) 
                       (= x62 x63))))
         :named hyp6))
(assert (! (exists ((x64 Int)) 
               (and 
                   (= x64 1) 
                   (MS p x64 o)))
         :named hyp7))
(assert (! (exists ((x65 Int)) 
               (and 
                   (<= 0 x65) 
                   (exists ((f3 PNZ)) 
                       (and 
                           (forall ((x66 N) (x67 Int)) 
                               (=> 
                                   (MS x66 x67 f3) 
                                   (and 
                                       (MS0 x66 n) 
                                       (<= 1 x67) 
                                       (<= x67 x65)))) 
                           (forall ((x68 N) (x69 Int) (x70 Int)) 
                               (=> 
                                   (and 
                                       (MS x68 x69 f3) 
                                       (MS x68 x70 f3)) 
                                   (= x69 x70))) 
                           (forall ((x71 N)) 
                               (=> 
                                   (MS0 x71 n) 
                                   (exists ((x72 Int)) 
                                       (MS x71 x72 f3)))) 
                           (forall ((x73 Int)) 
                               (=> 
                                   (and 
                                       (<= 1 x73) 
                                       (<= x73 x65)) 
                                   (exists ((x74 N)) 
                                       (MS x74 x73 f3)))) 
                           (forall ((x75 Int) (x76 N) (x77 N)) 
                               (=> 
                                   (and 
                                       (MS x76 x75 f3) 
                                       (MS x77 x75 f3)) 
                                   (= x76 x77))))) 
                   (MS t x65 o)))
         :named hyp8))
(assert (! (forall ((q PN)) 
               (=> 
                   (and 
                       (forall ((x78 N)) 
                           (=> 
                               (MS0 x78 q) 
                               (MS0 x78 n))) 
                       (forall ((z N)) 
                           (=> 
                               (and 
                                   (MS0 z n) 
                                   (forall ((x79 N)) 
                                       (=> 
                                           (exists ((x80 N)) 
                                               (and 
                                                   (= x80 z) 
                                                   (f0 x79 x80))) 
                                           (MS0 x79 q)))) 
                               (MS0 z q)))) 
                   (forall ((x81 N)) 
                       (=> 
                           (MS0 x81 n) 
                           (MS0 x81 q)))))
         :named hyp9))
(assert (! (not 
               (= p t))
         :named hyp10))
(assert (! (forall ((x82 N)) 
               (=> 
                   (and 
                       (MS0 x82 n) 
                       (not 
                           (= x82 t))) 
                   (exists ((x83 N) (x84 Int)) 
                       (and 
                           (f0 x82 x83) 
                           (forall ((x85 Int)) 
                               (=> 
                                   (MS x82 x85 o) 
                                   (= x84 (+ x85 1)))) 
                           (MS x83 x84 o)))))
         :named hyp11))
(assert (! (forall ((x86 N)) 
               (=> 
                   (and 
                       (MS0 x86 n) 
                       (not 
                           (= x86 t)) 
                       (not 
                           (f0 x86 t))) 
                   (and 
                       (forall ((x87 N) (x88 N)) 
                           (=> 
                               (or 
                                   (and 
                                       (f0 x87 x88) 
                                       (not 
                                           (f0 x86 x87)) 
                                       (not 
                                           (exists ((x89 N)) 
                                               (and 
                                                   (= x87 x86) 
                                                   (exists ((x90 N)) 
                                                       (and 
                                                           (f0 x86 x90) 
                                                           (f0 x90 x89))))))) 
                                   (and 
                                       (= x87 x86) 
                                       (exists ((x91 N)) 
                                           (and 
                                               (f0 x86 x91) 
                                               (f0 x91 x88))))) 
                               (and 
                                   (MS0 x87 n) 
                                   (not 
                                       (f0 x86 x87)) 
                                   (not 
                                       (= x87 t)) 
                                   (MS0 x88 n) 
                                   (not 
                                       (f0 x86 x88)) 
                                   (not 
                                       (= x88 p))))) 
                       (forall ((x92 N) (x93 N) (x94 N)) 
                           (=> 
                               (and 
                                   (or 
                                       (and 
                                           (f0 x92 x93) 
                                           (not 
                                               (f0 x86 x92)) 
                                           (not 
                                               (exists ((x95 N)) 
                                                   (and 
                                                       (= x92 x86) 
                                                       (exists ((x96 N)) 
                                                           (and 
                                                               (f0 x86 x96) 
                                                               (f0 x96 x95))))))) 
                                       (and 
                                           (= x92 x86) 
                                           (exists ((x97 N)) 
                                               (and 
                                                   (f0 x86 x97) 
                                                   (f0 x97 x93))))) 
                                   (or 
                                       (and 
                                           (f0 x92 x94) 
                                           (not 
                                               (f0 x86 x92)) 
                                           (not 
                                               (exists ((x98 N)) 
                                                   (and 
                                                       (= x92 x86) 
                                                       (exists ((x99 N)) 
                                                           (and 
                                                               (f0 x86 x99) 
                                                               (f0 x99 x98))))))) 
                                       (and 
                                           (= x92 x86) 
                                           (exists ((x100 N)) 
                                               (and 
                                                   (f0 x86 x100) 
                                                   (f0 x100 x94)))))) 
                               (= x93 x94))) 
                       (forall ((x101 N)) 
                           (=> 
                               (and 
                                   (MS0 x101 n) 
                                   (not 
                                       (f0 x86 x101)) 
                                   (not 
                                       (= x101 t))) 
                               (or 
                                   (exists ((x102 N)) 
                                       (and 
                                           (f0 x101 x102) 
                                           (not 
                                               (f0 x86 x101)) 
                                           (not 
                                               (exists ((x103 N)) 
                                                   (and 
                                                       (= x101 x86) 
                                                       (exists ((x104 N)) 
                                                           (and 
                                                               (f0 x86 x104) 
                                                               (f0 x104 x103)))))))) 
                                   (exists ((x105 N)) 
                                       (and 
                                           (= x101 x86) 
                                           (exists ((x106 N)) 
                                               (and 
                                                   (f0 x86 x106) 
                                                   (f0 x106 x105)))))))) 
                       (forall ((x107 N)) 
                           (=> 
                               (and 
                                   (MS0 x107 n) 
                                   (not 
                                       (f0 x86 x107)) 
                                   (not 
                                       (= x107 p))) 
                               (or 
                                   (exists ((x108 N)) 
                                       (and 
                                           (f0 x108 x107) 
                                           (not 
                                               (f0 x86 x108)) 
                                           (not 
                                               (exists ((x109 N)) 
                                                   (and 
                                                       (= x108 x86) 
                                                       (exists ((x110 N)) 
                                                           (and 
                                                               (f0 x86 x110) 
                                                               (f0 x110 x109)))))))) 
                                   (exists ((x111 N)) 
                                       (and 
                                           (= x111 x86) 
                                           (exists ((x112 N)) 
                                               (and 
                                                   (f0 x86 x112) 
                                                   (f0 x112 x107)))))))) 
                       (forall ((x113 N) (x114 N) (x115 N)) 
                           (=> 
                               (and 
                                   (or 
                                       (and 
                                           (f0 x114 x113) 
                                           (not 
                                               (f0 x86 x114)) 
                                           (not 
                                               (exists ((x116 N)) 
                                                   (and 
                                                       (= x114 x86) 
                                                       (exists ((x117 N)) 
                                                           (and 
                                                               (f0 x86 x117) 
                                                               (f0 x117 x116))))))) 
                                       (and 
                                           (= x114 x86) 
                                           (exists ((x118 N)) 
                                               (and 
                                                   (f0 x86 x118) 
                                                   (f0 x118 x113))))) 
                                   (or 
                                       (and 
                                           (f0 x115 x113) 
                                           (not 
                                               (f0 x86 x115)) 
                                           (not 
                                               (exists ((x119 N)) 
                                                   (and 
                                                       (= x115 x86) 
                                                       (exists ((x120 N)) 
                                                           (and 
                                                               (f0 x86 x120) 
                                                               (f0 x120 x119))))))) 
                                       (and 
                                           (= x115 x86) 
                                           (exists ((x121 N)) 
                                               (and 
                                                   (f0 x86 x121) 
                                                   (f0 x121 x113)))))) 
                               (= x114 x115))))))
         :named hyp12))
(assert (! (MS0 x n)
         :named hyp13))
(assert (! (not 
               (= x t))
         :named hyp14))
(assert (! (not 
               (f0 x t))
         :named hyp15))
(assert (! (forall ((x122 N)) 
               (=> 
                   (MS0 x122 s) 
                   (and 
                       (MS0 x122 n) 
                       (not 
                           (f0 x x122)))))
         :named hyp16))
(assert (! (not 
               (exists ((x123 N) (x124 N)) 
                   (and 
                       (f0 x x124) 
                       (f0 x124 x123))))
         :named goal))
(check-sat)
(exit)

