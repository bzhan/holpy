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
(assert (forall ((x130 N) (x131 Int)) 
            (exists ((X PNZ)) 
                (and 
                    (MS x130 x131 X) 
                    (forall ((y N) (y0 Int)) 
                        (=> 
                            (MS y y0 X) 
                            (and 
                                (= y x130) 
                                (= y0 x131))))))))
; Elementary Sets axiom (Singleton part)
(assert (forall ((x132 N)) 
            (exists ((X0 PN)) 
                (and 
                    (MS0 x132 X0) 
                    (forall ((y1 N)) 
                        (=> 
                            (MS0 y1 X0) 
                            (= y1 x132)))))))
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
               (MS p x65 o))
         :named hyp8))
(assert (! (forall ((x66 N) (x67 Int) (x68 Int)) 
               (=> 
                   (and 
                       (MS x66 x67 o) 
                       (MS x66 x68 o)) 
                   (= x67 x68)))
         :named hyp9))
(assert (! (exists ((x69 Int)) 
               (and 
                   (<= 0 x69) 
                   (exists ((f3 PNZ)) 
                       (and 
                           (forall ((x70 N) (x71 Int)) 
                               (=> 
                                   (MS x70 x71 f3) 
                                   (and 
                                       (MS0 x70 n) 
                                       (<= 1 x71) 
                                       (<= x71 x69)))) 
                           (forall ((x72 N) (x73 Int) (x74 Int)) 
                               (=> 
                                   (and 
                                       (MS x72 x73 f3) 
                                       (MS x72 x74 f3)) 
                                   (= x73 x74))) 
                           (forall ((x75 N)) 
                               (=> 
                                   (MS0 x75 n) 
                                   (exists ((x76 Int)) 
                                       (MS x75 x76 f3)))) 
                           (forall ((x77 Int)) 
                               (=> 
                                   (and 
                                       (<= 1 x77) 
                                       (<= x77 x69)) 
                                   (exists ((x78 N)) 
                                       (MS x78 x77 f3)))) 
                           (forall ((x79 Int) (x80 N) (x81 N)) 
                               (=> 
                                   (and 
                                       (MS x80 x79 f3) 
                                       (MS x81 x79 f3)) 
                                   (= x80 x81))))) 
                   (MS t x69 o)))
         :named hyp10))
(assert (! (exists ((x82 Int)) 
               (MS t x82 o))
         :named hyp11))
(assert (! (forall ((q PN)) 
               (=> 
                   (and 
                       (forall ((x83 N)) 
                           (=> 
                               (MS0 x83 q) 
                               (MS0 x83 n))) 
                       (forall ((z N)) 
                           (=> 
                               (and 
                                   (MS0 z n) 
                                   (forall ((x84 N)) 
                                       (=> 
                                           (exists ((x85 N)) 
                                               (and 
                                                   (= x85 z) 
                                                   (f0 x84 x85))) 
                                           (MS0 x84 q)))) 
                               (MS0 z q)))) 
                   (forall ((x86 N)) 
                       (=> 
                           (MS0 x86 n) 
                           (MS0 x86 q)))))
         :named hyp12))
(assert (! (not 
               (= p t))
         :named hyp13))
(assert (! (forall ((x87 N)) 
               (=> 
                   (and 
                       (MS0 x87 n) 
                       (not 
                           (= x87 t))) 
                   (exists ((x88 N) (x89 Int)) 
                       (and 
                           (f0 x87 x88) 
                           (forall ((x90 Int)) 
                               (=> 
                                   (MS x87 x90 o) 
                                   (= x89 (+ x90 1)))) 
                           (MS x88 x89 o)))))
         :named hyp14))
(assert (! (forall ((x91 N)) 
               (=> 
                   (and 
                       (MS0 x91 n) 
                       (not 
                           (= x91 t)) 
                       (not 
                           (f0 x91 t))) 
                   (and 
                       (forall ((x92 N) (x93 N)) 
                           (=> 
                               (or 
                                   (and 
                                       (f0 x92 x93) 
                                       (not 
                                           (f0 x91 x92)) 
                                       (not 
                                           (exists ((x94 N)) 
                                               (and 
                                                   (= x92 x91) 
                                                   (exists ((x95 N)) 
                                                       (and 
                                                           (f0 x91 x95) 
                                                           (f0 x95 x94))))))) 
                                   (and 
                                       (= x92 x91) 
                                       (exists ((x96 N)) 
                                           (and 
                                               (f0 x91 x96) 
                                               (f0 x96 x93))))) 
                               (and 
                                   (MS0 x92 n) 
                                   (not 
                                       (f0 x91 x92)) 
                                   (not 
                                       (= x92 t)) 
                                   (MS0 x93 n) 
                                   (not 
                                       (f0 x91 x93)) 
                                   (not 
                                       (= x93 p))))) 
                       (forall ((x97 N) (x98 N) (x99 N)) 
                           (=> 
                               (and 
                                   (or 
                                       (and 
                                           (f0 x97 x98) 
                                           (not 
                                               (f0 x91 x97)) 
                                           (not 
                                               (exists ((x100 N)) 
                                                   (and 
                                                       (= x97 x91) 
                                                       (exists ((x101 N)) 
                                                           (and 
                                                               (f0 x91 x101) 
                                                               (f0 x101 x100))))))) 
                                       (and 
                                           (= x97 x91) 
                                           (exists ((x102 N)) 
                                               (and 
                                                   (f0 x91 x102) 
                                                   (f0 x102 x98))))) 
                                   (or 
                                       (and 
                                           (f0 x97 x99) 
                                           (not 
                                               (f0 x91 x97)) 
                                           (not 
                                               (exists ((x103 N)) 
                                                   (and 
                                                       (= x97 x91) 
                                                       (exists ((x104 N)) 
                                                           (and 
                                                               (f0 x91 x104) 
                                                               (f0 x104 x103))))))) 
                                       (and 
                                           (= x97 x91) 
                                           (exists ((x105 N)) 
                                               (and 
                                                   (f0 x91 x105) 
                                                   (f0 x105 x99)))))) 
                               (= x98 x99))) 
                       (forall ((x106 N)) 
                           (=> 
                               (and 
                                   (MS0 x106 n) 
                                   (not 
                                       (f0 x91 x106)) 
                                   (not 
                                       (= x106 t))) 
                               (or 
                                   (exists ((x107 N)) 
                                       (and 
                                           (f0 x106 x107) 
                                           (not 
                                               (f0 x91 x106)) 
                                           (not 
                                               (exists ((x108 N)) 
                                                   (and 
                                                       (= x106 x91) 
                                                       (exists ((x109 N)) 
                                                           (and 
                                                               (f0 x91 x109) 
                                                               (f0 x109 x108)))))))) 
                                   (exists ((x110 N)) 
                                       (and 
                                           (= x106 x91) 
                                           (exists ((x111 N)) 
                                               (and 
                                                   (f0 x91 x111) 
                                                   (f0 x111 x110)))))))) 
                       (forall ((x112 N)) 
                           (=> 
                               (and 
                                   (MS0 x112 n) 
                                   (not 
                                       (f0 x91 x112)) 
                                   (not 
                                       (= x112 p))) 
                               (or 
                                   (exists ((x113 N)) 
                                       (and 
                                           (f0 x113 x112) 
                                           (not 
                                               (f0 x91 x113)) 
                                           (not 
                                               (exists ((x114 N)) 
                                                   (and 
                                                       (= x113 x91) 
                                                       (exists ((x115 N)) 
                                                           (and 
                                                               (f0 x91 x115) 
                                                               (f0 x115 x114)))))))) 
                                   (exists ((x116 N)) 
                                       (and 
                                           (= x116 x91) 
                                           (exists ((x117 N)) 
                                               (and 
                                                   (f0 x91 x117) 
                                                   (f0 x117 x112)))))))) 
                       (forall ((x118 N) (x119 N) (x120 N)) 
                           (=> 
                               (and 
                                   (or 
                                       (and 
                                           (f0 x119 x118) 
                                           (not 
                                               (f0 x91 x119)) 
                                           (not 
                                               (exists ((x121 N)) 
                                                   (and 
                                                       (= x119 x91) 
                                                       (exists ((x122 N)) 
                                                           (and 
                                                               (f0 x91 x122) 
                                                               (f0 x122 x121))))))) 
                                       (and 
                                           (= x119 x91) 
                                           (exists ((x123 N)) 
                                               (and 
                                                   (f0 x91 x123) 
                                                   (f0 x123 x118))))) 
                                   (or 
                                       (and 
                                           (f0 x120 x118) 
                                           (not 
                                               (f0 x91 x120)) 
                                           (not 
                                               (exists ((x124 N)) 
                                                   (and 
                                                       (= x120 x91) 
                                                       (exists ((x125 N)) 
                                                           (and 
                                                               (f0 x91 x125) 
                                                               (f0 x125 x124))))))) 
                                       (and 
                                           (= x120 x91) 
                                           (exists ((x126 N)) 
                                               (and 
                                                   (f0 x91 x126) 
                                                   (f0 x126 x118)))))) 
                               (= x119 x120))))))
         :named hyp15))
(assert (! (MS0 x n)
         :named hyp16))
(assert (! (not 
               (= x t))
         :named hyp17))
(assert (! (not 
               (f0 x t))
         :named hyp18))
(assert (! (forall ((x127 N)) 
               (=> 
                   (MS0 x127 s) 
                   (and 
                       (MS0 x127 n) 
                       (not 
                           (f0 x x127)))))
         :named hyp19))
(assert (! (not 
               (exists ((x128 N) (x129 N)) 
                   (and 
                       (f0 x x129) 
                       (f0 x129 x128))))
         :named goal))
(check-sat)
(exit)

