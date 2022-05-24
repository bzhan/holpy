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
(declare-fun t () N)
(declare-fun x () N)

; Elementary Sets axiom (Singleton part)
(assert (forall ((x126 N) (x127 Int)) 
            (exists ((X PNZ)) 
                (and 
                    (MS x126 x127 X) 
                    (forall ((y N) (y0 Int)) 
                        (=> 
                            (MS y y0 X) 
                            (and 
                                (= y x126) 
                                (= y0 x127))))))))
; Elementary Sets axiom (Singleton part)
(assert (forall ((x128 N)) 
            (exists ((X0 PN)) 
                (and 
                    (MS0 x128 X0) 
                    (forall ((y1 N)) 
                        (=> 
                            (MS0 y1 X0) 
                            (= y1 x128)))))))
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
(assert (! (forall ((s PN)) 
               (=> 
                   (and 
                       (forall ((x22 N)) 
                           (=> 
                               (MS0 x22 s) 
                               (MS0 x22 n))) 
                       (forall ((x23 N)) 
                           (=> 
                               (MS0 x23 s) 
                               (exists ((x24 N)) 
                                   (and 
                                       (MS0 x24 s) 
                                       (f0 x24 x23)))))) 
                   (forall ((x25 N)) 
                       (not 
                           (MS0 x25 s)))))
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
(assert (! (MS0 x n)
         :named hyp12))
(assert (! (not 
               (= x t))
         :named hyp13))
(assert (! (not 
               (f0 x t))
         :named hyp14))
(assert (! (exists ((x86 Int)) 
               (MS p x86 o))
         :named hyp15))
(assert (! (forall ((x87 N) (x88 Int) (x89 Int)) 
               (=> 
                   (and 
                       (MS x87 x88 o) 
                       (MS x87 x89 o)) 
                   (= x88 x89)))
         :named hyp16))
(assert (! (exists ((x90 Int)) 
               (MS t x90 o))
         :named hyp17))
(assert (! (not 
               (and 
                   (forall ((x91 N) (x92 N)) 
                       (=> 
                           (or 
                               (and 
                                   (f0 x91 x92) 
                                   (not 
                                       (f0 x x91)) 
                                   (not 
                                       (exists ((x93 N)) 
                                           (and 
                                               (= x91 x) 
                                               (exists ((x94 N)) 
                                                   (and 
                                                       (f0 x x94) 
                                                       (f0 x94 x93))))))) 
                               (and 
                                   (= x91 x) 
                                   (exists ((x95 N)) 
                                       (and 
                                           (f0 x x95) 
                                           (f0 x95 x92))))) 
                           (and 
                               (MS0 x91 n) 
                               (not 
                                   (f0 x x91)) 
                               (not 
                                   (= x91 t)) 
                               (MS0 x92 n) 
                               (not 
                                   (f0 x x92)) 
                               (not 
                                   (= x92 p))))) 
                   (forall ((x96 N) (x97 N) (x98 N)) 
                       (=> 
                           (and 
                               (or 
                                   (and 
                                       (f0 x96 x97) 
                                       (not 
                                           (f0 x x96)) 
                                       (not 
                                           (exists ((x99 N)) 
                                               (and 
                                                   (= x96 x) 
                                                   (exists ((x100 N)) 
                                                       (and 
                                                           (f0 x x100) 
                                                           (f0 x100 x99))))))) 
                                   (and 
                                       (= x96 x) 
                                       (exists ((x101 N)) 
                                           (and 
                                               (f0 x x101) 
                                               (f0 x101 x97))))) 
                               (or 
                                   (and 
                                       (f0 x96 x98) 
                                       (not 
                                           (f0 x x96)) 
                                       (not 
                                           (exists ((x102 N)) 
                                               (and 
                                                   (= x96 x) 
                                                   (exists ((x103 N)) 
                                                       (and 
                                                           (f0 x x103) 
                                                           (f0 x103 x102))))))) 
                                   (and 
                                       (= x96 x) 
                                       (exists ((x104 N)) 
                                           (and 
                                               (f0 x x104) 
                                               (f0 x104 x98)))))) 
                           (= x97 x98))) 
                   (forall ((x105 N)) 
                       (=> 
                           (and 
                               (MS0 x105 n) 
                               (not 
                                   (f0 x x105)) 
                               (not 
                                   (= x105 t))) 
                           (or 
                               (exists ((x106 N)) 
                                   (and 
                                       (f0 x105 x106) 
                                       (not 
                                           (f0 x x105)) 
                                       (not 
                                           (exists ((x107 N)) 
                                               (and 
                                                   (= x105 x) 
                                                   (exists ((x108 N)) 
                                                       (and 
                                                           (f0 x x108) 
                                                           (f0 x108 x107)))))))) 
                               (exists ((x109 N)) 
                                   (and 
                                       (= x105 x) 
                                       (exists ((x110 N)) 
                                           (and 
                                               (f0 x x110) 
                                               (f0 x110 x109)))))))) 
                   (forall ((x111 N)) 
                       (=> 
                           (and 
                               (MS0 x111 n) 
                               (not 
                                   (f0 x x111)) 
                               (not 
                                   (= x111 p))) 
                           (or 
                               (exists ((x112 N)) 
                                   (and 
                                       (f0 x112 x111) 
                                       (not 
                                           (f0 x x112)) 
                                       (not 
                                           (exists ((x113 N)) 
                                               (and 
                                                   (= x112 x) 
                                                   (exists ((x114 N)) 
                                                       (and 
                                                           (f0 x x114) 
                                                           (f0 x114 x113)))))))) 
                               (exists ((x115 N)) 
                                   (and 
                                       (= x115 x) 
                                       (exists ((x116 N)) 
                                           (and 
                                               (f0 x x116) 
                                               (f0 x116 x111)))))))) 
                   (forall ((x117 N) (x118 N) (x119 N)) 
                       (=> 
                           (and 
                               (or 
                                   (and 
                                       (f0 x118 x117) 
                                       (not 
                                           (f0 x x118)) 
                                       (not 
                                           (exists ((x120 N)) 
                                               (and 
                                                   (= x118 x) 
                                                   (exists ((x121 N)) 
                                                       (and 
                                                           (f0 x x121) 
                                                           (f0 x121 x120))))))) 
                                   (and 
                                       (= x118 x) 
                                       (exists ((x122 N)) 
                                           (and 
                                               (f0 x x122) 
                                               (f0 x122 x117))))) 
                               (or 
                                   (and 
                                       (f0 x119 x117) 
                                       (not 
                                           (f0 x x119)) 
                                       (not 
                                           (exists ((x123 N)) 
                                               (and 
                                                   (= x119 x) 
                                                   (exists ((x124 N)) 
                                                       (and 
                                                           (f0 x x124) 
                                                           (f0 x124 x123))))))) 
                                   (and 
                                       (= x119 x) 
                                       (exists ((x125 N)) 
                                           (and 
                                               (f0 x x125) 
                                               (f0 x125 x117)))))) 
                           (= x118 x119)))))
         :named goal))
(check-sat)
(exit)

