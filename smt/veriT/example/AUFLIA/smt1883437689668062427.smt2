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
(declare-fun MS (B PB0) Bool)
(declare-fun MS0 (B B PBB) Bool)
(declare-fun frm (R) Bool)
(declare-fun fst (R B) Bool)
(declare-fun lst (R B) Bool)
(declare-fun nxt (R PBB) Bool)
(declare-fun resrt (R) Bool)
(declare-fun rsrtbl (B R) Bool)
(declare-fun rtbl (B R) Bool)
(declare-fun LBT () PB0)
(declare-fun OCC () PB0)
(declare-fun TRK () PBB)
(declare-fun b () B)
(declare-fun resbl () PB0)

; Elementary Sets axiom (Singleton part)
(assert (forall ((x124 B)) 
            (exists ((X PB0)) 
                (and 
                    (MS x124 X) 
                    (forall ((y0 B)) 
                        (=> 
                            (MS y0 X) 
                            (= y0 x124)))))))
; Elementary Sets axiom (Singleton part)
(assert (forall ((x125 B) (x126 B)) 
            (exists ((X0 PBB)) 
                (and 
                    (MS0 x125 x126 X0) 
                    (forall ((y1 B) (y2 B)) 
                        (=> 
                            (MS0 y1 y2 X0) 
                            (and 
                                (= y1 x125) 
                                (= y2 x126))))))))
(assert (! (MS b LBT)
         :named hyp1))
(assert (! (not 
               (exists ((x B)) 
                   (MS0 b x TRK)))
         :named hyp2))
(assert (! (forall ((x0 B)) 
               (exists ((x1 R)) 
                   (rtbl x0 x1)))
         :named hyp3))
(assert (! (forall ((x2 R)) 
               (exists ((x3 B)) 
                   (rtbl x3 x2)))
         :named hyp4))
(assert (! (and 
               (forall ((x4 R) (x5 PBB)) 
                   (=> 
                       (nxt x4 x5) 
                       (and 
                           (forall ((x6 B) (x7 B) (x8 B)) 
                               (=> 
                                   (and 
                                       (MS0 x6 x7 x5) 
                                       (MS0 x6 x8 x5)) 
                                   (= x7 x8))) 
                           (forall ((x9 B) (x10 B) (x11 B)) 
                               (=> 
                                   (and 
                                       (MS0 x10 x9 x5) 
                                       (MS0 x11 x9 x5)) 
                                   (= x10 x11)))))) 
               (forall ((x12 R) (x13 PBB) (x14 PBB)) 
                   (=> 
                       (and 
                           (nxt x12 x13) 
                           (nxt x12 x14)) 
                       (forall ((x15 B) (x16 B)) 
                           (= 
                               (MS0 x15 x16 x13) 
                               (MS0 x15 x16 x14))))) 
               (forall ((x17 R)) 
                   (exists ((x18 PBB)) 
                       (nxt x17 x18))))
         :named hyp5))
(assert (! (and 
               (forall ((x19 R) (x20 B) (x21 B)) 
                   (=> 
                       (and 
                           (fst x19 x20) 
                           (fst x19 x21)) 
                       (= x20 x21))) 
               (forall ((x22 R)) 
                   (exists ((x23 B)) 
                       (fst x22 x23))))
         :named hyp6))
(assert (! (and 
               (forall ((x24 R) (x25 B) (x26 B)) 
                   (=> 
                       (and 
                           (lst x24 x25) 
                           (lst x24 x26)) 
                       (= x25 x26))) 
               (forall ((x27 R)) 
                   (exists ((x28 B)) 
                       (lst x27 x28))))
         :named hyp7))
(assert (! (forall ((x29 B) (x30 R)) 
               (=> 
                   (fst x30 x29) 
                   (rtbl x29 x30)))
         :named hyp8))
(assert (! (forall ((x31 B) (x32 R)) 
               (=> 
                   (lst x32 x31) 
                   (rtbl x31 x32)))
         :named hyp9))
(assert (! (and 
               (forall ((x33 B) (x34 R)) 
                   (=> 
                       (rsrtbl x33 x34) 
                       (and 
                           (MS x33 resbl) 
                           (resrt x34)))) 
               (forall ((x35 B) (x36 R) (x37 R)) 
                   (=> 
                       (and 
                           (rsrtbl x35 x36) 
                           (rsrtbl x35 x37)) 
                       (= x36 x37))) 
               (forall ((x38 B)) 
                   (=> 
                       (MS x38 resbl) 
                       (exists ((x39 R)) 
                           (rsrtbl x38 x39)))))
         :named hyp10))
(assert (! (forall ((x40 B) (x41 R)) 
               (=> 
                   (rsrtbl x40 x41) 
                   (rtbl x40 x41)))
         :named hyp11))
(assert (! (forall ((x42 B)) 
               (=> 
                   (MS x42 OCC) 
                   (MS x42 resbl)))
         :named hyp12))
(assert (! (and 
               (forall ((x43 B) (x44 B) (x45 B)) 
                   (=> 
                       (and 
                           (MS0 x43 x44 TRK) 
                           (MS0 x43 x45 TRK)) 
                       (= x44 x45))) 
               (forall ((x46 B) (x47 B) (x48 B)) 
                   (=> 
                       (and 
                           (MS0 x47 x46 TRK) 
                           (MS0 x48 x46 TRK)) 
                       (= x47 x48))))
         :named hyp13))
(assert (! (forall ((x49 R)) 
               (=> 
                   (exists ((x50 B)) 
                       (and 
                           (MS x50 OCC) 
                           (rsrtbl x50 x49))) 
                   (frm x49)))
         :named hyp14))
(assert (! (forall ((r R)) 
               (=> 
                   (and 
                       (resrt r) 
                       (not 
                           (frm r))) 
                   (forall ((x51 B) (x52 R)) 
                       (= 
                           (and 
                               (rtbl x51 x52) 
                               (= x52 r)) 
                           (and 
                               (rsrtbl x51 x52) 
                               (= x52 r))))))
         :named hyp15))
(assert (! (forall ((r0 R)) 
               (=> 
                   (frm r0) 
                   (forall ((x53 B) (x54 B)) 
                       (= 
                           (and 
                               (exists ((x55 PBB)) 
                                   (and 
                                       (nxt r0 x55) 
                                       (MS0 x53 x54 x55))) 
                               (exists ((x56 R)) 
                                   (and 
                                       (= x56 r0) 
                                       (rsrtbl x53 x56)))) 
                           (and 
                               (MS0 x53 x54 TRK) 
                               (exists ((x57 R)) 
                                   (and 
                                       (= x57 r0) 
                                       (rsrtbl x53 x57))))))))
         :named hyp16))
(assert (! (forall ((x58 B)) 
               (=> 
                   (MS x58 LBT) 
                   (MS x58 OCC)))
         :named hyp17))
(assert (! (forall ((b0 B)) 
               (=> 
                   (and 
                       (MS b0 OCC) 
                       (exists ((x59 B)) 
                           (MS0 b0 x59 TRK))) 
                   (exists ((x60 PBB)) 
                       (and 
                           (exists ((x61 R)) 
                               (and 
                                   (rsrtbl b0 x61) 
                                   (nxt x61 x60))) 
                           (exists ((x62 B)) 
                               (and 
                                   (MS0 b0 x62 TRK) 
                                   (MS0 b0 x62 x60)))))))
         :named hyp18))
(assert (! (forall ((a B) (b1 B)) 
               (=> 
                   (and 
                       (MS b1 LBT) 
                       (exists ((x63 B) (x64 PBB)) 
                           (and 
                               (exists ((x65 R)) 
                                   (and 
                                       (rsrtbl b1 x65) 
                                       (nxt x65 x64))) 
                               (MS0 x63 b1 x64))) 
                       (exists ((x66 PBB)) 
                           (and 
                               (exists ((x67 R)) 
                                   (and 
                                       (rsrtbl b1 x67) 
                                       (nxt x67 x66))) 
                               (MS0 a b1 x66))) 
                       (exists ((x68 R)) 
                           (rsrtbl a x68))) 
                   (not 
                       (exists ((x69 R)) 
                           (and 
                               (rsrtbl b1 x69) 
                               (rsrtbl a x69))))))
         :named hyp19))
(assert (! (forall ((r1 R) (S PB0)) 
               (=> 
                   (forall ((x70 B)) 
                       (=> 
                           (MS x70 S) 
                           (exists ((x71 B)) 
                               (and 
                                   (MS x71 S) 
                                   (exists ((x72 PBB)) 
                                       (and 
                                           (nxt r1 x72) 
                                           (MS0 x71 x70 x72))))))) 
                   (forall ((x73 B)) 
                       (not 
                           (MS x73 S)))))
         :named hyp20))
(assert (! (and 
               (forall ((r2 R)) 
                   (forall ((x74 B) (x75 B)) 
                       (=> 
                           (exists ((x76 PBB)) 
                               (and 
                                   (nxt r2 x76) 
                                   (MS0 x74 x75 x76))) 
                           (and 
                               (exists ((x77 R)) 
                                   (and 
                                       (= x77 r2) 
                                       (rtbl x74 x77))) 
                               (not 
                                   (lst r2 x74)) 
                               (exists ((x78 R)) 
                                   (and 
                                       (= x78 r2) 
                                       (rtbl x75 x78))) 
                               (not 
                                   (fst r2 x75)))))) 
               (forall ((r3 R)) 
                   (forall ((x79 B) (x80 B) (x81 B)) 
                       (=> 
                           (and 
                               (exists ((x82 PBB)) 
                                   (and 
                                       (nxt r3 x82) 
                                       (MS0 x79 x80 x82))) 
                               (exists ((x83 PBB)) 
                                   (and 
                                       (nxt r3 x83) 
                                       (MS0 x79 x81 x83)))) 
                           (= x80 x81)))) 
               (forall ((r4 R)) 
                   (forall ((x84 B)) 
                       (=> 
                           (and 
                               (exists ((x85 R)) 
                                   (and 
                                       (= x85 r4) 
                                       (rtbl x84 x85))) 
                               (not 
                                   (lst r4 x84))) 
                           (exists ((x86 B) (x87 PBB)) 
                               (and 
                                   (nxt r4 x87) 
                                   (MS0 x84 x86 x87)))))) 
               (forall ((r5 R)) 
                   (forall ((x88 B)) 
                       (=> 
                           (and 
                               (exists ((x89 R)) 
                                   (and 
                                       (= x89 r5) 
                                       (rtbl x88 x89))) 
                               (not 
                                   (fst r5 x88))) 
                           (exists ((x90 B) (x91 PBB)) 
                               (and 
                                   (nxt r5 x91) 
                                   (MS0 x90 x88 x91)))))) 
               (forall ((r6 R)) 
                   (forall ((x92 B) (x93 B) (x94 B)) 
                       (=> 
                           (and 
                               (exists ((x95 PBB)) 
                                   (and 
                                       (nxt r6 x95) 
                                       (MS0 x93 x92 x95))) 
                               (exists ((x96 PBB)) 
                                   (and 
                                       (nxt r6 x96) 
                                       (MS0 x94 x92 x96)))) 
                           (= x93 x94)))))
         :named hyp21))
(assert (! (forall ((r7 R) (x97 B)) 
               (=> 
                   (exists ((x98 B)) 
                       (and 
                           (exists ((x99 R)) 
                               (and 
                                   (= x99 r7) 
                                   (rsrtbl x98 x99))) 
                           (exists ((x100 PBB)) 
                               (and 
                                   (nxt r7 x100) 
                                   (MS0 x98 x97 x100))))) 
                   (exists ((x101 R)) 
                       (and 
                           (= x101 r7) 
                           (rsrtbl x97 x101)))))
         :named hyp22))
(assert (! (forall ((r8 R) (x102 B)) 
               (=> 
                   (exists ((x103 B)) 
                       (and 
                           (exists ((x104 R)) 
                               (and 
                                   (= x104 r8) 
                                   (rsrtbl x103 x104))) 
                           (not 
                               (MS x103 OCC)) 
                           (exists ((x105 PBB)) 
                               (and 
                                   (nxt r8 x105) 
                                   (MS0 x103 x102 x105))))) 
                   (and 
                       (exists ((x106 R)) 
                           (and 
                               (= x106 r8) 
                               (rsrtbl x102 x106))) 
                       (not 
                           (MS x102 OCC)))))
         :named hyp23))
(assert (! (forall ((x107 B) (y B)) 
               (=> 
                   (MS0 x107 y TRK) 
                   (exists ((r9 R) (x108 PBB)) 
                       (and 
                           (nxt r9 x108) 
                           (MS0 x107 y x108)))))
         :named hyp24))
(assert (! (forall ((r10 R)) 
               (not 
                   (exists ((x109 B)) 
                       (and 
                           (lst r10 x109) 
                           (fst r10 x109)))))
         :named hyp25))
(assert (! (forall ((r11 R) (s R)) 
               (=> 
                   (not 
                       (= r11 s)) 
                   (not 
                       (and 
                           (exists ((x110 R)) 
                               (and 
                                   (= x110 s) 
                                   (exists ((x111 B)) 
                                       (and 
                                           (fst r11 x111) 
                                           (rtbl x111 x110))))) 
                           (not 
                               (or 
                                   (exists ((x112 B)) 
                                       (and 
                                           (fst s x112) 
                                           (fst r11 x112))) 
                                   (exists ((x113 B)) 
                                       (and 
                                           (lst s x113) 
                                           (fst r11 x113)))))))))
         :named hyp26))
(assert (! (forall ((r12 R) (s0 R)) 
               (=> 
                   (not 
                       (= r12 s0)) 
                   (not 
                       (and 
                           (exists ((x114 R)) 
                               (and 
                                   (= x114 s0) 
                                   (exists ((x115 B)) 
                                       (and 
                                           (lst r12 x115) 
                                           (rtbl x115 x114))))) 
                           (not 
                               (or 
                                   (exists ((x116 B)) 
                                       (and 
                                           (fst s0 x116) 
                                           (lst r12 x116))) 
                                   (exists ((x117 B)) 
                                       (and 
                                           (lst s0 x117) 
                                           (lst r12 x117)))))))))
         :named hyp27))
(assert (! (forall ((r13 R) (x118 B)) 
               (=> 
                   (and 
                       (exists ((x119 B)) 
                           (and 
                               (exists ((x120 R)) 
                                   (and 
                                       (= x120 r13) 
                                       (rtbl x119 x120))) 
                               (not 
                                   (exists ((x121 R)) 
                                       (and 
                                           (= x121 r13) 
                                           (rsrtbl x119 x121)))) 
                               (exists ((x122 PBB)) 
                                   (and 
                                       (nxt r13 x122) 
                                       (MS0 x119 x118 x122))))) 
                       (exists ((x123 R)) 
                           (and 
                               (= x123 r13) 
                               (rsrtbl x118 x123)))) 
                   (MS x118 OCC)))
         :named hyp28))
(assert (! (not 
               (MS b OCC))
         :named goal))
(check-sat)
(exit)

