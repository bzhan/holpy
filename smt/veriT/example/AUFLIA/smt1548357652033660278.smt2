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
(declare-fun rdy (R) Bool)
(declare-fun resrt (R) Bool)
(declare-fun rsrtbl (B R) Bool)
(declare-fun rtbl (B R) Bool)
(declare-fun LBT () PB0)
(declare-fun OCC () PB0)
(declare-fun TRK () PBB)
(declare-fun b () B)
(declare-fun r () R)
(declare-fun resbl () PB0)

; Elementary Sets axiom (Singleton part)
(assert (forall ((x132 B)) 
            (exists ((X PB0)) 
                (and 
                    (MS x132 X) 
                    (forall ((y0 B)) 
                        (=> 
                            (MS y0 X) 
                            (= y0 x132)))))))
; Elementary Sets axiom (Singleton part)
(assert (forall ((x133 B) (x134 B)) 
            (exists ((X0 PBB)) 
                (and 
                    (MS0 x133 x134 X0) 
                    (forall ((y1 B) (y2 B)) 
                        (=> 
                            (MS0 y1 y2 X0) 
                            (and 
                                (= y1 x133) 
                                (= y2 x134))))))))
(assert (! (forall ((r0 R)) 
               (=> 
                   (rdy r0) 
                   (forall ((x B) (x0 R)) 
                       (= 
                           (and 
                               (rtbl x x0) 
                               (= x0 r0)) 
                           (and 
                               (rsrtbl x x0) 
                               (= x0 r0))))))
         :named hyp1))
(assert (! (MS b LBT)
         :named hyp2))
(assert (! (not 
               (exists ((x1 B)) 
                   (MS0 b x1 TRK)))
         :named hyp3))
(assert (! (rdy r)
         :named hyp4))
(assert (! (forall ((x2 B)) 
               (exists ((x3 R)) 
                   (rtbl x2 x3)))
         :named hyp5))
(assert (! (forall ((x4 R)) 
               (exists ((x5 B)) 
                   (rtbl x5 x4)))
         :named hyp6))
(assert (! (and 
               (forall ((x6 R) (x7 PBB)) 
                   (=> 
                       (nxt x6 x7) 
                       (and 
                           (forall ((x8 B) (x9 B) (x10 B)) 
                               (=> 
                                   (and 
                                       (MS0 x8 x9 x7) 
                                       (MS0 x8 x10 x7)) 
                                   (= x9 x10))) 
                           (forall ((x11 B) (x12 B) (x13 B)) 
                               (=> 
                                   (and 
                                       (MS0 x12 x11 x7) 
                                       (MS0 x13 x11 x7)) 
                                   (= x12 x13)))))) 
               (forall ((x14 R) (x15 PBB) (x16 PBB)) 
                   (=> 
                       (and 
                           (nxt x14 x15) 
                           (nxt x14 x16)) 
                       (forall ((x17 B) (x18 B)) 
                           (= 
                               (MS0 x17 x18 x15) 
                               (MS0 x17 x18 x16))))) 
               (forall ((x19 R)) 
                   (exists ((x20 PBB)) 
                       (nxt x19 x20))))
         :named hyp7))
(assert (! (and 
               (forall ((x21 R) (x22 B) (x23 B)) 
                   (=> 
                       (and 
                           (fst x21 x22) 
                           (fst x21 x23)) 
                       (= x22 x23))) 
               (forall ((x24 R)) 
                   (exists ((x25 B)) 
                       (fst x24 x25))))
         :named hyp8))
(assert (! (and 
               (forall ((x26 R) (x27 B) (x28 B)) 
                   (=> 
                       (and 
                           (lst x26 x27) 
                           (lst x26 x28)) 
                       (= x27 x28))) 
               (forall ((x29 R)) 
                   (exists ((x30 B)) 
                       (lst x29 x30))))
         :named hyp9))
(assert (! (forall ((x31 B) (x32 R)) 
               (=> 
                   (fst x32 x31) 
                   (rtbl x31 x32)))
         :named hyp10))
(assert (! (forall ((x33 B) (x34 R)) 
               (=> 
                   (lst x34 x33) 
                   (rtbl x33 x34)))
         :named hyp11))
(assert (! (and 
               (forall ((x35 B) (x36 R)) 
                   (=> 
                       (rsrtbl x35 x36) 
                       (and 
                           (MS x35 resbl) 
                           (resrt x36)))) 
               (forall ((x37 B) (x38 R) (x39 R)) 
                   (=> 
                       (and 
                           (rsrtbl x37 x38) 
                           (rsrtbl x37 x39)) 
                       (= x38 x39))) 
               (forall ((x40 B)) 
                   (=> 
                       (MS x40 resbl) 
                       (exists ((x41 R)) 
                           (rsrtbl x40 x41)))))
         :named hyp12))
(assert (! (forall ((x42 B) (x43 R)) 
               (=> 
                   (rsrtbl x42 x43) 
                   (rtbl x42 x43)))
         :named hyp13))
(assert (! (forall ((x44 B)) 
               (=> 
                   (MS x44 OCC) 
                   (MS x44 resbl)))
         :named hyp14))
(assert (! (and 
               (forall ((x45 B) (x46 B) (x47 B)) 
                   (=> 
                       (and 
                           (MS0 x45 x46 TRK) 
                           (MS0 x45 x47 TRK)) 
                       (= x46 x47))) 
               (forall ((x48 B) (x49 B) (x50 B)) 
                   (=> 
                       (and 
                           (MS0 x49 x48 TRK) 
                           (MS0 x50 x48 TRK)) 
                       (= x49 x50))))
         :named hyp15))
(assert (! (forall ((x51 R)) 
               (=> 
                   (frm x51) 
                   (resrt x51)))
         :named hyp16))
(assert (! (forall ((x52 R)) 
               (=> 
                   (exists ((x53 B)) 
                       (and 
                           (MS x53 OCC) 
                           (rsrtbl x53 x52))) 
                   (frm x52)))
         :named hyp17))
(assert (! (forall ((r1 R)) 
               (=> 
                   (and 
                       (resrt r1) 
                       (not 
                           (frm r1))) 
                   (forall ((x54 B) (x55 R)) 
                       (= 
                           (and 
                               (rtbl x54 x55) 
                               (= x55 r1)) 
                           (and 
                               (rsrtbl x54 x55) 
                               (= x55 r1))))))
         :named hyp18))
(assert (! (forall ((r2 R)) 
               (=> 
                   (frm r2) 
                   (forall ((x56 B) (x57 B)) 
                       (= 
                           (and 
                               (exists ((x58 PBB)) 
                                   (and 
                                       (nxt r2 x58) 
                                       (MS0 x56 x57 x58))) 
                               (exists ((x59 R)) 
                                   (and 
                                       (= x59 r2) 
                                       (rsrtbl x56 x59)))) 
                           (and 
                               (MS0 x56 x57 TRK) 
                               (exists ((x60 R)) 
                                   (and 
                                       (= x60 r2) 
                                       (rsrtbl x56 x60))))))))
         :named hyp19))
(assert (! (forall ((x61 B)) 
               (=> 
                   (MS x61 LBT) 
                   (MS x61 OCC)))
         :named hyp20))
(assert (! (forall ((b0 B)) 
               (=> 
                   (and 
                       (MS b0 OCC) 
                       (exists ((x62 B)) 
                           (MS0 b0 x62 TRK))) 
                   (exists ((x63 PBB)) 
                       (and 
                           (exists ((x64 R)) 
                               (and 
                                   (rsrtbl b0 x64) 
                                   (nxt x64 x63))) 
                           (exists ((x65 B)) 
                               (and 
                                   (MS0 b0 x65 TRK) 
                                   (MS0 b0 x65 x63)))))))
         :named hyp21))
(assert (! (forall ((x66 R)) 
               (=> 
                   (rdy x66) 
                   (frm x66)))
         :named hyp22))
(assert (! (forall ((r3 R)) 
               (=> 
                   (rdy r3) 
                   (forall ((x67 B)) 
                       (not 
                           (and 
                               (exists ((x68 R)) 
                                   (and 
                                       (rtbl x67 x68) 
                                       (= x68 r3))) 
                               (MS x67 OCC))))))
         :named hyp23))
(assert (! (forall ((a B) (b1 B)) 
               (=> 
                   (and 
                       (MS b1 LBT) 
                       (exists ((x69 B) (x70 PBB)) 
                           (and 
                               (exists ((x71 R)) 
                                   (and 
                                       (rsrtbl b1 x71) 
                                       (nxt x71 x70))) 
                               (MS0 x69 b1 x70))) 
                       (exists ((x72 PBB)) 
                           (and 
                               (exists ((x73 R)) 
                                   (and 
                                       (rsrtbl b1 x73) 
                                       (nxt x73 x72))) 
                               (MS0 a b1 x72))) 
                       (exists ((x74 R)) 
                           (rsrtbl a x74))) 
                   (not 
                       (exists ((x75 R)) 
                           (and 
                               (rsrtbl b1 x75) 
                               (rsrtbl a x75))))))
         :named hyp24))
(assert (! (forall ((r4 R) (S PB0)) 
               (=> 
                   (forall ((x76 B)) 
                       (=> 
                           (MS x76 S) 
                           (exists ((x77 B)) 
                               (and 
                                   (MS x77 S) 
                                   (exists ((x78 PBB)) 
                                       (and 
                                           (nxt r4 x78) 
                                           (MS0 x77 x76 x78))))))) 
                   (forall ((x79 B)) 
                       (not 
                           (MS x79 S)))))
         :named hyp25))
(assert (! (and 
               (forall ((r5 R)) 
                   (forall ((x80 B) (x81 B)) 
                       (=> 
                           (exists ((x82 PBB)) 
                               (and 
                                   (nxt r5 x82) 
                                   (MS0 x80 x81 x82))) 
                           (and 
                               (exists ((x83 R)) 
                                   (and 
                                       (= x83 r5) 
                                       (rtbl x80 x83))) 
                               (not 
                                   (lst r5 x80)) 
                               (exists ((x84 R)) 
                                   (and 
                                       (= x84 r5) 
                                       (rtbl x81 x84))) 
                               (not 
                                   (fst r5 x81)))))) 
               (forall ((r6 R)) 
                   (forall ((x85 B) (x86 B) (x87 B)) 
                       (=> 
                           (and 
                               (exists ((x88 PBB)) 
                                   (and 
                                       (nxt r6 x88) 
                                       (MS0 x85 x86 x88))) 
                               (exists ((x89 PBB)) 
                                   (and 
                                       (nxt r6 x89) 
                                       (MS0 x85 x87 x89)))) 
                           (= x86 x87)))) 
               (forall ((r7 R)) 
                   (forall ((x90 B)) 
                       (=> 
                           (and 
                               (exists ((x91 R)) 
                                   (and 
                                       (= x91 r7) 
                                       (rtbl x90 x91))) 
                               (not 
                                   (lst r7 x90))) 
                           (exists ((x92 B) (x93 PBB)) 
                               (and 
                                   (nxt r7 x93) 
                                   (MS0 x90 x92 x93)))))) 
               (forall ((r8 R)) 
                   (forall ((x94 B)) 
                       (=> 
                           (and 
                               (exists ((x95 R)) 
                                   (and 
                                       (= x95 r8) 
                                       (rtbl x94 x95))) 
                               (not 
                                   (fst r8 x94))) 
                           (exists ((x96 B) (x97 PBB)) 
                               (and 
                                   (nxt r8 x97) 
                                   (MS0 x96 x94 x97)))))) 
               (forall ((r9 R)) 
                   (forall ((x98 B) (x99 B) (x100 B)) 
                       (=> 
                           (and 
                               (exists ((x101 PBB)) 
                                   (and 
                                       (nxt r9 x101) 
                                       (MS0 x99 x98 x101))) 
                               (exists ((x102 PBB)) 
                                   (and 
                                       (nxt r9 x102) 
                                       (MS0 x100 x98 x102)))) 
                           (= x99 x100)))))
         :named hyp26))
(assert (! (forall ((r10 R) (x103 B)) 
               (=> 
                   (exists ((x104 B)) 
                       (and 
                           (exists ((x105 R)) 
                               (and 
                                   (= x105 r10) 
                                   (rsrtbl x104 x105))) 
                           (exists ((x106 PBB)) 
                               (and 
                                   (nxt r10 x106) 
                                   (MS0 x104 x103 x106))))) 
                   (exists ((x107 R)) 
                       (and 
                           (= x107 r10) 
                           (rsrtbl x103 x107)))))
         :named hyp27))
(assert (! (forall ((r11 R) (x108 B)) 
               (=> 
                   (exists ((x109 B)) 
                       (and 
                           (exists ((x110 R)) 
                               (and 
                                   (= x110 r11) 
                                   (rsrtbl x109 x110))) 
                           (not 
                               (MS x109 OCC)) 
                           (exists ((x111 PBB)) 
                               (and 
                                   (nxt r11 x111) 
                                   (MS0 x109 x108 x111))))) 
                   (and 
                       (exists ((x112 R)) 
                           (and 
                               (= x112 r11) 
                               (rsrtbl x108 x112))) 
                       (not 
                           (MS x108 OCC)))))
         :named hyp28))
(assert (! (forall ((x113 B) (y B)) 
               (=> 
                   (MS0 x113 y TRK) 
                   (exists ((r12 R) (x114 PBB)) 
                       (and 
                           (nxt r12 x114) 
                           (MS0 x113 y x114)))))
         :named hyp29))
(assert (! (forall ((r13 R)) 
               (not 
                   (exists ((x115 B)) 
                       (and 
                           (lst r13 x115) 
                           (fst r13 x115)))))
         :named hyp30))
(assert (! (forall ((r14 R) (s R)) 
               (=> 
                   (not 
                       (= r14 s)) 
                   (not 
                       (and 
                           (exists ((x116 R)) 
                               (and 
                                   (= x116 s) 
                                   (exists ((x117 B)) 
                                       (and 
                                           (fst r14 x117) 
                                           (rtbl x117 x116))))) 
                           (not 
                               (or 
                                   (exists ((x118 B)) 
                                       (and 
                                           (fst s x118) 
                                           (fst r14 x118))) 
                                   (exists ((x119 B)) 
                                       (and 
                                           (lst s x119) 
                                           (fst r14 x119)))))))))
         :named hyp31))
(assert (! (forall ((r15 R) (s0 R)) 
               (=> 
                   (not 
                       (= r15 s0)) 
                   (not 
                       (and 
                           (exists ((x120 R)) 
                               (and 
                                   (= x120 s0) 
                                   (exists ((x121 B)) 
                                       (and 
                                           (lst r15 x121) 
                                           (rtbl x121 x120))))) 
                           (not 
                               (or 
                                   (exists ((x122 B)) 
                                       (and 
                                           (fst s0 x122) 
                                           (lst r15 x122))) 
                                   (exists ((x123 B)) 
                                       (and 
                                           (lst s0 x123) 
                                           (lst r15 x123)))))))))
         :named hyp32))
(assert (! (forall ((r16 R) (x124 B)) 
               (=> 
                   (and 
                       (exists ((x125 B)) 
                           (and 
                               (exists ((x126 R)) 
                                   (and 
                                       (= x126 r16) 
                                       (rtbl x125 x126))) 
                               (not 
                                   (exists ((x127 R)) 
                                       (and 
                                           (= x127 r16) 
                                           (rsrtbl x125 x127)))) 
                               (exists ((x128 PBB)) 
                                   (and 
                                       (nxt r16 x128) 
                                       (MS0 x125 x124 x128))))) 
                       (exists ((x129 R)) 
                           (and 
                               (= x129 r16) 
                               (rsrtbl x124 x129)))) 
                   (MS x124 OCC)))
         :named hyp33))
(assert (! (not 
               (forall ((x130 B) (x131 R)) 
                   (= 
                       (and 
                           (rtbl x130 x131) 
                           (= x131 r)) 
                       (and 
                           (rsrtbl x130 x131) 
                           (not 
                               (= x130 b)) 
                           (= x131 r)))))
         :named goal))
(check-sat)
(exit)

