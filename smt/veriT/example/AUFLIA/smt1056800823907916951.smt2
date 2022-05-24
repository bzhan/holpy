(set-info :smt-lib-version 2.6)
(set-logic AUFLIA)
(set-info :source |Generator: Rodin SMT Plug-in|)
(set-info :license "https://creativecommons.org/licenses/by-nc/4.0/")
(set-info :category "industrial")
(set-info :status unsat)

(declare-sort ENQUEUEABLE_ELEMENTS 0)
(declare-sort PACKET_START_ADDRESSES_IN_TC_BUFFER 0)
(declare-sort PACKET_START_ADDRESSES_IN_TC_POOL 0)
(declare-sort PACKET_START_ADDRESSES_IN_TM_BUFFER 0)
(declare-sort PACKET_START_ADDRESSES_IN_TM_POOL 0)
(declare-sort PE 0)
(declare-sort PQ 0)
(declare-sort PZ 0)
(declare-sort QUEUES 0)
(declare-fun Dequeue (QUEUES QUEUES) Bool)
(declare-fun Duplicate_Elements_of_Queue (QUEUES PE) Bool)
(declare-fun Elements_of_Queue (QUEUES PE) Bool)
(declare-fun Enqueue (ENQUEUEABLE_ELEMENTS QUEUES QUEUES) Bool)
(declare-fun Head_of_Queue (QUEUES ENQUEUEABLE_ELEMENTS) Bool)
(declare-fun Length_of_Queue (QUEUES Int) Bool)
(declare-fun MS (QUEUES PQ) Bool)
(declare-fun MS0 (ENQUEUEABLE_ELEMENTS PE) Bool)
(declare-fun MS1 (Int PZ) Bool)
(declare-fun Queues_of_Length (Int PQ) Bool)
(declare-fun TC_Buffer_Element_Address (ENQUEUEABLE_ELEMENTS PACKET_START_ADDRESSES_IN_TC_BUFFER) Bool)
(declare-fun TC_Pool_Element_Address (ENQUEUEABLE_ELEMENTS PACKET_START_ADDRESSES_IN_TC_POOL) Bool)
(declare-fun TM_Buffer_Element_Address (ENQUEUEABLE_ELEMENTS PACKET_START_ADDRESSES_IN_TM_BUFFER) Bool)
(declare-fun TM_Pool_Element_Address (ENQUEUEABLE_ELEMENTS PACKET_START_ADDRESSES_IN_TM_POOL) Bool)
(declare-fun ENQUEUEABLE_TC_BUFFER_ELEMENTS () PE)
(declare-fun ENQUEUEABLE_TC_POOL_ELEMENTS () PE)
(declare-fun ENQUEUEABLE_TM_BUFFER_ELEMENTS () PE)
(declare-fun ENQUEUEABLE_TM_POOL_ELEMENTS () PE)
(declare-fun Empty_Queue () QUEUES)
(declare-fun MAGIC_LENGTHS () PZ)

; Elementary Sets axiom (Singleton part)
(assert (forall ((x188 Int)) 
            (exists ((X PZ)) 
                (and 
                    (MS1 x188 X) 
                    (forall ((y Int)) 
                        (=> 
                            (MS1 y X) 
                            (= y x188)))))))
; Elementary Sets axiom (Singleton part)
(assert (forall ((x189 QUEUES)) 
            (exists ((X0 PQ)) 
                (and 
                    (MS x189 X0) 
                    (forall ((y0 QUEUES)) 
                        (=> 
                            (MS y0 X0) 
                            (= y0 x189)))))))
; Elementary Sets axiom (Singleton part)
(assert (forall ((x190 ENQUEUEABLE_ELEMENTS)) 
            (exists ((X1 PE)) 
                (and 
                    (MS0 x190 X1) 
                    (forall ((y1 ENQUEUEABLE_ELEMENTS)) 
                        (=> 
                            (MS0 y1 X1) 
                            (= y1 x190)))))))
(assert (! (and 
               (forall ((x ENQUEUEABLE_ELEMENTS) (x0 QUEUES) (x1 QUEUES)) 
                   (=> 
                       (Enqueue x x0 x1) 
                       (not 
                           (= x1 Empty_Queue)))) 
               (forall ((x2 ENQUEUEABLE_ELEMENTS) (x3 QUEUES) (x4 QUEUES) (x5 QUEUES)) 
                   (=> 
                       (and 
                           (Enqueue x2 x3 x4) 
                           (Enqueue x2 x3 x5)) 
                       (= x4 x5))) 
               (forall ((x6 ENQUEUEABLE_ELEMENTS) (x7 QUEUES)) 
                   (exists ((x8 QUEUES)) 
                       (Enqueue x6 x7 x8))) 
               (forall ((x9 QUEUES)) 
                   (=> 
                       (not 
                           (= x9 Empty_Queue)) 
                       (exists ((x10 ENQUEUEABLE_ELEMENTS) (x11 QUEUES)) 
                           (Enqueue x10 x11 x9)))) 
               (forall ((x12 QUEUES) (x13 ENQUEUEABLE_ELEMENTS) (x14 QUEUES) (x15 ENQUEUEABLE_ELEMENTS) (x16 QUEUES)) 
                   (=> 
                       (and 
                           (Enqueue x13 x14 x12) 
                           (Enqueue x15 x16 x12)) 
                       (and 
                           (= x13 x15) 
                           (= x14 x16)))))
         :named hyp1))
(assert (! (and 
               (forall ((x17 QUEUES) (x18 Int)) 
                   (=> 
                       (Length_of_Queue x17 x18) 
                       (<= 0 x18))) 
               (forall ((x19 QUEUES) (x20 Int) (x21 Int)) 
                   (=> 
                       (and 
                           (Length_of_Queue x19 x20) 
                           (Length_of_Queue x19 x21)) 
                       (= x20 x21))) 
               (forall ((x22 QUEUES)) 
                   (exists ((x23 Int)) 
                       (Length_of_Queue x22 x23))) 
               (forall ((x24 Int)) 
                   (=> 
                       (<= 0 x24) 
                       (exists ((x25 QUEUES)) 
                           (Length_of_Queue x25 x24)))))
         :named hyp2))
(assert (! (exists ((x26 Int)) 
               (and 
                   (= x26 0) 
                   (Length_of_Queue Empty_Queue x26)))
         :named hyp3))
(assert (! (and 
               (forall ((x27 Int) (x28 PQ)) 
                   (=> 
                       (Queues_of_Length x27 x28) 
                       (<= 0 x27))) 
               (forall ((x29 Int) (x30 PQ) (x31 PQ)) 
                   (=> 
                       (and 
                           (Queues_of_Length x29 x30) 
                           (Queues_of_Length x29 x31)) 
                       (forall ((x32 QUEUES)) 
                           (= 
                               (MS x32 x30) 
                               (MS x32 x31))))) 
               (forall ((x33 Int)) 
                   (=> 
                       (<= 0 x33) 
                       (exists ((x34 PQ)) 
                           (Queues_of_Length x33 x34)))))
         :named hyp4))
(assert (! (and 
               (forall ((x35 QUEUES) (x36 PE) (x37 PE)) 
                   (=> 
                       (and 
                           (Elements_of_Queue x35 x36) 
                           (Elements_of_Queue x35 x37)) 
                       (forall ((x38 ENQUEUEABLE_ELEMENTS)) 
                           (= 
                               (MS0 x38 x36) 
                               (MS0 x38 x37))))) 
               (forall ((x39 QUEUES)) 
                   (exists ((x40 PE)) 
                       (Elements_of_Queue x39 x40))))
         :named hyp5))
(assert (! (exists ((x41 PE)) 
               (and 
                   (forall ((x42 ENQUEUEABLE_ELEMENTS)) 
                       (not 
                           (MS0 x42 x41))) 
                   (Elements_of_Queue Empty_Queue x41)))
         :named hyp6))
(assert (! (and 
               (forall ((x43 QUEUES) (x44 PE) (x45 PE)) 
                   (=> 
                       (and 
                           (Duplicate_Elements_of_Queue x43 x44) 
                           (Duplicate_Elements_of_Queue x43 x45)) 
                       (forall ((x46 ENQUEUEABLE_ELEMENTS)) 
                           (= 
                               (MS0 x46 x44) 
                               (MS0 x46 x45))))) 
               (forall ((x47 QUEUES)) 
                   (exists ((x48 PE)) 
                       (Duplicate_Elements_of_Queue x47 x48))))
         :named hyp7))
(assert (! (exists ((x49 PE)) 
               (and 
                   (forall ((x50 ENQUEUEABLE_ELEMENTS)) 
                       (not 
                           (MS0 x50 x49))) 
                   (Duplicate_Elements_of_Queue Empty_Queue x49)))
         :named hyp8))
(assert (! (and 
               (forall ((x51 QUEUES) (x52 ENQUEUEABLE_ELEMENTS)) 
                   (=> 
                       (Head_of_Queue x51 x52) 
                       (not 
                           (= x51 Empty_Queue)))) 
               (forall ((x53 QUEUES) (x54 ENQUEUEABLE_ELEMENTS) (x55 ENQUEUEABLE_ELEMENTS)) 
                   (=> 
                       (and 
                           (Head_of_Queue x53 x54) 
                           (Head_of_Queue x53 x55)) 
                       (= x54 x55))) 
               (forall ((x56 QUEUES)) 
                   (=> 
                       (not 
                           (= x56 Empty_Queue)) 
                       (exists ((x57 ENQUEUEABLE_ELEMENTS)) 
                           (Head_of_Queue x56 x57)))))
         :named hyp9))
(assert (! (and 
               (forall ((x58 QUEUES) (x59 QUEUES)) 
                   (=> 
                       (Dequeue x58 x59) 
                       (not 
                           (= x58 Empty_Queue)))) 
               (forall ((x60 QUEUES) (x61 QUEUES) (x62 QUEUES)) 
                   (=> 
                       (and 
                           (Dequeue x60 x61) 
                           (Dequeue x60 x62)) 
                       (= x61 x62))) 
               (forall ((x63 QUEUES)) 
                   (=> 
                       (not 
                           (= x63 Empty_Queue)) 
                       (exists ((x64 QUEUES)) 
                           (Dequeue x63 x64)))))
         :named hyp10))
(assert (! (forall ((x65 Int)) 
               (=> 
                   (MS1 x65 MAGIC_LENGTHS) 
                   (<= 0 x65)))
         :named hyp11))
(assert (! (exists ((x66 Int)) 
               (and 
                   (= x66 0) 
                   (MS1 x66 MAGIC_LENGTHS)))
         :named hyp12))
(assert (! (exists ((x67 ENQUEUEABLE_ELEMENTS)) 
               (MS0 x67 ENQUEUEABLE_TC_BUFFER_ELEMENTS))
         :named hyp13))
(assert (! (exists ((x68 ENQUEUEABLE_ELEMENTS)) 
               (MS0 x68 ENQUEUEABLE_TM_BUFFER_ELEMENTS))
         :named hyp14))
(assert (! (exists ((x69 ENQUEUEABLE_ELEMENTS)) 
               (MS0 x69 ENQUEUEABLE_TC_POOL_ELEMENTS))
         :named hyp15))
(assert (! (exists ((x70 ENQUEUEABLE_ELEMENTS)) 
               (MS0 x70 ENQUEUEABLE_TM_POOL_ELEMENTS))
         :named hyp16))
(assert (! (forall ((x71 ENQUEUEABLE_ELEMENTS)) 
               (not 
                   (and 
                       (MS0 x71 ENQUEUEABLE_TC_BUFFER_ELEMENTS) 
                       (MS0 x71 ENQUEUEABLE_TM_BUFFER_ELEMENTS))))
         :named hyp17))
(assert (! (forall ((x72 ENQUEUEABLE_ELEMENTS)) 
               (not 
                   (and 
                       (MS0 x72 ENQUEUEABLE_TC_BUFFER_ELEMENTS) 
                       (MS0 x72 ENQUEUEABLE_TC_POOL_ELEMENTS))))
         :named hyp18))
(assert (! (forall ((x73 ENQUEUEABLE_ELEMENTS)) 
               (not 
                   (and 
                       (MS0 x73 ENQUEUEABLE_TC_BUFFER_ELEMENTS) 
                       (MS0 x73 ENQUEUEABLE_TM_POOL_ELEMENTS))))
         :named hyp19))
(assert (! (forall ((x74 ENQUEUEABLE_ELEMENTS)) 
               (not 
                   (and 
                       (MS0 x74 ENQUEUEABLE_TM_BUFFER_ELEMENTS) 
                       (MS0 x74 ENQUEUEABLE_TC_POOL_ELEMENTS))))
         :named hyp20))
(assert (! (forall ((x75 ENQUEUEABLE_ELEMENTS)) 
               (not 
                   (and 
                       (MS0 x75 ENQUEUEABLE_TM_BUFFER_ELEMENTS) 
                       (MS0 x75 ENQUEUEABLE_TM_POOL_ELEMENTS))))
         :named hyp21))
(assert (! (forall ((x76 ENQUEUEABLE_ELEMENTS)) 
               (not 
                   (and 
                       (MS0 x76 ENQUEUEABLE_TC_POOL_ELEMENTS) 
                       (MS0 x76 ENQUEUEABLE_TM_POOL_ELEMENTS))))
         :named hyp22))
(assert (! (and 
               (forall ((x77 ENQUEUEABLE_ELEMENTS) (x78 PACKET_START_ADDRESSES_IN_TC_BUFFER)) 
                   (=> 
                       (TC_Buffer_Element_Address x77 x78) 
                       (MS0 x77 ENQUEUEABLE_TC_BUFFER_ELEMENTS))) 
               (forall ((x79 ENQUEUEABLE_ELEMENTS) (x80 PACKET_START_ADDRESSES_IN_TC_BUFFER) (x81 PACKET_START_ADDRESSES_IN_TC_BUFFER)) 
                   (=> 
                       (and 
                           (TC_Buffer_Element_Address x79 x80) 
                           (TC_Buffer_Element_Address x79 x81)) 
                       (= x80 x81))) 
               (forall ((x82 ENQUEUEABLE_ELEMENTS)) 
                   (=> 
                       (MS0 x82 ENQUEUEABLE_TC_BUFFER_ELEMENTS) 
                       (exists ((x83 PACKET_START_ADDRESSES_IN_TC_BUFFER)) 
                           (TC_Buffer_Element_Address x82 x83)))) 
               (forall ((x84 PACKET_START_ADDRESSES_IN_TC_BUFFER)) 
                   (exists ((x85 ENQUEUEABLE_ELEMENTS)) 
                       (TC_Buffer_Element_Address x85 x84))) 
               (forall ((x86 PACKET_START_ADDRESSES_IN_TC_BUFFER) (x87 ENQUEUEABLE_ELEMENTS) (x88 ENQUEUEABLE_ELEMENTS)) 
                   (=> 
                       (and 
                           (TC_Buffer_Element_Address x87 x86) 
                           (TC_Buffer_Element_Address x88 x86)) 
                       (= x87 x88))))
         :named hyp23))
(assert (! (and 
               (forall ((x89 ENQUEUEABLE_ELEMENTS) (x90 PACKET_START_ADDRESSES_IN_TM_BUFFER)) 
                   (=> 
                       (TM_Buffer_Element_Address x89 x90) 
                       (MS0 x89 ENQUEUEABLE_TM_BUFFER_ELEMENTS))) 
               (forall ((x91 ENQUEUEABLE_ELEMENTS) (x92 PACKET_START_ADDRESSES_IN_TM_BUFFER) (x93 PACKET_START_ADDRESSES_IN_TM_BUFFER)) 
                   (=> 
                       (and 
                           (TM_Buffer_Element_Address x91 x92) 
                           (TM_Buffer_Element_Address x91 x93)) 
                       (= x92 x93))) 
               (forall ((x94 ENQUEUEABLE_ELEMENTS)) 
                   (=> 
                       (MS0 x94 ENQUEUEABLE_TM_BUFFER_ELEMENTS) 
                       (exists ((x95 PACKET_START_ADDRESSES_IN_TM_BUFFER)) 
                           (TM_Buffer_Element_Address x94 x95)))) 
               (forall ((x96 PACKET_START_ADDRESSES_IN_TM_BUFFER)) 
                   (exists ((x97 ENQUEUEABLE_ELEMENTS)) 
                       (TM_Buffer_Element_Address x97 x96))) 
               (forall ((x98 PACKET_START_ADDRESSES_IN_TM_BUFFER) (x99 ENQUEUEABLE_ELEMENTS) (x100 ENQUEUEABLE_ELEMENTS)) 
                   (=> 
                       (and 
                           (TM_Buffer_Element_Address x99 x98) 
                           (TM_Buffer_Element_Address x100 x98)) 
                       (= x99 x100))))
         :named hyp24))
(assert (! (and 
               (forall ((x101 ENQUEUEABLE_ELEMENTS) (x102 PACKET_START_ADDRESSES_IN_TC_POOL)) 
                   (=> 
                       (TC_Pool_Element_Address x101 x102) 
                       (MS0 x101 ENQUEUEABLE_TC_POOL_ELEMENTS))) 
               (forall ((x103 ENQUEUEABLE_ELEMENTS) (x104 PACKET_START_ADDRESSES_IN_TC_POOL) (x105 PACKET_START_ADDRESSES_IN_TC_POOL)) 
                   (=> 
                       (and 
                           (TC_Pool_Element_Address x103 x104) 
                           (TC_Pool_Element_Address x103 x105)) 
                       (= x104 x105))) 
               (forall ((x106 ENQUEUEABLE_ELEMENTS)) 
                   (=> 
                       (MS0 x106 ENQUEUEABLE_TC_POOL_ELEMENTS) 
                       (exists ((x107 PACKET_START_ADDRESSES_IN_TC_POOL)) 
                           (TC_Pool_Element_Address x106 x107)))) 
               (forall ((x108 PACKET_START_ADDRESSES_IN_TC_POOL)) 
                   (exists ((x109 ENQUEUEABLE_ELEMENTS)) 
                       (TC_Pool_Element_Address x109 x108))) 
               (forall ((x110 PACKET_START_ADDRESSES_IN_TC_POOL) (x111 ENQUEUEABLE_ELEMENTS) (x112 ENQUEUEABLE_ELEMENTS)) 
                   (=> 
                       (and 
                           (TC_Pool_Element_Address x111 x110) 
                           (TC_Pool_Element_Address x112 x110)) 
                       (= x111 x112))))
         :named hyp25))
(assert (! (and 
               (forall ((x113 ENQUEUEABLE_ELEMENTS) (x114 PACKET_START_ADDRESSES_IN_TM_POOL)) 
                   (=> 
                       (TM_Pool_Element_Address x113 x114) 
                       (MS0 x113 ENQUEUEABLE_TM_POOL_ELEMENTS))) 
               (forall ((x115 ENQUEUEABLE_ELEMENTS) (x116 PACKET_START_ADDRESSES_IN_TM_POOL) (x117 PACKET_START_ADDRESSES_IN_TM_POOL)) 
                   (=> 
                       (and 
                           (TM_Pool_Element_Address x115 x116) 
                           (TM_Pool_Element_Address x115 x117)) 
                       (= x116 x117))) 
               (forall ((x118 ENQUEUEABLE_ELEMENTS)) 
                   (=> 
                       (MS0 x118 ENQUEUEABLE_TM_POOL_ELEMENTS) 
                       (exists ((x119 PACKET_START_ADDRESSES_IN_TM_POOL)) 
                           (TM_Pool_Element_Address x118 x119)))) 
               (forall ((x120 PACKET_START_ADDRESSES_IN_TM_POOL)) 
                   (exists ((x121 ENQUEUEABLE_ELEMENTS)) 
                       (TM_Pool_Element_Address x121 x120))) 
               (forall ((x122 PACKET_START_ADDRESSES_IN_TM_POOL) (x123 ENQUEUEABLE_ELEMENTS) (x124 ENQUEUEABLE_ELEMENTS)) 
                   (=> 
                       (and 
                           (TM_Pool_Element_Address x123 x122) 
                           (TM_Pool_Element_Address x124 x122)) 
                       (= x123 x124))))
         :named hyp26))
(assert (! (forall ((s PZ)) 
               (=> 
                   (and 
                       (forall ((x125 Int)) 
                           (=> 
                               (MS1 x125 s) 
                               (<= 0 x125))) 
                       (exists ((x126 Int)) 
                           (and 
                               (= x126 0) 
                               (MS1 x126 s))) 
                       (not 
                           (forall ((x127 Int)) 
                               (=> 
                                   (<= 0 x127) 
                                   (MS1 x127 s))))) 
                   (exists ((x128 Int)) 
                       (and 
                           (forall ((x129 Int)) 
                               (=> 
                                   (and 
                                       (<= 0 x129) 
                                       (not 
                                           (MS1 x129 s)) 
                                       (forall ((x130 Int)) 
                                           (=> 
                                               (and 
                                                   (<= 0 x130) 
                                                   (not 
                                                       (MS1 x130 s))) 
                                               (<= x129 x130)))) 
                                   (= x128 (- x129 1)))) 
                           (MS1 x128 s)))))
         :named hyp27))
(assert (! (forall ((s0 PZ)) 
               (=> 
                   (and 
                       (forall ((x131 Int)) 
                           (=> 
                               (MS1 x131 s0) 
                               (<= 0 x131))) 
                       (exists ((x132 Int)) 
                           (and 
                               (= x132 0) 
                               (MS1 x132 s0))) 
                       (forall ((n Int)) 
                           (=> 
                               (MS1 n s0) 
                               (exists ((x133 Int)) 
                                   (and 
                                       (= x133 (+ n 1)) 
                                       (MS1 x133 s0)))))) 
                   (forall ((x134 Int)) 
                       (=> 
                           (<= 0 x134) 
                           (MS1 x134 s0)))))
         :named hyp28))
(assert (! (forall ((k Int) (q QUEUES)) 
               (=> 
                   (and 
                       (<= 0 k) 
                       (exists ((x135 PQ)) 
                           (and 
                               (Queues_of_Length k x135) 
                               (MS q x135)))) 
                   (Length_of_Queue q k)))
         :named hyp29))
(assert (! (forall ((k0 Int)) 
               (=> 
                   (and 
                       (MS1 k0 MAGIC_LENGTHS) 
                       (not 
                           (= k0 0))) 
                   (forall ((q0 QUEUES)) 
                       (=> 
                           (exists ((x136 PQ)) 
                               (and 
                                   (Queues_of_Length k0 x136) 
                                   (MS q0 x136))) 
                           (and 
                               (exists ((x137 PE)) 
                                   (and 
                                       (forall ((x138 ENQUEUEABLE_ELEMENTS)) 
                                           (= 
                                               (MS0 x138 x137) 
                                               (or 
                                                   (Head_of_Queue q0 x138) 
                                                   (exists ((x139 PE)) 
                                                       (and 
                                                           (exists ((x140 QUEUES)) 
                                                               (and 
                                                                   (Dequeue q0 x140) 
                                                                   (Elements_of_Queue x140 x139))) 
                                                           (MS0 x138 x139)))))) 
                                       (Elements_of_Queue q0 x137))) 
                               (exists ((x141 PE)) 
                                   (and 
                                       (forall ((x142 ENQUEUEABLE_ELEMENTS)) 
                                           (= 
                                               (MS0 x142 x141) 
                                               (or 
                                                   (and 
                                                       (Head_of_Queue q0 x142) 
                                                       (exists ((x143 PE)) 
                                                           (and 
                                                               (exists ((x144 QUEUES)) 
                                                                   (and 
                                                                       (Dequeue q0 x144) 
                                                                       (Elements_of_Queue x144 x143))) 
                                                               (MS0 x142 x143)))) 
                                                   (exists ((x145 PE)) 
                                                       (and 
                                                           (exists ((x146 QUEUES)) 
                                                               (and 
                                                                   (Dequeue q0 x146) 
                                                                   (Duplicate_Elements_of_Queue x146 x145))) 
                                                           (MS0 x142 x145)))))) 
                                       (Duplicate_Elements_of_Queue q0 x141))))))))
         :named hyp30))
(assert (! (forall ((k1 Int)) 
               (=> 
                   (and 
                       (<= 0 k1) 
                       (not 
                           (= k1 0)) 
                       (forall ((q1 QUEUES)) 
                           (=> 
                               (exists ((x147 PQ)) 
                                   (and 
                                       (Queues_of_Length k1 x147) 
                                       (MS q1 x147))) 
                               (and 
                                   (exists ((x148 PE)) 
                                       (and 
                                           (forall ((x149 ENQUEUEABLE_ELEMENTS)) 
                                               (= 
                                                   (MS0 x149 x148) 
                                                   (or 
                                                       (Head_of_Queue q1 x149) 
                                                       (exists ((x150 PE)) 
                                                           (and 
                                                               (exists ((x151 QUEUES)) 
                                                                   (and 
                                                                       (Dequeue q1 x151) 
                                                                       (Elements_of_Queue x151 x150))) 
                                                               (MS0 x149 x150)))))) 
                                           (Elements_of_Queue q1 x148))) 
                                   (exists ((x152 PE)) 
                                       (and 
                                           (forall ((x153 ENQUEUEABLE_ELEMENTS)) 
                                               (= 
                                                   (MS0 x153 x152) 
                                                   (or 
                                                       (and 
                                                           (Head_of_Queue q1 x153) 
                                                           (exists ((x154 PE)) 
                                                               (and 
                                                                   (exists ((x155 QUEUES)) 
                                                                       (and 
                                                                           (Dequeue q1 x155) 
                                                                           (Elements_of_Queue x155 x154))) 
                                                                   (MS0 x153 x154)))) 
                                                       (exists ((x156 PE)) 
                                                           (and 
                                                               (exists ((x157 QUEUES)) 
                                                                   (and 
                                                                       (Dequeue q1 x157) 
                                                                       (Duplicate_Elements_of_Queue x157 x156))) 
                                                               (MS0 x153 x156)))))) 
                                           (Duplicate_Elements_of_Queue q1 x152))))))) 
                   (MS1 k1 MAGIC_LENGTHS)))
         :named hyp31))
(assert (! (forall ((k2 Int)) 
               (=> 
                   (and 
                       (<= 0 k2) 
                       (not 
                           (= k2 0))) 
                   (<= 0 (- k2 1))))
         :named hyp32))
(assert (! (forall ((t PZ)) 
               (=> 
                   (and 
                       (forall ((x158 Int)) 
                           (=> 
                               (MS1 x158 t) 
                               (<= 0 x158))) 
                       (not 
                           (forall ((x159 Int)) 
                               (not 
                                   (MS1 x159 t))))) 
                   (exists ((x160 Int)) 
                       (and 
                           (MS1 x160 t) 
                           (forall ((x161 Int)) 
                               (=> 
                                   (MS1 x161 t) 
                                   (<= x160 x161)))))))
         :named hyp33))
(assert (! (forall ((t0 PZ)) 
               (=> 
                   (and 
                       (forall ((x162 Int)) 
                           (=> 
                               (MS1 x162 t0) 
                               (<= 0 x162))) 
                       (not 
                           (forall ((x163 Int)) 
                               (not 
                                   (MS1 x163 t0))))) 
                   (forall ((x164 Int)) 
                       (=> 
                           (MS1 x164 t0) 
                           (exists ((x165 Int)) 
                               (and 
                                   (MS1 x165 t0) 
                                   (<= x165 x164)))))))
         :named hyp34))
(assert (! (forall ((a ENQUEUEABLE_ELEMENTS)) 
               (exists ((x166 QUEUES)) 
                   (and 
                       (Enqueue a Empty_Queue x166) 
                       (Head_of_Queue x166 a))))
         :named hyp35))
(assert (! (forall ((a0 ENQUEUEABLE_ELEMENTS)) 
               (exists ((x167 QUEUES)) 
                   (and 
                       (Enqueue a0 Empty_Queue x167) 
                       (Dequeue x167 Empty_Queue))))
         :named hyp36))
(assert (! (forall ((a1 ENQUEUEABLE_ELEMENTS) (q2 QUEUES)) 
               (exists ((x168 QUEUES) (x169 Int)) 
                   (and 
                       (Enqueue a1 q2 x168) 
                       (forall ((x170 Int)) 
                           (=> 
                               (Length_of_Queue q2 x170) 
                               (= x169 (+ x170 1)))) 
                       (Length_of_Queue x168 x169))))
         :named hyp37))
(assert (! (forall ((k3 Int) (q3 QUEUES)) 
               (=> 
                   (and 
                       (<= 0 k3) 
                       (Length_of_Queue q3 k3)) 
                   (exists ((x171 PQ)) 
                       (and 
                           (Queues_of_Length k3 x171) 
                           (MS q3 x171)))))
         :named hyp38))
(assert (! (forall ((a2 ENQUEUEABLE_ELEMENTS) (q4 QUEUES)) 
               (exists ((x172 QUEUES) (x173 PE)) 
                   (and 
                       (Enqueue a2 q4 x172) 
                       (forall ((x174 ENQUEUEABLE_ELEMENTS)) 
                           (= 
                               (MS0 x174 x173) 
                               (or 
                                   (= x174 a2) 
                                   (exists ((x175 PE)) 
                                       (and 
                                           (Elements_of_Queue q4 x175) 
                                           (MS0 x174 x175)))))) 
                       (Elements_of_Queue x172 x173))))
         :named hyp39))
(assert (! (forall ((a3 ENQUEUEABLE_ELEMENTS) (q5 QUEUES)) 
               (exists ((x176 QUEUES) (x177 PE)) 
                   (and 
                       (Enqueue a3 q5 x176) 
                       (forall ((x178 ENQUEUEABLE_ELEMENTS)) 
                           (= 
                               (MS0 x178 x177) 
                               (or 
                                   (and 
                                       (= x178 a3) 
                                       (exists ((x179 PE)) 
                                           (and 
                                               (Elements_of_Queue q5 x179) 
                                               (MS0 x178 x179)))) 
                                   (exists ((x180 PE)) 
                                       (and 
                                           (Duplicate_Elements_of_Queue q5 x180) 
                                           (MS0 x178 x180)))))) 
                       (Duplicate_Elements_of_Queue x176 x177))))
         :named hyp40))
(assert (! (forall ((a4 ENQUEUEABLE_ELEMENTS) (q6 QUEUES)) 
               (=> 
                   (not 
                       (= q6 Empty_Queue)) 
                   (exists ((x181 QUEUES) (x182 ENQUEUEABLE_ELEMENTS)) 
                       (and 
                           (Enqueue a4 q6 x181) 
                           (Head_of_Queue q6 x182) 
                           (Head_of_Queue x181 x182)))))
         :named hyp41))
(assert (! (forall ((a5 ENQUEUEABLE_ELEMENTS) (q7 QUEUES)) 
               (=> 
                   (not 
                       (= q7 Empty_Queue)) 
                   (exists ((x183 QUEUES) (x184 QUEUES)) 
                       (and 
                           (Enqueue a5 q7 x183) 
                           (exists ((x185 QUEUES)) 
                               (and 
                                   (Dequeue q7 x185) 
                                   (Enqueue a5 x185 x184))) 
                           (Dequeue x183 x184)))))
         :named hyp42))
(assert (! (not 
               (exists ((x186 PQ) (x187 Int)) 
                   (and 
                       (= x187 0) 
                       (Queues_of_Length x187 x186))))
         :named goal))
(check-sat)
(exit)

