(set-info :smt-lib-version 2.6)
(set-logic AUFLIA)
(set-info :source |Generator: Rodin SMT Plug-in|)
(set-info :license "https://creativecommons.org/licenses/by-nc/4.0/")
(set-info :category "industrial")
(set-info :status unsat)

(declare-sort ABSTRACT_TM_SIZES 0)
(declare-sort ENQUEUEABLE_ELEMENTS 0)
(declare-sort PACKET_START_ADDRESSES_IN_TM_POOL 0)
(declare-sort PE 0)
(declare-sort PIDS 0)
(declare-sort PP 0)
(declare-sort PQ 0)
(declare-sort QUEUES 0)
(declare-sort TC_SET 0)
(declare-sort TC_STATUSES 0)
(declare-sort TM_PRIORITIES 0)
(declare-sort TM_SET 0)
(declare-sort TM_STATUSES 0)
(declare-fun Abstract_Size_of_TM (TM_SET ABSTRACT_TM_SIZES) Bool)
(declare-fun Abstract_Slot_Size_in_TM_Pool (PACKET_START_ADDRESSES_IN_TM_POOL ABSTRACT_TM_SIZES) Bool)
(declare-fun Duplicate_Elements_of_Queue (QUEUES PE) Bool)
(declare-fun Elements_of_Queue (QUEUES PE) Bool)
(declare-fun Enqueue (ENQUEUEABLE_ELEMENTS QUEUES QUEUES) Bool)
(declare-fun Head_of_Queue (QUEUES ENQUEUEABLE_ELEMENTS) Bool)
(declare-fun Length_of_Queue (QUEUES Int) Bool)
(declare-fun MS (PIDS PP) Bool)
(declare-fun MS0 (QUEUES PQ) Bool)
(declare-fun MS1 (ENQUEUEABLE_ELEMENTS PE) Bool)
(declare-fun Pid_of_TC (TC_SET PIDS) Bool)
(declare-fun Pid_of_TM (TM_SET PIDS) Bool)
(declare-fun Priority_of_TM (TM_SET TM_PRIORITIES) Bool)
(declare-fun Queues_of_Length (Int PQ) Bool)
(declare-fun Slot_Pids_in_TM_Pool (PACKET_START_ADDRESSES_IN_TM_POOL PP) Bool)
(declare-fun Slot_Priority_in_TM_Pool (PACKET_START_ADDRESSES_IN_TM_POOL TM_PRIORITIES) Bool)
(declare-fun VALID_TCS (TC_SET) Bool)
(declare-fun ASW_PIDS () PP)
(declare-fun Empty_Queue () QUEUES)
(declare-fun High_Priority_TM () TM_PRIORITIES)
(declare-fun Long_TM () ABSTRACT_TM_SIZES)
(declare-fun Low_Priority_TM () TM_PRIORITIES)
(declare-fun Medium_Priority_TM () TM_PRIORITIES)
(declare-fun Short_TM () ABSTRACT_TM_SIZES)
(declare-fun TC_Accepted () TC_STATUSES)
(declare-fun TC_Execution_Failed () TC_STATUSES)
(declare-fun TC_Rejected () TC_STATUSES)
(declare-fun TC_Removable () TC_STATUSES)
(declare-fun TC_Successfully_Executed () TC_STATUSES)
(declare-fun TC_Unchecked () TC_STATUSES)
(declare-fun TC_Waiting_for_Execution () TC_STATUSES)
(declare-fun TM_Effective () TM_STATUSES)
(declare-fun TM_Removable () TM_STATUSES)
(declare-fun csw () PIDS)
(declare-fun mixsc () PIDS)
(declare-fun mixst () PIDS)
(declare-fun q () QUEUES)
(declare-fun sixsp () PIDS)
(declare-fun sixsx () PIDS)

; Elementary Sets axiom (Singleton part)
(assert (forall ((x165 QUEUES)) 
            (exists ((X PQ)) 
                (and 
                    (MS0 x165 X) 
                    (forall ((y QUEUES)) 
                        (=> 
                            (MS0 y X) 
                            (= y x165)))))))
; Elementary Sets axiom (Singleton part)
(assert (forall ((x166 ENQUEUEABLE_ELEMENTS)) 
            (exists ((X0 PE)) 
                (and 
                    (MS1 x166 X0) 
                    (forall ((y0 ENQUEUEABLE_ELEMENTS)) 
                        (=> 
                            (MS1 y0 X0) 
                            (= y0 x166)))))))
; Elementary Sets axiom (Singleton part)
(assert (forall ((x167 PIDS)) 
            (exists ((X1 PP)) 
                (and 
                    (MS x167 X1) 
                    (forall ((y1 PIDS)) 
                        (=> 
                            (MS y1 X1) 
                            (= y1 x167)))))))
(assert (! (forall ((x TC_STATUSES)) 
               (or 
                   (= x TC_Unchecked) 
                   (= x TC_Accepted) 
                   (= x TC_Rejected) 
                   (= x TC_Waiting_for_Execution) 
                   (= x TC_Successfully_Executed) 
                   (= x TC_Execution_Failed) 
                   (= x TC_Removable)))
         :named hyp1))
(assert (! (forall ((x0 TM_STATUSES)) 
               (or 
                   (= x0 TM_Effective) 
                   (= x0 TM_Removable)))
         :named hyp2))
(assert (! (forall ((x1 PIDS)) 
               (or 
                   (= x1 csw) 
                   (= x1 mixsc) 
                   (= x1 mixst) 
                   (= x1 sixsp) 
                   (= x1 sixsx)))
         :named hyp3))
(assert (! (forall ((x2 PIDS)) 
               (= 
                   (MS x2 ASW_PIDS) 
                   (not 
                       (= x2 csw))))
         :named hyp4))
(assert (! (and 
               (forall ((x3 TC_SET) (x4 PIDS)) 
                   (=> 
                       (Pid_of_TC x3 x4) 
                       (VALID_TCS x3))) 
               (forall ((x5 TC_SET) (x6 PIDS) (x7 PIDS)) 
                   (=> 
                       (and 
                           (Pid_of_TC x5 x6) 
                           (Pid_of_TC x5 x7)) 
                       (= x6 x7))) 
               (forall ((x8 TC_SET)) 
                   (=> 
                       (VALID_TCS x8) 
                       (exists ((x9 PIDS)) 
                           (Pid_of_TC x8 x9)))) 
               (forall ((x10 PIDS)) 
                   (exists ((x11 TC_SET)) 
                       (Pid_of_TC x11 x10))))
         :named hyp5))
(assert (! (and 
               (forall ((x12 TM_SET) (x13 PIDS) (x14 PIDS)) 
                   (=> 
                       (and 
                           (Pid_of_TM x12 x13) 
                           (Pid_of_TM x12 x14)) 
                       (= x13 x14))) 
               (forall ((x15 TM_SET)) 
                   (exists ((x16 PIDS)) 
                       (Pid_of_TM x15 x16))) 
               (forall ((x17 PIDS)) 
                   (exists ((x18 TM_SET)) 
                       (Pid_of_TM x18 x17))))
         :named hyp6))
(assert (! (forall ((x19 TM_PRIORITIES)) 
               (or 
                   (= x19 High_Priority_TM) 
                   (= x19 Medium_Priority_TM) 
                   (= x19 Low_Priority_TM)))
         :named hyp7))
(assert (! (forall ((x20 ABSTRACT_TM_SIZES)) 
               (or 
                   (= x20 Short_TM) 
                   (= x20 Long_TM)))
         :named hyp8))
(assert (! (and 
               (forall ((x21 TM_SET) (x22 TM_PRIORITIES) (x23 TM_PRIORITIES)) 
                   (=> 
                       (and 
                           (Priority_of_TM x21 x22) 
                           (Priority_of_TM x21 x23)) 
                       (= x22 x23))) 
               (forall ((x24 TM_SET)) 
                   (exists ((x25 TM_PRIORITIES)) 
                       (Priority_of_TM x24 x25))) 
               (forall ((x26 TM_PRIORITIES)) 
                   (exists ((x27 TM_SET)) 
                       (Priority_of_TM x27 x26))))
         :named hyp9))
(assert (! (and 
               (forall ((x28 TM_SET) (x29 ABSTRACT_TM_SIZES) (x30 ABSTRACT_TM_SIZES)) 
                   (=> 
                       (and 
                           (Abstract_Size_of_TM x28 x29) 
                           (Abstract_Size_of_TM x28 x30)) 
                       (= x29 x30))) 
               (forall ((x31 TM_SET)) 
                   (exists ((x32 ABSTRACT_TM_SIZES)) 
                       (Abstract_Size_of_TM x31 x32))) 
               (forall ((x33 ABSTRACT_TM_SIZES)) 
                   (exists ((x34 TM_SET)) 
                       (Abstract_Size_of_TM x34 x33))))
         :named hyp10))
(assert (! (and 
               (forall ((x35 PACKET_START_ADDRESSES_IN_TM_POOL) (x36 TM_PRIORITIES) (x37 TM_PRIORITIES)) 
                   (=> 
                       (and 
                           (Slot_Priority_in_TM_Pool x35 x36) 
                           (Slot_Priority_in_TM_Pool x35 x37)) 
                       (= x36 x37))) 
               (forall ((x38 PACKET_START_ADDRESSES_IN_TM_POOL)) 
                   (exists ((x39 TM_PRIORITIES)) 
                       (Slot_Priority_in_TM_Pool x38 x39))) 
               (forall ((x40 TM_PRIORITIES)) 
                   (exists ((x41 PACKET_START_ADDRESSES_IN_TM_POOL)) 
                       (Slot_Priority_in_TM_Pool x41 x40))))
         :named hyp11))
(assert (! (and 
               (forall ((x42 PACKET_START_ADDRESSES_IN_TM_POOL) (x43 ABSTRACT_TM_SIZES) (x44 ABSTRACT_TM_SIZES)) 
                   (=> 
                       (and 
                           (Abstract_Slot_Size_in_TM_Pool x42 x43) 
                           (Abstract_Slot_Size_in_TM_Pool x42 x44)) 
                       (= x43 x44))) 
               (forall ((x45 PACKET_START_ADDRESSES_IN_TM_POOL)) 
                   (exists ((x46 ABSTRACT_TM_SIZES)) 
                       (Abstract_Slot_Size_in_TM_Pool x45 x46))) 
               (forall ((x47 ABSTRACT_TM_SIZES)) 
                   (exists ((x48 PACKET_START_ADDRESSES_IN_TM_POOL)) 
                       (Abstract_Slot_Size_in_TM_Pool x48 x47))))
         :named hyp12))
(assert (! (and 
               (forall ((x49 PACKET_START_ADDRESSES_IN_TM_POOL) (x50 PP)) 
                   (=> 
                       (Slot_Pids_in_TM_Pool x49 x50) 
                       (or 
                           (forall ((x51 PIDS)) 
                               (= 
                                   (MS x51 x50) 
                                   (= x51 csw))) 
                           (forall ((x52 PIDS)) 
                               (= 
                                   (MS x52 x50) 
                                   (= x52 mixsc))) 
                           (forall ((x53 PIDS)) 
                               (= 
                                   (MS x53 x50) 
                                   (= x53 mixst))) 
                           (forall ((x54 PIDS)) 
                               (= 
                                   (MS x54 x50) 
                                   (= x54 sixsp))) 
                           (forall ((x55 PIDS)) 
                               (= 
                                   (MS x55 x50) 
                                   (= x55 sixsx))) 
                           (forall ((x56 PIDS)) 
                               (= 
                                   (MS x56 x50) 
                                   (or 
                                       (= x56 csw) 
                                       (= x56 mixsc) 
                                       (= x56 mixst) 
                                       (= x56 sixsp) 
                                       (= x56 sixsx))))))) 
               (forall ((x57 PACKET_START_ADDRESSES_IN_TM_POOL) (x58 PP) (x59 PP)) 
                   (=> 
                       (and 
                           (Slot_Pids_in_TM_Pool x57 x58) 
                           (Slot_Pids_in_TM_Pool x57 x59)) 
                       (forall ((x60 PIDS)) 
                           (= 
                               (MS x60 x58) 
                               (MS x60 x59))))) 
               (forall ((x61 PACKET_START_ADDRESSES_IN_TM_POOL)) 
                   (exists ((x62 PP)) 
                       (Slot_Pids_in_TM_Pool x61 x62))) 
               (forall ((x63 PP)) 
                   (=> 
                       (or 
                           (forall ((x64 PIDS)) 
                               (= 
                                   (MS x64 x63) 
                                   (= x64 csw))) 
                           (forall ((x65 PIDS)) 
                               (= 
                                   (MS x65 x63) 
                                   (= x65 mixsc))) 
                           (forall ((x66 PIDS)) 
                               (= 
                                   (MS x66 x63) 
                                   (= x66 mixst))) 
                           (forall ((x67 PIDS)) 
                               (= 
                                   (MS x67 x63) 
                                   (= x67 sixsp))) 
                           (forall ((x68 PIDS)) 
                               (= 
                                   (MS x68 x63) 
                                   (= x68 sixsx))) 
                           (forall ((x69 PIDS)) 
                               (= 
                                   (MS x69 x63) 
                                   (or 
                                       (= x69 csw) 
                                       (= x69 mixsc) 
                                       (= x69 mixst) 
                                       (= x69 sixsp) 
                                       (= x69 sixsx))))) 
                       (exists ((x70 PACKET_START_ADDRESSES_IN_TM_POOL)) 
                           (Slot_Pids_in_TM_Pool x70 x63)))))
         :named hyp13))
(assert (! (and 
               (forall ((x71 ENQUEUEABLE_ELEMENTS) (x72 QUEUES) (x73 QUEUES)) 
                   (=> 
                       (Enqueue x71 x72 x73) 
                       (not 
                           (= x73 Empty_Queue)))) 
               (forall ((x74 ENQUEUEABLE_ELEMENTS) (x75 QUEUES) (x76 QUEUES) (x77 QUEUES)) 
                   (=> 
                       (and 
                           (Enqueue x74 x75 x76) 
                           (Enqueue x74 x75 x77)) 
                       (= x76 x77))) 
               (forall ((x78 ENQUEUEABLE_ELEMENTS) (x79 QUEUES)) 
                   (exists ((x80 QUEUES)) 
                       (Enqueue x78 x79 x80))) 
               (forall ((x81 QUEUES)) 
                   (=> 
                       (not 
                           (= x81 Empty_Queue)) 
                       (exists ((x82 ENQUEUEABLE_ELEMENTS) (x83 QUEUES)) 
                           (Enqueue x82 x83 x81)))) 
               (forall ((x84 QUEUES) (x85 ENQUEUEABLE_ELEMENTS) (x86 QUEUES) (x87 ENQUEUEABLE_ELEMENTS) (x88 QUEUES)) 
                   (=> 
                       (and 
                           (Enqueue x85 x86 x84) 
                           (Enqueue x87 x88 x84)) 
                       (and 
                           (= x85 x87) 
                           (= x86 x88)))))
         :named hyp14))
(assert (! (and 
               (forall ((x89 QUEUES) (x90 Int)) 
                   (=> 
                       (Length_of_Queue x89 x90) 
                       (<= 0 x90))) 
               (forall ((x91 QUEUES) (x92 Int) (x93 Int)) 
                   (=> 
                       (and 
                           (Length_of_Queue x91 x92) 
                           (Length_of_Queue x91 x93)) 
                       (= x92 x93))) 
               (forall ((x94 QUEUES)) 
                   (exists ((x95 Int)) 
                       (Length_of_Queue x94 x95))) 
               (forall ((x96 Int)) 
                   (=> 
                       (<= 0 x96) 
                       (exists ((x97 QUEUES)) 
                           (Length_of_Queue x97 x96)))))
         :named hyp15))
(assert (! (exists ((x98 Int)) 
               (and 
                   (= x98 0) 
                   (Length_of_Queue Empty_Queue x98)))
         :named hyp16))
(assert (! (exists ((x99 Int)) 
               (Length_of_Queue Empty_Queue x99))
         :named hyp17))
(assert (! (forall ((x100 QUEUES) (x101 Int) (x102 Int)) 
               (=> 
                   (and 
                       (Length_of_Queue x100 x101) 
                       (Length_of_Queue x100 x102)) 
                   (= x101 x102)))
         :named hyp18))
(assert (! (and 
               (forall ((x103 Int) (x104 PQ)) 
                   (=> 
                       (Queues_of_Length x103 x104) 
                       (<= 0 x103))) 
               (forall ((x105 Int) (x106 PQ) (x107 PQ)) 
                   (=> 
                       (and 
                           (Queues_of_Length x105 x106) 
                           (Queues_of_Length x105 x107)) 
                       (forall ((x108 QUEUES)) 
                           (= 
                               (MS0 x108 x106) 
                               (MS0 x108 x107))))) 
               (forall ((x109 Int)) 
                   (=> 
                       (<= 0 x109) 
                       (exists ((x110 PQ)) 
                           (Queues_of_Length x109 x110)))))
         :named hyp19))
(assert (! (and 
               (forall ((x111 QUEUES) (x112 PE) (x113 PE)) 
                   (=> 
                       (and 
                           (Elements_of_Queue x111 x112) 
                           (Elements_of_Queue x111 x113)) 
                       (forall ((x114 ENQUEUEABLE_ELEMENTS)) 
                           (= 
                               (MS1 x114 x112) 
                               (MS1 x114 x113))))) 
               (forall ((x115 QUEUES)) 
                   (exists ((x116 PE)) 
                       (Elements_of_Queue x115 x116))))
         :named hyp20))
(assert (! (exists ((x117 PE)) 
               (and 
                   (forall ((x118 ENQUEUEABLE_ELEMENTS)) 
                       (not 
                           (MS1 x118 x117))) 
                   (Elements_of_Queue Empty_Queue x117)))
         :named hyp21))
(assert (! (exists ((x119 PE)) 
               (Elements_of_Queue Empty_Queue x119))
         :named hyp22))
(assert (! (forall ((x120 QUEUES) (x121 PE) (x122 PE)) 
               (=> 
                   (and 
                       (Elements_of_Queue x120 x121) 
                       (Elements_of_Queue x120 x122)) 
                   (forall ((x123 ENQUEUEABLE_ELEMENTS)) 
                       (= 
                           (MS1 x123 x121) 
                           (MS1 x123 x122)))))
         :named hyp23))
(assert (! (and 
               (forall ((x124 QUEUES) (x125 PE) (x126 PE)) 
                   (=> 
                       (and 
                           (Duplicate_Elements_of_Queue x124 x125) 
                           (Duplicate_Elements_of_Queue x124 x126)) 
                       (forall ((x127 ENQUEUEABLE_ELEMENTS)) 
                           (= 
                               (MS1 x127 x125) 
                               (MS1 x127 x126))))) 
               (forall ((x128 QUEUES)) 
                   (exists ((x129 PE)) 
                       (Duplicate_Elements_of_Queue x128 x129))))
         :named hyp24))
(assert (! (exists ((x130 PE)) 
               (and 
                   (forall ((x131 ENQUEUEABLE_ELEMENTS)) 
                       (not 
                           (MS1 x131 x130))) 
                   (Duplicate_Elements_of_Queue Empty_Queue x130)))
         :named hyp25))
(assert (! (exists ((x132 PE)) 
               (Duplicate_Elements_of_Queue Empty_Queue x132))
         :named hyp26))
(assert (! (forall ((x133 QUEUES) (x134 PE) (x135 PE)) 
               (=> 
                   (and 
                       (Duplicate_Elements_of_Queue x133 x134) 
                       (Duplicate_Elements_of_Queue x133 x135)) 
                   (forall ((x136 ENQUEUEABLE_ELEMENTS)) 
                       (= 
                           (MS1 x136 x134) 
                           (MS1 x136 x135)))))
         :named hyp27))
(assert (! (and 
               (forall ((x137 QUEUES) (x138 ENQUEUEABLE_ELEMENTS)) 
                   (=> 
                       (Head_of_Queue x137 x138) 
                       (not 
                           (= x137 Empty_Queue)))) 
               (forall ((x139 QUEUES) (x140 ENQUEUEABLE_ELEMENTS) (x141 ENQUEUEABLE_ELEMENTS)) 
                   (=> 
                       (and 
                           (Head_of_Queue x139 x140) 
                           (Head_of_Queue x139 x141)) 
                       (= x140 x141))) 
               (forall ((x142 QUEUES)) 
                   (=> 
                       (not 
                           (= x142 Empty_Queue)) 
                       (exists ((x143 ENQUEUEABLE_ELEMENTS)) 
                           (Head_of_Queue x142 x143)))))
         :named hyp28))
(assert (! (not 
               (forall ((x144 TC_SET)) 
                   (VALID_TCS x144)))
         :named hyp29))
(assert (! (not 
               (= TC_Unchecked TC_Accepted))
         :named hyp30))
(assert (! (not 
               (= TC_Unchecked TC_Rejected))
         :named hyp31))
(assert (! (not 
               (= TC_Unchecked TC_Waiting_for_Execution))
         :named hyp32))
(assert (! (not 
               (= TC_Unchecked TC_Successfully_Executed))
         :named hyp33))
(assert (! (not 
               (= TC_Unchecked TC_Execution_Failed))
         :named hyp34))
(assert (! (not 
               (= TC_Unchecked TC_Removable))
         :named hyp35))
(assert (! (not 
               (= TC_Accepted TC_Rejected))
         :named hyp36))
(assert (! (not 
               (= TC_Accepted TC_Waiting_for_Execution))
         :named hyp37))
(assert (! (not 
               (= TC_Accepted TC_Successfully_Executed))
         :named hyp38))
(assert (! (not 
               (= TC_Accepted TC_Execution_Failed))
         :named hyp39))
(assert (! (not 
               (= TC_Accepted TC_Removable))
         :named hyp40))
(assert (! (not 
               (= TC_Rejected TC_Waiting_for_Execution))
         :named hyp41))
(assert (! (not 
               (= TC_Rejected TC_Successfully_Executed))
         :named hyp42))
(assert (! (not 
               (= TC_Rejected TC_Execution_Failed))
         :named hyp43))
(assert (! (not 
               (= TC_Rejected TC_Removable))
         :named hyp44))
(assert (! (not 
               (= TC_Waiting_for_Execution TC_Successfully_Executed))
         :named hyp45))
(assert (! (not 
               (= TC_Waiting_for_Execution TC_Execution_Failed))
         :named hyp46))
(assert (! (not 
               (= TC_Waiting_for_Execution TC_Removable))
         :named hyp47))
(assert (! (not 
               (= TC_Successfully_Executed TC_Execution_Failed))
         :named hyp48))
(assert (! (not 
               (= TC_Successfully_Executed TC_Removable))
         :named hyp49))
(assert (! (not 
               (= TC_Execution_Failed TC_Removable))
         :named hyp50))
(assert (! (not 
               (= TM_Effective TM_Removable))
         :named hyp51))
(assert (! (not 
               (= csw mixsc))
         :named hyp52))
(assert (! (not 
               (= csw mixst))
         :named hyp53))
(assert (! (not 
               (= csw sixsp))
         :named hyp54))
(assert (! (not 
               (= csw sixsx))
         :named hyp55))
(assert (! (not 
               (= mixsc mixst))
         :named hyp56))
(assert (! (not 
               (= mixsc sixsp))
         :named hyp57))
(assert (! (not 
               (= mixsc sixsx))
         :named hyp58))
(assert (! (not 
               (= mixst sixsp))
         :named hyp59))
(assert (! (not 
               (= mixst sixsx))
         :named hyp60))
(assert (! (not 
               (= sixsp sixsx))
         :named hyp61))
(assert (! (not 
               (= High_Priority_TM Medium_Priority_TM))
         :named hyp62))
(assert (! (not 
               (= High_Priority_TM Low_Priority_TM))
         :named hyp63))
(assert (! (not 
               (= Medium_Priority_TM Low_Priority_TM))
         :named hyp64))
(assert (! (not 
               (= Short_TM Long_TM))
         :named hyp65))
(assert (! (forall ((k Int) (q0 QUEUES)) 
               (=> 
                   (and 
                       (<= 0 k) 
                       (exists ((x145 PQ)) 
                           (and 
                               (Queues_of_Length k x145) 
                               (MS0 q0 x145)))) 
                   (Length_of_Queue q0 k)))
         :named hyp66))
(assert (! (forall ((a PACKET_START_ADDRESSES_IN_TM_POOL)) 
               (=> 
                   (Abstract_Slot_Size_in_TM_Pool a Long_TM) 
                   (Slot_Priority_in_TM_Pool a Low_Priority_TM)))
         :named hyp67))
(assert (! (forall ((a0 ENQUEUEABLE_ELEMENTS)) 
               (exists ((x146 QUEUES)) 
                   (and 
                       (Enqueue a0 Empty_Queue x146) 
                       (Head_of_Queue x146 a0))))
         :named hyp68))
(assert (! (forall ((a1 PACKET_START_ADDRESSES_IN_TM_POOL)) 
               (=> 
                   (Slot_Priority_in_TM_Pool a1 Medium_Priority_TM) 
                   (not 
                       (exists ((x147 PP)) 
                           (and 
                               (forall ((x148 PIDS)) 
                                   (= 
                                       (MS x148 x147) 
                                       (= x148 csw))) 
                               (Slot_Pids_in_TM_Pool a1 x147))))))
         :named hyp69))
(assert (! (forall ((pri TM_PRIORITIES) (size ABSTRACT_TM_SIZES) (pid PIDS)) 
               (=> 
                   (and 
                       (or 
                           (not 
                               (= size Long_TM)) 
                           (= pri Low_Priority_TM)) 
                       (or 
                           (not 
                               (= pri Medium_Priority_TM)) 
                           (not 
                               (= pid csw)))) 
                   (exists ((a2 PACKET_START_ADDRESSES_IN_TM_POOL)) 
                       (and 
                           (Slot_Priority_in_TM_Pool a2 pri) 
                           (Abstract_Slot_Size_in_TM_Pool a2 size) 
                           (exists ((x149 PP)) 
                               (and 
                                   (forall ((x150 PIDS)) 
                                       (= 
                                           (MS x150 x149) 
                                           (= x150 pid))) 
                                   (Slot_Pids_in_TM_Pool a2 x149)))))))
         :named hyp70))
(assert (! (forall ((a3 ENQUEUEABLE_ELEMENTS) (q1 QUEUES)) 
               (exists ((x151 QUEUES) (x152 Int)) 
                   (and 
                       (Enqueue a3 q1 x151) 
                       (forall ((x153 Int)) 
                           (=> 
                               (Length_of_Queue q1 x153) 
                               (= x152 (+ x153 1)))) 
                       (Length_of_Queue x151 x152))))
         :named hyp71))
(assert (! (forall ((k0 Int) (q2 QUEUES)) 
               (=> 
                   (and 
                       (<= 0 k0) 
                       (Length_of_Queue q2 k0)) 
                   (exists ((x154 PQ)) 
                       (and 
                           (Queues_of_Length k0 x154) 
                           (MS0 q2 x154)))))
         :named hyp72))
(assert (! (forall ((a4 ENQUEUEABLE_ELEMENTS) (q3 QUEUES)) 
               (exists ((x155 QUEUES) (x156 PE)) 
                   (and 
                       (Enqueue a4 q3 x155) 
                       (forall ((x157 ENQUEUEABLE_ELEMENTS)) 
                           (= 
                               (MS1 x157 x156) 
                               (or 
                                   (= x157 a4) 
                                   (exists ((x158 PE)) 
                                       (and 
                                           (Elements_of_Queue q3 x158) 
                                           (MS1 x157 x158)))))) 
                       (Elements_of_Queue x155 x156))))
         :named hyp73))
(assert (! (forall ((a5 ENQUEUEABLE_ELEMENTS) (q4 QUEUES)) 
               (exists ((x159 QUEUES) (x160 PE)) 
                   (and 
                       (Enqueue a5 q4 x159) 
                       (forall ((x161 ENQUEUEABLE_ELEMENTS)) 
                           (= 
                               (MS1 x161 x160) 
                               (or 
                                   (and 
                                       (= x161 a5) 
                                       (exists ((x162 PE)) 
                                           (and 
                                               (Elements_of_Queue q4 x162) 
                                               (MS1 x161 x162)))) 
                                   (exists ((x163 PE)) 
                                       (and 
                                           (Duplicate_Elements_of_Queue q4 x163) 
                                           (MS1 x161 x163)))))) 
                       (Duplicate_Elements_of_Queue x159 x160))))
         :named hyp74))
(assert (! (not 
               (= q Empty_Queue))
         :named hyp75))
(assert (! (not 
               (exists ((x164 ENQUEUEABLE_ELEMENTS)) 
                   (Head_of_Queue q x164)))
         :named goal))
(check-sat)
(exit)

