(set-info :smt-lib-version 2.6)
(set-logic AUFLIA)
(set-info :source |Generator: Rodin SMT Plug-in|)
(set-info :license "https://creativecommons.org/licenses/by-nc/4.0/")
(set-info :category "industrial")
(set-info :status unsat)

(declare-sort S 0)
(declare-fun il () S)

(assert (! (not 
               (and 
                   (forall ((x S) (x0 Int)) 
                       (=> 
                           (or 
                               (and 
                                   (= x0 0) 
                                   (not 
                                       (exists ((x1 Int)) 
                                           (and 
                                               (= x il) 
                                               (= x1 1))))) 
                               (and 
                                   (= x il) 
                                   (= x0 1))) 
                           (<= 0 x0))) 
                   (forall ((x2 S) (x3 Int) (x4 Int)) 
                       (=> 
                           (and 
                               (or 
                                   (and 
                                       (= x3 0) 
                                       (not 
                                           (exists ((x5 Int)) 
                                               (and 
                                                   (= x2 il) 
                                                   (= x5 1))))) 
                                   (and 
                                       (= x2 il) 
                                       (= x3 1))) 
                               (or 
                                   (and 
                                       (= x4 0) 
                                       (not 
                                           (exists ((x6 Int)) 
                                               (and 
                                                   (= x2 il) 
                                                   (= x6 1))))) 
                                   (and 
                                       (= x2 il) 
                                       (= x4 1)))) 
                           (= x3 x4))) 
                   (forall ((x7 S)) 
                       (or 
                           (exists ((x8 Int)) 
                               (and 
                                   (= x8 0) 
                                   (not 
                                       (exists ((x9 Int)) 
                                           (and 
                                               (= x7 il) 
                                               (= x9 1)))))) 
                           (exists ((x10 Int)) 
                               (and 
                                   (= x7 il) 
                                   (= x10 1)))))))
         :named goal))
(check-sat)
(exit)

