(set-info :smt-lib-version 2.6)
(set-logic AUFLIA)
(set-info :source |Generator: Rodin SMT Plug-in|)
(set-info :license "https://creativecommons.org/licenses/by-nc/4.0/")
(set-info :category "industrial")
(set-info :status unsat)


(assert (! (not 
               (and 
                   (forall ((x Int)) 
                       (=> 
                           (= x 0) 
                           (<= 0 x))) 
                   (forall ((x0 Int) (x1 Int)) 
                       (=> 
                           (and 
                               (= x0 0) 
                               (= x1 0)) 
                           (= x0 x1))) 
                   (exists ((x2 Int)) 
                       (= x2 0))))
         :named goal))
(check-sat)
(exit)

