(set-info :smt-lib-version 2.6)
(set-logic AUFLIA)
(set-info :source |Generator: Rodin SMT Plug-in|)
(set-info :license "https://creativecommons.org/licenses/by-nc/4.0/")
(set-info :category "industrial")
(set-info :status unsat)

(declare-sort S 0)
(declare-fun DA (S Bool) Bool)
(declare-fun da (S) Bool)
(declare-fun l () S)
(declare-fun x () S)

(assert (! (not 
               (exists ((x0 Bool)) 
                   (and 
                       x0 
                       (DA l x0))))
         :named hyp1))
(assert (! (forall ((x1 S)) 
               (=> 
                   (da x1) 
                   (exists ((x2 Bool)) 
                       (and 
                           x2 
                           (DA x1 x2)))))
         :named hyp2))
(assert (! (or 
               (da x) 
               (= x l))
         :named hyp3))
(assert (! (not 
               (= x l))
         :named hyp4))
(assert (! (not 
               (exists ((x3 Bool)) 
                   (and 
                       x3 
                       (DA x x3))))
         :named goal))
(check-sat)
(exit)

