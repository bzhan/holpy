(set-info :smt-lib-version 2.6)
(set-logic AUFLIA)
(set-info :source |Generator: Rodin SMT Plug-in|)
(set-info :license "https://creativecommons.org/licenses/by-nc/4.0/")
(set-info :category "industrial")
(set-info :status unsat)

(declare-sort N 0)
(declare-fun m (N N) Bool)
(declare-fun n (N) Bool)
(declare-fun x () N)
(declare-fun x0 () N)
(declare-fun y () N)
(declare-fun y0 () N)

(assert (! (forall ((x1 N) (y1 N)) 
               (=> 
                   (m x1 y1) 
                   (n x1)))
         :named hyp1))
(assert (! (m x y)
         :named hyp2))
(assert (! (not 
               (exists ((x2 N)) 
                   (m y x2)))
         :named hyp3))
(assert (! (and 
               (m x0 y0) 
               (not 
                   (= x0 x)))
         :named hyp4))
(assert (! (not 
               (and 
                   (n x0) 
                   (not 
                       (= x0 x))))
         :named goal))
(check-sat)
(exit)

