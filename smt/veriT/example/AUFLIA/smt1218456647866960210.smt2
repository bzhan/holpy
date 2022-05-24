(set-info :smt-lib-version 2.6)
(set-logic AUFLIA)
(set-info :source |Generator: Rodin SMT Plug-in|)
(set-info :license "https://creativecommons.org/licenses/by-nc/4.0/")
(set-info :category "industrial")
(set-info :status unsat)

(declare-sort N 0)
(declare-fun c (N Int) Bool)
(declare-fun n () N)
(declare-fun x () N)
(declare-fun y () N)

(assert (! (forall ((x0 N) (y0 N) (x1 Int) (x2 Int)) 
               (=> 
                   (and 
                       (c x0 x2) 
                       (c y0 x1)) 
                   (<= x2 (+ x1 1))))
         :named hyp1))
(assert (! (forall ((m N) (x3 Int) (x4 Int)) 
               (=> 
                   (and 
                       (c n x4) 
                       (c m x3)) 
                   (<= x4 x3)))
         :named hyp2))
(assert (! (not 
               (= x n))
         :named hyp3))
(assert (! (not 
               (= y n))
         :named hyp4))
(assert (! (not 
               (forall ((x5 Int) (x6 Int)) 
                   (=> 
                       (and 
                           (c x x6) 
                           (c y x5)) 
                       (<= x6 (+ x5 1)))))
         :named goal))
(check-sat)
(exit)

