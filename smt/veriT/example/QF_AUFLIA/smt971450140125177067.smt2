(set-info :smt-lib-version 2.6)
(set-logic QF_AUFLIA)
(set-info :source |Generator: Rodin SMT Plug-in|)
(set-info :license "https://creativecommons.org/licenses/by-nc/4.0/")
(set-info :category "industrial")
(set-info :status unsat)

(declare-fun n () Int)
(declare-fun r () Int)

(assert (! (<= r n)
         :named hyp1))
(assert (! (not 
               (< (- (+ n 1) (+ r 1)) (- (+ n 1) r)))
         :named goal))
(check-sat)
(exit)

