(set-info :smt-lib-version 2.6)
(set-logic UFLIA)
(set-info :source | SMT-COMP'06 organizers |)
(set-info :category "check")
(set-info :status unsat)
(set-info :notes |This benchmark is designed to check if the DP supports bignumbers.|)
(declare-fun f (Int) Int)
(assert (= (f 0) 1))
(assert (forall ((?x Int)) (=> (> ?x 0) (= (f ?x) (* (- 1000) (f (- ?x 1)))))))
(assert (< (f 20) 0))
(check-sat)
(exit)
