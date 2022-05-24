(set-info :smt-lib-version 2.6)
(set-logic LRA)
(set-info :source |
   Scholl, Christoph; Disch, Stefan; Pigorsch, Florian and Kupferschmid, 
   Stefan; Using an SMT Solver and Craig Interpolation to Detect and Remove 
   Redundant Linear Constraints in Representations of Non-Convex Polyhedra.
   Proceedings of 6th International Workshop on Satisfiability Modulo
   Theories, Princeton, USA, July 2008.
   <http://abs.informatik.uni-freiburg.de/smtbench/>
|)
(set-info :category "random")
(set-info :status unsat)
(declare-fun y3 () Real)
(declare-fun x1 () Real)
(declare-fun y2 () Real)
(assert (and (forall ((?y3 Real)) (or (and (or (< (+ (* 87 ?y3) (* (- 64) x1)) 94) (< (+ (* 68 ?y3) (* (- 12) x1)) 49)) (or (>= (* (- 2) ?y3) (- 14)) (= (+ (* (- 5) ?y3) (* 42 x1)) (- 63)))) (and (<= (+ (* 83 ?y3) (* (- 35) x1)) 14) (or (>= (* 73 ?y3) 88) (>= (* (- 80) x1) 0))))) (and (exists ((?y2 Real)) (forall ((?y3 Real)) (and (or (= (+ (+ (* (- 96) ?y3) (* (- 55) ?y2)) (* (- 70) x1)) (- 31)) (or (< (+ (* 6 ?y3) (* (- 58) ?y2)) 31) (>= (+ (* (- 26) ?y3) (* 97 x1)) 67))) (and (and (= (+ (+ (* (- 54) ?y3) (* 32 ?y2)) (* 40 x1)) (- 21)) (>= (+ (+ (* 44 ?y3) (* 66 ?y2)) (* (- 56) x1)) (- 23))) (and (= (+ (* 63 ?y3) (* (- 76) x1)) 81) (>= (+ (+ (* (- 20) ?y3) (* 2 ?y2)) (* 28 x1)) 0)))))) (exists ((?y2 Real)) (or (or (or (and (<= (* 66 x1) 0) (not (= (+ (* (- 90) ?y2) (* 3 x1)) 0))) (exists ((?y3 Real)) (<= (+ (* (- 49) ?y2) (* (- 26) x1)) 0))) (exists ((?y3 Real)) (or (= (* 71 ?y3) 69) (< (+ (+ (* 89 ?y3) (* (- 8) ?y2)) (* 86 x1)) (- 8))))) (and (forall ((?y3 Real)) (and (< (+ (+ (* (- 35) ?y3) (* 88 ?y2)) (* (- 45) x1)) 28) (<= (* 40 ?y3) 0))) (forall ((?y3 Real)) (>= (+ (* (- 4) ?y3) (* (- 16) ?y2)) (- 53)))))))))
(check-sat)
(exit)
