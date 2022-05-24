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
(declare-fun y4 () Real)
(assert (and (forall ((?y3 Real)) (or (and (or (< (+ (* 87 ?y3) (* (- 64) x1)) 94) (< (+ (* 68 ?y3) (* (- 12) x1)) 49)) (or (>= (* (- 2) ?y3) (- 14)) (= (+ (* (- 5) ?y3) (* 42 x1)) (- 63)))) (and (<= (+ (* 83 ?y3) (* (- 35) x1)) 14) (or (>= (* 73 ?y3) 88) (>= (* (- 80) x1) 0))))) (and (exists ((?y2 Real)) (forall ((?y3 Real)) (exists ((?y4 Real)) (or (and (not (= (+ (+ (+ (* (- 96) ?y4) (* (- 55) ?y3)) (* (- 70) ?y2)) (* (- 95) x1)) (- 31))) (< (+ (+ (+ (* 67 ?y4) (* 6 ?y3)) (* (- 26) ?y2)) (* (- 58) x1)) 31)) (not (= (+ (+ (* 81 ?y4) (* (- 23) ?y3)) (* (- 54) x1)) (- 21))))))) (exists ((?y2 Real)) (or (or (or (and (<= (* 66 x1) 0) (not (= (+ (* (- 90) ?y2) (* 3 x1)) 0))) (exists ((?y3 Real)) (<= (+ (* (- 49) ?y2) (* (- 26) x1)) 0))) (exists ((?y3 Real)) (or (= (* 71 ?y3) 69) (< (+ (+ (* 89 ?y3) (* (- 8) ?y2)) (* 86 x1)) (- 8))))) (and (forall ((?y3 Real)) (exists ((?y4 Real)) (< (+ (+ (* (- 35) ?y3) (* 40 ?y2)) (* 88 x1)) 28))) (forall ((?y3 Real)) (>= (+ (* (- 4) ?y3) (* (- 16) ?y2)) (- 53)))))))))
(check-sat)
(exit)
