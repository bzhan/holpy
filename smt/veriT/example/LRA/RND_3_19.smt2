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
(declare-fun y2 () Real)
(declare-fun y3 () Real)
(declare-fun x1 () Real)
(declare-fun y1 () Real)
(assert (and (and (exists ((y2 Real)) (or (exists ((y3 Real)) (and (or (< (+ (* (- 48) y3) (* 84 y2)) (- 32)) (not (= (* (- 60) x1) 0))) (and (>= (+ (* (- 51) y3) (* (- 87) y2)) 0) (> (+ (* (- 61) y3) (* (- 94) x1)) 86)))) (and (exists ((y3 Real)) (or (not (= (* (- 31) y2) (- 25))) (>= (+ (* 30 y3) (* 54 y2)) 0))) (and (< (* (- 88) y2) (- 86)) (>= (+ (* 73 y2) (* (- 59) x1)) 82))))) (exists ((y2 Real)) (and (forall ((y3 Real)) (and (and (= (* 20 y2) (- 90)) (not (= (+ (+ (* 90 y3) (* 5 y2)) (* (- 23) x1)) 8))) (and (not (= (+ (* 100 y3) (* 91 y2)) (- 28))) (< (+ (* (- 43) y3) (* 14 x1)) (- 41))))) (or (and (and (<= (* (- 89) y2) 30) (> (+ (* 56 y2) (* 31 x1)) (- 46))) (forall ((y3 Real)) (not (= (+ (* (- 36) y3) (* (- 10) x1)) 0)))) (>= (+ (* 34 y2) (* 98 x1)) (- 71)))))) (and (and (and (exists ((y1 Real)) (or (forall ((y3 Real)) (>= (+ (+ (* 55 y3) (* 34 y1)) (* 41 x1)) 0)) (or (= (+ (* 33 y1) (* 100 x1)) 63) (>= (* 85 x1) (- 8))))) (forall ((y1 Real)) (and (and (>= (+ (* 54 y1) (* 11 x1)) 0) (and (= (+ (* (- 61) y1) (* 25 x1)) 0) (> (+ (* 14 y1) (* 97 x1)) (- 45)))) (exists ((y2 Real)) (forall ((y3 Real)) (<= (+ (+ (* 74 y3) (* (- 20) y2)) (* (- 67) y1)) (- 100))))))) (or (forall ((y1 Real)) (forall ((y2 Real)) (exists ((y3 Real)) (or (not (= (+ (+ (+ (* 6 y3) (* 82 y2)) (* (- 78) y1)) (* 32 x1)) (- 9))) (>= (+ (+ (* (- 73) y3) (* 84 y2)) (* (- 88) y1)) (- 62)))))) (exists ((y1 Real)) (and (forall ((y2 Real)) (> (+ (* 3 y2) (* (- 82) y1)) (- 54))) (>= (* 35 y1) 0))))) (or (forall ((y1 Real)) (exists ((y3 Real)) (and (and (<= (+ (* (- 81) y3) (* (- 41) x1)) (- 81)) (not (= (+ (+ (* (- 74) y3) (* 62 y1)) (* (- 78) x1)) 0))) (> (* (- 34) y1) 0)))) (and (or (exists ((y1 Real)) (or (exists ((y2 Real)) (<= (+ (+ (* 65 y2) (* 100 y1)) (* (- 71) x1)) 53)) (exists ((y2 Real)) (<= (+ (+ (* 28 y2) (* 62 y1)) (* 43 x1)) 80)))) (exists ((y1 Real)) (exists ((y2 Real)) (< (+ (* 91 y2) (* (- 18) x1)) 1)))) (or (exists ((y1 Real)) (or (= (+ (* (- 8) y1) (* 87 x1)) 3) (> (+ (* (- 67) y1) (* 29 x1)) 47))) (forall ((y1 Real)) (forall ((y2 Real)) (>= (+ (+ (* 26 y2) (* (- 62) y1)) (* 67 x1)) 0)))))))))
(check-sat)
(exit)
