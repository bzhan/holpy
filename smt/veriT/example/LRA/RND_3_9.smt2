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
(assert (and (and (exists ((?y2 Real)) (or (exists ((?y3 Real)) (< (* 86 x1) (- 32))) (>= (+ (* 82 ?y2) (* (- 88) x1)) (- 86)))) (exists ((?y2 Real)) (and (forall ((?y3 Real)) (= (+ (+ (* (- 28) ?y3) (* 8 ?y2)) (* (- 41) x1)) (- 90))) (or (<= (* (- 46) x1) 30) (< (+ (* (- 5) ?y2) (* 34 x1)) (- 71)))))) (and (and (and (exists ((?y1 Real)) (or (< (+ (* 55 ?y1) (* 34 x1)) 0) (not (= (+ (* (- 8) ?y1) (* 33 x1)) 63)))) (forall ((?y1 Real)) (and (< (* 54 x1) 0) (<= (+ (* 74 ?y1) (* (- 20) x1)) (- 100))))) (or (forall ((?y1 Real)) (forall ((?y2 Real)) (not (= (+ (+ (* (- 62) ?y2) (* 6 ?y1)) (* (- 73) x1)) (- 9))))) (exists ((?y1 Real)) (or (> (* 3 x1) (- 54)) (< (* (- 71) ?y1) 100))))) (and (or (exists ((?y1 Real)) (<= (+ (* 80 ?y1) (* 65 x1)) 53)) (and (< (* 91 x1) 1) (<= (* 88 x1) (- 52)))) (or (exists ((?y1 Real)) (not (= (+ (* 47 ?y1) (* (- 8) x1)) 3))) (forall ((?y1 Real)) (< (+ (* 26 ?y1) (* (- 62) x1)) 0)))))))
(check-sat)
(exit)
