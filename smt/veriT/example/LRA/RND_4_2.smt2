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
(declare-fun y1 () Real)
(declare-fun y2 () Real)
(declare-fun x1 () Real)
(declare-fun y3 () Real)
(declare-fun y4 () Real)
(assert (and (and (exists ((?y1 Real)) (and (or (exists ((?y2 Real)) (and (and (>= (+ (* 14 ?y2) (* (- 86) ?y1)) 19) (>= (+ (+ (* (- 23) ?y2) (* (- 57) ?y1)) (* (- 60) x1)) (- 80))) (exists ((?y3 Real)) (< (+ (+ (+ (* (- 86) ?y3) (* 50 ?y2)) (* (- 80) ?y1)) (* 32 x1)) (- 50))))) (and (not (= (+ (* 63 ?y1) (* (- 98) x1)) 69)) (> (+ (* 15 ?y1) (* (- 74) x1)) 0))) (exists ((?y2 Real)) (exists ((?y3 Real)) (forall ((?y4 Real)) (and (<= (+ (+ (+ (* (- 2) ?y4) (* 50 ?y3)) (* 72 ?y1)) (* (- 73) x1)) (- 4)) (= (+ (+ (+ (* (- 92) ?y4) (* (- 65) ?y3)) (* 20 ?y2)) (* (- 42) x1)) (- 4)))))))) (forall ((?y1 Real)) (exists ((?y3 Real)) (forall ((?y4 Real)) (and (= (+ (+ (* 30 ?y4) (* 88 ?y3)) (* 8 ?y1)) 0) (and (= (+ (* (- 86) ?y3) (* (- 26) x1)) (- 90)) (not (= (+ (* (- 47) ?y4) (* 44 x1)) 0)))))))) (or (or (exists ((?y1 Real)) (forall ((?y2 Real)) (or (and (or (<= (+ (* (- 23) ?y2) (* (- 20) ?y1)) (- 91)) (= (+ (+ (* (- 70) ?y2) (* (- 98) ?y1)) (* 33 x1)) 0)) (forall ((?y3 Real)) (not (= (+ (+ (* 32 ?y3) (* (- 25) ?y2)) (* 23 ?y1)) (- 54))))) (and (forall ((?y3 Real)) (< (+ (+ (+ (* (- 31) ?y3) (* 67 ?y2)) (* (- 2) ?y1)) (* 4 x1)) 82)) (forall ((?y3 Real)) (not (= (+ (+ (* 75 ?y3) (* (- 62) ?y2)) (* 24 ?y1)) 33))))))) (exists ((?y1 Real)) (forall ((?y3 Real)) (forall ((?y4 Real)) (or (= (+ (+ (+ (* 53 ?y4) (* (- 79) ?y3)) (* (- 41) ?y1)) (* (- 17) x1)) (- 33)) (<= (+ (+ (* 40 ?y4) (* 79 ?y3)) (* (- 5) ?y1)) 0)))))) (forall ((?y1 Real)) (and (and (and (exists ((?y3 Real)) (<= (+ (* (- 68) ?y3) (* 27 x1)) (- 78))) (exists ((?y3 Real)) (>= (+ (+ (* (- 92) ?y3) (* 5 ?y1)) (* 61 x1)) 97))) (exists ((?y3 Real)) (exists ((?y4 Real)) (<= (+ (+ (+ (* 79 ?y4) (* (- 25) ?y3)) (* (- 87) ?y1)) (* (- 11) x1)) (- 21))))) (forall ((?y2 Real)) (or (exists ((?y3 Real)) (and (not (= (+ (+ (* 51 ?y3) (* 48 ?y1)) (* (- 85) x1)) 3)) (>= (+ (+ (* (- 69) ?y3) (* (- 27) ?y2)) (* 71 x1)) 4))) (or (and (<= (+ (+ (* (- 87) ?y2) (* (- 40) ?y1)) (* (- 10) x1)) 92) (<= (+ (* (- 90) ?y1) (* (- 18) x1)) (- 79))) (or (> (+ (* 23 ?y2) (* (- 65) ?y1)) 0) (<= (+ (* (- 71) ?y2) (* 15 x1)) 38))))))))))
(check-sat)
(exit)
