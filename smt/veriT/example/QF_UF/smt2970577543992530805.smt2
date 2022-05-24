(set-info :smt-lib-version 2.6)
(set-logic QF_UF)
(set-info :source |Generator: Rodin SMT Plug-in|)
(set-info :license "https://creativecommons.org/licenses/by-nc/4.0/")
(set-info :category "industrial")
(set-info :status unsat)

(declare-sort MODE 0)
(declare-sort Z 0)
(declare-fun i1 () Bool)
(declare-fun i2 () Bool)
(declare-fun p1 () Bool)
(declare-fun p2 () Bool)
(declare-fun a1 () Z)
(declare-fun a2 () Z)
(declare-fun b1 () Z)
(declare-fun b2 () Z)
(declare-fun cir () MODE)
(declare-fun mode () MODE)
(declare-fun r1 () Z)
(declare-fun r2 () Z)

(assert (! (= mode cir)
         :named hyp1))
(assert (! (= a1 b1)
         :named hyp2))
(assert (! (= a2 b2)
         :named hyp3))
(assert (! (= 
               (not 
                   i1) 
               (= r1 b1))
         :named hyp4))
(assert (! (= 
               (not 
                   i2) 
               (= r2 b2))
         :named hyp5))
(assert (! (=> 
               (= r1 b1) 
               (not 
                   p1))
         :named hyp6))
(assert (! (=> 
               (= r2 b2) 
               (not 
                   p2))
         :named hyp7))
(assert (! (or 
               (and 
                   (not 
                       (= r1 b1)) 
                   (not 
                       p2)) 
               (and 
                   (not 
                       (= r2 b2)) 
                   (not 
                       p1)) 
               (and 
                   (= r1 b1) 
                   (= r2 b2)))
         :named hyp8))
(assert (! (not 
               (or 
                   (and 
                       i1 
                       (not 
                           p2)) 
                   (and 
                       i2 
                       (or 
                           (not 
                               i1) 
                           p2)) 
                   (and 
                       (not 
                           i1) 
                       (not 
                           i2))))
         :named goal))
(check-sat)
(exit)

