(set-info :smt-lib-version 2.6)
(set-logic QF_UF)
(set-info :source |Generator: Rodin SMT Plug-in|)
(set-info :license "https://creativecommons.org/licenses/by-nc/4.0/")
(set-info :category "industrial")
(set-info :status unsat)

(declare-sort Z 0)
(declare-fun circuit () Bool)
(declare-fun input () Bool)
(declare-fun reg () Bool)
(declare-fun flash () Z)
(declare-fun nf () Z)

(assert (! circuit
         :named hyp1))
(assert (! (= nf flash)
         :named hyp2))
(assert (! (not 
               (or 
                   (and 
                       input 
                       (not 
                           reg)) 
                   (not 
                       input) 
                   reg))
         :named goal))
(check-sat)
(exit)

