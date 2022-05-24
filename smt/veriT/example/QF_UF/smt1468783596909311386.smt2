(set-info :smt-lib-version 2.6)
(set-logic QF_UF)
(set-info :source |Generator: Rodin SMT Plug-in|)
(set-info :license "https://creativecommons.org/licenses/by-nc/4.0/")
(set-info :category "industrial")
(set-info :status unsat)

(declare-fun circuit () Bool)
(declare-fun grn () Bool)
(declare-fun org () Bool)
(declare-fun rd1 () Bool)
(declare-fun rd2 () Bool)

(assert (! (=> 
               rd1 
               (not 
                   rd2))
         :named hyp1))
(assert (! circuit
         :named hyp2))
(assert (! rd2
         :named hyp3))
(assert (! (not 
               grn)
         :named hyp4))
(assert (! (not 
               org)
         :named hyp5))
(assert (! (not 
               (not 
                   rd1))
         :named goal))
(check-sat)
(exit)

