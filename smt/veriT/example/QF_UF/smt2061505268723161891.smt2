(set-info :smt-lib-version 2.6)
(set-logic QF_UF)
(set-info :source |Generator: Rodin SMT Plug-in|)
(set-info :license "https://creativecommons.org/licenses/by-nc/4.0/")
(set-info :category "industrial")
(set-info :status unsat)

(declare-fun circuit () Bool)
(declare-fun grn () Bool)
(declare-fun grn_SR () Bool)
(declare-fun org () Bool)
(declare-fun org_MR () Bool)
(declare-fun org_SR () Bool)
(declare-fun prt () Bool)
(declare-fun rd1 () Bool)
(declare-fun rd2 () Bool)
(declare-fun red_MR () Bool)
(declare-fun red_SR () Bool)

(assert (! circuit
         :named hyp1))
(assert (! rd2
         :named hyp2))
(assert (! red_MR
         :named hyp3))
(assert (! (or 
               grn_SR 
               org_SR)
         :named hyp4))
(assert (! (=> 
               grn 
               (and 
                   (not 
                       org) 
                   (not 
                       rd1) 
                   (not 
                       rd2)))
         :named hyp5))
(assert (! (=> 
               org 
               (and 
                   (not 
                       rd1) 
                   (not 
                       rd2)))
         :named hyp6))
(assert (! (=> 
               rd1 
               (not 
                   rd2))
         :named hyp7))
(assert (! (= 
               org_MR 
               org)
         :named hyp8))
(assert (! (= 
               grn_SR 
               rd1)
         :named hyp9))
(assert (! (= 
               org_SR 
               rd2)
         :named hyp10))
(assert (! (= 
               red_SR 
               (or 
                   grn 
                   org))
         :named hyp11))
(assert (! (not 
               (= 
                   rd1 
                   (or 
                       org 
                       (and 
                           prt 
                           rd1))))
         :named goal))
(check-sat)
(exit)

