(set-info :smt-lib-version 2.6)
(set-logic QF_AUFLIA)
(set-info :source |Generator: Rodin SMT Plug-in|)
(set-info :license "https://creativecommons.org/licenses/by-nc/4.0/")
(set-info :category "industrial")
(set-info :status unsat)

(declare-fun car () Bool)
(declare-fun circuit () Bool)
(declare-fun clk () Bool)
(declare-fun grn_SR () Bool)
(declare-fun prt () Bool)
(declare-fun d () Int)

(assert (! (not 
               circuit)
         :named hyp1))
(assert (! (= d 1)
         :named hyp2))
(assert (! grn_SR
         :named hyp3))
(assert (! (and 
               (<= 0 1) 
               (<= 1 5))
         :named hyp4))
(assert (! (=> 
               circuit 
               (or 
                   (and 
                       (not 
                           prt) 
                       car 
                       clk) 
                   (and 
                       prt 
                       (or 
                           (not 
                               car) 
                           clk)) 
                   (and 
                       (not 
                           prt) 
                       (or 
                           (not 
                               car) 
                           (not 
                               clk))) 
                   (and 
                       prt 
                       car 
                       (not 
                           clk))))
         :named hyp5))
(assert (! (and 
               (<= 0 d) 
               (<= d 5))
         :named hyp6))
(assert (! (= 
               (= d 0) 
               (not 
                   car))
         :named hyp7))
(assert (! (not 
               (and 
                   (<= 0 0) 
                   (<= 0 5)))
         :named goal))
(check-sat)
(exit)

