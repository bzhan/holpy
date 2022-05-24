(set-info :smt-lib-version 2.6)
(set-logic QF_AUFLIA)
(set-info :source |
Benchmarks used in the followin paper:
Big proof engines as little proof engines: new results on rewrite-based satisfiability procedure
Alessandro Armando, Maria Paola Bonacina, Silvio Ranise, Stephan Schulz. 
PDPAR'05
http://www.ai.dist.unige.it/pdpar05/


|)
(set-info :category "crafted")
(set-info :status unsat)
(declare-fun a_39 () (Array Int Int))
(declare-fun a_40 () (Array Int Int))
(declare-fun a_42 () (Array Int Int))
(declare-fun a_43 () (Array Int Int))
(declare-fun e_38 () Int)
(declare-fun e_41 () Int)
(declare-fun e_45 () Int)
(declare-fun i_44 () Int)
(declare-fun a1 () (Array Int Int))
(declare-fun i0 () Int)
(declare-fun i1 () Int)
(declare-fun sk ((Array Int Int) (Array Int Int)) Int)
(assert (= a_39 (store a1 i1 e_38)))
(assert (= a_40 (store a_39 i1 e_38)))
(assert (= a_42 (store a_40 i0 e_41)))
(assert (= a_43 (store a_42 i0 e_41)))
(assert (= e_38 (select a1 i1)))
(assert (= e_41 (select a_40 i0)))
(assert (= e_45 (select a_43 i_44)))
(assert (= i_44 (sk a_43 a_43)))
(assert (not (= e_45 e_45)))
(check-sat)
(exit)
