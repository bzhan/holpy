(set-info :smt-lib-version 2.6)
(set-logic UFLIA)
(set-info :source | An Optimal Algorithm for Mutual Exclusion in Computer Networks. Glenn Ricart and Ashok K. Agrawala. Communications of the ACM Vol.: 24 Number: 1. This is a benchmark of the haRVey theorem prover. It was translated to SMT-LIB by Leonardo  de Moura |)
(set-info :category "industrial")
(set-info :status unsat)
(declare-fun p () Int)
(declare-fun q () Int)
(declare-fun r () Int)
(declare-fun s () Int)
(declare-fun s0 (Int) Bool)
(declare-fun s1 (Int) Bool)
(declare-fun s2 (Int) Bool)
(declare-fun s3 (Int) Bool)
(declare-fun s4 (Int) Bool)
(declare-fun s5 (Int) Bool)
(declare-fun s6 (Int) Bool)
(declare-fun rcs1 (Int) Bool)
(declare-fun rcs2 (Int) Bool)
(declare-fun x (Int Int) Bool)
(declare-fun ro (Int Int) Bool)
(declare-fun rd (Int Int) Bool)
(declare-fun sn (Int) Int)
(declare-fun time () Int)
(assert (not (=> (and (forall ((?p Int)) (forall ((?q Int)) (=> (or (s0 ?p) (s5 ?p)) (not (x ?p ?q))))) (forall ((?p Int)) (= (or (s0 ?p) (s6 ?p)) (not (rcs2 ?p)))) (forall ((?p Int)) (< (sn ?p) time)) (forall ((?p Int)) (forall ((?q Int)) (=> (not (= ?p ?q)) (not (= (sn ?p) (sn ?q)))))) (forall ((?p Int)) (forall ((?q Int)) (=> (and (not (= ?p ?q)) (or (and (s4 ?p) (x ?p ?q)) (s5 ?p)) (rcs2 ?q)) (< (sn ?p) (sn ?q))))) (forall ((?p Int)) (forall ((?q Int)) (=> (and (not (= ?p ?q)) (rd ?q ?p)) (ro ?p ?q)))) (forall ((?p Int)) (forall ((?q Int)) (let ((?v_0 (x ?p ?q))) (=> (not (= ?p ?q)) (= (not (or (and (s2 ?p) ?v_0) (and (s3 ?p) (not ?v_0)))) (=> (ro ?p ?q) (rd ?q ?p))))))) (forall ((?p Int)) (forall ((?q Int)) (let ((?v_1 (x ?q ?p))) (let ((?v_2 (or (and (s3 ?q) ?v_1) (and (s4 ?q) (not ?v_1))))) (=> (not (= ?p ?q)) (or (and (s6 ?p) (not (x ?p ?q)) ?v_2) (= (rd ?p ?q) (and ?v_2 (rcs2 ?p) (< (sn ?p) (sn ?q)))))))))) (forall ((?p Int)) (=> (s0 ?p) (not (or (s2 ?p) (s3 ?p) (s4 ?p) (s5 ?p) (s6 ?p))))) (forall ((?p Int)) (=> (s2 ?p) (not (or (s3 ?p) (s4 ?p) (s5 ?p) (s6 ?p))))) (forall ((?p Int)) (=> (s3 ?p) (not (or (s4 ?p) (s5 ?p) (s6 ?p))))) (forall ((?p Int)) (=> (s4 ?p) (not (or (s5 ?p) (s6 ?p))))) (forall ((?p Int)) (=> (s5 ?p) (not (s6 ?p)))) (forall ((?q Int)) (let ((?v_3 (not (= ?q p)))) (=> (and ?v_3 (=> ?v_3 (s0 ?q))) (not (or (=> ?v_3 (s2 ?q)) (s3 ?q) (s4 ?q) (s5 ?q) (s6 ?q)))))) (forall ((?q Int)) (=> (=> (not (= ?q p)) (s2 ?q)) (not (or (s3 ?q) (s4 ?q) (s5 ?q) (s6 ?q))))) (forall ((?q Int)) (=> (s3 ?q) (not (or (s4 ?q) (s5 ?q) (s6 ?q))))) (forall ((?q Int)) (=> (s4 ?q) (not (or (s5 ?q) (s6 ?q))))) (forall ((?q Int)) (=> (s5 ?q) (not (s6 ?q)))) (s0 p) (rcs1 p)) (and (forall ((?r Int)) (forall ((?q Int)) (let ((?v_4 (not (= ?r p)))) (=> (or (and ?v_4 (=> ?v_4 (s0 ?r))) (s5 ?r)) (not (x ?r ?q)))))) (forall ((?r Int)) (let ((?v_5 (not (= ?r p)))) (= (or (and ?v_5 (=> ?v_5 (s0 ?r))) (s6 ?r)) (not (=> ?v_5 (rcs2 ?r)))))) (forall ((?r Int)) (let ((?v_6 (= ?r p))) (and (=> ?v_6 (< 0 1)) (=> (not ?v_6) (< (sn ?r) (+ time 1)))))) (forall ((?r Int)) (forall ((?q Int)) (let ((?v_7 (= ?q p)) (?v_8 (= ?r p))) (let ((?v_9 (not ?v_8)) (?v_10 (sn ?r)) (?v_11 (sn ?q))) (=> (not (= ?r ?q)) (not (and (=> (and ?v_7 ?v_9) (= ?v_10 time)) (=> (not ?v_7) (and (=> ?v_8 (= time ?v_11)) (=> ?v_9 (= ?v_10 ?v_11))))))))))) (forall ((?r Int)) (forall ((?q Int)) (let ((?v_12 (= ?q p))) (let ((?v_14 (not ?v_12)) (?v_15 (= ?r p))) (let ((?v_13 (not ?v_15)) (?v_16 (sn ?r)) (?v_17 (sn ?q))) (=> (and (not (= ?r ?q)) (or (and (s4 ?r) (x ?r ?q)) (s5 ?r)) (=> ?v_14 (rcs2 ?q))) (and (=> ?v_12 (and ?v_13 (=> ?v_13 (< ?v_16 time)))) (=> ?v_14 (and (=> ?v_15 (< time ?v_17)) (=> ?v_13 (< ?v_16 ?v_17))))))))))) (forall ((?r Int)) (forall ((?q Int)) (=> (and (not (= ?r ?q)) (rd ?q ?r)) (ro ?r ?q)))) (forall ((?r Int)) (forall ((?q Int)) (let ((?v_18 (x ?r ?q))) (=> (not (= ?r ?q)) (= (not (or (and (=> (not (= ?r p)) (s2 ?r)) ?v_18) (and (s3 ?r) (not ?v_18)))) (=> (ro ?r ?q) (rd ?q ?r))))))) (forall ((?r Int)) (forall ((?q Int)) (let ((?v_19 (x ?q ?r))) (let ((?v_20 (or (and (s3 ?q) ?v_19) (and (s4 ?q) (not ?v_19)))) (?v_23 (= ?r p))) (let ((?v_21 (not ?v_23)) (?v_22 (= ?q p)) (?v_24 (sn ?r)) (?v_25 (sn ?q))) (=> (not (= ?r ?q)) (or (and (s6 ?r) (not (x ?r ?q)) ?v_20) (= (rd ?r ?q) (and ?v_20 (=> ?v_21 (rcs2 ?r)) (=> ?v_22 (and ?v_21 (=> ?v_21 (< ?v_24 time)))) (=> (not ?v_22) (and (=> ?v_23 (< time ?v_25)) (=> ?v_21 (< ?v_24 ?v_25)))))))))))))))))
(check-sat)
(exit)
