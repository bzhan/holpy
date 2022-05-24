(set-info :smt-lib-version 2.6)
(set-logic UFLIA)
(set-info :source |
      Tokeneer case study <http://www.adacore.com/home/products/gnatpro/tokeneer/>
  |)
(set-info :category "industrial")
(set-info :status unsat)
(declare-fun field.t.rolepresent () Int)
(declare-fun field.t.currentop () Int)
(declare-fun archivelog () Int)
(declare-fun nullop () Int)
(declare-fun opandnullt__base__first () Int)
(declare-fun opandnullt__base__last () Int)
(declare-fun opandnullt__first () Int)
(declare-fun opandnullt__last () Int)
(declare-fun opandnullt__size () Int)
(declare-fun overridelock () Int)
(declare-fun privtypes__adminprivileget__base__first () Int)
(declare-fun privtypes__adminprivileget__base__last () Int)
(declare-fun privtypes__adminprivileget__first () Int)
(declare-fun privtypes__adminprivileget__last () Int)
(declare-fun privtypes__adminprivileget__size () Int)
(declare-fun privtypes__auditmanager () Int)
(declare-fun privtypes__guard () Int)
(declare-fun privtypes__privileget__base__first () Int)
(declare-fun privtypes__privileget__base__last () Int)
(declare-fun privtypes__privileget__first () Int)
(declare-fun privtypes__privileget__last () Int)
(declare-fun privtypes__privileget__size () Int)
(declare-fun privtypes__securityofficer () Int)
(declare-fun privtypes__useronly () Int)
(declare-fun shutdownop () Int)
(declare-fun updateconfigdata () Int)
(declare-fun role () Int)
(declare-fun init.role () Int)
(declare-fun theadmin () Int)
(declare-fun init.theadmin () Int)
(declare-fun bit__and (Int Int) Int)
(declare-fun bit__not (Int Int) Int)
(declare-fun bit__or (Int Int) Int)
(declare-fun bit__xor (Int Int) Int)
(declare-fun character__pos (Int) Int)
(declare-fun character__val (Int) Int)
(declare-fun integer__pred (Int) Int)
(declare-fun integer__succ (Int) Int)
(declare-fun opandnullt__pos (Int) Int)
(declare-fun opandnullt__pred (Int) Int)
(declare-fun opandnullt__succ (Int) Int)
(declare-fun opandnullt__val (Int) Int)
(declare-fun prf_rolepresent (Int) Int)
(declare-fun privtypes__privileget__pos (Int) Int)
(declare-fun privtypes__privileget__pred (Int) Int)
(declare-fun privtypes__privileget__succ (Int) Int)
(declare-fun privtypes__privileget__val (Int) Int)
(declare-fun round__ (Int) Int)
(declare-fun i.div (Int Int) Int)
(declare-fun i.mod (Int Int) Int)
(declare-fun i.mult (Int Int) Int)
(declare-fun i.exp (Int Int) Int)
(declare-fun tm.true () Int)
(declare-fun tm.false () Int)
(declare-fun tm.not (Int) Int)
(declare-fun tm.and (Int Int) Int)
(declare-fun tm.or (Int Int) Int)
(declare-fun tm.iff (Int Int) Int)
(declare-fun tm.eq (Int Int) Int)
(declare-fun tm.ne (Int Int) Int)
(declare-fun tm.lt (Int Int) Int)
(declare-fun tm.le (Int Int) Int)
(declare-fun tuple.2 (Int Int) Int)
(declare-fun a.store (Int Int Int) Int)
(declare-fun a.select (Int Int) Int)
(declare-fun a.mk_const_array (Int) Int)
(declare-fun a.default_array () Int)
(declare-fun r.default_record () Int)
(declare-fun isdoingop (Int) Bool)
(declare-fun ispresent (Int) Bool)
(declare-fun opandnullt__LE (Int Int) Bool)
(declare-fun opandnullt__LT (Int Int) Bool)
(declare-fun privtypes__privileget__LE (Int Int) Bool)
(declare-fun privtypes__privileget__LT (Int Int) Bool)
(assert (forall ((?i Int)) (=> (and (<= 0 ?i) (< ?i 4)) (= (privtypes__privileget__pos ?i) ?i))))
(assert (forall ((?i Int)) (=> (and (<= 0 ?i) (< ?i 4)) (= (privtypes__privileget__val ?i) ?i))))
(assert (forall ((?i Int)) (=> (and (<= 0 ?i) (< ?i 3)) (= (privtypes__privileget__succ ?i) (+ ?i 1)))))
(assert (forall ((?i Int)) (=> (and (<= 1 ?i) (< ?i 4)) (= (privtypes__privileget__pred ?i) (- ?i 1)))))
(assert (= privtypes__useronly 0))
(assert (= privtypes__guard 1))
(assert (= privtypes__auditmanager 2))
(assert (= privtypes__securityofficer 3))
(assert (forall ((?i Int)) (=> (and (<= 0 ?i) (< ?i 5)) (= (opandnullt__pos ?i) ?i))))
(assert (forall ((?i Int)) (=> (and (<= 0 ?i) (< ?i 5)) (= (opandnullt__val ?i) ?i))))
(assert (forall ((?i Int)) (=> (and (<= 0 ?i) (< ?i 4)) (= (opandnullt__succ ?i) (+ ?i 1)))))
(assert (forall ((?i Int)) (=> (and (<= 1 ?i) (< ?i 5)) (= (opandnullt__pred ?i) (- ?i 1)))))
(assert (= nullop 0))
(assert (= archivelog 1))
(assert (= updateconfigdata 2))
(assert (= overridelock 3))
(assert (= shutdownop 4))
(assert (<= 0 privtypes__privileget__size))
(assert (= privtypes__privileget__first privtypes__useronly))
(assert (= privtypes__privileget__last privtypes__securityofficer))
(assert (= privtypes__privileget__base__first privtypes__useronly))
(assert (= privtypes__privileget__base__last privtypes__securityofficer))
(assert (<= 0 privtypes__adminprivileget__size))
(assert (= privtypes__adminprivileget__first privtypes__guard))
(assert (= privtypes__adminprivileget__last privtypes__securityofficer))
(assert (= privtypes__adminprivileget__base__first privtypes__useronly))
(assert (= privtypes__adminprivileget__base__last privtypes__securityofficer))
(assert (<= 0 opandnullt__size))
(assert (= opandnullt__first nullop))
(assert (= opandnullt__last shutdownop))
(assert (= opandnullt__base__first nullop))
(assert (= opandnullt__base__last shutdownop))
(assert (forall ((?X Int) (?Y Int)) (=> (< 0 ?Y) (<= 0 (i.mod ?X ?Y)))))
(assert (forall ((?X Int) (?Y Int)) (=> (< 0 ?Y) (< (i.mod ?X ?Y) ?Y))))
(assert (forall ((?X Int) (?Y Int)) (=> (and (<= 0 ?X) (< 0 ?Y)) (<= (i.mult ?Y (i.div ?X ?Y)) ?X))))
(assert (forall ((?X Int) (?Y Int)) (=> (and (<= 0 ?X) (< 0 ?Y)) (< (- ?X ?Y) (i.mult ?Y (i.div ?X ?Y))))))
(assert (forall ((?X Int) (?Y Int)) (=> (and (<= ?X 0) (< 0 ?Y)) (<= ?X (i.mult ?Y (i.div ?X ?Y))))))
(assert (forall ((?X Int) (?Y Int)) (=> (and (<= ?X 0) (< 0 ?Y)) (< (i.mult ?Y (i.div ?X ?Y)) (+ ?X ?Y)))))
(assert (forall ((?X Int) (?Y Int)) (=> (and (<= 0 ?X) (<= 0 ?Y)) (<= 0 (bit__or ?X ?Y)))))
(assert (forall ((?X Int) (?Y Int)) (=> (and (<= 0 ?X) (<= 0 ?Y)) (<= ?X (bit__or ?X ?Y)))))
(assert (forall ((?X Int) (?Y Int)) (=> (and (<= 0 ?X) (<= 0 ?Y)) (<= ?Y (bit__or ?X ?Y)))))
(assert (forall ((?X Int) (?Y Int)) (=> (and (<= 0 ?X) (<= 0 ?Y)) (<= (bit__or ?X ?Y) (+ ?X ?Y)))))
(assert (distinct field.t.rolepresent field.t.currentop))
(assert (distinct tm.true tm.false))
(assert (forall ((?x Int)) (! (= (= (tm.not ?x) tm.true) (not (= ?x tm.true))) :pattern ((tm.not ?x)) )))
(assert (forall ((?x Int) (?y Int)) (! (= (= (tm.and ?x ?y) tm.true) (and (= ?x tm.true) (= ?y tm.true))) :pattern ((tm.and ?x ?y)) )))
(assert (forall ((?x Int) (?y Int)) (! (= (= (tm.or ?x ?y) tm.true) (or (= ?x tm.true) (= ?y tm.true))) :pattern ((tm.or ?x ?y)) )))
(assert (forall ((?x Int) (?y Int)) (! (= (= (tm.iff ?x ?y) tm.true) (= (= ?x tm.true) (= ?y tm.true))) :pattern ((tm.iff ?x ?y)) )))
(assert (forall ((?x Int) (?y Int)) (! (= (= (tm.eq ?x ?y) tm.true) (= ?x ?y)) :pattern ((tm.eq ?x ?y)) )))
(assert (forall ((?x Int) (?y Int)) (! (= (= (tm.ne ?x ?y) tm.true) (not (= ?x ?y))) :pattern ((tm.ne ?x ?y)) )))
(assert (forall ((?x Int) (?y Int)) (! (= (= (tm.lt ?x ?y) tm.true) (< ?x ?y)) :pattern ((tm.lt ?x ?y)) )))
(assert (forall ((?x Int) (?y Int)) (! (= (= (tm.le ?x ?y) tm.true) (<= ?x ?y)) :pattern ((tm.le ?x ?y)) )))
(assert (forall ((?a Int) (?i Int) (?v Int)) (! (= (a.select (a.store ?a ?i ?v) ?i) ?v) :pattern ((a.select (a.store ?a ?i ?v) ?i)) )))
(assert (forall ((?a Int) (?i Int) (?v Int) (?j Int)) (! (or (= ?i ?j) (= (a.select (a.store ?a ?i ?v) ?j) (a.select ?a ?j))) :pattern ((a.select (a.store ?a ?i ?v) ?j)) )))
(assert (forall ((?i Int) (?v Int)) (! (= (a.select (a.mk_const_array ?v) ?i) ?v) :pattern ((a.select (a.mk_const_array ?v) ?i)) )))
(assert true)
(assert (<= privtypes__adminprivileget__first role))
(assert (<= role privtypes__adminprivileget__last))
(assert (not (and (<= privtypes__privileget__first role) (<= role privtypes__privileget__last))))
(check-sat)
(exit)
