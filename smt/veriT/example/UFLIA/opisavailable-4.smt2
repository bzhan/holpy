(set-info :smt-lib-version 2.6)
(set-logic UFLIA)
(set-info :source |
      Tokeneer case study <http://www.adacore.com/home/products/gnatpro/tokeneer/>
  |)
(set-info :category "industrial")
(set-info :status unsat)
(declare-fun field.datat.length () Int)
(declare-fun field.datat.minmatchlength () Int)
(declare-fun field.datat.text () Int)
(declare-fun field.keyboard__datat.length () Int)
(declare-fun field.keyboard__datat.text () Int)
(declare-fun field.t.rolepresent () Int)
(declare-fun field.t.currentop () Int)
(declare-fun archivelog () Int)
(declare-fun character__base__first () Int)
(declare-fun character__base__last () Int)
(declare-fun character__first () Int)
(declare-fun character__last () Int)
(declare-fun character__size () Int)
(declare-fun datai__base__first () Int)
(declare-fun datai__base__last () Int)
(declare-fun datai__first () Int)
(declare-fun datai__last () Int)
(declare-fun datai__size () Int)
(declare-fun datalengtht__base__first () Int)
(declare-fun datalengtht__base__last () Int)
(declare-fun datalengtht__first () Int)
(declare-fun datalengtht__last () Int)
(declare-fun datalengtht__size () Int)
(declare-fun integer__base__first () Int)
(declare-fun integer__base__last () Int)
(declare-fun integer__first () Int)
(declare-fun integer__last () Int)
(declare-fun integer__size () Int)
(declare-fun isavailable () Int)
(declare-fun keyboard__datai__base__first () Int)
(declare-fun keyboard__datai__base__last () Int)
(declare-fun keyboard__datai__first () Int)
(declare-fun keyboard__datai__last () Int)
(declare-fun keyboard__datai__size () Int)
(declare-fun keyboard__datalengtht__base__first () Int)
(declare-fun keyboard__datalengtht__base__last () Int)
(declare-fun keyboard__datalengtht__first () Int)
(declare-fun keyboard__datalengtht__last () Int)
(declare-fun keyboard__datalengtht__size () Int)
(declare-fun null__string () Int)
(declare-fun nullop () Int)
(declare-fun opandnullt__base__first () Int)
(declare-fun opandnullt__base__last () Int)
(declare-fun opandnullt__first () Int)
(declare-fun opandnullt__last () Int)
(declare-fun opandnullt__size () Int)
(declare-fun opt__base__first () Int)
(declare-fun opt__base__last () Int)
(declare-fun opt__first () Int)
(declare-fun opt__last () Int)
(declare-fun opt__size () Int)
(declare-fun optokeyed () Int)
(declare-fun overridelock () Int)
(declare-fun positive__base__first () Int)
(declare-fun positive__base__last () Int)
(declare-fun positive__first () Int)
(declare-fun positive__last () Int)
(declare-fun positive__size () Int)
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
(declare-fun keyedop () Int)
(declare-fun keyedop__entry__loop__2 () Int)
(declare-fun init.keyedop__entry__loop__2 () Int)
(declare-fun init.keyedop () Int)
(declare-fun loop__1__op () Int)
(declare-fun init.loop__1__op () Int)
(declare-fun loop__2__i () Int)
(declare-fun init.loop__2__i () Int)
(declare-fun theadmin () Int)
(declare-fun init.theadmin () Int)
(declare-fun theop () Int)
(declare-fun init.theop () Int)
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
(declare-fun matched () Bool)
(declare-fun init.matched () Bool)
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
(assert (forall ((?I Int)) (=> (and (<= archivelog ?I) (<= ?I shutdownop)) (<= datalengtht__first (a.select (a.select optokeyed ?I) field.datat.length)))))
(assert (forall ((?I Int)) (=> (and (<= archivelog ?I) (<= ?I shutdownop)) (<= (a.select (a.select optokeyed ?I) field.datat.length) datalengtht__last))))
(assert (forall ((?I Int)) (=> (and (<= archivelog ?I) (<= ?I shutdownop)) (<= datai__first (a.select (a.select optokeyed ?I) field.datat.minmatchlength)))))
(assert (forall ((?I Int)) (=> (and (<= archivelog ?I) (<= ?I shutdownop)) (<= (a.select (a.select optokeyed ?I) field.datat.minmatchlength) datai__last))))
(assert (forall ((?I Int) (?J Int)) (=> (and (<= archivelog ?I) (<= ?I shutdownop) (<= 1 ?J) (<= ?J 18)) (<= character__first (a.select (a.select (a.select optokeyed ?I) field.datat.text) ?J)))))
(assert (forall ((?I Int) (?J Int)) (=> (and (<= archivelog ?I) (<= ?I shutdownop) (<= 1 ?J) (<= ?J 18)) (<= (a.select (a.select (a.select optokeyed ?I) field.datat.text) ?J) character__last))))
(assert (<= 0 integer__size))
(assert (= integer__first (- 2147483648)))
(assert (= integer__last 2147483647))
(assert (= integer__base__first (- 2147483648)))
(assert (= integer__base__last 2147483647))
(assert (<= 0 character__size))
(assert (= character__first 0))
(assert (= character__last 255))
(assert (= character__base__first 0))
(assert (= character__base__last 255))
(assert (<= 0 positive__size))
(assert (= positive__first 1))
(assert (= positive__last 2147483647))
(assert (= positive__base__first (- 2147483648)))
(assert (= positive__base__last 2147483647))
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
(assert (<= 0 keyboard__datalengtht__size))
(assert (= keyboard__datalengtht__first 0))
(assert (= keyboard__datalengtht__last 78))
(assert (= keyboard__datalengtht__base__first (- 2147483648)))
(assert (= keyboard__datalengtht__base__last 2147483647))
(assert (<= 0 keyboard__datai__size))
(assert (= keyboard__datai__first 1))
(assert (= keyboard__datai__last 78))
(assert (= keyboard__datai__base__first (- 2147483648)))
(assert (= keyboard__datai__base__last 2147483647))
(assert (<= 0 opandnullt__size))
(assert (= opandnullt__first nullop))
(assert (= opandnullt__last shutdownop))
(assert (= opandnullt__base__first nullop))
(assert (= opandnullt__base__last shutdownop))
(assert (<= 0 opt__size))
(assert (= opt__first archivelog))
(assert (= opt__last shutdownop))
(assert (= opt__base__first nullop))
(assert (= opt__base__last shutdownop))
(assert (<= 0 datalengtht__size))
(assert (= datalengtht__first 0))
(assert (= datalengtht__last 18))
(assert (= datalengtht__base__first (- 2147483648)))
(assert (= datalengtht__base__last 2147483647))
(assert (<= 0 datai__size))
(assert (= datai__first 1))
(assert (= datai__last 18))
(assert (= datai__base__first (- 2147483648)))
(assert (= datai__base__last 2147483647))
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
(assert (distinct field.datat.length field.datat.minmatchlength field.datat.text))
(assert (distinct field.keyboard__datat.length field.keyboard__datat.text))
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
(assert (<= opt__first loop__1__op))
(assert (<= loop__1__op opt__last))
(assert (<= datai__first (a.select keyedop field.keyboard__datat.length)))
(assert (<= (a.select keyedop field.keyboard__datat.length) datai__last))
(assert (<= privtypes__adminprivileget__first (a.select theadmin field.t.rolepresent)))
(assert (<= (a.select theadmin field.t.rolepresent) privtypes__adminprivileget__last))
(assert (= theop nullop))
(assert (<= opandnullt__first (a.select theadmin field.t.currentop)))
(assert (<= (a.select theadmin field.t.currentop) opandnullt__last))
(assert (<= privtypes__privileget__first (a.select theadmin field.t.rolepresent)))
(assert (<= (a.select theadmin field.t.rolepresent) privtypes__privileget__last))
(assert (forall ((?i___1 Int)) (let ((?v_0 (a.select (a.select keyedop field.keyboard__datat.text) ?i___1))) (=> (and (<= keyboard__datai__first ?i___1) (<= ?i___1 keyboard__datai__last)) (and (<= character__first ?v_0) (<= ?v_0 character__last))))))
(assert (<= keyboard__datalengtht__first (a.select keyedop field.keyboard__datat.length)))
(assert (<= (a.select keyedop field.keyboard__datat.length) keyboard__datalengtht__last))
(assert (ispresent theadmin))
(assert (<= opt__first loop__1__op))
(assert (<= loop__1__op opt__last))
(assert (<= loop__1__op opt__last))
(assert (<= integer__first (a.select keyedop field.keyboard__datat.length)))
(assert (<= (a.select keyedop field.keyboard__datat.length) integer__last))
(assert (<= integer__first 1))
(assert (<= 1 integer__last))
(assert (let ((?v_0 (a.select keyedop field.keyboard__datat.length))) (=> (<= 1 ?v_0) (and (<= datai__first ?v_0) (<= ?v_0 datai__last)))))
(assert (=> (<= 1 (a.select keyedop field.keyboard__datat.length)) (and (<= datai__first 1) (<= 1 datai__last))))
(assert (not (<= 1 (a.select keyedop field.keyboard__datat.length))))
(assert true)
(assert (not true))
(assert (not (= loop__1__op opt__last)))
(assert (let ((?v_3 (a.select keyedop field.keyboard__datat.length)) (?v_1 (a.select theadmin field.t.rolepresent)) (?v_2 (a.select theadmin field.t.currentop)) (?v_0 (opandnullt__succ loop__1__op))) (let ((?v_4 (<= opt__first ?v_0)) (?v_5 (<= ?v_0 opt__last))) (not (and ?v_4 ?v_5 (<= privtypes__adminprivileget__first ?v_1) (<= ?v_1 privtypes__adminprivileget__last) (= theop nullop) (<= opandnullt__first ?v_2) (<= ?v_2 opandnullt__last) (<= privtypes__privileget__first ?v_1) (<= ?v_1 privtypes__privileget__last) (forall ((?i___1 Int)) (let ((?v_6 (a.select (a.select keyedop field.keyboard__datat.text) ?i___1))) (=> (and (<= keyboard__datai__first ?i___1) (<= ?i___1 keyboard__datai__last)) (and (<= character__first ?v_6) (<= ?v_6 character__last))))) (<= keyboard__datalengtht__first ?v_3) (<= ?v_3 keyboard__datalengtht__last) (ispresent theadmin) ?v_4 ?v_5 ?v_5)))))
(check-sat)
(exit)
