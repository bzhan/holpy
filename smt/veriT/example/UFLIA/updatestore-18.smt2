(set-info :smt-lib-version 2.6)
(set-logic UFLIA)
(set-info :source |
      Tokeneer case study <http://www.adacore.com/home/products/gnatpro/tokeneer/>
  |)
(set-info :category "industrial")
(set-info :status unsat)
(declare-fun audittypes__admintokenexpired () Int)
(declare-fun audittypes__admintokeninvalid () Int)
(declare-fun audittypes__admintokenpresent () Int)
(declare-fun audittypes__admintokenremoved () Int)
(declare-fun audittypes__admintokenvalid () Int)
(declare-fun audittypes__alarmraised () Int)
(declare-fun audittypes__alarmsilenced () Int)
(declare-fun audittypes__archivecheckfailed () Int)
(declare-fun audittypes__archivecomplete () Int)
(declare-fun audittypes__archivelog () Int)
(declare-fun audittypes__auditalarmraised () Int)
(declare-fun audittypes__auditalarmsilenced () Int)
(declare-fun audittypes__authcertinvalid () Int)
(declare-fun audittypes__authcertvalid () Int)
(declare-fun audittypes__authcertwritefailed () Int)
(declare-fun audittypes__authcertwritten () Int)
(declare-fun audittypes__critical () Int)
(declare-fun audittypes__displaychanged () Int)
(declare-fun audittypes__doorclosed () Int)
(declare-fun audittypes__dooropened () Int)
(declare-fun audittypes__elementt__base__first () Int)
(declare-fun audittypes__elementt__base__last () Int)
(declare-fun audittypes__elementt__first () Int)
(declare-fun audittypes__elementt__last () Int)
(declare-fun audittypes__elementt__size () Int)
(declare-fun audittypes__enrolmentcomplete () Int)
(declare-fun audittypes__enrolmentfailed () Int)
(declare-fun audittypes__entrydenied () Int)
(declare-fun audittypes__entrypermitted () Int)
(declare-fun audittypes__entrytimeout () Int)
(declare-fun audittypes__fingerdetected () Int)
(declare-fun audittypes__fingermatched () Int)
(declare-fun audittypes__fingernotmatched () Int)
(declare-fun audittypes__fingertimeout () Int)
(declare-fun audittypes__information () Int)
(declare-fun audittypes__invalidconfigdata () Int)
(declare-fun audittypes__invalidoprequest () Int)
(declare-fun audittypes__latchlocked () Int)
(declare-fun audittypes__latchunlocked () Int)
(declare-fun audittypes__operationstart () Int)
(declare-fun audittypes__overridelock () Int)
(declare-fun audittypes__screenchanged () Int)
(declare-fun audittypes__severityt__base__first () Int)
(declare-fun audittypes__severityt__base__last () Int)
(declare-fun audittypes__severityt__first () Int)
(declare-fun audittypes__severityt__last () Int)
(declare-fun audittypes__severityt__size () Int)
(declare-fun audittypes__shutdown () Int)
(declare-fun audittypes__startenrolledtis () Int)
(declare-fun audittypes__startunenrolledtis () Int)
(declare-fun audittypes__systemfault () Int)
(declare-fun audittypes__truncatelog () Int)
(declare-fun audittypes__updatedconfigdata () Int)
(declare-fun audittypes__usertokeninvalid () Int)
(declare-fun audittypes__usertokenpresent () Int)
(declare-fun audittypes__usertokenremoved () Int)
(declare-fun audittypes__warning () Int)
(declare-fun certtypes__serialnumbert__base__first () Int)
(declare-fun certtypes__serialnumbert__base__last () Int)
(declare-fun certtypes__serialnumbert__first () Int)
(declare-fun certtypes__serialnumbert__last () Int)
(declare-fun certtypes__serialnumbert__size () Int)
(declare-fun nextserialnumber () Int)
(declare-fun init.nextserialnumber () Int)
(declare-fun storefile () Int)
(declare-fun init.storefile () Int)
(declare-fun audittypes__elementt__pos (Int) Int)
(declare-fun audittypes__elementt__pred (Int) Int)
(declare-fun audittypes__elementt__succ (Int) Int)
(declare-fun audittypes__elementt__val (Int) Int)
(declare-fun audittypes__severityt__pos (Int) Int)
(declare-fun audittypes__severityt__pred (Int) Int)
(declare-fun audittypes__severityt__succ (Int) Int)
(declare-fun audittypes__severityt__val (Int) Int)
(declare-fun bit__and (Int Int) Int)
(declare-fun bit__not (Int Int) Int)
(declare-fun bit__or (Int Int) Int)
(declare-fun bit__xor (Int Int) Int)
(declare-fun character__pos (Int) Int)
(declare-fun character__val (Int) Int)
(declare-fun integer__pred (Int) Int)
(declare-fun integer__succ (Int) Int)
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
(declare-fun |exists'| () Bool)
(declare-fun exists__1 () Bool)
(declare-fun init.exists__1 () Bool)
(declare-fun exists__2 () Bool)
(declare-fun init.exists__2 () Bool)
(declare-fun init.exists () Bool)
(declare-fun written () Bool)
(declare-fun written__3 () Bool)
(declare-fun init.written__3 () Bool)
(declare-fun init.written () Bool)
(declare-fun audittypes__elementt__LE (Int Int) Bool)
(declare-fun audittypes__elementt__LT (Int Int) Bool)
(declare-fun audittypes__severityt__LE (Int Int) Bool)
(declare-fun audittypes__severityt__LT (Int Int) Bool)
(declare-fun file__exists (Int) Bool)
(assert (forall ((?i Int)) (=> (and (<= 0 ?i) (< ?i 44)) (= (audittypes__elementt__pos ?i) ?i))))
(assert (forall ((?i Int)) (=> (and (<= 0 ?i) (< ?i 44)) (= (audittypes__elementt__val ?i) ?i))))
(assert (forall ((?i Int)) (=> (and (<= 0 ?i) (< ?i 43)) (= (audittypes__elementt__succ ?i) (+ ?i 1)))))
(assert (forall ((?i Int)) (=> (and (<= 1 ?i) (< ?i 44)) (= (audittypes__elementt__pred ?i) (- ?i 1)))))
(assert (= audittypes__startunenrolledtis 0))
(assert (= audittypes__startenrolledtis 1))
(assert (= audittypes__enrolmentcomplete 2))
(assert (= audittypes__enrolmentfailed 3))
(assert (= audittypes__displaychanged 4))
(assert (= audittypes__screenchanged 5))
(assert (= audittypes__doorclosed 6))
(assert (= audittypes__dooropened 7))
(assert (= audittypes__latchlocked 8))
(assert (= audittypes__latchunlocked 9))
(assert (= audittypes__alarmraised 10))
(assert (= audittypes__alarmsilenced 11))
(assert (= audittypes__truncatelog 12))
(assert (= audittypes__auditalarmraised 13))
(assert (= audittypes__auditalarmsilenced 14))
(assert (= audittypes__usertokenremoved 15))
(assert (= audittypes__usertokenpresent 16))
(assert (= audittypes__usertokeninvalid 17))
(assert (= audittypes__authcertvalid 18))
(assert (= audittypes__authcertinvalid 19))
(assert (= audittypes__fingerdetected 20))
(assert (= audittypes__fingertimeout 21))
(assert (= audittypes__fingermatched 22))
(assert (= audittypes__fingernotmatched 23))
(assert (= audittypes__authcertwritten 24))
(assert (= audittypes__authcertwritefailed 25))
(assert (= audittypes__entrypermitted 26))
(assert (= audittypes__entrytimeout 27))
(assert (= audittypes__entrydenied 28))
(assert (= audittypes__admintokenpresent 29))
(assert (= audittypes__admintokenvalid 30))
(assert (= audittypes__admintokeninvalid 31))
(assert (= audittypes__admintokenexpired 32))
(assert (= audittypes__admintokenremoved 33))
(assert (= audittypes__invalidoprequest 34))
(assert (= audittypes__operationstart 35))
(assert (= audittypes__archivelog 36))
(assert (= audittypes__archivecomplete 37))
(assert (= audittypes__archivecheckfailed 38))
(assert (= audittypes__updatedconfigdata 39))
(assert (= audittypes__invalidconfigdata 40))
(assert (= audittypes__shutdown 41))
(assert (= audittypes__overridelock 42))
(assert (= audittypes__systemfault 43))
(assert (forall ((?i Int)) (=> (and (<= 0 ?i) (< ?i 3)) (= (audittypes__severityt__pos ?i) ?i))))
(assert (forall ((?i Int)) (=> (and (<= 0 ?i) (< ?i 3)) (= (audittypes__severityt__val ?i) ?i))))
(assert (forall ((?i Int)) (=> (and (<= 0 ?i) (< ?i 2)) (= (audittypes__severityt__succ ?i) (+ ?i 1)))))
(assert (forall ((?i Int)) (=> (and (<= 1 ?i) (< ?i 3)) (= (audittypes__severityt__pred ?i) (- ?i 1)))))
(assert (= audittypes__information 0))
(assert (= audittypes__warning 1))
(assert (= audittypes__critical 2))
(assert (<= 0 audittypes__elementt__size))
(assert (= audittypes__elementt__first audittypes__startunenrolledtis))
(assert (= audittypes__elementt__last audittypes__systemfault))
(assert (= audittypes__elementt__base__first audittypes__startunenrolledtis))
(assert (= audittypes__elementt__base__last audittypes__systemfault))
(assert (<= 0 audittypes__severityt__size))
(assert (= audittypes__severityt__first audittypes__information))
(assert (= audittypes__severityt__last audittypes__critical))
(assert (= audittypes__severityt__base__first audittypes__information))
(assert (= audittypes__severityt__base__last audittypes__critical))
(assert (<= 0 certtypes__serialnumbert__size))
(assert (= certtypes__serialnumbert__first 0))
(assert (= certtypes__serialnumbert__last 4294967295))
(assert (<= certtypes__serialnumbert__base__first certtypes__serialnumbert__base__last))
(assert (<= certtypes__serialnumbert__base__first certtypes__serialnumbert__first))
(assert (<= certtypes__serialnumbert__last certtypes__serialnumbert__base__last))
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
(assert (<= certtypes__serialnumbert__first nextserialnumber))
(assert (<= nextserialnumber certtypes__serialnumbert__last))
(assert (< nextserialnumber certtypes__serialnumbert__last))
(assert (<= certtypes__serialnumbert__first (+ nextserialnumber 1)))
(assert (<= (+ nextserialnumber 1) certtypes__serialnumbert__last))
(assert true)
(assert (not (not (file__exists storefile))))
(assert true)
(assert (not true))
(assert true)
(assert true)
(assert (not (and true false)))
(assert (not (and (<= audittypes__severityt__first audittypes__warning) (<= audittypes__warning audittypes__severityt__last) (<= audittypes__elementt__first audittypes__systemfault) (<= audittypes__systemfault audittypes__elementt__last))))
(check-sat)
(exit)