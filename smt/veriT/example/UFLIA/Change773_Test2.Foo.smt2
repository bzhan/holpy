(set-info :smt-lib-version 2.6)
(set-logic UFLIA)
(set-info :source | 
  Boogie/Spec# benchmarks.
  This benchmark was translated by Michal Moskal.
|)
(set-info :category "industrial")
(set-info :status unsat)
(declare-fun boolIff (Int Int) Int)
(declare-fun PeerGroupPlaceholder_ () Int)
(declare-fun intGreater (Int Int) Int)
(declare-fun IfThenElse_ (Int Int Int) Int)
(declare-fun CONCVARSYM (Int) Int)
(declare-fun SharingMode_Unshared_ () Int)
(declare-fun int_m2147483648 () Int)
(declare-fun System.Int32 () Int)
(declare-fun intAtMost (Int Int) Int)
(declare-fun multiply (Int Int) Int)
(declare-fun Is_ (Int Int) Int)
(declare-fun Smt.true () Int)
(declare-fun ElementType_ (Int) Int)
(declare-fun divide (Int Int) Int)
(declare-fun int_m9223372036854775808 () Int)
(declare-fun divides (Int Int) Int)
(declare-fun select1 (Int Int) Int)
(declare-fun store1 (Int Int Int) Int)
(declare-fun select2 (Int Int Int) Int)
(declare-fun nullObject () Int)
(declare-fun store2 (Int Int Int Int) Int)
(declare-fun modulo (Int Int) Int)
(declare-fun ownerRef_ () Int)
(declare-fun StructSet_ (Int Int Int) Int)
(declare-fun AsDirectSubClass (Int Int) Int)
(declare-fun System.Boolean () Int)
(declare-fun shl_ (Int Int) Int)
(declare-fun DimLength_ (Int Int) Int)
(declare-fun anyEqual (Int Int) Int)
(declare-fun System.Array () Int)
(declare-fun Test1 () Int)
(declare-fun Test2 () Int)
(declare-fun SharingMode_LockProtected_ () Int)
(declare-fun IsMemberlessType_ (Int) Int)
(declare-fun System.UInt16 () Int)
(declare-fun ClassRepr (Int) Int)
(declare-fun boolNot (Int) Int)
(declare-fun block3315_correct () Int)
(declare-fun boolAnd (Int Int) Int)
(declare-fun boolImplies (Int Int) Int)
(declare-fun Unbox (Int) Int)
(declare-fun intAtLeast (Int Int) Int)
(declare-fun block3349_correct () Int)
(declare-fun ownerFrame_ () Int)
(declare-fun int_4294967295 () Int)
(declare-fun IsAllocated (Int Int) Int)
(declare-fun TypeName (Int) Int)
(declare-fun AsPeerField (Int) Int)
(declare-fun int_9223372036854775807 () Int)
(declare-fun AsRepField (Int Int) Int)
(declare-fun ArrayCategoryValue_ () Int)
(declare-fun is (Int Int) Int)
(declare-fun InRange (Int Int) Bool)
(declare-fun AsOwner (Int Int) Int)
(declare-fun System.Int64 () Int)
(declare-fun or_ (Int Int) Int)
(declare-fun As_ (Int Int) Int)
(declare-fun exposeVersion_ () Int)
(declare-fun System.Type () Int)
(declare-fun intLess (Int Int) Int)
(declare-fun AsImmutable_ (Int) Int)
(declare-fun NonNullFieldsAreInitialized_ () Int)
(declare-fun LBound_ (Int Int) Int)
(declare-fun System.Object () Int)
(declare-fun System.UInt32 () Int)
(declare-fun localinv_ () Int)
(declare-fun inv_ () Int)
(declare-fun Heap_0_ () Int)
(declare-fun entry_correct () Int)
(declare-fun FirstConsistentOwner_ () Int)
(declare-fun UnboxedType (Int) Int)
(declare-fun AsRefField (Int Int) Int)
(declare-fun block3298_correct () Int)
(declare-fun System.Byte () Int)
(declare-fun int_2147483647 () Int)
(declare-fun ArrayCategoryRef_ () Int)
(declare-fun Heap_ () Int)
(declare-fun Length_ (Int) Int)
(declare-fun AsNonNullRefField (Int Int) Int)
(declare-fun IsHeap (Int) Int)
(declare-fun UBound_ (Int Int) Int)
(declare-fun System.String () Int)
(declare-fun System.String.IsInterned_System.String_notnull_ (Int) Int)
(declare-fun UnknownRef_ () Int)
(declare-fun Rank_ (Int) Int)
(declare-fun RefArraySet (Int Int Int) Int)
(declare-fun ValueArraySet (Int Int Int) Int)
(declare-fun boolOr (Int Int) Int)
(declare-fun sharingMode_ () Int)
(declare-fun subtypes (Int Int) Bool)
(declare-fun System.String.Equals_System.String_System.String_ (Int Int) Int)
(declare-fun anyNeq (Int Int) Int)
(declare-fun IsStaticField (Int) Int)
(declare-fun IsNotNull_ (Int Int) Int)
(declare-fun typeof_ (Int) Int)
(declare-fun ArrayCategoryNonNullRef_ () Int)
(declare-fun RefArrayGet (Int Int) Int)
(declare-fun ValueArrayGet (Int Int) Int)
(declare-fun TypeObject (Int) Int)
(declare-fun and_ (Int Int) Int)
(declare-fun BoxTester (Int Int) Int)
(declare-fun IsValueType_ (Int) Int)
(declare-fun AsRangeField (Int Int) Int)
(declare-fun System.SByte () Int)
(declare-fun BeingConstructed_ () Int)
(declare-fun FieldDependsOnFCO_ (Int Int Int) Int)
(declare-fun NonNullRefArray (Int Int) Int)
(declare-fun RefArray (Int Int) Int)
(declare-fun ArrayCategory_ (Int) Int)
(declare-fun block3332_correct () Int)
(declare-fun AsPureObject_ (Int) Int)
(declare-fun System.String.Equals_System.String_ (Int Int) Int)
(declare-fun System.Int16 () Int)
(declare-fun AsMutable_ (Int) Int)
(declare-fun System.Char () Int)
(declare-fun System.UInt64 () Int)
(declare-fun StructGet_ (Int Int) Int)
(declare-fun OneClassDown (Int Int) Int)
(declare-fun ArrayIndex (Int Int Int Int) Int)
(declare-fun Box (Int Int) Int)
(declare-fun int_18446744073709551615 () Int)
(declare-fun shr_ (Int Int) Int)
(declare-fun IsDirectlyModifiableField (Int) Int)
(declare-fun StringLength_ (Int) Int)
(declare-fun allocated_ () Int)
(declare-fun xs_0 () Int)
(declare-fun i_0 () Int)
(declare-fun BaseClass_ (Int) Int)
(declare-fun ValueArray (Int Int) Int)
(declare-fun Smt.false () Int)
(declare-fun IsImmutable_ (Int) Int)
(declare-fun elements_ () Int)
(declare-fun block3281_correct () Int)
(declare-fun DeclType (Int) Int)
(declare-fun ReallyLastGeneratedExit_correct () Int)
(assert (distinct allocated_ elements_ inv_ localinv_ exposeVersion_ sharingMode_ SharingMode_Unshared_ SharingMode_LockProtected_ ownerRef_ ownerFrame_ PeerGroupPlaceholder_ ArrayCategoryValue_ ArrayCategoryRef_ ArrayCategoryNonNullRef_ System.Array System.Object System.Type BeingConstructed_ NonNullFieldsAreInitialized_ System.String FirstConsistentOwner_ System.SByte System.Byte System.Int16 System.UInt16 System.Int32 System.UInt32 System.Int64 System.UInt64 System.Char int_m2147483648 int_2147483647 int_4294967295 int_m9223372036854775808 int_9223372036854775807 int_18446744073709551615 UnknownRef_ System.Boolean Test2 Test1))
(assert (= (DeclType exposeVersion_) System.Object))
(assert (forall ((?c0 Int) (?c1 Int)) (! (=> (not (= ?c0 ?c1)) (not (= (ClassRepr ?c0) (ClassRepr ?c1)))) :pattern ((ClassRepr ?c0) (ClassRepr ?c1)) )))
(assert (forall ((?T Int)) (not (subtypes (typeof_ (ClassRepr ?T)) System.Object))))
(assert (forall ((?T Int)) (not (= (ClassRepr ?T) nullObject))))
(assert (forall ((?T Int) (?h Int)) (! (=> (= (IsHeap ?h) Smt.true) (= (select2 ?h (ClassRepr ?T) ownerFrame_) PeerGroupPlaceholder_)) :pattern ((select2 ?h (ClassRepr ?T) ownerFrame_)) )))
(assert (not (= (IsDirectlyModifiableField allocated_) Smt.true)))
(assert (= (IsDirectlyModifiableField elements_) Smt.true))
(assert (not (= (IsDirectlyModifiableField inv_) Smt.true)))
(assert (not (= (IsDirectlyModifiableField localinv_) Smt.true)))
(assert (not (= (IsDirectlyModifiableField ownerRef_) Smt.true)))
(assert (not (= (IsDirectlyModifiableField ownerFrame_) Smt.true)))
(assert (not (= (IsDirectlyModifiableField exposeVersion_) Smt.true)))
(assert (not (= (IsStaticField allocated_) Smt.true)))
(assert (not (= (IsStaticField elements_) Smt.true)))
(assert (not (= (IsStaticField inv_) Smt.true)))
(assert (not (= (IsStaticField localinv_) Smt.true)))
(assert (not (= (IsStaticField exposeVersion_) Smt.true)))
(assert (forall ((?A Int) (?i Int) (?x Int)) (= (ValueArrayGet (ValueArraySet ?A ?i ?x) ?i) ?x)))
(assert (forall ((?A Int) (?i Int) (?j Int) (?x Int)) (=> (not (= ?i ?j)) (= (ValueArrayGet (ValueArraySet ?A ?i ?x) ?j) (ValueArrayGet ?A ?j)))))
(assert (forall ((?A Int) (?i Int) (?x Int)) (= (RefArrayGet (RefArraySet ?A ?i ?x) ?i) ?x)))
(assert (forall ((?A Int) (?i Int) (?j Int) (?x Int)) (=> (not (= ?i ?j)) (= (RefArrayGet (RefArraySet ?A ?i ?x) ?j) (RefArrayGet ?A ?j)))))
(assert (forall ((?a Int) (?d Int) (?x Int) (?y Int) (|?x'| Int) (|?y'| Int)) (! (=> (= (ArrayIndex ?a ?d ?x ?y) (ArrayIndex ?a ?d |?x'| |?y'|)) (and (= ?x |?x'|) (= ?y |?y'|))) :pattern ((ArrayIndex ?a ?d ?x ?y) (ArrayIndex ?a ?d |?x'| |?y'|)) )))
(assert (forall ((?a Int) (?T Int) (?i Int) (?r Int) (?heap Int)) (! (=> (and (= (IsHeap ?heap) Smt.true) (subtypes (typeof_ ?a) (RefArray ?T ?r))) (= (Is_ (RefArrayGet (select2 ?heap ?a elements_) ?i) ?T) Smt.true)) :pattern ((subtypes (typeof_ ?a) (RefArray ?T ?r)) (RefArrayGet (select2 ?heap ?a elements_) ?i)) )))
(assert (forall ((?a Int) (?T Int) (?i Int) (?r Int) (?heap Int)) (! (=> (and (= (IsHeap ?heap) Smt.true) (subtypes (typeof_ ?a) (NonNullRefArray ?T ?r))) (= (IsNotNull_ (RefArrayGet (select2 ?heap ?a elements_) ?i) ?T) Smt.true)) :pattern ((subtypes (typeof_ ?a) (NonNullRefArray ?T ?r)) (RefArrayGet (select2 ?heap ?a elements_) ?i)) )))
(assert (forall ((?a Int)) (<= 1 (Rank_ ?a))))
(assert (forall ((?a Int) (?T Int) (?r Int)) (! (=> (and (not (= ?a nullObject)) (subtypes (typeof_ ?a) (RefArray ?T ?r))) (= (Rank_ ?a) ?r)) :pattern ((subtypes (typeof_ ?a) (RefArray ?T ?r))) )))
(assert (forall ((?a Int) (?T Int) (?r Int)) (! (=> (and (not (= ?a nullObject)) (subtypes (typeof_ ?a) (NonNullRefArray ?T ?r))) (= (Rank_ ?a) ?r)) :pattern ((subtypes (typeof_ ?a) (NonNullRefArray ?T ?r))) )))
(assert (forall ((?a Int) (?T Int) (?r Int)) (! (=> (and (not (= ?a nullObject)) (subtypes (typeof_ ?a) (ValueArray ?T ?r))) (= (Rank_ ?a) ?r)) :pattern ((subtypes (typeof_ ?a) (ValueArray ?T ?r))) )))
(assert (forall ((?a Int)) (! (<= 0 (Length_ ?a)) :pattern ((Length_ ?a)) )))
(assert (forall ((?a Int) (?i Int)) (<= 0 (DimLength_ ?a ?i))))
(assert (forall ((?a Int)) (! (=> (= (Rank_ ?a) 1) (= (DimLength_ ?a 0) (Length_ ?a))) :pattern ((DimLength_ ?a 0)) )))
(assert (forall ((?a Int) (?i Int)) (! (= (LBound_ ?a ?i) 0) :pattern ((LBound_ ?a ?i)) )))
(assert (forall ((?a Int) (?i Int)) (! (= (UBound_ ?a ?i) (- (DimLength_ ?a ?i) 1)) :pattern ((UBound_ ?a ?i)) )))
(assert (forall ((?T Int) (?ET Int) (?r Int)) (! (=> (subtypes ?T (ValueArray ?ET ?r)) (= (ArrayCategory_ ?T) ArrayCategoryValue_)) :pattern ((subtypes ?T (ValueArray ?ET ?r))) )))
(assert (forall ((?T Int) (?ET Int) (?r Int)) (! (=> (subtypes ?T (RefArray ?ET ?r)) (= (ArrayCategory_ ?T) ArrayCategoryRef_)) :pattern ((subtypes ?T (RefArray ?ET ?r))) )))
(assert (forall ((?T Int) (?ET Int) (?r Int)) (! (=> (subtypes ?T (NonNullRefArray ?ET ?r)) (= (ArrayCategory_ ?T) ArrayCategoryNonNullRef_)) :pattern ((subtypes ?T (NonNullRefArray ?ET ?r))) )))
(assert (subtypes System.Array System.Object))
(assert (forall ((?T Int) (?r Int)) (! (subtypes (ValueArray ?T ?r) System.Array) :pattern ((ValueArray ?T ?r)) )))
(assert (forall ((?T Int) (?r Int)) (! (subtypes (RefArray ?T ?r) System.Array) :pattern ((RefArray ?T ?r)) )))
(assert (forall ((?T Int) (?r Int)) (! (subtypes (NonNullRefArray ?T ?r) System.Array) :pattern ((NonNullRefArray ?T ?r)) )))
(assert (forall ((?T Int) (?U Int) (?r Int)) (=> (subtypes ?U ?T) (subtypes (RefArray ?U ?r) (RefArray ?T ?r)))))
(assert (forall ((?T Int) (?U Int) (?r Int)) (=> (subtypes ?U ?T) (subtypes (NonNullRefArray ?U ?r) (NonNullRefArray ?T ?r)))))
(assert (forall ((?A Int) (?r Int)) (= (ElementType_ (ValueArray ?A ?r)) ?A)))
(assert (forall ((?A Int) (?r Int)) (= (ElementType_ (RefArray ?A ?r)) ?A)))
(assert (forall ((?A Int) (?r Int)) (= (ElementType_ (NonNullRefArray ?A ?r)) ?A)))
(assert (forall ((?A Int) (?r Int) (?T Int)) (! (let ((?v_0 (ElementType_ ?T))) (=> (subtypes ?T (RefArray ?A ?r)) (and (= ?T (RefArray ?v_0 ?r)) (subtypes ?v_0 ?A)))) :pattern ((subtypes ?T (RefArray ?A ?r))) )))
(assert (forall ((?A Int) (?r Int) (?T Int)) (! (let ((?v_0 (ElementType_ ?T))) (=> (subtypes ?T (NonNullRefArray ?A ?r)) (and (= ?T (NonNullRefArray ?v_0 ?r)) (subtypes ?v_0 ?A)))) :pattern ((subtypes ?T (NonNullRefArray ?A ?r))) )))
(assert (forall ((?A Int) (?r Int) (?T Int)) (let ((?v_0 (ValueArray ?A ?r))) (=> (subtypes ?T ?v_0) (= ?T ?v_0)))))
(assert (forall ((?A Int) (?r Int) (?T Int)) (let ((?v_0 (ElementType_ ?T))) (=> (subtypes (RefArray ?A ?r) ?T) (or (subtypes System.Array ?T) (and (= ?T (RefArray ?v_0 ?r)) (subtypes ?A ?v_0)))))))
(assert (forall ((?A Int) (?r Int) (?T Int)) (let ((?v_0 (ElementType_ ?T))) (=> (subtypes (NonNullRefArray ?A ?r) ?T) (or (subtypes System.Array ?T) (and (= ?T (NonNullRefArray ?v_0 ?r)) (subtypes ?A ?v_0)))))))
(assert (forall ((?A Int) (?r Int) (?T Int)) (let ((?v_0 (ValueArray ?A ?r))) (=> (subtypes ?v_0 ?T) (or (subtypes System.Array ?T) (= ?T ?v_0))))))
(assert (forall ((?s Int) (?f Int) (?x Int)) (= (StructGet_ (StructSet_ ?s ?f ?x) ?f) ?x)))
(assert (forall ((?s Int) (?f Int) (|?f'| Int) (?x Int)) (=> (not (= ?f |?f'|)) (= (StructGet_ (StructSet_ ?s ?f ?x) |?f'|) (StructGet_ ?s |?f'|)))))
(assert (forall ((?A Int) (?B Int) (?C Int)) (! (=> (subtypes ?C (AsDirectSubClass ?B ?A)) (= (OneClassDown ?C ?A) ?B)) :pattern ((subtypes ?C (AsDirectSubClass ?B ?A))) )))
(assert (forall ((?T Int)) (=> (= (IsValueType_ ?T) Smt.true) (and (forall ((?U Int)) (=> (subtypes ?T ?U) (= ?T ?U))) (forall ((?U Int)) (=> (subtypes ?U ?T) (= ?T ?U)))))))
(assert (subtypes System.Type System.Object))
(assert (forall ((?T Int)) (! (= (IsNotNull_ (TypeObject ?T) System.Type) Smt.true) :pattern ((TypeObject ?T)) )))
(assert (forall ((?T Int)) (! (= (TypeName (TypeObject ?T)) ?T) :pattern ((TypeObject ?T)) )))
(assert (forall ((?o Int) (?T Int)) (! (= (= (Is_ ?o ?T) Smt.true) (or (= ?o nullObject) (subtypes (typeof_ ?o) ?T))) :pattern ((Is_ ?o ?T)) )))
(assert (forall ((?o Int) (?T Int)) (! (= (= (IsNotNull_ ?o ?T) Smt.true) (and (not (= ?o nullObject)) (= (Is_ ?o ?T) Smt.true))) :pattern ((IsNotNull_ ?o ?T)) )))
(assert (forall ((?o Int) (?T Int)) (=> (= (Is_ ?o ?T) Smt.true) (= (As_ ?o ?T) ?o))))
(assert (forall ((?o Int) (?T Int)) (=> (not (= (Is_ ?o ?T) Smt.true)) (= (As_ ?o ?T) nullObject))))
(assert (forall ((?h Int) (?o Int)) (! (let ((?v_0 (typeof_ ?o))) (=> (and (= (IsHeap ?h) Smt.true) (not (= ?o nullObject)) (subtypes ?v_0 System.Array)) (and (= (select2 ?h ?o inv_) ?v_0) (= (select2 ?h ?o localinv_) ?v_0)))) :pattern ((select2 ?h ?o inv_)) )))
(assert (forall ((?h Int) (?o Int) (?f Int)) (! (=> (and (= (IsHeap ?h) Smt.true) (= (select2 ?h ?o allocated_) Smt.true)) (= (IsAllocated ?h (select2 ?h ?o ?f)) Smt.true)) :pattern ((IsAllocated ?h (select2 ?h ?o ?f))) )))
(assert (forall ((?h Int) (?o Int) (?f Int)) (! (=> (and (= (IsHeap ?h) Smt.true) (= (select2 ?h ?o allocated_) Smt.true)) (= (select2 ?h (select2 ?h ?o ?f) allocated_) Smt.true)) :pattern ((select2 ?h (select2 ?h ?o ?f) allocated_)) )))
(assert (forall ((?h Int) (?s Int) (?f Int)) (! (=> (= (IsAllocated ?h ?s) Smt.true) (= (IsAllocated ?h (StructGet_ ?s ?f)) Smt.true)) :pattern ((IsAllocated ?h (StructGet_ ?s ?f))) )))
(assert (forall ((?h Int) (?e Int) (?i Int)) (! (=> (= (IsAllocated ?h ?e) Smt.true) (= (IsAllocated ?h (RefArrayGet ?e ?i)) Smt.true)) :pattern ((IsAllocated ?h (RefArrayGet ?e ?i))) )))
(assert (forall ((?h Int) (?e Int) (?i Int)) (! (=> (= (IsAllocated ?h ?e) Smt.true) (= (IsAllocated ?h (ValueArrayGet ?e ?i)) Smt.true)) :pattern ((IsAllocated ?h (ValueArrayGet ?e ?i))) )))
(assert (forall ((?h Int) (?o Int)) (! (=> (= (IsAllocated ?h ?o) Smt.true) (= (select2 ?h ?o allocated_) Smt.true)) :pattern ((select2 ?h ?o allocated_)) )))
(assert (forall ((?h Int) (?c Int)) (! (=> (= (IsHeap ?h) Smt.true) (= (select2 ?h (ClassRepr ?c) allocated_) Smt.true)) :pattern ((select2 ?h (ClassRepr ?c) allocated_)) )))
(assert (forall ((?f Int) (?T Int)) (! (=> (= (AsNonNullRefField ?f ?T) ?f) (= (AsRefField ?f ?T) ?f)) :pattern ((AsNonNullRefField ?f ?T)) )))
(assert (forall ((?h Int) (?o Int) (?f Int) (?T Int)) (! (=> (= (IsHeap ?h) Smt.true) (= (Is_ (select2 ?h ?o (AsRefField ?f ?T)) ?T) Smt.true)) :pattern ((select2 ?h ?o (AsRefField ?f ?T))) )))
(assert (forall ((?h Int) (?o Int) (?f Int) (?T Int)) (! (=> (and (= (IsHeap ?h) Smt.true) (not (= ?o nullObject)) (or (not (= ?o BeingConstructed_)) (= (= (select2 ?h BeingConstructed_ NonNullFieldsAreInitialized_) Smt.true) true))) (not (= (select2 ?h ?o (AsNonNullRefField ?f ?T)) nullObject))) :pattern ((select2 ?h ?o (AsNonNullRefField ?f ?T))) )))
(assert (forall ((?h Int) (?o Int) (?f Int) (?T Int)) (! (=> (= (IsHeap ?h) Smt.true) (InRange (select2 ?h ?o (AsRangeField ?f ?T)) ?T)) :pattern ((select2 ?h ?o (AsRangeField ?f ?T))) )))
(assert (forall ((?o Int)) (! (not (= (IsMemberlessType_ (typeof_ ?o)) Smt.true)) :pattern ((IsMemberlessType_ (typeof_ ?o))) )))
(assert (not (= (IsImmutable_ System.Object) Smt.true)))
(assert (forall ((?T Int) (?U Int)) (! (=> (subtypes ?U (AsImmutable_ ?T)) (and (= (IsImmutable_ ?U) Smt.true) (= (AsImmutable_ ?U) ?U))) :pattern ((subtypes ?U (AsImmutable_ ?T))) )))
(assert (forall ((?T Int) (?U Int)) (! (=> (subtypes ?U (AsMutable_ ?T)) (and (not (= (IsImmutable_ ?U) Smt.true)) (= (AsMutable_ ?U) ?U))) :pattern ((subtypes ?U (AsMutable_ ?T))) )))
(assert (forall ((?o Int) (?T Int)) (! (=> (and (not (= ?o nullObject)) (not (= ?o BeingConstructed_)) (subtypes (typeof_ ?o) (AsImmutable_ ?T))) (forall ((?h Int)) (! (let ((?v_0 (typeof_ ?o))) (=> (= (IsHeap ?h) Smt.true) (and (= (select2 ?h ?o inv_) ?v_0) (= (select2 ?h ?o localinv_) ?v_0) (= (select2 ?h ?o ownerFrame_) PeerGroupPlaceholder_) (= (AsOwner ?o (select2 ?h ?o ownerRef_)) ?o) (forall ((?t Int)) (! (=> (= (AsOwner ?o (select2 ?h ?t ownerRef_)) ?o) (or (= ?t ?o) (not (= (select2 ?h ?t ownerFrame_) PeerGroupPlaceholder_)))) :pattern ((AsOwner ?o (select2 ?h ?t ownerRef_))) ))))) :pattern ((IsHeap ?h)) ))) :pattern ((subtypes (typeof_ ?o) (AsImmutable_ ?T))) )))
(assert (forall ((?s Int)) (! (<= 0 (StringLength_ ?s)) :pattern ((StringLength_ ?s)) )))
(assert (forall ((?h Int) (?o Int) (?f Int) (?T Int)) (! (let ((?v_0 (select2 ?h ?o (AsRepField ?f ?T)))) (=> (and (= (IsHeap ?h) Smt.true) (not (= ?v_0 nullObject))) (and (= (select2 ?h ?v_0 ownerRef_) ?o) (= (select2 ?h ?v_0 ownerFrame_) ?T)))) :pattern ((select2 ?h ?o (AsRepField ?f ?T))) )))
(assert (forall ((?h Int) (?o Int) (?f Int)) (! (let ((?v_0 (select2 ?h ?o (AsPeerField ?f)))) (=> (and (= (IsHeap ?h) Smt.true) (not (= ?v_0 nullObject))) (and (= (select2 ?h ?v_0 ownerRef_) (select2 ?h ?o ownerRef_)) (= (select2 ?h ?v_0 ownerFrame_) (select2 ?h ?o ownerFrame_))))) :pattern ((select2 ?h ?o (AsPeerField ?f))) )))
(assert (forall ((?h Int) (?o Int)) (let ((?v_0 (select2 ?h ?o ownerFrame_)) (?v_1 (select2 ?h ?o ownerRef_)) (?v_2 (typeof_ ?o))) (=> (and (= (IsHeap ?h) Smt.true) (not (= ?v_0 PeerGroupPlaceholder_)) (subtypes (select2 ?h ?v_1 inv_) ?v_0) (not (= (select2 ?h ?v_1 localinv_) (BaseClass_ ?v_0)))) (and (= (select2 ?h ?o inv_) ?v_2) (= (select2 ?h ?o localinv_) ?v_2))))))
(assert (forall ((?o Int) (?f Int) (?h Int)) (! (let ((?v_0 (select2 ?h ?o ownerFrame_)) (?v_1 (select2 ?h ?o ownerRef_))) (=> (and (= (IsHeap ?h) Smt.true) (not (= ?o nullObject)) (= (= (select2 ?h ?o allocated_) Smt.true) true) (not (= ?v_0 PeerGroupPlaceholder_)) (subtypes (select2 ?h ?v_1 inv_) ?v_0) (not (= (select2 ?h ?v_1 localinv_) (BaseClass_ ?v_0)))) (= (select2 ?h ?o ?f) (FieldDependsOnFCO_ ?o ?f (select2 ?h (select2 ?h ?o FirstConsistentOwner_) exposeVersion_))))) :pattern ((select2 ?h (AsPureObject_ ?o) ?f)) )))
(assert (forall ((?o Int) (?h Int)) (! (let ((?v_0 (select2 ?h ?o ownerFrame_)) (?v_1 (select2 ?h ?o ownerRef_)) (?v_2 (select2 ?h ?o FirstConsistentOwner_))) (let ((?v_3 (select2 ?h ?v_2 ownerFrame_)) (?v_4 (select2 ?h ?v_2 ownerRef_))) (=> (and (= (IsHeap ?h) Smt.true) (not (= ?o nullObject)) (= (= (select2 ?h ?o allocated_) Smt.true) true) (not (= ?v_0 PeerGroupPlaceholder_)) (subtypes (select2 ?h ?v_1 inv_) ?v_0) (not (= (select2 ?h ?v_1 localinv_) (BaseClass_ ?v_0)))) (and (not (= ?v_2 nullObject)) (= (= (select2 ?h ?v_2 allocated_) Smt.true) true) (or (= ?v_3 PeerGroupPlaceholder_) (not (subtypes (select2 ?h ?v_4 inv_) ?v_3)) (= (select2 ?h ?v_4 localinv_) (BaseClass_ ?v_3))))))) :pattern ((select2 ?h ?o FirstConsistentOwner_)) )))
(assert (forall ((?x Int) (?p Int)) (! (= (Unbox (Box ?x ?p)) ?x) :pattern ((Unbox (Box ?x ?p))) )))
(assert (forall ((?p Int)) (! (=> (= (IsValueType_ (UnboxedType ?p)) Smt.true) (forall ((?heap Int) (?x Int)) (let ((?v_0 (Box ?x ?p))) (let ((?v_1 (typeof_ ?v_0))) (=> (= (IsHeap ?heap) Smt.true) (and (= (select2 ?heap ?v_0 inv_) ?v_1) (= (select2 ?heap ?v_0 localinv_) ?v_1))))))) :pattern ((IsValueType_ (UnboxedType ?p))) )))
(assert (forall ((?x Int) (?p Int)) (let ((?v_0 (Box ?x ?p))) (=> (and (subtypes (UnboxedType ?v_0) System.Object) (= ?v_0 ?p)) (= ?x ?p)))))
(assert (forall ((?p Int) (?typ Int)) (! (= (= (UnboxedType ?p) ?typ) (not (= (BoxTester ?p ?typ) nullObject))) :pattern ((BoxTester ?p ?typ)) )))
(assert (= (IsValueType_ System.SByte) Smt.true))
(assert (= (IsValueType_ System.Byte) Smt.true))
(assert (= (IsValueType_ System.Int16) Smt.true))
(assert (= (IsValueType_ System.UInt16) Smt.true))
(assert (= (IsValueType_ System.Int32) Smt.true))
(assert (= (IsValueType_ System.UInt32) Smt.true))
(assert (= (IsValueType_ System.Int64) Smt.true))
(assert (= (IsValueType_ System.UInt64) Smt.true))
(assert (= (IsValueType_ System.Char) Smt.true))
(assert (< int_m9223372036854775808 int_m2147483648))
(assert (< int_m2147483648 (- 0 100000)))
(assert (< 100000 int_2147483647))
(assert (< int_2147483647 int_4294967295))
(assert (< int_4294967295 int_9223372036854775807))
(assert (< int_9223372036854775807 int_18446744073709551615))
(assert (forall ((?i Int)) (= (InRange ?i System.SByte) (and (<= (- 0 128) ?i) (< ?i 128)))))
(assert (forall ((?i Int)) (= (InRange ?i System.Byte) (and (<= 0 ?i) (< ?i 256)))))
(assert (forall ((?i Int)) (= (InRange ?i System.Int16) (and (<= (- 0 32768) ?i) (< ?i 32768)))))
(assert (forall ((?i Int)) (= (InRange ?i System.UInt16) (and (<= 0 ?i) (< ?i 65536)))))
(assert (forall ((?i Int)) (= (InRange ?i System.Int32) (and (<= int_m2147483648 ?i) (<= ?i int_2147483647)))))
(assert (forall ((?i Int)) (= (InRange ?i System.UInt32) (and (<= 0 ?i) (<= ?i int_4294967295)))))
(assert (forall ((?i Int)) (= (InRange ?i System.Int64) (and (<= int_m9223372036854775808 ?i) (<= ?i int_9223372036854775807)))))
(assert (forall ((?i Int)) (= (InRange ?i System.UInt64) (and (<= 0 ?i) (<= ?i int_18446744073709551615)))))
(assert (forall ((?i Int)) (= (InRange ?i System.Char) (and (<= 0 ?i) (< ?i 65536)))))
(assert (forall ((?b Int) (?x Int) (?y Int)) (! (=> (= ?b Smt.true) (= (IfThenElse_ ?b ?x ?y) ?x)) :pattern ((IfThenElse_ ?b ?x ?y)) )))
(assert (forall ((?b Int) (?x Int) (?y Int)) (! (=> (not (= ?b Smt.true)) (= (IfThenElse_ ?b ?x ?y) ?y)) :pattern ((IfThenElse_ ?b ?x ?y)) )))
(assert (forall ((?x Int) (?y Int)) (! (= (modulo ?x ?y) (- ?x (multiply (divide ?x ?y) ?y))) :pattern ((modulo ?x ?y))  :pattern ((divide ?x ?y)) )))
(assert (forall ((?x Int) (?y Int)) (! (let ((?v_0 (modulo ?x ?y))) (=> (and (<= 0 ?x) (< 0 ?y)) (and (<= 0 ?v_0) (< ?v_0 ?y)))) :pattern ((modulo ?x ?y)) )))
(assert (forall ((?x Int) (?y Int)) (! (let ((?v_0 (modulo ?x ?y))) (=> (and (<= 0 ?x) (< ?y 0)) (and (<= 0 ?v_0) (< ?v_0 (- 0 ?y))))) :pattern ((modulo ?x ?y)) )))
(assert (forall ((?x Int) (?y Int)) (! (let ((?v_0 (modulo ?x ?y))) (=> (and (<= ?x 0) (< 0 ?y)) (and (< (- 0 ?y) ?v_0) (<= ?v_0 0)))) :pattern ((modulo ?x ?y)) )))
(assert (forall ((?x Int) (?y Int)) (! (let ((?v_0 (modulo ?x ?y))) (=> (and (<= ?x 0) (< ?y 0)) (and (< ?y ?v_0) (<= ?v_0 0)))) :pattern ((modulo ?x ?y)) )))
(assert (forall ((?x Int) (?y Int)) (=> (and (<= 0 ?x) (<= 0 ?y)) (= (modulo (+ ?x ?y) ?y) (modulo ?x ?y)))))
(assert (forall ((?x Int) (?y Int)) (=> (and (<= 0 ?x) (<= 0 ?y)) (= (modulo (+ ?y ?x) ?y) (modulo ?x ?y)))))
(assert (forall ((?x Int) (?y Int)) (let ((?v_0 (- ?x ?y))) (=> (and (<= 0 ?v_0) (<= 0 ?y)) (= (modulo ?v_0 ?y) (modulo ?x ?y))))))
(assert (forall ((?a Int) (?b Int) (?d Int)) (! (=> (and (<= 2 ?d) (= (modulo ?a ?d) (modulo ?b ?d)) (< ?a ?b)) (<= (+ ?a ?d) ?b)) :pattern ((modulo ?a ?d) (modulo ?b ?d)) )))
(assert (forall ((?x Int) (?y Int)) (! (=> (or (<= 0 ?x) (<= 0 ?y)) (<= 0 (and_ ?x ?y))) :pattern ((and_ ?x ?y)) )))
(assert (forall ((?x Int) (?y Int)) (! (let ((?v_0 (or_ ?x ?y))) (=> (and (<= 0 ?x) (<= 0 ?y)) (and (<= 0 ?v_0) (<= ?v_0 (+ ?x ?y))))) :pattern ((or_ ?x ?y)) )))
(assert (forall ((?i Int)) (! (= (shl_ ?i 0) ?i) :pattern ((shl_ ?i 0)) )))
(assert (forall ((?i Int) (?j Int)) (=> (<= 0 ?j) (= (shl_ ?i (+ ?j 1)) (* (shl_ ?i ?j) 2)))))
(assert (forall ((?i Int)) (! (= (shr_ ?i 0) ?i) :pattern ((shr_ ?i 0)) )))
(assert (forall ((?i Int) (?j Int)) (=> (<= 0 ?j) (= (shr_ ?i (+ ?j 1)) (divide (shr_ ?i ?j) 2)))))
(assert (forall ((?a Int) (?b Int)) (! (= (= (System.String.Equals_System.String_ ?a ?b) Smt.true) (= (System.String.Equals_System.String_System.String_ ?a ?b) Smt.true)) :pattern ((System.String.Equals_System.String_ ?a ?b)) )))
(assert (forall ((?a Int) (?b Int)) (! (= (= (System.String.Equals_System.String_System.String_ ?a ?b) Smt.true) (= (System.String.Equals_System.String_System.String_ ?b ?a) Smt.true)) :pattern ((System.String.Equals_System.String_System.String_ ?a ?b)) )))
(assert (forall ((?a Int) (?b Int)) (! (=> (and (not (= ?a nullObject)) (not (= ?b nullObject)) (= (System.String.Equals_System.String_System.String_ ?a ?b) Smt.true)) (= (System.String.IsInterned_System.String_notnull_ ?a) (System.String.IsInterned_System.String_notnull_ ?b))) :pattern ((System.String.Equals_System.String_System.String_ ?a ?b)) )))
(assert (subtypes Test1 Test1))
(assert (= (BaseClass_ Test1) System.Object))
(assert (subtypes Test1 (BaseClass_ Test1)))
(assert (= (AsDirectSubClass Test1 (BaseClass_ Test1)) Test1))
(assert (not (= (IsImmutable_ Test1) Smt.true)))
(assert (= (AsMutable_ Test1) Test1))
(assert (forall ((?U_ Int)) (! (=> (subtypes ?U_ Test1) (= ?U_ Test1)) :pattern ((subtypes ?U_ Test1)) )))
(assert (forall ((?U_ Int)) (! (=> (subtypes ?U_ System.Boolean) (= ?U_ System.Boolean)) :pattern ((subtypes ?U_ System.Boolean)) )))
(assert (subtypes Test2 Test2))
(assert (= (BaseClass_ Test2) System.Object))
(assert (subtypes Test2 (BaseClass_ Test2)))
(assert (= (AsDirectSubClass Test2 (BaseClass_ Test2)) Test2))
(assert (not (= (IsImmutable_ Test2) Smt.true)))
(assert (= (AsMutable_ Test2) Test2))
(assert (forall ((?U_ Int)) (! (=> (subtypes ?U_ Test2) (= ?U_ Test2)) :pattern ((subtypes ?U_ Test2)) )))
(assert (forall ((?A Int) (?i Int) (?v Int)) (= (select1 (store1 ?A ?i ?v) ?i) ?v)))
(assert (forall ((?A Int) (?i Int) (?j Int) (?v Int)) (=> (not (= ?i ?j)) (= (select1 (store1 ?A ?i ?v) ?j) (select1 ?A ?j)))))
(assert (forall ((?A Int) (?o Int) (?f Int) (?v Int)) (= (select2 (store2 ?A ?o ?f ?v) ?o ?f) ?v)))
(assert (forall ((?A Int) (?o Int) (?f Int) (?p Int) (?g Int) (?v Int)) (=> (not (= ?o ?p)) (= (select2 (store2 ?A ?o ?f ?v) ?p ?g) (select2 ?A ?p ?g)))))
(assert (forall ((?A Int) (?o Int) (?f Int) (?p Int) (?g Int) (?v Int)) (=> (not (= ?f ?g)) (= (select2 (store2 ?A ?o ?f ?v) ?p ?g) (select2 ?A ?p ?g)))))
(assert (forall ((?x Int) (?y Int)) (= (= (boolIff ?x ?y) Smt.true) (= (= ?x Smt.true) (= ?y Smt.true)))))
(assert (forall ((?x Int) (?y Int)) (= (= (boolImplies ?x ?y) Smt.true) (=> (= ?x Smt.true) (= ?y Smt.true)))))
(assert (forall ((?x Int) (?y Int)) (= (= (boolAnd ?x ?y) Smt.true) (and (= ?x Smt.true) (= ?y Smt.true)))))
(assert (forall ((?x Int) (?y Int)) (= (= (boolOr ?x ?y) Smt.true) (or (= ?x Smt.true) (= ?y Smt.true)))))
(assert (forall ((?x Int)) (! (= (= (boolNot ?x) Smt.true) (not (= ?x Smt.true))) :pattern ((boolNot ?x)) )))
(assert (forall ((?x Int) (?y Int)) (= (= (anyEqual ?x ?y) Smt.true) (= ?x ?y))))
(assert (forall ((?x Int) (?y Int)) (! (= (= (anyNeq ?x ?y) Smt.true) (not (= ?x ?y))) :pattern ((anyNeq ?x ?y)) )))
(assert (forall ((?x Int) (?y Int)) (= (= (intLess ?x ?y) Smt.true) (< ?x ?y))))
(assert (forall ((?x Int) (?y Int)) (= (= (intAtMost ?x ?y) Smt.true) (<= ?x ?y))))
(assert (forall ((?x Int) (?y Int)) (= (= (intAtLeast ?x ?y) Smt.true) (>= ?x ?y))))
(assert (forall ((?x Int) (?y Int)) (= (= (intGreater ?x ?y) Smt.true) (> ?x ?y))))
(assert (distinct Smt.false Smt.true))
(assert (forall ((?t Int)) (! (subtypes ?t ?t) :pattern ((subtypes ?t ?t)) )))
(assert (forall ((?t Int) (?u Int) (?v Int)) (! (=> (and (subtypes ?t ?u) (subtypes ?u ?v)) (subtypes ?t ?v)) :pattern ((subtypes ?t ?u) (subtypes ?u ?v)) )))
(assert (forall ((?t Int) (?u Int)) (! (=> (and (subtypes ?t ?u) (subtypes ?u ?t)) (= ?t ?u)) :pattern ((subtypes ?t ?u) (subtypes ?u ?t)) )))
(assert (let ((?v_0 (<= 0 4)) (?v_1 (ValueArray System.Int32 1)) (?v_9 (Length_ xs_0)) (?v_3 (select2 Heap_ xs_0 ownerRef_)) (?v_4 (select2 Heap_ xs_0 ownerFrame_))) (let ((?v_2 (= ?v_4 PeerGroupPlaceholder_)) (?v_5 (<= 4 4))) (let ((?v_6 (and ?v_5 ?v_5)) (?v_7 (not (= xs_0 nullObject))) (?v_8 (<= 0 1)) (?v_10 (< 1 ?v_9)) (?v_11 (<= 1 1))) (let ((?v_12 (and ?v_5 ?v_5 ?v_11 ?v_11)) (?v_13 (forall ((?o_ Int)) (=> (and (not (= ?o_ nullObject)) (= (= (select2 Heap_ ?o_ allocated_) Smt.true) true)) (and (= (select2 Heap_ ?o_ ownerRef_) (select2 Heap_0_ ?o_ ownerRef_)) (= (select2 Heap_ ?o_ ownerFrame_) (select2 Heap_0_ ?o_ ownerFrame_)))))) (?v_14 (= ReallyLastGeneratedExit_correct Smt.true)) (?v_15 (= block3349_correct Smt.true)) (?v_16 (= block3332_correct Smt.true)) (?v_17 (= block3315_correct Smt.true)) (?v_18 (= block3298_correct Smt.true)) (?v_19 (= block3281_correct Smt.true)) (?v_20 (= entry_correct Smt.true))) (not (=> (=> (=> true (=> (= (IsHeap Heap_) Smt.true) (=> (= BeingConstructed_ nullObject) (=> true (=> true (=> (=> (=> true (=> true (=> true (=> (=> (=> true (=> true (and ?v_0 (=> ?v_0 (=> (= (Is_ xs_0 ?v_1) Smt.true) (=> (and (= (= (select2 Heap_ xs_0 allocated_) Smt.true) false) (= ?v_9 4)) (=> (= (IsNotNull_ xs_0 ?v_1) Smt.true) (=> (and (= ?v_3 xs_0) ?v_2) (=> (and (= (select2 Heap_ xs_0 inv_) ?v_1) (= (select2 Heap_ xs_0 localinv_) ?v_1) (or ?v_2 (not (subtypes (select2 Heap_ ?v_3 inv_) ?v_4)) (= (select2 Heap_ ?v_3 localinv_) (BaseClass_ ?v_4)))) (=> (forall ((?i_ Int)) (= (ValueArrayGet (select2 Heap_ xs_0 elements_) ?i_) 0)) (=> (= Heap_0_ (store2 Heap_ xs_0 allocated_ Smt.true)) (=> (= (IsHeap Heap_0_) Smt.true) (=> ?v_6 (=> (=> (=> true (=> ?v_6 (and ?v_7 (=> ?v_7 (and ?v_8 (=> ?v_8 (and ?v_10 (=> ?v_10 (=> (= i_0 (ValueArrayGet (select2 Heap_0_ xs_0 elements_) 1)) (=> ?v_12 (=> (=> (=> true (=> ?v_12 (=> ?v_12 (=> (=> (=> true (=> ?v_12 (=> ?v_12 (=> (=> (=> true (and ?v_13 (=> ?v_13 (=> true true)))) ?v_14) ?v_14)))) ?v_15) ?v_15)))) ?v_16) ?v_16))))))))))) ?v_17) ?v_17)))))))))))))) ?v_18) ?v_18)))) ?v_19) ?v_19)))))) ?v_20) ?v_20)))))))
(check-sat)
(exit)
