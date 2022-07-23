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
(declare-fun System.IConvertible () Int)
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
(declare-fun block5814_correct () Int)
(declare-fun nullObject () Int)
(declare-fun store2 (Int Int Int Int) Int)
(declare-fun modulo (Int Int) Int)
(declare-fun System.IComparable () Int)
(declare-fun ownerRef_ () Int)
(declare-fun StructSet_ (Int Int Int) Int)
(declare-fun AsDirectSubClass (Int Int) Int)
(declare-fun System.Collections.ICollection () Int)
(declare-fun System.IEquatable_1...System.String () Int)
(declare-fun shl_ (Int Int) Int)
(declare-fun DimLength_ (Int Int) Int)
(declare-fun anyEqual (Int Int) Int)
(declare-fun System.Array () Int)
(declare-fun System.Collections.Generic.IEnumerable_1...System.Char () Int)
(declare-fun SharingMode_LockProtected_ () Int)
(declare-fun IsMemberlessType_ (Int) Int)
(declare-fun System.UInt16 () Int)
(declare-fun block5916_correct () Int)
(declare-fun block6001_correct () Int)
(declare-fun ClassRepr (Int) Int)
(declare-fun boolNot (Int) Int)
(declare-fun block6086_correct () Int)
(declare-fun boolAnd (Int Int) Int)
(declare-fun boolImplies (Int Int) Int)
(declare-fun Unbox (Int) Int)
(declare-fun intAtLeast (Int Int) Int)
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
(declare-fun entry_correct () Int)
(declare-fun FirstConsistentOwner_ () Int)
(declare-fun UnboxedType (Int) Int)
(declare-fun AsRefField (Int Int) Int)
(declare-fun System.Byte () Int)
(declare-fun this () Int)
(declare-fun int_2147483647 () Int)
(declare-fun ArrayCategoryRef_ () Int)
(declare-fun Heap_ () Int)
(declare-fun Length_ (Int) Int)
(declare-fun AsNonNullRefField (Int Int) Int)
(declare-fun IsHeap (Int) Int)
(declare-fun UBound_ (Int Int) Int)
(declare-fun System.String () Int)
(declare-fun System.Collections.IList () Int)
(declare-fun System.String.IsInterned_System.String_notnull_ (Int) Int)
(declare-fun UnknownRef_ () Int)
(declare-fun Rank_ (Int) Int)
(declare-fun block6171_correct () Int)
(declare-fun RefArraySet (Int Int Int) Int)
(declare-fun ValueArraySet (Int Int Int) Int)
(declare-fun boolOr (Int Int) Int)
(declare-fun sharingMode_ () Int)
(declare-fun subtypes (Int Int) Bool)
(declare-fun System.IComparable_1...System.String () Int)
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
(declare-fun test3.MyClass () Int)
(declare-fun ArrayCategory_ (Int) Int)
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
(declare-fun System.ICloneable () Int)
(declare-fun IsDirectlyModifiableField (Int) Int)
(declare-fun StringLength_ (Int) Int)
(declare-fun allocated_ () Int)
(declare-fun BaseClass_ (Int) Int)
(declare-fun ValueArray (Int Int) Int)
(declare-fun Smt.false () Int)
(declare-fun IsImmutable_ (Int) Int)
(declare-fun elements_ () Int)
(declare-fun DeclType (Int) Int)
(declare-fun a_in () Int)
(declare-fun System.Collections.IEnumerable () Int)
(declare-fun ReallyLastGeneratedExit_correct () Int)
(assert (distinct allocated_ elements_ inv_ localinv_ exposeVersion_ sharingMode_ SharingMode_Unshared_ SharingMode_LockProtected_ ownerRef_ ownerFrame_ PeerGroupPlaceholder_ ArrayCategoryValue_ ArrayCategoryRef_ ArrayCategoryNonNullRef_ System.Array System.Object System.Type BeingConstructed_ NonNullFieldsAreInitialized_ System.String FirstConsistentOwner_ System.SByte System.Byte System.Int16 System.UInt16 System.Int32 System.UInt32 System.Int64 System.UInt64 System.Char int_m2147483648 int_2147483647 int_4294967295 int_m9223372036854775808 int_9223372036854775807 int_18446744073709551615 UnknownRef_ System.ICloneable System.Collections.Generic.IEnumerable_1...System.Char System.IComparable System.IConvertible System.Collections.ICollection System.Collections.IEnumerable System.IEquatable_1...System.String test3.MyClass System.Collections.IList System.IComparable_1...System.String))
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
(assert (subtypes test3.MyClass test3.MyClass))
(assert (= (BaseClass_ test3.MyClass) System.Object))
(assert (subtypes test3.MyClass (BaseClass_ test3.MyClass)))
(assert (= (AsDirectSubClass test3.MyClass (BaseClass_ test3.MyClass)) test3.MyClass))
(assert (not (= (IsImmutable_ test3.MyClass) Smt.true)))
(assert (= (AsMutable_ test3.MyClass) test3.MyClass))
(assert (subtypes System.String System.String))
(assert (= (BaseClass_ System.String) System.Object))
(assert (subtypes System.String (BaseClass_ System.String)))
(assert (= (AsDirectSubClass System.String (BaseClass_ System.String)) System.String))
(assert (= (IsImmutable_ System.String) Smt.true))
(assert (= (AsImmutable_ System.String) System.String))
(assert (subtypes System.IComparable System.Object))
(assert (= (IsMemberlessType_ System.IComparable) Smt.true))
(assert (subtypes System.String System.IComparable))
(assert (subtypes System.ICloneable System.Object))
(assert (= (IsMemberlessType_ System.ICloneable) Smt.true))
(assert (subtypes System.String System.ICloneable))
(assert (subtypes System.IConvertible System.Object))
(assert (= (IsMemberlessType_ System.IConvertible) Smt.true))
(assert (subtypes System.String System.IConvertible))
(assert (subtypes System.IComparable_1...System.String System.Object))
(assert (= (IsMemberlessType_ System.IComparable_1...System.String) Smt.true))
(assert (subtypes System.String System.IComparable_1...System.String))
(assert (subtypes System.Collections.Generic.IEnumerable_1...System.Char System.Object))
(assert (subtypes System.Collections.IEnumerable System.Object))
(assert (= (IsMemberlessType_ System.Collections.IEnumerable) Smt.true))
(assert (subtypes System.Collections.Generic.IEnumerable_1...System.Char System.Collections.IEnumerable))
(assert (= (IsMemberlessType_ System.Collections.Generic.IEnumerable_1...System.Char) Smt.true))
(assert (subtypes System.String System.Collections.Generic.IEnumerable_1...System.Char))
(assert (subtypes System.String System.Collections.IEnumerable))
(assert (subtypes System.IEquatable_1...System.String System.Object))
(assert (= (IsMemberlessType_ System.IEquatable_1...System.String) Smt.true))
(assert (subtypes System.String System.IEquatable_1...System.String))
(assert (forall ((?U_ Int)) (! (=> (subtypes ?U_ System.String) (= ?U_ System.String)) :pattern ((subtypes ?U_ System.String)) )))
(assert (subtypes System.Array System.Array))
(assert (= (BaseClass_ System.Array) System.Object))
(assert (subtypes System.Array (BaseClass_ System.Array)))
(assert (= (AsDirectSubClass System.Array (BaseClass_ System.Array)) System.Array))
(assert (not (= (IsImmutable_ System.Array) Smt.true)))
(assert (= (AsMutable_ System.Array) System.Array))
(assert (subtypes System.Array System.ICloneable))
(assert (subtypes System.Collections.IList System.Object))
(assert (subtypes System.Collections.ICollection System.Object))
(assert (subtypes System.Collections.ICollection System.Collections.IEnumerable))
(assert (= (IsMemberlessType_ System.Collections.ICollection) Smt.true))
(assert (subtypes System.Collections.IList System.Collections.ICollection))
(assert (subtypes System.Collections.IList System.Collections.IEnumerable))
(assert (= (IsMemberlessType_ System.Collections.IList) Smt.true))
(assert (subtypes System.Array System.Collections.IList))
(assert (subtypes System.Array System.Collections.ICollection))
(assert (subtypes System.Array System.Collections.IEnumerable))
(assert (= (IsMemberlessType_ System.Array) Smt.true))
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
(assert (let ((?v_0 (select2 Heap_ a_in ownerFrame_)) (?v_1 (select2 Heap_ a_in ownerRef_)) (?v_2 (select2 Heap_ this ownerFrame_)) (?v_3 (select2 Heap_ this ownerRef_)) (?v_4 (>= (Length_ a_in) 0)) (?v_5 (= (Rank_ a_in) 2)) (?v_6 (= (IsNotNull_ a_in System.Array) Smt.true)) (?v_7 (forall ((?o_ Int)) (let ((?v_15 (select2 Heap_ ?o_ ownerRef_)) (?v_16 (select2 Heap_ ?o_ ownerFrame_))) (=> (and (not (= ?o_ nullObject)) (= (= (select2 Heap_ ?o_ allocated_) Smt.true) true)) (and (= ?v_15 ?v_15) (= ?v_16 ?v_16)))))) (?v_8 (= ReallyLastGeneratedExit_correct Smt.true)) (?v_9 (= block6171_correct Smt.true)) (?v_10 (= block6086_correct Smt.true)) (?v_11 (= block6001_correct Smt.true)) (?v_12 (= block5916_correct Smt.true)) (?v_13 (= block5814_correct Smt.true)) (?v_14 (= entry_correct Smt.true))) (not (=> (=> (=> true (=> (= (IsHeap Heap_) Smt.true) (=> (= (IsNotNull_ a_in (RefArray test3.MyClass 2)) Smt.true) (=> (= BeingConstructed_ nullObject) (=> (and (or (= ?v_0 PeerGroupPlaceholder_) (not (subtypes (select2 Heap_ ?v_1 inv_) ?v_0)) (= (select2 Heap_ ?v_1 localinv_) (BaseClass_ ?v_0))) (forall ((?pc_ Int)) (let ((?v_17 (typeof_ ?pc_))) (=> (and (not (= ?pc_ nullObject)) (= (= (select2 Heap_ ?pc_ allocated_) Smt.true) true) (= (select2 Heap_ ?pc_ ownerRef_) ?v_1) (= (select2 Heap_ ?pc_ ownerFrame_) ?v_0)) (and (= (select2 Heap_ ?pc_ inv_) ?v_17) (= (select2 Heap_ ?pc_ localinv_) ?v_17)))))) (=> (and (or (= ?v_2 PeerGroupPlaceholder_) (not (subtypes (select2 Heap_ ?v_3 inv_) ?v_2)) (= (select2 Heap_ ?v_3 localinv_) (BaseClass_ ?v_2))) (forall ((?pc_ Int)) (let ((?v_18 (typeof_ ?pc_))) (=> (and (not (= ?pc_ nullObject)) (= (= (select2 Heap_ ?pc_ allocated_) Smt.true) true) (= (select2 Heap_ ?pc_ ownerRef_) ?v_3) (= (select2 Heap_ ?pc_ ownerFrame_) ?v_2)) (and (= (select2 Heap_ ?pc_ inv_) ?v_18) (= (select2 Heap_ ?pc_ localinv_) ?v_18)))))) (=> (= (= (select2 Heap_ a_in allocated_) Smt.true) true) (=> true (=> (= (IsNotNull_ this test3.MyClass) Smt.true) (=> (= (= (select2 Heap_ this allocated_) Smt.true) true) (=> true (=> (=> (=> true (=> true (=> true (=> (=> (=> true (=> true (and ?v_4 (=> ?v_4 (=> true (=> (=> (=> true (=> true (and ?v_5 (=> ?v_5 (=> true (=> (=> (=> true (=> true (and ?v_6 (=> ?v_6 (=> true (=> (=> (=> true (=> true (=> true (=> (=> (=> true (and ?v_7 (=> ?v_7 (=> true true)))) ?v_8) ?v_8)))) ?v_9) ?v_9)))))) ?v_10) ?v_10)))))) ?v_11) ?v_11)))))) ?v_12) ?v_12)))) ?v_13) ?v_13)))))))))))) ?v_14) ?v_14))))
(check-sat)
(exit)