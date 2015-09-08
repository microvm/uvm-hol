open HolKernel Parse boolLib bossLib;

val _ = new_theory "uvmTypes";

local open stringTheory finite_mapTheory in end
val _ = ParseExtras.tight_equality()

val _ = type_abbrev ("structID", ``:string``)

val _ = Datatype`
  uvmType =
     Int num
   | Float
   | Double
   | Ref uvmType
   | Iref uvmType
   | Weakref uvmType
   | CPtr uvmType
   | Struct structID
   | Array uvmType num
   | Hybrid uvmType uvmType
   | Void
   | ThreadRef
   | StackRef
   | Tagref64
   | Vector uvmType num
   | FuncRef uvmType (uvmType list)
   | CFuncPtr uvmType (uvmType list)
`

val fpType_def = Define`
  fpType Float = T ∧
  fpType Double = T ∧
  fpType _ = F
`;

val intType_def = Define`
  intType (Int _) = T ∧
  intType _ = F
`;

val ptrType_def = Define`
  ptrType (CPtr _) = T ∧
  ptrType (CFuncPtr _ _) = T ∧
  ptrType _ = F
`;

val irefType_def = Define`
  irefType (Iref _) = T ∧
  irefType _ = F
`;

val eqcomparable_def = Define`
  eqcomparable (Int _) = T ∧
  eqcomparable (Ref _) = T ∧
  eqcomparable (Iref _) = T ∧
  eqcomparable (CPtr _) = T ∧
  eqcomparable (FuncRef _ _) = T ∧
  eqcomparable (CFuncPtr _ _) = T ∧
  eqcomparable ThreadRef = T ∧
  eqcomparable StackRef = T ∧
  eqcomparable _ = F
`;


val scalarType_def = Define`
  scalarType ty =
    case ty of
    | Int _ => T
    | Float => T
    | Double => T
    | Ref _ => T
    | Iref _ => T
    | Weakref _ => T
    | FuncRef _ _ => T
    | CFuncPtr _ _ => T
    | ThreadRef => T
    | StackRef => T
    | Tagref64 => T
    | CPtr _ => T
    | _ => F
`;

(*
   maybeVector : (uvmType -> bool) -> uvmType -> bool

   [maybeVector P ty] checks to see if P is true of ty.  Alternatively,
   if ty is a vector type, it checks to see if P is true of the element
   type of the vector
*)
val maybeVector_def = Define`
  maybeVector P ty ⇔
    P ty ∨ case ty of Vector ty0 _ => P ty0 | _ => F
`;

val (traced_rules, traced_ind, traced_cases) = Hol_reln`
  (∀ty. tracedtype smap (Ref ty)) ∧
  (∀ty. tracedtype smap (Iref ty)) ∧
  (∀sz ty.
     tracedtype smap ty ⇒
     tracedtype smap (Array ty sz)) ∧
  (∀sz ty.
     tracedtype smap ty ⇒
     tracedtype smap (Vector ty sz)) ∧
  (∀fixty varty.
     tracedtype smap fixty ⇒ tracedtype smap (Hybrid fixty varty)) ∧
  (∀fixty varty.
     tracedtype smap varty ⇒ tracedtype smap (Hybrid fixty varty)) ∧
  (∀tag ty.
     tag ∈ FDOM smap ∧ tracedtype smap ty ∧ MEM ty (smap ' tag)
   ⇒
     tracedtype smap (Struct tag))
`;


val (wftype_rules, wftype_ind, wftype_cases) = Hol_reln`
  (∀smap n.
      0 < n
     ⇒
      wftype smap (Int n)) ∧

  (∀smap. wftype smap Float) ∧
  (∀smap. wftype smap Double) ∧
  (∀smap. wftype smap Void) ∧
  (∀smap. wftype smap ThreadRef) ∧
  (∀smap. wftype smap StackRef) ∧
  (∀smap. wftype smap Tagref64) ∧
  (∀smap. wftype smap Void) ∧

  (∀smap ty.
     wftype smap ty ∨ (∃tag. ty = Struct tag ∧ tag ∈ SND smap)
    ⇒
     wftype smap (Ref ty)) ∧

  (∀smap ty.
     wftype smap ty ∨ (∃tag. ty = Struct tag ∧ tag ∈ SND smap)
    ⇒
     wftype smap (Iref ty)) ∧

  (∀smap ty.
     wftype smap ty ∨ (∃tag. ty = Struct tag ∧ tag ∈ SND smap)
    ⇒
     wftype smap (Weakref ty)) ∧

  (∀smap ty.
     ¬tracedtype (FST smap) ty ∧
     wftype smap ty ∨ (∃tag. ty = Struct tag ∧ tag ∈ SND smap)
    ⇒
     wftype smap (CPtr ty)) ∧

  (∀smap retty argtys.
     wftype smap retty ∧
     (∀ty. ty ∈ set argtys ⇒ wftype smap ty)
    ⇒
     wftype smap (FuncRef retty argtys)) ∧

  (∀smap retty argtys.
     wftype smap retty ∧
     (∀ty. ty ∈ set argtys ⇒ wftype smap ty)
    ⇒
     wftype smap (CFuncPtr retty argtys)) ∧

  (∀smap sz ty.
     (* 0 < sz ??? ∧ *) wftype smap ty
    ⇒
     wftype smap (Array ty sz)) ∧

  (∀smap sz ty.
     0 < sz ∧ wftype smap ty ∧ scalarType ty
    ⇒
     wftype smap (Vector ty sz)) ∧

  (∀smap fixty varty.
      wftype smap fixty ∧ wftype smap varty
    ⇒
      wftype smap (Hybrid fixty varty)) ∧

  (∀sm sset tag.
     tag ∈ FDOM sm ∧
     (∀ty. MEM ty (sm ' tag) ⇒ wftype (sm, tag INSERT sset) ty)
    ⇒
     wftype (sm, sset) (Struct tag))
`

val _ = export_theory();
