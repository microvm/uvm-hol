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
   | Ptr uvmType
   | Struct structID
   | Array uvmType num
   | Hybrid uvmType uvmType
   | Void
   | Thread
   | Stack
   | Tagref64
   | Vector uvmType num
   | Func uvmType (uvmType list) (* need both? *)
   | FuncPtr uvmType (uvmType list)
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
  ptrType (Ptr _) = T ∧
  ptrType _ = F (* KW wants FuncPtr here *)
`;

val irefType_def = Define`
  irefType (Iref _) = T ∧
  irefType _ = F
`;

val eqcomparable_def = Define`
  eqcomparable (Int _) = T ∧
  eqcomparable (Ref _) = T ∧
  eqcomparable (Iref _) = T ∧
  eqcomparable (Weakref _) = T ∧
  eqcomparable (Ptr _) = T ∧
  eqcomparable (Func _ _) = T ∧
  eqcomparable (FuncPtr _ _) = T ∧
  eqcomparable Thread = T ∧
  eqcomparable Stack = T ∧
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
    | Func _ _ => T
    | FuncPtr _ _ => T
    | Thread => T
    | Stack => T
    | Tagref64 => T
    | Ptr _ => T
    | _ => F
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
  (∀smap. wftype smap Thread) ∧
  (∀smap. wftype smap Stack) ∧
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
     wftype smap (Ptr ty)) ∧

  (∀smap retty argtys.
     wftype smap retty ∧
     (∀ty. ty ∈ set argtys ⇒ wftype smap ty)
    ⇒
     wftype smap (Func retty argtys)) ∧

  (∀smap retty argtys.
     wftype smap retty ∧
     (∀ty. ty ∈ set argtys ⇒ wftype smap ty)
    ⇒
     wftype smap (FuncPtr retty argtys)) ∧

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
