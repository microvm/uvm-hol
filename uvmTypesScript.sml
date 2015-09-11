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
   | UPtr uvmType
   | Struct structID
   | Array uvmType num
   | Hybrid uvmType uvmType
   | Void
   | ThreadRef
   | StackRef
   | Tagref64
   | Vector uvmType num
   | FuncRef uvmType (uvmType list)
   | UFuncPtr uvmType (uvmType list)
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
  ptrType (UPtr _) = T ∧
  ptrType (UFuncPtr _ _) = T ∧
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
  eqcomparable (UPtr _) = T ∧
  eqcomparable (FuncRef _ _) = T ∧
  eqcomparable (UFuncPtr _ _) = T ∧
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
    | UFuncPtr _ _ => T
    | ThreadRef => T
    | StackRef => T
    | Tagref64 => T
    | UPtr _ => T
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

val (tracedtype_rules, tracedtype_ind, tracedtype_cases) = Hol_reln`
  (∀ty. tracedtype smap (Ref ty)) ∧
  (∀ty. tracedtype smap (Iref ty)) ∧
  (∀ty. tracedtype smap (Weakref ty)) ∧
  (∀sz ty.
     tracedtype smap ty ⇒
     tracedtype smap (Array ty sz)) ∧
  (∀sz ty.
     tracedtype smap ty ⇒
     tracedtype smap (Vector ty sz)) ∧
  tracedtype smap ThreadRef ∧
  tracedtype smap StackRef ∧
  tracedtype smap Tagref64 ∧
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
  (∀vset n.
      0 < n
     ⇒
      wftype smap vset (Int n)) ∧

  (∀vset. wftype smap vset Float) ∧
  (∀vset. wftype smap vset Double) ∧
  (∀vset. wftype smap vset Void) ∧
  (∀vset. wftype smap vset ThreadRef) ∧
  (∀vset. wftype smap vset StackRef) ∧
  (∀vset. wftype smap vset Tagref64) ∧

  (∀vset ty.
     wftype smap vset ty ∨ (∃tag. ty = Struct tag ∧ tag ∈ vset)
    ⇒
     wftype smap vset (Ref ty)) ∧

  (∀vset ty.
     wftype smap vset ty ∨ (∃tag. ty = Struct tag ∧ tag ∈ vset)
    ⇒
     wftype smap vset (Iref ty)) ∧

  (∀vset ty.
     wftype smap vset ty ∨ (∃tag. ty = Struct tag ∧ tag ∈ vset)
    ⇒
     wftype smap vset (Weakref ty)) ∧

  (∀vset ty.
     ¬tracedtype smap ty ∧
     wftype smap vset ty ∨ (∃tag. ty = Struct tag ∧ tag ∈ vset)
    ⇒
     wftype smap vset (UPtr ty)) ∧

  (∀vset retty argtys.
     wftype smap vset retty ∧
     (∀ty. ty ∈ set argtys ⇒ wftype smap vset ty)
    ⇒
     wftype smap vset (FuncRef retty argtys)) ∧

  (∀vset retty argtys.
     wftype smap vset retty ∧
     (∀ty. ty ∈ set argtys ⇒ wftype smap vset ty)
    ⇒
     wftype smap vset (UFuncPtr retty argtys)) ∧

  (∀vset sz ty.
     (* 0 < sz ??? ∧ *) wftype smap vset ty
    ⇒
     wftype smap vset (Array ty sz)) ∧

  (∀vset sz ty.
     0 < sz ∧ wftype smap vset ty ∧ scalarType ty
    ⇒
     wftype smap vset (Vector ty sz)) ∧

  (∀vset fixty varty.
      wftype smap vset fixty ∧ wftype smap vset varty
    ⇒
      wftype smap vset (Hybrid fixty varty)) ∧

  (∀vset tag.
     tag ∈ FDOM smap ∧
     (∀ty. MEM ty (smap ' tag) ⇒ wftype smap (tag INSERT vset) ty)
    ⇒
     wftype smap vset (Struct tag))
`

val _ = export_theory();
