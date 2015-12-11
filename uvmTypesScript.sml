open HolKernel Parse boolLib bossLib;

val _ = new_theory "uvmTypes";

local open stringTheory finite_mapTheory in end
open lcsymtacs
val _ = ParseExtras.tight_equality()

val _ = type_abbrev ("structID", ``:string``)

val _ = Datatype`
  machine = <| ptrsize : num ; floatsize : num ; doublesize : num  |>
`;

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
(* | Hybrid (uvmType list) uvmType *) (* TODO: match this change in code below *)
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

(* A native-safe type can be handed off to the "native" world. *)
val (native_safe_rules, native_safe_ind, native_safe_cases) = Hol_reln`
  (∀n. native_safe smap (Int n)) ∧
  (native_safe smap Float) ∧
  (native_safe smap Double) ∧
  (native_safe smap Void) ∧
  (∀ty n. native_safe smap ty ⇒ native_safe smap (Vector ty n)) ∧
  (∀ty n. native_safe smap ty ⇒ native_safe smap (Array ty n)) ∧
  (∀ty. native_safe smap (UPtr ty)) ∧
  (∀ty argtys. native_safe smap (UFuncPtr ty argtys)) ∧
  (∀fty vty. native_safe smap fty ∧ native_safe smap vty ⇒
             native_safe smap (Hybrid fty vty)) ∧
  (∀tag.
     (∀ty. ty ∈ set (smap ' tag) ⇒ native_safe smap ty) ∧
     tag ∈ FDOM smap
    ⇒
     native_safe smap (Struct tag))
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
     (∀ty. ty ∈ set argtys ⇒ wftype smap vset ty ∧ ty ≠ Void)
    ⇒
     wftype smap vset (FuncRef retty argtys)) ∧

  (∀vset retty argtys.
     wftype smap vset retty ∧
     (∀ty. ty ∈ set argtys ⇒ wftype smap vset ty)
    ⇒
     wftype smap vset (UFuncPtr retty argtys)) ∧

  (∀vset sz ty.
     0 < sz ∧ wftype smap vset ty ∧ ty ≠ Void
    ⇒
     wftype smap vset (Array ty sz)) ∧

  (∀vset sz ty.
     0 < sz ∧ wftype smap vset ty ∧ scalarType ty
    ⇒
     wftype smap vset (Vector ty sz)) ∧

  (∀vset fixty varty.
      wftype smap vset fixty ∧ wftype smap vset varty ∧ varty ≠ Void
    ⇒
      wftype smap vset (Hybrid fixty varty)) ∧

  (∀vset tag.
     tag ∈ FDOM smap ∧ smap ' tag ≠ [] ∧
     (∀ty. MEM ty (smap ' tag) ⇒ wftype smap (tag INSERT vset) ty ∧ ty ≠ Void)
    ⇒
     wftype smap vset (Struct tag))
`

(* Note that FuncRefs are not native_safe, but are not traced either, so the
   reverse implication doesn't hold *)
val native_safe_nottraced = store_thm(
  "native_safe_traced",
  ``∀vset ty.
      wftype sm vset ty ⇒ native_safe sm ty ⇒ ¬tracedtype sm ty``,
  Induct_on `wftype` >> rpt conj_tac >> strip_tac >>
  TRY (simp[Once native_safe_cases, Once tracedtype_cases] >> NO_TAC) >>
  TRY (ntac 2 strip_tac >>
       simp[Once native_safe_cases, Once tracedtype_cases] >> NO_TAC) >>
  TRY (ntac 3 strip_tac >>
       simp[Once native_safe_cases, Once tracedtype_cases] >> NO_TAC) >>
  (* struct *)
  ntac 2 strip_tac >>
  dsimp[Once native_safe_cases, Once tracedtype_cases] >> rpt strip_tac >>
  qcase_tac `MEM ty (sm ' tag)` >> Cases_on `MEM ty (sm ' tag)` >> simp[])

(* ----------------------------------------------------------------------

    canconvert pair

   ---------------------------------------------------------------------- *)

val _ = Datatype`
  convtype =
  	TRUNC | ZEXT	| SEXT
      | FPTRUNC | FPEXT | FPTOUI | FPTOSI | UITOFP | SITOFP
      | BITCAST | REFCAST | PTRCAST
`

(* canconvert M convtype (src : uvmType) (tgt : uvmType) *)

val (canconvert_rules, canconvert_ind, canconvert_cases) = Hol_reln`
  (∀m n.
     m ≤ n
    ⇒
     canconvert M Smap TRUNC (Int n) (Int m))

    ∧

  (∀m n.
    m ≤ n
   ⇒
    canconvert M Smap ZEXT (Int m) (Int n))

    ∧

  (∀m n.
    m ≤ n
   ⇒
    canconvert M Smap SEXT (Int m) (Int n))

    ∧

  canconvert M Smap FPTRUNC Double Float

    ∧

  canconvert M Smap FPEXT Float Double

    ∧

  (∀ty n.
     fpType ty
    ⇒
     canconvert M Smap FPTOUI ty (Int n))

    ∧

  (∀ty n.
     fpType ty
    ⇒
     canconvert M Smap FPTOSI ty (Int n))

    ∧

  (∀ty n.
     fpType ty
    ⇒
     canconvert M Smap UITOFP (Int n) ty)

    ∧

  (∀ty n.
     fpType ty
    ⇒
     canconvert M Smap SITOFP (Int n) ty)

    ∧

     canconvert M Smap BITCAST (Int M.floatsize) Float

    ∧

     canconvert M Smap BITCAST Float (Int M.floatsize)

    ∧

     canconvert M Smap BITCAST (Int M.doublesize) Double

    ∧

     canconvert M Smap BITCAST Double (Int M.doublesize)


    ∧

  (* ptrcast cases *)
  (∀n ty.
     M.ptrsize = n
    ⇒
     canconvert M Smap BITCAST (Int n) (UPtr ty))

    ∧

  (∀n ty.
     M.ptrsize = n (* tell KW *)
    ⇒
     canconvert M Smap BITCAST (UPtr ty) (Int n))

    ∧

  (* refcast cases *)
  (∀ty.
     canconvert M Smap BITCAST (Ref Void) (Ref ty))

    ∧

  (∀ty.
     canconvert M Smap BITCAST (Ref ty) (Ref Void))

    ∧

  (∀ty.
     canconvert M Smap BITCAST (Ref Void) (Ref ty))

    ∧

  (∀tag1 tag2.
     tag1 ∈ FDOM Smap ∧ tag2 ∈ FDOM Smap ∧
     (Smap ' tag1 <<= Smap ' tag2 ∨ Smap ' tag2 <<= Smap ' tag1)
    ⇒
     canconvert M Smap BITCAST (Ref (Struct tag1)) (Ref (Struct tag2)))
`


val _ = export_theory();
