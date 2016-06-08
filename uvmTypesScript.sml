open HolKernel Parse boolLib bossLib;

val _ = new_theory "uvmTypes";

local open stringTheory finite_mapTheory in end
open lcsymtacs
val _ = ParseExtras.tight_equality()

val _ = type_abbrev ("struct_id", ``:string``)

val _ = Datatype`
  machine = <|
    ptrsize : num;
    floatsize : num;
    doublesize : num
  |>
`

val _ = Datatype`
  uvm_type =
  | Int num
  | Float
  | Double
  | Ref uvm_type
  | IRef uvm_type
  | WeakRef uvm_type
  | UPtr uvm_type
  | Struct struct_id
  | Array uvm_type num
  | Hybrid (uvm_type list) uvm_type
  | Void
  | ThreadRef
  | StackRef
  | TagRef64
  | Vector uvm_type num
  | FuncRef funcsig
  | UFuncPtr funcsig ;

  funcsig = <|
    arg_types : uvm_type list ;
    return_types : uvm_type list
  |>
`

val fp_type_def = Define`
  fp_type Float = T ∧
  fp_type Double = T ∧
  fp_type _ = F
`

val int_type_def = Define`
  int_type (Int _) = T ∧
  int_type _ = F
`

val ptr_type_def = Define`
  ptr_type (UPtr _) = T ∧
  ptr_type (UFuncPtr _) = T ∧
  ptr_type _ = F
`

val iref_type_def = Define`
  iref_type (IRef _) = T ∧
  iref_type _ = F
`

val eqcomparable_def = Define`
  eqcomparable (Int _) = T ∧
  eqcomparable (Ref _) = T ∧
  eqcomparable (IRef _) = T ∧
  eqcomparable (UPtr _) = T ∧
  eqcomparable (FuncRef _) = T ∧
  eqcomparable (UFuncPtr _) = T ∧
  eqcomparable ThreadRef = T ∧
  eqcomparable StackRef = T ∧
  eqcomparable _ = F
`


val scalar_type_def = Define`
  scalar_type ty =
    case ty of
    | Int _ => T
    | Float => T
    | Double => T
    | Ref _ => T
    | IRef _ => T
    | WeakRef _ => T
    | FuncRef _ => T
    | UFuncPtr _ => T
    | ThreadRef => T
    | StackRef => T
    | TagRef64 => T
    | UPtr _ => T
    | _ => F
`

(*
   maybe_vector : (uvm_type -> bool) -> uvm_type -> bool

   [maybe_vector P ty] checks to see if P is true of ty.  Alternatively,
   if ty is a vector type, it checks to see if P is true of the element
   type of the vector
*)
val maybe_vector_def = Define`
  maybe_vector P ty ⇔
    P ty ∨ case ty of Vector ty0 _ => P ty0 | _ => F
`

val (tracedtype_rules, tracedtype_ind, tracedtype_cases) = Hol_reln`
    (∀ty. tracedtype smap (Ref ty))
  ∧ (∀ty. tracedtype smap (IRef ty))
  ∧ (∀ty. tracedtype smap (WeakRef ty))
  ∧ (∀sz ty.
      tracedtype smap ty ⇒
      tracedtype smap (Array ty sz))
  ∧ (∀sz ty.
      tracedtype smap ty ⇒
      tracedtype smap (Vector ty sz))
  ∧ tracedtype smap ThreadRef
  ∧ tracedtype smap StackRef
  ∧ tracedtype smap TagRef64
  ∧ (∀ty fixty varty.
      tracedtype smap ty ∧ ty ∈ set fixty
    ⇒ 
      tracedtype smap (Hybrid fixty varty))
  ∧ (∀fixty varty.
      tracedtype smap varty ⇒ tracedtype smap (Hybrid fixty varty))
  ∧ (∀tag ty.
      tag ∈ FDOM smap
    ∧ tracedtype smap ty
    ∧ MEM ty (smap ' tag)
    ⇒
      tracedtype smap (Struct tag))
`

(* A native-safe type can be handed off to the "native" world. *)
val (native_safe_rules, native_safe_ind, native_safe_cases) = Hol_reln`
    (∀n. native_safe smap (Int n))
  ∧ native_safe smap Float
  ∧ native_safe smap Double
  ∧ native_safe smap Void
  ∧ (∀ty n. native_safe smap ty ⇒ native_safe smap (Vector ty n))
  ∧ (∀ty n. native_safe smap ty ⇒ native_safe smap (Array ty n))
  ∧ (∀ty. native_safe smap (UPtr ty))
  ∧ (∀sig. native_safe smap (UFuncPtr sig))
  ∧ (∀fty vty. 
      (∀ty. ty ∈ set fty ⇒ native_safe smap ty)
    ∧ native_safe smap vty
    ⇒
      native_safe smap (Hybrid fty vty))
  ∧ (∀tag.
      (∀ty. ty ∈ set (smap ' tag) ⇒ native_safe smap ty)
    ∧ tag ∈ FDOM smap
    ⇒
      native_safe smap (Struct tag))
`

val (wftype_rules, wftype_ind, wftype_cases) = Hol_reln`
    (∀vset n.
      0 < n
    ⇒
      wftype smap vset (Int n))
  ∧ (∀vset. wftype smap vset Float)
  ∧ (∀vset. wftype smap vset Double)
  ∧ (∀vset. wftype smap vset Void)
  ∧ (∀vset. wftype smap vset ThreadRef)
  ∧ (∀vset. wftype smap vset StackRef)
  ∧ (∀vset. wftype smap vset TagRef64)
  ∧ (∀vset ty.
      wftype smap vset ty ∨ (∃tag. ty = Struct tag ∧ tag ∈ vset)
    ⇒
      wftype smap vset (Ref ty))
  ∧ (∀vset ty.
      wftype smap vset ty ∨ (∃tag. ty = Struct tag ∧ tag ∈ vset)
    ⇒
      wftype smap vset (IRef ty))
  ∧ (∀vset ty.
      wftype smap vset ty ∨ (∃tag. ty = Struct tag ∧ tag ∈ vset)
    ⇒
      wftype smap vset (WeakRef ty))
  ∧ (∀vset ty.
      ¬tracedtype smap ty
    ∧ wftype smap vset ty ∨ (∃tag. ty = Struct tag ∧ tag ∈ vset)
    ⇒
      wftype smap vset (UPtr ty))
  ∧ (∀vset sig.
      (∀ty. ty ∈ set sig.arg_types ⇒ wftype smap vset ty)
    ∧ (∀ty. ty ∈ set sig.return_types ⇒ wftype smap vset ty)
    ⇒
      wftype smap vset (FuncRef sig))
  ∧ (∀vset sig.
      (∀ty. ty ∈ set sig.arg_types ⇒ wftype smap vset ty)
    ∧ (∀ty. ty ∈ set sig.return_types ⇒ wftype smap vset ty)
    ⇒
      wftype smap vset (UFuncPtr sig))
  ∧ (∀vset sz ty.
      0 < sz ∧ wftype smap vset ty ∧ ty ≠ Void
    ⇒
      wftype smap vset (Array ty sz))
  ∧ (∀vset sz ty.
      0 < sz ∧ wftype smap vset ty ∧ scalar_type ty
    ⇒
      wftype smap vset (Vector ty sz))
  ∧ (∀vset fixty varty.
      (∀ty. ty ∈ set fixty ⇒ wftype smap vset ty)
    ∧ wftype smap vset varty
    ∧ varty ≠ Void
    ⇒
      wftype smap vset (Hybrid fixty varty))
  ∧ (∀vset tag.
      tag ∈ FDOM smap
    ∧ smap ' tag ≠ []
    ∧ (∀ty. MEM ty (smap ' tag) ⇒ wftype smap (tag INSERT vset) ty ∧ ty ≠ Void)
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
  | TRUNC
  | ZEXT
  | SEXT
  | FPTRUNC
  | FPEXT
  | FPTOUI
  | FPTOSI
  | UITOFP
  | SITOFP
  | BITCAST
  | REFCAST
  | PTRCAST
`

(* canconvert M convtype (src : uvm_type) (tgt : uvm_type) *)

val (canconvert_rules, canconvert_ind, canconvert_cases) = Hol_reln`

    (∀m n. m ≤ n ⇒ canconvert M Smap TRUNC (Int n) (Int m))
  ∧ (∀m n. m ≤ n ⇒ canconvert M Smap ZEXT (Int m) (Int n))
  ∧ (∀m n. m ≤ n ⇒ canconvert M Smap SEXT (Int m) (Int n))
  ∧ canconvert M Smap FPTRUNC Double Float
  ∧ canconvert M Smap FPEXT Float Double
  ∧ (∀ty n. fpType ty ⇒ canconvert M Smap FPTOUI ty (Int n))
  ∧ (∀ty n. fpType ty ⇒ canconvert M Smap FPTOSI ty (Int n))
  ∧ (∀ty n. fpType ty ⇒ canconvert M Smap UITOFP (Int n) ty)
  ∧ (∀ty n. fpType ty ⇒ canconvert M Smap SITOFP (Int n) ty)
  ∧ canconvert M Smap BITCAST (Int M.floatsize) Float
  ∧ canconvert M Smap BITCAST Float (Int M.floatsize)
  ∧ canconvert M Smap BITCAST (Int M.doublesize) Double
  ∧ canconvert M Smap BITCAST Double (Int M.doublesize)

  (* ptrcast cases *)
  ∧ (∀n ty.
      M.ptrsize = n
    ⇒ 
      canconvert M Smap BITCAST (Int n) (UPtr ty))
  ∧ (∀n ty.
      M.ptrsize = n (* tell KW *)
    ⇒
      canconvert M Smap BITCAST (UPtr ty) (Int n))

  (* refcast cases *)
  ∧ (∀ty. canconvert M Smap BITCAST (Ref Void) (Ref ty))
  ∧ (∀ty. canconvert M Smap BITCAST (Ref ty) (Ref Void))
  ∧ (∀ty. canconvert M Smap BITCAST (Ref Void) (Ref ty))
  ∧ (∀tag1 tag2.
      tag1 ∈ FDOM Smap ∧ tag2 ∈ FDOM Smap
    ∧ (Smap ' tag1 <<= Smap ' tag2 ∨ Smap ' tag2 <<= Smap ' tag1)
    ⇒
      canconvert M Smap BITCAST (Ref (Struct tag1)) (Ref (Struct tag2)))
`

val _ = export_theory()

