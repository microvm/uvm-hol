open HolKernel Parse boolLib bossLib;

val _ = new_theory "uvmTypes";

local open stringTheory finite_mapTheory in end
open lcsymtacs
val _ = ParseExtras.tight_equality()

val _ = type_abbrev ("typename", ``:string``)

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
  | Struct ((uvm_type + typename) list)
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

(* Relation of type `(typename |-> uvm_type) -> uvm_type set` *)
val (tracedtype_rules, tracedtype_ind, tracedtype_cases) = Hol_reln`
    (∀ty. tracedtype tmap (Ref ty))
  ∧ (∀ty. tracedtype tmap (IRef ty))
  ∧ (∀ty. tracedtype tmap (WeakRef ty))
  ∧ (∀sz ty.
      tracedtype tmap ty ⇒
      tracedtype tmap (Array ty sz))
  ∧ (∀sz ty.
      tracedtype tmap ty ⇒
      tracedtype tmap (Vector ty sz))
  ∧ tracedtype tmap ThreadRef
  ∧ tracedtype tmap StackRef
  ∧ tracedtype tmap TagRef64
  ∧ (∀ty fixtys varty.
      tracedtype tmap ty ∧ MEM ty fixtys
    ⇒
      tracedtype tmap (Hybrid fixtys varty))
  ∧ (∀fixtys varty.
      tracedtype tmap varty ⇒ tracedtype tmap (Hybrid fixtys varty))
  ∧ (∀ty fields.
      tracedtype tmap ty
    ∧ MEM (INL ty) fields
    ⇒
      tracedtype tmap (Struct fields))
  ∧ (∀ty_name ty fields.
      SOME ty = FLOOKUP tmap ty_name
    ∧ tracedtype tmap ty
    ∧ MEM (INR ty_name) fields
    ⇒
      tracedtype tmap (Struct fields))
`

(* A native-safe type can be handed off to the "native" world.

   Relation of type `(typename |-> uvm_type) -> uvm_type set`
*)
val (native_safe_rules, native_safe_ind, native_safe_cases) = Hol_reln`
    (∀n. native_safe tmap (Int n))
  ∧ native_safe tmap Float
  ∧ native_safe tmap Double
  ∧ native_safe tmap Void
  ∧ (∀ty n. native_safe tmap ty ⇒ native_safe tmap (Vector ty n))
  ∧ (∀ty n. native_safe tmap ty ⇒ native_safe tmap (Array ty n))
  ∧ (∀ty. native_safe tmap (UPtr ty))
  ∧ (∀sig. native_safe tmap (UFuncPtr sig))
  ∧ (∀ftys vty.
      (∀ty. MEM ty ftys ⇒ native_safe tmap ty)
    ∧ native_safe tmap vty
    ⇒
      native_safe tmap (Hybrid ftys vty))
  ∧ (∀fields.
      (∀ty. MEM (INL ty) fields ⇒ native_safe tmap ty)
    ∧ (∀ty_name ty.
        SOME ty = FLOOKUP tmap ty_name
      ∧ MEM (INR ty_name) fields
      ⇒
        native_safe tmap ty)
    ⇒
      native_safe tmap (Struct fields))
`

(* The set of well-formed types. The type of this relation is

       (typename |-> uvm_type) ->
       typename set ->
       uvm_type set
   
   The first parameter is the global type name map (for recursively-defined
   structs), and the second parameter is an accumulator of previously-followed
   typenames (also for recursively-defined structs). The second parameter is
   only used for recursion, and therefore should always be the empty set.
*)
val (wftype_rules, wftype_ind, wftype_cases) = Hol_reln`
    (∀vset n.
      0 < n
    ⇒
      wftype tmap vset (Int n))
  ∧ (∀vset. wftype tmap vset Float)
  ∧ (∀vset. wftype tmap vset Double)
  ∧ (∀vset. wftype tmap vset Void)
  ∧ (∀vset. wftype tmap vset ThreadRef)
  ∧ (∀vset. wftype tmap vset StackRef)
  ∧ (∀vset. wftype tmap vset TagRef64)
  ∧ (∀vset ty.
      wftype tmap vset ty
    ⇒
      wftype tmap vset (Ref ty))
  ∧ (∀vset ty.
      wftype tmap vset ty
    ⇒
      wftype tmap vset (IRef ty))
  ∧ (∀vset ty.
      wftype tmap vset ty
    ⇒
      wftype tmap vset (WeakRef ty))
  ∧ (∀vset ty.
      ¬tracedtype tmap ty
    ∧ wftype tmap vset ty
    ⇒
      wftype tmap vset (UPtr ty))
  ∧ (∀vset sig.
      (∀ty. MEM ty sig.arg_types ⇒ wftype tmap vset ty)
    ∧ (∀ty. MEM ty sig.return_types ⇒ wftype tmap vset ty)
    ⇒
      wftype tmap vset (FuncRef sig))
  ∧ (∀vset sig.
      (∀ty. MEM ty sig.arg_types ⇒ wftype tmap vset ty)
    ∧ (∀ty. MEM ty sig.return_types ⇒ wftype tmap vset ty)
    ⇒
      wftype tmap vset (UFuncPtr sig))
  ∧ (∀vset sz ty.
      0 < sz ∧ wftype tmap vset ty ∧ ty ≠ Void
    ⇒
      wftype tmap vset (Array ty sz))
  ∧ (∀vset sz ty.
      0 < sz ∧ wftype tmap vset ty ∧ scalar_type ty
    ⇒
      wftype tmap vset (Vector ty sz))
  ∧ (∀vset fixtys varty.
      (∀ty. MEM ty fixtys ⇒ wftype tmap vset ty)
    ∧ wftype tmap vset varty
    ∧ varty ≠ Void
    ⇒
      wftype tmap vset (Hybrid fixtys varty))
  ∧ (∀vset fields.
      fields ≠ []
    ∧ (∀ty. MEM (INL ty) fields ⇒ wftype tmap vset ty ∧ ty ≠ Void)
    ∧ (∀ty_name ty.
        MEM (INR ty_name) fields
      ⇒
        SOME ty = FLOOKUP tmap ty_name
      ∧ ty ≠ Void
      ∧ (ty_name ∈ vset ∨ wftype tmap (ty_name INSERT vset) ty))
    ⇒
      wftype tmap vset (Struct tag))
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
       simp[Once native_safe_cases, Once tracedtype_cases] >> NO_TAC)
  >- ((* hybrid *)
      ntac 3 strip_tac >>
      dsimp[Once native_safe_cases, Once tracedtype_cases] >> rpt strip_tac >>
      metis_tac[])
  >- ((* struct *)
      ntac 2 strip_tac >>
      dsimp[Once native_safe_cases, Once tracedtype_cases] >> rpt strip_tac >>
      metis_tac[]))

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
