open HolKernel Parse boolLib bossLib;

open uvmTypesTheory

val _ = new_theory "uvmIR";

val _ = type_abbrev ("SSAvar", ``:string``)

val _ = type_abbrev ("label", ``:string``)

val _ = Datatype`
  memoryorder = Relaxed | Atomic (*... *)`

val _ = Datatype`
  binop = Add | Sub | Mul | Sdiv | Srem | Udiv | Urem | Shl | LShr | AShr
        | And | Or | Xor | FAdd | FSub | FMul | FDiv | FRem
`;

val (binoptype_rules, binoptype_ind, binoptype_cases) = Hol_reln`
  (∀n opn. opn ∈ {Add; Sub; Mul; Sdiv; Srem; Udiv; Urem; And; Or; Xor}
           ⇒
           binoptype opn (Int n) (Int n) (Int n)) ∧

  (∀n m opn. opn ∈ {Shl; LShr; AShr} ⇒
             binoptype opn (Int n) (Int m) (Int n)) ∧

  (∀ty opn. fpType ty ∧ opn ∈ {FAdd; FSub; FMul; FDiv; FRem} ⇒
            binoptype opn ty ty ty)
`;

val _ = Datatype`
  cmpOp = EQ | NE | SGE | SGT | SLE | SLT | UGE | UGT | ULE | ULT
        | FFALSE | FTRUE | FOEQ | FOGT | FOGE | FOLT | FOLE | FONE
        | FORD | FUEQ | FUGT | FUGE | FULT | FULE | FUNE | FUNO
`

val cmpresult_def = Define`
  cmpresult (Vector _ sz) = Vector (Int 1) sz ∧
  cmpresult _ = Int 1
`;

val maybeVector_def = Define`
  maybeVector P ty ⇔ P ty ∨ ∃ty0 sz. ty = Vector ty0 sz ∧ P ty0
`;

val (cmpOptype_rules, cmpOptype_ind, cmpOptype_cases) = Hol_reln`
  (∀iop ity.
    maybeVector eqcomparable ity ∧ iop ∈ {EQ ; NE }
   ⇒
    cmpOptype iop ity ity (cmpresult ity)) ∧

  (∀iop ity.
      maybeVector (intType ∪ ptrType ∪ irefType) ity ∧
      iop ∈ { UGE ; UGT ; ULE ; ULT}
    ⇒
      cmpOptype iop ity ity (cmpresult ity)) ∧

  (∀iop ity.
       maybeVector intType ity ∧
       iop ∈ {SGE ; SGT ; SLE ; SLT}
    ⇒
       cmpOptype iop ity ity (cmpresult ity))

    ∧

  (∀fop fty.
      (fpType fty ∨ (∃sz fty0. fpType fty0 ∧ fty = Vector fty0 sz)) ∧
      fop ∈ { FFALSE ; FTRUE ; FOEQ ; FOGT ; FOGE ; FOLT ; FOLE ; FONE ;
              FORD ; FUEQ ; FUGT ; FUGE ; FULT ; FULE ; FUNE ; FUNO }
    ⇒
      cmpOptype fop fty fty (cmpresult fty))
`;



val _ = export_theory();
