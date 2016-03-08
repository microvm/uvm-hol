open HolKernel Parse boolLib bossLib;

open uvmTypesTheory;
open uvmValuesTheory;

val _ = new_theory "uvmIR";

val _ = type_abbrev ("SSAVar", ``:string``)

val _ = type_abbrev ("label", ``:string``)
val _ = type_abbrev ("block_label", ``:string``)

val _ = type_abbrev ("trapData", ``:num``)

val _ = Datatype`
  memoryorder =
   NOT_ATOMIC | RELAXED | CONSUME | ACQUIRE | RELEASE | ACQ_REL | SEQ_CST
`;

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


val _ = type_abbrev("constname", ``:string``)
val _ = type_abbrev("typename", ``:string``)
val _ = type_abbrev("fnname", ``:string``)
val _ = type_abbrev("signame", ``:string``)
val _ = type_abbrev("label", ``:string``)

val _ = Datatype`
  destarg =
    DA_Normal SSAVar    (* i.e., something already in scope *)
  | DA_FreshBound num   (* index to resumed value list - may not be any if, for
                           example, the statement is Return or Tailcall, but
                           if the statement is a call, the concrete syntax might
                           be something like

                              CALL m(...args...) EXC(%ndbl(%x, $2) %hbl($1, %a))
                        *)
  | DA_Value value
`;

val _ = type_abbrev("destination", ``:block_label # (destarg list)``)

val _ = Datatype`
  resumption_data = <|
    normaldest : destination ;
    exceptionaldest : destination
  |>
`;

val _ = type_abbrev("ffitype", ``:string``)

val _ = Datatype`
  callconvention = Mu | Foreign ffitype
`

val _ = Datatype`
  calldata = <|
    methodname : SSAVar ;  (* allowing for indirect calls *)
    args : SSAVar list ;
    convention : callconvention
  |>
`

val _ = Datatype`
  AtomicRMW_Op =
    XCHG | ADD | SUB | AND | NAND | OR | XOR | MAX | MIN | UMAX | UMIN
`

val _ = Datatype`operand = SSAV_OP SSAVar | CONST_OP value`

val _ = Datatype`
  expression =
     Binop binop SSAVar SSAVar
   | Value value
     (* memory operations *)

   | CMPXCHG bool (* T for iref, F for ptr *)
             bool (* T for strong, F for weak *)
             memoryorder (* success order *)
             memoryorder (* failure order *)
             SSAVar (* memory location *)
             operand (* expected value *)
             operand (* desired value *)
   | ATOMICRMW bool (* T for iref, F for ptr *)
               memoryorder
               AtomicRMW_Op
               SSAVar (* memory location *)
               operand (* operand for op *)
   | FENCE memoryorder

     (* allocation operations *)
   | New uvmType
   | AllocA uvmType
   | NewHybrid uvmType SSAVar (* num can be zero; will cause u.b., or raise exn if
                              get variable part iref call is made on return value *)
   | AllocAHybrid uvmType SSAVar
   | NewStack SSAVar (* variable contains method *)
   | NewThread SSAVar (* stack id *) (SSAVar list) (* args for resumption point *)
   | NewThreadExn SSAVar (* stack id *) SSAVar (* exception value *)


   | PushFrame signame (* stackID *) SSAVar (* method *) SSAVar
   | PopFrame SSAVar (* stackID *)
`

val _ = Datatype`
  instruction =
    Assign (SSAVar list) expression
  | Load SSAVar  (* destination register *)
         bool (* T for iref, F for ptr *)
         SSAVar (* memory location *)
         memoryorder
  | Store SSAVar (* value to be written *)
          bool (* T for iref, F for ptr *)
          SSAVar (* memory location *)
          memoryorder
`

val _ = type_abbrev("wpid", ``:num``)

val _ = Datatype`
  terminst =
      Return (SSAVar list)
    | ThreadExit
    | Throw (SSAVar list)
    | TailCall calldata
    | Branch1 destination
    | Branch2 SSAVar destination destination
    | Watchpoint ((wpid # destination) option) resumption_data
    | WPBranch wpid destination destination
    | Call calldata resumption_data
    | Swapstack
        SSAVar (* stackID *)
        bool (* T if exception values are being transferred *)
        (SSAVar list) (* parameters *)
        resumption_data
    | Switch SSAVar destination (value |-> destination)
    | ExnInstruction expression resumption_data
`;

(* Wrapping expressions with ExnInstruction forces the implementation
   to gracefully handle what would have otherwise been undefined
   behaviour. For example, an unwrapped division lets demons fly out
   of your nose if the second argument is 0. On the other hand, if the
   client wraps a division with resumption_data, the implementation
   must check for the zero argument and/or set up the appropriate
   signal handling so that the exceptional branch can get called when
   the second argument is indeed 0.
*)

val _ = Datatype`
  bblock = <|
    args : (SSAVar # uvmType) list ;
    body : instruction list ;
    exit : terminst ;
    keepalives : SSAVar list
  |>
`


val _ = Datatype`
  declaration =
    ConstDecl constname uvmType value
  | TypeDef typename uvmType
  | FunctionSignature signame uvmType (uvmType list)
  | FuncDef fnname signame label (label |-> bblock)
`





val _ = type_abbrev("tid", ``:num``)

val _ = type_abbrev("memreqid", ``:num``)
val _ = type_abbrev("memdeps", ``:memreqid set``)



val memoryMessage_def = Datatype`
  memoryMessage = Read  addr memreqid       memoryorder memdeps
                | Write addr memreqid value memoryorder memdeps
                | Fence                     memoryorder
`;

val memoryMessageResolve_def = Datatype`
    memoryMessageResolve = ResolvedRead value memreqid`;





val _ = export_theory();
