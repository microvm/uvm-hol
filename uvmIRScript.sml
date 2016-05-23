open HolKernel Parse boolLib bossLib;

open uvmTypesTheory;
open uvmValuesTheory;

val _ = new_theory "uvmIR";

val _ = type_abbrev ("ssavar", ``:string``)

val _ = type_abbrev ("label", ``:string``)
val _ = type_abbrev ("block_label", ``:string``)

val _ = type_abbrev ("trap_data", ``:num``)

val _ = Datatype`
  memoryorder =
    NOT_ATOMIC | RELAXED | CONSUME | ACQUIRE | RELEASE | ACQ_REL | SEQ_CST
`;

val _ = Datatype`
  binop = Add | Sub | Mul | Sdiv | Srem | Udiv | Urem | Shl | LShr | AShr
        | And | Or | Xor | FAdd | FSub | FMul | FDiv | FRem
`;

val (binoptype_rules, binoptype_ind, binoptype_cases) = Hol_reln`
  (∀n opn. opn ∈ {Add; Sub; Mul; Sdiv; Srem; Udiv; Urem; And; Or; Xor} ⇒
           binoptype opn (Int n) (Int n) (Int n)) ∧

  (∀n m opn. opn ∈ {Shl; LShr; AShr} ⇒
             binoptype opn (Int n) (Int m) (Int n)) ∧

  (∀ty opn. fp_type ty ∧ opn ∈ {FAdd; FSub; FMul; FDiv; FRem} ⇒
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
      maybeVector eqcomparable ity ∧ iop ∈ {EQ ; NE}
    ⇒
      cmpOptype iop ity ity (cmpresult ity)) ∧

  (∀iop ity.
      maybeVector (int_type ∪ ptr_type ∪ iref_type) ity ∧
      iop ∈ { UGE ; UGT ; ULE ; ULT}
    ⇒
      cmpOptype iop ity ity (cmpresult ity)) ∧

  (∀iop ity.
       maybeVector int_type ity ∧
       iop ∈ {SGE ; SGT ; SLE ; SLT}
    ⇒
       cmpOptype iop ity ity (cmpresult ity)) ∧

  (∀fop fty.
      (fp_type fty ∨ (∃sz fty0. fp_type fty0 ∧ fty = Vector fty0 sz)) ∧
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
  | DA_Normal ssavar    (* i.e., something already in scope *)
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
    methodname : ssavar ;  (* allowing for indirect calls *)
    args : ssavar list ;
    convention : callconvention
  |>
`

val _ = Datatype`
  atomicrmw_op =
    XCHG | ADD | SUB | AND | NAND | OR | XOR | MAX | MIN | UMAX | UMIN
`

val _ = Datatype`operand = SSAV_OP ssavar | CONST_OP value`

val _ = Datatype`
  expression =
  | Binop binop operand operand
       (* performs arithmetic, yielding a value *)
  | Value value
       (* yields the value *)
  | ExprCall calldata
             bool (* T to abort, F to rethrow *)
       (* yields a tuple of results from the call *)
  | New uvm_type (* must not be hybrid *)
       (* yields a reference of type uvm_type *)
  | AllocA uvm_type (* must not be hybrid *)
       (* yields an iref to the type uvm_type *)
  | NewHybrid uvm_type  (* must be a hybrid type *)
              ssavar (* length of varying part (can be zero);
                        will cause u.b., or raise exn if
                        get-variable-part-iref call is made on return value *)
       (* yields ref *)
  | AllocAHybrid uvm_type ssavar
       (* as above, but returns iref *)
  | NewStack ssavar (* function reference *)
       (* yields stack reference *)
  | NewThread ssavar (* stack id *)
              (ssavar list) (* args for resumption point *)
       (* yields thread reference *)
  | NewThreadExn ssavar (* stack id *)
                 ssavar (* exception value *)
       (* yields thread reference (thread resumes with exceptional value) *)

  | NewFrameCursor ssavar (* stack id *)
       (* yields frame cursor *)
    (* stack manipulation API to be expanded *)
  | GetIref ssavar (* ref *)
       (* yields corresponding iref *)
  | GetFieldIref ssavar (* iref / ptr *)
                 value  (* field index *)
       (* yields iref/ptr *)
  | GetElementIref ssavar (* iref / ptr to array type *)
                   ssavar (* array index *)
       (* yields iref/ptr *)
  | ShiftIref ssavar (* iref/ptr to anything (not void) *)
              ssavar (* offset *)
       (* yields iref/ptr *)
  | GetVarPartIref ssavar (* iref/ptr to hybrid *)
       (* yeilds iref/ptr to first element of var-part of hybrid IF IT EXISTS *)
`;

val _ = Datatype`
  instruction =
  | Assign (ssavar list) expression
  | Load ssavar (* destination variable  *)
         bool (* T for iref, F for ptr *)
         ssavar (* source memory address *)
         memoryorder
  | Store ssavar (* value to be written *)
          bool (* T for iref, F for ptr *)
          ssavar (* destination memory address *)
          memoryorder
  | CmpXchg ssavar (* output: pair (oldvalue, boolean (T = success, F = failure)) *)
            bool (* T for iref, F for ptr *)
            bool (* T for strong, F for weak *)
            memoryorder (* success order *)
            memoryorder (* failure order *)
            ssavar (* memory location *)
            operand (* expected value *)
            operand (* desired value *)
  | AtomicRMW ssavar (* output: old memory value *)
              bool (* T for iref, F for ptr *)
              memoryorder
              atomicrmw_op
              ssavar (* memory location *)
              operand (* operand for op *)
  | Fence memoryorder
`

val read_opnd_vars_def = Define`
  read_opnd_vars (opnd : operand) : ssavar set =
    case opnd of
    | SSAV_OP v => {v}
    | CONST_OP _ => {}
`

val read_expr_vars_def = Define`
  read_expr_vars (expr : expression) : ssavar set =
    case expr of
    | Binop _ a b => read_opnd_vars a ∪ read_opnd_vars b
    | Value _ => {}
    | ExprCall cd _ => {cd.methodname} ∪ LIST_TO_SET cd.args
    | New _ => {}
    | AllocA _ => {}
    | NewHybrid _ len => {len}
    | AllocAHybrid _ len => {len}
    | NewStack fn => {fn}
    | NewThread stack args => {stack} ∪ LIST_TO_SET args
    | NewThreadExn stack exn => {stack; exn}
    | NewFrameCursor stack => {stack}
    | GetIref ref => {ref}
    | GetFieldIref ref _ => {ref}
    | GetElementIref ref index => {ref; index}
    | ShiftIref ref offset => {ref; offset}
    | GetVarPartIref ref => {ref}
`

val read_vars_def = Define`
  read_vars (inst : instruction) : ssavar set =
    case inst of
    | Assign _ e => read_expr_vars e
    | Load _ _ src _ => {src}
    | Store src _ _ _ => {src}
    | CmpXchg _ _ _ _ _ loc exp des =>
        {loc} ∪ read_opnd_vars exp ∪ read_opnd_vars des
    | AtomicRMW _ _ _ _ loc opnd =>
        {loc} ∪ read_opnd_vars opnd
    | Fence _ => {}
`

val _ = type_abbrev("wpid", ``:num``)

val _ = Datatype`
  terminst =
  | Return (ssavar list)
  | ThreadExit
  | Throw (ssavar list)
  | TailCall calldata
  | Branch1 destination
  | Branch2 ssavar destination destination
  | Watchpoint
      ((wpid # destination) option)
         (* NONE = unconditional trap *)
         (* SOME(wpid, dest) = conditional on wpid, trap if set;
                               if not, branch to dest *)
      resumption_data
  | WPBranch wpid destination destination
  | Call calldata resumption_data
  | Swapstack
      ssavar (* stackID *)
      bool (* T if exception values are being transferred *)
      (ssavar list) (* parameters *)
      resumption_data
  | Switch ssavar destination (value |-> destination)
  | ExnInstruction instruction resumption_data
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
    args : (ssavar # uvm_type) list ;
    body : instruction list ;
    exit : terminst ;
    keepalives : ssavar list
  |>
`


val _ = Datatype`
  declaration =
  | ConstDecl constname uvm_type value
  | TypeDef typename uvm_type
  | FunctionSignature signame uvm_type (uvm_type list)
  | FuncDef fnname signame label (label |-> bblock)
`

val _ = type_abbrev("tid", ``:num``)

val _ = type_abbrev("memreqid", ``:num``)
val _ = type_abbrev("memdeps", ``:memreqid set``)

val memory_message_def = Datatype`
  memory_message =
  | Read  addr memreqid       memoryorder memdeps
  | Write addr memreqid value memoryorder memdeps
  | MMFence                   memoryorder
`;

val memory_message_resolve_def = Datatype`
  memory_message_resolve =
  | ResolvedRead value memreqid`;

val _ = export_theory();
