open HolKernel Parse boolLib bossLib;

open uvmTypesTheory;
open uvmValuesTheory;

val _ = new_theory "uvmIR";

val _ = type_abbrev ("ssavar", ``:string``)
val _ = type_abbrev ("label", ``:string``)
val _ = type_abbrev ("block_label", ``:string``)
val _ = type_abbrev ("trap_data", ``:num``)

(* Memory order (see the spec)
   https://github.com/microvm/microvm-spec/blob/master/memory-model.rest#memory-operations
*)
val _ = Datatype`
  memory_order =
  | NOT_ATOMIC
  | RELAXED
  | CONSUME
  | ACQUIRE
  | RELEASE
  | ACQ_REL
  | SEQ_CST
`

(* Binary operations (see the spec)
   https://github.com/microvm/microvm-spec/blob/master/instruction-set.rest#binary-operations
*)
val _ = Datatype`
  bin_op =
  | ADD  (* <int> - add *)
  | SUB  (* <int> - subtract *)
  | MUL  (* <int> - multiply *)
  | SDIV (* <int> - signed divide *)
  | SREM (* <int> - signed remainder *)
  | UDIV (* <int> - unsigned divide *)
  | UREM (* <int> - unsigned remainder *)
  | SHL  (* <int> - left shift *)
  | LSHR (* <int> - logical right shift *)
  | ASHR (* <int> - arithmetic right shift *)
  | AND  (* <int> - bitwise and *)
  | OR   (* <int> - bitwise or *)
  | XOR  (* <int> - bitwise exclusive or *)
  | FADD (* <float|double> - FP add *)
  | FSUB (* <float|double> - FP subtract *)
  | FMUL (* <float|double> - FP multiply *)
  | FDIV (* <float|double> - FP divide *)
  | FREM (* <float|double> - FP remainder *)
`

(* Binary operation types: Relation between a binary operation * and a triple of
   types (α, β, ρ) such that (a: α) * (b: β) = (r: ρ).
*)
val (bin_op_type_rules, bin_op_type_ind, bin_op_type_cases) = Hol_reln`
  (∀n opn. opn ∈ {ADD; SUB; MUL; SDIV; SREM; UDIV; UREM; AND; OR; XOR} ⇒
           bin_op_type opn (Int n) (Int n) (Int n)) ∧

  (∀n m opn. opn ∈ {SHL; LSHR; ASHR} ⇒
             bin_op_type opn (Int n) (Int m) (Int n)) ∧

  (∀ty opn. fp_type ty ∧ opn ∈ {FADD; FSUB; FMUL; FDIV; FREM} ⇒
            bin_op_type opn ty ty ty)
`

(* Comparison operations (see the spec)
   https://github.com/microvm/microvm-spec/blob/master/instruction-set.rest#comparison
*)
val _ = Datatype`
  cmp_op =
  | EQ     (* <any EQ-comparable> - equal *)
  | NE     (* <any EQ-comparable> - not equal *)
  | SGE    (* <int> - signed greater than or equal *)
  | SGT    (* <int> - signed greater than *)
  | SLE    (* <int> - signed less than or equal *)
  | SLT    (* <int> - signed less than *)
  | UGE    (* <any ULT-comparable> - unsigned greater than or equal *)
  | UGT    (* <any ULT-comparable> - unsigned greater than *)
  | ULE    (* <any ULT-comparable> - unsigned less than or equal *)
  | ULT    (* <any ULT-comparable> - unsigned less than *)
  | FFALSE (* <float|double> - always false *)
  | FTRUE  (* <float|double> - always true *)
  | FOEQ   (* <float|double> - ordered equal *)
  | FOGT   (* <float|double> - ordered greater than *)
  | FOGE   (* <float|double> - ordered greater than or equal *)
  | FOLT   (* <float|double> - ordered less than *)
  | FOLE   (* <float|double> - ordered less than or equal *)
  | FONE   (* <float|double> - ordered not equal *)
  | FORD   (* <float|double> - ordered *)
  | FUEQ   (* <float|double> - unordered equal *)
  | FUGT   (* <float|double> - unordered greater than *)
  | FUGE   (* <float|double> - unordered greater than or equal *)
  | FULT   (* <float|double> - unordered less than *)
  | FULE   (* <float|double> - unordered less than or equal *)
  | FUNE   (* <float|double> - unordered not equal *)
  | FUNO   (* <float|double> - unordered *)
`

(* The result type of a comparison operation on a given type *)
val cmp_result_def = Define`
  cmp_result (Vector _ sz) = Vector (Int 1) sz ∧
  cmp_result _ = Int 1
`

(* Comparison operation types: Relation between a comparison operation ≤ and a
   triple of types (α, β, ρ) such that (a: α) ≤ (b: β) = (r: ρ).
*)
val (cmp_op_type_rules, cmp_op_type_ind, cmp_op_type_cases) = Hol_reln`
  (∀iop ity.
      maybeVector eqcomparable ity ∧ iop ∈ {EQ ; NE}
    ⇒
      cmp_op_type iop ity ity (cmp_result ity)) ∧

  (∀iop ity.
      maybeVector (int_type ∪ ptr_type ∪ iref_type) ity ∧
      iop ∈ { UGE ; UGT ; ULE ; ULT}
    ⇒
      cmp_op_type iop ity ity (cmp_result ity)) ∧

  (∀iop ity.
       maybeVector int_type ity ∧
       iop ∈ {SGE ; SGT ; SLE ; SLT}
    ⇒
       cmp_op_type iop ity ity (cmp_result ity)) ∧

  (∀fop fty.
      (fp_type fty ∨ (∃sz fty0. fp_type fty0 ∧ fty = Vector fty0 sz)) ∧
      fop ∈ { FFALSE ; FTRUE ; FOEQ ; FOGT ; FOGE ; FOLT ; FOLE ; FONE ;
              FORD ; FUEQ ; FUGT ; FUGE ; FULT ; FULE ; FUNE ; FUNO }
    ⇒
      cmp_op_type fop fty fty (cmp_result fty))
`

val _ = type_abbrev("constname", ``:string``)
val _ = type_abbrev("typename", ``:string``)
val _ = type_abbrev("fnname", ``:string``)
val _ = type_abbrev("fnvname", ``:fnname # num``)
val _ = type_abbrev("signame", ``:string``)
val _ = type_abbrev("label", ``:string``)

val _ = Datatype`
  destarg =
  | ExistingVar α      (* i.e., something already in scope *)
  | CallReturnVal num  (* index to resumed value list - may not be any if, for
                          example, the statement is Return or Tailcall, but
                          if the statement is a call, the concrete syntax might
                          be something like

                              CALL m(...args...) EXC(%ndbl(%x, $2) %hbl($1, %a))
                       *)
`

val _ = type_abbrev("destination", ``:block_label # (α destarg) list``)

val _ = Datatype`
  resumption_data = <|
    normal_dest : α destination ;
    exceptional_dest : α destination
  |>
`

val _ = type_abbrev("ffitype", ``:string``)

val _ = Datatype`
  callconvention =
  | Mu
  | Foreign ffitype
`

val _ = Datatype`
  calldata = <|
    methodname : α ;  (* allowing for indirect calls *)
    args : α list ;
    convention : callconvention
  |>
`

(* AtomicRMW operators (see the spec)
   https://github.com/microvm/microvm-spec/blob/master/instruction-set.rest#atomicrmw-instruction
*)
val _ = Datatype`
  atomicrmw_op =
  | RMW_XCHG (* <any> - exchange *)
  | RMW_ADD  (* <int> - add *)
  | RMW_SUB  (* <int> - subtract *)
  | RMW_AND  (* <int> - bitwise and *)
  | RMW_NAND (* <int> - bitwise nand *)
  | RMW_OR   (* <int> - bitwise or *)
  | RMW_XOR  (* <int> - bitwise xor *)
  | RMW_MAX  (* <int> - signed max *)
  | RMW_MIN  (* <int> - signed min *)
  | RMW_UMAX (* <int> - unsigned max *)
  | RMW_UMIN (* <int> - unsigned min *)
`

(* Either an SSA variable or a constant *)
val _ = Datatype`
  operand =
  | VarOp ssavar
  | ConstOp value
`

(* All instruction types are generic in their SSA variable type. For example, a
   `ssavar instruction` is a normal instruction (as per the spec), whereas an
   `operand instruction` may contain literal constants in place of SSA
   variables. The same applies to `expression`, `calldata`, etc.
*)

val _ = Datatype`
  expression =
  | Binop bin_op α α
       (* performs arithmetic, yielding a value *)
  | Value value
       (* yields the value *)
  | ExprCall (α calldata)
             bool (* T to abort, F to rethrow *)
       (* yields a tuple of results from the call *)
  | New uvm_type (* must not be hybrid *)
       (* yields a reference of type uvm_type *)
  | AllocA uvm_type (* must not be hybrid *)
       (* yields an iref to the type uvm_type *)
  | NewHybrid uvm_type  (* must be a hybrid type *)
              α (* length of varying part (can be zero);
                   will cause u.b., or raise exn if
                   get-variable-part-iref call is made on return value *)
       (* yields ref *)
  | AllocAHybrid uvm_type α
       (* as above, but returns iref *)
  | NewStack α (* function reference *)
       (* yields stack reference *)
  | NewThread α (* stack id *)
              (α list) (* args for resumption point *)
       (* yields thread reference *)
  | NewThreadExn α (* stack id *)
                 α (* exception value *)
       (* yields thread reference (thread resumes with exceptional value) *)

  | NewFrameCursor α (* stack id *)
       (* yields frame cursor *)
    (* stack manipulation API to be expanded *)
  | GetIref α (* ref *)
       (* yields corresponding iref *)
  | GetFieldIref α (* iref / ptr *)
                 num  (* field index *)
       (* yields iref/ptr *)
  | GetElementIref α (* iref / ptr to array type *)
                   α (* array index *)
       (* yields iref/ptr *)
  | ShiftIref α (* iref/ptr to anything (not void) *)
              α (* offset *)
       (* yields iref/ptr *)
  | GetVarPartIref α (* iref/ptr to hybrid *)
       (* yields iref/ptr to first element of var-part of hybrid IF IT EXISTS *)
`

val _ = Datatype`
  instruction =
  | Assign (α list) (α expression)
  | Load α (* destination variable  *)
         bool (* T for iref, F for ptr *)
         α (* source memory address *)
         memory_order
  | Store α (* value to be written *)
          bool (* T for iref, F for ptr *)
          α (* destination memory address *)
          memory_order
  | CmpXchg α (* output: pair (oldvalue, boolean (T = success, F = failure)) *)
            bool (* T for iref, F for ptr *)
            bool (* T for strong, F for weak *)
            memory_order (* success order *)
            memory_order (* failure order *)
            α (* memory location *)
            α (* expected value *)
            α (* desired value *)
  | AtomicRMW α (* output: old memory value *)
              bool (* T for iref, F for ptr *)
              memory_order
              atomicrmw_op
              α (* memory location *)
              α (* operand for op *)
  | Fence memory_order
`

val _ = type_abbrev("wpid", ``:num``)

val _ = Datatype`
  terminst =
  | Return (α list)
  | ThreadExit
  | Throw (α list)
  | TailCall (α calldata)
  | Branch1 (α destination)
  | Branch2 α (α destination) (α destination)
  | Watchpoint
      ((wpid # α destination) option)
         (* NONE = unconditional trap *)
         (* SOME(wpid, dest) = conditional on wpid, trap if set;
                               if not, branch to dest *)
      (α resumption_data)
  | WPBranch wpid (α destination) (α destination)
  | Call (α calldata) (α resumption_data)
  | Swapstack
      α (* stackID *)
      bool (* T if exception values are being transferred *)
      (α list) (* parameters *)
      (α resumption_data)
  | Switch α (α destination) (value |-> α destination)
  | ExnInstruction (α instruction) (α resumption_data)
`

(* Wrapping expressions with ExnInstruction forces the implementation
   to gracefully handle what would have otherwise been undefined
   behaviour. For example, an unwrapped division lets demons fly out
   of your nose if the second argument is 0. On the other hand, if the
   client wraps a division with resumption_data, the implementation
   must check for the zero argument and/or set up the appropriate
   signal handling so that the exceptional branch can get called when
   the second argument is indeed 0.
*)

(* Map functions: map the SSA variables in expressions, instructions, etc. to
   new SSA variable types. Each maps from an `α foo` to a `β foo`.
*)

val map_calldata_def = Define`
  map_calldata (f : α -> β) (cd : α calldata) : β calldata = <|
      methodname := f cd.methodname ;
      args := MAP f cd.args ;
      convention := cd.convention
    |>
`

val map_expr_def = Define`
  map_expr (f : α -> β) (expr : α expression) : β expression =
    case expr of
    | Binop op a b => Binop op (f a) (f b)
    | Value v => Value v
    | ExprCall cd flag => ExprCall (map_calldata f cd) flag
    | New t => New t
    | AllocA t => AllocA t
    | NewHybrid t len => NewHybrid t (f len)
    | AllocAHybrid t len => AllocAHybrid t (f len)
    | NewStack fn => NewStack (f fn)
    | NewThread stack args => NewThread (f stack) (MAP f args)
    | NewThreadExn stack exn => NewThreadExn (f stack) (f exn)
    | NewFrameCursor stack => NewFrameCursor (f stack)
    | GetIref ref => GetIref (f ref)
    | GetFieldIref ref n => GetFieldIref (f ref) n
    | GetElementIref ref index => GetElementIref (f ref) (f index)
    | ShiftIref ref offset => ShiftIref (f ref) (f offset)
    | GetVarPartIref ref => GetVarPartIref (f ref)
`

val map_inst_def = Define`
  map_inst (f : α -> β) (inst : α instruction) : β instruction =
    case inst of
    | Assign v e => Assign (MAP f v) (map_expr f e)
    | Load v ptr src ord => Load (f v) ptr (f src) ord
    | Store v ptr dst ord => Store (f v) ptr (f dst) ord
    | CmpXchg v ptr weak sord ford loc exp des =>
        CmpXchg (f v) ptr weak sord ford (f loc) (f exp) (f des)
    | AtomicRMW v ptr ord op loc opnd =>
        AtomicRMW (f v) ptr ord op (f loc) (f opnd)
    | Fence ord => Fence ord
`

val map_terminst_def = Define`
  map_terminst (f : α -> β) (inst : α terminst) : β terminst =
    let map_dest : α destination -> β destination =
      λ(dst, args). dst,
        MAP (λarg.
          (case arg of
           | ExistingVar v => ExistingVar (f v)
           | CallReturnVal n => CallReturnVal n)
        ) args in
    let map_rd : α resumption_data -> β resumption_data =
      λrd. <|
         normal_dest := map_dest rd.normal_dest ;
         exceptional_dest := map_dest rd.exceptional_dest
       |> in
    case inst of
    | Return vals => Return (MAP f vals)
    | ThreadExit => ThreadExit
    | Throw vals => Throw (MAP f vals)
    | TailCall cd => TailCall (map_calldata f cd)
    | Branch1 dst => Branch1 (map_dest dst)
    | Branch2 cond dst1 dst2 =>
        Branch2 (f cond) (map_dest dst1) (map_dest dst2)
    | Watchpoint NONE rd => Watchpoint NONE (map_rd rd)
    | Watchpoint (SOME (id, dst)) rd =>
        Watchpoint (SOME (id, map_dest dst)) (map_rd rd)
    | WPBranch id dst1 dst2 => WPBranch id (map_dest dst1) (map_dest dst2)
    | Call cd rd => Call (map_calldata f cd) (map_rd rd)
    | Swapstack stack_id exc params rd =>
        Swapstack (f stack_id) exc (MAP f params) (map_rd rd)
    (* TODO: Implement map_terminst for Switch *)
    | ExnInstruction inst rd => ExnInstruction (map_inst f inst) (map_rd rd)
`

(* Dependency functions: return the dependencies (input variables) for a given
   expression, instruction, etc.
*)

val expr_dependencies_def = Define`
  expr_dependencies (expr : α expression) : α set =
    case expr of
    | Binop _ a b => {a; b}
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

val inst_dependencies_def = Define`
  inst_dependencies (inst : α instruction) : α set =
    case inst of
    | Assign _ e => expr_dependencies e
    | Load _ _ src _ => {src}
    | Store src _ _ _ => {src}
    | CmpXchg _ _ _ _ _ loc exp des => {loc; exp; des}
    | AtomicRMW _ _ _ _ loc opnd => {loc; opnd}
    | Fence _ => {}
`

(* A basic block (see the spec)
   https://github.com/microvm/microvm-spec/blob/master/uvm-ir.rest#function-body
*)
val _ = Datatype`
  bblock = <|
    args : (ssavar # uvm_type) list ;
    body : (operand instruction) list ;
    exit : (operand terminst) ;
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
  | Read  addr memreqid       memory_order memdeps
  | Write addr memreqid value memory_order memdeps
  | MMFence                   memory_order
`;

val memory_message_resolve_def = Datatype`
  memory_message_resolve =
  | ResolvedRead value memreqid`;

val _ = export_theory();
