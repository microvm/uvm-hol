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

(* Either a variable or a constant *)
val _ = type_abbrev("or_const", ``:α + value``)

val _ = Datatype`
  destarg =
  | PassVar α      (* i.e., something already in scope *)
  | PassConst value
  | PassReturnVal num  (* index to resumed value list - may not be any if, for
                          example, the statement is Return or Tailcall, but
                          if the statement is a call, the concrete syntax might
                          be something like

                              CALL m(...args...) EXC(%ndbl(%x, $2) %hbl($1, %a))
                       *)
`

val _ = type_abbrev("destination", ``:block_label # α destarg list``)

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
    methodname : α + fnname ;  (* allowing for indirect calls *)
    args : α or_const list ;
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

(* All instruction types are generic in their SSA variable type. For example, a
   `ssavar instruction` is a normal instruction (as per the spec), whereas a
   `num instruction` would use natural numbers to identify variables. The same
   applies to `expression`, `calldata`, etc.
*)

(* Type for expressions, instructions which do not contain a reference to their
   output variable(s). Note that the α type of an expression should allow for
   literal constants; that is, the expression type contained in an
   `α instruction` is an `(α or_const) expression`.
*)
val _ = Datatype`
  expression =
  | Id α
       (* no-op identity expr, yields its argument *)
  | BinOp bin_op α α
       (* performs arithmetic, yields a value *)
  | New uvm_type (* must not be hybrid *)
       (* yields a reference of type uvm_type *)
  | AllocA uvm_type (* must not be hybrid *)
       (* yields an iref to the type uvm_type *)
  | NewHybrid uvm_type  (* must be a hybrid type *)
              α (* length of varying part (can be zero);
                   will cause u.b., or raise exn if
                   GetVarPartIRef call is made on return value *)
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
  | GetIRef α (* ref *)
       (* yields corresponding iref *)
  | GetFieldIRef α (* iref / ptr *)
                 num  (* field index *)
       (* yields iref/ptr *)
  | GetElementIRef α (* iref / ptr to array type *)
                   α (* array index *)
       (* yields iref/ptr *)
  | ShiftIRef α (* iref/ptr to anything (not void) *)
              α (* offset *)
       (* yields iref/ptr *)
  | GetVarPartIRef α (* iref/ptr to hybrid *)
       (* yields iref/ptr to first element of var-part of hybrid IF IT EXISTS *)
`

(* Type for non-terminal instructions. Use `Assign` to create an
   `α instruction` from an `(α or_const) expression`.
*)
val _ = Datatype`
  instruction =
  | Assign (α list) (* destination variable(s) *)
           (α or_const expression) (*  *)
  | Load α (* destination variable  *)
         bool (* T for iref, F for ptr *)
         α (* source memory address *)
         memory_order
  | Store (α or_const) (* value to be written *)
          bool (* T for iref, F for ptr *)
          α (* destination memory address *)
          memory_order
  | CmpXchg α (* output: pair (oldvalue, boolean (T = success, F = failure)) *)
            bool (* T for iref, F for ptr *)
            bool (* T for strong, F for weak *)
            memory_order (* success order *)
            memory_order (* failure order *)
            α (* memory location *)
            (α or_const) (* expected value *)
            (α or_const) (* desired value *)
  | AtomicRMW α (* output: old memory value *)
              bool (* T for iref, F for ptr *)
              memory_order
              atomicrmw_op
              α (* memory location *)
              (α or_const) (* operand for op *)
  | Fence memory_order
`

val _ = type_abbrev("wpid", ``:num``)

val _ = Datatype`
  terminst =
  | Return (α or_const list)
  | ThreadExit
  | Throw (α or_const list)
  | TailCall (α calldata)
  | Branch1 (α destination)
  | Branch2 (α or_const) (α destination) (α destination)
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
      (α or_const list) (* parameters *)
      (α resumption_data)
  | Switch (α or_const) (α destination) (value |-> α destination)
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

(* Some extra sum type functions, for use with the or_const type. Because these
   are generic, they should probably be put in another file at some point.
*)

val map_left_def = Define`
  map_left (f : α -> β) (sum : α + γ) : β + γ =
    case sum of
    | INL a => INL (f a)
    | INR b => INR b
`

val map_right_def = Define`
  map_right (f : α -> β) (sum : γ + α) : γ + β =
    case sum of
    | INL a => INL a
    | INR b => INR (f b)
`

val left_set_def = Define`
  left_set (sum : α + β) : α set =
    case sum of
    | INL a => {a}
    | INR _ => {}
`

val right_set_def = Define`
  right_set (sum : α + β) : β set =
    case sum of
    | INL _ => {}
    | INR b => {b}
`

(* Map functions: map the SSA variables in expressions, instructions, etc. to
   new SSA variable types. Each maps from an `α foo` to a `β foo`.
*)

val map_calldata_def = Define`
  map_calldata (f : α -> β) (cd : α calldata) : β calldata = <|
      methodname := map_left f cd.methodname ;
      args := MAP (map_left f) cd.args ;
      convention := cd.convention
    |>
`

val map_expr_def = Define`
  map_expr (f : α -> β) (expr : α expression) : β expression =
    case expr of
    | Id v => Id (f v)
    | BinOp op a b => BinOp op (f a) (f b)
    | New t => New t
    | AllocA t => AllocA t
    | NewHybrid t len => NewHybrid t (f len)
    | AllocAHybrid t len => AllocAHybrid t (f len)
    | NewStack fn => NewStack (f fn)
    | NewThread stack args => NewThread (f stack) (MAP f args)
    | NewThreadExn stack exn => NewThreadExn (f stack) (f exn)
    | NewFrameCursor stack => NewFrameCursor (f stack)
    | GetIRef ref => GetIRef (f ref)
    | GetFieldIRef ref n => GetFieldIRef (f ref) n
    | GetElementIRef ref index => GetElementIRef (f ref) (f index)
    | ShiftIRef ref offset => ShiftIRef (f ref) (f offset)
    | GetVarPartIRef ref => GetVarPartIRef (f ref)
`

val map_inst_def = Define`
  map_inst (f : α -> β) (inst : α instruction) : β instruction =
    case inst of
    | Assign v e => Assign (MAP f v) (map_expr (map_left f) e)
    | Load v ptr src ord => Load (f v) ptr (f src) ord
    | Store src ptr dst ord => Store (map_left f src) ptr (f dst) ord
    | CmpXchg v ptr weak sord ford loc exp des =>
        CmpXchg (f v) ptr weak sord ford (f loc) (map_left f exp) (map_left f des)
    | AtomicRMW v ptr ord op loc opnd =>
        AtomicRMW (f v) ptr ord op (f loc) (map_left f opnd)
    | Fence ord => Fence ord
`

val map_terminst_def = Define`
  map_terminst (f : α -> β) (inst : α terminst) : β terminst =
    let map_dest : α destination -> β destination =
      λ(dst, args). dst,
        MAP (λarg. case arg of
                   | PassVar v => PassVar (f v)
                   | PassConst v => PassConst v
                   | PassReturnVal n => PassReturnVal n
            ) args in
    let map_rd : α resumption_data -> β resumption_data =
      λrd. <|
         normal_dest := map_dest rd.normal_dest ;
         exceptional_dest := map_dest rd.exceptional_dest
       |> in
    case inst of
    | Return vals => Return (MAP (map_left f) vals)
    | ThreadExit => ThreadExit
    | Throw vals => Throw (MAP (map_left f) vals)
    | TailCall cd => TailCall (map_calldata f cd)
    | Branch1 dst => Branch1 (map_dest dst)
    | Branch2 cond dst1 dst2 =>
        Branch2 (map_left f cond) (map_dest dst1) (map_dest dst2)
    | Watchpoint NONE rd => Watchpoint NONE (map_rd rd)
    | Watchpoint (SOME (id, dst)) rd =>
        Watchpoint (SOME (id, map_dest dst)) (map_rd rd)
    | WPBranch id dst1 dst2 => WPBranch id (map_dest dst1) (map_dest dst2)
    | Call cd rd => Call (map_calldata f cd) (map_rd rd)
    | Swapstack stack_id exc params rd =>
        Swapstack (f stack_id) exc (MAP (map_left f) params) (map_rd rd)
    (* TODO: Implement map_terminst for Switch *)
    | ExnInstruction inst rd => ExnInstruction (map_inst f inst) (map_rd rd)
`

(* Given an expression, returns a set of all variables read by the expression
   (its _input variables_).
*)
val expr_vars_def = Define`
  expr_vars (expr : α expression) : α set =
    case expr of
    | Id v => {v}
    | BinOp _ a b => {a; b}
    | New _ => {}
    | AllocA _ => {}
    | NewHybrid _ len => {len}
    | AllocAHybrid _ len => {len}
    | NewStack fn => {fn}
    | NewThread stack args => {stack} ∪ set args
    | NewThreadExn stack exn => {stack; exn}
    | NewFrameCursor stack => {stack}
    | GetIRef ref => {ref}
    | GetFieldIRef ref _ => {ref}
    | GetElementIRef ref index => {ref; index}
    | ShiftIRef ref offset => {ref; offset}
    | GetVarPartIRef ref => {ref}
`

(* Given an instruction, returns a pair of sets (input variables, output
   variables). The union of these sets is the set of all variables referenced
   by the instruction.
*)
val inst_vars_def = Define`
  inst_vars (inst : α instruction) : α set # α set =
    case inst of
    | Assign vs e => expr_vars e :> IMAGE left_set :> BIGUNION, set vs
    | Load v _ src _ => {src}, {v}
    | Store src _ dst _ => left_set src, {dst}
    | CmpXchg v _ _ _ _ loc exp des =>
        {loc} ∪ left_set exp ∪ left_set des, {v}
    | AtomicRMW v _ _ _ loc opnd => {loc} ∪ left_set opnd, {v}
    | Fence _ => {}, {}
`

val inst_input_vars_def = Define`inst_input_vars i = FST (inst_vars i)`

val inst_output_vars_def = Define`inst_output_vars i = SND (inst_vars i)`

val inst_all_vars_def = Define`inst_all_vars i = let (a, b) = inst_vars i in a ∪ b`

(* Given a terminal instruction, returns a pair of sets (input variables, passed
   variables). The union of these sets is the set of all variables referenced by
   the instruction.

   Note that "input variables" are variables whose values are required in order
   to determine the outcome of the instruction, whereas "passed variables" are
   variables whose values are passed to another block or function without being
   read.
*)
val terminst_vars_def = Define`
  terminst_vars (inst : α terminst) : α set # α set =
    let flat_left_set = λl. set l :> IMAGE left_set :> BIGUNION in
    let dest_vars : α destination -> α set =
      λ(_, args) v. MEM (PassVar v) args in
    let rd_vars : α resumption_data -> α set =
      λrd. dest_vars rd.normal_dest ∪ dest_vars rd.exceptional_dest in
    case inst of
    | Return vals => {}, flat_left_set vals
    | ThreadExit => {}, {}
    | Throw vals => {}, flat_left_set vals
    | TailCall cd => left_set cd.methodname, flat_left_set cd.args
    | Branch1 dst => {}, dest_vars dst
    | Branch2 cond dst1 dst2 => left_set cond, dest_vars dst1 ∪ dest_vars dst2
    | Watchpoint NONE rd => {}, rd_vars rd
    | Watchpoint (SOME (id, dst)) rd => {}, dest_vars dst ∪ rd_vars rd
    | WPBranch id dst1 dst2 => {}, dest_vars dst1 ∪ dest_vars dst2
    | Call cd rd => left_set cd.methodname, flat_left_set cd.args ∪ rd_vars rd
    | Swapstack stack_id exc params rd =>
        {stack_id}, flat_left_set params ∪ rd_vars rd
    | Switch param def_dst branches =>
        left_set param,
        dest_vars def_dst ∪ λvr. ∃vl. vr ∈ dest_vars (branches ' vl)
    | ExnInstruction inst rd => inst_input_vars inst, rd_vars rd
`

val terminst_input_vars_def = Define`terminst_input_vars i = FST (terminst_vars i)`

val terminst_passed_vars_def = Define`terminst_passed_vars i = SND (terminst_vars i)`

val terminst_all_vars_def = Define`terminst_all_vars i = let (a, b) = terminst_vars i in a ∪ b`

(* A basic block (see the spec)
   https://github.com/microvm/microvm-spec/blob/master/uvm-ir.rest#function-body
*)
val _ = Datatype`
  bblock = <|
    args : (α # uvm_type) list ;
    body : α instruction list ;
    exit : α terminst ;
    keepalives : α list
  |>
`

val _ = Datatype`
  declaration =
  | ConstDecl constname uvm_type value
  | TypeDef typename uvm_type
  | FunctionSignature signame uvm_type (uvm_type list)
  | FuncDef fnname signame label (block_label |-> ssavar bblock)
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
