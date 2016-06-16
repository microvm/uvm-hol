open HolKernel Parse boolLib bossLib;

open uvmTypesTheory;
open uvmValuesTheory;
open sumMonadTheory;

val _ = new_theory "uvmIR";

val _ = type_abbrev ("ssavar", ``:string``)
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
val _ = type_abbrev("signame", ``:string``)

(* Either a variable or a constant *)
val _ = type_abbrev("or_const", ``:σ + value``)
val _ = overload_on("Var", ``INL : σ -> σ or_const``)
val _ = overload_on("Const", ``INR : value -> σ or_const``)

(* Either a variable or a $-notation return value index

   $-notation is used for the destinations of CALL, to pass return values that
   don't get assigned SSA variables. e.g.,

       CALL m(...args...) EXC(%ndbl(%x, $2) %hbl($1, %a))
*)
val _ = type_abbrev("destarg", ``:σ or_const + num``)
val _ = overload_on("PassVar", ``INL : σ or_const -> σ destarg``)
val _ = overload_on("PassReturnVal", ``INR : num -> σ destarg``)

(* A block label with arguments *)
val _ = type_abbrev("destination", ``:block_label # σ destarg list``)

val _ = Datatype`
  resumption_data = <|
    normal_dest : σ destination ;
    exceptional_dest : σ destination
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
    name : σ + fnname ;  (* allowing for indirect calls *)
    args : σ or_const list ;
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

(* Type for expressions, instructions which do not contain a reference to their
   output variable(s).

   Note that the σ type of an expression should allow for literal constants;
   that is, the expression type contained in a `σ instruction` is a
   `σ or_const expression`.
*)
val _ = Datatype`
  expression =

  (* Basic Operations *)

  | Id (* no-op identity expr, yields its argument *)
      uvm_type  (* type of argument *)
      σ (* argument *)
  | BinOp (* performs arithmetic, yields a value *)
      bin_op (* operation to perform *)
      uvm_type  (* type of both operands *)
      σ (* op1 *)
      σ (* op2 *)
  | CmpOp (* performs a comparison, yields an int<1> (or a vector) *)
      cmp_op (* operation to perform *)
      uvm_type  (* type of both operands *)
      σ (* op1 *)
      σ (* op2 *)
  | ConvOp (* converts between two types *)
      convtype (* operation to perform *)
      uvm_type  (* source type *)
      uvm_type  (* destination type *)
      σ (* operand *)
  | Select (* Given a boolean (int<1>), select one of two values *)
      uvm_type  (* cond type *)
      uvm_type  (* ifTrue, ifFalse type *)
      σ (* cond *)
      σ (* ifTrue *)
      σ (* ifFalse *)

  (* Aggregate Type Operations *)

  | ExtractValue (* get field from struct in SSA var *)
      uvm_type  (* type of opnd, should be struct *)
      num  (* field index *)
      σ (* opnd - struct *)
  | InsertValue (* set field in struct in SSA var *)
      uvm_type  (* type of opnd, should be struct *)
      num  (* field index *)
      σ (* opnd - struct to insert into *)
      σ (* value to insert into struct *)
  | ExtractElement (* get element from array/vector in SSA var *)
      uvm_type  (* type of opnd, should be array/vector *)
      uvm_type  (* type of index, should be int *)
      σ (* opnd - array/vector *)
      σ (* index *)
  | InsertElement (* set element in array/vector in SSA var *)
      uvm_type  (* type of opnd, should be array/vector *)
      uvm_type  (* type of index, should be int *)
      σ (* opnd - array/vector *)
      σ (* index *)
      σ (* value to insert *)
  | ShuffleVector (* mix two vectors according to a mask *)
      uvm_type  (* type of opnd, should be vector *)
      uvm_type  (* type of mask, should be vector of any int type *)
      σ (* vec1 *)
      σ (* vec2 *)
      σ (* mask *)

  (* Memory Allocation *)

  | New (* heap allocate new object, yields ref *)
      uvm_type (* type - must not be hybrid *)
  | Alloca (* stack allocate new object, yields iref *)
      uvm_type
  | NewHybrid (* heap allocate new hybrid object, yields ref *)
      uvm_type  (* hybrid type *)
      uvm_type  (* length type *)
      σ (* length of varying part (can be zero);
              will cause u.b., or raise exn if
              GetVarPartIRef call is made on return value *)
  | AllocaHybrid (* stack allocate new hybrid object, yields iref *)
      uvm_type
      uvm_type
      σ

  (* Memory Addressing *)

  | GetIRef (* convert a ref into an iref *)
      uvm_type  (* referent type of opnd *)
      σ (* opnd, should be a ref *)
  | GetFieldIRef (* move iref to struct/hybrid field *)
      ref_type (* REF/PTR *)
      uvm_type  (* referent type of opnd - should be struct or hybrid *)
      num  (* field index *)
      σ (* opnd - iref/ptr *)
  | GetElementIRef (* move iref to array element *)
      ref_type (* REF/PTR *)
      uvm_type  (* referent type of opnd - should be array *)
      uvm_type  (* index type - should be int *)
      σ (* opnd - iref/ptr *)
      σ (* index *)
  | ShiftIRef (* move iref by specific offset, yields same iref type *)
      ref_type (* REF/PTR *)
      uvm_type  (* referent type of opnd *)
      uvm_type  (* offset type - should be int *)
      σ (* opnd - iref/ptr *)
      σ (* offset *)
  | GetVarPartIRef (* yields iref/ptr to first element of var-part of hybrid, if it exists *)
      ref_type (* REF/PTR *)
      uvm_type  (* referent type of opnd - should be hybrid *)
      σ (* opnd - iref/ptr *)
`

val _ = type_abbrev("wpid", ``:num``)

(* Types for instructions, both normal and terminal. Use `Assign` to create a
   `σ instruction` from a `σ or_const expression`.
*)
val _ = Datatype`
  instruction =
  | Assign 
      (σ list) (* output variable(s) *)
      (σ or_const expression)
  | Load
      σ (* destination variable  *)
      ref_type (* REF/PTR *)
      uvm_type  (* referent type of source *)
      σ (* source - iref/uptr *)
      memory_order
  | Store
      (σ or_const) (* value to be written *)
      ref_type (* REF/PTR *)
      uvm_type  (* referent type of destination *)
      σ (* destination - iref/uptr *)
      memory_order
  | CmpXchg
      σ (* output1 : oldvalue *)
      σ (* output2 : boolean for whether compare succeeded *)
      ref_type (* REF/PTR *)
      bool (* T for strong, F for weak *)
      memory_order (* success order *)
      memory_order (* failure order *)
      uvm_type  (* referent type of location *)
      σ (* memory location - iref/uptr *)
      (σ or_const) (* expected value *)
      (σ or_const) (* desired value *)
  | AtomicRMW
      σ (* output: old memory value *)
      ref_type (* REF/PTR *)
      memory_order
      atomicrmw_op
      uvm_type  (* referent type of location*)
      σ (* memory location - iref/uptr *)
      (σ or_const) (* operand for op *)
  | Fence memory_order
  | NewThread
      σ (* output: threadref *)
      (σ option) (* threadlocal *)
      (σ new_stack_clause)
  | CommInst
      (σ list) (* output variable(s) *)
      (σ comm_inst_args) ;

  terminst =
  | Ret (σ or_const list)
  | Throw (σ or_const list)
  | Call (σ calldata) (σ resumption_data)
  | TailCall (σ calldata)
  | Branch1 (σ destination)
  | Branch2 (σ or_const) (σ destination) (σ destination)
  | Switch
      uvm_type
      (σ or_const)
      (σ destination)
      (value |-> σ destination)
  | Watchpoint
      ((wpid # σ destination) option)
         (* NONE = unconditional trap *)
         (* SOME(wpid, dest) = conditional on wpid, trap if set;
                               if not, branch to dest *)
      (uvm_type list) (* return types *)
      (σ resumption_data)
  | WPBranch wpid (σ destination) (σ destination)
  | SwapStack
      σ (* swappee - stackref *)
      (σ new_stack_clause)
      cur_stack_clause
      (σ resumption_data)
  | TermCommInst
      (σ comm_inst_args)
      (σ resumption_data)
  | ExcClause
      (σ instruction)
      (σ resumption_data) ;

  (* Wrapping expressions with ExcClause forces the implementation to
     gracefully handle what would have otherwise been undefined
     behaviour. For example, an unwrapped division lets demons fly out
     of your nose if the second argument is 0. On the other hand, if the
     client wraps a division with resumption_data, the implementation
     must check for the zero argument and/or set up the appropriate
     signal handling so that the exceptional branch can get called when
     the second argument is indeed 0.
  *)

  comm_inst_args = <|
    inst : string ;
    flag_list : string list ;
    type_list : uvm_type list ;
    func_sig_list : signame list ;
    arg_list : σ list
  |> ;

  new_stack_clause =
  | PassValues ((σ # uvm_type) list)
  | ThrowExc σ ;

  cur_stack_clause =
  | RetWith (uvm_type list)
  | KillOld
`

(* Map functions: map the SSA variables in expressions, instructions, etc. to
   new SSA variable types. Each maps from an `α foo` to a `β foo`.
*)

val map_calldata_def = Define`
  map_calldata (f : α -> β) (cd : α calldata) : β calldata = <|
      name := lift_left f cd.name ;
      args := MAP (lift_left f) cd.args ;
      convention := cd.convention
    |>
`

val map_expr_def = Define`
  map_expr (f : α -> β) (expr : α expression) : β expression =
    case expr of
    | Id t v => Id t (f v)
    | BinOp op t a b => BinOp op t (f a) (f b)
    | CmpOp op t a b => CmpOp op t (f a) (f b)
    | ConvOp op t1 t2 x => ConvOp op t1 t2 (f x)
    | Select t1 t2 c a b => Select t1 t2 (f c) (f a) (f b)

    | ExtractValue t n s => ExtractValue t n (f s)
    | InsertValue t n s v => InsertValue t n (f s) (f v)
    | ExtractElement t1 t2 a i => ExtractElement t1 t2 (f a) (f i)
    | InsertElement t1 t2 a i v =>
        InsertElement t1 t2 (f a) (f i) (f v)
    | ShuffleVector t1 t2 v1 v2 m =>
        ShuffleVector t1 t2 (f v1) (f v2) (f m)

    | New t => New t
    | Alloca t => Alloca t
    | NewHybrid t1 t2 len => NewHybrid t1 t2 (f len)
    | AllocaHybrid t1 t2 len => AllocaHybrid t1 t2 (f len)

    | GetIRef t ref => GetIRef t (f ref)
    | GetFieldIRef p t n ref => GetFieldIRef p t n (f ref)
    | GetElementIRef p t1 t2 ref index =>
        GetElementIRef p t1 t2 (f ref) (f index)
    | ShiftIRef p t1 t2 ref offset =>
        ShiftIRef p t1 t2 (f ref) (f offset)
    | GetVarPartIRef p t ref => GetVarPartIRef p t (f ref)
`

val map_inst_def = Define`
  map_inst (f : α -> β) (inst : α instruction) : β instruction =
    case inst of
    | Assign vs e => Assign (MAP f vs) (map_expr (lift_left f) e)
    | Load v p t src ord => Load (f v) p t (f src) ord
    | Store src p t dst ord => Store (lift_left f src) p t (f dst) ord
    | CmpXchg v1 v2 p w sord ford t loc exp des =>
        CmpXchg (f v1) (f v2) p w sord ford t (f loc)
                (lift_left f exp) (lift_left f des)
    | AtomicRMW v p ord op t loc opnd =>
        AtomicRMW (f v) p ord op t (f loc) (lift_left f opnd)
    | Fence ord => Fence ord
    | NewThread v tl nsc =>
        NewThread (f v) (OPTION_MAP f tl) (
          case nsc of
          | PassValues vs => PassValues (MAP (f ## I) vs)
          | ThrowExc e => ThrowExc (f e))
    (* TODO: CommInst *)
`

val map_terminst_def = Define`
  map_terminst (f : α -> β) (inst : α terminst) : β terminst =
    let map_dest : α destination -> β destination =
      I ## (MAP o lift_left o lift_left) f in
    let map_rd : α resumption_data -> β resumption_data =
      λrd. <|
         normal_dest := map_dest rd.normal_dest ;
         exceptional_dest := map_dest rd.exceptional_dest
       |> in
    case inst of
    | Ret vals => Ret (MAP (lift_left f) vals)
    | Throw vals => Throw (MAP (lift_left f) vals)
    | Call cd rd => Call (map_calldata f cd) (map_rd rd)
    | TailCall cd => TailCall (map_calldata f cd)
    | Branch1 dst => Branch1 (map_dest dst)
    | Branch2 cond dst1 dst2 =>
        Branch2 (lift_left f cond) (map_dest dst1) (map_dest dst2)
    | Switch t cond dst branches =>
        Switch t (lift_left f cond) (map_dest dst) (map_dest o_f branches)
    | Watchpoint wpdst tys rd =>
        Watchpoint (OPTION_MAP (I ## map_dest) wpdst) tys (map_rd rd)
    | WPBranch id dst1 dst2 => WPBranch id (map_dest dst1) (map_dest dst2)
    | SwapStack v nsc csc rd =>
        SwapStack (f v) (
          case nsc of
          | PassValues vs => PassValues (MAP (f ## I) vs)
          | ThrowExc e => ThrowExc (f e)
        ) csc (map_rd rd)
    (* TODO: TermCommInst *)
    | ExcClause inst rd => ExcClause (map_inst f inst) (map_rd rd)
`

(* Given an expression, returns a set of all variables read by the expression
   (its _input variables_).
*)
val expr_vars_def = Define`
  expr_vars (expr : α expression) : α set =
    case expr of
    | Id _ v => {v}
    | BinOp _ _ a b => {a; b}
    | CmpOp _ _ a b => {a; b}
    | ConvOp _ _ _ v => {v}
    | Select _ _ c t f => {c; t; f}

    | ExtractValue _ _ s => {s}
    | InsertValue _ _ s v => {s; v}
    | ExtractElement _ _ a i => {a; i}
    | InsertElement _ _ a i v => {a; i; v}
    | ShuffleVector _ _ v1 v2 m => {v1; v2; m}

    | New _ => {}
    | Alloca _ => {}
    | NewHybrid _ _ len => {len}
    | AllocaHybrid _ _ len => {len}

    | GetIRef _ ref => {ref}
    | GetFieldIRef _ _ _ ref => {ref}
    | GetElementIRef _ _ _ ref index => {ref; index}
    | ShiftIRef _ _ _ ref offset => {ref; offset}
    | GetVarPartIRef _ _ ref => {ref}
`

(* Given an instruction, returns a pair of sets (input variables, output
   variables). The union of these sets is the set of all variables referenced
   by the instruction.
*)
val inst_vars_def = Define`
  inst_vars (inst : α instruction) : α set # α set =
    case inst of
    | Assign vs e => expr_vars e :> IMAGE left_set :> BIGUNION, set vs
    | Load v _ _ src _ => {src}, {v}
    | Store src _ _ dst _ => left_set src, {dst}
    | CmpXchg v1 v2 _ _ _ _ _ loc exp des =>
        {loc} ∪ left_set exp ∪ left_set des, {v1; v2}
    | AtomicRMW v _ _ _ _ loc opnd => {loc} ∪ left_set opnd, {v}
    | Fence _ => {}, {}
    | NewThread v tl nsc =>
      (case tl of SOME v' => {v'} | NONE => {}) ∪ (
        case nsc of
        | PassValues vs => set (MAP FST vs)
        | ThrowExc e => {e}
      ), {v}
    | CommInst vs ci => set ci.arg_list, set vs
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
      λ(_, args) v. MEM (PassVar (Var v)) args in
    let rd_vars : α resumption_data -> α set =
      λrd. dest_vars rd.normal_dest ∪ dest_vars rd.exceptional_dest in
    case inst of
    | Ret vals => {}, flat_left_set vals
    | Throw vals => {}, flat_left_set vals
    | Call cd rd => left_set cd.name, flat_left_set cd.args ∪ rd_vars rd
    | TailCall cd => left_set cd.name, flat_left_set cd.args
    | Branch1 dst => {}, dest_vars dst
    | Branch2 cond dst1 dst2 => left_set cond, dest_vars dst1 ∪ dest_vars dst2
    | Switch _ cond def_dst branches =>
        left_set cond,
        dest_vars def_dst ∪ λvr. ∃vl. vr ∈ dest_vars (branches ' vl)
    | Watchpoint NONE _ rd => {}, rd_vars rd
    | Watchpoint (SOME (id, dst)) _ rd => {}, dest_vars dst ∪ rd_vars rd
    | WPBranch id dst1 dst2 => {}, dest_vars dst1 ∪ dest_vars dst2
    | SwapStack stack_id nsc _ rd =>
        {stack_id}, (
          case nsc of
          | PassValues vs => set (MAP FST vs)
          | ThrowExc e => {e}
        ) ∪ rd_vars rd
    | ExcClause inst rd => inst_input_vars inst, rd_vars rd
`

val terminst_input_vars_def = Define`terminst_input_vars i = FST (terminst_vars i)`

val terminst_passed_vars_def = Define`terminst_passed_vars i = SND (terminst_vars i)`

val terminst_all_vars_def = Define`terminst_all_vars i = let (a, b) = terminst_vars i in a ∪ b`

(* A basic block (see the spec)
   https://github.com/microvm/microvm-spec/blob/master/uvm-ir.rest#function-body
*)
val _ = Datatype`
  bblock = <|
    args : (σ # uvm_type) list ;
    body : σ instruction list ;
    exit : σ terminst ;
    keepalives : σ list
  |>
`

val _ = Datatype`
  function = <|
    signature : signame ;
    entry_block : block_label ;
    blocks : block_label |-> ssavar bblock
  |>
`

val _ = Datatype`
  environment = <|
    constants : constname |-> (uvm_type # value) ;
    types : typename |-> uvm_type ;
    funcsigs : signame |-> uvm_type # uvm_type list ;
    func_versions : fnname |-> fnvname option ;
    functions : fnvname |-> function
  |>
`

val empty_env_def = Define`
  empty_env : environment = <|
    constants := FEMPTY ;
    types := FEMPTY ;
    funcsigs := FEMPTY ;
    func_versions := FEMPTY ;
    functions := FEMPTY
  |>
`

(* A bundle is simply a function that extends an environment. *)
val _ = type_abbrev("bundle", ``:environment -> environment``)

val _ = type_abbrev("tid", ``:num``)

val _ = type_abbrev("memreqid", ``:num``)
val _ = type_abbrev("memdeps", ``:memreqid set``)

(* `memory_message` is the type of memory mutation actions waiting to be
   performed. Because most of the messages have complicated argument lists,
   their arguments are defined as records.
*)
val _ = Datatype`
  memory_message =
  | MemLoad memory_message_load_args
  | MemStore memory_message_store_args
  | MemCmpXchg memory_message_cmp_xchg_args
  | MemAtomicRMW memory_message_atomic_rmw_args
  | MemFence memory_order memdeps ;

  memory_message_load_args = <|
    addr: addr ;
    id : memreqid ;
    order : memory_order ;
    memdeps : memdeps
  |> ;

  memory_message_store_args = <|
    addr: addr ;
    value : value ;
    id : memreqid ;
    order : memory_order ;
    memdeps : memdeps
  |> ;

  memory_message_cmp_xchg_args = <|
    addr : addr ;
    id : memreqid ;
    is_strong : bool ;
    success_order : memory_order ;
    failure_order : memory_order ;
    expected : value ;
    desired : value ;
    memdeps : memdeps
  |> ;

  memory_message_atomic_rmw_args = <|
    addr : addr ;
    id : memreqid ;
    order : memory_order ;
    op : atomicrmw_op ;
    opnd : value ;
    memdeps : memdeps
  |>
`

val _ = type_abbrev("memory_response", ``:memreqid # value list``)

val _ = export_theory()

