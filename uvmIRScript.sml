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
val _ = type_abbrev("typename", ``:string``)
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

   Type variables:
   'ssa - SSA variable type
   'ty  - Type parameter type
   
   Note that the σ type of an expression should allow for literal constants;
   that is, the expression type contained in a `(σ, τ) instruction` is a
   `(σ or_const, τ) expression`.
*)
val _ = Datatype`
  expression =

  (* Basic Operations *)

  | Id (* no-op identity expr, yields its argument *)
      'ty  (* type of argument *)
      'ssa (* argument *)
  | BinOp (* performs arithmetic, yields a value *)
      bin_op (* operation to perform *)
      'ty  (* type of both operands *)
      'ssa (* op1 *)
      'ssa (* op2 *)
  | CmpOp (* performs a comparison, yields an int<1> (or a vector) *)
      cmp_op (* operation to perform *)
      'ty  (* type of both operands *)
      'ssa (* op1 *)
      'ssa (* op2 *)
  | ConvOp (* converts between two types *)
      convtype (* operation to perform *)
      'ty  (* source type *)
      'ty  (* destination type *)
      'ssa (* operand *)
  | Select (* Given a boolean (int<1>), select one of two values *)
      'ty  (* cond type *)
      'ty  (* ifTrue, ifFalse type *)
      'ssa (* cond *)
      'ssa (* ifTrue *)
      'ssa (* ifFalse *)

  (* Aggregate Type Operations *)

  | ExtractValue (* get field from struct in SSA var *)
      'ty  (* type of opnd, should be struct *)
      num  (* field index *)
      'ssa (* opnd - struct *)
  | InsertValue (* set field in struct in SSA var *)
      'ty  (* type of opnd, should be struct *)
      num  (* field index *)
      'ssa (* opnd - struct to insert into *)
      'ssa (* value to insert into struct *)
  | ExtractElement (* get element from array/vector in SSA var *)
      'ty  (* type of opnd, should be array/vector *)
      'ty  (* type of index, should be int *)
      'ssa (* opnd - array/vector *)
      'ssa (* index *)
  | InsertElement (* set element in array/vector in SSA var *)
      'ty  (* type of opnd, should be array/vector *)
      'ty  (* type of index, should be int *)
      'ssa (* opnd - array/vector *)
      'ssa (* index *)
      'ssa (* value to insert *)
  | ShuffleVector (* mix two vectors according to a mask *)
      'ty  (* type of opnd, should be vector *)
      'ty  (* type of mask, should be vector of any int type *)
      'ssa (* vec1 *)
      'ssa (* vec2 *)
      'ssa (* mask *)

  (* Memory Allocation *)

  | New (* heap allocate new object, yields ref *)
      'ty (* type - must not be hybrid *)
  | Alloca (* stack allocate new object, yields iref *)
      'ty
  | NewHybrid (* heap allocate new hybrid object, yields ref *)
      'ty  (* hybrid type *)
      'ty  (* length type *)
      'ssa (* length of varying part (can be zero);
              will cause u.b., or raise exn if
              GetVarPartIRef call is made on return value *)
  | AllocaHybrid (* stack allocate new hybrid object, yields iref *)
      'ty
      'ty
      'ssa

  (* Memory Addressing *)

  | GetIRef (* convert a ref into an iref *)
      'ty  (* referent type of opnd *)
      'ssa (* opnd, should be a ref *)
  | GetFieldIRef (* move iref to struct/hybrid field *)
      ref_type (* REF/PTR *)
      'ty  (* referent type of opnd - should be struct or hybrid *)
      num  (* field index *)
      'ssa (* opnd - iref/ptr *)
  | GetElementIRef (* move iref to array element *)
      ref_type (* REF/PTR *)
      'ty  (* referent type of opnd - should be array *)
      'ty  (* index type - should be int *)
      'ssa (* opnd - iref/ptr *)
      'ssa (* index *)
  | ShiftIRef (* move iref by specific offset, yields same iref type *)
      ref_type (* REF/PTR *)
      'ty  (* referent type of opnd *)
      'ty  (* offset type - should be int *)
      'ssa (* opnd - iref/ptr *)
      'ssa (* offset *)
  | GetVarPartIRef (* yields iref/ptr to first element of var-part of hybrid, if it exists *)
      ref_type (* REF/PTR *)
      'ty  (* referent type of opnd - should be hybrid *)
      'ssa (* opnd - iref/ptr *)
`

val _ = type_abbrev("wpid", ``:num``)

(* Types for instructions, both normal and terminal. Use `Assign` to create a
   `(σ, τ) instruction` from a `(σ or_const, τ) expression`.

   Type variables:
   'ssa - SSA variable type
   'ty  - Type parameter type
*)
val _ = Datatype`
  instruction =
  | Assign 
      ('ssa list) (* output variable(s) *)
      (('ssa or_const, 'ty) expression)
  | Load
      'ssa (* destination variable  *)
      ref_type (* REF/PTR *)
      'ty  (* referent type of source *)
      'ssa (* source - iref/uptr *)
      memory_order
  | Store
      ('ssa or_const) (* value to be written *)
      ref_type (* REF/PTR *)
      'ty  (* referent type of destination *)
      'ssa (* destination - iref/uptr *)
      memory_order
  | CmpXchg
      'ssa (* output1 : oldvalue *)
      'ssa (* output2 : boolean for whether compare succeeded *)
      ref_type (* REF/PTR *)
      bool (* T for strong, F for weak *)
      memory_order (* success order *)
      memory_order (* failure order *)
      'ty  (* referent type of location *)
      'ssa (* memory location - iref/uptr *)
      ('ssa or_const) (* expected value *)
      ('ssa or_const) (* desired value *)
  | AtomicRMW
      'ssa (* output: old memory value *)
      ref_type (* REF/PTR *)
      memory_order
      atomicrmw_op
      'ty  (* referent type of location*)
      'ssa (* memory location - iref/uptr *)
      ('ssa or_const) (* operand for op *)
  | Fence memory_order
  | NewThread
      'ssa (* output: threadref *)
      ('ssa option) (* threadlocal *)
      (('ssa, 'ty) new_stack_clause)
  | CommInst
      ('ssa list) (* output variable(s) *)
      (('ssa, 'ty) comm_inst_args) ;

  terminst =
  | Ret ('ssa or_const list)
  | Throw ('ssa or_const list)
  | Call ('ssa calldata) ('ssa resumption_data)
  | TailCall ('ssa calldata)
  | Branch1 ('ssa destination)
  | Branch2 ('ssa or_const) ('ssa destination) ('ssa destination)
  | Switch
      'ty
      ('ssa or_const)
      ('ssa destination)
      (value |-> 'ssa destination)
  | Watchpoint
      ((wpid # 'ssa destination) option)
         (* NONE = unconditional trap *)
         (* SOME(wpid, dest) = conditional on wpid, trap if set;
                               if not, branch to dest *)
      ('ty list) (* return types *)
      ('ssa resumption_data)
  | WPBranch wpid ('ssa destination) ('ssa destination)
  | SwapStack
      'ssa (* swappee - stackref *)
      (('ssa, 'ty) new_stack_clause)
      ('ty cur_stack_clause)
      ('ssa resumption_data)
  | TermCommInst
      (('ssa, 'ty) comm_inst_args)
      ('ssa resumption_data)
  | ExcClause
      (('ssa, 'ty) instruction)
      ('ssa resumption_data) ;

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
    type_list : 'ty list ;
    func_sig_list : signame list ;
    arg_list : 'ssa list
  |> ;

  new_stack_clause =
  | PassValues (('ssa # 'ty) list)
  | ThrowExc 'ssa ;

  cur_stack_clause =
  | RetWith ('ty list)
  | KillOld
`

(* Map functions: map the SSA variables in expressions, instructions, etc. to
   new SSA variable types. Each maps from an `(α, τ) foo` to a `(β, τ) foo`.
*)

val map_calldata_def = Define`
  map_calldata (f : α -> β) (cd : α calldata) : β calldata = <|
      name := lift_left f cd.name ;
      args := MAP (lift_left f) cd.args ;
      convention := cd.convention
    |>
`

val map_expr_def = Define`
  map_expr (vf : α -> β)
           (tf : γ -> δ)
           (expr : (α, γ) expression)
           : (β, δ) expression =
    case expr of
    | Id t v => Id (tf t) (vf v)
    | BinOp op t a b => BinOp op (tf t) (vf a) (vf b)
    | CmpOp op t a b => CmpOp op (tf t) (vf a) (vf b)
    | ConvOp op t1 t2 x => ConvOp op (tf t1) (tf t2) (vf x)
    | Select t1 t2 c a b => Select (tf t1) (tf t2) (vf c) (vf a) (vf b)

    | ExtractValue t n s => ExtractValue (tf t) n (vf s)
    | InsertValue t n s v => InsertValue (tf t) n (vf s) (vf v)
    | ExtractElement t1 t2 a i => ExtractElement (tf t1) (tf t2) (vf a) (vf i)
    | InsertElement t1 t2 a i v =>
        InsertElement (tf t1) (tf t2) (vf a) (vf i) (vf v)
    | ShuffleVector t1 t2 v1 v2 m =>
        ShuffleVector (tf t1) (tf t2) (vf v1) (vf v2) (vf m)

    | New t => New (tf t)
    | Alloca t => Alloca (tf t)
    | NewHybrid t1 t2 len => NewHybrid (tf t1) (tf t2) (vf len)
    | AllocaHybrid t1 t2 len => AllocaHybrid (tf t1) (tf t2) (vf len)

    | GetIRef t ref => GetIRef (tf t) (vf ref)
    | GetFieldIRef p t n ref => GetFieldIRef p (tf t) n (vf ref)
    | GetElementIRef p t1 t2 ref index =>
        GetElementIRef p (tf t1) (tf t2) (vf ref) (vf index)
    | ShiftIRef p t1 t2 ref offset =>
        ShiftIRef p (tf t1) (tf t2) (vf ref) (vf offset)
    | GetVarPartIRef p t ref => GetVarPartIRef p (tf t) (vf ref)
`

val map_inst_def = Define`
  map_inst (vf : α -> β)
           (tf : γ -> δ)
           (inst : (α, γ) instruction)
           : (β, δ) instruction =
    case inst of
    | Assign vs e => Assign (MAP vf vs) (map_expr (lift_left vf) tf e)
    | Load v p t src ord => Load (vf v) p (tf t) (vf src) ord
    | Store src p t dst ord => Store (lift_left vf src) p (tf t) (vf dst) ord
    | CmpXchg v1 v2 p w sord ford t loc exp des =>
        CmpXchg (vf v1) (vf v2) p w sord ford (tf t) (vf loc)
                (lift_left vf exp) (lift_left vf des)
    | AtomicRMW v p ord op t loc opnd =>
        AtomicRMW (vf v) p ord op (tf t) (vf loc) (lift_left vf opnd)
    | Fence ord => Fence ord
    | NewThread v tl nsc =>
        NewThread (vf v) (OPTION_MAP vf tl) (
          case nsc of
          | PassValues vs => PassValues (MAP (vf ## tf) vs)
          | ThrowExc e => ThrowExc (vf e))
    (* TODO: CommInst *)
`

val map_terminst_def = Define`
  map_terminst (vf : α -> β)
               (tf : γ -> δ)
               (inst : (α, γ) terminst)
               : (β, δ) terminst =
    let map_dest : α destination -> β destination =
      I ## (MAP o lift_left o lift_left) vf in
    let map_rd : α resumption_data -> β resumption_data =
      λrd. <|
         normal_dest := map_dest rd.normal_dest ;
         exceptional_dest := map_dest rd.exceptional_dest
       |> in
    case inst of
    | Ret vals => Ret (MAP (lift_left vf) vals)
    | Throw vals => Throw (MAP (lift_left vf) vals)
    | Call cd rd => Call (map_calldata vf cd) (map_rd rd)
    | TailCall cd => TailCall (map_calldata vf cd)
    | Branch1 dst => Branch1 (map_dest dst)
    | Branch2 cond dst1 dst2 =>
        Branch2 (lift_left vf cond) (map_dest dst1) (map_dest dst2)
    | Switch t cond dst branches =>
        Switch (tf t) (lift_left vf cond) (map_dest dst) (map_dest o_f branches)
    | Watchpoint wpdst tys rd =>
        Watchpoint (OPTION_MAP (I ## map_dest) wpdst) (MAP tf tys) (map_rd rd)
    | WPBranch id dst1 dst2 => WPBranch id (map_dest dst1) (map_dest dst2)
    | SwapStack v nsc csc rd =>
        SwapStack (vf v) (
          case nsc of
          | PassValues vs => PassValues (MAP (vf ## tf) vs)
          | ThrowExc e => ThrowExc (vf e)
        ) (
          case csc of
          | RetWith tys => RetWith (MAP tf tys)
          | KillOld => KillOld
        ) (map_rd rd)
    (* TODO: TermCommInst *)
    | ExcClause inst rd => ExcClause (map_inst vf tf inst) (map_rd rd)
`

(* Given an expression, returns a set of all variables read by the expression
   (its _input variables_).
*)
val expr_vars_def = Define`
  expr_vars (expr : (α, β) expression) : α set =
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
  inst_vars (inst : (α, β) instruction) : α set # α set =
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
  terminst_vars (inst : (α, β) terminst) : α set # α set =
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
    args : ('ssa # 'ty) list ;
    body : ('ssa, 'ty) instruction list ;
    exit : ('ssa, 'ty) terminst ;
    keepalives : 'ssa list
  |>
`

val _ = Datatype`
  function = <|
    signature : signame ;
    entry_block : block_label ;
    blocks : block_label |-> (ssavar, uvm_type) bblock
  |>
`

val _ = Datatype`
  declaration =
  | ConstDecl constname uvm_type value
  | TypeDef typename uvm_type
  | FunctionSignature signame uvm_type (uvm_type list)
  | FunctionDecl fnname signame
  | FunctionDef fnname function
`

val _ = type_abbrev("bundle", ``:declaration set``)

val _ = Datatype`
  environment = <|
    constants : constname |-> (uvm_type # value) ;
    types : typename |-> uvm_type ;
    funcsigs : signame |-> uvm_type # uvm_type list ;
    func_versions : fnname |-> fnvname option ;
    functions : fnvname |-> function
  |>
`

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

