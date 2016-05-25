open HolKernel Parse boolLib bossLib;

open uvmIRTheory
open errorMonadTheory
open lcsymtacs
open monadsyntax

val _ = new_theory "uvmThreadSemantics";

val _ = Datatype`
  fninfo = <|
    start_label : label ;
    blocks : block_label |-> bblock
  |>
`

val _ = Datatype`
  frame = <|
    fn : fnvname ;
    ssavars : ssavar |-> value option # memdeps
  |>`

val _ = Datatype`
  respt_arg =
  | RPVal value    (* values already computed in resumee's context *)
  | ResumerArg num (* index into values from resumer *)
`

val _ = type_abbrev(
  "resumption_point", ``:block_label # respt_arg list``)

val _ = type_abbrev(
  "respt_pair", ``:resumption_point # resumption_point option``)

val _ = type_abbrev("sus_frame", ``:frame # respt_pair``)

val _ = Datatype`
  thread_state = <|
    stack : sus_frame list ;
    curframe : frame ;
    curblock : block_label ;
    pc : num ;
    tid : tid ;
    memreq_map : num |-> ssavar ;
      (* maps load request ids to the ssa variable that is going to receive
         the value from memory *)
    addrwr_map : num |-> addr ;
    pending_insts : instruction set
  |>`

(* 
 * Gets the current basic block for a given state. Returns an error if the state
 * is malformed (has an invalid function and/or block name).
 *)
val current_block_def = Define`
  current_block (code : fnvname |-> fninfo) (state : thread_state) : bblock or_error =
    do
      current_fn <- expect (FLOOKUP code state.curframe.fn)
        ("no function named " ++ FST state.curframe.fn) ;
      expect (FLOOKUP current_fn.blocks state.curblock)
        ("no block named " ++ state.curblock)
    od
`

(* The set of pending SSA variables in a frame *)
val pending_vars_def = Define`
  pending_vars (f : frame) : ssavar set =
    {v | ∃val md. FLOOKUP f.ssavars v = SOME (SOME val, md)}
`

(* 
 * True if the instruction `i` is blocked (waiting on the value of some variable
 * it depends on) in the state `state`.
 *)
val is_blocked_def = Define`
  is_blocked (state : thread_state) (i : instruction) : bool ⇔
    DISJOINT (pending_vars state.curframe) (read_vars i)
`

(* 
 * True if the state's program counter is at (or after) the terminal instruction
 * of its current basic block. Returns an error if the state is malformed.
 *)
val at_block_end_def = Define`
  at_block_end (code : fnvname |-> fninfo) (state : thread_state) : bool or_error =
    do b <- current_block code state; return (LENGTH b.body ≤ state.pc) od
`

(* 
 * The current instruction at the state's program counter. Returns an error if
 * the state is malformed or the program counter has reached the end of the
 * block.
 *)
val current_inst_def = Define`
  current_inst (code : fnvname |-> fninfo) (state : thread_state) : instruction or_error =
    do
      at_end <- at_block_end code state ;
      block <- if at_end
                 then Error "no current instruction; program counter at end"
                 else current_block code state ;
      return (EL state.pc block.body)
    od
`

(*
 * Returns the value of an operand in a given state, or an error if the
 * operand's variable is not yet available.
 *)
val opnd_value_def = Define`
  opnd_value (state : thread_state) (x : operand) : (value # memdeps) or_error =
    case x of
    | SSAV_OP ssa => (
        case FLOOKUP state.curframe.ssavars ssa of
        | SOME (SOME v, m) => return (v, m)
        | SOME (NONE, _) => Error ("variable " ++ ssa ++ " not yet available")
        | NONE => Error ("variable " ++ ssa ++ " does not exist"))
    | CONST_OP v => return (v, {})
`

(*
 * Evaluates a binary operation, returning the values it produces. Returns an
 * error if the values `v1`, `v2` are incorrectly typed or if the binary
 * operation produces undefined behavior (such as division by zero).
 *)
val eval_bop_def = Define`
  eval_bop bop v1 v2 : (value list) or_error =
    case bop of
    | Add => 
        do v <- expect (value_add v1 v2) "type mismatch"; return [v] od
    | Sdiv =>
        do v <- expect (value_div v1 v2) "type mismatch"; return [v] od
`

(*
 * Evaluates an expression in a given state, returning the values it produces.
 * Returns an error if the expression is ill-typed or if it produces undefined
 * behavior (such as division by zero).
 *)
val eval_expr_def = Define`
  eval_expr (state : thread_state) (e : expression) : ((value list) # memdeps) or_error =
    case e of
    | Binop bop v1 v2 =>
        do
          (val1, dep1) <- opnd_value state v1 ;
          (val2, dep2) <- opnd_value state v2 ;
          v <- eval_bop bop val1 val2 ;
          return (v, dep1 UNION dep2)
        od
    | Value v => return ([v], {})
`


(* -----------------------------------------------------------------------------
 * TODO: CONTINUE HERE:
 *
 * Consider the following scenario: A loop that sums the contents of an array.
 *
 *     %sum(%array, %len, %i, %n):
 *       %ref    = GETELEMIREF %array %i
 *       %loaded = LOAD %ref
 *       %n2     = ADD %n %loaded
 *       %i2     = ADD %i @const_1
 *       %done   = GE %i %len
 *       BRANCH2 %done %exit(n) %sum(array, len, i2, n2)
 *
 * As this loop runs, it will build up a chain of dependencies, which will
 * contain repeated instances of each SSA variable. It seems like mapping SSA
 * variables to values is not enough. Perhaps a memreq should be generated for
 * every SSA variable?
 *
 * -----------------------------------------------------------------------------
 *)

val enqueue_inst_def = Define`
  enqueue_inst (state : thread_state) (inst : instruction) : thread_state or_error =
    
`

(*
 * Creates a new thread state in which a single variable has been assigned a new
 * value.
 *)
val bind_state_var_def = Define`
  bind_state_var (state : thread_state)
                 (var : ssavar)
                 (val : value option)
                 (deps : memdeps)
                 : thread_state or_error =
    state with 
    if LENGTH vars ≠ LENGTH values ∨ ¬ALL_DISTINCT vars then TSDIE
    else do
      ts0 <- TSGET ;
      TSASSERT (EVERY (λv. v ∉ FDOM ts0.curframe.ssavars) vars) ;
      TSSET (FOLDL (λts (var,value).
                      ts with curframe updated_by
                        (λcf.
                           cf with ssavars updated_by
                             (λfm. fm |+ (var, (SOME value,dep) ))))
                   ts0
                   (ZIP(vars,values)))
    od
`;

val exec_inst_def = Define`
  exec_inst (inst : instruction) (state : thread_state) : thread_state or_error =
    case inst of
    | Assign vtuple exp =>
        do
           values <- eval_exp exp ;
           valbind vtuple values
        od
    | Load destvar isiref srcvar morder =>
        do
           (av, depa) <- read_var srcvar ;
           a <- opt_lift (value_to_address av) ;
           TSLOAD destvar (a,depa) morder
        od
    | Store srcvar isiref destvar morder =>
        do
           (v,depv) <- read_var srcvar ;
           (av,depa) <- read_var destvar ;
           a <- opt_lift (value_to_address av) ;
           TSSTORE (v,depv) (a,depa) morder
        od
(*    | Fence morder =>
        do
            (λts. Success((),ts,[Fence morder]))
        od*)
     (*| AtomicRMW opr destloc srcvar isiref morder => *)
`

val (exec_rules, exec_ind, exec_cases) = Hol_reln`
  (∀ts0 ts1 i.
      i ∈ ts0.pending_insts ∧
      ¬is_blocked ts0 i ∧
      ts1 = exec_inst i (ts0 with pending_insts updated_by (DELETE) i)
    ⇒ exec code ts0 ts1) ∧

  (∀ts0 ts1.
      ¬at_block_end code ts0 ∧
      ts1 = ts0 with <|
              pc updated_by SUC ;
              pending_insts updated_by (INSERT) (current_inst code ts0) 
            |>
    ⇒ exec code ts0 ts1)
`

val paircase_eq = prove(
  ``(pair_CASE x f = y) ⇔ ∃a b. (x = (a,b)) ∧ (f a b = y)``,
  Cases_on `x` >> simp[]);

val exec_inst_def = Define`
  exec_inst inst : unit TSM =
    case inst of
    | Assign vtuple exp =>
        do
           values <- eval_exp exp ;
           valbind vtuple values
        od
    | Load destvar isiref srcvar morder =>
        do
           (av, depa) <- read_var srcvar ;
           a <- opt_lift (value_to_address av) ;
           TSLOAD destvar (a,depa) morder
        od
    | Store srcvar isiref destvar morder =>
        do
           (v,depv) <- read_var srcvar ;
           (av,depa) <- read_var destvar ;
           a <- opt_lift (value_to_address av) ;
           TSSTORE (v,depv) (a,depa) morder
        od
(*    | Fence morder =>
        do
            (λts. Success((),ts,[Fence morder]))
        od*)
     (*| AtomicRMW opr destloc srcvar isiref morder => *)
`

val thread_receive_def = Define`
  thread_receive ts ms =
    case ms of
    | ResolvedRead v mid =>
        let var = ts.memreq_map ' mid in
        let deps = SND ((ts.curframe.ssavars) ' var) in
        let cf = ts.curframe with ssavars updated_by (λvars. FUPDATE vars (var, (SOME v,deps))) in
        let ts1 = ts with curframe updated_by (λcfs. cf) in
        ts1
`;

(* Test:

load "uvmThreadSemanticsTheory";


Define`get_result (r:(unit # thread_state # memory_message list) tsstep_result) = case r of
    | Success (α,β,δ) => β
`


Define`ts = <| curframe :=
               <| ssavars := FEMPTY |+ ("a", (SOME (Int 32 8), {})) |> ;
               memreq_map := FEMPTY ; addrwr_map := FEMPTY
            |> `;

Define `ts2 = get_result ((exec_inst (Load "x" T "a" SEQ_CST)) ts)`;
 ``exec_inst (Assign ["x"] (Value (Int 32 2))) ts``;

Define`ts1 = get_result (exec_inst (Load "b" T "a" SEQ_CST) ts)`;
EVAL ``thread_receive ts1 (ResolvedRead (Int 32 8) 0)``;

type_of(``ResolvedRead (Int 8 2)``);

EVAL ``(do
        exec_inst (Assign ["a1"] (Value (Int32 2))) ;
        exec_inst (Assign ["a2"] (Value (Int32 8))) ;
        exec_inst (Load   "c" T "a1" SEQ_CST)       ;
        exec_inst (Store  "a1" T "a2" SEQ_CST)
       od ts)``;





Define`ts = <| curframe :=
               <| ssavars := FEMPTY |+ ("y", (SOME 1,{}) ) |+ ("z", (SOME 2,{}))
                                    |+ ("a", (SOME 1024,{}))
                                    |+ ("p", (NONE,{}) ) |> ;
               memreq_map := FEMPTY
            |> `;



EVAL ``exec_inst (Assign ["x"] (Binop Add "z" "y")) ts``;
EVAL ``exec_inst (Assign ["x"; "y"] (Binop Add "z" "y")) ts``;
EVAL ``exec_inst (Assign ["x"] (Binop Add "z" "u")) ts``;
EVAL ``exec_inst (Assign ["x"] (Binop Add "z" "p")) ts``;
EVAL ``do
        exec_inst (Load "x" T "a" SEQ_CST)
        exec_inst (Load "x'" T "a" SEQ_CST)
       od ts``;

EVAL ``exec_inst (Load "x" T "a" SEQ_CST) ts``;
EVAL ``exec_inst (Assign ["w"] (Binop Add "x" "y")) ts``;

EVAL ``exec_inst (Store "z" T "a" SEQ_CST) ts``;

Define `ts2 = get_result ((exec_inst (Load "x" T "a" SEQ_CST)) ts)`;
EVAL ``do
        exec_inst (Load "x" T "a" SEQ_CST) ;
        exec_inst (Load "a" T "a" SEQ_CST) ;
        exec_inst (Store "z" T "a" SEQ_CST)
       od ts``

EVAL ``ts2``;

*)


(*
val ts_step_def = Define`
  ts_step codemap (ts0 : thread_state) : tsstep_result =
    case FLOOKUP ts0.curframe.code ts0.curblock of
      NONE => Abort
    | SOME bb =>
      if ts0.pc > LENGTH bb.body then Abort
      else if ts0.pc = LENGTH bb.body then exec_terminst ts0 bb.exit
      else exec_inst ts0 (EL ts0.pc bb.body)
`;

*)

val _ = export_theory();
