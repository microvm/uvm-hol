open HolKernel Parse boolLib bossLib;

open uvmIRTheory
open errorMonadTheory
open lcsymtacs
open monadsyntax

val _ = new_theory "uvmThreadSemantics"

val _ = reveal "C" (* The C (flip) combinator is used in this theory *)

val _ = type_abbrev("register", ``:ssavar # num``)

val _ = Datatype`
  fninfo = <|
    start_label : label ;
    blocks : block_label |-> ssavar bblock
  |>
`

val _ = Datatype`
  frame = <|
    fn : fninfo ;
    registers : register |-> value
  |>
`

val _ = type_abbrev(
  "resumption_point", ``:block_label # register or_const list``)

(* Normal and exceptional resumption points *)
val _ = type_abbrev(
  "respt_pair", ``:resumption_point # resumption_point option``)

val _ = type_abbrev("sus_frame", ``:frame # respt_pair``)

val _ = Datatype`
  thread_state = <|
    stack : sus_frame list ;
    tid : tid ;
    memreq_map : memreqid |-> register ;
      (* maps load request ids to the ssa variable that is going to receive
         the value from memory *)
    addrwr_map : num |-> addr ;
    pending_insts : register instruction set ;
    mailbox : memory_message_resolve set ;
    next_register_index : num ;
    next_memreqid : memreqid
  |>
`

val _ = Datatype`
  running_thread = <|
    frame : frame ;
    block : register bblock ;
    pc : num ;
    register_index : num ;
    state: thread_state
  |>
`

(* True if the instruction `i` is executable (all the variables it reads are
   defined) in the thread `thread`.
*)
val is_ready_def = Define`
  is_ready (thread : running_thread) (i : register instruction) : bool ⇔
    inst_input_vars i ⊆ FDOM thread.frame.registers
`

(* True if the thread's program counter is at (or after) the terminal instruction
   of its current basic block.
*)
val at_block_end_def = Define`
  at_block_end (thread : running_thread) : bool ⇔
    LENGTH thread.block.body ≤ thread.pc
`

(* The current instruction at the thread's program counter. Returns an error if
   the program counter has reached the end of the block.
*)
val current_inst_def = Define`
  current_inst (thread : running_thread) : register instruction or_error =
    if at_block_end thread
      then Error "no current instruction; program counter at end"
      else return (EL thread.pc thread.block.body)
`

(* Returns the value of a variable or constant in a given frame, or an error if
   the variable is not yet available in the frame.
*)
val get_value_def = Define`
  get_value (f : frame) (x : register or_const) : value or_error =
    case x of
    | INL reg =>
        expect (FLOOKUP f.registers reg) "register value not yet available"
    | INR v => return v
`

(* Evaluates a binary operation, returning the values it produces. Returns an
   error if the values `v1`, `v2` are incorrectly typed or if the binary
   operation produces undefined behavior (such as division by zero).
*)
val eval_bop_def = Define`
  eval_bop bop v1 v2 : value list or_error =
    case bop of
    | ADD => do v <- expect (value_add v1 v2) "type mismatch"; return [v] od
    | SDIV => do v <- expect (value_div v1 v2) "type mismatch"; return [v] od
`

(* Evaluates an expression in a given thread, returning the values it produces.
   Returns an error if the expression is ill-typed or if it produces undefined
   behavior (such as division by zero).
*)
val eval_expr_def = Define`
  eval_expr (f : frame) (e : register or_const expression) : value list or_error =
    case e of
    | Id v => do v' <- get_value f v; return [v'] od
    | BinOp bop v1 v2 =>
        do
          v1' <- get_value f v1 ;
          v2' <- get_value f v2 ;
          eval_bop bop v1' v2'
        od
`

(* Creates a new thread state in which a single register has been assigned a
   value.
*)
val bind_register_def = Define`
  bind_register : running_thread -> register # value -> running_thread =
    λt u. t with frame updated_by λf. f with registers updated_by C $|+ u
`

(* Generates a new running_thread state and a set of memory messages by
   executing an instruction. Note that this does *not* advance the program
   counter, as it may represent the execution of a queued instruction.
*)
val exec_inst_def = Define`
  exec_inst (thread : running_thread)
            (inst : register instruction)
            : (running_thread # memory_message option) or_error =
    case inst of
    | Assign regs expr =>
        do
          values <- eval_expr thread.frame expr ;
          return (FOLDL bind_register thread (ZIP (regs, values)), NONE)
        od
    | Load destvar is_iref src mem_order =>
        do
          iref <- get_value thread.frame (Var src) ;
          a <- expect (value_to_address iref) "invalid iref" ;
          return (
            thread with state updated_by
              (λs. s with <|
                memreq_map updated_by C FUPDATE (s.next_memreqid, destvar);
                next_memreqid updated_by SUC
              |>),
            SOME (MemLoad <|
              addr := a; id := thread.state.next_memreqid;
              order := mem_order; memdeps := {}
            |>))
        od
    | Store srcvar is_iref destvar mem_order =>
        do
          src_value <- get_value thread.frame srcvar ;
          dest_iref <- get_value thread.frame (Var destvar) ;
          a <- expect (value_to_address dest_iref) "invalid iref" ;
          return (
            thread with state updated_by
              (λs. s with next_memreqid updated_by SUC),
            SOME (MemStore <|
              addr := a; id := thread.state.next_memreqid;
              value := src_value; order := mem_order; memdeps := {}
            |>))
        od
    | CmpXchg v1 v2 is_iref is_strong success_order failure_order loc exp des =>
        do
          loc_iref <- get_value thread.frame (Var loc) ;
          exp_value <- get_value thread.frame exp ;
          des_value <- get_value thread.frame des ;
          a <- expect (value_to_address loc_iref) "invalid iref" ;
          return (
            thread with state updated_by
              (λs. s with <|
                memreq_map updated_by C $|++
                  [(s.next_memreqid, v1); (s.next_memreqid, v2)];
                next_memreqid updated_by SUC
              |>),
            SOME (MemCmpXchg <|
              addr := a; id := thread.state.next_memreqid;
              expected := exp_value; desired := des_value;
              success_order := success_order; failure_order := failure_order;
              is_strong := is_strong; memdeps := {}
            |>))
        od
    | AtomicRMW destvar is_iref mem_order op loc opnd =>
        do
          loc_iref <- get_value thread.frame (Var loc) ;
          opnd_value <- get_value thread.frame opnd ;
          a <- expect (value_to_address loc_iref) "invalid iref" ;
          return (
            thread with state updated_by
              (λs. s with <|
                memreq_map updated_by C FUPDATE (s.next_memreqid, destvar);
                next_memreqid updated_by SUC
              |>),
            SOME (MemAtomicRMW <|
              addr := a; id := thread.state.next_memreqid;
              op := op; opnd := opnd_value; order := mem_order; memdeps := {}
            |>))
        od
    | Fence mem_order => return (thread, SOME (MemFence mem_order))
`

(* Resumes a suspended `thread_state`, converting it into a `running_thread`
   whose execution starts at the top frame of the suspended thread's stack.
   Returns an error if the suspended thread has an empty stack, or if its stack
   refers to a nonexistent bblock.
*)
val resume_thread_def = Define`
  resume_thread (state : thread_state)
                (normal : bool) (* F if handling an exception *)
                : running_thread or_error =
    do
      (* 1. Pop the next frame off of the stack. *)
      ((fr, respts), stack) <-
        case state.stack of
        | next_sus_fr::rest => return (next_sus_fr, rest)
        | NIL => Error "stack underflow" ;

      (label, res_args) <- 
        if normal then return (FST respts)
                  else expect (SND respts) "no exceptional resumption point" ;

      (* 2. Look up the block that the frame refers to. *)
      block <- expect (FLOOKUP fr.fn.blocks label) ("no block named " ++ label);
      assert (LEN res_args = LEN block.args) "block arity mismatch" ;

      (* 3. Convert the block's SSA variables into registers. *)
      let new_block : register bblock =
        let reg = λv. (v, state.next_register_index) in
        <|
          args := MAP (reg ## I) block.args ;
          body := MAP (map_inst reg) block.body ;
          exit := map_terminst reg block.exit ;
          keepalives := MAP reg block.keepalives
        |> in

      (* 4. Add the resumption point arguments to the state. Constant values
            are inserted directly into thread.frame.registers, while passed
            variables are converted into pending Assign instructions.
      *)
      let (new_registers, new_pending)
          : (register |-> value) # register instruction set =
        FOLDR (λ((var, _), arg).
          case arg of
          | Var var' => I ## $INSERT (Assign [var] (Id (Var var')))
          | Const val => C $|+ (var, val) ## I
        ) (FEMPTY, {}) (ZIP (new_block.args, res_args)) in

      (* 5. Construct a new running_thread record for the new state. *)
      return <|
          frame := fr with registers updated_by (FUNION new_registers) ;
          block := new_block ;
          pc := 0 ;
          register_index := state.next_register_index ;
          state := state with <|
            stack := stack ;
            pending_insts updated_by $UNION new_pending;
            next_register_index updated_by SUC
          |>
        |>
    od
`

val thread_receive_def = Define`
  thread_receive (thread : running_thread)
                 (ms : memory_message_resolve)
                 : running_thread or_error =
    case ms of
    | ResolvedLoad v mid =>
        do
          var <- expect (FLOOKUP thread.state.memreq_map mid) "invalid memreqid" ;
          return (thread with frame updated_by λf.
            f with registers updated_by C FUPDATE (var, v))
        od
`;

val (exec_rules, exec_ind, exec_cases) = Hol_reln`
  (∀thread inst.
      inst ∈ ts0.state.pending_insts
      ∧ is_ready thread inst
    ⇒
      exec thread
           (exec_inst (thread with state updated_by λs.
                         s with pending_insts updated_by C $DELETE inst)
                      inst))

  ∧ (∀thread thread' inst.
      ¬at_block_end thread
      ∧ OK inst = current_inst thread
      ∧ thread' = thread with <|
          pc updated_by SUC ;
          state updated_by λs. (s with pending_insts updated_by $INSERT inst)
        |>
    ⇒
      exec thread (OK (thread', NONE)))

  ∧ (∀thread msg.
      msg ∈ thread.state.mailbox
    ⇒
      exec thread (map_error
        (λt. (t with state updated_by (λs.
                s with mailbox updated_by C $DELETE msg),
             NONE))
        (thread_receive thread msg)))

  (*
    add a rule to allow blocks to finish and transfer,
    including:
      - unconditional branch (tailcall)
      - tailcalls to other functions
      - calls
      - conditional branch (speculating through these will require
        addition of boolean context information to the frame(?) state
  *)
`

(*
exec_cases is of form:

  exec ts0 ts1 ⇔
     (∃i. i ∈ ts0.pending_insts ∧ .... ∧

          ts1 = OK (exec_inst i ....)) ∨

     (¬at_block_end ts0 ... /\ ts1 = ...) ∨


Then you can "evaluate" a concrete example by writing something like

   val th = ONCE_REWRITE_CONV [exec_cases] ``exec concrete_example tsresult``

this generates a theorem th of the form

   exec concrete_example tsresult ⇔
      clause1' ∨ clause2' ∨ ...

where each clausei' is a substitution instance of the original rules.

Then you need to simplify away clauses that don't apply.

  val th2 = SIMP_RULE (srw_ss()) [] th

will handle all the built-in constants nicely.  If you have constants with definitions that you want expanded, (foo_def, say), put those definitions/theorems into the list, i.e.

  val th2' = SIMP_RULE (srw_ss()) [foo_def] th

To get term corresponding to RHS of theorem, write

  val t2 = rhs (concl th2')

which will be a disjunction of possible clauses.

*)


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

val _ = export_theory();
