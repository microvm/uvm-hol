open HolKernel Parse boolLib bossLib;

open uvmIRTheory
open uvmErrorTheory
open sumMonadTheory
open lcsymtacs
open monadsyntax

val _ = new_theory "uvmThreadSemantics"

val _ = reveal "C" (* The C (flip) combinator is used in this theory *)

val _ = type_abbrev("register", ``:ssavar # num``)

val _ = Datatype`
  suspended_frame = <|
    fn : function ;
    normal_resume : register destination ;
    exceptional_resume : register destination option
  |>
`

val _ = Datatype`
  thread_state = <|
    stack : suspended_frame list ;
    tid : tid ;
    registers : register |-> value ;
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
    fn : function ;
    block : register bblock ;
    pc : num ;
    register_index : num ;
    state: thread_state
  |>
`

(* True if the instruction `i` is executable (all the variables it reads are
   defined) in the thread state `state`.
*)
val is_ready_def = Define`
  is_ready (state : thread_state) (i : register instruction) : bool ⇔
    inst_input_vars i ⊆ FDOM state.registers
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
      then state_error "no current instruction; program counter at end"
      else return (EL thread.pc thread.block.body)
`

(* Returns the value of a variable or constant in a given state, or an error if
   the variable is not yet available in the state.
*)
val get_value_def = Define`
  get_value (s : thread_state) (x : register or_const) : value or_error =
    case x of
    | Var reg =>
        expect (FLOOKUP s.registers reg) 
          (state_error "register value not yet available")
    | Const v => return v
`

(* Evaluates a binary operation, returning the values it produces. Returns an
   error if the values `v1`, `v2` are incorrectly typed or if the binary
   operation produces undefined behavior (such as division by zero).
*)
val eval_bop_def = Define`
  eval_bop bop v1 v2 : value list or_error =
    case bop of
    | ADD => lift_left (C CONS []) (value_add v1 v2)
    | SDIV => lift_left (C CONS []) (value_div v1 v2)
`

(* Evaluates an expression in a given thread, returning the values it produces.
   Returns an error if the expression is ill-typed or if it produces undefined
   behavior (such as division by zero).
*)
val eval_expr_def = Define`
  eval_expr (s : thread_state)
            (e : register or_const expression)
            : value list or_error =
    case e of
    | Id v => lift_left (C CONS []) (get_value s v)
    | BinOp bop v1 v2 =>
        do
          v1' <- get_value s v1 ;
          v2' <- get_value s v2 ;
          eval_bop bop v1' v2'
        od
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
          values <- eval_expr thread.state expr ;
          return (
            thread with state updated_by
              (λs. s with registers updated_by C $|++ (ZIP (regs, values))),
            NONE)
        od
    | Load destvar is_iref src mem_order =>
        do
          iref <- get_value thread.state (Var src) ;
          a <- get_iref_addr iref ;
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
          src_value <- get_value thread.state srcvar ;
          dest_iref <- get_value thread.state (Var destvar) ;
          a <- get_iref_addr dest_iref ;
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
          loc_iref <- get_value thread.state (Var loc) ;
          exp_value <- get_value thread.state exp ;
          des_value <- get_value thread.state des ;
          a <- get_iref_addr loc_iref ;
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
          loc_iref <- get_value thread.state (Var loc) ;
          opnd_value <- get_value thread.state opnd ;
          a <- get_iref_addr loc_iref ;
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

(* Enters a new basic block in the given thread and function, with the given
   arguments, creating a `running_thread` record. Returns an error if the block
   label refers to a nonexistent block, or if the wrong number of arguments is
   passed.
*)
val enter_block_def = Define`
  enter_block (state : thread_state)
              (fn : function)
              (label : block_label)
              (args : register or_const list)
              : running_thread or_error =
    do
      (* 1. Look up the block that the label refers to. *)
      block <- expect (FLOOKUP fn.blocks label) 
        (state_error ("no block named " ++ label));

      assert (LENGTH args = LENGTH block.args)
        (type_error "block arity mismatch");

      (* 2. Convert the block's SSA variables into registers. *)
      let new_block : register bblock =
        let reg = λv. (v, state.next_register_index) in
        <|
          args := MAP (reg ## I) block.args ;
          body := MAP (map_inst reg) block.body ;
          exit := map_terminst reg block.exit ;
          keepalives := MAP reg block.keepalives
        |> in

      (* 3. Add the resumption point arguments to the state. Constant values
            are inserted directly into thread.state.registers, while passed
            variables are converted into pending Assign instructions. *)
      let (new_registers, new_pending)
          : (register |-> value) # register instruction set =
        FOLDR (λ((var, _), arg).
          case arg of
          | Var var' => I ## $INSERT (Assign [var] (Id (Var var')))
          | Const val => C $|+ (var, val) ## I
        ) (FEMPTY, {}) (ZIP (new_block.args, args)) in

      (* 4. Construct a new running_thread record for the new state. *)
      return <|
          fn := fn ;
          block := new_block ;
          pc := 0 ;
          register_index := state.next_register_index ;
          state := state with <|
            registers updated_by (FUNION new_registers) ;
            pending_insts updated_by ($UNION new_pending) ;
            next_register_index updated_by SUC
          |>
        |>
    od
`

(* Given an environment and a thread state, creates a `running_thread` record
   for the beginning of the execution of a named function. Returns an error if
   the named function does not exist, or if the arguments are invalid.
*)
val enter_function_def = Define`
  enter_function (env : environment)
                 (state : thread_state)
                 (cd : register calldata)
                 : running_thread or_error =
    do
      fnname <- merge_right
          (λv. get_value state (Var v) >>= get_funcref_fnname)
          (lift_right return cd.name) ;
      version_opt <- expect (FLOOKUP env.func_versions fnname)
        (state_error ("undeclared function: " ++ fnname)) ;
      (* TODO: Trap on undefined functions *)
      version <- expect version_opt (undef_error "undefined function") ;
      fn <- expect (FLOOKUP env.functions version) 
        (state_error "missing function version") ;
      enter_block state fn fn.entry_block cd.args
    od
`

(* Resumes a suspended `thread_state`, converting it into a `running_thread`
   whose execution starts at the top frame of the suspended thread's stack.
   Returns an error if the suspended thread has an empty stack, or if its stack
   refers to a nonexistent bblock.
*)
val resume_thread_def = Define`
  resume_thread (state : thread_state)
                (normal : bool) (* F if handling an exception *)
                (return_vals : register or_const list)
                : running_thread or_error =
    do
      (frame, stack_tail) <-
        case state.stack of
        | next_sus_frame::rest => return (next_sus_frame, rest)
        | NIL => state_error "stack underflow" ;

      (label, destargs) <- 
        if normal
        then return frame.normal_resume
        else expect frame.exceptional_resume
               (state_error "no exceptional resumption point") ;

      args <- FOLDR (λdestarg args.
        do
          tl <- args ;
          hd <- merge_left
            (λn. assert (n < LENGTH return_vals)
                   (state_error "return value index out of bounds")
                 >> return (EL n return_vals))
            (lift_left return destarg) ;
          return (hd :: tl)
        od) (OK []) destargs ;

      enter_block (state with stack := stack_tail) frame.fn label args
    od
`

(* Executes a terminal instruction in a given environment and thread, returning
   a running_thread in a different block. Returns an error if something about
   the terminal instruction or the environment is invalid (e.g., an arity
   mismatch, or a nonexistent function or block).
*)
val exec_terminst_def = Define`
  exec_terminst (env : environment)
                (thread : running_thread)
                (inst : register terminst)
                : running_thread or_error =
    let no_returns : register destarg list -> register or_const list or_error =
      FOLDR (λdestarg args.
        do
          tl <- args ;
          hd <- case destarg of
                | PassVar v => return v
                | _ => state_error "return value in non-CALL instruction" ;
          return (hd::tl)
        od) (OK []) in
    case inst of
    | Return vals => resume_thread thread.state T vals
    | ThreadExit =>
        (* TODO: Return something more sensible than Error for ThreadExit *)
        undef_error "thread exited"
    | Throw vals => resume_thread thread.state F vals
    | TailCall cd => enter_function env thread.state cd
    | Branch1 (lbl, destargs) => 
        do
          args <- no_returns destargs ;
          enter_block thread.state thread.fn lbl args
        od
    | Branch2 cond (l1, destargs1) (l2, destargs2) =>
        (* TODO: Branch speculation *)
        do
          cond_value <- get_value thread.state cond ;
          cond_bool <- get_int1_as_bool cond_value ;
          args1 <- no_returns destargs1 ;
          args2 <- no_returns destargs2 ;
          if cond_bool
          then enter_block thread.state thread.fn l1 args1
          else enter_block thread.state thread.fn l2 args2
        od
    | Call cd rd =>
        enter_function env (thread.state with stack updated_by (CONS <|
            fn := thread.fn ;
            normal_resume := rd.normal_dest ;
            exceptional_resume := SOME rd.exceptional_dest
          |>)) cd
    | Switch param def_dst branches =>
        (* TODO: Branch speculation *)
        do
          param_value <- get_value thread.state param ;
          (lbl, destargs) <- return (
            case FLOOKUP branches param_value of
            | SOME dst => dst
            | NONE => def_dst) ;
          args <- no_returns destargs ;
          enter_block thread.state thread.fn lbl args
        od
    (* TODO: Watchpoint, WPBranch, Swapstack, ExnInstruction *)
`

val thread_receive_def = Define`
  thread_receive (state : thread_state)
                 (ms : memory_message_resolve)
                 : thread_state or_error =
    case ms of
    | ResolvedLoad v mid =>
        do
          var <- expect (FLOOKUP state.memreq_map mid)
                   (state_error "invalid memreqid") ;
          return (state with registers updated_by C FUPDATE (var, v))
        od
`

val (exec_rules, exec_ind, exec_cases) = Hol_reln`
  (∀thread inst.
      inst ∈ thread.state.pending_insts
      ∧ is_ready thread.state inst
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
      exec thread (lift_left
        (λs. (thread with state := (s with mailbox updated_by C $DELETE msg),
              NONE))
        (thread_receive thread.state msg)))

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

val _ = export_theory()

