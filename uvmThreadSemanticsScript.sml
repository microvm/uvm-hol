open HolKernel Parse boolLib bossLib;

open uvmIRTheory
open sumMonadTheory
open lcsymtacs
open monadsyntax

val _ = new_theory "uvmThreadSemantics"

val _ = reveal "C" (* The C (flip) combinator is used in this theory *)

val _ = type_abbrev("register", ``:ssavar # num``)

val _ = Datatype`
  thread_state = <|
    stack : suspended_frame list ;
    tid : tid ;
    registers : register |-> value ;
    memreq_map : memreqid |-> register list;
      (* maps load request ids to the ssa variable that is going to receive
         the value from memory *)
    addrwr_map : num |-> addr ;
    pending_insts : register instruction set ;
    mailbox : memory_response set ;
    next_register_index : num ;
    next_memreqid : memreqid
  |> ;

  running_thread = <|
    (* INL = thread is still executing code
       INR = thread is done executing, is waiting on return/exception values *)
    frame : running_frame + (resume_type # register or_const list) ;
    state : thread_state
  |> ;

  running_frame = <|
    fn : function ;
    block : register bblock ;
    pc : num ;
    register_index : num
  |> ;

  suspended_frame = <|
    fn : function ;
    normal_resume : register destination ;
    exceptional_resume : register destination option
  |> ;

  resume_type = NOR | EXC
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
    case thread.frame of
    | INL frame => LENGTH frame.block.body ≤ frame.pc
    | _ => T
`

(* The current instruction at the thread's program counter. Exit with an error
   if the program counter has reached the end of the block.
*)
val current_inst_def = Define`
  current_inst (thread : running_thread)
               : register instruction or_exit =
    if at_block_end thread
    then fail InvalidState "no current instruction; program counter at end"
    else let frame = OUTL thread.frame in return (EL frame.pc frame.block.body)
`

(* Returns the value of a variable or constant in a given state. Exits with an
   error if the variable is not yet available in the state.
*)
val get_value_def = Define`
  get_value (s : thread_state) (x : register or_const) : value or_exit =
    case x of
    | Var reg =>
        expect (FLOOKUP s.registers reg) InvalidState
          "register value not yet available"
    | Const v => return v
`

(* Evaluates a binary operation, returning the values it produces. Exits with an
   error if the values `v1`, `v2` are incorrectly typed or if the binary
   operation produces undefined behavior (such as division by zero).
*)
val eval_bop_def = Define`
  eval_bop bop v1 v2 : value list or_exit =
    case bop of
    | ADD => lift_left (C CONS []) (value_add v1 v2)
    | SDIV => lift_left (C CONS []) (value_div v1 v2)
`

(* Evaluates an expression in a given thread, returning the values it produces.
   Exits with an error if the expression is ill-typed or if it produces
   undefined behavior (such as division by zero).
*)
val eval_expr_def = Define`
  eval_expr (s : thread_state)
            (e : register or_const expression)
            : value list or_exit =
    case e of
    | Id _ v => lift_left (C CONS []) (get_value s v)
    | BinOp bop _ v1 v2 =>
        do
          v1' <- get_value s v1 ;
          v2' <- get_value s v2 ;
          eval_bop bop v1' v2'
        od
`

(* Generates a new running_thread state and an optional memory message by
   executing an instruction. Note that this does *not* advance the program
   counter, as it may represent the execution of a queued instruction.
*)
val exec_inst_def = Define`
  exec_inst (thread : running_thread)
            (inst : register instruction)
            : (running_thread # memory_message option) or_exit =
    case inst of
    | Assign regs expr =>
        do
          values <- eval_expr thread.state expr ;
          assert (LENGTH values = LENGTH regs)
            TypeMismatch "arity mismatch in Assign" ;
          assert (DISJOINT (set regs) (FDOM thread.state.registers))
            InvalidState "register being reused" ;
          return (
            thread with state updated_by
              (λs. s with registers updated_by C $|++ (ZIP (regs, values))),
            NONE)
        od
    | Load destvar is_iref _ src mem_order =>
        do
          iref <- get_value thread.state (Var src) ;
          a <- get_iref_addr iref ;
          return (
            thread with state updated_by
              (λs. s with <|
                memreq_map updated_by C FUPDATE (s.next_memreqid, [destvar]);
                next_memreqid updated_by SUC
              |>),
            SOME (MemLoad <|
              addr := a; id := thread.state.next_memreqid;
              order := mem_order;
              memdeps := {} (* TODO : needs filling in *)
            |>))
        od
    | Store srcvar is_iref _ destvar mem_order =>
        do
          src_value <- get_value thread.state srcvar ;
          dest_iref <- get_value thread.state (Var destvar) ;
          a <- get_iref_addr dest_iref ;
          return (
            thread with state updated_by
              (λs. s with next_memreqid updated_by SUC),
            SOME (MemStore <|
              addr := a; id := thread.state.next_memreqid;
              value := src_value; order := mem_order;
              memdeps := {} (* TODO : needs filling in *)
            |>))
        od
    | CmpXchg v1 v2 is_iref is_strong succ_order fail_order _ loc exp des =>
        do
          loc_iref <- get_value thread.state (Var loc) ;
          exp_value <- get_value thread.state exp ;
          des_value <- get_value thread.state des ;
          a <- get_iref_addr loc_iref ;
          return (
            thread with state updated_by
              (λs. s with <|
                memreq_map updated_by C FUPDATE (s.next_memreqid, [v1; v2]);
                next_memreqid updated_by SUC
              |>),
            SOME (MemCmpXchg <|
              addr := a; id := thread.state.next_memreqid;
              expected := exp_value; desired := des_value;
              success_order := succ_order; failure_order := fail_order;
              is_strong := is_strong;
              memdeps := {} (* TODO : needs filling in *)
            |>))
        od
    | AtomicRMW destvar is_iref mem_order op _ loc opnd =>
        do
          loc_iref <- get_value thread.state (Var loc) ;
          opnd_value <- get_value thread.state opnd ;
          a <- get_iref_addr loc_iref ;
          return (
            thread with state updated_by
              (λs. s with <|
                memreq_map updated_by C FUPDATE (s.next_memreqid, [destvar]);
                next_memreqid updated_by SUC
              |>),
            SOME (MemAtomicRMW <|
              addr := a; id := thread.state.next_memreqid;
              op := op; opnd := opnd_value; order := mem_order;
              memdeps := {} (* TODO : needs filling in *)
            |>))
        od
    | Fence mem_order => return (thread, SOME (MemFence mem_order {}))
        (* TODO : needs filling in *)
    (* TODO: NewThread, CommInst *)
`

(* Enters a new basic block in the given thread and function, with the given
   arguments, creating a `running_thread` record. Exits with an error if the
   block label refers to a nonexistent block, or if the wrong number of
   arguments is passed.
*)
val enter_block_def = Define`
  enter_block (state : thread_state)
              (fn : function)
              (label : block_label)
              (args : register or_const list)
              : running_thread or_exit =
    do
      (* 1. Look up the block that the label refers to. *)
      block <- expect (FLOOKUP fn.blocks label)
        InvalidState ("no block named " ++ label) ;

      assert (LENGTH args = LENGTH block.args)
        TypeMismatch "block arity mismatch" ;

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
      let new_pending : register instruction set =
        (* TODO: Something better than void for the type of the instruction.
                 If types are checked in future versions of this theory, then
                 something more sophisticated than pseudo-pending-instructions
                 will be needed to pass variables between blocks. *)
        FOLDR (λ((var, _), arg). $INSERT (Assign [var] (Id Void arg)))
              {}
              (ZIP (new_block.args, args)) in

      (* 4. Construct a new running_thread record for the new state. *)
      return <|
          frame := INL <|
            fn := fn ;
            block := new_block ;
            pc := 0 ;
            register_index := state.next_register_index
          |> ;
          state := state with <|
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
                 : running_thread or_exit =
    do
      fnname <- merge_right
          (λv. get_value state (Var v) >>= get_funcref_fnname)
          (lift_right return cd.name) ;
      version_opt <- expect (FLOOKUP env.func_versions fnname)
        InvalidState ("undeclared function: " ++ fnname) ;
      (* TODO: Trap on undefined functions *)
      version <- expect version_opt UndefinedBehavior "undefined function" ;
      fn <- expect (FLOOKUP env.functions version)
        InvalidState "missing function version" ;
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
                (res : resume_type)
                (return_vals : register or_const list)
                : running_thread or_exit =
    case state.stack of
    | [] => return <| frame := INR (res, return_vals) ; state := state |>
    | frame::stack_tail =>
        do
          (label, destargs) <-
            case res of
            | NOR => return frame.normal_resume
            | EXC => expect frame.exceptional_resume
                       InvalidState "no exceptional resumption point" ;
          args <- FOLDR (λdestarg args.
            do
              tl <- args ;
              hd <- merge_left
                (λn. assert (n < LENGTH return_vals)
                       InvalidState "return value index out of bounds"
                     >> return (EL n return_vals))
                (lift_left return destarg) ;
              return (hd :: tl)
            od) (Next []) destargs ;
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
                : running_thread or_exit =
    let no_returns : register destarg list -> register or_const list or_exit =
      FOLDR (λdestarg args.
        do
          tl <- args ;
          hd <- case destarg of
                | PassVar v => return v
                | _ => fail InvalidState "return value in non-CALL instruction" ;
          return (hd::tl)
        od) (Next []) in
    let get_frame : running_frame or_exit =
      lift_right
        (K (ExitError InvalidState "branch from terminated thread"))
        thread.frame in
    case inst of
    | Ret vals => resume_thread thread.state NOR vals
    | Throw vals => resume_thread thread.state EXC vals
    | Call cd rd =>
        get_frame >>= λframe.
        enter_function env (thread.state with stack updated_by (CONS <|
            fn := frame.fn ;
            normal_resume := rd.normal_dest ;
            exceptional_resume := SOME rd.exceptional_dest
          |>)) cd
    | TailCall cd => enter_function env thread.state cd
    | Branch1 (lbl, destargs) =>
        do
          frame <- get_frame ;
          args <- no_returns destargs ;
          enter_block thread.state frame.fn lbl args
        od
    | Branch2 cond (l1, destargs1) (l2, destargs2) =>
        (* TODO: Branch speculation *)
        do
          frame <- get_frame ;
          cond_value <- get_value thread.state cond ;
          cond_bool <- get_int1_as_bool cond_value ;
          args1 <- no_returns destargs1 ;
          args2 <- no_returns destargs2 ;
          if cond_bool
          then enter_block thread.state frame.fn l1 args1
          else enter_block thread.state frame.fn l2 args2
        od
    | Switch _ param def_dst branches =>
        (* TODO: Branch speculation *)
        do
          frame <- get_frame ;
          param_value <- get_value thread.state param ;
          (lbl, destargs) <- return (
            case FLOOKUP branches param_value of
            | SOME dst => dst
            | NONE => def_dst) ;
          args <- no_returns destargs ;
          enter_block thread.state frame.fn lbl args
        od
    (* TODO: Watchpoint, WPBranch, SwapStack, TermCommInst, ExcClause *)
`

val thread_receive_def = Define`
  thread_receive (state : thread_state)
                 ((mid, vs) : memory_response)
                 : thread_state or_exit =
    do
      vars <- expect (FLOOKUP state.memreq_map mid)
        InvalidState "invalid memreqid" ;
      assert (LENGTH vars = LENGTH vs)
        InvalidState "memory response arity mismatch" ;
      assert (DISJOINT (set vars) (FDOM state.registers))
        InvalidState "attempt to re-assign to SSA variable" ;
      return (state with registers updated_by C $|++ (ZIP (vars, vs)))
    od
`

(* Returns the appropriate exit state for a terminated thread with the given
   "resumption type" (normal or exceptional) and return/exception value(s).
*)
val thread_exit_def = Define`
  thread_exit (state : thread_state)
              (res : resume_type)
              (return_vals : register or_const list)
              : exit_state =
    merge_right (case res of NOR => ExitReturn | EXC => ExitThrow)
      (FOLDR (λv accum. do
        vs <- accum;
        v' <- get_value state v;
        return (v'::vs)
      od) (Next []) return_vals)
`

(* `nondet_step` is a relation of type

       environment ->
       running_thread ->
       (running_thread # memory_message option) or_exit set

   That is, given an environment and a current thread state, produce either a
   new thread state (possibly including an emitted memory message) or an exit
   state (error or return value(s)). Because this execution is nondeterministic,
   the return value is a set of possible next steps.
*)
val (nondet_step_rules, nondet_step_ind, nondet_step_cases) = Hol_reln`

    (* If a thread has pending instructions whose arguments are available,
       execute one of the instructions. *)
    (∀env thread thread' inst.
      inst ∈ thread.state.pending_insts
    ∧ is_ready thread.state inst
    ∧ thread' = thread with state updated_by
        (λs. s with pending_insts updated_by C $DELETE inst)
    ⇒
      nondet_step env thread (exec_inst thread' inst))

    (* If a thread's PC has not reached the end of its block, add the current
       instruction to the pending set, then advance the PC. *)
  ∧ (∀env thread thread' inst.
      ¬at_block_end thread
    ∧ Next inst = current_inst thread
    ∧ thread' = thread with <|
        frame updated_by lift_left λf. (f with pc updated_by SUC) ;
        state updated_by λs. (s with pending_insts updated_by $INSERT inst)
      |>
    ⇒
      nondet_step env thread (Next (thread', NONE)))

    (* If a thread's PC has reached the end of its block, and its terminal
       instruction's arguments are available, execute its terminal instruction.
    
       TODO: This is where branch speculation should be added. The only input
             variables a terminst can take are branch conditions (which can be
             guessed) or function refs (which should probably be waited on,
             though maybe those can be guessed too?).
    *)
  ∧ (∀env thread thread' frame.
      at_block_end thread
    ∧ INL frame = thread.frame
    ∧ terminst_input_vars frame.block.exit ⊆ FDOM thread.state.registers
    ∧ thread' = exec_terminst env thread frame.block.exit
    ⇒
      nondet_step env thread (thread' :> lift_left λt. (t, NONE)))

    (* If a thread's mailbox contains a memory response, add the contents of
       that response to the thread's registers. *)
  ∧ (∀env thread msg next_step.
      msg ∈ thread.state.mailbox
    ∧ next_step =
        lift_left
          (λs. (thread with state := (s with mailbox updated_by C $DELETE msg),
                NONE))
          (thread_receive thread.state msg)
    ⇒
      nondet_step env thread next_step)

    (* If a thread has terminated normally, and all of its return values are
       available, transition to a return exit state. *)
  ∧ (∀env thread exit_ty vs.
      INR (exit_ty, vs) = thread.frame
    ∧ (vs :> MAP left_set :> set :> BIGUNION) ⊆ FDOM thread.state.registers
    ⇒
      nondet_step env thread (Exit (thread_exit thread.state exit_ty vs)))
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

