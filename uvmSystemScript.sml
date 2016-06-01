open HolKernel Parse boolLib bossLib;

open uvmMemoryModelTheory;
open uvmThreadSemanticsTheory;
open lcsymtacs
open monadsyntax
open uvmIRTheory;

val _ = new_theory "uvmSystem"; 


val machine_state_def = Datatype`
   machine_state = <|
     g : graph;
     threads : running_thread list
   |>
`;

val _ = Datatype`
  msstep_result = SuccessM α | AbortM | BlockedM
`

(* set up MSM, a monad *)
val _ = type_abbrev(
  "MSM",
  ``:machine_state -> (α # machine_state) msstep_result``)

val MSUNIT_def = Define`
  MSUNIT (x:α) :α MSM = λms. SuccessM (x, ms)
`;

val _ = overload_on ("return", ``MSUNIT``);

val MSBIND_def = Define`
  MSBIND (x : α MSM) (f : α -> β MSM) : β MSM =
    λms0.
      case x ms0 of
      | SuccessM (a, ms1) => (
          case f a ms1 of
          | SuccessM(b, ms2) => SuccessM(b, ms2)
          | r => r)
      | AbortM => AbortM
      | BlockedM => BlockedM
`;

val _ = overload_on ("monad_bind", ``MSBIND``)
val _ = overload_on ("monad_unitbind", ``λm1 m2. MSBIND m1 (K m2)``)


val MSGET_def = Define`
  MSGET : machine_state MSM = λms. SuccessM(ms, ms)
`

val read_var_def = Define`
  read_var (x : num) : (graph) MSM =
    do
      ms <- MSGET ;
      return ms.g
    od
`;

val eval_exp_def = Define`
  eval_exp (e:num) : (value # value) MSM =
    return ((Int 32 1), (Int 32 8))
`

val valbind_def = Define`
  valbind : unit MSM =
    do
      λms. SuccessM((), ms)
    od
`;

val find_node_fun_def = Define`
  find_node_fun list (n,tid) =
    case list of
    | [] => NONE
    | x::xs => if (x.mid = n ∧ x.thread_id = tid) then SOME x else find_node_fun xs (n,tid)
`;

val find_node_def = Define`
  find_node (n,tid) : (node option) MSM =
    do
      ms <- MSGET ;
      return (find_node_fun (ms.g.nodes) (n,tid))
    od
`;

val resolveM_def = Define`
  resolveM R W : memory_message_resolve MSM =
    λms. SuccessM(ResolvedLoad (THE W.values) R.mid, ms with g updated_by (λgr. gr with rf updated_by (λr. r|+(R,W))))
`;

val list_update_def = Define`
  list_update list index v =
    case list of
    | [] => []
    | x::xs => if (index=0) then (v::xs) else (x::(list_update xs (index-1) v))
`;

val thread_receiveM_def = Define`
  thread_receiveM msg tid : unit MSM =
    λms. SuccessM ((),  <| g := ms.g ; threads := list_update ms.threads tid (thread_receive (EL tid ms.threads) msg) |>)
`;


val get_result_def = Define`
  get_result (r:(unit # thread_state # memory_message list) tsstep_result) : (unit # thread_state # memory_message list) MSM =
    case r of
    | Success α => return α
`;

val run_inst_def = Define`
  run_inst inst t1 : (memory_message list) MSM = 
    do
      ms0 <- MSGET ;
      (a,ts1,msg) <- get_result (exec_inst inst (EL t1 ms0.threads)) ;
      λms. SuccessM ( msg, <| g:= ms.g ; threads := list_update ms.threads t1 ts1 |>)
    od
`;

type_of(``get_result(exec_inst inst (EL t1 ms.threads))``);
type_of(``SuccessM ( msg, <| g:= ms.g ; threads := list_update ms.threads t1 ts1 |>)``);

val receiveH_def = Define`
  receiveH inGraph (msg,ttid) =
    case msg of
    | MemLoad load =>
        let new_node = <|
              operation := Rd ;
              address := load.addr ; values := NONE    ;
              mid := load.id       ; thread_id := ttid ;
              order := load.order  ; ddeps := load.memdeps
            |>
        in inGraph with nodes updated_by (λlst. lst ++ [new_node])
    | MemStore store =>
        let new_node = <|
              operation := Wr ;
              address := load.addr ; values := SOME load.value ;
              mid := load.id       ; thread_id := ttid ;
              order := load.order  ; ddeps := load.memdeps
            |>
        in inGraph with nodes updated_by (λlst. lst ++ [new_node])
`;

val receive_list_def = Define`
  receive_list g (messages,tid) =
    case messages of
    | [] => g
    | m::rest => receive_list (receiveH g (m,tid)) (rest,tid)
`;

val receiveM_def = Define`
  receiveM messages tid : unit MSM =
    λms. SuccessM ((), <| g := receive_list ms.g (messages,tid) ; threads := ms.threads |>)
`;


val _ = Datatype`
  command =
  | read (memreqid # tid) (memreqid # tid)
  | eval (instruction # tid)
`;

val machine_step_def = Define`
  machine_step com : unit MSM =
    case com of
    | read (r,t1) (w,t2) =>
        do
          read  <- find_node (r,t1) ;
          write <- find_node (w,t2) ;
          msg <- resolveM (THE read) (THE write) ;
          thread_receiveM msg t1
        od
    | eval (inst, t1) =>
        do
          messages <- run_inst inst t1;
          receiveM messages t1
        od
`;

val _ = export_theory();

