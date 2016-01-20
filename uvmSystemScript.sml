open HolKernel Parse boolLib bossLib;

open uvmMemoryModelTheory;
open uvmThreadSemanticsTheory;
open lcsymtacs
open monadsyntax
open uvmIRTheory;

val _ = new_theory "uvmSystem"; 


val machineState_def = Datatype`
    machineState = <| g : graph ;
                      tsList : threadState list |>`;

val _ = Datatype`
  msstep_result = SuccessM α | AbortM | BlockedM
`

(* set up MSM, a monad *)
val _ = type_abbrev(
  "MSM",
  ``:machineState -> (α # machineState) msstep_result``)

val MSUNIT_def = Define`
  MSUNIT (x:α) :α MSM = λms. SuccessM (x, ms)
`;

val _ = overload_on ("return", ``MSUNIT``);

val MSBIND_def = Define`
  MSBIND (x : α MSM) (f : α -> β MSM) : β MSM =
    λms0.
      case x ms0 of
      | SuccessM (a, ms1) =>
        (case f a ms1 of
         | SuccessM(b, ms2) => SuccessM(b, ms2)
         | r => r)
      | AbortM => AbortM
      | BlockedM => BlockedM
`;

val _ = overload_on ("monad_bind", ``MSBIND``)
val _ = overload_on ("monad_unitbind", ``λm1 m2. MSBIND m1 (K m2)``)


val MSGET_def = Define`
  MSGET : machineState MSM = λms. SuccessM(ms, ms)
`

val readVar_def = Define`
readVar (x : num) : (graph) MSM =
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

val findNodeFun_def = Define`
findNodeFun list (n,tid) = case list of
                               [] => NONE
                             | x::xs => if (x.mid = n ∧ x.thread_id = tid) then SOME x else findNodeFun xs (n,tid)`;
val findNode_def = Define`
findNode (n,tid) : (node option) MSM =
                               do
                                   ms <- MSGET ;
                                   return (findNodeFun (ms.g.nodes) (n,tid))
                               od
`;

val resolveM_def = Define`
    resolveM R W : memoryMessageResolve MSM =
      λms. SuccessM(ResolvedRead (THE W.values) R.mid, ms with g updated_by (λgr. gr with rf updated_by (λr. r|+(R,W) )   )    )`;

val listUpdate_def = Define`
    listUpdate list index v = case list of
        [] => []
      | x::xs => if(index=0)then(v::xs)else(x::(listUpdate xs (index-1) v))`;

val threadReceiveM_def = Define`
    threadReceiveM msg tid : unit MSM =
      λms. SuccessM (  (),  <| g:= ms.g ; tsList := listUpdate ms.tsList tid (threadReceive (EL tid ms.tsList) msg) |>)
`;


val getResult_def = Define`
    getResult (r:(unit # threadState # memoryMessage list) tsstep_result) : (unit # threadState # memoryMessage list) MSM = case r of
      | Success α => return α`;

val runInst_def = Define`
    runInst inst t1 : (memoryMessage list) MSM = 
      do
          ms0 <- MSGET ;
          (a,ts1,msg) <- getResult (exec_inst inst (EL t1 ms0.tsList)) ;
          λms. SuccessM ( msg, <| g:= ms.g ; tsList := listUpdate ms.tsList t1 ts1 |>)
      od`;

type_of(``getResult(exec_inst inst (EL t1 ms.tsList))``);
type_of(``SuccessM ( msg, <| g:= ms.g ; tsList := listUpdate ms.tsList t1 ts1 |>)``);

val receiveH_def = Define`
    receiveH inGraph (msg,ttid) = case msg of
        Read a' id order' dep => let new_node = <| operation := Rd ; address := a' ;
                                     values := NONE      ; mid := id ;
                                     thread_id := ttid   ; order := order' ;
                                     ddeps := dep |>
                                 in inGraph with nodes updated_by (λlst. lst ++ [new_node])
      | Write a' id vl order' dep => let new_node = <| operation := Wr ;
                                         address := a'   ; values := SOME vl ;
                                         mid := id       ; thread_id := ttid ;
                                         order := order' ; ddeps := dep |>
                                     in inGraph with nodes updated_by (λlst. lst ++ [new_node])  `;

val receiveList_def = Define`
    receiveList g (messages,tid) = case messages of
      | [] => g
      | m::rest => receiveList (receiveH g (m,tid)) (rest,tid)`;

val receiveM_def = Define`
    receiveM messages tid : unit MSM = λms. SuccessM ((), <| g := receiveList ms.g (messages,tid) ; tsList := ms.tsList |>)`;


val _ = Datatype` command = read (memreqid # tid) (memreqid # tid)
                          | eval (instruction # tid)`;

val machine_step_def = Define`
machine_step com : unit MSM =
      case com of
           read (r,t1) (w,t2) =>
             do
                 read  <- findNode (r,t1) ;
                 write <- findNode (w,t2) ;
                 msg <- resolveM (THE read) (THE write) ;
                 threadReceiveM msg t1
             od
         | eval (inst, t1) =>
             do
                 messages <- runInst inst t1;
                 receiveM messages t1
             od
`;



val _ = export_theory();
