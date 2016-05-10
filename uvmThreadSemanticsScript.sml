open HolKernel Parse boolLib bossLib;

open uvmIRTheory
open lcsymtacs
open monadsyntax

val _ = new_theory "uvmThreadSemantics";


val _ = Datatype`
  frame = <|
    function : fnname ;
    ssavars : ssavar |-> value option # memdeps;
    code : block_label |-> bblock
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
    offset : num ;
    tid : tid ;
    memreq_map : num |-> ssavar ;
    addrwr_map : num |-> addr
  |>`

val _ = Datatype`
  tsstep_result = Success α | Abort | Blocked
`

val tsresult_case_eq = prove_case_eq_thm {
  case_def = TypeBase.case_def_of ``:α tsstep_result``,
  nchotomy = TypeBase.nchotomy_of ``:α tsstep_result``
};

val paircase_eq = prove(
  ``(pair_CASE x f = y) ⇔ ∃a b. (x = (a,b)) ∧ (f a b = y)``,
  Cases_on `x` >> simp[]);

(* set up TSM, a monad *)
val _ = type_abbrev(
  "TSM",
  ``:thread_state -> (α # thread_state # memory_message list) tsstep_result``)

val TSUNIT_def = Define`
  TSUNIT (x:α) :α TSM = λts. Success (x, ts, [])
`;

val _ = overload_on ("return", ``TSUNIT``)

val TSBIND_def = Define`
  TSBIND (x : α TSM) (f : α -> β TSM) : β TSM =
    λts0.
      case x ts0 of
      | Success (a, ts1, msgs1) =>
        (case f a ts1 of
         | Success(b, ts2, msgs2) => Success(b, ts2, msgs1 ++ msgs2)
         | r => r)
      | Abort => Abort
      | Blocked => Blocked
`;

val TSLOAD_def = Define`
  TSLOAD (v : ssavar) (a : addr, depa : memdeps) (m : memoryorder) : unit TSM =
    λts0.
      let reqnum = LEAST n. n ∉ ((FDOM ts0.memreq_map) UNION (FDOM ts0.addrwr_map)) in
      let mesg = Read a reqnum m (depa UNION {reqnum}) in
      let ts1 = ts0 with memreq_map updated_by (λrmap. rmap |+ (reqnum, v)) in
      let ts2 = ts1 with curframe updated_by (λf. f with ssavars updated_by (λs. s |+ (v,(NONE,depa UNION {reqnum}))))
      in
        Success((), ts2, [mesg])
`

val TSSTORE_def = Define`
  TSSTORE (v : value, depv : memdeps) (a : addr, depa : memdeps) (m : memoryorder) : unit TSM =
    λts0.
      let reqnum = LEAST n. n ∉ ((FDOM ts0.memreq_map) UNION FDOM (ts0.addrwr_map)) in
      let mesg = Write a reqnum v m (depv UNION depa) in
      let ts1 = ts0 with addrwr_map updated_by (λrmap. rmap |+ (reqnum, a))
      in
        Success((), ts1, [mesg])
`;

val _ = overload_on ("monad_bind", ``TSBIND``)
val _ = overload_on ("monad_unitbind", ``λm1 m2. TSBIND m1 (K m2)``)

val TSDIE_def = Define`TSDIE : α TSM = λts. Abort`
val TSBLOCKED_def = Define`TSBLOCKED : α TSM = λts. Blocked`

(* Sanity theorems about the monad *)

val TSBIND_DIEL = store_thm(
  "TSBIND_DIEL[simp]",
  ``TSBIND TSDIE f = TSDIE``,
  simp[FUN_EQ_THM, TSBIND_def, TSDIE_def]);

val TSBIND_UNITL = store_thm(
  "TSBIND_UNITL[simp]",
  ``TSBIND (TSUNIT x) f = f x``,
  dsimp[FUN_EQ_THM, TSBIND_def, TSUNIT_def, tsresult_case_eq, paircase_eq] >>
  csimp[] >> qx_gen_tac `ts` >> Cases_on `f x ts` >> simp[] >>
  qcase_tac `f x ts = Success a` >> PairCases_on `a` >> simp[]);

val TSBIND_UNITR = store_thm(
  "TSBIND_UNITR[simp]",
  ``TSBIND tsm TSUNIT = tsm``,
  dsimp[FUN_EQ_THM, TSBIND_def, TSUNIT_def, tsresult_case_eq, paircase_eq] >>
  csimp[] >> qx_gen_tac `ts` >> Cases_on `tsm ts` >> simp[] >>
  qcase_tac `tsm ts = Success a` >> PairCases_on `a` >> simp[]);

val TSGET_def = Define`
  TSGET : thread_state TSM = λts. Success(ts, ts, [])
`

val read_var_def = Define`
  read_var (x : ssavar) : (value # memdeps) TSM =
    do
      ts <- TSGET;
      case FLOOKUP ts.curframe.ssavars x of
      | NONE => TSDIE
      | SOME (NONE,_) => TSBLOCKED
      | SOME ((SOME v,deps)) => return (v,deps)
    od
`

val get_value_of_def = Define`
  get_value_of (x : operand) : (value # memdeps) TSM =
    case x of
    | SSAV_OP ssa => read_var ssa
    | CONST_OP v => return (v, {})
`

val opt_lift_def = Define`
opt_lift NONE = TSDIE /\
opt_lift (SOME x) = return x`;

val evalbop_def = Define`
  evalbop bop v1 v2 : (value list) TSM =
    case bop of
    | Add => (do v <- opt_lift (value_add v1 v2) ; return [v] od)
    | Sdiv => (do v <- opt_lift (value_div v1 v2) ; return [v] od)
`;

val eval_exp_def = Define`
  eval_exp (e : expression) : ((value list) # memdeps) TSM =
    case e of
    | Binop bop v1 v2 =>
        do
          (val1, dep1) <- get_value_of v1 ;
          (val2, dep2) <- get_value_of v2 ;
          v <- evalbop bop val1 val2 ;
          return (v, dep1 UNION dep2)
        od
    | Value v => return ([v], {})
`

val TSFUPD_def = Define`
  TSFUPD (f:thread_state -> thread_state) : unit TSM = λts. Success((), f ts, [])
`;

val _ = overload_on("TSSET", ``λts. TSFUPD (K ts)``)

val TSASSERT_def = Define`
  TSASSERT (P : bool) : unit TSM =
    λts. if P then Success((), ts, []) else Abort
`;

val valbind_def = Define`
  valbind vars (values, dep) : unit TSM =
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
      if ts0.offset > LENGTH bb.body then Abort
      else if ts0.offset = LENGTH bb.body then exec_terminst ts0 bb.exit
      else exec_inst ts0 (EL ts0.offset bb.body)
`;

*)

val _ = export_theory();

