open HolKernel Parse boolLib bossLib;

open uvmIRTheory
open lcsymtacs
open monadsyntax

val _ = new_theory "uvmThreadSemantics";
val _ = type_abbrev("tid", ``:num``)
val _ = type_abbrev("addr", ``:num``)  (* non-local memory addresses *)


val _ = Datatype`
  frame = <|
    function : fnname ;
    ssavars : SSAVar |-> value option ;
    code : block_label |-> bblock
  |>`

val _ = Datatype`
  respt_arg = RPVal value    (* values already computed in resumee's context *)
            | ResumerArg num (* index into values from resumer *)
`

val _ = type_abbrev(
  "resumption_point", ``:block_label # respt_arg list``)

val _ = type_abbrev(
  "respt_pair", ``:resumption_point # resumption_point option``)

val _ = type_abbrev("sus_frame", ``:frame # respt_pair``)


val _ = Datatype`
  threadState = <|
    stack : sus_frame list ;
    curframe : frame ;
    curblock : block_label ;
    offset : num ;
    tid : tid ;
    memreq_map : num |-> SSAVar
|>`

val _ = Datatype`
  memoryMessage = Read addr num (* memreq id *) memoryorder
                | Write addr value memoryorder
`;

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
  ``:threadState -> (α # threadState # memoryMessage list) tsstep_result``)

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
  TSLOAD (v : SSAVar) (a : addr) (m : memoryorder) : unit TSM =
    λts0.
      let reqnum = LEAST n. n ∉ FDOM ts0.memreq_map in
      let mesg = Read a reqnum m in
      let ts1 = ts0 with memreq_map updated_by (λrmap. rmap |+ (reqnum, v))
      in
        Success((), ts1, [mesg])
`

val TSSTORE_def = Define`
  TSSTORE (v : value) (a : addr) (m : memoryorder) : unit TSM =
    λts0.
       Success((), ts0, [Write a v m])
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
  TSGET : threadState TSM = λts. Success(ts, ts, [])
`

val readVar_def = Define`
  readVar (x : SSAVar) : value TSM =
    do
      ts <- TSGET ;
      case FLOOKUP ts.curframe.ssavars x of
          NONE => TSDIE
        | SOME NONE => TSBLOCKED
        | SOME (SOME v) => return v
    od
`

val evalbop_def = Define`
  evalbop bop v1 v2 : value list TSM =
   case bop of
     Add => return [v1 + v2]
   | Sdiv => if v2 ≠ 0 then return [v1 DIV v2] else TSDIE
`;

val eval_exp_def = Define`
  eval_exp (e : expression) : value list TSM =
      case e of
      | Binop bop v1 v2 =>
          do
            val1 <- readVar v1 ;
            val2 <- readVar v2 ;
            evalbop bop val1 val2
          od
`

val TSFUPD_def = Define`
  TSFUPD (f:threadState -> threadState) : unit TSM = λts. Success((), f ts, [])
`;

val _ = overload_on("TSSET", ``λts. TSFUPD (K ts)``)

val TSASSERT_def = Define`
  TSASSERT (P : bool) : unit TSM =
    λts. if P then Success((), ts, []) else Abort
`;

val valbind_def = Define`
  valbind vars values : unit TSM =
    if LENGTH vars ≠ LENGTH values ∨ ¬ALL_DISTINCT vars then TSDIE
    else do
      ts0 <- TSGET ;
      TSASSERT (EVERY (λv. v ∉ FDOM ts0.curframe.ssavars) vars) ;
      TSSET (FOLDL (λts (var,value).
                      ts with curframe updated_by
                        (λcf.
                           cf with ssavars updated_by
                             (λfm. fm |+ (var, SOME value))))
                   ts0
                   (ZIP(vars,values)))
    od
`;

val exec_inst_def = Define`
  exec_inst inst : unit TSM =
    case inst of
      Assign vtuple exp =>
        do
           values <- eval_exp exp ;
           valbind vtuple values
        od
    | Load destvar b srcvar morder =>
        do
           a <- readVar srcvar ;
           TSLOAD destvar a morder
        od
    | Store srcvar b destvar morder =>
        do
           v <- readVar srcvar ;
           a <- readVar destvar ;
           TSSTORE v a morder
        od
`

(* Test:

Define`ts = <| curframe :=
               <| ssavars := FEMPTY |+ ("y", SOME 1) |+ ("z", SOME 2)
                                    |+ ("a", SOME 1024)
                                    |+ ("p", NONE) |> ;
               memreq_map := FEMPTY
            |> `;

EVAL ``exec_inst (Assign ["x"] (Binop Add "z" "y")) ts``;
EVAL ``exec_inst (Assign ["x"; "y"] (Binop Add "z" "y")) ts``;
EVAL ``exec_inst (Assign ["x"] (Binop Add "z" "u")) ts``;
EVAL ``exec_inst (Assign ["x"] (Binop Add "z" "p")) ts``;
EVAL ``do
        exec_inst (Load "x" T "a" SEQ_CST) ;
        exec_inst (Load "x'" T "a" SEQ_CST)
       od ts``

EVAL ``exec_inst (Store "z" T "a" SEQ_CST) ts``;

EVAL ``do
        exec_inst (Load "x" T "a" SEQ_CST) ;
        exec_inst (Load "x'" T "a" SEQ_CST) ;
        exec_inst (Store "z" T "a" SEQ_CST)
       od ts``


*)


(*
val ts_step_def = Define`
  ts_step codemap (ts0 : threadState) : tsstep_result =
    case FLOOKUP ts0.curframe.code ts0.curblock of
      NONE => Abort
    | SOME bb =>
      if ts0.offset > LENGTH bb.body then Abort
      else if ts0.offset = LENGTH bb.body then exec_terminst ts0 bb.exit
      else exec_inst ts0 (EL ts0.offset bb.body)
`;

*)

val _ = export_theory();
