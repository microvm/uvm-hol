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
  memoryMessage = Read addr num (* memreq id *) | Write addr value
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
  "TSM", ``:threadState -> (α # memoryMessage list) tsstep_result``)

val TSUNIT_def = Define`
  TSUNIT (x:α) :α TSM = λts. Success (x, [])
`;
val _ = overload_on ("return", ``TSUNIT``)

val TSBIND_def = Define`
  TSBIND (x : α TSM) (f : α -> β TSM) : β TSM =
    λts.
      case x ts of
      | Success (a, msgs1) =>
        (case f a ts of
         | Success(b, msgs2) => Success(b, msgs1 ++ msgs2)
         | r => r)
      | Abort => Abort
      | Blocked => Blocked
`;

val TSDIE_def = Define`TSDIE : α TSM = λts. Abort`
val TSBLOCKED_def = Define`TSBLOCKED : α TSM = λts. Blocked`

val TSBIND_DIEL = store_thm(
  "TSBIND_DIEL[simp]",
  ``TSBIND TSDIE f = TSDIE``,
  simp[FUN_EQ_THM, TSBIND_def, TSDIE_def]);

val TSBIND_UNITL = store_thm(
  "TSBIND_UNITL[simp]",
  ``TSBIND (TSUNIT x) f = f x``,
  dsimp[FUN_EQ_THM, TSBIND_def, TSUNIT_def, tsresult_case_eq, paircase_eq] >>
  csimp[] >> qx_gen_tac `ts` >> Cases_on `f x ts` >> simp[] >>
  qcase_tac `f x ts = Success a` >> Cases_on `a` >> simp[]);

val TSBIND_UNITR = store_thm(
  "TSBIND_UNITR[simp]",
  ``TSBIND tsm TSUNIT = tsm``,
  dsimp[FUN_EQ_THM, TSBIND_def, TSUNIT_def, tsresult_case_eq, paircase_eq] >>
  csimp[] >> qx_gen_tac `ts` >> Cases_on `tsm ts` >> simp[] >>
  qcase_tac `tsm ts = Success a` >> Cases_on `a` >> simp[]);

val TSGET_def = Define`
  TSGET : threadState TSM = λts. Success(ts, [])
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

val eval_exp_def = Define`
  eval_exp (e : expression) : (value list) TSM =
    let cf = ts.curframe in
      case e of
        Binop bop v1 v2 =>
          let val1 = THE (FAPPLY cf.ssavars v1) in
          let val2 = THE (FAPPLY cf.ssavars v2)
          in
            (case evalbop bop val1 val2 of
                NONE => Abort
              | SOME result => (result, []))
      | Load mtype destvar morder =>




'a memory_monad : memoryOp list -> ('a * memoryOp list) option

val exec_inst_def = Define`
  exec_inst ts0 inst =
    case inst of
      Assign vtuple exp =>
        if ¬expr_ready ts0 exp then Blocked
        else bind vtuple (eval_exp ts0 exp)
`

val ts_step_def = Define`
  ts_step codemap (ts0 : threadState) : tsstep_result =
    case FLOOKUP ts0.curframe.code ts0.curblock of
      NONE => Abort
    | SOME bb =>
      if ts0.offset > LENGTH bb.body then Abort
      else if ts0.offset = LENGTH bb.body then exec_terminst ts0 bb.exit
      else exec_inst ts0 (EL ts0.offset bb.body)
`;



val _ = export_theory();
