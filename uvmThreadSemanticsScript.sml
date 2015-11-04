open HolKernel Parse boolLib bossLib;

open uvmIRTheory

val _ = new_theory "uvmThreadSemantics";
val _ = type_abbrev("tid", ``:num``)


val _ = Datatype`
  frame = <|
    function : funcid ;
    ssavars : SSAVar |-> value
  |>`

val _ = Datatype`
  resumption_point =
    BlockEntry block_label
  | BlockExit block_label
`

val _ = type_abbrev("sus_frame", ``:frame # resumption_point``)


val _ = Datatype`
  threadState = <|
    stack : sus_frame list ;
    curframe : frame ;
    pc : block_label # num ;
    tid : tid
|>

val _ = export_theory();
