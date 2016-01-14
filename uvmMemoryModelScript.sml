open HolKernel Parse boolLib bossLib;

open uvmIRTheory;
open lcsymtacs;
open listTheory;

val _ = new_theory "uvmMemoryModel";


(* Datatypes and type abbreviations *)
val _ = type_abbrev("input", ``:(memoryMessage # tid)``);
val _ = Datatype` output_message = Out value memreqid tid `;
val _ = Datatype`ops = Rd | Wr | Fn `;
val _ = Datatype`
  node = <|
    operation : ops ;
    address   : addr ;
    values    : value option ;
    mid       : memreqid ;
    thread_id : tid ;
    order     : memoryorder ;
    ddeps     : memdeps
  |>`
val _ = Datatype`
  graph = <|
          nodes : node list ;
             rf : node |-> node
          |>`;


(* Term definitions *)
val isFence_def = Define`
    isFence n = (n.operation = Fn)`;

val isLoad_def = Define`
    isLoad n = (n.operation = Rd)`;

val isStore_def = Define`
    isStore n = (n.operation = Wr)`;

val isAcquire_def = Define`
    isAcquire n = case n.order of
        ACQUIRE => (n.operation = Rd) ∨ (n.operation = Fn)
      | ACQ_REL => (n.operation = Rd) ∨ (n.operation = Fn)
      | SEQ_CST => (n.operation = Rd) ∨ (n.operation = Fn)
      | CONSUME => (n.operation = Fn)
      | _       => F`;

val isConsume_def = Define`
    isConsume n = ((n.operation = Rd) ∧ (n.order <> NOT_ATOMIC) ∧ (n.order <> RELAXED)) (* or (n.order=CONSUME) *)`;

val isRelease_def = Define`
    isRelease n = case n.order of
        RELEASE => (n.operation = Wr) ∨ (n.operation = Fn)
      | ACQ_REL => (n.operation = Wr) ∨ (n.operation = Fn)
      | SEQ_CST => (n.operation = Wr) ∨ (n.operation = Fn)
      | _       => F`;

val isSeqCst_def = Define`
    isSeqCst n = (n.order = SEQ_CST)`;

val isAtomic_def = Define`
    isAtomic n = (n.order <> NOT_ATOMIC)`;

val sameThread_def = Define`
    sameThread A B = (A.thread_id = B.thread_id)`;

val sameAddress_def = Define`
    sameAddress A B = (A.address = B.address)`;

val isInGraph_def = Define`
    isInGraph g A = MEM A g.nodes`;






(* Undefined for missing items *)
val orderedBefore_def = Define`
    orderedBefore g A B = ((isInGraph g A) ∧ (isInGraph g B) ∧ (THE (INDEX_OF A g.nodes)) < (THE (INDEX_OF B g.nodes)))`;
    (*             of
                              (SOME a, SOME b) => (a < b)
                            | _ => (F)  `;*)

val isReadBy_def = Define`
    isReadBy g A B = (FLOOKUP g.rf B = SOME A)`;

val modifiesBefore_def = Define`
    modifiesBefore g A B = ( (orderedBefore g A B) ∧ (sameAddress A B) ∧ (isStore A) ∧ (isStore B))`;

val sequencedBefore_def = Define`
    sequencedBefore g A B = ((orderedBefore g A B) ∧ (sameThread A B)  )`;

val inReleaseSequenceOf_def = Define`
    inReleaseSequenceOf g B A = ( ((B = A) ∧ (isInGraph g A)) ∨ ((modifiesBefore g A B) ∧ (isAtomic B) ∧ (sequencedBefore g A B)))`;
val releaseSequenceOf_def = Define` (* TODO: include read-write ops *)
    releaseSequenceOf g A = { B | (B = A) ∨ ((modifiesBefore g A B) ∧ (isAtomic B) ∧ (isStore B) ∧ ((sequencedBefore g A B) ∨ (F) )  )}   `;

val carriesDependencyTo_def = Define`
    carriesDependencyTo g A B = ((A.mid IN B.ddeps) ∧ (isInGraph g A) ∧ (isInGraph g B))`;
(* This should be worked out within the thread? *)
(* val (cdep_rules, cdep_ind, cdep_cases) = Hol_reln` (* This might not be how reln is supposed to work *)
    (∀ g B A. (A.mid IN B.ddeps) ==> (carriesDependencyTo g B A)) ∧
    (∀ g B A. (∃ X. (sequencedBefore g A X) ∧ (sequencedBefore g X B) ∧ (isStore X) ∧ (isLoad B) ∧ (sameAddress X B) ∧ (A.mid IN X.ddeps)) ==> (carriesDependencyTo g B A)) ∧
    (∀ g B A. (∃ X. (carriesDependencyTo g A X) ∧ (carriesDependencyTo g X B)) ==> (carriesDependencyTo g B A) )`;*)

val synchronizesWith_def = Define`
    synchronizesWith g A B = (
        (*1.*) ( (isRelease A) ∧ (isAcquire B) ∧ (sameAddress A B) ∧ (∃ X. (isReadBy g X B ) ∧ (inReleaseSequenceOf g X A)) ) ∨
        (*2.*) ( (isRelease A) ∧ (isAcquire B) ∧ (isFence A) ∧ (isFence B) ∧ (∃ X Y. (isAtomic X) ∧ (isAtomic Y) ∧ (sameAddress X Y) ∧ (sequencedBefore g A X) ∧ (isStore X) ∧ (sequencedBefore g Y B) ∧ ( (isReadBy g X Y) ∨ (∃ Z. (isReadBy g Z Y) ∧ (inReleaseSequenceOf g Z X)))) ) ∨
        (*3.*) ( (isRelease A) ∧ (isAcquire B) ∧ (isFence A) ∧ (∃ X. (sequencedBefore g A X) ∧ (sameAddress B X) ∧ ((isReadBy g X B) ∨ (∃ Z. (isReadBy g Z B) ∧ (inReleaseSequenceOf g Z X))) ) ) ∨
        (*4.*) ( (isAtomic A) ∧ (isRelease A) ∧ (isAcquire B) ∧ (isFence B) ∧ (∃ X. (sameAddress A X) ∧ (sequencedBefore g X B) ∧ ((isReadBy g A X) ∨ (∃ Z. (isReadBy g Z X) ∧ (inReleaseSequenceOf g Z A))  ))  ) ∨ (* TODO *)
        (*5. A is the creation of a thread and B is the beginning of the execution of the new thread. *) (F) ∨
        (*6. A is a futex wake operation and B is the next operation after the futex wait operation of the thread woken up by A. *) (F)   )`;

val (dob_rules, dob_ind, dob_cases) = xHol_reln "dob" `
      (*1.*) (∀ g A B  . (isRelease A) ∧ (modifiesBefore g A B) ∧ ~(sameThread A B) ∧ (isConsume B) ∧ (∃ X. (inReleaseSequenceOf g X A) ∧ (isReadBy g X B) ) ==> dependencyOrderedBefore g A B  ) ∧
      (*2.*) (∀ g A B X. (dependencyOrderedBefore g A X) ∧ (carriesDependencyTo g X B) ==> dependencyOrderedBefore g A B)   `;

val (ithb_rules, ithb_ind, ithb_cases) = xHol_reln "ithb" `
    (* A.  *) ( ∀ g A B  . (synchronizesWith g A B) ==> (interthreadHappensBefore g A B)) ∧
    (* B.  *) ( ∀ g A B  . (dependencyOrderedBefore g A B) ==> (interthreadHappensBefore g A B)) ∧
    (* C.1 *) ( ∀ g A B X. ((synchronizesWith g A X) ∧ (sequencedBefore g X B)) ==> (interthreadHappensBefore g A B)) ∧
    (* C.2 *) ( ∀ g A B X. ((sequencedBefore g A X) ∧ (interthreadHappensBefore g X B)) ==> (interthreadHappensBefore g A B)) ∧
    (* C.3 *) ( ∀ g A B X. ((interthreadHappensBefore g A X) ∧ (interthreadHappensBefore g X B)) ==> (interthreadHappensBefore g A B)   )`;

val happensBefore_def = Define`
    happensBefore g A B = (
      (*1.*) (sequencedBefore g A B) ∨
      (*2.*) (interthreadHappensBefore g A B)   )`;

val visibleTo_def = Define`
    visibleTo g A B = ( (isStore A) ∧ (isLoad B) ∧
      (*1.*) (happensBefore g A B) ∧
      (*2.*) ~(∃ X. (happensBefore g A X) ∧ (happensBefore g X B))   )`;

(* TODO: fix to only look at writes and only return a set given a read *)
val inVisibleSequenceOf_def = Define` (* TODO: fix to only look at writes and only return a set given a read? *)
    inVisibleSequenceOf g A B =
      let visible_sequence X = { nd | (nd.address = X.address) ∧ (isStore nd) ∧ (isAtomic nd) ∧
                                      (      (visibleTo g nd X) ∨ (* The first in sequence *)
                                             (    ~(happensBefore g X nd) ∧
                                                   (∃fs. (visibleTo g fs X) ∧
                                                        (modifiesBefore g fs nd))))} (* the rest *)
      in A IN (visible_sequence B)    `;

val sequentiallyConsistent_def = Define`
    sequentiallyConsistent g A B = (isSeqCst A ∧ isSeqCst B ∧ orderedBefore g A B)`;

val seqCstException_def = Define`
    seqCstException g X B =
      let isMostRecentSeqCst n = ( (isInGraph g n) ∧
                                   (sequentiallyConsistent g n B) ∧ (sameAddress n B) ∧ ~(∃ Y.
                                   (sequentiallyConsistent g Y B) ∧ (sameAddress Y B) ∧ (sequentiallyConsistent g n Y)))
      in
         ( ∃ A. (isMostRecentSeqCst A ∧ ( (X = A) ∨ ( (inVisibleSequenceOf g X B) ∧ ~(isSeqCst X) ∧ ~(happensBefore g X A)))) ∨
          ~∃ A. (isMostRecentSeqCst A ∧ (inVisibleSequenceOf g X B) ∧ ~(isSeqCst X)))`;


val canBeReadBy_def = Define`
    canBeReadBy g B A = (
      (~(isAtomic A) ∧ ~(isAtomic B) ∧ (visibleTo g B A) ) ∨           (* non-atomic *)
      (~(isSeqCst B) ∧ (isAtomic A) ∧  (isAtomic B) ∧ (inVisibleSequenceOf g B A) ) ∨ (* atomic *)
      ( (isSeqCst B) ∧ (sequentiallyConsistent g B A)) ∨                    (* Sequentally Consistent *)
      ( F )                                                                       (* undefined combinations? *)  )`;





(*******************************************************************************)
(*                                                                             *)
(* Everything above is building up to these two relations, receive and resolve *)
(*                                                                             *)
(* The receive relation is for receiving a new memory operation message        *)
(* The resolve relation is for resolving a Write operation and returning a     *)
(* message                                                                     *)
(*                                                                             *)
(*******************************************************************************)

(* Receive input message, create new nodes from these messages *)
val receive_def = Define`
    receive (inGraph, (msg, ttid)) graph' = case msg of
      Read a' id order' dep => let new_node = <| operation := Rd ;
                                             address := a' ;
                                             values := NONE ;
                                             mid := id ;
                                             thread_id := ttid ;
                                             order := order' ;
                                             ddeps := dep |>
                           in (graph' = inGraph with nodes updated_by (λlst. lst ++ [new_node] ))

    | Write a' id vl order' dep => let new_node = <| operation := Wr ;
                                              address := a' ;
                                              values := SOME vl ;
                                              (* mid := LEAST n. ~(∃ nd. (nd.mid = n) ∧ (nd IN inGraph.nodes) ) ;*)
                                              mid := id;
                                              thread_id := ttid ;
                                              order := order' ;
                                              ddeps := dep |>
                           in (graph' = inGraph with nodes updated_by (λlst. lst ++ [new_node]))
`;

(* TODO: output message *)
val resolve_def = Define`
    resolve g1 (msg, g2) = ∃ w r. (g1.nodes = g2.nodes) ∧ (* TODO: maybe update r's value? *)
                                  (canBeReadBy g1 w r) ∧ (g2.rf = g1.rf |+ (r, w)) ∧
                                  (~∃ w'. FLOOKUP g1.rf r = SOME w') ∧
                                  (msg = Out (THE w.values) (r.mid) (r.thread_id))
`;




(***********************************)
(* Defined and Undefined Behaviour *)
(***********************************)
val dataRace_def = Define`
    dataRace g A B = (
       (isInGraph g A)               ∧
       (isInGraph g B)               ∧
       (sameAddress A B)             ∧
       ( (isStore A) ∨ (isStore B) ) ∧
      ~(happensBefore g A B)         ∧
      ~(happensBefore g B A)
 )`;

val indeterminate_read_def = Define`
    indeterminate_read g A = ~∃ B. canBeReadBy g B A`;

val consistent_sc_order_def = Define`
    consistent_sc_order g = ∀ A B.
        (isSeqCst A ∧ isSeqCst B) ==> ((happensBefore g A B ==> sequentiallyConsistent g A B) ∧
                                       (modifiesBefore g A B ==> sequentiallyConsistent g A B))`;

val consistent_reads_from_mapping_def = Define`
    consistent_reads_from_mapping g = ∀ A B. isReadBy g A B ==> (canBeReadBy g A B ∧ isInGraph g A ∧ isInGraph g B)`;

val consistent_ithb_def = Define`
    consistent_ithb g = ∀ A. ~interthreadHappensBefore g A A`;

val consistent_modification_order_def = Define`
    consistent_modification_order g = ∀ A B.
        ( (isAtomic A ∧ isAtomic B) ==> (happensBefore g A B ==> modifiesBefore g A B)) ∧
        (~(isAtomic A ∧ isAtomic B) ==> ~modifiesBefore g A B)`;

(* Coherence *)
val CoRR_def = Define`
    CoRR g = ~∃ A B C D. (happensBefore g C D ∧ isReadBy g A C ∧ isReadBy g B D ∧ modifiesBefore g B A)`;

val CoWR_def = Define`
    CoWR g = ~∃ B C D. (isReadBy g B D ∧ happensBefore g C D ∧ modifiesBefore g B C)`;

val CoWW_def = Define`
    CoWW g = ~∃ A B. happensBefore g A B ∧ modifiesBefore g B A`;

val CoRW_def = Define`
    CoRW g = let rhm = ($RUNION ( $RUNION (isReadBy g) (happensBefore g)) (modifiesBefore g))
              in (~∃ A. rhm^* A A)`;          

val wellFormed_def = Define`
    wellFormed g = consistent_reads_from_mapping g`;

val consistent_execution_def = Define`
    consistent g = (
        consistent_ithb g ∧
        consistent_sc_order g ∧                                    
        consistent_modification_order g ∧
        consistent_reads_from_mapping g ∧
        (* No dataraces *)
        (~∃ A B. dataRace g A B) ∧
        (* No indeterminate reads *)
        (~∃ A. indeterminate_read g A)
)`;




(*************************************************************)
(* Proofs for some properties of the relations defined above *)
(*************************************************************)

val impliesOB_def = Define`
    impliesOrderedBefore p = ∀ g A B. (wellFormed g ∧ p g A B ==> orderedBefore g A B)`;
val trans_def = Define`
    transitive p = ∀ A B C. p A B ∧ p B C ==> p A C`;
val asym_def = Define`
    assymetric p = ∀ A B. p A B ==> ~p B A`;
val irrefl_def = Define`
    irreflexive p = ∀ A. ~p A A`;
val impliesInGraph_def = Define`
    impliesInGraph p = ∀ g A B. (wellFormed g ∧ p g A B) ==> (isInGraph g A ∧ isInGraph g B)`;



(* orderedBefore *)
val orderedBefore_irreflexivity = prove(
    ``∀ g. irreflexive (orderedBefore g)``,
        rw [irrefl_def, orderedBefore_def]);
val orderedBefore_asymmetry = prove(
    ``∀ g. assymetric (orderedBefore g)``,
        RW_TAC arith_ss [asym_def,orderedBefore_def]);
val orderedBefore_transitivity = prove(
    ``∀g. transitive (orderedBefore g)``,
        RW_TAC arith_ss [trans_def,orderedBefore_def]);
(* If something implies orderedBefore then it is also irreflexive and assymetrical *)
val orderedBefore_inGraph = prove(
    ``impliesInGraph orderedBefore``, rw [impliesInGraph_def, orderedBefore_def]);

val isReadBy_inGraph = prove(
    ``impliesInGraph isReadBy``, prove_tac [impliesInGraph_def, consistent_reads_from_mapping_def,wellFormed_def]);

(* modifiesBefore *)
val modifiesBefore_orderedBefore = prove(
    ``∀ g A B. modifiesBefore g A B ==> orderedBefore g A B``,
        RW_TAC (srw_ss()) [modifiesBefore_def]);
val modifiesBefore_transitivity = prove(
    ``∀ g. transitive (modifiesBefore g)``,
        METIS_TAC [trans_def, modifiesBefore_def,sameAddress_def, orderedBefore_transitivity]);
val modifiesBefore_inGraph = prove(
    ``impliesInGraph modifiesBefore``, metis_tac[impliesInGraph_def,orderedBefore_inGraph,modifiesBefore_def]);

(* sequencedBefore *)
val sequencedBefore_orderedBefore = prove(
    ``∀ g A B. sequencedBefore g A B ==> orderedBefore g A B``,
        RW_TAC (srw_ss()) [sequencedBefore_def]);
val sequencedBefore_transitivity = prove(
    ``∀ g. transitive (sequencedBefore g)``,
        METIS_TAC [trans_def, sequencedBefore_def,orderedBefore_transitivity,sameThread_def]);
val sequencedBefore_inGraph = prove(
    ``impliesInGraph sequencedBefore``, metis_tac[impliesInGraph_def,orderedBefore_inGraph,sequencedBefore_def]);

(* releaseSequenceOf *)
val inReleaseSequenceOf_selfOrderedBefore = prove(
    ``∀ g A B. inReleaseSequenceOf g A B ∧ (A <> B) ==> orderedBefore g B A``,
        RW_TAC(srw_ss()) [inReleaseSequenceOf_def,sequencedBefore_def]);
(*val inReleaseSequenceOf_headOrderedBefore = prove(
    ``∀ g A B C. isReadBy g B C ∧ inReleaseSequenceOf g B A ==> orderedBefore g A C``,
        METIS_TAC [trans_def, isReadBy_def,inReleaseSequenceOf_selfOrderedBefore,orderedBefore_transitivity]);*)
val inReleaseSequenceOf_reflexivity = prove(
    ``∀ g A. isInGraph g A ==> inReleaseSequenceOf g A A``,
        rw [inReleaseSequenceOf_def]);
val inReleaseSequenceOf_transitivity = prove(
    ``∀ g A B C. inReleaseSequenceOf g A B ∧ inReleaseSequenceOf g B C ==> inReleaseSequenceOf g A C``,
        RW_TAC arith_ss [trans_def,inReleaseSequenceOf_def, orderedBefore_transitivity] THEN
        METIS_TAC [trans_def,sequencedBefore_transitivity,modifiesBefore_transitivity]);
val inReleaseSequenceOf_inGraph = prove(
    ``impliesInGraph inReleaseSequenceOf``,
        rw [impliesInGraph_def,inReleaseSequenceOf_def,sequencedBefore_def,orderedBefore_def] >> rw []);

(* carriesDependencyTo *)
val carriesDependencyTo_inGraph = prove(
    ``impliesInGraph carriesDependencyTo``,
        rw [impliesInGraph_def,carriesDependencyTo_def]);    

(* synchronizesWith *)
val synchronizesWith_inGraph = prove(
    ``impliesInGraph synchronizesWith``,
        rw [impliesInGraph_def, synchronizesWith_def] THEN metis_tac [inReleaseSequenceOf_inGraph,impliesInGraph_def,isReadBy_inGraph,sequencedBefore_inGraph]);

(* dependencyOrderedBefore *)
val dob_inGraph = prove(
    ``impliesInGraph dependencyOrderedBefore``,
        rw [impliesInGraph_def] >>
        UNDISCH_TAC ``wellFormed g`` >>
        UNDISCH_TAC ``dependencyOrderedBefore g A B`` >>
        SPEC_TAC (``B:node``,``B:node``) >>
        SPEC_TAC (``A:node``,``A:node``) >>
        SPEC_TAC (``g:graph``,``g:graph``) >>
        Induct_on `dependencyOrderedBefore` >>
        rw [] >> metis_tac [impliesInGraph_def, modifiesBefore_inGraph,carriesDependencyTo_def]);

(* interthreadHappensBefore *)
val ithb_inGraph = prove(
    ``impliesInGraph interthreadHappensBefore``,
        rw [impliesInGraph_def] >>
        UNDISCH_TAC ``wellFormed g`` >>
        UNDISCH_TAC ``interthreadHappensBefore g A B`` >>
        SPEC_TAC (``B:node``,``B:node``) >>
        SPEC_TAC (``A:node``,``A:node``) >>
        SPEC_TAC (``g:graph``,``g:graph``) >>
        Induct_on `interthreadHappensBefore` >>
        rw [] >>
        metis_tac [impliesInGraph_def,synchronizesWith_inGraph, dob_inGraph,sequencedBefore_inGraph,synchronizesWith_inGraph]);

(* happensBefore *)
val happensBefore_partial_transitivity = prove(
    ``∀ g. (~∃ X. (isInGraph g X ∧ isConsume X)) ==> transitive (happensBefore g)``,
    cheat); (*TODO*)
    
(* visibleTo *)
(*val visibleTo_orderedBefore = prove(
    ``impliesOrderedBefore visibleTo``,
        METIS_TAC [impliesOB_def, visibleTo_def, happensBefore_orderedBefore]);*)
(* visibleTo is not transitive, since happensBefore isn't transitive *)


(* inVisibleSequenceOf *)
(*val inVisibleSequenceOf_irreflexivity = prove(
    ``∀ g. wellFormed g ==> irreflexive (inVisibleSequenceOf g)``,
        RW_TAC (srw_ss()) [irrefl_def, LET_THM, inVisibleSequenceOf_def, visibleTo_def] >>
        `~visibleTo g A A ∧ ~happensBefore g A A` by METIS_TAC [wellFormed_def, irrefl_def, impliesOB_def,visibleTo_orderedBefore, happensBefore_orderedBefore, orderedBefore_irreflexivity] >>
        Cases_on `isStore A` >> Cases_on `isAtomic A` >> rw [] >>
        `~isLoad A` by EVAL_TAC >> UNDISCH_TAC ``isStore A`` >> rw [isStore_def,isLoad_def]);*)
(* inVisibleSequenceOf DOESN'T imply orderedBefore (see example in tests/) *)


(* sequentiallyConsistent *)
(*val sequentiallyConsistent_irreflexivity = prove(
    ``∀ g. wellFormed g ==> irreflexive (sequentiallyConsistent g)``,
        METIS_TAC [wellFormed_def, irrefl_def, LET_THM, sequentiallyConsistent_def, inVisibleSequenceOf_irreflexivity, sameAddress_def, orderedBefore_irreflexivity]);*)
(* sequentiallyConsistent doesn't imply orderedBefore (see inVisibleSequenceOf) *)


(* canBeReadBy *)
(*val canBeReadBy_irreflexivity = prove(
    ``∀ g. wellFormed g ==> irreflexive (canBeReadBy g)``,
        METIS_TAC [wellFormed_def, irrefl_def,impliesOB_def, canBeReadBy_def, sequentiallyConsistent_irreflexivity,inVisibleSequenceOf_irreflexivity,visibleTo_orderedBefore,orderedBefore_irreflexivity]);*)
(* canBeReadBy doesn't imply orderedBefore (see seqConsistent) *)






(* resolve *)

(*open finite_mapTheory;*)
(*
val resolve_visibleTo = prove(
    ``∀ g1 g2 msg A B. resolve g1 (msg, g2) ∧ visibleTo g1 A B ==> visibleTo g2 A B``,
        rw [resolve_def, visibleTo_def]

    
val resolve_canBeReadBy = prove(
    ``∀ g1 g2 msg A B. resolve g1 (msg, g2) ∧ canBeReadBy g1 A B ==> canBeReadBy g2 A B``,
        rw [resolve_def,canBeReadBy_def] THENL [
          (*1.*)  FULL_SIMP_TAC (srw_ss()) [inVisibleSequenceOf_def,sequentiallyConsistent_def,visibleTo_def,LET_THM,visibleTo_def,orderedBefore_def,happensBefore_def]
        ]
           METIS_TAC []
           
val resolve_wellFormed = prove(
    ``∀ g1 g2 msg. wellFormed g1 ∧ resolve g1 (msg, g2) ==> wellFormed g2``,
        rw [wellFormed_def] THENL [
            metis_tac [resolve_def,orderedBefore_def,carriesDependencyTo_def],
            FULL_SIMP_TAC (srw_ss()) [resolve_def]>>
            Cases_on `(r,w)=(B,A)` >> rw [] >>
            FULL_SIMP_TAC (srw_ss()) [isReadBy_def]
            Cases_on `r=B` >> rw []
            `(g1.rf |+ (B,w)) ' B = A ∧ w = A` by FULL_SIMP_TAC (srw_ss()) [FLOOKUP_DEF] THENL [
                METIS_TAC [FLOOKUP_DEF,FAPPLY_FUPDATE_THM],
                rw []
            ]
 *)         





(* TODO:

1. Find example where A isReadBy B but B is orderedBefore A
2. Find example where A is orderedBefore B but B is in the visibleSequence of A

 *)



val _ = export_theory();
