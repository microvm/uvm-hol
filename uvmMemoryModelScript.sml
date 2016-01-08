open HolKernel Parse boolLib bossLib;

open uvmIRTheory;
open lcsymtacs;

val _ = new_theory "uvmMemoryModel";


(* Datatypes and type abbreviations *)
val _ = type_abbrev("input", ``:(memoryMessage # tid)``);
val _ = Datatype` output_message = Out value memreqid tid `;
val _ = Datatype`ops = Rd | Wr | Fn `
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


(* Utlility function: *)
val indexOf_def = Define`
    indexOf list n A= case list of
                          x::xs => if (x=A) then SOME n else indexOf xs (n+1) A
                        | [] => NONE`;




(* Set of relations that are used to define `receive` and `resolve`:

 * ordered_before              [✓]
 * modifies_before             [✓]
 * sequenced_before            [✓]
 * release_sequence_of         [✓] : missing wrm
 * carries_dependency_to       [✓]




 * synchronizes_with           [ ] : missing fences, mutex, thread creation
 * dependency_ordered_before   [✓]
 * interthread_happens_before  [✓]
 * happens_before              [✓]
 * visible_to                  [✓]
 * visible_sequence_of         [~] : change format

(* can_read_from *)            [✓]
(* readsFrom *)                [✓]

 * receive                     [~]
 * resolve                     [~]

 ? Undefined behaviour         [?]


 *)



(* Undefined for missing items *)
val orderedBefore_def = Define`
    orderedBefore g A B = ((THE (indexOf g.nodes 0 A)) < (THE (indexOf g.nodes 0 B)))`;
    (*             of
                              (SOME a, SOME b) => (a < b)
                            | _ => (F)  `;*)

val readsFrom_def = Define`
    readsFrom g A B = ((FLOOKUP g.rf A = SOME B) ∧ (orderedBefore g B A))`;

val modifiesBefore_def = Define`
    modifiesBefore g A B = ( (orderedBefore g A B) ∧ (sameAddress A B) ∧ (isStore A) ∧ (isStore B))`;

val sequencedBefore_def = Define`
    sequencedBefore g A B = ((orderedBefore g A B) ∧ (sameThread A B)  )`;

val inReleaseSequenceOf_def = Define`
    inReleaseSequenceOf g B A = ((B = A) ∨ ((modifiesBefore g A B) ∧ (isAtomic B) ∧ (sequencedBefore g A B)))`;
val releaseSequenceOf_def = Define` (* TODO: include read-write ops *)
    releaseSequenceOf g A = { B | (B = A) ∨ ((modifiesBefore g A B) ∧ (isAtomic B) ∧ (isStore B) ∧ ((sequencedBefore g A B) ∨ (F) )  )}   `;

val carriesDependencyTo_def = Define`
    carriesDependencyTo g B A = ((B.mid IN A.ddeps) ∧ (orderedBefore g B A))`;
(* This should be worked out within the thread? *)
(* val (cdep_rules, cdep_ind, cdep_cases) = Hol_reln` (* This might not be how reln is supposed to work *)
    (∀ g B A. (A.mid IN B.ddeps) ==> (carriesDependencyTo g B A)) ∧
    (∀ g B A. (∃ X. (sequencedBefore g A X) ∧ (sequencedBefore g X B) ∧ (isStore X) ∧ (isLoad B) ∧ (sameAddress X B) ∧ (A.mid IN X.ddeps)) ==> (carriesDependencyTo g B A)) ∧
    (∀ g B A. (∃ X. (carriesDependencyTo g A X) ∧ (carriesDependencyTo g X B)) ==> (carriesDependencyTo g B A) )`;*)

val synchronizesWith_def = Define`
    synchronizesWith g A B = (
        (*1.*) ( (isRelease A) ∧ (isAcquire B) ∧ (sameAddress A B) ∧ (∃ X. (readsFrom g B X ) ∧ (inReleaseSequenceOf g X A)) ) ∨
        (*2.*) ( (isRelease A) ∧ (isAcquire B) ∧ (isFence A) ∧ (isFence B) ∧ (∃ X Y. (isAtomic X) ∧ (isAtomic Y) ∧ (sameAddress X Y) ∧ (sequencedBefore g A X) ∧ (isStore X) ∧ (sequencedBefore g Y B) ∧ ( (readsFrom g Y X) ∨ (∃ Z. (readsFrom g Y Z) ∧ (inReleaseSequenceOf g Z X)))) ) ∨
        (*3.*) ( (isRelease A) ∧ (isAcquire B) ∧ (isFence A) ∧ (∃ X. (sequencedBefore g A X) ∧ (sameAddress B X) ∧ ((readsFrom g B X) ∨ (∃ Z. (readsFrom g B Z) ∧ (inReleaseSequenceOf g Z X))) ) ) ∨
        (*4.*) ( (isAtomic A) ∧ (isRelease A) ∧ (isAcquire B) ∧ (isFence B) ∧ (∃ X. (sameAddress A X) ∧ (sequencedBefore g X B) ∧ ((readsFrom g X A) ∨ (∃ Z. (readsFrom g X Z) ∧ (inReleaseSequenceOf g Z A))  ))  ) ∨ (* TODO *)
        (*5. A is the creation of a thread and B is the beginning of the execution of the new thread. *) (F) ∨
        (*6. A is a futex wake operation and B is the next operation after the futex wait operation of the thread woken up by A. *) (F)   )`;

val (dob_rules, dob_ind, dob_cases) = Hol_reln`
      (*1.*) ((∀ A B g. (isRelease A) ∧ (modifiesBefore g A B) ∧ ~(sameThread A B) ∧ (isConsume B) ∧ (∃ X. (X IN (releaseSequenceOf g A)) ∧ (readsFrom g B X) )) ==> dob g A B  ) ∧
      (*2.*) ((∀ A B g X. (dependencyOrderedBefore g A X) ∧ (carriesDependencyTo g X B)) ==> dependencyOrderedBefore g A B)   `;

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
    visibleTo g A B = (
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
    sequentiallyConsistent g X B = let isA n = ( (isSeqCst n) ∧ (sameAddress n B) ∧ (orderedBefore g n B) ∧ ~(∃ Y.
                                       (isSeqCst Y) ∧ (sameAddress Y B) ∧ (orderedBefore g n Y) ∧ (orderedBefore g Y B)))
      in
        (∃ A. (isA A) ∧ (
                (X = A) ∨
                ( (inVisibleSequenceOf g X B) ∧ ~(isSeqCst X) ∧ ~(happensBefore g X A))  ) ∨
        ( ~(∃ A. (isA A)) ∧ (inVisibleSequenceOf g X B) ∧ ~(isSeqCst X)))`;
                                                                                                                  

val canReadFrom_def = Define`
    canReadFrom g A B = (
      (~(isAtomic A) ∧ ~(isAtomic B) ∧ (visibleTo g B A) ) ∨           (* non-atomic *)
      ( (isAtomic A) ∧  (isAtomic B) ∧ (inVisibleSequenceOf g B A) ) ∨ (* atomic *)
      ( (isSeqCst A) ∧  (sequentiallyConsistent g A B)) ∨                    (* Sequentally Consistent *)
      ( F )                                                                       (* undefined combinations? *)  )`;





(*******************************************************************************)
(* Everything above is building up to these two relations, receive and resolve *)
(*******************************************************************************)

(* Receive input message, create new nodes from these messages *)
val receive = Define`
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
val resolve = Define`
    resolve g1 (msg, g2) = ∃ w r. (g1.nodes = g2.nodes) ∧ (* TODO: maybe update r's value? *)
                                      (canReadFrom g1 w r) ∧ (g2.rf = g1.rf |+ (r, w)) ∧
                                      (msg = Out (THE w.values) (r.mid) (r.thread_id))
`;









(* Some properties of the above relations *)


(* orderedBefore *)
val orderedBefore_irreflexivity = prove(
    ``∀ g nd. ~orderedBefore g nd nd``,
        rw [orderedBefore_def]);
val orderedBefore_asymmetry = prove(
    ``∀ g nd1 nd2. orderedBefore g nd1 nd2 ==> ~orderedBefore g nd2 nd1``,
        RW_TAC arith_ss [orderedBefore_def]);
val orderedBefore_transitivity = prove(
    ``∀ g nd1 nd2 nd3. orderedBefore g nd1 nd2 ∧ orderedBefore g nd2 nd3 ==> orderedBefore g nd1 nd3``,
        RW_TAC arith_ss [orderedBefore_def]);


(* modifiesBefore *)
val modifiesBefore_irreflexivity = prove(
    ``∀ g nd. ~modifiesBefore g nd nd``,
        rw [modifiesBefore_def,orderedBefore_def,sameAddress_def]);
val modifiesBefore_asymmetry = prove(
    ``∀ g nd1 nd2. modifiesBefore g nd1 nd2 ==> ~modifiesBefore g nd2 nd1``,
        RW_TAC arith_ss [modifiesBefore_def,orderedBefore_def,sameAddress_def]);
val modifiesBefore_transitivity = prove(
    ``∀ g nd1 nd2 nd3. modifiesBefore g nd1 nd2 ∧ modifiesBefore g nd2 nd3 ==> modifiesBefore g nd1 nd3``,
        METIS_TAC [modifiesBefore_def,sameAddress_def, orderedBefore_transitivity]);


(* sequencedBefore *)
val sequencedBefore_irreflexivity = prove(
    ``∀ nd g. ~sequencedBefore g nd nd``,
        RW_TAC arith_ss [sequencedBefore_def,orderedBefore_def,sameThread_def] );
val sequencedBefore_asymmetry = prove(
    ``∀ g nd1 nd2. sequencedBefore g nd1 nd2 ==> ~sequencedBefore g nd2 nd1``,
        RW_TAC arith_ss [sequencedBefore_def,sameThread_def,orderedBefore_def]);
val sequencedBefore_transitivity = prove(
    ``∀ g nd1 nd2 nd3. sequencedBefore g nd1 nd2 ∧ sequencedBefore g nd2 nd3 ==> sequencedBefore g nd1 nd3``,
        METIS_TAC [sequencedBefore_def,orderedBefore_transitivity,sameThread_def]);


(* releaseSequenceOf *)
val inReleaseSequenceOf_headOrderedBefore = prove(
    ``∀ A B C g. readsFrom g C B ∧ inReleaseSequenceOf g B A ==> orderedBefore g A C``,
        METIS_TAC [sequencedBefore_def,
                   inReleaseSequenceOf_def,
                   readsFrom_def,AND_IMP_INTRO,
                   orderedBefore_transitivity]);
val inReleaseSequenceOf_selfOrderedBefore = prove(
    ``∀ g A B. inReleaseSequenceOf g A B ∧ (A <> B) ==> orderedBefore g B A``,
        RW_TAC(srw_ss()) [inReleaseSequenceOf_def,sequencedBefore_def]);
val inReleaseSequenceOf_reflexivity = prove(
    ``∀ g A. inReleaseSequenceOf g A A``,
        RW_TAC (srw_ss()) [inReleaseSequenceOf_def]);
val inReleaseSequenceOf_asymmetry = prove(
    ``∀ g A B. inReleaseSequenceOf g A B ∧ (A <> B) ==> ~inReleaseSequenceOf g B A``,
        METIS_TAC [inReleaseSequenceOf_def, modifiesBefore_def, orderedBefore_asymmetry]);
val inReleaseSequenceOf_transitivity = prove(
    ``∀ g A B C. inReleaseSequenceOf g A B ∧ inReleaseSequenceOf g B C ==> inReleaseSequenceOf g A C``,
        RW_TAC arith_ss [inReleaseSequenceOf_def, orderedBefore_transitivity] THEN
        METIS_TAC [sequencedBefore_transitivity,modifiesBefore_transitivity]);

(* carriesDependencyTo *)
val carriesDependencyTo_irreflexivity = prove(
    ``! g nd. ~carriesDependencyTo g nd nd``,
        RW_TAC (srw_ss()) [carriesDependencyTo_def, orderedBefore_irreflexivity]);


(* synchronizesWith *)
val synchronizesWith_irreflexivity = prove(
    ``∀ nd g. ~(synchronizesWith g nd nd)``,
        RW_TAC (srw_ss()) [synchronizesWith_def] THEN
        METIS_TAC [readsFrom_def, 
                   inReleaseSequenceOf_def, 
                   sequencedBefore_def, 
                   orderedBefore_def, 
                   orderedBefore_irreflexivity,
                   orderedBefore_asymmetry, 
                   orderedBefore_transitivity, 
                   inReleaseSequenceOf_selfOrderedBefore]);


(* interthreadHappensBefore *)
val ithb_obf = prove(
    `` ∀ g X Y. interthreadHappensBefore g X Y ==> orderedBefore g X Y``,
        cheat);
  (*  Induct_on `interthreadHappensBefore` >>
              metis_tac[orderedBefore_TRANS, sequencedBefore_obf,
                        syncWith_obf])
              MATCH_MP_TAC ithb_ind

val it_sanity0 = prove(
`` ∀ nd g. ~ interthreadHappensBefore g nd nd ``,
metis_tac[ithb_obf, obf_IRREFL]
    
    RW_TAC (srw_ss()) [ithb_rules] THEN
    `~synchronizesWith g nd nd` by METIS_TAC [sw_sanity1]
    `~dependencyOrderedBefore g nd nd` by METIS_TAC [dob_rules]
    ...);
*)


(*happensBefore*)
(*
g `∀ nd g. ~(happensBefore g nd nd)`;
METIS_TAC [happensBefore_def, sequencedBefore_def, orderedBefore_def, sameThread_def
RW_TAC arith_ss [happensBefore_def,sequencedBefore_def,orderedBefore_def, sameThread_def]
RW_TAC arith_ss [ithb_rules]
*)

(* visibleSequenceOf *)
(* Incomplete:
val in_own_release_seq = prove(
``∀ g nd. (MEM nd g.nodes) ==> (releaseSequenceOf g nd nd)``,
RW_TAC arith_ss [releaseSequenceOf_def]
    RW_TAC arith_ss [releaseSequenceOf_def,modifiesBefore_def,isAtomic_def,isStore_def,sequencedBefore_def,orderedBefore_def,sameAddress_def,sameThread_def] THEN
e(DISCH_TAC ``orderedBefore g nd1 nd2``);
e(`nd1.thread_id = nd2.thread_id` by METIS_TAC []);
e(Cases_on `SOME x'`);
e(RW_TAC arith_ss []  );
 *)

(* canReadFrom *)
(*
g `canReadFrom g11 r11_1 w11_0 = T`;
e (RW_TAC arith_ss [canReadFrom_def,isAtomic_def]);
e (`r11_1.order <> NOT_ATOMIC` by EVAL_TAC );
e (UNDISCH_TAC ``r11_1.order <> NOT_ATOMIC``);
e (RW_TAC arith_ss [canReadFrom_def, isAtomic_def,visibleTo_def,happensBefore_def,sequencedBefore_def,orderedBefore_def]);
e (`w11_1.order = SEQ_CST` by EVAL_TAC);
e (EVAL_TAC);
e (RW_TAC arith_ss []);
e (`w11_2.order = SEQ_CST` by PROVE_TAC [] );
e (Cases_on `w11_2.order` THEN Cases_on `r11_3.order`);
(* HOW DO I SIMPLIFY w1_2.order to SEQ_CST? *)
e (SIMP_TAC (srw_ss()) [node_accessors, memoryorder_distinct]);
(*e (`w1_2.order <> NOT_ATOMIC` by DECIDE_TAC);*)
g `inVisibleSequenceOf g11 r11_3 w11_2`;
e (RW_TAC (srw_ss()) [inVisibleSequenceOf_def]);
*)



val _ = export_theory();
