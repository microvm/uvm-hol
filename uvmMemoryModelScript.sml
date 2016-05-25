open HolKernel Parse boolLib bossLib;

open uvmIRTheory;
open lcsymtacs;
open listTheory;

val _ = new_theory "uvmMemoryModel";


(* Datatypes and type abbreviations *)
val _ = type_abbrev("input", ``:(memory_message # tid)``);
val _ = Datatype` output_message = Out value memreqid tid `;
val _ = Datatype`ops = Rd | Wr | Fn `;
val _ = Datatype`
  node = <|
    operation : ops ;
    address   : addr ;
    values    : value option ;
    mid       : memreqid ;
    thread_id : tid ;
    order     : memory_order ;
    ddeps     : memdeps
  |>
`;
val _ = Datatype`
  graph = <|
    nodes : node list ;
    rf    : node |-> node
  |>
`;

(* Term definitions *)
val is_fence_def = Define`
    is_fence n = (n.operation = Fn)`;

val is_load_def = Define`
    is_load n = (n.operation = Rd)`;

val is_store_def = Define`
    is_store n = (n.operation = Wr)`;

val is_acquire_def = Define`
    is_acquire n = case n.order of
        ACQUIRE => (n.operation = Rd) ∨ (n.operation = Fn)
      | ACQ_REL => (n.operation = Rd) ∨ (n.operation = Fn)
      | SEQ_CST => (n.operation = Rd) ∨ (n.operation = Fn)
      | CONSUME => (n.operation = Fn)
      | _       => F`;

val is_consume_def = Define`
    is_consume n = ((n.operation = Rd) ∧ (n.order <> NOT_ATOMIC) ∧ (n.order <> RELAXED)) (* or (n.order=CONSUME) *)`;

val is_release_def = Define`
    is_release n = case n.order of
        RELEASE => (n.operation = Wr) ∨ (n.operation = Fn)
      | ACQ_REL => (n.operation = Wr) ∨ (n.operation = Fn)
      | SEQ_CST => (n.operation = Wr) ∨ (n.operation = Fn)
      | _       => F`;

val is_seq_cst_def = Define`
    is_seq_cst n = (n.order = SEQ_CST)`;

val is_atomic_def = Define`
    is_atomic n = (n.order <> NOT_ATOMIC)`;

val same_thread_def = Define`
    same_thread A B = (A.thread_id = B.thread_id)`;

val same_address_def = Define`
    same_address A B = (A.address = B.address)`;

val is_in_graph_def = Define`
    is_in_graph g A = MEM A g.nodes`;






(* Undefined for missing items *)
val ordered_before_def = Define`
    ordered_before g A B = ((is_in_graph g A) ∧ (is_in_graph g B) ∧ (THE (INDEX_OF A g.nodes)) < (THE (INDEX_OF B g.nodes)))`;
    (*             of
                              (SOME a, SOME b) => (a < b)
                            | _ => (F)  `;*)

val is_read_by_def = Define`
    is_read_by g A B = (FLOOKUP g.rf B = SOME A)`;

val modifies_before_def = Define`
    modifies_before g A B = ( (ordered_before g A B) ∧ (same_address A B) ∧ (is_store A) ∧ (is_store B))`;

val sequenced_before_def = Define`
    sequenced_before g A B = ((ordered_before g A B) ∧ (same_thread A B)  )`;

val in_release_sequence_of_def = Define`
    in_release_sequence_of g B A = ( ((B = A) ∧ (is_in_graph g A)) ∨ ((modifies_before g A B) ∧ (is_atomic B) ∧ (sequenced_before g A B)))`;
val release_sequence_of_def = Define` (* TODO: include read-write ops *)
    release_sequence_of g A = { B | (B = A) ∨ ((modifies_before g A B) ∧ (is_atomic B) ∧ (is_store B) ∧ ((sequenced_before g A B) ∨ (F) )  )}   `;

val carries_dependency_to_def = Define`
    carries_dependency_to g A B = ((A.mid IN B.ddeps) ∧ (is_in_graph g A) ∧ (is_in_graph g B))`;
(* This should be worked out within the thread? *)
(* val (cdep_rules, cdep_ind, cdep_cases) = Hol_reln` (* This might not be how reln is supposed to work *)
    (∀ g B A. (A.mid IN B.ddeps) ==> (carries_dependency_to g B A)) ∧
    (∀ g B A. (∃ X. (sequenced_before g A X) ∧ (sequenced_before g X B) ∧ (is_store X) ∧ (is_load B) ∧ (same_address X B) ∧ (A.mid IN X.ddeps)) ==> (carries_dependency_to g B A)) ∧
    (∀ g B A. (∃ X. (carries_dependency_to g A X) ∧ (carries_dependency_to g X B)) ==> (carries_dependency_to g B A) )`;*)

val synchronizes_with_def = Define`
    synchronizes_with g A B = (
        (*1.*) ( (is_release A) ∧ (is_acquire B) ∧ (same_address A B) ∧ (∃ X. (is_read_by g X B ) ∧ (in_release_sequence_of g X A)) ) ∨
        (*2.*) ( (is_release A) ∧ (is_acquire B) ∧ (is_fence A) ∧ (is_fence B) ∧ (∃ X Y. (is_atomic X) ∧ (is_atomic Y) ∧ (same_address X Y) ∧ (sequenced_before g A X) ∧ (is_store X) ∧ (sequenced_before g Y B) ∧ ( (is_read_by g X Y) ∨ (∃ Z. (is_read_by g Z Y) ∧ (in_release_sequence_of g Z X)))) ) ∨
        (*3.*) ( (is_release A) ∧ (is_acquire B) ∧ (is_fence A) ∧ (∃ X. (sequenced_before g A X) ∧ (same_address B X) ∧ ((is_read_by g X B) ∨ (∃ Z. (is_read_by g Z B) ∧ (in_release_sequence_of g Z X))) ) ) ∨
        (*4.*) ( (is_atomic A) ∧ (is_release A) ∧ (is_acquire B) ∧ (is_fence B) ∧ (∃ X. (same_address A X) ∧ (sequenced_before g X B) ∧ ((is_read_by g A X) ∨ (∃ Z. (is_read_by g Z X) ∧ (in_release_sequence_of g Z A))  ))  ) ∨ (* TODO *)
        (*5. A is the creation of a thread and B is the beginning of the execution of the new thread. *) (F) ∨
        (*6. A is a futex wake operation and B is the next operation after the futex wait operation of the thread woken up by A. *) (F)   )`;

val (dob_rules, dob_ind, dob_cases) = xHol_reln "dob" `
      (*1.*) (∀ g A B  . (is_release A) ∧ (modifies_before g A B) ∧ ~(same_thread A B) ∧ (is_consume B) ∧ (∃ X. (in_release_sequence_of g X A) ∧ (is_read_by g X B) ) ==> dependency_ordered_before g A B  ) ∧
      (*2.*) (∀ g A B X. (dependency_ordered_before g A X) ∧ (carries_dependency_to g X B) ==> dependency_ordered_before g A B)   `;

val (ithb_rules, ithb_ind, ithb_cases) = xHol_reln "ithb" `
    (* A.  *) ( ∀ g A B  . (synchronizes_with g A B) ==> (interthread_happens_before g A B)) ∧
    (* B.  *) ( ∀ g A B  . (dependency_ordered_before g A B) ==> (interthread_happens_before g A B)) ∧
    (* C.1 *) ( ∀ g A B X. ((synchronizes_with g A X) ∧ (sequenced_before g X B)) ==> (interthread_happens_before g A B)) ∧
    (* C.2 *) ( ∀ g A B X. ((sequenced_before g A X) ∧ (interthread_happens_before g X B)) ==> (interthread_happens_before g A B)) ∧
    (* C.3 *) ( ∀ g A B X. ((interthread_happens_before g A X) ∧ (interthread_happens_before g X B)) ==> (interthread_happens_before g A B)   )`;

val happens_before_def = Define`
    happens_before g A B = (
      (*1.*) (sequenced_before g A B) ∨
      (*2.*) (interthread_happens_before g A B)   )`;

val visible_to_def = Define`
    visible_to g A B = ( (is_store A) ∧ (is_load B) ∧
      (*1.*) (happens_before g A B) ∧
      (*2.*) ~(∃ X. (happens_before g A X) ∧ (happens_before g X B))   )`;

(* TODO: fix to only look at writes and only return a set given a read *)
val in_visible_sequence_of_def = Define` (* TODO: fix to only look at writes and only return a set given a read? *)
    in_visible_sequence_of g A B =
      let visible_sequence X = { nd | (nd.address = X.address) ∧ (is_store nd) ∧ (is_atomic nd) ∧
                                      (      (visible_to g nd X) ∨ (* The first in sequence *)
                                             (    ~(happens_before g X nd) ∧
                                                   (∃fs. (visible_to g fs X) ∧
                                                         (modifies_before g fs nd))))} (* the rest *)
      in A IN (visible_sequence B)    `;

val sequentially_consistent_def = Define`
    sequentially_consistent g A B = (is_seq_cst A ∧ is_seq_cst B ∧ ordered_before g A B)`;

val seq_cst_exception_def = Define`
    seq_cst_exception g X B =
      let is_most_recent_seq_cst n = ( (is_in_graph g n) ∧
                                       (sequentially_consistent g n B) ∧ (same_address n B) ∧ ~(∃ Y.
                                       (sequentially_consistent g Y B) ∧ (same_address Y B) ∧ (sequentially_consistent g n Y)))
      in
         ( ∃ A. (is_most_recent_seq_cst A ∧ ( (X = A) ∨ ( (in_visible_sequence_of g X B) ∧ ~(is_seq_cst X) ∧ ~(happens_before g X A)))) ∨
          ~∃ A. (is_most_recent_seq_cst A ∧ (in_visible_sequence_of g X B) ∧ ~(is_seq_cst X)))`;


val can_be_read_by_def = Define`
    can_be_read_by g B A = (
      (~(is_atomic A) ∧ ~(is_atomic B) ∧ (visible_to g B A) ) ∨                              (* non-atomic *)
      (~(is_seq_cst B) ∧ (is_atomic A) ∧  (is_atomic B) ∧ (in_visible_sequence_of g B A) ) ∨ (* atomic *)
      ( (is_seq_cst B) ∧ (sequentially_consistent g B A)) ∨                                  (* Sequentally Consistent *)
      ( F )                                                                                  (* undefined combinations? *)  )`;





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
  receive (in_graph, (msg, ttid)) graph' =
    case msg of
    | Read a' id order' dep =>
        let new_node = <| operation := Rd;
                          address := a';
                          values := NONE;
                          mid := id;
                          thread_id := ttid;
                          order := order';
                          ddeps := dep |>
        in (graph' = in_graph with nodes updated_by (λlst. lst ++ [new_node] ))

    | Write a' id vl order' dep =>
        let new_node = <| operation := Wr;
                          address := a';
                          values := SOME vl;
                          (* mid := LEAST n. ~(∃ nd. (nd.mid = n) ∧ (nd IN in_graph.nodes));*)
                          mid := id;
                          thread_id := ttid;
                          order := order';
                          ddeps := dep |>
        in (graph' = in_graph with nodes updated_by (λlst. lst ++ [new_node]))
`;

(* TODO: output message *)
val resolve_def = Define`
    resolve g1 (msg, g2) = ∃ w r. (g1.nodes = g2.nodes) ∧ (* TODO: maybe update r's value? *)
                                  (can_be_read_by g1 w r) ∧ (g2.rf = g1.rf |+ (r, w)) ∧
                                  (~∃ w'. FLOOKUP g1.rf r = SOME w') ∧
                                  (msg = Out (THE w.values) (r.mid) (r.thread_id))
`;




(***********************************)
(* Defined and Undefined Behaviour *)
(***********************************)
val data_race_def = Define`
    data_race g A B = (
       (is_in_graph g A)               ∧
       (is_in_graph g B)               ∧
       (same_address A B)              ∧
       ( (is_store A) ∨ (is_store B) ) ∧
      ~(happens_before g A B)          ∧
      ~(happens_before g B A)
 )`;

val indeterminate_read_def = Define`
    indeterminate_read g A = ~∃ B. can_be_read_by g B A`;

val consistent_sc_order_def = Define`
    consistent_sc_order g = ∀ A B.
        (is_seq_cst A ∧ is_seq_cst B) ==> ((happens_before g A B ==> sequentially_consistent g A B) ∧
                                          (modifies_before g A B ==> sequentially_consistent g A B))`;

val consistent_reads_from_mapping_def = Define`
    consistent_reads_from_mapping g = ∀ A B. is_read_by g A B ==> (can_be_read_by g A B ∧ is_in_graph g A ∧ is_in_graph g B)`;

val consistent_ithb_def = Define`
    consistent_ithb g = ∀ A. ~interthread_happens_before g A A`;

val consistent_modification_order_def = Define`
    consistent_modification_order g = ∀ A B.
        ( (is_atomic A ∧ is_atomic B) ==> (happens_before g A B ==> modifies_before g A B)) ∧
        (~(is_atomic A ∧ is_atomic B) ==> ~modifies_before g A B)`;

(* Coherence *)
val CoRR_def = Define`
    CoRR g = ~∃ A B C D. (happens_before g C D ∧ is_read_by g A C ∧ is_read_by g B D ∧ modifies_before g B A)`;

val CoWR_def = Define`
    CoWR g = ~∃ B C D. (is_read_by g B D ∧ happens_before g C D ∧ modifies_before g B C)`;

val CoWW_def = Define`
    CoWW g = ~∃ A B. happens_before g A B ∧ modifies_before g B A`;

val CoRW_def = Define`
    CoRW g = let rhm = ($RUNION ( $RUNION (is_read_by g) (happens_before g)) (modifies_before g))
              in (~∃ A. rhm^* A A)`;          

val well_formed_def = Define`
    well_formed g = consistent_reads_from_mapping g`;

val consistent_execution_def = Define`
    consistent g = (
        consistent_ithb g ∧
        consistent_sc_order g ∧                                    
        consistent_modification_order g ∧
        consistent_reads_from_mapping g ∧
        (* No dataraces *)
        (~∃ A B. data_race g A B) ∧
        (* No indeterminate reads *)
        (~∃ A. indeterminate_read g A)
)`;




(*************************************************************)
(* Proofs for some properties of the relations defined above *)
(*************************************************************)

val implies_ob_def = Define`
    implies_ordered_before p = ∀ g A B. (well_formed g ∧ p g A B ==> ordered_before g A B)`;
val trans_def = Define`
    transitive p = ∀ A B C. p A B ∧ p B C ==> p A C`;
val asym_def = Define`
    assymetric p = ∀ A B. p A B ==> ~p B A`;
val irrefl_def = Define`
    irreflexive p = ∀ A. ~p A A`;
val implies_in_graph_def = Define`
    implies_in_graph p = ∀ g A B. (well_formed g ∧ p g A B) ==> (is_in_graph g A ∧ is_in_graph g B)`;



(* ordered_before *)
val ordered_before_irreflexivity = prove(
    ``∀ g. irreflexive (ordered_before g)``,
        rw [irrefl_def, ordered_before_def]);
val ordered_before_asymmetry = prove(
    ``∀ g. assymetric (ordered_before g)``,
        RW_TAC arith_ss [asym_def,ordered_before_def]);
val ordered_before_transitivity = prove(
    ``∀g. transitive (ordered_before g)``,
        RW_TAC arith_ss [trans_def,ordered_before_def]);
(* If something implies ordered_before then it is also irreflexive and assymetrical *)
val ordered_before_in_graph = prove(
    ``implies_in_graph ordered_before``, rw [implies_in_graph_def, ordered_before_def]);

val is_read_by_in_graph = prove(
    ``implies_in_graph is_read_by``, prove_tac [implies_in_graph_def, consistent_reads_from_mapping_def,well_formed_def]);

(* modifies_before *)
val modifies_before_ordered_before = prove(
    ``∀ g A B. modifies_before g A B ==> ordered_before g A B``,
        RW_TAC (srw_ss()) [modifies_before_def]);
val modifies_before_transitivity = prove(
    ``∀ g. transitive (modifies_before g)``,
        METIS_TAC [trans_def, modifies_before_def,same_address_def, ordered_before_transitivity]);
val modifies_before_in_graph = prove(
    ``implies_in_graph modifies_before``, metis_tac[implies_in_graph_def,ordered_before_in_graph,modifies_before_def]);

(* sequenced_before *)
val sequenced_before_ordered_before = prove(
    ``∀ g A B. sequenced_before g A B ==> ordered_before g A B``,
        RW_TAC (srw_ss()) [sequenced_before_def]);
val sequenced_before_transitivity = prove(
    ``∀ g. transitive (sequenced_before g)``,
        METIS_TAC [trans_def, sequenced_before_def,ordered_before_transitivity,same_thread_def]);
val sequenced_before_in_graph = prove(
    ``implies_in_graph sequenced_before``, metis_tac[implies_in_graph_def,ordered_before_in_graph,sequenced_before_def]);

(* release_sequence_of *)
val in_release_sequence_of_self_ordered_before = prove(
    ``∀ g A B. in_release_sequence_of g A B ∧ (A <> B) ==> ordered_before g B A``,
        RW_TAC(srw_ss()) [in_release_sequence_of_def,sequenced_before_def]);
(*val in_release_sequence_of_headOrderedBefore = prove(
    ``∀ g A B C. is_read_by g B C ∧ in_release_sequence_of g B A ==> ordered_before g A C``,
        METIS_TAC [trans_def, is_read_by_def,in_release_sequence_of_self_ordered_before,ordered_before_transitivity]);*)
val in_release_sequence_of_reflexivity = prove(
    ``∀ g A. is_in_graph g A ==> in_release_sequence_of g A A``,
        rw [in_release_sequence_of_def]);
val in_release_sequence_of_transitivity = prove(
    ``∀ g A B C. in_release_sequence_of g A B ∧ in_release_sequence_of g B C ==> in_release_sequence_of g A C``,
        RW_TAC arith_ss [trans_def,in_release_sequence_of_def, ordered_before_transitivity] THEN
        METIS_TAC [trans_def,sequenced_before_transitivity,modifies_before_transitivity]);
val in_release_sequence_of_in_graph = prove(
    ``implies_in_graph in_release_sequence_of``,
        rw [implies_in_graph_def,in_release_sequence_of_def,sequenced_before_def,ordered_before_def] >> rw []);

(* carries_dependency_to *)
val carries_dependency_to_in_graph = prove(
    ``implies_in_graph carries_dependency_to``,
        rw [implies_in_graph_def,carries_dependency_to_def]);    

(* synchronizes_with *)
val synchronizes_with_in_graph = prove(
    ``implies_in_graph synchronizes_with``,
        rw [implies_in_graph_def, synchronizes_with_def] THEN metis_tac [in_release_sequence_of_in_graph,implies_in_graph_def,is_read_by_in_graph,sequenced_before_in_graph]);

(* dependency_ordered_before *)
val dob_in_graph = prove(
    ``implies_in_graph dependency_ordered_before``,
        rw [implies_in_graph_def] >>
        UNDISCH_TAC ``well_formed g`` >>
        UNDISCH_TAC ``dependency_ordered_before g A B`` >>
        SPEC_TAC (``B:node``,``B:node``) >>
        SPEC_TAC (``A:node``,``A:node``) >>
        SPEC_TAC (``g:graph``,``g:graph``) >>
        Induct_on `dependency_ordered_before` >>
        rw [] >> metis_tac [implies_in_graph_def, modifies_before_in_graph,carries_dependency_to_def]);

(* interthread_happens_before *)
val ithb_in_graph = prove(
    ``implies_in_graph interthread_happens_before``,
        rw [implies_in_graph_def] >>
        UNDISCH_TAC ``well_formed g`` >>
        UNDISCH_TAC ``interthread_happens_before g A B`` >>
        SPEC_TAC (``B:node``,``B:node``) >>
        SPEC_TAC (``A:node``,``A:node``) >>
        SPEC_TAC (``g:graph``,``g:graph``) >>
        Induct_on `interthread_happens_before` >>
        rw [] >>
        metis_tac [implies_in_graph_def,synchronizes_with_in_graph, dob_in_graph,sequenced_before_in_graph,synchronizes_with_in_graph]);

(* happens_before *)
val happens_before_partial_transitivity = prove(
    ``∀ g. (~∃ X. (is_in_graph g X ∧ is_consume X)) ==> transitive (happens_before g)``,
    cheat); (*TODO*)
    
(* visible_to *)
(*val visible_to_ordered_before = prove(
    ``implies_ordered_before visible_to``,
        METIS_TAC [implies_ob_def, visible_to_def, happens_before_ordered_before]);*)
(* visible_to is not transitive, since happens_before isn't transitive *)


(* in_visible_sequence_of *)
(*val in_visible_sequence_of_irreflexivity = prove(
    ``∀ g. well_formed g ==> irreflexive (in_visible_sequence_of g)``,
        RW_TAC (srw_ss()) [irrefl_def, LET_THM, in_visible_sequence_of_def, visible_to_def] >>
        `~visible_to g A A ∧ ~happens_before g A A` by METIS_TAC [well_formed_def, irrefl_def, implies_ob_def,visible_to_ordered_before, happens_before_ordered_before, ordered_before_irreflexivity] >>
        Cases_on `is_store A` >> Cases_on `is_atomic A` >> rw [] >>
        `~is_load A` by EVAL_TAC >> UNDISCH_TAC ``is_store A`` >> rw [is_store_def,is_load_def]);*)
(* in_visible_sequence_of DOESN'T imply ordered_before (see example in tests/) *)


(* sequentially_consistent *)
(*val sequentially_consistent_irreflexivity = prove(
    ``∀ g. well_formed g ==> irreflexive (sequentially_consistent g)``,
        METIS_TAC [well_formed_def, irrefl_def, LET_THM, sequentially_consistent_def, in_visible_sequence_of_irreflexivity, same_address_def, ordered_before_irreflexivity]);*)
(* sequentially_consistent doesn't imply ordered_before (see in_visible_sequence_of) *)


(* can_be_read_by *)
(*val can_be_read_by_irreflexivity = prove(
    ``∀ g. well_formed g ==> irreflexive (can_be_read_by g)``,
        METIS_TAC [well_formed_def, irrefl_def,implies_ob_def, can_be_read_by_def, sequentially_consistent_irreflexivity,in_visible_sequence_of_irreflexivity,visible_to_ordered_before,ordered_before_irreflexivity]);*)
(* can_be_read_by doesn't imply ordered_before (see seq_consistent) *)






(* resolve *)

(*open finite_mapTheory;*)
(*
val resolve_visible_to = prove(
    ``∀ g1 g2 msg A B. resolve g1 (msg, g2) ∧ visible_to g1 A B ==> visible_to g2 A B``,
        rw [resolve_def, visible_to_def]

    
val resolve_can_be_read_by = prove(
    ``∀ g1 g2 msg A B. resolve g1 (msg, g2) ∧ can_be_read_by g1 A B ==> can_be_read_by g2 A B``,
        rw [resolve_def,can_be_read_by_def] THENL [
          (*1.*)  FULL_SIMP_TAC (srw_ss()) [in_visible_sequence_of_def,sequentially_consistent_def,visible_to_def,LET_THM,visible_to_def,ordered_before_def,happens_before_def]
        ]
           METIS_TAC []
           
val resolve_well_formed = prove(
    ``∀ g1 g2 msg. well_formed g1 ∧ resolve g1 (msg, g2) ==> well_formed g2``,
        rw [well_formed_def] THENL [
            metis_tac [resolve_def,ordered_before_def,carries_dependency_to_def],
            FULL_SIMP_TAC (srw_ss()) [resolve_def]>>
            Cases_on `(r,w)=(B,A)` >> rw [] >>
            FULL_SIMP_TAC (srw_ss()) [is_read_by_def]
            Cases_on `r=B` >> rw []
            `(g1.rf |+ (B,w)) ' B = A ∧ w = A` by FULL_SIMP_TAC (srw_ss()) [FLOOKUP_DEF] THENL [
                METIS_TAC [FLOOKUP_DEF,FAPPLY_FUPDATE_THM],
                rw []
            ]
 *)         





(* TODO:

1. Find example where A is_read_by B but B is ordered_before A
2. Find example where A is ordered_before B but B is in the visible_sequence of A

 *)



val _ = export_theory();
