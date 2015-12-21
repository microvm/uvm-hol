
open HolKernel Parse boolLib bossLib;

open uvmThreadSemanticsTheory;

val _ = new_theory "uvmMemoryModel";


(* Datatypes and type abbreviations *)
val _ = type_abbrev("input", ``:(memoryMessage # tid)``);
val _ = Datatype` output_message = Out value memreqid tid `;
val _ = Datatype`ops = Rd | Wr | Fn `
val _ = Datatype`
  node = <|
    operation : ops ;
    address   : addr ;
    timestamp : num ;
    values    : value option ;
    mid       : memreqid ;
    thread_id : tid ;
    order     : memoryorder ;
    ddeps      : memdeps
  |>`
val _ = Datatype`
  graph = <|
          nodes : node set ;
             rf : node |-> node
          |>`;

          
(* Term definitions *)
val is_fence = Define`
    is_fence n = (n.operation = Fn)`;

val is_load = Define`
    is_load n = (n.operation = Rd)`;

val is_store = Define`
    is_store n = (n.operation = Wr)`;

val is_acquire = Define`
    is_acquire n = case n.order of
        ACQUIRE => (n.operation = Rd) ∨ (n.operation = Fn)
      | ACQ_REL => (n.operation = Rd) ∨ (n.operation = Fn)
      | SEQ_CST => (n.operation = Rd) ∨ (n.operation = Fn)
      | CONSUME => (n.operation = Fn)
      | _       => F`;

val is_consume = Define`
    is_consume n = ((n.operation = Rd) ∧ (n.order <> NOT_ATOMIC) ∧ (n.order <> RELAXED)) (* or (n.order=CONSUME) *)`;

val is_release = Define`
    is_release n = case n.order of
        RELEASE => (n.operation = Wr) ∨ (n.operation = Fn)
      | ACQ_REL => (n.operation = Wr) ∨ (n.operation = Fn)
      | SEQ_CST => (n.operation = Wr) ∨ (n.operation = Fn)
      | _       => F`;

val is_atomic = Define`
    is_atomic n = (n.order <> NOT_ATOMIC)`;

val same_thread = Define`
    same_thread A B = (A.thread_id = B.thread_id)`;

val same_address = Define`
    same_address A B = (A.address = B.address)`;

val reads_from = Define`
    reads_from g A B = (FLOOKUP g.rf A = SOME B)`;





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
(* reads_from *)               [✓]

 * receive                     [~]
 * resolve                     [~]

 ? Undefined behaviour         [?]



Questions, notes:

 * Are Hol_defns okay? Proving termination? Insert empty node.
 * Is release_sequence_of dependent on the Modification order? -> Circular logic?  
 * Does the release sequence include the head?

 *)



(* PRIMITIVES: mod, po, dep *)
val ordered_before = Define`
    ordered_before g A B = ( (A IN g.nodes) ∧ (B IN g.nodes) ∧ (A.timestamp < B.timestamp))`;

val modifies_before = Define`
    modifies_before g A B = ( (ordered_before g A B) ∧ (same_address A B) )`;

val sequenced_before = Define`
    sequenced_before g A B = ((ordered_before g A B) ∧ (same_thread A B)  )`;

val release_sequence_of = Define` (* TODO: include read-write ops *)
    release_sequence_of g A = { B | (B = A) ∨ ((modifies_before g A B) ∧ (is_atomic B) ∧ (is_store B) ∧ ((sequenced_before g A B) ∨ (F) )  )}   `;

val (cdep_rules, cdep_ind, cdep_cases) = Hol_reln`
    (∀ g B A. (A.mid IN B.ddeps) ==> (carries_dependency_to g B A)) ∧
    (∀ g B A. (∃ X. (sequenced_before g A X) ∧ (sequenced_before g X B) ∧ (is_store X) ∧ (is_load B) ∧ (same_address X B) ∧ (A.mid IN X.ddeps)) ==> (carries_dependency_to g B A)) ∧
    (∀ g B A. (∃ X. (carries_dependency_to g A X) ∧ (carries_dependency_to g X B)) ==> (carries_dependency_to g B A) )`;

val synchronizes_with = Define`
    synchronizes_with g A B = ( (ordered_before g A B) ∧
        (*1.*) ( (is_release A) ∧ (is_acquire B) ∧ (same_address A B) ∧ (∃ X. (reads_from g B X ) ∧ (X IN release_sequence_of g A)) ) ∨
        (*2.*) ( (is_release A) ∧ (is_acquire B) ∧ (is_fence A) ∧ (is_fence B) ∧ (∃ X Y. (is_atomic X) ∧ (is_atomic Y) ∧ (same_address X Y) ∧ (sequenced_before g A X) ∧ (is_store X) ∧ (sequenced_before g Y B) ∧ ( (reads_from g Y X) ∨ (∃ Z. (reads_from g Y Z) ∧ (Z IN release_sequence_of g X)))) ) ∨
        (*3.*) ( (is_release A) ∧ (is_acquire B) ∧ (is_fence A) ∧ (∃ X. (sequenced_before g A X) ∧ (same_address B X) ∧ ((reads_from g B X) ∨ (∃ Z. (reads_from g B Z) ∧ (Z IN release_sequence_of g X))) ) ) ∨
        (*4.*) ( (is_atomic A) ∧ (is_release A) ∧ (is_acquire B) ∧ (is_fence B) ∧ (∃ X. (same_address A X) ∧ (sequenced_before g X B) ∧ ((reads_from g B A) ∨ (∃ Z. (reads_from g B Z) ∧ (Z IN release_sequence_of g X))  ))  ) ∨ (* TODO *)
        (*5. A is the creation of a thread and B is the beginning of the execution of the new thread. *) (F) ∨
        (*6. A is a futex wake operation and B is the next operation after the futex wait operation of the thread woken up by A. *) (F)   )`;

val (dob_rules, dob_ind, dob_cases) = Hol_reln`
      (*1.*) ((∀ A B g. (A IN g.nodes) ∧ (B IN g.nodes) ∧ (is_release A) ∧ (modifies_before g A B) ∧ ~(same_thread A B) ∧ (is_consume B) ∧ (∃ X. (X IN (release_sequence_of g A)) ∧ (reads_from g B X) )) ==> dob g A B  ) ∧
      (*2.*) ((∀ A B g X. (dependency_ordered_before g A X) ∧ (carries_dependency_to g X B)) ==> dependency_ordered_before g A B)   `;


val (ithb_rules, ithb_ind, ithb_cases) = Hol_reln`
    (* A.  *) ( ∀ g A B  . (synchronizes_with g A B) ==> (interthread_happens_before g A B)) ∧
    (* B.  *) ( ∀ g A B  . (dependency_ordered_before g A B) ==> (interthread_happens_before g A B)) ∧
    (* C.1 *) ( ∀ g A B X. ((synchronizes_with g A X) ∧ (suquenced_before g X B)) ==> (interthread_happens_before g A B)) ∧
    (* C.2 *) ( ∀ g A B X. ((sequenced_before g A X) ∧ (interthread_happens_before g X B)) ==> (interthread_happens_before g A B)) ∧
    (* C.3 *) ( ∀ g A B X. ((interthread_happens_before g A X) ∧ (interthread_happens_before g X B)) ==> (interthread_happens_before g A B))  )`;

val happens_before = Define`
    happens_before g A B = (
      (*1.*) (sequenced_before g A B) ∨
      (*2.*) (interthread_happens_before g A B)   )`;

val visible_to = Define`
    visible_to g A B = (
      (*1.*) (happens_before g A B) ∧
      (*2.*) ~(∃ X. (happens_before g A X) ∧ (happens_before g X B))   )`;

(* TODO: fix to only look at writes and only return a set given a read *)
val in_visible_sequence_of = Define` (* TODO: fix to only look at writes and only return a set given a read? *)
    in_visible_sequence_of g A B =
      let visible_sequence X = { nd | (nd.address = X.address) ∧
                                      (      (visible_to g nd X) ∨ (* The first in sequence *)
                                             (    ~(happens_before g X nd) ∧
                                                   (∃fs. (visible_to g fs X) ∧
                                                        (modifies_before g fs nd))))} (* the rest *)
      in A IN (visible_sequence B)    `;

val can_read_from = Define`
    can_read_from g A B = (
      (~(is_atomic A) ∧ ~(is_atomic B) ∧ (visible_to g B A) ) ∨             (* non-atomic *)
      ( (is_atomic A) ∧  (is_atomic B) ∧ (in_visible_sequence_of g B A) ) ∨ (* atomic *)
      ( F )                                                                       (* undefined combinations? *)  )`;







(*******************************************)
(* TODO: Probably not the best way to this *)
(*******************************************)
val UNSOME = Define`
    UNSOME (SOME x) = x
`;



(*******************************************************************************)
(* Everything above is building up to these two relations, receive and resolve *)
(*******************************************************************************)

(* Receive input message, create new nodes from these messages *)
val receive = Define`
    receive (inGraph, (msg, ttid)) graph' = let new_time = LEAST n. ~(∃ nd. (nd.timestamp = n) ∧ (nd IN inGraph.nodes) ) in case msg of
      Read a' id order' dep => let new_node = <| operation := Rd ;
                                             address := a' ;
                                             timestamp := new_time ;
                                             values := NONE ;
                                             mid := id ;
                                             thread_id := ttid ;
                                             order := order' ;
                                             ddeps := dep |>
                           in (graph' = inGraph with nodes updated_by (λlst. {new_node} UNION lst))

    | Write a' vl order' dep => let new_node = <| operation := Rd ;
                                              address := a' ;
                                              timestamp := new_time ;
                                              values := SOME vl ;
                                              mid := LEAST n. ~(∃ nd. (nd.mid = n) ∧ (nd IN inGraph.nodes) ) ;
                                              thread_id := ttid ;
                                              order := order' ;
                                              ddeps := dep |>
                           in (graph' = inGraph with nodes updated_by (λlst. {new_node} UNION lst))
`;

(* TODO: output message *)
val resolve = Define`
    resolve g1 (msg, g2) = ∃ w r. (w IN g1.nodes) ∧ (r IN g1.nodes) ∧ (g1.nodes = g2.nodes) ∧ (* TODO: maybe update r's value? *)
                                      (can_read_from g1 w r) ∧ (g2.rf = g1.rf |+ (r, w)) ∧
                                      (msg = Out (UNSOME w.values) (r.mid) (r.thread_id))
`;

val _ = export_theory();








(*

Here lie the old Hol_defns, to be removed when the Hol_relns are confirmed and checked.


val dependency_ordered_before = Hol_defn "dependency_ordered_before" `
    dependency_ordered_before g A B = ( (A IN g.nodes) ∧ (B IN g.nodes) ∧
        (*1.*) ( (is_release A) ∧ (same_address A B) ∧ ~(same_thread A B) ∧ (is_consume B) ∧ (∃ X. (X IN (release_sequence_of g A)) ∧ (reads_from g B X) )) ∨
        (*2.*) (∃ X. (dependency_ordered_before g A X) ∧ (carries_dependency_to g X B))     )`;


(* TODO: turn into Hol_reln *)
val carries_dependency_to = Hol_defn "carries_dependency_to" `
    carries_dependency_to g B A = (
      (*1.*) (A.mid IN B.ddeps) ∨
      (*2.*) (∃ X. (sequenced_before g A X) ∧ (sequenced_before g X B) ∧ (is_store X) ∧ (is_load B) ∧ (same_address X B) ∧ (A.mid IN X.ddeps)) ∨
      (*3.*) (∃ X. (carries_dependency_to g A X) ∧ (carries_dependency_to g X B))   )`;


val interthread_happens_before = Hol_defn "interthread_happens_before" `
    (interthread_happens_before g A B) = ( (A IN g.nodes) ∧ (B IN g.nodes) ∧ (
      (*A.*) (synchronizes_with g A B) ∨
      (*B.*) (dependency_ordered_before g A B) ∨
      (*C.*) (∃ X. X IN g.nodes ∧
               (*1.*) (( synchronizes_with g A X ∧ sequenced_before g X B) ∨
               (*2.*) ( sequenced_before g A X ∨ interthread_happens_before g X B) ∨ 
               (*3.*)( interthread_happens_before g A X ∨ interthread_happens_before g X B)))   ))`;


*)

