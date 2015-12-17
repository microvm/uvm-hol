
open HolKernel Parse boolLib bossLib;

open uvmThreadSemanticsTheory;

val _ = new_theory "uvmMemoryModel";

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
    deps      : memdeps
  |>`

val _ = Datatype`
  graph = <|
          nodes : node set ;
             rf : node |-> node
          |>`;

val is_fence = Define`
    is_fence n = (n.operation = Fn)
`;

val is_load = Define`
    is_load n = (n.operation = Rd)
`;

val is_store = Define`
    is_store n = (n.operation = Wr)
`;

val is_acquire = Define`
    is_acquire n = case n.order of
        ACQUIRE => (n.operation = Rd) ∨ (n.operation = Fn)
      | ACQ_REL => (n.operation = Rd) ∨ (n.operation = Fn)
      | SEQ_CST => (n.operation = Rd) ∨ (n.operation = Fn)
      | CONSUME => (n.operation = Fn)
      | _       => F
`;

val is_consume = Define`
    is_consume n = ((n.operation = Rd) ∧ (n.order <> NOT_ATOMIC) ∧ (n.order <> RELAXED)) (* or (n.order=CONSUME) *)
`;

val is_release = Define`
    is_release n = case n.order of
        RELEASE => (n.operation = Wr) ∨ (n.operation = Fn)
      | ACQ_REL => (n.operation = Wr) ∨ (n.operation = Fn)
      | SEQ_CST => (n.operation = Wr) ∨ (n.operation = Fn)
      | _       => F
`;

val is_atomic = Define`
    is_atomic n = (n.order <> NOT_ATOMIC)
`;

val same_thread = Define`
    same_thread A B = (A.thread_id = B.thread_id)
`;

val reads_from = Define`
    reads_from A B inGraph = (FLOOKUP inGraph.rf A = SOME B)
`;

(* Program order: Evaluations in the same thread  *)
val sequenced_before = Define`
    (sequenced_before A B inGraph) = ((A.thread_id = B.thread_id) ∧ (A.timestamp < B.timestamp) ∧ (A IN inGraph.nodes) ∧ (B IN inGraph.nodes))
`;


val in_release_sequence_of = Define`
    in_release_sequence_of A B inGraph = (F) (*TODO*)
`;

(* An evaluation A synchronises with another evaluation B if: (M is a memory location)
     1. A does a release op on M. B does an acquire op on M. B sees a value stored by an op in the release sequence headed by A, or
     2. A is a release fence, and, B is an acquire fence, and, there exist atomic X and Y, both on location M, such that A is sequenced before X, X store into M, Y is sequenced before B, and Y sees the value written by X or a value written by any store operation in the hypothetical release sequence X would head if it were a release operation, or
     3. A is a release fence, and, B is an atomic op that performs an acquire operation on M, and, ∃ atomic op X s.t A is sequenced before X, X stores into M, and B sees the value written by X or a value written by any store operations in the hypothetical release sequence X would head if it were a release operation, or
     4. A is an atomic op that performs a release operation on M, and, B is an acquire fence, and, there exists some atomic operation X on M such that X is sequenced before B and sees the value written by A or a value written by any side effect in the release sequence headed by A, or
     5. A is the creation of a thread and B is the beginning of the execution of the new thread.
     6. A is a futex wake operation and B is the next operation after the futex wait operation of the thread woken up by A.
 *)
val synchronizes_with = Define`
    (synchronizes_with A B inGraph) = ((A IN inGraph.nodes) ∧ (B IN inGraph.nodes) ∧  (*(A.timestamp < B.timestamp)*)
                   ( (A.address = B.address) ∧ (is_release A) ∧ (is_acquire B) ∧ (reads_from A B inGraph) ) ∨
                   ( (is_fence A) ∧ (is_release A) ∧ (is_fence B) ∧ (is_acquire B) ∧
                     (∃ X Y M. (is_atomic X) ∧ (is_atomic Y) ∧ (X.address = M) ∧ (Y.address = M) ∧ (sequenced_before A X inGraph) ∧ (sequenced_before Y B inGraph) ∧ (reads_from Y X inGraph))) ∧
                   ( F ) (* TODO: fences, futex *))
`;

(* A memory operation B depends on A if:
     1. The data value of A is used as a data argument of B (given through deps)
     2. The address of A has been written to by B (okay, but possibly wrong. TODO: fix this)
     3. B depends on X and X depends on A
*)
val deps_of = Define`
  deps_of (msg, ttid) inGraph = case msg of                 (* same thread *)       (* same addr *)      (* most recent *)
      Read a' id order dep => let tmp = dep UNION {nd.mid | (nd.thread_id = ttid) ∧ (nd.address = a') ∧ ~(∃nd2. nd2.timestamp>nd.timestamp) }
                              in { nd.mid | (nd.mid IN tmp) ∨ (∃nd2. (nd.mid IN nd2.deps) ∧ (nd2.mid IN tmp)) }
    | Write a' vl order dep => { nd.mid | (nd.mid IN dep) ∨ (∃ nd2. (nd.mid IN nd2.deps) ∧ (nd2.mid IN dep))}
`;
val carries_dependency_to = Define`
    carries_dependency_to A B inGraph = (
                               (A IN inGraph.nodes) ∧ (B IN inGraph.nodes) ∧
                               (B.mid IN A.deps)
)`; 

(* A is dependency-ordered before B if:
     1. A does a release op on M. in another thread, B does a consume op on M. B sees a value stored by any store ops in the release sequence headed by A. OR
     2. For some X, A is dependency-ordered before X and X carries a dependency to B.
*)
val dependency_ordered_before = Hol_defn "dependency_ordered_before" `
    dependency_ordered_before A B inGraph = ( (A IN inGraph.nodes) ∧ (B IN inGraph.nodes) ∧
                                                               
                  (*1.*) (synchronizes_with A B inGraph) ∨ (* TODO: is this right? No. *)
                (*  (*1.*) ( (is_release A) ∧ (A.address = B.address) ∧ ~(same_thread A B) ∧ (is_consume B) ) (*TODO*) *)
                  (*2.*) (∃ X. (dependency_ordered_before A B inGraph) ∧ (carries_dependency_to X B inGraph))
                  
)`;

(* An evaluation A inter-thread happens before an evaluation B if A synchronises with B, A is dependency-ordered before B, or, for some evaluation X:
    1. A synchronises with X and X is sequenced before B,
    2. A is sequenced before X and X inter-thread happens before B, or
    3. A inter-thread happens before X and X inter-thread happens before B.
*)
val interthread_happens_before = Hol_defn "interthread_happens_before" `
    (interthread_happens_before A B inGraph) = (
      (A IN inGraph.nodes) ∧ (B IN inGraph.nodes) ∧
      (synchronizes_with A B inGraph) ∨
      (dependency_ordered_before A B inGraph) ∨
      (∃ X. X IN inGraph.nodes ∧
            (( synchronizes_with A X inGraph ∧ sequenced_before X B inGraph) ∨
            ( sequenced_before A X inGraph ∨ interthread_happens_before X B inGraph) ∨ 
            ( interthread_happens_before A X inGraph ∨ interthread_happens_before X B inGraph)))
)`;

(* An evaluation A happens before an evaluation B if A is sequenced before B or A inter-thread happens before B. *)
val happens_before = Define`
    (happens_before A B inGraph) = (
      (A IN inGraph.nodes) ∧ (B IN inGraph.nodes) ∧
      (sequenced_before A B inGraph) ∨
      (interthread_happens_before A B inGraph)
)`;

(* A visible store operation A to a memory location M with respect to a load operation B from M satisfies the conditions:
     1. A happens before B, and
     2. There is no other store operation X to M such that A happens before X and X happens before B.
*)
val visible_to = Define`
    visible_to A B inGraph = ( (A IN inGraph.nodes) ∧ (B IN inGraph.nodes) ∧
                               (happens_before A B inGraph) ∧
                               ~(∃ X. (happens_before A X inGraph) ∧ (happens_before X B inGraph)))
`;

(* From C++11:

*)
val must_modify_before = Hol_defn "must_modify_before" `
    must_modify_before A B inGraph = (
      (A IN inGraph.nodes) ∧ (is_atomic A) ∧ (is_store A) ∧
      (B IN inGraph.nodes) ∧ (is_atomic B) ∧ (is_store B) ∧
      (A <> B) ∧
      (

        (happens_before A B inGraph) ∨                                                                (* write-write coherence *)
        (∃ X Y. (reads_from X A inGraph) ∧ (reads_from Y B inGraph) ∧ (happens_before X Y inGraph)) ∨ (* read-read coherence *)
        (∃ X.   (reads_from X A inGraph) ∧ (happens_before X B inGraph)) ∨                            (* read-write coherence *)
        (∃ X.   (happens_before A X inGraph) ∧ (reads_from X B inGraph)) ∨                            (* write-read coherence *)
      
      
        (∃ X. (must_modify_before A X inGraph) ∧ (must_modify_before X B inGraph))                    (* ^* *)
        
      (* ((A.timestamp < B.timestamp) ∧ (same_thread A B) ∧ ((is_acquire A) ∨ (is_release B))) ∨       (* release, acquire *) *)
      (* (F) (*TODO: is this complete? *) ∨ *)
    ))
`;

val can_modify_afer = Define`
    can_modify_after A B inGraph = ((A<>B) ∧ ~(must_modify_before A B inGraph))
`;

val in_visible_sequence_of = Define`
    in_visible_sequence_of A B inGraph =
      let visible_sequence X = { nd | (nd.address = X.address) ∧
                                      (      (visible_to nd X inGraph) ∨ (* The first in sequence *)
                                             (    ~(happens_before X nd inGraph) ∧
                                                   (∃fs. (visible_to fs X inGraph) ∧
                                                         (can_modify_after nd fs inGraph)
                                                   )
                                             )
                                      )
                               } (* the rest *)
      in A IN (visible_sequence B)
`;

val can_read_from = Define`
    can_read_from A B inGraph = (
      (~(is_atomic A) ∧ ~(is_atomic B) ∧ (visible_to B A inGraph) ) ∨             (* non-atomic *)
      ( (is_atomic A) ∧  (is_atomic B) ∧ (in_visible_sequence_of B A inGraph) ) ∨ (* atomic *)
      ( F )                                                                       (* undefined combinations? *)
    )
`;







(* TODO: Probably not the best way to this *)
val UNSOME = Define`
    UNSOME (SOME x) = x
`;







(* Everything above is building up to these two relations, receive and resolve *)


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
                                             deps := deps_of (msg,ttid) inGraph |>
                           in (graph' = inGraph with nodes updated_by (λlst. {new_node} UNION lst))

    | Write a' vl order' dep => let new_node = <| operation := Rd ;
                                              address := a' ;
                                              timestamp := new_time ;
                                              values := SOME vl ;
                                              mid := LEAST n. ~(∃ nd. (nd.mid = n) ∧ (nd IN inGraph.nodes) ) ;
                                              thread_id := ttid ;
                                              order := order' ;
                                              deps := deps_of (msg,ttid) inGraph |>
                           in (graph' = inGraph with nodes updated_by (λlst. {new_node} UNION lst))
`;

(* TODO: output message *)
val resolve = Define`
    resolve g1 (msg, g2) = ∃ w r. (w IN g1.nodes) ∧ (r IN g1.nodes) ∧ (g1.nodes = g2.nodes) ∧ (* TODO: maybe update r's value? *)
                                      (can_read_from w r g1) ∧ (g2.rf = g1.rf |+ (r, w)) ∧
                                      (msg = Out (UNSOME w.values) (r.mid) (r.thread_id))
`;

val _ = export_theory();
