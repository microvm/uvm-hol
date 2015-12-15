
open HolKernel Parse boolLib bossLib;

open uvmThreadSemanticsTheory;

val _ = new_theory "uvmMemoryModel";

val _ = type_abbrev("input", ``:(memoryMessage # tid)``);
val _ = Datatype` output_message = Out addr value tid memreqid `;
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

val is_acquire = Define`
    is_acquire n = case n.order of
        ACQUIRE => (n.operation = Rd) ∨ (n.operation = Fn)
      | ACQ_REL => (n.operation = Rd) ∨ (n.operation = Fn)
      | SEQ_CST => (n.operation = Rd) ∨ (n.operation = Fn)
      | CONSUME => (n.operation = Fn)
      | _       => F
`;

val is_consume = Define`
    is_consume n = case n.order of (* or (n.order=CONSUME) *)
       CONSUME => (n.operation = Rd)
     | _       => F
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

val reads_from = Define`
    reads_from A B inGraph = (FLOOKUP inGraph.rf A = SOME B)
`;

(* Program order: Evaluations in the same thread  *)
val sequenced_before = Define`
    (sequenced_before A B inGraph) = ((A.thread_id = B.thread_id) ∧ (A.timestamp < B.timestamp) ∧ (A IN inGraph.nodes) ∧ (B IN inGraph.nodes))
`;

(* TODO: fences, futex, etc. *)
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
                   ( F ) (* TODO *)
)`;

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
    dependency_ordered_before A B inGraph = (
                  (A IN inGraph.nodes) ∧ (B IN inGraph.nodes) ∧
                  (synchronizes_with A B inGraph) ∨
                  (∃ X. (dependency_ordered_before A B inGraph) ∧ (carries_dependency_to X B inGraph))
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




(* Receive input message, create new nodes from these messages *)
val receive_message = Define`
  receive_message (msg, ttid) inGraph : graph = let new_time = LEAST n. ~(∃ nd. (nd.timestamp = n) ∧ (nd IN inGraph.nodes) ) in case msg of
      Read a' id order' dep => let new_node = <| operation := Rd ;
                                             address := a' ;
                                             timestamp := new_time ;
                                             values := NONE ;
                                             mid := id ;
                                             thread_id := ttid ;
                                             order := order' ;
                                             deps := deps_of (msg,ttid) inGraph |>
                           in inGraph with nodes updated_by (λlst. {new_node} UNION lst)

    | Write a' vl order' dep => let new_node = <| operation := Rd ;
                                              address := a' ;
                                              timestamp := new_time ;
                                              values := SOME vl ;
                                              mid := LEAST n. ~(∃ nd. (nd.mid = n) ∧ (nd IN inGraph.nodes) ) ;
                                              thread_id := ttid ;
                                              order := order' ;
                                              deps := deps_of (msg,ttid) inGraph |>
                           in inGraph with nodes updated_by (λlst. {new_node} UNION lst)
`;


(* TODO: output message *)
val resolves_to = Define`
    resolves_to g1 g2 = ∃ w r. (w IN g1.nodes) ∧ (r IN g1.nodes) ∧ (g1.nodes = g2.nodes) ∧ (* TODO: update r's value *)
                               (visible_to w r g1) ∧ (g2.rf = g1.rf |+ (r, w))
`;

val _ = export_theory();
