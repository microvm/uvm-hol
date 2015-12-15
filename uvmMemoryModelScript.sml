
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


(* Program order: Evaluations in the same thread  *)
val sequenced_before = Define`
    (sequenced_before n1 n2 inGraph) = ((n1.thread_id = n2.thread_id) ∧ (n1.timestamp < n2.timestamp) ∧ (n1 IN inGraph.nodes) ∧ (n2 IN inGraph.nodes))
`;

(* TODO: fences, etc. *)
(* An evaluation A synchronises with another evaluation B if: (M is a memory location)
     1. A does a release op on M. B does an acquire op on M. B sees a value stored by an op in the release sequence headed by A, or
     2. A is a release fence, and, B is an acquire fence, and, there exist atomic X and Y, both on location M, such that A is sequenced before X, X store into M, Y is sequenced before B, and Y sees the value written by X or a value written by any store operation in the hypothetical release sequence X would head if it were a release operation, or
     3. A is a release fence, and, B is an atomic op that performs an acquire operation on M, and, ∃ atomic op X s.t A is sequenced before X, X stores into M, and B sees the value written by X or a value written by any store operations in the hypothetical release sequence X would head if it were a release operation, or
     4. A is an atomic op that performs a release operation on M, and, B is an acquire fence, and, there exists some atomic operation X on M such that X is sequenced before B and sees the value written by A or a value written by any side effect in the release sequence headed by A, or
     5. A is the creation of a thread and B is the beginning of the execution of the new thread.
     6. A is a futex wake operation and B is the next operation after the futex wait operation of the thread woken up by A.
*)
val synchronizes_with = Define`
    (synchronizes_with n1 n2 inGraph) = ((n1.address = n2.address) ∧ (* same address *)
                                 (is_release n1) ∧ (is_acquire n2) ∧ (* a,b are a release,acquire resp. *)
                                 (FLOOKUP inGraph.rf n2 = SOME n1) ∧ (* n2 reads from n1 *)
                                 (*(n1.timestamp < n2.timestamp)*)
                                 (n1.thread_id <> n2.thread_id) ∧ (* different threads *)
                                 (n1 IN inGraph.nodes) ∧ (n2 IN inGraph.nodes)) (* Both ops exist *)
`;

(* A memory operation B depends on A if:
     1. The data value of A is used as a data argument of B (given through deps)
     2. The address of A has been written to by B (okay, but slightly wrong. TODO: fix this)
     3. B depends on X and X depends 
*)
val deps_of = Define`
  deps_of (msg, ttid) inGraph = case msg of   (* same thread *) (* same addr *)   (* most recent *)
      Read a' id order dep => let tmp = dep UNION {nd.mid | (nd.thread_id = ttid) ∧ (nd.address = a') ∧ ~(∃nd2. nd2.timestamp>nd.timestamp) }
                              in { nd.mid | (nd.mid IN tmp) ∨ (∃nd2. (nd.mid IN nd2.deps) ∧ (nd2.mid IN tmp)) }
    | Write a' vl order dep => { nd.mid | (nd.mid IN dep) ∨ (∃ nd2. (nd.mid IN nd2.deps) ∧ (nd2.mid IN dep))}
`;
val carries_dependency_to = Define`
    carries_dependency_to n1 n2 inGraph = (n2.mid IN n1.deps)
`;

(* A is dependency-ordered before B if:
     1. A does a release op on M. in another thread, B does a consume op on M. B sees a value stored by any store ops in the release sequence headed by A. OR
     2. For some X, A is dependency-ordered before X and X carries a dependency to B.
*)
val dependency_ordered_before = Hol_defn "dependency_ordered_before" `
   (dependency_ordered_before A B inGraph) =
                  ((synchronizes_with A B inGraph) ∨
                   (∃ X. (dependency_ordered_before A B inGraph) ∧ (carries_dependency_to X B inGraph)))
`;

(* An evaluation A inter-thread happens before an evaluation B if A synchronises with B, A is dependency-ordered before B, or, for some evaluation X:
    1. A synchronises with X and X is sequenced before B,
    2. A is sequenced before X and X inter-thread happens before B, or
    3. A inter-thread happens before X and X inter-thread happens before B.
*)
val interthread_happens_before = Hol_defn "interthread_happens_before" `
    (interthread_happens_before n1 n2 inGraph) =
      ((synchronizes_with n1 n2 inGraph) ∨
       (dependency_ordered_before n1 n2 inGraph) ∨
       (∃ X. X IN inGraph.nodes ∧
             (( synchronizes_with n1 X inGraph ∧ sequenced_before X n2 inGraph) ∨
             ( sequenced_before n1 X inGraph ∨ interthread_happens_before X n2 inGraph) ∨ 
             ( interthread_happens_before n1 X inGraph ∨ interthread_happens_before X n2 inGraph))))
`;


(* An evaluation A happens before an evaluation B if A is sequenced before B or A inter-thread happens before B. *)
val happens_before = Define`
    (happens_before n1 n2 inGraph) =
      ((sequenced_before n1 n2 inGraph) ∨
       (interthread_happens_before n1 n2 inGraph))
`;

(* A visible store operation A to a memory location M with respect to a load operation B from M satisfies the conditions:
     1. A happens before B, and
     2. There is no other store operation X to M such that A happens before X and X happens before B.
*)
val visible_to = Define`
    visible_to n1 n2 inGraph = ((happens_before n1 n2 inGraph) ∧
                               ~(∃ X. (happens_before n1 X inGraph) ∧ (happens_before X n2 inGraph)))
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
