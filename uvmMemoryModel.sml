
open HolKernel Parse boolLib bossLib;

open uvmThreadSemanticsTheory;

val _ = new_theory "uvmMemoryModel";

val _ = type_abbrev("input", ``:(memoryMessage, tid)``);
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
    order     : memoryorder
  |>`

val _ = Datatype`
  model = <|
          nodes : node list ; (*set*)
             sw : node |-> node
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



(* Define program order *)
set_fixity "sequenced_before" (Infix(NONASSOC,450));
val sequenced_before = Define`
    (n1 sequenced_before n2) = ((n1.thread_id = n2.thread_id) ∧ (n1.timestamp < n2.timestamp))
`;

(* TODO: fences *)
set_fixity "synchronizes_with" (Infix(NONASSOC,450));
val synchronizes_with = Define`
    (n1:node synchronizes_with n2:node) = ((n1.address = n2.address) ∧ (* same address *)
                                 (is_release n1) ∧ (is_acquire n2) ∧ (* a,b are a release,acquire resp. *)
                                 (* a doesn't synchronize with anything else ∧ --> covered in actual graph *)
                                 (n1.timestamp < n2.timestamp) ∧ (* ??? when is timestamp assigned? does this imply visibility? *)
                                 (n1.thread_id <> n2.thread_id)) (* different threads *)
`;

(* The combination of `sequenced_before` and `synchronises_with`  *)
set_fixity "happens_before" (Infix(NONASSOC,450));
val happens_before = Define`
  (n1 happens_before n2) = let (either a b) = ((a sequenced_before b) ∨ (a synchronizes_with b))
                            in (either^+) n1 n2
`;


(* TODO: fix set of sync_with with set of read_from *)
val model_add = Define`
    model_add m node' = let m' = m with sw updated_by (λmap. case some n2. ( (n2 synchronizes_with node') ∧ ~(∃n3. m.sw ' n2 = n3)) of
                           NONE => map
                         | SOME n2 => map |+ (n2, node')) in
                       let m'' = m' with nodes updated_by (λnds. node'::nds) in
                       m''
`;

val model_hb = Define`
    model_hb m n1 n2 = let (sync_with a b) = (FLOOKUP m.sw a = SOME b) in
                       let (either a b) = ((sync_with a b) ∨ (a sequenced_before b)) in
                       (MEM n1 m.nodes) ∧ (MEM n2 m.nodes) ∧ ( (either^+) n1 n2)
`;


val _ = export_theory();
