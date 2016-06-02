open HolKernel Parse boolLib bossLib;
load "../uvmSystemTheory";
open uvmSystemTheory;
open uvmMemoryModelTheory;
open lcsymtacs;

val _ = new_theory "testMemoryModel";



(* I define an alternate receive that's not a relation *)
val receive' = Define`
    receive' inGraph (msg,ttid) = case msg of
      Read a' id order' dep => let new_node = <| operation := Rd ; address := a' ;
                                             values := NONE      ; mid := id ;
                                             thread_id := ttid   ; order := order' ;
                                             ddeps := dep |>
                               in inGraph with nodes updated_by (λlst. lst ++ [new_node])
    | Write a' id vl order' dep => let new_node = <| operation := Wr ;
                                              address := a'   ; values := SOME vl ;
                                              mid := id       ; thread_id := ttid ;
                                              order := order' ; ddeps := dep |>
                           in inGraph with nodes updated_by (λlst. lst ++ [new_node])  `;

val resolve' = Define`
    resolve' g A B = g with rf updated_by (λm. m |+ (A, B)) `;

Define `empty = <| nodes:=[]; rf:=FEMPTY |>`;

(* Abbreviation for defining 8-bit Ints *)
val n = Define`n m = (IntV m 8)`;







(* EXAMPLE 0: orderedBefore, modifiesBefore, sequencedBefore *)
Define `g0= FOLDL (receive') empty
         [
            ( Write 10 0 (n 11) NOT_ATOMIC {} , 0) ;
            ( Read  10 1        SEQ_CST    {} , 1) ;
            ( Write 10 2 (n 12) SEQ_CST    {} , 1) ;
            ( Write 10 3 (n 13) NOT_ATOMIC {} , 1)
         ]`;
Define `w0_0 = (EL 0 g0.nodes)`; Define `r0_1 = (EL 1 g0.nodes)`; Define `w0_2 = (EL 2 g0.nodes)`;
Define `w0_3 = (EL 3 g0.nodes)`;
(* orderedBefore *)
val g0_ob0 = prove(``orderedBefore g0 r0_1 w0_2``, EVAL_TAC);
val g0_ob1 = prove(``orderedBefore g0 w0_0 r0_1``, EVAL_TAC);
val g0_ob2 = prove(``~orderedBefore g0 r0_1 w0_0``, EVAL_TAC);
(* modifiesBefore *)
val g0_mb0 = prove(`` modifiesBefore g0 w0_2 w0_3``, EVAL_TAC);
val g0_mb1 = prove(`` modifiesBefore g0 w0_0 w0_2``, EVAL_TAC);
val g0_mb3 = prove(`` modifiesBefore g0 w0_0 w0_3``, EVAL_TAC);
val g0_mb2 = prove(``~modifiesBefore g0 w0_0 r0_1``, EVAL_TAC);
(* sequencedBefore *)
val g0_sb1 = prove(`` sequencedBefore g0 r0_1 w0_2 ``, EVAL_TAC);
val g0_sb2 = prove(`` sequencedBefore g0 w0_2 w0_3 ``, EVAL_TAC);
val g0_sb3 = prove(`` sequencedBefore g0 r0_1 w0_3 ``, EVAL_TAC);
val g0_sb0 = prove(``~sequencedBefore g0 w0_0 r0_1 ``, EVAL_TAC);



(* EXAMPLE 1: sequencedBefore     (taken from UCAM, p. 3) *)
Define `g1'= FOLDL (receive') empty
         [                                                (* int main() {   *)
           ( Write 10 0 (n 2) NOT_ATOMIC    {} , 1 ) ;    (*   int x = 2    *)
           ( Write 20 1 (n 0) NOT_ATOMIC    {} , 1 ) ;    (*   int y = 0    *)
           ( Read  10 2       NOT_ATOMIC    {} , 1 ) ;    (*   y = (x == x) *)
           ( Read  10 3       NOT_ATOMIC    {} , 1 ) ;
           ( Write 20 4 (n 1) NOT_ATOMIC {2;3} , 1 )
         ]`;                                          (*   return 0;    *)
Define `w1_0 = (EL 0 g1'.nodes)`; Define `w1_1 = (EL 1 g1'.nodes)`; Define `r1_2 = (EL 2 g1'.nodes)`;
Define `r1_3 = (EL 3 g1'.nodes)`; Define `w1_4 = (EL 4 g1'.nodes)`;
Define `g1'' = resolve' g1'  r1_2 w1_0`;
Define `g1   = resolve' g1'' r1_3 w1_0`;
(* sequencedBefore *)
val g1_sb0 = prove(`` sequencedBefore g1 w1_0 w1_1``,EVAL_TAC);
val g1_sb1 = prove(`` sequencedBefore g1 w1_1 r1_2``,EVAL_TAC);
val g1_sb2 = prove(`` sequencedBefore g1 w1_1 r1_3``,EVAL_TAC);
val g1_sb3 = prove(`` sequencedBefore g1 r1_2 w1_4``,EVAL_TAC);
val g1_sb4 = prove(`` sequencedBefore g1 r1_3 w1_4``,EVAL_TAC);
(* isReadBy *)
val g1_rf0 = prove( ``isReadBy g1 w1_0 r1_2``, EVAL_TAC);
val g1_rf1 = prove( ``isReadBy g1 w1_0 r1_3``, EVAL_TAC);


(* Example 2: Data Race      (taken from UCAM, p. 3) *)
Define `g2 = FOLDL (receive') empty
         [                                                (* int main() {   *)
           ( Write 10 0 (n 2) NOT_ATOMIC    {} , 1 ) ;    (*   int x = 2    *)
           ( Write 10 1 (n 3) NOT_ATOMIC    {} , 2 ) ;    (*   {{{ x = 3    *)
           ( Read  10 2       NOT_ATOMIC    {} , 3 )      (*   ||| x?       *)
         ]`;                                              (*   }}}          *)
Define `w2_0 = (EL 0 g2.nodes)`; Define `w2_1 = (EL 1 g2.nodes)`; Define `r2_2 = (EL 2 g2 .nodes)`;
val g2_datarace = prove(
    ``dataRace g2 w2_1 r2_2``,
        rw [dataRace_def] THENL [
            EVAL_TAC,
            EVAL_TAC,
            EVAL_TAC,
            rw [happensBefore_def] THENL [
                EVAL_TAC,
                rw [Once ithb_cases] THENL [
                    EVAL_TAC,
                    rw [Once dob_cases] >> EVAL_TAC,
                    rw [carriesDependencyTo_def,orderedBefore_def] >> EVAL_TAC,
                    cheat, (* ithb - how can I Cases_on 'X'? *)
                    cheat (* ithb *)
                    ]
                ],
            rw[ happensBefore_def] THENL [
                EVAL_TAC,
                cheat (* ithb *)
                ]
            ]
);




(* EXAMPLE 3: sequencedBefore     (taken from UCAM, p. 3) *)
(*Define `g= FOLDL (receive') empty
         [                                                (* int main() {   *)
           ( Write 10 0 (n 2) NOT_ATOMIC    {} , 1 ) ;    (*   int x = 2    *)
           ( Write 20 1 (n 0) NOT_ATOMIC    {} , 1 ) ;    (*   int y = 0    *)
           ( Read  10 2       NOT_ATOMIC    {} , 1 ) ;    (*   y = (x == x) *)
           ( Read  10 3       NOT_ATOMIC    {} , 1 ) ;
           ( Write 20 4 (n 1) NOT_ATOMIC {2;3} , 1 )
         ]`;                                          (*   return 0;    *)
Define `w1_0 = (EL 0 g1'.nodes)`; Define `w1_1 = (EL 1 g1'.nodes)`; Define `r1_2 = (EL 2 g1'.nodes)`;
Define `r1_3 = (EL 3 g1'.nodes)`; Define `w1_4 = (EL 4 g1'.nodes)`;
Define `g1'' = resolve' g1'  r1_2 w1_0`;
Define `g1   = resolve' g1'' r1_3 w1_0`;*)









(* releaseSequenceOf *)



(* carriesDependencyTo *)
Define `g4= FOLDL (receive') empty
         [
            ( Read  10 0       ACQUIRE    {} , 1) ;
            ( Write 20 1 (n 1) RELAXED   {0} , 1)
]`;
Define `r4_0 = (EL 0 g4.nodes)`; Define `w4_1 = (EL 1 g4.nodes)`;

val cd_rel0 = prove(``carriesDependencyTo g4 r4_0 w4_1``, EVAL_TAC);



(* synchronizesWith *)
Define `g5'= FOLDL (receive') empty
         [
            ( Write 10 0 (n 1) NOT_ATOMIC {} , 0) ;
            ( Write 20 1 (n 1) RELEASE    {} , 0) ;
            ( Read  20 2       ACQUIRE    {} , 1) ;
            ( Read  10 3       NOT_ATOMIC {} , 1)
]`;
Define `w5_0 = (EL 0 g5'.nodes)`; Define `w5_1 = (EL 1 g5'.nodes)`;
Define `r5_2 = (EL 2 g5'.nodes)`; Define `r5_3 = (EL 3 g5'.nodes)`;
Define `g5 = resolve' g5' r5_2 w5_1`; 
val sw_rel0 = prove(`` sequencedBefore  g5 w5_0 w5_1 ``, EVAL_TAC );
val sw_rel1 = prove(`` synchronizesWith g5 w5_1 r5_2 ``,
    RW_TAC (srw_ss()) [synchronizesWith_def] THEN
    `isRelease w5_1 ∧ isAcquire r5_2 ∧ sameAddress w5_1 r5_2` by EVAL_TAC THEN
    `isReadBy g5 r5_2 w5_1 ∧ inReleaseSequenceOf g5 w5_1 w5_1` by EVAL_TAC THEN
    METIS_TAC []);
val sw_rel2 = prove(`` sequencedBefore  g5 r5_2 r5_3 ``, EVAL_TAC );
val sw_rel4 = prove(``(happensBefore g5 w5_0 r5_3)``,
                    RW_TAC (srw_ss()) [happensBefore_def,ithb_rules] THEN
                    `synchronizesWith g5 w5_1 r5_2` by RW_TAC (srw_ss()) [sw_rel1] THEN
                    `sequencedBefore g5 r5_2 r5_3` by EVAL_TAC THEN
                    `sequencedBefore g5 w5_0 w5_1` by EVAL_TAC THEN
                    METIS_TAC [sw_rel1, ithb_rules] );
val sw_unrel_5 = prove( `` ~(synchronizesWith g5 w5_0 w5_1) ``, EVAL_TAC);



(* dependencyOrderedBefore *)
Define `g6'= FOLDL (receive') empty
         [
            ( Write 10 0 (n 1) RELEASE    {} , 0) ;
            ( Write 10 1 (n 2) RELAXED    {} , 0) ;
            ( Read  10 2       ACQUIRE    {} , 1) ;
            ( Write 20 3 (n 3) RELAXED   {2} , 1)
]`;
Define `w6_0 = (EL 0 g6'.nodes)`; Define `w6_1 = (EL 1 g6'.nodes)`;
Define `r6_2 = (EL 2 g6'.nodes)`; Define `r6_3 = (EL 3 g6'.nodes)`;
Define `g6 = resolve' g6' r6_2 w6_1`; 
(*val do_rel0 = prove(``dependencyOrderedBefore g6 w6_1 r6_2``, );
val do_self = prove(`` ∀ nd g. ~dependencyOrderedBefore g nd nd``, );*)



(* interthreadHappensBefore *)
Define `g7'= FOLDL (receive') empty
         [
            ( Write 10 0 (n 1) NOT_ATOMIC {} , 0) ;
            ( Write 20 1 (n 1) RELEASE    {} , 0) ;
            ( Read  20 2       ACQUIRE    {} , 1) ;
            ( Read  10 3       NOT_ATOMIC {} , 1)
]`;



(* happensBefore *)
Define `g8 = FOLDL (receive') empty
         [
            ( Write 1024 0 (n 11) SEQ_CST    {} , 1) ;
            ( Read  1024 1        SEQ_CST    {} , 1) ;
            ( Write 1024 2 (n 10) SEQ_CST    {} , 1)
         ]`;
Define `w8_0 = (EL 0 g8.nodes)`; Define `r8_1 = (EL 1 g8.nodes)`; Define `w8_2 = (EL 2 g8.nodes)`;
val hb_rel0 = prove( `` happensBefore g8 w8_0 r8_1``, EVAL_TAC);



(* visibleTo *)
Define `g9= FOLDL (receive') empty
         [
            ( Write 10 0 (n 1) NOT_ATOMIC    {} , 0) ;
            ( Write 10 1 (n 2) NOT_ATOMIC    {} , 0) ;
            ( Read  10 2       NOT_ATOMIC    {} , 1)
]`;
Define `w9_0 = (EL 0 g9.nodes)`; Define `w9_1 = (EL 1 g9.nodes)`;
Define `r9_2 = (EL 2 g9.nodes)`;



(* inVisibleSequenceOf *)



(* canReadFrom*)
Define `g11= FOLDL (receive') <| nodes:=[]; rf:=FEMPTY |>
         [
            ( Write 1024 0 (n 11) SEQ_CST    {} , 1) ;
            ( Read  1024 1        SEQ_CST    {} , 1) ;
            ( Write 1024 2 (n 10)  SEQ_CST    {} , 1)
         ]`;
Define `w11_0 = (EL 0 g11.nodes)`; Define `r11_1 = (EL 1 g11.nodes)`; Define `w11_2 = (EL 2 g11.nodes)`;



(* SEQ_CST *)
(*
int main() {
  atomic_int x;
  x.store(2);
  int y = 0;
  {{{ x.store(3);
  ||| y = ((x.load())==3);
  }}};
  return 0; }       

       *)

Define `cg4= FOLDL (receive') empty
         [
           ( Write 10 0 (n 2) SEQ_CST       {} , 0 ) ;
           ( Write 20 1 (n 2) NOT_ATOMIC    {} , 0 ) ;
           ( Read  10 2   SEQ_CST       {} , 2 ) ;
           ( Write 10 3 (n 3) SEQ_CST       {} , 1 ) ;
           ( Write 20 4 (n 0) NOT_ATOMIC   {3} , 2 )
         ]`;

Define `cw4_0 = (EL 0 cg4.nodes)`;
Define `cw4_1 = (EL 1 cg4.nodes)`;
Define `cr4_2 = (EL 2 cg4.nodes)`;
Define `cw4_3 = (EL 3 cg4.nodes)`;
Define `cw4_4 = (EL 4 cg4.nodes)`;


val cg4_rel0 = prove( ``sequencedBefore cg4 cw4_0 cw4_1``,EVAL_TAC );
val cg4_rel2 = prove( ``sequencedBefore cg4 cr4_2 cw4_4``, EVAL_TAC );

(*
val cg4_rel1 = prove(
      ``sequentiallyConsistent cg4 cw4_0 cr4_2``,
      RW_TAC (srw_ss()) [sequentiallyConsistent_def]
      ...
*)

(* }}} *)





val _ = export_theory();
