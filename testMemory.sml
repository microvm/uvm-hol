
(*load "uvmThreadSemanticsTheory";*)
load "uvmMemoryModelTheory";
open uvmMemoryModelTheory;
open uvmIRTheory;
(*open optionTheory;*)

(* I define an alternate receive that's not a relation *)
val receive' = Define`
    receive' inGraph (msg,ttid) = case msg of
      Read a' id order' dep => let new_node = <| operation := Rd ;
                                             address := a' ;
                                             values := NONE ;
                                             mid := id ;
                                             thread_id := ttid ;
                                             order := order' ;
                                             ddeps := dep |>
                               in inGraph with nodes updated_by (λlst. lst ++ [new_node])

    | Write a' id vl order' dep => let new_node = <| operation := Wr ;
                                              address := a' ;
                                              values := SOME vl ;
                                              mid := id;
                                              thread_id := ttid ;
                                              order := order' ;
                                              ddeps := dep |>
                           in inGraph with nodes updated_by (λlst. lst ++ [new_node])

`;



(* Relations for UNDEFINED BEHAVIOUR *)
val dataRace_def = Define`
    dataRace g A B = (
      ~(sameThread A B)              ∧
       (sameAddress A B)            ∧
       ( (isStore A) ∨ (isStore B) ) ∧
      ~(happensBefore g A B)         ∧
      ~(happensBefore g B A)
 )`;

(* not possible in uvm-ir? *)
val unsequencedRace_def = Define`
    unsequencedRace g A B = (
       (sameThread A B)              ∧
       (sameAddress A B)            ∧
       ( (isStore A) ∨ (isStore B) ) ∧
      ~(sequencedBefore g A B)       ∧
      ~(sequencedBefore g B A)
)`;




(* Different scenarios to consider:


* orderedBefore            [✓]
* modifiesBefore           [✓]
* sequencedBefore          [✓]
* releaseSequenceOf        [ ]

    T1                    T2
    w1( a1, *, release) 
                          w2( *, *, * )
    w3( a1, *, * )
    w4( a2, *, * )
    w5( a1, *, * )

    Assert that w3,w5 in release sequence of w1, w2 and w4 aren't.

* carriesDependencyTo      [ ]

    T1

* synchronizesWith         [ ]
* dependencyOrderedBefore  [ ]
* interthreadHappensBefore [ ]
* happensBefore            [ ]
* visibleTo                [ ]
* visibleSequenceOf        [ ]
* canReadFrom              [ ]



*)

Define `empty = <| nodes:=[]; rf:=FEMPTY |>`;



(* I'll start with the really easy relations *)

(*           _                _ ___       __             
  ___ _ _ __| |___ _ _ ___ __| | _ ) ___ / _|___ _ _ ___ 
 / _ \ '_/ _` / -_) '_/ -_) _` | _ \/ -_)  _/ _ \ '_/ -_)
 \___/_| \__,_\___|_| \___\__,_|___/\___|_| \___/_| \___|  *)


Define `g0= FOLDL (receive') empty
         [
            ( Write 1024 0 112 NOT_ATOMIC {} , 0) ;
            ( Read  1024 1     SEQ_CST    {} , 1) ;
            ( Write 1024 2 10  SEQ_CST    {} , 1)
         ]`;
Define `w0_0 = (EL 0 g0.nodes)`;
Define `r0_1 = (EL 1 g0.nodes)`;
Define `w0_2 = (EL 2 g0.nodes)`;

(* Specific *)
val ob_sanity_0 = prove(
    ``orderedBefore g0 r0_1 w0_2``,
    EVAL_TAC);
val ob_sanity_1 = prove(
    ``orderedBefore g0 w0_0 r0_1``,
    EVAL_TAC);
val ob_sanity_2 = prove(
    ``~orderedBefore g0 r0_1 w0_0``,
    EVAL_TAC);

(* General *)
val ob_sanity_3 = prove(
    ``∀ g nd. ~orderedBefore g nd nd``,
    RW_TAC arith_ss [orderedBefore_def]);
val ob_sanity_4 = prove(
    ``∀ g nd1 nd2. (orderedBefore g nd1 nd2) ==> ~(orderedBefore g nd2 nd1)``,
    RW_TAC arith_ss [orderedBefore_def]);
val ob_sanity_5 = prove(
    ``∀ g nd1 nd2 nd3. ((orderedBefore g nd1 nd2) ∧ (orderedBefore g nd2 nd3)) ==> (orderedBefore g nd1 nd3)``,
    RW_TAC arith_ss [orderedBefore_def]);

(*              _ _  __ _        ___       __             
  _ __  ___  __| (_)/ _(_)___ __| _ ) ___ / _|___ _ _ ___ 
 | '  \/ _ \/ _` | |  _| / -_|_-< _ \/ -_)  _/ _ \ '_/ -_)
 |_|_|_\___/\__,_|_|_| |_\___/__/___/\___|_| \___/_| \___|  *)

Define `g1= FOLDL (receive') empty
         [
            ( Write 1024 0 112 NOT_ATOMIC {} , 0) ;
            ( Write 9999 1 112 NOT_ATOMIC {} , 0) ;
            ( Write 1024 2 112 NOT_ATOMIC {} , 1) ;
            ( Read  1024 4     SEQ_CST    {} , 0) 
         ]`;
Define `w1_0 = (EL 0 g1.nodes)`;
Define `w1_1 = (EL 1 g1.nodes)`;
Define `w1_2 = (EL 2 g1.nodes)`;
Define `r1_3 = (EL 3 g1.nodes)`;

(* Specific *)
val mb_sanity_0 = prove(
    ``modifiesBefore g1 w1_0 w1_2``,
    EVAL_TAC);
val mb_sanity_1 = prove(
    ``~modifiesBefore g1 w1_0 w1_1``,
    EVAL_TAC);
val mb_sanity_2 = prove(
  ``~modifiesBefore g1 w1_0 r1_3``,
    EVAL_TAC);

(* General *)
val mb_sanity_3 = prove(
    ``∀ g nd. ~modifiesBefore g nd nd``,
    RW_TAC arith_ss [modifiesBefore_def,orderedBefore_def,sameAddress_def]);
val mb_sanity_3 = prove(
    ``∀ g nd1 nd2. (modifiesBefore g nd1 nd2) ==> ~(modifiesBefore g nd2 nd1)``,
    RW_TAC arith_ss [modifiesBefore_def,orderedBefore_def,sameAddress_def]);


(*                                     _ ___       __             
  ___ ___ __ _ _  _ ___ _ _  __ ___ __| | _ ) ___ / _|___ _ _ ___ 
 (_-</ -_) _` | || / -_) ' \/ _/ -_) _` | _ \/ -_)  _/ _ \ '_/ -_)
 /__/\___\__, |\_,_\___|_||_\__\___\__,_|___/\___|_| \___/_| \___|
            |_|                                                    *)

val cant_be_sequenced_before_self = prove(
    ``∀ nd g. ~(sequencedBefore g nd nd)``,
    RW_TAC arith_ss [sequencedBefore_def,orderedBefore_def,sameThread_def] );
val one_sequence = prove(
  ``∀ g nd1 nd2. (sequencedBefore g nd1 nd2) ==> ~(sequencedBefore g nd2 nd1)``,
  RW_TAC arith_ss [sequencedBefore_def,sameThread_def,orderedBefore_def]);


(*        _                  ___                                 ___   __ 
  _ _ ___| |___ __ _ ___ ___/ __| ___ __ _ _  _ ___ _ _  __ ___ / _ \ / _|
 | '_/ -_) / -_) _` (_-</ -_)__ \/ -_) _` | || / -_) ' \/ _/ -_) (_) |  _|
 |_| \___|_\___\__,_/__/\___|___/\___\__, |\_,_\___|_||_\__\___|\___/|_|  
                                        |_|                                *)

val rs_sanity_0 = prove(``∀ A B C g. ( (readsFrom g C B) ∧ (inReleaseSequenceOf g B A)) ==> (orderedBefore g A C)``,
                        METIS_TAC [sequencedBefore_def,
                                   inReleaseSequenceOf_def,
                                   readsFrom_def,AND_IMP_INTRO,
                                   ob_sanity_5]);


(*                _        ___                        _                 _____    
  __ __ _ _ _ _ _(_)___ __|   \ ___ _ __  ___ _ _  __| |___ _ _  __ _  |_   _|__ 
 / _/ _` | '_| '_| / -_|_-< |) / -_) '_ \/ -_) ' \/ _` / -_) ' \/ _| || || |/ _ \
 \__\__,_|_| |_| |_\___/__/___/\___| .__/\___|_||_\__,_\___|_||_\__|\_, ||_|\___/
                                   |_|                              |__/         *)


(*                _                 _          __      ___ _   _    
  ____  _ _ _  __| |_  _ _ ___ _ _ (_)______ __\ \    / (_) |_| |_  
 (_-< || | ' \/ _| ' \| '_/ _ \ ' \| |_ / -_|_-<\ \/\/ /| |  _| ' \ 
 /__/\_, |_||_\__|_||_|_| \___/_||_|_/__\___/__/ \_/\_/ |_|\__|_||_|
     |__/                                                            *)

Define `g5= FOLDL (receive') empty
         [
            ( Write 1024 0 112 RELEASE {} , 0) ;
            ( Write 1024 1 432 RELAXED {} , 0) ;
            ( Write 9999 2 111 RELAXED {} , 0) ;
            ( Read  1024 3     ACQUIRE {} , 1) ;
            ( Write 1024 4 888 RELAXED {} , 0) 
]`;

Define `w5_0 = (EL 0 g5.nodes)`;
Define `w5_1 = (EL 1 g5.nodes)`;
Define `w5_2 = (EL 2 g5.nodes)`;
Define `r5_3 = (EL 3 g5.nodes)`;
Define `w5_4 = (EL 4 g5.nodes)`;

(*1*)
g `(readsFrom g5 r5_3 w5_0) ==> (synchronizesWith g5 w5_0 r5_2)`;
e (STRIP_TAC)
e (RW_TAC arith_ss [synchronizesWith_def]);
(* How do I tell Hol4 that w5_0.order equals RELEASE? *)

(*2*)
g `(readsFrom g5 r5_3 w5_1) ==> (synchronizesWith g5 w5_0 r5_2)`;
(*3*)
g `(readsFrom g5 r5_3 w5_2) ==> ~(synchronizesWith g5 w5_0 r5_2)`;
(*4*)
g `(readsFrom g5 r5_3 w5_3) ==> ~(synchronizesWith g5 w5_0 r5_2)`;

(* NOT DONE *) (*rs_sanity_0*)
val sw_sanity_4 = prove(
    ``∀ g nd. ~(synchronizesWith g nd nd)``,
    RW_TAC (srw_ss()) [synchronizesWith_def] THENL [
    RW_TAC arith_ss [ob_sanity_3], 
    RW_TAC arith_ss [rs_sanity_0]
           METIS_TAC [synchronizesWith_def]
    METIS_TAC [synchronizesWith_def,ob_sanity_3, DE_MORGAN_THM,NOT_EXISTS_THM,rs_sanity_0]
      RW_TAC arith_ss [releaseSequenceOf_def]
...
(*   _           ___         _                _ ___       __             
  __| |___ _ __ / _ \ _ _ __| |___ _ _ ___ __| | _ ) ___ / _|___ _ _ ___ 
 / _` / -_) '_ \ (_) | '_/ _` / -_) '_/ -_) _` | _ \/ -_)  _/ _ \ '_/ -_)
 \__,_\___| .__/\___/|_| \__,_\___|_| \___\__,_|___/\___|_| \___/_| \___|
          |_|                                                             *)


(*_     _           _  _                             ___       __             
 (_)_ _| |_ ___ _ _| || |__ _ _ __ _ __  ___ _ _  __| _ ) ___ / _|___ _ _ ___ 
 | | ' \  _/ -_) '_| __ / _` | '_ \ '_ \/ -_) ' \(_-< _ \/ -_)  _/ _ \ '_/ -_)
 |_|_||_\__\___|_| |_||_\__,_| .__/ .__/\___|_||_/__/___/\___|_| \___/_| \___|
                             |_|  |_|                                          *)


(*_                                ___       __             
 | |_  __ _ _ __ _ __  ___ _ _  __| _ ) ___ / _|___ _ _ ___ 
 | ' \/ _` | '_ \ '_ \/ -_) ' \(_-< _ \/ -_)  _/ _ \ '_/ -_)
 |_||_\__,_| .__/ .__/\___|_||_/__/___/\___|_| \___/_| \___|
           |_|  |_|                                          *)

(* Only sequencedBefore for now - too trivial. Should check other cases. *)
Define `g0= FOLDL (receive') empty
         [
            ( Write 1024 0 112 SEQ_CST    {} , 1) ;
            ( Read  1024 1     SEQ_CST    {} , 1) ;
            ( Write 1024 2 10  SEQ_CST    {} , 1)
         ]`;
Define `w0_0 = (EL 0 g0.nodes)`;
Define `r0_1 = (EL 1 g0.nodes)`;
Define `w0_2 = (EL 2 g0.nodes)`;

val hb_sanity_0 = prove(
    `` happensBefore g0 w0_0 r0_1``,
    EVAL_TAC);



(*    _    _ _    _    _____    
 __ _(_)__(_) |__| |__|_   _|__ 
 \ V / (_-< | '_ \ / -_)| |/ _ \
  \_/|_/__/_|_.__/_\___||_|\___/
                                 *)


(*    _    _ _    _     ___                                 ___   __ 
 __ _(_)__(_) |__| |___/ __| ___ __ _ _  _ ___ _ _  __ ___ / _ \ / _|
 \ V / (_-< | '_ \ / -_)__ \/ -_) _` | || / -_) ' \/ _/ -_) (_) |  _|
  \_/|_/__/_|_.__/_\___|___/\___\__, |\_,_\___|_||_\__\___|\___/|_|  
                                   |_|                                *)


(*             ___             _ ___              
  __ __ _ _ _ | _ \___ __ _ __| | __| _ ___ _ __  
 / _/ _` | ' \|   / -_) _` / _` | _| '_/ _ \ '  \ 
 \__\__,_|_||_|_|_\___\__,_\__,_|_||_| \___/_|_|_|
                                                   *)
(*
Hand written:

(1) WTS r1_3 canReadFrom w1_2
(2) ((aren't_atomic r1_3, w1_2) AND (w1_2 visible_to w1_2 r1_3)) OR
    ((   are_atomic r1_3, w1_2) AND (w1_2 inVisibleSequenceOf r1_3))
(3) w1_2 inVisibleSequenceOf r1_3
(4) w1_2 IN visibleSequence r1_3
(5) w1_2 IN {nd | (sameAddress nd r1_3) ∧ ( (nd visibleTo r1_3) ∨ ( ~(r1_3 happensBefore nd) ∧ (∃fs. (fs visibleTo r1_3) ∧ (fs modifies_before nd) ))) }
(6) (sameAddress w1_2 r1_3) ∧ ( (w1_2 visibleTo r1_3) ∨ ( ~(r1_3 happensBefore w1_2) ∧ (∃fs. (fs visibleTo r1_3) ∧ (fs modifies_before w1_2) )))
(7) ( (w1_2 happens_before r1_3) ∧ ~(E X. (w1_2 happensBefore X) ∧ (X happens_before r1_3) )) ∨ ...
(8) ( (( w1_2 sequenced_before r1_3) ∨ ...) ∧ (    ~( (w1_2 happensBefore w1_1) ∧ (w1_1 happens_before r1_3))
                                               AND ~( (w1_2 happensBefore w1_2) ∧ (w1_2 happens_before r1_3))
                                               AND ~( (w1_2 happensBefore r1_3) ∧ (r1_3 happens_before r1_3)) )) ∨ ...
(9) ( (((same_thread w1_2 r1_3) ∧ (ordered_before)) ∨ ...) ∧ () ) ∨ ...

...


*)






(* ___   _   __  __ ___ ___ ___ ___   ___ ___ 
  / __| /_\ |  \/  | _ ) _ \_ _|   \ / __| __|
 | (__ / _ \| |\/| | _ \   /| || |) | (_ | _| 
  \___/_/ \_\_|  |_|___/_|_\___|___/ \___|___| *)

(* The Cambridge paper has numerous examples. Here, I show the those examples still hold, where possible (if the instructions have been defined). *)


(* sequencedBefore and readsFrom
  __  
 /  | 
 `| | 
  | | 
 _| |_
 \___/  

int main() {
  int x = 2;
  int y = 0;
  y = (x==x);
  return 0;}

*)

Define `cg1= FOLDL (receive') empty
         [
           ( Write 10 0 2 NOT_ATOMIC    {} , 1 ) ;
           ( Write 20 1 0 NOT_ATOMIC    {} , 1 ) ;
           ( Read  10 2   NOT_ATOMIC    {} , 1 ) ;
           ( Read  10 3   NOT_ATOMIC    {} , 1 ) ;
           ( Write 20 4 1 NOT_ATOMIC {2;3} , 1 )
         ]`;

Define `cw1_0 = (EL 0 cg1.nodes)`;
Define `cw1_1 = (EL 1 cg1.nodes)`;
Define `cr1_2 = (EL 2 cg1.nodes)`;
Define `cr1_3 = (EL 3 cg1.nodes)`;
Define `cw1_4 = (EL 4 cg1.nodes)`;

(* All the arrows defined in the example's diagram: *)
val cg0_rel0 = prove( ``sequencedBefore cg1 cw1_0 cw0_1``,EVAL_TAC);
val cg0_rel1 = prove( ``sequencedBefore cg1 cw1_1 cr0_2``,EVAL_TAC);
val cg0_rel2 = prove( ``sequencedBefore cg1 cw1_1 cr0_3``,EVAL_TAC);
val cg0_rel3 = prove( ``sequencedBefore cg1 cr1_2 cw0_4``,EVAL_TAC);
val cg0_rel4 = prove( ``sequencedBefore cg1 cr1_3 cw0_4``,EVAL_TAC);

val cg0_rel5 = prove( ``canReadFrom cg1 cr1_2 cw1_0``, EVAL_TAC);
e (RW_TAC (srw_ss()) [canReadFrom_def,isAtomic_def]);
e (`cr1_2.order = NOT_ATOMIC ∧ cw1_0.order = NOT_ATOMIC` by EVAL_TAC);
e (RW_TAC (srw_ss()) [visibleTo_def]);
  e (`sequencedBefore cg1 cw1_0 cr1_2` by EVAL_TAC);
  e (RW_TAC (srw_ss()) [happensBefore_def]);

  e (RW_TAC (srw_ss()) [happensBefore_def,sequencedBefore_def,orderedBefore_def,sameThread_def]);
  e (RW_TAC (srw_ss()) [indexOf_def]);
  e (UNDISCH_TAC ``X IN cg1.nodeSet``);
  e (Cases_on `X`);
  e (EVAL_TAC);
  
  e (RW_TAC (srw_ss()) [sequencedBefore_def,orderedBefore_def]);

  
e (`sameThread cw1_0 cr1_2 ∧ orderedBefore cg1 cw1_0 cr1_2` by EVAL_TAC);
EVAL ``sequencedBefore cg1 cw1_0 cr1_2``;
e (RW_TAC (srw_ss()) [visibleTo_def,happensBefore_def,sequencedBefore_def,orderedBefore_def]);


(* UNSEQUENCED RACES
 _____ 
/ __  \
`' / /'
  / /  
./ /___
\_____/

int main() {
  int x = 2;
  int y = 0;
  y = (x == (x=3));
  return 0;}
        *)


(* synchronizesWith
 _____ 
|____ |
    / /
    \ \
.___/ /
\____/ 
       
void foo(int* p) {*p = 3;}
int main() {
  int x = 2;
  int y;
  thread t1(foo, &x);
  y = 3;
  t1.join();
  return 0; }

*)


(* SEQ_CST
   ___ 
  /   |
 / /| |
/ /_| |
\___  |
    |_/

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
           ( Write 10 0 2 SEQ_CST       {} , 0 ) ;
           ( Write 20 1 2 NOT_ATOMIC    {} , 0 ) ;
           ( Read  10 2   SEQ_CST       {} , 2 ) ;
           ( Write 10 3 3 SEQ_CST       {} , 1 ) ;
           ( Write 20 4 0 NOT_ATOMIC   {3} , 2 )
         ]`;

Define `cw4_0 = (EL 0 cg4.nodes)`;
Define `cw4_1 = (EL 1 cg4.nodes)`;
Define `cr4_2 = (EL 2 cg4.nodes)`;
Define `cw4_3 = (EL 3 cg4.nodes)`;
Define `cw4_4 = (EL 4 cg4.nodes)`;


val cg4_rel0 = prove( ``sequencedBefore cg4 cw4_0 cw4_1``,EVAL_TAC );
val cg4_rel2 = prove( ``sequencedBefore cg4 cr4_2 cw4_4``, EVAL_TAC );

val cg4_rel1 = prove(
      ``sequentiallyConsistent cg4 cw4_0 cr4_2``,
      RW_TAC (srw_ss()) [sequentiallyConsistent_def]
      ...
























(*__  __ ___ ___  ___ 
 |  \/  |_ _/ __|/ __|
 | |\/| || |\__ \ (__ 
 |_|  |_|___|___/\___|
                      *)




Define `g0= FOLDL (receive') <| nodes:=[]; rf:=FEMPTY |>
         [
            ( Write 1024 0 112 SEQ_CST    {} , 1) ;
            ( Read  1024 1     SEQ_CST    {} , 1) ;
            ( Write 1024 2 10  SEQ_CST    {} , 1)
         ]`;
Define `w0_0 = (EL 0 g0.nodes)`;
Define `r0_1 = (EL 1 g0.nodes)`;
Define `w0_2 = (EL 2 g0.nodes)`;

EVAL `` readsFrom g0 r0_1 w0_2 ``; (* = F *)
EVAL `` modifiesBefore g0 w0_0 w0_2 ``; (* = T *)
EVAL `` synchronizesWith g0 w0_0 w0_2 ``; (* = F *)

EVAL `` r0_1.order = SEQ_CST ``;


g `r0_1.order = SEQ_CST`;
e (`r0_1.order = SEQ_CST` by EVAL_TAC );

e (


g `canReadFrom g0 r0_1 w0_0 = T`;
e (RW_TAC arith_ss [canReadFrom_def,isAtomic_def]);
e (`r0_1.order <> NOT_ATOMIC` by EVAL_TAC );
e (UNDISCH_TAC ``r0_1.order <> NOT_ATOMIC``);






















e (RW_TAC arith_ss [canReadFrom_def, isAtomic_def,visibleTo_def,happensBefore_def,sequencedBefore_def,orderedBefore_def]);

e (`w0_1.order = SEQ_CST` by EVAL_TAC);
e (EVAL_TAC);
e (RW_TAC arith_ss []);
e (`w1_2.order = SEQ_CST` by PROVE_TAC [] );


e (Cases_on `w1_2.order` THEN Cases_on `r1_3.order`);
(* HOW DO I SIMPLIFY w1_2.order to SEQ_CST? *)
e (SIMP_TAC (srw_ss()) [node_accessors, memoryorder_distinct]);
(*e (`w1_2.order <> NOT_ATOMIC` by DECIDE_TAC);*)






g `inVisibleSequenceOf g0 r1_3 w1_2`;
e (RW_TAC (srw_ss()) [inVisibleSequenceOf_def]);





(* Incomplete: *)
val in_own_release_seq = prove(
``∀ g nd. (MEM nd g.nodes) ==> (releaseSequenceOf g nd nd)``,
RW_TAC arith_ss [releaseSequenceOf_def]
    RW_TAC arith_ss [releaseSequenceOf_def,modifiesBefore_def,isAtomic_def,isStore_def,sequencedBefore_def,orderedBefore_def,sameAddress_def,sameThread_def] THEN







e(DISCH_TAC ``orderedBefore g nd1 nd2``);

e(`nd1.thread_id = nd2.thread_id` by METIS_TAC []);

e(Cases_on `SOME x'`);
e(RW_TAC arith_ss []  );

(* SynchronizesWith *)
g `∀ nd g. ~(synchronizesWith g nd nd)`;

(*uh............... I don't think this is the way to go.*)
e (RW_TAC arith_ss [synchronizesWith_def,isRelease_def,isAcquire_def,orderedBefore_def,sameAddress_def,readsFrom_def,releaseSequenceOf_def,modifiesBefore_def,isAtomic_def,isStore_def,sequencedBefore_def,sameThread_def] THEN Cases_on `indexOf g.nodes 0 nd` THEN RW_TAC arith_ss [] THEN Cases_on `X.order` THEN RW_TAC arith_ss [] THEN Cases_on `nd.order` THEN RW_TAC arith_ss [] THEN Cases_on `nd.operation` THEN RW_TAC arith_ss [isFence_def] THEN Cases_on `Y.order` THEN RW_TAC arith_ss []);
e (REPEAT STRIP_TAC);
 
e (REPEAT STRIP_TAC);




(* happensBefore *)
g `∀ nd g. ~(happensBefore g nd nd)`;
e (RW_TAC arith_ss [happensBefore_def,sequencedBefore_def,orderedBefore_def, sameThread_def]);



                               












(* Thread semantics *)
Define`ts = <| curframe :=
               <| ssavars := FEMPTY |+ ("y", (SOME 1,{}) ) |+ ("z", (SOME 2,{}))
                                    |+ ("a", (SOME 1024,{}))
                                    |+ ("p", (NONE,{}) ) |> ;
               memreq_map := FEMPTY ;
               addrwr_map := FEMPTY
            |> `;
EVAL ``exec_inst (Assign ["x"] (Binop Add "z" "y")) ts``;
EVAL ``exec_inst (Load "x" T "a" SEQ_CST) ts``;
EVAL ``exec_inst (Store "z" T "a" SEQ_CST) ts``;



