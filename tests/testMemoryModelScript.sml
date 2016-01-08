open HolKernel Parse boolLib bossLib;

load "../uvmSystemTheory";
open uvmSystemTheory;
open uvmMemoryModelTheory;

val _ = new_theory "testMemoryModel";


(* {{{ *)

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
       (sameAddress A B)             ∧
       ( (isStore A) ∨ (isStore B) ) ∧
      ~(sequencedBefore g A B)       ∧
      ~(sequencedBefore g B A)
)`;


val n = Define`n m = (Int m 8)`;

(* sameAddress *)
val ad_sanity_0 = prove( ``∀nd. (sameAddress nd nd)``, EVAL_TAC THEN RW_TAC (srw_ss()) []);


(* }}} *)




(* ___ _ _ __| |___ _ _ ___ __| | _ ) ___ / _|___ _ _ ___ 
  / _ \ '_/ _` / -_) '_/ -_) _` | _ \/ -_)  _/ _ \ '_/ -_)
  \___/_| \__,_\___|_| \___\__,_|___/\___|_| \___/_| \___|  *)

(* {{{ *)

Define `g0= FOLDL (receive') empty
         [
            ( Write 10 0 (n 11) NOT_ATOMIC {} , 0) ;
            ( Read  10 1        SEQ_CST    {} , 1) ;
            ( Write 10 2 (n 12) SEQ_CST    {} , 1) ;
            ( Write 10 3 (n 13) NOT_ATOMIC {} , 1)
         ]`;
Define `w0_0 = (EL 0 g0.nodes)`; Define `r0_1 = (EL 1 g0.nodes)`; Define `w0_2 = (EL 2 g0.nodes)`;
Define `w0_3 = (EL 3 g0.nodes)`;


(* Specific *)
val ob_eg0 = prove(``orderedBefore g0 r0_1 w0_2``, EVAL_TAC);
val ob_eg1 = prove(``orderedBefore g0 w0_0 r0_1``, EVAL_TAC);
val ob_eg2 = prove(``~orderedBefore g0 r0_1 w0_0``, EVAL_TAC);

(* General *)

(* }}} *)

(* _ __  ___  __| (_)/ _(_)___ __| _ ) ___ / _|___ _ _ ___ 
  | '  \/ _ \/ _` | |  _| / -_|_-< _ \/ -_)  _/ _ \ '_/ -_)
  |_|_|_\___/\__,_|_|_| |_\___/__/___/\___|_| \___/_| \___|  *)

(* {{{ *)

val mb_eg0 = prove(`` modifiesBefore g0 w0_2 w0_3``, EVAL_TAC);
val mb_eg1 = prove(`` modifiesBefore g0 w0_0 w0_2``, EVAL_TAC);
val mb_eg2 = prove(``~modifiesBefore g0 w0_0 r0_1``, EVAL_TAC);
val mb_eg2 = prove(`` modifiesBefore g0 w0_0 w0_3``, EVAL_TAC);

(* }}} *)

(* ___ ___ __ _ _  _ ___ _ _  __ ___ __| | _ ) ___ / _|___ _ _ ___ 
  (_-</ -_) _` | || / -_) ' \/ _/ -_) _` | _ \/ -_)  _/ _ \ '_/ -_)
  /__/\___\__, |\_,_\___|_||_\__\___\__,_|___/\___|_| \___/_| \___|
            |_|                                                    *)
(* {{{ *)

Define `g2= FOLDL (receive') empty
         [                                            (* int main() {   *)
           ( Write 10 0 (n 2) NOT_ATOMIC    {} , 1 ) ;    (*   int x = 2    *)
           ( Write 20 1 (n 0) NOT_ATOMIC    {} , 1 ) ;    (*   int y = 0    *)
           ( Read  10 2       NOT_ATOMIC    {} , 1 ) ;    (*   y = (x == x) *)
           ( Read  10 3       NOT_ATOMIC    {} , 1 ) ;
           ( Write 20 4 (n 1) NOT_ATOMIC {2;3} , 1 )
         ]`;                                          (*   return 0;    *)
Define `w2_0 = (EL 0 g2.nodes)`; Define `w2_1 = (EL 1 g2.nodes)`; Define `r2_2 = (EL 2 g2.nodes)`;
Define `r2_3 = (EL 3 g2.nodes)`; Define `w2_4 = (EL 4 g2.nodes)`;

(* All the arrows defined in the example's diagram: *)
val cg0_rel0 = prove( ``sequencedBefore g2 w2_0 w2_1``,EVAL_TAC);
val cg0_rel1 = prove( ``sequencedBefore g2 w2_1 r2_2``,EVAL_TAC);
val cg0_rel2 = prove( ``sequencedBefore g2 w2_1 r2_3``,EVAL_TAC);
val cg0_rel3 = prove( ``sequencedBefore g2 r2_2 w2_4``,EVAL_TAC);
val cg0_rel4 = prove( ``sequencedBefore g2 r2_3 w2_4``,EVAL_TAC);

(* }}} *)

(*        _                  ___                                 ___   __ 
  _ _ ___| |___ __ _ ___ ___/ __| ___ __ _ _  _ ___ _ _  __ ___ / _ \ / _|
 | '_/ -_) / -_) _` (_-</ -_)__ \/ -_) _` | || / -_) ' \/ _/ -_) (_) |  _|
 |_| \___|_\___\__,_/__/\___|___/\___\__, |\_,_\___|_||_\__\___|\___/|_|  
                                        |_|                                *)
(* {{{ *)


(* }}} *)

(*                _        ___                        _                 _____    
  __ __ _ _ _ _ _(_)___ __|   \ ___ _ __  ___ _ _  __| |___ _ _  __ _  |_   _|__ 
 / _/ _` | '_| '_| / -_|_-< |) / -_) '_ \/ -_) ' \/ _` / -_) ' \/ _| || || |/ _ \
 \__\__,_|_| |_| |_\___/__/___/\___| .__/\___|_||_\__,_\___|_||_\__|\_, ||_|\___/
                                   |_|                              |__/         *)
(* {{{ *)

Define `g4= FOLDL (receive') empty
         [
            ( Read  10 0       ACQUIRE    {} , 1) ;
            ( Write 20 1 (n 1) RELAXED   {0} , 1)
]`;
Define `r4_0 = (EL 0 g4.nodes)`; Define `w4_1 = (EL 1 g4.nodes)`;

val cd_rel0 = prove(``carriesDependencyTo g4 r4_0 w4_1``, EVAL_TAC);
(* }}} *)

(*                _                 _          __      ___ _   _    
  ____  _ _ _  __| |_  _ _ ___ _ _ (_)______ __\ \    / (_) |_| |_  
 (_-< || | ' \/ _| ' \| '_/ _ \ ' \| |_ / -_|_-<\ \/\/ /| |  _| ' \ 
 /__/\_, |_||_\__|_||_|_| \___/_||_|_/__\___/__/ \_/\_/ |_|\__|_||_|
     |__/                                                            *)
(* {{{ *)

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
    `readsFrom g5 r5_2 w5_1 ∧ inReleaseSequenceOf g5 w5_1 w5_1` by EVAL_TAC THEN
    METIS_TAC []);
val sw_rel2 = prove(`` sequencedBefore  g5 r5_2 r5_3 ``, EVAL_TAC );
val sw_rel4 = prove(``(happensBefore g5 w5_0 r5_3)``,
                    RW_TAC (srw_ss()) [happensBefore_def,ithb_rules] THEN
                    `synchronizesWith g5 w5_1 r5_2` by RW_TAC (srw_ss()) [sw_rel1] THEN
                    `sequencedBefore g5 r5_2 r5_3` by EVAL_TAC THEN
                    `sequencedBefore g5 w5_0 w5_1` by EVAL_TAC THEN
                    METIS_TAC [sw_rel1, ithb_rules] );
val sw_unrel_5 = prove( `` ~(synchronizesWith g5 w5_0 w5_1) ``, EVAL_TAC);

(* }}} *)

(*   _           ___         _                _ ___       __             
  __| |___ _ __ / _ \ _ _ __| |___ _ _ ___ __| | _ ) ___ / _|___ _ _ ___ 
 / _` / -_) '_ \ (_) | '_/ _` / -_) '_/ -_) _` | _ \/ -_)  _/ _ \ '_/ -_)
 \__,_\___| .__/\___/|_| \__,_\___|_| \___\__,_|___/\___|_| \___/_| \___|
          |_|                                                             *)
(* {{{ *)

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
(*
val do_rel0 = prove(``dependencyOrderedBefore g6 w6_1 r6_2``, 
                   );

val do_self = prove(`` ∀ nd g. ~dependencyOrderedBefore g nd nd``,
                   );
*)
(* }}} *)

(*_     _           _  _                             ___       __             
 (_)_ _| |_ ___ _ _| || |__ _ _ __ _ __  ___ _ _  __| _ ) ___ / _|___ _ _ ___ 
 | | ' \  _/ -_) '_| __ / _` | '_ \ '_ \/ -_) ' \(_-< _ \/ -_)  _/ _ \ '_/ -_)
 |_|_||_\__\___|_| |_||_\__,_| .__/ .__/\___|_||_/__/___/\___|_| \___/_| \___|
                             |_|  |_|                                          *)
(* {{{ *)

Define `g7'= FOLDL (receive') empty
         [
            ( Write 10 0 (n 1) NOT_ATOMIC {} , 0) ;
            ( Write 20 1 (n 1) RELEASE    {} , 0) ;
            ( Read  20 2       ACQUIRE    {} , 1) ;
            ( Read  10 3       NOT_ATOMIC {} , 1)
]`;



 
 (* }}} *)
    
(*_                                ___       __             
 | |_  __ _ _ __ _ __  ___ _ _  __| _ ) ___ / _|___ _ _ ___ 
 | ' \/ _` | '_ \ '_ \/ -_) ' \(_-< _ \/ -_)  _/ _ \ '_/ -_)
 |_||_\__,_| .__/ .__/\___|_||_/__/___/\___|_| \___/_| \___|
           |_|  |_|                                          *)
(* {{{ *)

Define `g8 = FOLDL (receive') empty
         [
            ( Write 1024 0 (n 11) SEQ_CST    {} , 1) ;
            ( Read  1024 1        SEQ_CST    {} , 1) ;
            ( Write 1024 2 (n 10) SEQ_CST    {} , 1)
         ]`;
Define `w8_0 = (EL 0 g8.nodes)`; Define `r8_1 = (EL 1 g8.nodes)`; Define `w8_2 = (EL 2 g8.nodes)`;


val hb_rel0 = prove( `` happensBefore g8 w8_0 r8_1``, EVAL_TAC);







(* }}} *)

(*    _    _ _    _    _____    
 __ _(_)__(_) |__| |__|_   _|__ 
 \ V / (_-< | '_ \ / -_)| |/ _ \
  \_/|_/__/_|_.__/_\___||_|\___/ *)

(* {{{ *)

Define `g9= FOLDL (receive') empty
         [
            ( Write 10 0 (n 1) NOT_ATOMIC    {} , 0) ;
            ( Write 10 1 (n 2) NOT_ATOMIC    {} , 0) ;
            ( Read  10 2       NOT_ATOMIC    {} , 1)
]`;
Define `w9_0 = (EL 0 g9.nodes)`; Define `w9_1 = (EL 1 g9.nodes)`;
Define `r9_2 = (EL 2 g9.nodes)`;

(* }}} *)

(*    _    _ _    _     ___                                 ___   __ 
 __ _(_)__(_) |__| |___/ __| ___ __ _ _  _ ___ _ _  __ ___ / _ \ / _|
 \ V / (_-< | '_ \ / -_)__ \/ -_) _` | || / -_) ' \/ _/ -_) (_) |  _|
  \_/|_/__/_|_.__/_\___|___/\___\__, |\_,_\___|_||_\__\___|\___/|_|  
                                   |_|                                *)
(* {{{ *)


(* }}} *)

(*             ___             _ ___              
  __ __ _ _ _ | _ \___ __ _ __| | __| _ ___ _ __  
 / _/ _` | ' \|   / -_) _` / _` | _| '_/ _ \ '  \ 
 \__\__,_|_||_|_|_\___\__,_\__,_|_||_| \___/_|_|_|
                                                   *)
(* {{{ *)

Define `g11= FOLDL (receive') <| nodes:=[]; rf:=FEMPTY |>
         [
            ( Write 1024 0 (n 11) SEQ_CST    {} , 1) ;
            ( Read  1024 1        SEQ_CST    {} , 1) ;
            ( Write 1024 2 (n 10)  SEQ_CST    {} , 1)
         ]`;
Define `w11_0 = (EL 0 g11.nodes)`; Define `r11_1 = (EL 1 g11.nodes)`; Define `w11_2 = (EL 2 g11.nodes)`;

(* }}} *)

(*___ ___ ___     ___ ___ _____ 
 / __| __/ _ \   / __/ __|_   _|
 \__ \ _| (_) | | (__\__ \ | |  
 |___/___\__\_\  \___|___/ |_|   *)

(* {{{ *)

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
