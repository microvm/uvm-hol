open HolKernel Parse boolLib bossLib;

open wordsTheory;
open uvmTypesTheory;
open sumMonadTheory;
open monadsyntax;

val _ = new_theory "uvmValues";

val _ = type_abbrev("addr", ``:num``)  (* non-local memory addresses *)
val _ = type_abbrev("fnname", ``:string``) (* function name *)
val _ = type_abbrev("fnvname", ``:fnname # num``) (* function version *)

val _ = Datatype`
  value =
  | IntV num word64 (* word64 because 64 bits is the max int size *)
  | RefV uvm_type addr
  | IRefV ref_type uvm_type addr
  | FloatV word32
  | DoubleV word64
  | ArrayV uvm_type (value list)
  | VectorV uvm_type (value list)
  | StructV struct_id (value list)
  | HybridV ((value # uvm_type) list) uvm_type (value list)
  | FuncRefV ref_type funcsig fnname ;

  ref_type = REF | PTR
`

val type_of_value_def = Define`
  type_of_value (v : value) : uvm_type =
    case v of
    | IntV n _ => Int n
    | RefV t _ => Ref t
    | IRefV REF t _ => IRef t
    | IRefV PTR t _ => UPtr t
    | FloatV _ => Float
    | DoubleV _ => Double
    | ArrayV t vs => Array t (LENGTH vs)
    | VectorV t vs => Vector t (LENGTH vs)
    | StructV id _ => Struct id
    | HybridV fvs vt _ => Hybrid (MAP SND fvs) vt
    | FuncRefV REF sig _ => FuncRef sig
    | FuncRefV PTR sig _ => UFuncPtr sig
`

val _ = Datatype`
  exit_state =
  (* Execution ended normally with return value(s) *)
  | ExitReturn (value list)
  (* Execution ended due to uncaught exception value(s) *)
  | ExitThrow (value list)
  (* Execution ended in error state (such as undefined behavior) *)
  | ExitError error_type string ;

  (* Error states for ExitError *)
  error_type =
  | UndefinedBehavior
  | InvalidState
  | TypeMismatch
`

val _ = type_abbrev("or_exit", ``:α + exit_state``)
val _ = overload_on("Next", ``INL : α -> α or_exit``)
val _ = overload_on("Exit", ``INR : exit_state -> α or_exit``)

val fail_def = Define`
  fail (err : error_type) (msg : string) : α or_exit =
    Exit (ExitError err msg)
`

(* `assert cond err msg` asserts that `cond` is true, continuing with `Next ()`
   if it is, and exiting with `Exit (ExitError err msg)` if it isn't.
*)
val assert_def = Define`
  assert (cond : bool) (err : error_type) (msg : string) : one or_exit =
    if cond then return () else fail err msg
`

(* `expect opt err` converts the `α option` `opt` into an `α or_exit`, exiting
   with the given error type and message if `NONE` is encountered.
*)
val expect_def = Define`
  (* expect : α option -> error_type -> string -> α or_exit *)
  (expect NONE err msg = fail err msg) ∧
  (expect (SOME x) _ _ = return x)
`

val value_add_def = Define`
  value_add (v1 : value) (v2 : value) : value or_exit =
    case (v1, v2) of
    | (IntV sz1 n1, IntV sz2 n2) =>
        do
          assert (sz1 = sz2) TypeMismatch "cannot add differently-sized ints";
          return (IntV sz1 (n1 + n2))
        od
    | _ => fail TypeMismatch "incompatible values for add"
`
val _ = overload_on ("+", ``value_add``)

val value_div_def = Define`
  value_div (v1 : value) (v2 : value) : value or_exit =
    case (v1,v2) of
    | (IntV sz1 n1, IntV sz2 n2) => 
        do
          assert (sz1 = sz2) TypeMismatch "cannot div differently-sized ints";
          assert (n2 ≠ 0w) UndefinedBehavior "division by zero";
          return (IntV sz1 (n1 // n2))
        od
    | _ => fail TypeMismatch "incompatible values for div"
`
val _ = overload_on ("DIV", ``value_div``)

val get_int1_as_bool_def = Define`
  get_int1_as_bool (v : value) : (bool or_exit) =
    case v of
    | IntV 1 n => return (n ≠ 0w)
    | _ => fail TypeMismatch "boolean value must be int<1>"
`

val get_iref_addr_def = Define`
  get_iref_addr (v : value) : (addr or_exit) =
    case v of
    | IRefV _ _ a => return a
    | _ => fail TypeMismatch "expected iref or uptr"
`

val get_funcref_fnname_def = Define`
  get_funcref_fnname (v : value) : (fnname or_exit) =
    case v of
    | FuncRefV _ _ n => return n
    | _ => fail TypeMismatch "expected funcref or ufuncptr"
`
val _ = export_theory()

