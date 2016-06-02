open HolKernel Parse boolLib bossLib;

open uvmTypesTheory;
open errorMonadTheory;
open monadsyntax;

val _ = new_theory "uvmValues";

val _ = type_abbrev("addr", ``:num``)  (* non-local memory addresses *)
val _ = type_abbrev("fnname", ``:string``) (* function name *)
val _ = type_abbrev("fnvname", ``:fnname # num``) (* function version *)

(*tmp: ==========================================================*)
val _ = type_abbrev("float32", ``:num``)
val _ = type_abbrev("float64", ``:num``)
val _ = type_abbrev("int",     ``:num``)
(*===============================================================*)

val _ = Datatype`
  value =
  | IntV num int
  | IRefV uvm_type addr
  | FloatV float32
  | DoubleV float64
  (* not sure if these are storable-in-register values
  | StructV (value list)
  | ArrayV (value list)
  | HybridV (value list) (value list) *)
  | VectorV (value list)
  | FuncRefV fnname
`

val value_add_def = Define`
  value_add (v1 : value) (v2 : value) : value or_error =
    case (v1, v2) of
    | (IntV sz1 n1, IntV sz2 n2) =>
        do
          assert (sz1 = sz2) "type mismatch: cannot add differently-sized ints";
          return (IntV sz1 (n1 + n2))
        od
    | _ => Error "type mismatch: incompatible values for add"
`
val _ = overload_on ("+", ``value_add``)

val value_div_def = Define`
  value_div (v1 : value) (v2 : value) : value or_error =
    case (v1,v2) of
    | (IntV sz1 n1, IntV sz2 n2) => 
        do
          assert (sz1 = sz2) "type mismatch: cannot div differently-sized ints";
          assert (n2 ≠ 0) "division by zero";
          return (IntV sz1 (n1 DIV n2))
        od
    | _ => Error "type mismatch: incompatible values for div"
`
val _ = overload_on ("DIV", ``value_div``)

val get_int1_as_bool_def = Define`
  get_int1_as_bool (v : value) : (bool or_error) =
    case v of
    | IntV 1 0 => return F
    | IntV 1 1 => return T
    | IntV 1 _ => Error "int<1> value out of range"
    | _ => Error "type mismatch: boolean value must be int<1>"
`

val get_iref_addr_def = Define`
  get_iref_addr (v : value) : (addr or_error) =
    case v of
    | IRefV _ a => return a
    | _ => Error "type mismatch: expected iref"
`

val get_funcref_fnname_def = Define`
  get_funcref_fnname (v : value) : (fnname or_error) =
    case v of
    | FuncRefV n => return n
    | _ => Error "type mismatch: expected funcref"
`
val _ = export_theory()

