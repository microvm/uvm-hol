open HolKernel Parse boolLib bossLib;

open uvmTypesTheory;

val _ = new_theory "uvmValues";

val _ = type_abbrev("addr", ``:num``)  (* non-local memory addresses *)

(*tmp: ==========================================================*)
val _ = type_abbrev("float32", ``:num``)
val _ = type_abbrev("float64", ``:num``)
val _ = type_abbrev("int",     ``:num``)
(*===============================================================*)


val _ = Datatype`
   value =
     Int num int
   | IRef uvmType addr
   | FloatV float32
   | DoubleV float64
   (* not sure if these are storable-in-register values
   | StructV (value list)
   | ArrayV (value list)
   | Hybrid (value list) (value list) *)
   | VectorV (value list)
   | FuncRefV addr
   | UFuncRefV addr
`;

(* TEMPORARY *)
val Int32_def = Define`
    Int32 = Int 32`;

val value_add_def = Define`
value_add v1 v2 =
     case (v1, v2) of
         (Int sz1 n1, Int sz2 n2) => if sz1 = sz2 then SOME (Int sz1 (n1 + n2))
                                     else NONE
      |  (Int _ _, _) => NONE
      | _ => NONE
`;
val _ = overload_on ("+", ``value_add``);

val value_div_def = Define`
    value_div v1 v2 =
             case (v1,v2) of
                 (Int sz1 n1, Int sz2 n2) => if (sz2=sz1 ∧ n2<>0) then SOME (Int sz1 (n1 DIV n2))
                                             else NONE
               | _ => NONE
`;
val _ = overload_on ("DIV", ``value_div``);

val value_to_address = Define`
    value_to_address (v:value) : (addr option) = case v of
        Int sz1 n1 => SOME n1
      | _ => NONE
`;
                    
val _ = export_theory();
