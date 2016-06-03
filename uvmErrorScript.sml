open HolKernel Parse boolLib bossLib;

open stringTheory

(* Defines the `uvm_error` type and the `or_error` monad. Instances of
   `or_error` are constructed using `return` or one of the constructor functions
   (`state_error`, `undef_error`, `type_error`).
*)
val _ = new_theory "uvmError"

val _ = Datatype`
  uvm_error =
  | InvalidState string
  | UndefinedBehavior string
  | TypeMismatch string
`

val _ = type_abbrev("or_error", ``:α + uvm_error``)
val _ = overload_on("OK", ``INL : α -> α or_error``)
val _ = overload_on("Error", ``INR : uvm_error -> α or_error``)

val state_error_def = Define`
  state_error (msg : string) : α or_error = Error (InvalidState msg)
`

val undef_error_def = Define`
  undef_error (msg : string) : α or_error = Error (UndefinedBehavior msg)
`

val type_error_def = Define`
  type_error (msg : string) : α or_error = Error (TypeMismatch msg)
`

(* `assert cond err` asserts that `cond` is true, returning the given error if
   it isn't.
*)
val assert_def = Define`
  assert (cond : bool) (err : one or_error) : one or_error =
    if cond then OK () else err
`

(* `expect opt err` converts the `α option` `opt` into an `α or_error`, using
   the given error if `NONE` is encountered.
*)
val expect_def = Define`
  (* expect : α option -> α or_error -> α or_error *)
  (expect NONE err = err) ∧
  (expect (SOME x) _ = OK x)
`

val _ = export_theory ()

