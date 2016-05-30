open HolKernel Parse boolLib bossLib;

open stringTheory

(*  Defines the `or_error` monad, a simple sum type equivalent to
   `Either α String` in Haskell. Instances of `or_error` are constructed using
   the `OK` and `Error` constructors. The function `expect` can convert an
   `option` to an `or_error`, with a specific error message for `NONE`.
*)
val _ = new_theory "errorMonad";

val _ = Datatype`
  or_error =
  | OK α
  | Error string
`

(* The `return` operation for `or_error` *)
val or_error_return_def = Define`
  or_error_return (x:α) = OK x
`

(* The `bind` operation for `or_error` *)
val or_error_bind_def = Define`
  or_error_bind (x : α or_error) (f : α -> β or_error) : β or_error =
    case x of
    | OK y => f y
    | Error s => Error s
`

(* Overload the default monad functions, making `or_error` usable with
   do-notation.
*)
val _ = overload_on ("return", ``or_error_return``)
val _ = overload_on ("monad_bind", ``or_error_bind``)
val _ = overload_on ("monad_unitbind", ``λm1 m2. or_error_bind m1 (K m2)``)

(* `expect opt msg` converts the `α option` `opt` into an `α or_error`, using
   the error message `msg` if `NONE` is encountered.
*)
val expect_def = Define`
  (* expect : α option -> string -> α or_error *)
  (expect NONE msg = Error msg) ∧
  (expect (SOME x) _ = OK x)
`

val _ = export_theory ()

