open HolKernel Parse boolLib bossLib;

(* A monad for sum types, roughly equivalent to Haskell's `Either` monad. It
   favors the left side of a sum type (although `bind_right` can be used to bind
   over the right side instead). Also contains several utility functions for sum
   types.
*)
val _ = new_theory "sumMonad"

val bind_left_def = Define`
  bind_left (sum : α + β) (fn : α -> γ + β) : γ + β =
    case sum of
    | INL a => fn a
    | INR b => INR b
`

val bind_right_def = Define`
  bind_right (sum : α + β) (fn : β -> α + γ) : α + γ =
    case sum of
    | INL a => INL a
    | INR b => fn b
`

val lift_left_def = Define`
  lift_left (f : α -> β) (sum : α + γ) : β + γ =
    case sum of
    | INL a => INL (f a)
    | INR b => INR b
`

val lift_right_def = Define`
  lift_right (f : α -> β) (sum : γ + α) : γ + β =
    case sum of
    | INL a => INL a
    | INR b => INR (f b)
`

(* Merge left side of sum into right side *)
val merge_right_def = Define`
  merge_right (f : α -> β) (sum : α + β) : β =
    case sum of
    | INL a => f a
    | INR b => b
`

(* Merge right side of sum into left side *)
val merge_left_def = Define`
  merge_left (f : β -> α) (sum : α + β) : α =
    case sum of
    | INL a => a
    | INR b => f b
`

val left_set_def = Define`
  left_set (sum : α + β) : α set =
    case sum of
    | INL a => {a}
    | INR _ => {}
`

val right_set_def = Define`
  right_set (sum : α + β) : β set =
    case sum of
    | INL _ => {}
    | INR b => {b}
`

(* Left-biased sum monad definition *)
val _ = overload_on ("return", ``INL``)
val _ = overload_on ("monad_bind", ``bind_left``)
val _ = overload_on ("monad_unitbind", ``λm1 m2. bind_left m1 (K m2)``)

(* Bonus: Haskellish monad operators *)
val _ = set_fixity ">>=" (Infixr 660)
val _ = set_fixity ">>" (Infixr 660)
val _ = overload_on (">>=", ``monad_bind``)
val _ = overload_on (">>", ``monad_unitbind``)

val _ = export_theory ()

