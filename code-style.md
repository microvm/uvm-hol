# uvm-hol Code Style Guidelines

- Indent with 2 spaces.
- Data constructors use `PascalCase`, data types and identifiers use `lowercase_with_underscores`. This applies to both SML and HOL code.
- Multiline datatype declarations and `case` statements should have a leading `|` character, and `|` should not be indented.
  ```sml
  (* CORRECT: *)
  case x of
  | Foo => do_something_with_foo()
  | Bar => do_something_with_bar()
  
  (* INCORRECT: *)
  case x of
      Foo => do_something_with_foo()
    | Bar => do_something_with_foo()
  ```
- Multiline HOL4 code should start on a new line, and should start at 1 level of indentation above the containing SML code. The closing backquote should be on its own line.
  ```sml
  (* CORRECT: *)
  let foo_def = Define`
    foo x y = x + y
  `
  
  (* INCORRECT: *)
  let foo_def = Define`foo x y =
        x + y`
  
  (* INCORRECT: *)
  let foo_def = Define`
      foo x y = x + y
  `
  ```
- For complex nested expressions, prefer adding newlines over using Lisp-style hanging indentation.
  ```sml
  (* PREFERRED: *)
  foo x y = 
    case x of
    | Foo -> Foo (
        91,
        (case y of
         | Bar -> baz),
        Quux)
    | Bar -> 0
  
  (* LESS PREFERRED: *)
  (* Although this is somewhat more readable, it can be difficult to maintain.
     Also, once an expression like this becomes very wide, it becomes difficult to read. *)
  foo x y = case x of
            | Foo -> Foo (91, (case y of
                               | Bar -> baz), Quux)
            | Bar -> 0
  ```
- Prefer unicode HOL operators over their ASCII equivalents.
