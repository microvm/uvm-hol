open HolKernel
open Parse
open Term
open listSyntax
open stringSyntax
open uvmIRTheory

structure ParseUIR : ParseUIR =
struct

  datatype ssa_scope =
      Local
    | Global

  datatype uir_token =
      Word     of string
    | Decl     of string
    | SSA      of (ssa_scope * string)
    | Num      of string
    | Parens   of (uir_token list)
    | Brackets of (uir_token list)
    | Type     of (uir_token list)
    | OpenBrace
    | CloseBrace
    | Eq
    | Colon
    | Arrow

  exception IllegalChar of char
  exception Unclosed of char
  exception ParseError of string

  fun is_name_char (c : char) : bool =
    Char.isAlphaNum c orelse c = #"." orelse c = #"_" orelse c = #"-"

  fun is_number_char (c : char) : bool =
    Char.isDigit c orelse c = #"." orelse c = #"+" orelse c = #"-"
      orelse c = #"e" orelse c = #"E"

  fun read_word (predicate : char -> bool)
                (chars : char list)
                : string * char list =
    let 
      fun read (c::cs) =
            if predicate c then
              let val (rest_word, rest_str) = read cs in
                (c::rest_word, rest_str)
              end
            else ([], c::cs)
        | read [] = ([], [])
      val (word, rest) = read chars
    in
      (String.implode word, rest)
    end

  fun lexer (chars : char list) : uir_token list * char list =
    case chars of
      #"."::cs =>
        let val (name, rest) = read_word Char.isAlpha cs in
          continue_lexer (Decl name) rest
        end
    | #"@"::cs =>
        let val (name, rest) = read_word is_name_char cs in
          continue_lexer (SSA (Global, name)) rest
        end
    | #"%"::cs =>
        let val (name, rest) = read_word is_name_char cs in
          continue_lexer (SSA (Local, name)) rest
        end
    | #"("::cs =>
        let val (contents, rest) = lexer cs in
          case rest of
            #")"::rest' => continue_lexer (Parens contents) rest'
          | _ => raise Unclosed #"("
        end
    | #")"::cs => ([], #")"::cs)
    | #"["::cs =>
        let val (contents, rest) = lexer cs in
          case rest of
            #"]"::rest' => continue_lexer (Brackets contents) rest'
          | _ => raise Unclosed #"["
        end
    | #"]"::cs => ([], #"]"::cs)
    | #"<"::cs =>
        let val (contents, rest) = lexer cs in
          case rest of
            #">"::rest' => continue_lexer (Type contents) rest'
          | _ => raise Unclosed #"<"
        end
    | #">"::cs => ([], #">"::cs)
    | #"{"::cs => continue_lexer OpenBrace cs
    | #"}"::cs => continue_lexer CloseBrace cs
    | #"="::cs => continue_lexer Eq cs
    | #":"::cs => continue_lexer Colon cs
    | #"-"::(#">"::cs) => continue_lexer Arrow cs
    | #"/"::(#"/"::_) => ([], [])
    | c::cs =>
        if Char.isSpace c then
          lexer cs
        else if Char.isAlpha c then
          let val (word, rest) = read_word Char.isAlpha (c::cs) in
            continue_lexer (Word word) rest
          end
        else if Char.isDigit c orelse c = #"+" orelse c = #"-" then
          let val (number, rest) = read_word is_number_char (c::cs) in
            continue_lexer (Num number) rest
          end
        else ([], c::cs)
    | [] => ([], [])
  and continue_lexer (token : uir_token)
                     (rest : char list)
                     : uir_token list * char list =
        let val (rest_tokens, rest_str) = lexer rest in
          (token::rest_tokens, rest_str)
        end

  fun tokenize (chars : char list) : uir_token list =
    let val (tokens, remaining) = lexer chars in
      case remaining of
        c::_ => raise IllegalChar c
      | [] => tokens
    end

  fun unquote (QUOTE str) =
        let
          fun find_loc_end (#"*"::(#")"::rest)) = rest
            | find_loc_end (c::cs) = find_loc_end cs
            | find_loc_end [] = String.explode str
        in
          find_loc_end (String.explode str)
        end
    | unquote (ANTIQUOTE _) = raise ParseError "antiquote not supported"

  fun unquote_all (quotes : 'a frag list) : char list =
    List.concat (map unquote quotes)

  val bin_ops : string list = [
    "ADD", "SUB", "MUL", "SDIV", "SREM", "UDIV", "UREM", "SHL", "LSHR", "ASHR",
    "AND", "OR", "XOR", "FADD", "FSUB", "FMUL", "FDIV", "FREM"
  ]

  val cmp_ops : string list = [
    "EQ", "NE", "SGE", "SGT", "SLE", "SLT", "UGE", "UGT", "ULE", "ULT",
    "FFALSE", "FTRUE", "FOEQ", "FOGT", "FOGE", "FOLT", "FOLE", "FONE", "FORD",
    "FUEQ", "FUGT", "FUGE", "FULT", "FULE", "FUNE", "FUNO"
  ]

  fun inst_from_tokens (global_context : string -> term)
                       (tokens : uir_token list)
                       : term =
    let
      fun ssa_var (Local, v) = ``Var ^(fromMLstring v)``
        | ssa_var (Global, v) = global_context v
      fun ssa_vars (SSA (Local, v)) = mk_list ([fromMLstring v], ``:ssavar``)
        | ssa_vars (Parens vs) =
            let 
              fun var (SSA (Local, v)) = fromMLstring v
                | var _ = raise ParseError "SSA var list contains non-SSA-var"
            in
              mk_list (map var vs, ``:ssavar``)
            end
        | ssa_vars _ = raise ParseError "expected SSA variable(s) before ="
    in
    case tokens of
    (* Identity insruction *)
      [SSA v, Eq, Word "ID", Type ty, SSA i] =>
        ``Assign [^(ssa_var v)] (Id ^(ssa_var i))``
    (* Binary operations *)
    | [vs, Eq, Word opn, Type ty, SSA l, SSA r] =>
        if exists (fn x => x = opn) bin_ops then
          let val opn' = mk_thy_const{Thy="uvmIR", Name=opn, Ty=``:bin_op``} in
            ``Assign ^(ssa_vars vs) (BinOp ^opn' ^(ssa_var l) ^(ssa_var r))``
          end
        else if exists (fn x => x = opn) cmp_ops then
          let val opn' = mk_thy_const{Thy="uvmIR", Name=opn, Ty=``:cmp_op``} in
            ``Assign ^(ssa_vars vs) (CmpOp ^opn' ^(ssa_var l) ^(ssa_var r))``
          end
        else raise ParseError ("not a binary operation: " ^ opn)
    | _ =>
        raise ParseError "not a valid instruction"
    end

  fun uir_inst (quotation : 'a frag list) : term =
    inst_from_tokens (fn v => raise ParseError ("no global variable @" ^ v))
                     (tokenize (unquote_all quotation))

  fun uir_terminst (quotation : 'a frag list) : term =
    raise ParseError "not yet implemented"

  fun uir_block (quotation : 'a frag list) : term =
    raise ParseError "not yet implemented"

  fun uir_bundle (quotation : 'a frag list) : term =
    raise ParseError "not yet implemented"
end

