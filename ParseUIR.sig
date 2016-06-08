open HolKernel

signature ParseUIR =
sig
  val uir_inst : 'a frag list -> term
  val uir_terminst : 'a frag list -> term
  val uir_block : 'a frag list -> term
  val uir_bundle : 'a frag list -> term
  exception IllegalChar of char
  exception Unclosed of char
  exception ParseError of string
end

