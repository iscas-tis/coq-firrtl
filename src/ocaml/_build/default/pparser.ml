open Arg
open Firrtl_lang

  
(*let output_file = ref None*)
(*let file = "./demo/Accumulator.lo.fir"*)
(*let file = "./demo/demo"*)

let args = [
  ]

let usage = "Usage: pparse FILE\n"

let anon file =
  let f = (Parser.parse file) in
  let _ = Ast.pp_file stdout f in
  ()

let _ = parse args anon usage
