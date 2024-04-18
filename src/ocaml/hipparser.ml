open Arg
open Hifirrtl_lang

let args = [
  ]

let usage = "Usage: hipparse FILE\n"

let anon file =
  let f = (Parser.hiparse file) in
  let _ = Ast.pp_file stdout f in
  ()

let _ = parse args anon usage
