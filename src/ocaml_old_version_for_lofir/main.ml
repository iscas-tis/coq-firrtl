open Arg
(* open Firrtl_lang*)
open Interpreter
       
let args = [
  ]

let usage = "Usage: demo"

let anon file =
  (*let f = (Parser.parse file) in*)
  let out =
    if file <> "" then
    open_out file else stdout
  in
  let _ = Interp.print_demo out in
  ()

let _ = parse args anon usage

