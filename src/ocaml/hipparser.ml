open Arg
open Hifirrtl_lang
open Extraction.Semantics

let args = [
  ]

let usage = "Usage: hipparse FILE\n"

let anon in_file =
  let hif_ast = (Parser.hiparse in_file) in 

  let flatten_cir = Inline.inline_cir stdout hif_ast in 
  let oc_fir = open_out (Transhiast.process_string in_file "_cons.txt") in

  (*Ast.pp_fcircuit oc_fir flatten_cir;*)
  match flatten_cir with
  | Ast.Fcircuit (v, ml) ->
    let ((map0, flag), tmap_ast) = Transhiast.mapcir flatten_cir in 
    (*StringMap.iter (fun key value -> output_string oc_fir (key^": ["); Stdlib.List.iter (fprintf oc_fir "%d;") value; output_string oc_fir "]\n") map0;*)
    let c = Transhiast.trans_cir flatten_cir map0 flag tmap_ast in 
    let _ = expandWhens c in
    ()

let _ = parse args anon usage
