
open Firrtl_lang

  
let output_file = ref None
let file = "./demo/demo"
                
let pparse file =
  let f = (Parser.parse file) in
  let out =
    match !output_file with
    | None -> stdout
    | Some fn -> open_out fn in
  let _ = Ast.pp_file out f in
  let _ = flush out in
  close_out out


let _ =  pparse file
