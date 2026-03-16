open Arg
open Hifirrtl_lang
open Printf
open Extraction.Semantics
open Extraction.HiFirrtl
open Extraction.HiEnv

let args = [
  ]

let usage = "Usage: hipparse FILE\n"

let anon in_file =
  let hif_ast = (Parser.hiparse in_file) in 

  let flatten_cir = Inline.inline_cir stdout hif_ast in 
  let oc_fir = (*open_out (Transhiast.process_string in_file "_cons.txt"*) stdout in

  Ast.pp_fcircuit oc_fir flatten_cir;
  match flatten_cir with
  | Ast.Fcircuit (v, ml) ->
    let ((map0, flag), tmap_ast) = Transhiast.mapcir flatten_cir in 
    Transhiast.StringMap.iter (fun key value -> output_string oc_fir (key^": ["); Stdlib.List.iter (fprintf oc_fir "%d;") value; output_string oc_fir "]\n") map0;
    let c = Transhiast.trans_cir flatten_cir map0 flag tmap_ast in 
    output_string oc_fir "\norigin\n";
    Printfir.pp_fcircuit_fir oc_fir v c;
    output_string oc_fir "\nafter expandconnects :\n";
    (match expandconnects c with
    | Some c_expandconnects -> Printfir_pair.pp_fcircuit_fir oc_fir v c_expandconnects; 
      output_string oc_fir "\nafter expandwhens :\n";
      (match expandWhens c_expandconnects with
      | Some c_expandwhens -> Printfir_pair.pp_fcircuit_fir oc_fir v c_expandwhens; close_out oc_fir;
      | _ -> output_string stdout "error expandwhens\n"; close_out oc_fir;)
      (*match c_expandconnects with
        | Fcircuit (fv, l) ->
          (match l with
           | [] -> output_string oc_fir "expandwhens find empty module list\n"
           | m :: l0 ->
             (match l0 with
              | [] ->
                (match Sem_HiFP.circuit_tmap (Fcircuit (fv, (m :: []))) with
                 | Some tmap -> output_string oc_fir "expandwhens tmap is built\n"
                   (*match coq_ExpandWhens_fun m tmap with
                    | Some fm -> Some (Fcircuit (fv, (fm :: [])))
                    | None -> None*)
                 | None -> output_string oc_fir "expandwhens build tmap fail\n")
              | _ :: _ -> output_string oc_fir "expandwhens find two long module list\n"))
      *)
      ;
    | _ -> output_string stdout "error expandconnects\n";);
    ()

let _ = parse args anon usage
