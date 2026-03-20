open Arg
open Hifirrtl_lang
open Printf
open Extraction.Semantics
open Extraction.HiFirrtl
open Extraction.HiEnv

let args = [
  ]

let usage = "Usage: hipparse FILE\n"

let print_dexpr de =
  match de with
  | D_invalidated gt -> Printfir_pair.pp_fgtyp_fir stdout gt
  | D_fexpr e -> Printfir_pair.pp_expr_fir stdout e 

let rec print_dexpr_list del = 
  match del with
  | [] -> fprintf stdout ""
  | (v, de) :: tl -> fprintf stdout "_%d_%d is cnct to " (fst (Obj.magic v)) (snd (Obj.magic v)); print_dexpr de; fprintf stdout "\n"; print_dexpr_list tl

let anon in_file =
  let hif_ast = (Parser.hiparse in_file) in 

  let flatten_cir = Inline.inline_cir stdout hif_ast in 
  let oc_fir = (*open_out (Transhiast.process_string in_file "_cons.txt"*) stdout in

  Ast.pp_fcircuit oc_fir flatten_cir;
  match flatten_cir with
  | Ast.Fcircuit (v, ml) ->
    let (((map0, _), flag), tmap_ast) = Transhiast.mapcir flatten_cir in (* map0 is string to num, map1 is num to string *)
    Transhiast.StringMap.iter (fun key value -> output_string oc_fir (key^": ["); Stdlib.List.iter (fprintf oc_fir "%d;") value; output_string oc_fir "]\n") map0;
    let map_p2s = Transhiast.StringMap.fold (fun key ft acc -> let base_num = Obj.magic (Stdlib.List.hd (Stdlib.List.rev (Transhiast.StringMap.find key map0))) in
        Pair2string.store_pair key 0 base_num ft acc) tmap_ast Transhiast.IntPairMap.empty in
    let c = Transhiast.trans_cir flatten_cir map0 flag tmap_ast in 
    output_string oc_fir "\norigin\n";
    Printfir.pp_fcircuit_fir oc_fir v c;
    output_string oc_fir "\nafter expandconnects :\n";
    (match expandconnects c with
    | Some c_expandconnects -> Printfir_pair.pp_fcircuit_fir oc_fir v c_expandconnects; 
      output_string oc_fir "\nafter expandwhens :\n";
      (match expandWhens c_expandconnects with
      | Some (c_expandwhens, conn_map) -> Printfir_pair.pp_fcircuit_fir oc_fir v c_expandwhens;
        output_string oc_fir "\nocaml connection map :\n";
        print_dexpr_list (PVM.elements conn_map); close_out oc_fir;
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
