open Arg
open Hifirrtl_lang
open Mlir_lang
open Printf
open Extraction.Semantics
open Extraction.HiFirrtl
open Extraction.ExpandConnects_inst 
open Extraction.ExpandWhens_inst

let args = [
  ]

let usage = "Usage: hipparse FILE\n"

let fir_to_mlir filename =
  if Filename.check_suffix filename ".fir" then
    let len = String.length filename - 4 in 
    String.sub filename 0 len ^ ".mlir"
  else
    filename 

(* 检查带入过程
let map =
  Transhiast.StringMap.empty
  |> Transhiast.StringMap.add "x" (Mast.Econst (Ast.Fuint 1, Z.of_int 5))
  |> Transhiast.StringMap.add "y" (Mast.Eprim_binop (Ast.Badd, "x", "z"))
  |> Transhiast.StringMap.add "z" (Mast.Eref "w")

let whitelist = ["w"; "out"]
let expr = Mast.Eprim_binop (Ast.Bmul, "y", "out")*)

let anon file =
  (*let result = Compare_conn_map.expand map whitelist expr in
  Compare_conn_map.pp_expr stdout result;*)

  (* mlir connection tree *)
  let mlir_file = fir_to_mlir file in
  let mlirf = Mparser.mlirparse mlir_file in 
  (*Mast.pp_modules stdout mlirf;*)
  output_string stdout "\nfirtool connection tree\n";
  let mlir_cm = Mast.cm_modl mlirf Mast.initmap_s in 
  Mast.StringMap.iter (fun mv mod_cm -> output_string stdout ("module "^mv^" :\n"); 
    Mast.StringMap.iter (fun v e -> output_string stdout (v^" -> "); Mast.pp_expr stdout e; output_string stdout "\n") mod_cm; 
    output_string stdout "\n") mlir_cm; 

  (* ocaml connection tree *)
  let hif_ast = Parser.hiparse file in 
  let oc_fir = (*open_out (Transhiast.process_string in_file "_cons.txt"*) stdout in
  
  let ((modmap, _), map) = Transhiast_without_inline.mapcir hif_ast in 
  let hif_without_inline = Transhiast_without_inline.trans_cir hif_ast modmap map in
  output_string oc_fir "\norigin\n";
  Printfir.pp_fcircuit_fir oc_fir hif_without_inline;

  output_string oc_fir "\nafter expandconnects :\n";
  (match expandconnects hif_without_inline with
  | Some c_expandconnects -> Printfir_pair.pp_fcircuit_fir oc_fir c_expandconnects;
    output_string oc_fir "\nafter expandwhens :\n";
    (match expandWhens c_expandconnects with
    | Some ((c_expandwhens, conn_map), pvlist) -> Printfir_pair.pp_fcircuit_fir oc_fir c_expandwhens;
    (* compare conn_map between mlir and ocaml *)
      Mast.StringMap.iter (fun mv mod_cm -> output_string stdout ("\nmodule "^mv^" :\n");
        let modnum = Mast.StringMap.find mv modmap in
        let ((map0, map1), tmap) = Mast.StringMap.find mv map in
        let modnump = Obj.magic (modnum, 0) in
        match PVM.find modnump conn_map with
        | Some ocaml_mod_cm -> match PVM.find modnump pvlist with
          | Some mod_pvlist -> 
            let whitelist = List.map (fun pv -> Compare_conn_map.pair_to_string (Obj.magic pv) map1 tmap) mod_pvlist in 
            Compare_conn_map.compare_ocaml_mlir (PVM.elements ocaml_mod_cm) map1 tmap mod_cm whitelist
          | _ -> output_string stdout ("find module "^mv^" in whitelist error\n");
        | _ -> output_string stdout ("find module "^mv^" in ocaml cm error\n");
        ) mlir_cm; 

    | None -> output_string stdout "error expandwhens\n";)
  | None -> output_string stdout "error expandconnects\n";)

  (*let map_p2s = Transhiast.StringMap.fold (fun key ft acc -> let base_num = Obj.magic (Stdlib.List.hd (Stdlib.List.rev (Transhiast.StringMap.find key map0))) in
        Pair2string.store_pair key 0 base_num ft acc) tmap_ast Transhiast.IntPairMap.empty in

    (match expandconnects c with
    | Some c_expandconnects -> (*Printfir_pair.pp_fcircuit_fir oc_fir v c_expandconnects; 
      output_string oc_fir "\nafter expandwhens :\n";*)
      (match expandWhens c_expandconnects with
      | Some ((c_expandwhens, conn_map), pvlist) -> (*Printfir_pair.pp_fcircuit_fir oc_fir v c_expandwhens;*)
        output_string oc_fir "\nocaml connection map :\n";
        Compare_conn_map.print_circuit_cmap (PVM.elements conn_map) map1 tmap_ast; 
        
        (*output_string oc_fir "\nfirtool connection map after substitute :\n";
        let whitelist = List.map (fun pv -> Compare_conn_map.pair_to_string (Obj.magic pv) map1 tmap_ast) pvlist in 
        Mast.StringMap.iter (fun mv mod_cm -> output_string stdout ("module "^mv^" :\n");
          Mast.StringMap.iter (fun v e -> output_string stdout (v^" -> "); 
            let e_after_substitute = Compare_conn_map.expand mod_cm whitelist e in 
            Compare_conn_map.pp_expr stdout e_after_substitute; output_string stdout "\n") mod_cm; 
          output_string stdout "\n") mlir_cm; 

        Compare_conn_map.compare_ocaml_mlir (PVM.elements conn_map) map1 tmap_ast (Transhiast.StringMap.find v mlir_cm) whitelist;*)
        
        close_out oc_fir;
      | _ -> output_string stdout "error expandwhens\n"; close_out oc_fir;)*)

let _ = parse args anon usage
