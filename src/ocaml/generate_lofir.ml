open Arg
open Hifirrtl_lang
open Printf
open Extraction.Semantics
open Extraction.HiFirrtl
open Extraction.LowerTypes 
open Extraction.ExpandWhens

let () =
  let open Gc in
  let c = get () in
  set { c with
    minor_heap_size = 64 * 1024 * 1024;  
    major_heap_increment = 256;        
    space_overhead = 180;             
    max_overhead = 500;
    allocation_policy = 2; }

let args = [
  ]

let usage = "Usage: Genarating LoFIRRTL\n"

let fir_to_mlir filename =
  if Filename.check_suffix filename ".fir" then
    let len = String.length filename - 4 in 
    String.sub filename 0 len ^ ".mlir"
  else
    filename 

let anon file =
  let hif_ast = Parser.hiparse file in 
  let oc_fir = open_out (Transhiast.process_string file ".lo.fir") in

  let (((modmap, modmap_rev), _), map) = Transhiast_without_inline.mapcir hif_ast in 
  let hif_without_inline = Transhiast_without_inline.trans_cir hif_ast modmap map in
  (*output_string oc_fir "\norigin\n";
  Printfir.pp_fcircuit_fir oc_fir hif_without_inline;*)
  let ut0 = (Unix.times()).tms_utime in 
  match preprocess_subaccess hif_without_inline with
  | Some fcir -> let ut1 = (Unix.times()).tms_utime in 
    (*output_string oc_fir "\npreprocess subaccess\n";
    Printfir.pp_fcircuit_fir oc_fir fcir;
    printf "preprocess subaccess time : %f\n" (Float.sub ut1 ut0); *)

  (match lowertypes fcir with
  | Some c_lowertypes -> let ut2 = (Unix.times()).tms_utime in 
    printf "after lowerTypes :\n";
    Printfir_pair.pp_fcircuit_fir stdout c_lowertypes;
    printf "lowerTypes time : %fs\n" (Float.sub ut2 ut1); 
    printf "\nafter expandWhens :\n";
    (match expandWhens c_lowertypes with
    | Some ((c_expandwhens, conn_map), pvlist) -> let ut3 = (Unix.times()).tms_utime in 
      Printfir_pair.pp_fcircuit_fir stdout c_expandwhens;
      printf "expandWhens time : %fs\n" (Float.sub ut3 ut2); 
      printf "total time : %fs\n\n" (Float.sub ut3 ut0); 
      let string_cir = Transfast.trans_cir c_expandwhens modmap_rev map in 
      Ast.pp_fcircuit stdout string_cir;
      Ast.pp_fcircuit oc_fir string_cir; close_out oc_fir
    | None -> output_string stdout "error expandwhens\n";)
  | None -> output_string stdout "error lowertypes\n";) 
  | None -> output_string stdout "error subaccess preprocess\n"
  
let _ = parse args anon usage
