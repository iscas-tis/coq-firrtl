open Arg
open Hifirrtl_lang
open Printf
open Mlir_lang
open Extraction.Semantics
open Extraction.HiFirrtl
open Extraction.HiEnv
open Extraction

let args = [
  ]

let usage = "Usage: hipparse FILE\n"

(* 根据 pair of num 的 cm, 转换为 string 的 cm. 把(2,1), 先根据 map1, 找到 2 对应的 string 和 ftype, 再根据 offset 和 ftype 对应到新名 *)

let rec offset_to_string base_id offset = function
| Ast.Gtyp gt ->
  if offset = 0 then base_id else "wrong name"
| Atyp (atyp, n) ->
  let index = offset / (Ast.size_of_ftype atyp) in
  let offset_new = offset mod (Ast.size_of_ftype atyp) in
  offset_to_string (base_id^"_"^(string_of_int index)) offset_new atyp
| Btyp ff -> offset_to_string_b base_id offset ff

and offset_to_string_b base_id offset = function
| Ast.Fnil -> base_id
| Fflips (v0, fl, ft, ff') ->
  if offset < (Ast.size_of_ftype ft)
    then offset_to_string (base_id^"_"^v0) offset ft
  else offset_to_string_b base_id (offset - (Ast.size_of_ftype ft)) ff'

let pair_to_string pv nummap tmap =
  let base_id = Transhiast.IntMap.find (fst pv) nummap in 
  let ftype = Transhiast.StringMap.find base_id tmap in 
  offset_to_string base_id (snd pv) ftype


let fgtyp_pair_to_string gt = 
  match gt with
  | Env.Fuint s -> Ast.Fuint s
  | Env.Fsint s -> Ast.Fsint s
  | Env.Fclock -> Ast.Fclock
  | Env.Freset -> Ast.Freset
  | Env.Fasyncreset -> Ast.Fasyncreset

let cast_pair_to_string ucast = 
  match ucast with
  | Firrtl.AsUInt -> Ast.AsUInt
  | Firrtl.AsSInt -> Ast.AsSInt
  | Firrtl.AsClock -> Ast.AsClock
  | Firrtl.AsAsync -> Ast.AsAsync

let eunop_pair_to_string eunop = 
  match eunop with
  | Firrtl.Upad s -> Ast.Upad s
  | Firrtl.Ushl s -> Ast.Ushl s
  | Firrtl.Ushr s -> Ast.Ushr s 
  | Firrtl.Ucvt -> Ast.Ucvt
  | Firrtl.Uneg -> Ast.Uneg
  | Firrtl.Unot -> Ast.Unot
  | Firrtl.Uandr -> Ast.Uandr
  | Firrtl.Uorr -> Ast.Uorr
  | Firrtl.Uxorr -> Ast.Uxorr
  | Firrtl.Uextr (s1, s2) -> Ast.Uextr (s1, s2)
  | Firrtl.Uhead s -> Ast.Uhead s
  | Firrtl.Utail s -> Ast.Utail s

let cmp_pair_to_string cmp = 
  match cmp with
  | Firrtl.Blt -> Ast.Blt 
  | Firrtl.Bleq -> Ast.Bleq
  | Firrtl.Bgt -> Ast.Bgt
  | Firrtl.Bgeq -> Ast.Bgeq
  | Firrtl.Beq -> Ast.Beq
  | Firrtl.Bneq -> Ast.Bneq

let binop_pair_to_string binop = 
  match binop with
  | Firrtl.Badd -> Ast.Badd
  | Firrtl.Bsub -> Ast.Bsub
  | Firrtl.Bmul -> Ast.Bmul
  | Firrtl.Bdiv -> Ast.Bdiv
  | Firrtl.Brem -> Ast.Brem
  | Firrtl.Bcomp s -> Ast.Bcomp (cmp_pair_to_string s)
  | Firrtl.Bdshl -> Ast.Bdshl
  | Firrtl.Bdshr -> Ast.Bdshr
  | Firrtl.Band -> Ast.Band
  | Firrtl.Bor -> Ast.Bor
  | Firrtl.Bxor -> Ast.Bxor
  | Firrtl.Bcat -> Ast.Bcat

let rec expr_pair_to_string e nummap tmap = 
  match e with
  | HiFirrtl.Econst (gt, bs) -> (match gt with
                          | Env.Fuint n -> Ast.Econst (fgtyp_pair_to_string gt, Printfir.nat_of_bits bs)
                          | Env.Fsint n -> Ast.Econst (fgtyp_pair_to_string gt, Printfir.z_of_bits bs)
                          | _ -> Ast.Econst (fgtyp_pair_to_string gt, Z.of_int 0))
  | HiFirrtl.Eref (Eid v) -> Ast.Eref (Eid (pair_to_string (Obj.magic v) nummap tmap))
  | HiFirrtl.Eprim_unop (op, e) -> Ast.Eprim_unop (eunop_pair_to_string op, expr_pair_to_string e nummap tmap)
  | HiFirrtl.Eprim_binop (op, e1, e2) -> Ast.Eprim_binop (binop_pair_to_string op, 
    expr_pair_to_string e1 nummap tmap, expr_pair_to_string e2 nummap tmap)
  | HiFirrtl.Emux (e1,e2,e3) -> Ast.Emux (expr_pair_to_string e1 nummap tmap, 
    expr_pair_to_string e2 nummap tmap, expr_pair_to_string e3 nummap tmap)
  | HiFirrtl.Ecast (s, e) -> Ast.Ecast(cast_pair_to_string s, expr_pair_to_string e nummap tmap)

let dexpr_pair_to_string de nummap tmap =
  match de with
  | D_invalidated gt -> Ast.Econst (fgtyp_pair_to_string gt, Z.of_int 0)
  | D_fexpr e -> expr_pair_to_string e nummap tmap

let rec print_dexpr_list del nummap tmap = 
  match del with
  | [] -> output_string stdout ""
  | (v, de) :: tl -> let string_v = pair_to_string (Obj.magic v) nummap tmap in
    let string_e = dexpr_pair_to_string de nummap tmap in
    output_string stdout (string_v^" is cnct to "); Ast.pp_expr stdout string_e;
    output_string stdout "\n"; print_dexpr_list tl nummap tmap

let fir_to_mlir filename =
  if Filename.check_suffix filename ".fir" then
    let len = String.length filename - 4 in 
    String.sub filename 0 len ^ ".mlir"
  else
    filename 

let anon file =
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
  let flatten_cir = Inline.inline_cir stdout hif_ast in 
  let oc_fir = (*open_out (Transhiast.process_string in_file "_cons.txt"*) stdout in
  (*Ast.pp_fcircuit oc_fir flatten_cir;*)
  match flatten_cir with
  | Ast.Fcircuit (v, ml) ->
    let (((map0, map1), flag), tmap_ast) = Transhiast.mapcir flatten_cir in (* map0 is string to num, map1 is num to string *)
    Transhiast.StringMap.iter (fun key value -> output_string oc_fir (key^": ["); Stdlib.List.iter (fprintf oc_fir "%d;") value; output_string oc_fir "]\n") map0;
    Transhiast.IntMap.iter (fun key value -> output_string oc_fir ((string_of_int key)^" is "^ value^"\n")) map1;
    let map_p2s = Transhiast.StringMap.fold (fun key ft acc -> let base_num = Obj.magic (Stdlib.List.hd (Stdlib.List.rev (Transhiast.StringMap.find key map0))) in
        Pair2string.store_pair key 0 base_num ft acc) tmap_ast Transhiast.IntPairMap.empty in
    let c = Transhiast.trans_cir flatten_cir map0 flag tmap_ast in 
    (*output_string oc_fir "\norigin\n";
    Printfir.pp_fcircuit_fir oc_fir v c;
    output_string oc_fir "\nafter expandconnects :\n";*)
    (match expandconnects c with
    | Some c_expandconnects -> (*Printfir_pair.pp_fcircuit_fir oc_fir v c_expandconnects; 
      output_string oc_fir "\nafter expandwhens :\n";*)
      (match expandWhens c_expandconnects with
      | Some (c_expandwhens, conn_map) -> (*Printfir_pair.pp_fcircuit_fir oc_fir v c_expandwhens;*)
        output_string oc_fir "\nocaml connection map :\n";
        print_dexpr_list (PVM.elements conn_map) map1 tmap_ast; close_out oc_fir;
      | _ -> output_string stdout "error expandwhens\n"; close_out oc_fir;))

let _ = parse args anon usage
