open Hifirrtl_lang
open Mlir_lang
open Extraction
open Extraction.HiFirrtl
open Extraction.Semantics
open Printf
(* 方便 ocaml 与 firtool 对齐的语法树结构 *)
type var = string

type hfexpr =
| Econst of Ast.fgtyp * Z.t
| Ecast of Ast.ucast * hfexpr
| Eprim_unop of Ast.eunop * hfexpr
| Eprim_binop of Ast.ebinop * hfexpr * hfexpr
| Emux of hfexpr * hfexpr * hfexpr
| Emultimux of hfexpr list
| Eref of var

let rec pp_expr out e =
  match e with
  | Econst (ty, s) -> output_string out "(econst "; Ast.pp_gtyp out ty; output_string out (", "^(Z.to_string s)^")")
  | Eref v -> output_string out ("(eref "^v^")")
  | Eprim_unop (op, e1) -> output_string out "(eprim_unop "; Ast.pp_unop out op; pp_expr out e1; output_string out ")"
  | Eprim_binop (bop, e1, e2) -> output_string out "(eprim_binop "; Ast.pp_binop out bop; pp_expr out e1; output_string out ", "; pp_expr out e2; output_string out ")"
  | Emux (e1,e2,e3)  -> output_string out "(emux "; pp_expr out e1; output_string out ", "; pp_expr out e2; output_string out ", "; pp_expr out e3; output_string out ")"
  | Ecast (s, e) -> output_string out "(ecast "; Ast.pp_cast out s; output_string out " "; pp_expr out e; output_string out ")"
  | Emultimux el  -> output_string out "(emultimux "; List.iter (fun c -> pp_expr out c; output_string out ", ") el;  output_string out ")"

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
                          | Env.Fuint n -> Econst (fgtyp_pair_to_string gt, Printfir.nat_of_bits bs)
                          | Env.Fsint n -> Econst (fgtyp_pair_to_string gt, Printfir.z_of_bits bs)
                          | _ -> Econst (fgtyp_pair_to_string gt, Z.of_int 0))
  | HiFirrtl.Eref (Eid v) -> Eref (pair_to_string (Obj.magic v) nummap tmap)
  | HiFirrtl.Eprim_unop (op, e) -> Eprim_unop (eunop_pair_to_string op, expr_pair_to_string e nummap tmap)
  | HiFirrtl.Eprim_binop (op, e1, e2) -> Eprim_binop (binop_pair_to_string op, 
    expr_pair_to_string e1 nummap tmap, expr_pair_to_string e2 nummap tmap)
  | HiFirrtl.Emux (e1,e2,e3) -> Emux (expr_pair_to_string e1 nummap tmap, 
    expr_pair_to_string e2 nummap tmap, expr_pair_to_string e3 nummap tmap)
  | HiFirrtl.Ecast (s, e) -> Ecast(cast_pair_to_string s, expr_pair_to_string e nummap tmap)

let dexpr_pair_to_string de nummap tmap =
  match de with
  | D_invalidated gt -> Econst (fgtyp_pair_to_string gt, Z.of_int 0)
  | D_fexpr e -> expr_pair_to_string e nummap tmap

let rec print_dexpr_list del nummap tmap = 
  match del with
  | [] -> output_string stdout ""
  | (v, de) :: tl -> let string_v = pair_to_string (Obj.magic v) nummap tmap in
    let string_e = dexpr_pair_to_string de nummap tmap in
    output_string stdout (string_v^" is cnct to "); pp_expr stdout string_e;
    output_string stdout "\n"; print_dexpr_list tl nummap tmap

let rec print_circuit_cmap cmap_list nummap tmap = 
  match cmap_list with
  | [] -> output_string stdout ""
  | (mv, cmap) :: tl -> printf "in module %d\n" (fst (Obj.magic mv)); 
    print_dexpr_list (PVM.elements cmap) nummap tmap; 
    print_circuit_cmap tl nummap tmap

let rec expand (mlir_cm : Mast.hfexpr Transhiast.StringMap.t) (whitelist : var list) (expr : Mast.hfexpr) : hfexpr =
  (* 判断变量是否在白名单中 *)
  let is_whitelist v = List.mem v whitelist in

  (* 展开单个变量（可能递归多次） *)
  let rec expand_var v =
    if is_whitelist v then
      Eref v
    else
      match Transhiast.StringMap.find_opt v mlir_cm with
      | None -> failwith ("Undefined variable: " ^ v)
      | Some e -> expand mlir_cm whitelist e   (* 递归展开定义体 *)
  in

  match expr with
  | Econst (t, z) -> Econst (t, z)
  | Ecast (c, v) -> Ecast (c, expand_var v)
  | Eprim_unop (op, v) -> Eprim_unop (op, expand_var v)
  | Eprim_binop (op, v1, v2) -> Eprim_binop (op, expand_var v1, expand_var v2)
  | Emux (v1, v2, v3) -> Emux (expand_var v1, expand_var v2, expand_var v3)
  | Emultimux vs -> Emultimux (List.map expand_var vs)
  | Eref v -> expand_var v

let rec compare_ocaml_mlir del nummap tmap mod_cm whitelist = 
  match del with
  | [] -> output_string stdout "compare finished\n"
  | (v, de) :: tl -> let string_v = pair_to_string (Obj.magic v) nummap tmap in
    let string_e = dexpr_pair_to_string de nummap tmap in (* ocaml 结果对应的 expr*)
    let mlir_e = Transhiast.StringMap.find string_v mod_cm in (* mlir 结果对应的 expr*)
    let e_after_substitute = expand mod_cm whitelist mlir_e in (* mlir 代入*)
    output_string stdout (string_v^" is cnct to\nocaml version : "); pp_expr stdout string_e;
    output_string stdout "\nfirtool version : "; pp_expr stdout e_after_substitute; output_string stdout "\n";
    compare_ocaml_mlir tl nummap tmap mod_cm whitelist
