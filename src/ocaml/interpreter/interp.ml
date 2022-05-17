
open Extraction.FMaps
open Extraction.ExtrOcamlIntConv
open Extraction.Datatypes
open Extraction.BinNums
open Extraction.Var
open Extraction
open Extraction.Env
open Extraction.Firrtl

let interp_fmodule n m =
  let s0 = Store.empty in
  let te0 = TE.empty in
  let s' = LoFirrtl.run_fmodule m s0 te0 n in
  let te' = LoFirrtl.upd_typenv_fmodule m te0 s0 in
  (s', te')

let interp_fcircuit (c : fcircuit) (n : int) =
  match c with
  | Fcircuit (_, ms) -> List.map (interp_fmodule n) ms

let string_of_bits bs =
  String.concat "" (List.map (fun b -> if b then "1" else "0") (List.rev bs))

let vars_of_env (te:TE.env) = List.map (fun (v, _) -> v) (Obj.magic (TE.elements te))
                               
let print_res p =
  let (s, te) = p in
  (List.map (
      fun v ->
      let bs = Store.acc (Obj.magic v) s in
      let r = string_of_int (int_of_n (v)) ^ ": " ^ (string_of_bits bs) ^ "\n" in r)
  (vars_of_env te))
  
let print_store_all out c =
  List.iter (output_string out) (List.concat (List.map print_res (interp_fcircuit c 1)))


let interp_fmodule_demo n m =
  let s' = LoFirrtl.run_fmodule m st1 te1 n in
  (s', te1)
  
let print_demo out =
   List.iter (output_string out) (print_res (interp_fmodule_demo 10 fm1))
