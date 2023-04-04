open Extraction.NBitsDef
open Printf
open Firrtl_lang
open Big_int_Z

let lowf = "./demo/demo1"
let file = "./demo/input.txt"

let parse f =
  let lexbuf = Lexing.from_channel (open_in f) in
  FirrtlParser.file FirrtlLexer.token lexbuf

let lowf_ast = parse lowf

let rec gen size wid l =
  if size = 0 then
    l
  else
    let n = Z.of_int (if wid > (Z.of_int 29) then (Random.int ((Z.to_int(Z.pow (Z.of_int 2) (30))) - 1)) else (Random.int (Z.to_int(Z.pow (Z.of_int 2) (Z.to_int wid))))) in
    let list = List.cons n l in
    gen (size - 1) wid list

let rec gen_neg size wid l =
  if size = 0 then
    l
  else
    let b = Random.bool () in
    let n = Z.of_int (if wid > (Z.of_int 30) then (Random.int ((Z.to_int(Z.pow (Z.of_int 2) (30))) - 1)) else (Random.int (Z.to_int(Z.pow (Z.of_int 2) ((Z.to_int wid)-1))))) in
    let list = (if b = true then 
      List.cons n l 
    else
      List.cons (Z.neg n) l) in
    gen_neg (size - 1) wid list

let bits_of_z (size : int) (z : Z.t) : bits =
  let binstr =
    if z >= Z.zero then
      Z.format ("%0" ^ (string_of_int size) ^ "b") z
    else
      Z.format ("%0" ^ (string_of_int size) ^ "b")
        (Z.add (Z.pow (Z.of_int 2) size) z) in
  let rec helper i max str res =
    if i >= max then res
    else match String.get str i with
    | '0' -> helper (succ i) max str (false::res)
    | '1' -> helper (succ i) max str (true::res)
    | _ -> assert false in
  helper 0 (String.length binstr) binstr []

let nat_of_bits (bv : bits) : big_int = 
  let rec helper i max lst res =
    if i >= max then res
    else match List.nth bv i with
    | false -> helper (succ i) max lst res
    | true -> helper (succ i) max lst (add_big_int (power_int_positive_int (2) i) res) in
  helper 0 (List.length bv) bv zero_big_int

let z_of_bits (bv : bits) : big_int = 
  let (v,sign) = splitmsb bv in
  if sign then (sub_big_int (nat_of_bits v) (power_int_positive_int (2) ((List.length bv)-1))) (*最高位true，负数*)
  else
    nat_of_bits v

module StringMap = Map.Make(String)
module IntMap = Map.Make(Int)
let intmap = IntMap.empty
let map = StringMap.empty
let lst = []

(*val t_generate_map : string -> fgtyp -> StringMap -> StringMap*)

let t_generate_map v ty inp_map inp_lst ul clks =
     match ty with
       | Ast.Fuint s -> let rand_l = List.map (bits_of_z (Z.to_int s)) (gen clks s []) 
      in (StringMap.add v rand_l inp_map, List.cons v inp_lst, List.cons v ul)
       | Ast.Fsint s -> let rand_l = List.map (bits_of_z (Z.to_int s)) (gen_neg clks s []) 
      in (StringMap.add v rand_l inp_map, List.cons v inp_lst, ul)
       | Ast.Fclock -> let rand_l = List.map (bits_of_z 1) (gen clks (Z.of_int 1) []) 
      in (StringMap.add v rand_l inp_map, List.cons v inp_lst, List.cons v ul)

let o_generate_map v ty inp_map inp_lst ul =
     match ty with
       | Ast.Fuint _ -> (StringMap.add v [] inp_map, inp_lst, ul)
       | Ast.Fsint _ -> (StringMap.add v [] inp_map, inp_lst, ul)
       | Ast.Fclock -> (inp_map, inp_lst, ul)

(*val p_generate_map : StringMap -> fport -> StringMap*)
let p_generate_map clks (inp_map,inp_lst,ul) p = 
  match p with
    | Ast.Finput (v, ty) -> t_generate_map v ty inp_map inp_lst ul clks
    | Ast.Foutput (v, ty) -> o_generate_map v ty inp_map inp_lst ul

(*val m_generate_map : StringMap -> fmod -> StringMap*)
let m_generate_map clks cv (inp_map,inp_lst,ul) m = 
  match m with
    | Ast.FInmod (mv, pl, _) -> if (String.equal mv cv) then List.fold_left (p_generate_map clks) (inp_map,inp_lst,ul) pl
                                else (inp_map,inp_lst,ul)
    | Ast.FExmod (mv, pl, _) -> if (String.equal mv cv) then List.fold_left (p_generate_map clks) (inp_map,inp_lst,ul) pl
                                else (inp_map,inp_lst,ul)
              
(*val generate_map : StringMap -> StringMap*)
let generate_map lowf_ast clks (inp_map,inp_lst,ul) =
  match lowf_ast with
    | (cv, fmod) -> List.fold_left (m_generate_map clks cv) (inp_map,inp_lst,ul) fmod

(*extract input intmap*)
let p_extract_i ml imap (m,l,ll) p = 
  match p with
    | Ast.Finput (v, ty) -> (match ty with
      | Ast.Fuint _ -> (IntMap.add (StringMap.find v ml) (StringMap.find v imap) m, List.cons (StringMap.find v ml) l,List.cons (StringMap.find v ml) ll)
      | Ast.Fsint _ -> (IntMap.add (StringMap.find v ml) (StringMap.find v imap) m, List.cons (StringMap.find v ml) l,ll)
      | Ast.Fclock -> (IntMap.add (StringMap.find v ml) (StringMap.find v imap) m, List.cons (StringMap.find v ml) l,List.cons (StringMap.find v ml) ll))
      
    | Ast.Foutput (v, ty) -> (match ty with
      | Ast.Fuint _ -> (IntMap.add (StringMap.find v ml) [] m, l,List.cons (StringMap.find v ml) ll)
      | Ast.Fsint _ -> (IntMap.add (StringMap.find v ml) [] m, l,ll)
      | Ast.Fclock -> (m,l,ll))

let m_extract_i mainmap imap m = 
  match m with
    | Ast.FInmod (_, pl, _) -> List.fold_left (p_extract_i mainmap imap) (IntMap.empty,[],[]) pl
    | Ast.FExmod _ -> (IntMap.empty,[],[])

let rec print_list oc l = 
  match l with
    | [] -> ()
    | h::t -> fprintf oc "%d " h; print_list oc t

let rec printf0_list l = 
  match l with
    | [] -> ()
    | h::t -> printf "%s " h; printf0_list t

let rec printf00_list l = 
  match l with
    | [] -> printf "\n"
    | h::t -> printf "%b " h; printf00_list t
(*
let () =
  let clks = 10 in
  let (inp_bitsmap, inp_lst, ulst) = generate_map clks (map, lst, lst) in
  let my2Z k = 
    (if (List.mem k ulst) then (List.map nat_of_bits)
    else (List.map z_of_bits)) in
  let inp_map = StringMap.map (List.map Z.to_int) (StringMap.mapi my2Z inp_bitsmap) in
  
  let (cm, mm, maplist, _) = Transast1. lowf_ast map map map 0 in
  let (inp_intmap,inp_intlst,uintlst) = extract_i maplist inp_bitsmap in(*uintlst*)
  let (_,olst,ointlst) = extract_o maplist in(*ointlst*)
    
  
  let mytoZ k = 
    (if (List.mem k uintlst) then (List.map nat_of_bits)
    else (List.map z_of_bits)) in
  let out_map = IntMap.map (List.map string_of_big_int) (IntMap.mapi mytoZ out_bitsmap) in
  
    let oc = open_out file in
    fprintf oc "input:\n";
    List.iter (fprintf oc "%s ") inp_lst;
    fprintf oc "\n";
    fprintf oc "output:\n";
    List.iter (fprintf oc "%s ") olst;
    fprintf oc "\n";
    fprintf oc "valmap:\n";
    StringMap.iter (fun key value -> if (List.mem key inp_lst) then (fprintf oc "%s:" key; List.iter (fprintf oc " %d") value; fprintf oc "\n")) inp_map;
    fprintf oc "answer:\n";
    IntMap.iter (fun key value -> (fprintf oc "%d:" key; List.iter (fprintf oc " %s") (value)); fprintf oc "\n") out_map;
    fprintf oc "label:\n";
    StringMap.iter (fun key value -> (fprintf oc "Circuit %s:%d" key value); fprintf oc "\n") cm;
    StringMap.iter (fun key value -> (fprintf oc "Module %s:%d" key value); fprintf oc "\n") mm;
    StringMap.iter (fun _ value -> (StringMap.iter (fun key value -> (fprintf oc "%s:%d" key value); fprintf oc "\n") value)) maplist;(*fprintf oc "module %s:\n" key; *)
    close_out oc*)


