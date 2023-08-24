open Extraction
open Extraction.NBitsDef
open Printf
open Firrtl_lang
open Firrtl
open Big_int_Z
open Graph

let lowf = "./demo/treadle_lofir/sub/ContextNestingTop"
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
       | Ast.Fclock -> (inp_map, inp_lst, ul)

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
let m_generate_map clks (inp_map,inp_lst,ul) m = 
  match m with
    | Ast.FInmod (_, pl, _) -> List.fold_left (p_generate_map clks) (inp_map,inp_lst,ul) pl
    | Ast.FExmod (_, pl, _) -> List.fold_left (p_generate_map clks) (inp_map,inp_lst,ul) pl
              
(*val generate_map : StringMap -> StringMap*)
let generate_map clks (inp_map,inp_lst,ul) =
  match lowf_ast with
    | (_, fmod) -> List.fold_left (m_generate_map clks) (inp_map,inp_lst,ul) fmod

(*extract input intmap*)
let p_extract_i ml imap (m,l,ll) p = 
  match p with
    | Ast.Finput (v, ty) -> (match ty with
      | Ast.Fuint _ -> (IntMap.add (StringMap.find v ml) (StringMap.find v imap) m, List.cons (StringMap.find v ml) l,List.cons (StringMap.find v ml) ll)
      | Ast.Fsint _ -> (IntMap.add (StringMap.find v ml) (StringMap.find v imap) m, List.cons (StringMap.find v ml) l,ll)
      | Ast.Fclock -> m,l,ll)
      
    | Ast.Foutput (v, ty) -> (match ty with
      | Ast.Fuint _ -> (IntMap.add (StringMap.find v ml) [] m, l,List.cons (StringMap.find v ml) ll)
      | Ast.Fsint _ -> (IntMap.add (StringMap.find v ml) [] m, l,ll)
      | Ast.Fclock -> m,l,ll)

let m_extract_i ml imap (mm,l,ll) m = 
  match m with
    | Ast.FInmod (v, pl, _) -> List.fold_left (p_extract_i (StringMap.find v ml) imap) (mm,l,ll) pl
    | Ast.FExmod (v, pl, _) -> List.fold_left (p_extract_i (StringMap.find v ml) imap) (mm,l,ll) pl
              
let extract_i ml imap =
  match lowf_ast with
    | (_, fmod) -> List.fold_left (m_extract_i ml imap) (intmap,lst,lst) fmod

(*extract output*)
let p_extract_o ml (m,l,ll) p = 
  match p with
    | Ast.Foutput (v, _) -> (IntMap.add (StringMap.find v ml) [] m, List.cons v l, List.cons (StringMap.find v ml) ll)
    | Ast.Finput (_, _) -> m,l,ll

let m_extract_o ml (mm,l,ll) m = 
  match m with
    | Ast.FInmod (v, pl, _) -> List.fold_left (p_extract_o (StringMap.find v ml)) (mm,l,ll) pl
    | Ast.FExmod (v, pl, _) -> List.fold_left (p_extract_o (StringMap.find v ml)) (mm,l,ll) pl
              
let extract_o ml =
  match lowf_ast with
    | (_, fmod) -> List.fold_left (m_extract_o ml) (intmap,lst,lst) fmod

let rec print_list oc l = 
  match l with
    | [] -> ()
    | h::t -> fprintf oc "%d " h; print_list oc t

let rec printf_list l = 
  match l with
    | [] -> printf "\n"
    | h::t -> printf "%d " h; printf_list t

let rec printf0_list l = 
  match l with
    | [] -> ()
    | h::t -> printf "%s " h; printf0_list t

let rec printf00_list l = 
  match l with
    | [] -> printf "\n"
    | h::t -> printf "%b " h; printf00_list t

(*Ast*)
(*val m_extract_stmt : stmt lst -> fmod -> stmt lst*)
let m_extract_stmt lst m = 
  match m with
    | Ast.FInmod (_, _, sl) -> List.append lst sl
    | Ast.FExmod (_, _, sl) -> List.append lst sl

(* stmt lst -> stmt lst *)
let extract_stmt lst = 
  match lowf_ast with
    | (_, fmod) -> List.fold_left m_extract_stmt lst fmod

(*Firrtl*)
(*val m_extract_stmt : stmt lst -> fmod -> stmt lst*)
let fm_extract_stmt (l,ll) m = 
  match m with
    | Firrtl.FInmod (_, pl, sl) -> List.append l sl, List.append ll pl
    | Firrtl.FExmod (_, pl, sl) -> List.append l sl, List.append ll pl

(* stmt lst -> stmt lst *)
let fextract_stmt fc l ll = 
  match fc  with
    | Firrtl.Fcircuit(_, fmod) -> List.fold_left fm_extract_stmt (l,ll) fmod

(* stmt 顺序 *)
(* directed graphs with lefthand(int) as vertex and fstmt as edge *)
module Int = struct
  type t = int
  let compare = compare
  let hash = Hashtbl.hash
  let equal = (=)
  let default = -1
end
module G = Persistent.Digraph.Concrete(Int)

module C = Graph.Components.Make(G)
module GPDFS = Traverse.Dfs (G)

(* expr -> var list *)
let rec expr2varlist expr ls = 
  match expr with
  | Firrtl.Econst (_,_) -> ls
  | Firrtl.Eref v -> List.cons v ls
  | Firrtl.Eprim_unop (_, e1) -> expr2varlist e1 ls
  | Firrtl.Eprim_binop (_, e1, e2) -> expr2varlist e2 (expr2varlist e1 ls)
  | Firrtl.Emux (e1,e2,e3) -> expr2varlist e3 (expr2varlist e2 (expr2varlist e1 ls))
  | Firrtl.Evalidif (e1,e2) -> expr2varlist e2 (expr2varlist e1 ls)
  | Firrtl.Ecast (_, e) -> expr2varlist e ls

let cons_end a ls = List.rev (List.cons a (List.rev ls))

let rec genG st (g,kl,rl,rs,m) = 
  match st with
  | Firrtl.Sskip -> (g, cons_end st kl,rl,rs,m)
  | Firrtl.Swire (_, _) -> (g, cons_end st kl,rl,rs,m)
  | Firrtl.Smem _ -> (g, cons_end st kl,rl,rs,m)(*TBD*)
  | Firrtl.Sinst (v1,v2) -> (G.add_edge g (Obj.magic v2) (Obj.magic v1), kl,rl,rs,IntMap.add (Obj.magic v1) st m)
  | Firrtl.Sfcnct (e1, e2) -> (match e1 with
                      | Eref v1 -> (match e2 with 
                                  | Econst (_,_) -> (g, cons_end st kl,rl, rs,m)
                                  | _ ->
                      (if (List.mem v1 rl) then (g,kl,rl,List.cons st rs,m) else
                        (let func v v2 ggg = G.add_edge ggg v2 v in
                        let gg = List.fold_right (func (Obj.magic v1)) (List.map Obj.magic (expr2varlist e2 [])) g (*G.add_vertex g v1 自动包含*) in
                        (gg, kl,rl,rs, IntMap.add (Obj.magic v1) st m))))
                      | _ -> (g, kl,rl, rs,m))
  | Firrtl.Sinvalid _ -> (g, cons_end st kl,rl,rs, m)
  | Firrtl.Swhen (_, s1, s2) -> genG s2 (genG s1 (g,kl,rl,rs,m))
  | Firrtl.Sreg v -> (g, cons_end st kl,List.cons v.rid rl, rs,m)
  | Firrtl.Sstop (_,_,_) -> (g,kl,rl,rs,m)(*TBD*)
  | Firrtl.Snode (v, e) -> let func v1 v2 ggg = G.add_edge ggg v2 v1 in
                        let gg = List.fold_right (func (Obj.magic v)) (List.map Obj.magic (expr2varlist e [])) g (*G.add_vertex g v1 自动包含*) in
                        (gg, kl, rl,rs, IntMap.add (Obj.magic v) st m)

(* m1: var -> var list; m2: var -> stmt; m3: var -> n; kl: known variable list *)
let rec generateG st (g,kls,rls,rsl,m) =
  match st with
    | [] -> (g,kls,rls,rsl,m)
    | h :: tl ->
      let (gg,kl,rl,rs,mm) = genG h (g,kls,rls,rsl,m) in
      generateG tl (gg,kl,rl,rs,mm)
  

(** val upd_argulist :
    Store.t -> (int list IntMap/int -> Natlist0.natlist) -> int list -> int -> Store.t **)

let rec upd_argulist s io_in0 name ind =
  match name with
  | [] -> s
  | h :: t0 ->
    upd_argulist
      (Env.Store.upd (Obj.magic h) 
        ((List.nth (IntMap.find h io_in0) ind)) s)(*from_nat (succ 0)*)
      io_in0 t0 ind

(** val clk_steps :
    LoFirrtl.fstmt list -> Store.t -> TE.env -> (int list IntMap/int -> Natlist0.natlist) ->
    int list -> int -> Store.t * nat list **)

let myupdateo s2 omap l = 
  let newv = (Env.Store.acc (Obj.magic l) s2) in
  let f a = (match a with
  | Some a -> Some(List.rev (List.cons newv (List.rev a)))
  | None -> None) in
  IntMap.update l f omap

let rec clk_steps_tail_rec_aux st rs s te io_in0 name ols clk_num len =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ ->
    (*let s1 = upd_argulist s io_in0 name (len-1) in
    (*let te1 = LoFirrtl.upd_typenv_fstmts st te s1 in*)(*更新te*)
    let (_, s2) = LoFirrtl.eval_fstmts st rs s1 te in*)
    (*let temp = (match (Env.TE.vtyp (Obj.magic 5) te) with
    | Env.Fuint ss -> ss
    | Env.Fsint ss -> ss
    | Env.Fclock -> 0
    | Env.Freset -> 0
    | Env.Fasyncreset -> 0) in*)
     (s,io_in0))(*printf "%d\n" (Seq.size (Env.Store.acc (Obj.magic 7) s2) )*)
    (fun m ->
    let n = Ssrnat.subn len (m+1) in
    let s1 = upd_argulist s io_in0 name n in
    (*let te1 = LoFirrtl.upd_typenv_fstmts st te s1 in*)(*更新te*)
    let (rs2, s2) = LoFirrtl.eval_fstmts st rs s1 te in
    let ommap = List.fold_left (myupdateo s2) io_in0 ols in
    clk_steps_tail_rec_aux st rs2 s2 te ommap name ols m len)
    clk_num

let clk_steps_tail_rec st rs s te ios nms ols nclk =
  clk_steps_tail_rec_aux st rs s te ios nms ols nclk nclk

(*
let writeinp = IntMap.add 1 [[true];[false]] intmap
let writeinp = IntMap.add 2 [[false;false;false;true;false;true];[true;false;true;false;true;false]] writeinp
let writeinp = IntMap.add 3 [[true;false;true;false;false;false;false;false];[true;false;true;false;true;false;false;false]] writeinp
let writeinp = IntMap.add 4 [] writeinp
let writeinp = IntMap.add 5 [] writeinp
let writeinp = IntMap.add 6 [] writeinp
let writeinp = IntMap.add 7 [] writeinp
let writeinp = IntMap.add 8 [] writeinp*)

let writeinp = IntMap.add 1 [[true];[false]] intmap
let writeinp = IntMap.add 2 [[true;true];[true;false]] writeinp
let writeinp = IntMap.add 3 [[true;true;false;true];[true;true;false;true]] writeinp
let writeinp = IntMap.add 4 [[true;true];[true;false]] writeinp
let writeinp = IntMap.add 5 [] writeinp
let writeinp = IntMap.add 6 [] writeinp

(*
let () = 
printf "%d\n" (Z.to_int (Z.of_string_base 16 "deadf00d"));
printf "%d\n" (Z.to_int (nat_of_bits [b1;b1;b0;b1;b1;b1;b1;b0;b1;b0;b1;b0;b1;b1;b0;b1;b1;b1;b0;b1;b1;b1;b1;b0;b1;b0;b1;b0;b1;b1;b0;b1]))
*)
let p_stmt s = 
  match s with
  | Firrtl.Sfcnct (e1, _) -> (match e1 with
                            | Eref v1 -> printf "%d\n" (Obj.magic v1)
                            | _ -> printf "\n")
  | Firrtl.Snode (v, _) -> printf "%d\n" (Obj.magic v)
  | Firrtl.Swire (v, _) -> printf "%d\n" (Obj.magic v)
  | Firrtl.Sinvalid v -> printf "%d\n" (Obj.magic v)  
  | Firrtl.Sreg r -> printf "%d\n" (Obj.magic r.rid)
  | _ -> printf "\n"

let () =
  let clks = 100 in
  (*printf "%s\n" ((string_of_big_int (power_int_positive_int 2 (160))));*)
  let s0 = Env.Store.empty in
  let te0 = Env.TE.empty in
  let (inp_bitsmap, inp_lst, ulst) = generate_map clks (map, lst, lst) in
  let my2Z k = 
    (if (List.mem k ulst) then (List.map nat_of_bits)
    else (List.map z_of_bits)) in
  let inp_map = StringMap.map (List.map Z.to_int) (StringMap.mapi my2Z inp_bitsmap) in
  
  let (cm, mm, maplist, _) = Transast.str2N lowf_ast map map map 0 in
  let (inp_intmap,inp_intlst,uintlst) = extract_i maplist inp_bitsmap in(*uintlst*)
  let (_,olst,ointlst) = extract_o maplist in(*ointlst*)
  let fcir = Transast.trans_cir lowf_ast cm mm maplist in 
  let (rsl, pl) = fextract_stmt fcir [] [] in 
  let te00 = LoFirrtl.upd_typenv_fports pl te0 in
  let sl = List.rev rsl in 
  let (gg,kls,_,rsl,ukm) = generateG sl (G.empty,[],[],[],intmap) in
    (*printf "%d\n" (List.length kls);
    IntMap.iter (fun key _ -> (printf "%d:" key;); printf "\n") ukm;*)
  let (_,order) = C.scc gg in(*(key -> 'a -> 'b -> 'b)*)
  (*printf "vertex %d\n" (G.nb_vertex gg);
  IntMap.iter (fun k _ -> (printf "%d:" k; printf "%d\n" (order k)) ) ukm;*)

  let (_,stmtorder) = List.split (IntMap.bindings (IntMap.fold (fun k v mm -> IntMap.add (order k) v mm) ukm intmap)) in
  (*printf "%d\n" (List.length stmtorder);*)
  let fsl = List.append (List.append kls (List.rev stmtorder)) rsl in 
  if (GPDFS.has_cycle gg)
    then printf  "HasCycle\n";
  let ut1 = (Unix.times()).tms_utime in
  (*let inp_intmap = IntMap.add 3 (List.map (bits_of_z 1) (List.map Z.of_int [1;1;1;1;1;1;1;1;1;1])) inp_intmap in
  let inp_intmap = IntMap.add 1 (List.map (bits_of_z 1) (List.map Z.of_int [0;0;0;0;0;0;0;0;0;0])) inp_intmap in
  let inp_intmap = IntMap.add 8 [] inp_intmap in
  let inp_intmap = IntMap.add 9 [] inp_intmap in
  let inp_intmap = IntMap.add 15 [] inp_intmap in
  let inp_intmap = IntMap.add 26 [] inp_intmap in
  let inp_intmap = IntMap.add 27 [] inp_intmap in
  let inp_intmap = IntMap.add 28 [] inp_intmap in
  let inp_intmap = IntMap.add 29 [] inp_intmap in*)
  (*let inp_intmap = IntMap.add 3 (List.map (bits_of_z 4) (List.map Z.of_int [6;6])) inp_intmap in
  let sl = [(Firrtl.Sfcnct ((Firrtl.Eref (Obj.magic 5)), (Firrtl.Econst ((Fuint 32),[b1;b1;b0;b1;b1;b1;b1;b0;b1;b0;b1;b0;b1;b1;b0;b1;b1;b1;b0;b1;b1;b1;b1;b0;b1;b0;b1;b0;b1;b1;b0;b1]))))] in*)
  let (_,out_bitsmap) = clk_steps_tail_rec fsl s0 s0 te00 inp_intmap inp_intlst ointlst clks in(*out_bitsmap inp_intmap ointlst*)
  printf "%f\n" (Float.sub (Unix.times()).tms_utime ut1);
  (*printf "%d\n" (Seq.size(Env.Store.acc (Obj.magic 15) s2));
  printf "%d\n" (Seq.size(Env.Store.acc (Obj.magic 18) s2));
  
  printf "%d\n" (Z.to_int (nat_of_bits(Env.Store.acc (Obj.magic 1) s2)));
  printf "%d\n" (Z.to_int (z_of_bits [false;true;true;true;false;true;true;true;true;true;false]));
  printf00_list (bits_of_z 64 (Z.pow (Z.of_int 2) (63)));(*ok*)
  printf_list (List.map Z.to_int (gen 1 (Z.of_int 64) []));(*ok*)
  List.iter printf00_list (List.map (bits_of_z 64) (gen_neg 200 (Z.of_int 64) []));(*ok*)
  printf_list (List.map Z.to_int (List.map z_of_bits (List.map (bits_of_z 64) (gen_neg 200 (Z.of_int 64) []))));*)
  
  
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
    close_out oc



(*
generate key为string的input map
let () = 
  let (inp_map, inp_lst) = generate_map 10 (map, lst) in 
  let (inp_intmap, inp_intlst) = strmap2intmap (inp_map,inp_lst) (intmap,lst) (List.length inp_lst) in
  (*
  StringMap.iter (fun key value -> (printf "%s:" key; List.iter (printf " %d") value); printf "\n") inp_map;
  IntMap.iter (fun key value -> (printf "%d:" key; List.iter (printf " %d") value); printf "\n") inp_intmap;
  printf_list inp_intlst*)
 
*)

(*
input从stringmap转为对应标好的intmap
let () =
  let clks = 100 in
  let (inp_map, inp_lst) = generate_map clks (map, lst) in
  let (cm, mm, maplist, _) = Transast.str2N lowf_ast map map map initflag in
  let (inp_intmap,inp_intlst) = extract_i maplist inp_map in
    StringMap.iter (fun key value -> (printf "%s:" key; List.iter (printf " %d") (value)); printf "\n") inp_map;
    List.iter (printf "%s\n") inp_lst;
    printf ("\n");
    StringMap.iter (fun key value -> (printf "%s: %d" key value); printf "\n") cm;
    StringMap.iter (fun key value -> (printf "%s: %d" key value); printf "\n") mm;
    StringMap.iter (fun key value -> (printf "module %s:\n" key; StringMap.iter (fun key value -> (printf "%s: %d" key value); printf "\n") value)) maplist;
    IntMap.iter (fun key value -> (printf "%d:" key; List.iter (printf " %d") (value)); printf "\n") inp_intmap;
    List.iter (printf " %d") inp_intlst
*)

(*

let trys:Firrtl.fstmt = Firrtl.Sfcnct ((Firrtl.Eref (Obj.magic 3)),(Firrtl.Eref (Obj.magic 2)))
let trysl:Firrtl.fstmt list = List.cons trys []*)

(*let () = 
  let inp_map = generate_map map in 
    let oc = open_out file in
      fprintf oc "in:\n";
      StringMap.iter (fun key value -> (fprintf oc "%s:" key; List.iter (fprintf oc " %d") value); fprintf oc "\n") inp_map;
  (*let out_map = 
    fprintf oc "out:\n";
    StringMap.iter (fun key value -> (fprintf oc "%s: %d" key value); fprintf oc "\n") out_map*)
    close_out oc
*)

(*
   let () =
    let oc = open_out file in    (* 新建或修改文件,返回通道 *)
        (*fprintf oc "%s\n" arg_l[0];*)
        List.iter (fprintf oc " %s") arg_l;   (* 写一些东西 *)
        close_out oc;                (* 写入并关闭通道 *)
*)

(*
let printMap m =
  StringMap.iter (fun key value -> printf "%s -> %d\n" key value) m

let () = printMap map*)
