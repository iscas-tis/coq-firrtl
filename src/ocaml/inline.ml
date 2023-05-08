open Firrtl_lang
open Printf
open Extraction
open Big_int_Z

module StringMap = Map.Make(String)
let initmap = StringMap.empty
module IntMap = Map.Make(Int)
let initmap0 = IntMap.empty

let parse f =
  let lexbuf = Lexing.from_channel (open_in f) in
  FirrtlParser.file FirrtlLexer.token lexbuf

let lowf_ast = parse "./demo/Mytest1.lo.fir" 

let rec addpre_e v0 e = 
  match e with
  | Ast.Econst _ -> e
  | Ast.Eref v -> Ast.Eref (v0^"."^v)
  | Ast.Eprim_unop (op, e1) -> Ast.Eprim_unop (op, addpre_e v0 e1)
  | Ast.Eprim_binop (bop, e1, e2) -> Ast.Eprim_binop (bop, addpre_e v0 e1, addpre_e v0 e2)
  | Ast.Emux (e1,e2,e3)  -> Ast.Emux (addpre_e v0 e1, addpre_e v0 e2, addpre_e v0 e3)
  | Ast.Evalidif (e1,e2)  -> Ast.Evalidif (addpre_e v0 e1, addpre_e v0 e2)
  | Ast.Ecast (s, e) -> Ast.Ecast (s, addpre_e v0 e)

let addpre v0 s =
  match s with
  | Ast.Sskip -> Ast.Sskip
  | Ast.Swire (v, ty) -> Ast.Swire ((v0^"."^v), ty)
  | Ast.Sfcnct (e1, e2) -> Ast.Sfcnct (addpre_e v0 e1, addpre_e v0 e2)
  | Ast.Sinvalid v -> Ast.Sinvalid (v0^"."^v)
  | Ast.Snode (v, e) -> Ast.Snode ((v0^"."^v), addpre_e v0 e)
  | Ast.Sreg r -> (match r.reset with
                | NRst -> Ast.Sreg (Ast.mk_freg_non (v0^"."^r.rid) r.rtype r.clock)
                | Rst (e1, e2) -> Ast.Sreg (Ast.mk_freg (v0^"."^r.rid) r.rtype r.clock (addpre_e v0 e1) (addpre_e v0 e2)))
  | Ast.Smem _ -> Ast.Sskip (* ignore *)
  | Ast.Sinst (v, e) -> Ast.Sinst ((v0^"."^v), e)

let rec flatstmts fmodmap ls instdepth newls = 
  match ls with 
  | [] -> newls
  | h::tl -> match h with
            | Ast.Sinst (v1, e) -> let inststs = match StringMap.find e fmodmap with
                                                | Ast.FInmod (_, pl, sl) -> let instsl = List.map (fun s -> addpre v1 s) sl in
                                                                            let instpl = List.fold_left (fun wl p -> match p with
                                                                                        | Ast.Finput (v, ty) -> List.cons (Ast.Swire ((v1^"."^v), ty)) wl
                                                                                        | Ast.Foutput (v, ty) -> List.cons (Ast.Swire ((v1^"."^v), ty)) wl) [] pl in 
                                                                            List.append instpl instsl
                                                | _ -> [] in
                                   flatstmts fmodmap (List.append tl inststs) instdepth newls
            | _ -> flatstmts fmodmap tl instdepth (List.cons h newls)
            
let generate_fmodmap a_cir = 
  match a_cir with
  | (cv, fmod) -> let modmap = List.fold_left (fun map fm -> match fm with 
                              | Ast.FInmod (mv, _, _) -> StringMap.add mv fm map
                              | _ -> map) initmap fmod in
                  let instdepth = List.fold_left (fun num fm -> match fm with 
                              | Ast.FInmod (_, _, sl) -> List.fold_left (fun num0 s -> match s with
                                                                        | Ast.Sinst _ -> num0 + 1
                                                                        | _ -> num0) num sl
                              | _ -> num) 0 fmod in
    (modmap, cv, instdepth)

let p_str2N (map,flag) p = 
  match p with
  | Ast.Finput (v, _) -> (StringMap.add v flag map,flag + 1)
  | Ast.Foutput (v, _) -> (StringMap.add v flag map,flag + 1)

let s_str2N (map,flag) stmt = 
  match stmt with
  | Ast.Swire (v, _) -> (StringMap.add v flag map,flag + 1)
  | Ast.Sreg r -> let (map0, flag0) = (StringMap.add r.rid flag map,flag + 1) in
                  (StringMap.add r.clock flag0 map0,flag0 + 1)
  | Ast.Snode (v, _) -> (StringMap.add v flag map,flag + 1)
  | _ -> (map,flag)

let generate_modsmap m =  
  match m with 
            | Ast.FInmod (_, pl, sl) -> let (thismap0, flag0) = List.fold_left p_str2N (initmap,0) pl in
                                         List.fold_left s_str2N (thismap0, flag0) sl 
            | _ -> (initmap,0)


let trans_stmt smap s = 
  match s with
  | Ast.Sskip -> Firrtl.Sskip
  | Ast.Swire (v, ty) -> Firrtl.Swire(Obj.magic (StringMap.find v smap), Transast1.trans_fgtyp ty)
  | Ast.Sfcnct (e1, e2) -> Firrtl.Sfcnct(Transast1.trans_expr e1 smap, Transast1.trans_expr e2 smap)
  | Ast.Sinvalid v -> Firrtl.Sinvalid (Obj.magic (StringMap.find v smap))
  | Ast.Snode (v, e) -> Firrtl.Snode(Obj.magic (StringMap.find v smap), Transast1.trans_expr e smap)
  | Ast.Sreg r -> Firrtl.Sreg (Firrtl.LoFirrtl.mk_freg (Obj.magic (StringMap.find r.rid smap)) (Transast1.trans_fgtyp r.rtype) (Obj.magic (StringMap.find r.clock smap)) (Transast1.trans_rst r.reset smap))
  | _ -> Firrtl.Sskip

let trans_main flag mainmap flattenmain =
  match flattenmain with
  | Ast.FInmod (_, pl, sl) -> Firrtl.FInmod (Obj.magic flag, List.fold_left (Transast1.trans_port mainmap) [] pl, List.map (trans_stmt mainmap) sl)
  | Ast.FExmod (_, pl, sl) -> Firrtl.FExmod (Obj.magic flag, List.fold_left (Transast1.trans_port mainmap) [] pl, List.map (trans_stmt mainmap) sl)

let () = 
  let (fmodmap ,cv, instdepth) = generate_fmodmap lowf_ast in
  match StringMap.find cv fmodmap with
  | Ast.FInmod (_, pl, sl) -> let flattensl = flatstmts fmodmap sl instdepth [] in
                              let flattenmain = Ast.FInmod (cv, pl, flattensl) in
                              (*Ast.pp_module stdout flattenmain;*)
                              let (mainmap, flag) = generate_modsmap flattenmain in
                              StringMap.iter (fun key value -> printf "%s :%d\n" key value) mainmap;
                              (*printf "%d\n" flag;*)
                              let fmain = trans_main flag mainmap flattenmain in 
                              let clks = 100 in
                              let (inp_bitsmap, _, ulst) = Helper.generate_map (cv, List.cons flattenmain []) clks (initmap, [], []) in
                              let my2Z k = 
                                (if (List.mem k ulst) then (List.map Helper.nat_of_bits)
                                else (List.map Helper.z_of_bits)) in
                              let (_,inp_intlst,uintlst) = Helper.m_extract_i mainmap inp_bitsmap flattenmain in
                              let inp_map = StringMap.map (List.map Z.to_int) (StringMap.mapi my2Z inp_bitsmap) in
                              StringMap.iter (fun key value -> printf "%s: \n" key; Transast1.printf_list value) inp_map;
                              (*IntMap.iter (fun key _ -> printf "%d:\n" key; printf "\n") inp_intmap;
                              Transast1.printf_list0 inp_lst;
                              Transast1.printf_list inp_intlst;
                              Transast1.printf_list uintlst;*)
                              let ols = List.fold_left (fun ls p -> match p with
                                                          | Ast.Finput _ -> ls
                                                          | Ast.Foutput (pv, _) -> List.cons pv ls) [] pl in
                              let ointls = List.map (fun o -> (StringMap.find o mainmap)) ols in
                              let finp_bitsmap = StringMap.fold (fun key value -> Env.TE.add (Obj.magic (StringMap.find key mainmap)) value) inp_bitsmap Env.TE.empty in
                              let te0 = Transast1.initmod fmain in
                              let ((_,_), outputmap) = Firrtl.LoFirrtl.no_mem_run_module_inline fmain Env.Store.empty Env.Store.empty te0 finp_bitsmap (List.map Obj.magic inp_intlst) (List.map Obj.magic ointls) clks clks in
                              let out_map = List.fold_left (fun b a -> match (Env.TE.find a outputmap) with
                                          | Some tols -> let newol = (if (List.mem a (List.map Obj.magic uintlst)) then (List.map string_of_big_int (List.map Helper.nat_of_bits tols))
                                          else (List.map string_of_big_int (List.map Helper.z_of_bits tols)))
                                             in IntMap.add (Obj.magic a) newol b
                                          | None -> IntMap.add (Obj.magic a) [] b) initmap0 (List.map Obj.magic ointls) in
                              IntMap.iter (fun key value -> (printf "%d:" key; List.iter (printf " %s") (value)); printf "\n") out_map;
  | _ -> printf "not right mainmod.\n";

