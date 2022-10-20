open Extraction
open Firrtl_lang
(*open Printf
open Extraction.NBitsDef*)

let initflag = 0
module StringMap = Map.Make(String)
let initmap = StringMap.empty

let p_str2N (map,flag) p = 
  match p with
  | Ast.Finput (v, _) -> (StringMap.add v flag map,flag + 1)
  | Ast.Foutput (v, _) -> (StringMap.add v flag map,flag + 1)

let mem_str2N (m:Ast.fmem) map flag = 
  let v_str2N (a, b) v = (StringMap.add v b a,b + 1) 
in
  List.fold_left v_str2N (List.fold_left v_str2N (map,flag) (m.reader)) (m.writer)

let rec s_str2N (map,flag) stmt = 
  match stmt with
  | Ast.Swire (v, _) -> (StringMap.add v flag map,flag + 1)
  | Ast.Sinst (v1,_) -> (StringMap.add v1 flag map,flag + 1)
  | Ast.Swhen (_, s1, s2) -> s_str2N (s_str2N (map,flag) s1) s2
  | Ast.Sreg r -> (StringMap.add r.rid flag map,flag + 1)
  | Ast.Smem m -> let (map0,flag0) = mem_str2N m map flag in 
    (StringMap.add m.mid flag0 map0,flag0 + 1)
  | Ast.Snode (v, _) -> (StringMap.add v flag map,flag + 1)
  | _ -> (map,flag)

let m_str2N (mm, maplist, flag) m = 
  match m with
  | Ast.FInmod (v, pl, sl) -> let (map0, flag0) = List.fold_left s_str2N (List.fold_left p_str2N (initmap,flag) pl) sl in
    (StringMap.add v flag0 mm, StringMap.add v map0 maplist,flag0 + 1)
  | Ast.FExmod (v, pl, sl) -> let (map0, flag0) = List.fold_left s_str2N (List.fold_left p_str2N (initmap,flag) pl) sl in
    (StringMap.add v flag0 mm, StringMap.add v map0 maplist,flag0 + 1)

let str2N a_cir cm mm maplist flag = 
  match a_cir with
  | (v, fmod) -> let (map0, mlist, flag0) = List.fold_left m_str2N (mm, maplist, flag) fmod in
  (StringMap.add v flag0 cm, map0, mlist, flag0 + 1)

(*transast*)

let trans_ucast a_ucast = 
  match a_ucast with
  | Ast.AsUInt -> Firrtl.AsUInt
  | Ast.AsSInt -> Firrtl.AsSInt
  | Ast.AsClock -> Firrtl.AsClock

let trans_eunop a_eunop = 
  match a_eunop with
  | Ast.Upad s -> Firrtl.Upad (Z.to_int s)
  | Ast.Ushl s -> Firrtl.Ushl (Z.to_int s)
  | Ast.Ushr s -> Firrtl.Ushr (Z.to_int s)
  | Ast.Ucvt -> Firrtl.Ucvt
  | Ast.Uneg -> Firrtl.Uneg
  | Ast.Unot -> Firrtl.Unot
  | Ast.Uandr -> Firrtl.Uandr
  | Ast.Uorr -> Firrtl.Uorr
  | Ast.Uxorr -> Firrtl.Uxorr
  | Ast.Uextr (s1, s2) -> Firrtl.Uextr ((Z.to_int s1), (Z.to_int s2))
  | Ast.Uhead s -> Firrtl.Uhead (Z.to_int s)
  | Ast.Utail s -> Firrtl.Utail (Z.to_int s)
  | Ast.Ubits (s1, s2) -> Firrtl.Uextr (Z.to_int s1, Z.to_int s2)
  (*| Ast.Uincp
  | Ast.Udecp
  | Ast.Usetp*)

let trans_cmp a_cmp = 
  match a_cmp with
  | Ast.Blt -> Firrtl.Blt
  | Ast.Bleq -> Firrtl.Bleq
  | Ast.Bgt -> Firrtl.Bgt
  | Ast.Bgeq -> Firrtl.Bgeq
  | Ast.Beq -> Firrtl.Beq
  | Ast.Bneq -> Firrtl.Bneq

let trans_ebinop a_ebinop = 
  match a_ebinop with
  | Ast.Badd -> Firrtl.Badd
  | Ast.Bsub -> Firrtl.Bsub
  | Ast.Bmul -> Firrtl.Bmul
  | Ast.Bdiv -> Firrtl.Bdiv
  | Ast.Brem -> Firrtl.Brem
  | Ast.Bcomp s -> Firrtl.Bcomp (trans_cmp s)
  | Ast.Bdshl -> Firrtl.Bdshl
  | Ast.Bdshr -> Firrtl.Bdshr
  | Ast.Band -> Firrtl.Band
  | Ast.Bor -> Firrtl.Bor
  | Ast.Bxor -> Firrtl.Bxor
  | Ast.Bcat -> Firrtl.Bcat
  | Ast.Bsdiv -> Firrtl.Bdiv
  | Ast.Bsrem ->Firrtl.Brem

let trans_fgtyp ty = 
  match ty with
  | Ast.Fuint s -> Env.Fuint (Z.to_int s)
  | Ast.Fsint s -> Env.Fsint (Z.to_int s)
  | Ast.Fclock -> Env.Fclock

  let bits_of_z (size : int) (z : Z.t) =
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
let rec trans_expr e map = 
  match e with
  | Ast.Econst (ty, s) -> Firrtl.Econst(trans_fgtyp ty, bits_of_z (Z.to_int (Ast.sizeof_fgtyp ty)) s)
  | Ast.Eref v -> Firrtl.Eref(Obj.magic (StringMap.find v map))
  (*| Edeclare (v, ty) -> output_string out "(edeclare "; output_string out (v^" "); output_string out " ";  fpp_type out ty; output_string out ")\n"
  | Esubacc (v, s) -> output_string out "(Esubacc "; output_string out (v^" "); output_string out " "; output_string out (Z.to_string s); output_string out ")\n" *)
  | Ast.Eprim_unop (op, e1) -> Firrtl.Eprim_unop(trans_eunop op, trans_expr e1 map)
  | Ast.Eprim_binop (bop, e1, e2) -> Firrtl.Eprim_binop(trans_ebinop bop, trans_expr e1 map, trans_expr e2 map)
  | Ast.Emux (e1,e2,e3) -> Firrtl.Emux(trans_expr e1 map, trans_expr e2 map, trans_expr e3 map)
  | Ast.Evalidif (e1,e2) -> Firrtl.Evalidif(trans_expr e1 map,trans_expr e2 map)
  | Ast.Ecast (s, e) -> Firrtl.Ecast(trans_ucast s, trans_expr e map)
  (*| Ast.Efield (e1,e2) -> Firrtl.E?(trans_expr e1 map,trans_expr e2 map)*)
  
let trans_ruw r = 
  match r with
  | Ast.Mold -> Firrtl.Coq_old
  | Ast.Mnew -> Firrtl.Coq_new
  | Ast.Mundefined -> Firrtl.Coq_undefined

let myfind givenmap s = StringMap.find s givenmap

let trans_rst rst map = 
  match rst with
     | Ast.NRst -> Firrtl.NRst
     | Ast.Rst (e1, e2) -> Firrtl.Rst(trans_expr e1 map, trans_expr e2 map)

let rec trans_stmt smap s = 
  match s with
  | Ast.Sskip -> Firrtl.Sskip
  | Ast.Swire (v, ty) -> Firrtl.Swire(Obj.magic (StringMap.find v smap), trans_fgtyp ty)
  | Ast.Smem m -> Firrtl.Smem (Firrtl.LoFirrtl.mk_fmem (Obj.magic (StringMap.find m.mid smap)) (trans_fgtyp m.data_type) (Z.to_int m.depth) (Obj.magic (List.map (myfind smap) m.reader)) (Obj.magic (List.map (myfind smap) m.writer)) (Z.to_int m.read_latency) (Z.to_int m.write_latency) (trans_ruw m.read_write))
  | Ast.Sinst (v1,v2) -> Firrtl.Sinst(Obj.magic (StringMap.find v1 smap), Obj.magic (StringMap.find v2 smap))
  | Ast.Sfcnct (e1, e2) -> Firrtl.Sfcnct(trans_expr e1 smap, trans_expr e2 smap)
  (*| Ast.Spcnct (e1, e2) -> Firrtl.Spcnct(trans_expr e1 smap, trans_expr e2 smap)*)
  | Ast.Sinvalid v -> Firrtl.Sinvalid (Obj.magic (StringMap.find v smap))
  | Ast.Swhen (e, s1, s2) -> Firrtl.Swhen((trans_expr e smap), (trans_stmt smap s1), (trans_stmt smap s2))
  | Ast.Sreg r -> Firrtl.Sreg (Firrtl.LoFirrtl.mk_freg (Obj.magic (StringMap.find r.rid smap)) (trans_fgtyp r.rtype) (trans_expr r.clock smap) (trans_rst r.reset smap))
  | Ast.Sstop (e1,e2,s) -> Firrtl.Sstop(trans_expr e1 smap, trans_expr e2 smap, Z.to_int s)
  | Ast.Snode (v, e) -> Firrtl.Snode(Obj.magic (StringMap.find v smap), trans_expr e smap)
  | _ -> Firrtl.Sskip

let trans_stmtl smap fsl s = 
  match s with
  | Ast.Sskip -> List.cons Firrtl.Sskip fsl
  | Ast.Swire (v, ty) -> List.cons (Firrtl.Swire(Obj.magic (StringMap.find v smap), trans_fgtyp ty)) fsl
  | Ast.Smem m -> List.cons (Firrtl.Smem (Firrtl.LoFirrtl.mk_fmem (Obj.magic (StringMap.find m.mid smap)) (trans_fgtyp m.data_type) (Z.to_int m.depth) (Obj.magic (List.map (myfind smap) m.reader)) (Obj.magic (List.map (myfind smap) m.writer)) (Z.to_int m.read_latency) (Z.to_int m.write_latency) (trans_ruw m.read_write))) fsl
  | Ast.Sinst (v1,v2) -> List.cons (Firrtl.Sinst(Obj.magic (StringMap.find v1 smap), Obj.magic (StringMap.find v2 smap))) fsl
  | Ast.Sfcnct (e1, e2) -> List.cons (Firrtl.Sfcnct(trans_expr e1 smap, trans_expr e2 smap)) fsl
  (*| Ast.Spcnct (e1, e2) -> List.cons (Firrtl.Spcnct(trans_expr e1 smap, trans_expr e2 smap)) fsl*)
  | Ast.Sinvalid v -> List.cons (Firrtl.Sinvalid (Obj.magic (StringMap.find v smap))) fsl
  | Ast.Swhen (e, s1, s2) -> List.cons (Firrtl.Swhen((trans_expr e smap), (trans_stmt smap s1), (trans_stmt smap s2))) fsl
  | Ast.Sreg r -> List.cons (Firrtl.Sreg (Firrtl.LoFirrtl.mk_freg (Obj.magic (StringMap.find r.rid smap)) (trans_fgtyp r.rtype) (trans_expr r.clock smap) (trans_rst r.reset smap))) fsl
  | Ast.Sstop (e1,e2,s) -> List.cons (Firrtl.Sstop(trans_expr e1 smap, trans_expr e2 smap, Z.to_int s)) fsl
  | Ast.Snode (v, e) -> List.cons (Firrtl.Snode(Obj.magic (StringMap.find v smap), trans_expr e smap)) fsl
  | _ -> fsl

let trans_port pmap fpl p = 
  match p with
  | Ast.Finput (v, ty) -> List.cons (Firrtl.Finput(Obj.magic (StringMap.find v pmap), trans_fgtyp ty)) fpl
  | Ast.Foutput (v, ty) -> List.cons (Firrtl.Foutput(Obj.magic (StringMap.find v pmap), trans_fgtyp ty)) fpl

let trans_mod mm maplist fml a_mod = 
  match a_mod with
  | Ast.FInmod (v, pl, sl) -> List.cons (Firrtl.FInmod(Obj.magic (StringMap.find v mm), List.fold_left (trans_port (StringMap.find v maplist)) [] pl, List.fold_left (trans_stmtl (StringMap.find v maplist)) [] sl)) fml
  | Ast.FExmod (v, pl, sl) -> List.cons (Firrtl.FExmod(Obj.magic (StringMap.find v mm), List.fold_left (trans_port (StringMap.find v maplist)) [] pl, List.fold_left (trans_stmtl (StringMap.find v maplist)) [] sl)) fml

let trans_cir a_cir cm mm maplist= 
  match a_cir with
  | (v, fmod) -> Firrtl.Fcircuit(Obj.magic (StringMap.find v cm), List.fold_left (trans_mod mm maplist) [] fmod)

(*
let lowf_ast = parse "./demo/mem.lo.fir"

let () = 
  let (cm, mm, maplist, _) = str2N lowf_ast initmap initmap initmap initflag in
  (*fcir = *)trans_cir lowf_ast cm mm maplist
  
    StringMap.iter (fun key value -> (printf "%s: %d" key value); printf "\n") cm;
    StringMap.iter (fun key value -> (printf "%s: %d" key value); printf "\n") mm;
    StringMap.iter (fun _ value -> StringMap.iter (fun key value -> (printf "%s: %d" key value); printf "\n") value) maplist

    
let lowf = "./demo/Accumulator.lo.fir"

let parse f =
  let lexbuf = Lexing.from_channel (open_in f) in
  FirrtlParser.file FirrtlLexer.token lexbuf

let lowf_ast = parse lowf
let () = 
  let s0 = Env.Store.empty in
  let t0 = Env.TE.empty in
  let (cm, mm, maplist, _) = str2N lowf_ast Tryfile.map Tryfile.map Tryfile.map initflag in
  let fc = trans_cir lowf_ast cm mm maplist in 
  let sl = Tryfile.fextract_stmt fc [] in
    printf "%d" (to_nat(Env.Store.acc (Obj.magic 4) (Firrtl.clk_steps (List.rev sl) s0 t0 Firrtl.exampleinp [1;2] 4)))
    *)