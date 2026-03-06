open Firrtl_lang
open Printf
open Extraction
(*open Extraction.NBitsDef*)

module StringMap = Map.Make(String)
let initmap = StringMap.empty
module IntMap = Map.Make(Int)
let initmap0 = IntMap.empty

let rec printf_list l = 
  match l with
    | [] -> printf "\n"
    | h::t -> printf "%d " h; printf_list t

let rec ls_max l = 
  if (List.length l) == 0
    then 0
  else (if (List.length l) == 1
        then (List.hd l)
      else (if (List.hd l) > (ls_max (List.tl l))
              then (List.hd l)
            else (ls_max (List.tl l))
      )
  )
(* old
let p_str2N (map,flag) p = 
  match p with
  | Ast.Finput (v, _) -> (StringMap.add v flag map,flag + 1)
  | Ast.Foutput (v, _) -> (StringMap.add v flag map,flag + 1)

let mem_str2N (m:Ast.fmem) map flag = 
  let v_str2N (a, b) v = (StringMap.add v b a,b + 1) 
in
  List.fold_left v_str2N (List.fold_left v_str2N (map,flag) (m.reader)) (m.writer)

let s_str2N (map,flag) stmt = 
  match stmt with
  | Ast.Swire (v, _) -> (StringMap.add v flag map,flag + 1)
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
*)

  (* have mod var -> all var in N *)
let p_str2N (map,flag) p = 
  match p with
  | Ast.Finput (v, _) -> (StringMap.add v flag map,flag + 1)
  | Ast.Foutput (v, _) -> (StringMap.add v flag map,flag + 1)

  (* 生成mem所需参数: readerls writerls data2etc memmap *)
let mem_str2N (m:Ast.fmem) map flag rl wl datatoetc = 
  let reader_str2N (a, b, rls, wls, data2etc) v = 
    (
    let (a1,b1) = (StringMap.add (m.mid^"."^v^".data") b a,b + 1) in (* reader.data 为b*)
    let (a2,b2) = (StringMap.add (m.mid^"."^v^".addr") b1 a1,b1 + 1) in 
    let (a3,b3) = (StringMap.add (m.mid^"."^v^".en") b2 a2,b2 + 1) in 
    (StringMap.add (m.mid^"."^v^".clk") b3 a3, b3 + 1, List.cons b rls, wls, IntMap.add b (b1,b2,b3,-1) data2etc)
    ) in
  let writer_str2N (a, b, rls, wls, data2etc) v = 
    (
    let (a1,b1) = (StringMap.add (m.mid^"."^v^".data") b a,b + 1) in 
    let (a2,b2) = (StringMap.add (m.mid^"."^v^".addr") b1 a1,b1 + 1) in 
    let (a3,b3) = (StringMap.add (m.mid^"."^v^".en") b2 a2,b2 + 1) in 
    let (a4,b4) = (StringMap.add (m.mid^"."^v^".mask") b3 a3,b3 + 1) in 
    (StringMap.add (m.mid^"."^v^".clk") b4 a4, b4 + 1, rls, List.cons b wls, IntMap.add b (b1,b2,b3,b4) data2etc)
    ) in
  List.fold_left writer_str2N (List.fold_left reader_str2N (map,flag,rl,wl,datatoetc) (m.reader)) (m.writer)

let s_str2N name2ports (map,flag,rl,wl,datatoetc,memmap) stmt = 
  match stmt with
  | Ast.Swire (v, _) -> (StringMap.add v flag map,flag + 1, rl, wl, datatoetc, memmap)
  | Ast.Sreg r -> let (map0, flag0) = (StringMap.add r.rid flag map,flag + 1) in
                  (StringMap.add r.clock flag0 map0,flag0 + 1, rl, wl, datatoetc, memmap)
  | Ast.Smem m -> let (map0,flag0,rls,wls,data2etc) = mem_str2N m map flag rl wl datatoetc in 
                  (StringMap.add m.mid flag0 map0,flag0 + 1,rls,wls, data2etc,IntMap.add flag0 IntMap.empty memmap)
  | Ast.Snode (v, _) -> (StringMap.add v flag map,flag + 1, rl, wl, datatoetc, memmap)
  | Ast.Sinst (v1, e) -> (match e with
                        | Ast.Eref v2 -> let (map0, flag0) = List.fold_left (fun (a,b) p -> (match p with
                                                        | Ast.Finput (v3, _) -> (StringMap.add (v1^"."^v3) b a, b + 1)
                                                        | Ast.Foutput (v3, _) -> (StringMap.add (v1^"."^v3) b a, b + 1))) (map,flag) (StringMap.find v2 name2ports) in
                                             (StringMap.add v1 flag0 map0, flag0 + 1, rl, wl, datatoetc, memmap)
                        | _ -> (map,flag, rl, wl, datatoetc, memmap))
  | _ -> (map,flag, rl, wl, datatoetc, memmap)

let g_modsmap name2ports (modsmap,ls, rlsm, wlsm, datatoetc, memmap) hd =  
  match hd with 
            | Ast.FInmod (mv, pl, sl) -> let (thismap0, flag0) = List.fold_left p_str2N (initmap,0) pl in
                                         let (thismap,flag, rls, wls, data2etc, memmap0) = List.fold_left (s_str2N name2ports) (thismap0, flag0, [], [], IntMap.empty, IntMap.empty) sl in
                                               (StringMap.add mv thismap modsmap, List.cons flag ls, StringMap.add mv rls rlsm, StringMap.add mv wls wlsm, StringMap.add mv data2etc datatoetc, StringMap.add mv memmap0 memmap)
            | _ -> (modsmap,ls, rlsm, wlsm, datatoetc, memmap)

let generate_modsmap a_cir name2ports = 
  match a_cir with
  | (_, fmod) -> List.fold_left (g_modsmap name2ports) (initmap,[],initmap,initmap,initmap,initmap) fmod

let generate_fmodsmap a_cir = 
  match a_cir with
  | (_, fmod) -> List.fold_left (fun a b -> (match b with
                                            | Ast.FInmod (mv, _,_) -> StringMap.add mv b a
                                            | Ast.FExmod (mv, _,_) -> StringMap.add mv b a)) initmap fmod

(* var -> fport list *)
let plbyname a_cir = 
  match a_cir with
  | (cv, ml) -> let m = List.fold_left (fun m x -> match x with 
                                            | Ast.FInmod (mv, pl, _) -> StringMap.add mv pl m
                                            | Ast.FExmod (mv, pl, _) -> StringMap.add mv pl m) initmap ml in (m, cv)

(* 对每次声明instance找到端口对应*)
(* var -> map(N -> N)*)
let mmapport name2ports modsmap mv (inin2exin,exout2inout) s = 
  match s with
  | Ast.Sinst (v1, e) -> (match e with
                        | Ast.Eref v2 -> let _ = name2ports in
                        let _ = modsmap in
                        let _ = mv in
                        List.fold_left (fun (a,b) p -> (match p with
                                                        | Ast.Finput (v3, _) -> (IntMap.add (StringMap.find v3 (StringMap.find v2 modsmap)) (StringMap.find (v1^"."^v3) (StringMap.find mv modsmap)) a,b)
                                                        | Ast.Foutput (v3, _) -> (a,IntMap.add (StringMap.find (v1^"."^v3) (StringMap.find mv modsmap)) (StringMap.find v3 (StringMap.find v2 modsmap)) b))) (inin2exin,exout2inout) (StringMap.find v2 name2ports)
                        | _ -> (inin2exin,exout2inout))
  | _ -> (inin2exin,exout2inout)

let mapport name2ports modsmap (inin2exin,exout2inout) m = 
  match m with
  | Ast.FInmod (mv, _, sl) -> let (a,b) =  List.fold_left (mmapport name2ports modsmap mv) (initmap0, initmap0) sl in
                              (StringMap.add mv a inin2exin, StringMap.add mv b exout2inout)
  | Ast.FExmod _ -> (inin2exin,exout2inout)

let mapinstport a_cir name2ports modsmap = 
  match a_cir with
  | (_, ml) -> List.fold_left (mapport name2ports modsmap) (initmap, initmap) ml

(* give the N name for modules *)
(* map: string -> N *)
let nummod flag modsmap = 
  StringMap.fold (fun key _ (map,f) -> (StringMap.add key f map, f+1)) modsmap (initmap,flag)
(*
let () = 
  let parse f =
  (let lexbuf = Lexing.from_channel (open_in f) in
  FirrtlParser.file FirrtlLexer.token lexbuf) in
  let lowf_ast = parse "./demo/treadle_lofir/sub/mem/SmallOdds5.lo.fir" in
  (* var -> fport list *)
  let (name2ports, cv) = plbyname lowf_ast in
  let (modsmap,flagls,rlsm,wlsm,datatoetc,memmap) = generate_modsmap lowf_ast name2ports in
  let (modsnum,_) = nummod (ls_max flagls) modsmap in
  let fmodsmap = generate_fmodsmap lowf_ast in 
  let _ = StringMap.find cv modsmap in
  let _ = StringMap.find cv fmodsmap in

  StringMap.iter (fun key value -> (printf "%s: " key); printf "\n"; StringMap.iter (fun key0 value0 -> (printf "%s: %d" key0 value0); printf "\n") value; printf "\n") modsmap;
  StringMap.iter (fun key0 value0 -> (printf "%s: %d" key0 value0); printf "\n") modsnum;

  StringMap.iter (fun key value -> (printf "%s: " key); (if (IntMap.is_empty value) then printf "0" else printf "1"); printf "\n") memmap; printf "\n";
  StringMap.iter (fun key value -> (printf "%s: " key); printf "\n"; IntMap.iter (fun key0 (a,b,c,d) -> (printf "%d: %d; %d; %d; %d" key0 a b c d); printf "\n") value) datatoetc; printf "\n";
  StringMap.iter (fun key value -> (printf "%s: " key); printf "\n"; printf_list value) wlsm; printf "\n";
  StringMap.iter (fun key value -> (printf "%s: " key); printf "\n"; printf_list value) rlsm; printf "\n";

  let (inin2exin,exout2inout) = mapinstport lowf_ast name2ports modsmap in
  StringMap.iter (fun key value -> (printf "%s: " key); printf "\n"; IntMap.iter (fun key0 value0 -> (printf "%d: %d" key0 value0); printf "\n") value; printf "\n") inin2exin;
  StringMap.iter (fun key value -> (printf "%s: " key); printf "\n"; IntMap.iter (fun key0 value0 -> (printf "%d: %d" key0 value0); printf "\n") value; printf "\n") exout2inout
*)

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
  | Ast.Eprim_unop (op, e1) -> Firrtl.Eprim_unop(trans_eunop op, trans_expr e1 map)
  | Ast.Eprim_binop (bop, e1, e2) -> Firrtl.Eprim_binop(trans_ebinop bop, trans_expr e1 map, trans_expr e2 map)
  | Ast.Emux (e1,e2,e3) -> Firrtl.Emux(trans_expr e1 map, trans_expr e2 map, trans_expr e3 map)
  | Ast.Evalidif (e1,e2) -> Firrtl.Evalidif(trans_expr e1 map,trans_expr e2 map)
  | Ast.Ecast (s, e) -> Firrtl.Ecast(trans_ucast s, trans_expr e map)
  
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

let trans_stmt smap modsnum s = 
  match s with
  | Ast.Sskip -> Firrtl.Sskip
  | Ast.Swire (v, ty) -> Firrtl.Swire(Obj.magic (StringMap.find v smap), trans_fgtyp ty)
  | Ast.Sfcnct (e1, e2) -> Firrtl.Sfcnct(trans_expr e1 smap, trans_expr e2 smap)
  | Ast.Sinvalid v -> Firrtl.Sinvalid (Obj.magic (StringMap.find v smap))
  | Ast.Snode (v, e) -> Firrtl.Snode(Obj.magic (StringMap.find v smap), trans_expr e smap)

  | Ast.Sreg r -> Firrtl.Sreg (Firrtl.LoFirrtl.mk_freg (Obj.magic (StringMap.find r.rid smap)) (trans_fgtyp r.rtype) (Obj.magic (StringMap.find r.clock smap)) (trans_rst r.reset smap))
  | Ast.Smem m -> Firrtl.Smem (Firrtl.LoFirrtl.mk_fmem (Obj.magic (StringMap.find m.mid smap)) (trans_fgtyp m.data_type) (Z.to_int m.depth) 
                  (List.fold_left (fun ls x -> List.cons (Firrtl.LoFirrtl.mk_freader_port (Obj.magic (StringMap.find (m.mid^"."^x^".addr") smap)) (Obj.magic (StringMap.find (m.mid^"."^x^".data") smap)) (Obj.magic (StringMap.find (m.mid^"."^x^".en") smap)) (Obj.magic (StringMap.find (m.mid^"."^x^".clk") smap))) ls) [] m.reader)
                  (List.fold_left (fun ls x -> List.cons (Firrtl.LoFirrtl.mk_fwriter_port (Obj.magic (StringMap.find (m.mid^"."^x^".addr") smap)) (Obj.magic (StringMap.find (m.mid^"."^x^".data") smap)) (Obj.magic (StringMap.find (m.mid^"."^x^".en") smap)) (Obj.magic (StringMap.find (m.mid^"."^x^".clk") smap)) (Obj.magic (StringMap.find (m.mid^"."^x^".mask") smap))) ls) [] m.writer)
                  (Z.to_int m.read_latency) (Z.to_int m.write_latency) (trans_ruw m.read_write))
  | Ast.Sinst (v, e) -> (match e with
                        | Ast.Eref v2 -> Firrtl.Sinst (Obj.magic (StringMap.find v smap), Obj.magic (StringMap.find v2 modsnum))
                        | _ -> Firrtl.Sskip)

let trans_port pmap fpl p = 
  match p with
  | Ast.Finput (v, ty) -> List.cons (Firrtl.Finput(Obj.magic (StringMap.find v pmap), trans_fgtyp ty)) fpl
  | Ast.Foutput (v, ty) -> List.cons (Firrtl.Foutput(Obj.magic (StringMap.find v pmap), trans_fgtyp ty)) fpl

let trans_mod modsnum modsmap a_mod = 
  match a_mod with
  | Ast.FInmod (v, pl, sl) -> (v, Firrtl.FInmod(Obj.magic (StringMap.find v modsnum), List.fold_left (trans_port (StringMap.find v modsmap)) [] pl, List.fold_left (fun a b -> List.cons ((trans_stmt (StringMap.find v modsmap) modsnum) b) a) [] sl))
  | Ast.FExmod (v, pl, sl) -> (v, Firrtl.FExmod(Obj.magic (StringMap.find v modsnum), List.fold_left (trans_port (StringMap.find v modsmap)) [] pl, List.fold_left (fun a b -> List.cons ((trans_stmt (StringMap.find v modsmap) modsnum) b) a) [] sl))

  (* 返回 map modnum(N) -> Firrtl.fmod *)
let trans_ml fmod modsnum modsmap = 
  List.fold_left (fun ma mo -> let (v, fm) = trans_mod modsnum modsmap mo in IntMap.add (StringMap.find v modsnum) fm ma) initmap0 fmod

let trans_cir a_cir modsnum modsmap = 
  match a_cir with
  | (v, fmod) -> (v, trans_ml fmod modsnum modsmap)

let parse f =
  let lexbuf = Lexing.from_channel (open_in f) in
  FirrtlParser.file FirrtlLexer.token lexbuf

let lowf_ast = parse "./demo/demo"

let writeinp = IntMap.add 2 [[true];[false]] IntMap.empty
(*let writeinp = IntMap.add 2 [[true;true];[true;false]] writeinp
let writeinp = IntMap.add 3 [[true;true;false;true];[true;true;false;true]] writeinp
let writeinp = IntMap.add 4 [[true;true];[true;false]] writeinp
let writeinp = IntMap.add 5 [] writeinp
let writeinp = IntMap.add 6 [] writeinp*)

let () = 
  let (name2ports, _) = plbyname lowf_ast in
  let (modsmap,flagls,rlsm,wlsm,datatoetc,memmap) = generate_modsmap lowf_ast name2ports in
  let (modsnum,_) = nummod (ls_max flagls) modsmap in

  StringMap.iter (fun key value -> (printf "%s: " key); printf "\n"; StringMap.iter (fun key0 value0 -> (printf "%s: %d" key0 value0); printf "\n") value; printf "\n") modsmap;
  StringMap.iter (fun key0 value0 -> (printf "%s: %d" key0 value0); printf "\n") modsnum;

  StringMap.iter (fun key value -> (printf "%s: " key); (if (IntMap.is_empty value) then printf "no mem" else printf "have mem"); printf "\n") memmap; printf "\n";
  StringMap.iter (fun key value -> (printf "%s: " key); printf "\n"; IntMap.iter (fun key0 (a,b,c,d) -> (printf "%d: %d; %d; %d; %d" key0 a b c d); printf "\n") value) datatoetc; printf "\n";
  StringMap.iter (fun key value -> (printf "%s: \nwriter.data:" key ); printf "\n"; printf_list value) wlsm;
  StringMap.iter (fun key value -> (printf "%s: \nreader.data:" key ); printf "\n"; printf_list value) rlsm;

  
  let (cv, fmodsmap) = trans_cir lowf_ast modsnum modsmap in
  printf "mainmod : %s\n" cv;
  IntMap.iter (fun key _ -> printf "%d:\n" key; printf "\n") fmodsmap;

  let s0 = Env.Store.empty in
  let te0 = Env.TE.empty in
  let mainmod = IntMap.find (StringMap.find cv modsnum) fmodsmap in
  let (_,s,memmap0) = Firrtl.LoFirrtl.run_module mainmod s0 s0 te0 writeinp [2] readerls writerls data2etc memmap 1 1 in
  IntMap.iter (fun key _ -> printf "%d:\n" key; printf "\n") memmap0;
  printf "%d\n" (Z.to_int (nat_of_bits(Env.Store.acc (Obj.magic 3) s2)));


  (*
  let (cm, mm, maplist, _) = str2N lowf_ast initmap initmap initmap initflag in
  (*fcir = *)trans_cir lowf_ast cm mm maplist
  
    StringMap.iter (fun key value -> (printf "%s: %d" key value); printf "\n") cm;
    StringMap.iter (fun key value -> (printf "%s: %d" key value); printf "\n") mm;
    StringMap.iter (fun _ value -> StringMap.iter (fun key value -> (printf "%s: %d" key value); printf "\n") value) maplist

let () = 
  let s0 = Env.Store.empty in
  let t0 = Env.TE.empty in
  let (cm, mm, maplist, _) = str2N lowf_ast Tryfile.map Tryfile.map Tryfile.map initflag in
  let fc = trans_cir lowf_ast cm mm maplist in 
  let sl = Tryfile.fextract_stmt fc [] in
    printf "%d" (to_nat(Env.Store.acc (Obj.magic 4) (Firrtl.clk_steps (List.rev sl) s0 t0 Firrtl.exampleinp [1;2] 4)))
    *)