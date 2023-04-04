open Firrtl_lang
open Printf
open Extraction
open Extraction.NBitsDef
open Big_int_Z
open Graph

module StringMap = Map.Make(String)
let initmap = StringMap.empty
module IntMap = Map.Make(Int)
let initmap0 = IntMap.empty

let file = "./demo/input.txt"

let rec printf_list l = 
  match l with
    | [] -> printf "\n"
    | h::t -> printf "%d " h; printf_list t

let rec printf_list0 l = 
  match l with
    | [] -> printf "\n"
    | h::t -> printf "%s " h; printf_list0 t

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

let nat_of_bits (bv : bits) : big_int = 
  let rec helper i max lst res =
    if i >= max then res
    else match List.nth bv i with
    | false -> helper (succ i) max lst res
    | true -> helper (succ i) max lst (add_big_int (power_int_positive_int (2) i) res) in
  helper 0 (List.length bv) bv zero_big_int

  (* have mod var -> all var in N *)
let p_str2N (map,flag) p = 
  match p with
  | Ast.Finput (v, _) -> (StringMap.add v flag map,flag + 1)
  | Ast.Foutput (v, _) -> (StringMap.add v flag map,flag + 1)

  (* 生成mem所需参数: readerls writerls data2etc memmap *)
let mem_str2N (m:Ast.fmem) map flag rl wl datatoetc = (*addrvar,envar), midvar), maskvar*)
  let reader_str2N (a, b, rls, wls, data2etc) v = 
    (
    let (a1,b1) = (StringMap.add (m.mid^"."^v^".data") b a,b + 1) in (* reader.data 为b*)
    let (a2,b2) = (StringMap.add (m.mid^"."^v^".addr") b1 a1,b1 + 1) in 
    let (a3,b3) = (StringMap.add (m.mid^"."^v^".en") b2 a2,b2 + 1) in 
    let (a4,b4) = (StringMap.add (m.mid^"."^v^".clk") b3 a3,b3 + 1) in 
    (a4, b4, List.cons b rls, wls, IntMap.add b (b1,b2,flag-1,-1,b3) data2etc)
    ) in
  let writer_str2N (a, b, rls, wls, data2etc) v = 
    (
    let (a1,b1) = (StringMap.add (m.mid^"."^v^".data") b a,b + 1) in 
    let (a2,b2) = (StringMap.add (m.mid^"."^v^".addr") b1 a1,b1 + 1) in 
    let (a3,b3) = (StringMap.add (m.mid^"."^v^".en") b2 a2,b2 + 1) in 
    let (a4,b4) = (StringMap.add (m.mid^"."^v^".mask") b3 a3,b3 + 1) in 
    let (a5,b5) = (StringMap.add (m.mid^"."^v^".clk") b4 a4,b4 + 1) in
    (a5, b5, rls, List.cons b wls, IntMap.add b (b1,b2,flag-1,b3,b4) data2etc)
    ) in
  List.fold_left writer_str2N (List.fold_left reader_str2N (map,flag,rl,wl,datatoetc) (m.reader)) (m.writer)

let s_str2N name2ports (map,flag,rl,wl,datatoetc,memmap) stmt = 
  match stmt with
  | Ast.Swire (v, _) -> (StringMap.add v flag map,flag + 1, rl, wl, datatoetc, memmap)
  | Ast.Sreg r -> let (map0, flag0) = (StringMap.add r.rid flag map,flag + 1) in
                  (StringMap.add r.clock flag0 map0,flag0 + 1, rl, wl, datatoetc, memmap)
  | Ast.Smem m -> let map0 = StringMap.add m.mid flag map in
                  let flag0 = flag + 1 in
                  let (map1,flag1,rls,wls,data2etc) = mem_str2N m map0 flag0 rl wl datatoetc in 
                  (map1,flag1,rls,wls, data2etc,IntMap.add flag IntMap.empty memmap)
  | Ast.Snode (v, _) -> (StringMap.add v flag map,flag + 1, rl, wl, datatoetc, memmap)
  | Ast.Sinst (v1, e) -> (match e with
                        | Ast.Eref v2 -> let (map0, flag0) = List.fold_left (fun (a,b) p -> (match p with
                                                        | Ast.Finput (v3, _) -> (StringMap.add (v1^"."^v3) b a, b + 1)
                                                        | Ast.Foutput (v3, _) -> (StringMap.add (v1^"."^v3) b a, b + 1))) (map,flag) (StringMap.find v2 name2ports) in
                                             (map0, flag0, rl, wl, datatoetc, memmap)
                        | _ -> (map,flag, rl, wl, datatoetc, memmap))
  | _ -> (map,flag, rl, wl, datatoetc, memmap)

let g_modsmap name2ports (modsmap,ls, fmap, rlsm, wlsm, datatoetc, memmap) hd =  
  match hd with 
            | Ast.FInmod (mv, pl, sl) -> let (thismap0, flag0) = List.fold_left p_str2N (initmap,0) pl in
                                         let (thismap,flag, rls, wls, data2etc, memmap0) = List.fold_left (s_str2N name2ports) (thismap0, flag0, [], [], IntMap.empty, IntMap.empty) sl in
                                               (StringMap.add mv thismap modsmap, List.cons flag ls, StringMap.add mv flag fmap, StringMap.add mv rls rlsm, StringMap.add mv wls wlsm, StringMap.add mv data2etc datatoetc, StringMap.add mv memmap0 memmap)
            | _ -> (modsmap,ls, fmap, rlsm, wlsm, datatoetc, memmap)

let generate_modsmap a_cir name2ports = 
  match a_cir with
  | (_, fmod) -> List.fold_left (g_modsmap name2ports) (initmap,[],initmap,initmap,initmap,initmap,initmap) fmod

let generate_fmodsmap a_cir = 
  match a_cir with
  | (_, fmod) -> List.fold_left (fun a b -> (match b with
                                            | Ast.FInmod (mv, _,_) -> StringMap.add mv b a
                                            | Ast.FExmod (mv, _,_) -> StringMap.add mv b a)) initmap fmod

(* var -> fport list/fstmts list *)
let plbyname a_cir = 
  match a_cir with
  | (cv, ml) -> let (m1,m2) = List.fold_left (fun (m3,m4) x -> match x with 
                                            | Ast.FInmod (mv, pl, sl) -> (StringMap.add mv pl m3,StringMap.add mv sl m4)
                                            | Ast.FExmod _ -> (m3,m4)) (initmap,initmap) ml in (m1,m2, cv)

(* give the N name for modules *)
(* map: string -> N *)
let nummod flag modsmap = 
  StringMap.fold (fun key _ (map,f) -> (StringMap.add key f map, f+1)) modsmap (initmap,flag)

(* give the N name for instances *)
(* map: string(modname.instname) -> N *)
let numins flag a_cir = 
  match a_cir with
  | (_, ml) -> List.fold_left (fun (m,f) x -> match x with 
                                            | Ast.FInmod (mv, _, sl) -> List.fold_left (fun (mm,ff) xx -> match xx with 
                                                                                        | Ast.Sinst (v1, e) -> (match e with
                                                                                                              | Ast.Eref _ -> (StringMap.add (mv^"."^v1) ff mm,ff+1)
                                                                                                              | _ -> (mm,ff))
                                                                                        | _ -> (mm,ff)) (m,f) sl
                                            | Ast.FExmod _ -> (m,f)) (initmap,flag) ml

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

let trans_subport inst pmap fpl p = 
  match p with
  | Ast.Finput (v, ty) -> List.cons (Firrtl.Finput(Obj.magic (StringMap.find (inst^"."^v) pmap), trans_fgtyp ty)) fpl
  | Ast.Foutput (v, ty) -> List.cons (Firrtl.Foutput(Obj.magic (StringMap.find (inst^"."^v) pmap), trans_fgtyp ty)) fpl

let trans_stmt mv modsmap modsnum insnum name2ports s = 
  let smap = StringMap.find mv modsmap in
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
  | Ast.Sinst (v, e) -> match e with
                        | Ast.Eref v2 -> 
                          Firrtl.Sinst (Firrtl.LoFirrtl.mk_finst (Obj.magic (StringMap.find (mv^"."^v) insnum)) (Obj.magic (StringMap.find v2 modsnum)) (List.fold_left (trans_subport v smap) [] (StringMap.find v2 name2ports)))
                        | _ -> Firrtl.Sskip

let trans_port pmap fpl p = 
  match p with
  | Ast.Finput (v, ty) -> List.cons (Firrtl.Finput(Obj.magic (StringMap.find v pmap), trans_fgtyp ty)) fpl
  | Ast.Foutput (v, ty) -> List.cons (Firrtl.Foutput(Obj.magic (StringMap.find v pmap), trans_fgtyp ty)) fpl

let trans_mod modsnum modsmap insnum name2ports a_mod = 
  match a_mod with
  | Ast.FInmod (v, pl, sl) -> let fsl = List.fold_left (fun a b -> List.cons ((trans_stmt v modsmap modsnum insnum name2ports) b) a) [] sl in
                              (v, Firrtl.FInmod(Obj.magic (StringMap.find v modsnum), List.fold_left (trans_port (StringMap.find v modsmap)) [] pl, fsl), fsl)
  | Ast.FExmod (v, pl, sl) -> (v, Firrtl.FExmod(Obj.magic (StringMap.find v modsnum), List.fold_left (trans_port (StringMap.find v modsmap)) [] pl, List.fold_left (fun a b -> List.cons ((trans_stmt v modsmap modsnum insnum name2ports) b) a) [] sl), [])

  (* 返回 map modnum(N) -> Firrtl.fmod *)
let trans_ml fmod modsnum modsmap insnum name2ports = 
  List.fold_left (fun (ma,mb) mo -> let (v, fm, fsl) = (trans_mod modsnum modsmap insnum name2ports mo) in 
                               let vn = (StringMap.find v modsnum) in
                                IntMap.add vn fm ma, IntMap.add vn fsl mb) (initmap0, initmap0) fmod

let find_mainm cv old a_mod = 
  match a_mod with
  | Ast.FInmod (v, _,_) -> if (String.equal cv v) then a_mod else old
  | Ast.FExmod (v, _,_) -> if (String.equal cv v) then a_mod else old
                            
let trans_cir a_cir modsnum modsmap insnum name2ports = 
  match a_cir with
  | (v, fmod) -> let (fm, fsl) = trans_ml fmod modsnum modsmap insnum name2ports in
                 let mainm = List.fold_left (find_mainm v) (List.nth fmod 0) fmod in
                  (v,mainm, fm,fsl)

let m_readla modsmap rlmap s =
  match s with
  | Ast.Smem m -> if (Z.to_int m.read_latency) == 0 then IntMap.add (StringMap.find m.mid modsmap) false rlmap
  else IntMap.add (StringMap.find m.mid modsmap) true rlmap
  | _ -> rlmap

let mod_readla modsnum modsmap rlmap m =
  match m with
  | Ast.FInmod (v, _,sl) -> let mv = (StringMap.find v modsnum) in 
                            let trlmap = List.fold_left (m_readla (StringMap.find v modsmap)) initmap0 sl in
                            IntMap.add mv trlmap rlmap
  | Ast.FExmod (_, _,_) -> rlmap

let read_la_map a_cir modsnum modsmap =
  match a_cir with
  | (_, fmod) -> List.fold_left (mod_readla modsnum modsmap) initmap0 fmod

(* 对每次声明instance找到端口对应*)
(* var -> map(N -> N)*)
let mmapport name2ports modsmap insnum mv (inin2exin,exout2inout) s = 
  match s with
  | Ast.Sinst (v1, e) -> (match e with
                        | Ast.Eref v2 -> 
                        let (newin, newout) = List.fold_left (fun (a,b) p -> (match p with
                                                        | Ast.Finput (v3, _) -> (IntMap.add (StringMap.find v3 (StringMap.find v2 modsmap)) (StringMap.find (v1^"."^v3) (StringMap.find mv modsmap)) a,b)
                                                        | Ast.Foutput (v3, _) -> (a,IntMap.add (StringMap.find (v1^"."^v3) (StringMap.find mv modsmap)) (StringMap.find v3 (StringMap.find v2 modsmap)) b))) (initmap0,exout2inout) (StringMap.find v2 name2ports) in
                        (IntMap.add (StringMap.find (mv^"."^v1) insnum) newin inin2exin, newout)
                        | _ -> (inin2exin,exout2inout) )
  | _ -> (inin2exin,exout2inout)

let mapport name2ports modsmap insnum instportm m = 
  match m with
  | Ast.FInmod (mv, _, sl) -> let (a,b) =  List.fold_left (mmapport name2ports modsmap insnum mv) (initmap0, initmap0) sl in
                              StringMap.add mv (a,b) instportm
  | Ast.FExmod _ -> instportm

let mapinstport a_cir name2ports modsmap insnum = 
  match a_cir with
  | (_, ml) -> List.fold_left (mapport name2ports modsmap insnum) initmap ml

let oouti2e name2ports modsmap insnum mv inout2exout s = 
  match s with
  | Ast.Sinst (v1, e) -> (match e with
                        | Ast.Eref v2 -> 
                        let newout = List.fold_left (fun a p -> (match p with
                                                        | Ast.Finput (_, _) -> a
                                                        | Ast.Foutput (v3, _) -> IntMap.add (StringMap.find v3 (StringMap.find v2 modsmap)) (StringMap.find (v1^"."^v3) (StringMap.find mv modsmap)) a))
                                                         initmap0 (StringMap.find v2 name2ports) in
                        IntMap.add (StringMap.find (mv^"."^v1) insnum) newout inout2exout
                        | _ -> inout2exout)
  | _ -> inout2exout

let outi2e name2ports modsmap insnum instportm m = 
  match m with
  | Ast.FInmod (mv, _, sl) -> List.fold_left (oouti2e name2ports modsmap insnum mv) instportm sl
  | Ast.FExmod _ -> instportm

let instouti2e a_cir name2ports modsmap insnum = 
  match a_cir with
  | (_, ml) -> List.fold_left (outi2e name2ports modsmap insnum) initmap0 ml

(* 初始化所有inst的env、store、memory *)
let initinst modsnum _ insnum initmodmap memmap tt m = (* te -> ( inst -> te/rs/s/mem)*)
  match m with
  | Ast.FInmod (v, _, sl) ->  List.fold_left (fun t s -> match s with
                              | Ast.Sinst (v1, e) -> (match e with
                                                    | Ast.Eref v2 -> let tesrs = IntMap.find (StringMap.find v2 modsnum) initmodmap in
                                                                     let tmem = StringMap.find v2 memmap in
                                                                                IntMap.add (StringMap.find (v^"."^v1) insnum) (((tesrs, Env.Store.empty), Env.Store.empty),tmem) t
                                                    | _ -> t)
                              | _ -> t
                            ) tt sl
  | Ast.FExmod _ -> tt

let initmod m =  (* mod var -> te *)
  match m with
  | Firrtl.FInmod (_, pl, sl) -> let te0 = Firrtl.LoFirrtl.upd_typenv_fports pl Env.TE.empty in
                                 Firrtl.LoFirrtl.upd_typenv_fstmts sl te0 Env.Store.empty
  | Firrtl.FExmod _ -> Env.TE.empty

let initmodenv a_cir modsmap fmodsmap modsnum insnum memmap =  (* inst var -> (te\s\rs\mid->mem) *)
  let initmodmap = IntMap.fold (fun v m -> IntMap.add v (initmod m)) fmodsmap initmap0 in
  match a_cir with
  | (cv, amod) -> let tempm = List.fold_left (fun t m -> initinst modsnum modsmap insnum initmodmap memmap t m) initmap0 amod in
                  let mainname = (StringMap.find cv modsnum) in
                  let mainte = IntMap.find mainname initmodmap in
                  IntMap.add mainname (((mainte,Env.Store.empty),Env.Store.empty),StringMap.find cv memmap) tempm

let instout (l1,l2) mo = 
  match mo with
  | Ast.FInmod (v, pl, _) -> let (nl1,nl2) = List.fold_left (fun (templ1,templ2) tempp -> match tempp with 
                                                                          | Ast.Finput (v1, _) -> (List.cons v1 templ1, templ2)
                                                                          | Ast.Foutput (v1, _) -> (templ1, List.cons v1 templ2)) ([],[]) pl in
                              (StringMap.add v nl1 l1,StringMap.add v nl2 l2)

  | Ast.FExmod _ -> (l1,l2)

let instoutport modsnum modsmap insnum instout (m,l) mo = (* outer module name -> inst output -> (inner module name, instance name) *)
match mo with
| Ast.FInmod (v, _, sl) ->  let modname = StringMap.find v modsnum in
                            let tmodsmap = StringMap.find v modsmap in (* string -> int *)
                            let (outportm,outportl) =  List.fold_left (fun (t1,t2) s -> match s with
                                                      | Ast.Sinst (v1, e) -> (match e with
                                                                            | Ast.Eref v2 -> let templ = StringMap.find v2 instout in(* 该inst stmt声明的mod的 outport list *)
                                                                                             let ttempl = List.map (fun str -> StringMap.find (v1^"."^str) tmodsmap) templ in
                                                                                             let tempm = List.fold_left (fun tt1 tp -> IntMap.add tp ((StringMap.find v2 modsnum),StringMap.find (v^"."^v1) insnum) tt1) t1 ttempl in
                                                                                                         (tempm, List.append ttempl t2)
                                                                            | _ -> (t1,t2))
                                                      | _ -> (t1,t2)
                            ) (initmap0,[]) sl in
                            (IntMap.add modname outportm m,IntMap.add modname outportl l)
| Ast.FExmod _ -> (m,l)

let findoutport a_cir modsmap modsnum insnum =
  match a_cir with
  | (_, amod) -> let (instin,instout) = List.fold_left (fun t m -> instout t m) (initmap,initmap) amod in(* mod -> outport int -> string list*)
                  (instin,instout,List.fold_left (fun t m -> instoutport modsnum modsmap insnum instout t m) (initmap0,initmap0) amod)

let inst2sl_m modsnum insnum fstmtsmap m mo = 
  match mo with
  | Ast.FInmod (v, _, sl) -> List.fold_left (fun m0 s -> match s with
                             | Ast.Sinst (v1, e) -> (match e with
                                                    | Ast.Eref v2 -> IntMap.add (StringMap.find (v^"."^v1) insnum) (IntMap.find (StringMap.find v2 modsnum) fstmtsmap) m0
                                                    | _ -> m0)
                             | _ -> m0) m sl
  | Ast.FExmod _ -> m

let inst2sl a_cir modsnum insnum fstmtsmap = 
  match a_cir with
  | (_, amod) -> List.fold_left (inst2sl_m modsnum insnum fstmtsmap) initmap0 amod 

let rec countnum_e e ls = 
  match e with
  | Firrtl.Econst _ -> 0
  | Firrtl.Eref v -> if List.mem (Obj.magic v) ls then 1 else 0
  | Firrtl.Eprim_unop (_, e1) -> countnum_e e1 ls
  | Firrtl.Eprim_binop (_, e1, e2) -> countnum_e e1 ls + countnum_e e2 ls
  | Firrtl.Emux (e1, e2, e3) -> countnum_e e1 ls + countnum_e e2 ls + countnum_e e3 ls
  | Firrtl.Evalidif (e1,e2) -> countnum_e e1 ls + countnum_e e2 ls
  | Firrtl.Ecast (_, e1) -> countnum_e e1 ls

let countnum_s fst ls = 
  match fst with
  | Firrtl.Sskip -> 0
  | Firrtl.Swire _ -> 0
  | Firrtl.Sfcnct (e1, e2) -> countnum_e e1 ls + countnum_e e2 ls
  | Firrtl.Sinvalid v -> if List.mem (Obj.magic v) ls then 1 else 0
  | Firrtl.Snode (_, e) -> countnum_e e ls
  | Firrtl.Sreg _ -> 0
  | Firrtl.Smem _ -> 0
  | Firrtl.Sinst _ -> 0
  | _ -> 0

let countnum fmod ls = 
  match fmod with
  | Firrtl.FInmod (_ , _, sl) -> List.fold_left (fun n st -> n + (countnum_s st ls)) 0 sl 
  | Firrtl.FExmod _ -> 0
                
let finditernum fmodsmap instoutl = (* 两个以modname int为key*)
  IntMap.fold (fun key value num -> (num + (countnum (IntMap.find key fmodsmap) value))) instoutl 0 (* value *)

module Int = struct
  type t = int
  let compare = compare
  let hash = Hashtbl.hash
  let equal = (=)
  let default = -1
end
module G = Persistent.Digraph.Concrete(Int)

module C = Graph.Components.Make(G)

let modgraph_s modnum modsnum g s =
  match s with
  | Ast.Sinst (_,e) -> (match e with
                        | Ast.Eref v2 -> G.add_edge g modnum (StringMap.find v2 modsnum)
                        | _ -> g)
  | _ -> g

let modgraph_m modsnum g m = 
  match m with
  | Ast.FInmod (mv , _, sl) -> let modnum = StringMap.find mv modsnum in
                               let g0 = G.add_vertex g modnum in
                                  List.fold_left (modgraph_s modnum modsnum) g0 sl
  | Ast.FExmod _ -> g

let modgraph modsnum a_cir = 
  match a_cir with
  | (_, fmod) -> List.fold_left (modgraph_m modsnum) G.empty fmod

let parse f =
  let lexbuf = Lexing.from_channel (open_in f) in
  FirrtlParser.file FirrtlLexer.token lexbuf

let lowf_ast = parse "./demo/Accumulator.lo.fir" 

let p_stmt s = 
  match s with
  | Firrtl.Sfcnct (e1, _) -> (match e1 with
                            | Eref v1 -> printf "%d cnct\n" (Obj.magic v1)
                            | _ -> printf "\n")
  | Firrtl.Snode (v, _) -> printf "%d node\n" (Obj.magic v)
  | Firrtl.Swire (v, _) -> printf "%d wire\n" (Obj.magic v)
  | Firrtl.Sinvalid v -> printf "%d invalid\n" (Obj.magic v)  
  | Firrtl.Sreg r -> printf "%d reg\n" (Obj.magic r.rid)
  | Firrtl.Sskip -> printf "skip\n"
  | _ -> printf "\n"

let () = 
  let clks = 100 in
  let (name2ports,_ , _) = plbyname lowf_ast in
  let (modsmap,flagls,flagmap,rlsm,wlsm,datatoetc,memmap) = generate_modsmap lowf_ast name2ports in (* memmap *)
  let (modsnum,flags) = nummod (ls_max flagls) modsmap in

  let readla = read_la_map lowf_ast modsnum modsmap in
  IntMap.iter (fun _ value -> IntMap.iter (fun key bv -> printf "%d:%b\n" key bv) value;) readla;

  let (insnum,flagss) = numins flags lowf_ast in
  let inslength = flagss - flags in
  (*
  printf "inslength : %d\n" inslength;
  StringMap.iter (fun key value -> (printf "%s: " key); (if (IntMap.is_empty value) then printf "no mem" else (IntMap.iter (fun key0 _ -> (printf "%d:" key0); printf "\n") value)); printf "\n") memmap; printf "\n";
  StringMap.iter (fun key value -> (printf "%s: " key); printf "\n"; IntMap.iter (fun key0 (a,b,c,d) -> (printf "%d: %d; %d; %d; %d" key0 a b c d); printf "\n") value) datatoetc; printf "\n";
  *)StringMap.iter (fun key value -> (printf "%s: \nwriter.data:" key ); printf "\n"; printf_list value) wlsm;
  StringMap.iter (fun key value -> (printf "%s: \nreader.data:" key ); printf "\n"; printf_list value) rlsm;
  
  let (cv, mainm, fmodsmap, fstmtsmap) = trans_cir lowf_ast modsnum modsmap insnum name2ports in
  (*printf "mainmod : %s\n" cv;
  IntMap.iter (fun key _ -> printf "%d:\n" key) fmodsmap;
  IntMap.iter (fun key _ -> printf " modstmt %d:\n" key) fstmtsmap;
  StringMap.iter (fun key value -> printf "%s : %d\n" key value) insnum;*)

  (* generate inp *)
  let (inp_bitsmap, inp_lst, ulst) = Helper.generate_map lowf_ast clks (initmap, [], []) in
  let my2Z k = 
    (if (List.mem k ulst) then (List.map Helper.nat_of_bits)
    else (List.map Helper.z_of_bits)) in
  
  let mainmap = StringMap.find cv modsmap in
  let (_,inp_intlst,uintlst) = Helper.m_extract_i mainmap inp_bitsmap mainm in(*inp_intmap*)
  (*StringMap.iter (fun key _ -> printf "%s:\n" key; printf "\n") inp_map;
  IntMap.iter (fun key _ -> printf "%d:\n" key; printf "\n") inp_intmap;
  printf_list0 inp_lst;
  printf_list inp_intlst;
  printf_list uintlst;*)

  let instportmap = mapinstport lowf_ast name2ports modsmap insnum in (* 每个mod 内外部接口关系 *)
  let insti2e_outmap = instouti2e lowf_ast name2ports modsmap insnum in 
  let newinstportmap = StringMap.map (fun (value1,value2) -> (IntMap.fold (fun _ tempv newm -> IntMap.fold (fun tempk0 tempv0 newm0 -> IntMap.add tempv0 tempk0 newm0) tempv newm) value1 IntMap.empty, value2)) instportmap in
  StringMap.iter (fun key (value1,value2) -> (printf "%s: \n" key; IntMap.iter (fun key3 value3 -> (printf "%d: \n" key3; IntMap.iter (fun key0 val0 -> printf "inin2exin : %d -> %d\n" key0 val0) value3;)) value1; IntMap.iter (fun key0 val0 -> printf "exout2inout : %d -> %d\n" key0 val0) value2;)) instportmap;
  StringMap.iter (fun key (value1,value2) -> (printf "%s: \n" key; IntMap.iter (fun key0 val0 -> printf "exin2inin : %d -> %d\n" key0 val0) value1; IntMap.iter (fun key0 val0 -> printf "exout2inout : %d -> %d\n" key0 val0) value2;)) newinstportmap;
  IntMap.iter (fun key value -> (printf "%d: \n" key; IntMap.iter (fun key3 value3 -> (printf "%d: %d\n" key3 value3;)) value)) insti2e_outmap;
  let initterss = initmodenv lowf_ast modsmap fmodsmap modsnum insnum memmap in (* mod的内部inst的状态te/rs/s/mem *)
  (*IntMap.iter (fun key (((value,_),_),_) -> printf "%d:\n" key; printf "%d\n" (Env.TE.vsize (Obj.magic 2) value); printf "\n") initterss;
*)
  let (instin,instout,(instoutm,instoutl)) = findoutport lowf_ast modsmap modsnum insnum in
  printf "module inputs:\n";
  StringMap.iter (fun key0 value0 -> (printf "%s: \n" key0 ; printf_list0 value0;)) instin;
  StringMap.iter (fun key0 value0 -> (printf "%s: \n" key0 ; printf_list0 value0;)) instout;
  IntMap.iter (fun key0 value0 -> (printf "%d: \n" key0 ; printf_list value0;)) instoutl;
  (*IntMap.iter (fun key0 value0 -> (printf "%d: \n" key0 ; IntMap.iter (fun key (value1,value2) -> (printf "%d -> (%d, %d)" key value1 value2); printf "\n") value0;)) instoutm;*)
  let insoutnum = finditernum fmodsmap instoutl in
  printf "insoutnum: %d \n" insoutnum;
  printf "insnum: %d \n" inslength;
  let iternum = insoutnum + inslength in
  printf "iternum: %d \n" iternum;

  let readerls = StringMap.fold (fun key value -> Env.TE.add (Obj.magic (StringMap.find key modsnum)) (List.map Obj.magic value)) rlsm Env.TE.empty in
  let writerls = StringMap.fold (fun key value -> Env.TE.add (Obj.magic (StringMap.find key modsnum)) (List.map Obj.magic value)) wlsm Env.TE.empty in
  let transmap0 imap = IntMap.fold (fun key (a,b,c,d,e) -> Env.TE.add (Obj.magic key) ((((((Obj.magic a),(Obj.magic b)),(Obj.magic c)),(Obj.magic d)),(Obj.magic e)))) imap Env.TE.empty in
  let data2etc = StringMap.fold (fun key value -> Env.TE.add (Obj.magic (StringMap.find key modsnum)) (transmap0 value)) datatoetc Env.TE.empty in
  let transmap2 imap = IntMap.fold (fun key value -> Firrtl.LoFirrtl.memupd (bits_of_z 1 (Z.of_int key)) (bits_of_z 1 (Z.of_int value))) imap Firrtl.LoFirrtl.memempty in (* 应该是个空 *)
  let transmap1 imap = IntMap.fold (fun key value -> Env.TE.add (Obj.magic key) (transmap2 value)) imap Env.TE.empty in
  (*let vmemmap = StringMap.fold (fun key value -> Env.TE.add (Obj.magic (StringMap.find key modsnum)) (transmap1 value)) memmap Env.TE.empty in*)
  
  let transmap3 imap = IntMap.fold (fun key value -> Env.TE.add (Obj.magic key) (Obj.magic value)) imap Env.TE.empty in
  let transmap4 imap = IntMap.fold (fun key value -> Env.TE.add (Obj.magic key) (transmap3 value)) imap Env.TE.empty in
  let finstportmap = StringMap.fold (fun key (value1,value2) -> Env.TE.add (Obj.magic (StringMap.find key modsnum)) (transmap4 value1, transmap3 value2)) instportmap Env.TE.empty in
  let fnewinstportmap = StringMap.fold (fun key (value1,value2) -> Env.TE.add (Obj.magic (StringMap.find key modsnum)) (transmap3 value1, transmap3 value2)) newinstportmap Env.TE.empty in
  let finsti2e_outmap = IntMap.fold (fun key value -> Env.TE.add (Obj.magic key) (transmap3 value)) insti2e_outmap Env.TE.empty in
  let finitterss = IntMap.fold (fun key (((value1,value2),value3),value4) -> Env.TE.add (Obj.magic key) (((value1,value2),value3),transmap1 value4)) initterss Env.TE.empty in

  let finstoutl = IntMap.fold (fun key value -> Env.TE.add (Obj.magic key) (List.map Obj.magic value)) instoutl Env.TE.empty in
  
  let transmap5 imap = IntMap.fold (fun key (value1,value2) -> Env.TE.add (Obj.magic key) ((Obj.magic value1),(Obj.magic value2))) imap Env.TE.empty in
  let finstoutm = IntMap.fold (fun key value -> Env.TE.add (Obj.magic key) (transmap5 value)) instoutm Env.TE.empty in

  let ffstmtsmap = IntMap.fold (fun key value -> Env.TE.add (Obj.magic key) value) fstmtsmap Env.TE.empty in

  let finstin = StringMap.fold (fun key value -> Env.TE.add (Obj.magic (StringMap.find key modsnum)) (List.map (fun str -> (Obj.magic (StringMap.find str (StringMap.find key modsmap)))) value)) instin Env.TE.empty in
  let finstout = StringMap.fold (fun key value -> Env.TE.add (Obj.magic (StringMap.find key modsnum)) (List.map (fun str -> (Obj.magic (StringMap.find str (StringMap.find key modsmap)))) value)) instout Env.TE.empty in
  (*let finst2stmts = IntMap.fold (fun key value -> Env.TE.add (Obj.magic key) value) inst2stmts Env.TE.empty in
  *)
  let fflagmap = StringMap.fold (fun key value -> Env.TE.add (Obj.magic (StringMap.find key modsnum)) value) flagmap Env.TE.empty in
  let transmap6 imap = IntMap.fold (fun key value -> Env.TE.add (Obj.magic key) value) imap Env.TE.empty in
  let freadla =  IntMap.fold (fun key value -> Env.TE.add (Obj.magic key) (transmap6 value)) readla Env.TE.empty in
  
  (*let inp_bitsmap = StringMap.add "clockw" [[false;];[true;];[false;];[true;];[false;];] inp_bitsmap in
  let inp_bitsmap = StringMap.add "clockr" [[false;];[false;];[true;];[true;];[false;];] inp_bitsmap in
  let inp_bitsmap = StringMap.add "io_writeAddress" [[true;];[true;];[true;];[true;];[true;];] inp_bitsmap in
  let inp_bitsmap = StringMap.add "io_readAddress" [[true;];[true;];[true;];[true;];[true;];] inp_bitsmap in*)
  let inp_map = StringMap.map (List.map Z.to_int) (StringMap.mapi my2Z inp_bitsmap) in
  let finp_bitsmap = StringMap.fold (fun key value -> Env.TE.add (Obj.magic (StringMap.find key mainmap)) value) inp_bitsmap Env.TE.empty in

  (*let mainmod = IntMap.find (StringMap.find cv modsnum) fmodsmap in
  match mainmod with
  | Firrtl.FExmod _ -> printf "no stmt\n";
  | Firrtl.FInmod (_ , _, sl) -> List.iter p_stmt sl;*)

  let modg = modgraph modsnum lowf_ast in
  let modorder = C.scc_list modg in
  let morder = List.concat modorder in
  printf "mod order\n";
  printf_list morder;

  match Env.TE.find (Obj.magic (StringMap.find cv modsnum)) finitterss with
  | None -> printf "no main te s rs mem.\n";
  | Some a -> let (((te0,rs0),s0),mem0) = a in

  let ointls = List.map (fun a -> StringMap.find a (StringMap.find cv modsmap)) (StringMap.find cv instout) in
  let ut1 = (Unix.times()).tms_utime in
(*
  let (((_,sor),_),_)= Firrtl.LoFirrtl.modname2g (Obj.magic morder) fflagmap ffstmtsmap fnewinstportmap finsti2e_outmap finstin finstout finstoutl Env.TE.empty Env.TE.empty Env.TE.empty Env.TE.empty in
  match (Env.TE.find (Obj.magic 42) sor) with
  | None -> printf "no 42";
  | Some sorder -> List.iter p_stmt sorder;

  match (Env.TE.find (Obj.magic 40) allg) with
  | None -> printf "no 44g";
  | Some kg -> if (Firrtl.LoFirrtl.dfs_path kg 44 (Obj.magic 12) (Obj.magic 2)) then printf "12->2\n";

  match (Env.TE.find (Obj.magic 45) allg) with
  | None -> printf "no 45g";
  | Some kg -> 
  printf_list (Obj.magic (Firrtl.LoFirrtl.dfs kg 39 [] (Obj.magic 5)));
  printf_list (Obj.magic (kg (Obj.magic 15)));

  match (Env.TE.find (Obj.magic 45) finstin) with
  | None -> printf "no 45";
  | Some inps ->
  let len = (match (Env.TE.find (Obj.magic 45) fflagmap) with
  | Some n -> n 
  | None -> 0
  ) in 
  match (Env.TE.find (Obj.magic 45) ffstmtsmap) with
  | None -> printf "no ordered45";
  | Some olds -> 
  let (_, roots) = List.fold_left (fun (ls1, ls2) tst -> Firrtl.LoFirrtl.findreg ls1 ls2 tst) ([], []) olds in

  match (Firrtl.LoFirrtl.topo_sort kg len (List.append inps roots)) with
              | None -> printf "meipai";
              | Some tseq -> printf_list (Obj.magic tseq);
  
  let (inportsmap, outportsmap) =
        match Env.TE.find (Obj.magic 40) fnewinstportmap with
        | Some tempm -> tempm
        | None -> (Env.TE.empty, Env.TE.empty)
      in
      let (newg, var2stmt) =
        List.fold_left (fun pat tempst ->
          let (tempg, tempm) = pat in
          Firrtl.LoFirrtl.buildg [] fflagmap inportsmap outportsmap allg tempg tempm
            tempst) (Firrtl.LoFirrtl.emptyg, Env.TE.empty) olds
      in

  let (newstmts, varorder) = Firrtl.LoFirrtl.reorder (Obj.magic morder) fflagmap ffstmtsmap fnewinstportmap finsti2e_outmap finstin finstout finstoutl in
  
  printf "varorder:\n";
  match (Env.TE.find (Obj.magic 29) varorder) with
  | None -> printf "no var42";
  | Some tor -> printf_list (Obj.magic tor); printf "len: %d\n" (List.length tor);

  match (Env.TE.find (Obj.magic 29) ffstmtsmap) with
  | None -> printf "no var42";
  | Some tor -> printf "old stmts length:%d\n" (List.length tor); 

  match (Env.TE.find (Obj.magic 29) newstmts) with
  | None -> printf "no var38";
  | Some tnewsts -> List.iter p_stmt tnewsts; printf "new length:%d\n" (List.length tnewsts); 
  
  match (Env.TE.find (Obj.magic 9) var2stmt) with
  | None -> printf "no9stmt\n";
  | Some _ -> printf "yes9stmt\n";

  printf_list (Obj.magic (Firrtl.LoFirrtl.dfs kg 39 [] (Obj.magic 5)));
  printf_list (Obj.magic (newg (Obj.magic 15)));

  printf "origin: %d\n" (List.length olds);
  (*printf "vars: %d\n" (List.length tor);
  printf "news: %d\n" (List.length tst);*)
*)
  let ((((rs2,s2),_),_), outputmap) = Firrtl.LoFirrtl.run_module (Obj.magic morder) fflagmap fnewinstportmap finsti2e_outmap (Obj.magic (StringMap.find cv modsnum)) rs0 s0 te0 finp_bitsmap (List.map Obj.magic inp_intlst) (List.map Obj.magic ointls) readerls writerls data2etc mem0 clks clks finstoutl finstoutm ffstmtsmap finitterss freadla finstin finstout finstportmap iternum in

  printf "%f\n" (Float.sub (Unix.times()).tms_utime ut1);
  let out_map = List.fold_left (fun b a -> match (Env.TE.find a outputmap) with
                                          | Some ols -> let newol = (if (List.mem a (List.map Obj.magic uintlst)) then (List.map string_of_big_int (List.map nat_of_bits ols))
                                          else (List.map string_of_big_int (List.map Helper.z_of_bits ols)))
                                             in (*printf "output3\n"; printf_list0 (List.map string_of_big_int (List.map nat_of_bits ols));*)
                                             IntMap.add (Obj.magic a) newol b
                                          | None -> (*printf "no output3\n"; *)
                                             IntMap.add (Obj.magic a) [] b) initmap0 (List.map Obj.magic ointls) in

let ((((_,_),_),_), outputmap0) = Firrtl.LoFirrtl.run_module0 (Obj.magic (StringMap.find cv modsnum)) rs0 s0 te0 finp_bitsmap (List.map Obj.magic inp_intlst) (List.map Obj.magic ointls) readerls writerls data2etc mem0 clks clks finstoutl finstoutm ffstmtsmap finitterss freadla finstin finstportmap iternum in

  let out_map0 = List.fold_left (fun b a -> match (Env.TE.find a outputmap0) with
                                          | Some ols -> let newol = (if (List.mem a (List.map Obj.magic uintlst)) then (List.map string_of_big_int (List.map nat_of_bits ols))
                                          else (List.map string_of_big_int (List.map Helper.z_of_bits ols)))
                                             in (*printf "output3\n"; printf_list0 (List.map string_of_big_int (List.map nat_of_bits ols));*)
                                             IntMap.add (Obj.magic a) newol b
                                          | None -> (*printf "no output3\n"; *)
                                             IntMap.add (Obj.magic a) [] b) initmap0 (List.map Obj.magic ointls) in

  let oc = open_out file in
  fprintf oc "input:\n";
  List.iter (fprintf oc "%s ") inp_lst;
  fprintf oc "\n";
  fprintf oc "output:\n";
  List.iter (fprintf oc "%s ") (StringMap.find cv instout);
  fprintf oc "\n";
  fprintf oc "valmap:\n";
  StringMap.iter (fun key value -> if (List.mem key inp_lst) then (fprintf oc "%s:" key; List.iter (fprintf oc " %d") value; fprintf oc "\n")) inp_map;
  fprintf oc "answer:\n";
  IntMap.iter (fun key value -> (fprintf oc "%d:" key; List.iter (fprintf oc " %s") (value)); fprintf oc "\n") out_map;
  fprintf oc "answer0:\n";
  IntMap.iter (fun key value -> (fprintf oc "%d:" key; List.iter (fprintf oc " %s") (value)); fprintf oc "\n") out_map0;
  fprintf oc "label:\n";
  StringMap.iter (fun key value -> if (String.equal cv key) then ((fprintf oc "%s:" key); StringMap.iter (fun key0 value0 -> (fprintf oc "\n"; fprintf oc "%s:%d" key0 value0)) value)
                                    ) modsmap;
  (*StringMap.iter (fun key0 value0 -> (fprintf oc "%s: %d" key0 value0); fprintf oc "\n") modsnum;
  StringMap.iter (fun key0 value0 -> (fprintf oc "%s: %d" key0 value0); fprintf oc "\n") insnum;
  *)close_out oc;

  printf "T4clk:%d\n" (Z.to_int (nat_of_bits (Env.Store.acc (Obj.magic 16) s2)));
  printf "wclk:%d\n" (Z.to_int (nat_of_bits (Env.Store.acc (Obj.magic 1) s2)));
  printf "T4clk:%d\n" (Z.to_int (nat_of_bits (Env.Store.acc (Obj.magic 16) rs2)));

  (*
  printf "wradd:%d\n" (Z.to_int (nat_of_bits (Env.Store.acc (Obj.magic 13) s2)));
  printf "wrclk:%d\n" (Z.to_int (nat_of_bits (Env.Store.acc (Obj.magic 16) s2)));
  printf "wrdata:%d\n" (Z.to_int (nat_of_bits (Env.Store.acc (Obj.magic 12) s2)));
  printf "wren:%d\n" (Z.to_int (nat_of_bits (Env.Store.acc (Obj.magic 14) s2)));
  printf "wrmsk:%d\n" (Z.to_int (nat_of_bits (Env.Store.acc (Obj.magic 15) s2)));

  printf "rdadd:%d\n" (Z.to_int (nat_of_bits (Env.Store.acc (Obj.magic 9) s2)));
  printf "rdclk:%d\n" (Z.to_int (nat_of_bits (Env.Store.acc (Obj.magic 11) s2)));
  printf "rddata:%d\n" (Z.to_int (nat_of_bits (Env.Store.acc (Obj.magic 8) s2)));
  printf "rden:%d\n" (Z.to_int (nat_of_bits (Env.Store.acc (Obj.magic 10) s2)));

  match Env.TE.find (Obj.magic 7) mem2 with
  | None -> printf "no mem.\n";
  | Some a -> printf "1:%d\n" (Z.to_int (nat_of_bits (Firrtl.LoFirrtl.memfind [true;] a)));
  printf "0:%d\n" (Z.to_int (nat_of_bits (Firrtl.LoFirrtl.memfind [false;] a)));
*)
  (*  printf "word:%d\n" (Seq.size (Env.Store.acc (Obj.magic 27) s2));
  match (Env.TE.vtyp (Obj.magic 27) te0) with
  | Env.Fuint w1 -> printf "uint %d\n" (w1);
  | Env.Fsint w1 -> printf "sint %d\n" (w1);
  | _ -> printf "shayebushi";

  printf "gen14:%d\n" (Z.to_int (nat_of_bits (Env.Store.acc (Obj.magic 41) s2)));

  match Env.TE.find (Obj.magic 41) fterss2 with
  | None -> printf "no inst24 te s rs mem.\n";
  | Some a -> 
    
    let (((te3,rs3),s3),_) = a in
  List.iter (fun key -> printf "a: %d: %d\n" key (Z.to_int (nat_of_bits (Env.Store.acc (Obj.magic key) s3)));) [2;3;4;5;6;7;8;9;10;12;20;21;22;23;24;25;26;27;28;29;30;31;32;33;34;35;36;37;38];
  printf "%d\n" (Z.to_int (nat_of_bits (Env.Store.acc (Obj.magic 3) rs2)));
  printf "10: %d\n" (Z.to_int (nat_of_bits (Env.Store.acc (Obj.magic 10) rs3)));
  printf "12: %d\n" (Z.to_int (nat_of_bits (Env.Store.acc (Obj.magic 12) rs3)));
  printf "%d\n" (Env.TE.vsize (Obj.magic 4) te3);

  match Env.TE.find (Obj.magic 42) fterss2 with
  | None -> printf "no inst42 te s rs mem.\n";
  | Some a -> let (((te3,rs3),s3),_) = a in
  List.iter (fun key -> printf "b: %d: %d\n" key (Z.to_int (nat_of_bits (Env.Store.acc (Obj.magic key) s3)));) [2;3;4;5;6;7;8;9;10;12;20;21;22;23;24;25;26;27;28;29;30;31;32;33;34;35;36;37;38];
  printf "10: %d\n" (Z.to_int (nat_of_bits (Env.Store.acc (Obj.magic 10) rs3)));
  printf "12: %d\n" (Z.to_int (nat_of_bits (Env.Store.acc (Obj.magic 12) rs3)));
  printf "%d\n" (Seq.size (Env.Store.acc (Obj.magic 3) s2));
  printf "%d\n" (Env.TE.vsize (Obj.magic 4) te3);
  *)