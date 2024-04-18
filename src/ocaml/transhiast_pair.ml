open Hifirrtl_lang
open Printf
open Extraction
open Nodehelper
open HiFirrtl

module StringMap = Map.Make(String)
let initmap_s = StringMap.empty
(*module IntMap = Map.Make(Int)
let initmap_i = IntMap.empty*)

let rec mapftype v (map, flag) cnt ft =
  match ft with
  | Ast.Gtyp _ -> (StringMap.add v (flag, cnt) map, cnt + 1)
  | Ast.Atyp (atyp, n) -> mapatyp v (StringMap.add v (flag, cnt) map, flag) (cnt + 1) atyp n
  | Ast.Btyp btyp -> mapbtyp v (StringMap.add v (flag, cnt) map, flag) (cnt + 1) btyp 
  
  and mapatyp v (map, flag) cnt ft n =
  if n = 1 then
  mapftype (v^"[0]") (map, flag) cnt ft
  else let (map0, cnt0) = mapatyp v (map, flag) cnt ft (n - 1) in 
       mapftype (v^"["^(Int.to_string (n - 1))^"]") (map0, flag) cnt0 ft

  and mapbtyp v (map, flag) cnt btyp =
  match btyp with 
  | Ast.Fnil -> (map, cnt)
  | Ast.Fflips (fv, _, ft, ff) -> let (map0, cnt0) = mapftype (v^"."^fv) (map, flag) cnt ft in
                                  mapbtyp v (map0, flag) cnt0 ff

let mapport (map, tmap, flag) p = 
  match p with
  | Ast.Finput (v, ty) -> let (map0, _) = mapftype v (map, flag) 0 ty in
                         (map0, StringMap.add v ty tmap, flag + 1)
  | Ast.Foutput (v, ty) -> let (map0, _) = mapftype v (map, flag) 0 ty in
                         (map0, StringMap.add v ty tmap, flag + 1)
                         
let rec mapstmt (map, tmap, flag) stmt = 
  match stmt with
  | Ast.Swire (v, ty) -> let (map0, _) = mapftype v (map, flag) 0 ty in
                         (map0, StringMap.add v ty tmap, flag + 1)
  | Ast.Sreg (v, r) -> let (map0, _) = mapftype v (map, flag) 0 r.coq_type in
                       (map0, StringMap.add v r.coq_type tmap, flag + 1)
  | Ast.Smem (v, _) -> (StringMap.add v (flag, 0) map, tmap, flag + 1)
  | Ast.Snode (v, e) -> (match type_of_hfexpr e tmap with
                        | Some ty -> let (map0, _) = mapftype v (map, flag) 0 ty in
                                    (map0, StringMap.add v ty tmap, flag + 1)
                        | None -> printf "%s wrong expr type\n" v; (map,tmap,flag))
  | Ast.Sinst (v, _) -> (StringMap.add v (flag, 0) map, tmap, flag + 1)
  | Ast.Swhen (_, s1, s2) -> mapstmts (mapstmts (map, tmap, flag) s1) s2
  | _ -> (map,tmap,flag)

 and mapstmts (map, tmap, flag) stmts = 
  match stmts with
  | Ast.Qnil -> (map, tmap, flag)
  | Ast.Qcons (s, ss) -> mapstmts (mapstmt (map, tmap, flag) s) ss

let mapmod (map, flag) m =  
  match m with 
  | Ast.FInmod (_, pl, sl) -> let (map0, tmap0, flag0) = List.fold_left mapport (initmap_s, initmap_s, 0) pl in
                              mapstmts (map0, tmap0, flag0) sl 
  | _ -> (map, initmap_s, flag)

(*transast*)

let trans_fgtyp ty = 
  match ty with
  | Ast.Fuint s -> Env.Fuint s
  | Ast.Fsint s -> Env.Fsint s
  | Ast.Fuint_implicit s -> Env.Fuint_implicit s
  | Ast.Fsint_implicit s -> Env.Fsint_implicit s
  | Ast.Fclock -> Env.Fclock
  | Ast.Freset -> Env.Freset
  | Ast.Fasyncreset -> Env.Fasyncreset

let trans_flip f = 
  match f with
  | Ast.Flipped -> HiEnv.Flipped
  | Ast.Nflip -> HiEnv.Nflip

let trans_ucast a_ucast = 
  match a_ucast with
  | Ast.AsUInt -> Firrtl.AsUInt
  | Ast.AsSInt -> Firrtl.AsSInt
  | Ast.AsClock -> Firrtl.AsClock
  | Ast.AsAsync -> Firrtl.AsAsync

let trans_eunop a_eunop = 
  match a_eunop with
  | Ast.Upad s -> Firrtl.Upad s
  | Ast.Ushl s -> Firrtl.Ushl s
  | Ast.Ushr s -> Firrtl.Ushr s
  | Ast.Ucvt -> Firrtl.Ucvt
  | Ast.Uneg -> Firrtl.Uneg
  | Ast.Unot -> Firrtl.Unot
  | Ast.Uandr -> Firrtl.Uandr
  | Ast.Uorr -> Firrtl.Uorr
  | Ast.Uxorr -> Firrtl.Uxorr
  | Ast.Uextr (s1, s2) -> Firrtl.Uextr (s1, s2)
  | Ast.Uhead s -> Firrtl.Uhead s
  | Ast.Utail s -> Firrtl.Utail s

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

let rec trans_ftype v ty map = 
  match ty with
  | Ast.Gtyp gt -> HiEnv.Gtyp (trans_fgtyp gt)
  | Ast.Atyp (atyp, n) -> HiEnv.Atyp (trans_ftype (v^"[0]") atyp map, n)
  | Ast.Btyp btyp -> HiEnv.Btyp (trans_btyp v btyp map)

and trans_btyp v btyp map =
  match btyp with
  | Ast.Fnil -> HiEnv.Fnil
  | Ast.Fflips (fv, fl, ft, ff) -> HiEnv.Fflips (Obj.magic (StringMap.find (v^"."^fv) map), trans_flip fl, trans_ftype (v^"."^fv) ft map, (trans_btyp v ff map))

let rec find_nat4v ref =
  match ref with
  | Ast.Eid v -> v
  | Ast.Esubfield (ref1, v) -> (find_nat4v ref1)^"."^v
  | Ast.Esubindex (ref1, n) -> (find_nat4v ref1)^"["^(Int.to_string n)^"]"
  | Ast.Esubaccess (ref1, _) -> (find_nat4v ref1)

(*let rec trans_ref ref map = 
  match ref with
  | Ast.Eid v -> HiFirrtl.Eid (Obj.magic (StringMap.find v map))
  | Ast.Esubfield (r, _) -> HiFirrtl.Esubfield (trans_ref r map, Obj.magic (StringMap.find (find_nat4v ref) map))
  | Ast.Esubindex (r, n) -> HiFirrtl.Esubindex (trans_ref r map, n)
  | Ast.Esubaccess (r, _) -> (trans_ref r map)*)

let rec trans_expr e map = 
  match e with
  | Ast.Econst (ty, s) -> HiFirrtl.Econst (trans_fgtyp ty, bits_of_z (Env.sizeof_fgtyp (trans_fgtyp ty)) s)
  | Ast.Eref v -> HiFirrtl.Eref (HiFirrtl.Eid (Obj.magic (StringMap.find (find_nat4v v) map)))
  | Ast.Eprim_unop (op, e1) -> HiFirrtl.Eprim_unop(trans_eunop op, trans_expr e1 map)
  | Ast.Eprim_binop (bop, e1, e2) -> HiFirrtl.Eprim_binop(trans_ebinop bop, trans_expr e1 map, trans_expr e2 map)
  | Ast.Emux (e1,e2,e3) -> HiFirrtl.Emux(trans_expr e1 map, trans_expr e2 map, trans_expr e3 map)
  (*| Ast.Evalidif (e1,e2) -> HiFirrtl.Evalidif(trans_expr e1 map,trans_expr e2 map)*)
  | Ast.Ecast (s, e) -> HiFirrtl.Ecast(trans_ucast s, trans_expr e map)
  
let trans_ruw r = 
  match r with
  | Ast.Coq_old -> Firrtl.Coq_old
  | Ast.Coq_new -> Firrtl.Coq_new
  | Ast.Coq_undefined -> Firrtl.Coq_undefined

let trans_rst rst map = 
  match rst with
  | Ast.NRst -> HiFirrtl.NRst
  | Ast.Rst (e1, e2) -> HiFirrtl.Rst(trans_expr e1 map, trans_expr e2 map)

let rec trans_stmt s map = 
  match s with
  | Ast.Sskip -> HiFirrtl.Sskip
  | Ast.Swire (v, ty) -> HiFirrtl.Swire(Obj.magic (StringMap.find v map), trans_ftype v ty map)
  | Ast.Sfcnct (ref, e) -> HiFirrtl.Sfcnct(HiFirrtl.Eid (Obj.magic (StringMap.find (find_nat4v ref) map)), trans_expr e map)
  | Ast.Sinvalid ref -> HiFirrtl.Sinvalid (HiFirrtl.Eid (Obj.magic (StringMap.find (find_nat4v ref) map)))
  | Ast.Snode (v, e) -> HiFirrtl.Snode(Obj.magic (StringMap.find v map), trans_expr e map)
  | Ast.Sreg (v, r) -> HiFirrtl.Sreg (Obj.magic (StringMap.find v map), HiFP.mk_hfreg (trans_ftype v r.coq_type map) (trans_expr r.clock map) (trans_rst r.reset map))
  | Ast.Smem _ -> HiFirrtl.Sskip
  | Ast.Sinst _ -> HiFirrtl.Sskip
  | Ast.Swhen (c, s1, s2) -> HiFirrtl.Swhen (trans_expr c map, trans_stmts s1 map, trans_stmts s2 map)

and trans_stmts ss map =
  match ss with
  | Ast.Qnil -> HiFirrtl.Qnil
  | Ast.Qcons (s, st) -> HiFirrtl.Qcons (trans_stmt s map, trans_stmts st map)

let trans_port p map = 
  match p with
  | Ast.Finput (v, ty) -> HiFirrtl.Finput(Obj.magic (StringMap.find v map), trans_ftype v ty map)
  | Ast.Foutput (v, ty) -> HiFirrtl.Foutput(Obj.magic (StringMap.find v map), trans_ftype v ty map)

let trans_mod m map flag = 
  match m with
  | Ast.FInmod (_, pl, sl) -> HiFirrtl.FInmod(Obj.magic (flag, 0), List.map (fun a -> trans_port a map) pl, trans_stmts sl map)
  | Ast.FExmod (_, pl, sl) -> HiFirrtl.FExmod(Obj.magic (flag, 0), List.map (fun a -> trans_port a map) pl, trans_stmts sl map)

(*let trans_cir cir map flag = 
  match cir with
  | Ast.Fcircuit (_, ml) -> HiFirrtl.Fcircuit ((Obj.magic flag), (trans_mod (List.hd ml) map flag) :: [])*)

let hiparse f =
  let lexbuf = Lexing.from_channel (open_in f) in
  FirrtlParser.file FirrtlLexer.token lexbuf

(*let rec print_ref_e e =
  match e with
  | Ast.Eref v -> (find_nat4v v) :: []
  | Ast.Eprim_unop (_, e1) -> (print_ref_e e1)
  | Ast.Eprim_binop (_, e1, e2) -> List.append (print_ref_e e1) (print_ref_e e2)
  | Ast.Emux (e1,e2,e3) -> List.append (print_ref_e e1) (List.append (print_ref_e e2) (print_ref_e e3))
  | Ast.Evalidif (e1,e2) -> List.append (print_ref_e e1) (print_ref_e e2)
  | Ast.Ecast (_, e) -> print_ref_e e
  | _ -> []

let rec print_ref_s s =
  match s with
  | Ast.Sfcnct (ref, e) -> (find_nat4v ref) :: (print_ref_e e)
  | Ast.Sinvalid ref -> (find_nat4v ref) :: []
  | Ast.Snode (v, e) -> v :: (print_ref_e e)
  | _ -> []
and print_ref_ss ss =
  match ss with
  | Ast.Qnil -> []
  | Ast.Qcons (s, st) -> List.append (print_ref_s s) (print_ref_ss st)



let rec print_fd v ty map = 
  match ty with
  | Ast.Gtyp _ -> []
  | Ast.Atyp (atyp, _) -> (v^"[0]") :: (print_fd (v^"[0]") atyp map)
  | Ast.Btyp btyp -> v :: (print_fd_b v btyp map)

and print_fd_b v btyp map =
  match btyp with
  | Ast.Fnil -> []
  | Ast.Fflips (fv, _, ft, ff) -> (v^"."^fv) :: (List.append (print_fd (v^"."^fv) ft map) (print_fd_b v ff map))

let rec print_fd_p p map =
  match p with
  | Ast.Finput (v, ty) -> v :: (print_fd v ty map)
  | Ast.Foutput (v, ty) ->  v :: (print_fd v ty map)

and print_fd_pl pl map =
  match pl with
  | [] -> []
  | s :: st -> List.append (print_fd_p s map) (print_fd_pl st map)
*)

let pp_fgtyp_mlir gt =
  match gt with
  | Env.Fuint n -> printf "uint<%d>" n
  | Env.Fsint n -> printf "sint<%d>" n
  | Env.Fclock -> printf "clock"
  | Env.Fasyncreset -> printf "asyncreset"
  | Env.Fuint_implicit n -> printf "uint_implicit<%d>" n
  | Env.Fsint_implicit n -> printf "sint_implicit<%d>" n
  | Env.Freset -> printf "reset"

let pp_ftype_mlir ft = 
  match ft with
  | HiEnv.Gtyp gt -> pp_fgtyp_mlir gt; printf "\n"
  | HiEnv.Atyp _ -> printf "array type\n"
  | HiEnv.Btyp _ -> printf "bundle type\n"
  
let rec pp_expr e =
  match e with
  | HiFirrtl.Econst (ty, s) -> printf "(econst "; pp_fgtyp_mlir ty; printf " %d" (NBitsDef.to_nat s) ; printf"])"
  | Eref (Eid r) -> printf "(eref (%d, %d)" (fst (Obj.magic r)) (snd (Obj.magic r)); printf ")"
  | Eprim_unop (_, e1) -> printf "(eprim_unop "; pp_expr e1; printf ")"
  | Eprim_binop (_, e1, e2) -> printf "(eprim_binop "; pp_expr e1; printf " "; pp_expr e2; printf ")"
  | Emux (e1,e2,e3)  -> printf "(emux "; pp_expr e1; printf " "; pp_expr e2; printf " "; pp_expr e3; printf " "; printf ")"
  (*| Evalidif (e1,e2)  -> printf "(evalidif "; pp_expr e1; printf " "; pp_expr e2; printf ")"*)
  | Ecast (_, e) -> printf "(ecast "; printf " "; pp_expr e; printf ")";
  | _ -> printf "wrong id"

let hif_ast = hiparse "./demo/chiselhi/FormalSimple.fir"

(*let () =
  match hif_ast with
  | Ast.Fcircuit (_, ml) -> let (map0, tmap0, flag) = mapmod (initmap_s, 0) (List.hd ml) in 
    StringMap.iter (fun key (value1, value2) -> (printf "%s: (%d, %d)" key value1 value2); printf "\n") map0;
    StringMap.iter (fun key value -> (printf "%s: " key; Ast.pp_type stdout value); printf "\n") tmap0;
  (*let _ = trans_cir hif_ast map0 flag in*)
    let fmod = trans_mod (List.hd ml) map0 flag in
    (*match InferWidth_rewritten.coq_InferWidths_stage1 fmod with*)
    match fmod with
    | FInmod (_, ps, ss) -> (match InferWidth_rewritten.stmts_tmap ((InferWidth_rewritten.ports_tmap ps), CEP.empty) ss with
                          | Some p -> 
                            let (tmap', var2exprs) = p in (*match CEP.find (Obj.magic (1,0)) tmap' with
                            | Some _ -> printf "1"
                            | None -> printf "2"*)
                            (match InferWidth_rewritten.lsreg_stmts ss with
                             | Some expli_reg ->
                              printf "expli_reg: "; List.iter (fun r -> printf "(%d, %d) " (fst (Obj.magic r)) (snd (Obj.magic r))) expli_reg; printf "\n";
                              (*(match CEP.find (Obj.magic (1,0)) tmap' with
                              | Some ft -> pp_ftype_mlir ft; (match CEP.find (Obj.magic (0,0)) tmap' with
                                          | Some ft0 -> pp_ftype_mlir ft0; (match CEP.find (Obj.magic (1,0)) var2exprs with
                                                      | Some el -> (*List.iter (fun e -> pp_expr e; printf "\n") el (* 都是对的 *);*)
                                                                   (*(match InferWidth_rewritten.drawel (Obj.magic (1,0)) el tmap' InferWidth_rewritten.emptyg [] with
                                                                   | Some (newg, vs) -> printf "(1,0) -> "; List.iter (fun v -> printf "(%d, %d) " (fst (Obj.magic v)) (snd (Obj.magic v))) (newg (Obj.magic (1,0)));
                                                                                        printf "\nvertices : "; List.iter (fun v -> printf "(%d, %d) " (fst (Obj.magic v)) (snd (Obj.magic v))) vs;
                                                                   | _ -> printf "6";)*)
                                                      | _ -> printf "2")
                                          | _ -> printf "5")
                              | _ -> printf "0");*)
                              printf "var2expr : "; List.iter (fun ((v1, v2), e) -> printf "(%d, %d) <= " (Obj.magic v1) (Obj.magic v2); List.iter pp_expr e; printf "\n") (Obj.magic CEP.elements var2exprs);
                              (*let _ = CEP.fold (fun v el n -> printf "(%d, %d) <= " (fst (Obj.magic v)) (snd (Obj.magic v)); List.iter pp_expr el; printf "\n"; n+1) var2exprs 0 in printf ""*)
                              
                              (match InferWidth_rewritten.drawg (Obj.magic CEP.elements var2exprs) expli_reg
                              InferWidth_rewritten.emptyg [] with
                               | Some p0 ->
                                let (theg, vertices) = p0 in
                                printf "(3,0) -> " ;List.iter (fun v -> printf "(%d, %d) " (fst (Obj.magic v)) (snd (Obj.magic v))) (theg (Obj.magic (3,0))); printf "\n";
                                printf "(7,0) -> " ;List.iter (fun v -> printf "(%d, %d) " (fst (Obj.magic v)) (snd (Obj.magic v))) (theg (Obj.magic (7,0))); printf "\nvertices : "; 
                                (*match InferWidth_rewritten.drawreg expli_reg var2exprs InferWidth_rewritten.emptyg [] with
                                | Some p1 ->
                                  let (regg, _) = p1 in
                                  printf "(6,0) -> " ;List.iter (fun v -> printf "(%d, %d) " (fst (Obj.magic v)) (snd (Obj.magic v))) (regg (Obj.magic (3,0))); printf "\n";
                                  printf "(7,0) -> " ;List.iter (fun v -> printf "(%d, %d) " (fst (Obj.magic v)) (snd (Obj.magic v))) (regg (Obj.magic (4,0))); printf "\nvertices : "; 
                                | _ -> printf "5"*)
                                (match TopoSort.TopoSort.topo_sort ProdVarOrder.coq_T vertices theg with
                                 | TopoSort.TopoSort.Sorted sort -> printf "sorted : " ;List.iter (fun v -> printf "(%d, %d) " (fst (Obj.magic v)) (snd (Obj.magic v))) sort; printf "\n"; 
                                                                    (match InferWidth_rewritten.coq_InferWidths_fun sort var2exprs tmap' with 
                                                                    | Some tmap -> (match CEP.find (Obj.magic (3, 0)) tmap with
                                                                                  | Some t -> pp_ftype_mlir t; (*match InferWidth_rewritten.coq_InferWidths_stage1 fmod with
                                                                                                              | Some tmap' -> (match CEP.find (Obj.magic (7, 0)) tmap' with
                                                                                                                              | Some t' -> pp_ftype_mlir t'
                                                                                                                              | _ -> printf "11")
                                                                                                              | _ -> printf "12"*)
                                                                                  | _ -> printf "1")
                                                                    | _ -> printf "6")
                                 | _ -> printf "5")
                               | None -> printf "4")
                             | None -> printf "2")
                          | None -> printf "0"); (match InferWidth_rewritten.coq_InferWidths_m fmod with
                                                | Some p ->
                                                  let (h, tmap) = p in
                                                  (match h with
                                                   | FInmod (v, ps, ss) ->
                                                     (match ExpandWhens_rewritten.coq_ExpandWhens_fun
                                                              (ExpandConnects_new.expandconnects_fmodule (FInmod (v, ps, ss)) tmap) with
                                                      | Some _ -> printf "10"
                                                      | None -> printf "12")
                                                   | FExmod (_, _, _) -> printf "13")
                                                | _ -> printf "11")
    | _ -> printf "3"
    *)