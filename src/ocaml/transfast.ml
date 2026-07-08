open Hifirrtl_lang
open Extraction

let trans_port p map tmap = 
  match p with
  | HiFirrtl.Finput (v, HiEnv.Gtyp ty) -> let nv = Pair2string.pair_to_string (Obj.magic v) map tmap in
                              let nty = Pair2string.fgtyp_pair_to_string ty in
                              Ast.Finput (nv, Ast.Gtyp nty)
  | HiFirrtl.Foutput (v, HiEnv.Gtyp ty) -> let nv = Pair2string.pair_to_string (Obj.magic v) map tmap in
                              let nty = Pair2string.fgtyp_pair_to_string ty in
                              Ast.Foutput (nv, Ast.Gtyp nty)

let trans_rst rst map tmap = 
  match rst with
  | HiFirrtl.NRst -> Ast.NRst
  | HiFirrtl.Rst (e1, e2) -> Ast.Rst(Pair2string.expr_pair_to_string e1 map tmap, Pair2string.expr_pair_to_string e2 map tmap)

let rec trans_stmt s map tmap res = 
  match s with
  | HiFirrtl.Swire (v, HiEnv.Gtyp ty) -> let nv = Pair2string.pair_to_string (Obj.magic v) map tmap in
                              let nty = Pair2string.fgtyp_pair_to_string ty in
                              let ns = Ast.Swire (nv, Ast.Gtyp nty) in
                              Ast.Qcons (ns, res)
  | HiFirrtl.Sfcnct (Eid v, e) -> let nv = Pair2string.pair_to_string (Obj.magic v) map tmap in
                              let ne = Pair2string.expr_pair_to_string e map tmap in
                              let ns = Ast.Sfcnct (Eid nv, ne) in
                              Ast.Qcons (ns, res)
  | HiFirrtl.Sinvalid (Eid v) -> let nv = Pair2string.pair_to_string (Obj.magic v) map tmap in
                              let ns = Ast.Sinvalid (Eid nv) in
                              Ast.Qcons (ns, res)
  | HiFirrtl.Snode (v, e) -> let nv = Pair2string.pair_to_string (Obj.magic v) map tmap in
                              let ne = Pair2string.expr_pair_to_string e map tmap in
                              let ns = Ast.Snode (nv, ne) in
                              Ast.Qcons (ns, res)
  | HiFirrtl.Sreg (v, r) -> let nv = Pair2string.pair_to_string (Obj.magic v) map tmap in
                              (match r.coq_type with
                              | HiEnv.Gtyp ty ->
                                let nty = Pair2string.fgtyp_pair_to_string ty in
                                let nclock = Pair2string.expr_pair_to_string r.clock map tmap in
                                let nrst = trans_rst r.reset map tmap in
                                let ns = Ast.Sreg (nv, Ast.mk_freg_r (Ast.Gtyp nty) nclock nrst) in
                                Ast.Qcons (ns, res)
                              | _ -> res)
  | HiFirrtl.Sinst (v, modv) -> let nv = Pair2string.pair_to_string (Obj.magic v) map tmap in
                              let nmodv = Pair2string.pair_to_string (Obj.magic modv) map tmap in
                              let ns = Ast.Sinst (nv, nmodv) in
                              Ast.Qcons (ns, res)
  | HiFirrtl.Swhen (c, s1, s2) -> let nc = Pair2string.expr_pair_to_string c map tmap in
                              let ns1 = trans_stmts s1 map tmap Ast.Qnil in 
                              let ns2 = trans_stmts s2 map tmap Ast.Qnil in 
                              let ns = Ast.Swhen (nc, ns1, ns2) in
                              Ast.Qcons (ns, res)
  | _ -> res 

and trans_stmts ss map tmap res =
  match ss with
  | HiFirrtl.Qnil -> res
  | HiFirrtl.Qcons (s, st) -> trans_stmts st map tmap (trans_stmt s map tmap res)

let rec revstmts sts res = 
  match sts with 
  | Ast.Qnil -> res
  | Ast.Qcons (h, tl) -> revstmts tl (revstmt h res)
    
and revstmt st res =
  match st with
  | Ast.Swhen (c, s1, s2) -> Ast.Qcons ((Ast.Swhen (c, revstmts s1 Ast.Qnil, revstmts s2 Ast.Qnil)), res)
  | _ -> Ast.Qcons (st, res)

let trans_mod m modmap map = 
  match m with
  | HiFirrtl.FInmod (mv, pl, sl) -> 
    let mv_string = Transhiast.IntMap.find (fst (Obj.magic mv)) modmap in
    let ((map0, map1), tmap) = Transhiast.StringMap.find mv_string map in
    let newports = List.map (fun a -> trans_port a map1 tmap) pl in
    let newstmts = trans_stmts sl map1 tmap Ast.Qnil in
    Ast.FInmod(mv_string, newports, revstmts newstmts Ast.Qnil)
  | HiFirrtl.FExmod (mv, _, _) -> 
    let mv_string = Transhiast.IntMap.find (fst (Obj.magic mv)) modmap in
    Ast.FExmod(mv_string,[],Ast.Qnil)

let rec trans_modl ml modmap map =
  match ml with
  | [] -> []
  | hd :: tl -> 
    let m = trans_mod hd modmap map in
    m :: (trans_modl tl modmap map)

let trans_cir cir modmap map = 
  match cir with
  | HiFirrtl.Fcircuit (cv, ml) -> 
    Ast.Fcircuit (Transhiast.IntMap.find (fst (Obj.magic cv)) modmap, 
    (trans_modl ml modmap map))