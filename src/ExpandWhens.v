From Coq Require Import FunInd FMaps FMapAVL OrderedType ZArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat ssrint eqtype seq fintype fingraph.
From simplssrlib Require Import Types SsrOrder FSets FMaps Tactics Var Store.
From firrtl Require Import Env HiEnv HiFirrtl Semantics.

(* a type to indicate connects *)
Inductive def_expr : Type :=
  | D_undefined (* declared but not connected, no "is invalid" statement *)
  | D_invalidated (* declared but not connected, there is a "is invalid" statement *)
  | D_fexpr : HiFP.hfexpr -> def_expr (* declared and connected *)
  .

(* equality of def_expr is decidable [because equality of hfexpr is decidable] *)
Lemma def_expr_eq_dec : forall {x y : def_expr}, {x = y} + {x <> y}.
  Proof.
  decide equality.
  apply hfexpr_eq_dec.
Qed.

Definition def_expr_eqn (x y : def_expr) : bool :=
  match x, y with
  | D_undefined, D_undefined => true
  | D_invalidated, D_invalidated => true
  | D_fexpr expr1, D_fexpr expr2 => expr1 == expr2
  | _, _ => false
  end.

Lemma def_expr_eqP : Equality.axiom def_expr_eqn.
Proof.
  unfold Equality.axiom, def_expr_eqn.
  intros ; induction x, y ; try (apply ReflectF ; discriminate) ; try (apply ReflectT ; reflexivity).
  case Eq: (h == h0).
  all: move /hfexpr_eqP : Eq => Eq.
  apply ReflectT ; replace h0 with h ; reflexivity.
  apply ReflectF ; injection ; apply Eq.
Qed.

Canonical def_expr_eqMixin := EqMixin def_expr_eqP.
Canonical def_expr_eqType := Eval hnf in EqType def_expr def_expr_eqMixin.

Definition merge_expr (c : HiFP.hfexpr) (true_expr : def_expr) (false_expr : def_expr) : def_expr := 
  match true_expr, false_expr with
  | D_fexpr t, D_fexpr f => if t == f then true_expr 
                                      else (D_fexpr (Emux c t f)) 
  | D_invalidated, D_fexpr f => false_expr
  | D_undefined, _ => D_undefined
  | _, D_undefined => D_undefined
  | _, D_invalidated => true_expr
  end.

Definition combine_true_connections cond big small : PVM.t def_expr :=
  PVM.fold (fun k v acc =>
    match PVM.find k big with
    | None => PVM.add k v acc               
    | Some v' => PVM.add k (merge_expr cond v v') acc
    end
  ) small big.

Definition combine_false_connections cond big small : PVM.t def_expr :=
  PVM.fold (fun k v acc =>
    match PVM.find k big with
    | None => PVM.add k v acc               
    | Some v' => PVM.add k (merge_expr cond v' v) acc
    end
  ) small big.

Definition combine_branches cond true_conn_map false_conn_map old_conn_map : PVM.t def_expr :=
  let combined := PVM.fold (fun k v acc =>
    match PVM.find k false_conn_map, PVM.find k old_conn_map with
    | Some v', _ => PVM.add k (merge_expr cond v v') acc
    | None, Some v' => PVM.add k (merge_expr cond v v') acc     
    | None, None => PVM.add k v acc     
    end
  ) true_conn_map (PVM.empty def_expr) in
  PVM.fold (fun k v acc =>
    match PVM.find k true_conn_map, PVM.find k old_conn_map with
    | None, Some v' => PVM.add k (merge_expr cond v' v) acc     
    | _, _ => acc
    end
  ) false_conn_map combined.

Fixpoint connectConnects_funs
(* split a statement sequence (possibly containing when
   statements) into a connection map.  The output does not contain when statements. *)
(ss           : HiFP.hfstmt_seq)   (* sequence of statements being translated *)
(old_conn_map : PVM.t def_expr)    (* connections made by earlier statements in the sequence (used for recursion) *)
(scope_conn_map : PVM.t def_expr)
(hseq_result : HiFP.hfstmt_seq)
(tmap : PVM.t (fgtyp * fcomponent))
:   option ((PVM.t def_expr) * (PVM.t def_expr) * HiFP.hfstmt_seq)
(* old_conn_map, extended with the connection statements in ss *)
:=  match ss with
| Qnil => Some (old_conn_map, scope_conn_map, hseq_result)
| Qcons s ss =>
    match connectConnect_fun s old_conn_map scope_conn_map hseq_result tmap with
    | Some (temp_conn_map, temp_scope_conn_map, hseq_result0) =>
        connectConnects_funs ss temp_conn_map temp_scope_conn_map hseq_result0 tmap
    | None => None
    end
end
with connectConnect_fun
(* split a single statement (possibly consisting of a when
   statement) into a connection map.  The output does not contain when statements. *)
(s            : HiFP.hfstmt)       (* a single statement being translated *)
(old_conn_map : PVM.t def_expr)    (* connections made by earlier statements in the sequence (used for recursion) *)
(scope_conn_map : PVM.t def_expr)
(hseq_result : HiFP.hfstmt_seq)
(tmap : PVM.t (fgtyp * fcomponent))
:   option ((PVM.t def_expr) * (PVM.t def_expr) * HiFP.hfstmt_seq)
:=  match s with
| Sskip => Some (old_conn_map, scope_conn_map, hseq_result)
| Sreg var reg =>
    match type reg with
    | Gtyp gt => Some (PVM.add var (D_fexpr (Eref (Eid var))) old_conn_map, 
      PVM.add var (D_fexpr (Eref (Eid var))) scope_conn_map, Qcons s hseq_result)
    | _ => None
    end
| Sfcnct (Eid var) expr => Some (PVM.add var (D_fexpr expr) old_conn_map, 
  PVM.add var (D_fexpr expr) scope_conn_map, hseq_result)
| Sfcnct _ expr => None
| Sinvalid (Eid var) => match PVM.find var tmap with
  | Some (gt, _) => Some (PVM.add var D_invalidated old_conn_map, 
    PVM.add var D_invalidated scope_conn_map, hseq_result)
  | _ => None
  end
| Sinvalid _ => None
| Swhen cond ss_true ss_false =>
    match connectConnects_funs ss_true old_conn_map (PVM.empty def_expr) hseq_result tmap with
    | Some (_, true_conn_map, hseq_result0) =>
        match connectConnects_funs ss_false old_conn_map (PVM.empty def_expr) hseq_result0 tmap with
        | Some (_, false_conn_map, hseq_result1) =>
            let combined := combine_branches cond true_conn_map false_conn_map old_conn_map in 
            let new_scope := PVM.fold (fun k v acc => PVM.add k v acc) combined scope_conn_map in
            Some (PVM.fold (fun k v acc => PVM.add k v acc) combined old_conn_map, new_scope, hseq_result1)
        | _ => None
        end
    | _ => None
    end
| _ => Some (old_conn_map, scope_conn_map, Qcons s hseq_result) (* wire, mem, inst, node *)
end.

Definition convert_to_connect_stmt
    (* convert one entry in a map of connections to a connect statement,
       helper function for PVM.fold *)
    (v : PVM.key) (* key of the connection *)
    (d : def_expr) (* value of the connection *)
    (old_ss : option HiFP.hfstmt_seq) (* old sequence of connect statements *)
:   option HiFP.hfstmt_seq (* returns old_ss, extended with assigning d to v *)
:=  match old_ss, d with
    | Some old_ss', D_invalidated => Some (Qcons (Sinvalid (Eid v)) old_ss')
    | Some old_ss', D_fexpr e => Some (Qcons (Sfcnct (Eid v) e) old_ss')
    | _, D_undefined => None
    | None, _ => None
    end.

Definition convert_to_connect_stmts
    (* converts a map of connections to connect statements *)
    (conn_map : PVM.t def_expr) (* map that needs to be converted *)
:   option HiFP.hfstmt_seq
:=  PVM.fold convert_to_connect_stmt conn_map (Some (Qnil ProdVarOrder.T)).

Fixpoint ExpandWhens_fun
    (ml : list HiFP.hfmodule) (tmap : (PVM.t (PVM.t (fgtyp * fcomponent)))) 
    (fml : list HiFP.hfmodule) (conn_map : PVM.t (PVM.t def_expr))
:   option ((list HiFP.hfmodule) * (PVM.t (PVM.t def_expr))) 
:=  match ml with
    | nil => Some (fml, conn_map)
    | (FInmod mv pp ss) :: tl => match PVM.find mv tmap with
        | Some tmap' => match connectConnects_funs ss (PVM.empty def_expr) (PVM.empty def_expr) HiFP.qnil tmap' with
            | Some (conn_map', _, list1) =>
                match convert_to_connect_stmts conn_map' with
                | Some list2 =>
                  let combined := Qcatrev list1 list2 in
                  let fm := FInmod mv pp combined in
                  ExpandWhens_fun tl tmap (fm :: fml) (PVM.add mv conn_map' conn_map)
                | None => None
                end
            | None => None
            end
        | _ => None
        end
    | m :: tl => ExpandWhens_fun tl tmap (m :: fml) conn_map
    end.

Fixpoint addplaswire (instv : VarOrder.t) (offset : nat) (pl : seq HiFP.hfport) (tmap : PVM.t (fgtyp * fcomponent)) (vl : list ProdVarOrder.t) : option ((PVM.t (fgtyp * fcomponent)) * (list ProdVarOrder.t)) :=
  match pl with
  | nil => Some (tmap, vl)
  | Finput v (Gtyp t) :: tl => let pv := (instv, N.of_nat offset) in
      addplaswire instv (offset + 1) tl (PVM.add pv (t, Wire) tmap) (pv :: vl)
  | Foutput v (Gtyp t) :: tl => let pv := (instv, N.of_nat offset) in
      addplaswire instv (offset + 1) tl (PVM.add pv (t, Wire) tmap) (pv :: vl)
  | _ => None
  end.

(* functions used to record ftype and component type *)
Fixpoint stmts_tmap (modplmap : PVM.t (seq HiFP.hfport)) (tmap : PVM.t (fgtyp * fcomponent)) (vl : list ProdVarOrder.t) (ss : HiFP.hfstmt_seq): option ((PVM.t (fgtyp * fcomponent)) * (list ProdVarOrder.t)) :=
  match ss with
  | Qnil => Some (tmap, vl)
  | Qcons s ss' => match stmt_tmap modplmap tmap vl s with
      | Some (tmap', vl') => stmts_tmap modplmap tmap' vl' ss'
      | None => None
      end
  end
with stmt_tmap (modplmap : PVM.t (seq HiFP.hfport)) (tmap : PVM.t (fgtyp * fcomponent)) (vl : list ProdVarOrder.t) (s : HiFP.hfstmt) : option ((PVM.t (fgtyp * fcomponent)) * (list ProdVarOrder.t)) :=
  match s with
  | Sskip => Some (tmap, vl)
  | Sfcnct _ _ => Some (tmap, vl)
  | Sinvalid _ => Some (tmap, vl)
  | Smem v m => Some (tmap, vl) 
  | Sinst v mv => match PVM.find mv modplmap with
      | Some pl => addplaswire (fst v) 0 pl tmap vl
      | _ => None
      end
  | Swire v (Gtyp t) => match PVM.find v tmap with
      | None => Some (PVM.add v (t, Wire) tmap, v :: vl)
      | _ => None
      end
  | Swire v _ => None
  | Sreg v reg => match PVM.find v tmap, Sem_HiFP.type_of_hfexpr (clock reg) tmap, type reg with
      | None, Some _, Gtyp gt => Some (PVM.add v (gt, Register) tmap, v :: vl)
      | _, _, _ => None
      end
  | Snode v expr => match PVM.find v tmap, Sem_HiFP.type_of_hfexpr expr tmap with
                  | None, Some ft => Some (PVM.add v (ft, Node) tmap, vl)
                  | _, _ => None
                  end
  | Swhen _ ss_true ss_false =>
      match stmts_tmap modplmap tmap vl ss_true with
      | Some (tmap_true, vl_true) => stmts_tmap modplmap tmap_true vl_true ss_false 
      | _ => None
      end
  end.

Fixpoint modules_tmap (modplmap : PVM.t (seq HiFP.hfport)) (tmap : PVM.t (PVM.t (fgtyp * fcomponent))) 
  (whitelist_map : PVM.t (list ProdVarOrder.t)) (ml : seq HiFP.hfmodule) : option ((PVM.t (PVM.t (fgtyp * fcomponent))) * (PVM.t (list ProdVarOrder.t))):=
  match ml with
  | nil => Some (tmap, whitelist_map)
  | (FInmod mv ps ss) :: tl => match Sem_HiFP.ports_tmap (PVM.empty (fgtyp * fcomponent)) ps with
              | Some pmap => match stmts_tmap modplmap pmap (fst (List.split (PVM.elements pmap))) ss with
                  | Some (tmap', whitelist) => modules_tmap modplmap (PVM.add mv tmap' tmap) (PVM.add mv whitelist whitelist_map) tl
                  | None => None
                  end
              | None => None
              end 
  | _ :: tl => modules_tmap modplmap tmap whitelist_map tl
  end.

Definition circuit_tmap (c : HiFP.hfcircuit) : option ((PVM.t (PVM.t (fgtyp * fcomponent))) * (PVM.t (list ProdVarOrder.t))) :=
  match c with
  | Fcircuit v ml => let modplmap := List.fold_left (fun acc m => 
      match m with
      | FInmod mv ps _ => PVM.add mv ps acc
      | FExmod mv ps _ => PVM.add mv ps acc
      end) ml (PVM.empty (seq HiFP.hfport)) in
    modules_tmap modplmap (PVM.empty (PVM.t (fgtyp * fcomponent))) (PVM.empty (list ProdVarOrder.t)) ml
  end.

Fixpoint ss_add_node_in_cm (ss : HiFP.hfstmt_seq) (mod_cm : PVM.t def_expr) : PVM.t def_expr :=
  match ss with
  | Qnil => mod_cm
  | Qcons (Snode v expr) ss' => ss_add_node_in_cm ss' (PVM.add v (D_fexpr expr) mod_cm)
  | Qcons (Swhen _ ss_true ss_false) ss' => ss_add_node_in_cm ss' (ss_add_node_in_cm ss_false (ss_add_node_in_cm ss_true mod_cm))
  | Qcons _ ss' => ss_add_node_in_cm ss' mod_cm
  end.

Fixpoint modules_add_node_in_cm (ml : seq HiFP.hfmodule) (conn_map : PVM.t (PVM.t def_expr)) : PVM.t (PVM.t def_expr) :=
  match ml with
  | nil => conn_map
  | (FInmod mv ps ss) :: tl => match PVM.find mv conn_map with
                              | Some mod_cm => modules_add_node_in_cm tl (PVM.add mv (ss_add_node_in_cm ss mod_cm) conn_map)
                              | None => modules_add_node_in_cm tl conn_map
                              end
  | _ :: tl => modules_add_node_in_cm tl conn_map
  end.

Definition expandWhens (c : HiFP.hfcircuit) : option (HiFP.hfcircuit * (PVM.t (PVM.t def_expr)) * (PVM.t (list ProdVarOrder.t))) :=
  match c, circuit_tmap c with
  | Fcircuit v ml, Some (tmap, vl_map) => match ExpandWhens_fun ml tmap nil (PVM.empty (PVM.t def_expr)) with
    | Some (fml, conn_map) => let conn_map' := modules_add_node_in_cm ml conn_map in
                              Some (Fcircuit v (List.rev fml), conn_map', vl_map)
    | _ => None
    end
  | _, _ => None
  end.
