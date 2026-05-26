From Coq Require Import FunInd FMaps FMapAVL OrderedType ZArith Lia.
From nbits Require Import NBitsDef.
From mathcomp Require Import ssreflect ssrbool ssrnat ssrint eqtype seq fintype fingraph.
From simplssrlib Require Import Types SsrOrder FSets FMaps Tactics Var Store.
From firrtl Require Import Firrtl Env HiEnv HiFirrtl Semantics.

Fixpoint pl2btyp (pl : seq HiF.hfport) : ffield := 
  match pl with
  | nil => Fnil
  | Finput v t :: tl => Fflips v Nflip t (pl2btyp tl)
  | Foutput v t :: tl => Fflips v Flipped t (pl2btyp tl)
  end.

(* functions used to record ftype and component type *)
Fixpoint stmts_tmap (modplmap : VM.t (seq HiF.hfport)) (tmap : VM.t (ftype * fcomponent)) (ss : HiF.hfstmt_seq): option (VM.t (ftype * fcomponent)) :=
  match ss with
  | Qnil => Some tmap
  | Qcons s ss' => match stmt_tmap modplmap tmap s with
      | Some tmap' => stmts_tmap modplmap tmap' ss'
      | None => None
      end
  end
with stmt_tmap (modplmap : VM.t (seq HiF.hfport)) (tmap : VM.t (ftype * fcomponent)) (s : HiF.hfstmt) : option (VM.t (ftype * fcomponent)) :=
  match s with
  | Sskip => Some tmap
  | Sfcnct _ _ => Some tmap
  | Sinvalid _ => Some tmap
  | Smem v m => Some (VM.add v (data_type m, Memory) tmap)
  | Sinst v mv => match VM.find mv modplmap with
      | Some pl => let t := Btyp (pl2btyp pl) in
                  Some (VM.add v (t, Instanceof) tmap)
      | _ => None
      end
  | Swire v t => match VM.find v tmap with
      | None => Some (VM.add v (t, Wire) tmap)
      | _ => None
      end
  | Sreg v reg => match VM.find v tmap, Sem_HiF.type_of_hfexpr (clock reg) tmap with
      | None, Some _ => Some (VM.add v ((type reg), Register) tmap)
      | _, _ => None
      end
  | Snode v expr => match VM.find v tmap, Sem_HiF.type_of_hfexpr expr tmap with
                  | None, Some ft => Some (VM.add v (ft, Node) tmap)
                  | _, _ => None
                  end
  | Swhen cond ss_true ss_false =>
      match Sem_HiF.type_of_hfexpr cond tmap, stmts_tmap modplmap tmap ss_true with
      | Some (Gtyp _), Some tmap_true => stmts_tmap modplmap tmap_true ss_false 
      | _, _ => None
      end
  end.

Fixpoint modules_tmap (modplmap : VM.t (seq HiF.hfport)) (tmap : VM.t (VM.t (ftype * fcomponent))) (ml : seq HiF.hfmodule) : option (VM.t (VM.t (ftype * fcomponent))) :=
  match ml with
  | nil => Some tmap
  | FInmod mv ps ss :: tl => match Sem_HiF.ports_tmap' (VM.empty (ftype * fcomponent)) ps with
              | Some pmap => match stmts_tmap modplmap pmap ss with
                  | Some tmap' => modules_tmap modplmap (VM.add mv tmap' tmap) tl
                  | None => None
                  end
              | None => None
              end 
  | _ :: tl => modules_tmap modplmap tmap tl
  end.

Definition circuit_tmap (c : HiF.hfcircuit) : option (VM.t (VM.t (ftype * fcomponent))) :=
  match c with
  | Fcircuit v ml => let modplmap := List.fold_left (fun acc m => 
      match m with
      | FInmod mv ps _ => VM.add mv ps acc
      | FExmod mv ps _ => VM.add mv ps acc
      end) ml (VM.empty (seq HiF.hfport)) in
    modules_tmap modplmap (VM.empty (VM.t (ftype * fcomponent))) ml
  end.

Fixpoint list_ref_subaccess (r : HiF.href) (tmap : VM.t (ftype * fcomponent)) : option (list HiF.href) :=
  match r with
  | Eid v => Some [::r]
  | Esubindex v i => match list_ref_subaccess v tmap with
                    | Some ref_list => Some (map (fun ref => Esubindex v i) ref_list)
                    | _ => None
                    end
  | Esubfield v f => match list_ref_subaccess v tmap with
                    | Some ref_list => Some (map (fun ref => Esubfield v f) ref_list)
                    | _ => None
                    end
  | Esubaccess v e => match Sem_HiF.type_of_ref v tmap, list_ref_subaccess v tmap with
                    | Some (Atyp _ n), Some ref_list =>
                      let fix aux ref m ls := match m with
                                          | m'.+1 => aux ref m' ((Esubindex ref m') :: ls)
                                          | 0 => ls
                                          end
                                  in
                      Some (flat_map (fun ref => aux ref n nil) ref_list)
                    | _, _ => None
                    end
  end.

Fixpoint generate_cond (r ref : HiF.href) (cond : option HiF.hfexpr) (tmap : VM.t (ftype * fcomponent)) : option HiF.hfexpr :=
  match r, ref with
  | Eid _, Eid _ => cond
  | Esubindex v0 _, Esubindex v1 _ => generate_cond v0 v1 cond tmap
  | Esubfield v0 _, Esubfield v1 _ => generate_cond v0 v1 cond tmap
  | Esubaccess v0 e, Esubindex v1 i => match cond, Sem_HiF.type_of_ref v1 tmap with
                    | Some c, Some (Atyp _ n) => let bv_length := Nat.log2 n + 1 in (* 假设n不为0 *)
                      let cond' := Some (Eprim_binop Band c (Eprim_binop (Bcomp Beq) e (HiF.econst (Fuint bv_length) (from_nat bv_length i)))) in
                      generate_cond v0 v1 cond' tmap
                    | None, Some (Atyp _ n) => let bv_length := Nat.log2 n + 1 in (* 假设n不为0 *)
                      let cond' := Some (Eprim_binop (Bcomp Beq) e (HiF.econst (Fuint bv_length) (from_nat bv_length i))) in
                      generate_cond v0 v1 cond' tmap
                    | _, _ => None
                    end
  | _, _ => None
  end.

Fixpoint preprocess_subaccess_ref (r : HiF.href) (ref_tl : list HiF.href) (e : HiF.hfexpr) (tmap : VM.t (ftype * fcomponent)) : option HiF.hfexpr :=
  match ref_tl with
  | nil => Some e 
  | hd :: tl => match generate_cond r hd None tmap with
                | Some cond => preprocess_subaccess_ref r tl (Emux cond (Eref hd) e) tmap
                | _ => None
                end
  end.

Fixpoint preprocess_subaccess_expr (e : HiF.hfexpr) (tmap : VM.t (ftype * fcomponent)) : option HiF.hfexpr :=
  match e with
  | Econst _ _ => Some e
  | Eref ref => match list_ref_subaccess ref tmap with
                | Some (ref_hd :: ref_tl) => preprocess_subaccess_ref ref ref_tl (Eref ref_hd) tmap
                | _ => None
                end
  | Ecast c e0 => match preprocess_subaccess_expr e0 tmap with
                | Some e' => Some (Ecast c e')
                | _ => None
                end
  | Eprim_unop op e0 => match preprocess_subaccess_expr e0 tmap with
                | Some e' => Some (Eprim_unop op e')
                | _ => None
                end
  | Eprim_binop op e0 e1 => match preprocess_subaccess_expr e0 tmap, preprocess_subaccess_expr e1 tmap with
                | Some e', Some e'' => Some (Eprim_binop op e' e'')
                | _, _ => None
                end
  | Emux c e0 e1 => match preprocess_subaccess_expr c tmap, preprocess_subaccess_expr e0 tmap, preprocess_subaccess_expr e1 tmap with
                | Some c', Some e', Some e'' => Some (Emux c' e' e'')
                | _, _, _ => None
                end
end.

Fixpoint preprocess_subaccess_stmt (s : HiF.hfstmt) (sts : HiF.hfstmt_seq) (tmap : VM.t (ftype * fcomponent)) : option HiF.hfstmt_seq :=
  match s with
  | Sskip 
  | Sinvalid _ 
  | Smem _ _
  | Sinst _ _
  | Swire _ _
  | Sreg _ _ => Some (Qcons s sts)
  | Snode v expr => match preprocess_subaccess_expr expr tmap with
                  | Some e => Some (Qcons (Snode v e) sts)
                  | _ => None
                  end
  | Sfcnct ref expr => match list_ref_subaccess ref tmap, preprocess_subaccess_expr expr tmap with
                  | Some ref_list, Some e => let fix aux ls acc := match ls with
                                          | nil => acc
                                          | hd :: tl => match generate_cond ref hd None tmap with
                                                  | Some cond => aux tl (Qcons (Sfcnct hd (Emux cond e (Eref hd))) acc)
                                                  | _ => acc
                                                  end
                                          end
                                  in Some (aux ref_list sts)
                  | _, _ => None
                  end
  | Swhen cond ss_true ss_false => match preprocess_subaccess_expr cond tmap, 
                  preprocess_subaccess_stmts ss_true HiF.qnil tmap, preprocess_subaccess_stmts ss_false HiF.qnil tmap with
                  | Some cond', Some ss_true', Some ss_false' => Some (Qcons (Swhen cond ss_true ss_false) sts)
                  | _, _, _ => None
                  end
  end
with preprocess_subaccess_stmts (ss : HiF.hfstmt_seq) (sts : HiF.hfstmt_seq) (tmap : VM.t (ftype * fcomponent)) : option HiF.hfstmt_seq :=
  match ss with
  | Qnil => Some (Qrev sts)
  | Qcons s ss' => match preprocess_subaccess_stmt s sts tmap with
      | Some sts' => preprocess_subaccess_stmts ss' sts' tmap
      | None => None
      end
  end.

Fixpoint expandconnects_fml (ml : list HiF.hfmodule) (tmap : VM.t (VM.t (ftype * fcomponent))) : option (list HiFP.hfmodule) :=
  match ml with
  | nil => Some nil
  | (FInmod mv ps ss) :: tl => match VM.find mv tmap with
                          | Some tmap_mod => let ps' := expand_ports ps nil in
                              (*match preprocess_subaccess_stmts ss HiFP.qnil with
                              | Some ss' =>
                                *)match expandconnects_stmts ss tmap_mod HiFP.qnil, expandconnects_fml tl tmap with
                                | Some sts, Some fml => Some ((HiFP.hfinmod (mv, N0) (rev ps') sts) :: fml)
                                | _, _ => None
                                end
                              (*| _ => None
                              end*)
                          | _ => None
                          end
  | _ :: tl => expandconnects_fml tl tmap
  end.

Definition expandconnects (c : HiF.hfcircuit) : option HiFP.hfcircuit :=
  match c, circuit_tmap c with
  | Fcircuit v ml, Some tmap => match expandconnects_fml ml tmap with
    | Some fml => Some (HiFP.fcircuit (v,N0) fml)
    | _ => None
    end
  | _, _ => None
  end.