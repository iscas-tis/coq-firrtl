From Coq Require Import FunInd FMaps FMapAVL OrderedType ZArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat ssrint eqtype seq fintype fingraph.
From simplssrlib Require Import Types SsrOrder FSets FMaps Tactics Var Store.
From firrtl Require Import Env HiEnv HiFirrtl Semantics.

Fixpoint ExpandWhens_fun
    (ml : list HiFP.hfmodule) (tmap : (PVM.t (PVM.t (fgtyp * fcomponent)))) 
    (fml : list HiFP.hfmodule) (conn_map : PVM.t (PVM.t def_expr))
:   option ((list HiFP.hfmodule) * (PVM.t (PVM.t def_expr))) 
:=  match ml with
    | nil => Some (fml, conn_map)
    | (FInmod mv pp ss) :: tl => match PVM.find mv tmap with
        | Some tmap' => match ExpandBranches_funs ss (PVM.empty def_expr) tmap' with
            | Some conn_map' =>
                let fm := FInmod mv pp (Qcat (component_stmts_of ss) (convert_to_connect_stmts conn_map')) in
                ExpandWhens_fun tl tmap (fm :: fml) (PVM.add mv conn_map' conn_map)
            | None => None
            end
        | _ => None
        end
    | m :: tl => ExpandWhens_fun tl tmap (m :: fml) conn_map
    end.

Fixpoint addplaswire (instv : VarOrder.t) (offset : nat) (pl : seq HiFP.hfport) (tmap : PVM.t (fgtyp * fcomponent)) : option (PVM.t (fgtyp * fcomponent)) :=
  match pl with
  | nil => Some tmap
  | Finput v (Gtyp t) :: tl => addplaswire instv (offset + 1) tl (PVM.add (instv, N.of_nat offset) (t, Wire) tmap)
  | Foutput v (Gtyp t) :: tl => addplaswire instv (offset + 1) tl (PVM.add (instv, N.of_nat offset) (t, Wire) tmap)
  | _ => None
  end.

(* functions used to record ftype and component type *)
Fixpoint stmts_tmap (modplmap : PVM.t (seq HiFP.hfport)) (tmap : PVM.t (fgtyp * fcomponent)) (ss : HiFP.hfstmt_seq): option (PVM.t (fgtyp * fcomponent)) :=
  match ss with
  | Qnil => Some tmap
  | Qcons s ss' => match stmt_tmap modplmap tmap s with
      | Some tmap' => stmts_tmap modplmap tmap' ss'
      | None => None
      end
  end
with stmt_tmap (modplmap : PVM.t (seq HiFP.hfport)) (tmap : PVM.t (fgtyp * fcomponent)) (s : HiFP.hfstmt) : option (PVM.t (fgtyp * fcomponent)) :=
  match s with
  | Sskip => Some tmap
  | Sfcnct _ _ => Some tmap
  | Sinvalid _ => Some tmap
  | Smem v m => Some tmap (* TBD *)
  | Sinst v mv => match PVM.find mv modplmap with
      | Some pl => addplaswire (fst v) 0 pl tmap
      | _ => None
      end
  | Swire v (Gtyp t) => match PVM.find v tmap with
      | None => Some (PVM.add v (t, Wire) tmap)
      | _ => None
      end
  | Swire v _ => None
  | Sreg v reg => match PVM.find v tmap, Sem_HiFP.type_of_hfexpr (clock reg) tmap, type reg with
      | None, Some _, Gtyp gt => Some (PVM.add v (gt, Register) tmap)
      | _, _, _ => None
      end
  | Snode v expr => match PVM.find v tmap, Sem_HiFP.type_of_hfexpr expr tmap with
                  | None, Some ft => Some (PVM.add v (ft, Node) tmap)
                  | _, _ => None
                  end
  | Swhen _ ss_true ss_false =>
      match stmts_tmap modplmap tmap ss_true with
      | Some tmap_true => stmts_tmap modplmap tmap_true ss_false 
      | _ => None
      end
  end.

Fixpoint modules_tmap (modplmap : PVM.t (seq HiFP.hfport)) (tmap : PVM.t (PVM.t (fgtyp * fcomponent))) (ml : seq HiFP.hfmodule) : option (PVM.t (PVM.t (fgtyp * fcomponent))) :=
  match ml with
  | nil => Some tmap
  | (FInmod mv ps ss) :: tl => match Sem_HiFP.ports_tmap' (PVM.empty (fgtyp * fcomponent)) ps with
              | Some pmap => match stmts_tmap modplmap pmap ss with
                  | Some tmap' => modules_tmap modplmap (PVM.add mv tmap' tmap) tl
                  | None => None
                  end
              | None => None
              end 
  | _ :: tl => modules_tmap modplmap tmap tl
  end.

Definition circuit_tmap (c : HiFP.hfcircuit) : option ((PVM.t (PVM.t (fgtyp * fcomponent))) * (PVM.t (list ProdVarOrder.t))) :=
  match c with
  | Fcircuit v ml => let modplmap := List.fold_left (fun acc m => 
      match m with
      | FInmod mv ps _ => PVM.add mv ps acc
      | FExmod mv ps _ => PVM.add mv ps acc
      end) ml (PVM.empty (seq HiFP.hfport)) in
    match modules_tmap modplmap (PVM.empty (PVM.t (fgtyp * fcomponent))) ml with
      | Some tmap => Some (tmap, PVM.map (fun tmap' => fst (List.split (PVM.elements tmap'))) tmap)
      | _ => None
      end
  end.

Definition expandWhens (c : HiFP.hfcircuit) : option (HiFP.hfcircuit * (PVM.t (PVM.t def_expr)) * (PVM.t (list ProdVarOrder.t))) :=
  match c, circuit_tmap c with
  | Fcircuit v ml, Some (tmap, vl_map) => match ExpandWhens_fun ml tmap nil (PVM.empty (PVM.t def_expr)) with
    | Some (fml, conn_map) => Some (Fcircuit v (List.rev fml), conn_map, vl_map)
    | _ => None
    end
  | _, _ => None
  end.
