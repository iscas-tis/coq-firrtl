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

Fixpoint modules_tmap (tmap : PVM.t (PVM.t (fgtyp * fcomponent))) (ml : seq HiFP.hfmodule) : option (PVM.t (PVM.t (fgtyp * fcomponent))) :=
  match ml with
  | nil => Some tmap
  | (FInmod mv ps ss) :: tl => match Sem_HiFP.ports_tmap' (PVM.empty (fgtyp * fcomponent)) ps with
              | Some pmap => match Sem_HiFP.stmts_tmap' pmap ss with
                  | Some tmap' => modules_tmap (PVM.add mv tmap' tmap) tl
                  | None => None
                  end
              | None => None
              end 
  | _ :: tl => modules_tmap tmap tl
  end.

Definition circuit_tmap (c : HiFP.hfcircuit) : option ((PVM.t (PVM.t (fgtyp * fcomponent))) * (PVM.t (list ProdVarOrder.t))) :=
  match c with
  | Fcircuit v ml => match modules_tmap (PVM.empty (PVM.t (fgtyp * fcomponent))) ml with
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
