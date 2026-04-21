From Coq Require Import FunInd FMaps FMapAVL OrderedType ZArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat ssrint eqtype seq fintype fingraph.
From simplssrlib Require Import Types SsrOrder FSets FMaps Tactics Var Store.
From firrtl Require Import HiEnv HiFirrtl Semantics.

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

Fixpoint expandconnects_fml (ml : list HiF.hfmodule) (tmap : VM.t (VM.t (ftype * fcomponent))) : option (list HiFP.hfmodule) :=
  match ml with
  | nil => Some nil
  | (FInmod mv ps ss) :: tl => match VM.find mv tmap with
                          | Some tmap_mod => let ps' := expand_ports ps nil in
                              match expandconnects_stmts ss tmap_mod HiFP.qnil, expandconnects_fml tl tmap with
                              | Some sts, Some fml => Some ((HiFP.hfinmod (mv, N0) (rev ps') sts) :: fml)
                              | _, _ => None
                              end
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