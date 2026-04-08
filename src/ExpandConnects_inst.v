From Coq Require Import FunInd FMaps FMapAVL OrderedType ZArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat ssrint eqtype seq fintype fingraph.
From simplssrlib Require Import Types SsrOrder FSets FMaps Tactics Var Store.
From firrtl Require Import HiEnv HiFirrtl Semantics.

Fixpoint modules_tmap (tmap : VM.t (VM.t (ftype * fcomponent))) (ml : seq HiF.hfmodule) : option (VM.t (VM.t (ftype * fcomponent))) :=
  match ml with
  | nil => Some tmap
  | (FInmod mv ps ss) :: tl => match Sem_HiF.ports_tmap' (VM.empty (ftype * fcomponent)) ps with
              | Some pmap => match Sem_HiF.stmts_tmap' pmap ss with
                  | Some tmap' => modules_tmap (VM.add mv tmap' tmap) tl
                  | None => None
                  end
              | None => None
              end 
  | _ :: tl => modules_tmap tmap tl
  end.

Definition circuit_tmap (c : HiF.hfcircuit) : option (VM.t (VM.t (ftype * fcomponent))) :=
  match c with
  | Fcircuit v ml => modules_tmap (VM.empty (VM.t (ftype * fcomponent))) ml
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