From Coq Require Import FunInd FMaps FMapAVL OrderedType ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat ssrint eqtype seq ssrfun.
From simplssrlib Require Import Types SsrOrder FSets FMaps Tactics Var Store.
From nbits Require Import NBits.
From firrtl Require Import Env HiEnv Firrtl HiFirrtl InferWidth_rewritten ExpandConnects_new ExpandWhens_2024_05_OLD.
(*Inductive hfexpr : Type :=
  | Econst : fgtyp -> bits -> hfexpr
  | Ecast : ucast -> hfexpr -> hfexpr
  | Eprim_unop : eunop -> hfexpr -> hfexpr
  | Eprim_binop : ebinop -> hfexpr -> hfexpr -> hfexpr
  | Emux : hfexpr -> hfexpr -> hfexpr -> hfexpr
  (*| Evalidif : hfexpr -> hfexpr -> hfexpr*)
  | Eref : href -> hfexpr
  with href : Type :=
  | Eid : Var.var -> href
  | Esubfield : href -> Var.var -> href (* HiFirrtl *)
  | Esubindex : href -> nat -> href (* HiFirrtl *)
  | Esubaccess : href -> hfexpr -> href (* HiFirrtl *).

Record hfmem : Type :=
    mk_fmem
      {
        data_type : ftype;
        depth : nat;
        read_latency : nat;
        write_latency : nat;
        read_write : ruw
      }.

Inductive rst : Type :=
  | NRst : rst
  | Rst : hfexpr -> hfexpr -> rst.

Record hfreg : Type :=
  mk_freg
    {
        type : ftype;
        clock : hfexpr;
        reset : rst
    }.

Inductive hfstmt : Type :=
  | Sskip
  | Swire : Var.var -> ftype -> hfstmt
  | Sreg : Var.var -> hfreg -> hfstmt
  | Smem : Var.var -> hfmem -> hfstmt
  | Sinst : Var.var -> Var.var -> hfstmt
  | Snode : Var.var -> hfexpr -> hfstmt
  | Sfcnct : href -> hfexpr -> hfstmt
  | Sinvalid : href -> hfstmt
  | Swhen : hfexpr -> hfstmt_seq -> hfstmt_seq -> hfstmt
with hfstmt_seq : Type :=
  | Qnil
  | Qcons : hfstmt -> hfstmt_seq -> hfstmt_seq.

Inductive hfport : Type :=
  | Finput : Var.var -> ftype -> hfport
  | Foutput : Var.var -> ftype -> hfport.

Inductive hfmodule : Type :=
  | FInmod : Var.var -> seq hfport -> hfstmt_seq -> hfmodule
  | FExmod : Var.var -> seq hfport -> hfstmt_seq -> hfmodule.

Inductive hfcircuit : Type := Fcircuit : Var.var -> seq hfmodule -> hfcircuit.

(***************    remove reference structure    ***************)

Definition store_ft_p (p : hfport) (tmap : VM.t ftype) : VM.t ftype :=
  match p with
  | Finput v ft => VM.add v ft tmap
  | Foutput v ft => VM.add v ft tmap
  end.

Fixpoint store_ft_s (s : hfstmt) (tmap : VM.t ftype) : VM.t ftype :=
  match s with
  | Swire v ft => VM.add v ft tmap
  | Sreg v r => VM.add v (type r) tmap
  | Snode v e => (*match type_of_e e tmap with
                | Some te => VM.add v te tmap
                | None => tmap
                end*) tmap
  | Swhen e s1 s2 => store_ft_ss s2 (store_ft_ss s1 tmap)
  | _ => tmap
  end
with store_ft_ss (ss : hfstmt_seq) (tmap : VM.t ftype) : VM.t ftype :=
  match ss with
  | Qnil => tmap
  | Qcons s st => store_ft_ss st (store_ft_s s tmap)
  end.

Definition remove_ref_p (p : hfport) : HiFP.hfport :=
  match p with
  | Finput v ft => (@HiFirrtl.Finput ProdVarOrder.T) (v, N0) ft
  | Foutput v ft => (@HiFirrtl.Foutput ProdVarOrder.T) (v, N0) ft
  end.

Fixpoint tmap_type_size (t : ftype) : N :=
(* calculates how many entries in tmap.env would be created/affected by a variable of type t *)
   match t with
   | Gtyp _ => 1%num
   | Atyp t n => N.mul (tmap_type_size t) (N.of_nat n) (* only one entry is needed for the array *)
   | Btyp ff => tmap_type_size_fields ff
   end
with tmap_type_size_fields (ff : ffield) : N :=
   match ff with
   | Fnil => 0%num
   | Fflips _ _ ft ff' => N.add (N.add (tmap_type_size ft) (tmap_type_size_fields ff')) 1%num
   end.

Fixpoint base_ref_fields (base : ProdVarOrder.t) (v : VarOrder.t) (ff : ffield) : option (ProdVarOrder.t * ftype) :=
(* find field v in ff. If found, return its type as an auxiliary to base_ref. *)
match ff with
| Fnil => None
| Fflips v' _ t' ff' =>
    if v == v' then Some ((base.1, N.add base.2 1%num), t')
               else base_ref_fields (base.1, N.add base.2 (tmap_type_size t')) v ff'
end.
   
Fixpoint base_ref (ref : href) (tmap : VM.t ftype) : option (ProdVarOrder.t * ftype) :=
match ref with
| Eid v =>
    match VM.find v tmap with
    | Some t => Some ((v, 0%num), t)
    | None   => None
    end
| Esubfield ref' v' =>
    match base_ref ref' tmap with
    | Some (base, Btyp ff) => base_ref_fields base v' ff
    | _ => None
    end
| Esubindex ref' n =>
    match base_ref ref' tmap with
    | Some (base, Atyp t' _) => Some ((base.1, N.add (N.add base.2 (N.mul (tmap_type_size t') (N.of_nat n))) 1%num), t')
    | _ => None
    end
| Esubaccess ref' _ => None
end.

Definition remove_ref_ref (r : href) (tmap : VM.t ftype) : option HiFP.href :=
  match base_ref r tmap with
  | Some (pv, _) => Some ((@HiFirrtl.Eid ProdVarOrder.T) pv)
  | _ => None
  end.

Fixpoint remove_ref_e (e : hfexpr) (tmap : VM.t ftype) : option HiFP.hfexpr :=
  match e with
  | Econst gt bs => Some ((@HiFirrtl.Econst ProdVarOrder.T) gt bs)
  | Ecast c e => match remove_ref_e e tmap with
                | Some e0 => Some ((@HiFirrtl.Ecast ProdVarOrder.T) c (e0))
                | _ => None
                end
  | Eprim_unop op e => match remove_ref_e e tmap with
                      | Some e0 => Some ((@HiFirrtl.Eprim_unop ProdVarOrder.T) op e0)
                      | _ => None
                      end
  | Eprim_binop op e1 e2 => match remove_ref_e e1 tmap, remove_ref_e e2 tmap with
                      | Some e3, Some e4 => Some ((@HiFirrtl.Eprim_binop ProdVarOrder.T) op e3 e4)
                      | _, _ => None
                      end
  | Emux c e1 e2 => match remove_ref_e c tmap, remove_ref_e e1 tmap, remove_ref_e e2 tmap with
                      | Some c0, Some e3, Some e4 => Some ((@HiFirrtl.Emux ProdVarOrder.T) c0 e3 e4)
                      | _, _, _ => None
                      end
  | Eref ref => match remove_ref_ref ref tmap with
              | Some r => Some ((@HiFirrtl.Eref ProdVarOrder.T) r)
              | _ => None
              end
  end.
  
Definition remove_ref_reg (r : hfreg) (tmap : VM.t ftype) : option HiFP.hfreg :=
  match (reset r) with
  | NRst => match remove_ref_e (clock r) tmap with
            | Some nc => Some (HiFP.mk_hfreg (type r) nc (@HiFirrtl.NRst ProdVarOrder.T))
            | _ => None
            end
  | Rst e1 e2 => match remove_ref_e (clock r) tmap, remove_ref_e e1 tmap, remove_ref_e e2 tmap with
            | Some nc, Some e3, Some e4 => Some (HiFP.mk_hfreg (type r) nc ((@HiFirrtl.Rst ProdVarOrder.T) e3 e4))
            | _, _, _ => None
            end
  end.

Fixpoint remove_ref_s (s : hfstmt) (tmap : VM.t ftype) : option HiFP.hfstmt :=
  match s with
  | Swire v ft => Some ((@HiFirrtl.Swire ProdVarOrder.T) (v, N0) ft)
  | Sreg v r => match remove_ref_reg r tmap with
              | Some r0 => Some ((@HiFirrtl.Sreg ProdVarOrder.T) (v, N0) r0)
              | None => None
              end
  | Snode v e => match remove_ref_e e tmap with
              | Some e0 => Some ((@HiFirrtl.Snode ProdVarOrder.T) (v, N0) e0)
              | None => None
              end
  | Sfcnct r e =>  match remove_ref_ref r tmap, remove_ref_e e tmap with
                  | Some r0, Some e0 => Some ((@HiFirrtl.Sfcnct ProdVarOrder.T) r0 e0)
                  | _, _ => None
                  end
  | Sinvalid r => match remove_ref_ref r tmap with
                  | Some r0 => Some ((@HiFirrtl.Sinvalid ProdVarOrder.T) r0)
                  | _ => None
                  end
  | Swhen e s1 s2 => match remove_ref_e e tmap, remove_ref_ss s1 tmap, remove_ref_ss s2 tmap with
                    | Some e0, Some s10, Some s20 => Some ((@HiFirrtl.Swhen ProdVarOrder.T) e0 s10 s20)
                    | _, _, _ => None
                    end
  | Sskip => Some (@HiFirrtl.Sskip ProdVarOrder.T)
  | _ => None
  end
with remove_ref_ss (ss : hfstmt_seq) (tmap : VM.t ftype) : option (HiFP.hfstmt_seq) :=
  match ss with
  | Qnil => Some (@HiFirrtl.Qnil ProdVarOrder.T)
  | Qcons s st => match remove_ref_s s tmap, remove_ref_ss st tmap with
                | Some s1, Some s2 => Some ((@HiFirrtl.Qcons ProdVarOrder.T) s1 s2)
                | _, _ => None
                end
  end.

Definition remove_ref (F : hfmodule) : option HiFP.hfmodule :=
  match F with
  | FInmod v pl sl => let tmap := store_ft_ss sl (List.fold_left (fun m p => store_ft_p p m) pl (VM.empty ftype)) in
                      match remove_ref_ss sl tmap with
                      | Some sl0 => Some ((@HiFirrtl.FInmod ProdVarOrder.T) (v, 0%num) (List.map remove_ref_p pl) sl0)
                      | _ => None
                      end
  | FExmod v pl sl => let tmap := store_ft_ss sl (List.fold_left (fun m p => store_ft_p p m) pl (VM.empty ftype)) in
                      match remove_ref_ss sl tmap with
                      | Some sl0 => Some ((@HiFirrtl.FExmod ProdVarOrder.T) (v, 0%num) (List.map remove_ref_p pl) sl0)
                      | _ => None
                      end
  end.


(************     lowing passes      ************)

Fixpoint seq_stmts ss : seq HiFP.hfstmt :=
  match ss with
  | @HiFirrtl.Qnil _ => [::]
  | @HiFirrtl.Qcons _ s st => s :: (seq_stmts st)
  end.
*)
Definition transformF (F : HiFP.hfmodule) : option (HiFP.hfmodule * CEP.t ftype) :=
  match InferWidth_rewritten.InferWidths_m F with
  | Some (m, tmap) => match ExpandWhens_2024_05_OLD.ExpandWhens_fun (expandconnects_fmodule m (rcd_pmap_from_m m (CEP.empty ftype))) with
                                              | Some m => Some (m, output_ft_pmap m tmap)
                                              | _ => None
                                              end
  | _ => None
  end.

