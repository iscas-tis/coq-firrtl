From Coq Require Import FunInd FMaps FMapAVL OrderedType ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat ssrint eqtype seq ssrfun.
From simplssrlib Require Import Types SsrOrder FSets FMaps Tactics Var Store.
From nbits Require Import NBits.
From firrtl Require Import Firrtl Env HiEnv HiFirrtl InferTypes.


(** Pass ExpandConnect *)
Section ExpandConnectsP.
  
  (*recursively add sub-elements accroding to the declared aggr_typ*)
  (*as for element declaration statement, add a default connection*)
  (*as for element invalid statement, add an invalid connection*)
  Fixpoint upd_aggr_elements_aux_rdef (v:pvar) (ts:seq ftype) (r:HiFP.rhs_expr) (sv:StructStateP.t) (n:N) :StructStateP.t:=
    match ts with
    | nil => sv
    | cons hd tl => upd_aggr_elements_aux_rdef v tl r (StructStateP.upd (fst v, n) r sv) (N.add n 1%num)
    end.

  (*use the types recorded in ce, since ce inclueds the result of type infering*)
  Definition upd_aggr_elements_rdef (v:pvar) (ce : CEP.env) (r:HiFP.rhs_expr) (sv:StructStateP.t) : StructStateP.t :=
    let ts := ftype_list_all (type_of_cmpnttyp (fst (CEP.vtyp v ce))) nil in
    StructStateP.upd v HiFP.r_default (upd_aggr_elements_aux_rdef v ts r sv initial_index).


  Definition is_gtyp t := match t with | Gtyp _ => true | _ => false end.
  
  (*recursively expand reference on rhs*) 
  Fixpoint expand_eref_aux (r : pvar) (sz : nat) (ce : CEP.env) (rs : seq HiFP.hfexpr) : seq HiFP.hfexpr :=
    match sz with
    | 0 => rs
    | S n => match (CEP.find (r.1, (r.2 + N.of_nat n)%num) ce) with
             | Some (t, c) => if is_gtyp (type_of_cmpnttyp t)
                              then expand_eref_aux r n ce (cons (HiFP.eref (HiFP.eid (r.1, r.2 + N.of_nat n)%num)) rs)
                              else expand_eref_aux r n ce rs
             | None => rs
             end                                              
    end.

  Definition expand_eref (r : pvar) (ce : CEP.env) : seq HiFP.hfexpr :=
    match (CEP.find r ce) with
    | Some (t, c) =>
        let ts := ftype_list_all (type_of_cmpnttyp t) nil in
        let sz := size ts in
        expand_eref_aux r sz ce nil
    | None => nil
    end.

  (*recursively expand mux, output a sequence of expressions*) 
  Fixpoint expand_emux (c : HiFP.hfexpr) (ze : seq (HiFP.hfexpr * HiFP.hfexpr)) (es : seq HiFP.hfexpr) : seq HiFP.hfexpr :=
    match ze with
    | nil => es
    | (e1, e2) :: zes => expand_emux c zes (rcons es (HiFP.emux c e1 e2))
    end.

  (*recursively expand validif, output a sequence of expressions*) 
  Fixpoint expand_evalidif (c : HiFP.hfexpr) (e : seq HiFP.hfexpr) (es : seq HiFP.hfexpr) : seq HiFP.hfexpr :=
    match e with
    | nil => es
    | e1 :: zes => expand_evalidif c zes (rcons es (HiFP.evalidif c e1))
    end.
  
  (*TODO?: Somewhere "Replaces constant [[firrtl.WSubAccess]] with [[firrtl.WSubIndex]]"*)
  (*recursively expand expr on rhs*) 
  Fixpoint expand_expr (e : HiFP.hfexpr) (ce : CEP.env) (es : seq HiFP.hfexpr) : seq HiFP.hfexpr :=
    match e with
    | Eref (Eid (r, o)) => expand_eref (r, o) ce
    | Emux c e1 e2 => expand_emux c (extzip (HiFP.econst (Fuint 0) nil) (HiFP.econst (Fuint 0) nil) (expand_expr e1 ce nil) (expand_expr e2 ce nil)) es
    | Evalidif c e => expand_evalidif c (expand_expr e ce nil) es
    | Eref _ => es
    | e => e :: es
    end.

  (*update the structure according to expanded expressions*)
  (*full connection only, connected sub-elements are all the offsets of the original target*)
  Fixpoint upd_expand_expr (v:pvar) (es: seq HiFP.hfexpr) (sv:StructStateP.t) (n:N) :StructStateP.t:=
    match es with
    | nil => sv
    | cons hd tl => upd_expand_expr v tl (StructStateP.upd (fst v, n) (HiFP.r_cnct (nth (HiFP.econst (Fuint 0) [::]) es n)) sv) (N.add n 1%num)
    end.

  Fixpoint expand_fcnct_stmts (v:pvar) (es: seq HiFP.hfexpr) (sts : HiFP.hfstmt_seq) n : HiFP.hfstmt_seq :=
    match es with
    | nil => sts
    | cons e ess => expand_fcnct_stmts v ess (HiFP.qcons (HiFP.sfcnct (HiFP.eid (v.1, N.of_nat n)) e) sts) (n-1)
    end.

  (*tests*)
  Definition p1 : pvar := (N.of_nat 1, N0).
  Definition cem := CEP.empty (cmpnt_init_typs ProdVarOrder.T * fcomponent).
  Definition ec1 := (HiFP.econst (Fuint 1) [::b1]).
  Definition ec2 := (HiFP.econst (Fuint 1) [::b0]).
  Definition ev1 := HiFP.eref (Eid p1).
  Definition ce1 := upd_aggr_elements_all p1 (HiFP.aggr_typ (Atyp (Gtyp (Fuint 1)) 3), Wire) cem.
  Definition es1 := expand_expr (HiFP.emux ec1 (HiFP.emux ec1 ev1 ev1) (HiFP.emux ec1 ev1 ev1)) ce1 nil.
  Compute (CEP.find (1%num, 0%num) ce1).
  Compute (expand_eref (1%num, 0%num) ce1).
  Compute es1.
  Compute (expand_fcnct_stmts p1 es1 HiFP.qnil) (size es1).
  
  Fixpoint expand_pcnct_atyp v1 v2 (sv:StructStateP.t) n  :StructStateP.t :=
    match n with
    | O => sv
    | S n' => expand_pcnct_atyp v1 v2 (StructStateP.upd (fst v1, N.add (snd v1) (N.of_nat n')) (HiFP.r_cnct (HiFP.eref (HiFP.eid (fst v2, N.add (snd v2) (N.of_nat n))))) sv) n'
    end.

  Fixpoint expand_pcnct_atyp_stmts v1 v2 (sts : HiFP.hfstmt_seq) n : HiFP.hfstmt_seq :=
    match n with
    | 0 => sts
    | S n' => expand_pcnct_atyp_stmts v1 v2 (HiFP.qcons (HiFP.sfcnct (HiFP.eid (v1.1, N.add v1.2 (N.of_nat n'))) (HiFP.eref (HiFP.eid (fst v2, N.add (snd v2) (N.of_nat n))))) sts) n'
    end.
  
  Fixpoint expand_pcnct_btyp (v1 v2: pvar) (t1 t2:ffield) (sv:StructStateP.t) :StructStateP.t:=
    match t1 with
    | Fnil => sv
    | Fflips vb1 f1 tf1 fs1 =>
        match t2 with
        | Fnil => sv
        | Fflips vb2 f2 tf2 fs2 =>
            if (vb1 == vb2)
            then expand_pcnct_btyp v1 v2 fs1 fs2 (StructStateP.upd (fst v1, N.add (snd v2) vb1) (HiFP.r_cnct (HiFP.eref (HiFP.eid (fst v2, N.add (snd v2) vb2)))) sv)
            else expand_pcnct_btyp v1 v2 t1 fs2 sv
        end
    end.

  Fixpoint expand_pcnct_btyp_stmts (v1 v2: pvar) (t1 t2:ffield) (sts : HiFP.hfstmt_seq) : HiFP.hfstmt_seq :=
    match t1 with
    | Fnil => sts
    | Fflips vb1 f1 tf1 fs1 =>
        match t2 with
        | Fnil => sts
        | Fflips vb2 f2 tf2 fs2 =>
            if (vb1 == vb2)
            then expand_pcnct_btyp_stmts v1 v2 fs1 fs2 (HiFP.qcons (HiFP.sfcnct (HiFP.eid (v1.1, N.add v1.2 vb1)) (HiFP.eref (HiFP.eid (fst v2, N.add (snd v2) vb2)))) sts)
            else expand_pcnct_btyp_stmts v1 v2 t1 fs2 sts
        end
    end.
  
  Definition upd_expand_pcnct_eref v1 v2 (t1 t2:ftype) (sv:StructStateP.t) :StructStateP.t:=
    match t1, t2 with
    | Gtyp gt1, Gtyp gt2 => StructStateP.upd v1 (HiFP.r_cnct (HiFP.eref (HiFP.eid v2))) sv
    | Atyp at1 n1, Atyp at2 n2 => expand_pcnct_atyp v1 v2 sv (minn n1 n2)
    | Btyp bs1, Btyp bs2 => expand_pcnct_btyp v1 v2 bs1 bs2 sv
    | _, _ => sv
    end.

  Definition expand_pcnct_stmts v1 v2 (t1 t2:ftype) (sts : HiFP.hfstmt_seq) : HiFP.hfstmt_seq :=
    match t1, t2 with
    | Gtyp gt1, Gtyp gt2 => HiFP.qcons (HiFP.sfcnct (HiFP.eid v1) (HiFP.eref (HiFP.eid v2))) sts
    | Atyp at1 n1, Atyp at2 n2 => expand_pcnct_atyp_stmts v1 v2 sts (minn n1 n2)
    | Btyp bs1, Btyp bs2 => expand_pcnct_btyp_stmts v1 v2 bs1 bs2 sts
    | _, _ => sts
    end.

   Definition element_connection (sv : StructStateP.t) (sts : HiFP.hfstmt_seq) : HiFP.hfstmt_seq :=
    let cs := StructStateP.elements sv in
    match cs with
    | nil => sts
    | c :: cs => match c with
                | (v, R_cnct e) => HiFP.qcons (Sfcnct (Eid v) e) sts
                | (v, R_invalid e) => HiFP.qcons (Sinvalid (Eid v)) sts
                | (v, R_default') => sts
                end
    end.

  Fixpoint expandconnects_stmt (s : HiFP.hfstmt) (ce : CEP.env) (sv : StructStateP.t) (sts : HiFP.hfstmt_seq) : HiFP.hfstmt_seq :=
    match s with
    | Sskip => sts
    | Swire _ _
    | Sreg _ _
    | Smem _ _ 
    | Snode _ _ => sts
    | Sfcnct (Eid v) e => Qcat (element_connection (upd_expand_expr v (expand_expr e ce nil) sv (N.of_nat (size (expand_expr e ce nil)))) sts) sts
    | Spcnct (Eid v1) (Eref (Eid v2)) => Qcat (element_connection (upd_expand_pcnct_eref v1 v2 (type_of_cmpnttyp (CEP.vtyp v1 ce).1) (type_of_cmpnttyp (CEP.vtyp v2 ce).1) sv) sts) sts
    | Sinvalid (Eid v) => Qcat (element_connection (upd_aggr_elements_rdef v ce (HiFP.r_invalid (HiFP.econst (Fuint 0) [::])) sv) sts) sts
    | Sinst v1 v2 => sts
    | Swhen c s1 s2 => expandconnects_stmt_seq s2 ce sv (expandconnects_stmt_seq s1 ce sv sts)
    | _ => sts
    end
      with expandconnects_stmt_seq (ss : HiFP.hfstmt_seq) (ce : CEP.env) (sv : StructStateP.t) (sts : HiFP.hfstmt_seq) : HiFP.hfstmt_seq :=
      match ss with
      | Qnil => sts
      | Qcons s ss => expandconnects_stmt_seq ss ce sv (expandconnects_stmt s ce sv sts)
    end.
  
  (* Fixpoint expand_expr_weak_eq (v1 v2:pvar) (ce:CEP.env)(sv:StructStateP.t) (n m:N) :StructStateP.t:= *)
  (*   let t1 := CEP.find (fst v1, initial_index) ce in *)
  (*   let t2 := CEP.find (fst v2, initial_index) ce in *)
  
  (* Fixpoint align_weak_equiv_ftype (t1 t2 : ftype) : ftype := *)
  (*   match t1, t2 with *)
  (*   | Gtyp gt1, Gtyp gt2 => t1 *)
  (*   | Atyp at1 n1, Atyp at2 n2 => Atyp (align_weak_equiv_ftype at1 at2) (minn n1 n2) *)
  (*   | Btyp bs1, Btyp bs2 => Btyp (align_weak_equiv_ffields bs1 bs2) *)
  (*   | _ , _ => t1 *)
  (*   end *)
  (* with align_weak_equiv_ffields (bs1 bs2 : ffield) : ffield := *)
  (*        match bs1 with *)
  (*        | Fnil => bs1 *)
  (*        | Fflips v1 f1 tf1 fs1 => *)
  (*            match bs2 with *)
  (*            | Fnil => bs1 *)
  (*            | Fflips v2 f2 tf2 fs2 => *)
  (*                if (v1 == v2) *)
  (*                then Fflips v1 f1 (align_weak_equiv_ftype tf1 tf2) (align_weak_equiv_ffields fs1 fs2) *)
  (*                else align_weak_equiv_ffields bs1 fs2 *)
  (*            end *)
  (*        end. *)
  
  (* Fixpoint upd_expand_expr_weak_eq (v1 v2:pvar) (es: seq HiFP.hfexpr) (ce : CEP.env) (sv:StructStateP.t) (n:N) :StructStateP.t:= *)
  (*   match es with *)
  (*   | nil => sv *)
  (*   | cons hd tl => match CEP.find (fst v2, n) ce with *)
  (*                   | None => sv *)
  (*                   | Some t => *)
  (*                       upd_expand_expr v1 tl (StructStateP.upd (fst v1, n) (HiFP.r_cnct (nth (HiFP.econst (Fuint 0) [::]) es n)) sv) (N.add n 1%num) *)
  (*                   end *)
  (*   end. *)

  
  (* Fixpoint expandconnects_stmt (s : HiFP.hfstmt) (ce : CEP.env) (sv : StructStateP.t): StructStateP.t := *)
  (*   match s with *)
  (*   | Sskip => sv *)
  (*   | Swire v t => upd_aggr_elements_rdef v ce HiFP.r_default sv *)
  (*   | Sreg v t => upd_aggr_elements_rdef v ce HiFP.r_default sv *)
  (*   | Smem v t => upd_aggr_elements_rdef v ce HiFP.r_default sv *)
  (*   | Snode v e => upd_expand_expr v (expand_expr e ce nil) sv 0 *)
  (*   | Sfcnct (Eid v) e => upd_expand_expr v (expand_expr e ce nil) sv 0 *)
  (*   | Spcnct (Eid v1) (Eref (Eid v2)) => upd_expand_pcnct_eref v1 v2 (type_of_cmpnttyp (CEP.vtyp v1 ce).1) (type_of_cmpnttyp (CEP.vtyp v2 ce).1) sv *)
  (*   | Sinvalid (Eid v) => upd_aggr_elements_rdef v ce (HiFP.r_invalid (HiFP.econst (Fuint 0) [::])) sv *)
  (*   | Sinst v1 v2 => upd_expand_expr v1 (expand_expr (Eref (Eid v2)) ce nil) sv 0 *)
  (*   | Swhen c s1 s2 => expandconnects_stmt_seq s2 ce (expandconnects_stmt_seq s1 ce sv) *)
  (*   | _ => sv *)
  (*   end *)
  (*     with expandconnects_stmt_seq (ss : HiFP.hfstmt_seq) (ce : CEP.env) (sv : StructStateP.t): StructStateP.t := *)
  (*     match ss with *)
  (*     | Qnil => sv *)
  (*     | Qcons s sts => expandconnects_stmt_seq sts ce (expandconnects_stmt s ce sv) *)
  (*   end. *)

  Definition elements_declaration (ce : CEP.env) (sts : HiFP.hfstmt_seq) : HiFP.hfstmt_seq :=
    let es := CEP.elements ce in
    match es with
    | nil => sts
    | e :: es => match e with
                           | (v, (t, Wire)) => HiFP.qcons (HiFP.swire v (type_of_cmpnttyp t)) sts
                           | (v, (Reg_typ t, Register)) => HiFP.qcons (HiFP.sreg v t) sts
                           | (v, (Mem_typ t, Memory)) => HiFP.qcons (HiFP.smem v t) sts
                           | _ => sts
                           end
    end.

  
 (* (* Check all the sub-elements connected are of ground type *) *)
 (*  Inductive expand_connects_stmt_weak_sem : HiFP.hfstmt -> StructStateP.t -> Prop := *)
 (*  | ExpandConnects_fcnct : *)
 (*    forall v1 e sv ce, *)
 (*      (forall n exs , StructStateP.find (fst v1, n) sv = Some (HiFP.r_cnct exs) -> *)
 (*                      is_gtyp (HiFP.type_of_hfexpr exs ce) -> *)
 (*                      type_of_cmpnttyp (CEP.vtyp (fst v1, n) ce).1 = HiFP.type_of_hfexpr exs ce *)
 (*      ) -> *)
 (*      expand_connects_stmt_weak_sem (Sfcnct (Eid v1) e) sv *)
 (*  | ExpandConnects_pcnct : *)
 (*    forall v1 e sv ce n exs, *)
 (*      StructStateP.find (fst v1, n) sv = Some (HiFP.r_cnct exs) -> *)
 (*      is_gtyp (HiFP.type_of_hfexpr exs ce) -> *)
 (*      expand_connects_stmt_weak_sem (Spcnct (Eid v1) e) sv *)
 (*  . *)

 (* Check all the sub-elements connected are of ground type, and connections are of equivalent types *)
  Inductive expand_connects_stmt_sem : HiFP.hfstmt -> StructStateP.t -> Prop :=
  | ExpandConnects_fcnct :
    forall v1 e sv ce,
      (forall n exs , StructStateP.find (fst v1, n) sv = Some (HiFP.r_cnct exs) ->
                      is_gtyp (HiFP.type_of_hfexpr exs ce) ->
                      ftype_equiv (type_of_cmpnttyp (CEP.vtyp (fst v1, n) ce).1) (HiFP.type_of_hfexpr exs ce)) ->
      expand_connects_stmt_sem (Sfcnct (Eid v1) e) sv
  | ExpandConnects_pcnct :
    forall v1 e sv ce ,
      (forall n exs, StructStateP.find (fst v1, n) sv = Some (HiFP.r_cnct exs) ->
                     is_gtyp (HiFP.type_of_hfexpr exs ce) ->
                     ftype_equiv (type_of_cmpnttyp (CEP.vtyp (fst v1, n) ce).1) (HiFP.type_of_hfexpr exs ce)) ->
      expand_connects_stmt_sem (Spcnct (Eid v1) e) sv.

  (* From Coq Require Export Reals. *)
  (* Coercion IZR : Z >-> R. *)
  (* Coercion INR : nat >-> R. *)
  (* Coercion Z_of_nat : nat >-> Z. *)
  (* Definition Feq (x y : Z) := x = y :>R. *)
  (* Definition Fle (x y : Z) := (x <= y)%R. *)

  Lemma expand_eref_aux_cons :
    forall n e ce id se,
      (expand_eref_aux e n ce (id :: se)) = (expand_eref_aux e n ce nil) ++ (id :: se).
  Proof.
    elim; intros; first done.
    rewrite /=.
    case Hf : (CEP.find (e.1, (e.2 + N.of_nat n)%num) ce) => [[t c]|]; last rewrite cat0s//.
    case Hg : (is_gtyp (type_of_cmpnttyp t)).
    rewrite (H e ce (HiFP.eref (HiFP.eid (e.1, (e.2 + N.of_nat n)%num))) (id :: se)).
    rewrite (H e ce (HiFP.eref (HiFP.eid (e.1, (e.2 + N.of_nat n)%num))) nil).
    rewrite -catA cat1s//.
    done.
  Qed.

  Lemma expand_eref_aux_ground_ftype :
    forall sz a b ce se,
      all (fun ex : HiFP.hfexpr => is_gtyp (HiFP.type_of_hfexpr ex ce)) se ->
      all (fun ex : HiFP.hfexpr => is_gtyp (HiFP.type_of_hfexpr ex ce)) (expand_eref_aux (a, b) sz ce se).
  Proof.
    elim; first done.
    intros; rewrite /=.
    case Hf : (CEP.find (a, (b + N.of_nat n)%num) ce) => [[t c]|].
    - case Hg: (is_gtyp (type_of_cmpnttyp t)).
      + rewrite expand_eref_aux_cons/= all_cat.
        have Hn : (all (fun ex : HiFP.hfexpr => is_gtyp (HiFP.type_of_hfexpr ex ce)) nil) by done.
        rewrite (H a b ce nil Hn) andTb/= H0.
        rewrite (CEP.find_some_vtyp Hf)/= Hg//.
      + by apply H.
    - done.
  Qed.

  (* expanding eref results in a list of expressions of ground types*)
  Lemma expand_ref_expr_ground_ftype :
    forall (h : href ProdVarOrder.T) (ce : CEP.env) (se0 : seq HiFP.hfexpr),
      all (fun ex : HiFP.hfexpr => is_gtyp (HiFP.type_of_hfexpr ex ce)) se0 ->
      all (fun ex : HiFP.hfexpr => is_gtyp (HiFP.type_of_hfexpr ex ce)) (expand_expr (Eref h) ce se0).
  Proof.
    elim; try done.
    rewrite /=.
    case; intros.
    rewrite /expand_eref.
    case Hf: (CEP.find (a, b) ce) => [[t c]|]; last done. 
    case Hsz : (size (ftype_list_all (type_of_cmpnttyp t) [::])) => [|n]; first done.
    by apply expand_eref_aux_ground_ftype.
  Qed.

  Lemma expand_emux_rcons :
    forall zl h se0 a,
      expand_emux h zl (rcons se0 a) = se0 ++ a :: (expand_emux h zl nil).
  Proof.
    elim; intros; first rewrite /= cats1//.
    rewrite /=.
    case a; intros. 
    rewrite (H h (rcons se0 a0) (HiFP.emux h h0 h1))/=.
    move : (H h nil (HiFP.emux h h0 h1)). rewrite /= => <-.
    rewrite cat_rcons//.
  Qed.

  Lemma is_gtyp_mux_types :
    forall t1 t2,
      is_gtyp t1 -> is_gtyp t2 ->
      is_gtyp (HiFP.mux_types t1 t2).
  Proof.
    elim; try done.
    elim; try done; [intro|intro|]; elim; try done; elim; try done.
  Qed.
    
  (* expanding emux results in a list of expressions of ground types*) Print expand_emux.
  Lemma expand_mux_expr_ground_ftype :
    forall (h : hfexpr ProdVarOrder.T) ce,
      (* (forall (se0 : seq HiFP.hfexpr), *)
      (*     all (fun ex : HiFP.hfexpr => is_gtyp (HiFP.type_of_hfexpr ex ce)) se0 -> *)
      (*     all (fun ex : HiFP.hfexpr => is_gtyp (HiFP.type_of_hfexpr ex ce)) *)
      (*       (expand_expr h ce se0)) -> *)
      forall hs0 : seq HiFP.hfexpr,
        (all (fun ex : HiFP.hfexpr => is_gtyp (HiFP.type_of_hfexpr ex ce)) hs0) ->
        forall hs1 : seq HiFP.hfexpr,
          (all (fun ex : HiFP.hfexpr => is_gtyp (HiFP.type_of_hfexpr ex ce)) hs1) ->
          forall (se0 : seq HiFP.hfexpr),
            all (fun ex : HiFP.hfexpr => is_gtyp (HiFP.type_of_hfexpr ex ce)) se0 ->
            all (fun ex : HiFP.hfexpr => is_gtyp (HiFP.type_of_hfexpr ex ce))
              (expand_emux h (extzip (HiFP.econst (Fuint 0) nil) (HiFP.econst (Fuint 0) nil) hs0 hs1) se0).
  Proof.
    intros h ce.
    elim.
    - intros Hn.
      elim; first done.
      intros a1 l1 Hl1 Hal1 se0 Hse0. rewrite /= in Hal1.
      move : Hal1 => /andP [Ha1 Hl11].
      rewrite /= expand_emux_rcons all_cat Hse0 andTb.
      have Hzip : (extzip (HiFP.econst (Fuint 0) [::]) (HiFP.econst (Fuint 0) [::]) [::] l1) = (zip (copy (size l1) (HiFP.econst (Fuint 0) [::])) l1).
      { rewrite extzip_zip /=subn0 cats0//. }
      move : (Hl1 Hl11 nil Hn). rewrite Hzip/= => Haux.
      rewrite Haux.
      case Hth: (HiFP.type_of_hfexpr a1 ce) => [g|a|b]; rewrite /=//.
      case g; rewrite //.
    - intros a1 l1 Hl1 Hal1.
      have Hzip : (extzip (HiFP.econst (Fuint 0) [::]) (HiFP.econst (Fuint 0) [::]) l1 [::]) = (zip l1 (copy (size l1) (HiFP.econst (Fuint 0) [::]))).
      { rewrite extzip_zip /=subn0 cats0//. }
      rewrite /= in Hal1. move/andP : Hal1 => [Hal1 Hal2].
      elim; intros.
      + rewrite /= -Hzip /=; apply Hl1; try done.
        rewrite all_rcons/= is_gtyp_mux_types//.
      + rewrite /= in H0. move/andP : H0 => [H11 H12].
        move : (Hl1 Hal2 l H12 (rcons se0 (HiFP.emux h a1 a))).
        rewrite all_rcons/= (is_gtyp_mux_types _ _ Hal1 H11) andTb => Haux.
        rewrite (Haux H1)//.
  Qed.

  Lemma expand_evalidif_cons :
    forall l h a se0,
      expand_evalidif h l (cons a se0) = cons a (expand_evalidif h l se0).
  Proof.
    elim.
    - intros. rewrite //.
    - intros. rewrite /= (H h a0 (rcons se0 (HiFP.evalidif h a)))//.
  Qed.

  Lemma expand_evalidif_rcons :
    forall se0 l h a,
      expand_evalidif h l (rcons se0 a) = se0 ++ a :: (expand_evalidif h l nil).
  Proof.
    elim. 
    - intros. rewrite /= expand_evalidif_cons//. 
    - intros. rewrite /=. rewrite -(H l0 h a0) expand_evalidif_cons//.
  Qed.

  (* expanding evalidif results in a list of expressions of ground types*)
  Lemma expand_validif_expr_ground_ftype :
    forall (h : hfexpr ProdVarOrder.T) ce,
      (forall (se0 : seq HiFP.hfexpr),
          all (fun ex : HiFP.hfexpr => is_gtyp (HiFP.type_of_hfexpr ex ce)) se0 ->
          all (fun ex : HiFP.hfexpr => is_gtyp (HiFP.type_of_hfexpr ex ce)) (expand_expr h ce se0)) ->
      forall hs,
        (all (fun ex : HiFP.hfexpr => is_gtyp (HiFP.type_of_hfexpr ex ce)) hs) ->
        forall (se0 : seq HiFP.hfexpr),
          all (fun ex : HiFP.hfexpr => is_gtyp (HiFP.type_of_hfexpr ex ce)) se0 ->
          all (fun ex : HiFP.hfexpr => is_gtyp (HiFP.type_of_hfexpr ex ce)) (expand_evalidif h hs se0).
  Proof.
    intros.
    move : hs H0 se0 H1. elim; intros; try rewrite //.
    rewrite /= in H1. move/andP : H1 => [H11 H12].
    rewrite /= expand_evalidif_rcons all_cat H2 andTb /= H11.
    have Hn : (all (fun ex : HiFP.hfexpr => is_gtyp (HiFP.type_of_hfexpr ex ce)) nil) by done.
    rewrite (H0 H12 nil Hn)//.
  Qed.

  (* expanding expressions results in a list of expressions of ground types*)
  Lemma expand_expr_ground_ftype :
    forall e ce se0,
      all (fun ex : HiFP.hfexpr => is_gtyp (HiFP.type_of_hfexpr ex ce)) se0 ->
      all (fun ex => is_gtyp (HiFP.type_of_hfexpr ex ce)) (expand_expr e ce se0).
  Proof.
    elim.
    - (*const*) intros; done. 
    - (*cast*) intros.
      case u; rewrite/=; case (HiFP.type_of_hfexpr h ce); rewrite //.
      intro; case f; rewrite //. intro; case f; rewrite //.
    - (*unary ops*)
      intros.
      case e; rewrite /=; case (HiFP.type_of_hfexpr h ce); intros;
        try (rewrite /=; done || case f; rewrite /=; done). 
      case f; intros; try done; case (n < n0); try done.
      case f; intros; try done; case (n0 <= n < n1); try done.
      case f; intros; try done; case (n <= n0); try done.
      case f; intros; try done; case (n <= n0); try done.
    - (*binary ops*)
      intros.
      case e; rewrite /=; case (HiFP.type_of_hfexpr h ce); rewrite //; intros; case (HiFP.type_of_hfexpr h0 ce); intros;
        case f; rewrite /=; intros; rewrite /=//; case f0; intros; rewrite //.
    - (*mux*)
      intros; rewrite /=.
      have Hn : (all (fun ex : HiFP.hfexpr => is_gtyp (HiFP.type_of_hfexpr ex ce)) nil) by done.
      exact : (expand_mux_expr_ground_ftype h ce (expand_expr h0 ce nil) (H0 ce nil Hn) (expand_expr h1 ce nil) (H1 ce nil Hn) se0 H2).
    - (*validif*)
      intros; rewrite /=.
      have Hn : (all (fun ex : HiFP.hfexpr => is_gtyp (HiFP.type_of_hfexpr ex ce)) nil) by done.
      exact : (expand_validif_expr_ground_ftype h ce (H ce) (expand_expr h0 ce nil) (H0 ce nil Hn) se0 H1) => Haux.
    - (*eref*)
      intros; by apply expand_ref_expr_ground_ftype.
  Qed.

  Lemma upd_expand_expr_ground_ftype :
    forall se1 ce,
      forallb (fun ex => is_gtyp (HiFP.type_of_hfexpr ex ce)) se1 ->
      (* (forall e1, In e1 se1 -> is_gtyp (HiFP.type_of_hfexpr e1 ce))  -> *)
      forall v n sv1 sv2,
        StructStateP.find (v.1, n) sv1 = None ->
        upd_expand_expr v se1 sv1 0 = sv2 ->
      forall ex, StructStateP.find (v.1, n) sv2 = Some (HiFP.r_cnct ex) ->
                   is_gtyp (HiFP.type_of_hfexpr ex ce).
  Proof.
  Admitted.
  
  (* Lemma expandconnects_fcnct_sem_comform : *)
  (*   forall v1 e sv1 sv2 ce, *)
  (*     sv2 = expandconnects_stmt (Sfcnct (Eid v1) e) ce sv1 -> *)
  (*     expand_connects_stmt_sem (Sfcnct (Eid v1) e) sv1 sv2. *)
  (* Proof. *)
  (* Admitted. *)
  

End ExpandConnectsP.
    

   (* Fixpoint size_of_ftype (ft : ftype) : nat := *)
   (* (* calculates the number of ground type elements in the type ft. *) *)
   (*   match ft with *)
   (*   | Gtyp t => 1 *)
   (*   | Atyp t n => (size_of_ftype t) * n *)
   (*   | Btyp b => size_of_fields b *)
   (*   end *)
   (* with size_of_fields (b : ffield) : nat := *)
   (*        match b with *)
   (*        | Fnil => 0 *)
   (*        | Fflips v fl t fs => (size_of_ftype t) + size_of_fields fs *)
   (*        end. *)

   (* Fixpoint offset_of_subfield_b (ft : ffield) (fid : Var.var) (n : nat) : nat := *)
   (* (* calculates n + the offset of field fid in the bundle type ft. *) *)
   (*   match ft with *)
   (*   | Fnil => n *)
   (*   | Fflips v fl t fs => if fid == v then n else offset_of_subfield_b fs fid (n + size_of_ftype t) *)
   (*   end. *)

   (* Definition offset_of_subfield (ft : ftype) (fid : Var.var) (n : nat) : nat := *)
   (* (* calculates n + the offset of field fid, if ft is a bundle type; *)
   (*    if ft is a ground or an array type it returns 0. *) *)
   (*   match ft with *)
   (*   | Gtyp t => 0 *)
   (*   | Atyp t n => 0 *)
   (*   | Btyp b => offset_of_subfield_b b fid n *)
   (*   end. *)

   (* (** TBD *) *)
   (* Parameter new_var : var -> Var.var -> var. *)
   (* Parameter new_subvar : var -> nat -> var. *)
   (* Parameter new_subvar_i : var -> nat -> var. *)
   (* Parameter new_subvar_t : var -> var -> var. *)
   (* Parameter var2v : Var.var -> V.t. *)
   (* Parameter vtmp : var. *)


   (* Fixpoint list_repeat_fn (f : list ftype -> list ftype) (n : nat) (l : list ftype) : list ftype := *)
   (* (* calculates f(f(...(f l)...)) (n applications of f). *) *)
   (*   match n with *)
   (*   | 0 => l *)
   (*   | S m => list_repeat_fn f m (f l) *)
   (*   end. *)

   (* Fixpoint ftype_list (ft : ftype) (l : list ftype) : list ftype := *)
   (* (* prepends to l a list containing all the ground type elements' types in ft. *) *)
   (*   match ft with *)
   (*   | Gtyp t => Gtyp t :: l *)
   (*   | Atyp t n => list_repeat_fn (ftype_list t) n l *)
   (*   | Btyp b => ftype_list_btyp b l *)
   (*   end *)

   (* with ftype_list_btyp (b : ffield) (l : list ftype) : list ftype := *)
   (* (* prepends to l a list containing all the ground type elements' types in the fields b. *)
   (*    Note that the list has reverse order of the fields in b. *) *)
   (*   match b with *)
   (*   | Fnil => l *)
   (*   | Fflips v fl t fs => ftype_list_btyp fs (ftype_list t l) *)
   (*   end. *)

   (* Fixpoint vlist_repeat_fn (f : list (var * ftype) -> list (var * ftype)) (v : V.T) (i : nat) (n : nat) (l : list (var * ftype)) {struct n} : list (var * ftype) := *)
   (* (* calculates f(f(...(f l)...)) (n applications of f). *)
   (*    The parameteres v and i do not influence the result. *) *)
   (*   match n with *)
   (*   | 0 => l *)
   (*   | S m => vlist_repeat_fn f (new_subvar v i) i m (f l) *)
   (*   end. *)

   (* Fixpoint ftype_vlist (v : var) (ft : ftype) (l : list (var * ftype)) : list (var * ftype) := *)
   (* (* prepends to l a list containing, for every ground type element in ft, *)
   (*    a pair (identifier, type). *)
   (*    However, I think the case of vector types is implemented wrongly. *) *)
   (*   match ft with *)
   (*   | Gtyp t => (v, Gtyp t) :: l *)
   (*   | Atyp t n => vlist_repeat_fn (ftype_vlist v t) v (size_of_ftype t) n l *)
   (*   | Btyp b => ftype_vlist_btyp v b l *)
   (*   end *)

   (* with ftype_vlist_btyp (r : var) (b : ffield) (l : list (var * ftype)) : list (var * ftype) := *)
   (* (* prepends to l a list containing, for every ground type element in bundle b, *)
   (*    a pair (identifier, type).  The order in l is the reverse of the order in b. *)
   (*    However, I think the case of vector types is implemented wrongly. *) *)
   (*   match b with *)
   (*   | Fnil => l *)
   (*   | Fflips v fl t fs => ftype_vlist_btyp r fs (ftype_vlist (new_subvar r (offset_of_subfield_b b v 0)) t l) *)
   (*   end. *)

(*    (* A map to store types destruct *) *)
(*    Definition dmap := CE.t (fgtyp * fcomponent). *)
(*    Definition empty_dmap : dmap := CE.empty (fgtyp * fcomponent). *)
(*    Definition findsd (v:var) (d:dmap) := *)
(*      match CE.find v d with Some t => t | None => (Fuint 0, Node)  end. *)

(*    Fixpoint expand_eref (er : href) (ce : cenv) : var := *)
(*    (* find a var that corresponds to the reference er (which may be a complex reference) *) *)
(*      match er with *)
(*      | Eid v => v *)
(*      | Esubfield r v => new_subvar (expand_eref r ce) (offset_of_subfield (type_of_ref r ce) (v2var v) 0) *)
(*      | Esubindex r n => new_subvar (expand_eref r ce) n *)
(*      | Esubaccess r e => new_subvar (expand_eref r ce) 0 (* TBD *) *)
(*      end. *)

(*    (* *)
(*    Fixpoint expand_index r t n l : list (var * ftype) := *)
(*      match n with *)
(*      | 0 => l *)
(*      | S m => expand_index r t m ((expand_eref (Esubindex r n), t) :: l) *)
(*      end. *)

(*    Fixpoint expand_fields_fun r bs l : list (var * ftype) := *)
(*      match bs with *)
(*      | Fnil => l *)
(*      | Fflips v fl t fs => expand_fields_fun r fs ((expand_eref (Esubfield r (var2v v)), t) :: l ) *)
(*      end. *)
(* *) *)

(*    Fixpoint fcnct_list (l1 :list (var * ftype)) (l2:list (var * ftype)) (cs : cstate) : cstate := *)
(*    (* This function assumes that the i-th element of list l1 is assigned the value of the i-th element of list l2. *)
(*       It updates cs accordingly. *) *)
(*      match l1, l2 with *)
(*      | nil, nil => cs *)
(*      | (v1, t1) :: tl1, (v2, t2):: tl2 => fcnct_list tl1 tl2 (SV.upd v1 (r_fexpr (Eref (Eid v2))) cs) *)
(*      | _, _ => cs *)
(*      end. *)

(*    (* premise : passive type, weak type equiv *) *)

(*    Fixpoint pcnct_pair_b (v1 : var) (v2 : var) (t1 : ffield) (t2: ffield) (cs : cstate) : cstate := *)
(*    (* This function expands a partial connect (Eid v1) <- (Eref (Eid v2)). *)
(*       It assigns the value of the correct subfield of v2 to the first field of (Eid v1) *)
(*       and adds the corresponding entry to cs. *) *)
(*      match t1 with *)
(*      | Fnil => cs *)
(*      | Fflips vt1 fp1 tf1 fs1 => *)
(*        match t2 with *)
(*        | Fnil => cs *)
(*        | Fflips vt2 fp2 tf2 fs2 => *)
(*          if vt1 == vt2 *)
(*          then SV.upd (new_subvar v1 (offset_of_subfield (Btyp t1) vt1 0)) *)
(*                      (r_fexpr (Eref (Eid (new_subvar v2 (offset_of_subfield (Btyp t2) vt2 0))))) cs *)
(*          else pcnct_pair_b v1 v2 t1 fs2 cs *)
(*        end *)
(*      end. *)

(*    Fixpoint pcnct_pair (t1 : (var * ftype)) (t2: (var * ftype)) (cs : cstate) : cstate := *)
(*    (* This function expands a partial connect (t1) <- (t2), depending on the types of t1 and t2 *)
(*       and returns the changed cs accordingly. *)
(*       If the types are not weakly equivalent, cs is not changed. *) *)
(*      match t1, t2 with *)
(*      | (v1, Gtyp t1) , (v2, Gtyp t2) => SV.upd v1 (r_fexpr (Eref (Eid v2))) cs *)
(*      | (v1, Atyp t1 n1) , (v2, Atyp t2 n2) => *)
(*        let n := minn n1 n2 in let t := Atyp t1 n in *)
(*                               fcnct_list (ftype_vlist v1 t nil) (ftype_vlist v2 t nil) cs *)
(*      | (v1, Btyp b1), (v2, Btyp b2) => pcnct_pair_b v1 v2 b1 b2 cs *)
(*      | _, _ => cs *)
(*      end. *)

(*    (* premise : passive type, weak type equiv *) *)

(*    Parameter store_spcnct : href -> href -> ftype -> cstate -> cstate. *)

(*    Definition store_rhsexpr (s : hfstmt) (cs : cstate) ce : cstate := *)
(*      match s with *)
(*      | Swire v t => SV.upd v r_default cs *)
(*      | Snode v e => SV.upd v (r_fexpr e) cs *)
(*      | Sreg v r => SV.upd v r_default cs *)
(*      | Smem v m => SV.upd v r_default cs *)
(*      | Sfcnct r1 (Eref r2) => *)
(*        let t1 := type_of_ref r1 ce in *)
(*        let t2 := type_of_ref r2 ce in *)
(*        fcnct_list (ftype_vlist (expand_eref r1 ce) t1 nil) (ftype_vlist (expand_eref r2 ce) t2 nil) cs *)
(*      | Spcnct r1 (Eref r2) => *)
(*        let t1 := type_of_ref r1 ce in *)
(*        let t2 := type_of_ref r2 ce in *)
(*        pcnct_pair (expand_eref r1 ce, t1) (expand_eref r2 ce, t2) cs *)
(*      | Sinvalid r1 => SV.upd (expand_eref r1 ce) r_default cs *)
(*      | _ => cs *)
(*      end. *)


   (*
   (* premise : passive type, type equiv *)
   Fixpoint expand_connect_subindex r1 r2 n : hfstmt_seq :=
     match n with
     | 0 => qnil
     | S m => Qcons (Sfcnct (Esubindex r1 n) (Eref (Esubindex r2 n))) (expand_connect_subindex r1 r2 m)
     end.

   (* premise : passive type, type equiv *)
   Fixpoint expand_fullconnect_subfield r1 r2 bs :=
     match bs with
     | Fnil => qnil
     | Fflips v Nflip t bs' => Qcons (Sfcnct (Esubfield r1 (var2v v)) (Eref (Esubfield r2 (var2v v))))
                                     (expand_fullconnect_subfield r1 r2 bs')
     | _ => Qnil
     end.

   (* premise : type weak equiv *)
   Fixpoint expand_partconnect_subfield r1 r2 bs1 bs2 {struct bs1} :=
     match bs1 with
     | Fflips v1 Nflip t1 bs1' =>
       if have_field bs2 v1 then
         Qcons (Sfcnct (Esubfield r1 (var2v v1)) (Eref (Esubfield r2 (var2v v1))))
               (expand_partconnect_subfield r1 r2 bs1' bs2)
       else expand_partconnect_subfield r1 r2 bs1' bs2
     | Fflips v1 Flipped t1 bs1' =>
       if have_field bs2 v1 then
         Qcons (Sfcnct (Esubfield r2 (var2v v1)) (Eref (Esubfield r1 (var2v v1))))
               (expand_partconnect_subfield r1 r2 bs1' bs2)
       else expand_partconnect_subfield r1 r2 bs1' bs2
     | Fnil => qnil
     end.

   (* premise: valid lhs rhs (resolve flow), type equiv/weak_equiv (type infer, width infer) *)
   (* since types are lowered in Pass LoweringType, ExpandConnect is only in transform pass, not in semantics representation ce cs *)
   Fixpoint expandConnect_fun st ce : hfstmt_seq :=
     match st with
     | Sfcnct r1 (Eref r2) =>
       let tr1 := type_of_ref r1 ce in
       let tr2 := type_of_ref r2 ce in
       match tr1, tr2 with
       | Gtyp t1, Gtyp t2 => Qcons (Sfcnct r1 (Eref r2)) qnil
       | Atyp t1 n1, Atyp t2 n2 => expand_connect_subindex r1 r2 n1
       | Btyp bs1, Btyp bs2 => expand_fullconnect_subfield r1 r2 bs1
       | _, _ => qnil
       end
     | Sfcnct r1 (Emux c r2a r2b) => TBD
     | Sfcnct r1 (Evalidif c r2) => TBD
     | Spcnct r1 (Eref r2) =>
       let tr1 := type_of_ref r1 ce in
       let tr2 := type_of_ref r2 ce in
       match tr1, tr2 with
       | Gtyp t1, Gtyp t2 => Qcons (Sfcnct r1 (Eref r2)) qnil
       | Atyp t1 n1, Atyp t2 n2 => if n1 < n2 then expand_connect_subindex r1 r2 n1
                                   else expand_connect_subindex r1 r2 n2
       | Btyp bs1, Btyp bs2 => expand_partconnect_subfield r1 r2 bs1 bs2
       | _, _ => qnil
       end
     | st => Qcons st qnil
     end.

   Inductive expand_fields : var -> var -> ffield -> CE.env -> cstate -> CE.env -> cstate -> Prop :=
   | Expand_fnil r1 r2 ce cs ce' cs' : expand_fields r1 r2 (Fnil) ce cs ce' cs'
   | Expand_fields r1 r2 v t f ffs ce0 cs0 ce1 ce2 cs1 ce' cs':
       CE.Add (new_var r1 v) (aggr_typ t, Wire) ce0 ce1 ->
       CE.Add (new_var r2 v) (aggr_typ t, Wire) ce1 ce2 ->
       SV.Upd (new_var r1 v) (R_fexpr (Eref (Eid (new_var r2 v)))) cs0 cs1 ->
       expand_fields r1 r2 ffs ce2 cs1 ce' cs' ->
       expand_fields r1 r2 (Fflips (v) f t ffs) ce0 cs0 ce' cs'.
  *)

   (*
   Inductive expandConnect : hfstmt -> CE.env -> cstate -> CE.env -> cstate -> Prop :=
   | Expand_fcnnct :
       forall r f bs r2 ce0 cs0 ce cs ,
         base_type_of_ref r ce0 == Btyp bs ->
         have_field bs (v2var f) ->
         ftype_equiv (type_of_ref r ce0) (type_of_ref r2 ce0) ->
         expand_fields (base_ref r) (base_ref r2) bs ce0 cs0 ce cs ->
         expandConnect (Sfcnct r (Eref r2)) ce0 cs0 ce cs
   | Expand_pcnnct r r2 ce0 cs0 ce cs:
       expandConnect (Spcnct r (Eref r2)) ce0 cs0 ce cs.
    *)
