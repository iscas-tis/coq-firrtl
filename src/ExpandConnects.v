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
    | Eref _ => (HiFP.econst (Fuint 0) [::]) :: es
    | e => e :: es
    end.

  (*update the structure according to expanded expressions*)
  (*full connection only, connected sub-elements are all the offsets of the original target*)
  Fixpoint upd_expand_expr (v:pvar) (es: seq HiFP.hfexpr) (sv:StructStateP.t) (n:N) :StructStateP.t:=
    match es with
    | nil => sv
    | cons hd tl => upd_expand_expr v tl (StructStateP.upd (fst v, n) (HiFP.r_cnct (nth (HiFP.econst (Fuint 0) [::]) es n)) sv) (N.add n 1%num)
    end.

  (* Fixpoint expand_fcnct_stmts (v:pvar) (es: seq HiFP.hfexpr) (sts : HiFP.hfstmt_seq) n : HiFP.hfstmt_seq := *)
  (*   match es with *)
  (*   | nil => sts *)
  (*   | cons e ess => expand_fcnct_stmts v ess (HiFP.qcons (HiFP.sfcnct (HiFP.eid (v.1, N.of_nat n)) e) sts) (n-1) *)
  (*   end. *)

  Fixpoint upd_expand_expr' (es: seq (HiFP.hfexpr * HiFP.hfexpr)) (sv:StructStateP.t) :StructStateP.t:=
    match es with
    | nil => sv
    | cons (Eref (Eid l), r) tl => upd_expand_expr' tl (StructStateP.upd l (HiFP.r_cnct r) sv)
    | cons _ tl => upd_expand_expr' tl sv
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
  Definition sv0 := StructStateP.empty.
  Definition sv1 := (upd_expand_expr' (zip (expand_eref (1%num, 0%num) ce1) es1) sv0).
  Compute (StructStateP.find (1%num, 2%num) sv1).
  (* Compute (expand_fcnct_stmts p1 es1 HiFP.qnil) (size es1). *)
  
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
    | Sfcnct (Eid v) e => Qcat (element_connection (upd_expand_expr' (zip (expand_eref v ce) (expand_expr e ce nil)) sv) sts) sts
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
    elim; try done; [intro|intro| | |]; elim; try done; elim; try done.
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

  Lemma size_expand_emux :
    forall z h se,
      size (expand_emux h z se) = size se + size z.
  Proof.
    elim. intros; rewrite /= addn0//.
    intros. rewrite/=.
    case a; intros.
    rewrite expand_emux_rcons/= seq.size_cat/= addnS (H h nil) /= add0n addnS//.
  Qed.

  Lemma size_mux_types :
    forall h0 h1 ce,
      size (ftype_list (HiFP.mux_types (HiFP.type_of_hfexpr h0 ce) (HiFP.type_of_hfexpr h1 ce)) [::])
      = maxn (size (ftype_list (HiFP.type_of_hfexpr h0 ce) nil)) (size (ftype_list (HiFP.type_of_hfexpr h1 ce) nil)).
  Proof. Admitted.

  Lemma ftype_equiv_mux_l :
    forall a1 a2,
      ftype_equiv a1 a2 ->
      ftype_equiv (HiFP.mux_types a1 a2) a1
  with ftype_equiv_mux_l_btyps :
         forall bs1 bs2,
           ftype_equiv (Btyp bs1) (Btyp bs2) ->
           fbtyp_equiv (HiFP.mux_btyps bs1 bs2) bs1.
  Proof.
    elim => [g1|a1 Hn n12|b1]; elim => [g2|a2 Hm n22|b2]; rewrite /=//.
    - case g1 => [tg1|tg1| | |]; case g2 => [tg2|tg2| | |]; rewrite /=//.
    - move /andP => [Heq Hfeq]. rewrite Heq Hfeq /= eq_refl andTb Hn//.
    - move => Haux. move : (ftype_equiv_mux_l_btyps b1 b2 Haux). move : Haux.
      case b1 => [|v1 f1 t1 fs1]; case b2 => [|v2 f2 t2 fs2]; rewrite //.
      + case f1; rewrite //.
      + case f1; case f2; rewrite /=//;
        case H12: (v1 == v2); rewrite /=// eq_refl/=; move/andP => [Hfeq Hfbeq]; move /andP =>[Hfeq2 Hfbeq2]; rewrite Hfeq Hfbeq /= Hfeq2 Hfbeq2 /=eq_refl//.

    elim => [|v1 f1 t1 fs1 Hn]; elim => [|v2 f2 t2 fs2 Hm]; rewrite /=//.
    - case f1; rewrite /=//.
    - case f1; case f2;
        rewrite //;
          case (v1 == v2); rewrite/=//;
                             move /andP => [Hfeq Hfbeq]; rewrite (Hn fs2 Hfbeq) eq_refl (ftype_equiv_mux_l t1 t2 Hfeq)//.
  Qed.
      
  Lemma ftype_equiv_mux_l_hfexpr :
    forall e1 e2 c ce,
      ftype_equiv (HiFP.type_of_hfexpr e1 ce) (HiFP.type_of_hfexpr e2 ce) ->
      ftype_equiv (HiFP.type_of_hfexpr (HiFP.emux c e1 e2) ce) (HiFP.type_of_hfexpr e1 ce).
  Proof.
    intros. rewrite /=.
    exact : (ftype_equiv_mux_l (HiFP.type_of_hfexpr e1 ce) (HiFP.type_of_hfexpr e2 ce) H).
  Qed.

  Lemma ftype_equiv_valid_l :
    forall a1 a2 ce,
      ftype_equiv (HiFP.type_of_hfexpr (HiFP.evalidif a1 a2) ce ) (HiFP.type_of_hfexpr a2 ce).
  Proof.
    rewrite /= ; intros; rewrite ftype_equiv_ident//.
  Qed.
    
  Lemma size_expand_eref :
    forall r t c ce ,
      CEP.find r ce = Some (t, c) ->
      size (expand_eref r ce) = size (ftype_list (type_of_cmpnttyp t) nil).
  Proof.
  Admitted.

  Lemma size_list_repeat_fn :
    forall n l1 l2 a1 a2,
      size l1 = size l2 ->
      (forall lx ly, size lx = size ly -> size (ftype_list a1 lx) = size (ftype_list a2 ly)) ->
      size (list_repeat_fn (ftype_list a1) n l1) = size (list_repeat_fn (ftype_list a2) n l2).
  Proof.
    elim => [|n Hn] l1 l2 a1 a2 Hsz H; first done.
    rewrite /=. exact : (Hn (ftype_list a1 l1) (ftype_list a2 l2) a1 a2 (H l1 l2 Hsz) H).
  Qed.
    
  Lemma ftype_equiv_ftype_list_len_ss :
    forall t1 t2 l1 l2,
      size l1 = size l2 ->
      ftype_equiv t1 t2 -> size (ftype_list t1 l1) = size (ftype_list t2 l2)
  with fbtyp_equiv_ftype_list_b_len_ss :
    forall bs1 bs2 l1 l2,
      size l1 = size l2 ->
      fbtyp_equiv bs1 bs2 -> size (ftype_list_btyp bs1 l1) = size (ftype_list_btyp bs2 l2).
  Proof.
    elim => [g1| a1 H n1| bs1] ; elim => [g2| a2 Hn n2| bs2] l1 l2 H12 ; rewrite /=//.
    - move => Hfeq. rewrite 2!size_rcons H12//.
    - move/andP => [Hsz Hfeq]. rewrite (eqP Hsz).
      apply size_list_repeat_fn; try done. 
      intros. exact : (H a2 lx ly H0 Hfeq).
    - intro. apply fbtyp_equiv_ftype_list_b_len_ss; try done.
    elim => [|v1 f1 t1 fs1 Hm]; elim => [|v2 f2 t2 fs2 Hn] l1 l2 H12; rewrite //.
    - by case f1.
    - rewrite /=. case f1; case f2; rewrite //; move/andP => [/andP [Hsz Hfeq] Hfbeq];
      exact : (Hm fs2 (ftype_list t1 l1) (ftype_list t2 l2) (ftype_equiv_ftype_list_len_ss t1 t2 l1 l2 H12 Hfeq) Hfbeq).
  Qed.
  
  Lemma size_expand_expr :
    forall e ce ,
      size (expand_expr e ce nil) = size (ftype_list (HiFP.type_of_hfexpr e ce) nil).
  Proof.
    elim; try done.
    - (*ucast*)
      intros u h; case u; rewrite /=; intros; case (HiFP.type_of_hfexpr h ce); try done; intro f; case f; done.
    - (*unary*)
      intros e h; case e; rewrite /=; intros; case (HiFP.type_of_hfexpr h ce); try done; intro f; case f; try done.
      + intros; case (n < n0); rewrite //.
      + intros; case (n < n0); rewrite //.
      + intros; case (n0 <= n < n1); rewrite //.
      + intros; case (n0 <= n < n1); rewrite //.
      + intros; case (n <= n0); rewrite //.
      + intros; case (n <= n0); rewrite //.
      + intros; case (n <= n0); rewrite //.
      + intros; case (n <= n0); rewrite //.
    - (*binary*)
      + intros e h; case e; rewrite/=; intros; case (HiFP.type_of_hfexpr h ce); case (HiFP.type_of_hfexpr h0 ce); try done; intros; case f; case f0; try done.
    - (*mux*)
      intros; rewrite/= size_expand_emux add0n/=.
      rewrite size_mux_types -(H0 ce) -(H1 ce) size_extzip//.
    - (*valid*)
      intros h H.
      elim; intros; try done; try (rewrite -(H1 ce)//).
      rewrite/=; case e; case (HiFP.type_of_hfexpr h0 ce); intros; try done; case f; intros; try done; case (HiFP.type_of_hfexpr h1 ce); intros; case f0; intros; done.
  Admitted.

  Lemma expand_emux_1 :
    forall c e1 e2 g ce,
      (HiFP.mux_types (HiFP.type_of_hfexpr e1 ce) (HiFP.type_of_hfexpr e2 ce))= Gtyp g ->
      (expand_emux c
          (extzip (HiFP.econst (Fuint 0) [::]) (HiFP.econst (Fuint 0) [::]) (expand_expr e1 ce [::])
             (expand_expr e2 ce [::])) [::])
       = [::HiFP.emux c e1 e2].
  Proof.
  Admitted.

  Lemma gtyp_expand_expr_1 :
    forall e ce,
      is_gtyp (HiFP.type_of_hfexpr e ce) ->
      expand_expr e ce nil = [::e].
  Proof.
  Admitted.

  Lemma type_of_ucast_gtyp :
    forall u e ce,
      is_gtyp (HiFP.type_of_hfexpr (HiFP.ecast u e) ce).
  Proof.
    elim; intros; rewrite /=; case (HiFP.type_of_hfexpr e ce); intros; try done.
    case f; done. case f; done.
  Qed.

  Lemma type_of_unop_gtyp :
    forall u e ce,
      is_gtyp (HiFP.type_of_hfexpr (HiFP.eprim_unop u e) ce).
  Proof.
    elim; intros; rewrite /=; case (HiFP.type_of_hfexpr e ce); intros; try done;
      case f; try done; intros.
    intros; case (n < n0); rewrite //.
    intros; case (n < n0); rewrite //.
    intros; case (n0 <= n < n1); rewrite //.
    intros; case (n0 <= n < n1); rewrite //.
    intros; case (n <= n0); rewrite //.
    intros; case (n <= n0); rewrite //.
    intros; case (n <= n0); rewrite //.
    intros; case (n <= n0); rewrite //.
  Qed.

  Lemma ftype_of_binop_gtyp :
    forall u e1 e2 ce,
      is_gtyp (HiFP.type_of_hfexpr (HiFP.eprim_binop u e1 e2) ce).
  Proof.
    elim; intros; rewrite/=; case He1 : (HiFP.type_of_hfexpr e1 ce) => [g||]; try done; case He2 :( HiFP.type_of_hfexpr e2 ce) => [g2||]; case g; try done; intros; case g2; try done.
  Qed.
    
  Lemma ftype_equiv_is_gtyp_ss :
    forall t1 t2,
      ftype_equiv t1 t2 -> is_gtyp t1 -> is_gtyp t2.
  Proof.
    elim; intros f; try discriminate.
    elim; try done.
  Qed.

  Lemma ftype_equiv_comm :
    forall a b,
      ftype_equiv a b -> ftype_equiv b a.
  Proof.
  Admitted.
  
  Lemma ftype_equiv_trans :
    forall a b c,
      ftype_equiv a b -> ftype_equiv b c -> ftype_equiv a c.
  Proof.
  Admitted.

  Lemma ftype_equiv_lr_mux_types_nondef :
    forall t1 t2,
      ~~ (ftype_equiv t1 t2) ->
      (HiFP.mux_types t1 t2) == def_ftype
  with fbtyp_equiv_lr_mux_btyp_nondef :
    forall bs1 bs2,
      ~~ (fbtyp_equiv bs1 bs2) ->
      (HiFP.mux_types (Btyp bs1) (Btyp bs2)) == def_ftype.
  Proof.
    elim => [g1|a1 H n1|bs1]; elim => [g2|a2 Hn n2|bs2]; rewrite //.
    - move : g1 g2; elim => [n1|n1| | |]; elim => [n2|n2| | |]; rewrite//.
    - by case g1. 
    - by case g1.
    - rewrite /=. 
      intros. rewrite (negbTE H0)//.
    - apply fbtyp_equiv_lr_mux_btyp_nondef.
    elim => [| v1 f1 t1 bs1 H]; elim => [| v2 f2 t2 bs2 Hn]; rewrite//.
    - by case f1.
    - rewrite /=. 
      case f1; case f2; rewrite /=//; case (v1 == v2); rewrite /=//; by move =>  ->. 
  Qed.
  
  (* Lemma ftype_equiv_lr_mux_types_nondef : *)
  (*   forall t1 t2, *)
  (*     ~~ (ftype_equiv t1 t2) -> *)
  (*     HiFP.is_deftyp (HiFP.mux_types t1 t2) *)
  (* with fbtyp_equiv_lr_mux_btyp_nondef : *)
  (*   forall bs1 bs2, *)
  (*     ~~ (fbtyp_equiv bs1 bs2) -> *)
  (*     HiFP.is_deftyp (HiFP.mux_types (Btyp bs1) (Btyp bs2)). *)
  (* Proof. *)
  (*   elim => [g1|a1 H n1|bs1]; elim => [g2|a2 Hn n2|bs2]; rewrite //. *)
  (*   - move : g1 g2; elim => [n1|n1| | |]; elim => [n2|n2| | |]; rewrite//. *)
  (*   - by case g1.  *)
  (*   - by case g1. *)
  (*   - rewrite /=; case (n1 == n2); last done. rewrite /=; exact : (H a2). *)
  (*   - apply fbtyp_equiv_lr_mux_btyp_nondef. *)
  (*   elim => [| v1 f1 t1 bs1 H]; elim => [| v2 f2 t2 bs2 Hn]; rewrite//. *)
  (*   - by case f1. Print HiFP.mux_types. *)
  (*   - rewrite /=.  *)
  (*     case f1; case f2; rewrite /=//; case (v1 == v2); rewrite /=//; by move =>  ->.  *)
  (* Qed. *)
      
  Lemma mux_types_nondef_ftype_equiv_lr :
    forall t1 t2,
      ~~ ((HiFP.mux_types t1 t2)==def_ftype) ->
      ftype_equiv t1 t2.
  Proof.
    intros. exact : (contraNT (ftype_equiv_lr_mux_types_nondef t1 t2)).
  Qed.

  Lemma expand_emux_cons :
    forall tl hd l c,
      (~~( expand_emux c tl (cons hd l) == nil)).
  Proof.
    elim => [|hd1 tl1 H] hd l c; first done.
    rewrite/=. case hd1; intros. rewrite (H hd (rcons l (HiFP.emux c h h0)) c)//.
  Qed.

  Lemma list_repeat_ftype_list :
    forall n gt ls,
      list_repeat_fn (ftype_list gt) n.+1 ls = ftype_list gt (list_repeat_fn (ftype_list gt) n ls).
  Proof.
    elim => [|ns Hn] gt ls. rewrite //.
    move : (Hn gt (ftype_list gt ls)).
    rewrite /=. exact.
  Qed.

  Lemma list_repeat_fn_ftype_equiv :
    forall n l1 l2 a1 a2,
      all2 (fun a : ftype => [eta ftype_equiv a]) l1 l2 ->
      (forall lx ly,  all2 (fun a : ftype => [eta ftype_equiv a]) lx ly ->
                      all2 (fun a : ftype => [eta ftype_equiv a]) (ftype_list a1 lx) (ftype_list a2 ly)) ->
      all2 (fun a : ftype => [eta ftype_equiv a]) (list_repeat_fn (ftype_list a1) n l1)
        (list_repeat_fn (ftype_list a2) n l2).
  Proof.
    elim => [|ns Hn] l1 l2 a1 a2 Hl12 H; first done.
    rewrite /=. exact : (Hn (ftype_list a1 l1) (ftype_list a2 l2) a1 a2 (H l1 l2 Hl12) H).
  Qed.

  Lemma ftype_equiv_ftype_list_equiv :
    forall t1 t2 l1 l2,
      ftype_equiv t1 t2 ->
      all2 (fun a b => ftype_equiv a b) l1 l2 ->
      all2 (fun a b => ftype_equiv a b) (ftype_list t1 l1) (ftype_list t2 l2)
  with fbtyp_equiv_ftype_list_btyp_equiv :
    forall t1 t2 (l1 l2 : seq ftype),
      fbtyp_equiv t1 t2 ->
      all2 (fun a b => ftype_equiv a b) l1 l2 ->
      all2 (fun a b => ftype_equiv a b) (ftype_list_btyp t1 l1) (ftype_list_btyp t2 l2).
  Proof.
    elim => [g1| a1 H n1| bs1]; elim => [g2| a2 H2 n2| bs2];  intros; rewrite //.
    - move : H H0.
      rewrite /= 2!all2E => Hfeq /andP [/eqP Hsz Hleq].
      rewrite zip_rcons// 2!size_rcons Hsz eq_refl andTb all_rcons/= Hfeq Hleq//.
    - move : H0; rewrite /= => /andP [/eqP Hsz Hfeq].
      rewrite Hsz.
      apply list_repeat_fn_ftype_equiv ; try done.
      intros. exact : (H a2 lx ly Hfeq H0).
    - move : H; rewrite /= => H. apply fbtyp_equiv_ftype_list_btyp_equiv; try done.
    elim => [|v1 f1 t1 fs1 Hn]; elim => [|v2 f2 t2 fs2 Hm]; rewrite //.
    - by case f1.
    - rewrite /=. case f1; case f2; case (v1 == v2); rewrite // andTb; move => l1 l2 /andP [Hfeq Hbeq] Hl12;
      apply Hn; try done; apply ftype_equiv_ftype_list_equiv; try done.
  Qed.

  (* H : forall ce : CEP.t (cmpnt_init_typs ProdVarOrder.T * fcomponent), *)
  (*     (forall (v : pvar) (t : cmpnt_init_typs ProdVarOrder.T * fcomponent), CEP.find v ce = Some t) -> *)
  (*     [seq HiFP.type_of_hfexpr a ce | a <- expand_expr h ce [::]] = *)
  (*     ftype_list (HiFP.type_of_hfexpr h ce) [::] *)
  (* h0 : hfexpr ProdVarOrder.T *)
  (* H0 : forall ce : CEP.t (cmpnt_init_typs ProdVarOrder.T * fcomponent), *)
  (*      (forall (v : pvar) (t : cmpnt_init_typs ProdVarOrder.T * fcomponent), CEP.find v ce = Some t) -> *)
  (*      [seq HiFP.type_of_hfexpr a ce | a <- expand_expr h0 ce [::]] = *)
  (*      ftype_list (HiFP.type_of_hfexpr h0 ce) [::] *)
  (* h1 : hfexpr ProdVarOrder.T *)
  (* H1 : forall ce : CEP.t (cmpnt_init_typs ProdVarOrder.T * fcomponent), *)
  (*      (forall (v : pvar) (t : cmpnt_init_typs ProdVarOrder.T * fcomponent), CEP.find v ce = Some t) -> *)
  (*      [seq HiFP.type_of_hfexpr a ce | a <- expand_expr h1 ce [::]] = *)
  (*      ftype_list (HiFP.type_of_hfexpr h1 ce) [::] *)
  (* ce : CEP.t (cmpnt_init_typs ProdVarOrder.T * fcomponent) *)
  (* H2 : forall (v : pvar) (t : cmpnt_init_typs ProdVarOrder.T * fcomponent), CEP.find v ce = Some t *)
  (* ============================ *)
  (* [seq HiFP.type_of_hfexpr a ce | a <- expand_expr (Emux h h0 h1) ce [::]] = *)
  (* ftype_list (HiFP.type_of_hfexpr (Emux h h0 h1) ce) [::] *)

  
  Lemma expand_emux_zip_mux_types_aux :
    forall l1 l2 h ce,
      [seq HiFP.type_of_hfexpr a ce
      | a <- expand_emux h (zip l1 l2) [::]] =
        map (fun (z : HiFP.hfexpr * HiFP.hfexpr) =>
               let (a,b) := z in HiFP.type_of_hfexpr (HiFP.emux h a b) ce) (zip l1 l2).
  Proof.
    elim => [|hd1 tl1 Hn]; elim => [|hd2 tl2 Hm] h ce; try (rewrite zip_nil//||rewrite zip_nil_r//).
    - rewrite /= -(Hn tl2 h ce).
      have -> : [:: HiFP.emux h hd1 hd2] = rcons nil (HiFP.emux h hd1 hd2) by done.
      rewrite expand_emux_rcons cat0s map_cons//.
  Qed.


  Fixpoint ftype_list_all' (ft : ftype) (l : list ftype) : list ftype :=
    match ft with
    | Gtyp t => rcons l ft
    | Atyp t n => rcons (repeat n (ftype_list_all' t l)) ft
    | Btyp b => rcons (ftype_list_btyp_all' b l) ft
    end
  with ftype_list_btyp_all' (b : ffield) (l : list ftype) : list ftype :=
         match b with
         | Fnil => l
         | Fflips v fl t fs => ftype_list_all' t (ftype_list_btyp_all' fs l)
         end.

  Fixpoint ftype_list' (ft : ftype) (l : list ftype) : list ftype :=
    match ft with
    | Gtyp t => rcons l ft
    | Atyp t n => l ++ repeat n (ftype_list' t nil) 
    | Btyp b => ftype_list_btyp' b l
    end
  with ftype_list_btyp' (b : ffield) (l : list ftype) : list ftype :=
         match b with
         | Fnil => l
         | Fflips v fl t fs => ftype_list_btyp' fs (ftype_list' t l)
         end.

    Definition agt := HiFP.aggr_typ (Atyp (Btyp (Fflips 5%num Nflip (Gtyp (Fsint 1)) (Fflips 6%num Nflip (Atyp (Gtyp (Fsint 2)) 4) Fnil))) 2).
  Definition tagt := type_of_cmpnttyp agt.
  Compute tagt.
        (* Atyp *)
        (*  (Btyp *)
        (*     (Fflips 5%num Nflip (Gtyp (Fsint 1)) *)
        (*        (Fflips 6%num Nflip (Atyp (Gtyp (Fsint 2)) 2) Fnil))) 3 *)
  Compute ftype_list' tagt nil.
       (* = [:: Gtyp (Fsint 2); Gtyp (Fsint 2); Atyp (Gtyp (Fsint 2)) 2;  *)
       (*    Gtyp (Fsint 1); *)
       (*     Btyp *)
       (*       (Fflips 5%num Nflip (Gtyp (Fsint 1)) *)
       (*          (Fflips 6%num Nflip (Atyp (Gtyp (Fsint 2)) 2) Fnil));  *)
       (*    Gtyp (Fsint 2); Gtyp (Fsint 2); Atyp (Gtyp (Fsint 2)) 2;  *)
       (*    Gtyp (Fsint 1); *)
       (*     Btyp *)
       (*       (Fflips 5%num Nflip (Gtyp (Fsint 1)) *)
       (*          (Fflips 6%num Nflip (Atyp (Gtyp (Fsint 2)) 2) Fnil));  *)
       (*    Gtyp (Fsint 2); Gtyp (Fsint 2); Atyp (Gtyp (Fsint 2)) 2;  *)
       (*    Gtyp (Fsint 1); *)
       (*     Btyp *)
       (*       (Fflips 5%num Nflip (Gtyp (Fsint 1)) *)
       (*          (Fflips 6%num Nflip (Atyp (Gtyp (Fsint 2)) 2) Fnil)); *)
       (*     Atyp *)
       (*       (Btyp *)
       (*          (Fflips 5%num Nflip (Gtyp (Fsint 1)) *)
  (*             (Fflips 6%num Nflip (Atyp (Gtyp (Fsint 2)) 2) Fnil))) 3] *)
  Compute (ftype_list' tagt nil == ftype_list tagt nil).

  
  Lemma list_repeat_fn_seq_repeat :
    forall n l f ,
      (forall l, f l = l ++ f [::]) ->
      list_repeat_fn f n.+1 l = l ++ repeat n.+1 (f nil).
  Proof.
    elim => [|ns H] l f Hnil.
    - rewrite /= cats0//.
    - move :(H (l) f Hnil); rewrite (lock (ns.+1)) /= => Hn.
      rewrite catA -Hnil -lock (H (f l) f)//.
  Qed.
  
  Lemma ftype_list_list :
    forall l t, (ftype_list t) l = l ++ ftype_list t nil
    with ftype_list_btyp_list :
      forall l bs, (ftype_list_btyp bs) l = l ++ ftype_list_btyp bs nil.
  Proof.
    move => l t. move : t l.
    elim => [gt| a Hn n| bs] l.
    - rewrite /= cats1//.
    - rewrite /=. case n. rewrite/= cats0//. intros. 
      rewrite (list_repeat_fn_seq_repeat n0 l (ftype_list a) Hn).
      rewrite (list_repeat_fn_seq_repeat n0 nil (ftype_list a) Hn) catA cats0//.
    - rewrite /=. exact : ftype_list_btyp_list.
    move => l t. move : t l.
    elim => [| v f t bs H] l.
    - rewrite /= cats0//.
    - rewrite /= (H (ftype_list t l)) (H (ftype_list t [::])).
      rewrite (ftype_list_list l t) catA. done.
  Qed.

  Lemma ftype_list_all_list :
    forall l t, (ftype_list_all t) l = l ++ ftype_list_all t nil
    with ftype_list_all_btyp_list :
      forall l bs, (ftype_list_btyp_all bs) l = l ++ ftype_list_btyp_all bs nil.
  Proof.
    move => l t. move : t l.
    elim => [gt| a Hn n| bs] l.
    - rewrite /= cats1//.
    - rewrite /=. case n. rewrite/= cats1//. intros. 
      rewrite (list_repeat_fn_seq_repeat n0 l (ftype_list_all a) Hn). rewrite rcons_cat.
      rewrite (list_repeat_fn_seq_repeat n0 nil (ftype_list_all a) Hn) cat0s//.
    - rewrite /= -rcons_cat. rewrite -ftype_list_all_btyp_list//.
    move => l t. move : t l.
    elim => [| v f t bs H] l.
    - rewrite /= cats0//.
    - rewrite /=. rewrite (H l). 
      rewrite (ftype_list_all_list (ftype_list_btyp_all bs [::]) t) catA. done.
  Qed.
  
  Lemma zip_repeat_n :
    forall n (l1 l2 : seq ftype),
      size l1 = size l2 ->
      zip (repeat n l1)  (repeat n l2) = repeat n (zip l1 l2).
  Proof. Admitted.

  Lemma repeat_map_n : 
    forall n a1 a2,
    [seq (let (a, b) := z in HiFP.mux_types a b)
     | z : ftype * ftype <- repeat n (zip (ftype_list a1 [::]) (ftype_list a2 [::]))] =
    repeat n (ftype_list (HiFP.mux_types a1 a2) [::]).
  Proof. Admitted.

  Lemma repeat_map :
    forall A (f : A -> A) n (l : seq A),
      [seq f z | z : A <- repeat n l] = repeat n ([seq f z | z <- l]).
  Proof. Admitted.

  Lemma mux_types_ftype_list :
    forall te1 te2,
      ftype_equiv te1 te2 ->
      [seq (let (a, b) := z in HiFP.mux_types a b)
      | z : ftype * ftype <- zip (ftype_list te1 [::]) (ftype_list te2 [::])] =
        ftype_list (HiFP.mux_types te1 te2) [::]
  with mux_btype_ftype_list :
    forall te1 te2,
      ftype_equiv (Btyp te1) (Btyp te2) ->
      [seq (let (a, b) := z in HiFP.mux_types a b)
      | z : ftype * ftype <- zip (ftype_list_btyp te1 [::]) (ftype_list_btyp te2 [::])] =
        ftype_list_btyp (HiFP.mux_btyps ( te1) ( te2)) [::].
  Proof.
    elim => [gt1|a1 Hn1 n1|bs1]; elim => [gt2|a2 Hn2 n2|bs2] Hfeq; rewrite //.
    - case gt1; case gt2; rewrite //.
    - move : Hfeq; rewrite /= => Hfeq; rewrite Hfeq /=.
      move/andP : Hfeq => [/eqP Hsz Hfeq].
      move : (Hn1 a2 Hfeq). rewrite Hsz.
      move : Hsz.
      case n2; intros. rewrite //.
      rewrite list_repeat_fn_seq_repeat; [|intros; apply ftype_list_list]. 
      rewrite list_repeat_fn_seq_repeat; [|intros; apply ftype_list_list]. 
      rewrite list_repeat_fn_seq_repeat; [|intros; apply ftype_list_list]. 
      rewrite !cat0s /=.
      rewrite zip_cat; last (apply ftype_equiv_ftype_list_len_ss; rewrite //). 
      rewrite map_cat. rewrite -{1}(Hn1 a2 Hfeq).
      rewrite zip_repeat_n; last (apply ftype_equiv_ftype_list_len_ss; rewrite //).
      rewrite repeat_map_n//.
    - generalize Hfeq. rewrite /= => Hfeqb. rewrite Hfeqb/=.
      move : (mux_btype_ftype_list bs1 bs2 Hfeq).
      case (HiFP.mux_btyps bs1 bs2); rewrite //.
    elim => [|v1 f1 t1 bs1 Hn]; elim => [|v2 f2 t2 bs2 Hn2]; rewrite  //; try by case f1.
    - case f1; case f2; rewrite /=//. 
      + move/andP => [/andP [/eqP Hsz Heq] Hbeq]. rewrite Hsz eq_refl/=.
        rewrite {1}ftype_list_btyp_list.
        have -> :(ftype_list_btyp bs2 (ftype_list t2 [::])) = (ftype_list t2 [::] ++ ftype_list_btyp bs2 [::])
          by rewrite ftype_list_btyp_list//.
        rewrite zip_cat; last (apply ftype_equiv_ftype_list_len_ss; rewrite //).
        rewrite map_cat /=. move : (Hn bs2). rewrite (lock HiFP.mux_types)/= -lock => Haux.
        rewrite (Haux Hbeq) (mux_types_ftype_list t1 t2 Heq). symmetry. rewrite ftype_list_btyp_list//.
      + move/andP => [/andP [/eqP Hsz Heq] Hbeq]. rewrite Hsz eq_refl/=.
        rewrite {1}ftype_list_btyp_list.
        have -> :(ftype_list_btyp bs2 (ftype_list t2 [::])) = (ftype_list t2 [::] ++ ftype_list_btyp bs2 [::])
          by rewrite ftype_list_btyp_list//.
        rewrite zip_cat; last (apply ftype_equiv_ftype_list_len_ss; rewrite //).
        rewrite map_cat /=. move : (Hn bs2). rewrite (lock HiFP.mux_types)/= -lock => Haux.
        rewrite (Haux Hbeq) (mux_types_ftype_list t1 t2 Heq). symmetry. rewrite ftype_list_btyp_list//.
  Qed.

  Lemma zip_map_pair :
    forall {A B} l1 l2 (f1 : A -> A -> A) (f2 : B -> A),
      [seq (let (a, b) := z in f1 (f2 a) (f2 b))
      | z : B * B <- zip l1 l2] =
        [seq (let (a, b) := z in f1 a b)
        | z : A * A <- zip [seq f2 a | a <- l1]
                 [seq f2 b | b <- l2]].
  Proof.
    intros A B. elim => [|hd1 tl1 Hn1]; elim => [|hd2 tl2 Hn2]; try (rewrite zip_nil/=//); try (rewrite zip_nil_r//).
    intros. rewrite /= (Hn1 tl2)//.
  Qed.
      
  Lemma expand_emux_zip_mux_types :
    forall h0 h1 h ce,
      [seq HiFP.type_of_hfexpr a ce | a <- (expand_expr h0 ce [::])] =
        ftype_list (HiFP.type_of_hfexpr h0 ce) nil ->
      [seq HiFP.type_of_hfexpr a ce | a <- (expand_expr h1 ce [::])] =
        ftype_list (HiFP.type_of_hfexpr h1 ce) nil ->
      ftype_equiv (HiFP.type_of_hfexpr h0 ce) (HiFP.type_of_hfexpr h1 ce) ->
      [seq HiFP.type_of_hfexpr a ce
      | a <- expand_emux h (zip (expand_expr h0 ce [::]) (expand_expr h1 ce [::])) [::]] =
        ftype_list (HiFP.mux_types (HiFP.type_of_hfexpr h0 ce) (HiFP.type_of_hfexpr h1 ce)) [::].
  Proof.
    intros. rewrite expand_emux_zip_mux_types_aux/=.
    rewrite -mux_types_ftype_list//. rewrite -H -H0. 
    rewrite zip_map_pair//.
  Qed.

  Lemma expand_evalidif_aux :
    forall lst h ce,
      [seq HiFP.type_of_hfexpr a ce | a <- expand_evalidif h lst [::]] =
        [seq HiFP.type_of_hfexpr a ce | a <- lst].
  Proof.
    elim => [| hd tl Hn] h ce; rewrite /=//.
    rewrite expand_evalidif_cons. rewrite -(Hn h ce)/=//.
  Qed.
    
  Lemma expand_evalidif_zip_ftypes :
    forall h0 h ce,
      [seq HiFP.type_of_hfexpr a ce | a <- expand_expr h0 ce [::]] =
        ftype_list (HiFP.type_of_hfexpr h0 ce) [::] ->
      [seq HiFP.type_of_hfexpr a ce
      | a <- expand_evalidif h (expand_expr h0 ce [::]) [::]] =
        ftype_list (HiFP.type_of_hfexpr h0 ce) [::].
  Proof. 
    intros. rewrite -H. apply expand_evalidif_aux.
  Qed.
  
  (* Lemma ftype_list_filter_ftype_list_all : *)
  (*   forall t l, *)
  (*     (forall la, [seq x <- la | is_gtyp x] = l) -> *)
  (*     ftype_list t l = filter is_gtyp (ftype_list_all t l). *)
  (* Proof.  *)
  (*   elim => [g| a Hn n |bs] l H; rewrite //. *)
  (*   - rewrite /= filter_rcons/= H//. *)
  (*   - rewrite /= filter_rcons/=. *)
  (*     move : n l H. *)
  (*     elim => [|ns Hm] l H; rewrite /= . *)
  (*     + rewrite H//. *)
  (*     + move : (Hn l H) => Haux. symmetry in Haux. *)
  (*        rewrite -(Hm (ftype_list_all a l)). *)
  (* Admitted. *)

  (* Lemma expand_eref_aux_cons : *)
  (*   forall r s ce hd tl , *)
  (*     expand_eref_aux r s ce (hd :: tl) = hd :: (expand_eref_aux r s ce tl). *)
  
  Lemma expand_eref_aux_ftypes :
    forall s t ce ,
      (forall c, CEP.find s ce = Some (t, c)) ->
      [seq HiFP.type_of_hfexpr a0 ce
      | a0 <- expand_eref_aux s (size (ftype_list_all (type_of_cmpnttyp t) [::])) ce [::]] =
        ftype_list (type_of_cmpnttyp t) [::]
  with expand_eref_aux_fbtyps :
    forall s t bs ce,
      (forall c, CEP.find s ce = Some (t, c)) ->
      type_of_cmpnttyp t = Btyp bs ->
      [seq HiFP.type_of_hfexpr a0 ce
      | a0 <- expand_eref_aux s (size (ftype_list_btyp_all bs [::])) ce [::]] =
        ftype_list_btyp bs [::]
  .
    (* forall s t ce , *)
    (*   (forall c, CEP.find s ce = Some (t, c)) -> *)
    (*   [seq HiFP.type_of_hfexpr a0 ce *)
    (*   | a0 <- expand_eref_aux s (size (ftype_list_all (type_of_cmpnttyp t) [::])) ce [::]] = *)
    (*     ftype_list (type_of_cmpnttyp t) [::]. *)
  Proof.
    elim . intros a b t. move : t a b.
    elim .
    - elim => [gt|an Hn tn | bs ] a b ce Hc.
      + rewrite /=N.add_0_r/= (Hc Node) /=.
        rewrite (CEP.find_some_vtyp (Hc Node))/=//.
      + rewrite /= size_rcons/=. rewrite expand_eref_aux_cons.
        case Hfd : (CEP.find (a, (b + N.of_nat (size (list_repeat_fn (ftype_list_all an) tn [::])))%num) ce) => [[tan can]|].
        case Hgt: (is_gtyp (type_of_cmpnttyp tan)).
        rewrite /= in Hn. rewrite map_cat. move : Hfd. case tn => [|tns]. 
        rewrite /= N.add_0_r (Hc can)/= => Hfd.
        injection Hfd. move => Hdis. rewrite -Hdis in Hgt; discriminate.
        rewrite list_repeat_fn_seq_repeat; [|intros; rewrite ftype_list_all_list//]. 
        rewrite seq.size_cat. rewrite list_repeat_fn_seq_repeat; [|intros; rewrite ftype_list_list//].
        have -> : size [::] = 0 by done.
        rewrite add0n cat0s. intros.
        rewrite (lock repeat)/= -lock (CEP.find_some_vtyp Hfd)/=.
        admit.
        move : Hfd. case tn => [|tns]. done.
        rewrite /= in Hn.
        rewrite list_repeat_fn_seq_repeat; [|intros; rewrite ftype_list_all_list//]. 
        rewrite seq.size_cat. rewrite list_repeat_fn_seq_repeat; [|intros; rewrite ftype_list_list//].
        have -> : size [::] = 0 by done.
        rewrite add0n cat0s. intros. rewrite /=.
        admit.
  Admitted.      
    
  Lemma expand_eref_ftypes :
    forall (s:pvar) (ce: CEP.env),
      (forall (a b : VarOrder.T) (t : cmpnt_init_typs ProdVarOrder.T* fcomponent), (*(b<= (size (ftype_list (type_of_cmpnttyp t.1) nil))) -> *)CEP.find (a,b) ce = Some t) -> 
      [seq HiFP.type_of_hfexpr a ce | a <- let (r, o) := s in expand_eref (r, o) ce] = ftype_list (HiFP.type_of_ref (HiFP.eid s) ce) [::].
  Proof.
    elim. intros.
    rewrite /=/expand_eref .
    case Hf : (CEP.find (a, b) ce) => [[t c]|].
    - rewrite (CEP.find_some_vtyp Hf)/=. 
      case(size (ftype_list_all (type_of_cmpnttyp t) [::])) => [|ns]. admit.
      rewrite /=. case Hfd : (CEP.find (a, (b + N.of_nat ns)%num)) => [t0|].
      case t0 => [t1 c1].
      case Hgt : (is_gtyp (type_of_cmpnttyp t1)).
  Admitted.
  
  Lemma expand_expr_ftype_list_equiv :
    forall e ce,
      (forall (v:pvar) t, CEP.find v ce = Some t) ->
      (map (fun a => HiFP.type_of_hfexpr a ce) (expand_expr e ce nil)) = (ftype_list (HiFP.type_of_hfexpr e ce) nil).
  Proof.
    elim; try rewrite //.
    - intros. move : (H ce).
      case u; rewrite /=; case (HiFP.type_of_hfexpr h ce); rewrite /=//.
      + intro f; case f; rewrite //.
      + intro f; case f; rewrite //.
    - intros. move : (H ce).
      case e; rewrite /=; case (HiFP.type_of_hfexpr h ce); rewrite /=//; try (intros; case f; rewrite //); try (intros ; case (n <= n0); rewrite //); try (intros ; case (n0 <= n < n1); rewrite //); try (intros ; case (n < n0); rewrite //).
    - intros. move : (H ce).
      case e; rewrite /=; case (HiFP.type_of_hfexpr h ce) => [g1| a1 t1| bs1]; rewrite /=//; case (HiFP.type_of_hfexpr h0 ce) => [g2| a2 t2| bs2]; rewrite /=//; try (case g1 => [n1|n1| | |]; case g2 => [n2|n2| | |]; rewrite //); try (case g1; rewrite //).
    - intros.
      case Heq : (ftype_equiv (HiFP.type_of_hfexpr h0 ce) (HiFP.type_of_hfexpr h1 ce)).
      move : (ftype_equiv_mux_l_hfexpr h0 h1 h ce Heq) => Heqmux.
      have Haux : (all2 (fun a : ftype => [eta ftype_equiv a]) [::] [::]) by done.
      move : (ftype_equiv_ftype_list_equiv _ _ nil nil Heqmux Haux). rewrite /= all2E => /andP [Hsz Heq2].
      rewrite/=.
      rewrite extzip_zip_ss. apply expand_emux_zip_mux_types; [by apply H0| by apply H1| by rewrite Heq].
      rewrite 2!size_expand_expr.
      move : (ftype_equiv_ftype_list_equiv _ _ nil nil Heq Haux). rewrite all2E => /andP [Hsz2 Heq3].
      rewrite (eqP Hsz2) //.
      rewrite /=. move : (ftype_equiv_lr_mux_types_nondef _ _ (negbT Heq)) => Hgt.
      rewrite (eqP Hgt). rewrite (expand_emux_1 h h0 h1 _ ce (eqP Hgt))/= (eqP Hgt)//.
    - intros. rewrite /= expand_evalidif_zip_ftypes//. by apply H0.
    - intros. rewrite /=.
      case h; rewrite //.
      intros. 
      case Hf: (CEP.find s ce) => [[t c]|]. 
      rewrite expand_eref_ftypes//.
      rewrite (H s (HiFP.aggr_typ (HiFP.type_of_ref (Eid (var:=ProdVarOrder.T) s) ce), Node)) //in Hf.
  Qed.
      
  Lemma ftype_list_equiv_expand_expr :
    forall e1 e2 ce,
      (forall (v:pvar) t, CEP.find v ce = Some t) ->
      all [pred xy |
      ftype_equiv (xy.1) (xy.2)]
        (zip (ftype_list (HiFP.type_of_hfexpr e1 ce) nil) (ftype_list (HiFP.type_of_hfexpr e2 ce) nil)) ->
      all [pred xy |
      ftype_equiv (xy.1) (xy.2)]
        (zip (map (fun a => HiFP.type_of_hfexpr a ce) (expand_expr e1 ce nil))
             (map (fun a => HiFP.type_of_hfexpr a ce) (expand_expr e2 ce nil))).
  Proof.
    intros e1 e2 ce Hf. rewrite -(expand_expr_ftype_list_equiv e2 ce Hf).
    rewrite -(expand_expr_ftype_list_equiv e1 ce Hf)//.
  Qed.
    
  Lemma ftype_equiv_all2 :
    forall e1 e2 ce,
      (forall (v:pvar) t, CEP.find v ce = Some t) ->
      ftype_equiv (HiFP.type_of_hfexpr e1 ce) (HiFP.type_of_hfexpr e2 ce) ->
      all [pred xy |
      ftype_equiv (xy.1) (xy.2)] (zip (map (fun a => HiFP.type_of_hfexpr a ce) (expand_expr e1 ce nil)) (map (fun a => HiFP.type_of_hfexpr a ce) (expand_expr e2 ce nil))).
  Proof.
    intros. 
    apply ftype_list_equiv_expand_expr. done.
    have Haux : (all2 (fun a : ftype => [eta ftype_equiv a]) [::] [::]) by done.
    move : (ftype_equiv_ftype_list_equiv _ _ nil nil H0 Haux).
    rewrite all2E => /andP [Hsz Heq]. done.
  Qed.
    
  (*   intros. rewrite all2E. *)
  (*   rewrite !size_expand_expr. *)
  (*   rewrite (ftype_equiv_ftype_list_len_ss _ _ H) eq_refl andTb. *)
  (*   move : ce H. *)
  (*   elim : e1; intros. *)
  (*   - rewrite /= in H; move : H. case Ht2 : (HiFP.type_of_hfexpr e2 ce) => [g||]; try done. *)
  (*     have Hg : (is_gtyp (HiFP.type_of_hfexpr e2 ce)) by rewrite Ht2. *)
  (*     rewrite (gtyp_expand_expr_1 e2 ce Hg)/=; intro; rewrite Ht2 H//. *)
  (*   - move : (gtyp_expand_expr_1 _ _ (ftype_equiv_is_gtyp_ss _ _ H0 (type_of_ucast_gtyp u h ce))) => He. *)
  (*     move : (gtyp_expand_expr_1 _ _ (type_of_ucast_gtyp u h ce)) => Hg. *)
  (*     rewrite (lock HiFP.type_of_hfexpr) He Hg/= -lock H0//. *)
  (*   - move : (gtyp_expand_expr_1 _ _ (ftype_equiv_is_gtyp_ss _ _ H0 (type_of_unop_gtyp e h ce))) => He. *)
  (*     move : (gtyp_expand_expr_1 _ _ (type_of_unop_gtyp e h ce)) => Hg. *)
  (*     rewrite (lock HiFP.type_of_hfexpr) He Hg/= -lock H0//. *)
  (*   - move : (gtyp_expand_expr_1 _ _ (ftype_equiv_is_gtyp_ss _ _ H1 (ftype_of_binop_gtyp e h h0 ce))) => He. *)
  (*     move : (gtyp_expand_expr_1 _ _ (ftype_of_binop_gtyp e h h0 ce)) => Hg. *)
  (*     rewrite (lock HiFP.type_of_hfexpr) He Hg/= -lock H1//. *)
  (*   -  (* assert (all (fun (z: ftype * ftype) => let (a, b):= z in ftype_equiv a b) (map (fun (z : HiFP.hfexpr * HiFP.hfexpr) => let (a, b) := z in(HiFP.type_of_hfexpr a ce, HiFP.type_of_hfexpr b ce)) (zip (expand_expr h1 ce nil) (expand_expr e2 ce nil)))). *) *)
  (*      (* rewrite all_map. rewrite /preim.  *) *)
  (*     rewrite /= in H2. *)
  (*     have Hmt : (ftype_equiv (HiFP.mux_types (HiFP.type_of_hfexpr h0 ce) (HiFP.type_of_hfexpr h1 ce)) (HiFP.type_of_hfexpr h0 ce)). admit. *)
  (*     have H12 : (ftype_equiv (HiFP.type_of_hfexpr h0 ce) (HiFP.type_of_hfexpr h1 ce)). admit. *)
  (*     move : (ftype_equiv_trans _ _ _ (ftype_equiv_comm _ _ H2) Hmt) => Hft. *)
  (*     rewrite /=.  *)
  (*     rewrite extzip_zip_ss; last admit. *)
  (*     admit. *)
  (*   - admit. *)
  (*   - rewrite /=. case h ; try rewrite zip_nil //. *)
  (*     elim => [a b]. rewrite /expand_eref. *)
  (* Admitted. *)
      
    
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
