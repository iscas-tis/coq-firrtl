(* This file contains some parts of ExpandWhens.v,
   and some edits based on how David sees the issue around Dec 2023/Jan 2024.

What does ExpandWhens need?
1. an implementation of ExpandWhens_fun : hfmodule -> option hfmodule
   This implementation heavily relies on
   ExpandBranch_fun : hfstmt_seq -> option (hfstmt_seq * CEP.t def_expr),
   a recursive function that translates a statement sequence
   to a list of declaration statements and a set of connection statements.
   The declaration statements are generally all component declarations;
   the set of connection statements indicates
   how every component input connector is connected.
2. a definition of module graph isomorphism
3. a correctness theorem, stating basically that the input and the output
   of ExpandWhens_fun are isomorphic.
*)

From Coq Require Import FunInd BinNat ZArith.
From mathcomp Require Import ssreflect ssrbool eqtype seq fintype ssrnat div ssrfun.
From simplssrlib Require Import SsrOrder Var FMaps.
From firrtl Require Import Firrtl Env HiEnv HiFirrtl ModuleGraph_simplified.

Section ExpandWhens.

(* Precondition of ExpandWhens: all types that appear in the module
   are fully inferred, i.e. they are ground types, have no implicit
   width, and there is no abstract Freset type. *)

Definition fully_inferred (gt : fgtyp) : bool :=
match gt with
| Fuint_implicit _
| Fsint_implicit _
| Freset => false
| _ => true
end.

Lemma fully_inferred_does_not_change :
forall (gt : fgtyp) (v : CEP.key) (vm : CEP.t vertex_type),
   fully_inferred gt ->
      match code_type_find_vm_widths (Gtyp gt) v vm with
      | Some (Gtyp gt', _) => gt = gt'
      | Some _ => False
      | None => True
      end.
Proof.
intros.
unfold fully_inferred in H.
destruct gt ; try discriminate H ; simpl code_type_find_vm_widths.
* destruct (CEP.find v vm) as [[newgt|newgt|newgt _ _ _|newgt|newgt]|] ; try trivial ;
  destruct newgt ; try trivial ; destruct (n == n0) eqn :Hnn0 ; try trivial ;
  move /eqP : Hnn0 => Hnn0 ; rewrite -Hnn0 ; reflexivity.
* destruct (CEP.find v vm) as [[newgt|newgt|newgt _ _ _|newgt|newgt]|] ; try trivial ;
  destruct newgt ; try trivial ; destruct (n == n0) eqn :Hnn0 ; try trivial ;
  move /eqP : Hnn0 => Hnn0 ; rewrite -Hnn0 ; reflexivity.
* destruct (CEP.find v vm) as [[newgt|newgt|newgt _ _ _|newgt|newgt]|] ; try trivial ;
  destruct newgt ; trivial.
* destruct (CEP.find v vm) as [[newgt|newgt|newgt _ _ _|newgt|newgt]|] ; try trivial ;
  destruct newgt ; trivial.
Qed.

Fixpoint ports_have_fully_inferred_ground_types (pp : seq HiFP.hfport) : bool :=
match pp with
| [::] => true
| Finput  _ (Gtyp gt) :: pp'
| Foutput _ (Gtyp gt) :: pp' => fully_inferred gt && ports_have_fully_inferred_ground_types pp'
| _ => false
end.

Definition tmap_has_fully_inferred_ground_types (tmap : CEP.t ftype) : Prop :=
forall (v : ProdVarOrder.T),
   match CEP.find v tmap return Prop with
   | Some (Gtyp gt) => fully_inferred gt
   | Some _ => False
   | None => True
   end.

Lemma ports_tmap_preserves_fully_inferred :
forall (vm : CEP.t vertex_type) (pp : seq HiFP.hfport),
   ports_have_fully_inferred_ground_types pp ->
      match ports_tmap pp vm with
      | Some pmap => tmap_has_fully_inferred_ground_types pmap
      | None => True
      end.
Proof.
induction pp.
* simpl ; intro ; intro.
  rewrite CEP.Lemmas.empty_o //.
* simpl ; intro.
  destruct a, f ; try done.
  1,2: move /andP : H => [H H0].
  1,2: specialize (IHpp H0).
  1,2: generalize (fully_inferred_does_not_change f s vm H);
          intro.
  1,2: destruct (code_type_find_vm_widths (Gtyp f) s vm) as [[[newgt| |] _]|] ; try done.
  1,2: rewrite -H1 ; clear H1 newgt.
  1,2: destruct (ports_tmap pp vm) ; last by trivial.
  1,2: destruct (CEP.find s t) ; first by trivial.
  1,2: intro.
  1,2: destruct (v == s) eqn: Hvs.
  1,3: rewrite CEP.Lemmas.find_add_eq ; first (by apply H) ;
       last by rewrite /HiFirrtl.PVM.SE.eq Hvs //.
  1,2: rewrite CEP.Lemmas.find_add_neq ; first (by apply IHpp) ;
       last by rewrite /HiFirrtl.PVM.SE.eq Hvs //.
Qed.

Fixpoint expr_has_fully_inferred_ground_types (expr : HiFP.hfexpr) : bool :=
match expr with
| Econst Freset _ => false
| Econst _ _ => true
| Ecast _ expr' => expr_has_fully_inferred_ground_types expr'
| Eprim_unop _ expr' => expr_has_fully_inferred_ground_types expr'
| Eprim_binop _ expr1 expr2 =>
       expr_has_fully_inferred_ground_types expr1
    &&
       expr_has_fully_inferred_ground_types expr2
| Emux cond expr1 expr2 =>
       expr_has_fully_inferred_ground_types cond
    &&
       expr_has_fully_inferred_ground_types expr1
    &&
       expr_has_fully_inferred_ground_types expr2
| Evalidif cond expr' =>
       expr_has_fully_inferred_ground_types cond
    &&
       expr_has_fully_inferred_ground_types expr'
| Eref ref => ref_has_fully_inferred_ground_types ref
end
with ref_has_fully_inferred_ground_types (ref : HiFP.href) : bool :=
match ref with
| Eid _ => true
| Esubfield ref' _
| Esubindex ref' _ => ref_has_fully_inferred_ground_types ref'
| Esubaccess ref' expr' =>
       ref_has_fully_inferred_ground_types ref'
    &&
       expr_has_fully_inferred_ground_types expr'
end.

Fixpoint stmt_has_fully_inferred_ground_types (s : HiFP.hfstmt) : bool :=
match s with
| Sskip => true
| Swire _ (Gtyp gt) => fully_inferred gt
| Swire _ _ => false
| Sreg _ r =>
    match type r, reset r with
    | Gtyp gt, NRst =>
           expr_has_fully_inferred_ground_types (clock r)
        &&
           fully_inferred gt
    | Gtyp gt, Rst rst_sig rst_val =>
           expr_has_fully_inferred_ground_types rst_sig
        &&
           expr_has_fully_inferred_ground_types rst_val
        &&
           expr_has_fully_inferred_ground_types (clock r)
        &&
           fully_inferred gt
    | _, _ => false
    end
| Smem _ m => if data_type m is Gtyp gt then fully_inferred gt else false
| Sinvalid r => ref_has_fully_inferred_ground_types r
| Sinst _ _ => false (* instances are not supported currently *)
| Snode _ e => expr_has_fully_inferred_ground_types e
| Sfcnct r e => ref_has_fully_inferred_ground_types r && expr_has_fully_inferred_ground_types e
| Swhen _ ss_true ss_false =>
       stmts_have_fully_inferred_ground_types ss_true
    &&
       stmts_have_fully_inferred_ground_types ss_false
end
with stmts_have_fully_inferred_ground_types (ss : HiFP.hfstmt_seq) : bool :=
match ss with
| Qnil => true
| Qcons s ss' =>
       stmt_has_fully_inferred_ground_types s
    &&
       stmts_have_fully_inferred_ground_types ss'
end.

Lemma stmts_have_fully_inferred_ground_types_cat :
forall (ss1 ss2 : HiFP.hfstmt_seq),
    stmts_have_fully_inferred_ground_types ss1 ->
        stmts_have_fully_inferred_ground_types ss2 ->
            stmts_have_fully_inferred_ground_types (Qcat ss1 ss2).
Proof.
induction ss1 ; first by simpl Qcat ; done.
intros.
simpl stmts_have_fully_inferred_ground_types.
simpl stmts_have_fully_inferred_ground_types in H.
move /andP : H => H.
rewrite (proj1 H) andTb.
apply IHss1 ; last by exact H0.
apply H.
Qed.

Lemma expr_preserves_fully_inferred :
forall scope : CEP.t ftype,
   tmap_has_fully_inferred_ground_types scope ->
      forall expr : HiFP.hfexpr,
         expr_has_fully_inferred_ground_types expr ->
            match type_of_expr expr scope return Prop with
            | Some (exist (Gtyp ft) _) => fully_inferred ft
            | Some _ => False
            | None => True
            end
with ref_preserves_fully_inferred :
forall scope : CEP.t ftype,
   tmap_has_fully_inferred_ground_types scope ->
      forall ref : HiFP.href,
         ref_has_fully_inferred_ground_types ref ->
            match type_of_ref ref scope return Prop with
            | Some (Gtyp ft) => fully_inferred ft
            | Some _ => False
            | None => True
            end.
Proof.
* clear expr_preserves_fully_inferred.
  induction expr ; simpl type_of_expr ; simpl expr_has_fully_inferred_ground_types ; intro.
  + destruct f ; done.
  + specialize (IHexpr H0) ; clear H0.
    destruct (type_of_expr expr scope) as [[[gt| |] _]|]; try done ;
    destruct u ; try done ;
    destruct gt ; done.
  + specialize (IHexpr H0) ; clear H0.
    destruct (type_of_expr expr scope) as [[[gt| |] _]|] ; try done ;
    destruct e ; try done ; destruct gt ; try done.
    - 1,2: destruct (n0 <= n < n1) ; by done.
    - 1,2,3,4: destruct (n <= n0) ; by done.
  + move /andP : H0 => [H0 H1].
    specialize (IHexpr1 H0) ; clear H0.
    specialize (IHexpr2 H1) ; clear H1.
    destruct (type_of_expr expr1 scope) as [[[gt1| |] _]|] ; try done ;
    destruct (type_of_expr expr2 scope) as [[[gt2| |] _]|] ; try done ;
    destruct e ; try done ;
    destruct gt1 ; try done ; destruct gt2 ; by done.
  + move /andP : H0 => [/andP [H0 H1] H2].
    specialize (IHexpr1 H0) ; clear H0.
    specialize (IHexpr2 H1) ; clear H1.
    specialize (IHexpr3 H2) ; clear H2.
    destruct (type_of_expr expr1 scope) as [[[[[|[|]]| | | | | |]| |] _]|] ; try done.
    destruct (type_of_expr expr2 scope) as [[[gt2| |] p2]|] ; try done ;
    destruct (type_of_expr expr3 scope) as [[[gt3| |] p3]|] ; try done ;
    unfold ftype_mux ; simpl ftype_mux'.
    destruct gt2, gt3 ; by done.
  + move /andP : H0 => [H0 H1].
    specialize (IHexpr1 H0) ; clear H0.
    specialize (IHexpr2 H1) ; clear H1.
    destruct (type_of_expr expr1 scope) as [[[[[|[|]]| | | | | |]| |] _]|] ; by done.
  + specialize (ref_preserves_fully_inferred scope H h H0).
    destruct (type_of_ref h scope) as [[gt| |]|]; try done.
    destruct gt ; by done.
* clear ref_preserves_fully_inferred.
  induction ref ; simpl type_of_ref ; simpl ref_has_fully_inferred_ground_types ; intro.
  + by apply H.
  + specialize (IHref H0).
    destruct (type_of_ref ref scope) as [[| |]|] ; by done.
  + specialize (IHref H0).
    destruct (type_of_ref ref scope) as [[| |]|] ; by done.
  + simpl ; trivial.
Qed.

Lemma stmt_tmap_preserves_fully_inferred :
forall (vm : CEP.t vertex_type) (tmap scope : CEP.t ftype) (s : HiFP.hfstmt),
   stmt_has_fully_inferred_ground_types s ->
   tmap_has_fully_inferred_ground_types tmap ->
   CEP.submap scope tmap ->
      match stmt_tmap (tmap, scope) s vm with
      | Some (tmap', scope') => tmap_has_fully_inferred_ground_types tmap'
      | _ => True
      end
with stmts_tmap_preserves_fully_inferred :
forall (vm : CEP.t vertex_type) (ss : HiFP.hfstmt_seq) (tmap scope : CEP.t ftype),
   stmts_have_fully_inferred_ground_types ss ->
   tmap_has_fully_inferred_ground_types tmap ->
   CEP.submap scope tmap ->
      match stmts_tmap (tmap, scope) ss vm with
      | Some (tmap', scope') => tmap_has_fully_inferred_ground_types tmap'
      | _ => True
      end.
Proof.
* clear stmt_tmap_preserves_fully_inferred.
  destruct s ; intros ; try done.
  + (* Swire *)
    simpl stmt_tmap.
    destruct (CEP.find s tmap) ; first by trivial.
    unfold stmt_has_fully_inferred_ground_types in H.
    destruct f as [gt| |]; try done.
    generalize (fully_inferred_does_not_change gt s vm H) ;
          intro.
    destruct (code_type_find_vm_widths (Gtyp gt) s vm) as [[[newgt| |] _]|] ;
        try by done.
    rewrite -H2 ; clear H2 newgt.
    intro.
    destruct (v == s) eqn: Hvs ; first by rewrite CEP.Lemmas.find_add_eq //.
    rewrite CEP.Lemmas.find_add_neq // ; last by rewrite /HiFirrtl.PVM.SE.eq Hvs //.
    by apply H0.
  + (* Sreg *)
    simpl stmt_tmap.
    destruct (CEP.find s tmap) ; first by trivial.
    destruct (type_of_expr (clock h) scope) ; last by trivial.
    unfold stmt_has_fully_inferred_ground_types in H.
    destruct (type h) as [gt| |]; try done.
    generalize (fully_inferred_does_not_change gt s vm) ;
          intro.
    destruct (code_type_find_vm_widths (Gtyp gt) s vm) as [[[newgt| |] _]|] ;
        destruct (reset h) ;
        move /andP : H => [H H'] ;
        specialize (H2 H') ;
        try by done.
    1,2: rewrite -H2 ; clear H2 newgt.
    2: destruct (type_of_expr h0 scope) ; last by trivial.
    2: destruct (type_of_expr h1 scope) ; last by trivial.
    1,2: intro.
    1,2: destruct (v == s) eqn: Hvs ; first by rewrite CEP.Lemmas.find_add_eq //.
    1,2: rewrite CEP.Lemmas.find_add_neq ; last by rewrite /HiFirrtl.PVM.SE.eq Hvs //.
    1,2: by apply H0.
  + (* Snode *)
    simpl stmt_tmap.
    destruct (CEP.find s tmap) ; first by trivial.
    assert (tmap_has_fully_inferred_ground_types scope).
          intro.
          specialize (H1 v).
          destruct (CEP.find v scope) ; try done.
          specialize (H0 v).
          rewrite (H1 f Logic.eq_refl) in H0.
          by exact H0.
    simpl stmt_has_fully_inferred_ground_types in H.
    generalize (expr_preserves_fully_inferred scope H2 h H) ; intro.
    destruct (type_of_expr h scope) as [[newt _]|] ; last by trivial.
    intro.
    destruct (v == s) eqn: Hvs ; first by rewrite CEP.Lemmas.find_add_eq //.
    rewrite CEP.Lemmas.find_add_neq ; last by rewrite /HiFirrtl.PVM.SE.eq Hvs //.
    by apply H0.
  + (* Sfcnct *)
    simpl stmt_tmap.
    simpl stmt_has_fully_inferred_ground_types in H.
    destruct (type_of_ref h scope) ; last by done.
    destruct (type_of_expr h0 scope) ; last by done.
    by exact H0.
  + (* Sinvalid *)
    simpl stmt_tmap.
    destruct (type_of_ref h scope) ; last by done.
    by exact H0.
  + (* Swhen *)
    rename h into cond ; rename h0 into ss_true ; rename h1 into ss_false.
    simpl stmt_tmap.
    destruct (type_of_expr cond scope) ; last by done.
    simpl stmt_has_fully_inferred_ground_types in H.
    move /andP : H => [Ht Hf].
    generalize (stmts_tmap_preserves_fully_inferred vm ss_true tmap scope Ht H0 H1) ;
          intro.
    generalize (stmts_submap vm ss_true tmap scope H1) ;
          intro.
    destruct (stmts_tmap (tmap, scope) ss_true vm) as [[tmap_true scope_true]|] ; try done.
    specialize (stmts_tmap_preserves_fully_inferred vm ss_false tmap_true scope Hf H).
    destruct (stmts_tmap (tmap_true, scope) ss_false vm) as [[tmap_false _]|] ; try done.
    apply stmts_tmap_preserves_fully_inferred.
    by apply (CEP.Lemmas.submap_trans H1), H2.
* clear stmts_tmap_preserves_fully_inferred.
  induction ss ; intros ; try done.
  simpl stmts_tmap.
  simpl in H ; move /andP : H => [H H'].
  specialize (stmt_tmap_preserves_fully_inferred vm tmap scope h H H0 H1).
  generalize (stmt_submap vm h tmap scope H1) ;
      intro.
  destruct (stmt_tmap (tmap, scope) h vm) as [[tmap' scope']|] ; try done.
  specialize (IHss tmap' scope' H' stmt_tmap_preserves_fully_inferred (proj1 H2)).
  destruct (stmts_tmap (tmap', scope') ss vm) as [[tmap'' _]|] ; by done.
Qed.

Lemma component_preserves_fully_inferred :
forall (s : HiFP.hfstmt),
    stmt_has_fully_inferred_ground_types s ->
        stmts_have_fully_inferred_ground_types (component_stmt_of s)
with components_preserves_fully_inferred :
forall (ss : HiFP.hfstmt_seq),
    stmts_have_fully_inferred_ground_types ss ->
        stmts_have_fully_inferred_ground_types (component_stmts_of ss).
Proof.
* clear component_preserves_fully_inferred.
  induction s ; simpl ; intros ; try done ; try rewrite andbT //.
  rename h into cond ; rename h0 into ss_true ; rename h1 into ss_false.
  move /andP : H => [Ht Hf].
  apply components_preserves_fully_inferred in Ht ;
  apply components_preserves_fully_inferred in Hf.
  apply stmts_have_fully_inferred_ground_types_cat ; assumption.
* clear components_preserves_fully_inferred.
  induction ss ; simpl ; intros ; try done.
  move /andP : H => H.
  apply stmts_have_fully_inferred_ground_types_cat.
  * apply component_preserves_fully_inferred, H.
  * apply IHss, H.
Qed.

Definition module_has_fully_inferred_ground_types (m : HiFP.hfmodule) : bool :=
match m with
| FInmod _ pp ss
| FExmod _ pp ss =>
       ports_have_fully_inferred_ground_types pp
    &&
       stmts_have_fully_inferred_ground_types ss
end.

(* Some helper properties of Sem *)
Lemma fully_inferred_makes_Sem_frag_stmts_unique :
forall (ss : HiFP.hfstmt_seq) (vm_old1 vm_old2 vm_new1 vm_new2 : CEP.t vertex_type)
       (ct_old1 ct_old2 ct_new1 ct_new2 : CEP.t def_expr) (tmap : CEP.t ftype),
    stmts_have_fully_inferred_ground_types ss ->
    tmap_has_fully_inferred_ground_types tmap ->
    CEP.Equal vm_old1 vm_old2 /\ CEP.Equal ct_old1 ct_old2 ->
    Sem_frag_stmts vm_old1 ct_old1 ss vm_new1 ct_new1 tmap ->
    Sem_frag_stmts vm_old2 ct_old2 ss vm_new2 ct_new2 tmap ->
        CEP.Equal vm_new1 vm_new2 /\ CEP.Equal ct_new1 ct_new2
with fully_inferred_makes_Sem_frag_stmt_unique :
forall (s : HiFP.hfstmt) (vm_old1 vm_old2 vm_new1 vm_new2 : CEP.t vertex_type)
       (ct_old1 ct_old2 ct_new1 ct_new2 : CEP.t def_expr) (tmap : CEP.t ftype),
    stmt_has_fully_inferred_ground_types s ->
    tmap_has_fully_inferred_ground_types tmap ->
    CEP.Equal vm_old1 vm_old2 /\ CEP.Equal ct_old1 ct_old2 ->
    Sem_frag_stmt vm_old1 ct_old1 s vm_new1 ct_new1 tmap ->
    Sem_frag_stmt vm_old2 ct_old2 s vm_new2 ct_new2 tmap ->
        CEP.Equal vm_new1 vm_new2 /\ CEP.Equal ct_new1 ct_new2.
Proof.
* clear fully_inferred_makes_Sem_frag_stmts_unique.
  induction ss as [|s ss] ; simpl Sem_frag_stmts.
  + split.
    - apply CEP.Lemmas.Equal_trans with (m' := vm_old2) ; last by apply H3.
      apply CEP.Lemmas.Equal_trans with (m' := vm_old1) ; last by apply H1.
      by apply CEP.Lemmas.Equal_sym, H2.
    - apply CEP.Lemmas.Equal_trans with (m' := ct_old2) ; last by apply H3.
      apply CEP.Lemmas.Equal_trans with (m' := ct_old1) ; last by apply H1.
      by apply CEP.Lemmas.Equal_sym, H2.
  + intros.
    simpl stmts_have_fully_inferred_ground_types in H ; move /andP : H => H.
    destruct H2 as [vm_temp1 [ct_temp1 H2]].
    destruct H3 as [vm_temp2 [ct_temp2 H3]].
    specialize (fully_inferred_makes_Sem_frag_stmt_unique s
                vm_old1 vm_old2 vm_temp1 vm_temp2
                ct_old1 ct_old2 ct_temp1 ct_temp2 tmap
                (proj1 H) H0 H1 (proj1 H2) (proj1 H3)).
    specialize (IHss vm_temp1 vm_temp2 vm_new1 vm_new2
                     ct_temp1 ct_temp2 ct_new1 ct_new2 tmap
                     (proj2 H) H0 fully_inferred_makes_Sem_frag_stmt_unique
                     (proj2 H2) (proj2 H3)).
    exact IHss.
* clear fully_inferred_makes_Sem_frag_stmt_unique.
  destruct s ; simpl Sem_frag_stmt.
  + (* Sskip *)
    split.
    - rewrite -(proj1 H2) -(proj1 H3) ; by apply H1.
    - rewrite -(proj2 H2) -(proj2 H3) ; by apply H1.
  + (* Swire *)
    intros.
    (*simpl stmt_has_fully_inferred_ground_types in H.*)
    (*destruct f as [gt| |] ; try by done.*)
    specialize (H0 s).
    destruct (CEP.find s tmap) as [[gt'| |]|] ; try by done.
    rewrite /list_rhs_type_p /size_of_ftype add1n in H2, H3.
    split ; intro.
    - destruct (y == s) eqn: Hys ; move /eqP : Hys => Hys.
      * destruct H2 as [H2 _] ; destruct H3 as [H3 _].
        specialize (H2 0) ; specialize (H3 0).
        rewrite /List.nth_error add0n nat_of_binK -surjective_pairing in H2, H3.
        by rewrite Hys (proj2 H2) (proj2 H3) //.
      * destruct H2 as [_ [H2 _]] ; destruct H3 as [_ [H3 _]].
        specialize (H2 y.1 y.2) ; specialize (H3 y.1 y.2).
        rewrite -surjective_pairing in H2, H3.
        destruct (N.eq_dec y.1 s.1) ;
              last by (rewrite -H2 ; last (by left ; exact n) ;
                       rewrite -H3 ; last (by left ; exact n) ;
                       apply H1).
        (* destruct (N.compare_spec y.2 s.2). --- Problem of this approach: the ``not equal'' cases are in %num scope, and I do not know how to change the scope *)
        destruct (Nat.compare_spec y.2 s.2) ;
              first (by apply (can_inj nat_of_binK) in H4 ;
                        generalize (injective_projections y s e H4) ;
                        contradiction) ;
              move /ltP : H4 => H4.
        + rewrite -H2 ; last (by right ; left ; exact H4) ;
          rewrite -H3 ; last (by right ; left ; exact H4).
          by apply H1.
        + rewrite -H2 ; last (by right ; right ; exact H4) ;
          rewrite -H3 ; last (by right ; right ; exact H4).
          by apply H1.
    - destruct (y == s) eqn: Hys ; move /eqP : Hys => Hys.
      * destruct H2 as [_ [_ [_ H2]]] ; destruct H3 as [_ [_ [_ H3]]].
        specialize (H2 0 (ltn0Sn 0)) ; specialize (H3 0 (ltn0Sn 0)).
        rewrite add0n nat_of_binK -surjective_pairing in H2, H3.
        by rewrite Hys H2 H3 //.
      * destruct H2 as [_ [_ [H2 _]]] ; destruct H3 as [_ [_ [H3 _]]].
        specialize (H2 y.1 y.2) ; specialize (H3 y.1 y.2).
        rewrite -surjective_pairing in H2, H3.
        destruct (N.eq_dec y.1 s.1) ;
              last by (rewrite -H2 ; last (by left ; exact n) ;
                       rewrite -H3 ; last (by left ; exact n) ;
                       apply H1).
        (* destruct (N.compare_spec y.2 s.2). --- Problem of this approach: the ``not equal'' cases are in %num scope, and I do not know how to change the scope *)
        destruct (Nat.compare_spec y.2 s.2) ;
              first (by apply (can_inj nat_of_binK) in H4 ;
                        generalize (injective_projections y s e H4) ;
                        contradiction) ;
              move /ltP : H4 => H4.
        + rewrite -H2 ; last (by right ; left ; exact H4) ;
          rewrite -H3 ; last (by right ; left ; exact H4).
          by apply H1.
        + rewrite -H2 ; last (by right ; right ; exact H4) ;
          rewrite -H3 ; last (by right ; right ; exact H4).
          by apply H1.
  + (* Sreg -- should be similar to Swire *)
    admit.
  + (* Smem -- not implemented *)
    simpl ; by done.
  + (* Sinst -- not implemented *)
    simpl ; by done.
  + (* Snode -- should be similar to Swire *)
    admit.
  + (* Sfcnct *)
    intros.
    destruct h0.
    - (* Econst *)
      simpl in H.
      split ;
            first (by destruct H2 as [H2 _] ; destruct H3 as [H3 _] ;
                      apply CEP.Lemmas.Equal_trans with (m' := vm_old2) ; last (by exact H3) ;
                      apply CEP.Lemmas.Equal_trans with (m' := vm_old1) ; last (by apply H1) ;
                      apply CEP.Lemmas.Equal_sym, H2).
      destruct H2 as [_ H2] ; destruct H3 as [_ H3].
      generalize (list_lhs_ref_p_size tmap h) ; intro.
      generalize (list_lhs_ref_p_type tmap h) ; intro.
      destruct (type_of_ref h tmap) as [ft_ref|] ; last by contradiction H2.
      destruct (type_of_expr (Econst ProdVarOrder.T f b) tmap) as [[ft_expr _]|] ; last by contradiction H2.
      destruct H2 as [H6 H2] ; destruct H3 as [_ H3].
      apply connect_type_compatible_size in H6.
      destruct (list_lhs_ref_p h tmap) as [[input_list ft]|] ; last by contradiction H2.
      rewrite H5 -H4 in H6 ; clear ft H4 H5.
      generalize (list_rhs_expr_p_size ft_expr (Econst ProdVarOrder.T f b)) ; intro.
      destruct (list_rhs_expr_p (Econst ProdVarOrder.T f b) ft_expr) as [expr_list|] ; last by contradiction H2.
      rewrite -H6 in H4 ; clear H6.
      intro.
      destruct (y \in input_list) eqn: Hylist ;
            last by (destruct H2 as [_ H2] ; destruct H3 as [_ H3] ;
                     specialize (H2 y) ; specialize (H3 y) ;
                     rewrite Hylist in H2, H3 ;
                     rewrite -H2 -H3 ; apply H1).
      destruct H2 as [H2 _] ; destruct H3 as [H3 _].
      rewrite -index_mem in Hylist.
      move /ltP : Hylist => Hylist.
      generalize (proj2 (List.nth_error_Some input_list (index y input_list)) Hylist) ; intro.
      specialize (H2 (index y input_list)) ; specialize (H3 (index y input_list)).
      destruct (List.nth_error input_list (index y input_list)) as [ic|] eqn: H6 ; last by contradict H5.
      clear H5.
      replace ic with y in H2, H3, H6
            by (clear -H6 ;
                induction input_list ; first (by simpl in H6 ; done) ;
                simpl in H6 ;
                destruct (a == y) eqn: Hay ; simpl in H6 ;
                      last (by apply IHinput_list, H6) ;
                move /eqP : Hay => Hay ; rewrite Hay in H6 ;
                symmetry ; injection H6 ; done).
      clear ic.
      rewrite -H4 in Hylist ; apply List.nth_error_Some in Hylist.
      destruct (List.nth_error expr_list (index y input_list)) as [ex|] ; last by contradict Hylist.
      by rewrite (proj2 H2) (proj2 H3) //.
    - (* Ecast -- other expressions should be similar... *)
      admit.
    - (* Eprim_unop *)
      admit.
    - (* Eprim_binop *)
      admit.
    - (* Emux *)
      admit.
    - (* Evalidif *)
      admit.
    - (* Eref needs a slightly different treatment because it's bidirectional *)
      admit.
  + (* Sinvalid should be similar to Sfcnct but simpler *)
    admit.
  + (* Swhen -- use the induction hypotheses *)
    admit.
Admitted.


Lemma Sem_frag_stmts_Equal :
forall (ss : HiFP.hfstmt_seq) (vm_old1 vm_old2 : CEP.t vertex_type) (ct_old1 ct_old2 : CEP.t def_expr) (vm_new1 vm_new2 : CEP.t vertex_type) (ct_new1 ct_new2 : CEP.t def_expr) (tmap1 tmap2 : CEP.t ftype),
    CEP.Equal vm_old1 vm_old2 ->
    CEP.Equal ct_old1 ct_old2 ->
    CEP.Equal vm_new1 vm_new2 ->
    CEP.Equal ct_new1 ct_new2 ->
    CEP.Equal tmap1 tmap2 ->
    Sem_frag_stmts vm_old1 ct_old1 ss vm_new1 ct_new1 tmap1 ->
    Sem_frag_stmts vm_old2 ct_old2 ss vm_new2 ct_new2 tmap2
with Sem_frag_stmt_Equal :
forall (s : HiFP.hfstmt) (vm_old1 vm_old2 : CEP.t vertex_type) (ct_old1 ct_old2 : CEP.t def_expr) (vm_new1 vm_new2 : CEP.t vertex_type) (ct_new1 ct_new2 : CEP.t def_expr) (tmap1 tmap2 : CEP.t ftype),
    CEP.Equal vm_old1 vm_old2 ->
    CEP.Equal ct_old1 ct_old2 ->
    CEP.Equal vm_new1 vm_new2 ->
    CEP.Equal ct_new1 ct_new2 ->
    CEP.Equal tmap1 tmap2 ->
    Sem_frag_stmt vm_old1 ct_old1 s vm_new1 ct_new1 tmap1 ->
    Sem_frag_stmt vm_old2 ct_old2 s vm_new2 ct_new2 tmap2.
Proof.
* clear Sem_frag_stmts_Equal.
  induction ss ; simpl Sem_frag_stmts.
  + split.
    - apply CEP.Lemmas.Equal_trans with (m' := vm_new1) ; last by exact H1.
      apply CEP.Lemmas.Equal_trans with (m' := vm_old1) ; last by apply H4.
      apply CEP.Lemmas.Equal_sym ; exact H.
    - apply CEP.Lemmas.Equal_trans with (m' := ct_new1) ; last by exact H2.
      apply CEP.Lemmas.Equal_trans with (m' := ct_old1) ; last by apply H4.
      apply CEP.Lemmas.Equal_sym ; exact H0.
  + intros.
    destruct H4 as [vm' [ct' H4]].
    exists vm', ct'.
    split ;
          first by apply (Sem_frag_stmt_Equal h vm_old1 vm_old2 ct_old1 ct_old2 vm' vm' ct' ct' tmap1 tmap2) ;
                   try assumption ; try apply CEP.Lemmas.Equal_refl ; apply H4.
    by apply (IHss vm' vm' ct' ct' vm_new1 vm_new2 ct_new1 ct_new2 tmap1 tmap2) ;
          try assumption ; try apply CEP.Lemmas.Equal_refl ; apply H4.
* clear Sem_frag_stmt_Equal.
  destruct s ; simpl ; intros ; try by done.
  + (* Sskip *)
    split.
    - apply CEP.Lemmas.Equal_trans with (m' := vm_new1) ; last by exact H1.
      apply CEP.Lemmas.Equal_trans with (m' := vm_old1) ; last by apply H4.
      by apply CEP.Lemmas.Equal_sym, H.
    - apply CEP.Lemmas.Equal_trans with (m' := ct_new1) ; last by exact H2.
      apply CEP.Lemmas.Equal_trans with (m' := ct_old1) ; last by apply H4.
      by apply CEP.Lemmas.Equal_sym, H0.
  + (* Swire *)
    specialize (H3 s).
    destruct (CEP.find s tmap1) ; last by contradiction H4.
    rewrite -H3 ; clear tmap1 tmap2 H3.
    split.
    - destruct H4 as [H4 _].
      intro ; specialize (H4 n).
      destruct (List.nth_error (list_rhs_type_p f0) n) ; last by trivial.
      by rewrite -H -H1 ; exact H4.
    destruct H4 as [_ H4] ; split.
    - destruct H4 as [H4 _].
      intro ; intro.
      by rewrite -H -H1 ; apply H4.
    destruct H4 as [_ H4] ; split.
    - destruct H4 as [H4 _].
      intro ; intro.
      by rewrite -H0 -H2 ; apply H4.
    - destruct H4 as [_ H4].
      intro.
      by rewrite -H2 ; apply H4.
  + (* Sreg *)
    generalize (H3 s) ; intro.
    destruct (CEP.find s tmap1) ; last by contradiction H4.
    rewrite -H5 ; clear H5.
    split.
    - destruct H4 as [H4 _].
      destruct (reset h) ; first by exact H4.
      rewrite (type_of_expr_Equal h0 tmap1 tmap2 H3) in H4.
      rewrite (type_of_expr_Equal h1 tmap1 tmap2 H3) in H4.
      by exact H4.
    destruct H4 as [_ H4] ; split.
    - destruct H4 as [H4 _].
      intro ; specialize (H4 n).
      destruct (List.nth_error (list_rhs_type_p f) n) ; last by trivial.
      rewrite -H -H1.
      destruct (reset h) ; first by exact H4.
      rewrite (type_of_expr_Equal h0 tmap1 tmap2 H3) in H4.
      by exact H4.
    destruct H4 as [_ H4] ; split.
    - destruct H4 as [H4 _].
      rewrite (type_of_expr_Equal (clock h) tmap1 tmap2 H3) in H4.
      by exact H4.
    destruct H4 as [_ H4] ; split.
    - destruct H4 as [H4 _].
      destruct (match f with
                | Gtyp _ => Some [:: Eref (Eid (var:=ProdVarOrder.T) s)]
                | _ => list_rhs_ref_p (Eid (var:=ProdVarOrder.T) s) f
                end) eqn: Hf ; rewrite Hf ; rewrite Hf in H4 ; clear Hf ;
            last by contradiction H4.
      intro ; specialize (H4 n).
      destruct (List.nth_error l n) eqn: Hl ; rewrite Hl ; rewrite Hl in H4 ; clear Hl ;
            last by trivial.
      by rewrite -H2 ; exact H4.
    destruct H4 as [_ H4] ; split.
    - destruct H4 as [H4 _].
      intro ; intro.
      by rewrite -H -H1 ; apply H4.
    - destruct H4 as [_ H4].
      intro ; intro.
      by rewrite -H0 -H2 ; apply H4.
  + (* Snode *)
    rewrite (type_of_expr_Equal h tmap1 tmap2 H3) in H4.
    destruct (type_of_expr h tmap2) as [[newft _]|] ; last by contradiction H4.
    clear tmap1 tmap2 H3.
    split.
    - destruct H4 as [H4 _].
      intro ; specialize (H4 n).
      destruct (List.nth_error (list_rhs_type_p newft) n) ; last by trivial.
      by rewrite -H -H1 ; exact H4.
    destruct H4 as [_ H4] ; split.
    - destruct H4 as [H4 _].
      intro ; intro.
      by rewrite -H -H1 ; apply H4.
    destruct H4 as [_ H4] ; split.
    - destruct H4 as [H4 _].
      intro ; intro.
      by rewrite -H0 -H2 ; apply H4.
    - destruct H4 as [_ H4].
      destruct (list_rhs_expr_p h newft) ; last by contradiction H4.
      intro.
      by rewrite -H2 ; apply H4.
  + (* Sfcnct *)
    admit.
  + (* Sinvalid *)
    admit.
  + (* Swhen *)
    admit.
Admitted.

Lemma Sem_frag_stmts_component_Equal :
forall (ss : HiFP.hfstmt_seq) (vm_old1 vm_old2 : CEP.t vertex_type) (ct_old1 ct_old2 : CEP.t def_expr) (vm_new1 vm_new2 : CEP.t vertex_type) (ct_new : CEP.t def_expr) (tmap1 tmap2 : CEP.t ftype),
    vm_and_ct_compatible vm_old1 ct_old1 ->
    vm_and_ct_compatible vm_old2 ct_old2 ->
    CEP.Equal vm_old1 vm_old2 ->
    CEP.Equal vm_new1 vm_new2 ->
    CEP.Equal tmap1 tmap2 ->
    Sem_frag_stmts vm_old1 ct_old1 (component_stmts_of ss) vm_new1 ct_new tmap1 ->
    Sem_frag_stmts vm_old2 ct_old2 (component_stmts_of ss) vm_new2 (extend_map_with ct_old2 ct_new) tmap2
with Sem_frag_stmt_component_Equal :
forall (s : HiFP.hfstmt) (vm_old1 vm_old2 : CEP.t vertex_type) (ct_old1 ct_old2 : CEP.t def_expr) (vm_new1 vm_new2 : CEP.t vertex_type) (ct_new : CEP.t def_expr) (tmap1 tmap2 : CEP.t ftype),
    vm_and_ct_compatible vm_old1 ct_old1 ->
    vm_and_ct_compatible vm_old2 ct_old2 ->
    CEP.Equal vm_old1 vm_old2 ->
    CEP.Equal vm_new1 vm_new2 ->
    CEP.Equal tmap1 tmap2 ->
    Sem_frag_stmts vm_old1 ct_old1 (component_stmt_of s) vm_new1 ct_new tmap1 ->
    Sem_frag_stmts vm_old2 ct_old2 (component_stmt_of s) vm_new2 (extend_map_with ct_old2 ct_new) tmap2.
Proof.
* clear Sem_frag_stmts_component_Equal.
  induction ss ; simpl ; intros.
  + split.
    - apply (CEP.Lemmas.Equal_trans (CEP.Lemmas.Equal_sym H1)).
      exact (CEP.Lemmas.Equal_trans (proj1 H4) H2).
    - intro ; rewrite /extend_map_with CEP.Lemmas.map2_1bis //.
      specialize (H0 y).
      destruct (CEP.find y ct_old2) ; first by reflexivity.
      specialize (H y).
      specialize (H1 y).
      specialize (proj2 H4 y) ; intro.
      destruct (CEP.find y vm_old2) as [[]|] ; try (by contradiction H0) ;
            rewrite H1 H5 in H ; by rewrite H //.
  + apply Sem_frag_stmts_cat.
    apply Sem_frag_stmts_cat in H4.
    destruct H4 as [vm_temp [ct_temp [H4 H5]]].
    exists vm_temp, (extend_map_with ct_old2 ct_temp).
    split.
    - by apply (Sem_frag_stmt_component_Equal h vm_old1 vm_old2 ct_old1 ct_old2 vm_temp vm_temp ct_temp tmap1 tmap2
                                              H H0 H1 (CEP.Lemmas.Equal_refl _) H3 H4).
    - generalize (Sem_frag_stmts_compatible (component_stmt_of h) vm_old1 ct_old1 vm_temp ct_temp tmap1
                                            H4) ; intro.
      destruct H6 as [H6 [_ H7]] ; specialize (H7 H).
      generalize (Sem_frag_stmts_component ss vm_temp ct_temp vm_new1 ct_new tmap1 H7 H5) ; intro.
      generalize (extend_map_with_submap ct_old2 ct_temp ct_new H8) ; intro.
      apply Sem_frag_stmts_Equal with (vm_old1 := vm_temp) (ct_old1 := extend_map_with ct_old2 ct_temp)
                                      (vm_new1 := vm_new2) (ct_new1 := extend_map_with (extend_map_with ct_old2 ct_temp) ct_new)
                                      (tmap1 := tmap2) ;
            try assumption ; try apply CEP.Lemmas.Equal_refl.
      apply IHss with (vm_old1 := vm_temp) (ct_old1 := ct_temp)
                      (vm_new1 := vm_new1)
                      (tmap1 := tmap1) ;
            try assumption ; try apply CEP.Lemmas.Equal_refl.
      generalize (Sem_frag_stmt_component h vm_old1 ct_old1 vm_temp ct_temp tmap1 H H4) ; intro.
      intro.
      specialize (H0 v) ; specialize (H1 v) ; specialize (H6 v) ;
            rewrite H1 in H6.
      rewrite CEP.Lemmas.map2_1bis //.
      destruct (CEP.find v vm_old2) as [[]|] ;
            try (by rewrite H0 ; apply H7) ;
            by (rewrite (H6 _ Logic.eq_refl) ;
                    destruct (CEP.find v ct_old2) ;
                          first (by discriminate) ;
                          last (by contradiction H0)).
* clear Sem_frag_stmt_component_Equal.
  destruct s ; intros.
  + (* Sskip *)
    simpl ; split ;
        first by apply (CEP.Lemmas.Equal_trans (CEP.Lemmas.Equal_sym H1)),
                       (CEP.Lemmas.Equal_trans (proj1 H4)), H2.
    intro ; rewrite CEP.Lemmas.map2_1bis //.
    specialize (H0 y).
    destruct (CEP.find y ct_old2) ; first by reflexivity.
    specialize (H1 y).
    destruct (CEP.find y vm_old2) as [[]|] ;
          try (by contradiction H0) ;
          by (specialize (H y) ; rewrite H1 in H ;
              specialize (proj2 H4 y) ; clear H4 ; intro H4 ;
              rewrite -H4 H //).
  + (* Swire *)
    simpl ; simpl in H4.
    destruct H4 as [vm' [ct' [H4 [H5 H6]]]].
    exists vm_new2, (extend_map_with ct_old2 ct_new).
    split ; last by split ; apply CEP.Lemmas.Equal_refl.
    apply (CEP.Lemmas.Equal_trans) with (2 := H2) in H5.
    clear H2 vm_new1.
    specialize (H3 s).
    destruct (CEP.find s tmap1) ; last by contradiction H4.
    rewrite -H3 ; clear H3.
    split.
    - destruct H4 as [H4 _].
      intro ; specialize (H4 n).
      destruct (List.nth_error (list_rhs_type_p f0) n) ; last by trivial.
      rewrite -H1 -H5.
      exact H4.
    split.
    - destruct H4 as [_ [H4 _]].
      intros v0 n0 ; specialize (H4 v0 n0).
      rewrite -H1 -H5.
      exact H4.
    split.
    - destruct H4 as [_ [_ [H4 _]]].
      intros ; specialize (H4 v0 n0 H2).
      rewrite CEP.Lemmas.map2_1bis // -H6.
      specialize (H0 (v0, n0)).
      destruct (CEP.find (v0, n0) ct_old2) ; first by reflexivity.
      specialize (H1 (v0, n0)).
      destruct (CEP.find (v0, n0) vm_old2) as [[]|] ;
            try (by contradiction H0) ;
            by (specialize (H (v0, n0)) ;
                rewrite H1 in H ;
                rewrite -H4 H //).
    - destruct H4 as [H7 [_ [_ H4]]].
      intros ; specialize (H4 n0 H2) ; specialize (H7 n0).
      rewrite -(list_rhs_type_p_size f0) in H2.
      move /ltP : H2 => H2.
      generalize (proj2 (List.nth_error_Some (list_rhs_type_p f0) n0) H2) ; intro.
      destruct (List.nth_error (list_rhs_type_p f0) n0) ; last by contradiction H3.
      rewrite H1 in H7.
      specialize (H0 (s.1, bin_of_nat (n0 + s.2))).
      rewrite (proj1 H7) in H0.
      rewrite CEP.Lemmas.map2_1bis // H0 -H6 H4 //.
  + (* Sreg, should be similar to Swire *)
    admit.
  + (* Smem, TBD *)
    simpl in H4.
    destruct H4 as [_ [_ [H4 _]]].
    contradiction H4.
  + (* Sinst, TBD *)
    simpl in H4.
    destruct H4 as [_ [_ [H4 _]]].
    contradiction H4.
  + (* Snode, should be similar to Swire *)
    admit.
  + (* Sfcnct, similar to Sskip *)
    simpl ; split ;
        first by apply (CEP.Lemmas.Equal_trans (CEP.Lemmas.Equal_sym H1)),
                       (CEP.Lemmas.Equal_trans (proj1 H4)), H2.
    intro ; rewrite CEP.Lemmas.map2_1bis //.
    specialize (H0 y).
    destruct (CEP.find y ct_old2) ; first by reflexivity.
    specialize (H1 y).
    destruct (CEP.find y vm_old2) as [[]|] ;
          try (by contradiction H0) ;
          by (specialize (H y) ; rewrite H1 in H ;
              specialize (proj2 H4 y) ; clear H4 ; intro H4 ;
              rewrite -H4 H //).
  + (* Sinvalid, similar to Sskip *)
    simpl ; split ;
        first by apply (CEP.Lemmas.Equal_trans (CEP.Lemmas.Equal_sym H1)),
                       (CEP.Lemmas.Equal_trans (proj1 H4)), H2.
    intro ; rewrite CEP.Lemmas.map2_1bis //.
    specialize (H0 y).
    destruct (CEP.find y ct_old2) ; first by reflexivity.
    specialize (H1 y).
    destruct (CEP.find y vm_old2) as [[]|] ;
          try (by contradiction H0) ;
          by (specialize (H y) ; rewrite H1 in H ;
              specialize (proj2 H4 y) ; clear H4 ; intro H4 ;
              rewrite -H4 H //).
  + (* Swhen *)
    rename h into cond ; rename h0 into ss_true ; rename h1 into ss_false.
    simpl component_stmt_of in H4 ; simpl component_stmt_of.
    apply Sem_frag_stmts_cat in H4 ; apply Sem_frag_stmts_cat.
    destruct H4 as [vm_temp [ct_temp [H4 H5]]].
    exists vm_temp, (extend_map_with ct_old2 ct_temp).
    split.
    - by apply (Sem_frag_stmts_component_Equal ss_true vm_old1 vm_old2 ct_old1 ct_old2 vm_temp vm_temp ct_temp tmap1 tmap2
                                              H H0 H1 (CEP.Lemmas.Equal_refl _) H3 H4).
    - generalize (Sem_frag_stmts_compatible (component_stmts_of ss_true) vm_old1 ct_old1 vm_temp ct_temp tmap1
                                            H4) ; intro.
      destruct H6 as [H6 [_ H7]] ; specialize (H7 H).
      generalize (Sem_frag_stmts_component ss_false vm_temp ct_temp vm_new1 ct_new tmap1 H7 H5) ; intro.
      generalize (extend_map_with_submap ct_old2 ct_temp ct_new H8) ; intro.
      apply Sem_frag_stmts_Equal with (vm_old1 := vm_temp) (ct_old1 := extend_map_with ct_old2 ct_temp)
                                      (vm_new1 := vm_new2) (ct_new1 := extend_map_with (extend_map_with ct_old2 ct_temp) ct_new)
                                      (tmap1 := tmap2) ;
            try assumption ; try apply CEP.Lemmas.Equal_refl.
      apply Sem_frag_stmts_component_Equal with (vm_old1 := vm_temp) (ct_old1 := ct_temp)
                      (vm_new1 := vm_new1)
                      (tmap1 := tmap1) ;
            try assumption ; try apply CEP.Lemmas.Equal_refl.
      generalize (Sem_frag_stmts_component ss_true vm_old1 ct_old1 vm_temp ct_temp tmap1 H H4) ; intro.
      intro.
      specialize (H0 v) ; specialize (H1 v) ; specialize (H6 v) ;
            rewrite H1 in H6.
      rewrite CEP.Lemmas.map2_1bis //.
      destruct (CEP.find v vm_old2) as [[]|] ;
            try (by rewrite H0 ; apply H7) ;
            by (rewrite (H6 _ Logic.eq_refl) ;
                    destruct (CEP.find v ct_old2) ;
                          first (by discriminate) ;
                          last (by contradiction H0)).
Admitted.

Lemma Sem_frag_stmts_no_component :
(* Only component statements change vm *)
forall (ss : HiFP.hfstmt_seq) (vm_old vm_new : CEP.t vertex_type)
       (ct_old ct_new : CEP.t def_expr) (tmap : CEP.t ftype),
component_stmts_of ss = (Qnil ProdVarOrder.T) ->
    Sem_frag_stmts vm_old ct_old ss vm_new ct_new tmap ->
           CEP.Equal vm_old vm_new
with Sem_frag_stmt_no_component :
forall (s : HiFP.hfstmt) (vm_old vm_new : CEP.t vertex_type)
       (ct_old ct_new : CEP.t def_expr) (tmap : CEP.t ftype),
component_stmt_of s = (Qnil ProdVarOrder.T) ->
    Sem_frag_stmt vm_old ct_old s vm_new ct_new tmap ->
           CEP.Equal vm_old vm_new.
Proof.
* clear Sem_frag_stmts_no_component.
  induction ss ; simpl Sem_frag_stmts ; intros ; first by apply H0.
  simpl component_stmts_of in H ; apply Qcat_nil in H.
  destruct H0 as [vm' [ct' H0]].
  specialize (Sem_frag_stmt_no_component h vm_old vm' ct_old ct' tmap (proj1 H) (proj1 H0)).
  specialize (IHss vm' vm_new ct' ct_new tmap (proj2 H) (proj2 H0)).
  intro.
  specialize (Sem_frag_stmt_no_component y) ; rewrite Sem_frag_stmt_no_component.
  apply IHss.
* clear Sem_frag_stmt_no_component.
  induction s ; simpl component_stmt_of ; try discriminate ;
  simpl Sem_frag_stmt ; intros.
  + (* Sskip *)
    rewrite (proj1 H0) ; reflexivity.
  + (* Sfcnct *)
    destruct h0 ; by apply H0.
  + (* Sinvalid *)
    by apply H0.
  + (* Swhen *)
    rename h into cond ; rename h0 into ss_true ; rename h1 into ss_false.
    destruct (type_of_expr cond tmap) as [[[[[|[|]]| | | | | |]| |] _]|] ; try by contradiction H0.
    apply Qcat_nil in H.
    destruct H0 as [vm_true [ct_true [ct_false [Ht [Hf H0]]]]].
    generalize (Sem_frag_stmts_no_component ss_true vm_old vm_true ct_old ct_true tmap (proj1 H) Ht) ; intro.
    specialize (Sem_frag_stmts_no_component ss_false vm_true vm_new (extend_map_with ct_old ct_true) ct_false tmap (proj2 H) Hf).
    intro.
    specialize (H1 y) ; rewrite H1.
    apply Sem_frag_stmts_no_component.
Qed.

(* We first define ExpandBranch_fun.
   It uses a map to indicate which expressions are connected in which
   situation.  To use this map, one needs the data type def_expr. *)

Definition helper_tf (c : HiFP.hfexpr) (true_expr : option def_expr) (false_expr : option def_expr) : option def_expr := 
(* helper function for bringing together the connection maps from true and false branches *)
match true_expr, false_expr with
| Some (D_fexpr t), Some (D_fexpr f) => if t == f then true_expr
                                        else Some (D_fexpr (Emux c t f))
| Some D_undefined, _
| _, Some D_undefined => Some D_undefined
| None, _ => false_expr
| _, None => true_expr
| Some D_invalidated, _ => false_expr
| _, Some D_invalidated => true_expr
end.

Definition ExpandBranch_connect (ref : HiFP.href) (val : def_expr) (old_def_ss : HiFP.hfstmt_seq) (old_conn_map : CEP.t def_expr) (old_scope : CEP.t ftype) : option (HiFP.hfstmt_seq * CEP.t def_expr * CEP.t ftype) :=
(* handle a connect statement, where ref is assigned val.
   ref can be a simple reference or a memory port or an inport of an instance.
   It will always have a ground type, as connects already have been
   expanded and types already have been lowered.
   It is checked that ref and val are in scope. *)
match ref with
| Eid v =>
    match CEP.find v old_scope, val with
    | Some ft_ref, D_fexpr expr =>
        match type_of_expr expr old_scope with
        | Some (exist ft_expr _) =>
            if connect_type_compatible false ft_ref ft_expr false
            then Some (old_def_ss, CEP.add v val old_conn_map, old_scope)
            else None
        | None => None
        end
    | Some _, _ => Some (old_def_ss, CEP.add v val old_conn_map, old_scope)
    | None, _ => None (* out of scope *)
    end
| Esubfield (Esubfield (Eid m) p) f =>
    (* memory port.
       m = name of memory,
       p = name of port,
       If p is a read  port, then f is one of addr / en / clk;
       If p is a write port, then f is one of addr / en / clk / data / mask
       If p is a r/w   port, then f is one of addr / en / clk / wmode / wdata / wmask *)
    None (* TBD *)
| Esubfield (Eid i) p =>
    (* inport of instance.
       i = name of instance,
       p = name of port *)
    (* Look up in the definition of instance i which field is p *)
    None (* TBD *)
| _ => None (* error: aggregate-type components are not allowed *)
end.

Fixpoint ExpandBranch_fun (s : HiFP.hfstmt) (old_def_ss : HiFP.hfstmt_seq) (old_conn_map : CEP.t def_expr) (old_scope : CEP.t ftype) : option (HiFP.hfstmt_seq * CEP.t def_expr * CEP.t ftype) :=
(* s is a statement in a branch (i.e. either the code of a module or of a when statement branch).
   s does not contain aggregate-type components.
   All ground-type elements have an explicit width.
   old_... is the information we already found before s:
   old_def_ss contains the component definition statements,
   old_conn_map contains the connections,
   old_scope contains the component types of the components that are in scope
   (which is a subset of the components in old_def_ss, plus all ports).

   The result is a triple:
   - a statement sequence containing old_def_ss, update with the definitions of components in s
   - a map containing old_conn_map, updated with the connections in s.
   - a map containing old_scope, updated with the definitions of components in s that remain in scope.

   We have to check scopes because ExpandBranch_fun gets rid of them,
   and it cannot be allowed to translate an incorrect statement (sequence)
   to a correct one.
*)
match s with
| Sskip => Some (old_def_ss, old_conn_map, old_scope)
| Swire v t =>
    (* Problem: need to correct the type for the actual width...
       Better: use the precondition of ExpandBranch_fun (namely, that all
       types are fully inferred) to show that code_type_find_vm_widths will
       not change anything. *)
    Some (Qrcons old_def_ss s, CEP.add v D_undefined old_conn_map, CEP.add v t old_scope)
| Sreg v reg =>
    (* type checking can be loose because the statement is a definition statement.
       We only need to verify that the expressions have any type, so they are in scope. *)
    if (if reset reg is Rst rst_sig rst_val
        then match type_of_expr rst_sig old_scope, type_of_expr rst_val old_scope with
             | Some _, Some _ => true
             | _, _ => false
             end
        else true)
    then match type_of_expr (clock reg) old_scope with
         | Some _ => Some (Qrcons old_def_ss s, CEP.add v (D_fexpr (Eref (Eid v))) old_conn_map, CEP.add v (type reg) old_scope)
         | _ => None
         end
    else None
| Smem v m =>
    (* TBD --- Some (Qrcons (fst old_info) s, CEP.add (ports of v) D_undefined (snd old_info)) *)
    None
| Sinvalid ref =>
    ExpandBranch_connect ref D_invalidated old_def_ss old_conn_map old_scope
| Sinst _ _ => None (* instances are not supported currently *)
| Snode v e =>
    if type_of_expr e old_scope is Some (exist ft_expr _)
    then Some (Qrcons old_def_ss s, CEP.add v (D_fexpr e) old_conn_map, CEP.add v ft_expr old_scope)
    else None
| Sfcnct ref e =>
    ExpandBranch_connect ref (D_fexpr e) old_def_ss old_conn_map old_scope
| Swhen c ss_true ss_false =>
    match type_of_expr c old_scope, ExpandBranch_funs ss_true old_def_ss old_conn_map old_scope with
    | Some (exist (Gtyp (Fuint 1)) _), Some (true_def_ss, true_conn_map, _) =>
        match ExpandBranch_funs ss_false true_def_ss (extend_map_with old_conn_map true_conn_map) old_scope with
        | None => None
        | Some (false_def_ss, false_conn_map, _) =>
            Some (false_def_ss, CEP.map2 (helper_tf c) true_conn_map false_conn_map, old_scope)
        end
    | _, _ => None
    end
end
with ExpandBranch_funs (ss : HiFP.hfstmt_seq) (old_def_ss : HiFP.hfstmt_seq) (old_conn_map : CEP.t def_expr) (old_scope : CEP.t ftype) : option (HiFP.hfstmt_seq * CEP.t def_expr * CEP.t ftype) :=
(* ss is the final fragment of a branch (i.e. either the code of a module or of a when statement branch).
   ss does not contain aggregate-type components.
   All ground-type elements have an explicit width.
   old_info is the information we already found before ss:
   the first part contains the component definition statements,
   the second part contains the connections,

   The result is a pair:
   - a statement sequence containing fst old_info, update with the definitions of components in ss
   - a map containing snd old_info, updated with the connections in ss.
*)
match ss with
| Qnil => Some (old_def_ss, old_conn_map, old_scope)
| Qcons s ss' =>
    if ExpandBranch_fun s old_def_ss old_conn_map old_scope is Some (temp_def_ss, temp_conn_map, temp_scope)
    then ExpandBranch_funs ss' temp_def_ss temp_conn_map temp_scope
    else None
end.


(* Now let's try to formulate a theorem that links the module graph
   of a module to the result of ExpandBranch_funs.
   The resulting ss corresponds to the vertices of the module graph,
   and the resulting cmap corresponds to the connection trees.
   With this difference: if the cmap contains a complex expression,
   it is resolved in the module graph to single-step calculations.
   So there is a mapping from ss to the vertices in the module graph
   that represent the components.
   There is also a mapping from output connectors to expressions.
   For component output connectors, the expression is just the reference;
   for output connectors of calculation nodes, the expression is made up
   from the correct operation and the input connectors’ expressions.
   It can be proven that these expressions are the same as those in the
   connect statements.
   Or perhaps better: it can be proven that these expressions are the same
   as those found in the dmap.

   Probably need to include something like the ce, e.g. to find the correct
   type for memories.

   The easiest is likely to model ce similar to what is found in Sem.
   Sem has an ft_pmap (a function from ProdVarOrder.t to ftype),
   that indicates for every component its type.
   (Perhaps for memories this can also indicate the memory type?)

Definition:
   For a module graph G and an out-connector o of a vertex v in G:
      The expression of o is defined to be ...

Perhaps we need a theorem like this:

For a module F = FInmod v pp ss (not containing aggregate types???),
   for all module graphs G,
      if Sem F G
      then for every connection statement s in ss,
              there exists a vertex in G that corresponds to the expression.
But perhaps we have to take into account the when statements as well.

The main theorem on which to base our correctness result may be something like this:

For a module F = FInmod v pp ss (not containing aggregate types),
   for all module graphs G,
      if Sem F G
      then 1. for all ports in pp, there is a vertex in G that corresponds to p;
           2. if ExpandBranch_fun ss = Some (ss', dd'),
              then a) the statements in ss' are exactly the register/wire/node statements in ss;
                   b) for every statement s in ss', there exists a vertex in G that corresponds to s;
                   c) for every connection tree (in-connector <--- out-connector) in dd',
                         there exists a corresponding connection in G
                         (i.e. the expression of the out-connector is the same as in dd')
 *)

Lemma ExpandBranch_components :
   forall (ss def_ss : HiFP.hfstmt_seq) (conn_map : CEP.t def_expr) (scope : CEP.t ftype)
          (def_ss' : HiFP.hfstmt_seq) (conn_map' : CEP.t def_expr) (scope' : CEP.t ftype),
      ExpandBranch_funs ss def_ss conn_map scope =
          Some (def_ss', conn_map', scope') ->
          def_ss' = Qcat def_ss (component_stmts_of ss)
with ExpandBranch_component :
   forall (def_ss' : HiFP.hfstmt_seq) (conn_map' : CEP.t def_expr) (scope : CEP.t ftype)
          (s : HiFP.hfstmt) (def_ss : HiFP.hfstmt_seq) (conn_map : CEP.t def_expr) (scope' : CEP.t ftype),
      ExpandBranch_fun s def_ss conn_map scope =
          Some (def_ss', conn_map', scope') ->
          def_ss' = Qcat def_ss (component_stmt_of s).
Proof.
* clear ExpandBranch_components.
  induction ss ; intros ; simpl ExpandBranch_funs in H ; simpl component_stmts_of.
  + rewrite Qcats0.
    symmetry.
    injection H.
    by trivial.
  + specialize ExpandBranch_component with (s := h) (def_ss := def_ss) (conn_map := conn_map) (scope := scope).
    destruct (ExpandBranch_fun h def_ss conn_map scope) as [[[def_ss0 conn_map0] scope0]|] ; last by discriminate H.
    specialize ExpandBranch_component with (def_ss' := def_ss0) (conn_map' := conn_map0) (scope' := scope0).
    apply IHss in H.
    rewrite ExpandBranch_component // Qcat_assoc in H.
    exact H.
* clear ExpandBranch_component.
  destruct s.
  + (* Sskip *)
    unfold ExpandBranch_fun, component_stmt_of.
    intros.
    rewrite Qcats0.
    injection H ; done.
  + (* Swire *)
    unfold ExpandBranch_fun, component_stmt_of.
    intros.
    injection H ; intros.
    rewrite -Qcat_rcons Qcats0 H2 //.
  + (* Sreg *)
    unfold ExpandBranch_fun, component_stmt_of.
    intros.
    destruct (match reset h with
              | @NRst _ => true
              | Rst rst_sig rst_val =>
                  match type_of_expr rst_sig scope with
                  | Some _ =>
                      match type_of_expr rst_val scope with
                      | Some _ => true
                      | None => false
                      end
                  | None => false
                  end
              end) ; last by discriminate H.
    destruct (type_of_expr (clock h) scope) ; last by discriminate H.
    injection H ; intros.
    rewrite -Qcat_rcons Qcats0 H2 //.
  + (* Smem *)
    unfold ExpandBranch_fun.
    discriminate.
  + (* Sinst *)
    unfold ExpandBranch_fun.
    discriminate.
  + (* Snode *)
    unfold ExpandBranch_fun, component_stmt_of.
    intros.
    destruct (type_of_expr h scope) as [[ft_expr _]|] ; last by discriminate H.
    injection H ; intros.
    rewrite -Qcat_rcons Qcats0 H2 //.
  + (* Sfcnct *)
    unfold ExpandBranch_fun, component_stmt_of.
    intros.
    unfold ExpandBranch_connect in H.
    destruct h ; try by discriminate H.
    - destruct (CEP.find s scope) as [ft_ref|] ; last by discriminate H.
    - destruct (type_of_expr h0 scope) as [[ft_expr _]|] ; last by discriminate H.
    - destruct (connect_type_compatible false ft_ref ft_expr false) ; last by discriminate H.
      injection H ; intros.
      rewrite Qcats0 H2 //.
    - destruct h ; try discriminate H.
      destruct h ; by discriminate H.
  + (* Sinvalid *)
    unfold ExpandBranch_fun, component_stmt_of.
    intros.
    unfold ExpandBranch_connect in H.
    destruct h ; try by discriminate H.
    - destruct (CEP.find s scope) ; last (by discriminate H).
      injection H ; intros.
      rewrite Qcats0 H2 //.
    - destruct h ; try discriminate H.
      destruct h ; by discriminate H.
  + (* Swhen *)
    simpl ExpandBranch_fun ; simpl component_stmt_of.
    rename h into cond ; rename h0 into ss_true ; rename h1 into ss_false.
    intros.
    generalize (ExpandBranch_components ss_true def_ss conn_map scope) ;
          intro.
    destruct (type_of_expr cond scope) as [[[[[|[|]]| | | | | |]| |] _]|] ; try by discriminate H.
    destruct (ExpandBranch_funs ss_true def_ss conn_map scope) as [[[def_ss_true conn_map_true] scope_true]|] ; last by discriminate H.
    specialize (H0 def_ss_true conn_map_true scope_true Logic.eq_refl).
    simpl fst in H.
    generalize (ExpandBranch_components ss_false def_ss_true (extend_map_with conn_map conn_map_true) scope) ;
          intro.
    destruct (ExpandBranch_funs ss_false def_ss_true (extend_map_with conn_map conn_map_true) scope) as [[[def_ss_false conn_map_false] scope_false]|] ; last by discriminate H.
    specialize (H1 def_ss_false conn_map_false scope_false Logic.eq_refl).
    unfold fst, snd in H ; injection H ; intros.
    rewrite -Qcat_assoc -H0 -H1 H4 //.
Qed.

(* The following is a nice lemma
   but the subset old_scope1 old_scope2 is the wrong way round.
   After this comes a lemma with the subsets the other way round;
   note that the proofs are almost literally the same.

Lemma ExpandBranch_stmt_tmap :
forall (vm : CEP.t vertex_type) (s : HiFP.hfstmt)
       (old_tmap new_tmap old_scope1 new_scope1 old_scope2 new_scope2 : CEP.t ftype)
       (old_def_ss new_def_ss : HiFP.hfstmt_seq) (old_conn_map new_conn_map : CEP.t def_expr),
   stmt_tmap (old_tmap, old_scope1) s vm = Some (new_tmap, new_scope1) ->
   ExpandBranch_fun s old_def_ss old_conn_map old_scope2 = Some (new_def_ss, new_conn_map, new_scope2) ->
   submap old_scope1 old_scope2 ->
   stmt_has_fully_inferred_ground_types s ->
      submap new_scope1 new_scope2
with ExpandBranch_stmts_tmap :
forall (vm : CEP.t vertex_type) (ss : HiFP.hfstmt_seq)
       (old_tmap new_tmap old_scope1 new_scope1 old_scope2 new_scope2 : CEP.t ftype)
       (old_def_ss new_def_ss : HiFP.hfstmt_seq) (old_conn_map new_conn_map : CEP.t def_expr),
   stmts_tmap (old_tmap, old_scope1) ss vm = Some (new_tmap, new_scope1) ->
   ExpandBranch_funs ss old_def_ss old_conn_map old_scope2 = Some (new_def_ss, new_conn_map, new_scope2) ->
   submap old_scope1 old_scope2 ->
   stmts_have_fully_inferred_ground_types ss ->
      submap new_scope1 new_scope2.
Proof.
* clear ExpandBranch_stmt_tmap.
  destruct s ; simpl stmt_tmap ; simpl ExpandBranch_fun ; simpl stmt_has_fully_inferred_ground_types ; intros.
  + (* Sskip *)
    injection H ; clear H ; intros H _.
    injection H0 ; clear H0 ; intros H0 _ _.
    rewrite -H -H0.
    by exact H1.
  + (* Swire *)
    injection H0 ; clear H0 ; intros H0 _ _.
    rewrite -H0 ; clear H0 new_scope2.
    destruct f as [gt| |] ; try done.
    destruct (CEP.find s old_tmap) ; first by discriminate H.
    generalize (fully_inferred_does_not_change gt s vm H2) ;
          intro.
    destruct (code_type_find_vm_widths (Gtyp gt) s vm) as [[[newgt| |] _]|]; try done.
    rewrite -H0 in H ; clear H0 newgt.
    injection H ; clear H ; intros H _.
    rewrite -H ; clear H new_scope1.
    apply submap_add_add, H1.
  + (* Sreg *)
    destruct (type h) as [gt| |] ; try done.
    destruct (CEP.find s old_tmap) ; first by discriminate H.
    destruct (type_of_expr (clock h) old_scope1) ; last by discriminate H.
    destruct (reset h) as [|rst_sig rst_val].
    1,2: move /andP : H2 => [_ H2].
    1,2: generalize (fully_inferred_does_not_change gt s vm H2) ;
          intro.
    1,2: destruct (code_type_find_vm_widths (Gtyp gt) s vm) as [[[newgt| |] _]|] ; try done.
    1,2: rewrite -H3 in H ; clear H3 newgt.
    2: destruct (type_of_expr rst_sig old_scope1) ; last by discriminate H.
    2: destruct (type_of_expr rst_val old_scope1) ; last by discriminate H.
    2: destruct (type_of_expr rst_sig old_scope2) ; last by discriminate H0.
    2: destruct (type_of_expr rst_val old_scope2) ; last by discriminate H0.
    1,2: injection H ; clear H ; intros H _ ; rewrite -H ; clear H new_scope1.
    1,2: destruct (type_of_expr (clock h) old_scope2) ; last by discriminate H0.
    1,2: injection H0 ; clear H0 ; intros H0 _ _ ; rewrite -H0 ; clear H0 new_scope2.
    1,2: apply submap_add_add, H1.
  + (* Smem *)
    by discriminate H.
  + (* Sinst *)
    by discriminate H.
  + (* Snode *)
    destruct (CEP.find s old_tmap) ; first by discriminate H.
    generalize (type_of_expr_submap h old_scope1 old_scope2 H1) ;
          intro.
    destruct (type_of_expr h old_scope1) as [[ft1 p1]|] ; last by discriminate H.
    destruct (type_of_expr h old_scope2) as [[ft2 p2]|] ; last by discriminate H0.
    injection H3 ; clear H3 ; intro H3 ; rewrite H3 in H0 ; clear H3 p2 p1 ft2.
    injection H ; clear H ; intros H _ ; rewrite -H ; clear H new_scope1.
    injection H0 ; clear H0 ; intros H0 _ _ ; rewrite -H0 ; clear H0 new_scope2.
    apply submap_add_add, H1.
  + (* Sfcnct *)
    unfold ExpandBranch_connect in H0.
    destruct (type_of_ref h old_scope1) ; last by discriminate H.
    destruct (type_of_expr h0 old_scope1) ; last by discriminate H.
    injection H ; clear H ; intros H _ ; rewrite -H ; clear H new_scope1.
    destruct h ; try done.
    - destruct (CEP.find s old_scope2) ; last by discriminate H0.
      destruct (type_of_expr h0 old_scope2) as [[ft_expr _]|] ; last by discriminate H0.
      destruct (connect_type_compatible false f1 ft_expr false) ; last by discriminate H0.
      injection H0 ; clear H0 ; intros H0 _ _ ; rewrite -H0 ; clear H0 new_scope2.
      by exact H1.
    - destruct h ; try done.
      destruct h ; by done.
  + (* Sinvalid *)
    unfold ExpandBranch_connect in H0.
    destruct (type_of_ref h old_scope1) ; last by discriminate H.
    injection H ; clear H ; intros H _ ; rewrite -H ; clear H new_scope1.
    destruct h ; try done.
    - destruct (CEP.find s old_scope2) ; last by discriminate H0.
      injection H0 ; clear H0 ; intros H0 _ _ ; rewrite -H0 ; clear H0 new_scope2.
      by exact H1.
    - destruct h ; try done.
      destruct h ; by done.
  + (* Swhen *)
    rename h into cond ; rename h0 into ss_true ; rename h1 into ss_false.
    destruct (type_of_expr cond old_scope1) ; last by discriminate H.
    destruct (type_of_expr cond old_scope2) as [[[[[|[|]]| | | | | |]| |] _]|] ; try by discriminate H0.
    destruct (stmts_tmap (old_tmap, old_scope1) ss_true vm) as [[tmap_true scope1_true]|] ; last by discriminate H.
    destruct (ExpandBranch_funs ss_true old_def_ss old_conn_map old_scope2) as [[[true_def_ss true_conn_map] true_scope2]|] ; last by discriminate H0.
    destruct (stmts_tmap (tmap_true, old_scope1) ss_false vm) as [[tmap_false scope1_false]|] ; last by discriminate H.
    injection H ; clear H ; intros H _ ; rewrite -H ; clear H new_scope1.
    destruct (ExpandBranch_funs ss_false true_def_ss old_conn_map old_scope2) as [[[false_def_ss false_conn_map] false_scope2]|] ; last by discriminate H0.
    injection H0 ; clear H0 ; intros H0 _ _ ; rewrite -H0 ; clear H0 new_scope2.
    by exact H1.
* clear ExpandBranch_stmts_tmap.
  induction ss.
  + simpl stmts_tmap ; simpl ExpandBranch_funs ; intros.
    injection H ; clear H ; intros H _ ; rewrite -H ; clear H new_scope1.
    injection H0 ; clear H0 ; intros H0 _ _ ; rewrite -H0 ; clear H0 new_scope2.
    by exact H1.
  + simpl stmts_tmap ; simpl ExpandBranch_funs ; simpl stmts_have_fully_inferred_ground_types ; intros.
    move /andP : H2 => [H2 H3].
    specialize (ExpandBranch_stmt_tmap vm h old_tmap)
          with (old_scope1 := old_scope1) (old_scope2 := old_scope2)
               (old_def_ss := old_def_ss) (old_conn_map := old_conn_map).
    destruct (stmt_tmap (old_tmap, old_scope1) h vm) as [[tmap' scope']|] ; last by discriminate H.
    specialize ExpandBranch_stmt_tmap
          with (new_tmap := tmap') (new_scope1 := scope').
    destruct (ExpandBranch_fun h old_def_ss old_conn_map old_scope2) as [[[temp_def_ss temp_conn_map] temp_scope]|]; last by discriminate H0.
    specialize (ExpandBranch_stmt_tmap temp_scope temp_def_ss temp_conn_map Logic.eq_refl Logic.eq_refl H1 H2).
    by apply (IHss tmap' new_tmap scope' new_scope1 temp_scope new_scope2
                temp_def_ss new_def_ss temp_conn_map new_conn_map H H0
                ExpandBranch_stmt_tmap H3).
Qed.
*)

Lemma ExpandBranch_stmt_tmap :
forall (vm : CEP.t vertex_type) (s : HiFP.hfstmt)
       (old_tmap new_tmap old_scope1 new_scope1 old_scope2 new_scope2 : CEP.t ftype)
       (old_def_ss new_def_ss : HiFP.hfstmt_seq) (old_conn_map new_conn_map : CEP.t def_expr),
   stmt_tmap (old_tmap, old_scope1) s vm = Some (new_tmap, new_scope1) ->
   ExpandBranch_fun s old_def_ss old_conn_map old_scope2 = Some (new_def_ss, new_conn_map, new_scope2) ->
   CEP.submap old_scope2 old_scope1 ->
   stmt_has_fully_inferred_ground_types s ->
      CEP.submap new_scope2 new_scope1
with ExpandBranch_stmts_tmap :
forall (vm : CEP.t vertex_type) (ss : HiFP.hfstmt_seq)
       (old_tmap new_tmap old_scope1 new_scope1 old_scope2 new_scope2 : CEP.t ftype)
       (old_def_ss new_def_ss : HiFP.hfstmt_seq) (old_conn_map new_conn_map : CEP.t def_expr),
   stmts_tmap (old_tmap, old_scope1) ss vm = Some (new_tmap, new_scope1) ->
   ExpandBranch_funs ss old_def_ss old_conn_map old_scope2 = Some (new_def_ss, new_conn_map, new_scope2) ->
   CEP.submap old_scope2 old_scope1 ->
   stmts_have_fully_inferred_ground_types ss ->
      CEP.submap new_scope2 new_scope1.
Proof.
* clear ExpandBranch_stmt_tmap.
  destruct s ; simpl stmt_tmap ; simpl ExpandBranch_fun ; simpl stmt_has_fully_inferred_ground_types ; intros.
  + (* Sskip *)
    injection H ; clear H ; intros H _ ; rewrite -H ; clear H new_scope1.
    injection H0 ; clear H0 ; intros H0 _ _ ; rewrite -H0 ; clear H0 new_scope2.
    by exact H1.
  + (* Swire *)
    injection H0 ; clear H0 ; intros H0 _ _.
    rewrite -H0 ; clear H0 new_scope2.
    destruct f as [gt| |] ; try done.
    destruct (CEP.find s old_tmap) ; first by discriminate H.
    generalize (fully_inferred_does_not_change gt s vm H2) ;
          intro.
    destruct (code_type_find_vm_widths (Gtyp gt) s vm) as [[[newgt| |] _]|]; try done.
    rewrite -H0 in H ; clear H0 newgt.
    injection H ; clear H ; intros H _.
    rewrite -H ; clear H new_scope1.
    apply submap_add_add, H1.
  + (* Sreg *)
    destruct (type h) as [gt| |] ; try done.
    destruct (CEP.find s old_tmap) ; first by discriminate H.
    destruct (type_of_expr (clock h) old_scope1) ; last by discriminate H.
    destruct (reset h) as [|rst_sig rst_val].
    1,2: move /andP : H2 => [_ H2].
    1,2: generalize (fully_inferred_does_not_change gt s vm H2) ;
          intro.
    1,2: destruct (code_type_find_vm_widths (Gtyp gt) s vm) as [[[newgt| |] _]|] ; try done.
    1,2: rewrite -H3 in H ; clear H3 newgt.
    2: destruct (type_of_expr rst_sig old_scope1) ; last by discriminate H.
    2: destruct (type_of_expr rst_val old_scope1) ; last by discriminate H.
    2: destruct (type_of_expr rst_sig old_scope2) ; last by discriminate H0.
    2: destruct (type_of_expr rst_val old_scope2) ; last by discriminate H0.
    1,2: injection H ; clear H ; intros H _ ; rewrite -H ; clear H new_scope1.
    1,2: destruct (type_of_expr (clock h) old_scope2) ; last by discriminate H0.
    1,2: injection H0 ; clear H0 ; intros H0 _ _ ; rewrite -H0 ; clear H0 new_scope2.
    1,2: apply submap_add_add, H1.
  + (* Smem *)
    by discriminate H.
  + (* Sinst *)
    by discriminate H.
  + (* Snode *)
    destruct (CEP.find s old_tmap) ; first by discriminate H.
    generalize (type_of_expr_submap h old_scope2 old_scope1 H1) ;
          intro.
    destruct (type_of_expr h old_scope1) as [[ft1 p1]|] ; last by discriminate H.
    destruct (type_of_expr h old_scope2) as [[ft2 p2]|] ; last by discriminate H0.
    injection H3 ; clear H3 ; intro H3 ; rewrite -H3 in H0 ; clear H3 p2 p1 ft2.
    injection H ; clear H ; intros H _ ; rewrite -H ; clear H new_scope1.
    injection H0 ; clear H0 ; intros H0 _ _ ; rewrite -H0 ; clear H0 new_scope2.
    apply submap_add_add, H1.
  + (* Sfcnct *)
    unfold ExpandBranch_connect in H0.
    destruct (type_of_ref h old_scope1) ; last by discriminate H.
    destruct (type_of_expr h0 old_scope1) ; last by discriminate H.
    injection H ; clear H ; intros H _ ; rewrite -H ; clear H new_scope1.
    destruct h ; try done.
    - destruct (CEP.find s old_scope2) ; last by discriminate H0.
      destruct (type_of_expr h0 old_scope2) as [[ft_expr _]|] ; last by discriminate H0.
      destruct (connect_type_compatible false f1 ft_expr false) ; last by discriminate H0.
      injection H0 ; clear H0 ; intros H0 _ _ ; rewrite -H0 ; clear H0 new_scope2.
      by exact H1.
    - destruct h ; try done.
      destruct h ; by done.
  + (* Sinvalid *)
    unfold ExpandBranch_connect in H0.
    destruct (type_of_ref h old_scope1) ; last by discriminate H.
    injection H ; clear H ; intros H _ ; rewrite -H ; clear H new_scope1.
    destruct h ; try done.
    - destruct (CEP.find s old_scope2) ; last by discriminate H0.
      injection H0 ; clear H0 ; intros H0 _ _ ; rewrite -H0 ; clear H0 new_scope2.
      by exact H1.
    - destruct h ; try done.
      destruct h ; by done.
  + (* Swhen *)
    rename h into cond ; rename h0 into ss_true ; rename h1 into ss_false.
    destruct (type_of_expr cond old_scope1) ; last by discriminate H.
    destruct (type_of_expr cond old_scope2) as [[[[[|[|]]| | | | | |]| |] _]|] ; try by discriminate H0.
    destruct (stmts_tmap (old_tmap, old_scope1) ss_true vm) as [[tmap_true scope1_true]|] ; last by discriminate H.
    destruct (ExpandBranch_funs ss_true old_def_ss old_conn_map old_scope2) as [[[true_def_ss true_conn_map] true_scope2]|] ; last by discriminate H0.
    destruct (stmts_tmap (tmap_true, old_scope1) ss_false vm) as [[tmap_false scope1_false]|] ; last by discriminate H.
    injection H ; clear H ; intros H _ ; rewrite -H ; clear H new_scope1.
    destruct (ExpandBranch_funs ss_false true_def_ss (extend_map_with old_conn_map true_conn_map) old_scope2) as [[[false_def_ss false_conn_map] false_scope2]|] ; last by discriminate H0.
    injection H0 ; clear H0 ; intros H0 _ _ ; rewrite -H0 ; clear H0 new_scope2.
    by exact H1.
* clear ExpandBranch_stmts_tmap.
  induction ss.
  + simpl stmts_tmap ; simpl ExpandBranch_funs ; intros.
    injection H ; clear H ; intros H _ ; rewrite -H ; clear H new_scope1.
    injection H0 ; clear H0 ; intros H0 _ _ ; rewrite -H0 ; clear H0 new_scope2.
    by exact H1.
  + simpl stmts_tmap ; simpl ExpandBranch_funs ; simpl stmts_have_fully_inferred_ground_types ; intros.
    move /andP : H2 => [H2 H3].
    specialize (ExpandBranch_stmt_tmap vm h old_tmap)
          with (old_scope1 := old_scope1) (old_scope2 := old_scope2)
               (old_def_ss := old_def_ss) (old_conn_map := old_conn_map).
    destruct (stmt_tmap (old_tmap, old_scope1) h vm) as [[tmap' scope']|] ; last by discriminate H.
    specialize ExpandBranch_stmt_tmap
          with (new_tmap := tmap') (new_scope1 := scope').
    destruct (ExpandBranch_fun h old_def_ss old_conn_map old_scope2) as [[[temp_def_ss temp_conn_map] temp_scope]|]; last by discriminate H0.
    specialize (ExpandBranch_stmt_tmap temp_scope temp_def_ss temp_conn_map Logic.eq_refl Logic.eq_refl H1 H2).
    by apply (IHss tmap' new_tmap scope' new_scope1 temp_scope new_scope2
                temp_def_ss new_def_ss temp_conn_map new_conn_map H H0
                ExpandBranch_stmt_tmap H3).
Qed.

(*
The following lemma is probably not needed.
Lemma ExpandBranch_funs_submap :
forall (ss : HiFP.hfstmt_seq) (old_def_ss : HiFP.hfstmt_seq) (old_conn_map : CEP.t def_expr) (old_scope : CEP.t ftype),
   forall (tmap : CEP.t ftype) (vm : CEP.t vertex_type),
      submap old_scope tmap ->
      stmts_tmap (tmap, old_scope) ss vm <> None ->
         match ExpandBranch_funs ss old_def_ss old_conn_map old_scope with
         | Some (_, _, new_scope) => submap old_scope new_scope
         | None => True
         end
with ExpandBranch_fun_submap :
forall (s : HiFP.hfstmt) (old_def_ss : HiFP.hfstmt_seq) (old_conn_map : CEP.t def_expr) (old_scope : CEP.t ftype),
   forall (tmap : CEP.t ftype) (vm : CEP.t vertex_type),
      submap old_scope tmap ->
      stmt_tmap (tmap, old_scope) s vm <> None ->
         match ExpandBranch_fun s old_def_ss old_conn_map old_scope with
         | Some (_, _, new_scope) => submap old_scope new_scope
         | None => True
         end.
Proof.
* clear ExpandBranch_funs_submap.
  induction ss.
  + intros.
    unfold ExpandBranch_funs.
    by apply submap_refl.
  + intros.
    simpl stmts_tmap in H0.
    simpl ExpandBranch_funs.
    specialize (ExpandBranch_fun_submap h old_def_ss old_conn_map old_scope tmap vm H).




    destruct (stmt_tmap (tmap, old_scope) h vm) as [[tmap' scope']|] ; last by contradiction H0.
    destruct (ExpandBranch_fun h old_def_ss old_conn_map old_scope) as [[[temp_def_ss temp_conn_map] temp_scope]|] ; last by trivial.
    specialize (IHss temp_def_ss temp_conn_map temp_scope tmap' vm).
    destruct (ExpandBranch_funs ss temp_def_ss temp_conn_map temp_scope) as [[[new_def_ss new_conn_map] new_scope]|] ; last by trivial.
    apply (submap_trans temp_scope).
    - apply ExpandBranch_fun_submap.
      discriminate.
    - apply IHss.
      (* submap temp_scope tmap' *)
      (* We now need: submap scope' temp_scope *)

* clear ExpandBranch_fun_submap.
  intros.
  destruct H as [vm_old [ct_old [vm_new [ct_new [tmap Hs]]]]].
  destruct s ; simpl ; simpl in Hs ; try trivial.
  * (* Sskip *)
    by apply submap_refl.
  * (* Swire *)
    intro.


   stmts_have_fully_inferred_ground_types ss ->
   tmap_has_fully_inferred_ground_types tmap ->
   submap scope1 tmap ->
   submap scope2 tmap ->
   submap scope1 scope2 ->
      stmts_tmap (tmap, scope1) ss vm = None ->
         stmts_tmap (tmap, scope2) (component_stmts_of ss) vm <> None ->
            forall (old_def_ss : HiFP.hfstmt_seq) (old_conn_map : CEP.t def_expr) (old_scope : CEP.t ftype),
               submap old_scope scope1 ->
                  ExpandBranch_funs ss old_def_ss old_conn_map old_scope = None
*)

Lemma ExpandBranch_funs_checks_scopes :
forall (ss : HiFP.hfstmt_seq) (tmap scope1 scope2 : CEP.t ftype) (vm : CEP.t vertex_type),
   stmts_have_fully_inferred_ground_types ss ->
   tmap_has_fully_inferred_ground_types tmap ->
   CEP.submap scope1 tmap ->
   CEP.submap scope2 tmap ->
   CEP.submap scope1 scope2 ->
      stmts_tmap (tmap, scope1) ss vm = None ->
         stmts_tmap (tmap, scope2) (component_stmts_of ss) vm <> None ->
            forall (old_def_ss : HiFP.hfstmt_seq) (old_conn_map : CEP.t def_expr) (old_scope : CEP.t ftype),
               CEP.submap old_scope scope1 ->
                  ExpandBranch_funs ss old_def_ss old_conn_map old_scope = None
with ExpandBranch_fun_checks_scopes :
forall (s : HiFP.hfstmt) (tmap scope1 scope2 : CEP.t ftype) (vm : CEP.t vertex_type),
   stmt_has_fully_inferred_ground_types s ->
   tmap_has_fully_inferred_ground_types tmap ->
   CEP.submap scope1 tmap ->
   CEP.submap scope2 tmap ->
   CEP.submap scope1 scope2 ->
      stmt_tmap (tmap, scope1) s vm = None ->
         stmts_tmap (tmap, scope2) (component_stmt_of s) vm <> None ->
            forall (old_def_ss : HiFP.hfstmt_seq) (old_conn_map : CEP.t def_expr) (old_scope : CEP.t ftype),
               CEP.submap old_scope scope1 ->
                  ExpandBranch_fun s old_def_ss old_conn_map old_scope = None.
Proof.
* clear ExpandBranch_funs_checks_scopes.
  induction ss.
  + unfold stmts_tmap at 1 ; discriminate.
  + intros until 1.
    simpl stmts_have_fully_inferred_ground_types in H ;
    move /andP : H => [H H0].
    intros.
    simpl stmts_tmap in H5, H6.
    rewrite stmts_tmap_cat in H6.
    simpl ExpandBranch_funs.
    specialize (ExpandBranch_fun_checks_scopes h tmap scope1 scope2 vm H H1 H2 H3 H4)
          with (3 := H7) (old_def_ss := old_def_ss) (old_conn_map := old_conn_map) (old_scope := old_scope).
    generalize (ExpandBranch_stmt_tmap vm h tmap) ;
          intro ;
          specialize H8 with (3 := H7) (4 := H) (old_scope1 := scope1) (old_def_ss := old_def_ss) (old_conn_map := old_conn_map) (old_scope2 := old_scope).
    destruct (ExpandBranch_fun h old_def_ss old_conn_map old_scope) as [[[temp_def_ss temp_conn_map] temp_scope]|] ; last by reflexivity.
    specialize H8 with (new_def_ss := temp_def_ss) (new_conn_map := temp_conn_map) (new_scope2 := temp_scope) (2 := Logic.eq_refl).
    generalize (stmt_submap vm h tmap scope1 H2) ;
          intro.
    generalize (stmt_tmap_components vm h tmap scope1 scope2 H2 H3 H4) ;
          intro.
    generalize (stmt_tmap_preserves_fully_inferred vm tmap scope1 h H H1 H2) ;
          intro.
    destruct (stmt_tmap (tmap, scope1) h vm) as [[tmap_h scope1_h]|] ;
          last by (destruct (stmts_tmap (tmap, scope2) (component_stmt_of h) vm) ;
                   last (by contradiction H6) ;
                   discriminate ExpandBranch_fun_checks_scopes ;
                   done).
    specialize (H8 tmap_h scope1_h Logic.eq_refl).
    clear ExpandBranch_fun_checks_scopes.
    generalize (stmts_submap vm (component_stmt_of h) tmap scope2 H3) ;
          intro.
    destruct (stmts_tmap (tmap, scope2) (component_stmt_of h) vm) as [[tmap_h' scope2_h]|] ; last by contradiction H6.
    destruct H10 as [H10' H10] ; rewrite -H10' in H6, H12 ; clear H10' tmap_h'.
    by apply (IHss tmap_h scope1_h scope2_h vm H0 H11 (proj1 H9) (proj1 H12)
                H10 H5 H6 temp_def_ss temp_conn_map temp_scope H8).
* clear ExpandBranch_fun_checks_scopes.
  destruct s ; simpl stmt_has_fully_inferred_ground_types ;
        simpl stmt_tmap ; simpl stmts_tmap ; simpl ExpandBranch_fun ; intros ; try done.
  + (* Swire *)
    destruct (CEP.find s tmap) ; first by contradiction H5.
    destruct (code_type_find_vm_widths f s vm) as [[]|]; last by contradiction H5.
    by discriminate H4.
  + (* Sreg *)
    destruct (CEP.find s tmap) ; first by contradiction H5.
    destruct (reset h) as [|rst_sig rst_val].
    2: generalize (type_of_expr_submap rst_sig old_scope scope1 H6) ;
            intro.
    2: destruct (type_of_expr rst_sig old_scope) ; last by reflexivity.
    2: rewrite H7 in H4 ; clear H7 f.
    2: generalize (type_of_expr_submap rst_val old_scope scope1 H6) ;
            intro.
    2: destruct (type_of_expr rst_val old_scope) ; last by reflexivity.
    2: rewrite H7 in H4 ; clear H7 f.
    1,2: generalize (type_of_expr_submap (clock h) old_scope scope1 H6) ;
            intro.
    1,2: destruct (type_of_expr (clock h) old_scope) ; last by reflexivity.
    1,2: rewrite H7 in H4 ; clear H7 f.
    1,2: destruct (type_of_expr (clock h) scope2) ; last by contradiction H5.
    1,2: destruct (code_type_find_vm_widths (type h) s vm) as [[newt _]|]; last by contradiction H5.
    2: destruct (type_of_expr rst_sig scope2) ; last by contradiction H5.
    2: destruct (type_of_expr rst_val scope2) ; last by contradiction H5.
    1,2: by discriminate H4.
  + (* Snode *)
    destruct (CEP.find s tmap) ; first by contradiction H5.
    generalize (type_of_expr_submap h old_scope scope1 H6) ;
            intro.
    destruct (type_of_expr h old_scope) as [[ft_expr p]|] ; last by reflexivity.
    rewrite H7 in H4 ; clear H7 p.
    by discriminate H4.
  + (* Sfcnct *)
    unfold ExpandBranch_connect.
    destruct h ; try done.
    - simpl type_of_ref in H4.
      generalize (H6 s) ; intro.
      destruct (CEP.find s old_scope) as [ft_ref|] ; last by reflexivity.
      rewrite (H7 _ Logic.eq_refl) in H4 ; clear H7.
      generalize (type_of_expr_submap h0 old_scope scope1 H6) ;
            intro.
      destruct (type_of_expr h0 old_scope) as [[ft_expr p]|] ; last by reflexivity.
      rewrite H7 in H4 ; clear H7 p.
      by discriminate H4.
    - destruct h ; try done.
      destruct h ; by done.
  + (* Sinvalid *)
    unfold ExpandBranch_connect.
    destruct h ; try done.
    - simpl type_of_ref in H4.
      specialize (H6 s).
      destruct (CEP.find s old_scope) as [ft_ref|] ; last by reflexivity.
      rewrite (H6 _ Logic.eq_refl) in H4 ; clear H6.
      by discriminate H4.
    - destruct h ; try done.
      destruct h ; by done.
  + (* Swhen *)
    rename h into cond ; rename h0 into ss_true ; rename h1 into ss_false.
    move /andP : H => [Ht Hf].
    generalize (type_of_expr_submap cond old_scope scope1 H6) ;
          intro.
    destruct (type_of_expr cond old_scope) as [[[[[|[|]]| | | | | |]| |] p]|] ; try by reflexivity.
    rewrite H in H4 ; clear H p.
    rewrite stmts_tmap_cat in H5.
    (* General line of the argument:
       Based on H4, we cannot have both
       a) isSome (stmts_tmap (tmap, scope1) ss_true vm) and
       b) isSome (stmts_tmap (tmap_true, scope1) ss_false vm).
       However, based on H5, we do have both
       - isSome (stmts_tmap (tmap, scope2) (component_stmts_of ss_true) vm) and
       - isSome (stmts_tmap (tmap_true, scope2_true) (component_stmts_of ss_false) vm).
       In case a), we can use ExpandBranch_funs_checks_scopes
       to prove that ExpandBranch_funs ss_true ... = None.
       In case b), we can use ExpandBranch_funs_checks_scopes
       to prove that ExpandBranch_funs ss_false ... = None.
       *)
    generalize (stmts_tmap_components vm ss_true tmap scope1 scope2 H1 H2 H3) ;
          intro.
    generalize (stmts_tmap_preserves_fully_inferred vm ss_true tmap scope1 Ht H0 H1) ;
          intro.
    generalize (stmts_submap vm ss_true tmap scope1 H1) ;
          intro.
    generalize (ExpandBranch_funs_checks_scopes ss_true tmap scope1 scope2 vm Ht H0 H1 H2 H3) ;
          intro.
    destruct (stmts_tmap (tmap, scope1) ss_true vm) as [[tmap_true scope1_true]|].
    - generalize (stmts_submap vm (component_stmts_of ss_true) tmap scope2 H2) ;
            intro.
      destruct (stmts_tmap (tmap, scope2) (component_stmts_of ss_true) vm) as [[tmap_true' scope2_true]|] ; last by contradiction H.
      destruct H as [H' H] ; rewrite -H' in H5 H9 H10 ; clear H' tmap_true'.
      destruct (ExpandBranch_funs ss_true old_def_ss old_conn_map old_scope) as [[[true_def_ss true_conn_map] _]|] ; last by reflexivity.
      assert (CEP.submap scope1 tmap_true) by apply (CEP.Lemmas.submap_trans (proj2 (proj2 H8))), H8.
      assert (CEP.submap scope1 scope2_true) by apply (CEP.Lemmas.submap_trans H3), H10.
      specialize (ExpandBranch_funs_checks_scopes ss_false tmap_true scope1 scope2_true vm
                  Hf H7 H11 (proj1 H10) H12)
            with (old_def_ss := true_def_ss) (old_conn_map := (extend_map_with old_conn_map true_conn_map)) (old_scope := old_scope).
      destruct (stmts_tmap (tmap_true, scope1) ss_false vm) as [[]|] ; first by discriminate H4.
      rewrite (ExpandBranch_funs_checks_scopes Logic.eq_refl H5 H6) //.
    - destruct (stmts_tmap (tmap, scope2) (component_stmts_of ss_true) vm) ; last by contradiction H5.
      specialize (H9 Logic.eq_refl) with (old_def_ss := old_def_ss) (old_conn_map := old_conn_map) (old_scope := old_scope).
      rewrite H9 //.
Qed.

Fixpoint ExpandPort_fun (pp : seq HiFP.hfport) : option (CEP.t def_expr * CEP.t ftype) :=
(* create a map of def_expr for the port sequence pp.
   Out ports need to be assigned value “undefined”;
   in ports do not need to be assigned any value.
   Because types have been lowered already, we can assume
   that all ports have ground types. *)
match pp with
| [::] => Some (CEP.empty def_expr, CEP.empty ftype)
| Finput p t :: pp' =>
    match ExpandPort_fun pp' with
    | Some (temp_conn_map, temp_scope) =>
        Some (temp_conn_map, CEP.add p t temp_scope)
    | None => None
    end
| Foutput p t :: pp' =>
    match ExpandPort_fun pp' with
    | Some (temp_conn_map, temp_scope) =>
        Some (CEP.add p D_undefined temp_conn_map, CEP.add p t temp_scope)
    | None => None
    end
end.

(* Some lemma about correctness of ports. *)

Lemma ExpandPort_correct :
forall (vm : CEP.t vertex_type) (pp : seq HiFP.hfport),
   ports_have_fully_inferred_ground_types pp ->
      match ports_tmap pp vm, ExpandPort_fun pp with
      | Some pmap, Some (new_conn_map, new_scope) =>
          CEP.Equal pmap new_scope
      | _, _ => True
      end.
Proof.
induction pp.
* intros ; simpl ; reflexivity.
* simpl ; intros.
  destruct a as [v [gt| |]|v [gt| |]] ; try done.
  1,2: move /andP : H => [H H0].
  1,2: specialize IHpp with (1 := H0) ; clear H0.
  1,2: generalize (fully_inferred_does_not_change gt v vm H) ;
        intro.
  1,2: destruct (code_type_find_vm_widths (Gtyp gt) v vm) as [[[newgt| |]]|] ; try done.
  1,2: rewrite -H0 ; clear H0 newgt n.
  1,2: destruct (ports_tmap pp vm) as [pmap|]; last by trivial.
  1,2: destruct (CEP.find v pmap) ; first by trivial.
  1,2: destruct (ExpandPort_fun pp) as [[temp_conn_map temp_scope]|]; last by trivial.
  1,2: intro.
  1,2: destruct (y == v) eqn: Hyv.
  1,3: rewrite CEP.Lemmas.find_add_eq ; last (by rewrite /HiFirrtl.PVM.SE.eq Hyv //) ;
       rewrite CEP.Lemmas.find_add_eq ; last (by rewrite /HiFirrtl.PVM.SE.eq Hyv //) ;
       by reflexivity.
  1,2: rewrite CEP.Lemmas.find_add_neq ; last (by rewrite /HiFirrtl.PVM.SE.eq Hyv //) ;
       rewrite CEP.Lemmas.find_add_neq ; last (by rewrite /HiFirrtl.PVM.SE.eq Hyv //) ;
       by apply IHpp.
Qed.

Lemma ExpandPort_Sem :
(* Sem_frag_ports and ExpandPort_fun produce essentially the same port map *)
forall (tmap : CEP.t ftype) (pp : seq HiFP.hfport) (vm vm_tmap : CEP.t vertex_type) (ct : CEP.t def_expr),
    ports_have_fully_inferred_ground_types pp ->
    match ports_tmap pp vm_tmap with
    | Some pmap =>
        CEP.submap pmap tmap ->
        Sem_frag_ports (CEP.empty vertex_type) (CEP.empty def_expr) pp vm ct tmap ->
           match ExpandPort_fun pp with
           | Some (new_conn_map, new_scope) =>
               CEP.Equal ct new_conn_map
           | _ => True
           end
    | None => True
    end.
Proof.
induction pp ; first by (simpl ; intros ; destruct H1 ; rewrite H2 ; reflexivity).
intros.
generalize (ports_tmap_preserves_fully_inferred vm_tmap (a :: pp) H) ; intro.
simpl ports_have_fully_inferred_ground_types in H.
generalize (ports_tmap_names vm_tmap pp) ; intro.
generalize (ports_tmap_uniq vm_tmap (a :: pp)) ; intro.
destruct (ports_tmap (a :: pp) vm_tmap) as [pmap|] eqn: Hpmap ; last by trivial.
intros.
simpl ports_tmap in Hpmap.
destruct H4 as [vm' [ct' [H4 H5]]].
assert (CEP.submap vm' vm /\ CEP.submap ct' ct)
      by (apply Sem_frag_ports_submap with (pp := [:: a]) (tmap := tmap) ;
          simpl ; exists vm', ct' ;
          split ; last (by exact H5) ; split ; reflexivity).
unfold Sem_frag_port in H5.
destruct (ExpandPort_fun (a :: pp)) as [[new_conn_map new_scope]|] eqn: Hexpand ; last by trivial.
simpl ExpandPort_fun in Hexpand.
destruct a as [p [gt| |]|p [gt| |]] ; try done.
1,2: move /andP : H => [H H7].
1,2: specialize (IHpp vm' vm_tmap ct' H7).
1,2: destruct (ExpandPort_fun pp) as [[temp_conn_map temp_scope]|] ; last by discriminate Hexpand.
1,2: injection Hexpand ; clear Hexpand ; intros _ Hexpand ;
     rewrite -Hexpand ; clear new_conn_map new_scope temp_scope Hexpand.
1,2: generalize (fully_inferred_does_not_change gt p vm_tmap H) ; intro.
1,2: destruct (code_type_find_vm_widths (Gtyp gt) p vm_tmap) as [[[gt'| |] _]|] ; try by done.
1,2: rewrite -H8 in Hpmap ; clear gt' H8.
1,2: destruct (ports_tmap pp vm_tmap) as [pmap'|] eqn: Hports_tmap ; last by done.
1,2: specialize (H1 p).
1,2: destruct (CEP.find p pmap') eqn: Hfindp' ; first by done.
1,2: destruct H1 as [H1 _].
1,2: injection Hpmap ; clear Hpmap ; intro Hpmap.
1,2: rewrite -Hpmap in H0, H3 ; clear pmap Hpmap.
1,2: generalize (H3 p) ; intro.
1,2: rewrite CEP.Lemmas.find_add_eq in H8 ; last by rewrite /CEP.SE.eq //.
1,2: rewrite (H8 _ Logic.eq_refl) in H5.
1,2: simpl size_of_ftype in H5 ; simpl list_rhs_type_p in H5.
(* First goal: we use proj2 (proj2 H5) and IHpp to prove the result.
   We only need to prove that ports_tmap pp vm' is Some pmap and is a submap of tmap;
   that should be possible to prove by using the other parts of H5,
   which state that vm and vm' are almost the same, so we finally get
   ports_tmap pp vm is basically CEP.Equal to ports_tmap pp vm'. *)
* destruct H5 as [_ [H9 H10]].
  (*specialize (H5 0) ; rewrite /List.nth_error add0n nat_of_binK -surjective_pairing in H5.*)
  intro.
  specialize (H10 y).
  rewrite -H10 ; destruct H6 as [H6 _] ; clear ct H10.
  (*
  assert (ports_tmap pp vm' = ports_tmap pp vm).
        clear -H2 H7 H9.
        revert H2 H7.
        induction pp ;
              first by (unfold ports_tmap ; reflexivity).
        intros ; simpl ports_tmap.
        simpl ports_have_fully_inferred_ground_types in H7.
        destruct a as [p0 [gt0| |]|p0 [gt0| |]] ; try done.
        1,2: simpl uniq in H2 ; move /andP : H2 => [H21 /andP [_ H23]].
        1,2: rewrite in_cons negb_or in H21.
        1,2: move /andP : H21 => [H21 H22].
        1,2: move /andP : H7 => [H H7].
        1,2: simpl uniq in IHpp.
        1,2: rewrite H22 H23 andTb in IHpp.
        1,2: specialize (IHpp is_true_true H7).
        1,2: rewrite IHpp.
        1,2: assert (CEP.find p0 vm' = CEP.find p0 vm)
              by (specialize (H9 p0.1 p0.2) ;
                  rewrite add1n -surjective_pairing in H9 ;
                  specialize (N.eq_dec p0.1 p.1) ; intro ;
                  destruct H0 ; last (by apply H9 ; left ; exact n) ;
                  destruct (Nat.compare_spec p0.2 p.2) ;
                        first (by specialize (injective_projections p0 p e) ; intro ;
                                  rewrite -(nat_of_binK p0.2) -(nat_of_binK p.2) H0 in H1 ;
                                  specialize (H1 Logic.eq_refl) ;
                                  rewrite H1 eq_refl // in H21) ;
                        first (by apply H9 ; right ; left  ; move /ltP : H0 => H0 ; exact H0) ;
                  apply H9 ; right ; right ; move /ltP : H0 => H0 ; exact H0).
        1,2: unfold code_type_find_vm_widths ;
             rewrite H0 ;
             fold (code_type_find_vm_widths (Gtyp gt0) p0 vm).
        1,2: reflexivity.
  rewrite H5 Hports_tmap in IHpp.*)
  apply IHpp ; last by exact H4.
  intro.
  specialize (H3 k).
  destruct (k == p) eqn: Hvp ; first by move /eqP : Hvp => Hvp ; rewrite Hvp Hfindp' //.
  rewrite CEP.Lemmas.find_add_neq // in H3.
  rewrite /PVM.SE.eq Hvp //.
(* Second goal: similar, just that an element is added to ct. *)
* destruct H5 as [_ [H9 [H10 H11]]].
  (*specialize (H5 0) ; rewrite /List.nth_error add0n nat_of_binK -surjective_pairing in H5.*)
  intro.
  specialize (H10 y.1 y.2) ; rewrite add1n -surjective_pairing in H10.
  specialize (H11 0 is_true_true) ; rewrite add0n nat_of_binK -surjective_pairing in H11.
  destruct (y == p) eqn: Hyp ;
        first by (move /eqP : Hyp => Hyp ;
                  rewrite CEP.Lemmas.find_add_eq /PVM.SE.eq Hyp // ;
                  apply H11).
  clear H11.
  rewrite CEP.Lemmas.find_add_neq ; last by rewrite /PVM.SE.eq Hyp //.
  assert (CEP.find y ct' = CEP.find y ct)
        by (specialize (N.eq_dec y.1 p.1) ; intro ;
            destruct H5 ; last (by apply H10 ; left ; exact n) ;
            destruct (Nat.compare_spec y.2 p.2) ;
                        first (by specialize (injective_projections y p e) ; intro ;
                                  rewrite -(nat_of_binK y.2) -(nat_of_binK p.2) H5 in H11 ;
                                  specialize (H11 Logic.eq_refl) ;
                                  rewrite H11 eq_refl // in Hyp) ;
                        first (by apply H10 ; right ; left  ; move /ltP : H5 => H5 ; exact H5) ;
                  apply H10 ; right ; right ; move /ltP : H5 => H5 ; exact H5).
  rewrite -H5 ; destruct H6 as [H6 _] ; clear ct H5 H10.
  (*assert (ports_tmap pp vm' = ports_tmap pp vm).
        clear -H2 H7 H9.
        revert H2 H7.
        induction pp ;
              first by (unfold ports_tmap ; reflexivity).
        intros ; simpl ports_tmap.
        simpl ports_have_fully_inferred_ground_types in H7.
        destruct a as [p0 [gt0| |]|p0 [gt0| |]] ; try done.
        1,2: simpl uniq in H2 ; move /andP : H2 => [H21 /andP [_ H23]].
        1,2: rewrite in_cons negb_or in H21.
        1,2: move /andP : H21 => [H21 H22].
        1,2: move /andP : H7 => [H H7].
        1,2: simpl uniq in IHpp.
        1,2: rewrite H22 H23 andTb in IHpp.
        1,2: specialize (IHpp is_true_true H7).
        1,2: rewrite IHpp.
        1,2: assert (CEP.find p0 vm' = CEP.find p0 vm)
              by (specialize (H9 p0.1 p0.2) ;
                  rewrite add1n -surjective_pairing in H9 ;
                  specialize (N.eq_dec p0.1 p.1) ; intro ;
                  destruct H0 ; last (by apply H9 ; left ; exact n) ;
                  destruct (Nat.compare_spec p0.2 p.2) ;
                        first (by specialize (injective_projections p0 p e) ; intro ;
                                  rewrite -(nat_of_binK p0.2) -(nat_of_binK p.2) H0 in H1 ;
                                  specialize (H1 Logic.eq_refl) ;
                                  rewrite H1 eq_refl // in H21) ;
                        first (by apply H9 ; right ; left  ; move /ltP : H0 => H0 ; exact H0) ;
                  apply H9 ; right ; right ; move /ltP : H0 => H0 ; exact H0).
        1,2: unfold code_type_find_vm_widths ;
             rewrite H0 ;
             fold (code_type_find_vm_widths (Gtyp gt0) p0 vm).
        1,2: reflexivity.
  rewrite H5 Hports_tmap in IHpp.*)
  apply IHpp ; last by exact H4.
  intro.
  specialize (H3 k).
  destruct (k == p) eqn: Hvp ; first by move /eqP : Hvp => Hvp ; rewrite Hvp Hfindp' //.
  rewrite CEP.Lemmas.find_add_neq // in H3.
  rewrite /PVM.SE.eq Hvp //.
Qed.

(*
Theorem ExpandBranch_Sem :
forall (vm : CEP.t vertex_type) (pp : seq HiFP.hfport) (ss : HiFP.hfstmt_seq),
    ports_have_fully_inferred_ground_types pp ->
    stmts_have_fully_inferred_ground_types ss ->
    match port_stmts_tmap pp ss vm with
    | Some tmap =>
        match ExpandPort_fun pp with
        | Some (port_conn_map, _) =>
            match ExpandBranch_funs ss (Qnil ProdVarOrder.T) port_conn_map tmap with
            | Some (def_ss, conn_map) =>
                exists (vm' vm_new : CEP.t ftype),
                              Sem_frag_ports (CEP.empty vertex_type) (CEP.empty def_expr) pp vm' port_conn_map tmap
                           /\ Sem_frag_stmts vm' port_conn_map ss vm_new conn_map
                        (* /\ vm_new is the extension of vm' with def_ss *)
            | None => True
            end
        | None => True
        end
    | None => True
    end.
*)

Definition helper_connect (v : ProdVarOrder.t) (d : def_expr) (old_ss : option HiFP.hfstmt_seq) : option HiFP.hfstmt_seq :=
(* The helper function adds a connect statement for reference v *)
match old_ss, d with
| None, _ (* propagate earlier error *)
| _, D_undefined => None (* component v is still not connected; error *)
| Some old_ss, D_invalidated => Some (Qcons (Sinvalid (Eid v)) old_ss)
| Some old_ss, D_fexpr e => Some (Qcons (Sfcnct (Eid v) e) old_ss)
end.

Lemma fold_connect_components :
forall conn_map : CEP.t def_expr,
      CEP.fold helper_connect conn_map None = None
   /\
      forall ss : HiFP.hfstmt_seq,
         match CEP.fold helper_connect conn_map (Some ss) with
         | Some conn_ss => component_stmts_of conn_ss = component_stmts_of ss
         | None => True
         end.
Proof.
intro.
assert (forall l : list (CEP.key * def_expr),
          List.fold_left
             (fun (a : option HiFP.hfstmt_seq) (p : CEP.key * def_expr)
                  => helper_connect p.1 p.2 a) l None = None).
      induction l.
      * unfold List.fold_left ; by reflexivity.
      * simpl List.fold_left ; apply IHl.
split ; first by rewrite CEP.fold_1 ; apply H.
intros.
rewrite CEP.fold_1.
revert ss.
generalize (CEP.elements conn_map).
induction l.
* intro ; simpl ; by reflexivity.
* intro ; simpl List.fold_left.
  destruct a.2 ; try (rewrite H ; trivial).
  + assert (component_stmts_of ss = component_stmts_of (Qcons (Sinvalid (Eid (var:=ProdVarOrder.T) a.1)) ss)).
          induction ss.
          + simpl ; by reflexivity.
          + simpl ; rewrite IHss ; by reflexivity.
    rewrite H0.
    apply IHl.
  + assert (component_stmts_of ss = component_stmts_of (Qcons (Sfcnct (Eid (var:=ProdVarOrder.T) a.1) h) ss)).
          induction ss.
          + simpl ; by reflexivity.
          + simpl ; rewrite IHss ; by reflexivity.
    rewrite H0.
    apply IHl.
Qed.

(* a lemma that states that helper_connect and Sem_frag_stmts are sort of inverses *)
Lemma helper_connect_Sem :
forall (vm_old : CEP.t vertex_type) (ct_old : CEP.t def_expr) (vm_new : CEP.t vertex_type) (ct_new : CEP.t def_expr) (tmap: CEP.t ftype)
       (conn_map : CEP.t def_expr),
    tmap_has_fully_inferred_ground_types tmap ->
    match (CEP.fold helper_connect conn_map (Some (Qnil ProdVarOrder.T))) with
    | Some conn_ss =>
        Sem_frag_stmts vm_old ct_old conn_ss vm_new ct_new tmap ->
               CEP.Equal vm_old vm_new
            /\
               CEP.Equal ct_new (extend_map_with conn_map ct_old)
    | None => True
    end.
Proof.
intros.
rewrite CEP.Lemmas.P.fold_spec_right.
(*
assert (List.fold_right (CEP.Lemmas.P.uncurry helper_connect)
                        (Some (Qnil ProdVarOrder.T))
                        (List.rev (PVM.elements conn_map)) =
        foldr (CEP.Lemmas.P.uncurry helper_connect)
              (Some (Qnil ProdVarOrder.T))
              (rev (CEP.elements conn_map)))
      by rewrite List.rev_alt //.
rewrite H0 ; clear H0.
generalize (perm_rev (CEP.elements conn_map)).
assert (rev (CEP.elements conn_map) = List.rev (CEP.elements conn_map))
    by rewrite List.rev_alt //.
rewrite H0 ; clear H0.*)
assert (SetoidList.equivlistA (PVM.eq_key_elt (elt:=def_expr))
                              (List.rev (CEP.elements conn_map))
                              (CEP.elements conn_map))
      by (intro ;
          apply (SetoidList.InA_rev (PVM.eq_key_elt (elt:=def_expr)))).
revert H0.
(*assert (rev (CEP.elements conn_map) = List.rev (CEP.elements conn_map))
    by rewrite List.rev_alt //.
rewrite H0 ; clear H0.*)
generalize (CEP.elements_3w conn_map) ; intro.
assert (Heqv_key : RelationClasses.Equivalence (CEP.eq_key (elt:=def_expr))) by admit.
assert (Heqv_key_elt : RelationClasses.Equivalence (CEP.eq_key_elt (elt:=def_expr))) by admit.
apply SetoidList.NoDupA_rev in H0 ; last by apply Heqv_key.
revert H0.
generalize (List.rev (CEP.elements conn_map)) as conn_map_list.
intro ; revert conn_map_list vm_old ct_old conn_map.
induction conn_map_list.
+ unfold List.fold_right.
  intros.
  split ; first by apply H2.
  intro.
  apply RelationClasses.Equivalence_Symmetric, SetoidList.equivlistA_nil_eq in H1 ;
        last by exact Heqv_key_elt.
  apply CEP.Lemmas.P.elements_Empty in H1.
  apply CEP.Lemmas.Empty_find with (x := y) in H1.
  simpl Sem_frag_stmts in H2.
  unfold extend_map_with.
  rewrite CEP.Lemmas.map2_1bis // H1.
  symmetry ; apply H2.
+ destruct a as [k v].
  simpl List.fold_right.
  intros.
  destruct ((List.fold_right (CEP.Lemmas.P.uncurry helper_connect)
                             (Some (Qnil ProdVarOrder.T)) conn_map_list)) eqn: Hfold ;
        rewrite Hfold // /CEP.Lemmas.P.uncurry /helper_connect /fst /snd.
  rewrite Hfold in IHconn_map_list.
  inversion H0 ; clear H2 H3 x l.
  destruct v ; first by done.
  - simpl Sem_frag_stmts.
    intro.
    destruct H2 as [vm' [ct' [[H2 H3] H6]]].
    specialize (IHconn_map_list vm' ct' (CEP.Lemmas.P.of_list conn_map_list)
                                H5 (CEP.Lemmas.P.of_list_2 H5) H6).
    split ; first by apply (CEP.Lemmas.Equal_trans H2), IHconn_map_list.
    apply (CEP.Lemmas.Equal_trans (proj2 IHconn_map_list)).
    intro.
    unfold extend_map_with.
    rewrite CEP.Lemmas.map2_1bis // (*CEP.Lemmas.P.of_list_1b //. *)
            CEP.Lemmas.map2_1bis //.
    specialize (H k).
    destruct (CEP.find k tmap) as [[gt| |]|] ; try by contradiction.
    rewrite /size_of_ftype /mkseq in H3 ; simpl in H3.
    rewrite N.add_0_r -surjective_pairing in H3.
    assert (Heqv_key0 : RelationClasses.Equivalence (fun x y : ProdVarOrder.T => x == y)).
            clear.
            assert (forall x y : ProdVarOrder.T, x == y -> y == x)
                  by (intros ; rewrite eq_sym //).
            assert (forall x y z : ProdVarOrder.T, x == y -> y == z -> x == z)
                  by (intros ; move /eqP : H0 => H0 ; rewrite H0 //).
            exact (RelationClasses.Build_Equivalence (fun x y : ProdVarOrder.T => x == y) (eq_refl (T := ProdVarOrder.T)) H H0).
    destruct (y == k) eqn: Hyk.
    + move /eqP : Hyk => Hyk.
      rewrite Hyk.
      destruct (PVM.find k (CEP.Lemmas.P.of_list conn_map_list)) eqn: Hfind_list.
      - contradict H4.
        apply (SetoidList.InA_eqA Heqv_key (x := (k, d))) ;
              first by rewrite /CEP.eq_key /fst /CEP.SE.eq //.
        apply SetoidList.In_InA ; first by exact Heqv_key.
        rewrite CEP.Lemmas.P.of_list_1b // in Hfind_list.
        apply SetoidList.findA_NoDupA in Hfind_list ;
              last (by exact H5) ;
              last (by exact Heqv_key0).
        (* I think there might be some lemma but I cannot find it... *)
        clear -Hfind_list.
        induction conn_map_list.
        * apply SetoidList.InA_nil in Hfind_list ; contradiction Hfind_list.
        * destruct ((k, d) == a) eqn: Hkda ; move /eqP : Hkda => Hkda ;
                first by (rewrite Hkda ; apply List.in_eq).
          apply List.in_cons, IHconn_map_list.
          inversion Hfind_list ; last by exact H0.
          clear H H1 l y.
          destruct H0.
          rewrite /PVM.SE.eq in H ; move /eqP : H => H.
          by generalize (injective_projections (k,d) a H H0) ; contradiction.
      - (* use H1 to show that PVM.find k conn_map = D_invalidated *)
        rewrite (CEP.Lemmas.elements_o conn_map k).
        generalize (SetoidList.findA_NoDupA (B := def_expr) Heqv_key0) ; intro.
        specialize H7 with (eqA_dec := HiFP.PVSLemmas.P.FM.eq_dec) (l := CEP.elements conn_map) (a := k) (b := D_invalidated) (1 := CEP.elements_3w conn_map).
        rewrite (proj1 H7).
        * destruct H3 as [H3 _] ; specialize (H3 0) ; simpl in H3.
          apply H3.
        * apply H1, SetoidList.InA_cons_hd.
          by done.
    + destruct (PVM.find y (CEP.Lemmas.P.of_list conn_map_list)) eqn: Hfind_list.
      - specialize (H1 (y, d)).
        destruct H1 as [H1 _].
        rewrite CEP.Lemmas.P.of_list_1b in Hfind_list ; last by apply H5.
        apply SetoidList.findA_NoDupA in Hfind_list ;
              last (by apply H5) ; last by apply Heqv_key0.
        apply SetoidList.InA_cons_tl with (y := (k, D_invalidated)) in Hfind_list.
        apply H1, CEP.elements_2, CEP.find_1 in Hfind_list.
        rewrite Hfind_list //.
      - destruct (PVM.find y conn_map) eqn: Hfind_map.
        * apply CEP.find_2, CEP.elements_1, H1, SetoidList.InA_cons in Hfind_map.
          destruct Hfind_map as [Hfind_map|Hfind_map] ;
                first (by rewrite /PVM.eq_key_elt /PVM.Raw.Proofs.PX.eqke /fst Hyk in Hfind_map ;
                          destruct Hfind_map as [Hfind_map _] ; done).
          rewrite CEP.Lemmas.P.of_list_1b in Hfind_list ; last by exact H5.
          apply (SetoidList.findA_NoDupA Heqv_key0 ProdVarOrder.eq_dec y d H5) in Hfind_map.
          rewrite Hfind_map // in Hfind_list.
        * destruct H3 as [_ H3].
          specialize (H3 y).
          rewrite mem_seq1 Hyk in H3.
          rewrite H3 //.
  - (* Expressions should not be very difficult... *)
    admit.
(* Here follows mostly material copied from the above proof that might be reused for expressions:
      simpl Sem_frag_stmts.
      intro.
      destruct H2 as [vm' [ct' [H2 H6]]].
      specialize (IHconn_map_list vm' ct' (CEP.Lemmas.P.of_list conn_map_list) H5)
            with (2 := H6).
      apply CEP.Lemmas.Equal_trans with (m' := (extend_map_with (CEP.Lemmas.P.of_list conn_map_list) ct')).
      * by apply IHconn_map_list, CEP.Lemmas.P.of_list_2, H5.
      * intro.
        unfold extend_map_with.
        rewrite CEP.Lemmas.map2_1bis // (*CEP.Lemmas.P.of_list_1b //. *)
                CEP.Lemmas.map2_1bis //.
        specialize (H k).
        destruct (CEP.find k tmap) as [[gt| |]|] ; try by contradiction.
        rewrite /size_of_ftype /mkseq in H3 ; simpl in H3.
        rewrite N.add_0_r -surjective_pairing in H3.
        assert (Heqv_key0 : RelationClasses.Equivalence (fun x y : ProdVarOrder.T => x == y)).
                clear.
                assert (forall x y : ProdVarOrder.T, x == y -> y == x)
                      by (intros ; rewrite eq_sym //).
                assert (forall x y z : ProdVarOrder.T, x == y -> y == z -> x == z)
                      by (intros ; move /eqP : H0 => H0 ; rewrite H0 //).
                exact (RelationClasses.Build_Equivalence (fun x y : ProdVarOrder.T => x == y) (eq_refl (T := ProdVarOrder.T)) H H0).
        destruct (y == k) eqn: Hyk.
        + move /eqP : Hyk => Hyk.
          rewrite Hyk.
          destruct (PVM.find k (CEP.Lemmas.P.of_list conn_map_list)) eqn: Hfind_list.
          - contradict H4.
            apply (SetoidList.InA_eqA Heqv_key (x := (k, d))) ;
                  first by rewrite /CEP.eq_key /fst /CEP.SE.eq //.
            apply SetoidList.In_InA ; first by exact Heqv_key.
            rewrite CEP.Lemmas.P.of_list_1b // in Hfind_list.
            apply SetoidList.findA_NoDupA in Hfind_list ;
                  last (by exact H5) ;
                  last (by exact Heqv_key0).
            (* I think there might be some lemma but I cannot find it... *)
            clear -Hfind_list.
            induction conn_map_list.
            * apply SetoidList.InA_nil in Hfind_list ; contradiction Hfind_list.
            * destruct ((k, d) == a) eqn: Hkda ; move /eqP : Hkda => Hkda ;
                    first by (rewrite Hkda ; apply List.in_eq).
              apply List.in_cons, IHconn_map_list.
              inversion Hfind_list ; last by exact H0.
              clear H H1 l y.
              destruct H0.
              rewrite /PVM.SE.eq in H ; move /eqP : H => H.
              by generalize (injective_projections (k,d) a H H0) ; contradiction.
          - (* use H1 to show that PVM.find k conn_map = D_fexpr h0 *)
            rewrite (CEP.Lemmas.elements_o conn_map k).
            generalize (SetoidList.findA_NoDupA (B := def_expr) Heqv_key0) ; intro.
            specialize H7 with (eqA_dec := HiFP.PVSLemmas.P.FM.eq_dec) (l := CEP.elements conn_map) (a := k) (b := D_fexpr h0) (1 := CEP.elements_3w conn_map).
            rewrite (proj1 H7).
            * destruct H3 as [H3 _] ; specialize (H3 0) ; simpl in H3.
              apply H3.
            * apply H1, SetoidList.InA_cons_hd.
              by done.
        + destruct (PVM.find y (CEP.Lemmas.P.of_list conn_map_list)) eqn: Hfind_list.
          - specialize (H1 (y, d)).
            destruct H1 as [H1 _].
            rewrite CEP.Lemmas.P.of_list_1b in Hfind_list ; last by apply H5.
            apply SetoidList.findA_NoDupA in Hfind_list ;
                  last (by apply H5) ; last by apply Heqv_key0.
            apply SetoidList.InA_cons_tl with (y := (k, D_fexpr h0)) in Hfind_list.
            apply H1, CEP.elements_2, CEP.find_1 in Hfind_list.
            rewrite Hfind_list //.
          - destruct (PVM.find y conn_map) eqn: Hfind_map.
            * apply CEP.find_2, CEP.elements_1, H1, SetoidList.InA_cons in Hfind_map.
              destruct Hfind_map as [Hfind_map|Hfind_map] ;
                    first (by rewrite /PVM.eq_key_elt /PVM.Raw.Proofs.PX.eqke /fst Hyk in Hfind_map ;
                              destruct Hfind_map as [Hfind_map _] ; done).
              rewrite CEP.Lemmas.P.of_list_1b in Hfind_list ; last by exact H5.
              apply (SetoidList.findA_NoDupA Heqv_key0 ProdVarOrder.eq_dec y d H5) in Hfind_map.
              rewrite Hfind_map // in Hfind_list.
            * destruct H3 as [_ H3].
              specialize (H3 y).
              rewrite mem_seq1 Hyk in H3.
              rewrite H3 //. *)
Admitted.

Theorem ExpandBranches_Sem_ct :
(* This theorem relates the connection maps generated by Sem_frag_stmts and ExpandBranch_funs. *)
forall (ss old_def_ss : HiFP.hfstmt_seq) (vm_old vm_new vm_tmap : CEP.t vertex_type)
       (ct_old ct_new old_conn_map : CEP.t def_expr) (old_scope tmap : CEP.t ftype)
       (old_tmap_scope new_tmap_scope : CEP.t ftype * CEP.t ftype),
    stmts_have_fully_inferred_ground_types ss ->
    tmap_has_fully_inferred_ground_types old_tmap_scope.1 ->
    CEP.submap old_scope old_tmap_scope.2 ->
    CEP.submap old_tmap_scope.2 old_tmap_scope.1 ->
    stmts_tmap old_tmap_scope ss vm_tmap = Some new_tmap_scope ->
    CEP.submap new_tmap_scope.1 tmap ->
    Sem_frag_stmts vm_old ct_old ss vm_new ct_new tmap ->
    CEP.Equal ct_old old_conn_map ->
       match ExpandBranch_funs ss old_def_ss old_conn_map old_scope with
       | Some (def_ss, new_conn_map, new_scope) =>
           (* def_ss = Qcat old_def_ss (component_stmts_of ss) *)
           CEP.Equal ct_new new_conn_map
       | None => True
       end
with ExpandBranch_Sem_ct :
forall (s : HiFP.hfstmt) (old_def_ss : HiFP.hfstmt_seq) (vm_old vm_new vm_tmap : CEP.t vertex_type)
       (ct_old ct_new old_conn_map : CEP.t def_expr) (old_scope tmap : CEP.t ftype)
       (old_tmap_scope new_tmap_scope : CEP.t ftype * CEP.t ftype),
    stmt_has_fully_inferred_ground_types s ->
    tmap_has_fully_inferred_ground_types old_tmap_scope.1 ->
    CEP.submap old_scope old_tmap_scope.2 ->
    CEP.submap old_tmap_scope.2 old_tmap_scope.1 ->
    stmt_tmap old_tmap_scope s vm_tmap = Some new_tmap_scope ->
    CEP.submap new_tmap_scope.1 tmap ->
    Sem_frag_stmt vm_old ct_old s vm_new ct_new tmap ->
    CEP.Equal ct_old old_conn_map ->
       match ExpandBranch_fun s old_def_ss old_conn_map old_scope with
       | Some (def_ss, new_conn_map, new_scope) =>
           (* def_ss = Qcat old_def_ss (component_stmt_of s) *)
           CEP.Equal ct_new new_conn_map
       | None => True
       end.
Proof.
* clear ExpandBranches_Sem_ct.
  induction ss ; first by (unfold Sem_frag_stmts, ExpandBranch_funs ; intros ;
                           apply (CEP.Lemmas.Equal_trans (m' := ct_old)) ; last (by apply H6) ;
                           apply CEP.Lemmas.Equal_sym, H5).
  simpl stmts_have_fully_inferred_ground_types ;
  simpl Sem_frag_stmts ;
  simpl ExpandBranch_funs.
  intros.
  move /andP : H => [H H7].
  simpl stmts_tmap in H3.
  destruct H5 as [vm' [ct' [H5 H8]]].
  specialize (ExpandBranch_Sem_ct h old_def_ss vm_old vm' vm_tmap ct_old ct' old_conn_map old_scope tmap old_tmap_scope).
  generalize (stmt_submap vm_tmap h old_tmap_scope.1 old_tmap_scope.2 H2) ; intro.
  rewrite -surjective_pairing in H9.
  specialize (ExpandBranch_stmt_tmap vm_tmap h old_tmap_scope.1)
        with (old_scope1 := old_tmap_scope.2) (old_def_ss := old_def_ss) (old_conn_map := old_conn_map) (old_scope2 := old_scope) ; intro.
  rewrite -surjective_pairing in H10.
  destruct (stmt_tmap old_tmap_scope h vm_tmap) as [[tmap' scope']|] eqn: Htmap_scope' ; last by discriminate H3.
  specialize (H10 tmap' scope') with (1 := Logic.eq_refl).
  specialize (ExpandBranch_Sem_ct (tmap', scope') H H0 H1 H2 Logic.eq_refl) with (2 := H5) (3 := H6).
  destruct (ExpandBranch_fun h old_def_ss old_conn_map old_scope) as [[[temp_def_ss temp_conn_map] temp_scope]|] ;
        last by done.
  specialize (H10 temp_scope temp_def_ss temp_conn_map Logic.eq_refl H1 H).
  specialize (stmt_tmap_preserves_fully_inferred vm_tmap old_tmap_scope.1 old_tmap_scope.2 h H H0 H2) ; intro.
  rewrite -surjective_pairing Htmap_scope' in H11.
  specialize (IHss temp_def_ss vm' vm_new vm_tmap ct' ct_new temp_conn_map temp_scope tmap (tmap', scope') new_tmap_scope H7 H11 H10 (proj1 H9) H3 H4 H8).
  apply IHss, ExpandBranch_Sem_ct.
  simpl fst.
  generalize (stmts_submap vm_tmap ss tmap' scope' (proj1 H9)) ; intro.
  rewrite H3 in H12.
  destruct new_tmap_scope as [new_tmap new_scope].
  apply (CEP.Lemmas.submap_trans (proj1 (proj2 H12))).
  apply H4.
* clear ExpandBranch_Sem_ct.
  destruct s ; simpl ; try done ; intros.
  + (* Sskip *)
    rewrite -(proj2 H5) //.
  + (* Swire *)
    destruct f as [gt| |] ; try by done.
    destruct (CEP.find s old_tmap_scope.1) ; first by discriminate H3.
    generalize (fully_inferred_does_not_change gt s vm_tmap H) ; intro.
    destruct (code_type_find_vm_widths (Gtyp gt) s vm_tmap) as [[[newgt| |] _]|] ; try by done.
    rewrite -H7 in H3 ; clear newgt H7.
    destruct new_tmap_scope as [new_tmap new_scope].
    injection H3 ; clear H3 ; intros _ H3.
    rewrite /fst -H3 in H4.
    specialize (H4 s (Gtyp gt)).
    rewrite CEP.Lemmas.find_add_eq in H4 ; last by rewrite /PVM.SE.eq //.
    rewrite H4 // /size_of_ftype add1n in H5.
    destruct H5 as [_ [_ [H5 H7]]].
    intro.
    destruct (y == s) eqn: Hys.
    - move /eqP : Hys => Hys ; rewrite Hys CEP.Lemmas.find_add_eq ; last by rewrite /PVM.SE.eq //.
      specialize (H7 N0 is_true_true).
      rewrite add0n nat_of_binK -surjective_pairing // in H7.
    - rewrite CEP.Lemmas.find_add_neq ; last by rewrite /PVM.SE.eq Hys //.
      specialize (H5 y.1 y.2).
      rewrite -surjective_pairing in H5.
      move /eqP : Hys => Hys.
      destruct (y.1 == s.1) eqn: Hys1 ; move /eqP : Hys1 => Hys1 ;
            last by (rewrite -H5 ; last (by left ; exact Hys1) ;
                     apply H6).
      destruct (Nat.compare_spec y.2 s.2).
      * specialize (injective_projections y s Hys1) ; intro.
        rewrite -(nat_of_binK y.2) -(nat_of_binK s.2) H8 in H9.
        rewrite H9 // in Hys.
      * rewrite -H5 ; first (by apply H6).
        right ; left ; move /ltP : H8 => H8 ; exact H8.
      * rewrite -H5 ; first (by apply H6).
        right ; right ; move /ltP : H8 => H8 ; exact H8.
  + (* Sreg *)
    destruct (match reset h with
              | @NRst _ => true
              | Rst rst_sig rst_val =>
                  match type_of_expr rst_sig old_scope with
                  | Some _ =>
                      match type_of_expr rst_val old_scope with
                      | Some _ => true
                      | None => false
                      end
                  | None => false
                  end
              end) ; last by done.
    destruct (type_of_expr (clock h) old_scope) ; last by done.
    destruct (type h) as [gt| |] ; try by done.
    assert (fully_inferred gt)
          by (destruct (reset h) ; move /andP : H => [_ H] ; exact H).
    clear f H ; rename H7 into H.
    destruct (CEP.find s old_tmap_scope.1) ; first by discriminate H3.
    destruct (type_of_expr (clock h) old_tmap_scope.2) ; last by discriminate H3.
    generalize (fully_inferred_does_not_change gt s vm_tmap H) ; intro.
    destruct (code_type_find_vm_widths (Gtyp gt) s vm_tmap) as [[[newgt| |] _]|] ; try by done.
    rewrite -H7 in H3 ; clear newgt H7.
    destruct new_tmap_scope as [new_tmap new_scope].
    assert (CEP.add s (Gtyp gt) old_tmap_scope.1 = new_tmap).
          destruct (reset h).
          2: destruct (type_of_expr h0 old_tmap_scope.2) ; last by discriminate H3.
          2: destruct (type_of_expr h1 old_tmap_scope.2) ; last by discriminate H3.
          1,2: injection H3 ; done.
    clear H3 ; rename H7 into H3.
    rewrite /fst -H3 in H4.
    specialize (H4 s (Gtyp gt)).
    rewrite CEP.Lemmas.find_add_eq in H4 ; last by rewrite /PVM.SE.eq //.
    rewrite H4 // /size_of_ftype add1n in H5.
    destruct H5 as [_ [_ [_ [H7 [_ H5]]]]].
    intro.
    destruct (y == s) eqn: Hys.
    - move /eqP : Hys => Hys ; rewrite Hys CEP.Lemmas.find_add_eq ; last by rewrite /PVM.SE.eq //.
      specialize (H7 N0).
      simpl in H7.
      rewrite add0n nat_of_binK -surjective_pairing // in H7.
    - rewrite CEP.Lemmas.find_add_neq ; last by rewrite /PVM.SE.eq Hys //.
      specialize (H5 y.1 y.2).
      rewrite -surjective_pairing in H5.
      move /eqP : Hys => Hys.
      destruct (y.1 == s.1) eqn: Hys1 ; move /eqP : Hys1 => Hys1 ;
            last by (rewrite -H5 ; last (by left ; exact Hys1) ;
                     apply H6).
      destruct (Nat.compare_spec y.2 s.2).
      * specialize (injective_projections y s Hys1) ; intro.
        rewrite -(nat_of_binK y.2) -(nat_of_binK s.2) H8 in H9.
        rewrite H9 // in Hys.
      * rewrite -H5 ; first (by apply H6).
        right ; left ; move /ltP : H8 => H8 ; exact H8.
      * rewrite -H5 ; first (by apply H6).
        right ; right ; move /ltP : H8 => H8 ; exact H8.
  + (* Snode *)
    destruct (type_of_expr h old_scope) as [[_ _]|] ; last by done.
    generalize (@CEP.Lemmas.submap_add_find_none _ old_tmap_scope.1 tmap s) ; intro.
    destruct (CEP.find s old_tmap_scope.1) ; first by discriminate H3.
    generalize (expr_preserves_fully_inferred old_tmap_scope.1 H0 h H) ; intro.
    generalize (type_of_expr_submap h old_tmap_scope.2 old_tmap_scope.1 H2) ; intro.
    generalize (type_of_expr_submap h old_tmap_scope.1 tmap) ; intro.
    destruct (type_of_expr h old_tmap_scope.2) as [[newt p]|] ; last by discriminate H3.
    rewrite H9 in H8 H10 ; clear H9.
    destruct newt as [gt| |] ; try by contradiction H8.
    destruct new_tmap_scope as [new_tmap new_scope].
    injection H3 ; clear H3 ; intros _ H3.
    rewrite /fst -H3 in H4.
    specialize (H7 (Gtyp gt) H4 Logic.eq_refl).
    rewrite (H10 H7) in H5 ; clear p H10 H7.
    destruct H5 as [_ [_ [H5 H7]]].
    intro.
    destruct (y == s) eqn: Hys.
    - move /eqP : Hys => Hys ; rewrite Hys CEP.Lemmas.find_add_eq ; last by rewrite /PVM.SE.eq //.
      replace (list_rhs_expr_p h (Gtyp gt)) with (Some [:: h]) in H7
            by (destruct h ; done).
      specialize (H7 N0).
      rewrite add0n nat_of_binK -surjective_pairing // in H7.
    - rewrite CEP.Lemmas.find_add_neq ; last by rewrite /PVM.SE.eq Hys //.
      specialize (H5 y.1 y.2).
      rewrite -surjective_pairing in H5.
      move /eqP : Hys => Hys.
      destruct (y.1 == s.1) eqn: Hys1 ; move /eqP : Hys1 => Hys1 ;
            last by (rewrite -H5 ; last (by left ; exact Hys1) ;
                     apply H6).
      destruct (Nat.compare_spec y.2 s.2).
      * specialize (injective_projections y s Hys1) ; intro.
        rewrite -(nat_of_binK y.2) -(nat_of_binK s.2) H9 in H10.
        rewrite H10 // in Hys.
      * rewrite -H5 ; first (by apply H6).
        right ; left ; move /ltP : H9 => H9 ; exact H9.
      * rewrite -H5 ; first (by apply H6).
        right ; right ; move /ltP : H9 => H9 ; exact H9.
  + (* Sfcnct *)
    unfold ExpandBranch_connect.
    destruct h ; try (by done) ; last by (destruct h ; try done ; destruct h ; done).
    generalize (type_of_expr_submap h0 old_scope old_tmap_scope.2 H1) ; intro.
    specialize (H1 s).
    destruct (CEP.find s old_scope) as [ft_ref|] ; last by done.
    specialize (H1 ft_ref Logic.eq_refl).
    destruct (type_of_expr h0 old_scope) as [[ft_expr p]|] ; last by done.
    destruct (connect_type_compatible false ft_ref ft_expr false) ; last by done.
    rewrite /type_of_ref H1 H7 in H3.
    injection H3 ; clear H3 ; intro H3.
    rewrite -H3 in H4 ; clear new_tmap_scope H3.
    generalize (type_of_expr_submap h0 old_tmap_scope.2 old_tmap_scope.1 H2) ; intro.
    rewrite H7 in H3.
    generalize (type_of_expr_submap h0 old_tmap_scope.1 tmap H4) ; intro.
    rewrite H3 in H8.
    generalize (expr_preserves_fully_inferred old_tmap_scope.1 H0 h0 H) ; intro.
    rewrite H3 in H9.
    destruct ft_expr as [gt_expr| |] ; try by contradiction H9.
    specialize (H2 s ft_ref) ; rewrite H1 in H2.
    specialize (H0 s) ; rewrite H2 // in H0.
    destruct ft_ref as [gt_ref| |] ; try by contradiction H0.
    specialize (H4 s (Gtyp gt_ref)) ; rewrite H2 // in H4.
    simpl list_lhs_ref_p in H5.
    rewrite /type_of_ref H4 // H8 in H5.
    replace (list_rhs_expr_p h0 (Gtyp gt_expr)) with (Some [:: h0]) in H5
          by (destruct h0 ; done).
    destruct h0.
    (* h0 is a normal expression *)
    1-6: destruct H5 as [_ [H10 H5]].
    1-6: intro.
    1-6: destruct (y == s) eqn: Hys ;
            first (by rewrite CEP.Lemmas.find_add_eq ; last (by rewrite /PVM.SE.eq Hys //) ;
                      destruct H5 as [H5 _] ;
                      specialize (H5 0) ; simpl in H5 ;
                      rewrite N.add_0_r -surjective_pairing in H5 ;
                      move /eqP : Hys => Hys ;
                      rewrite Hys (proj2 H5) //).
    1-6: rewrite CEP.Lemmas.find_add_neq ; last (by rewrite /PVM.SE.eq Hys //).
    1-6: destruct H5 as [_ H5].
    1-6: specialize (H5 y).
    1-6: rewrite /mkseq in H5 ; simpl map in H5.
    1-6: rewrite N.add_0_r -surjective_pairing mem_seq1 Hys in H5.
    1-6: rewrite -H5 //.
    (* h0 is a reference *)
    destruct H5 as [_ H5].
    simpl expr_has_fully_inferred_ground_types in H.
    simpl type_of_expr in H8.
    generalize (list_lhs_ref_p_type tmap h) ; intro.
    destruct (list_lhs_ref_p h tmap) as [[lst_src ft_src]|] ; last by contradiction H5.
    destruct (type_of_ref h tmap) as [ft_ref'|] ; last by discriminate H8.
    rewrite H10 in H8 ; clear ft_ref' H10.
    destruct ft_src as [gt_src| |] ;
          last (by injection H8 ;
                   destruct (make_ffield_explicit f) ;
                   intro ; inversion_sigma H10 ; discriminate H10_) ;
          last (by injection H8 ;
                   destruct (make_ftype_explicit ft_src) ;
                   intro ; inversion_sigma H10 ; discriminate H10_).
    destruct H5 as [H10 [H11 H5]].
    simpl in H11.
    destruct lst_src as [|oc lst_src'] ; first by done.
    destruct lst_src' ; last by done.
    intro.
    destruct (y == s) eqn: Hys.
    - rewrite CEP.Lemmas.find_add_eq ; last by (rewrite /PVM.SE.eq Hys //).
      move /eqP : Hys => Hys.
      rewrite Hys.
      move /andP : H11 => [/andP [_ /eqP H11] _].
      rewrite N.add_0_r -surjective_pairing // in H11.
    - rewrite CEP.Lemmas.find_add_neq ; last (by rewrite /PVM.SE.eq Hys //).
      destruct (y == oc) eqn: Hyoc.
      * move /eqP : Hyoc => Hyoc.
        move /andP : H11 => [_ /eqP H11].
        rewrite Hyoc H11 //.
      * specialize (H5 y).
        rewrite /mkseq in H5 ; simpl map in H5.
        rewrite N.add_0_r -surjective_pairing mem_seq1 Hys orFb mem_seq1 Hyoc in H5.
        rewrite -H5 //.
  + (* Sinvalid *)
    unfold ExpandBranch_connect.
    destruct h ; try (by done) ; last by (destruct h ; try done ; destruct h ; done).
    specialize (H1 s).
    destruct (CEP.find s old_scope) as [ft_ref|] ; last by done.
    specialize (H1 ft_ref Logic.eq_refl).
    rewrite /type_of_ref H1 in H3.
    injection H3 ; clear H3 ; intro H3.
    rewrite -H3 in H4 ; clear new_tmap_scope H3.
    specialize (H2 s ft_ref) ; rewrite H1 in H2.
    specialize (H4 s ft_ref) ; rewrite H2 // in H4.
    simpl list_lhs_ref_p in H5.
    rewrite H4 // in H5.
    specialize (H0 s).
    rewrite H2 // in H0.
    destruct ft_ref as [gt_ref| |] ; try by contradiction H0.
    destruct H5 as [_ H5].
    intro.
    destruct (y == s) eqn: Hys ;
            first (by rewrite CEP.Lemmas.find_add_eq ; last (by rewrite /PVM.SE.eq Hys //) ;
                      destruct H5 as [H5 _] ;
                      specialize (H5 0) ; simpl in H5 ;
                      rewrite N.add_0_r -surjective_pairing in H5 ;
                      move /eqP : Hys => Hys ;
                      rewrite Hys (proj2 H5) //).
    rewrite CEP.Lemmas.find_add_neq ; last (by rewrite /PVM.SE.eq Hys //).
    destruct H5 as [_ H5].
    specialize (H5 y).
    rewrite /mkseq in H5 ; simpl map in H5.
    rewrite N.add_0_r -surjective_pairing mem_seq1 Hys in H5.
    rewrite -H5 //.
  + (* Swhen *)
    rename h into cond ; rename h0 into ss_true ; rename h1 into ss_false.
    destruct (type_of_expr cond old_tmap_scope.2) ; last by discriminate H3.
    generalize (stmts_submap vm_tmap ss_true old_tmap_scope.1 old_tmap_scope.2 H2) ; intro.
    rewrite -(surjective_pairing) in H7.
    assert (CEP.submap old_scope tmap).
          apply (CEP.Lemmas.submap_trans H1).
          apply (CEP.Lemmas.submap_trans H2).
          destruct (stmts_tmap old_tmap_scope ss_true vm_tmap) as [[tmap_true scope_true]|] ; last by discriminate H3.
          generalize (CEP.Lemmas.submap_trans (proj2 (proj2 H7)) (proj1 H7)) ; intro.
          generalize (stmts_submap vm_tmap ss_false tmap_true old_tmap_scope.2 H8) ; intro.
          destruct (stmts_tmap (tmap_true, old_tmap_scope.2) ss_false vm_tmap) as [[tmap_false scope_false]|] ; last by discriminate H3.
          apply (CEP.Lemmas.submap_trans (proj1 (proj2 H7))).
          apply (CEP.Lemmas.submap_trans (proj1 (proj2 H9))).
          destruct new_tmap_scope as [new_tmap new_scope].
          injection H3 ; clear H3 ; intros _ H3.
          rewrite H3 //.
    generalize (type_of_expr_submap cond old_scope tmap H8) ; intro.
    destruct (type_of_expr cond old_scope) as [[[[[|[]]| | | | | |]| |] p]|] ; try by done.
    generalize (ExpandBranches_Sem_ct ss_true old_def_ss vm_old) ; intro.
    specialize H10 with (vm_tmap := vm_tmap) (old_tmap_scope := old_tmap_scope).
    move /andP : H => [Htrue Hfalse].
    generalize (stmts_tmap_preserves_fully_inferred vm_tmap ss_true old_tmap_scope.1 old_tmap_scope.2 Htrue H0 H2) ; intro.
    rewrite -surjective_pairing in H.
    destruct (stmts_tmap old_tmap_scope ss_true vm_tmap) as [[tmap_true scope_true]|] ; last by discriminate H3.
    rewrite H9 in H5.
    destruct H5 as [vm_true [ct_true [ct_false H5]]].
    specialize (H10 vm_true ct_old ct_true old_conn_map old_scope tmap (tmap_true, scope_true) Htrue H0 H1 H2 Logic.eq_refl)
          with (2 := proj1 H5) (3 := H6).
    destruct (ExpandBranch_funs ss_true old_def_ss old_conn_map old_scope) as [[[true_def_ss true_conn_map] _]|] ; last by done.
    assert (CEP.submap old_tmap_scope.2 tmap_true)
          by (apply (CEP.Lemmas.submap_trans (proj2 (proj2 H7)) (proj1 H7))).
    specialize (ExpandBranches_Sem_ct ss_false true_def_ss vm_true vm_new vm_tmap (extend_map_with ct_old ct_true) ct_false (extend_map_with old_conn_map true_conn_map) old_scope tmap (tmap_true, old_tmap_scope.2))
          with (1 := Hfalse) (2 := H) (3 := H1) (4 := H11) (7 := proj1 (proj2 H5)).
    generalize (stmts_submap vm_tmap ss_false tmap_true old_tmap_scope.2 H11) ; intro.
    destruct (stmts_tmap (tmap_true, old_tmap_scope.2) ss_false vm_tmap) as [[tmap_false scope_false]|] ; last by discriminate H3.
    destruct new_tmap_scope as [new_tmap new_scope].
    injection H3 ; clear H3 ; intros _ H3.
    rewrite -H3 /fst in H4.
    specialize (ExpandBranches_Sem_ct (tmap_false, scope_false) Logic.eq_refl H4).
    destruct (ExpandBranch_funs ss_false true_def_ss (extend_map_with old_conn_map true_conn_map) old_scope) as [[[false_def_ss false_conn_map] _]|] ; last by done.
    destruct H5 as [_ [_ H5]].
    intro.
    rewrite (H5 y) CEP.Lemmas.map2_1bis ; last by rewrite /helper_tf //.
    rewrite CEP.Lemmas.map2_1bis ; last by rewrite /Swhen_map2_helper //.
    assert (CEP.submap tmap_true tmap)
          by (apply (CEP.Lemmas.submap_trans (proj1 (proj2 H12)) H4)).
    specialize (H10 H13).
    assert (CEP.Equal (extend_map_with ct_old ct_true)
                      (extend_map_with old_conn_map true_conn_map))
          by (intro ; specialize (H6 y0) ; specialize (H10 y0) ;
              rewrite /extend_map_with CEP.Lemmas.map2_1bis // CEP.Lemmas.map2_1bis // H6 H10 //).
    specialize (ExpandBranches_Sem_ct H14).
    rewrite (ExpandBranches_Sem_ct y).
    rewrite (H10 y) /Swhen_map2_helper /helper_tf.
    destruct (CEP.find y true_conn_map) as [[]|] ; destruct (CEP.find y false_conn_map) as [[]|] ; reflexivity.
Qed.



(*
forall (vm_old vm_new : CEP.t vertex_type) (pp : seq HiFP.hfport) (ss : HiFP.hfstmt_seq),
    ports_have_fully_inferred_ground_types pp ->
    stmts_have_fully_inferred_ground_types ss ->
    match port_stmts_tmap pp ss vm with
    | Some tmap =>
        match ExpandPort_fun pp with
        | Some (port_conn_map, _) =>
            match ExpandBranch_funs ss old_def_ss ct_old old_scope with
            | Some (def_ss, new_conn_map, new_scope) =>
                exists (vm' vm_new : CEP.t ftype),
                              Sem_frag_ports (CEP.empty vertex_type) (CEP.empty def_expr) pp vm' port_conn_map tmap
                           /\ Sem_frag_stmts vm' port_conn_map ss vm_new conn_map
                        (* /\ vm_new is the extension of vm' with def_ss *)
            | None => True
            end
        | None => True
        end
    | None => True
    end.
*)

(* What would a theorem to relate expandBranch_funs with Sem_frag_stmts look like?
   We need to find an inductive formulation.
   At first let us concentrate on the connection map.

   So we need something like:

   Given Sem_frag_stmts vm_old ct_old ss vm_new ct_new tmap
     and ExpandBranch_funs ss old_def_ss ct_old old_scope = Some (def_ss, new_conn_map, new_scope)
   then def_ss = Qcat old_def_ss (component_stmts_of ss)
    and CEP.Equal ct_new new_conn_map
   (and something about vm_old and vm_new, perhaps through def_ss?)
   (and something about the scopes? -- probably not needed)

Ultimately we want:
   Given ExpandBranch_funs ss old_def_ss ct_old old_scope = Some (def_ss, new_conn_map, new_scope)
     and Sem_frag_stmts vm_old ct_old (Qcat def_ss (CEP.fold helper_connect conn_map (Some (Qnil ProdVarOrder.T)))) vm_new ct_new tmap,
   then Sem_frag_stmts vm_old ct_old ss vm_new ct_new tmap.
*)

(*
Lemma split_when :
    Sem_frag_stmt vm_old ct_old (Swhen cond ss_true ss_false) vm_new ct_new tmap ->
    Sem_frag_stmts vm_old ct_old (Qcat (component_stmt_of (Swhen cond ss_true ss_false))
                                       (connection_stmt_of (Swhen cond ss_true ss_false))) vm_new ct_new tmap.
*)

(* I don't think the following lemma is actually needed.

Lemma Sem_frag_stmts_reorder_component :
forall (ss: HiFP.hfstmt_seq) (s : HiFP.hfstmt) (vm_old : CEP.t vertex_type) (ct_old : CEP.t def_expr) (vm_new : CEP.t vertex_type) (ct_new : CEP.t def_expr) (tmap : CEP.t ftype),
    tmap_has_fully_inferred_ground_types tmap ->
    vm_and_ct_compatible vm_old ct_old ->
    stmt_has_fully_inferred_ground_types s ->
    stmts_have_fully_inferred_ground_types ss ->
    (exists old_tmap_scope vm new_tmap_scope, 
            CEP.submap old_tmap_scope.2 old_tmap_scope.1
        /\
            stmt_tmap  old_tmap_scope s  vm = Some new_tmap_scope
        /\
            CEP.submap new_tmap_scope.2 tmap) ->
    (exists old_tmap_scope vm new_tmap_scope,
            CEP.submap old_tmap_scope.2 old_tmap_scope.1
        /\
            stmts_tmap old_tmap_scope ss vm = Some new_tmap_scope
        /\
            CEP.submap new_tmap_scope.2 tmap) ->
    Sem_frag_stmts vm_old ct_old (Qcat (component_stmt_of s)
                                       (component_stmts_of ss)) vm_new ct_new tmap ->
    Sem_frag_stmts vm_old ct_old (Qcat (component_stmts_of ss)
                                       (component_stmt_of s)) vm_new ct_new tmap.
Proof.
induction ss.
* simpl Qcat.
  intros.
  rewrite Qcats0 in H5.
  exact H5.
* simpl component_stmts_of.
  intros.
  rewrite -Qcat_assoc in H5.
  apply Sem_frag_stmts_cat in H5.
  destruct H5 as [vm_temp [ct_temp [H5 H6]]].
  (* now show that in H5, the two component statements can be inversed. *)
  assert (Sem_frag_stmts vm_old ct_old
          (Qcat (component_stmt_of h) (component_stmt_of s)) vm_temp ct_temp tmap).
        simpl in H2.
        move /andP : H2 => [H2 _].
        assert (exists (old_tmap_scope : CEP.t ftype * CEP.t ftype) 
                       (vm : CEP.t vertex_type)
                       (new_tmap_scope : CEP.t ftype * CEP.t ftype),
                stmt_tmap old_tmap_scope h vm =
                Some new_tmap_scope /\ CEP.submap new_tmap_scope.2 tmap).
              destruct H4 as [old_tmap_scope_h [vm_h [[new_tmap_h new_scope_h] H4]]].
              exists old_tmap_scope_h, vm_h.
              simpl stmts_tmap in H4.
              generalize (stmt_submap vm_h h old_tmap_scope_h.1 old_tmap_scope_h.2 (proj1 H4)) ; intro.
              rewrite -surjective_pairing in H7.
              destruct (stmt_tmap old_tmap_scope_h h vm_h) as [[temp_tmap_h temp_scope_h]|] ;
                    last by discriminate (proj1 (proj2 H4)).
              exists (temp_tmap_h, temp_scope_h).
              split ; first by reflexivity.
              generalize (stmts_submap vm_h ss temp_tmap_h temp_scope_h (proj1 H7)) ; intro.
              rewrite (proj1 (proj2 H4)) in H8.
              by apply (CEP.Lemmas.submap_trans (proj2 (proj2 H8))), H4.
        clear H4 H6 IHss ss.
        destruct h ;
              try (by simpl Qcat ; simpl Qcat in H5 ; rewrite Qcats0 in H5 ; exact H5) ;
              apply Sem_frag_stmts_cat in H5 ;
              destruct H5 as [vm'' [ct'' [Hs Hh]]] ;
              apply Sem_frag_stmts_cat ;
              simpl in H2.
        * (* Swire *)
          destruct f as [gt1| |] ; try by done.
          exists (CEP.add s0 (Wire gt1) vm_old), (CEP.add s0 D_undefined ct_old).
          split.
          + simpl.
            exists (CEP.add s0 (Wire gt1) vm_old), (CEP.add s0 D_undefined ct_old).
            split ; last by split ; apply CEP.Lemmas.Equal_refl.
            simpl in Hh.
            destruct Hh as [vm_temph [ct_temph [Hh Hh_eq]]].
            generalize (H s0) ; intro.
            destruct H7 as [old_tmap_scope_h [vm_h [[new_tmap_h new_scope_h] H7]]].
            unfold stmt_tmap in H7.
            destruct (CEP.find s0 old_tmap_scope_h.1) ; first by discriminate (proj1 H7).
            generalize (fully_inferred_does_not_change gt1 s0 vm_h H2) ; intro.
            destruct (code_type_find_vm_widths (Gtyp gt1) s0 vm_h) as [[[newgt1| |] _]|] ;
                  last (by discriminate (proj1 H7)) ; try by contradiction H5.
            rewrite -H5 in H7 ; clear H5 newgt1.
            injection (proj1 H7) ; intros H6 _.
            destruct H7 as [_ H7] ; rewrite /snd -H6 in H7.
            specialize (H7 s0 (Gtyp gt1)).
            rewrite CEP.Lemmas.find_add_eq in H7 ; last by rewrite /PVM.SE.eq //.
            specialize (H7 Logic.eq_refl).
            clear H6 old_tmap_scope_h vm_h new_tmap_h new_scope_h.
            rewrite H7 in H4, Hh ; rewrite H7 ; clear H7.
            generalize (Sem_frag_stmts_compatible (component_stmt_of s) vm_old ct_old vm'' ct'' tmap Hs) ; intro.
            split.
            - destruct Hh as [Hh _].
              intro ; specialize (Hh n).
              destruct n.
              * simpl ; simpl in Hh.
                rewrite add0n nat_of_binK -surjective_pairing.
                rewrite add0n nat_of_binK -surjective_pairing in Hh.
                split.
                + destruct H5 as [H5 _] ; specialize (H5 s0).
                  rewrite (proj1 Hh) in H5.
                  destruct (CEP.find s0 vm_old) ; last by reflexivity.
                  rewrite (H5 v) //.
                + rewrite CEP.Lemmas.find_add_eq // /PVM.SE.eq //.
              * simpl.
                rewrite (proj2 (List.nth_error_None [::] n)) // /length.
                by apply Nat.le_0_l.
            split.
            - (*destruct Hh as [_ [Hh _]].*)
              intros.
              rewrite CEP.Lemmas.find_add_neq // /PVM.SE.eq (surjective_pairing s0).
              destruct H6 as [H6|[H6|H6]].
              3: rewrite /size_of_ftype add1n in H6.
              2,3: rewrite ltn_neqAle in H6 ; move /andP : H6 => [/eqP H6 _].
              1,2,3: contradict H6 ; move /eqP : H6 => H6 ; injection H6.
              done.
              1,2: intros H7 _ ; rewrite H7 //.
            split.
            - (*destruct Hh as [_ [_ [Hh _]]].*)
              intros.
              rewrite CEP.Lemmas.find_add_neq // /PVM.SE.eq (surjective_pairing s0).
              destruct H6 as [H6|[H6|H6]].
              3: rewrite /size_of_ftype add1n in H6.
              2,3: rewrite ltn_neqAle in H6 ; move /andP : H6 => [/eqP H6 _].
              1,2,3: contradict H6 ; move /eqP : H6 => H6 ; injection H6.
              done.
              1,2: intros H7 _ ; rewrite H7 //.
            - (*destruct Hh as [_ [_ [_ Hh]]].*)
              intros (* ; specialize (Hh n0 H6)*).
              rewrite /size_of_ftype ltnS leqn0 in H6.
              move /eqP : H6 => H6.
              rewrite H6 add0n nat_of_binK -surjective_pairing CEP.Lemmas.find_add_eq // /PVM.SE.eq //.
          + assert (CEP.Equal (CEP.add s0 (Wire gt1) vm'') vm_temp /\ CEP.Equal (CEP.add s0 D_undefined ct'') ct_temp)
                  by admit. (* basically the same proof as above. *)
            destruct s ;
                  try by (simpl ; simpl in Hs ;
                          split ; intro ; destruct (y == s0) eqn: Hys0 ;
                          first (by rewrite -(proj1 H4) CEP.Lemmas.find_add_eq // CEP.Lemmas.find_add_eq //) ;
                          first (by move /negP : Hys0 => Hys0 ;
                                 rewrite -(proj1 H4) CEP.Lemmas.find_add_neq // CEP.Lemmas.find_add_neq // (proj1 Hs) //) ;
                          first (by rewrite -(proj2 H4) CEP.Lemmas.find_add_eq // CEP.Lemmas.find_add_eq //) ;
                          move /negP : Hys0 => Hys0 ;
                          rewrite -(proj2 H4) CEP.Lemmas.find_add_neq // CEP.Lemmas.find_add_neq // (proj2 Hs) //).
            - (* Wire / Wire *)
              (* again, basically the same proof as above...
                 only need to check whether s == s0 or not. *)
Admitted.
(* Perhaps a more economical way to prove the above lemma is:
   if everything is fully inferred,
   then most component statements just add one element each to vm and ct.
   Then any pair of such component statements can be verified
   using CEP.Lemmas.add_comm.
   The only statement that is more complex is Swhen. *)
*)

(* The point is perhaps rather:
in the induction step of the correctness theorem,
we have something like
old graph -> one statement -> temp graph -> sequence of statements -> new graph

We know (as induction hypothesis) that for the sequence of statements, we can transform
from a split (component/connection) to a single sequence of combined statements.

We also know (as the other induction hypothesis) that the one statement
can be transformed from a split (component/connection) to a single statement.

We have then to show that the connection part of the one statement
can be moved through the sequence of statements.
This is basically done by Sem_frag_stmts_component_Equal.

In the corresponding theorem for single statements,
the only complex case is the Swhen statement.

*)

(* I am unsure whether the following lemma is needed at all.
Lemma stmts_components_connections :
forall (ss : HiFP.hfstmt_seq) (vm_old : CEP.t vertex_type) (ct_old : CEP.t def_expr) (vm_new1 vm_new2 : CEP.t vertex_type) (ct_new1 ct_new2 : CEP.t def_expr) (tmap: CEP.t ftype),
    tmap_has_fully_inferred_ground_types tmap ->
    vm_and_ct_compatible vm_old ct_old ->
    stmts_have_fully_inferred_ground_types ss ->
    Sem_frag_stmts vm_old ct_old (Qcat (component_stmts_of ss) (connection_stmts_of ss)) vm_new1 ct_new1 tmap ->
    Sem_frag_stmts vm_old ct_old ss vm_new2 ct_new2 tmap ->
        CEP.Equal vm_new1 vm_new2 /\ CEP.Equal ct_new1 ct_new2
with stmt_components_connections :
forall (s : HiFP.hfstmt) (vm_old : CEP.t vertex_type) (ct_old : CEP.t def_expr) (vm_new1 vm_new2 : CEP.t vertex_type) (ct_new1 ct_new2 : CEP.t def_expr) (tmap: CEP.t ftype),
    tmap_has_fully_inferred_ground_types tmap ->
    vm_and_ct_compatible vm_old ct_old ->
    stmt_has_fully_inferred_ground_types s ->
    Sem_frag_stmts vm_old ct_old (Qcat (component_stmt_of s) (connection_stmt_of s)) vm_new1 ct_new1 tmap ->
    Sem_frag_stmt vm_old ct_old s vm_new2 ct_new2 tmap ->
        CEP.Equal vm_new1 vm_new2 /\ CEP.Equal ct_new1 ct_new2.
Proof.
* clear stmts_components_connections.
  induction ss.
  + simpl ; intros.
    split.
    - apply (CEP.Lemmas.Equal_trans (CEP.Lemmas.Equal_sym (proj1 H2))), H3.
    - apply (CEP.Lemmas.Equal_trans (CEP.Lemmas.Equal_sym (proj2 H2))), H3.
  + simpl ; intros.
    move /andP : H1 => [H11 H12].
    destruct H3 as [vm' [ct' [H31 H32]]].
    generalize (proj2 (proj2 (Sem_frag_stmt_compatible h vm_old ct_old vm' ct' tmap H31)) H0) ; intro.
    destruct h.
    - (* Sskip *)
      simpl Qcat in H2.
      simpl in H31.
      generalize (Sem_frag_stmts_Equal ss vm' vm_old ct' ct_old vm_new2 vm_new2 ct_new2 ct_new2 tmap tmap
                  (CEP.Lemmas.Equal_sym (proj1 H31)) (CEP.Lemmas.Equal_sym (proj2 H31))
                  (CEP.Lemmas.Equal_refl _) (CEP.Lemmas.Equal_refl _) (CEP.Lemmas.Equal_refl _)
                  H32) ; intro.
      apply (IHss vm_old ct_old) with (tmap := tmap) ; by assumption.
    - (* Swire, a component statement *)
      rewrite Qcat_assoc in H2.
      apply Sem_frag_stmts_cat in H2.
      simpl component_stmt_of in H2 ; simpl Qcat in H2.
      destruct H2 as [vm_temp [ct_temp [H21 H22]]].
      apply (IHss vm' ct') with (tmap := tmap) ; try by assumption.
      admit. (* almost H22 but I am impatient... *)
    - (* Sreg, similar to Swire *)
      admit.
    - (* Smem : TBD *)
      contradiction H31.
    - (* Sinst : TBD *)
      contradiction H31.
    - (* Snode, similar to Swire *)
      admit.
    - (* Sfcnct: that needs a different treatment than the above ones. *)
      (* basically we have two routes to get ct_new1 and ct_new2:
         ct_old -> component_stmts_of ss -> ct_temp1 -> Sfcnct h0 h1 -> ct_temp2 -> connection_stmts_of ss -> ct_new1
         ct_old -> Sfcnct h0 h1 -> ct' -> ss -> ct_new2.
         We should show that the change from ct_temp1 to ct_temp2
         is the same as the change from ct_old to ct'.
         Then we can use Sem_frag_stmts_component_Equal to show:
         ct_old -> Sfcnct h0 h1 -> ct' -> component_stmts_of ss -> ct_temp2 -> connection_stmts_of ss -> ct_new1 *)
      apply (IHss vm' ct') with (tmap := tmap) ; try by assumption.
      apply Sem_frag_stmts_cat.
      apply Sem_frag_stmts_cat in H2.
      destruct H2 as [vm_temp1 [ct_temp1 [H2 H4]]].
      apply Sem_frag_stmts_cat in H4.
      destruct H4 as [vm_temp2 [ct_temp2 [H4 H5]]].
      exists vm_temp2, ct_temp2.
      split ; last by exact H5.
      simpl Qcat in H2.
      generalize (proj2 (Sem_frag_stmt_compatible (Sfcnct h h0) vm_old ct_old vm' ct' tmap H31)) ; intro.
      assert (CEP.Equal vm_old vm').
            simpl in H31.
            destruct h0 ; by apply H31.
      assert (CEP.Equal vm_temp1 vm_temp2).
            simpl in H4.
            destruct H4 as [vm'' [ct'' [H41 [H42 _]]]].
            destruct h0 ; by apply (CEP.Lemmas.Equal_trans (proj1 H41) H42).
      generalize (Sem_frag_stmts_component_Equal ss vm_old vm' ct_old ct' vm_temp1 vm_temp2 ct_temp1 tmap tmap
                  H0 (proj2 H3 H0) H6 H7 (CEP.Lemmas.Equal_refl _) H2) ; intro.
      generalize (Sem_frag_stmts_component ss vm_old ct_old vm_temp1 ct_temp1 tmap H0 H2) ; intro.
      apply Sem_frag_stmts_Equal with (vm_old1 := vm') (ct_old1 := ct') (vm_new1 := vm_temp2) (ct_new1 := extend_map_with ct' ct_temp1) (tmap1 := tmap) ;
            try (by apply CEP.Lemmas.Equal_refl) ;
            last by exact H8.
      (* use H4 and H31 together. Need to argue in detail now. *)
      intro.
      rewrite CEP.Lemmas.map2_1bis //.
      simpl in H4.
      destruct H4 as [vm_temp2' [ct_temp2' [H41 [_ H42]]]].
      simpl in H31.
      move /andP : H11 => H11.
      (* generalize (ref_preserves_fully_inferred tmap H h0 (proj1 H11)) ; intro. *)
      generalize (expr_preserves_fully_inferred tmap H h0 (proj2 H11)) ; intro.
      specialize (H42 y) ; rewrite -H42.
      destruct h0.
      1-6: destruct H31 as [_ H31] ; destruct H41 as [_ H41].
      1-6: generalize (list_lhs_ref_p_type tmap h) ; intro.
      1-6: destruct (type_of_ref h tmap) as [ft_ref|] ; last (by contradiction H31).
      1: destruct (type_of_expr (Econst ProdVarOrder.T f b) tmap) as [[[gt_expr| |] _]|] ; last (by contradiction H31) ; try by contradiction H4.
      2: destruct (type_of_expr (Ecast u h0) tmap) as [[[gt_expr| |] _]|] ; last (by contradiction H31) ; try by contradiction H4.
      3: destruct (type_of_expr (Eprim_unop e h0) tmap) as [[[gt_expr| |] _]|] ; last (by contradiction H31) ; try by contradiction H4.
      4: destruct (type_of_expr (Eprim_binop e h0_1 h0_2) tmap) as [[[gt_expr| |] _]|] ; last (by contradiction H31) ; try by contradiction H4.
      5: destruct (type_of_expr (Emux h0_1 h0_2 h0_3) tmap) as [[[gt_expr| |] _]|] ; last (by contradiction H31) ; try by contradiction H4.
      6: destruct (type_of_expr (Evalidif h0_1 h0_2) tmap) as [[[gt_expr| |] _]|] ; last (by contradiction H31) ; try by contradiction H4.
      1-6: destruct ft_ref as [gt_ref| |] ;
            try by (destruct H41 as [H41 _] ; done).
      1-6: destruct H31 as [_ H31] ; destruct H41 as [_ H41].
      1-6: generalize (list_lhs_ref_p_size tmap h) ; intro.
      1-6: destruct (list_lhs_ref_p h tmap) as [[input_list [gt_ref'| |]]|] ; last (by contradiction H31) ; try by discriminate H10.
      1-6: injection H10 ; clear H10 ; intro H10.
      1-6: rewrite -H10 /size_of_ftype in H13 ; clear H10 gt_ref'.
      1-6: simpl in H31 ; simpl in H41.
      1-6: destruct (y \in input_list) eqn: Hy ;
            last by (destruct H31 as [_ H31] ; destruct H41 as [_ H41] ;
                     specialize (H31 y) ; specialize (H41 y) ;
                     rewrite Hy in H31, H41 ;
                     rewrite -H31 -H41 ;
                     specialize (H9 y) ;
                     destruct (PVM.find y ct_old) ; last (by reflexivity) ;
                     rewrite (H9 d) //).
      1-6: destruct H31 as [H31 _] ; destruct H41 as [H41 _].
      1-6: specialize (H31 0) ; specialize (H41 0).
      1-6: destruct input_list as [|ic [|]] ; try by discriminate H13.
      1-6: rewrite mem_seq1 in Hy ; move /eqP : Hy => Hy.
      1-6: rewrite -Hy in H31 H41 ; clear Hy H13 ic.
      1-6: simpl in H31 ; simpl in H41.
      1-6: rewrite (proj2 H31) (proj2 H41) //.
      (* now remain reference connections: should follow a similar proof, probably somewhat reordered *)
      admit.
    - (* Sinvalid: should be similar to Sfcnct. *)
      admit.
    - (* Swhen *)
      rename h into cond ; rename h0 into ss_true ; rename h1 into ss_false.
      (* basically we have two routes to get ct_new1 and ct_new2, similar to Sfcnct
         ct_old -> Swhen-components -> ct_temp0 -> component_stmts_of ss -> ct_temp1 -> Swhen-connections -> ct_temp2 -> connection_stmts_of ss -> ct_new1
         ct_old -> Swhen -> ct' -> ss -> ct_new2.
         We change the second route to:
         ct_old -> Swhen-components -> ct_temp0' -> Swhen-connections -> ct' -> ss -> ct_new2.
         (where CEP.Equal ct_temp0 ct_temp0').

         We should show that the change from ct_temp1 to ct_temp2
         is the same as the change from ct_temp0' to ct'.
         Then we can use Sem_frag_stmts_component_Equal to show:
         ct_temp0 -> Swhen-connections -> ct' -> component_stmts_of ss -> ct_temp2 -> connection_stmts_of ss -> ct_new1 *)
      apply Sem_frag_stmts_cat in H2.
      destruct H2 as [vm_temp1 [ct_temp1 [H21 H23]]].
      apply Sem_frag_stmts_cat in H21.
      destruct H21 as [vm_temp0 [ct_temp0 [H21 H22]]].
      apply Sem_frag_stmts_cat in H23.
      destruct H23 as [vm_temp2 [ct_temp2 [H23 H24]]].
      assert (Sem_frag_stmts vm_temp0 ct_temp0 (connection_stmt_of (Swhen cond ss_true ss_false)) vm' ct' tmap).
            (* use mainly H31 and also H21 *)
(* find vm_true, ct_true, vm_false, ct_false according to H31.
   Then apply the induction hypothesis stmt_components_connections to
   (vm_old ct_old ss_true vm_true ct_true).
        This also produces a point between (component_stmts_of ss_true) and (connection_stmts_of ss_true)
   (vm_true (extend_map_with ct_temp0 ct_true) ss_false vm_false ct_false).
*)





        (* Now the difference between ct_temp and (extend_map_with ct' ct_temp)
           is exactly the connection (Sfcnct h0 h1).
           This can be derived from H4 and H31 together.
           (Both have ct_old as basis; ct' only extends Sfcnct. *)

      (* We know that CEP.Equal vm_old vm'.
         The effect of the Sfcnct statement is applied to vm'.
         The component statements do not depend on ct' / ct_temp.
         So the change of ct' should just be transparent
         (perhaps need another lemma about this transparency, something like:
         vm_and_ct_compatible vm_old1 ct_old1 ->
         vm_and_ct_compatible vm_old2 ct_old2 ->
         CEP.Equal vm_old1 vm_old2 ->
         CEP.Equal vm_new1 vm_new2 ->
         CEP.Equal tmap1 tmap2 ->
         Sem_frag_stmts vm_old1 ct_old1 (component_stmts_of ss) vm_new1 ct_new tmap1 ->
         Sem_frag_stmts vm_old2 ct_old2 (component_stmts_of ss) vm_new1 (extend_map_with ct_old2 ct_new) tmap2 *)


* simpl ; intros.
  apply Sem_frag_stmts_cat in H2.
  (* If h is a component statement, there is no problem:
     we apply the induction hypothesis to H3 etc.

     If h is a connection statement, we know that its href is already in vm_old,
     and that it already was assigned a value in ct_old (because of vm_and_ct_compatible).
     That value is not changed by component_stmts_of ss.
     Then we apply the effect of h to ct_old and apply the induction hypothesis to that. *)
  destruct h.
*)


Lemma ExpandBranches_correct :
forall (vm_new : CEP.t vertex_type) (ct_new : CEP.t def_expr) (new_tmap_scope : CEP.t ftype * CEP.t ftype)
       (ss : HiFP.hfstmt_seq) (vm_old : CEP.t vertex_type) (ct_old : CEP.t def_expr) (old_def_ss new_conn_ss : HiFP.hfstmt_seq) (old_conn_map new_conn_map : CEP.t def_expr)
       (old_scope new_scope : CEP.t ftype) (old_tmap_scope : CEP.t ftype * CEP.t ftype),
        tmap_has_fully_inferred_ground_types old_tmap_scope.1 ->
        (* ExpandPort_fun pp = Some (old_conn_map, old_scope) -> *)
        (* submap old_scope tmap ->*)
        vm_and_ct_compatible vm_old ct_old ->
        CEP.Equal ct_old old_conn_map ->
        stmts_have_fully_inferred_ground_types ss ->
        CEP.submap old_tmap_scope.2 old_tmap_scope.1 ->
        stmts_tmap old_tmap_scope ss vm_new = Some new_tmap_scope ->
        ExpandBranch_funs ss old_def_ss old_conn_map old_scope =
              Some (Qcat old_def_ss (component_stmts_of ss), new_conn_map, new_scope) ->
        CEP.fold helper_connect new_conn_map (Some (Qnil ProdVarOrder.T)) =
              Some new_conn_ss ->
        Sem_frag_stmts vm_old ct_old (Qcat (component_stmts_of ss) new_conn_ss) vm_new ct_new new_tmap_scope.1 ->
            Sem_frag_stmts vm_old ct_old ss vm_new ct_new new_tmap_scope.1.
Proof.
intros.
apply Sem_frag_stmts_cat in H7.
destruct H7 as [vm_temp [ct_temp [H7 H8]]].
generalize (Sem_frag_stmts_component ss vm_old ct_old vm_temp ct_temp new_tmap_scope.1 H0 H7) ; intro.
generalize (stmts_tmap_preserves_fully_inferred vm_new ss old_tmap_scope.1 old_tmap_scope.2 H2 H H3) ; intro.
rewrite -surjective_pairing H4 in H10.
destruct new_tmap_scope as [new_tmap_s new_t_scope].
generalize (helper_connect_Sem vm_temp ct_temp vm_new ct_new new_tmap_s new_conn_map H10) ; intro.
rewrite H6 in H11.
specialize (H11 H8).
(* Here follows an older attempt to prove ExpandBranches_correct
   by induction on ss.  The problem is that connect statements
   would need a very intricate treatment, depending on whether
   the statement is the last or not.
   (For this, it would have been easier to define statement sequences
   right-recursive, using Qrcons.)
induction ss as [|s ss].
* simpl ; intros.
  (* use a lemma that says:
  CEP.fold helper_connect new_conn_map (Some (Qnil ProdVarOrder.T)) = Some new_conn_ss ->
  Sem_frag_stmts vm_old ct_old new_conn_ss vm_new ct_new tmap ->
     CEP.Equal vm_old vm_new /\ CEP.Equal (extend_map_with new_conn_map ct_old) ct_new. *)
  admit.
* simpl ; intros.
  generalize (stmt_submap vm_new s old_tmap_scope.1 old_tmap_scope.2 H2) ; intro.
  rewrite -surjective_pairing in H7.
  destruct (stmt_tmap old_tmap_scope s vm_new) as [temp_tmap_scope|] eqn: Hstmt_tmap ; last by discriminate H3.
  rewrite (surjective_pairing temp_tmap_scope) in H7.
  generalize (stmts_submap vm_new ss temp_tmap_scope.1 temp_tmap_scope.2 (proj1 H7)) ; intro.
  rewrite -surjective_pairing in H8.
  destruct (stmts_tmap temp_tmap_scope ss vm_new) as [new_tmap_scope'|] eqn: Hstmts_tmap ; last by discriminate H3.
  injection H3 ; clear H3 ; intro H3.
  rewrite H3 in H8, Hstmts_tmap ; clear H3 new_tmap_scope'.
  rewrite (surjective_pairing new_tmap_scope) in H8.
  (* Let's just do two examples statements to try how it works... *)
  destruct s ; try by done.
  + (* Sskip *)
    simpl.
    exists vm_old, ct_old.
    split ; first by (split ; reflexivity).
    move /andP : H1 => [_ H1].
    simpl stmt_tmap in Hstmt_tmap.
    injection Hstmt_tmap ; clear Hstmt_tmap ; intro Hstmt_tmap.
    rewrite -Hstmt_tmap in H7, H8, Hstmts_tmap ; clear Hstmt_tmap temp_tmap_scope.
    simpl in H4.
    simpl Qcat in H6.
    by apply (IHss vm_old ct_old old_def_ss new_conn_ss old_conn_map new_conn_map old_scope new_scope old_tmap_scope
                   H H0 H1 H2 Hstmts_tmap H4 H5 H6).
  + (* Swire -- a component statement *)
    move /andP : H1 => [H1s H1ss].
    simpl stmt_has_fully_inferred_ground_types in H1s.
    destruct f as [gt| |] ; try rewrite // in H1s.
    unfold ExpandBranch_fun in H4.
    rewrite -Qcat_rcons in H4.
    simpl Sem_frag_stmts in H6.
    destruct H6 as [vm' [ct' H6]].
    unfold stmt_tmap in Hstmt_tmap.
    destruct (CEP.find s old_tmap_scope.1) eqn: Hold_tmap_scope ; first by discriminate Hstmt_tmap.
    generalize (fully_inferred_does_not_change gt s vm_new H1s) ; intro.
    destruct (code_type_find_vm_widths (Gtyp gt) s vm_new) as [[[gt'| |] p]|] ; try by done.
    rewrite -H1 in Hstmt_tmap ; clear gt' H1.
    injection Hstmt_tmap ; clear Hstmt_tmap ; intro Hstmt_tmap.
    rewrite -Hstmt_tmap in Hstmts_tmap, H7, H8 ; clear temp_tmap_scope Hstmt_tmap.
    simpl fst in H7, H8 ; simpl snd in H7, H8.
    generalize (proj1 (proj2 H8) s) ; intro.
    rewrite CEP.Lemmas.find_add_eq in H1 ; last by rewrite /PVM.SE.eq eq_refl //.
    rewrite (H1 (Gtyp gt)) // in H6.
    specialize (IHss (CEP.add s (Wire gt) vm_old) (CEP.add s D_undefined old_conn_map) (Qrcons old_def_ss (Swire (var:=ProdVarOrder.T) s (Gtyp gt)))
                     new_conn_ss (CEP.add s D_undefined old_conn_map)
                     new_conn_map (CEP.add s (Gtyp gt) old_scope) new_scope
                     (CEP.add s (Gtyp gt) old_tmap_scope.1, CEP.add s (Gtyp gt) old_tmap_scope.2))
                with (2 := CEP.Lemmas.Equal_refl (CEP.add s D_undefined old_conn_map)) (3 := H1ss)
                     (4 := proj1 H7) (5 := Hstmts_tmap) (6 := H4) (7 := H5).
    simpl fst in IHss ; simpl snd in IHss.
    exists (CEP.add s (Wire gt) vm_old), (CEP.add s D_undefined old_conn_map).
    split.
    - admit.
    - apply IHss.
      * intro ; destruct (v == s) eqn: Hvs.
        + rewrite CEP.Lemmas.find_add_eq ; last by rewrite /PVM.SE.eq Hvs //.
          by exact H1s.
        + rewrite CEP.Lemmas.find_add_neq ; last by rewrite /PVM.SE.eq Hvs //.
          by apply H.
      * (* almost proj2 H6 *)
        apply (Sem_frag_stmts_Equal (Qcat (component_stmts_of ss) new_conn_ss)
                                    vm' (CEP.add s (Wire gt) vm_old)
                                    ct' (CEP.add s D_undefined old_conn_map)
                                    vm_new vm_new ct_new ct_new new_tmap_scope.1 new_tmap_scope.1)
                               with (3 := CEP.Lemmas.Equal_refl vm_new) (4 := CEP.Lemmas.Equal_refl ct_new)
                                    (5 := CEP.Lemmas.Equal_refl new_tmap_scope.1) (6 := proj2 H6).
        + clear -H6 ; destruct H6 as [[H0 [H1 _]] _].
          intro.
          destruct (y == s) eqn: Hys.
          - rewrite CEP.Lemmas.find_add_eq ; last by rewrite /PVM.SE.eq Hys //.
            specialize (H0 0).
            move /eqP : Hys => Hys.
            rewrite /list_rhs_type_p /List.nth_error add0n nat_of_binK -surjective_pairing -Hys in H0.
            by apply H0.
          - rewrite CEP.Lemmas.find_add_neq ; last by rewrite /PVM.SE.eq Hys //.
            specialize (H1 y.1 y.2).
            rewrite -surjective_pairing /size_of_ftype add1n in H1.
            rewrite H1 //.
            destruct (N.eq_dec y.1 s.1) as [H|H] ; last (left ; exact H).
            right.
            destruct (Nat.compare_spec y.2 s.2) ;
                  first (by specialize (injective_projections y s H) ; intro ;
                            rewrite -(nat_of_binK y.2) -(nat_of_binK s.2) H2 in H3 ;
                            specialize (H3 Logic.eq_refl) ;
                            rewrite H3 eq_refl // in Hys) ;
                  move /ltP : H2 => H2.
            * left  ; exact H2.
            * right ; exact H2.
        + clear -H6 H0 ; destruct H6 as [[_ [_ [H1 H2]]] _].
          intro.
          destruct (y == s) eqn: Hys.
          - rewrite CEP.Lemmas.find_add_eq ; last by rewrite /PVM.SE.eq Hys //.
            specialize (H2 0).
            move /eqP : Hys => Hys.
            rewrite /list_rhs_type_p /List.nth_error add0n nat_of_binK -surjective_pairing -Hys in H2.
            by apply H2.
          - rewrite CEP.Lemmas.find_add_neq ; last by rewrite /PVM.SE.eq Hys //.
            specialize (H1 y.1 y.2).
            rewrite -surjective_pairing /size_of_ftype add1n in H1.
            rewrite -H1 ; first by apply H0.
            destruct (N.eq_dec y.1 s.1) as [H|H] ; last (left ; exact H).
            right.
            destruct (Nat.compare_spec y.2 s.2) ;
                  first (by specialize (injective_projections y s H) ; intro ;
                            rewrite -(nat_of_binK y.2) -(nat_of_binK s.2) H3 in H4 ;
                            specialize (H4 Logic.eq_refl) ;
                            rewrite H4 eq_refl // in Hys) ;
                  move /ltP : H3 => H3.
            * left  ; exact H3.
            * right ; exact H3.
  + (* Sreg -- should be similar to Swire *)
    admit.
  + (* Snode -- should be similar to Swire *)
    admit.
  + (* Sfcnct *)
    simpl stmt_has_fully_inferred_ground_types in H1.
    move /andP : H1 => [H1s H1ss].
    simpl Qcat in H4, H6.
    simpl ExpandBranch_fun in H4.
    unfold ExpandBranch_connect in H4.
    destruct h ; try (by discriminate H4) ;
          last by destruct h ; try (by discriminate H4) ;
                  destruct h ; by discriminate H4.
    simpl stmt_tmap in Hstmt_tmap.
    destruct (CEP.find s old_tmap_scope.2) ; last by discriminate Hstmt_tmap.
    destruct (type_of_expr h0 old_tmap_scope.2) ; last by discriminate Hstmt_tmap.
    injection Hstmt_tmap ; clear Hstmt_tmap ; intro Hstmt_tmap.
    rewrite -Hstmt_tmap in H7 H8 Hstmts_tmap ; clear temp_tmap_scope Hstmt_tmap.
    (* Perhaps we need here that ft_ref is fully inferred?
       Then we would also need to assume tmap_has_fully_inferred_ground_types old_scope. *)
    destruct (CEP.find s old_scope) as [ft_ref|] ; last by discriminate H4.
    destruct (type_of_expr h0 old_scope) as [[ft_expr _]|] ; last by discriminate H4.
    destruct (connect_type_compatible false ft_ref ft_expr false) ; last by discriminate H4.
    specialize (IHss vm_old (CEP.add s (D_fexpr h0) ct_old) old_def_ss new_conn_ss
                     (CEP.add s (D_fexpr h0) old_conn_map) (CEP.remove ??? new_conn_map) old_scope new_scope old_tmap_scope
                     H) with (2 := H1ss) (3 := H2) (4 := Hstmts_tmap) (5 := H4) (6 := H5).

This does not work properly as it is now.
We need to change new_conn_map:
If this "Sfcnct ref expr" statement is the last connect,
then one should remove the assignment to ref from new_conn_map in the induction hypothesis.
If there is another connect statement, the later one prevails.

We may resolve this by a lemma.
Something like:
a) In a correct program (without repeated definitions of components),
   a later component statement will not overwrite old connect statements,
   i.e. if all statements in ss are component statements,
        then CEP.submap ct_old ct_new.
   see Lemma Sem_frag_stmts_component.

b) To get the semantics of the connect map correct:
   we have something like (CEP.Equal ct_new (extend_map_with new_conn_map ct_old)).
   see Lemma helper_connect_Sem?

Then the connect statement's effect ends up in (CEP.add s (D_fexpr h0) ct_old).

Another idea:
First split the module into component and non-component statements
(without changing the structure).
The non-component statements only consist of
- Sfcnct
- Sinvalid
- Swhen
Then show that a program consisting of these does not change under ExpandWhens.
This may be easier because the domain of the connect map never changes.

Aha! Is that a way out? Not have a connect map that is undefined
for some components that have no connection statement in the branch?

Or rather try to formulate another inductive statement like:

the connect map of a branch (Qcons (Sfcnct ...) ss) and
the connect map of ss have this relation:
CEP.Equal (connect_map_of (Qcons (Sfcnct (Eid s) expr) ss))
          (extend_expr_map_with (connect_map_of ss) (CEP.add s (D_fexpr expr) (CEP.empty def_expr)))

and extend_expr_map_with takes into account validif expressions,
allowing for partial extension if ss did not define something in every subbranch.

Definition extend_expr_map_with_helper (ex1 ex2 : option def_expr) : option def_expr :=
match ex1, ex2 with
| None, _ => ex2
| Some D_fexpr expr1, Some D_fexpr expr2 =>
    (recursively go through expr1 and replace any (validif condition e1)
     with (mux condition e1 expr2)
     may require something like validifnot expressions
     to see whether the mux should be positive or negative).
| _, _ => ex1
end.

Definition extend_expr_map_with (m1 m2 : CEP.t def_expr) : CEP.t def_expr :=
CEP.map2 extend_expr_map_with_helper m1 m2.
*)

(*
Lemma ExpandBranches_correct :
forall (vm : CEP.t vertex_type) (ct : CEP.t def_expr)
       (ss old_def_ss def_ss old_conn_ss new_conn_ss : HiFP.hfstmt_seq)
       (old_conn_map conn_map ct' : CEP.t def_expr) (old_scope temp_scope tmap : CEP.t ftype)
       (vm' : CEP.t vertex_type),
(* perhaps tmap_has_fully_inferred_ground_types tmap -> *)
ExpandBranch_funs ss old_def_ss old_conn_map old_scope = Some ((Qcat old_def_ss def_ss), conn_map, temp_scope) ->
(*def_ss = component_stmts_of ss -> -- follows from ExpandBranches_component *)
CEP.fold helper_connect conn_map (Some (Qnil ProdVarOrder.T)) = Some new_conn_ss ->
Sem_frag_stmts vm' ct' (Qcat def_ss (Qcat old_conn_ss new_conn_ss)) vm ct tmap ->
(* vm' contains the component definitions in old_def_ss and old_conn_map -> *)
(* ct' contains the connections in old_conn_ss / old_conn_map -> *)
(* vm' and ct' fit together (i.e. have the same components) -> *)
   Sem_frag_stmts vm' ct' ss vm ct tmap
with ExpandBranch_correct :
forall (vm : CEP.t vertex_type) (ct : CEP.t def_expr)
       (s : HiFP.hfstmt) (old_def_ss def_ss old_conn_ss new_conn_ss : HiFP.hfstmt_seq)
       (old_conn_map conn_map ct' : CEP.t def_expr) (old_scope temp_scope tmap : CEP.t ftype)
       (vm' : CEP.t vertex_type),
ExpandBranch_fun s old_def_ss old_conn_map old_scope = Some ((Qcat old_def_ss def_ss), conn_map, temp_scope) ->
(*def_ss = component_stmt_of s -> -- follows from ExpandBranch_component *)
CEP.fold helper_connect conn_map (Some (Qnil ProdVarOrder.T)) = Some new_conn_ss ->
Sem_frag_stmts vm' ct' (Qcat def_ss (Qcat old_conn_ss new_conn_ss)) vm ct tmap ->
(* vm' contains the component definitions in old_def_ss and old_conn_map -> *)
(* ct' contains the connections in old_conn_ss / old_conn_map -> *)
(* vm' and ct' fit together (i.e. have the same components) -> *)
   Sem_frag_stmt vm' ct' s vm ct tmap.
Proof.
* clear ExpandBranches_correct.
  induction ss ; simpl ; intros.
  + injection H ; clear H ; intros _ H _ ; clear temp_scope.
    rewrite -H in H1 ; clear conn_map H.
    rewrite H0 in H2 ; simpl Qcat in H2.
    (* simpl.
      intros.
      rewrite H0 in H, H2 ; clear def_ss H0.
      simpl Qcat in H2 ; rewrite Qcats0 in H.
      destruct H ; injection H ; clear H ; intros _ H ; clear x.
      clear old_conn_map H. *)
    admit.
  + admit.
* clear ExpandBranch_correct.
  induction s ; simpl ; intros.
  + (* Sskip *)
    rewrite CEP.fold_1 in H1.
Admitted.
*)

Definition ExpandWhens_fun (m : HiFP.hfmodule) : option HiFP.hfmodule :=
(* expand whens in module m *)
match m with
| FInmod v pp ss =>
    match ExpandPort_fun pp with
    | Some (port_conn_map, port_scope) =>
        match ExpandBranch_funs ss (Qnil ProdVarOrder.T) port_conn_map port_scope with
        | Some (def_ss, conn_map, _) =>
            match CEP.fold helper_connect conn_map (Some (Qnil ProdVarOrder.T)) with
            | Some conn_ss => Some (FInmod v pp (Qcat def_ss conn_ss))
            | None => None
            end
        | None => None
        end
    | None => None
    end
| FExmod _ _ _ => None
end.

(*
Lemma option_eqn_refl {T : eqType} (x : option T) : x == x.
Proof.  rewrite eq_refl //.  Qed.

Lemma option_eqn_sym {T : eqType} (x y : option T) : x == y -> y == x.
Proof.  intro ; rewrite eq_sym //.  Qed.

Lemma option_eqn_trans {T : eqType} (x y z : option T) : x == y -> y == z -> x == z.
Proof.  intro ; move /eqP : H => H ; rewrite H ; done.  Qed.

Instance option_eqn_Reflexive {T : eqType} : RelationClasses.Reflexive (fun (x y : option T) => x == y) := @option_eqn_refl T.
Instance option_eqn_Symmetric {T : eqType} : RelationClasses.Symmetric (fun (x y : option T) => x == y) := @option_eqn_sym T.
Instance option_eqn_Transitive {T : eqType} : RelationClasses.Transitive (fun (x y : option T) => x == y) := @option_eqn_trans T.
Instance option_eqn_Equivalence {T : eqType} : RelationClasses.Equivalence (fun (x y : option T) => x == y) :=
    { Equivalence_Reflexive := @option_eqn_Reflexive T;
      Equivalence_Symmetric := @option_eqn_Symmetric T;
      Equivalence_Transitive := @option_eqn_Transitive T }.

Lemma ExpandWhens_finish :
(* The final phase of ExpandWhens leads to a connection map that is the same as the one generated by commands *)
forall (conn_map : CEP.t def_expr) (old_conn_stmts new_conn_stmts : HiFP.hfstmt_seq)
       (vm_old vm_new : CEP.t vertex_type) (ct_old ct_new : CEP.t def_expr) (tmap : CEP.t ftype),
CEP.fold helper_connect conn_map (Some old_conn_stmts) = Some new_conn_stmts ->
    Sem_frag_stmts vm_old ct_old new_conn_stmts vm_new ct_new tmap ->
        component_stmts_of old_conn_stmts = (Qnil ProdVarOrder.T) ->
            (forall v : CEP.key, CEP.mem v conn_map = CEP.mem v ct_old) ->
                CEP.Equal conn_map ct_new.
Proof.
intros.
specialize (proj2 (fold_connect_components conn_map) old_conn_stmts) ; intro.
rewrite H H1 in H3.
clear H1 ; rename H3 into H1.
revert old_conn_stmts new_conn_stmts vm_old vm_new ct_old ct_new tmap H H0 H1 H2.
induction (CEP.elements conn_map) eqn: Hconn_map.
* intros.
  apply CEP.Lemmas.P.elements_Empty in Hconn_map.
  generalize (CEP.Lemmas.P.fold_Empty option_eqn_Equivalence helper_connect (Some old_conn_stmts) Hconn_map).
  move /eqP => H3.
  rewrite H3 in H.
  injection H ; clear H ; intro H.
  intro.
  assert (CEP.Empty ct_old).
        unfold CEP.Empty.
        intros ; specialize (H2 a).
        contradict H2.
        assert (CEP.In a ct_old) by (exists e ; exact H2).
        apply CEP.mem_1 in H4 ; rewrite H4.
        intro.
        apply CEP.mem_2 in H5 ; destruct H5 as [e' H5].
        specialize (Hconn_map a e').
        contradiction.

  assert (~CEP.In y conn_map).

        contradict Hconn_map.
        destruct Hconn_map as [elt Hconn_map].
        apply CEP.elements_1 in Hconn_map.


intros until 1.
rewrite CEP.fold_1 in H.
revert old_conn_stmts new_conn_stmts vm_old vm_new ct_old ct_new H.


Theorem ExpandWhen_Sem :
(* This theorem relates ExpandWhen and Sem, concerning connection maps *)
forall (m m' : HiFP.hfmodule),
    module_has_fully_inferred_ground_types m ->
    ExpandWhens_fun m = Some m' ->
    forall (vm vm' : CEP.t vertex_type) (ct ct' : CEP.t def_expr),
        Sem m vm ct -> Sem m' vm' ct' -> CEP.Equal ct ct'.
Proof.
intros.
destruct m as [mname pp ss|] ; simpl ExpandWhens_fun in H0 ; last by discriminate H0.
simpl module_has_fully_inferred_ground_types in H.
move /andP : H => H.
simpl Sem in H1 ; unfold ports_stmts_tmap in H1.
generalize (ports_tmap_preserves_fully_inferred vm pp (proj1 H)) ; intro.
specialize (ExpandPort_Sem) with (* tmap *) (pp := pp) (* vm *) (vm_tmap := vm) (* ct *) (1 := proj1 H) ; intro.
specialize (ExpandPort_correct vm pp (proj1 H)) ; intro.
destruct (ports_tmap pp vm) as [pmap|] ; last by contradiction H1.
generalize (stmts_tmap_preserves_fully_inferred vm ss pmap pmap (proj2 H) H3 (submap_refl pmap)) ; intro.
specialize (ExpandBranches_Sem_ct ss (Qnil ProdVarOrder.T)) (* vm_old *)
with (vm_new := vm) (vm_tmap := vm) (* ct_old *) (ct_new := ct) (* old_conn_map, old_scope, tmap *)
     (old_tmap_scope := (pmap, pmap)) (* new_tmap_scope *)
     (1 := proj2 H) (2 := H3) (4 := submap_refl pmap) ; intro.
generalize (stmts_submap vm ss pmap pmap (submap_refl pmap)) ; intro.
destruct (stmts_tmap (pmap, pmap) ss vm) as [[tmap scope]|] ; last by contradiction H1.
destruct H1 as [_ [vm_ports [ct_ports H1]]].
specialize (H4 tmap vm_ports ct_ports (proj1 (proj2 H8)) (proj1 H1)).
destruct (ExpandPort_fun pp) as [[port_conn_map port_scope]|] ; last by discriminate H0.
apply CEP.Lemmas.Equal_sym, Equal_submap in H5.
specialize (H7 vm_ports ct_ports port_conn_map port_scope tmap (tmap, scope)
      H5 Logic.eq_refl (submap_refl tmap) (proj2 H1) H4).
destruct (ExpandBranch_funs ss (Qnil ProdVarOrder.T) port_conn_map port_scope) as [[[def_ss conn_map] _]|] ; last by discriminate H0.
(* Now we need a theorem that states:
   the last phase of ExpandWhens, where (CEP.fold helper_connect conn_map ...) is called,
   leads to a Sem-connect map that is equal to conn_map. *)
Admitted.
*)

(* We want to prove a correctness theorem about ExpandWhens,
namely that the semantics before and after ExpandWhens_fun of a module
are bisimilar.
Conditions: every type is an explicit-width ground type,
and there are no uninferred Resets.
We need these conditions so ExpandBranch_fun works correctly
and there is only one semantic for a module. *)

Theorem ExpandWhens_correct :
(* The theorem states that ExpandWhens preserves semantics.
   (This requires that ExpandWhens_fun checks the scopes of variables,
   because “Sem m vm ct” will be false if scoping is violated,
   i.e. if components defined within a when statement are used outside. *)
forall m m' : HiFP.hfmodule, module_has_fully_inferred_ground_types m ->
   ExpandWhens_fun m = Some m' ->
      forall (vm : CEP.t vertex_type) (ct : CEP.t def_expr),
         Sem m' vm ct -> Sem m vm ct.
Proof.
intros.
unfold ExpandWhens_fun in H0.
destruct m as [v pp ss|] ; last by discriminate H0.
simpl module_has_fully_inferred_ground_types in H.
move /andP : H => [Hpp Hss].
generalize (ExpandPort_correct vm pp Hpp) ;
      intro.
destruct (ExpandPort_fun pp) as [[port_conn_map port_scope]|] eqn: Hport ; last by discriminate.
destruct (ExpandBranch_funs ss (Qnil ProdVarOrder.T) port_conn_map port_scope) as [[[def_ss conn_map] scope]|] eqn: Hexpand ; last by discriminate H0.
destruct (CEP.fold helper_connect conn_map (Some (Qnil ProdVarOrder.T))) as [conn_ss|] eqn: Hfold ; last by discriminate H0.
injection H0 ; clear H0 ; intro.
rewrite -H0 in H1 ; clear H0 m'.
unfold Sem in H1 ; unfold Sem.
unfold ports_stmts_tmap in H1 ; unfold ports_stmts_tmap.
generalize (ports_tmap_preserves_fully_inferred vm pp Hpp) ;
      intro.
destruct (ports_tmap pp vm) as [pmap|] ; last by trivial.
generalize (stmts_tmap_components vm ss pmap pmap pmap (submap_refl pmap) (submap_refl pmap) (submap_refl pmap)) ;
      intro.
generalize (ExpandBranch_components ss (Qnil ProdVarOrder.T) port_conn_map port_scope
            def_ss conn_map scope Hexpand) ;
      intro ;
      unfold Qcat in H3.
rewrite stmts_tmap_cat H3 in H1 ; rewrite H3 in Hexpand ; clear def_ss H3.
generalize (ExpandBranch_funs_checks_scopes ss pmap pmap pmap vm
            Hss H0 (submap_refl pmap) (submap_refl pmap) (submap_refl pmap)) ;
      intro.
specialize H3 with (old_def_ss := (Qnil ProdVarOrder.T))
                   (old_conn_map := port_conn_map) (old_scope := port_scope)
                   (3 := Equal_submap port_scope pmap (CEP.Lemmas.Equal_sym H)).
generalize (stmts_submap vm (component_stmts_of ss) pmap pmap
            (submap_refl pmap)) ;
      intro.
generalize (components_preserves_fully_inferred ss Hss) ;
      intro.
generalize (stmts_tmap_preserves_fully_inferred vm (component_stmts_of ss) pmap pmap H5 H0 (submap_refl pmap)) ;
      intro.
destruct (stmts_tmap (pmap, pmap) (component_stmts_of ss) vm) as [[tmap' scope2]|] ; last by contradiction H1.
destruct (stmts_tmap (pmap, pmap) ss vm) as [[tmap scope1]|] ;
      last by (rewrite Hexpand in H3 ; discriminate H3 ; try done ;
               intro ; specialize (H v0) ; rewrite H ;
               destruct (CEP.find v0 port_scope) ; done).
clear H3.
destruct H2 as [H2' H2] ; rewrite -H2' in H1 H4 H6 ; clear H2' tmap'.
generalize (stmts_tmap_components vm conn_ss tmap scope2 scope2
            (proj1 H4) (proj1 H4) (submap_refl scope2)) ;
      intro.
destruct (stmts_tmap (tmap, scope2) conn_ss vm) as [[tmap' scope2']|] ; last by contradiction H1.
generalize (proj2 (fold_connect_components conn_map) (Qnil ProdVarOrder.T)) ;
      intro.
rewrite Hfold in H7 ; simpl component_stmts_of in H7.
rewrite H7 /stmts_tmap in H3 ; clear H7.
destruct H3 as [H3 _] ; rewrite H3 in H1 ; clear H3 tmap' scope2'.
split ; first by (apply H1).
destruct H1 as [_ [vm' [ct' H1]]].
exists vm', ct'.
split ; first by apply H1.
destruct H4 as [_ [H4 _]].
clear H2 scope2 scope1.
rename H0 into H0'.
assert (H0 : tmap_has_fully_inferred_ground_types port_scope).
      clear -H H0'.
      intro.
      specialize (H v) ; specialize (H0' v).
      destruct (CEP.find v pmap) as [[gt| |]|] ;
            try (by done) ; rewrite -H //.
rename H4 into H4'.
assert (H4 : submap port_scope tmap).
      clear -H H4'.
      intro.
      specialize (H v) ; specialize (H4' v).
      destruct (CEP.find v port_scope) as [ft|] ; last by done.
      rewrite H // in H4'.
clear H0' H4' H pmap.
destruct H1 as [_ H1].
(* Now use something like a Sem_frag_stmts_cat lemma,
   looking at the state of vm'' and ct'' between (component_stmts_of ss) and conn_ss.
   We can prove that
   * Sem_frag_stmts vm' ct' (component_stmts_of ss) vm'' ct'' tmap
     + sets vm essentially to the same as Sem_frag_stmts vm' ct' ss vm ct tmap.
     + sets ct'' to all default values.
   * Sem_frag_stmts vm'' ct'' conn_ss vm ct tmap
     + does not really change vm, we have CEP.Equal vm'' vm
     + sets ct to the same values as ss
       (this may need a more intricate proof!)

Or use another proof idea:
induction by ss.
If the first statement of ss is a component statement,
it moves to the first part of H1's Sem_frag_stmts.

If the first statement of ss is a connection statement,
then ExpandBranch_funs moves its effect to conn_map,
and CEP.fold helper_connect moves its effect to conn_ss.

---

Requires actually a mutual induction over statement sequences and statements.
*)



(* Now we have to verify that the module graph after ExpandBranch_funs
is the same as before.
Basically, the module graph vertex set vm only depends on components_of ss = def_ss,
and the connection trees ct only depends on connect statements = conn_ss. *)


(* Probably look through ExpandBranch_funs and Sem_frag_stmts in parallel.
We have:
ExpandBranch_funs ss old_def_ss old_conn_map old_scope = Some (def_ss, conn_map, _)
Hfold : CEP.fold helper_connect conn_map (Some (Qnil ProdVarOrder.T)) =
        Some conn_ss

and we have a correspondence
    def_ss_old  <---> vm_old (they contain the same components)
      forall v : ProdVarOrder.T,
         match CEP.find v vm_old with
         | Swire _ newgt
         | ... newgt => CEP.find v def_ss_old = Some (Gtyp newgt)
         end

   conn_map_old <---> ct_old (they contain the same connections)
     forall v : ProdVarOrder.T,
         CEP.find (v, N0) comm_map_old =
         CEP.find v ct_old

We should prove:
Sem_frag_stmts vm_old ct_old (Qcat (components ss) (connections ss)) vm ct

So we need to strengthen Hexpand so we can use this correspondence!
*)
