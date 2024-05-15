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

From Coq Require Import BinNat ZArith.
From mathcomp Require Import ssreflect ssrbool eqtype seq fintype ssrnat div ssrfun.
From simplssrlib Require Import SsrOrder Var FMaps.
From firrtl Require Import Firrtl Env HiEnv HiFirrtl ModuleGraph_oriented.

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

Definition tmap_has_fully_inferred_ground_types (tmap : CEP.t (ftype * HiF.forient)) : Prop :=
forall (v : ProdVarOrder.T),
   match CEP.find v tmap return Prop with
   | Some (Gtyp gt, _) => fully_inferred gt
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
  1,2: subst newgt.
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
| Swhen cond ss_true ss_false =>
       expr_has_fully_inferred_ground_types cond
    &&
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
forall scope : CEP.t (ftype * HiF.forient),
   tmap_has_fully_inferred_ground_types scope ->
      forall expr : HiFP.hfexpr,
         expr_has_fully_inferred_ground_types expr ->
            match type_of_expr expr scope return Prop with
            | Some (exist (Gtyp ft) _) => fully_inferred ft
            | Some _ => False
            | None => True
            end
with ref_preserves_fully_inferred :
forall scope : CEP.t (ftype * HiF.forient),
   tmap_has_fully_inferred_ground_types scope ->
      forall ref : HiFP.href,
         ref_has_fully_inferred_ground_types ref ->
            match type_of_ref ref scope return Prop with
            | Some (Gtyp ft, _) => fully_inferred ft
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
    destruct (type_of_ref h scope) as [[[gt| |] ori]|]; try done.
    destruct ori, gt ; by done.
* clear ref_preserves_fully_inferred.
  induction ref ; simpl type_of_ref ; simpl ref_has_fully_inferred_ground_types ; intro.
  + by apply H.
  + specialize (IHref H0).
    destruct (type_of_ref ref scope) as [[[| |] ori]|] ; by done.
  + specialize (IHref H0).
    destruct (type_of_ref ref scope) as [[[| |] ori]|] ; by done.
  + simpl ; trivial.
Qed.

Definition ct_has_fully_inferred_ground_types (ct : CEP.t def_expr) :=
forall k : CEP.key, if CEP.find k ct is Some (D_fexpr e)
                    then expr_has_fully_inferred_ground_types e
                    else true.

Lemma stmt_tmap_preserves_fully_inferred :
forall (vm : CEP.t vertex_type) (tmap scope : CEP.t (ftype * HiF.forient)) (s : HiFP.hfstmt),
   stmt_has_fully_inferred_ground_types s ->
   tmap_has_fully_inferred_ground_types tmap ->
   CEP.submap scope tmap ->
      match stmt_tmap (tmap, scope) s vm with
      | Some (tmap', _) => tmap_has_fully_inferred_ground_types tmap'
      | _ => True
      end
with stmts_tmap_preserves_fully_inferred :
forall (vm : CEP.t vertex_type) (ss : HiFP.hfstmt_seq) (tmap scope : CEP.t (ftype * HiF.forient)),
   stmts_have_fully_inferred_ground_types ss ->
   tmap_has_fully_inferred_ground_types tmap ->
   CEP.submap scope tmap ->
      match stmts_tmap (tmap, scope) ss vm with
      | Some (tmap', _) => tmap_has_fully_inferred_ground_types tmap'
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
    2: destruct (type_of_expr h0 scope) as [[[[[|[]]| | | | | |]| |] _]|] ; try by trivial.
    2: destruct (type_of_expr h1 (CEP.add s (Gtyp gt, HiF.Duplex) scope)) ; last by trivial.
    3: destruct (type_of_expr h1 scope) ; last by trivial.
    1-3: intro.
    1-3: destruct (v == s) eqn: Hvs ; first by rewrite CEP.Lemmas.find_add_eq //.
    1-3: rewrite CEP.Lemmas.find_add_neq ; last by rewrite /HiFirrtl.PVM.SE.eq Hvs //.
    1-3: by apply H0.
  + (* Snode *)
    simpl stmt_tmap.
    destruct (CEP.find s tmap) ; first by trivial.
    assert (tmap_has_fully_inferred_ground_types scope).
          intro.
          specialize (H1 v).
          destruct (CEP.find v scope) as [p|] ; try done.
          specialize (H0 v).
          rewrite (H1 p Logic.eq_refl) in H0.
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
    move /andP : H => [/andP [_ Ht] Hf].
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
  move /andP : H => [/andP [_ Ht] Hf].
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
       (ct_old1 ct_old2 ct_new1 ct_new2 : CEP.t def_expr) (tmap : CEP.t (ftype * HiF.forient)),
    stmts_have_fully_inferred_ground_types ss ->
    tmap_has_fully_inferred_ground_types tmap ->
    CEP.Equal vm_old1 vm_old2 /\ CEP.Equal ct_old1 ct_old2 ->
    Sem_frag_stmts vm_old1 ct_old1 ss vm_new1 ct_new1 tmap ->
    Sem_frag_stmts vm_old2 ct_old2 ss vm_new2 ct_new2 tmap ->
        CEP.Equal vm_new1 vm_new2 /\ CEP.Equal ct_new1 ct_new2
with fully_inferred_makes_Sem_frag_stmt_unique :
forall (s : HiFP.hfstmt) (vm_old1 vm_old2 vm_new1 vm_new2 : CEP.t vertex_type)
       (ct_old1 ct_old2 ct_new1 ct_new2 : CEP.t def_expr) (tmap : CEP.t (ftype * HiF.forient)),
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
    destruct (CEP.find s tmap) as [[[gt'| |] _]|] ; try by done.
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
      destruct (list_lhs_ref_p h tmap) as [[input_list [ft_ref [| | | |]]]|] ; try by contradiction H2.
      1,2: destruct (type_of_expr (Econst ProdVarOrder.T f b) tmap) as [[ft_expr _]|] ; last by contradiction H2.
      1,2: destruct H2 as [H6 H2] ; destruct H3 as [_ H3].
      1,2: apply connect_type_compatible_size in H6.
      1,2: rewrite -H4 in H6 ; clear H4.
      1,2: generalize (list_rhs_expr_p_size ft_expr (Econst ProdVarOrder.T f b)) ; intro.
      1,2: destruct (list_rhs_expr_p (Econst ProdVarOrder.T f b) ft_expr) as [expr_list|] ; last by contradiction H2.
      1,2: rewrite -H6 in H4 ; clear H6.
      1,2: intro.
      1,2: destruct (y \in input_list) eqn: Hylist ;
            last by (destruct H2 as [_ H2] ; destruct H3 as [_ H3] ;
                     specialize (H2 y) ; specialize (H3 y) ;
                     rewrite Hylist in H2, H3 ;
                     rewrite -H2 -H3 ; apply H1).
      1,2: destruct H2 as [H2 _] ; destruct H3 as [H3 _].
      1,2: rewrite -index_mem in Hylist.
      1,2: move /ltP : Hylist => Hylist.
      1,2: generalize (proj2 (List.nth_error_Some input_list (index y input_list)) Hylist) ; intro.
      1,2: specialize (H2 (index y input_list)) ; specialize (H3 (index y input_list)).
      1,2: destruct (List.nth_error input_list (index y input_list)) as [ic|] eqn: H6 ; last by contradict H5.
      1,2: clear H5.
      1,2: replace ic with y in H2, H3, H6
            by (clear -H6 ;
                induction input_list ; first (by simpl in H6 ; done) ;
                simpl in H6 ;
                destruct (a == y) eqn: Hay ; simpl in H6 ;
                      last (by apply IHinput_list, H6) ;
                move /eqP : Hay => Hay ; rewrite Hay in H6 ;
                symmetry ; injection H6 ; done).
      1,2: clear ic.
      1,2: rewrite -H4 in Hylist ; apply List.nth_error_Some in Hylist.
      1,2: destruct (List.nth_error expr_list (index y input_list)) as [ex|] ; last by contradict Hylist.
      1,2: by rewrite (proj2 H2) (proj2 H3) //.
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


Lemma Sem_frag_stmts_component_Equal :
forall (ss : HiFP.hfstmt_seq) (vm_old1 vm_old2 : CEP.t vertex_type) (ct_old1 ct_old2 : CEP.t def_expr) (vm_new1 vm_new2 : CEP.t vertex_type) (ct_new : CEP.t def_expr) (tmap1 tmap2 : CEP.t (ftype * HiF.forient)),
    vm_and_ct_compatible vm_old1 ct_old1 ->
    vm_and_ct_compatible vm_old2 ct_old2 ->
    CEP.Equal vm_old1 vm_old2 ->
    CEP.Equal vm_new1 vm_new2 ->
    CEP.Equal tmap1 tmap2 ->
    Sem_frag_stmts vm_old1 ct_old1 (component_stmts_of ss) vm_new1 ct_new tmap1 ->
    Sem_frag_stmts vm_old2 ct_old2 (component_stmts_of ss) vm_new2 (extend_map_with ct_old2 ct_new) tmap2
with Sem_frag_stmt_component_Equal :
forall (s : HiFP.hfstmt) (vm_old1 vm_old2 : CEP.t vertex_type) (ct_old1 ct_old2 : CEP.t def_expr) (vm_new1 vm_new2 : CEP.t vertex_type) (ct_new : CEP.t def_expr) (tmap1 tmap2 : CEP.t (ftype * HiF.forient)),
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
    destruct (CEP.find s tmap1) as [[newft ori]|] ; last by contradiction H4.
    rewrite -H3 ; clear ori H3.
    split.
    - destruct H4 as [H4 _].
      intro ; specialize (H4 n).
      destruct (List.nth_error (list_rhs_type_p newft) n) ; last by trivial.
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
      rewrite -(list_rhs_type_p_size newft) in H2.
      move /ltP : H2 => H2.
      generalize (proj2 (List.nth_error_Some (list_rhs_type_p newft) n0) H2) ; intro.
      destruct (List.nth_error (list_rhs_type_p newft) n0) ; last by contradiction H3.
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
       (ct_old ct_new : CEP.t def_expr) (tmap : CEP.t (ftype * HiF.forient)),
component_stmts_of ss = (Qnil ProdVarOrder.T) ->
    Sem_frag_stmts vm_old ct_old ss vm_new ct_new tmap ->
           CEP.Equal vm_old vm_new
with Sem_frag_stmt_no_component :
forall (s : HiFP.hfstmt) (vm_old vm_new : CEP.t vertex_type)
       (ct_old ct_new : CEP.t def_expr) (tmap : CEP.t (ftype * HiF.forient)),
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

Definition ExpandBranch_connect (ref : HiFP.href) (val : def_expr) (old_def_ss : HiFP.hfstmt_seq) (old_conn_map : CEP.t def_expr) (old_scope : CEP.t (ftype * HiF.forient)) : option (HiFP.hfstmt_seq * CEP.t def_expr * CEP.t (ftype * HiF.forient)) :=
(* handle a connect statement, where ref is assigned val.
   ref can be a simple reference or a memory port or an inport of an instance.
   It will always have a ground type, as connects already have been
   expanded and types already have been lowered.
   It is checked that ref and val are in scope. *)
match ref with
| Eid v =>
    match CEP.find v old_scope with
    | Some (ft_ref, HiF.Sink)
    | Some (ft_ref, HiF.Duplex) =>
        match val with
        | D_fexpr expr =>
            match type_of_expr expr old_scope with
            | Some (exist ft_expr _) =>
                if connect_type_compatible false ft_ref ft_expr false
                then Some (old_def_ss, CEP.add v val old_conn_map, old_scope)
                else None
            | None => None
            end
        | _ => Some (old_def_ss, CEP.add v val old_conn_map, old_scope)
        end
    | _ => None (* out of scope *)
    end
(*
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
*)
| _ => None (* error: aggregate-type components are not allowed *)
end.

Fixpoint ExpandBranch_fun (s : HiFP.hfstmt) (old_def_ss : HiFP.hfstmt_seq) (old_conn_map : CEP.t def_expr) (old_scope : CEP.t (ftype * HiF.forient)) : option (HiFP.hfstmt_seq * CEP.t def_expr * CEP.t (ftype * HiF.forient)) :=
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
    Some (Qrcons old_def_ss s, CEP.add v D_undefined old_conn_map, CEP.add v (t, HiF.Duplex) old_scope)
| Sreg v reg =>
    (* type checking can be loose because the statement is a definition statement.
       We only need to verify that the expressions have any type, so they are in scope.
       We do not have to distinguish non-constant and constant expressions here;
       we can always allow the register to be reset to itself, as the register is in
       its own scope. *)
    if (if reset reg is Rst rst_sig rst_val
        then match type_of_expr rst_sig old_scope, type_of_expr rst_val (CEP.add v (type reg, HiF.Duplex) old_scope) with
             | Some _, Some _ => true
             | _, _ => false
             end
        else true)
    then match type_of_expr (clock reg) old_scope with
         | Some _ => Some (Qrcons old_def_ss s, CEP.add v (D_fexpr (Eref (Eid v))) old_conn_map, CEP.add v (type reg, HiF.Duplex) old_scope)
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
    then Some (Qrcons old_def_ss s, old_conn_map, CEP.add v (ft_expr, HiF.Source) old_scope)
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
with ExpandBranch_funs (ss : HiFP.hfstmt_seq) (old_def_ss : HiFP.hfstmt_seq) (old_conn_map : CEP.t def_expr) (old_scope : CEP.t (ftype * HiF.forient)) : option (HiFP.hfstmt_seq * CEP.t def_expr * CEP.t (ftype * HiF.forient)) :=
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
   forall (ss def_ss : HiFP.hfstmt_seq) (conn_map : CEP.t def_expr) (scope : CEP.t (ftype * HiF.forient))
          (def_ss' : HiFP.hfstmt_seq) (conn_map' : CEP.t def_expr) (scope' : CEP.t (ftype * HiF.forient)),
      ExpandBranch_funs ss def_ss conn_map scope =
          Some (def_ss', conn_map', scope') ->
          def_ss' = Qcat def_ss (component_stmts_of ss)
with ExpandBranch_component :
   forall (def_ss' : HiFP.hfstmt_seq) (conn_map' : CEP.t def_expr) (scope : CEP.t (ftype * HiF.forient))
          (s : HiFP.hfstmt) (def_ss : HiFP.hfstmt_seq) (conn_map : CEP.t def_expr) (scope' : CEP.t (ftype * HiF.forient)),
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
                      match type_of_expr rst_val (CEP.add s (type h, HiF.Duplex) scope) with
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
    destruct (CEP.find s scope) as [[ft_ref [| | | |]]|] ; try by discriminate H.
    1,2: destruct (type_of_expr h0 scope) as [[ft_expr _]|] ; last by discriminate H.
    1,2: destruct (connect_type_compatible false ft_ref ft_expr false) ; last by discriminate H.
    1,2: injection H ; intros.
    1,2: rewrite Qcats0 H2 //.
  + (* Sinvalid *)
    unfold ExpandBranch_fun, component_stmt_of.
    intros.
    unfold ExpandBranch_connect in H.
    destruct h ; try by discriminate H.
    destruct (CEP.find s scope) as [[_ [| | | |]]|] ; try (by discriminate H).
    1,2: injection H ; intros.
    1,2: rewrite Qcats0 H2 //.
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


Lemma ExpandBranch_stmt_tmap :
(* When comparing stmt_tmap and ExpandBranch_fun:
   if the first function gets a larger scope as input,
   it will produce a larger scope as output.

   This lemma is used by the next theorem (ExpandBranch_funs_checks_scopes). *)
forall (vm : CEP.t vertex_type) (s : HiFP.hfstmt)
       (old_tmap new_tmap old_scope1 new_scope1 old_scope2 new_scope2 : CEP.t (ftype * HiF.forient))
       (old_def_ss new_def_ss : HiFP.hfstmt_seq) (old_conn_map new_conn_map : CEP.t def_expr),
   stmt_tmap (old_tmap, old_scope1) s vm = Some (new_tmap, new_scope1) ->
   ExpandBranch_fun s old_def_ss old_conn_map old_scope2 = Some (new_def_ss, new_conn_map, new_scope2) ->
   CEP.submap old_scope2 old_scope1 ->
   stmt_has_fully_inferred_ground_types s ->
      CEP.submap new_scope2 new_scope1
with ExpandBranch_stmts_tmap :
forall (vm : CEP.t vertex_type) (ss : HiFP.hfstmt_seq)
       (old_tmap new_tmap old_scope1 new_scope1 old_scope2 new_scope2 : CEP.t (ftype * HiF.forient))
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
    subst new_scope2.
    destruct f as [gt| |] ; try done.
    destruct (CEP.find s old_tmap) ; first by discriminate H.
    generalize (fully_inferred_does_not_change gt s vm H2) ;
          intro.
    destruct (code_type_find_vm_widths (Gtyp gt) s vm) as [[[newgt| |] _]|]; try done.
    subst newgt.
    injection H ; clear H ; intros H _.
    subst new_scope1.
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
    1,2: subst newgt.
    2: destruct (type_of_expr rst_sig old_scope1) as [[[[[|[]]| | | | | |]| |] _]|] ; try by discriminate H.
    2,3: destruct (type_of_expr rst_sig old_scope2) ; last by discriminate H0.
    2: destruct (type_of_expr rst_val (CEP.add s (Gtyp gt, HiF.Duplex) old_scope1)) ; last by discriminate H.
    3: destruct (type_of_expr rst_val old_scope1) ; last by discriminate H.
    2,3: destruct (type_of_expr rst_val (CEP.add s (Gtyp gt, HiF.Duplex) old_scope2)) ; last by discriminate H0.
    1-3: injection H ; clear H ; intros ; subst new_tmap new_scope1.
    1-3: destruct (type_of_expr (clock h) old_scope2) ; last by discriminate H0.
    1-3: injection H0 ; clear H0 ; intros ; subst new_def_ss new_conn_map new_scope2.
    1-3: by apply submap_add_add, H1.
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
    destruct (CEP.find s old_scope2) as [[ft_ref [| | | |]]|] ; try by discriminate H0.
    1,2: destruct (type_of_expr h0 old_scope2) as [[ft_expr _]|] ; last by discriminate H0.
    1,2: destruct (connect_type_compatible false ft_ref ft_expr false) ; last by discriminate H0.
    1,2: injection H0 ; clear H0 ; intros H0 _ _ ; rewrite -H0 ; clear H0 new_scope2.
    1,2: by exact H1.
  + (* Sinvalid *)
    unfold ExpandBranch_connect in H0.
    destruct (type_of_ref h old_scope1) ; last by discriminate H.
    injection H ; clear H ; intros H _ ; rewrite -H ; clear H new_scope1.
    destruct h ; try done.
    destruct (CEP.find s old_scope2) as [[_ [| | | |]]|]; try by discriminate H0.
    1,2: injection H0 ; clear H0 ; intros H0 _ _ ; rewrite -H0 ; clear H0 new_scope2.
    1,2: by exact H1.
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

Lemma ExpandBranch_funs_checks_scopes :
(* If ss contains a scoping error, then ExpandBranch_funs does not make it go away:
   either it produces no result, or it produces a result that also contains a scoping error. *)
forall (ss : HiFP.hfstmt_seq) (tmap scope1 scope2 : CEP.t (ftype * HiF.forient)) (vm : CEP.t vertex_type),
   stmts_have_fully_inferred_ground_types ss ->
   tmap_has_fully_inferred_ground_types tmap ->
   CEP.submap scope1 tmap ->
   CEP.submap scope2 tmap ->
   CEP.submap scope1 scope2 ->
      stmts_tmap (tmap, scope1) ss vm = None ->
         stmts_tmap (tmap, scope2) (component_stmts_of ss) vm <> None ->
            forall (old_def_ss : HiFP.hfstmt_seq) (old_conn_map : CEP.t def_expr) (old_scope : CEP.t (ftype * HiF.forient)),
               CEP.submap old_scope scope1 ->
                  ExpandBranch_funs ss old_def_ss old_conn_map old_scope = None
with ExpandBranch_fun_checks_scopes :
forall (s : HiFP.hfstmt) (tmap scope1 scope2 : CEP.t (ftype * HiF.forient)) (vm : CEP.t vertex_type),
   stmt_has_fully_inferred_ground_types s ->
   tmap_has_fully_inferred_ground_types tmap ->
   CEP.submap scope1 tmap ->
   CEP.submap scope2 tmap ->
   CEP.submap scope1 scope2 ->
      stmt_tmap (tmap, scope1) s vm = None ->
         stmts_tmap (tmap, scope2) (component_stmt_of s) vm <> None ->
            forall (old_def_ss : HiFP.hfstmt_seq) (old_conn_map : CEP.t def_expr) (old_scope : CEP.t (ftype * HiF.forient)),
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
    generalize (H2 s) ; intro.
    destruct (CEP.find s tmap) ; first by contradiction H5.
    destruct (type h) as [gt| |] ; try by discriminate H.
    destruct (type_of_expr (clock h) scope2) ; last by contradiction H5.
    generalize (fully_inferred_does_not_change gt s vm) ; intro.
    destruct (code_type_find_vm_widths (Gtyp gt) s vm) as [[newft _]|]; last by contradiction H5.
    destruct (reset h) as [|rst_sig rst_val].
    1,2: move /andP : H => [H H'] ; apply H8 in H' ; clear H8.
    1,2: destruct newft as [gt'| |] ; try by contradiction (H').
    1,2: subst gt'.
    1,2: generalize (type_of_expr_submap (clock h) old_scope scope1 H6) ; intro.
    - destruct (type_of_expr (clock h) old_scope) ; last by reflexivity.
      rewrite H8 // in H4.
    - generalize (type_of_expr_submap rst_sig old_scope scope1 H6) ;
            intro.
      destruct (type_of_expr rst_sig old_scope) as [[fto po]|] ; last by reflexivity.
      generalize (type_of_expr_submap rst_sig scope1 scope2 H3) ;
            intro.
      rewrite H9 in H4, H10 ; rewrite H10 in H5 ; clear H9 H10 po.
      destruct fto as [[[|[]]| | | | | |]| |] ; try by contradiction H5.
      * 1: generalize (submap_add_add old_scope scope1 s (Gtyp gt, HiF.Duplex) H6) ; intro.
        1: apply (type_of_expr_submap rst_val) in H9.
        1: destruct (type_of_expr rst_val (CEP.add s (Gtyp gt, HiF.Duplex) old_scope)) ;
              last by reflexivity.
      * 2: generalize (type_of_expr_add rst_val old_scope scope2 s (Gtyp gt, HiF.Duplex)
              (CEP.Lemmas.submap_trans H6 H3)) ; intro.
        2: destruct (CEP.find s scope2) ;
              first by discriminate (H7 _ Logic.eq_refl).
        2: destruct (type_of_expr rst_val scope2) ; last by contradiction H5.
        2: rewrite H9 // ; clear H9.
        2: generalize (type_of_expr_submap rst_val old_scope scope1 H6) ; intro.
        2: destruct (type_of_expr rst_val old_scope) ;
              last by reflexivity.
      1,2: rewrite H9 in H4.
      1,2: generalize (type_of_expr_submap (clock h) old_scope scope1 H6) ; intro.
      1,2: destruct (type_of_expr (clock h) old_scope) ; last by reflexivity.
      1,2: rewrite H10 // in H4.
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
    simpl type_of_ref in H4.
    generalize (H6 s) ; intro.
    destruct (CEP.find s old_scope) as [[ft_ref [| | | |]]|] ; try by reflexivity.
    1,2: rewrite (H7 _ Logic.eq_refl) in H4 ; clear H7.
    1,2: generalize (type_of_expr_submap h0 old_scope scope1 H6) ;
            intro.
    1,2: destruct (type_of_expr h0 old_scope) as [[ft_expr p]|] ; last by reflexivity.
    1,2: rewrite H7 in H4 ; clear H7 p.
    1,2: by discriminate H4.
  + (* Sinvalid *)
    unfold ExpandBranch_connect.
    destruct h ; try done.
    simpl type_of_ref in H4.
    specialize (H6 s).
    destruct (CEP.find s old_scope) as [ft_ref|] ; last by reflexivity.
    rewrite (H6 _ Logic.eq_refl) in H4 ; clear H6.
    by discriminate H4.
  + (* Swhen *)
    rename h into cond ; rename h0 into ss_true ; rename h1 into ss_false.
    move /andP : H => [/andP [_ Ht] Hf].
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


Lemma ExpandBranch_funs_preserves_fully_inferred :
forall (ss def_ss : HiFP.hfstmt_seq) (conn_map : CEP.t def_expr) (scope : CEP.t (ftype * HiF.forient))
       (def_ss' : HiFP.hfstmt_seq) (conn_map' : CEP.t def_expr) (scope' : CEP.t (ftype * HiF.forient)),
    tmap_has_fully_inferred_ground_types scope ->
    stmts_have_fully_inferred_ground_types ss ->
    ct_has_fully_inferred_ground_types conn_map ->
    ExpandBranch_funs ss def_ss conn_map scope = Some (def_ss', conn_map', scope') ->
            tmap_has_fully_inferred_ground_types scope'
        /\
            ct_has_fully_inferred_ground_types conn_map'
with ExpandBranch_fun_preserves_fully_inferred :
forall (def_ss' : HiFP.hfstmt_seq) (conn_map' : CEP.t def_expr) (scope : CEP.t (ftype * HiF.forient))
       (s : HiFP.hfstmt) (def_ss : HiFP.hfstmt_seq) (conn_map : CEP.t def_expr) (scope' : CEP.t (ftype * HiF.forient)),
    tmap_has_fully_inferred_ground_types scope ->
    stmt_has_fully_inferred_ground_types s ->
    ct_has_fully_inferred_ground_types conn_map ->
    ExpandBranch_fun s def_ss conn_map scope = Some (def_ss', conn_map', scope') ->
            tmap_has_fully_inferred_ground_types scope'
        /\
            ct_has_fully_inferred_ground_types conn_map'.
Proof.
* clear ExpandBranch_funs_preserves_fully_inferred.
  induction ss.
  + simpl ; intros.
    injection H2 ; clear H2 ; intros ; subst def_ss' conn_map' scope'.
    split.
    - exact H.
    - exact H1.
  + simpl ; intros.
    move /andP : H0 => H0.
    specialize ExpandBranch_fun_preserves_fully_inferred
          with (s := h) (def_ss := def_ss) (conn_map := conn_map) (scope := scope)
               (1 := H) (2 := proj1 H0) (3 := H1).
    destruct (ExpandBranch_fun h def_ss conn_map scope) as [[[temp_def_ss temp_conn_map] temp_scope]|] ; last by discriminate H2.
    specialize (ExpandBranch_fun_preserves_fully_inferred temp_def_ss temp_conn_map temp_scope Logic.eq_refl).
    apply (IHss temp_def_ss temp_conn_map temp_scope def_ss' conn_map' scope'
                     (proj1 ExpandBranch_fun_preserves_fully_inferred)
                     (proj2 H0)
                     (proj2 ExpandBranch_fun_preserves_fully_inferred)
                      H2).
* clear ExpandBranch_fun_preserves_fully_inferred.
  destruct s ; simpl.
  + (* Sskip *)
    intros.
    injection H2 ; clear H2 ; intros ; subst def_ss' conn_map' scope'.
    split.
    - exact H.
    - exact H1.
  + (* Swire *)
    intros.
    injection H2 ; clear H2 ; intros ; subst def_ss' conn_map' scope'.
    destruct f as [gt| |] ; try by discriminate H0.
    split.
    - intro ; specialize (H v).
      destruct (v == s) eqn: Hvs.
      * by rewrite CEP.Lemmas.find_add_eq //.
      * by rewrite CEP.Lemmas.find_add_neq // /PVM.SE.eq Hvs //.
    - intro ; specialize (H1 k).
      destruct (k == s) eqn: Hks.
      * by rewrite CEP.Lemmas.find_add_eq //.
      * by rewrite CEP.Lemmas.find_add_neq // /PVM.SE.eq Hks //.
  + (* Sreg *)
    intros.
    destruct (reset h).
    2: destruct (match type_of_expr h0 scope with
                 | Some _ =>
                     match type_of_expr h1 (CEP.add s (type h, HiF.Duplex) scope) with
                     | Some _ => true
                     | None => false
                     end
                 | None => false
                 end) ; last by discriminate H2.
    1,2: destruct (type_of_expr (clock h) scope) ; last by discriminate H2.
    1,2: destruct (type h) as [gt| |] ; try by discriminate H0.
    1,2: move /andP : H0 => [_ H0].
    1,2: injection H2 ; clear H2 ; intros ; subst def_ss' conn_map' scope'.
    1,2: split.
    - 1,3: intro ; specialize (H v).
      1,2: destruct (v == s) eqn: Hvs ;
            try (by rewrite CEP.Lemmas.find_add_eq //).
      1,2: by rewrite CEP.Lemmas.find_add_neq // /PVM.SE.eq Hvs //.
    - 1,2: intro ; specialize (H1 k).
      1,2: destruct (k == s) eqn: Hks ;
            try (by rewrite CEP.Lemmas.find_add_eq //).
      1,2: by rewrite CEP.Lemmas.find_add_neq // /PVM.SE.eq Hks //.
  + (* Smem *)
    intros ; discriminate H2.
  + (* Sinst *)
    intros ; discriminate H2.
  + (* Snode *)
    intros.
    generalize (expr_preserves_fully_inferred scope H h H0) ; intro.
    destruct (type_of_expr h scope) as [[[gt| |] _]|] ; try by done.
    injection H2 ; clear H2 ; intros ; subst def_ss' conn_map' scope'.
    split.
    - intro ; specialize (H v).
      destruct (v == s) eqn: Hvs.
      * by rewrite CEP.Lemmas.find_add_eq //.
      * by rewrite CEP.Lemmas.find_add_neq // /PVM.SE.eq Hvs //.
    - exact H1.
  + (* Sfcnct *)
    intros.
    unfold ExpandBranch_connect in H2.
    destruct h ; try (by discriminate H2).
    simpl type_of_ref.
    destruct (CEP.find s scope) as [[ft_ref [| | | |]]|] eqn: Hsscope ; try by discriminate H2.
    1,2: move /andP : H0 => [_ H0].
    1,2: generalize (expr_preserves_fully_inferred scope H h0 H0) ; intro.
    1,2: destruct (type_of_expr h0 scope) as [[[gt| |] p]|] eqn: Htexpr ; try done.
    1,2: destruct ft_ref as [gt_ref| |] ; try by discriminate H2.
    1,2: destruct (connect_type_compatible false (Gtyp gt_ref) (Gtyp gt) false) eqn: Hconn_comp ; last by discriminate H2.
    1,2: injection H2 ; clear H2 ; intros ; subst def_ss' conn_map' scope'.
    1,2: split ; first by exact H.
    1,2: intro ; specialize (H1 k).
    1,2: destruct (k == s) eqn: Hks ;
               first by rewrite CEP.Lemmas.find_add_eq //.
    1,2: by rewrite CEP.Lemmas.find_add_neq // /PVM.SE.eq Hks //.
  + (* Sinvalid *)
    intros.
    unfold ExpandBranch_connect in H2.
    destruct h ; try (by discriminate H2).
    simpl type_of_ref.
    destruct (CEP.find s scope) as [[ft_ref [| | | |]]|] ; try by discriminate H2.
    1,2: injection H2 ; clear H2 ; intros ; subst def_ss' conn_map' scope'.
    1,2: split ; first by exact H.
    1,2: intro ; specialize (H1 k).
    1,2: destruct (k == s) eqn: Hks ;
               first by by rewrite CEP.Lemmas.find_add_eq //.
    1,2: by rewrite CEP.Lemmas.find_add_neq // /PVM.SE.eq Hks //.
  + (* Swhen *)
    rename h into cond ; rename h0 into ss_true ; rename h1 into ss_false.
    intros.
    destruct (type_of_expr cond scope) as [[[[[|[|]]| | | | | |]| |] _]|] ; try by discriminate H2.
    move /andP : H0 => [/andP H3 H0].
    generalize (ExpandBranch_funs_preserves_fully_inferred ss_true def_ss conn_map scope) ; intro.
    destruct (ExpandBranch_funs ss_true def_ss conn_map scope) as [[[true_def_ss true_conn_map] true_scope]|] ;
          last by discriminate H2.
    specialize (H4 true_def_ss true_conn_map true_scope H (proj2 H3) H1 Logic.eq_refl).
    specialize (ExpandBranch_funs_preserves_fully_inferred ss_false true_def_ss (extend_map_with conn_map true_conn_map) scope).
    destruct (ExpandBranch_funs ss_false true_def_ss
                            (extend_map_with conn_map true_conn_map)
                            scope) as [[[false_def_ss false_conn_map] false_scope]|] ;
          last by discriminate H2.
    assert (ct_has_fully_inferred_ground_types (extend_map_with conn_map true_conn_map)).
          intro.
          rewrite /extend_map_with CEP.Lemmas.map2_1bis //.
          specialize (H1 k).
          destruct (CEP.find k conn_map) as [|] ; first by done.
          by apply H4.
    specialize (ExpandBranch_funs_preserves_fully_inferred false_def_ss false_conn_map false_scope
                H H0 H5 Logic.eq_refl).
    injection H2 ; clear H2 ; intros ; subst def_ss' conn_map' scope'.
    split.
    - exact H.
    - destruct H4 as [_ H4] ; destruct ExpandBranch_funs_preserves_fully_inferred as [_ ExpandBranch_funs_preserves_fully_inferred].
      intro.
      rewrite CEP.Lemmas.map2_1bis //.
      specialize (H4 k) ; specialize (ExpandBranch_funs_preserves_fully_inferred k).
      destruct (CEP.find k true_conn_map) as [[| |true_expr]|], (CEP.find k false_conn_map) as [[| |false_expr]|] ; try done.
      simpl.
      destruct (true_expr == false_expr) ; first by exact H4.
      simpl.
      by rewrite (proj1 H3) H4 ExpandBranch_funs_preserves_fully_inferred //.
Qed.


Fixpoint stmts_respect_scopes (ss : HiFP.hfstmt_seq) (scope : CEP.t (ftype * HiF.forient)) : option (CEP.t (ftype * HiF.forient)) :=
(* checks whether the statement sequence ss respects scopes.
   If it does, returns the scope after applying the component statements in ss. *)
match ss with
| Qnil => Some scope
| Qcons s ss =>
    match stmt_respects_scopes s scope with
    | Some temp_scope => stmts_respect_scopes ss temp_scope
    | None => None
    end
end
with stmt_respects_scopes (s : HiFP.hfstmt) (scope : CEP.t (ftype * HiF.forient)) : option (CEP.t (ftype * HiF.forient)) :=
match s with
| Sskip => Some scope
| Swire v (Gtyp gt) =>
    match CEP.find v scope with
    | Some _ => None
    | None => Some (CEP.add v (Gtyp gt, HiF.Duplex) scope)
    end
| Sreg v reg =>
    match CEP.find v scope with
    | Some _ => None
    | None => Some (CEP.add v (type reg, HiF.Duplex) scope)
    end
| Snode v expr =>
    match CEP.find v scope, type_of_expr expr scope with
    | None, Some (exist (Gtyp gt_expr) _) => Some (CEP.add v (Gtyp gt_expr, HiF.Source) scope)
    | _, _ => None
    end
| Sfcnct ref expr =>
    match type_of_ref ref scope with
    | Some (Gtyp _, HiF.Sink)
    | Some (Gtyp _, HiF.Duplex) =>
        match type_of_expr expr scope with
        | Some (exist (Gtyp _) _) => Some scope
        | _ => None
        end
    | _ => None
    end
| Sinvalid ref =>
    match type_of_ref ref scope with
    | Some (Gtyp _, HiF.Sink)
    | Some (Gtyp _, HiF.Duplex) => Some scope
    | _ => None
    end
| Swhen c ss_true ss_false =>
    match type_of_expr c scope, stmts_respect_scopes ss_true scope, stmts_respect_scopes ss_false scope with
    | Some (exist (Gtyp (Fuint 1)) _), Some _, Some _ => Some scope
    | _, _, _ => None
    end
| _ => None
end.


Lemma ExpandBranch_fun_submap :
forall (s : HiFP.hfstmt) (def_ss : HiFP.hfstmt_seq) (conn_map : CEP.t def_expr) (scope : CEP.t (ftype * HiF.forient)),
    stmt_respects_scopes s scope ->
        match ExpandBranch_fun s def_ss conn_map scope with
        | Some (_, _, scope') =>
                stmt_respects_scopes s scope = Some scope'
            /\
                CEP.submap scope scope'
        | None => True
        end
with ExpandBranch_funs_submap :
forall (ss def_ss : HiFP.hfstmt_seq) (conn_map : CEP.t def_expr) (scope : CEP.t (ftype * HiF.forient)),
    stmts_respect_scopes ss scope ->
        match ExpandBranch_funs ss def_ss conn_map scope with
        | Some (_, _, scope') =>
                stmts_respect_scopes ss scope = Some scope'
            /\
                CEP.submap scope scope'
        | None => True
        end.
Proof.
* clear ExpandBranch_fun_submap.
  induction s ; simpl ; intros.
  + (* Sskip *)
    split ; first by reflexivity.
    by apply CEP.Lemmas.submap_refl.
  + (* Swire *)
    destruct f ; try discriminate H.
    split.
    2: apply CEP.Lemmas.submap_none_add ; first by apply CEP.Lemmas.submap_refl.
    1,2: destruct (CEP.find s scope) ; done.
  + (* Sreg *)
    destruct (match reset h with
              | @NRst _ => true
              | Rst rst_sig rst_val =>
                  match type_of_expr rst_sig scope with
                  | Some _ =>
                      match
                        type_of_expr rst_val (CEP.add s (type h, HiF.Duplex) scope)
                      with
                      | Some _ => true
                      | None => false
                      end
                  | None => false
                  end
              end) ; last by trivial.
    destruct (type_of_expr (clock h) scope) ; last by trivial.
    split.
    2: apply CEP.Lemmas.submap_none_add ; first by apply CEP.Lemmas.submap_refl.
    1,2: destruct (CEP.find s scope) ; done.
  + (* Smem *)
    by trivial.
  + (* Sinst *)
    by trivial.
  + (* Snode *)
    destruct (type_of_expr h scope) as [[[]]|] ; try by trivial.
    - split.
      2: apply CEP.Lemmas.submap_none_add ; first by apply CEP.Lemmas.submap_refl.
    1-4: destruct (CEP.find s scope) ; done.
  + (* Sfcnct *)
    unfold ExpandBranch_connect.
    destruct h ; try (by trivial).
    simpl type_of_ref ; simpl type_of_ref in H.
    destruct (CEP.find s scope) as [[[gt_ref| |] [| | | |]]|] ; try by discriminate H.
    1,2: destruct (type_of_expr h0 scope) as [[[gt_expr| |] _]|] ; try by discriminate H.
    1,2: simpl connect_type_compatible.
    1,2: destruct gt_ref, gt_expr ; try destruct (n0 <= n) ; split ; try by done ;
         by apply CEP.Lemmas.submap_refl.
  + (* Sinvalid *)
    unfold ExpandBranch_connect.
    destruct h ; try (by trivial).
    simpl type_of_ref ; simpl type_of_ref in H.
    destruct (CEP.find s scope) as [[[gt_ref| |] [| | | |]]|] ; try by discriminate H.
    1,2: split ; first by reflexivity.
    1,2: by apply CEP.Lemmas.submap_refl.
  + (* Swhen *)
    rename h into cond ; rename h0 into ss_true ; rename h1 into ss_false.
    destruct (type_of_expr cond scope) as [[[[[|[|]]| | | | | |]| |] _]|] ; try by discriminate H.
    destruct (ExpandBranch_funs ss_true def_ss conn_map scope) as [[[true_def_ss true_conn_map] true_scope]|]; last by trivial.
    destruct (ExpandBranch_funs ss_false true_def_ss (extend_map_with conn_map true_conn_map) scope) as [[[]]|] ; last by trivial.
    split.
    - destruct (stmts_respect_scopes ss_true scope) ; last by discriminate H.
      destruct (stmts_respect_scopes ss_false scope) ; last by discriminate H.
      by reflexivity.
    - by apply CEP.Lemmas.submap_refl.
* clear ExpandBranch_funs_submap.
  induction ss ; simpl ; intros.
  + split ; first by reflexivity.
    by apply CEP.Lemmas.submap_refl.
  + specialize (ExpandBranch_fun_submap h def_ss conn_map scope).
    destruct (stmt_respects_scopes h scope) ; last by discriminate H.
    specialize (ExpandBranch_fun_submap is_true_true).
    destruct (ExpandBranch_fun h def_ss conn_map scope) as [[[temp_def_ss temp_conn_map] temp_scope]|] ; last by trivial.
    destruct ExpandBranch_fun_submap as [H0 ExpandBranch_fun_submap] ;
    injection H0 ; clear H0 ; intros ; subst t.
    specialize (IHss temp_def_ss temp_conn_map temp_scope H).
    destruct (ExpandBranch_funs ss temp_def_ss temp_conn_map temp_scope) as [[[] new_scope]|]; last by trivial.
    split ; first by apply IHss.
    apply (CEP.Lemmas.submap_trans ExpandBranch_fun_submap), IHss.
Qed.


Lemma ExpandBranch_funs_preserves_connect_compatible :
forall (vm : CEP.t vertex_type) (tmap : CEP.t (ftype * HiF.forient))
       (ss def_ss : HiFP.hfstmt_seq) (conn_map : CEP.t def_expr) (scope : CEP.t (ftype * HiF.forient))
       (def_ss' : HiFP.hfstmt_seq) (conn_map' : CEP.t def_expr) (scope' : CEP.t (ftype * HiF.forient)),
    (exists old_tmap_scope new_tmap_scope : CEP.t (ftype * HiF.forient) * CEP.t (ftype * HiF.forient),
            CEP.submap old_tmap_scope.2 old_tmap_scope.1
        /\
            stmts_tmap old_tmap_scope ss vm = Some new_tmap_scope
        /\
            CEP.submap scope old_tmap_scope.2
        /\
            CEP.submap new_tmap_scope.1 tmap) ->
    tmap_has_fully_inferred_ground_types tmap ->
    stmts_have_fully_inferred_ground_types ss ->
    ct_has_fully_inferred_ground_types conn_map ->
    ExpandBranch_funs ss def_ss conn_map scope = Some (def_ss', conn_map', scope') ->
        forall v : CEP.key,
            (if CEP.find v conn_map is Some (D_fexpr expr)
            then match type_of_ref (Eid v) tmap, type_of_expr expr tmap with
                 | Some (Gtyp gt_tgt, _), Some (exist (Gtyp gt_src) _) => connect_type_compatible false (Gtyp gt_tgt) (Gtyp gt_src) false
                 | _, _ => false
                 end
            else true) ->
                if CEP.find v conn_map' is Some (D_fexpr expr)
                then match type_of_ref (Eid v) tmap, type_of_expr expr tmap with
                     | Some (Gtyp gt_tgt, _), Some (exist (Gtyp gt_src) _) => connect_type_compatible false (Gtyp gt_tgt) (Gtyp gt_src) false
                     | _, _ => false
                     end
                else true
with ExpandBranch_fun_preserves_connect_compatible :
forall (vm : CEP.t vertex_type) (tmap : CEP.t (ftype * HiF.forient))
       (s : HiFP.hfstmt)  (def_ss : HiFP.hfstmt_seq) (conn_map : CEP.t def_expr) (scope : CEP.t (ftype * HiF.forient))
       (def_ss' : HiFP.hfstmt_seq) (conn_map' : CEP.t def_expr) (scope' : CEP.t (ftype * HiF.forient)),
    (exists old_tmap_scope new_tmap_scope : CEP.t (ftype * HiF.forient) * CEP.t (ftype * HiF.forient),
            CEP.submap old_tmap_scope.2 old_tmap_scope.1
        /\
            stmt_tmap old_tmap_scope s vm = Some new_tmap_scope
        /\
            CEP.submap scope old_tmap_scope.2
        /\
            CEP.submap new_tmap_scope.1 tmap) ->
    tmap_has_fully_inferred_ground_types tmap ->
    stmt_has_fully_inferred_ground_types s ->
    ct_has_fully_inferred_ground_types conn_map ->
    ExpandBranch_fun s def_ss conn_map scope = Some (def_ss', conn_map', scope') ->
        forall v : CEP.key,
            (if CEP.find v conn_map is Some (D_fexpr expr)
            then match type_of_ref (Eid v) tmap, type_of_expr expr tmap with
                 | Some (Gtyp gt_tgt, _), Some (exist (Gtyp gt_src) _) => connect_type_compatible false (Gtyp gt_tgt) (Gtyp gt_src) false
                 | _, _ => false
                 end
            else true) ->
                if CEP.find v conn_map' is Some (D_fexpr expr)
                then match type_of_ref (Eid v) tmap, type_of_expr expr tmap with
                     | Some (Gtyp gt_tgt, _), Some (exist (Gtyp gt_src) _) => connect_type_compatible false (Gtyp gt_tgt) (Gtyp gt_src) false
                     | _, _ => false
                     end
                else true.
Proof.
* clear ExpandBranch_funs_preserves_connect_compatible.
  induction ss ; simpl ; intros.
  + injection H3 ; clear H3 ; intros ; subst def_ss' conn_map' scope'.
    exact H4.
  + rename h into s.
    destruct H as [old_tmap_scope [[new_tmap new_scope] H]] ; simpl fst in H.
    move /andP : H1 => H1.
    generalize (stmt_submap vm s old_tmap_scope.1 old_tmap_scope.2 (proj1 H)) ; intro.
    specialize (ExpandBranch_stmt_tmap vm s old_tmap_scope.1) with (old_scope1 := old_tmap_scope.2)
               (old_scope2 := scope) (old_def_ss := def_ss) (old_conn_map := conn_map) ; intro.
    rewrite -surjective_pairing in H5, H6.
    destruct (stmt_tmap old_tmap_scope s vm) as [[temp_tmap temp_scope]|] eqn: Hstmt_tmap_s ;
          last by discriminate (proj1 (proj2 H)).
    specialize (H6 temp_tmap temp_scope) with (1 := Logic.eq_refl) (3 := proj1 (proj2 (proj2 H))) (4 := proj1 H1).
    generalize (stmts_submap vm ss temp_tmap temp_scope (proj1 H5)) ; intro.
    rewrite (proj1 (proj2 H)) in H7.
    assert (Hs : exists old_tmap_scope new_tmap_scope : CEP.t (ftype * HiF.forient) * CEP.t (ftype * HiF.forient),
                         CEP.submap old_tmap_scope.2 old_tmap_scope.1
                     /\
                         stmt_tmap old_tmap_scope s vm = Some new_tmap_scope
                     /\
                         CEP.submap scope old_tmap_scope.2
                     /\
                         CEP.submap new_tmap_scope.1 tmap).
          exists old_tmap_scope, (temp_tmap, temp_scope).
          split.
          - by apply H.
          split.
          - by apply Hstmt_tmap_s.
          split.
          - by apply H.
          - by apply (CEP.Lemmas.submap_trans (proj1 (proj2 H7))), H.
    specialize (ExpandBranch_fun_preserves_connect_compatible vm tmap s
                def_ss conn_map scope) with (1 := Hs) (2 := H0) (3 := proj1 H1) (4 := H2).
    generalize (ExpandBranch_fun_submap s def_ss conn_map scope) ; intro.
    assert (tmap_has_fully_inferred_ground_types scope).
          assert (CEP.submap scope tmap)
                by apply (CEP.Lemmas.submap_trans (proj1 (proj2 (proj2 H)))),
                         (CEP.Lemmas.submap_trans (proj2 (proj2 H5))),
                         (CEP.Lemmas.submap_trans (proj2 (proj2 H7))),
                         (CEP.Lemmas.submap_trans (proj1 H7)), H.
          intro ; specialize (H0 v0) ; specialize (H9 v0).
          destruct (CEP.find v0 scope) ; try by trivial.
          rewrite (H9 _ Logic.eq_refl) // in H0.
    specialize (ExpandBranch_fun_preserves_fully_inferred) with (scope := scope) (s := s) (def_ss := def_ss) (conn_map := conn_map)
                (1 := H9) (2 := proj1 H1) (3 := H2) ; intro.
    destruct (ExpandBranch_fun s def_ss conn_map scope) as [[[temp_def_ss temp_conn_map] temp_scope']|] ; last by discriminate H3.
    specialize (H6 temp_scope' temp_def_ss temp_conn_map Logic.eq_refl).
    specialize (H10 temp_def_ss temp_conn_map temp_scope' Logic.eq_refl).
    specialize (ExpandBranch_fun_preserves_connect_compatible temp_def_ss temp_conn_map temp_scope' Logic.eq_refl v).
    assert (Hss : exists old_tmap_scope new_tmap_scope : CEP.t (ftype * HiF.forient) * CEP.t (ftype * HiF.forient),
                          CEP.submap old_tmap_scope.2 old_tmap_scope.1
                      /\
                          stmts_tmap old_tmap_scope ss vm = Some new_tmap_scope
                      /\
                          CEP.submap temp_scope' old_tmap_scope.2
                      /\
                          CEP.submap new_tmap_scope.1 tmap).
          exists (temp_tmap, temp_scope), (new_tmap, new_scope).
          split.
          - by apply H5.
          split.
          - by apply H.
          split.
          - by apply H6.
          - by apply H.
    specialize (IHss temp_def_ss temp_conn_map temp_scope' def_ss' conn_map' scope'
                     Hss H0 (proj2 H1) (proj2 H10) H3 v).
    by apply IHss, ExpandBranch_fun_preserves_connect_compatible, H4.
* clear ExpandBranch_fun_preserves_connect_compatible.
  destruct s ; simpl ; intros.
  + (* Sskip *)
    injection H3 ; clear H3 ; intros ; subst def_ss' conn_map' scope'.
    exact H4.
  + (* Swire *)
    injection H3 ; clear H3 ; intros ; subst def_ss' conn_map' scope'.
    destruct f as [gt| |] ; try by discriminate H1.
    destruct (v == s) eqn: Hvs.
    - by rewrite (CEP.Lemmas.find_add_eq (m := conn_map) (e := D_undefined) Hvs) //.
    - by rewrite (CEP.Lemmas.find_add_neq (m := conn_map) (e := D_undefined)) // /PVM.SE.eq Hvs //.
  + (* Sreg *)
    destruct H as [old_tmap_scope [new_tmap_scope H]].
    destruct (CEP.find s old_tmap_scope.1) eqn: Hfinds ;
          first by discriminate (proj1 (proj2 H)).
    destruct (type h) as [gt| |] ; try by discriminate H1.
    destruct (type_of_expr (clock h) old_tmap_scope.2) ;
           last by discriminate (proj1 (proj2 H)).
    destruct (reset h).
    1,2: move /andP : H1 => [_ H1].
    1,2: generalize (fully_inferred_does_not_change gt s vm H1) ; intro.
    1,2: destruct (code_type_find_vm_widths (Gtyp gt) s vm) as [[[gt'| |]]|] ;
            last (by discriminate (proj1 (proj2 H))) ;
            try by contradiction H5.
    1,2: subst gt'.
    - 2: generalize (type_of_expr_submap h0 scope old_tmap_scope.2 (proj1 (proj2 (proj2 H)))) ; intro.
      2: destruct (type_of_expr h0 scope) as [[[[[|[]]| | | | | |]| |]]|] ;
            last (by discriminate H3) ;
            rewrite H5 in H ; clear H5 ;
            try by discriminate (proj1 (proj2 H)).
      2,3: destruct (type_of_expr h1 (CEP.add s (Gtyp gt, HiF.Duplex) scope)) ;
            last by discriminate H3.
      2: destruct (type_of_expr h1 (CEP.add s (Gtyp gt, HiF.Duplex) old_tmap_scope.2)) ;
            last by discriminate (proj1 (proj2 H)).
      3: destruct (type_of_expr h1 old_tmap_scope.2) ;
            last by discriminate (proj1 (proj2 H)).
    1-3: destruct (type_of_expr (clock h) scope) ;
            last by discriminate H3.
    1-3: injection H3 ; clear H3 ; intros ; subst def_ss' conn_map' scope'.
    1-3: assert (CEP.submap (CEP.add s (Gtyp gt, HiF.Duplex) old_tmap_scope.2) tmap)
               by (destruct new_tmap_scope as [new_tmap new_scope] ;
                   injection (proj1 (proj2 H)) ; intros ; subst new_tmap new_scope ;
                   apply (CEP.Lemmas.submap_trans (submap_add_add old_tmap_scope.2 old_tmap_scope.1 _ _ (proj1 H))), H).
    1-3: destruct (v == s) eqn: Hvs.
    - 1,3,5: rewrite (CEP.Lemmas.find_add_eq (m := conn_map) (e := D_fexpr (Eref (Eid (var:=ProdVarOrder.T) s))) Hvs) //.
      1-3: specialize (H3 s).
      1-3: rewrite (CEP.Lemmas.find_add_eq (eq_refl s)) in H3.
      1-3: specialize (H3 _ Logic.eq_refl).
      1-3: move /eqP : Hvs => Hvs ; rewrite Hvs.
      1-3: simpl type_of_expr.
      1-3: rewrite H3.
      1-3: destruct gt ; by rewrite // leqnn //.
    - 1-3: move /negP : Hvs => Hvs.
      1-3: by rewrite (CEP.Lemmas.find_add_neq (m := conn_map) (e := D_fexpr (Eref (Eid (var:=ProdVarOrder.T) s))) Hvs) //.
  + (* Smem *)
    by discriminate H3.
  + (* Sinst *)
    by discriminate H3.
  + (* Snode *)
    destruct (type_of_expr h scope) as [[]|] ; try by discriminate H3.
    injection H3 ; clear H3 ; intros ; subst def_ss' conn_map' scope'.
    by exact H4.
  + (* Sfcnct *)
    unfold ExpandBranch_connect in H3.
    destruct h ; try (by discriminate H3).
    destruct H as [old_tmap_scope [new_tmap_scope H]].
    simpl type_of_ref in H.
    specialize (proj1 (proj2 (proj2 H)) s) ; intro.
    destruct (CEP.find s scope) as [[ft_ref [| | | |]]|] ; try by discriminate H3.
    1,2: specialize (H5 _ Logic.eq_refl).
    1,2: rewrite H5 in H.
    1,2: generalize (type_of_expr_submap h0 scope old_tmap_scope.2 (proj1 (proj2 (proj2 H)))) ; intro.
    1,2: destruct (type_of_expr h0 scope) as [[ft_expr p]|] ; last by discriminate H3.
    1,2: rewrite H6 in H.
    1,2: injection (proj1 (proj2 H)) ; intros ; subst new_tmap_scope.
    1,2: specialize (proj1 H s) ; intro ; rewrite H5 in H7 ;
         specialize (H7 _ Logic.eq_refl) ; clear H5.
    1,2: specialize (proj2 (proj2 (proj2 H)) s) ; intro ; rewrite H7 in H5 ;
         specialize (H5 _ Logic.eq_refl) ; clear H7.
    1,2: destruct ft_ref as [gt_ref| |] ; try by (specialize (H0 s) ; rewrite H5 // in H0).
    1,2: generalize (type_of_expr_submap h0 old_tmap_scope.2 old_tmap_scope.1 (proj1 H)) ; intro.
    1,2: rewrite H6 in H7 ; clear H6.
    1,2: generalize (type_of_expr_submap h0 old_tmap_scope.1 tmap (proj2 (proj2 (proj2 H)))) ; intro.
    1,2: rewrite H7 in H6 ; clear H7.
    1,2: move /andP : H1 => [_ H1].
    1,2: generalize (expr_preserves_fully_inferred tmap H0 h0 H1) ; intro.
    1,2: rewrite H6 in H7.
    1,2: destruct ft_expr as [gt_expr| |] ; try by contradiction H7.
    1,2: destruct (connect_type_compatible false (Gtyp gt_ref) (Gtyp gt_expr) false) eqn: Hconn_comp ; last by discriminate H3.
    1,2: injection H3 ; clear H3 ; intros ; subst def_ss' conn_map' scope'.
    1,2: destruct (v == s) eqn: Hvs.
    - 1,3: rewrite (CEP.Lemmas.find_add_eq (m := conn_map) (e := D_fexpr h0)) //.
      1,2: move /eqP : Hvs => Hvs ; rewrite Hvs H5 H6.
      1,2: simpl connect_type_compatible in Hconn_comp.
      1,2: by rewrite Hconn_comp //.
    - 1,2: move /negP : Hvs => Hvs.
      1,2: by rewrite (CEP.Lemmas.find_add_neq (m := conn_map) (e := D_fexpr h0) Hvs) //.
  + (* Sinvalid *)
    unfold ExpandBranch_connect in H3.
    destruct h ; try (by discriminate H3).
    destruct H as [old_tmap_scope [new_tmap_scope H]].
    simpl type_of_ref in H.
    specialize (proj1 (proj2 (proj2 H)) s) ; intro.
    destruct (CEP.find s scope) as [[ft_ref [| | | |]]|] ; try by discriminate H3.
    1,2: specialize (H5 _ Logic.eq_refl).
    1,2: rewrite H5 in H.
    1,2: injection (proj1 (proj2 H)) ; intros ; subst new_tmap_scope.
    1,2: specialize (proj1 H s) ; intro ; rewrite H5 in H6 ;
         specialize (H6 _ Logic.eq_refl) ; clear H5.
    1,2: specialize (proj2 (proj2 (proj2 H)) s) ; intro ; rewrite H6 in H5 ;
         specialize (H5 _ Logic.eq_refl) ; clear H6.
    1,2: destruct ft_ref as [gt_ref| |] ; try by (specialize (H0 s) ; rewrite H5 // in H0).
    1,2: injection H3 ; clear H3 ; intros ; subst def_ss' conn_map' scope'.
    1,2: destruct (v == s) eqn: Hvs ;
         first by rewrite (CEP.Lemmas.find_add_eq (m := conn_map) (e := D_invalidated)) //.
    1,2: move /negP : Hvs => Hvs ;
         by rewrite (CEP.Lemmas.find_add_neq (m := conn_map) (e := D_invalidated) Hvs) //.
  + (* Swhen *)
    rename h into cond ; rename h0 into ss_true ; rename h1 into ss_false.
    destruct H as [old_tmap_scope [new_tmap_scope H]].
    generalize (type_of_expr_submap cond scope old_tmap_scope.2 (proj1 (proj2 (proj2 H)))) ; intro.
    destruct (type_of_expr cond scope) as [[[[[|[|]]| | | | | |]| |] p]|] ; try by discriminate H3.
    rewrite H5 in H.
    generalize (stmts_submap vm ss_true old_tmap_scope.1 old_tmap_scope.2 (proj1 H)) ; intro.
    rewrite -surjective_pairing in H6.
    destruct (stmts_tmap old_tmap_scope ss_true vm) as [[tmap_true scope_true]|] eqn: Hstt ; last by discriminate (proj1 (proj2 H)).
    generalize (CEP.Lemmas.submap_trans (proj1 H) (proj1 (proj2 H6))) ; intro.
    apply (stmts_submap vm ss_false tmap_true old_tmap_scope.2) in H7.
    destruct (stmts_tmap (tmap_true, old_tmap_scope.2) ss_false vm) as [[tmap_false scope_false]|] eqn: Hstf ; last by discriminate (proj1 (proj2 H)).
    move /andP : H1 => [/andP H8 H1].
    destruct new_tmap_scope as [new_tmap new_scope] ;
    injection (proj1 (proj2 H)) ; intros ; subst tmap_false new_scope ; simpl fst in H.
    generalize (type_of_expr_submap cond old_tmap_scope.2 scope_false (proj2 (proj2 H7))) ; intro.
    rewrite H5 in H9 ; clear H5.
    generalize (type_of_expr_submap cond scope_false new_tmap (proj1 H7)) ; intro.
    rewrite H9 in H5 ; clear H9.
    generalize (type_of_expr_submap cond new_tmap tmap (proj2 (proj2 (proj2 H)))) ; intro.
    rewrite H5 in H9 ; clear H5.
    assert (tmap_has_fully_inferred_ground_types scope).
          assert (CEP.submap scope tmap)
                by apply (CEP.Lemmas.submap_trans (proj1 (proj2 (proj2 H)))),
                         (CEP.Lemmas.submap_trans (proj2 (proj2 H7))),
                         (CEP.Lemmas.submap_trans (proj1 H7)), H.
          intro ; specialize (H0 v0) ; specialize (H5 v0).
          destruct (CEP.find v0 scope) ; last by trivial.
          rewrite (H5 _ Logic.eq_refl) // in H0.
    generalize (ExpandBranch_funs_preserves_connect_compatible vm tmap ss_true def_ss conn_map scope) ; intro.
    generalize (ExpandBranch_funs_preserves_fully_inferred ss_true def_ss conn_map scope) ; intro.
    (*ExpandBranch_funs_submap ss_true def_ss conn_map scope) ; intro.*)
    destruct (ExpandBranch_funs ss_true def_ss conn_map scope) as [[[true_def_ss true_conn_map] true_scope]|] ;
          last by discriminate H3.
    specialize (H11 true_def_ss true_conn_map true_scope H5 (proj2 H8) H2 Logic.eq_refl).
    assert (Ht : exists old_tmap_scope new_tmap_scope : CEP.t (ftype * HiF.forient) * CEP.t (ftype * HiF.forient),
                         CEP.submap old_tmap_scope.2 old_tmap_scope.1
                     /\
                         stmts_tmap old_tmap_scope ss_true vm = Some new_tmap_scope
                     /\
                         CEP.submap scope old_tmap_scope.2
                     /\
                         CEP.submap new_tmap_scope.1 tmap).
          exists old_tmap_scope, (tmap_true, scope_true).
          split.
          - by apply H.
          split.
          - by exact Hstt.
          split.
          - by apply H.
          - apply (CEP.Lemmas.submap_trans (proj1 (proj2 H7))), H.
    specialize (H10 true_def_ss true_conn_map true_scope Ht H0 (proj2 H8) H2 Logic.eq_refl).
    specialize (ExpandBranch_funs_preserves_connect_compatible vm tmap ss_false true_def_ss (extend_map_with conn_map true_conn_map) scope).
    (*generalize (ExpandBranch_funs_submap ss_false true_def_ss (extend_map_with conn_map true_conn_map) scope) ; intro.*)
    destruct (ExpandBranch_funs ss_false true_def_ss
                            (extend_map_with conn_map true_conn_map)
                            scope) as [[[false_def_ss false_conn_map] false_scope]|] ;
          last by discriminate H3.
    assert (Hf : exists old_tmap_scope new_tmap_scope : CEP.t (ftype * HiF.forient) * CEP.t (ftype * HiF.forient),
                         CEP.submap old_tmap_scope.2 old_tmap_scope.1
                     /\
                         stmts_tmap old_tmap_scope ss_false vm = Some new_tmap_scope
                     /\
                         CEP.submap scope old_tmap_scope.2
                     /\
                         CEP.submap new_tmap_scope.1 tmap).
          exists (tmap_true, old_tmap_scope.2), (new_tmap, scope_false).
          split.
          - by apply (CEP.Lemmas.submap_trans (proj1 H)), H6.
          split.
          - by exact Hstf.
          split.
          - by apply H.
          - by apply H.
    assert (ct_has_fully_inferred_ground_types (extend_map_with conn_map true_conn_map)).
          intro.
          rewrite /extend_map_with CEP.Lemmas.map2_1bis //.
          specialize (H2 k).
          destruct (CEP.find k conn_map) ; first by exact H2.
          by apply H11.
    specialize (ExpandBranch_funs_preserves_connect_compatible false_def_ss false_conn_map false_scope
                Hf H0 H1 H12 Logic.eq_refl).
    injection H3 ; clear H3 ; intros ; subst def_ss' conn_map' scope'.
    rewrite CEP.Lemmas.map2_1bis //.
    specialize (H10 v) ; specialize (ExpandBranch_funs_preserves_connect_compatible v).
    rewrite CEP.Lemmas.map2_1bis // in ExpandBranch_funs_preserves_connect_compatible.
    specialize (H10 H4).
    destruct (CEP.find v conn_map) as [[| |old_expr]|] eqn: Hold_conn,
             (CEP.find v true_conn_map) as [[| |true_expr]|] eqn: Htrue_conn,
             (CEP.find v false_conn_map) as [[| |false_expr]|] eqn: Hfalse_conn ;
          simpl ; try done.
    (* old: expression; true: D_invalidated; false: expression *)
    all : try exact (ExpandBranch_funs_preserves_connect_compatible H4).
    (* old: D_undefined; true: expression; false: expression *)
    all: try by (simpl type_of_ref in H10 ;
                 try (specialize (ExpandBranch_funs_preserves_connect_compatible H10)) ;
                 try (specialize (ExpandBranch_funs_preserves_connect_compatible H4)) ;
                 simpl type_of_ref in ExpandBranch_funs_preserves_connect_compatible ;
                 destruct (CEP.find v tmap) as [[[gt_tgt| |] _]|] ; try (by discriminate H10) ;
                 destruct (true_expr == false_expr) ;
                 try (by destruct (type_of_expr true_expr tmap) as [[[gt_srct| |] _]|] ; try (by discriminate H10) ;
                         exact H10) ;
                 simpl type_of_expr ;
                 rewrite H9 ;
                 destruct (type_of_expr true_expr tmap) as [[[gt_srct| |] pt]|] ; try (by discriminate H10) ;
                 destruct (type_of_expr false_expr tmap) as [[[gt_srcf| |] pf]|] ; try (by discriminate ExpandBranch_funs_preserves_connect_compatible) ;
                 destruct gt_tgt, gt_srct, gt_srcf ; try done ;
                 simpl ; simpl in H10 ; simpl in ExpandBranch_funs_preserves_connect_compatible ;
                 rewrite geq_max H10 ExpandBranch_funs_preserves_connect_compatible //).
    (* old: None; true: expression; false: expression *)
    (* That is perhaps a scoping error. But it can be proven by the above proof as well. *)
Qed.


Fixpoint ExpandPort_fun (pp : seq HiFP.hfport) : option (CEP.t def_expr * CEP.t (ftype * HiF.forient)) :=
(* create a map of def_expr for the port sequence pp.
   Out ports need to be assigned value “undefined”;
   in ports do not need to be assigned any value.
   Because types have been lowered already, we can assume
   that all ports have ground types. *)
match pp with
| [::] => Some (CEP.empty def_expr, CEP.empty (ftype * HiF.forient))
| Finput p t :: pp' =>
    match ExpandPort_fun pp' with
    | Some (temp_conn_map, temp_scope) =>
        Some (temp_conn_map, CEP.add p (t, HiF.Source) temp_scope)
    | None => None
    end
| Foutput p t :: pp' =>
    match ExpandPort_fun pp' with
    | Some (temp_conn_map, temp_scope) =>
        Some (CEP.add p D_undefined temp_conn_map, CEP.add p (t, HiF.Sink) temp_scope)
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
forall (tmap : CEP.t (ftype * HiF.forient)) (pp : seq HiFP.hfport) (vm vm_tmap : CEP.t vertex_type) (ct : CEP.t def_expr),
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
1,2: simpl size_of_ftype in H5.
1,2: intro.
1,2: specialize (IHpp (CEP.Lemmas.submap_add_find_none H3 Hfindp') H4).
1,2: destruct (y.1 != p.1) eqn: Hyp1 ; move /eqP : Hyp1 => Hyp1.
* 1,3: destruct H5 as [_ H5] ; specialize (H5 y.1 y.2 (or_introl Hyp1)).
  1,2: rewrite -surjective_pairing in H5 ; rewrite -(proj2 H5).
  2: rewrite CEP.Lemmas.find_add_neq ; last by contradict Hyp1 ; move /eqP : Hyp1 => Hyp1 ; rewrite Hyp1 //.
  1,2: by apply IHpp.
* 1,2: destruct (y.2 < p.2) eqn: Hypsmall.
  + 1,3: destruct H5 as [_ H5] ; specialize (H5 y.1 y.2 (or_intror (or_introl Hypsmall))).
    1,2: rewrite -surjective_pairing in H5 ; rewrite -(proj2 H5).
    2: rewrite CEP.Lemmas.find_add_neq ;
          last by (rewrite ltnNge in Hypsmall ; move /negP : Hypsmall => Hypsmall ;
                   contradict Hypsmall ; move /eqP : Hypsmall => Hypsmall ;
                   rewrite Hypsmall leqnn //).
    1,2: by apply IHpp.
  + 1,2: rewrite add1n in H5.
    1,2: destruct (p.2 < y.2) eqn: Hyplarge.
    - 1,3: destruct H5 as [_ H5] ; specialize (H5 y.1 y.2 (or_intror (or_intror Hyplarge))).
      1,2: rewrite -surjective_pairing in H5 ; rewrite -(proj2 H5).
      2: rewrite CEP.Lemmas.find_add_neq ;
            last by (rewrite ltnNge in Hyplarge ; move /negP : Hyplarge => Hyplarge ;
                     contradict Hyplarge ; move /eqP : Hyplarge => Hyplarge ;
                     rewrite Hyplarge leqnn //).
      1,2: by apply IHpp.
    - 1,2: destruct H5 as [H5 _] ; simpl in H5.
      1,2: move /and3P : H5 => [_ H5 H9].
      1,2: apply negbT in Hypsmall ; rewrite -leqNgt in Hypsmall.
      1,2: apply negbT in Hyplarge ; rewrite -leqNgt in Hyplarge.
      1,2: assert (nat_of_bin y.2 == nat_of_bin p.2)
            by (rewrite eqn_leq Hypsmall Hyplarge //).
      1,2: move /eqP : H10 => H10.
      1,2: assert (y = p)
            by (apply injective_projections ;
                first (by apply Hyp1) ;
                last (by rewrite -(nat_of_binK y.2) H10 nat_of_binK //)).
      1,2: move /eqP : H5 => H5 ; move /eqP : H9 => H9.
      1,2: rewrite H11 H9 -IHpp.
      * rewrite H5 //.
      * rewrite CEP.Lemmas.find_add_eq // /PVM.SE.eq //.
Qed.


Definition helper_connect (v : ProdVarOrder.t) (d : def_expr) (old_ss : HiFP.hfstmt_seq) : HiFP.hfstmt_seq :=
(* The helper function adds a connect statement for reference v.
   If the value is undefined, then silently nothing will be changed. *)
match d with
| D_undefined => old_ss (* component v is still not connected; error *)
| D_invalidated => Qcons (Sinvalid (Eid v)) old_ss
| D_fexpr e => Qcons (Sfcnct (Eid v) e) old_ss
end.

Lemma fold_connect_components :
forall (conn_map : CEP.t def_expr) (ss : HiFP.hfstmt_seq),
    component_stmts_of (CEP.fold helper_connect conn_map ss) = component_stmts_of ss.
Proof.
intro.
(*
assert (forall l : list (CEP.key * def_expr),
          List.fold_left
             (fun (a : option HiFP.hfstmt_seq) (p : CEP.key * def_expr)
                  => helper_connect p.1 p.2 a) l None = None).
      induction l.
      * unfold List.fold_left ; by reflexivity.
      * simpl List.fold_left ; apply IHl.
split ; first by rewrite CEP.fold_1 ; apply H. *)
intros.
rewrite CEP.fold_1.
revert ss.
generalize (CEP.elements conn_map).
induction l.
* intro ; simpl ; by reflexivity.
* intro ; simpl List.fold_left.
  destruct a as [k []] ; simpl ; rewrite IHl //.
Qed.

Definition extend_defined_map_with (m dflt : CEP.t def_expr) : CEP.t def_expr :=
(* Returns map m, except that undefined elements are copied from dflt.
   “undefined” here includes expressions that are assigned an undefined value *)
CEP.map2 (fun (elm eld : option def_expr) => match elm with
                                      | Some D_undefined | None => eld
                                      | _ => elm
                                      end) m dflt.

(*
Lemma test : forall (k : CEP.key) (v : def_expr), CEP.eq_key_elt (k,v) (k,v).
Proof.
rewrite /CEP.eq_key_elt /CEP.SE.eq.
split.
- apply eq_refl.
- reflexivity.
Qed.

Print test.
*)


(* a lemma that states that helper_connect and Sem_frag_stmts are sort of inverses *)
Lemma helper_connect_Sem :
forall (conn_map : CEP.t def_expr) (vm_old : CEP.t vertex_type) (ct_old : CEP.t def_expr) (vm_new : CEP.t vertex_type) (ct_new : CEP.t def_expr) (tmap: CEP.t (ftype * HiF.forient)),
    tmap_has_fully_inferred_ground_types tmap ->
    ct_has_fully_inferred_ground_types conn_map ->
            (Sem_frag_stmts vm_old ct_old (CEP.fold helper_connect conn_map (Qnil ProdVarOrder.T)) vm_new ct_new tmap ->
                    CEP.Equal vm_old vm_new
                /\
                    CEP.Equal ct_new (extend_defined_map_with conn_map ct_old))
        (*/\
            (vm_and_ct_compatible vm_old ct_old ->
            CEP.submap conn_map ct_old ->
            CEP.Equal vm_old vm_new ->
            CEP.Equal ct_new (extend_defined_map_with conn_map ct_old) ->
            "type correctness according to tmap" ->
            (* or perhaps write something like a weak semantics, i.e.
               "if there is no error, then ..." *)
                Sem_frag_stmts vm_old ct_old (CEP.fold helper_connect conn_map (Qnil ProdVarOrder.T)) vm_new ct_new tmap)*).
Proof.
intros until 2.
(*split.*)
* rewrite CEP.Lemmas.P.fold_spec_right.
  assert (SetoidList.equivlistA (PVM.eq_key_elt (elt:=def_expr))
                                (List.rev (CEP.elements conn_map))
                                (CEP.elements conn_map))
        by (intro ;
            apply (SetoidList.InA_rev (PVM.eq_key_elt (elt:=def_expr)))).
  revert H1.
  generalize (CEP.elements_3w conn_map) ; intro.
  assert (Heqv_key : RelationClasses.Equivalence (CEP.eq_key (elt:=def_expr))).
        clear.
        assert (forall x : CEP.key * def_expr, CEP.eq_key x x)
              by (intro ; rewrite /CEP.eq_key /CEP.SE.eq eq_refl //).
        assert (forall x y : CEP.key * def_expr, CEP.eq_key x y -> CEP.eq_key y x)
              by (intros ; rewrite /CEP.eq_key /CEP.SE.eq eq_sym H0 //).
        assert (forall x y z : CEP.key * def_expr, CEP.eq_key x y -> CEP.eq_key y z -> CEP.eq_key x z)
              by (intros ; rewrite H1 H2 /CEP.eq_key /CEP.SE.eq //).
        exact (RelationClasses.Build_Equivalence (CEP.eq_key (elt:=def_expr)) H H0 H1).
  assert (Heqv_key_elt : RelationClasses.Equivalence (CEP.eq_key_elt (elt:=def_expr))).
        clear.
        assert (forall x : CEP.key * def_expr, CEP.eq_key_elt x x)
              by (destruct x ; split ; first (by rewrite /CEP.SE.eq eq_refl //) ; last (by reflexivity)).
        assert (forall x y : CEP.key * def_expr, CEP.eq_key_elt x y -> CEP.eq_key_elt y x)
              by (destruct x, y ; split ; first (by rewrite /CEP.SE.eq eq_sym (proj1 H0) //) ; last (by symmetry ; apply H0)).
        assert (forall x y z : CEP.key * def_expr, CEP.eq_key_elt x y -> CEP.eq_key_elt y z -> CEP.eq_key_elt x z)
              by (destruct x, y, z ; split ; first (by rewrite (proj1 H1) (proj1 H2) /CEP.SE.eq //) ;
                  last (by apply (eq_trans (proj2 H1) (proj2 H2)))).
        exact (RelationClasses.Build_Equivalence (CEP.eq_key_elt (elt:=def_expr)) H H0 H1).
  assert (Heqv_key0 : RelationClasses.Equivalence (fun x y : ProdVarOrder.T => x == y)).
        clear.
        assert (forall x y : ProdVarOrder.T, x == y -> y == x)
              by (intros ; rewrite eq_sym //).
        assert (forall x y z : ProdVarOrder.T, x == y -> y == z -> x == z)
              by (intros ; move /eqP : H0 => H0 ; rewrite H0 //).
        exact (RelationClasses.Build_Equivalence (fun x y : ProdVarOrder.T => x == y) (eq_refl (T := ProdVarOrder.T)) H H0).
  assert (InA_In : forall (k : CEP.key) (d : def_expr) (conn_map_list : seq (CEP.key * def_expr)),
              SetoidList.InA (@CEP.eq_key_elt def_expr) (* (fun p p' : PVM.SE.t * def_expr => PVM.SE.eq p.1 p'.1 /\ p.2 = p'.2) *)
                             (k, d) conn_map_list ->
                  List.In (k, d) conn_map_list).
        (* I think this might be some lemma but I cannot find it... *)
        clear ; intros.
        induction conn_map_list.
        + apply SetoidList.InA_nil in H ; contradiction H.
        + destruct ((k, d) == a) eqn: Hkda ; move /eqP : Hkda => Hkda ;
                first by (rewrite Hkda ; apply List.in_eq).
          apply List.in_cons, IHconn_map_list.
          inversion H ; last by exact H1.
          clear H0 H2 l y.
          destruct H1.
          rewrite /PVM.SE.eq in H0 ; move /eqP : H0 => H0.
          by generalize (injective_projections (k,d) a H0 H1) ; contradiction.
  apply SetoidList.NoDupA_rev in H1 ; last by apply Heqv_key.
  revert H0 H1.
  generalize (List.rev (CEP.elements conn_map)) as conn_map_list.
  intro ; revert conn_map_list vm_old ct_old conn_map.
  induction conn_map_list.
  + unfold List.fold_right.
    intros.
    split ; first by apply H3.
    intro.
    apply RelationClasses.Equivalence_Symmetric, SetoidList.equivlistA_nil_eq in H2 ;
          last by exact Heqv_key_elt.
    apply CEP.Lemmas.P.elements_Empty in H2.
    apply CEP.Lemmas.Empty_find with (x := y) in H2.
    simpl Sem_frag_stmts in H3.
    unfold extend_map_with.
    rewrite CEP.Lemmas.map2_1bis // H2.
    symmetry ; apply H3.
  + destruct a as [k v].
    simpl List.fold_right.
    intros until 3.
    (*destruct (List.fold_right (CEP.Lemmas.P.uncurry helper_connect)
                              (Qnil ProdVarOrder.T) conn_map_list) eqn: Hfold ;
          rewrite Hfold // /CEP.Lemmas.P.uncurry /helper_connect /fst /snd.
    rewrite Hfold in IHconn_map_list.*)
    inversion H1 ; clear H3 H4 x l.
    assert (forall k : CEP.key,
                match CEP.find k (CEP.Lemmas.P.of_list conn_map_list) with
                | Some (D_fexpr e) => expr_has_fully_inferred_ground_types e
                | _ => true
                end).
          intro.
          generalize (CEP.find_2 (m := CEP.Lemmas.P.of_list conn_map_list) (x := k0)) ; intro.
          destruct (CEP.find k0 (CEP.Lemmas.P.of_list conn_map_list)) as [[]|] ; try done.
          specialize (H3 (D_fexpr h) Logic.eq_refl).
          apply (CEP.Lemmas.P.of_list_1 k0 (D_fexpr h) H6), (SetoidList.InA_cons_tl (k, v)),
                H2, CEP.Lemmas.elements_mapsto_iff, CEP.find_1 in H3.
          specialize (H0 k0) ; rewrite H3 // in H0.
    destruct v.
    - (* D_undefined *)
      unfold CEP.Lemmas.P.uncurry ; simpl Sem_frag_stmts.
      intro.
      specialize (IHconn_map_list vm_old ct_old (CEP.Lemmas.P.of_list conn_map_list)
                                  H3 H6 (CEP.Lemmas.P.of_list_2 H6) H4).
      split ; first by apply IHconn_map_list.
      apply (CEP.Lemmas.Equal_trans (proj2 IHconn_map_list)).
      intro.
      unfold extend_map_with.
      rewrite CEP.Lemmas.map2_1bis // (*CEP.Lemmas.P.of_list_1b //. *)
              CEP.Lemmas.map2_1bis //.
      (*
      specialize (H k).
      destruct (CEP.find k tmap) as [[gt| |]|] ; try by contradiction.
      rewrite /size_of_ftype /mkseq in H3 ; simpl in H3.
      rewrite N.add_0_r -surjective_pairing in H3. *)
      destruct (y == k) eqn: Hyk.
      + move /eqP : Hyk => Hyk.
        rewrite Hyk.
        destruct (PVM.find k (CEP.Lemmas.P.of_list conn_map_list)) eqn: Hfind_list.
        - contradict H5.
          apply (SetoidList.InA_eqA Heqv_key (x := (k, d))) ;
                first by rewrite /CEP.eq_key /fst /CEP.SE.eq //.
          apply SetoidList.In_InA ; first by exact Heqv_key.
          rewrite CEP.Lemmas.P.of_list_1b // in Hfind_list.
          apply SetoidList.findA_NoDupA in Hfind_list ;
                last (by exact H6) ;
                last (by exact Heqv_key0).
          apply InA_In, Hfind_list.
        - (* use H2 to show that PVM.find k conn_map = D_undefined *)
          rewrite (CEP.Lemmas.elements_o conn_map k).
          generalize (SetoidList.findA_NoDupA Heqv_key0 HiFP.PVSLemmas.P.FM.eq_dec
                      (l := CEP.elements conn_map) k D_undefined (CEP.elements_3w conn_map)) ; intro.
          rewrite (proj1 H7) //.
          apply H2, SetoidList.InA_cons_hd.
          by done.
      + destruct (PVM.find y (CEP.Lemmas.P.of_list conn_map_list)) eqn: Hfind_list.
        - specialize (H2 (y, d)).
          destruct H2 as [H2 _].
          rewrite CEP.Lemmas.P.of_list_1b in Hfind_list ; last by apply H6.
          apply SetoidList.findA_NoDupA in Hfind_list ;
                last (by apply H6) ; last by apply Heqv_key0.
          apply SetoidList.InA_cons_tl with (y := (k, D_undefined)) in Hfind_list.
          apply H2, CEP.elements_2, CEP.find_1 in Hfind_list.
          rewrite Hfind_list //.
        - destruct (PVM.find y conn_map) eqn: Hfind_map.
          * apply CEP.find_2, CEP.elements_1, H2, SetoidList.InA_cons in Hfind_map.
            destruct Hfind_map as [Hfind_map|Hfind_map] ;
                  first (by rewrite /PVM.eq_key_elt /PVM.Raw.Proofs.PX.eqke /fst Hyk in Hfind_map ;
                            destruct Hfind_map as [Hfind_map _] ; done).
            rewrite CEP.Lemmas.P.of_list_1b in Hfind_list ; last by exact H6.
            apply (SetoidList.findA_NoDupA Heqv_key0 ProdVarOrder.eq_dec y d H6) in Hfind_map.
            rewrite Hfind_map // in Hfind_list.
          * by reflexivity.
    - (* D_invalidated *)
      simpl Sem_frag_stmts.
      intro.
      destruct H4 as [vm' [ct' [[H4 H7] H8]]].
      specialize (IHconn_map_list vm' ct' (CEP.Lemmas.P.of_list conn_map_list)
                                  H3 H6 (CEP.Lemmas.P.of_list_2 H6) H8).
      split ; first by apply (CEP.Lemmas.Equal_trans H4), IHconn_map_list.
      apply (CEP.Lemmas.Equal_trans (proj2 IHconn_map_list)).
      intro.
      unfold extend_map_with.
      rewrite CEP.Lemmas.map2_1bis // (*CEP.Lemmas.P.of_list_1b //. *)
              CEP.Lemmas.map2_1bis //.
      specialize (H k).
      destruct (CEP.find k tmap) as [[[gt| |] ori]|] ; try by contradiction.
      rewrite /size_of_ftype /mkseq in H7 ; simpl in H7.
      rewrite N.add_0_r -surjective_pairing in H7.
      destruct (y == k) eqn: Hyk.
      + move /eqP : Hyk => Hyk.
        rewrite Hyk.
        destruct (PVM.find k (CEP.Lemmas.P.of_list conn_map_list)) eqn: Hfind_list.
        - contradict H5.
          apply (SetoidList.InA_eqA Heqv_key (x := (k, d))) ;
                first by rewrite /CEP.eq_key /fst /CEP.SE.eq //.
          apply SetoidList.In_InA ; first by exact Heqv_key.
          rewrite CEP.Lemmas.P.of_list_1b // in Hfind_list.
          apply SetoidList.findA_NoDupA in Hfind_list ;
                last (by exact H6) ;
                last (by exact Heqv_key0).
          apply InA_In, Hfind_list.
        - (* use H2 to show that PVM.find k conn_map = D_invalidated *)
          rewrite (CEP.Lemmas.elements_o conn_map k).
          generalize (SetoidList.findA_NoDupA (B := def_expr) Heqv_key0) ; intro.
          specialize H9 with (eqA_dec := HiFP.PVSLemmas.P.FM.eq_dec) (l := CEP.elements conn_map) (a := k) (b := D_invalidated) (1 := CEP.elements_3w conn_map).
          rewrite (proj1 H9).
          * destruct ori ; try by contradiction H7.
            1,2: destruct H7 as [H7 _] ; specialize (H7 0) ; simpl in H7.
            1,2: by apply H7.
          * apply H2, SetoidList.InA_cons_hd.
            by done.
      + destruct ori ; try by contradiction H7.
        1,2: destruct H7 as [_ H7].
        1,2: specialize (H7 y).
        1,2: rewrite mem_seq1 Hyk in H7.
        1,2: rewrite -H7.
        1,2: destruct (PVM.find y (CEP.Lemmas.P.of_list conn_map_list)) eqn: Hfind_list.
        - 1,3: specialize (H2 (y, d)).
          1,2: rewrite CEP.Lemmas.P.of_list_1b in Hfind_list ; last by apply H6.
          1,2: apply SetoidList.findA_NoDupA in Hfind_list ;
                last (by apply H6) ; last by apply Heqv_key0.
          1,2: apply SetoidList.InA_cons_tl with (y := (k, D_invalidated)) in Hfind_list.
          1,2: apply H2, CEP.elements_2, CEP.find_1 in Hfind_list.
          1,2: rewrite Hfind_list //.
        - 1,2: destruct (PVM.find y conn_map) eqn: Hfind_map ;
                last by reflexivity.
          1,2: apply CEP.find_2, CEP.elements_1 in Hfind_map.
          1,2: apply H2, SetoidList.InA_cons in Hfind_map.
          1,2: destruct Hfind_map as [Hfind_map|Hfind_map] ;
                  first (by rewrite /PVM.eq_key_elt /PVM.Raw.Proofs.PX.eqke /fst Hyk in Hfind_map ;
                            destruct Hfind_map as [Hfind_map _] ; done).
          1,2: rewrite CEP.Lemmas.P.of_list_1b in Hfind_list ; last by exact H6.
          1,2: apply (SetoidList.findA_NoDupA Heqv_key0 ProdVarOrder.eq_dec y d H6) in Hfind_map.
          1,2: rewrite Hfind_map // in Hfind_list.
    - (* Expressions should not be very difficult... *)
      simpl Sem_frag_stmts.
      intro.
      destruct H4 as [vm' [ct' H4]].
      specialize (H0 k).
      assert (CEP.eq_key_elt (k, D_fexpr h) (k, D_fexpr h))
            by (split ; first (by rewrite /CEP.SE.eq //) ; last by reflexivity).
      apply (SetoidList.InA_cons_hd conn_map_list), H2, CEP.Lemmas.elements_mapsto_iff, CEP.find_1 in H7.
      rewrite H7 in H0 ; clear H7.
      destruct h.
      1-6: destruct H4 as [[H4 H7] H8].
      1-6: specialize (IHconn_map_list vm' ct' (CEP.Lemmas.P.of_list conn_map_list)
                                  H3 H6 (CEP.Lemmas.P.of_list_2 H6) H8).
      1-6: split ; first by apply (CEP.Lemmas.Equal_trans H4), IHconn_map_list.
      1-6: apply (CEP.Lemmas.Equal_trans (proj2 IHconn_map_list)).
      1-6: intro.
      1-6: unfold extend_map_with.
      1-6: rewrite CEP.Lemmas.map2_1bis // (*CEP.Lemmas.P.of_list_1b //. *)
              CEP.Lemmas.map2_1bis //.
      1-6: generalize (H k) ; intro.
      1-6: destruct (CEP.find k tmap) as [[[gt| |] ori]|] ; try by contradiction.
      1-6: rewrite /size_of_ftype /mkseq in H7 ; simpl in H7.
      1-6: rewrite N.add_0_r -surjective_pairing in H7.
      1-6: destruct (y == k) eqn: Hyk.
      + 1,3,5,7,9,11: move /eqP : Hyk => Hyk.
        1-6: rewrite Hyk.
        1-6: destruct (PVM.find k (CEP.Lemmas.P.of_list conn_map_list)) eqn: Hfind_list.
        - 1,3,5,7,9,11: contradict H5.
          1-6: apply (SetoidList.InA_eqA Heqv_key (x := (k, d))) ;
                first by rewrite /CEP.eq_key /fst /CEP.SE.eq //.
          1-6: apply SetoidList.In_InA ; first by exact Heqv_key.
          1-6: rewrite CEP.Lemmas.P.of_list_1b // in Hfind_list.
          1-6: apply SetoidList.findA_NoDupA in Hfind_list ;
                last (by exact H6) ;
                last (by exact Heqv_key0).
          1-6: apply InA_In, Hfind_list.
        - (* use H1 to show that PVM.find k conn_map = D_invalidated *)
          1-6: rewrite (CEP.Lemmas.elements_o conn_map k).
          1-6: generalize (SetoidList.findA_NoDupA (B := def_expr) Heqv_key0) ; intro.
          1-6: specialize H10 with (eqA_dec := HiFP.PVSLemmas.P.FM.eq_dec) (l := CEP.elements conn_map) (a := k) (1 := CEP.elements_3w conn_map).
          1: specialize (H10 (D_fexpr (Econst ProdVarOrder.T f b))).
          2: specialize (H10 (D_fexpr (Ecast u h))).
          3: specialize (H10 (D_fexpr (Eprim_unop e h))).
          4: specialize (H10 (D_fexpr (Eprim_binop e h1 h2))).
          5: specialize (H10 (D_fexpr (Emux h1 h2 h3))).
          6: specialize (H10 (D_fexpr (Evalidif h1 h2))).
          1-6: rewrite (proj1 H10) ; last by (apply H2, SetoidList.InA_cons_hd ; done).
          1-6: destruct ori ; try (by contradiction H7).
          1,2: by destruct f, gt ; try (by destruct H7 as [H7 _] ; done) ;
                  destruct H7 as [_ [H7 _]] ; specialize (H7 0) ; simpl in H7 ; apply H7.
          1,2: by destruct u, (type_of_expr h tmap) as [[[[| | | | | |]| |] _]|] ; try (by contradiction H7) ;
                  destruct gt ; try (by destruct H7 as [H7 _] ; done) ;
                  destruct H7 as [_ [H7 _]] ; specialize (H7 0) ; simpl in H7 ; apply H7.
          1,2: destruct e, (type_of_expr h tmap) as [[[[| | | | | |]| |] _]|] ; try done ;
               destruct gt ; try (by destruct H7 as [H7 _] ; done) ;
               try (destruct (n0 <= n < n1)) ;
               try (destruct (n <= n0)) ; try (by contradiction H7) ;
               by destruct H7 as [_ [H7 _]] ; specialize (H7 0) ; simpl in H7 ; apply H7.
          1,2: by destruct e, (type_of_expr h1 tmap) as [[[[| | | | | |]| |] _]|],
                              (type_of_expr h2 tmap) as [[[[| | | | | |]| |] _]|] ; try done ;
                  destruct gt ; try (by destruct H7 as [H7 _] ; done) ;
                  destruct H7 as [_ [H7 _]] ; specialize (H7 0) ; simpl in H7 ; apply H7.
          1,2: simpl in H0 ; move /andP : H0 => [_ H0] ;
               generalize (expr_preserves_fully_inferred tmap H h3 H0) ; intro.
          1,2: by destruct (type_of_expr h1 tmap) as [[[[[|[|]]| | | | | |]| |] _]|],
                           (type_of_expr h2 tmap) as [[[[| | | | | |]| |] p2]|],
                           (type_of_expr h3 tmap) as [[[[| | | | | |]| |] p3]|] ; try done ;
                  simpl in H7 ;
                  destruct gt ; try (by destruct H7 as [H7 _] ; done) ;
                  destruct H7 as [_ [H7 _]] ; specialize (H7 0) ; simpl in H7 ; apply H7.
          1,2: simpl in H0 ; move /andP : H0 => [_ H0] ;
               generalize (expr_preserves_fully_inferred tmap H h2 H0) ; intro.
          1,2: by destruct (type_of_expr h1 tmap) as [[[[[|[|]]| | | | | |]| |] _]|],
                           (type_of_expr h2 tmap) as [[[[| | | | | |]| |] _]|] ; try done ;
                  simpl in H7 ;
                  destruct gt ; try (by destruct H7 as [H7 _] ; done) ;
                  destruct H7 as [_ [H7 _]] ; specialize (H7 0) ; simpl in H7 ; apply H7.
      + 1-6: simpl in H0.
        1-6: destruct ori ; try (by contradiction H7).
        11,12: move /andP : H0 => [_ H0] ;
           generalize (expr_preserves_fully_inferred tmap H h2 H0) ; intro ;
           destruct (type_of_expr h1 tmap) as [[[[[|[|]]| | | | | |]| |] _]|],
                    (type_of_expr h2 tmap) as [[[[| | | | | |]| |] _]|] ; try done ;
           destruct gt ; try (by destruct H7 as [H7 _] ; done).
        9,10: move /andP : H0 => [_ H0] ;
           generalize (expr_preserves_fully_inferred tmap H h3 H0) ; intro ;
           destruct (type_of_expr h1 tmap) as [[[[[|[|]]| | | | | |]| |] _]|],
                    (type_of_expr h2 tmap) as [[[[| | | | | |]| |] p2]|],
                    (type_of_expr h3 tmap) as [[[[| | | | | |]| |] p3]|] ; try done ;
           simpl in H7 ; destruct gt ; try (by destruct H7 as [H7 _] ; done).
        7,8: destruct e, (type_of_expr h1 tmap) as [[[[| | | | | |]| |] _]|],
                         (type_of_expr h2 tmap) as [[[[| | | | | |]| |] _]|] ; try done ;
                destruct gt ; try (by destruct H7 as [H7 _] ; done).
        5,6: destruct e, (type_of_expr h tmap) as [[[[| | | | | |]| |] _]|] ; try done ;
           destruct gt ; try (by destruct H7 as [H7 _] ; done) ;
           try (destruct (n0 <= n < n1)) ;
           try (destruct (n <= n0)) ; try (by contradiction H7).
        3,4: destruct u, (type_of_expr h tmap) as [[[[| | | | | |]| |] _]|] ; try (by contradiction H7) ;
           destruct gt ; try (by destruct H7 as [H7 _] ; done).
        1,2: destruct f, gt ; try (by destruct H7 as [H7 _] ; done).
           1-364: destruct H7 as [_ [_ H7]].
           1-364: specialize (H7 y).
           1-364: rewrite mem_seq1 Hyk in H7.
           1-364: rewrite -H7.
           1-364: destruct (PVM.find y (CEP.Lemmas.P.of_list conn_map_list)) eqn: Hfind_list ;
                 try (by specialize (H2 (y, d)) ;
                         rewrite CEP.Lemmas.P.of_list_1b in Hfind_list ; last (by apply H6) ;
                         apply SetoidList.findA_NoDupA in Hfind_list ;
                               last (by apply H6) ; last (by apply Heqv_key0) ;
                         destruct H2 as [H2 _] ;
                         apply CEP.elements_2 in H2 ;
                               last (by apply SetoidList.InA_cons_tl, Hfind_list) ;
                         rewrite (CEP.find_1 H2) //).
           1-364: destruct (PVM.find y conn_map) eqn: Hfind_map ;
                 try (by reflexivity).
           1-364: apply CEP.find_2, CEP.elements_1 in Hfind_map.
           1-364: apply H2, SetoidList.InA_cons in Hfind_map.
           1-364: destruct Hfind_map as [Hfind_map|Hfind_map] ;
                  try (by rewrite /PVM.eq_key_elt /PVM.Raw.Proofs.PX.eqke /fst Hyk in Hfind_map ;
                          destruct Hfind_map as [Hfind_map _] ; done).
           1-364: rewrite CEP.Lemmas.P.of_list_1b in Hfind_list ; try (by exact H6).
           1-364: apply (SetoidList.findA_NoDupA Heqv_key0 ProdVarOrder.eq_dec y d H6) in Hfind_map.
           1-364: by rewrite Hfind_map // in Hfind_list.
      (* what remains is a link with a reference, which is translated to a different Sfcnct case. *)
      destruct H4 as [[H4 H7] H8].
      specialize (IHconn_map_list vm' ct' (CEP.Lemmas.P.of_list conn_map_list)
                                  H3 H6 (CEP.Lemmas.P.of_list_2 H6) H8).
      split ; first by apply (CEP.Lemmas.Equal_trans H4), IHconn_map_list.
      apply (CEP.Lemmas.Equal_trans (proj2 IHconn_map_list)).
      intro.
      unfold extend_map_with.
      rewrite CEP.Lemmas.map2_1bis // (*CEP.Lemmas.P.of_list_1b //. *)
              CEP.Lemmas.map2_1bis //.
      generalize (H k) ; intro.
      destruct (CEP.find k tmap) as [[[gt| |] [| | | |]]|] ; try by contradiction.
      1,2: generalize (list_lhs_ref_p_type tmap h) ; intro.
      1,2: destruct (list_lhs_ref_p h tmap) as [[[|ic [|]] [[gt_src| |] [| | | |]]]|] ; try (by contradiction H7) ;
            destruct H7 as [_ H7] ; simpl in H7 ; try (by destruct H7 as [H7 _] ; done).
      1-4: rewrite /size_of_ftype /mkseq in H7 ; simpl in H7.
      1-4: rewrite N.add_0_r -surjective_pairing in H7.
      1-4: destruct (y == k) eqn: Hyk.
      + 1,3,5,7: move /eqP : Hyk => Hyk ; rewrite Hyk.
        1-4: destruct (PVM.find k (CEP.Lemmas.P.of_list conn_map_list)) eqn: Hfind_list.
        - 1,3,5,7: contradict H5.
          1-4: apply (SetoidList.InA_eqA Heqv_key (x := (k, d))) ;
                first by rewrite /CEP.eq_key /fst /CEP.SE.eq //.
          1-4: apply SetoidList.In_InA ; first by exact Heqv_key.
          1-4: rewrite CEP.Lemmas.P.of_list_1b // in Hfind_list.
          1-4: apply SetoidList.findA_NoDupA in Hfind_list ;
                last (by exact H6) ;
                last (by exact Heqv_key0).
          1-4: by apply InA_In, Hfind_list.
        - (* use H2 to show that PVM.find k conn_map = D_invalidated *)
          1-4: rewrite (CEP.Lemmas.elements_o conn_map k).
          1-4: generalize (SetoidList.findA_NoDupA (B := def_expr) Heqv_key0) ; intro.
          1-4: specialize H11 with (eqA_dec := HiFP.PVSLemmas.P.FM.eq_dec) (l := CEP.elements conn_map) (a := k) (b := D_fexpr (Eref h)) (1 := CEP.elements_3w conn_map).
          1-4: rewrite (proj1 H11).
          * 1,3,5,7: destruct H7 as [H7 _] ; move /andP : H7 => [/andP [_ /eqP H7] _].
            1-4: by apply H7.
          * 1-4: apply H2, SetoidList.InA_cons_hd.
            1-4: by done.
      + 1-4: destruct (y == ic) eqn: Hyic.
        - 1,3,5,7: move /eqP : Hyic => Hyic ; rewrite Hyic.
          1-4: destruct H7 as [H7 _] ; move /andP : H7 => [_ /eqP H7] ; rewrite H7.
          1-4: destruct (PVM.find ic (CEP.Lemmas.P.of_list conn_map_list)) eqn: Hfind_list.
          * 1,3,5,7: specialize (H2 (ic, d)).
            1-4: rewrite CEP.Lemmas.P.of_list_1b in Hfind_list ; last by apply H6.
            1-4: apply SetoidList.findA_NoDupA in Hfind_list ;
                  last (by apply H6) ; last by apply Heqv_key0.
            1-4: apply SetoidList.InA_cons_tl with (y := (k, D_fexpr (Eref h))) in Hfind_list.
            1-4: apply H2, CEP.elements_2, CEP.find_1 in Hfind_list.
            1-4: by rewrite Hfind_list //.
          * 1-4: destruct (PVM.find ic conn_map) eqn: Hfind_map ;
                  last by reflexivity.
            1-4: apply CEP.find_2, CEP.elements_1 in Hfind_map.
            1-4: apply H2, SetoidList.InA_cons in Hfind_map.
            1-4: destruct Hfind_map as [Hfind_map|Hfind_map] ;
                    first (by rewrite /PVM.eq_key_elt /PVM.Raw.Proofs.PX.eqke /fst -Hyic Hyk in Hfind_map ;
                              destruct Hfind_map as [Hfind_map _] ; done).
            1-4: rewrite CEP.Lemmas.P.of_list_1b in Hfind_list ; last by exact H6.
            1-4: apply (SetoidList.findA_NoDupA Heqv_key0 ProdVarOrder.eq_dec ic d H6) in Hfind_map.
            1-4: by rewrite Hfind_map // in Hfind_list.
        - 1-4: destruct H7 as [_ H7].
          1-4: specialize (H7 y).
          1-4: rewrite mem_seq1 Hyk orFb mem_seq1 Hyic in H7.
          1-4: rewrite -H7.
          1-4: destruct (PVM.find y (CEP.Lemmas.P.of_list conn_map_list)) eqn: Hfind_list.
          * 1,3,5,7: specialize (H2 (y, d)).
            1-4: rewrite CEP.Lemmas.P.of_list_1b in Hfind_list ; last by apply H6.
            1-4: apply SetoidList.findA_NoDupA in Hfind_list ;
                  last (by apply H6) ; last by apply Heqv_key0.
            1-4: apply SetoidList.InA_cons_tl with (y := (k, D_fexpr (Eref h))) in Hfind_list.
            1-4: apply H2, CEP.elements_2, CEP.find_1 in Hfind_list.
            1-4: by rewrite Hfind_list //.
          * 1-4: destruct (PVM.find y conn_map) eqn: Hfind_map ;
                  last by reflexivity.
            1-4: apply CEP.find_2, CEP.elements_1 in Hfind_map.
            1-4: apply H2, SetoidList.InA_cons in Hfind_map.
            1-4: destruct Hfind_map as [Hfind_map|Hfind_map] ;
                    first (by rewrite /PVM.eq_key_elt /PVM.Raw.Proofs.PX.eqke /fst Hyk in Hfind_map ;
                              destruct Hfind_map as [Hfind_map _] ; done).
            1-4: rewrite CEP.Lemmas.P.of_list_1b in Hfind_list ; last by exact H6.
            1-4: apply (SetoidList.findA_NoDupA Heqv_key0 ProdVarOrder.eq_dec y d H6) in Hfind_map.
            1-4: by rewrite Hfind_map // in Hfind_list.
Qed.


Theorem ExpandBranches_Sem_ct :
(* This theorem relates the connection maps generated by Sem_frag_stmts and ExpandBranch_funs. *)
forall (ss old_def_ss : HiFP.hfstmt_seq) (vm_old vm_new vm_tmap : CEP.t vertex_type)
       (ct_old ct_new old_conn_map : CEP.t def_expr) (old_scope tmap : CEP.t (ftype * HiF.forient))
       (old_tmap_scope new_tmap_scope : CEP.t (ftype * HiF.forient) * CEP.t (ftype * HiF.forient)),
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
       (ct_old ct_new old_conn_map : CEP.t def_expr) (old_scope tmap : CEP.t (ftype * HiF.forient))
       (old_tmap_scope new_tmap_scope : CEP.t (ftype * HiF.forient) * CEP.t (ftype * HiF.forient)),
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
    specialize (H4 s (Gtyp gt, HiF.Duplex)).
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
                      match type_of_expr rst_val (CEP.add s (type h, HiF.Duplex) old_scope) with
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
    assert (CEP.add s (Gtyp gt, HiF.Duplex) old_tmap_scope.1 = new_tmap).
          destruct (reset h).
          2: destruct (type_of_expr h0 old_tmap_scope.2) as [[[[[|[]]| | | | | |]| |]]|] ; try by discriminate H3.
          2: destruct (type_of_expr h1 (CEP.add s (Gtyp gt, HiF.Duplex) old_tmap_scope.2)) ; last by discriminate H3.
          3: destruct (type_of_expr h1 old_tmap_scope.2) ; last by discriminate H3.
          1-3: injection H3 ; done.
    clear H3 ; rename H7 into H3.
    rewrite /fst -H3 in H4.
    specialize (H4 s (Gtyp gt, HiF.Duplex)).
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
    specialize (H7 (Gtyp gt, HiF.Source) H4 Logic.eq_refl).
    rewrite (H10 H7) in H5 ; clear p H10 H7.
    destruct H5 as [_ [_ H5]].
    apply CEP.Lemmas.Equal_trans with (m' := ct_old) ; last by exact H6.
    apply CEP.Lemmas.Equal_sym, H5.
  + (* Sfcnct *)
    unfold ExpandBranch_connect.
    destruct h ; try (by done).
    generalize (type_of_expr_submap h0 old_scope old_tmap_scope.2 H1) ; intro.
    specialize (H1 s).
    destruct (CEP.find s old_scope) as [[ft_ref [| | | |]]|] ; try by done.
    1,2: specialize (H1 _ Logic.eq_refl).
    1,2: destruct (type_of_expr h0 old_scope) as [[ft_expr p]|] ; last by done.
    1,2: destruct (connect_type_compatible false ft_ref ft_expr false) ; last by done.
    1,2: rewrite /type_of_ref H1 H7 in H3.
    1,2: injection H3 ; clear H3 ; intro ; subst new_tmap_scope.
    1,2: generalize (type_of_expr_submap h0 old_tmap_scope.2 old_tmap_scope.1 H2) ; intro.
    1,2: rewrite H7 in H3.
    1,2: generalize (type_of_expr_submap h0 old_tmap_scope.1 tmap H4) ; intro.
    1,2: rewrite H3 in H8.
    1,2: generalize (expr_preserves_fully_inferred old_tmap_scope.1 H0 h0 H) ; intro.
    1,2: rewrite H3 in H9.
    1,2: destruct ft_expr as [gt_expr| |] ; try by contradiction H9.
    1,2: specialize (H2 s) ; rewrite H1 in H2 ; specialize (H2 _ Logic.eq_refl).
    1,2: specialize (H0 s) ; rewrite H2 in H0.
    1,2: destruct ft_ref as [gt_ref| |] ; try by contradiction H0.
    1,2: specialize (H4 s) ; rewrite H2 in H4 ; specialize (H4 _ Logic.eq_refl).
    1,2: simpl list_lhs_ref_p in H5.
    1,2: rewrite /type_of_ref H4 H8 in H5.
    1,2: destruct h0.
    1-14: simpl list_rhs_expr_p in H5.
    (* h0 is a normal expression *)
    1-6,8-13: destruct H5 as [_ [H10 H5]].
    1-12: intro.
    1-12: destruct (y == s) eqn: Hys ;
            first (by rewrite CEP.Lemmas.find_add_eq ; last (by rewrite /PVM.SE.eq Hys //) ;
                      destruct H5 as [H5 _] ;
                      specialize (H5 0) ; simpl in H5 ;
                      rewrite N.add_0_r -surjective_pairing in H5 ;
                      move /eqP : Hys => Hys ;
                      rewrite Hys (proj2 H5) //).
    1-12: rewrite CEP.Lemmas.find_add_neq ; last (by rewrite /PVM.SE.eq Hys //).
    1-12: destruct H5 as [_ H5].
    1-12: specialize (H5 y).
    1-12: rewrite /mkseq in H5 ; simpl map in H5.
    1-12: rewrite N.add_0_r -surjective_pairing mem_seq1 Hys in H5.
    1-12: by rewrite -H5 //.
    (* h0 is a reference *)
    1,2: destruct H5 as [_ H5].
    1,2: simpl expr_has_fully_inferred_ground_types in H.
    1,2: simpl type_of_expr in H8.
    1,2: generalize (list_lhs_ref_p_type tmap h) ; intro.
    1,2: destruct (list_lhs_ref_p h tmap) as [[lst_src [ft_src [| | | |]]]|] ;
          try by contradiction H5.
    1-4: destruct (type_of_ref h tmap) as [[ft_ref' ori']|] ;
          last by discriminate H8.
    1-4: injection H10 ; clear H10 ; intros ; subst ft_ref' ori'.
    1-4: destruct ft_src as [gt_src| |] ;
          last (by injection H8 ;
                   destruct (make_ffield_explicit f) ;
                   intro ; inversion_sigma H10 ; discriminate H10_) ;
          last (by injection H8 ;
                   destruct (make_ftype_explicit ft_src) ;
                   intro ; inversion_sigma H10 ; discriminate H10_).
    1-4: destruct H5 as [H10 [H11 H5]].
    1-4: simpl in H11.
    1-4: destruct lst_src as [|oc lst_src'] ; first by done.
    1-4: destruct lst_src' ; last by done.
    1-4: intro.
    1-4: destruct (y == s) eqn: Hys.
    - 1,3,5,7: rewrite CEP.Lemmas.find_add_eq ; last by (rewrite /PVM.SE.eq Hys //).
      1-4: move /eqP : Hys => Hys.
      1-4: rewrite Hys.
      1-4: move /andP : H11 => [/andP [_ /eqP H11] _].
      1-4: by rewrite N.add_0_r -surjective_pairing // in H11.
    - 1-4: rewrite CEP.Lemmas.find_add_neq ; last (by rewrite /PVM.SE.eq Hys //).
      1-4: destruct (y == oc) eqn: Hyoc.
      * 1,3,5,7: move /eqP : Hyoc => Hyoc.
        1-4: move /andP : H11 => [_ /eqP H11].
        1-4: by rewrite Hyoc H11 //.
      * 1-4: specialize (H5 y).
        1-4: rewrite /mkseq in H5 ; simpl map in H5.
        1-4: rewrite N.add_0_r -surjective_pairing mem_seq1 Hys orFb mem_seq1 Hyoc in H5.
        1-4: rewrite -H5 //.
  + (* Sinvalid *)
    unfold ExpandBranch_connect.
    destruct h ; try (by done).
    specialize (H1 s).
    destruct (CEP.find s old_scope) as [[ft_ref [| | | |]]|] ; try by done.
    1,2: specialize (H1 _ Logic.eq_refl).
    1,2: rewrite /type_of_ref H1 in H3.
    1,2: injection H3 ; clear H3 ; intro ; subst new_tmap_scope.
    1,2: specialize (H2 s) ; rewrite H1 in H2 ; specialize (H2 _ Logic.eq_refl).
    1,2: specialize (H4 s) ; rewrite H2 in H4 ; specialize (H4 _ Logic.eq_refl).
    1,2: simpl list_lhs_ref_p in H5.
    1,2: rewrite H4 in H5.
    1,2: specialize (H0 s).
    1,2: rewrite H2 in H0.
    1,2: destruct ft_ref as [gt_ref| |] ; try by contradiction H0.
    1,2: destruct H5 as [_ H5].
    1,2: intro.
    1,2: destruct (y == s) eqn: Hys ;
            first (by rewrite CEP.Lemmas.find_add_eq ; last (by rewrite /PVM.SE.eq Hys //) ;
                      destruct H5 as [H5 _] ;
                      specialize (H5 0) ; simpl in H5 ;
                      rewrite N.add_0_r -surjective_pairing in H5 ;
                      move /eqP : Hys => Hys ;
                      rewrite Hys (proj2 H5) //).
    1,2: rewrite CEP.Lemmas.find_add_neq ; last (by rewrite /PVM.SE.eq Hys //).
    1,2: destruct H5 as [_ H5].
    1,2: specialize (H5 y).
    1,2: rewrite /mkseq in H5 ; simpl map in H5.
    1,2: rewrite N.add_0_r -surjective_pairing mem_seq1 Hys in H5.
    1,2: by rewrite -H5 //.
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
    move /andP : H => [/andP [_ Htrue] Hfalse].
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


Lemma Sem_frag_stmts_uncomponent :
(* This lemma is the core of the correctness theorem.
   It shows that the split in (component_stmts_of ss) and a connection map
   can be undone. *)
forall (ss : HiFP.hfstmt_seq)
       (vm_old : CEP.t vertex_type) (ct_old : CEP.t def_expr) (vm_new : CEP.t vertex_type) (ct_new : CEP.t def_expr) (tmap : CEP.t (ftype * HiF.forient))
       (old_def_ss : HiFP.hfstmt_seq)
       (old_scope : CEP.t (ftype * HiF.forient))
       (ss_conn_map : CEP.t def_expr) (new_scope : CEP.t (ftype * HiF.forient)),
    stmts_have_fully_inferred_ground_types ss ->
    tmap_has_fully_inferred_ground_types tmap ->
    ct_has_fully_inferred_ground_types ct_old ->
    vm_and_ct_compatible vm_old ct_old ->
    (* ct_old and old_scope fit together -> *)
    CEP.submap old_scope tmap ->
    ExpandBranch_funs ss old_def_ss ct_old old_scope =
        Some (Qcat old_def_ss (component_stmts_of ss), ss_conn_map, new_scope) ->
    Sem_frag_stmts vm_old ct_old (Qcat (component_stmts_of ss) (CEP.fold helper_connect ss_conn_map (Qnil ProdVarOrder.T))) vm_new ct_new tmap ->
        Sem_frag_stmts vm_old ct_old ss vm_new ct_new tmap
with Sem_frag_stmt_uncomponent :
forall (s : HiFP.hfstmt)
       (vm_old : CEP.t vertex_type) (ct_old : CEP.t def_expr) (vm_new : CEP.t vertex_type) (ct_new : CEP.t def_expr) (tmap : CEP.t (ftype * HiF.forient))
       (old_def_ss : HiFP.hfstmt_seq)
       (old_scope : CEP.t (ftype * HiF.forient))
       (s_conn_map : CEP.t def_expr) (new_scope : CEP.t (ftype * HiF.forient)),
    stmt_has_fully_inferred_ground_types s ->
    tmap_has_fully_inferred_ground_types tmap ->
    ct_has_fully_inferred_ground_types ct_old ->
    vm_and_ct_compatible vm_old ct_old ->
    (* ct_old and old_scope fit together -> *)
    CEP.submap old_scope tmap ->
    ExpandBranch_fun s old_def_ss ct_old old_scope =
        Some (Qcat old_def_ss (component_stmt_of s), s_conn_map, new_scope) ->
    Sem_frag_stmts vm_old ct_old (Qcat (component_stmt_of s) (CEP.fold helper_connect s_conn_map (Qnil ProdVarOrder.T))) vm_new ct_new tmap ->
        Sem_frag_stmt vm_old ct_old s vm_new ct_new tmap.
Proof.
* clear Sem_frag_stmts_uncomponent.
  induction ss ; simpl ; intros.
  + (* induction base *)
    injection H4 ; clear H4 ; intros _ H4 _.
    rewrite -H4 in H5 ; clear ss_conn_map H4.
    generalize (helper_connect_Sem ct_old vm_old ct_old vm_new ct_new tmap H0 H1 H5) ; intro.
    split ; first by apply H4.
    destruct H4 as [_ H4].
    intro ; rewrite H4 /extend_defined_map_with CEP.Lemmas.map2_1bis //.
    destruct (CEP.find y ct_old) as [[| |]|] ; by reflexivity.
  + (* induction step *)
    rename h into s.
    move /andP : H => H.
    (* We want the following commutative diagram:

           vm_old/ct_old ---------------------------.
                 |                                   \ by Sem_frag_stmt_uncomponent
                 |                                    \ it is possible to
                 | comp s                              \ change this to s.
                 |                                      \
                 v                   conn s              v
       vm_after_s/ct_after_comp_s -----------> vm_after_s/ct_after_s ---------------------.
                 |                                       |                                 \ by induction hypothesis
                 |                                       |                                  \ it is possible to
                 | comp ss                               | comp ss                           \ change this to ss.
                 |                                       |                                    \
                 v                      conn s           v                   conn ss           v
           vm_new/ct_after_comp_s_ss ------------> vm_new/ct_after_conn_s -------------> vm_new/ct_new

       In this diagram, we have the leftmost and the bottom path by the assumptions of the theorem.
       (Connection maps are the same as the resulting ct,
       so we can use the result of ExpandBranch_fun(s) as ct,
       see ExpandBranch_Sem_ct.
       Perhaps we will have to change that, so that helper_connect will only generate connect statements
       for things that actually have been connected in the code translated by ExpandBranch_funs.)
       Perhaps, we may have to construct ct_after_conn_s.
       To use the induction hypothesis, we also need to construct ct_after_conn_s; that is:
          extend_defined_map_with conn_map_s ct_after_comp_s_ss. *)
    specialize (Sem_frag_stmt_uncomponent s vm_old ct_old)
          with (old_def_ss := old_def_ss) (old_scope := old_scope) (tmap := tmap).
    specialize (ExpandBranch_component) with (scope := old_scope) (s := s) (def_ss := old_def_ss) (conn_map := ct_old) ; intro.
    destruct (ExpandBranch_fun s old_def_ss ct_old old_scope) as [[[def_ss_after_s ct_after_s] scope_after_s]|] eqn: Hexpand_s ;
          last by discriminate H4.
    specialize (H6 def_ss_after_s ct_after_s scope_after_s Logic.eq_refl).
    subst def_ss_after_s.
    specialize Sem_frag_stmt_uncomponent with (s_conn_map := ct_after_s) (new_scope := scope_after_s)
               (1 := proj1 H) (2 := H0) (3 := H1) (4 := H2).
    specialize (ExpandBranch_components) with (scope := scope_after_s) (ss := ss) (def_ss := Qcat old_def_ss (component_stmt_of s)) (conn_map := ct_after_s) ; intro.
    destruct (ExpandBranch_funs ss (Qcat old_def_ss (component_stmt_of s)) ct_after_s scope_after_s) as [[[new_def_ss ct_new'] new_scope']|] eqn: Hexpand_ss ;
          last by discriminate H4.
    specialize (H6 new_def_ss ct_new' new_scope' Logic.eq_refl).
    subst new_def_ss.
    injection H4 ; clear H4 ; intros H4 H6 _.
    subst new_scope' ss_conn_map.
    apply Sem_frag_stmts_cat in H5.
    destruct H5 as [vm_new' [ct_after_comp_s_ss [H5 H7]]].
    assert (tmap_has_fully_inferred_ground_types old_scope).
          intro.
          specialize (H3 v) ; specialize (H0 v).
          destruct (CEP.find v old_scope) ; last by trivial.
          by rewrite (H3 p) // in H0.
    generalize (ExpandBranch_fun_preserves_fully_inferred (Qcat old_def_ss (component_stmt_of s)) ct_after_s old_scope s old_def_ss ct_old scope_after_s
                H4 (proj1 H) H1 Hexpand_s) ; intro H8.
    generalize (ExpandBranch_funs_preserves_fully_inferred ss (Qcat old_def_ss (component_stmt_of s)) ct_after_s scope_after_s
                (Qcat old_def_ss (Qcat (component_stmt_of s) (component_stmts_of ss))) ct_new' new_scope
                (proj1 H8) (proj2 H) (proj2 H8)) ; intro H9.
    rewrite -Qcat_assoc in H9 ; specialize (H9 Hexpand_ss).
    generalize (helper_connect_Sem ct_new' vm_new' ct_after_comp_s_ss vm_new ct_new tmap
                H0 (proj2 H9) H7) ; intro H10.
    apply Sem_frag_stmts_cat in H5.
    destruct H5 as [vm_after_s [ct_after_comp_s [H5 H6]]].
    exists vm_after_s, ct_after_s.
    split.
    - apply Sem_frag_stmt_uncomponent ; try done.
      apply Sem_frag_stmts_cat.
      exists vm_after_s, ct_after_comp_s.
      split ; first by exact H5.
      (* Now we should see that (subdomain ct_after_comp_s ct_after_s)
      and (vm_and_ct_compatible vm_after_s ct_after_s),
      so the Sem_frag_stmts holds. *)
      admit.
    - apply IHss with (old_def_ss := (Qcat old_def_ss (component_stmt_of s))) (old_scope := scope_after_s) (ss_conn_map := ct_new') (new_scope := new_scope) ; try done.
      - by apply H.
      - admit. (* three goals that I think are not so difficult *)
      - admit.
      - admit.
      - apply Sem_frag_stmts_cat.
        exists vm_new, (extend_defined_map_with ct_new' ct_after_s).
        split.
        * specialize (Sem_frag_stmts_component_Equal ss vm_after_s vm_after_s ct_after_comp_s ct_after_s vm_new' vm_new ct_after_comp_s_ss tmap tmap)
                   with (3 := CEP.Lemmas.Equal_refl vm_after_s) (4 := proj1 H10) (5 := CEP.Lemmas.Equal_refl tmap) (6 := H6) ; intro.
          (* We can almost apply this theorem... *)
          admit.
        * (* now we need a kind of converse of helper_connect_Sem *)
          admit.
* clear Sem_frag_stmt_uncomponent.
  admit.
Admitted.

Lemma ExpandBranches_correct :
forall (vm_new : CEP.t vertex_type) (ct_new : CEP.t def_expr) (new_tmap_scope : CEP.t (ftype * HiF.forient) * CEP.t (ftype * HiF.forient))
       (ss : HiFP.hfstmt_seq) (vm_old : CEP.t vertex_type) (ct_old : CEP.t def_expr) (old_def_ss : HiFP.hfstmt_seq) (old_conn_map new_conn_map : CEP.t def_expr)
       (old_scope new_scope : CEP.t (ftype * HiF.forient)) (old_tmap_scope : CEP.t (ftype * HiF.forient) * CEP.t (ftype * HiF.forient)),
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
        Sem_frag_stmts vm_old ct_old (Qcat (component_stmts_of ss) (CEP.fold helper_connect new_conn_map (Qnil ProdVarOrder.T))) vm_new ct_new new_tmap_scope.1 ->
            Sem_frag_stmts vm_old ct_old ss vm_new ct_new new_tmap_scope.1.
Proof.
intros.
apply Sem_frag_stmts_cat in H6.
destruct H6 as [vm_temp [ct_temp [H6 H7]]].
generalize (Sem_frag_stmts_component ss vm_old ct_old vm_temp ct_temp new_tmap_scope.1 H0 H6) ; intro.
generalize (stmts_tmap_preserves_fully_inferred vm_new ss old_tmap_scope.1 old_tmap_scope.2 H2 H H3) ; intro.
rewrite -surjective_pairing H4 in H9.
destruct new_tmap_scope as [new_tmap_s new_t_scope].
generalize (helper_connect_Sem new_conn_map vm_temp ct_temp vm_new ct_new new_tmap_s H9) ; intro.
specialize H10 with (2 := H7).
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
Admitted.


(*
Lemma ExpandBranches_correct :
forall (vm : CEP.t vertex_type) (ct : CEP.t def_expr)
       (ss old_def_ss def_ss old_conn_ss new_conn_ss : HiFP.hfstmt_seq)
       (old_conn_map conn_map ct' : CEP.t def_expr) (old_scope temp_scope tmap : CEP.t (ftype * HiF.forient))
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
       (old_conn_map conn_map ct' : CEP.t def_expr) (old_scope temp_scope tmap : CEP.t (ftype * HiF.forient))
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
            Some (FInmod v pp (Qcat def_ss (CEP.fold helper_connect conn_map (Qnil ProdVarOrder.T))))
        | None => None
        end
    | None => None
    end
| FExmod _ _ _ => None
end.

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
injection H0 ; clear H0 ; intro.
rewrite -H0 in H1 ; clear H0 m'.
unfold Sem in H1 ; unfold Sem.
unfold ports_stmts_tmap in H1 ; unfold ports_stmts_tmap.
generalize (ports_tmap_preserves_fully_inferred vm pp Hpp) ;
      intro.
destruct (ports_tmap pp vm) as [pmap|] ; last by trivial.
generalize (stmts_tmap_components vm ss pmap pmap pmap (CEP.Lemmas.submap_refl pmap) (CEP.Lemmas.submap_refl pmap) (CEP.Lemmas.submap_refl pmap)) ;
      intro.
generalize (ExpandBranch_components ss (Qnil ProdVarOrder.T) port_conn_map port_scope
            def_ss conn_map scope Hexpand) ;
      intro ;
      unfold Qcat in H3.
rewrite stmts_tmap_cat H3 in H1 ; rewrite H3 in Hexpand ; clear def_ss H3.
generalize (ExpandBranch_funs_checks_scopes ss pmap pmap pmap vm
            Hss H0 (CEP.Lemmas.submap_refl pmap) (CEP.Lemmas.submap_refl pmap) (CEP.Lemmas.submap_refl pmap)) ;
      intro.
specialize H3 with (old_def_ss := (Qnil ProdVarOrder.T))
                   (old_conn_map := port_conn_map) (old_scope := port_scope)
                   (3 := CEP.Lemmas.Equal_submap (CEP.Lemmas.Equal_sym H)).
generalize (stmts_submap vm (component_stmts_of ss) pmap pmap
            (CEP.Lemmas.submap_refl pmap)) ;
      intro.
generalize (components_preserves_fully_inferred ss Hss) ;
      intro.
generalize (stmts_tmap_preserves_fully_inferred vm (component_stmts_of ss) pmap pmap H5 H0 (CEP.Lemmas.submap_refl pmap)) ;
      intro.
destruct (stmts_tmap (pmap, pmap) (component_stmts_of ss) vm) as [[tmap' scope2]|] ; last by contradiction H1.
destruct (stmts_tmap (pmap, pmap) ss vm) as [[tmap scope1]|] ;
      last by (rewrite Hexpand in H3 ; discriminate H3 ; try done ;
               intro ; specialize (H v0) ; rewrite H ;
               destruct (CEP.find v0 port_scope) ; done).
clear H3.
destruct H2 as [H2' H2] ; rewrite -H2' in H1 H4 H6 ; clear H2' tmap'.
generalize (stmts_tmap_components vm (CEP.fold helper_connect conn_map
                    (Qnil ProdVarOrder.T)) tmap scope2 scope2
            (proj1 H4) (proj1 H4) (CEP.Lemmas.submap_refl scope2)) ;
      intro.
destruct (stmts_tmap (tmap, scope2) (CEP.fold helper_connect conn_map
                    (Qnil ProdVarOrder.T)) vm) as [[tmap' scope2']|] ; last by contradiction H1.
generalize (fold_connect_components conn_map (Qnil ProdVarOrder.T)) ;
      intro.
simpl component_stmts_of in H7.
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
      destruct (CEP.find v pmap) as [[[gt| |] p]|] ;
            try (by done) ; rewrite -H //.
rename H4 into H4'.
assert (H4 : CEP.submap port_scope tmap).
      clear -H H4'.
      intro.
      specialize (H k) ; specialize (H4' k).
      destruct (CEP.find k port_scope) as [ft|] ; last by done.
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
Admitted.

(* Example to test connections *)

Definition test_ports0 := [:: HiFP.hinport  (1%num, N0) (Gtyp (Fuint 10)) ;
                              HiFP.houtport (2%num, N0) (Gtyp (Fuint 10))].
Definition test_stmts0 := Qcons (HiFP.snode (3%num, N0) (Eref (HiFP.eid (1%num, N0))))
                         (Qcons (Sfcnct (HiFP.eid (2%num, N0)) (HiFP.econst (Fuint 1) [:: true]))
                         (Qcons (Sfcnct (HiFP.eid (2%num, N0)) (Eref (HiFP.eid (3%num, N0))))
                                (Qnil _))).

Definition test_mod0 := FInmod (var := ProdVarOrder.T) (101%num, N0) test_ports0 test_stmts0.

Compute (ExpandWhens_fun test_mod0).

(* Example to test registers *)

Definition test_ports1 := [:: Finput  (var := ProdVarOrder.T) (8%num, N0) (Gtyp Fclock) ;
                              Finput  (var := ProdVarOrder.T) (9%num, N0) (Gtyp (Fsint 10))].
Definition test_stmts1 := Qcons (HiFP.sreg (10%num, N0) (mk_freg (Gtyp (Fuint 2)) (Eref (HiFP.eid (8%num, N0)))
                                                                 (Rst (Eref (HiFP.eid (9%num, N0)))
                                                                      (Eref (HiFP.eid (10%num, N0))))))
                                (Qnil _).
Definition test_mod1 := HiFP.hfinmod (101%num, N0) test_ports1 test_stmts1.

Compute (ExpandWhens_fun test_mod1).











