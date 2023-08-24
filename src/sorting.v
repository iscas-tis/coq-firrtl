From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.

Parameter node : eqType.

Inductive result_type : Type :=
   | OK : seq node -> result_type
   | Cycle : seq node -> result_type
   | N_too_small : result_type
   .

Fixpoint topo_tree (g : node -> seq node) (n : nat) (gray_nodes : seq node)
                   (maybe_already_found: result_type) (root : node) : result_type :=
match maybe_already_found, n with
| Cycle _, _ | N_too_small, _ => maybe_already_found (* propagate earlier error *)
| _, 0 => N_too_small (* error: n was too small *)
| OK already_found, S n' =>
if root \in gray_nodes then Cycle (root :: gray_nodes) (* error: there is a cycle *)
else if root \in already_found then maybe_already_found
else match foldl (topo_tree g n' (root :: gray_nodes)) maybe_already_found (g root) with
     | OK result => OK (root :: result)
     | e => e (* propagate error *)
     end
end.

Fixpoint subset (s1 s2 : seq node) : bool :=
match s1 with
| [::] => true
| a :: tail1 => (a \in s2) && subset tail1 s2
end.

Lemma in_cat : forall (T : eqType) (a : T) (s t : seq T), (a \in s ++ t) = (a \in s) || (a \in t).
Proof.
induction s.
* intro.
  rewrite cat0s in_nil.
  reflexivity.
* intro.
  rewrite cat_cons.
  destruct (a == a0) eqn: Ha.
  + rewrite in_cons in_cons Ha.
    reflexivity.
  + rewrite in_cons in_cons Ha.
    unfold orb.
    apply IHs.
Qed.

Lemma subset_cat : forall (s t : seq node), subset s (t ++ s) = true.
Proof.
induction s.
* unfold subset ; reflexivity.
* intro.
  unfold subset.
  rewrite in_cat in_cons eq_refl orbT.
  unfold andb at 1.
  fold subset.
  rewrite <- cat1s, catA.
  apply IHs.
Qed.

Lemma subset_refl : forall (s : seq node), subset s s = true.
Proof.
intro.
rewrite <- cat0s at 2.
apply subset_cat.
Qed.

Lemma subset_notin : forall (x : node) (s t : seq node),
   x \notin s -> subset s (x :: t) = subset s t.
Proof.
induction s.
* intros.
  unfold subset.
  reflexivity.
* rewrite in_cons negb_or.
  intros.
  move /andP : H => H.
  destruct H.
  unfold subset ; fold subset.
  rewrite in_cons.
  replace (a == x) with false.
  unfold orb.
  rewrite IHs.
  reflexivity.
  exact H0.
  symmetry.
  apply negbTE.
  rewrite eq_sym ; exact H.
Qed.

Lemma in_subset_trans : forall (x : node) (s t : seq node),
   x \in s -> subset s t -> x \in t.
Proof.
intro.
induction s.
* rewrite in_nil.
  done.
* rewrite in_cons.
  unfold subset ; fold subset.
  intros.
  move /orP : H => H.
  move /andP : H0 => H0.
  destruct H.
  + move /eqP : H => H ; rewrite H ; apply H0.
  + apply IHs.
    apply H.
    apply H0.
Qed.

Lemma subset_trans : forall (s t u : seq node),
   subset s t -> subset t u -> subset s u.
Proof.
induction s.
* unfold subset ; done.
* intros.
  unfold subset in H ; fold subset in H.
  move /andP : H => H.
  unfold subset ; fold subset.
  apply rwP with (P := a \in u /\ subset s u) ; try apply andP.
  split.
  + apply in_subset_trans with (s := t).
    - apply H.
    - exact H0.
  + apply IHs with (t := t).
    - apply H.
    - exact H0.
Qed.

Lemma take_subset : forall (i : nat) (s t : seq node),
   subset s t -> subset (take i s) t.
Proof.
induction i, s;
      try (intros ;
           unfold take, subset ;
           done).
intro.
replace (take i.+1 (s :: s0)) with (s :: take i s0).
unfold subset.
fold subset.
intro.
move /andP : H => H.
apply rwP with (P := (s \in t) /\ subset (take i s0) t).
exact andP.
split. 
apply H.
apply IHi.
apply H.
reflexivity.
Qed.

Fixpoint reverse_path_to (g : node -> seq node) (r : node) (p : seq node) : bool :=
match p with
| [::] => true
| a :: tail => (r \in g a) && ~~(a \in tail) && reverse_path_to g a tail
end.

Fixpoint respects_topological_order (g : node -> seq node) (v : seq node) : bool :=
match v with
| [::] => true
| a :: tail => subset (g a) tail && respects_topological_order g tail
end.

Lemma node_notin_path :
  forall (t : node) (p : seq node) (g : node -> seq node), reverse_path_to g t p -> t \notin p.
Proof.
  unfold reverse_path_to.
  destruct p.
  simpl.
  trivial.
  intro.
Admitted.


Theorem topo_tree_correct :
   forall (vertices : seq node) (g : node -> seq node) (n : nat) (gray_nodes already_found : seq node) (root : node),
      (* g is closed under vertices *)
      (forall x : node, x \in vertices -> subset (g x) vertices) ->
      n + size gray_nodes = size vertices ->
      subset gray_nodes vertices ->
      reverse_path_to g root gray_nodes ->
      (* g does not contain cycles *)
      (forall v' : seq node, subset v' vertices -> v' <> [::] ->
          exists v0 : node, v0 \in v' /\ forall v1 : node, v1 \in v' -> ~(v0 \in g v1)) ->
      respects_topological_order g already_found ->
      root \in vertices ->
         if topo_tree g n gray_nodes (OK already_found) root is OK result
         then subset already_found result /\ (root \in result) /\ respects_topological_order g result
         else False
with foldl_topo_tree_correct :
   forall (vertices : seq node) (g : node -> seq node) (adjacents : seq node) (n : nat) (gray_nodes already_found : seq node) (root : node),
      (* g is closed under vertices *)
      (forall x : node, x \in vertices -> subset (g x) vertices) ->
      subset adjacents (g root) ->
      S n + size gray_nodes = size vertices ->
      subset gray_nodes vertices ->
      reverse_path_to g root gray_nodes ->
      (* g does not contain cycles *)
      (forall v' : seq node, subset v' vertices -> v' <> [::] ->
          exists v0 : node, v0 \in v' /\ forall v1 : node, v1 \in v' -> ~(v0 \in g v1)) ->
      respects_topological_order g already_found ->
      root \in vertices ->
         if foldl (topo_tree g n (root :: gray_nodes)) (OK already_found) adjacents is OK result
         then subset already_found result /\ subset adjacents result /\ respects_topological_order g result
         else False.
Proof.
clear topo_tree_correct.
destruct n.
* intros. (* n = 0 *)
  unfold topo_tree.
  rewrite add0n in H0.
  (* Now we have that gray_nodes contains every vertex exactly once,
     so in particular root \in gray_nodes, so there is a cycle in the graph.
     We will handle this later.
     Perhaps first prove uniq gray_nodes from H2;
     then prove subset vertices gray_nodes from H0 and H1;
     then we have root \in gray_nodes from in_subset_trans.
     (Alternatively, if root \notin gray_nodes,
      then there must be another repeated node in gray_nodes.)
     Then we can use the cycle argument to get a contradiction with H3. *)
  admit.
* intros.
  specialize foldl_topo_tree_correct with (vertices := vertices) (g := g) (adjacents := g root) (n := n) (gray_nodes := gray_nodes) (already_found := already_found) (root := root).
  unfold topo_tree ; fold topo_tree.
  destruct (root \in gray_nodes) eqn: Hcycle.
  + (* root \in gray_nodes: there is a cycle, which contradicts H3. *)
    specialize H3 with (v' := root :: take (index root gray_nodes) gray_nodes).
    destruct H3.
    - unfold subset.
      fold subset. (* 拆开:: *)
      apply rwP with (P := (root \in vertices) /\ subset (take (index root gray_nodes) gray_nodes) vertices).
      try exact andP.
      split.
      apply H5.
      apply take_subset.
      exact H1.
    - discriminate.
    - (* x should *not* have a predecessor in root :: take (...) gray_nodes,
         but at the same time we should be able to prove from H3 that x has a predecessor in root :: take (...) gray_nodes. *)
      admit.
  + destruct (root \in already_found) eqn: Hfound.
    - (* root \in already_found *)
      rewrite Hfound.
      rewrite subset_refl.
      split ; try trivial.
      split ; trivial.
    - destruct (foldl (topo_tree g n (root :: gray_nodes)) (OK already_found) (g root)) eqn: Hfoldl.
(* not sure whether the following is correct. *)
      * rewrite in_cons.
        rewrite eq_refl.
        unfold orb.
        unfold respects_topological_order.
        fold respects_topological_order.
        rewrite subset_notin.
        split.
        apply foldl_topo_tree_correct.
        apply H.
        rewrite subset_refl; trivial.
        apply H0.
        apply H1.
        apply H2.
        apply H3.
        apply H4.
        apply H5.
        split; trivial.
        apply rwP with (P := subset (g root) l /\ respects_topological_order g l).
        try apply andP.
        apply foldl_topo_tree_correct.
        apply H.
        rewrite subset_refl; trivial.
        apply H0.
        apply H1.
        apply H2.
        apply H3.
        apply H4.
        apply H5.
        apply negbT.
        apply Hfound.
      * apply foldl_topo_tree_correct; try trivial.
        apply subset_refl.
        apply foldl_topo_tree_correct; try trivial.
        apply subset_refl.

intro ; intro.
induction adjacents.
* intros.
  unfold foldl.
  rewrite subset_refl.
  unfold subset.
  split ; try trivial.
  split ; trivial.
* intros.

  replace (foldl (topo_tree g n (root :: gray_nodes)) (OK already_found) (a :: adjacents))
  with (foldl (topo_tree g n (root :: gray_nodes)) (topo_tree g n (root :: gray_nodes) (OK already_found) a) adjacents)
  by reflexivity.
  destruct (topo_tree g n (root :: gray_nodes) (OK already_found) a) eqn: Htopo_tree. 
  (* 3 cases of topo_tree return type *)
  + unfold subset ; fold subset.
    specialize IHadjacents with (n := n) (gray_nodes := gray_nodes) (already_found := l) (root := root).
    destruct (foldl (topo_tree g n (root :: gray_nodes)) (OK l) adjacents) eqn: Hfoldl.
    (* enough (subset l l0 /\ subset adjacents l0 /\ respects_topological_order g l0).*)
    - split.
      * apply subset_trans with (t := l).
        + specialize topo_tree_correct with (vertices := vertices) (g := g) (n := n) (gray_nodes := root :: gray_nodes) (already_found := already_found) (root := a).
          rewrite Htopo_tree in topo_tree_correct.
          apply topo_tree_correct ; try trivial.
          unfold size; fold (@size node).
          rewrite <- addSnnS.
          apply H1.
          unfold subset ; fold subset.
          apply rwP with (P := root \in vertices /\ subset gray_nodes vertices).
          apply andP.
          split ; trivial.
          unfold reverse_path_to ; fold reverse_path_to.
          apply rwP with (P := (a \in g root) && (root \notin gray_nodes) /\ reverse_path_to g root gray_nodes) ; try apply andP.
          split.
          apply rwP with (P := a \in g root /\ root \notin gray_nodes) ; try apply andP.
          split.
          unfold subset in H0 ; fold subset in H0.
          move /andP : H0 => H0.
          apply H0.
          apply node_notin_path with (g := g).
          (* root \notin gray_nodes: should be the proof about cycles. *) 
          apply H3.
          apply H3.
          apply in_subset_trans with (s := g root).
          - unfold subset in H0.
            fold subset in H0.
            move /andP : H0 => H0.
            apply H0.
          - apply H. 
            apply H6.
    apply IHadjacents; try trivial.
    unfold subset in H0.
    fold subset in H0. 
    move /andP : H0 => H0.
    apply H0.

    specialize topo_tree_correct with (vertices := vertices) (g := g) (n := n) (gray_nodes := root :: gray_nodes) (already_found := already_found) (root := a).
    rewrite Htopo_tree in topo_tree_correct.
    apply topo_tree_correct; try trivial.
    unfold size ; fold (@size node).
    rewrite <- addSnnS ; exact H1.
    unfold subset ; fold subset.
    apply rwP with (P := root \in vertices /\ subset gray_nodes vertices) ; try apply andP.
    split.
    apply H6. 
    apply H2.
    unfold reverse_path_to ; fold reverse_path_to.
    apply rwP with (P := (a \in g root) && (root \notin gray_nodes) /\ reverse_path_to g root gray_nodes) ; try apply andP.
    split.
    apply rwP with (P := a \in g root /\ root \notin gray_nodes) ; try apply andP.
    split.

    unfold subset in H0 ; fold subset in H0.
    move /andP : H0 => H0.
    apply H0.
    (* root \notin gray_nodes: should be the proof about cycles. *) admit.
    apply H3.
    apply in_subset_trans with (s := g root).
    unfold subset in H0 ; fold subset in H0 ; move /andP : H0 => H0 ; apply H0.
    apply H.
    apply H6.
    split.
    apply rwP with (P := (a \in l0) /\ subset adjacents l0) ; try apply andP.
    split.
    apply in_subset_trans with (s := g root).
    unfold subset in H0 ; fold subset in H0 ; move /andP : H0 => H0 ; apply H0.
    apply subset_trans with (t := l).
    admit.
    apply IHadjacents; try trivial.
    unfold subset in H0 ; fold subset in H0.
    move /andP : H0 => H0.
    apply H0.
    specialize topo_tree_correct with (vertices := vertices) (g := g) (n := n) (gray_nodes := root :: gray_nodes) (already_found := already_found) (root := a).
    rewrite Htopo_tree in topo_tree_correct.
    apply topo_tree_correct; try trivial.
    unfold size ; fold (@size node).
    rewrite <- addSnnS ; exact H1.
    unfold subset ; fold subset.
    apply rwP with (P := root \in vertices /\ subset gray_nodes vertices) ; try apply andP.
    split.
    apply H6. 
    apply H2.
    unfold reverse_path_to ; fold reverse_path_to.
    apply rwP with (P := (a \in g root) && (root \notin gray_nodes) /\ reverse_path_to g root gray_nodes) ; try apply andP.
    split.
    apply rwP with (P := a \in g root /\ root \notin gray_nodes) ; try apply andP.
    split.
    unfold subset in H0 ; fold subset in H0 ; move /andP : H0 => H0 ; apply H0.
    (* root \notin gray_nodes: should be the proof about cycles. *) admit.
    apply H3.
    apply in_subset_trans with (s := g root).
    unfold subset in H0 ; fold subset in H0 ; move /andP : H0 => H0 ; apply H0.
    apply H.
    apply H6.
    apply IHadjacents; try trivial.
    unfold subset in H0 ; fold subset in H0 ; move /andP : H0 => H0 ; apply H0.
    
    specialize topo_tree_correct with (vertices := vertices) (g := g) (n := n) (gray_nodes := root :: gray_nodes) (already_found := already_found) (root := a).
    rewrite Htopo_tree in topo_tree_correct.
    apply topo_tree_correct; try trivial.
    unfold size ; fold (@size node).
    rewrite <- addSnnS ; exact H1.
    unfold subset ; fold subset.
    apply rwP with (P := root \in vertices /\ subset gray_nodes vertices) ; try apply andP.
    split.
    apply H6. 
    apply H2.
    unfold reverse_path_to ; fold reverse_path_to.
    apply rwP with (P := (a \in g root) && (root \notin gray_nodes) /\ reverse_path_to g root gray_nodes) ; try apply andP.
    split.
    apply rwP with (P := a \in g root /\ root \notin gray_nodes) ; try apply andP.
    split.
    unfold subset in H0 ; fold subset in H0 ; move /andP : H0 => H0 ; apply H0.
    (* root \notin gray_nodes: should be the proof about cycles. *) admit.
    apply H3.
    apply in_subset_trans with (s := g root).
    unfold subset in H0 ; fold subset in H0 ; move /andP : H0 => H0 ; apply H0.
    apply H.
    apply H6.

    specialize foldl_topo_tree_correct with (vertices := vertices) (g := g) (adjacents := adjacents) (n := n) (gray_nodes := gray_nodes) (already_found := l) (root := root).
    rewrite Hfoldl in foldl_topo_tree_correct.
    apply foldl_topo_tree_correct.
    apply H.
    unfold subset in H0 ; fold subset in H0 ; move /andP : H0 => H0 ; apply H0.
    apply H1.
    apply H2.
    apply H3.
    apply H4.

    specialize topo_tree_correct with (vertices := vertices) (g := g) (n := n) (gray_nodes := root :: gray_nodes) (already_found := already_found) (root := a).
    rewrite Htopo_tree in topo_tree_correct.
    apply topo_tree_correct; try trivial.
    unfold size ; fold (@size node).
    rewrite <- addSnnS ; exact H1.
    unfold subset ; fold subset.
    apply rwP with (P := root \in vertices /\ subset gray_nodes vertices) ; try apply andP.
    split.
    apply H6. 
    apply H2.
    unfold reverse_path_to ; fold reverse_path_to.
    apply rwP with (P := (a \in g root) && (root \notin gray_nodes) /\ reverse_path_to g root gray_nodes) ; try apply andP.
    split.
    apply rwP with (P := a \in g root /\ root \notin gray_nodes) ; try apply andP.
    split.
    unfold subset in H0 ; fold subset in H0 ; move /andP : H0 => H0 ; apply H0.
    (* root \notin gray_nodes: should be the proof about cycles. *) admit.
    apply H3.
    apply in_subset_trans with (s := g root).
    unfold subset in H0 ; fold subset in H0 ; move /andP : H0 => H0 ; apply H0.
    apply H.
    apply H6.
    apply H6.
    
    * apply IHadjacents; try trivial.
    unfold subset in H0 ; fold subset in H0 ; move /andP : H0 => H0 ; apply H0.
    specialize topo_tree_correct with (vertices := vertices) (g := g) (n := n) (gray_nodes := root :: gray_nodes) (already_found := already_found) (root := a).
    rewrite Htopo_tree in topo_tree_correct.
    apply topo_tree_correct; try trivial.
    unfold size ; fold (@size node).
    rewrite <- addSnnS ; exact H1.
    unfold subset ; fold subset.
    apply rwP with (P := root \in vertices /\ subset gray_nodes vertices) ; try apply andP.
    split.
    apply H6. 
    apply H2.
    unfold reverse_path_to ; fold reverse_path_to.
    apply rwP with (P := (a \in g root) && (root \notin gray_nodes) /\ reverse_path_to g root gray_nodes) ; try apply andP.
    split.
    apply rwP with (P := a \in g root /\ root \notin gray_nodes) ; try apply andP.
    split.
    unfold subset in H0 ; fold subset in H0 ; move /andP : H0 => H0 ; apply H0.
    (* root \notin gray_nodes: should be the proof about cycles. *) admit.
    apply H3.
    apply in_subset_trans with (s := g root).
    unfold subset in H0 ; fold subset in H0 ; move /andP : H0 => H0 ; apply H0.
    apply H.
    apply H6.

    * apply IHadjacents; try trivial.
    unfold subset in H0 ; fold subset in H0 ; move /andP : H0 => H0 ; apply H0.
    specialize topo_tree_correct with (vertices := vertices) (g := g) (n := n) (gray_nodes := root :: gray_nodes) (already_found := already_found) (root := a).
    rewrite Htopo_tree in topo_tree_correct.
    apply topo_tree_correct; try trivial.
    unfold size ; fold (@size node).
    rewrite <- addSnnS ; exact H1.
    unfold subset ; fold subset.
    apply rwP with (P := root \in vertices /\ subset gray_nodes vertices) ; try apply andP.
    split.
    apply H6. 
    apply H2.
    unfold reverse_path_to ; fold reverse_path_to.
    apply rwP with (P := (a \in g root) && (root \notin gray_nodes) /\ reverse_path_to g root gray_nodes) ; try apply andP.
    split.
    apply rwP with (P := a \in g root /\ root \notin gray_nodes) ; try apply andP.
    split.
    unfold subset in H0 ; fold subset in H0 ; move /andP : H0 => H0 ; apply H0.
    (* root \notin gray_nodes: should be the proof about cycles. *) admit.
    apply H3.
    apply in_subset_trans with (s := g root).
    unfold subset in H0 ; fold subset in H0 ; move /andP : H0 => H0 ; apply H0.
    apply H.
    apply H6.

    (* cycle *)
  + specialize topo_tree_correct with (vertices := vertices) (g := g) (n := n) (gray_nodes := root :: gray_nodes) (already_found := already_found) (root := a).
    rewrite Htopo_tree in topo_tree_correct.
    induction adjacents as [| root' adjacents'].
    unfold foldl.
    apply topo_tree_correct; try trivial.
    unfold size ; fold (@size node).
    rewrite <- addSnnS ; exact H1.
    unfold subset ; fold subset.
    apply rwP with (P := root \in vertices /\ subset gray_nodes vertices) ; try apply andP.
    split.
    apply H6. 
    apply H2.
    unfold reverse_path_to ; fold reverse_path_to.
    apply rwP with (P := (a \in g root) && (root \notin gray_nodes) /\ reverse_path_to g root gray_nodes) ; try apply andP.
    split.
    apply rwP with (P := a \in g root /\ root \notin gray_nodes) ; try apply andP.
    split.
    unfold subset in H0 ; fold subset in H0 ; move /andP : H0 => H0 ; apply H0.
    (* root \notin gray_nodes: should be the proof about cycles. *) admit.
    apply H3.
    apply in_subset_trans with (s := g root).
    unfold subset in H0 ; fold subset in H0 ; move /andP : H0 => H0 ; apply H0.
    apply H.
    apply H6.

    replace (foldl (topo_tree g n (root :: gray_nodes)) (Cycle l) (root' :: adjacents')) 
    with (foldl (topo_tree g n (root :: gray_nodes)) (topo_tree g n (root :: gray_nodes) (Cycle l) root') adjacents') by reflexivity.
    unfold topo_tree.
    exfalso.
    apply topo_tree_correct; try trivial.
    unfold size ; fold (@size node).
    rewrite <- addSnnS ; exact H1.
    unfold subset ; fold subset.
    apply rwP with (P := root \in vertices /\ subset gray_nodes vertices) ; try apply andP.
    split.
    apply H6. 
    apply H2.
    unfold reverse_path_to ; fold reverse_path_to.
    apply rwP with (P := (a \in g root) && (root \notin gray_nodes) /\ reverse_path_to g root gray_nodes) ; try apply andP.
    split.
    apply rwP with (P := a \in g root /\ root \notin gray_nodes) ; try apply andP.
    split.
    unfold subset in H0 ; fold subset in H0 ; move /andP : H0 => H0 ; apply H0.
    (* root \notin gray_nodes: should be the proof about cycles. *) admit.
    apply H3.
    apply in_subset_trans with (s := g root).
    unfold subset in H0 ; fold subset in H0 ; move /andP : H0 => H0 ; apply H0.
    apply H.
    apply H6.

    (* Ntoosmall *)
    + specialize topo_tree_correct with (vertices := vertices) (g := g) (n := n) (gray_nodes := root :: gray_nodes) (already_found := already_found) (root := a).
    rewrite Htopo_tree in topo_tree_correct.
    induction adjacents as [| root' adjacents'].
    unfold foldl.
    apply topo_tree_correct; try trivial.
    unfold size ; fold (@size node).
    rewrite <- addSnnS ; exact H1.
    unfold subset ; fold subset.
    apply rwP with (P := root \in vertices /\ subset gray_nodes vertices) ; try apply andP.
    split.
    apply H6. 
    apply H2.
    unfold reverse_path_to ; fold reverse_path_to.
    apply rwP with (P := (a \in g root) && (root \notin gray_nodes) /\ reverse_path_to g root gray_nodes) ; try apply andP.
    split.
    apply rwP with (P := a \in g root /\ root \notin gray_nodes) ; try apply andP.
    split.
    unfold subset in H0 ; fold subset in H0 ; move /andP : H0 => H0 ; apply H0.
    (* root \notin gray_nodes: should be the proof about cycles. *) admit.
    apply H3.
    apply in_subset_trans with (s := g root).
    unfold subset in H0 ; fold subset in H0 ; move /andP : H0 => H0 ; apply H0.
    apply H.
    apply H6.

    replace (foldl (topo_tree g n (root :: gray_nodes)) N_too_small (root' :: adjacents')) 
    with (foldl (topo_tree g n (root :: gray_nodes)) (topo_tree g n (root :: gray_nodes) N_too_small root') adjacents') by reflexivity.
    unfold topo_tree.
    exfalso.
    apply topo_tree_correct; try trivial.
    unfold size ; fold (@size node).
    rewrite <- addSnnS ; exact H1.
    unfold subset ; fold subset.
    apply rwP with (P := root \in vertices /\ subset gray_nodes vertices) ; try apply andP.
    split.
    apply H6. 
    apply H2.
    unfold reverse_path_to ; fold reverse_path_to.
    apply rwP with (P := (a \in g root) && (root \notin gray_nodes) /\ reverse_path_to g root gray_nodes) ; try apply andP.
    split.
    apply rwP with (P := a \in g root /\ root \notin gray_nodes) ; try apply andP.
    split.
    unfold subset in H0 ; fold subset in H0 ; move /andP : H0 => H0 ; apply H0.
    (* root \notin gray_nodes: should be the proof about cycles. *) admit.
    apply H3.
    apply in_subset_trans with (s := g root).
    unfold subset in H0 ; fold subset in H0 ; move /andP : H0 => H0 ; apply H0.
    apply H.
    apply H6.

Admitted.



From mathcomp Require Import ssreflect ssrbool eqtype seq.

Parameter node : eqType.

Fixpoint topo_tree (g : node -> seq node) (n : nat) (gray_nodes : seq node) (maybe_already_found: option (seq node)) (root : node) : option (seq node) :=
match maybe_already_found, n with
| None, _ => maybe_already_found (* propagate earlier error *)
| _, 0 => None (* error: n was too small *)
| Some already_found, S n' =>
if root \in gray_nodes then None (* error: there is a cycle *)
else if root \in already_found then maybe_already_found
else match foldl (topo_tree g n' (root :: gray_nodes)) maybe_already_found (g root) with
     | Some result => Some (root :: result)
     | None => None (* propagate error *)
     end
end.

Definition topo_sort (g : node -> seq node) (vertices : seq node) : option (seq node) :=
foldl (topo_tree g (size vertices) [::]) (Some [::]) vertices.

Parameters a b c : node.

Hypothesis aEbF : (a == b) = false.
Hypothesis aEcF : (a == c) = false.
Hypothesis bEcF : (b == c) = false.

(*Definition g (n : node) : seq node :=
  if n == a then [:: c]
  else if n == b then [:: c]
  else [::].

Eval compute in (topo_sort g [:: a;b]).*)

Definition g (n : node) : seq node :=
if n == a then [:: b; c]
else if n == c then [:: b]
else [::].
Eval compute in (topo_sort g [:: a;b;c]).

Lemma test_a : topo_tree g 3 [::] (Some [::]) a = Some [:: a; c; b].
Proof.
unfold topo_tree.
rewrite in_nil.
replace (g a) with [:: b; c] by (unfold g ; rewrite eq_refl ; reflexivity).
unfold foldl.
replace (b \in [:: a]) with false by (rewrite in_cons in_nil orbF eq_sym aEbF ; reflexivity).
replace (c \in [:: a]) with false by (rewrite in_cons in_nil orbF eq_sym aEcF ; reflexivity).
rewrite in_nil.
replace (g c) with [:: b] by (unfold g ; rewrite eq_refl eq_sym aEcF ; reflexivity).
replace (g b) with (@Nil node) by (unfold g ; rewrite bEcF eq_sym aEbF ; reflexivity).
replace (c \in [:: b]) with false by (rewrite in_cons in_nil orbF eq_sym bEcF ; reflexivity).
replace (b \in [:: c; a]) with false by (rewrite in_cons in_cons in_nil orbF bEcF eq_sym aEbF orbF ; reflexivity).
rewrite in_cons eq_refl.
unfold orb.
reflexivity.
Qed.

Lemma test_abc : topo_sort g [:: a; b; c] = Some [:: a; c; b].
Proof.
unfold topo_sort, size, foldl.
rewrite test_a.
unfold topo_tree.
rewrite in_nil.
replace (b \in [:: a; c; b]) with true by (rewrite in_cons in_cons in_cons eq_refl orbT orbT ; reflexivity).
rewrite in_nil.
replace (c \in [:: a; c; b]) with true by (rewrite in_cons in_cons eq_refl orbT ; reflexivity).
reflexivity.
Qed.

(* What happens if b and c, the successors of a, are visited in the reverse order? *)

Definition gr (n : node) : seq node :=
if n == a then [:: c; b]
else if n == c then [:: b]
else [::].

Lemma testr_a : topo_tree gr 3 [::] (Some [::]) a = Some [:: a; c; b].
Proof.
unfold topo_tree.
rewrite in_nil.
replace (gr a) with [:: c; b] by (unfold gr ; rewrite eq_refl ; reflexivity).
unfold foldl.
replace (c \in [:: a]) with false by (rewrite in_cons in_nil orbF eq_sym aEcF ; reflexivity).
rewrite in_nil.
replace (gr c) with [:: b] by (unfold gr ; rewrite eq_refl eq_sym aEcF ; reflexivity).
unfold foldl.
replace (b \in [:: c; a]) with false by (rewrite in_cons in_cons in_nil orbF bEcF eq_sym aEbF orbF ; reflexivity).
rewrite in_nil.
replace (gr b) with (@Nil node) by (unfold gr ; rewrite bEcF eq_sym aEbF ; reflexivity).
replace (b \in [:: a]) with false by (rewrite in_cons in_nil orbF eq_sym aEbF ; reflexivity).
replace (b \in [:: c; b]) with true by (rewrite in_cons in_cons eq_refl orbT ; reflexivity).
reflexivity.
Qed.

Lemma testr_abc : topo_sort gr [:: a; b; c] = Some [:: a; c; b].
Proof.
unfold topo_sort, size, foldl.
rewrite testr_a.
unfold topo_tree.
rewrite in_nil.
replace (b \in [:: a; c; b]) with true by (rewrite in_cons in_cons in_cons eq_refl orbT orbT ; reflexivity).
rewrite in_nil.
replace (c \in [:: a; c; b]) with true by (rewrite in_cons in_cons eq_refl orbT ; reflexivity).
reflexivity.
Qed.

(* Now let's try a few other orders of vertices in the graph. *)

Lemma test_b : topo_tree g 3 [::] (Some [::]) b = Some [:: b].
Proof.
unfold topo_tree.
rewrite in_nil.
replace (g b) with (@Nil node) by (unfold g ; rewrite bEcF eq_sym aEbF ; reflexivity).
unfold foldl.
reflexivity.
Qed.

Lemma test_ba : topo_tree g 3 [::] (Some [:: b]) a = Some [:: a; c; b].
Proof.
unfold topo_tree.
rewrite in_nil.
replace (a \in [:: b]) with false by (rewrite in_cons in_nil orbF aEbF ; reflexivity).
replace (g a) with [:: b; c] by (unfold g ; rewrite eq_refl ; reflexivity).
unfold foldl.
replace (b \in [:: a]) with false by (rewrite in_cons in_nil orbF eq_sym aEbF ; reflexivity).
replace (b \in [:: b]) with true by (rewrite in_cons eq_refl ; unfold orb ; reflexivity).
replace (c \in [:: a]) with false by (rewrite in_cons in_nil orbF eq_sym aEcF ; reflexivity).
replace (c \in [:: b]) with false by (rewrite in_cons in_nil orbF eq_sym bEcF ; reflexivity).
replace (g c) with [:: b] by (unfold g ; rewrite eq_refl eq_sym aEcF ; reflexivity).
unfold foldl.
replace (b \in [:: c; a]) with false by (rewrite in_cons in_cons in_nil orbF bEcF eq_sym aEbF orbF ; reflexivity).
replace (b \in [:: b]) with true by (rewrite in_cons eq_refl ; unfold orb ; reflexivity).
reflexivity.
Qed.

Lemma test_bac : topo_sort g [:: b; a; c] = Some [:: a; c; b].
Proof.
unfold topo_sort, size, foldl.
rewrite test_b test_ba.
unfold topo_tree.
rewrite in_nil.
replace (c \in [:: a; c; b]) with true by (rewrite in_cons in_cons eq_refl orbT ; reflexivity).
reflexivity.
Qed.

Lemma test_bc : topo_tree g 3 [::] (Some [:: b]) c = Some [:: c; b].
Proof.
unfold topo_tree.
rewrite in_nil.
replace (c \in [:: b]) with false by (rewrite in_cons in_nil orbF eq_sym bEcF ; reflexivity).
replace (g c) with [:: b] by (unfold g ; rewrite eq_refl eq_sym aEcF ; reflexivity).
unfold foldl.
replace (b \in [:: c]) with false by (rewrite in_cons in_nil orbF bEcF ; reflexivity).
replace (b \in [:: b]) with true by (rewrite in_cons eq_refl ; unfold orb ; reflexivity).
reflexivity.
Qed.

Lemma test_bca : topo_sort g [:: b; c; a] = Some [:: a; c; b].
Proof.
unfold topo_sort, size, foldl.
rewrite test_b test_bc.
unfold topo_tree.
rewrite in_nil.
replace (a \in [:: c; b]) with false by (rewrite in_cons in_cons in_nil orbF aEbF aEcF orbF ; reflexivity).
replace (g a) with [:: b; c] by (unfold g ; rewrite eq_refl ; reflexivity).
unfold foldl.
replace (b \in [:: a]) with false by (rewrite in_cons in_nil orbF eq_sym aEbF ; reflexivity).
replace (b \in [:: c; b]) with true by (rewrite in_cons in_cons eq_refl orbT ; reflexivity).
replace (c \in [:: a]) with false by (rewrite in_cons in_nil orbF eq_sym aEcF ; reflexivity).
replace (c \in [:: c; b]) with true by (rewrite in_cons eq_refl ; unfold orb ; reflexivity).
reflexivity.
Qed.

Lemma test_c : topo_tree g 3 [::] (Some [::]) c = Some [:: c; b].
Proof.
unfold topo_tree.
rewrite in_nil.
replace (g c) with [:: b] by (unfold g ; rewrite eq_refl eq_sym aEcF ; reflexivity).
unfold foldl.
replace (b \in [:: c]) with false by (rewrite in_cons in_nil orbF bEcF ; reflexivity).
rewrite in_nil.
replace (g b) with (@Nil node) by (unfold g ; rewrite bEcF eq_sym aEbF ; reflexivity).
reflexivity.
Qed.

Lemma test_ca : topo_tree g 3 [::] (Some [:: c; b]) a = Some [:: a; c; b].
Proof.
unfold topo_tree.
rewrite in_nil.
replace (a \in [:: c; b]) with false by (rewrite in_cons in_cons in_nil orbF aEbF aEcF orbF ; reflexivity).
replace (g a) with [:: b; c] by (unfold g ; rewrite eq_refl ; reflexivity).
unfold foldl.
replace (b \in [:: a]) with false by (rewrite in_cons in_nil orbF eq_sym aEbF ; reflexivity).
replace (b \in [:: c; b]) with true by (rewrite in_cons in_cons eq_refl orbT ; reflexivity).
replace (c \in [:: a]) with false by (rewrite in_cons in_nil orbF eq_sym aEcF ; reflexivity).
replace (c \in [:: c; b]) with true by (rewrite in_cons eq_refl ; unfold orb ; reflexivity).
reflexivity.
Qed.

Lemma test_cab : topo_sort g [:: c; a; b] = Some [:: a; c; b].
Proof.
unfold topo_sort, size, foldl.
rewrite test_c test_ca.
unfold topo_tree.
rewrite in_nil.
replace (b \in [:: a; c; b]) with true by (rewrite in_cons in_cons in_cons eq_refl orbT orbT ; reflexivity).
reflexivity.
Qed.

Lemma test_cb : topo_tree g 3 [::] (Some [:: c; b]) b = Some [:: c; b].
Proof.
unfold topo_tree.
rewrite in_nil.
replace (b \in [:: c; b]) with true by (rewrite in_cons in_cons eq_refl orbT ; reflexivity).
reflexivity.
Qed.

Lemma test_cba : topo_sort g [:: c; b; a] = Some [:: a; c; b].
Proof.
unfold topo_sort, size, foldl.
rewrite test_c test_cb test_ca.
reflexivity.
Qed.

Fixpoint subset (s1 s2 : seq node) : bool :=
match s1 with
| [::] => true
| a :: t => (a \in s2) && subset t s2
end.

Fixpoint reverse_path_to (g : node -> seq node) (r : node) (p :seq node) : bool :=
match p with
| [::] => true
| a :: t => (r \in g a) && ~~(a \in t) && reverse_path_to g a t
end.

Fixpoint respects_topological_order (g : node -> seq node) (v : seq node) : bool :=
match v with
| [::] => true
| a :: t => subset (g a) t && respects_topological_order g t 
end.

Theorem topo_tree_correct : 
     forall (vertices : seq node) (g : node -> seq node) (n : nat) (gray_nodes already_found : seq node) (root : node),
     (forall x : node, x \in vertices -> subset (g x) vertices) ->
     n + size gray_nodes = size vertices ->
     subset gray_nodes vertices ->
     reverse_path_to g root gray_nodes ->
     (forall v' : seq node, subset v' vertices -> v' <> [::] ->
     exists v0 : node, v0 \in v' /\ forall v1 : node, v1 \in v' -> ~~ (v0 \in g v1)) ->
     respects_topological_order g already_found ->
     if topo_tree g n gray_nodes (Some already_found) root is Some result
     then (root \in result) && respects_topological_order g result
     else false.
Proof.
     
Admitted.
