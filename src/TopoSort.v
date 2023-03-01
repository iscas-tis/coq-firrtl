From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.

Section TopoSort.

Variable node : eqType.
Variable vertices : seq node.
Variable g : node -> seq node.

Fixpoint subset (s1 s2 : seq node) : bool :=
match s1 with
| [::] => true
| a :: tail1 => (a \in s2) && subset tail1 s2
end.

Fixpoint path_from (r : node) (p : seq node) : bool :=
match p with
| [::] => true
| a :: tail => (r \in g a) && ~~(a \in tail) && path_from a tail
end.

(* We assume that every graph is closed, but perhaps not every graph is acyclic.
   In the relevant theorems we will add graph_acyclic as a precondition. *)
Hypothesis graph_closed : forall v, v \in vertices -> subset (g v) vertices.

Definition graph_acyclic :=
   forall (r : node) (p : seq node),
      r \in vertices -> subset p vertices ->
         path_from r p -> r \notin p.

(* a type to present results or error messages from topological sorting *)
Inductive result_type : Type :=
   | Some : seq node -> result_type
   | Cycle : seq node -> result_type
   | N_too_small : result_type
   .

Fixpoint topo_tree (n : nat) (gray_nodes : seq node)
                   (root : node) (maybe_already_found: result_type) : result_type :=
match maybe_already_found with
| Cycle _ | N_too_small => maybe_already_found (* propagate earlier error *)
| Some already_found =>
if root \in gray_nodes then Cycle (root :: gray_nodes) (* error: there is a cycle *)
else if root \in already_found then maybe_already_found
else match n with
     | 0 => N_too_small (* error: n was too small *)
     | S n' => match foldr (topo_tree n' (root :: gray_nodes)) maybe_already_found (g root) with
               | Some result => Some (root :: result)
               | e => e (* propagate resursive error *)
               end
     end
end.

Definition topo_sort : result_type :=
   foldr (topo_tree (size vertices) [::]) (Some [::]) vertices.

(* Now we start to work on the correctness proof of topo_sort. We first want to express
an inductive property on topo_tree that will allow us to prove the correctness of
topo_sort. Basically, we request the following:
- if topo_tree returns Cycle _, then the graph is not acyclic.
- if topo_tree returns N_too_small, then n was smaller than size vertices - size gray_nodes.
- if topo_tree return Some _, then the result contains the successors of root in addition
  to what had been already found earlier.

Then we can request on topo_sort that it never returns N_too_small,
and that it *only* returns Cycle _ if the graph is not acyclic. *)

Fixpoint respects_topological_order (v : seq node) : bool :=
match v with
| [::] => true
| a :: tail => subset (g a) tail && respects_topological_order tail
end.

Local Lemma in_cat : forall (T : eqType) (a : T) (s t : seq T), (a \in s ++ t) = (a \in s) || (a \in t).
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

Local Lemma subset_cat : forall (s t : seq node), subset s (t ++ s) = true.
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

Lemma subset_cons_cons : forall (x : node) (s t : seq node), subset s t -> subset (x :: s) (x :: t).
Proof.
induction s.
+ intros ; unfold subset.
  rewrite in_cons eq_refl orTb andTb ; trivial.
+ unfold subset at 1 ; fold subset ; intros.
  move /andP : H => [Ha Hs].
  unfold subset ; fold subset.
  rewrite (in_cons x t a) Ha orbT andTb.
  apply IHs ; exact Hs.
Qed.

Lemma subset_refl : forall (s : seq node), subset s s = true.
Proof.
intro.
rewrite <- cat0s at 2.
apply subset_cat.
Qed.

(*
Lemma subset_notin : forall (x : node) (s t : seq node),
   x \notin s -> subset s (x :: t) = subset s t.
Proof.
induction s.
* intros.
  unfold subset.
  reflexivity.
* rewrite in_cons negb_or.
  intros.
  move /andP : H => [Hx_a Hx_s].
  apply negbTE in Hx_a.
  unfold subset ; fold subset.
  rewrite in_cons eq_sym Hx_a orFb IHs ; try exact Hx_s.
  reflexivity.
Qed.
*)

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

(*
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
*)

Fixpoint reachable' (n : nat) (root : node) (already_found : seq node) : seq node :=
   if n is S n'
   then foldr (reachable' n')
              (if root \in already_found then already_found else root :: already_found)
              (g root)
   else (* root :: *) already_found.

Lemma reachable'_subset :
   forall (n k : nat) (l m : seq node) (root : node),
      n <= k -> (subset l m) ->
         subset (reachable' n root l) (reachable' k root m).
Proof.
induction n.
* intros ; unfold reachable' at 1.
  clear H.
  move : root l m H0.
  induction k.
  + intros.
    exact H0.
  + unfold reachable' ; fold reachable'.
    intro ; induction (g root).
    - intros ; unfold foldr.
      destruct (root \in m) ; try apply H0.
      apply subset_trans with (t := m) ; try apply H0.
      rewrite <- cat1s ; apply subset_cat.
    - intros.
      replace (foldr (reachable' k)
                     (if root \in m then m else root :: m)
                     (a :: l))
      with (reachable' k a
              (foldr (reachable' k)
                     (if root \in m then m else root :: m)
                     l))
      by reflexivity.
      apply IHk, IHl, H0.
* intros.
  rewrite <- ltn_predK with (m := n) (n := k) ; try apply H.
  unfold reachable' ; fold reachable'.
  induction (g root).
  + unfold foldr.
    destruct (root \in l) eqn: Hroot_in_l.
    - replace ((root \in l) = true) with (is_true (root \in l)) in Hroot_in_l by reflexivity.
      apply in_subset_trans with (t := m) in Hroot_in_l ; try apply H0.
      rewrite Hroot_in_l ; apply H0.
    - destruct (root \in m) eqn: Hroot_in_m.
      * unfold subset ; rewrite Hroot_in_m andTb ; exact H0.
      * unfold subset ; fold subset.
        rewrite in_cons eq_refl orTb andTb.
        apply subset_trans with (t := m) ; try apply H0.
        rewrite <- cat1s ; apply subset_cat.
  + replace (foldr (reachable' n)
                   (if root \in l then l else root :: l)
                   (a :: l0))
    with (reachable' n a
            (foldr (reachable' n)
                   (if root \in l then l else root :: l)
                   l0))
    by reflexivity.
    replace (foldr (reachable' k.-1)
                   (if root \in m then m else root :: m)
                   (a :: l0))
    with (reachable' k.-1 a
            (foldr (reachable' k.-1)
                   (if root \in m then m else root :: m)
                   l0))
    by reflexivity.
    apply IHn, IHl0.
    rewrite <- ltn_predK with (m := n) (n := k) in H ; apply H.
Qed.

(*
Lemma reachable'_correct :
   forall (x : node) (n : nat) (already_found : seq node) (root : node),
         subset already_found (reachable' n root already_found)
      /\ (* reachable' ... root only contains successors of root *)
         (x \in reachable' n root already_found ->
             x == root \/ x \in already_found \/
             exists y : node, y \in reachable' n root already_found /\ x \in g y)
      /\ (* reachable' ... root contains all successors of root. *)
         ((exists p : seq node, path_from x p /\ size p <= n /\ last x p == root) ->
             x \in reachable' n root already_found).
Proof.
intros.
induction n.
* unfold reachable'.
  destruct (root \in already_found) eqn: Hroot_in_already_found.
  + split ; try apply subset_refl.
    split.
    - intro ; rewrite H.
      right ; left ; trivial.
    - intro ; destruct H ; destruct H ; destruct H0.
      rewrite leqn0 in H0 ; move /eqP : H0 => H0.
      apply size0nil in H0.
      rewrite H0 in H1 ; unfold last in H1 ; move /eqP : H1 => H1.
      rewrite H1 Hroot_in_already_found ; trivial.
  + split ; try apply subset_refl.
    split.
    - intro.
      rewrite in_cons in H ; move /orP : H => H.
      destruct H.
      * left ; rewrite H ; trivial.
      * right ; left ; rewrite H ; trivial.
    - intro ; destruct H ; destruct H ; destruct H0.
      rewrite leqn0 in H0 ; move /eqP : H0 => H0.
      apply size0nil in H0.
      rewrite H0 in H1 ; unfold last in H1 ; move /eqP : H1 => H1.
      rewrite H1 in_cons eq_refl orTb ; trivial.
-- not sure whether I actually need this --
Admitted.

Definition reachable (root : node) : seq node :=
   reachable' (size vertices) root [::].

Definition reachable_seq (roots : seq node) : seq node :=
   foldr (reachable' (size vertices)) [::] roots.
*)

Theorem topo_tree_correct :
   forall (n : nat) (gray_nodes already_found : seq node) (root : node),
      size vertices <= size gray_nodes + n ->
      subset gray_nodes vertices ->
      root \in vertices ->
      path_from root gray_nodes ->
      respects_topological_order already_found ->
         match topo_tree n gray_nodes root (Some already_found) with
         | Some result => subset (reachable' n root already_found) result /\
                          subset result (reachable' n root already_found) /\
                          respects_topological_order result
         | Cycle _ => ~graph_acyclic
         | _ => False
         end.
Proof.
induction n.
* intros gray_nodes already_found root Hn Hgray_nodes_ok Hroot_ok Hpath_ok Halready_found_ok.
  rewrite addn0 in Hn.
  unfold topo_tree.
  (* we prove that root \in gray_nodes, through the following steps:
     1. uniq gray_nodes (because of path_from root gray_nodes
     2. subset vertices gray_nodes (because there are at least as many gray nodes as
                                    vertices, as per precondition, and because of 1.)
  *)
  assert (Hgray_nodes_uniq : uniq gray_nodes).
        clear -Hpath_ok.
        move : root Hpath_ok.
        induction gray_nodes.
        + unfold uniq ; trivial.
        + unfold path_from ; fold path_from.
          intros.
          unfold uniq ; fold (@uniq node).
          move /andP : Hpath_ok => [Hpath_ok Hpf] ; move /andP : Hpath_ok => [_ Ha_ni_p].
          rewrite Ha_ni_p andTb.
          apply IHgray_nodes with (root := a) ; exact Hpf.
(*assert (forall (p : seq node) (a : node), uniq p -> a \notin rem a p).
        clear.
        induction p.
        + intros ; unfold rem ; rewrite in_nil ; trivial.
        + intros b Hu.
          rewrite cons_uniq in Hu ; move /andP : Hu => Hu.
          destruct (eqVneq a b).
          - rewrite <- e.
            unfold rem ; rewrite eq_refl ; apply Hu.
          - apply negbTE in i.
            rewrite rem_cons i in_cons eq_sym i orFb.
            apply IHp, Hu. *)
  assert (subset_remr : forall (p q : seq node) (a : node), a \notin p -> subset p q -> subset p (rem a q)).
        clear.
        induction p.
        + unfold subset at 2 ; trivial.
        + unfold subset ; fold subset.
          intros q b H H0.
          rewrite in_cons negb_or in H ; move /andP : H => [H H1].
          apply rwP with (P := a \in rem (T:=node) b q /\ subset p (rem (T:=node) b q)) ; try exact andP.
          move /andP : H0 => [H0 H2].
          split.
          - clear -H H0.
            induction q.
            * rewrite in_nil in H0 ; done.
            * rewrite in_cons in H0.
              move /orP : H0 => H0.
              destruct H0.
              + move /eqP : H0 => H0.
                apply negbTE in H.
                rewrite rem_cons eq_sym.
                rewrite <- H0.
                rewrite H in_cons eq_refl orTb ; trivial.
              + rewrite rem_cons.
                destruct (a0 == b) ; try exact H0.
                rewrite in_cons.
                apply rwP with (P := a == a0 \/ a \in rem b q) ; try apply orP.
                right ; apply IHq ; exact H0.
          - apply IHp ; trivial.
  assert (subset_reml : forall (q p : seq node) (a : node), subset (rem a q) p -> subset q (a :: p)).
        clear.
        induction q.
        + intros ; unfold subset ; trivial.
        + intros p b.
          rewrite rem_cons.
          destruct (eqVneq a b).
          - rewrite e.
            apply subset_cons_cons.
          - unfold subset ; fold subset.
            apply negbTE in i.
            move /andP => [Ha Hb].
            rewrite in_cons i orFb Ha andTb.
            apply IHq, Hb.
  assert (Hvertices_in_gray_nodes : subset vertices gray_nodes).
         clear -Hn Hgray_nodes_ok Hgray_nodes_uniq subset_reml subset_remr.
         move : vertices Hn Hgray_nodes_ok Hgray_nodes_uniq.
         induction gray_nodes.
        + unfold size at 2.
          intros.
          rewrite leqn0 in Hn ; move /nilP : Hn => Hn ; rewrite Hn.
          apply subset_refl.
        + intros.
          (*specialize IHgray_nodes with (rem a q).*)
          unfold size at 2 in Hn ; fold (@size node) in Hn.
          unfold subset in Hgray_nodes_ok ; fold subset in Hgray_nodes_ok ; move /andP : Hgray_nodes_ok => Hgray_nodes_ok.
          unfold uniq in Hgray_nodes_uniq ; fold (@uniq node) in Hgray_nodes_uniq ; move /andP : Hgray_nodes_uniq => Hgray_nodes_uniq.
          apply subset_reml, IHgray_nodes.
          - rewrite size_rem ; try apply Hgray_nodes_ok.
            rewrite leqNgt ltn_predRL ; rewrite <- leqNgt ; exact Hn.
          - apply subset_remr ; try apply Hgray_nodes_uniq ; apply Hgray_nodes_ok.
          - apply Hgray_nodes_uniq.
  assert (Hroot_in_gray_nodes : root \in gray_nodes).
        apply in_subset_trans with (s := vertices).
        + exact Hroot_ok.
        + exact Hvertices_in_gray_nodes.
  rewrite Hroot_in_gray_nodes.
  unfold graph_acyclic.
  rewrite <- negbK in Hroot_in_gray_nodes.
  move /negP : Hroot_in_gray_nodes => Hroot_in_gray_nodes.
  contradict Hroot_in_gray_nodes ; rename Hroot_in_gray_nodes into Hgraph_acyclic.
  apply Hgraph_acyclic.
  + exact Hroot_ok.
  + exact Hgray_nodes_ok.
  + exact Hpath_ok.
* intros gray_nodes already_found root Hn Hgray_nodes_ok Hroot_ok Hpath_ok Halready_found_ok.
  unfold topo_tree ; fold topo_tree.
  destruct (root \in gray_nodes) eqn: Hroot_in_gray_nodes.
  + unfold graph_acyclic.
    rewrite <- negbK in Hroot_in_gray_nodes.
    move /negP : Hroot_in_gray_nodes => Hroot_in_gray_nodes.
    contradict Hroot_in_gray_nodes ; rename Hroot_in_gray_nodes into Hgraph_acyclic.
    apply Hgraph_acyclic.
    - exact Hroot_ok.
    - exact Hgray_nodes_ok.
    - exact Hpath_ok.
  + assert (foldr_topo_tree_correct :
       forall (adjacents : seq node), subset adjacents (g root) ->
             match foldr (topo_tree n (root :: gray_nodes)) (Some already_found) adjacents with
             | Some result => subset (foldr (reachable' n) already_found adjacents) result /\
                              subset result (foldr (reachable' n) already_found adjacents) /\
                              respects_topological_order result
             | Cycle _ => ~graph_acyclic
             | _ => False
             end).
        induction adjacents.
        - intro.
          unfold foldr.
          split ; try apply subset_refl.
          split ; try apply subset_refl.
          exact Halready_found_ok.
        - replace (foldr (topo_tree n (root :: gray_nodes)) (Some already_found) (a :: adjacents))
          with (topo_tree n (root :: gray_nodes) a (foldr (topo_tree n (root :: gray_nodes)) (Some already_found) adjacents))
          by reflexivity.
          destruct (foldr (topo_tree n (root :: gray_nodes)) (Some already_found) adjacents) ;
                try (unfold topo_tree ; destruct n ; unfold subset ;
                     move /andP => [_ Hadjacents_g_root] ;
                     apply IHadjacents, Hadjacents_g_root).
          intro.
          replace (foldr (reachable' n) already_found (a :: adjacents))
          with (reachable' n a (foldr (reachable' n) already_found adjacents))
          by reflexivity.
          unfold subset in H ; fold subset in H ; move /andP : H => [Ha Hadjacents].
          assert (IHn' : match topo_tree n (root :: gray_nodes) a (Some l) with
                         | Some result => 
                              subset (reachable' n a l) result /\
                              subset result (reachable' n a l) /\
                              respects_topological_order result
                         | Cycle _ => ~ graph_acyclic
                         | N_too_small => False
                         end).
                apply IHn.
                * unfold size at 2 ; fold (@size node).
                  rewrite addSnnS ; exact Hn.
                * unfold subset ; fold subset.
                  rewrite Hroot_ok Hgray_nodes_ok ; trivial.
                * apply in_subset_trans with (s := g root) ; try apply Ha.
                  apply graph_closed ; exact Hroot_ok.
                * unfold path_from ; fold path_from.
                  rewrite Ha Hroot_in_gray_nodes Hpath_ok ; trivial.
                * apply IHadjacents, Hadjacents.
          clear IHn.
          destruct (topo_tree n (root :: gray_nodes) a (Some l)) ;
                try exact IHn'.
          split.
          * apply subset_trans with (t := reachable' n a l) ; try apply IHn'.
            apply reachable'_subset ; try apply leqnn.
            apply IHadjacents, Hadjacents.
          * split ; try apply IHn'.
            apply subset_trans with (t := reachable' n a l) ; try apply IHn'.
            apply reachable'_subset ; try apply leqnn.
            apply IHadjacents, Hadjacents.
    specialize foldr_topo_tree_correct with (adjacents := g root).
    rewrite subset_refl in foldr_topo_tree_correct.
    destruct (foldr (topo_tree n (root :: gray_nodes)) 
                    (Some already_found) (g root)) eqn: Hfoldr_topo_tree.
    - destruct (root \in already_found) eqn: Hroot_in_already_found.
      * rewrite Halready_found_ok.
        (* I think we need a property like:
           forall (k : nat) (root : node),
              respects_topological_order already_found -> root \in already_found ->
                 subset (reachable' k root already_found) already_found.
           This holds in particular because reachable' only adds g-successors
           to a set, but they are already in the set that respects the topological order.
           It should be provable by induction over k. *)
        admit.
      * (* we mainly use foldr_topo_tree_correct.
           We also need the property that g root is a subset of l,
           which may require a slight change of the definition of reachable',
           so that subset (foldr (reachable' n) already_found (g root)) l
           ensures this even when n == 0. *)
        admit.
    - (* There is a cycle in some successor of root; therefore we cannot have
         root \in already_found /\ respects_topological_order already_found.
         So we can assume that root \notin already_found. *)
      replace (root \in already_found) with false.
      apply foldr_topo_tree_correct ; done.
      admit.
    - contradict foldr_topo_tree_correct ; done.
Admitted.

Theorem topo_sort_correct :
   match topo_sort with
   | Some result => graph_acyclic /\
                    subset vertices result /\
                    subset result vertices /\
                    respects_topological_order result
   | Cycle _ => ~graph_acyclic
   | _ => False
   end.
Proof.
(* mainly use topo_tree_correct. *)
Admitted.

End TopoSort.
