From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.

Section TopoSort.

(* general parameters of the functions in this file:
   the nodes are an eqType,
   the vertices are a finite set (the order of the sequence does not matter),
   and g describes the adjacency relation: for every vertex v,
   the sequence (g v) contains the successors of v
   (again, the order of the sequence does not matter). *)
Context {node : eqType}.
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
| a :: tail => subset (g a) tail && (a \notin tail) && respects_topological_order tail
end.

Local Lemma subset_cat : forall (s t : seq node), subset s (t ++ s) = true.
Proof.
induction s.
* unfold subset ; reflexivity.
* intro.
  unfold subset ; fold subset.
  rewrite mem_cat mem_head orbT andTb -cat1s catA.
  apply IHs.
Qed.

Lemma subset_cons_cons : forall (x : node) (s t : seq node), subset s t -> subset (x :: s) (x :: t).
Proof.
induction s.
+ intros ; unfold subset.
  rewrite mem_head ; trivial.
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

Lemma subset_nil : forall (s : seq node), subset s [::] -> s = [::].
Proof.
destruct s.
* intro ; reflexivity.
* unfold subset ; rewrite in_nil andFb ; done.
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
  move /andP : H0 => H0.
  move /orP : H => [H|H].
  + move /eqP : H => H ; rewrite H ; apply H0.
  + apply IHs.
    - apply H.
    - apply H0.
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

Local Lemma respects_topological_order_gx :
   forall (v : seq node) (x : node),
      respects_topological_order v -> x \in v -> subset (g x) v.
Proof.
induction v.
* intro ; rewrite in_nil . done.
* intro ; rewrite in_cons.
  intros.
  apply subset_trans with (t := v).
  + move : H => /andP [/andP [H H1] H2].
    fold respects_topological_order in H2.
    destruct (eqVneq x a).
    - rewrite e ; exact H.
    - apply IHv; done.
  + rewrite -cat1s subset_cat. trivial.
Qed.

Definition disjoint (s t : seq node) :=
   forall (x : node), (x \notin s) || (x \notin t).

Theorem topo_tree_correct :
   forall (n : nat) (gray_nodes already_found : seq node) (root : node),
      size vertices <= size gray_nodes + n ->
      subset gray_nodes vertices ->
      subset already_found vertices ->
      disjoint gray_nodes already_found ->
      root \in vertices ->
      path_from root gray_nodes ->
      respects_topological_order already_found ->
         match topo_tree n gray_nodes root (Some already_found) with
         | Some result => subset already_found result /\
                          disjoint gray_nodes result /\
                          root \in result /\
                          subset result vertices /\
                          respects_topological_order result
         | Cycle _ => ~graph_acyclic
         | _ => False
         end.
Proof.
induction n.
* intros gray_nodes already_found root.
  intros Hn Hgray_nodes_closed Halready_found_closed Hdisjoint Hroot_ok Hpath_ok Halready_found_ok.
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
        + unfold uniq. trivial.
        + unfold path_from ; fold path_from.
          intros.
          unfold uniq ; fold (@uniq node).
          move /andP : Hpath_ok => [Hpath_ok Hpf].
          move /andP : Hpath_ok => [_ Ha_ni_p].
          rewrite Ha_ni_p. 
          rewrite andTb.
          apply IHgray_nodes with (root := a). 
          exact Hpf.
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
        + unfold subset at 2. trivial.
        + unfold subset ; fold subset.
          intros q b H H0.
          rewrite in_cons in H.
          rewrite negb_or in H. 
          move /andP : H => [H H1].
          apply rwP with (P := a \in rem (T:=node) b q /\ subset p (rem (T:=node) b q)) ; try exact andP.
          move /andP : H0 => [H0 H2].
          split.
          - clear -H H0.
            induction q.
            * rewrite in_nil in H0. done.
            * rewrite in_cons in H0.
              move /orP : H0 => [H0|H0].
              + move /eqP : H0 => H0.
                apply negbTE in H.
                rewrite rem_cons. 
                rewrite eq_sym.
                rewrite -H0. 
                rewrite H.
                rewrite mem_head ; trivial.
              + rewrite rem_cons.
                destruct (a0 == b) ; try exact H0.
                rewrite in_cons.
                apply rwP with (P := a == a0 \/ a \in rem b q) ; try apply orP.
                right.
                apply IHq ; exact H0.
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
         clear -Hn Hgray_nodes_closed Hgray_nodes_uniq subset_reml subset_remr.
         move : vertices Hn Hgray_nodes_closed Hgray_nodes_uniq.
         induction gray_nodes.
        + unfold size at 2.
          intros.
          rewrite leqn0 in Hn.
          move /nilP : Hn => Hn.
          rewrite Hn.
          apply subset_refl.
        + intros.
          unfold size at 2 in Hn ; fold (@size node) in Hn.
          unfold subset in Hgray_nodes_closed ; fold subset in Hgray_nodes_closed ; move /andP : Hgray_nodes_closed => Hgray_nodes_closed.
          unfold uniq in Hgray_nodes_uniq ; fold (@uniq node) in Hgray_nodes_uniq ; move /andP : Hgray_nodes_uniq => Hgray_nodes_uniq.
          apply subset_reml, IHgray_nodes.
          - rewrite size_rem ; try apply Hgray_nodes_closed.
            rewrite leqNgt ltn_predRL -leqNgt ; exact Hn.
          - apply subset_remr ; try apply Hgray_nodes_uniq ; apply Hgray_nodes_closed.
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
  + exact Hgray_nodes_closed.
  + exact Hpath_ok.
* intros gray_nodes already_found root Hn Hgray_nodes_closed Halready_found_closed Hdisjoint Hroot_ok Hpath_ok Halready_found_ok.
  unfold topo_tree ; fold topo_tree.
  destruct (root \in gray_nodes) eqn: Hroot_in_gray_nodes.
  + unfold graph_acyclic.
    rewrite <- negbK in Hroot_in_gray_nodes.
    move /negP : Hroot_in_gray_nodes => Hroot_in_gray_nodes.
    contradict Hroot_in_gray_nodes ; rename Hroot_in_gray_nodes into Hgraph_acyclic.
    apply Hgraph_acyclic.
    - exact Hroot_ok.
    - exact Hgray_nodes_closed.
    - exact Hpath_ok.
  + destruct (root \in already_found) eqn: Hroot_in_already_found.
    - split ; try apply subset_refl.
      split ; try apply Hdisjoint.
      rewrite Hroot_in_already_found Halready_found_closed Halready_found_ok ; done.
    - assert (foldr_topo_tree_correct :
         forall (adjacents : seq node), subset adjacents (g root) ->
               match foldr (topo_tree n (root :: gray_nodes)) (Some already_found) adjacents with
               | Some result => subset already_found result /\
                                disjoint (root :: gray_nodes) result /\
                                subset adjacents result /\
                                subset result vertices /\
                                respects_topological_order result
               | Cycle _ => ~graph_acyclic
               | _ => False
               end).
          induction adjacents.
          * intro.
            unfold foldr.
            split ; try apply subset_refl.
            split.
            + unfold disjoint ; intro.
              rewrite in_cons.
              destruct (eqVneq x root).
              - rewrite orTb orFb e Hroot_in_already_found ; trivial.
              - rewrite orFb ; apply Hdisjoint.
            + unfold subset at 1 ; rewrite Halready_found_closed Halready_found_ok ; done.
          * replace (foldr (topo_tree n (root :: gray_nodes)) (Some already_found) (a :: adjacents))
            with (topo_tree n (root :: gray_nodes) a (foldr (topo_tree n (root :: gray_nodes)) (Some already_found) adjacents))
            by reflexivity.
            destruct (foldr (topo_tree n (root :: gray_nodes)) (Some already_found) adjacents) ;
                  try (unfold topo_tree ; destruct n ; unfold subset ;
                       move /andP => [_ Hadjacents_g_root] ;
                       apply IHadjacents, Hadjacents_g_root).
            intro.
            unfold subset in H ; fold subset in H ; move /andP : H => [Ha Hadjacents].
            assert (IHn' : match topo_tree n (root :: gray_nodes) a (Some l) with
                           | Some result =>
                                subset l result /\
                                disjoint (root :: gray_nodes) result /\
                                a \in result /\
                                subset result vertices /\
                                respects_topological_order result
                           | Cycle _ => ~ graph_acyclic
                           | N_too_small => False
                           end).
                  apply IHn ; try apply IHadjacents, Hadjacents.
                  + rewrite {2}/size addSnnS ; exact Hn.
                  + rewrite /subset -/subset Hroot_ok Hgray_nodes_closed //.
                  + apply (in_subset_trans (g root)) ; try apply Ha.
                    apply graph_closed, Hroot_ok.
                  + unfold path_from ; fold path_from.
                    rewrite Ha Hroot_in_gray_nodes Hpath_ok ; trivial.
            clear IHn.
            destruct (topo_tree n (root :: gray_nodes) a (Some l)) ;
                  try exact IHn'.
            split.
            + apply subset_trans with (t := l) ; try apply IHn'.
              apply IHadjacents, Hadjacents.
            split.
            + apply IHn'.
            split.
            + unfold subset at 1 ; fold subset.
              apply rwP with (P := a \in l0 /\ subset adjacents l0) ; try exact andP.
              split ; try apply IHn'.
              apply subset_trans with (t := l) ; try apply IHn'.
              apply IHadjacents, Hadjacents.
            + apply IHn'.
      specialize foldr_topo_tree_correct with (adjacents := g root).
      rewrite subset_refl in foldr_topo_tree_correct.
      destruct (foldr (topo_tree n (root :: gray_nodes)) 
                      (Some already_found) (g root)) eqn: Hfoldr_topo_tree ;
            try (apply foldr_topo_tree_correct ; trivial).
      assert (disjoint (root :: gray_nodes) l) by (apply foldr_topo_tree_correct ; trivial).
      split.
      * apply subset_trans with (t := l) ; try (apply foldr_topo_tree_correct ; trivial).
        rewrite -cat1s subset_cat ; trivial.
      split.
      * unfold disjoint ; intro.
        rewrite in_cons negb_or.
        destruct (eqVneq x root).
        + rewrite andFb orbF e Hroot_in_gray_nodes ; trivial.
        + unfold disjoint in H ; specialize H with (x := x).
          rewrite in_cons negb_or i andTb in H.
          rewrite andTb H ; trivial.
      split.
      * apply mem_head.
      split.
      * unfold subset ; fold subset.
        rewrite Hroot_ok andTb.
        apply foldr_topo_tree_correct ; trivial.
      * unfold respects_topological_order ; fold respects_topological_order.
        apply rwP with (P := subset (g root) l && (root \notin l) /\ respects_topological_order l) ; try exact andP.
        split ; try (apply foldr_topo_tree_correct ; trivial).
        apply rwP with (P := subset (g root) l /\ root \notin l) ; try exact andP.
        split ; try (apply foldr_topo_tree_correct ; trivial).
        unfold disjoint in H ; specialize H with (x := root).
        rewrite mem_head orFb in H.
        exact H.
Qed.

Lemma index_behead :
   forall (x y : node) (s : seq node), x != y -> index x (y :: s) = (index x s).+1.
Proof.
intros.
unfold index at 1.
rewrite -cat1s find_cat.
unfold has.
apply negbTE in H.
rewrite orbF pred1E H.
unfold size.
done.
Qed.

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
unfold topo_sort.
assert (foldr_topo_sort_correct : forall v : seq node,
   subset v vertices ->
      match foldr (topo_tree (size vertices) [::]) (Some [::]) v with
      | Some result => subset v result /\
                       subset result vertices /\ respects_topological_order result
      | Cycle _ => ~ graph_acyclic
      | N_too_small => False
      end).
      induction v.
      * intro ; unfold foldr.
        split ; try apply subset_refl.
        split ; trivial.
      * unfold subset at 1 ; fold subset ; move /andP => [Ha_in_vertices Hv_in_vertices].
        replace (foldr (topo_tree (size vertices) [::]) (Some [::]) (a :: v))
        with (topo_tree (size vertices) [::] a (foldr (topo_tree (size vertices) [::]) (Some [::]) v))
        by reflexivity.
        destruct (foldr (topo_tree (size vertices) [::]) (Some [::]) v) ;
              try (unfold topo_tree ; destruct (size vertices) ;
                   apply IHv, Hv_in_vertices).
        assert (match topo_tree (size vertices) [::] a (Some l) with
                | Some result => subset l result /\
                                 disjoint [::] result /\
                                 a \in result /\
                                 subset result vertices /\
                                 respects_topological_order result
                | Cycle _ => ~graph_acyclic
                | _ => False
                end).
              apply topo_tree_correct ; try done ; apply IHv, Hv_in_vertices.
        destruct (topo_tree (size vertices) [::] a (Some l)) ; try exact H.
        split ; try apply H.
        unfold subset ; fold subset.
        apply rwP with (P := a \in l0 /\ subset v l0) ; try exact andP.
        split ; try apply H.
        apply subset_trans with (t := l) ; try apply H.
        apply IHv, Hv_in_vertices.
specialize foldr_topo_sort_correct with (v := vertices) ; rewrite subset_refl in foldr_topo_sort_correct.
destruct (foldr (topo_tree (size vertices) [::]) (Some [::]) vertices) ;
      try (apply foldr_topo_sort_correct ; trivial).
split ; try (apply foldr_topo_sort_correct ; trivial).
unfold graph_acyclic.
intros.
assert (Huniq : uniq l).
      assert (respects_topological_order l) by (apply foldr_topo_sort_correct ; trivial).
      clear -H2.
      induction l.
      * unfold uniq ; trivial.
      * unfold uniq ; fold (@uniq node).
        unfold respects_topological_order in H2 ;
        fold respects_topological_order in H2.
        move /andP : H2 => [H2 Hrespects_topological_order].
        move /andP : H2 => [_ Ha_notin_l].
        rewrite Ha_notin_l andTb.
        apply IHl, Hrespects_topological_order.
assert (forall (x y : node), x \in l -> y \in l -> y \in g x -> index x l < index y l).
      assert (respects_topological_order l) by (apply foldr_topo_sort_correct ; trivial).
      clear -Huniq H2.
      induction l.
      * intro ; rewrite in_nil ; done.
      * intros x y.
        unfold uniq in Huniq ; fold (@uniq node) in Huniq.
        move /andP : Huniq => [/negP Ha_notin_l Huniq].
        destruct (eqVneq x a).
        + rewrite !e ; intros.
          unfold respects_topological_order in H2 ; fold respects_topological_order in H2 ;
          move /andP : H2 => [H2 Hrespects_topological_order_l].
          move /andP : H2 => [Hg_a_l _].
          rewrite index_head index_behead.
          - apply ltn0Sn.
          - apply rwP with (P := ~y == a) ; try exact negP.
            contradict Ha_notin_l.
            move /eqP : Ha_notin_l => Ha_notin_l ; rewrite -Ha_notin_l.
            apply in_subset_trans with (s := g a) ; try exact H1.
            exact Hg_a_l.
        + rewrite index_behead ; try (exact i).
          intros.
          apply negbTE in i.
          rewrite in_cons in H ; rewrite i in H ; rewrite orFb in H.
          move /andP : H2 => [_ H2].
          assert (y != a).
                apply rwP with (P := ~ y == a) ; try exact negP.
                contradict Ha_notin_l.
                move /eqP : Ha_notin_l => Ha_notin_l ; rewrite -Ha_notin_l.
                apply in_subset_trans with (s := g x) ; try exact H1.
                apply respects_topological_order_gx ; done.
          rewrite index_behead ; try exact H3.
          apply negbTE in H3.
          rewrite in_cons in H0 ; rewrite H3 in H0 ; rewrite orFb in H0.
          rewrite ltnS.
          apply IHl ; try done.
assert (subset p (take (index r l) l)).
      move : r H0 H H1.
      induction p.
      * intros ; unfold subset ; trivial.
      * intros.
        specialize IHp with (r := a).
        move : H1 => /andP [/andP [Hr_in_ga Ha_notin_p] Hpath_from] ;
        fold path_from in Hpath_from.
        unfold subset ; fold subset.
        apply rwP with (P := a \in take (index r l) l /\ subset p (take (index r l) l)) ; try exact andP.
        unfold subset in H0 ; fold subset in H0.
        move /andP : H0 => H0.
        assert (index a l < index r l).
              apply H2 ; try done.
              + apply in_subset_trans with (s := vertices) ; try apply H0.
                apply foldr_topo_sort_correct ; trivial.
              + apply in_subset_trans with (s := vertices) ; try apply H.
                apply foldr_topo_sort_correct ; trivial.
        split.
        + rewrite in_take_leq ; try exact H1.
          apply index_size.
        + apply subset_trans with (t := (take (index a l) l)).
          - apply IHp ; try done ; apply H0.
          - clear -H1.
            induction l.
            * unfold take, subset ; trivial.
            * destruct (eqVneq a a0).
              + rewrite -!e index_head take0 ; unfold subset ; trivial.
              + rewrite index_behead ; try exact i.
                rewrite take_cons.
                assert (r != a0).
                      apply rwP with (P := ~ r == a0) ; try exact negP.
                      contradict H1.
                      move /eqP : H1 => H1.
                      rewrite H1 index_head ltn0 ; done.
                rewrite index_behead ; try exact H.
                rewrite take_cons.
                apply subset_cons_cons, IHl.
                - rewrite index_behead in H1 ; try exact i.
                  rewrite index_behead in H1 ; try exact H.
                  rewrite ltnS in H1.
                  exact H1.
assert (~index r l < index r l)
      by (apply rwP with (b := ~~ (index r l < index r l)) ; try exact negP ;
          apply negbT, ltnn).
apply rwP with (P := ~ r \in p) ; try exact negP.
contradict H4.
rewrite -(@has_take node (pred1 r) l (index r l)).
+ rewrite has_find index_mem.
  apply in_subset_trans with (s := p) ; done.
+ rewrite has_find index_mem.
  apply in_subset_trans with (s := vertices) ; try exact H.
  apply foldr_topo_sort_correct ; trivial.
Qed.

End TopoSort.

Print topo_sort.
Check topo_sort_correct.

