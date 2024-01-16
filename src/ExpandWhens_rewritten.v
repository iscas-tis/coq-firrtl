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
forall (gt : fgtyp) (v : ProdVarOrder.T) (vm : module_graph_vertex_set_p.env),
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
* destruct (module_graph_vertex_set_p.find v vm) as [[newgt|newgt|newgt|newgt _|newgt|newgt]|] ; try trivial ;
  destruct newgt ; try trivial ; destruct (n == n0) eqn :Hnn0 ; try trivial ;
  move /eqP : Hnn0 => Hnn0 ; rewrite -Hnn0 ; reflexivity.
* destruct (module_graph_vertex_set_p.find v vm) as [[newgt|newgt|newgt|newgt _|newgt|newgt]|] ; try trivial ;
  destruct newgt ; try trivial ; destruct (n == n0) eqn :Hnn0 ; try trivial ;
  move /eqP : Hnn0 => Hnn0 ; rewrite -Hnn0 ; reflexivity.
* destruct (module_graph_vertex_set_p.find v vm) as [[newgt|newgt|newgt|newgt _|newgt|newgt]|] ; try trivial ;
  destruct newgt ; trivial.
* destruct (module_graph_vertex_set_p.find v vm) as [[newgt|newgt|newgt|newgt _|newgt|newgt]|] ; try trivial ;
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
| Sinvalid _ => true
| Sinst _ _ => false (* instances are not supported currently *)
| Snode _ e => expr_has_fully_inferred_ground_types e
| Sfcnct _ e => true (* does not really need to check, as no new components are generated *)
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
forall (vm : module_graph_vertex_set_p.env) (tmap scope : CEP.t ftype) (s : HiFP.hfstmt),
   stmt_has_fully_inferred_ground_types s ->
   tmap_has_fully_inferred_ground_types tmap ->
   submap scope tmap ->
      match stmt_tmap (tmap, scope) s vm with
      | Some (tmap', scope') => tmap_has_fully_inferred_ground_types tmap'
      | _ => True
      end
with stmts_tmap_preserves_fully_inferred :
forall (vm : module_graph_vertex_set_p.env) (ss : HiFP.hfstmt_seq) (tmap scope : CEP.t ftype),
   stmts_have_fully_inferred_ground_types ss ->
   tmap_has_fully_inferred_ground_types tmap ->
   submap scope tmap ->
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
          rewrite H1 in H0.
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
    apply (submap_trans tmap) ; first by exact H1.
    by apply H2.
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

Definition module_has_fully_inferred_ground_types (m : HiFP.hfmodule) : bool :=
match m with
| FInmod _ pp ss
| FExmod _ pp ss =>
       ports_have_fully_inferred_ground_types pp
    &&
       stmts_have_fully_inferred_ground_types ss
end.

(* We first define ExpandBranch_fun.
   It uses a map to indicate which expressions are connected in which
   situation.  To use this map, one needs the data type def_expr. *)

Definition helper_tf (c : HiFP.hfexpr) (true_expr : option def_expr) (false_expr : option def_expr) : option def_expr := 
(* helper function for bringing together the connection maps from true and false branches *)
match true_expr, false_expr with
| Some (D_fexpr t), Some (D_fexpr f) => (*if t == f then true_expr
                                          else*) Some (D_fexpr (Emux c t f))
| Some D_invalidated, _
| None, _ => false_expr
| _, Some D_invalidated
| _, None => true_expr
| Some D_undefined, _
| _, Some D_undefined => Some D_undefined
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
        match ExpandBranch_funs ss_false true_def_ss old_conn_map old_scope with
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
  induction ss.
  + intros.
    unfold ExpandBranch_funs in H.
    unfold component_stmts_of.
    rewrite Qcats0.
    symmetry.
    injection H.
    by trivial.
  + intros.
    simpl ExpandBranch_funs in H ; simpl component_stmts_of.
    specialize ExpandBranch_component with (s := h) (def_ss := def_ss) (conn_map := conn_map) (scope := scope).
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
    generalize (ExpandBranch_components ss_false def_ss_true conn_map scope) ;
          intro.
    destruct (ExpandBranch_funs ss_false def_ss_true conn_map scope) as [[[def_ss_false conn_map_false] scope_false]|] ; last by discriminate H.
    specialize (H1 def_ss_false conn_map_false scope_false Logic.eq_refl).
    unfold fst, snd in H ; injection H ; intros.
    rewrite -Qcat_assoc -H0 -H1 H4 //.
Qed.

(* The following is a nice lemma
   but the subset old_scope1 old_scope2 is the wrong way round.
   After this comes a lemma with the subsets the other way round;
   note that the proofs are almost literally the same.

Lemma ExpandBranch_stmt_tmap :
forall (vm : module_graph_vertex_set_p.env) (s : HiFP.hfstmt)
       (old_tmap new_tmap old_scope1 new_scope1 old_scope2 new_scope2 : CEP.t ftype)
       (old_def_ss new_def_ss : HiFP.hfstmt_seq) (old_conn_map new_conn_map : CEP.t def_expr),
   stmt_tmap (old_tmap, old_scope1) s vm = Some (new_tmap, new_scope1) ->
   ExpandBranch_fun s old_def_ss old_conn_map old_scope2 = Some (new_def_ss, new_conn_map, new_scope2) ->
   submap old_scope1 old_scope2 ->
   stmt_has_fully_inferred_ground_types s ->
      submap new_scope1 new_scope2
with ExpandBranch_stmts_tmap :
forall (vm : module_graph_vertex_set_p.env) (ss : HiFP.hfstmt_seq)
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
forall (vm : module_graph_vertex_set_p.env) (s : HiFP.hfstmt)
       (old_tmap new_tmap old_scope1 new_scope1 old_scope2 new_scope2 : CEP.t ftype)
       (old_def_ss new_def_ss : HiFP.hfstmt_seq) (old_conn_map new_conn_map : CEP.t def_expr),
   stmt_tmap (old_tmap, old_scope1) s vm = Some (new_tmap, new_scope1) ->
   ExpandBranch_fun s old_def_ss old_conn_map old_scope2 = Some (new_def_ss, new_conn_map, new_scope2) ->
   submap old_scope2 old_scope1 ->
   stmt_has_fully_inferred_ground_types s ->
      submap new_scope2 new_scope1
with ExpandBranch_stmts_tmap :
forall (vm : module_graph_vertex_set_p.env) (ss : HiFP.hfstmt_seq)
       (old_tmap new_tmap old_scope1 new_scope1 old_scope2 new_scope2 : CEP.t ftype)
       (old_def_ss new_def_ss : HiFP.hfstmt_seq) (old_conn_map new_conn_map : CEP.t def_expr),
   stmts_tmap (old_tmap, old_scope1) ss vm = Some (new_tmap, new_scope1) ->
   ExpandBranch_funs ss old_def_ss old_conn_map old_scope2 = Some (new_def_ss, new_conn_map, new_scope2) ->
   submap old_scope2 old_scope1 ->
   stmts_have_fully_inferred_ground_types ss ->
      submap new_scope2 new_scope1.
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

(*
The following lemma is probably not needed.
Lemma ExpandBranch_funs_submap :
forall (ss : HiFP.hfstmt_seq) (old_def_ss : HiFP.hfstmt_seq) (old_conn_map : CEP.t def_expr) (old_scope : CEP.t ftype),
   forall (tmap : CEP.t ftype) (vm : module_graph_vertex_set_p.env),
      submap old_scope tmap ->
      stmts_tmap (tmap, old_scope) ss vm <> None ->
         match ExpandBranch_funs ss old_def_ss old_conn_map old_scope with
         | Some (_, _, new_scope) => submap old_scope new_scope
         | None => True
         end
with ExpandBranch_fun_submap :
forall (s : HiFP.hfstmt) (old_def_ss : HiFP.hfstmt_seq) (old_conn_map : CEP.t def_expr) (old_scope : CEP.t ftype),
   forall (tmap : CEP.t ftype) (vm : module_graph_vertex_set_p.env),
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
forall (ss : HiFP.hfstmt_seq) (tmap scope1 scope2 : CEP.t ftype) (vm : module_graph_vertex_set_p.env),
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
with ExpandBranch_fun_checks_scopes :
forall (s : HiFP.hfstmt) (tmap scope1 scope2 : CEP.t ftype) (vm : module_graph_vertex_set_p.env),
   stmt_has_fully_inferred_ground_types s ->
   tmap_has_fully_inferred_ground_types tmap ->
   submap scope1 tmap ->
   submap scope2 tmap ->
   submap scope1 scope2 ->
      stmt_tmap (tmap, scope1) s vm = None ->
         stmts_tmap (tmap, scope2) (component_stmt_of s) vm <> None ->
            forall (old_def_ss : HiFP.hfstmt_seq) (old_conn_map : CEP.t def_expr) (old_scope : CEP.t ftype),
               submap old_scope scope1 ->
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
      rewrite H7 in H4 ; clear H7.
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
      rewrite H6 in H4 ; clear H6.
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
      assert (submap scope1 tmap_true) by (apply (submap_trans scope1_true) ; apply H8).
      assert (submap scope1 scope2_true) by (apply (submap_trans scope2 _ _ H3), H10).
      specialize (ExpandBranch_funs_checks_scopes ss_false tmap_true scope1 scope2_true vm
                  Hf H7 H11 (proj1 H10) H12)
            with (old_def_ss := true_def_ss) (old_conn_map := old_conn_map) (old_scope := old_scope).
      destruct (stmts_tmap (tmap_true, scope1) ss_false vm) as [[]|] ; first by discriminate H4.
      rewrite (ExpandBranch_funs_checks_scopes Logic.eq_refl H5 H6) //.
    - destruct (stmts_tmap (tmap, scope2) (component_stmts_of ss_true) vm) ; last by contradiction H5.
      specialize (H9 Logic.eq_refl) with (old_def_ss := old_def_ss) (old_conn_map := old_conn_map) (old_scope := old_scope).
      rewrite H9 //.
Qed.

Fixpoint ExpandPort_fun (pp : seq HiFP.hfport) (old_conn_map : CEP.t def_expr) (old_scope : CEP.t ftype) : option (CEP.t def_expr * CEP.t ftype) :=
(* create a map of def_expr for the port sequence pp.
   Out ports need to be assigned value “undefined”;
   in ports do not need to be assigned any value.
   Because types have been lowered already, we can assume
   that all ports have ground types. *)
match pp with
| [::] => Some (old_conn_map, old_scope)
| Finput p t :: pp' =>
    ExpandPort_fun pp' old_conn_map (CEP.add p t old_scope)
| Foutput p t :: pp' =>
    ExpandPort_fun pp' (CEP.add p D_undefined old_conn_map) (CEP.add p t old_scope)
end.

(*
Theorem ExpandBranch_Sem :
   forall (pp : seq HiFP.hfport) (ss : hiFP.hfstmt_seq),
      match ExpandPort_fun pp (CEP.empty def_expr) with
      | Some port_conn_map => match ExpandBranch_funs ss (Qnil ProdVarOrder.T, port_conn_map) with
                  | Some (def_ss, conn_map) =>
                      match Sem (FInmod N0 pp ss)
                      exists vm',
                            Sem_frag_port pp vm'
                         /\ Sem_frag_stmt ...
                  | None => True
                  end.
      | None => True
      end.
*)

Definition helper_connect (v : ProdVarOrder.t) (d : def_expr) (old_ss : option HiFP.hfstmt_seq) : option HiFP.hfstmt_seq :=
(* The helper function adds a connect statement for reference v *)
match old_ss, d with
| None, _ (* propagate earlier error *)
| _, D_undefined => None (* component v is still not connected; error *)
| Some old_ss, D_invalidated => Some (Qrcons old_ss (Sinvalid (Eid v)))
| Some old_ss, D_fexpr e => Some (Qrcons old_ss (Sfcnct (Eid v) e))
end.


Definition ExpandWhens_fun (m : HiFP.hfmodule) : option HiFP.hfmodule :=
(* expand whens in module m *)
match m with
| FInmod v pp ss =>
    match ExpandPort_fun pp (CEP.empty def_expr) (CEP.empty ftype) with
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

(* We want to prove a correctness theorem about ExpandWhens,
namely that the semantics before and after ExpandWhens_fun of a module
are bisimilar.
Conditions: every type is an explicit-width ground type,
and there are no uninferred Resets.
We need these conditions so ExpandBranch_fun works correctly
and there is only one semantic for a module. *)



(* Some useful lemmas:
- The input and output of ExpandBranch_fun contain the same component definitions.

Because the output  *)

Theorem ExpandWhens_correct :
(* The theorem states that ExpandWhens preserves semantics.
   (This requires that ExpandWhens_fun checks the scopes of variables,
   because “Sem m vm ct” will be false if scoping is violated,
   i.e. if components defined within a when statement are used outside. *)
forall m m' : HiFP.hfmodule, module_has_fully_inferred_ground_types m ->
   ExpandWhens_fun m = Some m' ->
      forall (vm : module_graph_vertex_set_p.env) (ct : module_graph_connection_trees_p.env),
         Sem m' vm ct -> Sem m vm ct.
Proof.
intros.
unfold ExpandWhens_fun in H0.
destruct m as [v pp ss|] ; last by discriminate.
destruct (ExpandPort_fun pp (CEP.empty def_expr) (CEP.empty ftype)) as [[port_conn_map port_scope]|] eqn: Hport ; last by discriminate.
destruct (ExpandBranch_funs ss (Qnil ProdVarOrder.T) port_conn_map port_scope) as [[[def_ss conn_map] scope]|] eqn: Hexpand ; last by discriminate.
destruct (CEP.fold helper_connect conn_map (Some (Qnil ProdVarOrder.T))) as [conn_ss|] eqn: Hfold ; last by discriminate.
injection H0 ; clear H0 ; intro.
rewrite -H0 in H1 ; clear H0 m'.
(*unfold module_has_fully_inferred_ground_types in H.
move /andP : H => [Hp Hs].*)
unfold Sem in H1 ; unfold Sem.
destruct (ports_tmap pp vm) as [pmap|] eqn: Hports_tmap ; last by trivial.
destruct (stmts_tmap (pmap, pmap) (Qcat def_ss conn_ss) vm) as [[tmap' scope_map']|] eqn: Htmap' ; last done.
destruct H1.
destruct H1 as [vm'] ; destruct H1 as [ct'].
generalize (ExpandBranch_components ss (Qnil ProdVarOrder.T) port_conn_map port_scope def_ss conn_map scope Hexpand) ;
      intro.
unfold Qcat in H2.
rewrite stmts_tmap_cat H2 in Htmap'.
generalize (stmts_tmap_components vm ss pmap pmap pmap
            (submap_refl pmap) (submap_refl pmap) (submap_refl pmap)) ;
      intro.
generalize (stmts_submap vm ss pmap pmap (submap_refl pmap)) ;
      intro.
generalize (stmts_submap vm (component_stmts_of ss) pmap pmap (submap_refl pmap)) ;
      intro.
destruct (stmts_tmap (pmap, pmap) ss) as [[tmap scope_map]|] eqn: Htmap.
(* To prove the 2nd case, we need that ExpandBranch_fun checks that there are no scoping etc. errors. *)
destruct (stmts_tmap (pmap, pmap) (component_stmts_of ss) vm) as [[tmap_comp scope_map_comp]|] ; last by done.
destruct H3 ; simpl fst in H3 ; simpl snd in H6.
rewrite -H3 in Htmap' ; rewrite -H3 in H5 ; clear H3 tmap_comp.
assert (forall ss : HiFP.hfstmt_seq,
          CEP.fold helper_connect conn_map (Some ss) = Some conn_ss ->
             component_stmts_of conn_ss = component_stmts_of ss).
      intro.
      rewrite CEP.fold_1.
      clear.
      revert ss0 conn_ss.
      generalize (CEP.elements conn_map).
      induction l.
      * unfold List.fold_left.
        intros ; injection H ; intro.
        rewrite H0 ; reflexivity.
      * simpl List.fold_left.
        intros.
        destruct (a.2).
        + contradict H ; clear.
          induction l ; first by unfold List.fold_left ; discriminate.
          simpl List.fold_left ; exact IHl.
        + specialize IHl with (ss0 := (Qrcons ss0 (Sinvalid (Eid a.1))))
                              (conn_ss := conn_ss).
          rewrite IHl //.
          clear.
          induction ss0.
          - unfold Qrcons, component_stmts_of, Qcat.
            by reflexivity.
          - simpl Qrcons ; simpl component_stmts_of.
            rewrite IHss0 //.
        + specialize IHl with (ss0 := (Qrcons ss0 (Sfcnct (Eid (var:=ProdVarOrder.T) a.1) h)))
                              (conn_ss := conn_ss).
          rewrite IHl //.
          clear.
          induction ss0.
          - unfold Qrcons, component_stmts_of, Qcat.
            by reflexivity.
          - simpl Qrcons ; simpl component_stmts_of.
            rewrite IHss0 //.
generalize (H3 (Qnil ProdVarOrder.T) Hfold) ; clear H3 ; intro.
simpl component_stmts_of in H3.
generalize (stmts_tmap_components vm conn_ss tmap scope_map_comp scope_map_comp
            (proj1 H5) (proj1 H5) (submap_refl scope_map_comp)) ;
      intro.
rewrite Htmap' H3 /stmts_tmap /eq_submap /fst /snd in H7.
destruct H7.
rewrite H7 in H0 H1 Htmap' ; clear H7 tmap'.
split ; first by exact H0.
exists vm', ct'.
split ; first by apply H1.
(* Now we have to verify that the module graph after ExpandBranch_funs
is the same as before.
Basically, the module graph vertex set vm only depends on components_of ss = def_ss,
and the connection trees ct only depends on connect statements = conn_ss. *)
destruct H1 as [_ H1].
(* Probably look through ExpandBranch_funs and Sem_frag_stmts in parallel.
We have:
ExpandBranch_funs ss old_def_ss old_conn_map old_scope = Some (def_ss, conn_map, _)
Hfold : CEP.fold helper_connect conn_map (Some (Qnil ProdVarOrder.T)) =
        Some conn_ss

and we have a correspondence
    def_ss_old  <---> vm_old (they contain the same components)
      forall v : ProdVarOrder.T,
         match module_graph_vertex_set_p.find v vm_old with
         | Swire _ newgt
         | ... newgt => CEP.find v def_ss_old = Some (Gtyp newgt)
         end

   conn_map_old <---> ct_old (they contain the same connections)
     forall v : ProdVarOrder.T,
         module_graph_connection_trees_p.find (v, N0) comm_map_old =
         CEP.find v ct_old

We should prove:
Sem_frag_stmts vm_old ct_old (Qcat (components ss) (connections ss)) vm ct

So we need to strengthen Hexpand so we can use this correspondence!
*)

(* For the second goal (where the original stmts_tmap is None),
   we should prove that
   - either the new stmts_tmap also produces None
   - or there is a scope error, so ExpandBranch_funs produces an error.

So I suggest this:
From the fact that stmts_tmap (pmap, pmap) ss = None,
we find the place where the error happened
(through induction over ss).
Then we conclude that
either ExpandBranch_funs ... ss ... = None (for scope errors),
or that stmts_tmap (pmap, pmap) (components_of ss) = None (for other errors).

assert
   (forall (ss : HiFP.hfstmt_seq) (tmap_scope1 tmap_scope2 : CEP.t ftype),
      eq_submap tmap_scope1 tmap_scope2 ->
         stmts_tmap tmap_scope1 ss = None ->
            stmts_tmap tmap_scope2 (components_of ss) <> None ->
               forall (old_def_ss : HiFP.hfstmt_seq) (old_conn_map : module_graph_connection_trees_p.env) (old_scope : CEP.t unit),
                  (forall v : ProdVarOrder.T, CEP.find v (snd tmap_scope1) = None -> CEP.find v old_scope = None) ->
                     ExpandBranch_funs ss old_def_ss old_conn_map old_scope = None).

(ExpandBranch_funs does not verify any conditions on old_def_ss or old_conn_map,
 so the property does not depend on them!)

This should be proven by induction over ss.
*)


* (* In this first goal, we verify that tmap does not contain duplicate identifiers.
     We should be able to prove this because tmap' is basically the same as tmap. *)



(* ExpandBranch_funs determines def_ss and conn_map
   in the same way as Sem determines vm and ct.
   So we should now proceed by induction over pp and ss.

   First, by induction over pp, we should determine vm_ports and ct_ports
   and establish that they remain the same
   (independent of stmts_tmap). *)

(* I see that it is simpler for me to construct tmap
   together with going through the statements in ss. *)

