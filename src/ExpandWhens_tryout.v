From Coq Require Import BinNat ZArith.
From mathcomp Require Import ssreflect ssrbool eqtype seq fintype ssrnat div ssrfun.
From simplssrlib Require Import SsrOrder Var FMaps.
From firrtl Require Import Firrtl Env HiEnv HiFirrtl ModuleGraph_oriented.

(* In this version ExpandBranches_funs does not typecheck anything.
   It is assumed that the modules is correct,
   so only the semantics of correct modules is preserved.
   If the module was incorrect, it may happen that it becomes correct (or its behaviour changes.)
   Also, we try to use the same logic as in stmt_tmap
   to simplify the proof that links stmt_tmap and ExpandBranches_funs. *)

Definition fully_inferred
    (* checks the precondition of ExpandWhens on a type *)
    (gt : fgtyp) (* ground type to be checked *)
:   bool (* result is true iff the type has no implicit width or uninferred reset *)
:=  match gt with
    | Fuint_implicit _
    | Fsint_implicit _
    | Freset => false
    | _ => true
    end.

Definition tmap_has_fully_inferred_ground_types
    (* checks the precondition of ExpandWhens on a type map *)
    (tmap : CEP.t (ftype * HiF.forient)) (* type map to be checked *)
:   Prop (* result is True iff the type map contains
            no aggregate types, no implicit widths, or uninferred resets *)
:=  forall (v : ProdVarOrder.T),
        match CEP.find v tmap return Prop with
        | Some (Gtyp gt, _) => fully_inferred gt
        | Some _ => False
        | None => True
        end.

Fixpoint expr_has_fully_inferred_ground_types
    (* checks the precondition of ExpandWhens on an expression.
       It does not check the type of references. *)
    (expr : HiFP.hfexpr) (* expression to be checked *)
:   bool (* result is true iff the expression contains
            no uninferred resets in constants.
            (Constants never have an implicit width that cannot be made explicit trivially.) *)
:=  match expr with
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
with ref_has_fully_inferred_ground_types
    (* checks the precondition of ExpandWhens on a reference *)
    (ref : HiFP.href) (* reference to be checked *)
:   bool (* result is true if the expressions within the reference contain
            no uninferred resets in constants.
            (Constants never have an implicit width that cannot be made explicit trivially.) *)
:=  match ref with
    | Eid _ => true
    | Esubfield ref' _ => ref_has_fully_inferred_ground_types ref'
    | Esubindex _ _ (* Esubindex requires an array, which is not allowed after lowering types *)
    | Esubaccess _ _ => false (* Esubaccess is not allowed in the ExpandWhens phase *)
    end.

Definition ct_has_fully_inferred_ground_types
    (* checks the precondition of ExpandWhens on the edges of a module graph *)
    (ct : CEP.t def_expr) (* expression set / edge set to be checked *)
:   Prop (* result is True iff the expression set contains
            no aggregate types, no implicit widths, or uninferred resets *)
:=  forall k : CEP.key,
        if CEP.find k ct is Some (D_fexpr e)
        then expr_has_fully_inferred_ground_types e
        else true.

Fixpoint stmt_has_fully_inferred_ground_types
    (* checks the preconditin of ExpandWhens on a statement *)
    (s : HiFP.hfstmt) (* statement to be checked *)
:   bool (* result is true if the statements do not contain
            aggregate types, implicit widths or uninferred resets. *)
:=  match s with
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
with stmts_have_fully_inferred_ground_types
    (* checks the precondition of ExpandWhens on a statement sequence *)
    (ss : HiFP.hfstmt_seq) (* statement sequence to be checked *)
:   bool (* result is true iff the statement sequence does not contain
            aggregate types, implicit widths or uninferred resets *)
:=  match ss with
    | Qnil => true
    | Qcons s ss' =>
            stmt_has_fully_inferred_ground_types s
        &&
            stmts_have_fully_inferred_ground_types ss'
    end.

Definition vm_and_tmap_compatible
    (* checks whether a vertex set vm and a type map tmap are compatible,
       i.e. whether the type map could have been created from vm or a superset of vm. *)
    (vm : CEP.t vertex_type) (* vertex set *)
    (tmap : CEP.t (ftype * HiF.forient)) (* tmap *)
:   Prop
:=  CEP.submap (CEP.map (fun v : vertex_type
                         => match v with
                            | OutPort gt => (Gtyp gt, HiF.Sink)
                            | InPort gt
                            | Node gt => (Gtyp gt, HiF.Source)
                            | Register gt _ _ _
                            | Wire gt => (Gtyp gt, HiF.Duplex)
                            end)
                         vm) tmap.

Definition combine_when_connections
    (* a helper function that takes two connection maps, generated
       by the two branches of a when statement, and combines them
       into one connection map containing suitable multiplexers *)
    (cond           : HiFP.hfexpr)    (* condition under which to decide whether to take the value from true_conn_map *)
    (true_conn_map  : CEP.t def_expr) (* connections made before or in the true branch *)
    (false_conn_map : CEP.t def_expr) (* connections made before or in the false branch *)
:   CEP.t def_expr
:=  CEP.map2 (fun true_expr false_expr : option def_expr =>
                      match true_expr, false_expr with
                      | Some (D_fexpr te), Some (D_fexpr fe) =>
                          if te == fe then true_expr
                          else Some (D_fexpr (Emux cond te fe))
                      | Some D_undefined, _
                      | _, Some D_undefined => Some D_undefined
                      | None, _ => false_expr
                      | _, None => true_expr
                      | Some D_invalidated, _ => false_expr
                      | _, Some D_invalidated => true_expr
                      end)
             true_conn_map false_conn_map.


Fixpoint ExpandBranches_funs
    (* split a statement sequence (possibly containing when
       statements) into a sequence that defines components and a
       connection map.  The output does not contain when statements. *)
    (ss           : HiFP.hfstmt_seq)   (* sequence of statements being translated *)
    (old_comp_ss  : HiFP.hfstmt_seq)   (* component statements of earlier statements in the sequence (used for recursion) *)
    (old_conn_map : CEP.t def_expr)    (* connections made by earlier statements in the sequence (used for recursion) *)
    (old_scope    : CEP.t (ftype * HiF.forient)) (* part of module graph vertices that is currently in scope *)
:   option (HiFP.hfstmt_seq * CEP.t def_expr * CEP.t (ftype * HiF.forient))
    (* old_comp_ss, extended with the component statements in ss,
       old_conn_map, extended with the connection statements in ss,
       and old_scope, extended with the component statements in ss that remain in scope *)
:=  match ss with
    | Qnil => Some (old_comp_ss, old_conn_map, old_scope)
    | Qcons s ss =>
        match ExpandBranch_fun s old_comp_ss old_conn_map old_scope with
        | Some (temp_comp_ss, temp_conn_map, temp_scope) =>
            ExpandBranches_funs ss temp_comp_ss temp_conn_map temp_scope
        | None => None
        end
    end
with ExpandBranch_fun
    (* split a single statement (possibly consisting of a when
       statement) into a sequence that defines components and a
       connection map.  The output does not contain when statements. *)
    (s            : HiFP.hfstmt)       (* a single statement being translated *)
    (old_comp_ss  : HiFP.hfstmt_seq)   (* component statements of earlier statements in the sequence (used for recursion) *)
    (old_conn_map : CEP.t def_expr)    (* connections made by earlier statements in the sequence (used for recursion) *)
    (old_scope    : CEP.t (ftype * HiF.forient)) (* part of module graph vertices that is currently in scope *)
:   option (HiFP.hfstmt_seq * CEP.t def_expr * CEP.t (ftype * HiF.forient))
    (* old_comp_ss, extended with the component statements in s,
       old_conn_map, extended with the connection statements in s,
       and old_scope, extended with the component statements in s that remain in scope *)
:=  match s with
    | Sskip => Some (old_comp_ss, old_conn_map, old_scope)
    | Swire var ft =>
        match CEP.find var old_scope with
        | None => Some (Qrcons old_comp_ss s, CEP.add var D_undefined old_conn_map, CEP.add var (ft, HiF.Duplex) old_scope)
        | Some _ => None
        end
    | Sreg var reg =>
        match CEP.find var old_scope with
        | None => Some (Qrcons old_comp_ss s, CEP.add var (D_fexpr (Eref (Eid var))) old_conn_map, CEP.add var ((type reg), HiF.Duplex) old_scope)
        | Some _ => None
        end
    | Smem var mem => None
    | Sinst var1 var2 => None
    | Snode var expr =>
        match CEP.find var old_scope, type_of_expr expr old_scope with
        | None, Some (exist ft _) =>
            Some (Qrcons old_comp_ss s, old_conn_map, CEP.add var (ft, HiF.Source) old_scope)
        | _, _ => None
        end
    | Sfcnct (Eid var) expr =>
        (* The following code needs to be moved to a helper function
           because ref can be more complex than just (Eid var). *)
        match type_of_ref (Eid var) old_scope with
        | Some (Gtyp gt_ref, HiF.Duplex)
        | Some (Gtyp gt_ref, HiF.Sink) =>
            match type_of_expr expr old_scope with
            | Some (exist (Gtyp gt_expr) _) =>
                if connect_type_compatible false (Gtyp gt_ref) (Gtyp gt_expr) false
                then Some (old_comp_ss, CEP.add var (D_fexpr expr) old_conn_map, old_scope)
                else None
            | _ => None
            end
        | _ => None
        end
    | Sinvalid (Eid var) =>
        match type_of_ref (Eid var) old_scope with
        | Some (_, HiF.Duplex) | Some (_, HiF.Sink) =>
            Some (old_comp_ss, CEP.add var D_invalidated old_conn_map, old_scope)
        | _ => None
        end
    | Swhen cond ss_true ss_false =>
        match type_of_expr cond old_scope, ExpandBranches_funs ss_true old_comp_ss old_conn_map old_scope with
        | Some (exist (Gtyp (Fuint 1)) _), Some (true_comp_ss, true_conn_map, _) =>
            match ExpandBranches_funs ss_false true_comp_ss old_conn_map old_scope with
            | Some (false_comp_ss, false_conn_map, _) =>
                Some (false_comp_ss, combine_when_connections cond true_conn_map false_conn_map, old_scope)
            | _ => None
            end
        | _, _ => None
        end
    | _ => None
    end.

Lemma ExpandBranch_fun_submap :
forall (s : HiFP.hfstmt) (old_comp_ss : HiFP.hfstmt_seq) (old_conn_map : CEP.t def_expr) (old_scope : CEP.t (ftype * HiF.forient)),
    match ExpandBranch_fun s old_comp_ss old_conn_map old_scope with
    | Some (new_comp_ss, new_conn_map, new_scope) =>
            new_comp_ss = Qcat old_comp_ss (component_stmt_of s)
        /\
            subdomain old_conn_map new_conn_map
        /\
            CEP.submap old_scope new_scope
    | None => True
    end
with ExpandBranches_funs_submap :
forall (ss : HiFP.hfstmt_seq) (old_comp_ss : HiFP.hfstmt_seq) (old_conn_map : CEP.t def_expr) (old_scope : CEP.t (ftype * HiF.forient)),
    match ExpandBranches_funs ss old_comp_ss old_conn_map old_scope with
    | Some (new_comp_ss, new_conn_map, new_scope) =>
            new_comp_ss = Qcat old_comp_ss (component_stmts_of ss)
        /\
            subdomain old_conn_map new_conn_map
        /\
            CEP.submap old_scope new_scope
    | None => True
    end.
Proof.
* clear ExpandBranch_fun_submap.
  rename ExpandBranches_funs_submap into IHss.
  intros.
  induction s as [|var ft|var reg|var mem|var1 var2|var expr|ref expr|ref|cond sst ssf] ;
        simpl ; intros.
  + (* Sskip *)
    split.
    - rewrite Qcats0 //.
    split.
    - apply subdomain_refl.
    - apply CEP.Lemmas.submap_refl.
  + (* Swire *)
    destruct (CEP.find var old_scope) eqn: Hvar ; first by trivial.
    split.
    - rewrite -Qcats1 //.
    split.
    - apply subdomain_add.
    - apply (CEP.Lemmas.submap_none_add _ (CEP.Lemmas.submap_refl _)), Hvar.
  + (* Sreg *)
    destruct (CEP.find var old_scope) eqn: Hvar ; first by trivial.
    split.
    - rewrite -Qcats1 //.
    split.
    - apply subdomain_add.
    - apply (CEP.Lemmas.submap_none_add _ (CEP.Lemmas.submap_refl _)), Hvar.
  + (* Smem *)
    trivial.
  + (* Sinst *)
    trivial.
  + (* Snode *)
    destruct (CEP.find var old_scope) eqn: Hvar ; first by trivial.
    destruct (type_of_expr expr old_scope) as [[ft p]|] eqn: Hexpr ; last by trivial.
    split.
    - rewrite -Qcats1 //.
    split.
    - apply subdomain_refl.
    - apply (CEP.Lemmas.submap_none_add _ (CEP.Lemmas.submap_refl _)), Hvar.
  + (* Sfcnct *)
    destruct ref as [var| | |] ; try by trivial.
    destruct (CEP.find var old_scope) as [[[| |] [| | | |]]|] ; try by trivial.
    1,2: destruct (type_of_expr expr old_scope) as [[[| |] _]|] ; try by trivial.
    1,2: destruct (match f with
                   | Fuint _ => match f0 with | Fuint _ | Fuint_implicit _ => true | _ => false end
                   | Fsint _ => match f0 with | Fsint _ | Fsint_implicit _ => true | _ => false end
                   | Fuint_implicit w_tgt => match f0 with | Fuint w_src | Fuint_implicit w_src => w_src <= w_tgt | _ => false end
                   | Fsint_implicit w_tgt => match f0 with | Fsint w_src | Fsint_implicit w_src => w_src <= w_tgt | _ => false end
                   | Fclock => match f0 with | Fclock => true | _ => false end
                   | Freset => false
                   | Fasyncreset => match f0 with | Fasyncreset => true | _ => false end
                   end) ; try by trivial.
    1,2: split ; first by rewrite Qcats0 //.
    1,2: split ; first by apply subdomain_add.
    1,2: by apply CEP.Lemmas.submap_refl.
  + (* Sinvalid *)
    destruct ref as [var| | |] ; try by trivial.
    destruct (CEP.find var old_scope) as [[_ [| | | |]]|] ; try by trivial.
    1,2: split ; first by rewrite Qcats0 //.
    1,2: split ; first by apply subdomain_add.
    1,2: by apply CEP.Lemmas.submap_refl.
  + (* Swhen *)
    destruct (type_of_expr cond old_scope) as [[[[[|[|]]| | | | | |]| |] _]|] ; try by trivial.
    generalize (IHss sst old_comp_ss old_conn_map old_scope) ; intro IHsst.
    destruct (ExpandBranches_funs sst old_comp_ss old_conn_map old_scope) as [[[true_comp_ss true_conn_map] true_scope]|] ; last by trivial.
    specialize (IHss ssf true_comp_ss old_conn_map old_scope) ; rename IHss into IHssf.
    destruct (ExpandBranches_funs ssf true_comp_ss old_conn_map old_scope) as [[[false_comp_ss false_conn_map] false_scope]|] ; last by trivial.
    split.
    - rewrite (proj1 IHssf) (proj1 IHsst) Qcat_assoc //.
    split.
    - intro.
      rewrite /combine_when_connections CEP.Lemmas.map2_1bis //.
      destruct IHsst as [_ [IHsst _]] ; specialize (IHsst k).
      destruct IHssf as [_ [IHssf _]] ; specialize (IHssf k).
      destruct (CEP.find k true_conn_map) as [[]|], (CEP.find k false_conn_map) as [[]|] ;
            try by done.
      destruct (h == h0) ; done.
    - apply CEP.Lemmas.submap_refl.
* clear ExpandBranches_funs_submap.
  rename ExpandBranch_fun_submap into IHs.
  induction ss as [|s ss] ; simpl ; intros.
  + (* Qnil *)
    split.
    - rewrite Qcats0 //.
    split.
    - apply subdomain_refl.
    - apply CEP.Lemmas.submap_refl.
  + (* Qcons *)
    specialize (IHs s old_comp_ss old_conn_map old_scope).
    destruct (ExpandBranch_fun s old_comp_ss old_conn_map old_scope) as [[[temp_comp_ss temp_conn_map] temp_scope]|] ; last by trivial.
    specialize (IHss temp_comp_ss temp_conn_map temp_scope).
    destruct (ExpandBranches_funs ss temp_comp_ss temp_conn_map temp_scope) as [[[new_comp_ss new_conn_map] new_scope]|] ; last by trivial.
    split.
    + rewrite (proj1 IHss) (proj1 IHs) Qcat_assoc //.
    split.
    + apply (subdomain_trans _ _ _ (proj1 (proj2 IHs))), IHss.
    + apply (CEP.Lemmas.submap_trans (proj2 (proj2 IHs))), IHss.
Qed.

Definition convert_to_connect_stmt
    (* convert one entry in a map of connections to a connect statement,
       helper function for CEP.fold *)
    (v : CEP.key) (* key of the connection *)
    (d : def_expr) (* value of the connection *)
    (old_ss : HiFP.hfstmt_seq) (* old sequence of connect statements *)
:   HiFP.hfstmt_seq (* returns old_ss, extended with assigning d to v *)
:=  match d with
    | D_undefined => old_ss
    | D_invalidated => Qcons (Sinvalid (Eid v)) old_ss
    | D_fexpr e => Qcons (Sfcnct (Eid v) e) old_ss
    end.

Definition convert_to_connect_stmts
    (* converts a map of connections to connect statements *)
    (conn_map : CEP.t def_expr) (* map that needs to be converted *)
:   HiFP.hfstmt_seq
:=  CEP.fold convert_to_connect_stmt conn_map (Qnil ProdVarOrder.T).

(*
Lemma ExpandBranch_components :
   forall (ss def_ss : HiFP.hfstmt_seq) (conn_map : CEP.t def_expr) (scope : CEP.t (ftype * HiF.forient))
          (def_ss' : HiFP.hfstmt_seq) (conn_map' : CEP.t def_expr) (scope' : CEP.t (ftype * HiF.forient)),
      ExpandBranches_funs ss def_ss conn_map scope =
          Some (def_ss', conn_map', scope') ->
              def_ss' = Qcat def_ss (component_stmts_of ss)
          /\
              ((forall k : CEP.key, CEP.find k conn_map  <> Some D_undefined) ->
               (forall k : CEP.key, CEP.find k conn_map' <> Some D_undefined))
with ExpandBranch_component :
   forall (s : HiFP.hfstmt) (def_ss : HiFP.hfstmt_seq) (conn_map : CEP.t def_expr) (scope : CEP.t (ftype * HiF.forient))
          (def_ss' : HiFP.hfstmt_seq) (conn_map' : CEP.t def_expr) (scope' : CEP.t (ftype * HiF.forient)),
      ExpandBranch_fun s def_ss conn_map scope =
          Some (def_ss', conn_map', scope') ->
              def_ss' = Qcat def_ss (component_stmt_of s)
          /\
              ((forall k : CEP.key, CEP.find k conn_map  <> Some D_undefined) ->
               (forall k : CEP.key, CEP.find k conn_map' <> Some D_undefined)).
Proof.
Admitted.
*)

(*
This lemma is no longer relevant because every connection map should have the same domain.
Lemma adapt_conn_map_ss :
forall (ss old_comp : HiFP.hfstmt_seq) (old_conn_map_large : CEP.t def_expr) (old_scope : CEP.t (ftype * HiF.forient))
       (old_conn_map_small eb_conn_map_large : CEP.t def_expr) (eb_scope : CEP.t (ftype * HiF.forient)),
        ExpandBranches_funs ss old_comp old_conn_map_large old_scope =
              Some (Qcat old_comp (component_stmts_of ss), eb_conn_map_large, eb_scope)
    ->
        CEP.submap old_conn_map_small old_conn_map_large
    ->
        exists eb_conn_map_small : CEP.t def_expr,
                ExpandBranches_funs ss old_comp old_conn_map_small old_scope =
                     Some (Qcat old_comp (component_stmts_of ss), eb_conn_map_small, eb_scope)
            /\
                CEP.Equal eb_conn_map_large (extend_map_with eb_conn_map_small old_conn_map_large)
with adapt_conn_map_s :
forall (s : HiFP.hfstmt) (old_comp : HiFP.hfstmt_seq) (old_conn_map_large : CEP.t def_expr) (old_scope : CEP.t (ftype * HiF.forient))
       (old_conn_map_small eb_conn_map_large : CEP.t def_expr) (eb_scope : CEP.t (ftype * HiF.forient)),
        ExpandBranch_fun s old_comp old_conn_map_large old_scope =
              Some (Qcat old_comp (component_stmt_of s), eb_conn_map_large, eb_scope)
    ->
        CEP.submap old_conn_map_small old_conn_map_large
    ->
        exists eb_conn_map_small : CEP.t def_expr,
                ExpandBranch_fun s old_comp old_conn_map_small old_scope =
                     Some (Qcat old_comp (component_stmt_of s), eb_conn_map_small, eb_scope)
            /\
                CEP.Equal eb_conn_map_large (extend_map_with eb_conn_map_small old_conn_map_large).
Proof.
* clear adapt_conn_map_ss.
  induction ss as [|s ss]; simpl ; intros.
  + injection H ; clear H ; intros H H' _ ; subst eb_conn_map_large eb_scope.
    exists old_conn_map_small.
    rewrite Qcats0.
    split ; first by reflexivity.
    intro.
    rewrite /extend_map_with CEP.Lemmas.map2_1bis //.
    specialize (H0 y).
    destruct (PVM.find y old_conn_map_small) ; last by reflexivity.
    by rewrite (H0 _ Logic.eq_refl) //.
  + specialize (adapt_conn_map_s s old_comp old_conn_map_large old_scope).
    generalize (ExpandBranch_fun_submap s old_comp old_conn_map_large old_scope) ; intro.
    destruct (ExpandBranch_fun s old_comp old_conn_map_large) as [[[eb_comp eb_conn_map_s] eb_scope_s]|] eqn: Heb_s ; last by discriminate H.
    destruct H1 as [H1' H1] ; subst eb_comp.
    (*generalize (ExpandBranches_funs_submap ss (Qcat old_comp (component_stmt_of s)) eb_conn_map_s eb_scope_s) ;
          intro ; rewrite H in H2 ; destruct H2 as [_ H2].*)
    specialize (adapt_conn_map_s old_conn_map_small) with (1 := Logic.eq_refl) (2 := H0).
    destruct adapt_conn_map_s as [eb_conn_map_small_s adapt_conn_map_s].
    rewrite (proj1 adapt_conn_map_s).
    specialize (IHss (Qcat old_comp (component_stmt_of s)) eb_conn_map_s eb_scope_s eb_conn_map_small_s).
    rewrite H Qcat_assoc in IHss.
    specialize IHss with (1 := Logic.eq_refl).
    assert (CEP.submap eb_conn_map_small_s eb_conn_map_s).
          intro.
          rewrite (proj2 adapt_conn_map_s) /extend_map_with CEP.Lemmas.map2_1bis //.
          destruct (CEP.find k eb_conn_map_small_s) ; done.
    specialize IHss with (1 := H2) ; clear H2.
    destruct IHss as [eb_conn_map_small_s_ss IHss].
    exists eb_conn_map_small_s_ss.
    split.
    - by apply IHss.
    - intro.
      rewrite (proj2 IHss).
      rewrite /extend_map_with CEP.Lemmas.map2_1bis //.
      rewrite /extend_map_with CEP.Lemmas.map2_1bis //.
      generalize (ExpandBranches_funs_submap ss (Qcat old_comp (component_stmt_of s)) eb_conn_map_small_s eb_scope_s) ;
            intro ; rewrite (proj1 IHss) in H2.
      destruct H2 as [_ [H2 _]].
      specialize (H2 y).
      destruct (CEP.find y eb_conn_map_small_s_ss) ; try by done.
      rewrite (proj2 adapt_conn_map_s).
      rewrite /extend_map_with CEP.Lemmas.map2_1bis // H2 //.
* clear adapt_conn_map_s.
  rename adapt_conn_map_ss into IHss.
  induction s as [|var ft|var reg|var mem|var1 var2|var expr|ref expr|ref|cond sst ssf] ;
        simpl ; intros.
  + (* Sskip *)
    injection H ; clear H ; intros H H' _ ; subst eb_conn_map_large eb_scope.
    exists old_conn_map_small.
    rewrite Qcats0.
    split ; first by reflexivity.
    intro.
    rewrite /extend_map_with CEP.Lemmas.map2_1bis //.
    specialize (H0 y).
    destruct (PVM.find y old_conn_map_small) ; last by reflexivity.
    by rewrite (H0 _ Logic.eq_refl) //.
  + (* Swire *)
    destruct (CEP.find var old_scope) ; first by discriminate H.
    injection H ; clear H ; intros H H' _ ; subst eb_conn_map_large eb_scope.
    exists old_conn_map_small.
    split ; first by rewrite Qcats1 //.
    intro.
    rewrite /extend_map_with CEP.Lemmas.map2_1bis //.
    specialize (H0 y).
    destruct (PVM.find y old_conn_map_small) ; last by reflexivity.
    by rewrite (H0 _ Logic.eq_refl) //.
  + (* Sreg *)
    destruct (CEP.find var old_scope) ; first by discriminate H.
    injection H ; clear H ; intros H H' _ ; subst eb_conn_map_large eb_scope.
    exists old_conn_map_small.
    split ; first by rewrite Qcats1 //.
    intro.
    rewrite /extend_map_with CEP.Lemmas.map2_1bis //.
    specialize (H0 y).
    destruct (PVM.find y old_conn_map_small) ; last by reflexivity.
    by rewrite (H0 _ Logic.eq_refl) //.
  + (* Smem *)
    by discriminate H.
  + (* Sinst *)
    by discriminate H.
  + (* Snode *)
    destruct (CEP.find var old_scope) ; first by discriminate H.
    destruct (type_of_expr expr old_scope) as [[ft _]|] ; last by discriminate H.
    injection H ; clear H ; intros H H' _ ; subst eb_conn_map_large eb_scope.
    exists old_conn_map_small.
    split ; first by rewrite Qcats1 //.
    intro.
    rewrite /extend_map_with CEP.Lemmas.map2_1bis //.
    specialize (H0 y).
    destruct (PVM.find y old_conn_map_small) ; last by reflexivity.
    by rewrite (H0 _ Logic.eq_refl) //.
  + (* Sfcnct *)
    destruct ref as [var| | |] ; try by discriminate H.
    injection H ; clear H ; intros H H' _ ; subst eb_conn_map_large eb_scope.
    exists (CEP.add var (D_fexpr expr) old_conn_map_small).
    split ; first by rewrite Qcats0 //.
    intro.
    rewrite /extend_map_with CEP.Lemmas.map2_1bis //.
    destruct (y == var) eqn: Hyvar.
    - rewrite (CEP.Lemmas.find_add_eq Hyvar) (CEP.Lemmas.find_add_eq Hyvar) //.
    - apply negbT in Hyvar ; move /negP : Hyvar => Hyvar.
      rewrite (CEP.Lemmas.find_add_neq Hyvar) (CEP.Lemmas.find_add_neq Hyvar) //.
      specialize (H0 y).
      destruct (PVM.find y old_conn_map_small) ; last by reflexivity.
      by rewrite (H0 _ Logic.eq_refl) //.
  + (* Sinvalid *)
    destruct ref as [var| | |] ; try by discriminate H.
    injection H ; clear H ; intros H H' _ ; subst eb_conn_map_large eb_scope.
    exists (CEP.add var D_invalidated old_conn_map_small).
    split ; first by rewrite Qcats0 //.
    intro.
    rewrite /extend_map_with CEP.Lemmas.map2_1bis //.
    destruct (y == var) eqn: Hyvar.
    - rewrite (CEP.Lemmas.find_add_eq Hyvar) (CEP.Lemmas.find_add_eq Hyvar) //.
    - apply negbT in Hyvar ; move /negP : Hyvar => Hyvar.
      rewrite (CEP.Lemmas.find_add_neq Hyvar) (CEP.Lemmas.find_add_neq Hyvar) //.
      specialize (H0 y).
      destruct (PVM.find y old_conn_map_small) ; last by reflexivity.
      by rewrite (H0 _ Logic.eq_refl) //.
  + (* Swhen *)
    generalize (IHss sst old_comp old_conn_map_large old_scope old_conn_map_small) ; intro IHsst.
    specialize (IHss ssf (Qcat old_comp (component_stmts_of sst)) old_conn_map_large old_scope) ; rename IHss into IHssf.
    generalize (ExpandBranches_funs_submap sst old_comp old_conn_map_large old_scope) ; intro.
    destruct (ExpandBranches_funs sst old_comp old_conn_map_large old_scope) as [[[true_comp_ss true_conn_map_large] true_scope]|] ; last by discriminate H.
    destruct H1 as [H1' H1] ; subst true_comp_ss.
    specialize IHsst with (1 := Logic.eq_refl) (2 := H0).
    destruct IHsst as [eb_conn_map_small_true IHsst].
    (*generalize (ExpandBranches_funs_submap ssf (Qcat old_comp (component_stmts_of sst)) old_conn_map_large old_scope) ; intro.*)
    destruct (ExpandBranches_funs ssf (Qcat old_comp (component_stmts_of sst)) old_conn_map_large old_scope) as [[[false_comp_ss false_conn_map_large] false_scope]|] ;
          last by discriminate H.
    injection H ; clear H ; intros ; subst false_comp_ss eb_conn_map_large eb_scope.
    (*destruct H2 as [H2' H2] ; subst false_comp_ss.*)
    rewrite Qcat_assoc in IHssf.
    specialize IHssf with (1 := Logic.eq_refl) (2 := H0).
    destruct IHssf as [eb_conn_map_small_false IHssf].
    generalize (ExpandBranches_funs_submap sst old_comp old_conn_map_small old_scope) ; intro.
    destruct (ExpandBranches_funs sst old_comp old_conn_map_small old_scope) as [[[true_comp_ss true_conn_map_small] true_scope']|] ;
          last by discriminate (proj1 IHsst).
    destruct H as [H' H] ; subst true_comp_ss.
    injection (proj1 IHsst) ; destruct IHsst as [_ IHsst] ; intros ; subst true_conn_map_small true_scope'.
    generalize (ExpandBranches_funs_submap ssf (Qcat old_comp (component_stmts_of sst))
          old_conn_map_small old_scope) ; intro.
    destruct (ExpandBranches_funs ssf (Qcat old_comp (component_stmts_of sst))
          old_conn_map_small old_scope) as [[[false_comp_ss false_conn_map_small] false_scope']|] ;
          last by discriminate (proj1 IHssf).
    destruct H2 as [H2' H2] ; subst false_comp_ss.
    rewrite Qcat_assoc in IHssf.
    injection (proj1 IHssf) ; destruct IHssf as [_ IHssf] ; intros ; subst false_conn_map_small false_scope'.
    exists (combine_when_connections cond eb_conn_map_small_true eb_conn_map_small_false).
    split ; first by rewrite Qcat_assoc //.
    intro.
    rewrite /combine_when_connections CEP.Lemmas.map2_1bis // (IHsst y).
    rewrite /extend_map_with CEP.Lemmas.map2_1bis //.
    rewrite /extend_map_with CEP.Lemmas.map2_1bis // CEP.Lemmas.map2_1bis //.
    rewrite (IHssf y) /extend_map_with CEP.Lemmas.map2_1bis //.
    destruct (PVM.find y eb_conn_map_small_true) as [[]|] eqn: Hsmall_true ; try done.
    - destruct (PVM.find y eb_conn_map_small_false) as [[]|] eqn: Hsmall_false ; try by done.
      (* Problem of these goals: if one branch has a value and the other branch hasn't.
         Solution should be: then the situation in the large connection maps should be similar,
         i.e. the value in the branch that has a value should be the same, and the value in the branch without a value
         should be copied from the old conn map. 

         The problem of Swhen statements is:
         if one branch sets a value and the other doesn't,
         then the resulting connect statement should keep the old value for the other branch.
         That is why I inserted all ct into the connection map earlier!
         So we might have to insert all these into the connection map again.
         And then hope that the creation of connection statements doesn't upset that too much.
         (Ultimately the creation of connection statements is only called for a complete module,
         so if it doesn't work optimally if called on a module fragment it's not that important.
         Having all connections has another advantage: all earlier connection statements are overwritten.)

         The perfect solution would be to have expressions with holes---if there is a hole,
         fill in the old value. But that would require an extended expression type...
         probably not worth the effort. *)
      admit.
    - destruct (PVM.find y eb_conn_map_small_false) as [[]|] eqn: Hsmall_false ; try by done.
      * destruct (h == h0) ; done.
      * admit.
    - destruct (PVM.find y eb_conn_map_small_false) as [[]|] eqn: Hsmall_false ; try by done.
      * destruct (PVM.find y old_conn_map_large) as [[]|] ; done.
      * admit.
      * admit.
      * destruct (PVM.find y old_conn_map_large) as [[]|] ; try done.
        rewrite eq_refl //.
Admitted.
*)

Definition extend_defined_map_with
    (* Returns map m, except that undefined elements are copied from dflt.
       “undefined” here includes expressions that are assigned an undefined value *)
    (m (* main map whose values are all used *)
     dflt : CEP.t def_expr) (* default: values are used where m does not define an expression *)
:   CEP.t def_expr
:=  CEP.map2 (fun (elm eld : option def_expr)
              => match elm with
                 | Some D_undefined =>
                     match eld with Some _ => eld | None => elm end
                 | None => eld
                 | _ => elm
                 end)
             m dflt.

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
  + by discriminate H0.
  + by discriminate H0.
Qed.

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

Lemma convert_to_connect_stmts_Sem :
(* a lemma that states that convert_to_connect_stmts and Sem_frag_stmts are sort of inverses *)
forall (conn_map : CEP.t def_expr) (vm_old : CEP.t vertex_type) (ct_old : CEP.t def_expr) (vm_new : CEP.t vertex_type) (ct_new : CEP.t def_expr) (tmap: CEP.t (ftype * HiF.forient)),
        tmap_has_fully_inferred_ground_types tmap
    ->
        ct_has_fully_inferred_ground_types conn_map
    ->
        subdomain conn_map ct_old (* perhaps vm_and_ct_compatible vm_old ct_old, but that is not enough *)
    ->
        Sem_frag_stmts vm_old ct_old (convert_to_connect_stmts conn_map) vm_new ct_new tmap
    ->
            CEP.Equal vm_old vm_new
        /\
            CEP.Equal ct_new (extend_defined_map_with conn_map ct_old).
Proof.
intros until 3.
* rewrite /convert_to_connect_stmts CEP.Lemmas.P.fold_spec_right.
  assert (SetoidList.equivlistA (@CEP.Lemmas.O.eqke def_expr)
                                (List.rev (CEP.elements conn_map))
                                (CEP.elements conn_map))
        by (intro ;
            apply (SetoidList.InA_rev (@CEP.Lemmas.O.eqke def_expr))).
  revert H2.
  generalize (CEP.elements_3w conn_map) ; intro.
(*  assert (Heqv_key : RelationClasses.Equivalence (CEP.eq_key (elt:=def_expr))).
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
        exact (RelationClasses.Build_Equivalence (CEP.eq_key_elt (elt:=def_expr)) H H0 H1).*)
  assert (Heqv_key0 : RelationClasses.Equivalence (fun x y : ProdVarOrder.T => x == y)).
        clear.
        assert (forall x y : ProdVarOrder.T, x == y -> y == x)
              by (intros ; rewrite eq_sym //).
        assert (forall x y z : ProdVarOrder.T, x == y -> y == z -> x == z)
              by (intros ; move /eqP : H0 => H0 ; rewrite H0 //).
        exact (RelationClasses.Build_Equivalence (fun x y : ProdVarOrder.T => x == y) (eq_refl (T := ProdVarOrder.T)) H H0).
  (*assert (subdomain (CEP.Lemmas.P.of_list (List.rev (CEP.elements conn_map))) ct_old).
        intro ; specialize (H1 k).
        destruct (CEP.find k ct_old) ; try by trivial.
        rewrite CEP.Lemmas.P.of_list_1b ;
               last by apply (SetoidList.NoDupA_rev (CEP.Lemmas.O.eqk_equiv def_expr) H2).
        rewrite -CEP.Lemmas.P.findA_rev // -CEP.Lemmas.F.elements_o //.
  clear H1 ; rename H3 into H1.*)
  apply SetoidList.NoDupA_rev in H2 ; last by apply (CEP.Lemmas.O.eqk_equiv def_expr).
  revert H0 H1 H2.
  generalize (List.rev (CEP.elements conn_map)) as conn_map_list.
  intro ; revert conn_map_list vm_old ct_old conn_map.
  induction conn_map_list.
  + unfold List.fold_right.
    intros.
    split ; first by apply H4.
    intro.
    apply RelationClasses.Equivalence_Symmetric, SetoidList.equivlistA_nil_eq in H3 ;
          last by exact (CEP.Lemmas.O.eqke_equiv def_expr).
    apply CEP.Lemmas.P.elements_Empty in H3.
    apply CEP.Lemmas.Empty_find with (x := y) in H3.
    simpl Sem_frag_stmts in H4.
    unfold extend_defined_map_with.
    rewrite CEP.Lemmas.map2_1bis // H3.
    symmetry ; apply H4.
  + destruct a as [k v].
    simpl List.fold_right.
    intros until 4.
    (*destruct (List.fold_right (CEP.Lemmas.P.uncurry helper_connect)
                              (Qnil ProdVarOrder.T) conn_map_list) eqn: Hfold ;
          rewrite Hfold // /CEP.Lemmas.P.uncurry /helper_connect /fst /snd.
    rewrite Hfold in IHconn_map_list.*)
    inversion H2 ; clear H4 H5 x l.
    assert (ct_has_fully_inferred_ground_types (CEP.Lemmas.P.of_list conn_map_list)).
          intro.
          generalize (CEP.find_2 (m := CEP.Lemmas.P.of_list conn_map_list) (x := k0)) ; intro.
          destruct (CEP.find k0 (CEP.Lemmas.P.of_list conn_map_list)) as [[]|] ; try done.
          specialize (H4 (D_fexpr h) Logic.eq_refl).
          apply (CEP.Lemmas.P.of_list_1 k0 (D_fexpr h) H7), (SetoidList.InA_cons_tl (k, v)),
                H3, CEP.Lemmas.elements_mapsto_iff, CEP.find_1 in H4.
          specialize (H0 k0) ; by rewrite H4 // in H0.
    assert (subdomain (CEP.Lemmas.P.of_list conn_map_list) ct_old).
          intro.
          specialize (H1 k0).
          destruct (CEP.find k0 ct_old) ; first by trivial.
          apply CEP.Lemmas.not_find_in_iff ; intro.
          apply CEP.Lemmas.elements_in_iff in H5.
          destruct H5 as [elt H5].
          apply CEP.Lemmas.P.of_list_2 in H5 ; last by exact H7.
          apply (SetoidList.InA_cons_tl (k, v)), H3,
                (ex_intro (fun elt
                            => SetoidList.InA (@CEP.Lemmas.O.eqke def_expr)
                                              (k0, elt) (CEP.elements conn_map))),
                CEP.Lemmas.elements_in_iff in H5.
          revert H5.
          by apply CEP.Lemmas.not_find_in_iff, H1.
    assert (CEP.find k conn_map = Some v).
          apply CEP.find_1, CEP.elements_2, H3, SetoidList.InA_cons_hd, CEP.Lemmas.O.eqke_refl.
    assert (CEP.find k (CEP.Lemmas.P.of_list conn_map_list) = None).
          apply CEP.Lemmas.not_find_in_iff.
          contradict H6.
          destruct H6 as [elt H6].
          apply CEP.Lemmas.P.of_list_1, (CEP.Lemmas.P.InA_eqke_eqk v (eqxx k)) in H6 ;
                by assumption.
    destruct v.
    - (* D_undefined *)
      unfold CEP.Lemmas.P.uncurry ; simpl Sem_frag_stmts.
      intro.
      specialize (IHconn_map_list vm_old ct_old (CEP.Lemmas.P.of_list conn_map_list)
                                  H4 H5 H7 (CEP.Lemmas.P.of_list_2 H7) H10).
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
        rewrite Hyk H8 H9.
        specialize (H1 k) ; rewrite H8 in H1.
        by destruct (CEP.find k ct_old) ; by done.
      + destruct (PVM.find y (CEP.Lemmas.P.of_list conn_map_list)) eqn: Hfind_list.
        - specialize (H3 (y, d)).
          destruct H3 as [H3 _].
          rewrite CEP.Lemmas.P.of_list_1b in Hfind_list ; last by apply H7.
          apply SetoidList.findA_NoDupA in Hfind_list ;
                last (by apply H7) ; last by apply Heqv_key0.
          apply SetoidList.InA_cons_tl with (y := (k, D_undefined)) in Hfind_list.
          apply H3, CEP.elements_2, CEP.find_1 in Hfind_list.
          rewrite Hfind_list //.
        - destruct (PVM.find y conn_map) eqn: Hfind_map.
          * apply CEP.find_2, CEP.elements_1, H3, SetoidList.InA_cons in Hfind_map.
            destruct Hfind_map as [Hfind_map|Hfind_map] ;
                  first (by rewrite /CEP.Lemmas.O.eqke /PVM.SE.eq /fst Hyk in Hfind_map ;
                            destruct Hfind_map as [Hfind_map _] ; done).
            rewrite CEP.Lemmas.P.of_list_1b in Hfind_list ; last by exact H7.
            apply (SetoidList.findA_NoDupA Heqv_key0 ProdVarOrder.eq_dec y d H7) in Hfind_map.
            by rewrite Hfind_map // in Hfind_list.
          * by reflexivity.
    - (* D_invalidated *)
      simpl Sem_frag_stmts.
      intro.
      destruct H10 as [vm' [ct' [[H10 H11] H12]]].
      assert (CEP.Equal ct' (CEP.add k D_invalidated ct_old)).
            intro.
            specialize (H k).
            destruct (CEP.find k tmap) as [[[gt| |] ori]|] ; try by contradiction.
            rewrite /size_of_ftype /mkseq in H11 ; simpl in H11.
            rewrite N.add_0_r -surjective_pairing in H11.
            destruct ori ; try by contradiction H11.
            1,2: destruct (y == k) eqn: Hyk.
            * 1,3: rewrite (CEP.Lemmas.find_add_eq Hyk).
              1,2: move /eqP : Hyk => Hyk ; subst y.
              1,2: destruct H11 as [H11 _] ; specialize (H11 0) ; simpl in H11.
              1,2: by rewrite (proj2 H11) //.
            * 1,2: rewrite (CEP.Lemmas.find_add_neq (elimT negP (negbT Hyk))).
              1,2: destruct H11 as [_ H11] ; specialize (H11 y).
              1,2: rewrite mem_seq1 Hyk in H11.
              1,2: symmetry ; by exact H11.
      clear H11 ; rename H13 into H11.
      assert (subdomain (CEP.Lemmas.P.of_list conn_map_list) ct').
            apply subdomain_trans with (1 := H5).
            intro ; specialize (H11 k0).
            destruct (CEP.find k0 ct') ; first by trivial.
            destruct (k0 == k) eqn: Hk0k.
            * by rewrite (CEP.Lemmas.find_add_eq Hk0k) // in H11.
            * by rewrite H11 (CEP.Lemmas.find_add_neq (elimT negP (negbT Hk0k))) //.
      specialize (IHconn_map_list vm' ct' (CEP.Lemmas.P.of_list conn_map_list)
                                  H4 H13 H7 (CEP.Lemmas.P.of_list_2 H7) H12).
      split ; first by apply (CEP.Lemmas.Equal_trans H10), IHconn_map_list.
      apply (CEP.Lemmas.Equal_trans (proj2 IHconn_map_list)).
      intro.
      rewrite /extend_defined_map_with CEP.Lemmas.map2_1bis // (*CEP.Lemmas.P.of_list_1b //. *)
              CEP.Lemmas.map2_1bis // H11.
      destruct (y == k) eqn: Hyk.
      + rewrite (CEP.Lemmas.find_add_eq Hyk).
        move /eqP : Hyk => Hyk ; subst y.
        by rewrite H8 H9 //.
      + rewrite (CEP.Lemmas.find_add_neq (elimT negP (negbT Hyk))).
        destruct (PVM.find y (CEP.Lemmas.P.of_list conn_map_list)) eqn: Hfind_list.
        - rewrite CEP.Lemmas.P.of_list_1b // in Hfind_list.
          apply SetoidList.findA_NoDupA in Hfind_list ;
                last (by exact H7) ;
                last (by exact Heqv_key0).
          apply (SetoidList.InA_cons_tl (k, D_invalidated)), H3, CEP.elements_2, CEP.find_1 in Hfind_list.
          by rewrite Hfind_list //.
        - destruct (PVM.find y conn_map) eqn: Hfind_map ; last by reflexivity.
          apply CEP.find_2, CEP.elements_1, H3 in Hfind_map.
          inversion Hfind_map ; subst y0 l.
          * destruct H15 as [H15 _].
            by rewrite /PVM.SE.eq /fst Hyk // in H15.
          * apply CEP.Lemmas.P.of_list_1 in H15 ; last by exact H7.
            apply CEP.find_1 in H15.
            by rewrite Hfind_list // in H15.
    - (* Expressions should not be very difficult... *)
      simpl Sem_frag_stmts.
      intro.
      destruct H10 as [vm' [ct' [H10 H12]]].
      assert (CEP.Equal vm_old vm' /\ CEP.Equal ct' (CEP.add k (D_fexpr h) ct_old)).
            destruct h eqn: Hexpr ; split ; try (by apply H10) ; destruct H10 as [_ H11].
            1-7: intro.
            5:   specialize (H0 k) ; rewrite H8 in H0 ;
                 apply (expr_preserves_fully_inferred tmap H) in H0.
            1-7: specialize (H k).
            1-7: destruct (CEP.find k tmap) as [[[gt| |] ori]|] ; try by contradiction.
            1-7: rewrite /size_of_ftype /mkseq in H11 ; simpl in H11.
            1-7: rewrite N.add_0_r -surjective_pairing in H11.
            1-7: destruct ori ; try by contradiction H11.
            (* From now we have to distinguish references *)
            1-12: destruct (y == k) eqn: Hyk.
            * 1,3,5,7,9,11,13,15,17,19,21,23: rewrite (CEP.Lemmas.find_add_eq Hyk).
              1-12: move /eqP : Hyk => Hyk ; subst y.
              1-2: destruct f ;
                   destruct H11 as [_ [H11 _]] ; specialize (H11 0) ; simpl in H11 ; by rewrite (proj2 H11) //.
              1-2: destruct u, (type_of_expr h0 tmap) as [[[[]| |] _]|] ; try (by contradiction H11) ;
                   destruct H11 as [_ [H11 _]] ; specialize (H11 0) ; simpl in H11 ; by rewrite (proj2 H11) //.
              1-2: destruct e, (type_of_expr h0 tmap) as [[[[]| |] _]|] ; try (by contradiction H11) ;
                   try (destruct (n0 <= n < n1) ; try by contradiction H11) ;
                   try (destruct (n <= n0) ; try by contradiction H11) ;
                   destruct H11 as [_ [H11 _]] ; specialize (H11 0) ; simpl in H11 ; by rewrite (proj2 H11) //.
              1-2: destruct e, (type_of_expr h0_1 tmap) as [[[[]| |] _]|] ; try (by contradiction H11) ;
                      destruct (type_of_expr h0_2 tmap) as [[[[]| |] _]|] ; try (by contradiction H11) ;
                   destruct H11 as [_ [H11 _]] ; specialize (H11 0) ; simpl in H11 ; by rewrite (proj2 H11) //.
              1-2: simpl in H0.
              1-2: destruct (type_of_expr h0_1 tmap) as [[[[[|[|]]| | | | | |]| |] ]|] ; try (by contradiction H11) ;
                   destruct (type_of_expr h0_2 tmap) as [[[[]| |] p2]|] ; try (by contradiction H11) ;
                   destruct (type_of_expr h0_3 tmap) as [[[[]| |] p3]|] ; try (by contradiction H11) ;
                   rewrite /ftype_mux /sval /proj2_sig in H0, H11 ; simpl in H0, H11 ;
                   try (destruct (n == n0) ; try (by contradiction H11) ;
                        destruct (ftype_mux' f0 p2 f1 p3) as [[]|] ; by contradiction) ;
                   try (destruct (ffield_mux' f0 p2 f1 p3) as [[]|] ; by contradiction) ;
                   destruct H11 as [_ [H11 _]] ; specialize (H11 0) ; simpl in H11 ; by rewrite (proj2 H11) //.
              1-2: destruct (type_of_expr h0_1 tmap) as [[[[[|[|]]| | | | | |]| |] ]|] ; try (by contradiction H11) ;
                   destruct (type_of_expr h0_2 tmap) as [[[[]| |] p2]|] ; try (by contradiction H11) ;
                   rewrite /ftype_mux /sval /proj2_sig in H11 ; simpl in H11 ;
                   try (by contradiction (proj2 H11)) ;
                   destruct H11 as [_ [H11 _]] ; specialize (H11 0) ; simpl in H11 ; by rewrite (proj2 H11) //.
            * 1-12: rewrite (CEP.Lemmas.find_add_neq (elimT negP (negbT Hyk))).
              1-2: destruct f ;
                   destruct H11 as [_ [_ H11]] ; specialize (H11 y) ; rewrite mem_seq1 Hyk in H11 ; symmetry ; by exact H11.
              1-2: destruct u, (type_of_expr h0 tmap) as [[[[]| |] _]|] ; try (by contradiction H11) ;
                   destruct H11 as [_ [_ H11]] ; specialize (H11 y) ; rewrite mem_seq1 Hyk in H11 ; symmetry ; by exact H11.
              1-2: destruct e, (type_of_expr h0 tmap) as [[[[]| |] _]|] ; try (by contradiction H11) ;
                   try (destruct (n0 <= n < n1) ; try by contradiction H11) ;
                   try (destruct (n <= n0) ; try by contradiction H11) ;
                   destruct H11 as [_ [_ H11]] ; specialize (H11 y) ; rewrite mem_seq1 Hyk in H11 ; symmetry ; by exact H11.
              1-2: destruct e, (type_of_expr h0_1 tmap) as [[[[]| |] _]|] ; try (by contradiction H11) ;
                      destruct (type_of_expr h0_2 tmap) as [[[[]| |] _]|] ; try (by contradiction H11) ;
                   destruct H11 as [_ [_ H11]] ; specialize (H11 y) ; rewrite mem_seq1 Hyk in H11 ; symmetry ; by exact H11.
              1-2: simpl in H0.
              1-2: destruct (type_of_expr h0_1 tmap) as [[[[[|[|]]| | | | | |]| |] ]|] ; try (by contradiction H11) ;
                   destruct (type_of_expr h0_2 tmap) as [[[[]| |] p2]|] ; try (by contradiction H11) ;
                   destruct (type_of_expr h0_3 tmap) as [[[[]| |] p3]|] ; try (by contradiction H11) ;
                   rewrite /ftype_mux /sval /proj2_sig in H0, H11 ; simpl in H0, H11 ;
                   try (destruct (n == n0) ; try (by contradiction H11) ;
                        destruct (ftype_mux' f0 p2 f1 p3) as [[]|] ; by contradiction) ;
                   try (destruct (ffield_mux' f0 p2 f1 p3) as [[]|] ; by contradiction) ;
                   destruct H11 as [_ [_ H11]] ; specialize (H11 y) ; rewrite mem_seq1 Hyk in H11 ; symmetry ; by exact H11.
              1-2: destruct (type_of_expr h0_1 tmap) as [[[[[|[|]]| | | | | |]| |] ]|] ; try (by contradiction H11) ;
                   destruct (type_of_expr h0_2 tmap) as [[[[]| |] p2]|] ; try (by contradiction H11) ;
                   rewrite /ftype_mux /sval /proj2_sig in H11 ; simpl in H11 ;
                   try (by contradiction (proj2 H11)) ;
                   destruct H11 as [_ [_ H11]] ; specialize (H11 y) ; rewrite mem_seq1 Hyk in H11 ; symmetry ; by exact H11.
            (* Now two goals for references: *)
            1,2: destruct (list_lhs_ref_p h0 tmap) as [[[|ic [|]] [[| |] [| | | |]]]|]; try (by contradiction H11) ;
                       destruct H11 as [_ H11] ;
                       try by discriminate (proj1 H11).
            1-4: destruct (y == k) eqn: Hyk.
            * 1,3,5,7: rewrite (CEP.Lemmas.find_add_eq Hyk).
              1-4: move /eqP : Hyk => Hyk ; subst y.
              1-4: destruct H11 as [H11 _].
              1-4: move /andP : H11 => [/andP [_ /eqP H11] _].
              1-4: by exact H11.
            * 1-4: rewrite (CEP.Lemmas.find_add_neq (elimT negP (negbT Hyk))).
              1-4: destruct (y == ic) eqn: Hyic.
              + 1,3,5,7: destruct H11 as [H11 _].
                1-4: move /eqP : Hyic => Hyic ; rewrite -Hyic (eq_sym k) Hyk orFb in H11.
                1-4: move /andP : H11 => [_ /eqP H11].
                1-4: by exact H11.
              + 1-4: destruct H11 as [_ H11].
                1-4: specialize (H11 y).
                1-4: rewrite mem_seq1 Hyk mem_seq1 Hyic orFb in H11.
                1-4: by symmetry ; exact H11.
      clear H10 ; destruct H11 as [H10 H11].
      assert (subdomain (CEP.Lemmas.P.of_list conn_map_list) ct').
            apply subdomain_trans with (1 := H5).
            intro ; specialize (H11 k0).
            destruct (CEP.find k0 ct') ; first by trivial.
            destruct (k0 == k) eqn: Hk0k.
            * by rewrite (CEP.Lemmas.find_add_eq Hk0k) // in H11.
            * by rewrite H11 (CEP.Lemmas.find_add_neq (elimT negP (negbT Hk0k))) //.
      specialize (IHconn_map_list vm' ct' (CEP.Lemmas.P.of_list conn_map_list)
                                  H4 H13 H7 (CEP.Lemmas.P.of_list_2 H7) H12).
      split ; first by apply (CEP.Lemmas.Equal_trans H10), IHconn_map_list.
      apply (CEP.Lemmas.Equal_trans (proj2 IHconn_map_list)).
      intro.
      rewrite /extend_defined_map_with CEP.Lemmas.map2_1bis // (*CEP.Lemmas.P.of_list_1b //. *)
              CEP.Lemmas.map2_1bis // H11.
      destruct (y == k) eqn: Hyk.
      + rewrite (CEP.Lemmas.find_add_eq Hyk).
        move /eqP : Hyk => Hyk ; subst y.
        rewrite H8 H9 //.
      + rewrite (CEP.Lemmas.find_add_neq (elimT negP (negbT Hyk))).
        destruct (PVM.find y (CEP.Lemmas.P.of_list conn_map_list)) eqn: Hfind_list.
        - rewrite CEP.Lemmas.P.of_list_1b // in Hfind_list.
          apply SetoidList.findA_NoDupA in Hfind_list ;
                last (by exact H7) ;
                last (by exact Heqv_key0).
          apply (SetoidList.InA_cons_tl (k, D_fexpr h)), H3, CEP.elements_2, CEP.find_1 in Hfind_list.
          by rewrite Hfind_list //.
        - destruct (PVM.find y conn_map) eqn: Hfind_map ; last by reflexivity.
          apply CEP.find_2, CEP.elements_1, H3 in Hfind_map.
          inversion Hfind_map ; subst y0 l.
          * destruct H15 as [H15 _].
            by rewrite /PVM.SE.eq /fst Hyk // in H15.
          * apply CEP.Lemmas.P.of_list_1 in H15 ; last by exact H7.
            apply CEP.find_1 in H15.
            by rewrite Hfind_list // in H15.
Qed.

Lemma extend_defined_map_with_refl {ct1 ct2 : CEP.t def_expr} :
        CEP.Equal ct1 ct2
    ->
            CEP.Equal ct1 (extend_defined_map_with ct1 ct2)
        /\
            CEP.Equal ct1 (extend_defined_map_with ct2 ct1)
        /\
            CEP.Equal ct1 (extend_defined_map_with ct2 ct2).
Proof.
intro ; split ; last split.
1-3: intro ; specialize (H y).
1-3: rewrite /extend_defined_map_with CEP.Lemmas.map2_1bis // H.
1-3: destruct (PVM.find y ct2) as [[]|] ; by done.
Qed.

Definition conn_map_covers_scope
    (* checks whether the connection map assigns a value to everything in the scope *)
    (conn_map : CEP.t def_expr)
    (scope : CEP.t (ftype * HiF.forient))
:   Prop
:=  forall k : CEP.key,
        match CEP.find k scope with
        | Some (_, HiF.Sink)
        | Some (_, HiF.Duplex) => CEP.find k conn_map <> None
        | Some _ => CEP.find k conn_map = None
        | _ => True
        end.

Definition scope_sub_connmap
    (* checks whether the scope and connmap fit together:
       connmap contains a value for everything in scope (may be undefined),
       and types are correct *)
    (scope : CEP.t (ftype * HiF.forient))
    (connmap : CEP.t def_expr)
    (tmap : CEP.t (ftype * HiF.forient)) (* tmap is used to check types *)
:   Prop
:=  forall k : CEP.key,
        match CEP.find k scope with
        | Some (ft_tgt, HiF.Sink) | Some (ft_tgt, HiF.Duplex) =>
            match CEP.find k connmap with
            | None => False
            | Some (D_fexpr expr) =>
                match type_of_expr expr tmap with
                | Some (exist ft_src _) => connect_type_compatible false ft_tgt ft_src false
                | _ => False
                end
            | _ => True
            end
        | _ => True
        end.

(* We use the following maps to describe the graph and its values:
old_scope : CEP.t (ftype * HiF.forient) -- assigns a type to every assignable/usable component
old_connmap : CEP.t def_expr -- contains new connections
old_ct : CEP.t def_expr -- contains a value for every assignable component
old_vm : CEP.t vertex_type -- contains the components in the current graph
old_tmap : CEP.t (ftype * HiF.forient) -- contains all components in the final graph

Relations between the maps are:
- scope_sub_connmap scope connmap: connmap assigns to each Sink/Duplex in scope, and the types fit
- connmap_sub_ct connmap ct: connmap is a subdomain of ct, and the types fit
- ct_sub_vm ct vm: ct assigns a value exactly to every assignable component
- vm_sub_tmap vm tmap: tmap types every component in vm correctly

Type correctness is judged according to type_of_expr expr tmap

(Additionally, old_comp contains exactly the definitions of components in vm.)
*)

Definition connmap_sub_ct
    (* check whether the connmap and ct fit together:
       connmap does not assign anything to components outside ct,
       and types are correct *)
    (connmap : CEP.t def_expr)
    (ct : CEP.t def_expr)
    (tmap : CEP.t (ftype * HiF.forient))
:   Prop
:=  forall k : CEP.key,
        match CEP.find k connmap, CEP.find k ct with
        | Some (D_fexpr cm_expr), Some (D_fexpr ct_expr) =>
            match type_of_expr cm_expr tmap, type_of_expr ct_expr tmap with
            | Some (exist (Gtyp cm_gt) _), Some (exist (Gtyp ct_gt) _) => connect_type_compatible false (Gtyp cm_gt) (Gtyp ct_gt) false
            | _, _ => False
            end
       | Some _, None => False
       | _, _ => True
       end.

Definition ct_sub_vm
    (* check whether the ct/edges and vm/vertices of the module graph fit together:
       ct assigns a value exactly to every writable component in vm,
       and types are correct *)
    (ct : CEP.t def_expr)
    (vm : CEP.t vertex_type)
    (tmap : CEP.t (ftype * HiF.forient))
:   Prop
:=  forall k : CEP.key,
        match CEP.find k ct, CEP.find k vm with
        | Some (D_fexpr expr), Some (OutPort gt)
        | Some (D_fexpr expr), Some (Register gt _ _ _)
        | Some (D_fexpr expr), Some (Wire gt) =>
            match type_of_expr expr tmap with
            | Some (exist (Gtyp gt_expr) _) => connect_type_compatible false (Gtyp gt) (Gtyp gt_expr) false
            | _ => False
            end
        | Some _, Some (OutPort _)
        | Some _, Some (Register _ _ _ _)
        | Some _, Some (Wire _)
        | None, Some (InPort _)
        | None, Some (Node _)
        | None, None => True
        | _, _ => False
        end.

Definition vm_sub_tmap
    (* check whether the vm/vertices of the module graph and the tmap fit together:
       tmap defines their types and orientation correctly *)
    (vm : CEP.t vertex_type)
    (tmap : CEP.t (ftype * HiF.forient))
:   Prop
:=  forall k : CEP.key,
        match CEP.find k vm with
        | Some (OutPort  gt      ) => CEP.find k tmap = Some (Gtyp gt, HiF.Sink)
        | Some (InPort   gt      )
        | Some (Node     gt      ) => CEP.find k tmap = Some (Gtyp gt, HiF.Source)
        | Some (Register gt _ _ _)
        | Some (Wire     gt      ) => CEP.find k tmap = Some (Gtyp gt, HiF.Duplex)
        | None => True
        end.

Definition scope_sub_vm
    (* checks whether scope and vm fit together. This separate check is required
       because connmap and ct do not preserve information about read-only components. *)
    (scope : CEP.t (ftype * HiF.forient))
    (vm : CEP.t vertex_type)
:   Prop
:=  forall k : CEP.key,
        match CEP.find k scope, CEP.find k vm with
        | Some (ft, HiF.Source), Some (Node     gt      )
        | Some (ft, HiF.Source), Some (InPort   gt      )
        | Some (ft, HiF.Sink  ), Some (OutPort  gt      )
        | Some (ft, HiF.Duplex), Some (Register gt _ _ _)
        | Some (ft, HiF.Duplex), Some (Wire     gt      ) =>
            ft = Gtyp gt
        | Some _, _ => False
        | None, _ => True
        end.

Definition all_fit_together
    (scope : CEP.t (ftype * HiF.forient))
    (connmap : CEP.t def_expr)
    (ct : CEP.t def_expr)
    (vm : CEP.t vertex_type)
    (tmap : CEP.t (ftype * HiF.forient))
:   Prop
:=      scope_sub_connmap scope connmap tmap
    /\
        connmap_sub_ct connmap ct tmap
    /\
        ct_sub_vm ct vm tmap
    /\
        vm_sub_tmap vm tmap
    /\
        scope_sub_vm scope vm.

Lemma scope_vm_submap_tmap :
forall (scope : CEP.t (ftype * HiF.forient)) (vm : CEP.t vertex_type) (tmap : CEP.t (ftype * HiF.forient)),
        scope_sub_vm scope vm
    ->
        vm_sub_tmap vm tmap
    ->
        CEP.submap scope tmap.
Proof.
intros scope vm tmap Hsc_vm Hvm_tm k v Hsc.
destruct v as [ft ori].
specialize (Hsc_vm k) ; specialize (Hvm_tm k).
rewrite Hsc in Hsc_vm.
destruct ori, (CEP.find k vm) as [[gt|gt|gt|gt|gt]|].
all: try (by contradiction Hsc_vm).
all: rewrite Hsc_vm.
all: by exact Hvm_tm.
Qed.

Lemma aft_scope_submap_tmap :
forall (scope : CEP.t (ftype * HiF.forient)) (connmap : CEP.t def_expr)
       (ct : CEP.t def_expr) (vm : CEP.t vertex_type) (tmap : CEP.t (ftype * HiF.forient)),
        all_fit_together scope connmap ct vm tmap
    ->
        CEP.submap scope tmap.
Proof.
intros scope connmap ct vm tmap Haft.
destruct Haft as [_ [_ [_ [Hvm_tm Hsc_vm]]]].
exact (scope_vm_submap_tmap scope vm tmap Hsc_vm Hvm_tm).
Qed.

Lemma Sem_frag_stmts_connect :
forall (tmap : CEP.t (ftype * HiF.forient)),
        tmap_has_fully_inferred_ground_types tmap
    ->
        forall (connmap ct : CEP.t def_expr) (vm : CEP.t vertex_type),
                all_fit_together (CEP.empty (ftype * HiF.forient)) connmap ct vm tmap
            ->
                Sem_frag_stmts vm ct (convert_to_connect_stmts connmap) vm (extend_defined_map_with connmap ct) tmap.
Proof.
(*
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
  assert (Heqv_key : RelationClasses.Equivalence (CEP.eq_key (elt:=def_expr))).
        clear.
        assert (forall x : CEP.key * def_expr, CEP.eq_key x x)
              by (intro ; rewrite /CEP.eq_key /CEP.SE.eq eq_refl //).
        assert (forall x y : CEP.key * def_expr, CEP.eq_key x y -> CEP.eq_key y x)
              by (intros ; rewrite /CEP.eq_key /CEP.SE.eq eq_sym H0 //).
        assert (forall x y z : CEP.key * def_expr, CEP.eq_key x y -> CEP.eq_key y z -> CEP.eq_key x z)
              by (intros ; rewrite H1 H2 /CEP.eq_key /CEP.SE.eq //).
        exact (RelationClasses.Build_Equivalence (CEP.eq_key (elt:=def_expr)) H H0 H1). *)
intros tmap Htm_inf connmap ct vm Haft.
unfold convert_to_connect_stmts.
rewrite (CEP.Lemmas.P.fold_spec_right).
assert (forall (x : PVM.key) (e : def_expr),
       PVM.MapsTo x e connmap <->
       SetoidList.InA (@CEP.Lemmas.O.eqke def_expr) (x, e) (List.rev (PVM.elements connmap))).
      intros ; split ; intro.
      * apply SetoidList.InA_rev, CEP.elements_1, H.
      * apply CEP.elements_2, SetoidList.InA_rev, H.
revert H.
generalize (SetoidList.NoDupA_rev (CEP.Lemmas.O.eqk_equiv def_expr) (CEP.elements_3w connmap)).
(*assert (stmts_can_connect tmap (Qnil ProdVarOrder.T)) by rewrite /stmts_can_connect //.
revert H3.
generalize (Qnil ProdVarOrder.T) as old_conn_stmts.*)
replace (@List.rev (prod PVM.SE.t def_expr)
            (@CEP.elements def_expr connmap)) with (@List.rev (prod PVM.key def_expr)
            (@CEP.elements def_expr connmap)) by reflexivity.
generalize (List.rev (CEP.elements connmap)) as connmap_list ; intro.
revert connmap ct Haft.
induction connmap_list.
* simpl ; intros connmap ct Haft Hnodup Hlist.
  split ; first by apply CEP.Lemmas.F.Equal_refl.
  (* use H4 to show that conn_map is empty.
     Additionally need to do something about old_conn_stmts *)
  intro ; specialize (Hlist y).
  rewrite /extend_defined_map_with CEP.Lemmas.map2_1bis //.
  generalize (CEP.find_2 (m := connmap) (x := y)) ; intro Hfind_2.
  destruct (CEP.find y connmap) as [e|] ; last by reflexivity.
  specialize (Hfind_2 _ Logic.eq_refl).
  apply Hlist in Hfind_2.
  by inversion Hfind_2.
* simpl ; intros connmap ct Haft Hnodup Hlist.
  destruct a as [k el].
  generalize (proj1 (proj2 Haft) k) ; intro Hk_in_ct.
  specialize (proj2 (Hlist k el) (SetoidList.InA_cons_hd connmap_list (conj (eqxx (k, el).1) (erefl (k, el).2)))) ;
        intro Hfind_k.
  apply CEP.find_1 in Hfind_k.
  rewrite Hfind_k in Hk_in_ct.
  assert (Hmove_k: el <> D_undefined -> CEP.Equal (extend_defined_map_with (CEP.remove k connmap) (CEP.add k el ct)) (extend_defined_map_with connmap ct)).
        intros Hel y.
        rewrite /extend_defined_map_with CEP.Lemmas.map2_1bis // CEP.Lemmas.map2_1bis //.
        destruct (y == k) eqn: Hyk.
        - rewrite (CEP.Lemmas.remove_eq_o connmap) ; last by rewrite /PVM.SE.eq eq_sym Hyk.
          rewrite (CEP.Lemmas.find_add_eq Hyk) (elimT eqP Hyk) Hfind_k //.
          destruct el ; first (by contradiction Hel) ; by reflexivity.
        - rewrite (CEP.Lemmas.remove_neq_o connmap) ; last by rewrite /PVM.SE.eq eq_sym ; apply (elimT negP (negbT Hyk)).
          by rewrite (CEP.Lemmas.find_add_neq (elimT negP (negbT Hyk))) //.
  rewrite {1}/CEP.Lemmas.P.uncurry /fst /snd {1}/convert_to_connect_stmt.
  destruct el.
  + (* D_undefined *)
    apply Sem_frag_stmts_Equal with (vm_old1 := vm) (ct_old1 := ct) (vm_new1 := vm) (ct_new1 := extend_defined_map_with (CEP.remove k connmap) ct) (tmap1 := tmap) ;
        try by apply CEP.Lemmas.Equal_refl.
    - intro y.
      rewrite /extend_defined_map_with CEP.Lemmas.map2_1bis // /extend_defined_map_with CEP.Lemmas.map2_1bis //.
      destruct (y == k) eqn: Hyk.
      * rewrite (CEP.Lemmas.remove_eq_o connmap) ; last by rewrite /PVM.SE.eq eq_sym Hyk.
        rewrite (elimT eqP Hyk) Hfind_k //.
        destruct (CEP.find k ct) ; first (by reflexivity) ; last (by contradiction Hk_in_ct).
      * rewrite (CEP.Lemmas.remove_neq_o connmap) // /PVM.SE.eq eq_sym.
        by apply (elimT negP (negbT Hyk)).
    - apply IHconnmap_list ; admit.
  + (* D_invalidated: Sinvalid *)
    specialize (Hmove_k (fun H => False_ind False (eq_ind D_invalidated (fun e => if e is D_invalidated then True else False) I D_undefined H))).
    simpl Sem_frag_stmts.
    exists vm, (CEP.add k D_invalidated ct).
    split.
    - split ; first by apply CEP.Lemmas.F.Equal_refl.
      generalize (proj1 (proj2 (proj2 Haft)) k) ; intro Hk_in_vm.
      destruct (CEP.find k ct) eqn: Hfind_in_ct ; last by contradiction Hk_in_ct ; clear Hk_in_ct.
      generalize (proj1 (proj2 (proj2 (proj2 Haft))) k) ; intro Hk_in_tmap.
      destruct d, (CEP.find k vm) as [[gt|gt|gt|gt|gt]|] ; try (by contradiction Hk_in_vm).
      1-9: rewrite Hk_in_tmap /size_of_ftype /mkseq ; simpl map ; rewrite N.add_0_r -surjective_pairing.
      1-9: split ;
            last by (intro v0 ; rewrite mem_seq1 ;
                     destruct (v0 == k) eqn: Hvk ; first (by trivial) ;
                     rewrite (CEP.Lemmas.find_add_neq (elimT negP (negbT Hvk))) //).
      1-9: intro n ; destruct n ; simpl ;
            last by (assert (H: (@List.length CEP.key [::] <= n)%coq_nat) by apply Nat.le_0_l ;
                     apply List.nth_error_None in H ;
                     rewrite H //).
      1-9: split ;
            last by rewrite (CEP.Lemmas.find_add_eq (eq_refl k)) //.
      1-9: by rewrite Hfind_in_ct //.
    - apply (Sem_frag_stmts_Equal _ vm _ (CEP.add k D_invalidated ct) _
                                    vm _ (extend_defined_map_with (CEP.remove k connmap) (CEP.add k D_invalidated ct)) _ tmap) ;
            try (by apply CEP.Lemmas.Equal_refl) ;
            first (by apply Hmove_k).
      apply IHconnmap_list.
      * split.
        + intro k0.
          rewrite CEP.Lemmas.empty_o //.
        split.
        + intro k0.
          destruct (k == k0) eqn: Hkk0.
          + by rewrite CEP.Lemmas.remove_eq_o //.
          + apply negbT in Hkk0.
            move /negP : Hkk0 => Hkk0.
            generalize (proj1 (proj2 Haft) k0) ; intro Hk0_in_ct.
            by rewrite (CEP.Lemmas.remove_neq_o connmap Hkk0) (CEP.Lemmas.find_add_neq) //
                       /PVM.SE.eq eq_sym //.
        split.
        + intro k0.
          destruct (k0 == k) eqn: Hk0k.
          - rewrite (CEP.Lemmas.find_add_eq Hk0k) (elimT eqP Hk0k).
            generalize (proj1 (proj2 (proj2 Haft)) k) ; intro Hk_in_vm.
            destruct (CEP.find k ct) eqn: Hfind_in_ct ; last by contradiction Hk_in_ct ; clear Hk_in_ct.
            destruct d ; try exact Hk_in_vm.
            destruct (CEP.find k vm) as [[]|] ; try contradiction Hk_in_vm ; by trivial.
          - generalize (proj1 (proj2 (proj2 Haft)) k0) ; intro Hk0_in_vm.
            by rewrite (CEP.Lemmas.find_add_neq (elimT negP (negbT Hk0k))) //.
        split.
        + by apply Haft.
        + intro k0.
          rewrite CEP.Lemmas.empty_o //.
      * inversion Hnodup ; by assumption.
      * intros x e ; specialize (Hlist x e).
        split.
        + intro Hmapsto ; apply CEP.Lemmas.remove_mapsto_iff in Hmapsto.
          rewrite /PVM.SE.eq eq_sym in Hmapsto.
          destruct Hlist as [Hlist _].
          specialize (Hlist (proj2 Hmapsto)).
          inversion Hlist ; subst l y ; last by assumption.
          rewrite /CEP.Lemmas.O.eqke /PVM.SE.eq /fst in H0.
          destruct Hmapsto as [Hmapsto _].
          rewrite (proj1 H0) // in Hmapsto.
        + intro Hin ; destruct (k == x) eqn: Hkx.
          - move /eqP : Hkx => Hkx ; subst x.
            inversion Hnodup ; subst x l.
            contradict H1.
            apply CEP.Lemmas.O.InA_eqke_eqk, (SetoidList.InA_eqA (@CEP.Lemmas.O.eqk_equiv def_expr)) with (y := (k, D_invalidated)) in Hin ;
                  first by exact Hin.
            by rewrite /CEP.Lemmas.O.eqk /PVM.SE.eq eq_refl //.
          - move /negP : Hkx => Hkx.
            by apply (CEP.remove_2 Hkx), Hlist, SetoidList.InA_cons_tl, Hin.
  + (* D_fexpr: Sfcnct *)
    admit.
(*
    simpl Sem_frag_stmts.
    exists vm, (CEP.add k (D_fexpr h) ct_old).
    split.
    - destruct h ; split ; try by apply CEP.Lemmas.F.Equal_refl.
      1-6: destruct (CEP.find k tmap) as [[[gt_tgt| |] [| | | |]]|] ; try (by discriminate H5) ;
                 rewrite /size_of_ftype /mkseq ; simpl map ; rewrite N.add_0_r -surjective_pairing.
      1-12: simpl foldr.
      1-2: destruct (type_of_expr (Econst ProdVarOrder.T f b) tmap) as [[[gt_src| |] _]|] ; try (by discriminate H5).
      3-4: destruct (type_of_expr (Ecast u h) tmap) as [[[gt_src| |] _]|] ; try (by discriminate H5).
      5-6: destruct (type_of_expr (Eprim_unop e h) tmap) as [[[gt_src| |] _]|] ; try (by discriminate H5).
      7-8: destruct (type_of_expr (Eprim_binop e h1 h2) tmap) as [[[gt_src| |] _]|] ; try (by discriminate H5).
      9-10: destruct (type_of_expr (Emux h1 h2 h3) tmap) as [[[gt_src| |] _]|] ; try (by discriminate H5).
      11-12: destruct (type_of_expr (Evalidif h1 h2) tmap) as [[[gt_src| |] _]|] ; try (by discriminate H5).
      1-12: split ; first by exact H5.
      1-12: simpl ; split ;
            last by (intro ; rewrite mem_seq1 ;
                     destruct (v0 == k) eqn: Hvk ; first (by trivial) ;
                     rewrite (CEP.Lemmas.find_add_neq (elimT negP (negbT Hvk))) //).
      1-12: intro ; destruct n ; simpl ;
            last by (assert ((@List.length CEP.key [::] <= n)%coq_nat) by apply Nat.le_0_l ;
                     apply List.nth_error_None in H8 ;
                     rewrite H8 //).
      1-12: split ;
            last by rewrite (CEP.Lemmas.find_add_eq (eq_refl k)) //.
      1-12: specialize (H2 k) ; rewrite H6 in H2.
      1-12: by destruct (CEP.find k ct_old) ; done.
      (* What remains is a reference *)
      destruct (CEP.find k tmap) as [[[gt_tgt| |] [| | | |]]|] ;
                 try (by discriminate H5) ;
                 rewrite /size_of_ftype /mkseq ; simpl map.
      1,2: rewrite N.add_0_r -surjective_pairing.
      1,2: simpl foldr ; simpl type_of_expr in H5.
      1,2: generalize (list_lhs_ref_p_type tmap h) ; intro.
      1,2: generalize (list_lhs_ref_p_size tmap h) ; intro.
      1-2: destruct (type_of_ref h tmap) as [[type_ft [| | | |]]|] ;
                try by discriminate H5.
      1-4: destruct (list_lhs_ref_p h tmap) as [[lst_src [ft_src ori_src]]|] eqn: Hlist ;
                last by contradiction H8.
      1-4: injection H8 ; clear H8 ; intros ; subst type_ft ori_src.
      1-4: destruct ft_src as [[| | | | | |]| |] ; 
          simpl in H5 ;
          try (by discriminate H5) ;
          try (by destruct (make_ftype_explicit ft_src) ;
                  discriminate H5) ;
          try (by destruct (make_ffield_explicit f) ;
                  discriminate H5).
      1-28: simpl ; split ;
             first by (exact H5).
      1-28: destruct lst_src as [|ic [|]] ; try by discriminate H9.
      1-28: split ;
             last by (intro v0 ; rewrite mem_seq1 mem_seq1 ;
                      destruct ((v0 == k) || (v0 == ic)) eqn: Hv0k ; first (by trivial) ;
                      apply negbT in Hv0k ;
                      rewrite negb_or in Hv0k ;
                      move /andP : Hv0k => [/negP Hv0k _] ;
                      rewrite (CEP.Lemmas.find_add_neq Hv0k) //).
      1-28: specialize (H2 k) ; destruct (CEP.find k ct_old) ;
                  last by rewrite H6 // in H2.
      1-28: rewrite (CEP.Lemmas.find_add_eq (eq_refl k)) eq_refl andbT.
      1-28: destruct (k == ic) eqn: Hkic ; first by done.
      1-28: rewrite eq_sym in Hkic ;
            rewrite (CEP.Lemmas.find_add_neq (elimT negP (negbT Hkic))) eq_refl //.
    - apply (Sem_frag_stmts_Equal _ vm _ (CEP.add k (D_fexpr h) ct_old) _
                                    vm _ (extend_defined_map_with (CEP.remove k conn_map) (CEP.add k (D_fexpr h) ct_old)) _ tmap) ;
            try (by apply CEP.Lemmas.Equal_refl) ;
            first (by apply Hmove_k).
      apply IHconn_map_list.
      * intro ; specialize (H k0).
        destruct (k == k0) eqn: Hkk0.
        + by rewrite CEP.Lemmas.remove_eq_o //.
        + rewrite CEP.Lemmas.remove_neq_o // /PVM.SE.eq.
          apply (elimT negP (negbT Hkk0)).
      * trivial.
      * intro ; specialize (H2 k0).
        destruct (k0 == k) eqn: Hkk0.
        + by rewrite CEP.Lemmas.find_add_eq //.
        + move /negP : Hkk0 => Hkk0.
          rewrite (CEP.Lemmas.find_add_neq Hkk0).
          rewrite eq_sym in Hkk0.
          by rewrite (CEP.Lemmas.remove_neq_o _ Hkk0) //.
      * inversion H3 ; by assumption.
      * intros ; specialize (H4 x e).
        split ; intro.
        + apply CEP.Lemmas.remove_mapsto_iff in H8.
          rewrite /PVM.SE.eq eq_sym in H8.
          destruct H4 as [H4 _].
          specialize (H4 (proj2 H8)).
          inversion H4 ; subst l y ; last by assumption.
          rewrite /CEP.Lemmas.O.eqke /PVM.SE.eq /fst in H10.
          destruct H8 as [H8 _].
          rewrite (proj1 H10) // in H8.
        + destruct (k == x) eqn: Hkx.
          - move /eqP : Hkx => Hkx ; subst x.
            inversion H3 ; subst x l.
            contradict H11.
            apply CEP.Lemmas.O.InA_eqke_eqk, (SetoidList.InA_eqA (@CEP.Lemmas.O.eqk_equiv def_expr)) with (y := (k, D_fexpr h)) in H8 ;
                  try by exact H8.
            rewrite /CEP.Lemmas.O.eqk /PVM.SE.eq eq_refl //.
          - move /negP : Hkx => Hkx.
            by apply (CEP.remove_2 Hkx), H4, SetoidList.InA_cons_tl, H8. *)
Admitted.

Lemma ExpandWhens_correct_simple :
(* The simple, non-recursive cases of the correctness lemma. *)
forall (vm_for_tmap : CEP.t vertex_type) (tmap : CEP.t (ftype * HiF.forient)),
        tmap_has_fully_inferred_ground_types tmap
    ->
        vm_sub_tmap vm_for_tmap tmap
    ->
        forall s : HiFP.hfstmt,
                stmt_has_fully_inferred_ground_types s
            ->
                if s is Swhen _ _ _ then True
                else forall (old_scope : CEP.t (ftype * HiF.forient)) (old_connmap : CEP.t def_expr)
                       (old_ct : CEP.t def_expr) (old_vm : CEP.t vertex_type) (old_tmap: CEP.t (ftype * HiF.forient))
                       (tm_tmap tm_scope : CEP.t (ftype * HiF.forient))
                       (old_comp : HiFP.hfstmt_seq) (eb_connmap : CEP.t def_expr)
                       (sf_vm : CEP.t vertex_type) (sf_ct : CEP.t def_expr),
                            all_fit_together old_scope old_connmap old_ct old_vm old_tmap
                        ->
                            stmt_tmap (old_tmap, old_scope) s vm_for_tmap = Some (tm_tmap, tm_scope)
                        ->
                            ExpandBranch_fun s old_comp old_connmap old_scope =
                            Some (Qcat old_comp (component_stmt_of s), eb_connmap, tm_scope)
                        ->
                            Sem_frag_stmts old_vm old_ct (Qcat (component_stmt_of s)
                                           (convert_to_connect_stmts eb_connmap))
                                           sf_vm sf_ct tmap
                        ->
                            scope_sub_vm tm_tmap vm_for_tmap (* perhaps not needed here *)
                        ->
                                Sem_frag_stmt old_vm old_ct s sf_vm sf_ct tmap
                            /\
                                all_fit_together tm_scope eb_connmap sf_ct sf_vm tm_tmap.
Proof.
Admitted.

Lemma stmts_tmap_and_ExpandBranches_funs :
forall (ss : HiFP.hfstmt_seq) (old_scope : CEP.t (ftype * HiF.forient)) (old_connmap : CEP.t def_expr)
       (old_tmap : CEP.t (ftype * HiF.forient))
       (vm_for_tmap : CEP.t vertex_type) (tm_tmap tm_scope : CEP.t (ftype * HiF.forient))
       (old_comp: HiFP.hfstmt_seq) (eb_connmap : CEP.t def_expr) (eb_scope : CEP.t (ftype * HiF.forient)),
        tmap_has_fully_inferred_ground_types old_tmap
    ->
        CEP.submap old_scope old_tmap
    ->
        stmts_have_fully_inferred_ground_types ss
    ->
        stmts_tmap (old_tmap, old_scope) ss vm_for_tmap = Some (tm_tmap, tm_scope)
    ->
        ExpandBranches_funs ss old_comp old_connmap old_scope =
                            Some (Qcat old_comp (component_stmts_of ss), eb_connmap, eb_scope)
    ->
        tm_scope = eb_scope
with stmt_tmap_and_ExpandBranch_fun :
forall (s : HiFP.hfstmt) (old_scope : CEP.t (ftype * HiF.forient)) (old_connmap : CEP.t def_expr)
       (old_tmap : CEP.t (ftype * HiF.forient))
       (vm_for_tmap : CEP.t vertex_type) (tm_tmap tm_scope : CEP.t (ftype * HiF.forient))
       (old_comp: HiFP.hfstmt_seq) (eb_connmap : CEP.t def_expr) (eb_scope : CEP.t (ftype * HiF.forient)),
        tmap_has_fully_inferred_ground_types old_tmap
    ->
        CEP.submap old_scope old_tmap
    ->
        stmt_has_fully_inferred_ground_types s
    ->
        stmt_tmap (old_tmap, old_scope) s vm_for_tmap = Some (tm_tmap, tm_scope)
    ->
        ExpandBranch_fun s old_comp old_connmap old_scope =
                            Some (Qcat old_comp (component_stmt_of s), eb_connmap, eb_scope)
    ->
        tm_scope = eb_scope.
Proof.
* clear stmts_tmap_and_ExpandBranches_funs.
  rename stmt_tmap_and_ExpandBranch_fun into IHs.
  induction ss as [|s ss] ; simpl ; intros old_scope old_connmap old_tmap vm_for_tmap tm_tmap tm_scope old_comp eb_connmap eb_scope Htm_inf Hsc_tm Hss_inf Hst Heb.
  + injection Hst ; clear Hst ; intros ; subst tm_tmap tm_scope.
    rewrite Qcats0 in Heb.
    injection Heb ; clear Heb ; intros ; subst eb_connmap eb_scope.
    by reflexivity.
  + specialize (IHs s old_scope old_connmap old_tmap vm_for_tmap).
    move /andP : Hss_inf => [Hs_inf Hss_inf].
    generalize (stmt_tmap_preserves_fully_inferred vm_for_tmap old_tmap old_scope s Hs_inf Htm_inf Hsc_tm) ; intro Htm_s_inf.
    generalize (stmt_submap vm_for_tmap s old_tmap old_scope Hsc_tm) ; intro Hsc_tm_s.
    destruct (stmt_tmap (old_tmap, old_scope) s vm_for_tmap) as [[tm_tmap_s tm_scope_s]|] ;
          last by discriminate Hst.
    specialize (IHs tm_tmap_s tm_scope_s old_comp) with (1 := Htm_inf) (2 := Hsc_tm) (3 := Hs_inf) (4 := Logic.eq_refl).
    generalize (ExpandBranch_fun_submap s old_comp old_connmap old_scope) ; intro Heb_s.
    destruct (ExpandBranch_fun s old_comp old_connmap old_scope) as [[[eb_comp_s eb_connmap_s] eb_scope_s]|] ;
          last by discriminate Heb.
    destruct Heb_s as [H Heb_s] ; subst eb_comp_s.
    specialize IHs with (1 := Logic.eq_refl).
    subst eb_scope_s.
    rewrite -Qcat_assoc in Heb.
    exact (IHss tm_scope_s eb_connmap_s tm_tmap_s vm_for_tmap tm_tmap tm_scope
                     (Qcat old_comp (component_stmt_of s)) eb_connmap eb_scope Htm_s_inf (proj1 Hsc_tm_s) Hss_inf Hst Heb).
* clear stmt_tmap_and_ExpandBranch_fun.
  induction s as [|var ft|var reg|var mem|var1 var2|var expr|ref expr|ref|cond sst ssf] ; simpl ; intros old_scope old_connmap old_tmap vm_for_tmap tm_tmap tm_scope old_comp eb_connmap eb_scope Htm_inf Hsc_tm Hs_inf Hst Heb.
  + (* Sskip *)
    injection Hst ; clear Hst ; intros ; subst tm_tmap tm_scope.
    rewrite Qcats0 in Heb ; injection Heb ; clear Heb ; intros ; subst eb_connmap eb_scope.
    by reflexivity.
  + (* Swire *)
    destruct ft as [gt| |] ; try by discriminate Hs_inf.
    destruct (CEP.find var old_tmap) ; first by discriminate Hst.
    generalize (fully_inferred_does_not_change gt var vm_for_tmap Hs_inf) ; intro.
    destruct (code_type_find_vm_widths (Gtyp gt) var vm_for_tmap) as [[[gt'| |] _]|] ;
          last (by discriminate Hst) ;
          try (by contradiction H) ;
          subst gt'.
    injection Hst ; clear Hst ; intros ; subst tm_tmap tm_scope.
    destruct (CEP.find var old_scope) ; first by discriminate Heb.
    rewrite Qcats1 in Heb.
    injection Heb ; clear Heb ; intros ; subst eb_connmap eb_scope.
    by reflexivity.
  + (* Sreg should be similar to Swire *)
    destruct (type reg) as [gt| |] ; try by discriminate Hs_inf.
    destruct (CEP.find var old_tmap) ; first by discriminate Hst.
    destruct (type_of_expr (clock reg) old_scope) as [_|] ; last by discriminate Hst.
    destruct (reset reg) as [|rst_sig rst_val] ; last first.
    1,2: move /andP : Hs_inf => [_ Hs_inf].
    1,2: generalize (fully_inferred_does_not_change gt var vm_for_tmap Hs_inf) ; intro.
    1,2: destruct (code_type_find_vm_widths (Gtyp gt) var vm_for_tmap) as [[[gt'| |] _]|] ;
          last (by discriminate Hst) ;
          try (by contradiction H) ;
          subst gt'.
    destruct (type_of_expr rst_sig old_scope) as [[[[[|[|]]| | | | | |]| |] _]|] ; try by discriminate Hst.
    1: destruct (type_of_expr rst_val (CEP.add var (Gtyp gt, HiF.Duplex) old_scope)) as [_|] ; last by discriminate Hst.
    2: destruct (type_of_expr rst_val old_scope) as [_|] ; last by discriminate Hst.
    1-3: injection Hst ; clear Hst ; intros ; subst tm_tmap tm_scope.
    1-3: destruct (CEP.find var old_scope) ; first by discriminate Heb.
    1-3: rewrite Qcats1 in Heb.
    1-3: injection Heb ; clear Heb ; intros ; subst eb_connmap eb_scope.
    1-3: by reflexivity.
  + (* Smem *)
    by discriminate Hst.
  + (* Sinst *)
    by discriminate Hst.
  + (* Snode *)
    destruct (CEP.find var old_tmap) ; first by discriminate Hst.
    (*generalize (type_of_expr_submap expr old_scope old_tmap Hsc_tm) ; intro Hexpr.*)
    destruct (type_of_expr expr old_scope) as [[ft p]|] ; last by discriminate Hst.
    injection Hst ; clear Hst ; intros ; subst tm_tmap tm_scope.
    destruct (CEP.find var old_scope) ; first by discriminate Heb.
    rewrite (*Hexpr*) Qcats1 in Heb.
    injection Heb ; clear Heb ; intros ; subst eb_connmap eb_scope.
    by reflexivity.
  + (* Sfcnct *)
    destruct ref as [var| | |] ; try by discriminate Heb.
    simpl type_of_ref in Hst.
    (*generalize (type_of_expr_submap expr old_scope old_tmap Hsc_tm) ; intro Hexpr.
    specialize (Hsc_tm var).*)
    destruct (CEP.find var old_scope) as [[[gt| |] [| | | |]]|] ;
          (*last (by discriminate Hst) ;
          specialize Hsc_tm with (1 := Logic.eq_refl) ;
          rewrite Hsc_tm in Heb ;*)
          try by discriminate Heb.
    1,2: destruct (type_of_expr expr old_scope) as [[[gt_expr| |] p]|] ;
          (*last (by discriminate Hst) ;
          rewrite Hexpr in Heb ;*)
          try by discriminate Heb.
    1,2: injection Hst ; clear Hst ; intros ; subst tm_tmap tm_scope.
    1,2: destruct (match gt with
                   | Fuint _ => match gt_expr with | Fuint _ | Fuint_implicit _ => true | _ => false end
                   | Fsint _ => match gt_expr with | Fsint _ | Fsint_implicit _ => true | _ => false end
                   | Fuint_implicit w_tgt => match gt_expr with | Fuint w_src | Fuint_implicit w_src => w_src <= w_tgt | _ => false end
                   | Fsint_implicit w_tgt => match gt_expr with | Fsint w_src | Fsint_implicit w_src => w_src <= w_tgt | _ => false end
                   | Fclock => match gt_expr with | Fclock => true | _ => false end
                   | Freset => false
                   | Fasyncreset => match gt_expr with | Fasyncreset => true | _ => false end
                   end) ; last by discriminate Heb.
    1,2: rewrite Qcats0 in Heb.
    1,2: injection Heb ; clear Heb ; intros ; subst eb_connmap eb_scope.
    1,2: by reflexivity.
  + (* Sinvalid *)
    destruct ref as [var| | |] ; try by discriminate Heb.
    simpl type_of_ref in Hst.
    (*specialize (Hsc_tm var).*)
    destruct (CEP.find var old_scope) as [[ft [| | | |]]|] ;
          (*last (by discriminate Hst) ;
          specialize Hsc_tm with (1 := Logic.eq_refl) ;
          rewrite Hsc_tm in Heb ;*)
          try by discriminate Heb.
    1,2: injection Hst ; clear Hst ; intros ; subst tm_tmap tm_scope.
    1,2: rewrite Qcats0 in Heb.
    1,2: injection Heb ; clear Heb ; intros ; subst eb_connmap eb_scope.
    1,2: by reflexivity.
  + (* Swhen *)
    move /andP : Hs_inf => [/andP [_ Hsst_inf] Hssf_inf].
    (*generalize (type_of_expr_submap cond old_scope old_tmap Hsc_tm) ; intro Hcond.*)
    destruct (type_of_expr cond old_scope) as [[[[[|[|]]| | | | | |]| |] (*p*)_]|] ;
          (*last (by discriminate Hst) ;
          rewrite Hcond in Heb ;*)
          try by discriminate Heb.
    (*clear p Hcond.*)
    (* destruct stmts_tmap in both branches: *)
    destruct (stmts_tmap (old_tmap, old_scope) sst vm_for_tmap) as [[tm_tmap_t tm_scope_t]|] ; last by discriminate Hst.
    destruct (stmts_tmap (tm_tmap_t, old_scope) ssf vm_for_tmap) as [[tm_tmap_f tm_scope_f]|] ; last by discriminate Hst.
    injection Hst ; clear Hst ; intros ; subst tm_tmap_f tm_scope.
    (* destruct ExpandBranches_funs in both branches: *)
    generalize (ExpandBranches_funs_submap sst old_comp old_connmap old_scope) ; intro Heb_t.
    destruct (ExpandBranches_funs sst old_comp old_connmap old_scope) as [[[eb_comp_t eb_connmap_t] eb_scope_t]|] ;
          last by discriminate Heb.
    destruct Heb_t as [Heb_t' Heb_t] ; subst eb_comp_t.
    generalize (ExpandBranches_funs_submap ssf (Qcat old_comp (component_stmts_of sst)) old_connmap old_scope) ; intro Heb_f.
    destruct (ExpandBranches_funs ssf (Qcat old_comp (component_stmts_of sst)) old_connmap old_scope) as [[[eb_comp_f eb_connmap_f] eb_scope_f]|] ;
          last by discriminate Heb.
    destruct Heb_f as [Heb_f' Heb_f] ; subst eb_comp_f.
    rewrite Qcat_assoc in Heb.
    injection Heb ; clear Heb ; intros ; subst eb_connmap eb_scope.
    by reflexivity.
Qed.

Lemma ExpandBranches_funs_and_Sem_frag_stmts :
forall (vm_for_tmap : CEP.t vertex_type) (tmap : CEP.t (ftype * HiF.forient)),
        tmap_has_fully_inferred_ground_types tmap
    ->
        vm_sub_tmap vm_for_tmap tmap
    ->
        forall (ss : HiFP.hfstmt_seq)
               (old_tmap old_scope tm_tmap tm_scope : CEP.t (ftype * HiF.forient))
               (old_comp : HiFP.hfstmt_seq) (old_connmap : CEP.t def_expr)
               (eb_connmap : CEP.t def_expr) (eb_scope : CEP.t (ftype * HiF.forient))
               (old_vm : CEP.t vertex_type) (old_ct : CEP.t def_expr) (vm_comp : CEP.t vertex_type) (ct_comp : CEP.t def_expr),
                stmts_have_fully_inferred_ground_types ss
            ->
                CEP.submap old_scope old_tmap
            ->
                stmts_tmap (old_tmap, old_scope) ss vm_for_tmap = Some (tm_tmap, tm_scope)
            ->
                scope_sub_vm tm_tmap vm_for_tmap
            ->
                ExpandBranches_funs ss old_comp old_connmap old_scope = Some (Qcat old_comp (component_stmts_of ss), eb_connmap, eb_scope)
            ->
                Sem_frag_stmts old_vm old_ct (component_stmts_of ss) vm_comp ct_comp tmap
            ->
                all_fit_together old_scope old_connmap old_ct old_vm old_tmap
            ->
                all_fit_together eb_scope eb_connmap ct_comp vm_comp tm_tmap
with ExpandBranch_fun_and_Sem_frag_stmt :
forall (vm_for_tmap : CEP.t vertex_type) (tmap : CEP.t (ftype * HiF.forient)),
        tmap_has_fully_inferred_ground_types tmap
    ->
        vm_sub_tmap vm_for_tmap tmap
    ->
        forall (s : HiFP.hfstmt)
               (old_tmap old_scope tm_tmap tm_scope : CEP.t (ftype * HiF.forient))
               (old_comp : HiFP.hfstmt_seq) (old_connmap : CEP.t def_expr)
               (eb_connmap : CEP.t def_expr) (eb_scope : CEP.t (ftype * HiF.forient))
               (old_vm : CEP.t vertex_type) (old_ct : CEP.t def_expr) (vm_comp : CEP.t vertex_type) (ct_comp : CEP.t def_expr),
                stmt_has_fully_inferred_ground_types s
            ->
                CEP.submap old_scope old_tmap
            ->
                stmt_tmap (old_tmap, old_scope) s vm_for_tmap = Some (tm_tmap, tm_scope)
            ->
                scope_sub_vm tm_tmap vm_for_tmap
            ->
                ExpandBranch_fun s old_comp old_connmap old_scope = Some (Qcat old_comp (component_stmt_of s), eb_connmap, eb_scope)
            ->
                Sem_frag_stmts old_vm old_ct (component_stmt_of s) vm_comp ct_comp tmap
            ->
                all_fit_together old_scope old_connmap old_ct old_vm old_tmap
            ->
                all_fit_together eb_scope eb_connmap ct_comp vm_comp tm_tmap.
Proof.
* clear ExpandBranches_funs_and_Sem_frag_stmts.
  intros vm_for_tmap tmap Htm_inf Hvm_sub_tm.
  induction ss as [|s ss] ; simpl ; intros old_tmap old_scope tm_tmap tm_scope old_comp old_connmap eb_connmap eb_scope old_vm old_ct vm_comp ct_comp Hss_inf Hsc_sub_tm Hst Htm_sub_vm Heb Hsf Haft.
  + admit.
  + rename ExpandBranch_fun_and_Sem_frag_stmt into IHs ;
    move /andP : Hss_inf => Hss_inf.
    specialize (IHs vm_for_tmap tmap Htm_inf Hvm_sub_tm s old_tmap old_scope)
               with (old_comp := old_comp) (old_connmap := old_connmap) (old_vm := old_vm) (old_ct := old_ct) (1 := proj1 Hss_inf) (2 := Hsc_sub_tm).
    (* stmt_tmap *)
    generalize (stmt_submap vm_for_tmap s old_tmap old_scope Hsc_sub_tm) ; intro Htm_s.
    specialize (stmt_tmap_and_ExpandBranch_fun s old_scope old_connmap old_tmap vm_for_tmap)
               with (2 := Hsc_sub_tm) (3 := proj1 Hss_inf) ; intro Htm_eb.
    destruct (stmt_tmap (old_tmap, old_scope) s vm_for_tmap) as [[tm_tmap_s tm_scope_s]|] ; last by discriminate Hst.
    specialize (Htm_eb tm_tmap_s tm_scope_s old_comp) with (2 := Logic.eq_refl).
    specialize IHs with (1 := Logic.eq_refl).
    specialize IHss with (1 := proj2 Hss_inf) (2 := proj1 Htm_s) (3 := Hst) (4 := Htm_sub_vm).
    generalize (stmts_submap vm_for_tmap ss tm_tmap_s tm_scope_s (proj1 Htm_s)) ; intro Htm_ss.
    rewrite Hst in Htm_ss.
    assert (Htm_s_sub_vm: scope_sub_vm tm_tmap_s vm_for_tmap).
          destruct Htm_ss as [_ [Htm_ss _]].
          intro k ; specialize (Htm_ss k) ; specialize (Htm_sub_vm k).
          destruct (CEP.find k tm_tmap_s) as [[ft ori]|] ; last by trivial.
          specialize Htm_ss with (1 := Logic.eq_refl).
          rewrite Htm_ss // in Htm_sub_vm.
    specialize IHs with (1 := Htm_s_sub_vm) ; clear Htm_s_sub_vm.
    assert (Htm_tm_inf: tmap_has_fully_inferred_ground_types tm_tmap_s).
          destruct Htm_ss as [_ [Htm_ss _]].
          intro k ; specialize (Htm_ss k) ; specialize (Htm_sub_vm k) ; specialize (Hvm_sub_tm k) ; specialize (Htm_inf k).
          destruct (CEP.find k tm_tmap_s) as [[ft ori]|] ; last by trivial.
          specialize Htm_ss with (1 := Logic.eq_refl).
          rewrite Htm_ss in Htm_sub_vm.
          destruct ori ; try (by contradiction Htm_sub_vm) ;
                destruct (CEP.find k vm_for_tmap) as [[gt|gt|gt|gt|gt]|] ;
                try (by contradiction Htm_sub_vm) ;
                subst ft ;
                rewrite Hvm_sub_tm // in Htm_inf.
    assert (Hold_tm_inf: tmap_has_fully_inferred_ground_types old_tmap).
          destruct Htm_s as [_ [Htm_s _]].
          intro k ; specialize (Htm_s k) ; specialize (Htm_tm_inf k).
          destruct (CEP.find k old_tmap) as [[ft ori]|] ; last by trivial.
          specialize Htm_s with (1 := Logic.eq_refl).
          rewrite Htm_s // in Htm_tm_inf.
    specialize Htm_eb with (1 := Hold_tm_inf).
    clear Hst.
    (* ExpandBranch_fun *)
    generalize (ExpandBranch_fun_submap s old_comp old_connmap old_scope) ; intro Heb_s.
    destruct (ExpandBranch_fun s old_comp old_connmap old_scope) as [[[eb_comp_s eb_connmap_s] eb_scope_s]|] ; last by discriminate Heb.
    destruct Heb_s as [Heb_s' Heb_s] ; subst eb_comp_s.
    specialize Htm_eb with (1 := Logic.eq_refl).
    subst eb_scope_s.
    specialize IHs with (1 := Logic.eq_refl).
    specialize (IHss (Qcat old_comp (component_stmt_of s)) eb_connmap_s).
    generalize (ExpandBranches_funs_submap ss (Qcat old_comp (component_stmt_of s)) eb_connmap_s tm_scope_s) ; intro Heb_ss.
    rewrite -Qcat_assoc in Heb.
    rewrite Heb in Heb_ss.
    destruct Heb_ss as [_ Heb_ss].
    specialize IHss with (1 := Heb).
    clear Heb.
    (* Sem_frag_stmts: *)
    rewrite Sem_frag_stmts_cat in Hsf.
    destruct Hsf as [vm_comp_s [ct_comp_s Hsf]].
    specialize IHs with (1 := proj1 Hsf) (2 := Haft).
    specialize IHss with (1 := proj2 Hsf) (2 := IHs).
    exact IHss.
* clear ExpandBranch_fun_and_Sem_frag_stmt.
  intros vm_for_tmap tmap Htm_inf Hvm_sub_tm.
  induction s as [|var ft|var reg|var mem|var1 var2|var expr|ref expr|ref|cond sst ssf] ; simpl ;
        intros old_tmap old_scope tm_tmap tm_scope old_comp old_connmap eb_connmap eb_scope old_vm old_ct vm_comp ct_comp Hs_inf Hsc_sub_tm Hst Htm_sub_vm Heb Hsf Haft.
  + (* Sskip *)
    admit.
  + (* Swire *)
    destruct ft as [gt| |] ; try by discriminate Hs_inf.
    generalize (fully_inferred_does_not_change gt var vm_for_tmap Hs_inf) ; intro Htm_s.
    simpl in Htm_s ; simpl in Hst.
    destruct (CEP.find var old_tmap) eqn: Hnot_find_var ; first by discriminate Hst.
    destruct (match CEP.find var vm_for_tmap with
        | Some (OutPort newgt) | Some (InPort newgt) |
          Some (Register newgt _ _ _) | Some (Wire newgt) |
          Some (Node newgt) =>
            if code_vm_type_equivalent gt newgt
            then Some (Gtyp newgt, bin_of_nat (nat_of_bin var.2 + 1))
            else None
        | None => None
        end) as [[[gt'| |] n]|] eqn: Hdiscr ;
          rewrite Hdiscr in Hst, Htm_s ;
          last (by discriminate Hst) ; clear Hdiscr n ;
          try (by contradiction Htm_s) ;
          subst gt'.
    injection Hst ; clear Hst ; intros ; subst tm_tmap tm_scope.
    destruct (CEP.find var old_scope) ; first by discriminate Heb.
    rewrite Qcats1 in Heb.
    injection Heb ; clear Heb ; intros ; subst eb_connmap eb_scope.
    destruct Hsf as [vm_comp' [ct_comp' [Hsf Hcomp]]].
    assert (Hvar_tm: CEP.find var tmap = Some (Gtyp gt, HiF.Duplex)).
          specialize (Htm_sub_vm var) ; specialize (Hvm_sub_tm var).
          rewrite (CEP.Lemmas.find_add_eq (eq_refl var)) in Htm_sub_vm.
          destruct (CEP.find var vm_for_tmap) as [[gt'|gt'|gt'|gt'|gt']|] ;
                try (by contradiction Htm_sub_vm) ;
                injection Htm_sub_vm ; clear Htm_sub_vm ; intro ; subst gt' ;
                exact Hvm_sub_tm.
    rewrite Hvar_tm in Hsf ; simpl in Hsf ; rewrite add1n in Hsf.
    assert (Hadd: CEP.Equal (CEP.add var (Wire gt) old_vm) vm_comp /\ CEP.Equal (CEP.add var D_undefined old_ct) ct_comp).
          split ; intro k.
          - destruct (k == var) eqn: Hkvar.
            * destruct Hsf as [Hsf _] ; specialize (Hsf 0).
              simpl in Hsf. rewrite add0n nat_of_binK -surjective_pairing in Hsf.
              by rewrite (CEP.Lemmas.find_add_eq Hkvar)
                      -(proj1 Hcomp) (elimT eqP Hkvar) (proj2 Hsf) //.
            * destruct Hsf as [_ [Hsf _]] ; specialize (Hsf k.1 k.2).
              rewrite (CEP.Lemmas.find_add_neq (elimT negP (negbT Hkvar)))
                      -(proj1 Hcomp) (surjective_pairing k) Hsf //.
              destruct (k.1 == var.1) eqn: Hkvar1 ; move /eqP : Hkvar1 => Hkvar1 ;
                    last (by left ; exact Hkvar1).
              right.
              destruct (Nat.compare_spec k.2 var.2).
              + rewrite (injective_projections k var Hkvar1 (can_inj nat_of_binK H)) eq_refl // in Hkvar.
              + left ; rewrite (introT ltP H) //.
              + right ; rewrite (introT ltP H) //.
          - destruct (k == var) eqn: Hkvar.
            * destruct Hsf as [_ [_ [_ Hsf]]] ; specialize (Hsf 0 (ltn0Sn _)).
              rewrite add0n nat_of_binK -surjective_pairing in Hsf.
              by rewrite (CEP.Lemmas.find_add_eq Hkvar)
                      -(proj2 Hcomp) (elimT eqP Hkvar) Hsf //.
            * destruct Hsf as [_ [_ [Hsf _]]] ; specialize (Hsf k.1 k.2).
              rewrite (CEP.Lemmas.find_add_neq (elimT negP (negbT Hkvar)))
                      -(proj2 Hcomp) (surjective_pairing k) Hsf //.
              destruct (k.1 == var.1) eqn: Hkvar1 ; move /eqP : Hkvar1 => Hkvar1 ;
                    last (by left ; exact Hkvar1).
              right.
              destruct (Nat.compare_spec k.2 var.2).
              + rewrite (injective_projections k var Hkvar1 (can_inj nat_of_binK H)) eq_refl // in Hkvar.
              + left ; rewrite (introT ltP H) //.
              + right ; rewrite (introT ltP H) //.
    split.
    - destruct Haft as [Haft _].
      intro k ; specialize (Haft k).
      destruct (k == var) eqn: Hkvar.
      * by rewrite (CEP.Lemmas.find_add_eq Hkvar) (CEP.Lemmas.find_add_eq Hkvar) //.
      * apply negbT in Hkvar ; move /negP : Hkvar => Hkvar.
        rewrite (CEP.Lemmas.find_add_neq Hkvar) (CEP.Lemmas.find_add_neq Hkvar).
        destruct (CEP.find k old_scope) as [[ft_tgt [| | | |]]|] ; try by trivial.
        1,2: destruct (CEP.find k old_connmap) as [[| |expr]|] ; try (by exact Haft).
        1,2: generalize (type_of_expr_submap expr old_tmap (CEP.add var (Gtyp gt, HiF.Duplex) old_tmap)
                         (CEP.Lemmas.submap_none_add (Gtyp gt, HiF.Duplex) (CEP.Lemmas.submap_refl old_tmap) Hnot_find_var)) ;
             intro H.
        1,2: destruct (type_of_expr expr old_tmap) as [[ft_src p]|] ; last by contradiction Haft.
        1,2: by rewrite H //.
    destruct Haft as [_ Haft] ; split.
    - destruct Haft as [Haft _].
      intro k ; specialize (Haft k).
      rewrite -(proj2 Hadd k).
      destruct (k == var) eqn: Hkvar.
      * rewrite (CEP.Lemmas.find_add_eq Hkvar) (CEP.Lemmas.find_add_eq Hkvar) //.
      * apply negbT in Hkvar ; move /negP : Hkvar => Hkvar.
        rewrite (CEP.Lemmas.find_add_neq Hkvar) (CEP.Lemmas.find_add_neq Hkvar).
        destruct (PVM.find k old_connmap) as [[| |cm_expr]|] ; try by exact Haft.
        destruct (CEP.find k old_ct) as [[| |ct_expr]|] ; try by exact Haft.
        generalize (type_of_expr_submap cm_expr old_tmap (CEP.add var (Gtyp gt, HiF.Duplex) old_tmap)
                         (CEP.Lemmas.submap_none_add (Gtyp gt, HiF.Duplex) (CEP.Lemmas.submap_refl old_tmap) Hnot_find_var)) ;
              intro H.
        destruct (type_of_expr cm_expr old_tmap) as [[[cm_gt| |] cm_p]|] ; try by contradiction Haft.
        rewrite H ; clear H.
        generalize (type_of_expr_submap ct_expr old_tmap (CEP.add var (Gtyp gt, HiF.Duplex) old_tmap)
                         (CEP.Lemmas.submap_none_add (Gtyp gt, HiF.Duplex) (CEP.Lemmas.submap_refl old_tmap) Hnot_find_var)) ;
              intro H.
        destruct (type_of_expr ct_expr old_tmap) as [[[ct_gt| |] ct_p]|] ; try by contradiction Haft.
        by rewrite H //.
    destruct Haft as [_ Haft] ; split.
    - destruct Haft as [Haft _].
      intro k ; specialize (Haft k).
      rewrite -(proj1 Hadd k) -(proj2 Hadd k).
      destruct (k == var) eqn: Hkvar.
      * by rewrite (CEP.Lemmas.find_add_eq Hkvar) (CEP.Lemmas.find_add_eq Hkvar) //.
      * apply negbT in Hkvar ; move /negP : Hkvar => Hkvar.
        rewrite (CEP.Lemmas.find_add_neq Hkvar) (CEP.Lemmas.find_add_neq Hkvar).
        destruct (CEP.find k old_ct) as [[| |expr]|] ; try by exact Haft.
        generalize (type_of_expr_submap expr old_tmap (CEP.add var (Gtyp gt, HiF.Duplex) old_tmap)
                         (CEP.Lemmas.submap_none_add (Gtyp gt, HiF.Duplex) (CEP.Lemmas.submap_refl old_tmap) Hnot_find_var)) ;
              intro H.
        destruct (PVM.find k old_vm) as [[gt0|gt0|gt0|gt0|gt0]|] ; try by exact Haft.
        1-3: destruct (type_of_expr expr old_tmap) as [[ft p]|] ; last by contradiction Haft.
        1-3: by rewrite H //.
    destruct Haft as [_ Haft] ; split.
    - destruct Haft as [Haft _].
      intro k ; specialize (Haft k).
      rewrite -(proj1 Hadd k).
      destruct (k == var) eqn: Hkvar.
      * by rewrite (CEP.Lemmas.find_add_eq Hkvar) (CEP.Lemmas.find_add_eq Hkvar) //.
      * apply negbT in Hkvar ; move /negP : Hkvar => Hkvar.
        by rewrite (CEP.Lemmas.find_add_neq Hkvar) (CEP.Lemmas.find_add_neq Hkvar) //.
    - destruct Haft as [_ Haft].
      intro k ; specialize (Haft k).
      rewrite -(proj1 Hadd k).
      destruct (k == var) eqn: Hkvar.
      * by rewrite (CEP.Lemmas.find_add_eq Hkvar) (CEP.Lemmas.find_add_eq Hkvar) //.
      * apply negbT in Hkvar ; move /negP : Hkvar => Hkvar.
        by rewrite (CEP.Lemmas.find_add_neq Hkvar) (CEP.Lemmas.find_add_neq Hkvar) //.
  + (* Sreg *)
    admit.
  + (* Smem *)
    by discriminate Heb.
  + (* Sinst *)
    by discriminate Heb.
  + (* Snode *)
    admit.
  + (* Sfcnct *)
    destruct ref as [var| | |] ; try by discriminate Heb.
    simpl type_of_ref in Hst.
    generalize (aft_scope_submap_tmap old_scope old_connmap old_ct old_vm old_tmap Haft) ; intro Hsc_sub_tmap.
    generalize (type_of_expr_submap expr old_scope old_tmap Hsc_sub_tmap) ; intro Hexpr_tm.
    destruct (CEP.find var old_scope) as [[[gt_ref| |] [| | | |]]|] eqn: Hvar_sc ; try by discriminate Heb.
    1,2: destruct (type_of_expr expr old_scope) as [[[gt_expr| |] p]|] eqn: Hexpr_sc ; try by discriminate Heb.
    1,2: injection Hst ; clear Hst ; intros ; subst tm_tmap tm_scope.
    1,2: destruct (match gt_ref with
        | Fuint _ => match gt_expr with | Fuint _ | Fuint_implicit _ => true | _ => false end
        | Fsint _ => match gt_expr with | Fsint _ | Fsint_implicit _ => true | _ => false end
        | Fuint_implicit w_tgt => match gt_expr with | Fuint w_src | Fuint_implicit w_src => w_src <= w_tgt | _ => false end
        | Fsint_implicit w_tgt => match gt_expr with | Fsint w_src | Fsint_implicit w_src => w_src <= w_tgt | _ => false end
        | Fclock => match gt_expr with | Fclock => true | _ => false end
        | Freset => false
        | Fasyncreset => match gt_expr with | Fasyncreset => true | _ => false end
        end) eqn: Hconn ; last by discriminate Heb.
    1,2: rewrite Qcats0 in Heb ; injection Heb ; clear Heb ; intros ; subst eb_connmap eb_scope.
    1,2: generalize (proj1 Haft var) ; intro Hvar_cm ; rewrite Hvar_sc in Hvar_cm.
    1,2: generalize Hvar_sc ; intro Hvar_tm ; apply Hsc_sub_tmap in Hvar_tm.
    1,2: generalize (proj1 (proj2 (proj2 (proj2 Haft))) var) ; intro ;
         rewrite Hvar_tm in H.
    1,2: destruct (CEP.find var old_vm) as [[gt|gt|gt|gt|gt]|] eqn: Hvar_vm ;
               try (by discriminate H) ;
               try (injection H ; intro ; subst gt) ; clear H.
    1-5: generalize (proj1 (proj2 (proj2 Haft)) var) ; intro Hvar_ct ; rewrite Hvar_vm in Hvar_ct.
    1-5: generalize (proj1 (proj2 Haft) var) ; intro Hvar_cm'.
    2,5: destruct (CEP.find var old_ct) as [[]|] ; try (by contradiction Hvar_ct) ;
         destruct (CEP.find var old_connmap) as [[]|] ; try (by contradiction Hvar_cm') ;
         by contradiction Hvar_cm.
    1-3: split.
    - 1,3,5: destruct Haft as [Haft _].
      1-3: intro k ; specialize (Haft k).
      1-3: destruct (k == var) eqn: Hkvar.
      * 1,3,5: rewrite (CEP.Lemmas.find_add_eq Hkvar) (elimT eqP Hkvar) Hvar_sc.
        1-3: rewrite Hexpr_tm //.
      * 1-3: rewrite (CEP.Lemmas.find_add_neq (elimT negP (negbT Hkvar))) //.
    1-3: destruct Haft as [_ Haft] ; split.
    - 1,3,5: destruct Haft as [Haft _].
      1-3: intro k ; specialize (Haft k).
      1-3: destruct (k == var) eqn: Hkvar.
      * 1,3,5: rewrite (CEP.Lemmas.find_add_eq Hkvar).
        1-3: move /eqP : Hkvar => Hkvar ; subst k.
        1-3: rewrite -(proj2 Hsf var).
        1-3: destruct (CEP.find var old_ct) as [[| |ct_expr]|] ;
                   try (by contradiction Hvar_ct) ;
                   try (by trivial).
        1-3: rewrite Hexpr_tm //.
        1-3: destruct (type_of_expr ct_expr old_tmap) as [[ft p_ft]|] ; last by contradiction Hvar_ct.
        1-3: destruct gt_expr ; try (by discriminate p) ;
             destruct gt_ref ; try (by discriminate Hconn) ;
             destruct ft as [[]| |] ; try (by discriminate Hvar_ct) ;
             try (by discriminate p_ft) ; simpl ; done.
      * 1-3: rewrite (CEP.Lemmas.find_add_neq (elimT negP (negbT Hkvar))) -(proj2 Hsf k) //.
    1-3: destruct Haft as [_ Haft] ; split.
    - 1,3,5: destruct Haft as [Haft _].
      1-3: intro k ; specialize (Haft k).
      1-3: by rewrite -(proj1 Hsf k) -(proj2 Hsf k) //.
    1-3: destruct Haft as [_ Haft] ; split.
    - 1,3,5: destruct Haft as [Haft _].
      1-3: intro k ; specialize (Haft k).
      1-3: by rewrite -(proj1 Hsf k) //.
    - 1-3: destruct Haft as [_ Haft].
      1-3: intro k ; specialize (Haft k).
      1-3: by rewrite -(proj1 Hsf k) //.
  + (* Sinvalid should be similar to Sfcnct but simpler *)
    admit.
  + (* Swhen *)
    move /andP : Hs_inf => [/andP [_ Hsst_inf] Hssf_inf].
    rename ExpandBranches_funs_and_Sem_frag_stmts into IHsst.
    specialize (IHsst vm_for_tmap tmap Htm_inf Hvm_sub_tm).
    generalize (IHsst ssf) ; intro IHssf ; specialize IHssf with (1 := Hssf_inf).
    specialize (IHsst sst old_tmap old_scope) with (old_comp := old_comp) (old_connmap := old_connmap) (old_vm := old_vm) (old_ct := old_ct)
                                (1 := Hsst_inf) (2 := Hsc_sub_tm).
    destruct (type_of_expr cond old_scope) as [[[[[|[|]]| | | | | |]| |] p_cond]|] eqn: Hcond ; try by discriminate Heb.
    generalize (type_of_expr_submap cond old_scope old_tmap
                       (aft_scope_submap_tmap old_scope old_connmap old_ct old_vm old_tmap Haft)) ;
                 intro Hcond_tm ; rewrite Hcond in Hcond_tm.
    (* stmts_submap: *)
    generalize (stmts_submap vm_for_tmap sst old_tmap old_scope Hsc_sub_tm) ; intro Htm_t.
    destruct (stmts_tmap (old_tmap, old_scope) sst vm_for_tmap) as [[tm_tmap_t tm_scope_t]|] ; last by discriminate Hst.
    specialize IHsst with (1 := Logic.eq_refl).
    specialize (IHssf tm_tmap_t old_scope) with (1 := CEP.Lemmas.submap_trans (proj2 (proj2 Htm_t)) (proj1 Htm_t)).
    generalize (stmts_submap vm_for_tmap ssf tm_tmap_t old_scope (CEP.Lemmas.submap_trans (proj2 (proj2 Htm_t)) (proj1 Htm_t))) ; intro Htm_f.
    destruct (stmts_tmap (tm_tmap_t, old_scope) ssf vm_for_tmap) as [[tm_tmap_f tm_scope_f]|] ; last by discriminate Hst.
    injection Hst ; clear Hst ; intros ; subst tm_tmap_f tm_scope.
    specialize IHssf with (1 := Logic.eq_refl) (2 := Htm_sub_vm).
    assert (Htm_t_sub_tm: scope_sub_vm tm_tmap_t vm_for_tmap).
          destruct Htm_f as [_ [Htm_f _]].
          intro k ; specialize (Htm_f k) ; specialize (Htm_sub_vm k).
          destruct (CEP.find k tm_tmap_t) as [[ft ori]|] ; last by trivial.
          specialize Htm_f with (1 := Logic.eq_refl) ; rewrite Htm_f // in Htm_sub_vm.
    specialize IHsst with (1 := Htm_t_sub_tm).
    (* ExpandBranches_funs: *)
    generalize (ExpandBranches_funs_submap sst old_comp old_connmap old_scope) ; intro Heb_t.
    destruct (ExpandBranches_funs sst old_comp old_connmap old_scope) as [[[eb_comp_t eb_connmap_t] eb_scope_t]|] ; last by discriminate Heb.
    destruct Heb_t as [Heb_t' Heb_t] ; subst eb_comp_t.
    specialize IHsst with (1 := Logic.eq_refl).
    specialize (IHssf (Qcat old_comp (component_stmts_of sst)) old_connmap).
    generalize (ExpandBranches_funs_submap ssf (Qcat old_comp (component_stmts_of sst)) old_connmap old_scope) ; intro Heb_f.
    destruct (ExpandBranches_funs ssf (Qcat old_comp (component_stmts_of sst)) old_connmap old_scope) as [[[eb_comp_f eb_connmap_f] eb_scope_f]|] ; last by discriminate Heb.
    destruct Heb_f as [Heb_f' Heb_f] ; subst eb_comp_f.
    specialize IHssf with (1 := Logic.eq_refl).
    rewrite Qcat_assoc in Heb.
    injection Heb ; clear Heb ; intros ; subst eb_connmap eb_scope.
    (* Sem_frag_stmts: *)
    apply Sem_frag_stmts_cat in Hsf.
    destruct Hsf as [vm_comp_t [ct_comp_t Hsf]].
    specialize IHsst with (1 := proj1 Hsf) (2 := Haft).
    specialize IHssf with (1 := proj2 Hsf).
    assert (Hsf_t : vm_and_ct_compatible old_vm old_ct) by admit.
           (* should hold because of ct_sub_vm old_ct old_vm.
              Perhaps change Cem_frag_stmts_component to require this instead of vm_and_ct_compatible? *)
    apply (Sem_frag_stmts_component) with (2 := proj1 Hsf) in Hsf_t.
    assert (Hsf_f : vm_and_ct_compatible vm_comp_t ct_comp_t) by admit.
           (* should hold because ct_sub_vm ct_comp_t vm_comp_t (see IHsst) *)
    apply (Sem_frag_stmts_component) with (2 := proj2 Hsf) in Hsf_f.
    assert (Haft_f: all_fit_together old_scope old_connmap ct_comp_t vm_comp_t tm_tmap_t).
          split.
          - destruct Haft as [Haft _].
            intro k ; specialize (Haft k).
            destruct (CEP.find k old_scope) as [[ft_tgt [| | | |]]|] ; try by trivial.
            1-2: destruct (CEP.find k old_connmap) as [[| |expr]|] ; try by exact Haft.
            1-2: generalize (type_of_expr_submap expr old_tmap tm_tmap_t (proj1 (proj2 Htm_t))) ; intro.
            1-2: destruct (type_of_expr expr old_tmap) ; last by contradiction Haft.
            1-2: rewrite H //.
          destruct Haft as [_ Haft] ; split.
          - destruct Haft as [Haft _].
            intro k ; specialize (Haft k).
            specialize (Hsf_t k).
            destruct (CEP.find k old_connmap) as [[| |cm_expr]|] ; last by trivial.
            1-3: destruct (CEP.find k old_ct) as [|] ; last by contradiction Haft.
            1-3: specialize Hsf_t with (1 := Logic.eq_refl).
            1-3: rewrite Hsf_t ; try done. (* That solves two of the three goals *)
            destruct d as [| |ct_expr] ; try by exact Haft.
            generalize (type_of_expr_submap cm_expr old_tmap tm_tmap_t (proj1 (proj2 Htm_t))) ; intro.
            destruct (type_of_expr cm_expr old_tmap) as [[[cm_gt| |] cm_p]|] ; try by contradiction Haft.
            rewrite H ; clear H.
            generalize (type_of_expr_submap ct_expr old_tmap tm_tmap_t (proj1 (proj2 Htm_t))) ; intro.
            destruct (type_of_expr ct_expr old_tmap) as [[[ct_gt| |] ct_p]|] ; try by contradiction Haft.
            rewrite H //.
          destruct Haft as [_ Haft] ; split.
          - by apply IHsst.
          destruct Haft as [_ Haft] ; split.
          - by apply IHsst.
          - destruct Haft as [_ Haft].
            generalize (proj1 Hsf) ; intro Hvm_comp_t ; apply Sem_frag_stmts_compatible in Hvm_comp_t.
            destruct Hvm_comp_t as [Hvm_comp_t _].
            intro k ; specialize (Haft k) ; specialize (Hvm_comp_t k).
            destruct (CEP.find k old_scope) as [[ft ori]|] ; last by trivial.
            destruct ori, (PVM.find k old_vm) as [[gt|gt|gt|gt|gt]|] ;
                  try (by contradiction Haft) ;
                  subst ft ;
                  specialize Hvm_comp_t with (1 := Logic.eq_refl) ;
                  rewrite Hvm_comp_t //.
    specialize (IHssf Haft_f) ; clear Haft_f.
    split.
    - destruct IHsst as [IHsst _] ; destruct IHssf as [IHssf _].
      intro k ; specialize (IHsst k) ; specialize (IHssf k).
      destruct Heb_t as [_ Heb_t] ; specialize (Heb_t k).
      destruct Heb_f as [_ Heb_f] ; specialize (Heb_f k).
      generalize (scope_vm_submap_tmap tm_tmap vm_for_tmap tmap Htm_sub_vm Hvm_sub_tm) ; intro Hfind_tm.
      apply (CEP.Lemmas.submap_trans (proj1 (proj2 Htm_f))) in Hfind_tm.
      apply (CEP.Lemmas.submap_trans (proj1 (proj2 Htm_t))) in Hfind_tm.
      apply (CEP.Lemmas.submap_trans Hsc_sub_tm) in Hfind_tm.
      specialize (Hfind_tm k).
      destruct (CEP.find k old_scope) as [[ft_tgt ori]|] ;
            last (by trivial) ;
            specialize Heb_t with (1 := Logic.eq_refl) ;
            specialize Heb_f with (1 := Logic.eq_refl) ;
            specialize Hfind_tm with (1 := Logic.eq_refl).
      specialize (Htm_inf k).
      rewrite Hfind_tm in Htm_inf.
      destruct ft_tgt as [gt| |] ; try by contradiction Htm_inf.
      rewrite Heb_t in IHsst.
      rewrite Heb_f in IHssf.
      rewrite /combine_when_connections CEP.Lemmas.map2_1bis //.
      destruct ori ; try by trivial.
      1,2: destruct (CEP.find k eb_connmap_t) as [[| |expr_t]|] ;
                 last (by contradiction IHsst) ; try by done.
      1-4: destruct (CEP.find k eb_connmap_f) as [[| |expr_f]|] ;
                 last (by contradiction IHssf) ; try by done.
      1-4: generalize (type_of_expr_submap expr_t tm_tmap_t tm_tmap (proj1 (proj2 Htm_f))) ; intro ;
           destruct (type_of_expr expr_t tm_tmap_t) as [[ft_src p_src]|] eqn: Hexpr_t ; try (by contradiction IHsst) ;
           try rewrite H //.
      1,2: destruct (expr_t == expr_f) ; first (by rewrite H //) ; last clear H.
      1,2: simpl type_of_expr.
      1,2: generalize (type_of_expr_submap cond old_tmap tm_tmap (CEP.Lemmas.submap_trans (proj1 (proj2 Htm_t)) (proj1 (proj2 Htm_f)))) ;
           intro ; rewrite Hcond_tm in H ; rewrite H ; clear H.
      1,2: generalize (type_of_expr_submap expr_t tm_tmap_t tm_tmap (proj1 (proj2 Htm_f))) ;
           intro ; rewrite Hexpr_t in H ; rewrite H ; clear H.
      1,2: destruct (type_of_expr expr_f tm_tmap) as [[ft_src_f p_f]|] ; last by contradiction IHssf.
      1,2: rewrite /ftype_mux /sval /proj2_sig.
      1,2: destruct gt ; try (by discriminate Htm_inf) ;
           destruct ft_src   as [[| | | | | |]| |] ; try (by discriminate IHsst) ; try (by contradiction p_t) ;
           destruct ft_src_f as [[| | | | | |]| |] ; try (by discriminate IHssf) ; try (by contradiction p_f) ;
           simpl ; done.
    destruct Haft as [_ Haft] ; destruct IHsst as [_ IHsst] ; destruct IHssf as [_ IHssf] ; split.
    - destruct IHsst as [IHsst _] ; destruct IHssf as [IHssf _].
      intro k ; specialize (IHsst k) ; specialize (IHssf k) ; specialize (Hsf_t k) ; specialize (Hsf_f k).
      rewrite /combine_when_connections CEP.Lemmas.map2_1bis //.
      destruct (CEP.find k eb_connmap_t) as [[| |expr_t]|] eqn: Hfind_eb_t,
               (CEP.find k eb_connmap_f) as [[| |expr_f]|] eqn: Hfind_eb_f,
               (CEP.find k ct_comp_t) eqn: Hfind_ct_t, (CEP.find k ct_comp) eqn: Hfind_ct_f ; try (by done) ;
               try specialize Hsf_f with (1 := Logic.eq_refl) ; try (by discriminate Hsf_f).
      1-3: injection Hsf_f ; clear Hsf_f ; intros ; subst d0 ; try (by assumption).
      2: destruct (expr_t == expr_f) ; last simpl.
      1-4: destruct d as [| |ct_expr] ; try by trivial.
      3: generalize (type_of_expr_submap cond old_tmap tm_tmap (CEP.Lemmas.submap_trans (proj1 (proj2 Htm_t)) (proj1 (proj2 Htm_f)))) ;
         intro ; rewrite Hcond_tm in H ; rewrite H ; clear H.
      1-4: generalize (type_of_expr_submap expr_t tm_tmap_t tm_tmap (proj1 (proj2 Htm_f))) ; intro.
      1-4: destruct (type_of_expr expr_t tm_tmap_t) as [[[gt_t| |] p_t]|] ; try by contradiction IHsst.
      1-4: rewrite H ; clear H.
      3: destruct (type_of_expr expr_f tm_tmap) as [[[gt_f| |] p_f]|] ; try by contradiction IHssf.
      1-4: generalize (type_of_expr_submap ct_expr tm_tmap_t tm_tmap (proj1 (proj2 Htm_f))) ; intro.
      1-4: destruct (type_of_expr ct_expr tm_tmap_t) as [[[ct_gt| |] ct_p]|] ; try by contradiction IHsst.
      1-4: rewrite H //.
      rewrite H in IHssf ; clear H.
      rewrite /ftype_mux /sval /proj2_sig ; simpl ftype_mux'.
      destruct gt_t ; try (by contradiction p_t) ;
      destruct ct_gt ; try (by discriminate IHsst) ; (*try (by contradiction p_t) ;*)
      destruct gt_f ; try (by discriminate IHssf) ; try (by contradiction p_f).
      * 1,2: by rewrite /Fuint_exp //.
      * 1,2: by rewrite /Fsint_exp //.
      * by rewrite /Fclock_exp //.
      * by rewrite /Fasyncreset_exp //.
    destruct Haft as [_ Haft] ; destruct IHsst as [_ IHsst] ; destruct IHssf as [_ IHssf] ; split.
    - by apply IHssf.
    destruct Haft as [_ Haft] ; destruct IHsst as [_ IHsst] ; destruct IHssf as [_ IHssf] ; split.
    - by apply IHssf.
    - destruct IHssf as [_ IHssf].
      destruct Heb_f as [_ Heb_f].
      intro ; specialize (Heb_f k) ; specialize (IHssf k).
      destruct (CEP.find k old_scope) as [[ft ori]|] ; last by trivial.
      specialize Heb_f with (1 := Logic.eq_refl) ; rewrite Heb_f // in IHssf.
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

Lemma ExpandWhen_correct_inductive :
forall (vm_for_tmap : CEP.t vertex_type) (tmap : CEP.t (ftype * HiF.forient)),
        tmap_has_fully_inferred_ground_types tmap
    ->
        vm_sub_tmap vm_for_tmap tmap
    ->
        forall s : HiFP.hfstmt,
                stmt_has_fully_inferred_ground_types s
            ->
                forall (old_scope : CEP.t (ftype * HiF.forient)) (old_connmap : CEP.t def_expr)
                       (old_ct : CEP.t def_expr) (old_vm : CEP.t vertex_type) (old_tmap: CEP.t (ftype * HiF.forient))
                       (tm_tmap tm_scope : CEP.t (ftype * HiF.forient))
                       (old_comp : HiFP.hfstmt_seq) (eb_connmap : CEP.t def_expr)
                       (sf_vm : CEP.t vertex_type) (sf_ct : CEP.t def_expr),
                            all_fit_together old_scope old_connmap old_ct old_vm old_tmap
                        ->
                            stmt_tmap (old_tmap, old_scope) s vm_for_tmap = Some (tm_tmap, tm_scope)
                        ->
                            ExpandBranch_fun s old_comp old_connmap old_scope =
                            Some (Qcat old_comp (component_stmt_of s), eb_connmap, tm_scope)
                        ->
                            Sem_frag_stmts old_vm old_ct (Qcat (component_stmt_of s)
                                           (convert_to_connect_stmts eb_connmap))
                                           sf_vm sf_ct tmap
                        ->
                            scope_sub_vm tm_tmap vm_for_tmap (* perhaps not needed here *)
                        ->
                                Sem_frag_stmt old_vm old_ct s sf_vm sf_ct tmap
                            /\
                                all_fit_together tm_scope eb_connmap sf_ct sf_vm tm_tmap
with ExpandWhens_correct_inductive :
forall (vm_for_tmap : CEP.t vertex_type) (tmap : CEP.t (ftype * HiF.forient)),
        tmap_has_fully_inferred_ground_types tmap
    ->
        vm_sub_tmap vm_for_tmap tmap
    ->
        forall ss : HiFP.hfstmt_seq,
                stmts_have_fully_inferred_ground_types ss
            ->
                forall (old_scope : CEP.t (ftype * HiF.forient)) (old_connmap : CEP.t def_expr)
                       (old_ct : CEP.t def_expr) (old_vm : CEP.t vertex_type) (old_tmap: CEP.t (ftype * HiF.forient))
                       (tm_tmap tm_scope : CEP.t (ftype * HiF.forient))
                       (old_comp : HiFP.hfstmt_seq) (eb_connmap : CEP.t def_expr)
                       (sf_vm : CEP.t vertex_type) (sf_ct : CEP.t def_expr),
                            all_fit_together old_scope old_connmap old_ct old_vm old_tmap
                        ->
                            stmts_tmap (old_tmap, old_scope) ss vm_for_tmap = Some (tm_tmap, tm_scope)
                        ->
                            ExpandBranches_funs ss old_comp old_connmap old_scope =
                            Some (Qcat old_comp (component_stmts_of ss), eb_connmap, tm_scope)
                        ->
                            Sem_frag_stmts old_vm old_ct (Qcat (component_stmts_of ss)
                                           (convert_to_connect_stmts eb_connmap))
                                           sf_vm sf_ct tmap
                        ->
                            scope_sub_vm tm_tmap vm_for_tmap (* perhaps not needed here *)
                        ->
                                Sem_frag_stmts old_vm old_ct ss sf_vm sf_ct tmap
                            /\
                                all_fit_together tm_scope eb_connmap sf_ct sf_vm tm_tmap.
Proof.
* clear ExpandWhen_correct_inductive.
  intros vm_for_tmap tmap Htm_inf Hvm_tm s.
  generalize (ExpandWhens_correct_simple vm_for_tmap tmap Htm_inf Hvm_tm s) ; intro Hsimple.
  induction s as [| | | | | | | |cond sst ssf]; try (by apply Hsimple).
  (* only Swhen is left *)
  clear Hsimple.
  simpl.
  intros Hs_inf old_scope old_connmap old_ct old_vm old_tmap tm_tmap tm_scope old_comp eb_connmap sf_vm sf_ct
         Haft Hst Heb Hsf Htm_sub_vm.
  assert (Htm_tm_sub_tm : CEP.submap tm_tmap tmap).
        intros k v Hfind_k ; specialize (Htm_sub_vm k) ; specialize (Hvm_tm k).
        rewrite Hfind_k in Htm_sub_vm.
        destruct v as [ft [| | | |]] ;
              try (by contradiction Htm_sub_vm) ;
              destruct (CEP.find k vm_for_tmap) as [[gt|gt|gt|gt|gt]|] ;
              try (by contradiction Htm_sub_vm) ;
              subst ft ;
              exact Hvm_tm.
  specialize (ExpandWhens_correct_inductive vm_for_tmap tmap Htm_inf Hvm_tm).
  move /andP : Hs_inf => [/andP [Hs_inf Hsst_inf] Hssf_inf].
  generalize (ExpandWhens_correct_inductive ssf Hssf_inf old_scope old_connmap) ; intro IHssf ;
        specialize IHssf with (old_comp := (Qcat old_comp (component_stmts_of sst))).
  specialize (ExpandWhens_correct_inductive sst Hsst_inf old_scope old_connmap old_ct old_vm old_tmap)
             with (old_comp := old_comp) (1 := Haft) ; rename ExpandWhens_correct_inductive into IHsst.
  (* work further on the induction hypotheses *)
  destruct (type_of_expr cond old_scope) as [[[[[|[|]]| | | | | |]| |] p_cond]|] eqn: Htyp_cond ; try by discriminate Heb.
  (* stmts_tmap: *)
  generalize (aft_scope_submap_tmap _ _ _ _ _ Haft) ; intro Hsc_tm.
  generalize (stmts_submap vm_for_tmap sst old_tmap old_scope Hsc_tm) ; intro Hst_sub_t.
  specialize (stmts_tmap_and_ExpandBranches_funs sst old_scope old_connmap old_tmap vm_for_tmap)
        with (old_comp := old_comp) (2 := Hsc_tm) (3 := Hsst_inf) ; intro Htm_eb_t.
  specialize (ExpandBranches_funs_and_Sem_frag_stmts vm_for_tmap tmap Htm_inf Hvm_tm sst old_tmap old_scope)
              with (old_comp := old_comp) (old_connmap := old_connmap) (old_vm := old_vm) (old_ct := old_ct)
              (1 := Hsst_inf) (2 := Hsc_tm) ; intro Haft_comp_t.
  destruct (stmts_tmap (old_tmap, old_scope) sst vm_for_tmap) as [[tm_tmap_t tm_scope_t]|] eqn: Hst_t ; last by discriminate Hst.
  specialize IHsst with (1 := Logic.eq_refl).
  specialize Htm_eb_t with (2 := Logic.eq_refl).
  specialize Haft_comp_t with (1 := Logic.eq_refl).
  specialize IHssf with (old_tmap := tm_tmap_t).
  generalize (stmts_submap vm_for_tmap ssf tm_tmap_t old_scope (CEP.Lemmas.submap_trans (proj2 (proj2 Hst_sub_t)) (proj1 Hst_sub_t))) ; intro Hst_f.
  specialize (stmts_tmap_and_ExpandBranches_funs ssf old_scope old_connmap tm_tmap_t vm_for_tmap)
        with (old_comp := (Qcat old_comp (component_stmts_of sst)))
        (2 := CEP.Lemmas.submap_trans (proj2 (proj2 Hst_sub_t)) (proj1 Hst_sub_t)) (3 := Hssf_inf) ; intro Htm_eb_f.
  destruct (stmts_tmap (tm_tmap_t, old_scope) ssf vm_for_tmap) as [[tm_tmap_f tm_scope_f]|] ; last by discriminate Hst.
  specialize IHssf with (2 := Logic.eq_refl).
  specialize Htm_eb_f with (2 := Logic.eq_refl).
  injection Hst ; clear Hst ; intros ; subst tm_tmap_f tm_scope.
  assert (Htm_t_inf: tmap_has_fully_inferred_ground_types tm_tmap_t).
        destruct Hst_f as [_ [Hst_f _]].
        intro k ; specialize (Hst_f k) ; specialize (Htm_inf k).
        destruct (CEP.find k tm_tmap_t) as [[ft p]|] ; last by trivial.
        specialize Hst_f with (1 := Logic.eq_refl).
        apply Htm_tm_sub_tm in Hst_f.
        by rewrite Hst_f // in Htm_inf.
  specialize Htm_eb_f with (1 := Htm_t_inf).
  assert (Hold_tm_inf: tmap_has_fully_inferred_ground_types old_tmap).
        destruct Hst_sub_t as [_ [Hst_sub_t _]].
        intro k ; specialize (Hst_sub_t k) ; specialize (Htm_t_inf k).
        destruct (CEP.find k old_tmap) as [[ft p]|] ; last by trivial.
        specialize Hst_sub_t with (1 := Logic.eq_refl).
        by rewrite Hst_sub_t // in Htm_t_inf.
  specialize Htm_eb_t with (1 := Hold_tm_inf).
  (* intermezzo: type of cond in the goal *)
  generalize (type_of_expr_submap cond old_scope old_tmap Hsc_tm) ; intro ; rewrite Htyp_cond in H.
  generalize (type_of_expr_submap cond old_tmap tm_tmap (CEP.Lemmas.submap_trans (proj1 (proj2 Hst_sub_t)) (proj1 (proj2 (Hst_f))))) ;
        intro ; rewrite H in H0 ; clear H.
  generalize (type_of_expr_submap cond tm_tmap tmap (scope_vm_submap_tmap tm_tmap vm_for_tmap tmap Htm_sub_vm Hvm_tm)) ;
        intro ; rewrite H0 in H ; clear H0.
  rewrite H ; clear H.
  (* ExpandBranches_funs: *)
  generalize (ExpandBranches_funs_submap sst old_comp old_connmap old_scope) ; intro Heb_t.
  destruct (ExpandBranches_funs sst old_comp old_connmap old_scope) as [[[eb_comp_t eb_connmap_t] eb_scope_t]|] ; last by discriminate Heb.
  destruct Heb_t as [H Heb_t] ; subst eb_comp_t.
  specialize Htm_eb_t with (1 := Logic.eq_refl).
  specialize Haft_comp_t with (2 := Logic.eq_refl).
  subst eb_scope_t.
  specialize IHsst with (1 := Logic.eq_refl).
  generalize (ExpandBranches_funs_submap ssf (Qcat old_comp (component_stmts_of sst)) old_connmap old_scope) ; intro Heb_f.
  destruct (ExpandBranches_funs ssf (Qcat old_comp (component_stmts_of sst)) old_connmap old_scope) as [[[eb_comp_f eb_connmap_f] eb_scope_f]|] ; last by discriminate Heb.
  destruct Heb_f as [H Heb_f] ; subst eb_comp_f.
  specialize Htm_eb_f with (1 := Logic.eq_refl).
  subst eb_scope_f.
  specialize IHssf with (2 := Logic.eq_refl).
  rewrite Qcat_assoc in Heb.
  injection Heb ; clear Heb ; intro ; subst eb_connmap.
  (* Sem_frag_stmts: *)
  apply Sem_frag_stmts_cat in Hsf.
  destruct Hsf as [vm_comp [ct_comp [Hsf_comp Hsf_conn]]].
  apply Sem_frag_stmts_cat in Hsf_comp.
  destruct Hsf_comp as [vm_comp_t [ct_comp_t [Hsf_comp_t Hsf_comp_f]]].
  assert (Hstmt_sub_vm: scope_sub_vm tm_tmap_t vm_for_tmap).
        destruct Hst_f as [_ [Hst_f _]].
        intro k ; specialize (Hst_f k) ; specialize (Htm_sub_vm k).
        destruct (CEP.find k tm_tmap_t) as [[ft ori]|] ; last by trivial.
        specialize Hst_f with (1 := Logic.eq_refl).
        rewrite Hst_f // in Htm_sub_vm.
  specialize IHsst with (2 := Hstmt_sub_vm).
  specialize Haft_comp_t with (1 := Hstmt_sub_vm) (2 := Hsf_comp_t) (3 := Haft) ; clear Hstmt_sub_vm.
  assert (Hsf_t : Sem_frag_stmts old_vm old_ct
                        (Qcat (component_stmts_of sst) (convert_to_connect_stmts eb_connmap_t))
                        vm_comp_t (extend_defined_map_with eb_connmap_t ct_comp_t) tmap).
        apply Sem_frag_stmts_cat.
        exists vm_comp_t, ct_comp_t.
        split ; first by exact Hsf_comp_t.
        apply Sem_frag_stmts_connect ; first by exact Htm_inf.
        (* Now we can use Haft_comp_t to prove this *)
        assert (Htmt_sub_tm: CEP.submap tm_tmap_t tmap) by (apply (CEP.Lemmas.submap_trans (proj1 (proj2 Hst_f)) Htm_tm_sub_tm)).
        split.
        + intro k ; rewrite CEP.Lemmas.empty_o //.
        destruct Haft_comp_t as [_ Haft_comp_t] ; split.
        + destruct Haft_comp_t as [Haft_comp_t _].
          intro k ; specialize (Haft_comp_t k).
          destruct (CEP.find k eb_connmap_t) as [[| |cm_expr]|] ; try by exact Haft_comp_t.
          destruct (CEP.find k ct_comp_t) as [[| |ct_expr]|] ; try by exact Haft_comp_t.
          generalize (type_of_expr_submap cm_expr tm_tmap_t tmap Htmt_sub_tm) ; intro.
          destruct (type_of_expr cm_expr tm_tmap_t) as [[[cm_gt| |] cm_p]|] ; try by contradiction Haft_comp_t.
          rewrite H // ; clear H.
          generalize (type_of_expr_submap ct_expr tm_tmap_t tmap Htmt_sub_tm) ; intro.
          destruct (type_of_expr ct_expr tm_tmap_t) as [[[ct_gt| |] ct_p]|] ; try by contradiction Haft_comp_t.
          rewrite H //.
        destruct Haft_comp_t as [_ Haft_comp_t] ; split.
        + destruct Haft_comp_t as [Haft_comp_t _].
          intro k ; specialize (Haft_comp_t k).
          destruct (CEP.find k ct_comp_t) as [[| |expr]|] ; try by exact Haft_comp_t.
          destruct (CEP.find k vm_comp_t) as [[gt|gt|gt|gt|gt]|] ; try by exact Haft_comp_t.
          1-3: generalize (type_of_expr_submap expr tm_tmap_t tmap Htmt_sub_tm) ; intro.
          1-3: destruct (type_of_expr expr tm_tmap_t) as [[ft p]|] ; last by contradiction Haft_comp_t.
          1-3: rewrite H //.
        destruct Haft_comp_t as [_ Haft_comp_t] ; split.
        + destruct Haft_comp_t as [Haft_comp_t _].
          intro k ; specialize (Haft_comp_t k).
          destruct (CEP.find k vm_comp_t) as [[gt|gt|gt|gt|gt]|] ; try by exact Haft_comp_t.
          1-5: by apply Htmt_sub_tm, Haft_comp_t.
        + intro k ; rewrite CEP.Lemmas.empty_o //.
  specialize IHsst with (1 := Hsf_t) ; clear Hsf_t.

  specialize Sem_frag_stmts_compatible with (1 := proj1 IHsst) ; intro Hsf_sub_t.
  (*assert (Hsf_comp0_f : exists (vm_comp_f : CEP.t vertex_type) (ct_comp_f : CEP.t def_expr),
        Sem_frag_stmts old_vm old_ct (component_stmts_of ssf) vm_comp_f ct_comp_f tmap).
        (* This should hold because old_vm is a subset of vm_comp_t
           and based on Hsf_comp_f. *)
        admit.
  destruct Hsf_comp0_f as [vm_comp_f [ct_comp_f Hsf_comp0_f]].*)
  assert (Hsf_f : Sem_frag_stmts vm_comp_t (extend_map_with old_ct (extend_defined_map_with eb_connmap_t ct_comp_t))
                        (Qcat (component_stmts_of ssf) (convert_to_connect_stmts eb_connmap_f))
                        vm_comp (extend_defined_map_with eb_connmap_f (extend_defined_map_with eb_connmap_t ct_comp)) tmap).
        apply Sem_frag_stmts_cat.
        exists vm_comp, (extend_defined_map_with eb_connmap_t ct_comp) (* actually a slight variant of ct_comp *).
        split.
        + (* Sem_frag_stmts_component_Equal? *)
          admit.
        + apply Sem_frag_stmts_connect ; first by exact Htm_inf.
Check Haft_comp_t.
          admit. (* all should fit together here.
                    I think we need some property that says somehing about ExpandBranch_stmts and all_fit_togeter. *)
  specialize IHssf with (2 := Hsf_f) (3 := Htm_sub_vm) ; clear Hsf_f.
  assert (Haft_f: all_fit_together old_scope old_connmap
                (extend_map_with old_ct (extend_defined_map_with eb_connmap_t ct_comp_t))
                vm_comp_t tm_tmap_t).
        split.
        + destruct Haft as [Hsc_cm _].
          intro k ; specialize (Hsc_cm k).
          destruct (CEP.find k old_scope) as [[ft_tgt [| | | |]]|] ; try by trivial.
          1,2: destruct (CEP.find k old_connmap) as [[| |expr]|] ;
                last (by contradiction Hsc_cm) ; try by trivial.
          1,2: destruct Hst_sub_t as [_ [Hst_sub_t _]] ;
               apply (type_of_expr_submap expr) in Hst_sub_t.
          1,2: destruct (type_of_expr expr old_tmap) as [[ft_src p]|] ; last by contradiction Hsc_cm.
          1,2: by rewrite Hst_sub_t //.
        destruct Haft as [_ Haft] ; split.
        + destruct Haft as [Hcm_ct _].
          intro k ; specialize (Hcm_ct k).
          destruct (CEP.find k old_connmap) as [[| |cm_expr]|] ;
                try by exact Hcm_ct.
          1-3: rewrite /extend_map_with CEP.Lemmas.map2_1bis //.
          1-3: destruct (CEP.find k old_ct) as [[| |ct_expr]|] ;
                try by exact Hcm_ct.
          1,2,4: by rewrite /extend_defined_map_with CEP.Lemmas.map2_1bis //.
          destruct Hst_sub_t as [_ [Hct_expr _]].
          generalize (type_of_expr_submap cm_expr old_tmap tm_tmap_t Hct_expr) ; intro Hcm_expr.
          apply (type_of_expr_submap ct_expr) in Hct_expr.
          destruct (type_of_expr cm_expr old_tmap) as [[[cm_gt| |] cm_p]|] ; try by contradiction Hcm_ct.
          destruct (type_of_expr ct_expr old_tmap) as [[[ct_gt| |] ct_p]|] ; try by contradiction Hcm_ct.
          by rewrite Hcm_expr Hct_expr //.
        destruct Haft as [_ Haft] ; split.
        + destruct Haft as [Hct_vm _].
          intro k ; specialize (Hct_vm k).
          rewrite /extend_map_with CEP.Lemmas.map2_1bis //.
          destruct (CEP.find k old_ct) as [[| |expr]|] ; last by apply IHsst.
          1-3: destruct Hsf_sub_t as [Hsf_sub_t _] ; specialize (Hsf_sub_t k).
          1-3: destruct (PVM.find k old_vm) ; last by contradiction Hct_vm.
          1-3: specialize Hsf_sub_t with (1 := Logic.eq_refl) ;
               rewrite Hsf_sub_t //.
          (* This solves two of the three goals. *)
          destruct v as [gt|gt|gt|gt|gt] ; try by contradiction Hct_vm.
          1-3: generalize (type_of_expr_submap expr old_tmap tm_tmap_t (proj1 (proj2 Hst_sub_t))) ; intro Hexpr.
          1-3: destruct (type_of_expr expr old_tmap) as [[ft_expr p]|] ; last by contradiction Hct_vm.
          1-3: by rewrite Hexpr //.
        destruct Haft as [_ Haft] ; split.
        + by apply IHsst.
        + intro k.
          destruct Hst_sub_t as [_ [_ Hst_sub_t]] ; specialize (Hst_sub_t k).
          destruct (CEP.find k old_scope) as [[ft p]|] ; last by trivial.
          destruct IHsst as [_ [_ [_ [_ [_ IHsst]]]]] ; specialize (IHsst k).
          specialize Hst_sub_t with (1 := Logic.eq_refl) ; rewrite Hst_sub_t // in IHsst.
  specialize IHssf with (1 := Haft_f) ; clear Haft_f.
  split.
  + exists vm_comp_t, (extend_defined_map_with eb_connmap_t ct_comp_t), (extend_defined_map_with eb_connmap_f
             (extend_defined_map_with eb_connmap_t ct_comp)).
    apply convert_to_connect_stmts_Sem with (1 := Htm_inf) in Hsf_conn ;
          (* The other preconditions should hold because of all_fit_together.
             Best to reformulate convert_to_connect_Sem using that definition? *)
          last (by admit) (* subdomain (combine_when_connections cond eb_connmap_t eb_connmap_f) ct_comp *) ;
          last (by admit) (* ct_has_fully_inferred_ground_types (combine_when_connections cond eb_connmap_t eb_connmap_f) *).
    split.
    - by apply IHsst.
    split.
    - apply Sem_frag_stmts_Equal with (vm_old1 := vm_comp_t)
                  (ct_old1 := (extend_map_with old_ct (extend_defined_map_with eb_connmap_t ct_comp_t)))
                  (vm_new1 := vm_comp) (ct_new1 := (extend_defined_map_with eb_connmap_f (extend_defined_map_with eb_connmap_t ct_comp)))
                  (tmap1 := tmap) ;
            try (by apply CEP.Lemmas.Equal_refl) ;
            first (by apply Hsf_conn).
      by apply IHssf.
    - admit. (* use Hsf_conn? *)
  + admit. (* all should fit together here. *)
* admit.
Admitted.

(* The following is an older version of the lemma.

Lemma ExpandWhens_correct_inductive_cons :
forall (ss : HiFP.hfstmt_seq) (old_vm : CEP.t vertex_type) (old_ct : CEP.t def_expr)
       (sf_vm : CEP.t vertex_type) (old_conn_map sf_ct eb_conn_map : CEP.t def_expr)
       (old_tmap old_scope tm_tmap tm_scope : CEP.t (ftype * HiF.forient))
       (old_comp : HiFP.hfstmt_seq),
    tmap_has_fully_inferred_ground_types old_tmap ->
    vm_and_tmap_compatible old_vm old_tmap ->
    vm_and_ct_compatible old_vm old_ct ->
    stmts_have_fully_inferred_ground_types ss ->
    CEP.submap old_scope old_tmap ->
    stmts_tmap (old_tmap, old_scope) ss sf_vm = Some (tm_tmap, tm_scope) ->
    ExpandBranches_funs ss old_comp old_conn_map old_scope = Some (Qcat old_comp (component_stmts_of ss), eb_conn_map, tm_scope) ->
    Sem_frag_stmts old_vm old_ct (Qcat (component_stmts_of ss)
                                       (convert_to_connect_stmts eb_conn_map))
                   sf_vm sf_ct tm_tmap ->
    (exists (vm_new : CEP.t vertex_type) (ct_new : CEP.t def_expr),
          Sem_frag_stmts old_vm old_ct ss vm_new ct_new tm_tmap) ->
    ct_has_fully_inferred_ground_types old_ct ->
    (*subdomain old_scope old_vm ->*)
    conn_map_covers_scope old_conn_map old_scope ->
    CEP.submap old_conn_map old_ct ->
    Sem_frag_stmts old_vm old_ct ss sf_vm sf_ct tm_tmap
with ExpandWhen_correct_inductive :
forall (s : HiFP.hfstmt) (old_vm : CEP.t vertex_type) (old_ct : CEP.t def_expr)
       (sf_vm : CEP.t vertex_type) (old_conn_map sf_ct eb_conn_map : CEP.t def_expr)
       (old_tmap old_scope tm_tmap tm_scope : CEP.t (ftype * HiF.forient))
       (old_comp : HiFP.hfstmt_seq),
    tmap_has_fully_inferred_ground_types old_tmap ->
    vm_and_tmap_compatible old_vm old_tmap ->
    vm_and_ct_compatible old_vm old_ct ->
    stmt_has_fully_inferred_ground_types s ->
    CEP.submap old_scope old_tmap ->
    stmt_tmap (old_tmap, old_scope) s sf_vm = Some (tm_tmap, tm_scope) ->
    ExpandBranch_fun s old_comp old_conn_map old_scope = Some (Qcat old_comp (component_stmt_of s), eb_conn_map, tm_scope) ->
    Sem_frag_stmts old_vm old_ct (Qcat (component_stmt_of s)
                                       (convert_to_connect_stmts eb_conn_map))
                   sf_vm sf_ct tm_tmap ->
    (exists (vm_new : CEP.t vertex_type) (ct_new : CEP.t def_expr),
          Sem_frag_stmt old_vm old_ct s vm_new ct_new tm_tmap) ->
    ct_has_fully_inferred_ground_types old_ct ->
    (*subdomain old_scope old_vm ->*)
    conn_map_covers_scope old_conn_map old_scope ->
    CEP.submap old_conn_map old_ct ->
    Sem_frag_stmt old_vm old_ct s sf_vm sf_ct tm_tmap.

Proof.
clear ExpandWhens_correct_inductive_cons.
induction ss as [|s ss] ; simpl ; intros.
* (* Qnil. *)
  injection H4 ; clear H4 ; intros ; subst tm_tmap tm_scope.
  injection H5 ; clear H5 ; intro ; intros _ ; subst eb_conn_map.
  assert (ct_has_fully_inferred_ground_types old_conn_map).
        intro ; specialize (H8 k) ; specialize (H10 k).
        destruct (CEP.find k old_conn_map) as [[]|] ; try by reflexivity.
        rewrite (H10 _ Logic.eq_refl) // in H8.
  apply (convert_to_connect_stmts_Sem old_conn_map old_vm old_ct sf_vm sf_ct old_tmap
         H H4 (submap_subdomain old_conn_map old_ct H10)) in H6.
  split ; first by apply H6.
  intro.
  rewrite (proj2 H6).
  rewrite /extend_defined_map_with CEP.Lemmas.map2_1bis //.
  specialize (H10 y).
  destruct (CEP.find y old_conn_map) as [[]|] ; last (by done) ;
        by rewrite (H10 _ Logic.eq_refl) //.
* (* Qcons *)
  rename ExpandWhen_correct_inductive into IHs.
  specialize (IHs s).
  (* Now take apart the premissas of the theorem, to prepare their application in IHs and IHss. *)
  move /andP : H2 => H2.
  destruct (stmt_tmap (old_tmap, old_scope) s sf_vm) as [[tm_tmap_s tm_scope_s]|] eqn: H4s ;
        last by discriminate H4.
  generalize (ExpandBranch_fun_submap s old_comp old_conn_map old_scope) ; intro.
  destruct (ExpandBranch_fun s old_comp old_conn_map old_scope) as [[[eb_comp_s eb_conn_map_s] eb_scope_s]|] eqn: H5s ;
        last by discriminate H5.
  destruct H11 as [H11' [_ H11]] ; subst eb_comp_s.
  generalize (ExpandBranches_funs_submap ss (Qcat old_comp (component_stmt_of s)) eb_conn_map_s eb_scope_s) ; intro.
  rewrite H5 in H12.
  destruct H12 as [_ H12].
  apply Sem_frag_stmts_cat in H6.
  destruct H6 as [sf_vm_comps_compss [sf_ct_comps_compss [H6comps_compss H6cnct]]].
  apply Sem_frag_stmts_cat in H6comps_compss.
  destruct H6comps_compss as [sf_vm_comps [sf_ct_comps [H6comps H6compss]]].
  destruct H7 as [ex_vm_s_ss [ex_ct_s_ss [ex_vm_s [ex_ct_s [H7s H7]]]]].

  (* A few generally usable properties *)
  generalize (stmt_submap sf_vm s old_tmap old_scope H3) ; intro.
  rewrite H4s in H6.
  generalize (stmts_submap sf_vm ss tm_tmap_s tm_scope_s (proj1 H6)) ; intro.
  rewrite H4 in H13.

  (* Now that we have prepared the premissas, let's work on the premissas of IHs. *)
  specialize (IHs old_vm old_ct sf_vm_comps old_conn_map (extend_defined_map_with eb_conn_map_s sf_ct_comps) eb_conn_map_s old_tmap old_scope tm_tmap_s tm_scope_s old_comp
        H H0 H1 (proj1 H2) H3).
  assert (Htm_ind: stmt_tmap (old_tmap, old_scope) s sf_vm_comps = stmt_tmap (old_tmap, old_scope) s sf_vm).
        (* This should hold because sf_vm_comps contains all information needed *)
        admit.
  rewrite H4s in Htm_ind.
  specialize (IHs Htm_ind) ; clear Htm_ind.
  assert (eb_scope_s = tm_scope_s).
        (* This should hold because stmt_tmap and ExpandBranch_fun do the same calculation. *)
        admit.
  subst eb_scope_s.
  specialize (IHs H5s).
  assert (Hsf_ind: Sem_frag_stmts old_vm old_ct
                         (Qcat (component_stmt_of s) (convert_to_connect_stmts eb_conn_map_s))
                         sf_vm_comps (extend_defined_map_with eb_conn_map_s sf_ct_comps)
                         tm_tmap_s).
        apply Sem_frag_stmts_cat.
        exists sf_vm_comps, sf_ct_comps.
        split.
        + (* This should hold because of H6comps; tm_tmap_s contains all information needed *)
          admit.
        + (*apply Sem_frag_stmts_connect.*)
          admit.
  specialize (IHs Hsf_ind) ; clear Hsf_ind.
  assert (Hex_ind: exists (vm_new : CEP.t vertex_type) (ct_new : CEP.t def_expr),
              Sem_frag_stmt old_vm old_ct s vm_new ct_new tm_tmap_s).
         exists ex_vm_s, ex_ct_s.
         (* This should hold because tm_tmap_s contains all necessary information *)
         (*exact H7s.*)
         admit.
  specialize (IHs Hex_ind H8 H9 H10) ; clear Hex_ind.
  (* Now we have finished handling premissas of IHs.
     Simplify the writing a bit: *)
  assert (Hex_eq: CEP.Equal sf_vm_comps ex_vm_s /\ CEP.Equal (extend_defined_map_with eb_conn_map_s sf_ct_comps) ex_ct_s).
        (* This should hold because of fully_inferred_makes_Sem_frag_stmt_unique *)
        admit.
  apply Sem_frag_stmts_Equal with (vm_old2 := sf_vm_comps) (ct_old2 := extend_defined_map_with eb_conn_map_s sf_ct_comps) (vm_new2 := ex_vm_s_ss) (ct_new2 := ex_ct_s_ss) (tmap2 := tm_tmap) in H7 ;
        try (by apply CEP.Lemmas.Equal_refl) ;
        try (by symmetry ; apply Hex_eq).
  clear H7s Hex_eq ex_vm_s ex_ct_s.
  (* Let's turn to IHss. *)
  (*(* First need to find eb_conn_map_ss *)
  assert (H5ss: exists eb_conn_map_ss : CEP.t def_expr, forall old_comp : HiFP.hfstmt_seq,
              ExpandBranches_funs ss old_comp (extend_defined_map_with eb_conn_map_s sf_ct_comps) tm_scope_s =
              Some (Qcat old_comp (component_stmts_of ss), eb_conn_map_ss, tm_scope)).
        (* This should hold because of H5 -- this is perhaps the most difficult part *)
        admit.
  destruct H5ss as [eb_conn_map_ss H5ss].*)
  specialize (IHss sf_vm_comps (extend_defined_map_with eb_conn_map_s sf_ct_comps) sf_vm_comps_compss eb_conn_map_s
                   (extend_defined_map_with eb_conn_map sf_ct_comps_compss) eb_conn_map tm_tmap_s tm_scope_s tm_tmap tm_scope (Qcat old_comp (component_stmt_of s))).
  assert (Htm_ind: tmap_has_fully_inferred_ground_types tm_tmap_s).
        (* This should hold because of H and stmt_tmap_preserves_fully_inferred *)
        admit.
  specialize (IHss Htm_ind) ; clear Htm_ind.
  assert (Hvm_tm_ind: vm_and_tmap_compatible sf_vm_comps tm_tmap_s).
        (* This should hold because of H0 and preservation of compatibility through H4s / H6comps *)
        admit.
  specialize (IHss Hvm_tm_ind) ; clear Hvm_tm_ind.
  assert (Hct_vm_ind: vm_and_ct_compatible sf_vm_comps (extend_defined_map_with eb_conn_map_s sf_ct_comps)).
        (* This should hold because of IHs and preservation of compatibility *)
        admit.
  specialize (IHss Hct_vm_ind (proj2 H2) (proj1 H6)) ; clear Hct_vm_ind.
  assert (Htm_ind: stmts_tmap (tm_tmap_s, tm_scope_s) ss sf_vm_comps_compss = Some (tm_tmap, tm_scope)).
        (* This holds because (CEP.Equal sf_vm sf_vm_comps_compss) (use H6cnct) and H4 *)
        admit.
  rewrite Qcat_assoc in IHss.
  specialize (IHss Htm_ind H5) ; clear Htm_ind.
  assert (Hsf_ind: Sem_frag_stmts sf_vm_comps (extend_defined_map_with eb_conn_map_s sf_ct_comps)
         (Qcat (component_stmts_of ss)
            (convert_to_connect_stmts eb_conn_map)) sf_vm_comps_compss
         (extend_defined_map_with eb_conn_map sf_ct_comps_compss) tm_tmap).
        apply Sem_frag_stmts_cat.
        exists sf_vm_comps_compss, (extend_map_with eb_conn_map_s sf_ct_comps_compss).
        split.
        + (* This should hold because of H6compss and Sem_frag_stmts_component *)
          admit.
        + (* This should hold because of Sem_frag_stmts_connect *)
          admit.
  specialize (IHss Hsf_ind) ; clear Hsf_ind.
  assert (Hex_ind: exists (vm_new : CEP.t vertex_type) (ct_new : CEP.t def_expr),
          Sem_frag_stmts sf_vm_comps (extend_defined_map_with eb_conn_map_s sf_ct_comps) ss vm_new ct_new tm_tmap).
        exists ex_vm_s_ss, ex_ct_s_ss.
        exact H7.
  specialize (IHss Hex_ind) ; clear Hex_ind.
  assert (Hct_ind: ct_has_fully_inferred_ground_types (extend_defined_map_with eb_conn_map_s sf_ct_comps)).
        (* This should hold because Sem_frag_stmt (in IHs) preserves this property. Use H2, H8. *)
        admit.
  specialize (IHss Hct_ind) ; clear Hct_ind.
  assert (Hsc_cm_ind: conn_map_covers_scope eb_conn_map_s tm_scope_s).
        (* This should be proven in a separate lemma; I think it's just going through the definition of ExpandBranches_funs. *)
        admit.
  specialize (IHss Hsc_cm_ind) ; clear Hsc_cm_ind.
  assert (Hcm_ct_ind: CEP.submap eb_conn_map_s (extend_defined_map_with eb_conn_map_s sf_ct_comps)).
        (* This should hold because a conn_map should not contain undefined connections,
           unless they are also undefined in sf_ct_comps. *)
        admit.
  specialize (IHss Hcm_ct_ind) ; clear Hcm_ct_ind.
  (* Now that we have reached both IHs and IHss, let's turn to working on the conclusion. *)
  exists sf_vm_comps, (extend_defined_map_with eb_conn_map_s sf_ct_comps).
  split.
  + (* This should hold because of IHs; the only difference is tm_tmap vs. tm_tmap_s *)
    admit.
  + (* Not sure how to prove this -- but it should work out *)
    admit.
* (* This is simple in most cases.
     Only the Swhen statement requires an induction as before. *)
  clear ExpandWhen_correct_inductive.
  rename ExpandWhens_correct_inductive_cons into IHss.
  induction s as [|var ft|var reg|var mem|var1 var2|var expr|ref expr|ref|cond sst ssf] ; intros.
  + (* Sskip *)
    simpl.
    injection H4 ; clear H4 ; intros ; subst tm_tmap tm_scope.
    simpl in H5 ; injection H5 ; clear H5 ; intro ; intros _ ; subst eb_conn_map.
    admit.
    (*
    apply (convert_to_connect_stmts_Sem old_ct old_vm old_ct sf_vm sf_ct old_tmap H H8 (subdomain_refl old_ct)) in H6.
    split ; first by apply H6.
    destruct H6 as [_ H6].
    apply CEP.Lemmas.Equal_sym in H6.
    apply (CEP.Lemmas.Equal_trans (proj1 (extend_defined_map_with_refl (CEP.Lemmas.Equal_refl old_ct)))) in H6.
    exact H6.*)
  + (* Swire *)
    simpl in H2 ; destruct ft as [gt| |] ; try by discriminate H2.
    simpl in H4 ; destruct (CEP.find var old_tmap) ; first by discriminate H4.

    generalize (fully_inferred_does_not_change gt var sf_vm H2) ; intro Hfinc.
    simpl in Hfinc.
    destruct (match CEP.find var sf_vm with
              | Some (OutPort newgt) | Some (InPort newgt) | Some (Register newgt _ _ _) | Some (Wire newgt) | Some (Node newgt) =>
                  if code_vm_type_equivalent gt newgt
                  then Some (Gtyp newgt, bin_of_nat (var.2 + 1))
                  else None
              | None => None
              end) as [[[gt'| |] p]|] eqn: H4' ;
          rewrite H4' in H4, Hfinc ; clear H4' ;
          last (by discriminate H4) ;
          try (by contradiction Hfinc) ;
          subst gt'.
    injection H4 ; clear H4 ; intros ; subst tm_tmap tm_scope.
    simpl in H5 ; destruct (CEP.find var old_scope) ; first by discriminate H5.
    injection H5 ; clear H5 ; intro ; intros _ ; subst eb_conn_map.
    destruct H6 as [vm' [ct' [H6 H11]]].
    unfold Qcat in H11.
    (*assert (tmap_has_fully_inferred_ground_types (CEP.add var (Gtyp gt, HiF.Duplex) old_tmap)).
          intro ; destruct (v == var) eqn: Hvvar ;
                first (by rewrite CEP.Lemmas.find_add_eq //).
          rewrite (CEP.Lemmas.find_add_neq (elimT negP (negbT Hvvar))) ;
          apply H.*)
    assert (Hct_subdom: subdomain (CEP.add var D_undefined old_conn_map) ct').
          admit.
          (*
          simpl in H6.
          rewrite (CEP.Lemmas.find_add_eq (eq_refl var)) in H6.
          intro.
          destruct (k == var) eqn: Hkvar.
          * rewrite CEP.Lemmas.find_add_eq //.
            move /eqP : Hkvar => Hkvar ; subst var.
            rewrite (surjective_pairing k) -(nat_of_binK k.2) -(add0n k.2)
                    (proj2 (proj2 (proj2 H6)) 0 (ltn0Sn 0)) //.
          * rewrite (CEP.Lemmas.find_add_neq (elimT negP (negbT Hkvar))).
            destruct H6 as [_ [_ [H6 _]]].
            rewrite (surjective_pairing k) (H6 k.1 k.2) ;
                  first (by destruct (CEP.find (k.1, k.2) ct') eqn: Hh ; done).
            destruct (k.1 == var.1) eqn: Hkvar1 ; move /eqP : Hkvar1 => Hkvar1 ;
                  last (by left ; exact Hkvar1).
            destruct (Nat.compare_spec k.2 var.2).
            + rewrite (injective_projections k var Hkvar1 (can_inj nat_of_binK H4)) eq_refl // in Hkvar.
            + right ; left ; rewrite (introT ltP H4) //.
            + right ; right ; rewrite /size_of_ftype add1n (introT ltP H4) //.
            *)
    assert (Hcm_inf: ct_has_fully_inferred_ground_types old_conn_map).
           (* This should probably become another precondition. *)
           admit.
    apply convert_to_connect_stmts_Sem in H11 ;
          last (by exact Hct_subdom) ;
          last (by intro ; destruct (k == var) eqn: Hkvar ;
                   first (by rewrite CEP.Lemmas.find_add_eq //) ;
                   rewrite (CEP.Lemmas.find_add_neq (elimT negP (negbT Hkvar))) ;
                   apply Hcm_inf) ;
          last (by intro ; destruct (v == var) eqn: Hvvar ;
                   first (by rewrite CEP.Lemmas.find_add_eq //) ;
                   rewrite (CEP.Lemmas.find_add_neq (elimT negP (negbT Hvvar))) ;
                   apply H).
    destruct H11 as [H11 H12].
    simpl in H6 ; simpl.
    rewrite (CEP.Lemmas.find_add_eq (eqxx var)) in H6 ;
    rewrite (CEP.Lemmas.find_add_eq (eqxx var)).
    split.
    - destruct H6 as [H6 _].
      intro ; specialize (H6 n) ; rewrite -H11 //.
    destruct H6 as [_ H6] ; split.
    - destruct H6 as [H6 _].
      intros v0 n0 ; specialize (H6 v0 n0) ; rewrite -H11 //.
    destruct H6 as [_ H6] ; split.
    - destruct H6 as [H6 _].
      intros v0 n0 Hvnotvar ; specialize (H6 v0 n0 Hvnotvar).
      destruct ((v0,n0) == var) eqn : Hvvar.
      * rewrite (surjective_pairing var) in Hvvar.
        move /eqP : Hvvar => Hvvar ; injection Hvvar ; clear Hvvar ; intros ; subst v0 n0.
        destruct Hvnotvar as [Hvnotvar|[Hvnotvar|Hvnotvar]].
        + by contradiction Hvnotvar.
        + rewrite ltnn // in Hvnotvar.
        + rewrite /size_of_ftype add1n ltnn // in Hvnotvar.
      * rewrite H12 /extend_defined_map_with CEP.Lemmas.map2_1bis //.
        rewrite (CEP.Lemmas.find_add_neq (elimT negP (negbT Hvvar))) H6.
        admit. (* Here is a problem with the difference between ct' and old_conn_map *)
        (*destruct (CEP.find (v0, n0) ct') as [[]|] ; by reflexivity.*)
    - destruct H6 as [_ H6].
      intros n0 Hn0small ; rewrite /size_of_ftype ltnS leqn0 in Hn0small.
      move /eqP : Hn0small => Hn0small ; subst n0.
      rewrite H12 /extend_defined_map_with CEP.Lemmas.map2_1bis //
              add0n nat_of_binK -surjective_pairing (CEP.Lemmas.find_add_eq (eq_refl var)).
      specialize (H6 0 (ltn0Sn 0)).
      rewrite add0n nat_of_binK -surjective_pairing in H6.
      rewrite H6 //.
  + (* Sreg *)
    simpl in H5 ; destruct (CEP.find var old_scope) ; first by discriminate H5.
    injection H5 ; clear H5 ; intro ; intro ; intros _ ; subst eb_conn_map tm_scope.
    simpl in H4 ; destruct (CEP.find var old_tmap) ; first by discriminate H4.
    destruct (type_of_expr (clock reg) old_scope) ; last by discriminate H4.
    simpl in H2 ; destruct (type reg) as [gt| |] ; try by discriminate H2.
    destruct (reset reg) as [|rst_sig rst_val] ; first last.
    1,2: move /andP : H2 => [_ H2].

    1,2: generalize (fully_inferred_does_not_change gt var sf_vm H2) ; intro.
    1,2: destruct (code_type_find_vm_widths (Gtyp gt) var sf_vm) as [[[gt'| |] p]|] ;
          last (by discriminate H4) ;
          try (by contradiction H5) ;
          subst gt'.
    (*1: generalize (type_of_expr_submap rst_sig old_scope old_tmap H3) ; intro.*)
    1: destruct (type_of_expr rst_sig old_scope) as [[[[[|[|]]| | | | | |]| |] prst]|] ; try by discriminate H4.
    1: destruct (type_of_expr rst_val (CEP.add var (Gtyp gt, HiF.Duplex) old_scope)) ; last by discriminate H4.
    2: destruct (type_of_expr rst_val old_scope) ; last by discriminate H4.
    1-3: injection H4 ; clear H4 ; intro ; subst tm_tmap.
    1-3: destruct H6 as [vm' [ct' [H6 H10]]].
    1-3: unfold Qcat in H10.
    1-3: assert (subdomain (CEP.add var (D_fexpr (Eref (Eid var))) old_ct) ct').
          1,3,5: simpl in H6.
          1-3: rewrite (CEP.Lemmas.find_add_eq (eq_refl var)) in H6.
          1-3: destruct H6 as [_ H6].
          1-3: intro.
          1-3: destruct (k == var) eqn: Hkvar.
          * 1,3,5: rewrite CEP.Lemmas.find_add_eq //.
            1-3: move /eqP : Hkvar => Hkvar ; subst var.
            1-3: by rewrite (surjective_pairing k) -(nat_of_binK k.2) -(add0n k.2)
                    (proj1 (proj2 (proj2 H6)) 0) //.
          * 1-3: rewrite (CEP.Lemmas.find_add_neq (elimT negP (negbT Hkvar))).
            1-3: destruct H6 as [_ [_ [_ [_ H6]]]].
            1-3: rewrite (surjective_pairing k) (H6 k.1 k.2) ;
                  first (by destruct (CEP.find (k.1, k.2) ct') eqn: Hh ; done).
            1-3: destruct (k.1 == var.1) eqn: Hkvar1 ; move /eqP : Hkvar1 => Hkvar1 ;
                  last (by left ; exact Hkvar1).
            1-3: destruct (Nat.compare_spec k.2 var.2).
            + 1,4,7: by rewrite (injective_projections k var Hkvar1 (can_inj nat_of_binK H4)) eq_refl // in Hkvar.
            + 1,3,5: by right ; left ; rewrite (introT ltP H4) //.
            + 1-3: by right ; right ; rewrite /size_of_ftype add1n (introT ltP H4) //.
    1-3: apply convert_to_connect_stmts_Sem in H10 ;
          last (by exact H4) ;
          last (by intro ; destruct (k == var) eqn: Hkvar ;
                   first (by rewrite CEP.Lemmas.find_add_eq //) ;
                   rewrite (CEP.Lemmas.find_add_neq (elimT negP (negbT Hkvar))) ;
                   apply H8) ;
          last (by intro ; destruct (v == var) eqn: Hvvar ;
                   first (by rewrite CEP.Lemmas.find_add_eq //) ;
                   rewrite (CEP.Lemmas.find_add_neq (elimT negP (negbT Hvvar))) ;
                   apply H).
    1-3: destruct H10 as [H10 H11].
    1-3: simpl in H6 ; simpl.
    1-3: rewrite (CEP.Lemmas.find_add_eq (eqxx var)) in H6 ;
         rewrite (CEP.Lemmas.find_add_eq (eqxx var)).
    1-3: split ; first (by apply H6).
    1-3: destruct H6 as [_ H6] ; split ;
         first (by destruct H6 as [H6 _] ;
                   intro ; specialize (H6 n) ; rewrite -H10 //).
    1-3: destruct H6 as [_ H6] ; split ; first (by apply H6).
    1-3: destruct H6 as [_ H6] ; split.
    - 1,3,5: destruct H6 as [H6 _].
      1-3: intro ; specialize (H6 n).
      1-3: destruct (1 <= n) eqn: H1n ;
           first (by apply (elimT ltP), (List.nth_error_None [:: Eref (Eid var)]) in H1n ;
                     rewrite H1n //).
      1-3: apply negbT in H1n.
      1-3: rewrite -eqn0Ngt in H1n.
      1-3: move /eqP : H1n => H1n.
      1-3: rewrite H1n ; simpl ; rewrite H1n in H6 ; simpl in H6.
      1-3: by rewrite H11 add0n nat_of_binK -surjective_pairing
                      /extend_defined_map_with CEP.Lemmas.map2_1bis //
                      (CEP.Lemmas.find_add_eq (eqxx var)) //.
    1-3: destruct H6 as [_ H6] ; split ;
         first (by destruct H6 as [H6 _] ;
                   intros v0 n0 H12 ; specialize (H6 v0 n0 H12) ; rewrite -H10 //).
    1-3: destruct H6 as [_ H6].
    1-3: intros v0 n0 H12 ; specialize (H6 v0 n0 H12).
    1-3: rewrite H11 /extend_defined_map_with CEP.Lemmas.map2_1bis // CEP.Lemmas.find_add_neq ;
         first (by rewrite H6 ; destruct (CEP.find (v0, n0) ct') as [[]|] ; done).
    1-3: rewrite (surjective_pairing var) /PVM.SE.eq ; intro H13 ; move /eqP : H13 => H13.
    1-3: injection H13 ; clear H13 ; intros ; subst v0 n0.
    1-3: destruct H12 as [H12|[H12|H12]] ;
              first (by contradiction H12) ;
              by rewrite ltnn // in H12.
  + (* Smem *)
    simpl in H5 ; discriminate H5.
  + (* Sinst *)
    simpl in H5 ; discriminate H5.
  + (* Snode *)
    simpl in H2.
    specialize (@CEP.Lemmas.submap_none_add _ old_tmap old_tmap var) with (1 := CEP.Lemmas.submap_refl old_tmap) ; intro H11.
    simpl in H4 ; destruct (CEP.find var old_tmap) ; first by discriminate H4.
    specialize H11 with (1 := Logic.eq_refl).
    simpl in H5 ; destruct (CEP.find var old_scope) ; first by discriminate H5.
    generalize (type_of_expr_submap expr old_scope old_tmap H3) ; intro H12.
    destruct (type_of_expr expr old_scope) as [[ft_expr p]|] ; last by discriminate H4.
    injection H4 ; clear H4 ; intro ; intro ; subst tm_tmap tm_scope.
    injection H5 ; clear H5 ; intro ; intros _ ; subst eb_conn_map.

    destruct H6 as [vm' [ct' [H6 H10]]].
    unfold Qcat in H10.
    simpl in H6.
    generalize (expr_preserves_fully_inferred old_tmap H expr H2) ; intro.
    generalize (type_of_expr_submap expr old_tmap (CEP.add var (ft_expr, HiF.Source) old_tmap) (H11 _)) ; intro.
    rewrite H12 in H4, H5 ; clear H11 H12.
    simpl.
    rewrite H5 in H6 ; rewrite H5 ; clear H5.
    apply convert_to_connect_stmts_Sem in H10 ;
          last (by exact (Equal_subdomain _ _ (proj2 (proj2 H6)))) ;
          last (by exact H8) ;
          last (by intro v ; destruct (v == var) eqn: Hvvar ;
                   first (by rewrite CEP.Lemmas.find_add_eq //(* uses H4 *)) ;
                   rewrite (CEP.Lemmas.find_add_neq (elimT negP (negbT Hvvar))) ;
                   apply H).
    destruct H10 as [H10 H11].
    split.
    - destruct H6 as [H6 _].
      intro ; specialize (H6 n) ; rewrite -H10 //.
    destruct H6 as [_ H6] ; split.
    - destruct H6 as [H6 _].
      intros v0 n0 ; specialize (H6 v0 n0) ; rewrite -H10 //.
    - destruct H6 as [_ H6].
      by apply (CEP.Lemmas.Equal_trans (proj1 (extend_defined_map_with_refl H6))),
               CEP.Lemmas.Equal_sym, H11.
  + (* Sfcnct *)
    simpl in H2 ; move /andP : H2 => [_ H2].
    simpl in H5 ; destruct ref as [var| | |] ; try by discriminate H5.
    simpl in H4 ; destruct (CEP.find var old_scope) as [[[gt_ref| |] ori]|] eqn: Hvar ; try by discriminate H5.
    generalize (type_of_expr_submap expr old_scope old_tmap H3) ; intro.
    destruct (type_of_expr expr old_scope) as [[ft_expr p]|] ; last by discriminate H4.
    injection H4 ; clear H4 ; intro ; intro ; subst tm_tmap tm_scope.
    destruct ft_expr as [gt_expr| |], ori ; try by discriminate H5.
    1,2: destruct (match gt_ref with
                   | Fuint _ => match gt_expr with | Fuint _ | Fuint_implicit _ => true | _ => false end
                   | Fsint _ => match gt_expr with | Fsint _ | Fsint_implicit _ => true | _ => false end
                   | Fuint_implicit w_tgt => match gt_expr with | Fuint w_src | Fuint_implicit w_src => w_src <= w_tgt | _ => false end
                   | Fsint_implicit w_tgt => match gt_expr with | Fsint w_src | Fsint_implicit w_src => w_src <= w_tgt | _ => false end
                   | Fclock => match gt_expr with | Fclock => true | _ => false end
                   | Freset => false
                   | Fasyncreset => match gt_expr with | Fasyncreset => true | _ => false end
                   end) eqn: Hconnect_compatible ; last by discriminate H5.
    1,2: injection H5 ; clear H5 ; intro ; intros _ ; subst eb_conn_map.
    1,2: simpl in H6.
    1,2: assert (CEP.find var old_ct <> None).
          1,3: intro.
          1,2: specialize (H0 var) ; specialize (H1 var) ; specialize (H9 var).
          1,2: rewrite H4 in H1.
          1,2: rewrite CEP.Lemmas.map_o /option_map (H3 var _ Hvar) in H0.
          1,2: rewrite Hvar in H9.
          1,2: destruct (CEP.find var old_vm) as [[]|] eqn: Hold_vm ;
                     try (by contradiction H1) ;
                     try (by discriminate H9) ;
                     by specialize (H0 _ Logic.eq_refl) ; discriminate H0.
    1,2: assert (subdomain (CEP.add var (D_fexpr expr) old_ct) old_ct).
          1,3: intro.
          1,2: destruct (k == var) eqn: Hkvar ;
                last by rewrite (CEP.Lemmas.find_add_neq (elimT negP (negbT Hkvar))) ;
                        destruct (CEP.find k old_ct) ; done.
          1,2: rewrite CEP.Lemmas.find_add_eq //.
          1,2: move /eqP : Hkvar => Hkvar ; subst k.
          1,2: specialize (H0 var) ; specialize (H1 var) ; specialize (H9 var).
          1,2: destruct (CEP.find var old_ct) eqn: Hold_ct ; by done.
    1,2: apply convert_to_connect_stmts_Sem in H6 ;
          last (by exact H5) ;
          last (by intro v ; destruct (v == var) eqn: Hvvar ;
                   first (by rewrite CEP.Lemmas.find_add_eq //) ;
                   rewrite (CEP.Lemmas.find_add_neq (elimT negP (negbT Hvvar))) ;
                   apply H8) ;
          last (by exact H).
    1,2: simpl.
    1,2: apply H3 in Hvar.
    1,2: rewrite Hvar H10.
    1,2: generalize (expr_preserves_fully_inferred old_tmap H expr H2) ;
               intro ; rewrite H10 in H11.
    1,2: replace (list_rhs_expr_p expr (Gtyp gt_expr)) with (Some [:: expr])
               by (destruct expr ; reflexivity).
    1,2: unfold mkseq ; simpl ; rewrite N.add_0_r -surjective_pairing Hconnect_compatible.
    1,2: destruct expr ; simpl ; split ; try (by apply H6).
    (* 12 goals for expressions *)
    1-6, 8-13: split ; first by reflexivity.
    1-12: split.
    - 1,3,5,7,9,11,13,15,17,19,21,23: intro.
      1-12: destruct n ; simpl.
      * 1,3,5,7,9,11,13,15,17,19,21,23: split ; first by exact H4.
        1-12: rewrite (proj2 H6) /extend_defined_map_with CEP.Lemmas.map2_1bis //
              (CEP.Lemmas.find_add_eq (eqxx var)) //.
      * 1-12: destruct n ; done.
    - 1-12: intro ; rewrite mem_seq1.
      1-12: destruct (v0 == var) eqn: Hv0var ; first by trivial.
      1-12: rewrite (proj2 H6) /extend_defined_map_with CEP.Lemmas.map2_1bis //
                    (CEP.Lemmas.find_add_neq (elimT negP (negbT Hv0var))) //.
      1-12: destruct (CEP.find v0 old_ct) as [[]|] ; done.
    (* two goals left for references *)
    1,2: admit.
         (* Probably need to split up the proof between expressions and references earlier.
            For references we should not destruct on type_of_expr but on type_of_ref. *)
  + (* Sinvalid *)
    simpl in H5 ; destruct ref as [var| | |] ; try by discriminate H5.
    simpl in H4 ; destruct (CEP.find var old_scope) as [[ft_ref ori]|] eqn: Hvar ; try by discriminate H5.
    injection H4 ; clear H4 ; intro ; intro ; subst tm_tmap tm_scope.
    destruct ori ; try by discriminate H5.
    1,2: injection H5 ; clear H5 ; intro ; intros _ ; subst eb_conn_map.
    1,2: simpl in H6.
    1,2: assert (CEP.find var old_ct <> None).
          1,3: intro.
          1,2: specialize (H0 var) ; specialize (H1 var) ; specialize (H9 var).
          1,2: rewrite H4 in H1.
          1,2: rewrite CEP.Lemmas.map_o /option_map (H3 var _ Hvar) in H0.
          1,2: rewrite Hvar in H9.
          1,2: destruct (CEP.find var old_vm) as [[]|] eqn: Hold_vm ;
                     try (by contradiction H1) ;
                     try (by discriminate H9) ;
                     by specialize (H0 _ Logic.eq_refl) ; discriminate H0.
    1,2: assert (subdomain (CEP.add var D_invalidated old_ct) old_ct).
          1,3: intro.
          1,2: destruct (k == var) eqn: Hkvar ;
                last by rewrite (CEP.Lemmas.find_add_neq (elimT negP (negbT Hkvar))) ;
                        destruct (CEP.find k old_ct) ; done.
          1,2: rewrite CEP.Lemmas.find_add_eq //.
          1,2: move /eqP : Hkvar => Hkvar ; subst k.
          1,2: specialize (H0 var) ; specialize (H1 var) ; specialize (H9 var).
          1,2: destruct (CEP.find var old_ct) eqn: Hold_ct ; by done.
    1,2: apply convert_to_connect_stmts_Sem in H6 ;
          last (by exact H5) ;
          last (by intro v ; destruct (v == var) eqn: Hvvar ;
                   first (by rewrite CEP.Lemmas.find_add_eq //) ;
                   rewrite (CEP.Lemmas.find_add_neq (elimT negP (negbT Hvvar))) ;
                   apply H8) ;
          last (by exact H).
    1,2: simpl.
    1,2: apply H3 in Hvar.
    1,2: specialize (H var) ; rewrite Hvar in H.
    1,2: destruct ft_ref as [gt_ref| |] ; try by contradiction H.
    1,2: rewrite Hvar.
    1,2: unfold mkseq ; simpl ; rewrite N.add_0_r -surjective_pairing.
    1,2: split ; try (by apply H6).
    1-2: split.
    - 1,3: intro.
      1-2: destruct n ; simpl.
      * 1,3: split ; first by exact H4.
        1-2: rewrite (proj2 H6) /extend_defined_map_with CEP.Lemmas.map2_1bis //
              (CEP.Lemmas.find_add_eq (eqxx var)) //.
      * 1-2: destruct n ; done.
    - 1-2: intro ; rewrite mem_seq1.
      1-2: destruct (v0 == var) eqn: Hv0var ; first by trivial.
      1-2: rewrite (proj2 H6) /extend_defined_map_with CEP.Lemmas.map2_1bis //
                    (CEP.Lemmas.find_add_neq (elimT negP (negbT Hv0var))) //.
      1-2: destruct (CEP.find v0 old_ct) as [[]|] ; done.
  + (* Swhen *)
    generalize (IHss sst) ; intro IHsst.
    specialize (IHss ssf) ; rename IHss into IHssf.
    (* now the strategy is:
       first destruct stmts_tmap and ExpandBranches_funs for every subterm
       and add their equations so we can reuse them for other situations.
       After that we can try to prove all premises of H and H0.
       This might work better because we need some submap relations... *)
    simpl in H2.
    rewrite -andbA in H2 ; move /andP : H2 => [_ /andP H2].
    simpl in H4.
    destruct (type_of_expr cond old_scope) ; last by discriminate H4.
    destruct (stmts_tmap (old_tmap, old_scope) sst sf_vm) as [[tm_tmap_true tm_scope_true]|] eqn: Htm_true ;
          last by discriminate H4.
    destruct (stmts_tmap (tm_tmap_true, old_scope) ssf sf_vm) as [[tm_tmap_false tm_scope_false]|] eqn: Htm_false ;
          last by discriminate H4.
    injection H4 ; clear H4 ; intros ; subst tm_tmap_false tm_scope.
    simpl in H5.
    generalize (ExpandBranches_funs_submap sst old_comp old_ct old_scope) ; intro.
    destruct (ExpandBranches_funs sst old_comp old_ct old_scope) as [[[eb_comp_true eb_conn_map_true] eb_scope_true]|] eqn: Heb_true ;
          last by discriminate H5.
    destruct H4 as [H4' H4] ; subst eb_comp_true.
    generalize (ExpandBranches_funs_submap ssf (Qcat old_comp (component_stmts_of sst)) old_ct old_scope) ; intro.
    destruct (ExpandBranches_funs ssf (Qcat old_comp (component_stmts_of sst)) old_ct old_scope) as [[[eb_comp_false eb_conn_map_false] eb_scope_false]|] eqn: Heb_false ;
          last by discriminate H5.
    destruct H10 as [H10' H10] ; subst eb_comp_false.
    injection H5 ; clear H5 ; intros H5 _ ; subst eb_conn_map.
    simpl in H6.
    apply Sem_frag_stmts_cat in H6.
    destruct H6 as [sf_vm_comp [sf_ct_comp [H6comp H6cnct]]].
    apply Sem_frag_stmts_cat in H6comp.
    destruct H6comp as [sf_vm_comp_true [sf_ct_comp_true H6comp]].
    destruct H7 as [ex_vm [ex_ct H7]].
    simpl in H7.
    destruct (type_of_expr cond tm_tmap) as [[[[[|[|]]| | | | | |]| |] p]|] eqn: Hcond ; try by contradiction H7.
    destruct H7 as [ex_vm_true [ex_ct_true [ex_ct_false [H7t H7f]]]].
    (* Now start collecting the premissas of IHsst. *)
    specialize (IHsst old_vm old_ct sf_vm_comp_true (extend_map_with eb_conn_map_true sf_ct_comp_true) eb_conn_map_true old_tmap old_scope tm_tmap_true tm_scope_true old_comp
          H H0 H1 (proj1 H2) H3).
    assert (stmts_tmap (old_tmap, old_scope) sst sf_vm_comp_true = stmts_tmap (old_tmap, old_scope) sst sf_vm).
          (* This should hold because sf_vm_comp_true contains all the elements needed to handle sst *)
          admit.
    rewrite Htm_true in H5.
    specialize (IHsst H5) ; clear H5.
    assert (eb_scope_true = tm_scope_true).
          (* This should hold because ExpandBranches_funs makes the same calculations as stmts_tmap *)
          admit.
    subst eb_scope_true.
    specialize (IHsst Heb_true).
    assert (Sem_frag_stmts old_vm old_ct
                           (Qcat (component_stmts_of sst)
                                 (convert_to_connect_stmts eb_conn_map_true))
                           sf_vm_comp_true (extend_map_with eb_conn_map_true sf_ct_comp_true)
                           tm_tmap_true).
          apply Sem_frag_stmts_cat.
          exists sf_vm_comp_true, sf_ct_comp_true.
          split.
          + admit. (* This should hold because tm_tmap_true contains all the elements needed from tm_tmap *)
          + admit. (* This should hold based on Lemma Sem_frag_stmts_connect *)
    specialize (IHsst H5) ; clear H5.
    assert (exists (vm_new : CEP.t vertex_type) (ct_new : CEP.t def_expr), Sem_frag_stmts old_vm old_ct sst vm_new ct_new tm_tmap_true).
          exists ex_vm_true, ex_ct_true.
          (* This should hold based on H5t, because tm_tmap_true contains all elements needed *)
          admit.
    specialize (IHsst H5) ; clear H5.
    (* simplify notation a bit... *)
    assert (CEP.Equal sf_vm_comp_true ex_vm_true /\ CEP.Equal (extend_map_with eb_conn_map_true sf_ct_comp_true) ex_ct_true).
          (* This holds because of fully_inferred_makes_Sem_frag_stmts_unique, IHsst and H7t. *)
          admit.

    (* Now that we have handled all premissas of IHsst, let's go to the premissas of IHssf. *)
    assert (tmap_has_fully_inferred_ground_types tm_tmap_true).
          (* This should hold because of Lemma stmts_tmap_preserves_fully_inferred and Htm_true *)
          admit.
    specialize (IHssf) with (1 := H6) ; clear H6.
    assert (vm_and_tmap_compatible sf_vm_comp_true tm_tmap_true).
          (* This should hold because of H and Htm_true *)
          admit.
    specialize (IHssf) with (1 := H6) ; clear H6.
    assert (vm_and_ct_compatible sf_vm_comp_true (extend_map_with old_ct ex_ct_true)).
          (* This should hold because of H7t *)
          admit.
    specialize (IHssf) with (1 := H6) (2 := proj2 H2) ; clear H6.
    assert (CEP.submap old_scope tm_tmap_true).
          (* This should hold because of H3 and Htm_true *)
          admit.
    specialize (IHssf) with (1 := H6) (2 := Htm_false) ; clear H6.
    assert (eb_scope_false = tm_scope_false).
          (* This should hold because ExpandBranches_funs makes the same calculations as stmts_tmap *)
          admit.
    subst eb_scope_false.
(* Problem of the following statement:
   old_conn_map is not equal.
   I think we should require that old_conn_map is a *submap* of old_ct instead of identical to old_ct. *)

    specialize (IHssf) with (1 := Heb_false).
    assert (Sem_frag_stmts sf_vm_comp_true (extend_map_with old_ct ex_ct_true)
                           (Qcat (component_stmts_of ssf) (convert_to_connect_stmts eb_conn_map_false))
                           sf_vm (extend_map_with eb_conn_map_false (extend_map_with old_ct ex_ct_true))
                           tm_tmap).
            apply Sem_frag_stmts_cat.
            exists sf_vm_comp, (extend_map_with (extend_map_with old_ct ex_ct_true) sf_ct_comp).
            split.
            + (* use proj2 H6comp and Sem_frag_stmts_component_Equal *)
              admit.
            + (* not sure how to prove this. Perhaps use Sem_frag_stmts_connect? *)
              admit.
    specialize (IHssf) with (1 := H6) ; clear H6.
    assert (exists (vm_new : CEP.t vertex_type) (ct_new : CEP.t def_expr),
                Sem_frag_stmts sf_vm_comp_true (extend_map_with old_ct ex_ct_true)
                               ssf
                               vm_new ct_new tm_tmap).
          exists ex_vm, ex_ct_false.
          apply Sem_frag_stmts_Equal with (vm_old1 := ex_vm_true) (ct_old1 := extend_map_with old_ct ex_ct_true)
                                          (vm_new1 := ex_vm) (ct_new1 := ex_ct_false) (tmap1 := tm_tmap) ;
                try (by apply CEP.Lemmas.Equal_refl) ;
                try (by apply H7f).
          by apply CEP.Lemmas.Equal_sym, H5.
    specialize (IHssf) with (1 := H6) ; clear H6.
    assert (CEP.Equal sf_vm ex_vm /\ CEP.Equal (extend_map_with eb_conn_map_false (extend_map_with old_ct ex_ct_true)) ex_ct_false).
          admit. (* This holds by fully_inferred_makes_Sem_frag_stmts_unique *)
    (* Now that we have handled the premissas of both IHsst and IHssf, let us look at the goal. *)
    simpl.
    rewrite Hcond.
    exists sf_vm_comp_true, (extend_map_with eb_conn_map_true sf_ct_comp_true),
           (extend_map_with eb_conn_map_false (extend_map_with old_ct ex_ct_true)).
    split.
    + admit.
      (* The only difference with IHsst is that we tm_tmap vs. tm_tmap_true.
         This should hold because sst is not influenced by this difference. *)
    split.
    + admit.
      (* The difference with IHssf is actually covered by H6. *)
    + intro.
      rewrite CEP.Lemmas.map2_1bis //.
      (* Now we need to take H6cnct apart,
         basically to show that the connections made by eb_conn_map_true and eb_conn_map_false are correct. *)
      admit.
Admitted.

(* Older version, based on Qrcons_ind:

Definition Ps (s : HiFP.hfstmt) : Prop :=
forall (vm_old : CEP.t vertex_type) (ct_old : CEP.t def_expr)
       (sf_vm : CEP.t vertex_type) (sf_ct eb_conn_map : CEP.t def_expr)
       (old_tmap old_scope tm_tmap tm_scope : CEP.t (ftype * HiF.forient))
       (old_comp : HiFP.hfstmt_seq),
    tmap_has_fully_inferred_ground_types old_tmap ->
    vm_and_tmap_compatible vm_old old_tmap ->
    vm_and_ct_compatible vm_old ct_old ->
    stmt_has_fully_inferred_ground_types s ->
    CEP.submap old_scope old_tmap ->
    stmt_tmap (old_tmap, old_scope) s sf_vm = Some (tm_tmap, tm_scope) ->
    ExpandBranch_fun s old_comp (CEP.empty def_expr) old_scope = Some (Qcat old_comp (component_stmt_of s), eb_conn_map, tm_scope) ->
    Sem_frag_stmts vm_old ct_old (Qcat (component_stmt_of s)
                                       (convert_to_connect_stmts eb_conn_map))
                   sf_vm sf_ct tm_tmap ->
    (exists (vm_new : CEP.t vertex_type) (ct_new : CEP.t def_expr),
          Sem_frag_stmt vm_old ct_old s vm_new ct_new tm_tmap) ->
    Sem_frag_stmt vm_old ct_old s sf_vm sf_ct tm_tmap.

Definition Pss (ss : HiFP.hfstmt_seq) : Prop :=
forall (vm_old : CEP.t vertex_type) (ct_old : CEP.t def_expr)
       (sf_vm : CEP.t vertex_type) (sf_ct eb_conn_map : CEP.t def_expr)
       (old_tmap old_scope tm_tmap tm_scope : CEP.t (ftype * HiF.forient))
       (old_comp : HiFP.hfstmt_seq),
    tmap_has_fully_inferred_ground_types old_tmap ->
    vm_and_tmap_compatible vm_old old_tmap ->
    vm_and_ct_compatible vm_old ct_old ->
    stmts_have_fully_inferred_ground_types ss ->
    CEP.submap old_scope old_tmap ->
    stmts_tmap (old_tmap, old_scope) ss sf_vm = Some (tm_tmap, tm_scope) ->
    ExpandBranches_funs ss old_comp (CEP.empty def_expr) old_scope = Some (Qcat old_comp (component_stmts_of ss), eb_conn_map, tm_scope) ->
    Sem_frag_stmts vm_old ct_old (Qcat (component_stmts_of ss)
                                       (convert_to_connect_stmts eb_conn_map))
                   sf_vm sf_ct tm_tmap ->
    (exists (vm_new : CEP.t vertex_type) (ct_new : CEP.t def_expr),
          Sem_frag_stmts vm_old ct_old ss vm_new ct_new tm_tmap) ->
    Sem_frag_stmts vm_old ct_old ss sf_vm sf_ct tm_tmap.

Lemma ExpandWhens_correct_inductive :
forall ss : HiFP.hfstmt_seq, Pss ss.
Proof.
apply (Qrcons_ind (Ps := Ps)) ; unfold Ps, Pss ; intros.
* (* Sskip *)
  simpl.
  simpl in H5.
  injection H5 ; clear H5 ; intros H8 H9 _ ; subst eb_conn_map tm_scope.
  simpl in H6.
  exact H6.
* (* Swire *)
  simpl in H5.
  injection H5 ; clear H5 ; intros H8 H9 _ ; subst eb_conn_map tm_scope.
  simpl in H6.
  destruct H6 as [vm' [ct' [H6 [H8 H9]]]].
  apply Sem_frag_stmt_Equal with (vm_old1 := vm_old) (ct_old1 := ct_old) (vm_new1 := vm') (ct_new1 := ct') (tmap1 := tm_tmap) ;
        try (by apply CEP.Lemmas.Equal_refl) ;
        by assumption.
* (* Sreg *)
  simpl in H5.
  injection H5 ; clear H5 ; intros H8 H9 _ ; subst eb_conn_map tm_scope.
  simpl in H6.
  destruct H6 as [vm' [ct' [H6 [H8 H9]]]].
  apply Sem_frag_stmt_Equal with (vm_old1 := vm_old) (ct_old1 := ct_old) (vm_new1 := vm') (ct_new1 := ct') (tmap1 := tm_tmap) ;
        try (by apply CEP.Lemmas.Equal_refl) ;
        by assumption.
* (* Smem *)
  simpl in H5 ; discriminate H5.
* (* Sinst *)
  simpl in H5 ; discriminate H5.
* (* Snode *)
  (*simpl in H4 ;*) simpl in H5.
  (*destruct (CEP.find v old_tmap) ; first by discriminate H4.*)
  destruct (type_of_expr e old_scope) as [[ft _]|] ;
        last by discriminate H5.
  injection H5 ; clear H5 ; intros H8 H9 _ ; subst eb_conn_map tm_scope.
  simpl in H6.
  destruct H6 as [vm' [ct' [H6 [H8 H9]]]].
  apply Sem_frag_stmt_Equal with (vm_old1 := vm_old) (ct_old1 := ct_old) (vm_new1 := vm') (ct_new1 := ct') (tmap1 := tm_tmap) ;
        try (by apply CEP.Lemmas.Equal_refl) ;
        by assumption.
* (* Sfcnct *)
  simpl in H5.
  destruct r as [var| | |] ; try by discriminate H5.
  injection H5 ; clear H5 ; intros H8 H9 _ ; subst eb_conn_map tm_scope.
  simpl in H6.
  destruct H6 as [vm' [ct' [H6 [H8 H9]]]].
  apply Sem_frag_stmt_Equal with (vm_old1 := vm_old) (ct_old1 := ct_old) (vm_new1 := vm') (ct_new1 := ct') (tmap1 := tm_tmap) ;
        try (by apply CEP.Lemmas.Equal_refl) ;
        (by assumption).
* (* Sinvalid *)
  simpl in H5.
  destruct r as [var| | |] ; try by discriminate H5.
  injection H5 ; clear H5 ; intros H8 H9 _ ; subst eb_conn_map tm_scope.
  simpl in H6.
  destruct H6 as [vm' [ct' [H6 [H8 H9]]]].
  apply Sem_frag_stmt_Equal with (vm_old1 := vm_old) (ct_old1 := ct_old) (vm_new1 := vm') (ct_new1 := ct') (tmap1 := tm_tmap) ;
        try (by apply CEP.Lemmas.Equal_refl) ;
        (by assumption).
* (* Swhen *)
  (* now the strategy is:
     first destruct stmts_tmap and ExpandBranches_funs for every subterm
     and add their equations so we can reuse them for other situations.
     After that we can try to prove all premises of H and H0.
     This might work better because we need some submap relations... *)
  simpl in H4.
  rewrite -andbA in H4 ; move /andP : H4 => [_ /andP H4].
  simpl in H6.
  destruct (type_of_expr cond old_scope) ; last by discriminate H6.
  destruct (stmts_tmap (old_tmap, old_scope) sst sf_vm) as [[tm_tmap_true tm_scope_true]|] eqn: Htm_true ;
        last by discriminate H6.
  destruct (stmts_tmap (tm_tmap_true, old_scope) ssf sf_vm) as [[tm_tmap_false tm_scope_false]|] eqn: Htm_false ;
        last by discriminate H6.
  injection H6 ; clear H6 ; intros ; subst tm_tmap_false tm_scope.
  simpl in H7.
  generalize (ExpandBranch_components sst old_comp (CEP.empty def_expr) old_scope) ; intro.
  destruct (ExpandBranches_funs sst old_comp (CEP.empty def_expr) old_scope) as [[[eb_comp_true eb_conn_map_true] eb_scope_true]|] eqn: Heb_true ;
        last by discriminate H7.
  specialize H6 with (1 := Logic.eq_refl).
  destruct H6 as [H6' H6] ; subst eb_comp_true.
  specialize H6 with (1 := fun _ H => CEP.empty_1 (CEP.find_2 H)).
  generalize (ExpandBranch_components ssf (Qcat old_comp (component_stmts_of sst)) (CEP.empty def_expr) old_scope) ; intro.
  destruct (ExpandBranches_funs ssf (Qcat old_comp (component_stmts_of sst)) (CEP.empty def_expr) old_scope) as [[[eb_comp_false eb_conn_map_false] eb_scope_false]|] eqn: Heb_false ;
        last by discriminate H7.
  specialize H10 with (1 := Logic.eq_refl).
  destruct H10 as [H10' H10] ; subst eb_comp_false.
  specialize H10 with (1 := fun _ H => CEP.empty_1 (CEP.find_2 H)).
  injection H7 ; clear H7 ; intros H7 _ ; subst eb_conn_map.
  simpl in H8.
  apply Sem_frag_stmts_cat in H8.
  destruct H8 as [sf_vm_comp [sf_ct_comp [H8comp H8cnct]]].
  apply Sem_frag_stmts_cat in H8comp.
  destruct H8comp as [sf_vm_comp_true [sf_ct_comp_true H8comp]].
  destruct H9 as [vm_new [ct_new H9]].
  simpl in H9.
  destruct (type_of_expr cond tm_tmap) as [[[[[|[|]]| | | | | |]| |] p]|] eqn: Hcond ; try by contradiction H9.
  destruct H9 as [sf_vm_true [sf_ct_true [sf_ct_false [H9t H9f]]]].
  (* Now start collecting the premissas of H and H0. *)
  assert (stmts_tmap (old_tmap, old_scope) sst sf_vm_comp_true = stmts_tmap (old_tmap, old_scope) sst sf_vm).
        (* This should hold because sf_vm_comp_true contains all the elements needed to handle sst *)
        admit.
  rewrite Htm_true in H7.
  assert (eb_scope_true = tm_scope_true).
        (* This should hold because ExpandBranches_funs makes the same calculations as stmts_tmap *)
        admit.
  subst eb_scope_true.
  assert (True) by trivial.
  assert (Sem_frag_stmts vm_old ct_old
                         (Qcat (component_stmts_of sst)
                               (convert_to_connect_stmts eb_conn_map_true))
                         sf_vm_comp_true (extend_map_with eb_conn_map_true sf_ct_comp_true)
                         tm_tmap_true).
        apply Sem_frag_stmts_cat.
        exists sf_vm_comp_true, sf_ct_comp_true.
        split.
        + admit. (* This should hold because tm_tmap_true contains all the elements needed from tm_tmap *)
        + admit. (* This should hold based on Lemma Sem_frag_stmts_connect *)
  assert (exists (vm_new : CEP.t vertex_type) (ct_new : CEP.t def_expr), Sem_frag_stmts vm_old ct_old sst vm_new ct_new tm_tmap_true).
        exists sf_vm_true, sf_ct_true.
        (* This should hold based on H9t, because tm_tmap_true contains all elements needed *)
        admit.
  specialize H with (1 := H1) (2 := H2) (3 := H3) (4 := proj1 H4) (5 := H5) (6 := H7) (7 := Heb_true) (8 := H9) (9 := H11).
  assert (CEP.Equal sf_vm_comp_true sf_vm_true /\ CEP.Equal (extend_map_with eb_conn_map_true sf_ct_comp_true) sf_ct_true).
        (* This holds because of fully_inferred_makes_Sem_frag_stmts_unique, H and H9t. *)
        admit.
  (* Now that we have handled all premissas of H, let's go to the premissas of H0. *)
  assert (tmap_has_fully_inferred_ground_types tm_tmap_true).
        (* This should hold because of Lemma stmts_tmap_preserves_fully_inferred and Htm_true *)
        admit.
  assert (vm_and_tmap_compatible sf_vm_comp_true tm_tmap_true).
        (* This should hold because of H2 and Htm_true *)
        admit.
  assert (vm_and_ct_compatible sf_vm_comp_true (extend_map_with ct_old sf_ct_true)).
        (* This should hold because of H9t *)
        admit.
  assert (CEP.submap old_scope tm_tmap_true).
        (* This should hold because of H5 and Htm_true *)
        admit.
  assert (eb_scope_false = tm_scope_false).
        (* This should hold because ExpandBranches_funs makes the same calculations as stmts_tmap *)
        admit.
  subst eb_scope_false.
  assert (Sem_frag_stmts sf_vm_comp_true (extend_map_with ct_old sf_ct_true)
                         (Qcat (component_stmts_of ssf) (convert_to_connect_stmts eb_conn_map_false))
                         sf_vm (extend_map_with eb_conn_map_false (extend_map_with ct_old sf_ct_true))
                         tm_tmap).
          apply Sem_frag_stmts_cat.
          exists sf_vm_comp, (extend_map_with (extend_map_with ct_old sf_ct_true) sf_ct_comp).
          split.
          + (* use proj2 H8comp and Sem_frag_stmts_component_Equal *)
            admit.
          + (* not sure how to prove this. Perhaps use Sem_frag_stmts_connect? *)
            admit.
  assert (exists (vm_new : CEP.t vertex_type) (ct_new : CEP.t def_expr),
              Sem_frag_stmts sf_vm_comp_true (extend_map_with ct_old sf_ct_true)
                             ssf
                             vm_new ct_new tm_tmap).
        exists vm_new, sf_ct_false.
        apply Sem_frag_stmts_Equal with (vm_old1 := sf_vm_true) (ct_old1 := extend_map_with ct_old sf_ct_true)
                                        (vm_new1 := vm_new) (ct_new1 := sf_ct_false) (tmap1 := tm_tmap) ;
              try (by apply CEP.Lemmas.Equal_refl) ;
              try (by apply H9f).
        by apply CEP.Lemmas.Equal_sym, H12.
  specialize H0 with (1 := H13) (2 := H14) (3 := H15) (4 := proj2 H4) (5 := H16) (6 := Htm_false) (7 := Heb_false) (8 := H17) (9 := H18).
  assert (CEP.Equal sf_vm vm_new /\ CEP.Equal (extend_map_with eb_conn_map_false (extend_map_with ct_old sf_ct_true)) sf_ct_false).
        admit. (* This holds by fully_inferred_makes_Sem_frag_stmts_unique *)
  (* Now that we have handled the premissas of both H and H0, let us look at the goal. *)
  simpl.
  rewrite Hcond.
  exists sf_vm_comp_true, (extend_map_with eb_conn_map_true sf_ct_comp_true),
         (extend_map_with eb_conn_map_false (extend_map_with ct_old sf_ct_true)).
  split.
  + admit.
    (* The only difference with H is that we tm_tmap vs. tm_tmap_true.
       This should hold because sst is not influenced by this difference. *)
  split.
  + admit.
    (* The difference with H0 is actually covered by H19. *)
  + intro.
    rewrite CEP.Lemmas.map2_1bis //.
    (* Now we need to take H8cnct apart,
       basically to show that the connections made by eb_conn_map_true and eb_conn_map_false are correct. *)
    admit.
* (* Qnil *)
  simpl.
  simpl in H5.
  injection H5 ; clear H5 ; intros H8 H9 _ ; subst eb_conn_map tm_scope.
  simpl in H6.
  exact H6.
* (* Qrcons *)
  simpl in H4.
Admitted.

Lemma ExpandWhens_correct_inductive_cons :
forall (ss : HiFP.hfstmt_seq) (vm_old : CEP.t vertex_type) (ct_old : CEP.t def_expr)
       (sf_vm : CEP.t vertex_type) (sf_ct eb_conn_map : CEP.t def_expr)
       (old_tmap old_scope tm_tmap tm_scope : CEP.t (ftype * HiF.forient))
       (old_comp : HiFP.hfstmt_seq),
    tmap_has_fully_inferred_ground_types old_tmap ->
    vm_and_tmap_compatible vm_old old_tmap ->
    vm_and_ct_compatible vm_old ct_old ->
    stmts_have_fully_inferred_ground_types ss ->
    CEP.submap old_scope old_tmap ->
    stmts_tmap (old_tmap, old_scope) ss sf_vm = Some (tm_tmap, tm_scope) ->
    ExpandBranches_funs ss old_comp (CEP.empty def_expr) old_scope = Some (Qcat old_comp (component_stmts_of ss), eb_conn_map, tm_scope) ->
    Sem_frag_stmts vm_old ct_old (Qcat (component_stmts_of ss)
                                       (convert_to_connect_stmts eb_conn_map))
                   sf_vm sf_ct tm_tmap ->
    (exists (vm_new : CEP.t vertex_type) (ct_new : CEP.t def_expr),
          Sem_frag_stmts vm_old ct_old ss vm_new ct_new tm_tmap) ->
    Sem_frag_stmts vm_old ct_old ss sf_vm sf_ct tm_tmap
with ExpandWhen_correct_inductive :
forall (s : HiFP.hfstmt) (vm_old : CEP.t vertex_type) (ct_old : CEP.t def_expr)
       (sf_vm : CEP.t vertex_type) (sf_ct eb_conn_map : CEP.t def_expr)
       (old_tmap old_scope tm_tmap tm_scope : CEP.t (ftype * HiF.forient))
       (old_comp : HiFP.hfstmt_seq),
    tmap_has_fully_inferred_ground_types old_tmap ->
    vm_and_tmap_compatible vm_old old_tmap ->
    vm_and_ct_compatible vm_old ct_old ->
    stmt_has_fully_inferred_ground_types s ->
    CEP.submap old_scope old_tmap ->
    stmt_tmap (old_tmap, old_scope) s sf_vm = Some (tm_tmap, tm_scope) ->
    ExpandBranch_fun s old_comp (CEP.empty def_expr) old_scope = Some (Qcat old_comp (component_stmt_of s), eb_conn_map, tm_scope) ->
    Sem_frag_stmts vm_old ct_old (Qcat (component_stmt_of s)
                                       (convert_to_connect_stmts eb_conn_map))
                   sf_vm sf_ct tm_tmap ->
    (exists (vm_new : CEP.t vertex_type) (ct_new : CEP.t def_expr),
          Sem_frag_stmt vm_old ct_old s vm_new ct_new tm_tmap) ->
    Sem_frag_stmt vm_old ct_old s sf_vm sf_ct tm_tmap.

Proof.
clear ExpandWhens_correct_inductive_cons.
induction ss as [|s ss] ; simpl ; intros.
* (* Qnil. *)
  injection H5 ; clear H5 ; intros H8 H9 _ ; subst eb_conn_map tm_scope.
  simpl in H6.
  exact H6.
* (* Qcons *)
  rename ExpandWhen_correct_inductive into IHs.
  specialize (IHs s).
  (* Now take apart the premissas of the theorem, to prepare their application in IHs and IHss. *)
  move /andP : H2 => H2.
  destruct (stmt_tmap (old_tmap, old_scope) s sf_vm) as [[tm_tmap_s tm_scope_s]|] eqn: H4s ;
        last by discriminate H4.
  generalize (ExpandBranch_component s old_comp (CEP.empty def_expr) old_scope) ; intro.
  destruct (ExpandBranch_fun s old_comp (CEP.empty def_expr) old_scope) as [[[eb_comp_s eb_conn_map_s] eb_scope_s]|] eqn: H5s ;
        last by discriminate H5.
  specialize H8 with (1 := Logic.eq_refl).
  destruct H8 as [H8' H8] ; subst eb_comp_s.
  specialize H8 with (1 := fun _ H => CEP.empty_1 (CEP.find_2 H)).
  generalize (ExpandBranch_components ss (Qcat old_comp (component_stmt_of s)) eb_conn_map_s eb_scope_s) ; intro.
  rewrite H5 in H9.
  specialize H9 with (1 := Logic.eq_refl).
  destruct H9 as [_ H9].
  specialize H9 with (1 := H8).
  apply Sem_frag_stmts_cat in H6.
  destruct H6 as [sf_vm_comps_compss [sf_ct_comps_compss [H6comps_compss H6cnct]]].
  apply Sem_frag_stmts_cat in H6comps_compss.
  destruct H6comps_compss as [sf_vm_comps [sf_ct_comps [H6comps H6compss]]].
  destruct H7 as [ex_vm_s_ss [ex_ct_s_ss [ex_vm_s [ex_ct_s [H7s H7]]]]].

  (* A few generally usable properties *)
  generalize (stmt_submap sf_vm s old_tmap old_scope H3) ; intro.
  rewrite H4s in H6.
  generalize (stmts_submap sf_vm ss tm_tmap_s tm_scope_s (proj1 H6)) ; intro.
  rewrite H4 in H10.

  (* Now that we have prepared the premissas, let's work on the premissas of IHs. *)
  specialize (IHs vm_old ct_old sf_vm_comps (extend_map_with eb_conn_map_s sf_ct_comps) eb_conn_map_s old_tmap old_scope tm_tmap_s tm_scope_s old_comp
        H H0 H1 (proj1 H2) H3).
  assert (stmt_tmap (old_tmap, old_scope) s sf_vm_comps = stmt_tmap (old_tmap, old_scope) s sf_vm).
        (* This should hold because sf_vm_comps contains all information needed *)
        admit.
  rewrite H4s in H11.
  specialize (IHs H11) ; clear H11.
  assert (eb_scope_s = tm_scope_s).
        (* This should hold because stmt_tmap and ExpandBranch_fun do the same calculation. *)
        admit.
  subst eb_scope_s.
  specialize (IHs H5s).
  assert (Sem_frag_stmts vm_old ct_old
                         (Qcat (component_stmt_of s) (convert_to_connect_stmts eb_conn_map_s))
                         sf_vm_comps (extend_map_with eb_conn_map_s sf_ct_comps)
                         tm_tmap_s).
        apply Sem_frag_stmts_cat.
        exists sf_vm_comps, sf_ct_comps.
        split.
        + (* This should hold because of H6comps; tm_tmap_s contains all information needed *)
          admit.
        + (*apply Sem_frag_stmts_connect.*)
          admit.
  specialize (IHs H11) ; clear H11.
  assert (exists (vm_new : CEP.t vertex_type) (ct_new : CEP.t def_expr),
              Sem_frag_stmt vm_old ct_old s vm_new ct_new tm_tmap_s).
         exists ex_vm_s, ex_ct_s.
         (* This should hold because tm_tmap_s contains all necessary information *)
         (*exact H7s.*)
         admit.
  specialize (IHs H11) ; clear H11.
  (* Now we have finished handling premissas of IHs.
     Simplify the writing a bit: *)
  assert (CEP.Equal sf_vm_comps ex_vm_s /\ CEP.Equal (extend_map_with eb_conn_map_s sf_ct_comps) ex_ct_s).
        (* This should hold because of fully_inferred_makes_Sem_frag_stmt_unique *)
        admit.
  (* Let's turn to IHss. *)
  (* First need to find eb_conn_map_ss *)
  assert (H5ss: exists eb_conn_map_ss : CEP.t def_expr, forall old_comp : HiFP.hfstmt_seq,
              ExpandBranches_funs ss old_comp (CEP.empty def_expr) tm_scope_s =
              Some (Qcat old_comp (component_stmts_of ss), eb_conn_map_ss, tm_scope)).
        (* This should hold because of H5 *)
        admit.
  destruct H5ss as [eb_conn_map_ss H5ss].
  specialize (IHss ex_vm_s ex_ct_s sf_vm_comps_compss (extend_map_with eb_conn_map_ss ex_ct_s) eb_conn_map_ss tm_tmap_s tm_scope_s tm_tmap tm_scope (Qcat old_comp (component_stmt_of s))).
  assert (tmap_has_fully_inferred_ground_types tm_tmap_s).
        (* This should hold because of H and stmt_tmap_preserves_fully_inferred *)
        admit.
  specialize (IHss H12) ; clear H12.
  assert (vm_and_tmap_compatible ex_vm_s tm_tmap_s).
        (* This should hold because of H0 and preservation of compatibility through H4s / H6comps *)
        admit.
  specialize (IHss H12) ; clear H12.
  assert (vm_and_ct_compatible ex_vm_s ex_ct_s).
        (* This should hold because of IHs and preservation of compatibility *)
        admit.
  specialize (IHss H12 (proj2 H2) (proj1 H6)) ; clear H12.
  assert (stmts_tmap (tm_tmap_s, tm_scope_s) ss sf_vm_comps_compss = Some (tm_tmap, tm_scope)).
        (* This holds because (CEP.Equal sf_vm sf_vm_comps_compss) and H4 *)
        admit.
  specialize (IHss H12 (H5ss (Qcat old_comp (component_stmt_of s)))) ; clear H12.
  assert (Sem_frag_stmts ex_vm_s ex_ct_s
         (Qcat (component_stmts_of ss)
            (convert_to_connect_stmts eb_conn_map_ss)) sf_vm_comps_compss
         (extend_map_with eb_conn_map_ss ex_ct_s) tm_tmap).
        apply Sem_frag_stmts_cat.
        exists sf_vm_comps_compss, (extend_map_with ex_ct_s sf_ct_comps_compss).
        split.
        + (* This should hold because of H6compss and Sem_frag_stmts_component *)
          admit.
        + (* This should hold because of Sem_frag_stmts_connect *)
          admit.
  specialize (IHss H12) ; clear H12.
  assert (exists (vm_new : CEP.t vertex_type) (ct_new : CEP.t def_expr),
          Sem_frag_stmts ex_vm_s ex_ct_s ss vm_new ct_new tm_tmap).
        exists ex_vm_s_ss, ex_ct_s_ss.
        exact H7.
  specialize (IHss H12) ; clear H12.

  (* Now that we have reached both IHs and IHss, let's turn to working on the conclusion. *)
  exists sf_vm_comps, (extend_map_with eb_conn_map_s sf_ct_comps).
  split.
  + (* This should hold because of IHs; the only difference is tm_tmap vs. tm_tmap_s *)
    admit.
  + (* Not sure how to prove this -- but it should work out *)
    admit.
* (* This is proven as above; simple in most cases.
     Only the Swhen statement requires an induction as before. *)
  clear ExpandWhen_correct_inductive.
  rename ExpandWhens_correct_inductive_cons into IHss.
  induction s as [|var ft|var reg|var mem|var1 var2|var expr|ref expr|ref|cond sst ssf]; intros.
  + (* Sskip *)
    simpl in H5.
    injection H5 ; clear H5 ; intros H8 H9 _ ; subst eb_conn_map tm_scope.
    simpl in H6.
    exact H6.
  + (* Swire *)
    simpl in H5.
    injection H5 ; clear H5 ; intros H8 H9 _ ; subst eb_conn_map tm_scope.
    unfold convert_to_connect_stmts, CEP.fold in H6.
    simpl in H6.
    destruct H6 as [vm' [ct' [H6 [H8 H9]]]].
    apply Sem_frag_stmt_Equal with (vm_old1 := vm_old) (ct_old1 := ct_old) (vm_new1 := vm') (ct_new1 := ct') (tmap1 := tm_tmap) ;
          try (by apply CEP.Lemmas.Equal_refl) ;
          by assumption.
  + (* Sreg *)
    simpl in H5.
    injection H5 ; clear H5 ; intros H8 H9 _ ; subst eb_conn_map tm_scope.
    simpl in H6.
    destruct H6 as [vm' [ct' [H6 [H8 H9]]]].
    apply Sem_frag_stmt_Equal with (vm_old1 := vm_old) (ct_old1 := ct_old) (vm_new1 := vm') (ct_new1 := ct') (tmap1 := tm_tmap) ;
          try (by apply CEP.Lemmas.Equal_refl) ;
          by assumption.
  + (* Smem *)
    simpl in H5 ; discriminate H5.
  + (* Sinst *)
    simpl in H5 ; discriminate H5.
  + (* Snode *)
    (*simpl in H4 ;*) simpl in H5.
    (*destruct (CEP.find v old_tmap) ; first by discriminate H4.*)
    destruct (type_of_expr expr old_scope) as [[ft _]|] ;
          last by discriminate H5.
    injection H5 ; clear H5 ; intros H8 H9 _ ; subst eb_conn_map tm_scope.
    simpl in H6.
    destruct H6 as [vm' [ct' [H6 [H8 H9]]]].
    apply Sem_frag_stmt_Equal with (vm_old1 := vm_old) (ct_old1 := ct_old) (vm_new1 := vm') (ct_new1 := ct') (tmap1 := tm_tmap) ;
          try (by apply CEP.Lemmas.Equal_refl) ;
          by assumption.
  + (* Sfcnct *)
    simpl in H5.
    destruct ref as [var| | |] ; try by discriminate H5.
    injection H5 ; clear H5 ; intros H8 H9 _ ; subst eb_conn_map tm_scope.
    simpl in H6.
    destruct H6 as [vm' [ct' [H6 [H8 H9]]]].
    apply Sem_frag_stmt_Equal with (vm_old1 := vm_old) (ct_old1 := ct_old) (vm_new1 := vm') (ct_new1 := ct') (tmap1 := tm_tmap) ;
          try (by apply CEP.Lemmas.Equal_refl) ;
          (by assumption).
  + (* Sinvalid *)
    simpl in H5.
    destruct ref as [var| | |] ; try by discriminate H5.
    injection H5 ; clear H5 ; intros H8 H9 _ ; subst eb_conn_map tm_scope.
    simpl in H6.
    destruct H6 as [vm' [ct' [H6 [H8 H9]]]].
    apply Sem_frag_stmt_Equal with (vm_old1 := vm_old) (ct_old1 := ct_old) (vm_new1 := vm') (ct_new1 := ct') (tmap1 := tm_tmap) ;
          try (by apply CEP.Lemmas.Equal_refl) ;
          (by assumption).
  + (* Swhen *)
    generalize (IHss sst) ; intro IHsst.
    specialize (IHss ssf) ; rename IHss into IHssf.
    (* now the strategy is:
       first destruct stmts_tmap and ExpandBranches_funs for every subterm
       and add their equations so we can reuse them for other situations.
       After that we can try to prove all premises of H and H0.
       This might work better because we need some submap relations... *)
    simpl in H2.
    rewrite -andbA in H2 ; move /andP : H2 => [_ /andP H2].
    simpl in H4.
    destruct (type_of_expr cond old_scope) ; last by discriminate H4.
    destruct (stmts_tmap (old_tmap, old_scope) sst sf_vm) as [[tm_tmap_true tm_scope_true]|] eqn: Htm_true ;
          last by discriminate H4.
    destruct (stmts_tmap (tm_tmap_true, old_scope) ssf sf_vm) as [[tm_tmap_false tm_scope_false]|] eqn: Htm_false ;
          last by discriminate H4.
    injection H4 ; clear H4 ; intros ; subst tm_tmap_false tm_scope.
    simpl in H5.
    generalize (ExpandBranch_components sst old_comp (CEP.empty def_expr) old_scope) ; intro.
    destruct (ExpandBranches_funs sst old_comp (CEP.empty def_expr) old_scope) as [[[eb_comp_true eb_conn_map_true] eb_scope_true]|] eqn: Heb_true ;
          last by discriminate H5.
    specialize H4 with (1 := Logic.eq_refl).
    destruct H4 as [H4' H4] ; subst eb_comp_true.
    specialize H4 with (1 := fun _ H => CEP.empty_1 (CEP.find_2 H)).
    generalize (ExpandBranch_components ssf (Qcat old_comp (component_stmts_of sst)) (CEP.empty def_expr) old_scope) ; intro.
    destruct (ExpandBranches_funs ssf (Qcat old_comp (component_stmts_of sst)) (CEP.empty def_expr) old_scope) as [[[eb_comp_false eb_conn_map_false] eb_scope_false]|] eqn: Heb_false ;
          last by discriminate H5.
    specialize H8 with (1 := Logic.eq_refl).
    destruct H8 as [H8' H8] ; subst eb_comp_false.
    specialize H8 with (1 := fun _ H => CEP.empty_1 (CEP.find_2 H)).
    injection H5 ; clear H5 ; intros H5 _ ; subst eb_conn_map.
    simpl in H6.
    apply Sem_frag_stmts_cat in H6.
    destruct H6 as [sf_vm_comp [sf_ct_comp [H6comp H6cnct]]].
    apply Sem_frag_stmts_cat in H6comp.
    destruct H6comp as [sf_vm_comp_true [sf_ct_comp_true H6comp]].
    destruct H7 as [ex_vm [ex_ct H7]].
    simpl in H7.
    destruct (type_of_expr cond tm_tmap) as [[[[[|[|]]| | | | | |]| |] p]|] eqn: Hcond ; try by contradiction H7.
    destruct H7 as [ex_vm_true [ex_ct_true [ex_ct_false [H7t H7f]]]].
    (* Now start collecting the premissas of IHsst. *)
    specialize (IHsst vm_old ct_old sf_vm_comp_true (extend_map_with eb_conn_map_true sf_ct_comp_true) eb_conn_map_true old_tmap old_scope tm_tmap_true tm_scope_true old_comp
          H H0 H1 (proj1 H2) H3).
    assert (stmts_tmap (old_tmap, old_scope) sst sf_vm_comp_true = stmts_tmap (old_tmap, old_scope) sst sf_vm).
          (* This should hold because sf_vm_comp_true contains all the elements needed to handle sst *)
          admit.
    rewrite Htm_true in H5.
    specialize (IHsst H5) ; clear H5.
    assert (eb_scope_true = tm_scope_true).
          (* This should hold because ExpandBranches_funs makes the same calculations as stmts_tmap *)
          admit.
    subst eb_scope_true.
    specialize (IHsst Heb_true).
    assert (Sem_frag_stmts vm_old ct_old
                           (Qcat (component_stmts_of sst)
                                 (convert_to_connect_stmts eb_conn_map_true))
                           sf_vm_comp_true (extend_map_with eb_conn_map_true sf_ct_comp_true)
                           tm_tmap_true).
          apply Sem_frag_stmts_cat.
          exists sf_vm_comp_true, sf_ct_comp_true.
          split.
          + admit. (* This should hold because tm_tmap_true contains all the elements needed from tm_tmap *)
          + admit. (* This should hold based on Lemma Sem_frag_stmts_connect *)
    specialize (IHsst H5) ; clear H5.
    assert (exists (vm_new : CEP.t vertex_type) (ct_new : CEP.t def_expr), Sem_frag_stmts vm_old ct_old sst vm_new ct_new tm_tmap_true).
          exists ex_vm_true, ex_ct_true.
          (* This should hold based on H5t, because tm_tmap_true contains all elements needed *)
          admit.
    specialize (IHsst H5) ; clear H5.
    (* simplify notation a bit... *)
    assert (CEP.Equal sf_vm_comp_true ex_vm_true /\ CEP.Equal (extend_map_with eb_conn_map_true sf_ct_comp_true) ex_ct_true).
          (* This holds because of fully_inferred_makes_Sem_frag_stmts_unique, IHsst and H7t. *)
          admit.

    (* Now that we have handled all premissas of IHsst, let's go to the premissas of IHssf. *)
    assert (tmap_has_fully_inferred_ground_types tm_tmap_true).
          (* This should hold because of Lemma stmts_tmap_preserves_fully_inferred and Htm_true *)
          admit.
    specialize (IHssf) with (1 := H6) ; clear H6.
    assert (vm_and_tmap_compatible sf_vm_comp_true tm_tmap_true).
          (* This should hold because of H and Htm_true *)
          admit.
    specialize (IHssf) with (1 := H6) ; clear H6.
    assert (vm_and_ct_compatible sf_vm_comp_true (extend_map_with ct_old ex_ct_true)).
          (* This should hold because of H7t *)
          admit.
    specialize (IHssf) with (1 := H6) (2 := proj2 H2) ; clear H6.
    assert (CEP.submap old_scope tm_tmap_true).
          (* This should hold because of H3 and Htm_true *)
          admit.
    specialize (IHssf) with (1 := H6) (2 := Htm_false) ; clear H6.
    assert (eb_scope_false = tm_scope_false).
          (* This should hold because ExpandBranches_funs makes the same calculations as stmts_tmap *)
          admit.
    subst eb_scope_false.
    specialize (IHssf) with (1 := Heb_false).
    assert (Sem_frag_stmts sf_vm_comp_true (extend_map_with ct_old ex_ct_true)
                           (Qcat (component_stmts_of ssf) (convert_to_connect_stmts eb_conn_map_false))
                           sf_vm (extend_map_with eb_conn_map_false (extend_map_with ct_old ex_ct_true))
                           tm_tmap).
            apply Sem_frag_stmts_cat.
            exists sf_vm_comp, (extend_map_with (extend_map_with ct_old ex_ct_true) sf_ct_comp).
            split.
            + (* use proj2 H6comp and Sem_frag_stmts_component_Equal *)
              admit.
            + (* not sure how to prove this. Perhaps use Sem_frag_stmts_connect? *)
              admit.
    specialize (IHssf) with (1 := H6) ; clear H6.
    assert (exists (vm_new : CEP.t vertex_type) (ct_new : CEP.t def_expr),
                Sem_frag_stmts sf_vm_comp_true (extend_map_with ct_old ex_ct_true)
                               ssf
                               vm_new ct_new tm_tmap).
          exists ex_vm, ex_ct_false.
          apply Sem_frag_stmts_Equal with (vm_old1 := ex_vm_true) (ct_old1 := extend_map_with ct_old ex_ct_true)
                                          (vm_new1 := ex_vm) (ct_new1 := ex_ct_false) (tmap1 := tm_tmap) ;
                try (by apply CEP.Lemmas.Equal_refl) ;
                try (by apply H7f).
          by apply CEP.Lemmas.Equal_sym, H5.
    specialize (IHssf) with (1 := H6) ; clear H6.
    assert (CEP.Equal sf_vm ex_vm /\ CEP.Equal (extend_map_with eb_conn_map_false (extend_map_with ct_old ex_ct_true)) ex_ct_false).
          admit. (* This holds by fully_inferred_makes_Sem_frag_stmts_unique *)
    (* Now that we have handled the premissas of both IHsst and IHssf, let us look at the goal. *)
    simpl.
    rewrite Hcond.
    exists sf_vm_comp_true, (extend_map_with eb_conn_map_true sf_ct_comp_true),
           (extend_map_with eb_conn_map_false (extend_map_with ct_old ex_ct_true)).
    split.
    + admit.
      (* The only difference with IHsst is that we tm_tmap vs. tm_tmap_true.
         This should hold because sst is not influenced by this difference. *)
    split.
    + admit.
      (* The difference with IHssf is actually covered by H6. *)
    + intro.
      rewrite CEP.Lemmas.map2_1bis //.
      (* Now we need to take H6cnct apart,
         basically to show that the connections made by eb_conn_map_true and eb_conn_map_false are correct. *)
      admit.
Admitted. *)
