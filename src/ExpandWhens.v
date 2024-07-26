From Coq Require Import BinNat ZArith.
From mathcomp Require Import ssreflect ssrbool eqtype seq fintype ssrnat div ssrfun.
From simplssrlib Require Import SsrOrder Var FMaps.
From firrtl Require Import Firrtl Env HiEnv HiFirrtl ModuleGraph_oriented.

(* In this version ExpandBranches_funs does only typecheck what is strictly necessary.
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

Definition port_has_fully_inferred_ground_types
    (* checks the precondition of ExpandWhens on a port *)
    (p : HiFP.hfport) (* port to be checked *)
:   bool
:=  match p with
    | Finput _ (Gtyp gt)
    | Foutput _ (Gtyp gt) => fully_inferred gt
    | _ => false
    end.

Fixpoint ports_have_fully_inferred_ground_types
    (* checks the precondition of ExpandWhens on a port sequences *)
    (pp: seq HiFP.hfport)
:   bool
:=  match pp with
    | [::] => true
    | p :: pp' => port_has_fully_inferred_ground_types p && ports_have_fully_inferred_ground_types pp'
    end.

Definition module_has_fully_inferred_ground_types
    (* checks the precondition of ExpandWhens on a module *)
    (m : HiFP.hfmodule)
:   bool
:=  match m with
    | FInmod _ pp ss => ports_have_fully_inferred_ground_types pp && stmts_have_fully_inferred_ground_types ss
    | FExmod _ _ _ => false
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
                            | Node gt _ => (Gtyp gt, HiF.Source)
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
    (old_conn_map : CEP.t def_expr)    (* connections made by earlier statements in the sequence (used for recursion) *)
    (old_scope    : CEP.t (ftype * HiF.forient)) (* part of module graph vertices that is currently in scope *)
:   option (CEP.t def_expr * CEP.t (ftype * HiF.forient))
    (* old_conn_map, extended with the connection statements in ss,
       and old_scope, extended with the component statements in ss that remain in scope *)
:=  match ss with
    | Qnil => Some (old_conn_map, old_scope)
    | Qcons s ss =>
        match ExpandBranch_fun s old_conn_map old_scope with
        | Some (temp_conn_map, temp_scope) =>
            ExpandBranches_funs ss temp_conn_map temp_scope
        | None => None
        end
    end
with ExpandBranch_fun
    (* split a single statement (possibly consisting of a when
       statement) into a sequence that defines components and a
       connection map.  The output does not contain when statements. *)
    (s            : HiFP.hfstmt)       (* a single statement being translated *)
    (old_conn_map : CEP.t def_expr)    (* connections made by earlier statements in the sequence (used for recursion) *)
    (old_scope    : CEP.t (ftype * HiF.forient)) (* part of module graph vertices that is currently in scope *)
:   option (CEP.t def_expr * CEP.t (ftype * HiF.forient))
    (* old_comp_ss, extended with the component statements in s,
       old_conn_map, extended with the connection statements in s,
       and old_scope, extended with the component statements in s that remain in scope *)
:=  match s with
    | Sskip => Some (old_conn_map, old_scope)
    | Swire var ft =>
        match CEP.find var old_scope with
        | None => Some (CEP.add var D_undefined old_conn_map, CEP.add var (ft, HiF.Duplex) old_scope)
        | Some _ => None
        end
    | Sreg var reg =>
        match CEP.find var old_scope, type_of_expr (clock reg) old_scope with
        | None, Some _ =>
            match reset reg with
            | NRst => Some (CEP.add var (D_fexpr (Eref (Eid var))) old_conn_map, CEP.add var ((type reg), HiF.Duplex) old_scope)
            | Rst rst_sig rst_val =>
                match type_of_expr rst_sig old_scope with
                | Some (exist (Gtyp (Fuint 1)) _) =>
                    match type_of_expr rst_val (CEP.add var ((type reg), HiF.Duplex) old_scope) with
                    | Some _ => Some (CEP.add var (D_fexpr (Eref (Eid var))) old_conn_map, CEP.add var ((type reg), HiF.Duplex) old_scope)
                    | None => None
                    end
                | Some (exist (Gtyp Fasyncreset) _) =>
                    match type_of_expr rst_val old_scope with
                    | Some _ => Some (CEP.add var (D_fexpr (Eref (Eid var))) old_conn_map, CEP.add var ((type reg), HiF.Duplex) old_scope)
                    | None => None
                    end
                | _ => None
                end
            end
        | _, _ => None
        end
    | Smem var mem => None
    | Sinst var1 var2 => None
    | Snode var expr =>
        match CEP.find var old_scope, type_of_expr expr old_scope with
        | None, Some (exist ft _) =>
            Some (old_conn_map, CEP.add var (ft, HiF.Source) old_scope)
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
                then Some (CEP.add var (D_fexpr expr) old_conn_map, old_scope)
                else None
            | _ => None
            end
        | _ => None
        end
    | Sinvalid (Eid var) =>
        match type_of_ref (Eid var) old_scope with
        | Some (_, HiF.Duplex) | Some (_, HiF.Sink) =>
            Some (CEP.add var D_invalidated old_conn_map, old_scope)
        | _ => None
        end
    | Swhen cond ss_true ss_false =>
        match type_of_expr cond old_scope, ExpandBranches_funs ss_true old_conn_map old_scope with
        | Some (exist (Gtyp (Fuint 1)) _), Some (true_conn_map, _) =>
            match ExpandBranches_funs ss_false old_conn_map old_scope with
            | Some (false_conn_map, _) =>
                Some (combine_when_connections cond true_conn_map false_conn_map, old_scope)
            | _ => None
            end
        | _, _ => None
        end
    | _ => None
    end.

Fixpoint ExpandPorts_fun
    (* create a module graph for the port sequence pp.
       Out ports need to be assigned value “undefined”;
       in ports do not need to be assigned any value.
       Because types have been lowered already, we can assume
       that all ports have ground types. *)
    (pp : seq HiFP.hfport) (* the sequence of ports of the module *)
:   option (CEP.t def_expr * CEP.t (ftype * HiF.forient)) (* result: a connection map and a scope map for the ports *)
:=  match pp with
    | [::] => Some (CEP.empty def_expr, CEP.empty (ftype * HiF.forient))
    | Finput p (Gtyp gt) :: pp' =>
        match ExpandPorts_fun pp' with
        | Some (temp_ct, temp_scope) =>
            Some (temp_ct, CEP.add p (Gtyp gt, HiF.Source) temp_scope)
        | None => None
        end
    | Foutput p (Gtyp gt) :: pp' =>
        match ExpandPorts_fun pp' with
        | Some (temp_ct, temp_scope) =>
            Some (CEP.add p D_undefined temp_ct, CEP.add p (Gtyp gt, HiF.Sink) temp_scope)
        | None => None
        end
    | _ => None
    end.

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


Definition ExpandWhens_fun
    (* Expand When statements in a module *)
    (m : HiFP.hfmodule) (* module that needs to be handled *)
:   option HiFP.hfmodule (* result is either a semantically equivalent module without when statements,
                            or nothing if there was some error *)
:=  match m with
    | FInmod v pp ss =>
        match ExpandPorts_fun pp with
        | Some (port_ct, port_scope) =>
            match ExpandBranches_funs ss port_ct port_scope with
            | Some (conn_map, _) =>
                Some (FInmod v pp (Qcat (component_stmts_of ss) (convert_to_connect_stmts conn_map)))
            | None => None
            end
        | None => None
        end
    | FExmod _ _ _ => None
    end.

Lemma ExpandBranch_fun_submap :
forall (s : HiFP.hfstmt) (old_conn_map : CEP.t def_expr) (old_scope : CEP.t (ftype * HiF.forient)),
    match ExpandBranch_fun s old_conn_map old_scope with
    | Some (new_conn_map, new_scope) =>
            subdomain old_conn_map new_conn_map
                (* Actually we would like subdomain_undef old_conn_map new_conn_map,
                   but for that we need to involve tmap as well and require connmap_sub_tm old_conn_map tmap *)
        /\
            CEP.submap old_scope new_scope
    | None => True
    end
with ExpandBranches_funs_submap :
forall (ss : HiFP.hfstmt_seq) (old_conn_map : CEP.t def_expr) (old_scope : CEP.t (ftype * HiF.forient)),
    match ExpandBranches_funs ss old_conn_map old_scope with
    | Some (new_conn_map, new_scope) =>
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
    - apply subdomain_refl.
    - apply CEP.Lemmas.submap_refl.
  + (* Swire *)
    destruct (CEP.find var old_scope) eqn: Hvar ; first by trivial.
    split.
    - apply subdomain_add.
    - apply (CEP.Lemmas.submap_none_add _ (CEP.Lemmas.submap_refl _)), Hvar.
  + (* Sreg *)
    destruct (CEP.find var old_scope) eqn: Hvar ; first by trivial.
    destruct (type_of_expr (clock reg) old_scope) ; last by trivial.
    destruct (reset reg) as [|rst_sig rst_val].
    2: destruct (type_of_expr rst_sig old_scope) as [[[[[|[|]]| | | | | |]| |] _]|] ; try by trivial.
    2: destruct (type_of_expr rst_val (CEP.add var (type reg, HiF.Duplex) old_scope)) ; last by trivial.
    3: destruct (type_of_expr rst_val old_scope) ; last by trivial.
    1-3: split ; first by apply subdomain_add.
    1-3: by apply (CEP.Lemmas.submap_none_add _ (CEP.Lemmas.submap_refl _)), Hvar.
  + (* Smem *)
    trivial.
  + (* Sinst *)
    trivial.
  + (* Snode *)
    destruct (CEP.find var old_scope) eqn: Hvar ; first by trivial.
    destruct (type_of_expr expr old_scope) as [[ft p]|] eqn: Hexpr ; last by trivial.
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
    1,2: split ; first by apply subdomain_add.
    1,2: by apply CEP.Lemmas.submap_refl.
  + (* Sinvalid *)
    destruct ref as [var| | |] ; try by trivial.
    destruct (CEP.find var old_scope) as [[_ [| | | |]]|] ; try by trivial.
    1,2: split ; first by apply subdomain_add.
    1,2: by apply CEP.Lemmas.submap_refl.
  + (* Swhen *)
    destruct (type_of_expr cond old_scope) as [[[[[|[|]]| | | | | |]| |] _]|] ; try by trivial.
    generalize (IHss sst old_conn_map old_scope) ; intro IHsst.
    destruct (ExpandBranches_funs sst old_conn_map old_scope) as [[true_conn_map true_scope]|] ; last by trivial.
    specialize (IHss ssf old_conn_map old_scope) ; rename IHss into IHssf.
    destruct (ExpandBranches_funs ssf old_conn_map old_scope) as [[false_conn_map false_scope]|] ; last by trivial.
    split.
    - intro.
      rewrite /combine_when_connections CEP.Lemmas.map2_1bis //.
      destruct IHsst as [IHsst _] ; specialize (IHsst k).
      destruct IHssf as [IHssf _] ; specialize (IHssf k).
      destruct (CEP.find k true_conn_map) as [[]|], (CEP.find k false_conn_map) as [[]|] ;
            try by done.
      destruct (h == h0) ; done.
    - apply CEP.Lemmas.submap_refl.
* clear ExpandBranches_funs_submap.
  rename ExpandBranch_fun_submap into IHs.
  induction ss as [|s ss] ; simpl ; intros.
  + (* Qnil *)
    split.
    - apply subdomain_refl.
    - apply CEP.Lemmas.submap_refl.
  + (* Qcons *)
    specialize (IHs s old_conn_map old_scope).
    destruct (ExpandBranch_fun s old_conn_map old_scope) as [[temp_conn_map temp_scope]|] ; last by trivial.
    specialize (IHss temp_conn_map temp_scope).
    destruct (ExpandBranches_funs ss temp_conn_map temp_scope) as [[new_conn_map new_scope]|] ; last by trivial.
    split.
    + apply (subdomain_trans _ _ _ (proj1 IHs)), IHss.
    + apply (CEP.Lemmas.submap_trans (proj2 IHs)), IHss.
Qed.

Definition extend_defined_map_with
    (* Returns map m, except that undefined elements are copied from dflt.
       “undefined” here includes expressions that are assigned an undefined value *)
    (m (* main map whose values are all used *)
     dflt : CEP.t def_expr) (* default: values are used where m does not define an expression *)
:   CEP.t def_expr
:=  CEP.map2 (fun (elm eld : option def_expr)
              => match elm with
                 | Some D_undefined
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

Lemma ports_tmap_preserves_fully_inferred :
forall (pp : seq HiFP.hfport) (vm : CEP.t vertex_type),
        ports_have_fully_inferred_ground_types pp
    ->
        match ports_tmap pp vm with
        | Some (pmap) => tmap_has_fully_inferred_ground_types pmap
        | _ => True
        end.
Proof.
intros pp vm Hpp_inf.
induction pp as [|p pp].
* simpl.
  intro k.
  by rewrite CEP.Lemmas.empty_o //.
* simpl in Hpp_inf ; move /andP : Hpp_inf => [Hp_inf Hpp_inf].
  simpl.
  destruct p as [var ft|var ft].
  1,2: simpl in Hp_inf.
  1,2: destruct ft as [gt| |] ; try by discriminate Hp_inf.
  1,2: generalize (fully_inferred_does_not_change gt var vm Hp_inf) ; intro.
  1,2: destruct (code_type_find_vm_widths (Gtyp gt) var vm) as [[[gt'| |] _]|] ;
             try done ;
       subst gt'.
  1,2: destruct (ports_tmap pp vm) as [old_pmap|] ; last by trivial.
  1,2: destruct (CEP.find var old_pmap) eqn: Hvar_old ; first by trivial.
  1,2: intro k.
  1,2: destruct (k == var) eqn: Hkvar.
  + 1,3: by rewrite (CEP.Lemmas.find_add_eq Hkvar) //.
  + 1,2: rewrite (CEP.Lemmas.find_add_neq (elimT negP (negbT Hkvar))).
    1,2: by apply IHpp, Hpp_inf.
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
  destruct s as [|var ft|var reg|var mem|var1 var2|var expr|ref expr|ref|cond sst ssf] ;
  intros ; try done.
  + (* Swire *)
    simpl stmt_tmap.
    destruct (CEP.find var tmap) ; first by trivial.
    unfold stmt_has_fully_inferred_ground_types in H.
    destruct ft as [gt| |]; try done.
    generalize (fully_inferred_does_not_change gt var vm H) ;
          intro.
    destruct (code_type_find_vm_widths (Gtyp gt) var vm) as [[[newgt| |] _]|] ;
        try by done.
    subst newgt.
    intro.
    destruct (v == var) eqn: Hvs ; first by rewrite CEP.Lemmas.find_add_eq //.
    rewrite CEP.Lemmas.find_add_neq // ; last by rewrite /HiFirrtl.PVM.SE.eq Hvs //.
    by apply H0.
  + (* Sreg *)
    simpl stmt_tmap.
    destruct (CEP.find var tmap) ; first by trivial.
    destruct (type_of_expr (clock reg) scope) ; last by trivial.
    unfold stmt_has_fully_inferred_ground_types in H.
    destruct (type reg) as [gt| |]; try done.
    generalize (fully_inferred_does_not_change gt var vm) ;
          intro.
    destruct (code_type_find_vm_widths (Gtyp gt) var vm) as [[[newgt| |] _]|] ;
        destruct (reset reg) as [|rst_sig rst_val] ;
        move /andP : H => [H H'] ;
        specialize (H2 H') ;
        try by done.
    1,2: subst newgt.
    2: destruct (type_of_expr rst_sig scope) as [[[[[|[]]| | | | | |]| |] _]|] ; try by trivial.
    2: destruct (type_of_expr rst_val (CEP.add var (Gtyp gt, HiF.Duplex) scope)) ; last by trivial.
    3: destruct (type_of_expr rst_val scope) ; last by trivial.
    1-3: intro v.
    1-3: destruct (v == var) eqn: Hvs ; first by rewrite CEP.Lemmas.find_add_eq //.
    1-3: rewrite CEP.Lemmas.find_add_neq ; last by rewrite /HiFirrtl.PVM.SE.eq Hvs //.
    1-3: by apply H0.
  + (* Snode *)
    simpl stmt_tmap.
    destruct (CEP.find var tmap) ; first by trivial.
    assert (tmap_has_fully_inferred_ground_types scope).
          intro v.
          specialize (H1 v).
          destruct (CEP.find v scope) as [p|] ; try done.
          specialize (H0 v).
          rewrite (H1 p Logic.eq_refl) in H0.
          by exact H0.
    simpl stmt_has_fully_inferred_ground_types in H.
    generalize (expr_preserves_fully_inferred scope H2 expr H) ; intro.
    destruct (type_of_expr expr scope) as [[newt _]|] ; last by trivial.
    intro.
    destruct (v == var) eqn: Hvs ; first by rewrite CEP.Lemmas.find_add_eq //.
    rewrite CEP.Lemmas.find_add_neq ; last by rewrite /HiFirrtl.PVM.SE.eq Hvs //.
    by apply H0.
  + (* Sfcnct *)
    simpl stmt_tmap.
    simpl stmt_has_fully_inferred_ground_types in H.
    destruct (type_of_ref ref scope) ; last by done.
    destruct (type_of_expr expr scope) ; last by done.
    by exact H0.
  + (* Sinvalid *)
    simpl stmt_tmap.
    destruct (type_of_ref ref scope) ; last by done.
    by exact H0.
  + (* Swhen *)
    simpl stmt_tmap.
    destruct (type_of_expr cond scope) ; last by done.
    simpl stmt_has_fully_inferred_ground_types in H.
    move /andP : H => [/andP [_ Ht] Hf].
    generalize (stmts_tmap_preserves_fully_inferred vm sst tmap scope Ht H0 H1) ;
          intro.
    generalize (stmts_submap vm sst tmap scope H1) ;
          intro.
    destruct (stmts_tmap (tmap, scope) sst vm) as [[tmap_true scope_true]|] ; try done.
    specialize (stmts_tmap_preserves_fully_inferred vm ssf tmap_true scope Hf H).
    destruct (stmts_tmap (tmap_true, scope) ssf vm) as [[tmap_false _]|] ; try done.
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

Lemma stmts_have_fully_inferred_ground_types_cat :
forall (ss1 ss2 : HiFP.hfstmt_seq),
        (stmts_have_fully_inferred_ground_types ss1 && stmts_have_fully_inferred_ground_types ss2)
    =
        stmts_have_fully_inferred_ground_types (Qcat ss1 ss2).
Proof.
induction ss1 as [|s1 ss1] ; simpl ; intro.
* by reflexivity.
* by rewrite -IHss1 andbA //.
Qed.

Lemma components_preserve_fully_inferred :
forall (ss : HiFP.hfstmt_seq),
        stmts_have_fully_inferred_ground_types ss
    ->
        stmts_have_fully_inferred_ground_types (component_stmts_of ss)
with component_preserves_fully_inferred :
forall (s : HiFP.hfstmt),
        stmt_has_fully_inferred_ground_types s
    ->
        stmts_have_fully_inferred_ground_types (component_stmt_of s).
Proof.
* clear components_preserve_fully_inferred.
  induction ss as [|s ss] ; simpl ; intros ; first by done.
  rewrite -stmts_have_fully_inferred_ground_types_cat.
  move /andP : H => H.
  apply (introT andP) ; split.
  - by apply component_preserves_fully_inferred, H.
  - by apply IHss, H.
* clear component_preserves_fully_inferred.
  induction s as [|var ft|var reg|var mem|var1 var2|var expr|ref expr|ref|cond sst ssf] ;
  simpl ; intros ; try (by done) ; try by rewrite andbT //.
  rewrite -stmts_have_fully_inferred_ground_types_cat.
  apply (introT andP) ; split.
  - move /andP : H => [/andP [_ H] _].
    apply components_preserve_fully_inferred, H.
  - move /andP : H => [_ H].
    apply components_preserve_fully_inferred, H.
Qed.

(* We use the following maps to describe the graph and its values:
old_scope : CEP.t (ftype * HiF.forient) -- assigns a type to every assignable/usable component
old_connmap : CEP.t def_expr -- contains new connections
old_ct : CEP.t def_expr -- contains a value for every assignable component
old_vm : CEP.t vertex_type -- contains the components in the current graph
old_tmap : CEP.t (ftype * HiF.forient) -- contains all components in the final graph

Relations between the maps are:
- scope_sub_connmap scope connmap: connmap assigns to each Sink/Duplex in scope, and the types fit
- subdomain connmap ct: connmap is a subdomain of ct (no need to check whether the types fit, see Lemma aft_connmap_fits_ct_type)
- ct_sub_vm ct vm: ct assigns a value exactly to every assignable component
- vm_sub_tmap vm tmap: tmap types every component in vm correctly

Type correctness is judged according to type_of_expr expr tmap

(Additionally, old_comp contains exactly the definitions of components in vm.)
*)

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
        | Some (_, HiF.Source) => CEP.find k connmap = None
        | None => True
        | _ => False
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
        | None, Some (Node _ _)
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
        | Some (Node     gt _    ) => CEP.find k tmap = Some (Gtyp gt, HiF.Source)
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
        | Some (ft, HiF.Source), Some (Node     gt _    )
        | Some (ft, HiF.Source), Some (InPort   gt      )
        | Some (ft, HiF.Sink  ), Some (OutPort  gt      )
        | Some (ft, HiF.Duplex), Some (Register gt _ _ _)
        | Some (ft, HiF.Duplex), Some (Wire     gt      ) =>
            ft = Gtyp gt
        | Some _, _ => False
        | None, _ => True
        end.

Definition connmap_sub_tm
    (* checks whether the connmap and tmap fit together.
       We could alternatively check whether connmap and vm fit together,
       but in Lemma ExpandBranch_fun_and_stmt_tmap this definition is more suitable. *)
    (connmap : CEP.t def_expr)
    (tmap : CEP.t (ftype * HiF.forient))
:   Prop
:=  forall k : CEP.key,
        match CEP.find k connmap with
        | Some (D_fexpr expr) =>
            match type_of_expr expr tmap, CEP.find k tmap with
            | Some (exist (Gtyp gt_expr) _), Some (Gtyp gt_ref, HiF.Sink)
            | Some (exist (Gtyp gt_expr) _), Some (Gtyp gt_ref, HiF.Duplex) =>
                connect_type_compatible false (Gtyp gt_ref) (Gtyp gt_expr) false
            | _, _ => False
            end
        | Some _ =>
            match CEP.find k tmap with
            | Some (_, HiF.Sink)
            | Some (_, HiF.Duplex) => True
            | _ => False
            end
        | None => True
        end.

Definition all_fit_together
    (scope : CEP.t (ftype * HiF.forient)) (* type and orientation of components in the scope *)
    (connmap : CEP.t def_expr) (* connection map, i.e. map containing information about Sfncnt / Sinvalid *)
    (ct : CEP.t def_expr) (* edges of the module graph *)
    (vm : CEP.t vertex_type) (* vertices of the module graph *)
    (tmap : CEP.t (ftype * HiF.forient)) (* type and orientation of all components (for namespace checks) *)
:   Prop
:=      scope_sub_connmap scope connmap tmap
    /\
        subdomain connmap ct
    /\
        ct_sub_vm ct vm tmap
    /\
        vm_sub_tmap vm tmap
    /\
        scope_sub_vm scope vm
    /\
        connmap_sub_tm connmap tmap.

Lemma aft_connmap_fits_ct_type :
forall (scope : CEP.t (ftype * HiF.forient)) (connmap : CEP.t def_expr)
       (ct : CEP.t def_expr) (vm : CEP.t vertex_type) (tmap : CEP.t (ftype * HiF.forient)),
        all_fit_together scope connmap ct vm tmap
    ->
        forall k : CEP.key,
            match CEP.find k connmap, CEP.find k ct with
            | Some (D_fexpr cm_expr), Some (D_fexpr ct_expr) =>
                match type_of_expr cm_expr tmap, type_of_expr ct_expr tmap with
                | Some (exist (Gtyp cm_gt) _), Some (exist (Gtyp ct_gt) _) => connect_type_compatible false (Gtyp cm_gt) (Gtyp ct_gt) false
                | _, _ => False
                end
            | Some _, None => False
            | _, _ => True
            end.
Proof.
intros scope connmap ct vm tmap [_ [Hcm_sub_ct [Hct_sub_vm [Hvm_sub_tm [_ Hcm_sub_tm]]]]] k.
specialize (Hcm_sub_ct k) ; specialize (Hct_sub_vm k) ; specialize (Hvm_sub_tm k) ; specialize (Hcm_sub_tm k).
destruct (CEP.find k connmap) as [[| |cm_expr]|], (CEP.find k ct) as [[| |ct_expr]|] ;
      try (by done).
clear Hcm_sub_ct.
destruct (type_of_expr cm_expr tmap) as [[[cm_gt| |] Hcm_gt_inf]|] ;
      try by exact Hcm_sub_tm.
destruct (type_of_expr ct_expr tmap) as [[[ct_gt| |] Hct_gt_inf]|],
         (CEP.find k vm) as [[gt|gt|gt|gt|gt]|] ;
      try by contradiction Hct_sub_vm.
all: rewrite Hvm_sub_tm in Hcm_sub_tm ; clear Hvm_sub_tm.
all: destruct gt, cm_gt, ct_gt ; done.
Qed.

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
destruct Haft as [_ [_ [_ [Hvm_tm [Hsc_vm _]]]]].
exact (scope_vm_submap_tmap scope vm tmap Hsc_vm Hvm_tm).
Qed.

Lemma convert_to_connect_stmts_Sem :
(* a lemma that states that convert_to_connect_stmts and Sem_frag_stmts are sort of inverses *)
forall (conn_map : CEP.t def_expr) (vm_old : CEP.t vertex_type) (ct_old : CEP.t def_expr) (vm_new : CEP.t vertex_type) (ct_new : CEP.t def_expr) (tmap: CEP.t (ftype * HiF.forient)),
        all_fit_together (CEP.empty (ftype * HiF.forient)) conn_map ct_old vm_old tmap
    ->
        Sem_frag_stmts vm_old ct_old (convert_to_connect_stmts conn_map) vm_new ct_new tmap
    ->
            CEP.Equal vm_old vm_new
        /\
            CEP.Equal ct_new (extend_defined_map_with conn_map ct_old).
Proof.
intros conn_map vm_old ct_old vm_new ct_new tmap Haft.
destruct Haft as [_ [Hcm_sub_ct [Hct_sub_vm [Hvm_sub_tm [_ Hcm_sub_tm]]]]].
rewrite /convert_to_connect_stmts CEP.Lemmas.P.fold_spec_right.
assert (SetoidList.equivlistA (@CEP.Lemmas.O.eqke def_expr)
                                (List.rev (CEP.elements conn_map))
                                (CEP.elements conn_map))
        by (intro ;
            apply (SetoidList.InA_rev (@CEP.Lemmas.O.eqke def_expr))).
revert H.
generalize (CEP.elements_3w conn_map) ; intro Hnodup.
assert (Heqv_key0 : RelationClasses.Equivalence (fun x y : ProdVarOrder.T => x == y)).
        clear.
        assert (forall x y : ProdVarOrder.T, x == y -> y == x)
              by (intros ; rewrite eq_sym //).
        assert (forall x y z : ProdVarOrder.T, x == y -> y == z -> x == z)
              by (intros ; move /eqP : H0 => H0 ; rewrite H0 //).
        exact (RelationClasses.Build_Equivalence (fun x y : ProdVarOrder.T => x == y) (eq_refl (T := ProdVarOrder.T)) H H0).
apply SetoidList.NoDupA_rev in Hnodup ; last by apply (CEP.Lemmas.O.eqk_equiv def_expr).
revert vm_old ct_old Hcm_sub_ct Hct_sub_vm Hvm_sub_tm Hcm_sub_tm Hnodup.
generalize (List.rev (CEP.elements conn_map)) as conn_map_list.
intro ; revert conn_map_list conn_map.
induction conn_map_list.
* unfold List.fold_right.
  intros conn_map vm_old ct_old Hcm_sub_ct Hct_sub_vm Hvm_sub_tm Hcm_sub_tm Hnodup Hequiv Hsf.
  split ; first by apply Hsf.
  intro y.
  apply RelationClasses.Equivalence_Symmetric, SetoidList.equivlistA_nil_eq in Hequiv ;
          last by exact (CEP.Lemmas.O.eqke_equiv def_expr).
  apply CEP.Lemmas.P.elements_Empty in Hequiv.
  apply CEP.Lemmas.Empty_find with (x := y) in Hequiv.
  simpl Sem_frag_stmts in Hsf.
  by rewrite /extend_defined_map_with CEP.Lemmas.map2_1bis // Hequiv (proj2 Hsf) //.
* destruct a as [k v].
  simpl List.fold_right.
  intros conn_map vm_old ct_old Hcm_sub_ct Hct_sub_vm Hvm_sub_tm Hcm_sub_tm Hnodup Hequiv.
   (*destruct (List.fold_right (CEP.Lemmas.P.uncurry helper_connect)
                              (Qnil ProdVarOrder.T) conn_map_list) eqn: Hfold ;
          rewrite Hfold // /CEP.Lemmas.P.uncurry /helper_connect /fst /snd.
    rewrite Hfold in IHconn_map_list.*)
  inversion Hnodup as [|x l Hnotin Hnodup0] ; subst x l.
  (*assert (ct_has_fully_inferred_ground_types (CEP.Lemmas.P.of_list conn_map_list)).
          intro.
          generalize (CEP.find_2 (m := CEP.Lemmas.P.of_list conn_map_list) (x := k0)) ; intro.
          destruct (CEP.find k0 (CEP.Lemmas.P.of_list conn_map_list)) as [[]|] ; try done.
          specialize (H4 (D_fexpr h) Logic.eq_refl).
          apply (CEP.Lemmas.P.of_list_1 k0 (D_fexpr h) H7), (SetoidList.InA_cons_tl (k, v)),
                H3, CEP.Lemmas.elements_mapsto_iff, CEP.find_1 in H4.
          specialize (H0 k0) ; by rewrite H4 // in H0.*)
  assert (Hkinmap: CEP.find k conn_map = Some v).
          apply CEP.find_1, CEP.elements_2, Hequiv, SetoidList.InA_cons_hd, CEP.Lemmas.O.eqke_refl.
  assert (Hknotinlist: CEP.find k (CEP.Lemmas.P.of_list conn_map_list) = None).
          apply CEP.Lemmas.not_find_in_iff.
          contradict Hnotin.
          destruct Hnotin as [elt Hnotin].
          apply CEP.Lemmas.P.of_list_1, (CEP.Lemmas.P.InA_eqke_eqk v (eqxx k)) in Hnotin ;
                by assumption.
  assert (Hcmlist_sub_ct: subdomain (CEP.Lemmas.P.of_list conn_map_list) ct_old).
          intro k0.
          specialize (Hcm_sub_ct k0).
          destruct (CEP.find k0 ct_old) ; first by trivial.
          destruct (CEP.find k0 (CEP.Lemmas.P.of_list conn_map_list)) as [elt|] eqn: Hfindk0 ;
                last by trivial.
          apply CEP.find_2, (CEP.Lemmas.P.of_list_1 _ _ Hnodup0) in Hfindk0.
          apply (SetoidList.InA_cons_tl (k, v)), Hequiv, CEP.elements_2, CEP.find_1 in Hfindk0.
          rewrite Hfindk0 // in Hcm_sub_ct.
  assert (Hcmlist_sub_tm: connmap_sub_tm (CEP.Lemmas.P.of_list conn_map_list) tmap).
          intro k0.
          specialize (Hcm_sub_tm k0).
          destruct (CEP.find k0 (CEP.Lemmas.P.of_list conn_map_list)) as [elt|] eqn: Hfindk0 ;
                last by trivial.
          apply CEP.find_2, (CEP.Lemmas.P.of_list_1 _ _ Hnodup0) in Hfindk0.
          apply (SetoidList.InA_cons_tl (k, v)), Hequiv, CEP.elements_2, CEP.find_1 in Hfindk0.
          by rewrite Hfindk0 // in Hcm_sub_tm.
  destruct v.
  + (* D_undefined *)
    unfold CEP.Lemmas.P.uncurry ; simpl Sem_frag_stmts.
    intro Hsf.
    specialize (IHconn_map_list (CEP.Lemmas.P.of_list conn_map_list) vm_old ct_old
                                Hcmlist_sub_ct Hct_sub_vm Hvm_sub_tm Hcmlist_sub_tm Hnodup0 (CEP.Lemmas.P.of_list_2 Hnodup0) Hsf).
    split ; first by apply IHconn_map_list.
    apply (CEP.Lemmas.Equal_trans (proj2 IHconn_map_list)).
    intro y.
    unfold extend_map_with.
    rewrite CEP.Lemmas.map2_1bis // (*CEP.Lemmas.P.of_list_1b //. *)
            CEP.Lemmas.map2_1bis //.
    destruct (y == k) eqn: Hyk.
    - move /eqP : Hyk => Hyk.
      rewrite Hyk Hkinmap Hknotinlist.
      specialize (Hcm_sub_ct k) ; rewrite Hkinmap in Hcm_sub_ct.
      by destruct (CEP.find k ct_old) ; done.
    - destruct (PVM.find y (CEP.Lemmas.P.of_list conn_map_list)) eqn: Hfind_list.
      * specialize (Hequiv (y, d)).
        destruct Hequiv as [Hequiv _].
        apply CEP.find_2, (CEP.Lemmas.P.of_list_1 _ _ Hnodup0) in Hfind_list.
        apply (SetoidList.InA_cons_tl (k, D_undefined)), Hequiv, CEP.elements_2, CEP.find_1 in Hfind_list.
        rewrite Hfind_list //.
      * destruct (PVM.find y conn_map) eqn: Hfind_map ;
              last by reflexivity.
        apply CEP.find_2, CEP.elements_1, Hequiv, SetoidList.InA_cons in Hfind_map.
        destruct Hfind_map as [Hfind_map|Hfind_map] ;
                first (by rewrite /CEP.Lemmas.O.eqke /PVM.SE.eq /fst Hyk in Hfind_map ;
                          destruct Hfind_map as [Hfind_map _] ; done).
        apply (CEP.Lemmas.P.of_list_1 _ _ Hnodup0), CEP.find_1 in Hfind_map.
        by rewrite Hfind_map // in Hfind_list.
  + (* D_invalidated *)
    simpl Sem_frag_stmts.
    intro Hsf.
    destruct Hsf as [vm' [ct' [[H10 H11] H12]]].
    generalize (Hvm_sub_tm k) ; intro Hvm_sub_tmk.
    destruct (CEP.find k tmap) as [[[gt| |] ori]|] ;
          last (by contradiction H11).
    2,3: specialize (Hcm_sub_ct k) ; rewrite Hkinmap in Hcm_sub_ct ;
         specialize (Hct_sub_vm k) ;
         destruct (CEP.find k ct_old) as [[| |ct_expr]|] ;
               last (by discriminate Hcm_sub_ct) ;
         destruct (CEP.find k vm_old) as [[gt'|gt'|gt'|gt'|gt']|] ;
               try (by contradiction Hct_sub_vm) ;
         by discriminate Hvm_sub_tmk.
    rewrite /size_of_ftype /mkseq /invalidate in H11 ; simpl in H11.
    rewrite N.add_0_r -surjective_pairing in H11.
    assert (Hcmlist_sub_ct' : subdomain (CEP.Lemmas.P.of_list conn_map_list) ct').
          intro k0.
          specialize (Hcmlist_sub_ct k0).
          destruct (k0 == k) eqn: Hk0k.
          * move /eqP : Hk0k => Hk0k ; subst k0.
            destruct H11 as [H11 _].
            destruct ori ; try by discriminate H11.
            + move /eqP : H11 => H11 ; rewrite H11 //.
            + 1,2: move /andP : H11 => [_ /eqP H11] ;
                   by rewrite H11 //.
          * destruct H11 as [_ H11].
            specialize (H11 k0) ; rewrite mem_seq1 Hk0k in H11.
            by rewrite -H11 //.
    assert (Hct'_sub_vm': ct_sub_vm ct' vm' tmap).
          intro.
          specialize (Hct_sub_vm k0).
          rewrite -H10.
          destruct (k0 == k) eqn: Hk0k.
          * move /eqP : Hk0k => Hk0k ; subst k0.
            destruct H11 as [H11 _].
            destruct ori ; try by discriminate H11.
            + move /eqP : H11 => H11 ; rewrite H11 //.
            + 1,2: move /andP : H11 => [/eqP H11old /eqP H11'] ;
                   rewrite H11' ;
                   destruct (CEP.find k ct_old) as [[| |ct_expr]|] ;
                         last (by contradiction H11old) ;
                         try (by apply Hct_sub_vm) ;
                   destruct (CEP.find k vm_old) as [[]|] ;
                         try by trivial ;
                   by exact Hct_sub_vm.
          * destruct H11 as [_ H11].
            specialize (H11 k0) ; rewrite mem_seq1 Hk0k in H11.
            by rewrite -H11 //.
    assert (Hvm'_sub_tm: vm_sub_tmap vm' tmap).
          intro k0.
          specialize (Hvm_sub_tm k0).
          by rewrite -H10 //.
    specialize (IHconn_map_list (CEP.Lemmas.P.of_list conn_map_list) vm' ct'
                                Hcmlist_sub_ct' Hct'_sub_vm' Hvm'_sub_tm Hcmlist_sub_tm Hnodup0 (CEP.Lemmas.P.of_list_2 Hnodup0) H12).
    split ; first by apply (CEP.Lemmas.Equal_trans H10), IHconn_map_list.
    apply (CEP.Lemmas.Equal_trans (proj2 IHconn_map_list)).
    intro.
    rewrite /extend_defined_map_with CEP.Lemmas.map2_1bis // (*CEP.Lemmas.P.of_list_1b //. *)
            CEP.Lemmas.map2_1bis //.
    destruct (y == k) eqn: Hyk.
    - move /eqP : Hyk => Hyk ; subst y.
      rewrite Hkinmap Hknotinlist.
      destruct H11 as [H11 _].
      destruct ori ; try by discriminate H11.
      * (* Now we have to show that (k, D_invalidated) cannot be in connmap
           because the vertex has a source orientation *)
        specialize (Hcm_sub_ct k) ; rewrite Hkinmap in Hcm_sub_ct.
        specialize (Hct_sub_vm k).
        destruct (CEP.find k ct_old) as [[| |ct_expr]|] ;
               last (by discriminate Hcm_sub_ct) ;
        destruct (CEP.find k vm_old) as [[gt'|gt'|gt'|gt'|gt']|] ;
               by done.
      * 1,2: move /andP : H11 => [_ /eqP H11] ;
             rewrite H11 //.
    - destruct H11 as [_ H11].
      specialize (H11 y) ; rewrite mem_seq1 Hyk in H11.
      rewrite H11.
      destruct (PVM.find y (CEP.Lemmas.P.of_list conn_map_list)) eqn: Hfind_list.
      - apply CEP.find_2, (CEP.Lemmas.P.of_list_1 _ _ Hnodup0) in Hfind_list.
        apply (SetoidList.InA_cons_tl (k, D_invalidated)), Hequiv, CEP.elements_2, CEP.find_1 in Hfind_list.
        by rewrite Hfind_list //.
      - destruct (PVM.find y conn_map) eqn: Hfind_map ; last by reflexivity.
        apply CEP.find_2, CEP.elements_1, Hequiv in Hfind_map.
        inversion Hfind_map as [x l Hyeqk|x l Hyinlist] ; subst x l.
        * destruct Hyeqk as [Hyeqk _].
          by rewrite /PVM.SE.eq /fst Hyk // in Hyeqk.
        * apply (CEP.Lemmas.P.of_list_1 _ _ Hnodup0), CEP.find_1 in Hyinlist.
          by rewrite Hfind_list // in Hyinlist.
  + (* Expressions should not be very different from D_invalidated... *)
Admitted.
(*
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
    - rewrite (CEP.Lemmas.find_add_eq Hyk).
      move /eqP : Hyk => Hyk ; subst y.
      rewrite H8 H9 //.
    - rewrite (CEP.Lemmas.find_add_neq (elimT negP (negbT Hyk))).
      destruct (PVM.find y (CEP.Lemmas.P.of_list conn_map_list)) eqn: Hfind_list.
      * rewrite CEP.Lemmas.P.of_list_1b // in Hfind_list.
        apply SetoidList.findA_NoDupA in Hfind_list ;
                last (by exact H7) ;
                last (by exact Heqv_key0).
        apply (SetoidList.InA_cons_tl (k, D_fexpr h)), H3, CEP.elements_2, CEP.find_1 in Hfind_list.
        by rewrite Hfind_list //.
      * destruct (PVM.find y conn_map) eqn: Hfind_map ; last by reflexivity.
        apply CEP.find_2, CEP.elements_1, H3 in Hfind_map.
        inversion Hfind_map ; subst y0 l.
        + destruct H15 as [H15 _].
          by rewrite /PVM.SE.eq /fst Hyk // in H15.
        + apply CEP.Lemmas.P.of_list_1 in H15 ; last by exact H7.
          apply CEP.find_1 in H15.
          by rewrite Hfind_list // in H15.
Qed. *)

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
      destruct (CEP.find k ct) eqn: Hfind_in_ct ; last by discriminate Hk_in_ct ; clear Hk_in_ct.
      generalize (proj1 (proj2 (proj2 (proj2 Haft))) k) ; intro Hk_in_tmap.
      destruct d, (CEP.find k vm) as [[gt|gt|gt|gt|gt]|] ; try (by contradiction Hk_in_vm).
(*      1-9: rewrite Hk_in_tmap /size_of_ftype /mkseq ; simpl map ; rewrite N.add_0_r -surjective_pairing.
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
    admit.*)
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

Lemma Hneq_12small_large :
forall (k l : CEP.key),
        (k == l) = false
    ->
            k.1 <> l.1
        \/
            nat_of_bin k.2 < nat_of_bin l.2
        \/
            1 + nat_of_bin l.2 <= nat_of_bin k.2.
Proof.
intros.
destruct (k.1 == l.1) eqn: Hkl1 ; move /eqP : Hkl1 => Hkl1 ;
      last (left ; exact Hkl1).
right.
apply (elimT orP), negbFE.
rewrite negb_or -leqNgt add1n -leqNgt -eqn_leq.
apply (introF eqP).
intro Hlk2.
rewrite (surjective_pairing k) Hkl1 -(nat_of_binK k.2) -Hlk2 nat_of_binK -surjective_pairing eq_refl // in H.
Qed.

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
                       (eb_connmap : CEP.t def_expr)
                       (sf_vm : CEP.t vertex_type) (sf_ct : CEP.t def_expr),
                            all_fit_together old_scope old_connmap old_ct old_vm old_tmap
                        ->
                            CEP.submap old_connmap old_ct
                        ->
                            stmt_tmap (old_tmap, old_scope) s vm_for_tmap = Some (tm_tmap, tm_scope)
                        ->
                            ExpandBranch_fun s old_connmap old_scope = Some (eb_connmap, tm_scope)
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
                            /\
                                CEP.submap sf_ct (extend_map_with eb_connmap old_ct).
Proof.
intros vm_for_tmap tmap Htm_inf Hvm_sub_tm.
destruct s as [|var ft|var reg|var mem|var1 var2|var expr|ref expr|ref|cond sst ssf] eqn: Hstmt ; simpl ;
try done ; intros Hs_inf old_scope old_connmap old_ct old_vm old_tmap tm_tmap tm_scope eb_connmap sf_vm sf_ct
       Haft Holdcm_sub_oldct Htm Heb Hsf Htm_sub_vm.
* (* Sskip *)
  injection Htm ; clear Htm ; intros ; subst tm_tmap tm_scope.
  injection Heb ; clear Heb ; intros ; subst eb_connmap.
  apply convert_to_connect_stmts_Sem in Hsf.
  + split.
    - split ; first by apply Hsf.
      intro k ; rewrite (proj2 Hsf) /extend_defined_map_with CEP.Lemmas.map2_1bis //.
      specialize (Holdcm_sub_oldct k).
      destruct (CEP.find k old_connmap) as [[]|] ; try (by reflexivity) ;
      by rewrite (Holdcm_sub_oldct _ Logic.eq_refl) //.
    split.
    - split.
      * by apply Haft.
      destruct Haft as [_ Haft] ; split.
      * intro k ; destruct Haft as [Haft _] ; specialize (Haft k).
        rewrite (proj2 Hsf) /extend_defined_map_with CEP.Lemmas.map2_1bis //.
        destruct (CEP.find k old_connmap) as [[]|] ; done.
      destruct Haft as [_ Haft] ; split.
      * intro k ; destruct Haft as [Haft _] ; specialize (Haft k).
        rewrite -(proj1 Hsf) (proj2 Hsf) /extend_map_with CEP.Lemmas.map2_1bis //.
        specialize (Holdcm_sub_oldct k).
        destruct (CEP.find k old_connmap) as [[]|] ; try done ;
        by rewrite (Holdcm_sub_oldct _ Logic.eq_refl) // in Haft.
      destruct Haft as [_ Haft] ; split.
      * intro k ; destruct Haft as [Haft _] ; specialize (Haft k).
        by rewrite -(proj1 Hsf) //.
      destruct Haft as [_ Haft] ; split.
      * intro k ; destruct Haft as [Haft _] ; specialize (Haft k).
        by rewrite -(proj1 Hsf) //.
      * by apply Haft.
    - intro k ; destruct Hsf as [_ Hsf] ; specialize (Hsf k).
      rewrite Hsf /extend_map_with CEP.Lemmas.map2_1bis // /extend_defined_map_with CEP.Lemmas.map2_1bis //.
      specialize (Holdcm_sub_oldct k).
      destruct (CEP.find k old_connmap) as [[]|] ; try done.
      by rewrite (Holdcm_sub_oldct _ Logic.eq_refl) //.
  + generalize (scope_vm_submap_tmap old_tmap vm_for_tmap tmap Htm_sub_vm Hvm_sub_tm) ; intro Holdtm_sub_tm.
    split.
    * intro k ; by rewrite CEP.Lemmas.empty_o //.
    destruct Haft as [_ Haft] ; split.
    * by apply Haft.
    destruct Haft as [_ Haft] ; split.
    * intro k ; destruct Haft as [Haft _] ; specialize (Haft k).
      destruct (CEP.find k old_ct) as [[| |oldct_expr]|] ; try by exact Haft.
      destruct (CEP.find k old_vm) as [[gt|gt|gt|gt|gt]|] ; try (by exact Haft) ;
      generalize (type_of_expr_submap oldct_expr old_tmap tmap Holdtm_sub_tm) ; intro ;
      destruct (type_of_expr oldct_expr old_tmap) as [[[gt_oldct_expr| |] Hgt_oldct_expr_exp]|] ; try (by contradiction Haft) ;
      by rewrite H //.
    destruct Haft as [_ Haft] ; split.
    * intro k ; destruct Haft as [Haft _] ; specialize (Haft k) ; specialize (Holdtm_sub_tm k).
      destruct (CEP.find k old_vm) as [[gt|gt|gt|gt|gt]|] ; try trivial ;
      by rewrite (Holdtm_sub_tm _ Haft) //.
    destruct Haft as [_ Haft] ; split.
    * intro k ; by rewrite CEP.Lemmas.empty_o //.
    * intro k ; destruct Haft as [_ Haft] ; specialize (Haft k).
      destruct (CEP.find k old_connmap) as [[| |oldcm_expr]|] ; try done.
      + 1,2: specialize (Holdtm_sub_tm k) ;
             destruct (CEP.find k old_tmap) as [[[gt_ref| |] [| | | |]]|] ;
                   try rewrite (Holdtm_sub_tm _ Logic.eq_refl) ;
                   done.
      + generalize (type_of_expr_submap oldcm_expr old_tmap tmap Holdtm_sub_tm) ; intro.
        destruct (type_of_expr oldcm_expr old_tmap) as [[[gt_expr| |] Hgt_expr_exp]|] ;
            try done ;
        rewrite H //.
        specialize (Holdtm_sub_tm k) ;
        destruct (CEP.find k old_tmap) as [[[gt_ref| |] [| | | |]]|] ;
             try rewrite (Holdtm_sub_tm _ Logic.eq_refl) ;
             done.
* (* Swire *)
  destruct ft as [gt| |] ; try by discriminate Hs_inf.
  generalize (scope_vm_submap_tmap tm_tmap vm_for_tmap tmap Htm_sub_vm Hvm_sub_tm) ; intro Htm_tm_sub_tm.
  destruct (CEP.find var old_scope) ; first by discriminate Heb.
  injection Heb ; clear Heb ; intros ; subst eb_connmap tm_scope.
  destruct (CEP.find var old_tmap) eqn: Hvar_oldtm ; first by discriminate Htm.
  generalize (fully_inferred_does_not_change gt var vm_for_tmap Hs_inf) ; intro.
  destruct (code_type_find_vm_widths (Gtyp gt) var vm_for_tmap) as [[ft' _]|] ; last by discriminate Htm.
  destruct ft' as [gt'| |] ; try (by contradiction H) ; subst gt'.
  injection Htm ; clear Htm ; intros ; subst tm_tmap.
  destruct Hsf as [vm_comp [ct_comp [Hsf_comp Hsf_conn]]].
  generalize (CEP.Lemmas.submap_trans (CEP.Lemmas.submap_none_add (Gtyp gt, HiF.Duplex) (CEP.Lemmas.submap_refl old_tmap) Hvar_oldtm) Htm_tm_sub_tm) ;
          intro Holdtm_sub_tm.
  specialize (Htm_tm_sub_tm var) ; rewrite (CEP.Lemmas.find_add_eq (eqxx _)) in Htm_tm_sub_tm.
  rewrite (Htm_tm_sub_tm _ Logic.eq_refl) // in Hsf_comp.
  apply convert_to_connect_stmts_Sem in Hsf_conn.
  + rewrite (Htm_tm_sub_tm _ Logic.eq_refl) //.
    split.
    - split.
      * intro n ; destruct Hsf_comp as [Hsf_comp _] ; specialize (Hsf_comp n).
        by rewrite -(proj1 Hsf_conn) //.
      destruct Hsf_comp as [_ Hsf_comp] ; split.
      * intros v0 n0 ; destruct Hsf_comp as [Hsf_comp _] ; specialize (Hsf_comp v0 n0).
        by rewrite -(proj1 Hsf_conn) //.
      destruct Hsf_comp as [_ Hsf_comp] ; split.
      * intros v0 n0 Hvar12 ; destruct Hsf_comp as [Hsf_comp _] ; specialize (Hsf_comp v0 n0 Hvar12) ;
        specialize (Holdcm_sub_oldct (v0, n0)).
        rewrite (proj2 Hsf_conn) /extend_defined_map_with CEP.Lemmas.map2_1bis // -Hsf_comp CEP.Lemmas.find_add_neq.
        + destruct (CEP.find (v0, n0) old_connmap) as [[]|] ;
              last done ;
              by rewrite (Holdcm_sub_oldct _ Logic.eq_refl) //.
        + intro.
          move /eqP : H => H.
          rewrite (surjective_pairing var) in H.
          injection H ; clear H ; intros ; subst v0 n0.
          destruct Hvar12 as [Hvar12|[Hvar12|Hvar12]].
          3: rewrite /size_of_ftype add1n in Hvar12.
          2,3: apply ltn_eqF, (elimF eqP) in Hvar12.
          1-3: by contradiction Hvar12.
      * intros n Hnsmall ; destruct Hsf_comp as [_ Hsf_comp] ; specialize (Hsf_comp n Hnsmall).
        rewrite /size_of_ftype ltnS leqn0 in Hnsmall.
        move /eqP : Hnsmall => Hnsmall ; subst n.
        rewrite (proj2 Hsf_conn) /extend_defined_map_with CEP.Lemmas.map2_1bis // CEP.Lemmas.find_add_eq //.
        rewrite add0n nat_of_binK -(surjective_pairing) /PVM.SE.eq //.
    split.
    - split.
      * intro k ; destruct Haft as [Haft _] ; specialize (Haft k).
        destruct (k == var) eqn: Hkvar ;
              first by rewrite (CEP.Lemmas.find_add_eq Hkvar) (CEP.Lemmas.find_add_eq Hkvar) //.
        apply negbT, (elimT negP) in Hkvar.
        rewrite (CEP.Lemmas.find_add_neq Hkvar) (CEP.Lemmas.find_add_neq Hkvar).
        destruct (CEP.find k old_scope) as [[ft_tgt [| | | |]]|] ; try by exact Haft.
        1,2: destruct (CEP.find k old_connmap) as [[| |oldcm_expr]|] ; try by exact Haft.
        1,2: apply (CEP.Lemmas.submap_none_add (Gtyp gt, HiF.Duplex) (CEP.Lemmas.submap_refl old_tmap)),
                   (type_of_expr_submap oldcm_expr) in Hvar_oldtm.
        1,2: destruct (type_of_expr oldcm_expr old_tmap) as [[ft_src Hft_src_exp]|] ;
                   try done ;
             by rewrite Hvar_oldtm //.
      destruct Haft as [_ Haft] ; split.
      * intro k ; destruct Haft as [Haft _] ; specialize (Haft k).
        rewrite (proj2 Hsf_conn) /extend_defined_map_with CEP.Lemmas.map2_1bis //.
        destruct (k == var) eqn: Hkvar.
        + rewrite (CEP.Lemmas.find_add_eq Hkvar) //.
          destruct Hsf_comp as [_ [_ [_ Hsf_comp]]] ; specialize (Hsf_comp 0 (ltnSn 0)).
          rewrite add0n nat_of_binK -(surjective_pairing) in Hsf_comp.
          by rewrite (elimT eqP Hkvar) Hsf_comp //.
        + rewrite (CEP.Lemmas.find_add_neq (elimT negP (negbT Hkvar))) //.
          specialize (Holdcm_sub_oldct k).
          destruct (CEP.find k old_connmap) as [[]|] ; try done ;
                last by destruct (CEP.find k ct_comp) ; done.
          destruct Hsf_comp as [_ [_ [Hsf_comp _]]] ; specialize (Hsf_comp k.1 k.2).
          rewrite -(surjective_pairing) in Hsf_comp.
          rewrite -Hsf_comp //.
          apply Hneq_12small_large, Hkvar.
      destruct Haft as [_ Haft] ; split.
      * intro k ; destruct Haft as [Haft _] ; specialize (Haft k).
        rewrite -(proj1 Hsf_conn) (proj2 Hsf_conn) /extend_defined_map_with CEP.Lemmas.map2_1bis //.
        destruct (k == var) eqn: Hkvar.
        + rewrite (CEP.Lemmas.find_add_eq Hkvar).
          destruct Hsf_comp as [Hvm [_ [_ Hct]]] ; specialize (Hvm 0) ; specialize (Hct 0 (ltnSn 0)).
          simpl in Hvm.
          rewrite add0n nat_of_binK -(surjective_pairing) in Hvm, Hct.
          by rewrite (elimT eqP Hkvar) Hct (proj2 Hvm) //.
        + rewrite (CEP.Lemmas.find_add_neq (elimT negP (negbT Hkvar))).
          generalize (Holdcm_sub_oldct k) ; intro Holdct_k.
          destruct Hsf_comp as [_ [Hvm [Hct _]]] ; specialize (Hvm k.1 k.2 (Hneq_12small_large _ _ Hkvar)) ; specialize (Hct k.1 k.2 (Hneq_12small_large _ _ Hkvar)).
          rewrite -(surjective_pairing) in Hvm, Hct.
          rewrite -Hct -Hvm.
          destruct (CEP.find k old_connmap) as [[| |expr]|] ; try done ;
                try rewrite (Holdct_k _ Logic.eq_refl) // ;
                try rewrite (Holdct_k _ Logic.eq_refl) // in Haft.
          - 2: destruct (CEP.find k old_ct) as [[| |expr]|] ; try done.
          - 1,2: destruct (CEP.find k old_vm) as [[gt'|gt'|gt'|gt'|gt']|] ;
                  try exact Haft ;
            generalize (type_of_expr_submap expr old_tmap (CEP.add var (Gtyp gt, HiF.Duplex) old_tmap) (CEP.Lemmas.submap_none_add (Gtyp gt, HiF.Duplex) (CEP.Lemmas.submap_refl old_tmap) Hvar_oldtm)) ;
            intro H0 ;
            destruct (type_of_expr expr old_tmap) as [[[gt_expr| |] Hgt_expr_exp]|] ; try (by contradiction Haft) ;
            by rewrite H0 //.
      destruct Haft as [_ Haft] ; split.
      * intro k ; destruct Haft as [Haft _] ; specialize (Haft k).
        rewrite -(proj1 Hsf_conn).
        destruct (k == var) eqn: Hkvar.
        + destruct Hsf_comp as [Hvm _] ; specialize (Hvm 0) ; simpl in Hvm.
          rewrite add0n nat_of_binK -surjective_pairing in Hvm.
          rewrite (elimT eqP Hkvar) (proj2 Hvm) (CEP.Lemmas.find_add_eq (eqxx _)) //.
        + destruct Hsf_comp as [_ [Hvm _]] ; specialize (Hvm k.1 k.2).
          rewrite /size_of_ftype add1n -surjective_pairing in Hvm.
          rewrite (CEP.Lemmas.find_add_neq (elimT negP (negbT Hkvar))) -Hvm //.
          by apply Hneq_12small_large, Hkvar.
      destruct Haft as [_ Haft] ; split.
      * intro k ; destruct Haft as [Haft _] ; specialize (Haft k).
        rewrite -(proj1 Hsf_conn).
        destruct (k == var) eqn: Hkvar.
        + destruct Hsf_comp as [Hvm _] ; specialize (Hvm 0) ; simpl in Hvm.
          rewrite add0n nat_of_binK -surjective_pairing in Hvm.
          rewrite (CEP.Lemmas.find_add_eq Hkvar) (elimT eqP Hkvar) (proj2 Hvm) //.
        + destruct Hsf_comp as [_ [Hvm _]] ; specialize (Hvm k.1 k.2).
          rewrite /size_of_ftype add1n -surjective_pairing in Hvm.
          rewrite (CEP.Lemmas.find_add_neq (elimT negP (negbT Hkvar))) -Hvm //.
          by apply Hneq_12small_large, Hkvar.
      * intro k ; destruct Haft as [_ Haft] ; specialize (Haft k).
        destruct (k == var) eqn: Hkvar.
        + rewrite (CEP.Lemmas.find_add_eq Hkvar) (CEP.Lemmas.find_add_eq Hkvar) //.
        + apply negbT, (elimT negP) in Hkvar.
          rewrite (CEP.Lemmas.find_add_neq Hkvar) (CEP.Lemmas.find_add_neq Hkvar).
          destruct (CEP.find k old_connmap) as [[| |oldcm_expr]|] ; try by exact Haft.
          generalize (type_of_expr_submap oldcm_expr old_tmap (CEP.add var (Gtyp gt, HiF.Duplex) old_tmap) (CEP.Lemmas.submap_none_add (Gtyp gt, HiF.Duplex) (CEP.Lemmas.submap_refl old_tmap) Hvar_oldtm)) ; intro.
          destruct (type_of_expr oldcm_expr old_tmap) as [[[gt_oldcm_expr| |] Hgt_oldcm_expr_exp]|] ; try by contradiction Haft.
          by rewrite H //.
    - intro k ; rewrite (proj2 Hsf_conn) /extend_map_with /extend_defined_map_with CEP.Lemmas.map2_1bis // CEP.Lemmas.map2_1bis //.
      destruct (k == var) eqn: Hkvar.
      * rewrite (CEP.Lemmas.find_add_eq Hkvar).
        destruct Hsf_comp as [_ [_ [_ Hct]]] ; specialize (Hct 0 (ltnSn 0)).
        rewrite add0n nat_of_binK -surjective_pairing in Hct.
        by rewrite (elimT eqP Hkvar) Hct //.
      * rewrite (CEP.Lemmas.find_add_neq (elimT negP (negbT Hkvar))).
        destruct Hsf_comp as [_ [_ [Hct _]]] ; specialize (Hct k.1 k.2).
        rewrite add1n -surjective_pairing in Hct.
        specialize (Holdcm_sub_oldct k).
        destruct (CEP.find k old_connmap) as [[| |oldcm_expr]|] ; try by done.
        + rewrite (Holdcm_sub_oldct _ Logic.eq_refl) in Hct.
          1,2: rewrite -Hct //.
          1,2: by apply Hneq_12small_large, Hkvar.
    - split.
      * intro k ; by rewrite CEP.Lemmas.empty_o //.
      destruct Haft as [_ Haft] ; split.
      * intro k ; destruct Haft as [Haft _] ; specialize (Haft k).
        destruct (k == var) eqn: Hkvar.
        + rewrite (CEP.Lemmas.find_add_eq Hkvar).
          destruct Hsf_comp as [_ [_ [_ Hct]]] ; specialize (Hct 0 (ltnSn 0)).
          rewrite add0n nat_of_binK -surjective_pairing in Hct.
          rewrite (elimT eqP Hkvar) Hct //.
        + rewrite (CEP.Lemmas.find_add_neq (elimT negP (negbT Hkvar))).
Admitted.

Lemma stmts_tmap_and_ExpandBranches_funs :
forall (ss : HiFP.hfstmt_seq) (old_scope : CEP.t (ftype * HiF.forient)) (old_connmap : CEP.t def_expr)
       (old_tmap : CEP.t (ftype * HiF.forient))
       (vm_for_tmap : CEP.t vertex_type) (tm_tmap tm_scope : CEP.t (ftype * HiF.forient))
       (eb_connmap : CEP.t def_expr) (eb_scope : CEP.t (ftype * HiF.forient)),
        tmap_has_fully_inferred_ground_types old_tmap
    ->
        CEP.submap old_scope old_tmap
    ->
        stmts_have_fully_inferred_ground_types ss
    ->
        stmts_tmap (old_tmap, old_scope) ss vm_for_tmap = Some (tm_tmap, tm_scope)
    ->
        ExpandBranches_funs ss old_connmap old_scope =
                            Some (eb_connmap, eb_scope)
    ->
            tm_scope = eb_scope
        /\
            (connmap_sub_tm old_connmap old_tmap -> connmap_sub_tm eb_connmap tm_tmap)
with stmt_tmap_and_ExpandBranch_fun :
forall (s : HiFP.hfstmt) (old_scope : CEP.t (ftype * HiF.forient)) (old_connmap : CEP.t def_expr)
       (old_tmap : CEP.t (ftype * HiF.forient))
       (vm_for_tmap : CEP.t vertex_type) (tm_tmap tm_scope : CEP.t (ftype * HiF.forient))
       (eb_connmap : CEP.t def_expr) (eb_scope : CEP.t (ftype * HiF.forient)),
        tmap_has_fully_inferred_ground_types old_tmap
    ->
        CEP.submap old_scope old_tmap
    ->
        stmt_has_fully_inferred_ground_types s
    ->
        stmt_tmap (old_tmap, old_scope) s vm_for_tmap = Some (tm_tmap, tm_scope)
    ->
        ExpandBranch_fun s old_connmap old_scope =
                            Some (eb_connmap, eb_scope)
    ->
            tm_scope = eb_scope
        /\
            (connmap_sub_tm old_connmap old_tmap -> connmap_sub_tm eb_connmap tm_tmap).
Proof.
* clear stmts_tmap_and_ExpandBranches_funs.
  rename stmt_tmap_and_ExpandBranch_fun into IHs.
  induction ss as [|s ss] ; simpl ; intros old_scope old_connmap old_tmap vm_for_tmap tm_tmap tm_scope eb_connmap eb_scope Htm_inf Hsc_tm Hss_inf Hst Heb.
  + injection Hst ; clear Hst ; intros ; subst tm_tmap tm_scope.
    injection Heb ; clear Heb ; intros ; subst eb_connmap eb_scope.
    split ; by done.
  + specialize (IHs s old_scope old_connmap old_tmap vm_for_tmap).
    move /andP : Hss_inf => [Hs_inf Hss_inf].
    generalize (stmt_tmap_preserves_fully_inferred vm_for_tmap old_tmap old_scope s Hs_inf Htm_inf Hsc_tm) ; intro Htm_s_inf.
    generalize (stmt_submap vm_for_tmap s old_tmap old_scope Hsc_tm) ; intro Hsc_tm_s.
    destruct (stmt_tmap (old_tmap, old_scope) s vm_for_tmap) as [[tm_tmap_s tm_scope_s]|] ;
          last by discriminate Hst.
    specialize (IHs tm_tmap_s tm_scope_s) with (1 := Htm_inf) (2 := Hsc_tm) (3 := Hs_inf) (4 := Logic.eq_refl).
    generalize (ExpandBranch_fun_submap s old_connmap old_scope) ; intro Heb_s.
    destruct (ExpandBranch_fun s old_connmap old_scope) as [[eb_connmap_s eb_scope_s]|] ;
          last by discriminate Heb.
    specialize IHs with (1 := Logic.eq_refl).
    destruct IHs as [IHs' IHs] ; subst eb_scope_s.
    specialize (IHss tm_scope_s eb_connmap_s tm_tmap_s vm_for_tmap tm_tmap tm_scope
                     eb_connmap eb_scope Htm_s_inf (proj1 Hsc_tm_s) Hss_inf Hst Heb).
    split ; first by apply IHss.
    destruct IHss as [_ IHss].
    intro Hcm_sub_tm.
    by apply IHss, IHs, Hcm_sub_tm.
* clear stmt_tmap_and_ExpandBranch_fun.
  induction s as [|var ft|var reg|var mem|var1 var2|var expr|ref expr|ref|cond sst ssf] ; simpl ; intros old_scope old_connmap old_tmap vm_for_tmap tm_tmap tm_scope eb_connmap eb_scope Htm_inf Hsc_tm Hs_inf Hst Heb.
  + (* Sskip *)
    injection Hst ; clear Hst ; intros ; subst tm_tmap tm_scope.
    injection Heb ; clear Heb ; intros ; subst eb_connmap eb_scope.
    split ; by done.
  + (* Swire *)
    destruct ft as [gt| |] ; try by discriminate Hs_inf.
    generalize (CEP.Lemmas.submap_none_add (k := var) (Gtyp gt, HiF.Duplex)
                               (CEP.Lemmas.submap_refl old_tmap)) ; intro Hold_sub_new.
    destruct (CEP.find var old_tmap) ; first by discriminate Hst.
    generalize (fully_inferred_does_not_change gt var vm_for_tmap Hs_inf) ; intro.
    destruct (code_type_find_vm_widths (Gtyp gt) var vm_for_tmap) as [[[gt'| |] _]|] ;
          last (by discriminate Hst) ;
          try (by contradiction H) ;
          subst gt'.
    injection Hst ; clear Hst ; intros ; subst tm_tmap tm_scope.
    destruct (CEP.find var old_scope) ; first by discriminate Heb.
    injection Heb ; clear Heb ; intros ; subst eb_connmap eb_scope.
    split ; first by reflexivity.
    intros Hcm_sub_tm k ; specialize (Hcm_sub_tm k).
    destruct (k == var) eqn: Hkvar ;
          first by rewrite (CEP.Lemmas.find_add_eq Hkvar) (CEP.Lemmas.find_add_eq Hkvar) //.
    apply negbT in Hkvar ; move /negP : Hkvar => Hkvar.
    rewrite (CEP.Lemmas.find_add_neq Hkvar) (CEP.Lemmas.find_add_neq Hkvar) //.
    destruct (CEP.find k old_connmap) as [[| |expr]|] ; try by exact Hcm_sub_tm.
    generalize (type_of_expr_submap expr _ _ (Hold_sub_new Logic.eq_refl)) ; intro.
    destruct (type_of_expr expr old_tmap) as [[[gt_expr| |] p]|] ; try by contradiction Hcm_sub_tm.
    by rewrite H //.
  + (* Sreg should be similar to Swire *)
    destruct (type reg) as [gt| |] ; try by discriminate Hs_inf.
    generalize (CEP.Lemmas.submap_none_add (k := var) (Gtyp gt, HiF.Duplex)
                               (CEP.Lemmas.submap_refl old_tmap)) ; intro Hold_sub_new.
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
    1-3: injection Heb ; clear Heb ; intros ; subst eb_connmap eb_scope.
    1-3: split ; first by reflexivity.
    1-3: intros Hcm_sub_tm k ; specialize (Hcm_sub_tm k).
    1-3: destruct (k == var) eqn: Hkvar ;
               first by (rewrite (CEP.Lemmas.find_add_eq Hkvar) (CEP.Lemmas.find_add_eq Hkvar) ;
                         simpl type_of_expr ;
                         rewrite (CEP.Lemmas.find_add_eq (eq_refl var)) ;
                         destruct gt ; done).
    1-3: apply negbT in Hkvar ; move /negP : Hkvar => Hkvar.
    1-3: rewrite (CEP.Lemmas.find_add_neq Hkvar) (CEP.Lemmas.find_add_neq Hkvar) //.
    1-3: destruct (CEP.find k old_connmap) as [[| |expr]|] ; try by exact Hcm_sub_tm.
    1-3: generalize (type_of_expr_submap expr _ _ (Hold_sub_new Logic.eq_refl)) ; intro.
    1-3: destruct (type_of_expr expr old_tmap) as [[[gt_expr| |] p]|] ; try by contradiction Hcm_sub_tm.
    1-3: by rewrite H //.
  + (* Smem *)
    by discriminate Hst.
  + (* Sinst *)
    by discriminate Hst.
  + (* Snode *)
    specialize (@CEP.Lemmas.submap_none_add (ftype * HiF.forient) old_tmap old_tmap var)
               with (1 := CEP.Lemmas.submap_refl old_tmap) ; intro Hold_sub_new.
    destruct (CEP.find var old_tmap) eqn: Hfindvar ; first by discriminate Hst.
    (*generalize (type_of_expr_submap expr old_scope old_tmap Hsc_tm) ; intro Hexpr.*)
    destruct (type_of_expr expr old_scope) as [[ft p]|] ; last by discriminate Hst.
    injection Hst ; clear Hst ; intros ; subst tm_tmap tm_scope.
    destruct (CEP.find var old_scope) ; first by discriminate Heb.
    injection Heb ; clear Heb ; intros ; subst eb_connmap eb_scope.
    split ; first by reflexivity.
    intros Hcm_sub_tm k ; specialize (Hcm_sub_tm k).
    destruct (k == var) eqn: Hkvar.
    - move /eqP : Hkvar => Hkvar ; subst k.
      rewrite (CEP.Lemmas.find_add_eq (eq_refl _)) //.
      rewrite Hfindvar in Hcm_sub_tm.
      destruct (CEP.find var old_connmap) as [[| |old_expr]|] ; try by exact Hcm_sub_tm.
      destruct (type_of_expr old_expr old_tmap) as [[[| |]]|] ; by contradiction Hcm_sub_tm.
    - apply negbT in Hkvar ; move /negP : Hkvar => Hkvar.
      rewrite (CEP.Lemmas.find_add_neq Hkvar) //.
      destruct (CEP.find k old_connmap) as [[| |old_expr]|] ; try by exact Hcm_sub_tm.
      generalize (type_of_expr_submap old_expr _ _ (Hold_sub_new (ft, HiF.Source) Logic.eq_refl)) ; intro.
      destruct (type_of_expr old_expr old_tmap) as [[[gt_expr| |]]|] ; try by contradiction Hcm_sub_tm.
      by rewrite H //.
  + (* Sfcnct *)
    destruct ref as [var| | |] ; try by discriminate Heb.
    simpl type_of_ref in Hst.
    generalize (type_of_expr_submap expr old_scope old_tmap Hsc_tm) ; intro Hexpr.
    specialize (Hsc_tm var).
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
                   end) eqn: Hcomp ; last by discriminate Heb.
    1,2: injection Heb ; clear Heb ; intros ; subst eb_connmap eb_scope.
    1,2: split ; first by reflexivity.
    1,2: intros Hcm_sub_tm k ; specialize (Hcm_sub_tm k).
    1,2: destruct (k == var) eqn: Hkvar ;
          first by (move /eqP : Hkvar => Hkvar ; subst k ;
                    rewrite (CEP.Lemmas.find_add_eq (eq_refl _)) Hexpr
                            (Hsc_tm _ Logic.eq_refl) //).
    1,2: apply negbT in Hkvar ; move /negP : Hkvar => Hkvar.
    1,2: by rewrite (CEP.Lemmas.find_add_neq Hkvar) //.
  + (* Sinvalid *)
    destruct ref as [var| | |] ; try by discriminate Heb.
    simpl type_of_ref in Hst.
    specialize (Hsc_tm var).
    destruct (CEP.find var old_scope) as [[ft [| | | |]]|] ;
          (*last (by discriminate Hst) ;
          specialize Hsc_tm with (1 := Logic.eq_refl) ;
          rewrite Hsc_tm in Heb ;*)
          try by discriminate Heb.
    1,2: injection Hst ; clear Hst ; intros ; subst tm_tmap tm_scope.
    1,2: injection Heb ; clear Heb ; intros ; subst eb_connmap eb_scope.
    1,2: split ; first by reflexivity.
    1,2: intros Hcm_sub_tm k ; specialize (Hcm_sub_tm k).
    1,2: destruct (k == var) eqn: Hkvar ;
          first by (move /eqP : Hkvar => Hkvar ; subst k ;
                    rewrite (CEP.Lemmas.find_add_eq (eq_refl _))
                            (Hsc_tm _ Logic.eq_refl) //).
    1,2: apply negbT in Hkvar ; move /negP : Hkvar => Hkvar.
    1,2: by rewrite (CEP.Lemmas.find_add_neq Hkvar) //.
  + (* Swhen *)
    rename stmts_tmap_and_ExpandBranches_funs into IHsst.
    generalize (IHsst ssf) ; intro IHssf.
    specialize (IHsst sst old_scope old_connmap old_tmap vm_for_tmap).
    move /andP : Hs_inf => [/andP [_ Hsst_inf] Hssf_inf].
    destruct (type_of_expr cond old_scope) as [[[[[|[|]]| | | | | |]| |] p_cond]|] eqn: Hcond ;
          (*last (by discriminate Hst) ;
          rewrite Hcond in Heb ;*)
          try by discriminate Heb.
    generalize (stmts_tmap_preserves_fully_inferred vm_for_tmap sst old_tmap old_scope Hsst_inf Htm_inf Hsc_tm) ; intro Htm_t_inf.
    generalize (stmts_submap vm_for_tmap sst old_tmap old_scope Hsc_tm) ; intro Hsc_tm_t.
    destruct (stmts_tmap (old_tmap, old_scope) sst vm_for_tmap) as [[tm_tmap_t tm_scope_t]|] ;
          last by discriminate Hst.
    specialize (IHsst tm_tmap_t tm_scope_t) with (1 := Htm_inf) (2 := Hsc_tm) (3 := Hsst_inf) (4 := Logic.eq_refl).
    generalize (ExpandBranches_funs_submap sst old_connmap old_scope) ; intro Heb_t.
    destruct (ExpandBranches_funs sst old_connmap old_scope) as [[eb_connmap_t eb_scope_t]|] ;
          last by discriminate Heb.
    specialize IHsst with (1 := Logic.eq_refl).
    destruct IHsst as [IHsst' IHsst] ; subst eb_scope_t.
    specialize (IHssf old_scope old_connmap tm_tmap_t vm_for_tmap)
          with (1 := Htm_t_inf) (2 := CEP.Lemmas.submap_trans (proj2 (proj2 Hsc_tm_t)) (proj1 Hsc_tm_t))
               (3 := Hssf_inf).
    generalize (stmts_submap vm_for_tmap ssf tm_tmap_t old_scope (CEP.Lemmas.submap_trans (proj2 (proj2 Hsc_tm_t)) (proj1 Hsc_tm_t))) ; intro Hsc_tm_f.
    destruct (stmts_tmap (tm_tmap_t, old_scope) ssf vm_for_tmap) as [[tm_tmap_f tm_scope_f]|] ; last by discriminate Hst.
    specialize IHssf with (1 := Logic.eq_refl).
    injection Hst ; clear Hst ; intros ; subst tm_tmap_f tm_scope.
    generalize (ExpandBranches_funs_submap ssf old_connmap old_scope) ; intro Heb_f.
    destruct (ExpandBranches_funs ssf old_connmap old_scope) as [[eb_connmap_f eb_scope_f]|] ;
          last by discriminate Heb.
(*
  assert (Htm_tm_sub_tm : CEP.submap tm_tmap tmap).
        intros k v Hfind_k ; specialize (Htm_sub_vm k) ; specialize (Hvm_tm k).
        rewrite Hfind_k in Htm_sub_vm.
        destruct v as [ft [| | | |]] ;
              try (by contradiction Htm_sub_vm) ;
              destruct (CEP.find k vm_for_tmap) as [[gt|gt|gt|gt|gt]|] ;
              try (by contradiction Htm_sub_vm) ;
              subst ft ;
              exact Hvm_tm.
  assert (Htmt_sub_tm: CEP.submap tm_tmap_t tmap) by (apply (CEP.Lemmas.submap_trans (proj1 (proj2 Hst_f)) Htm_tm_sub_tm)).
*)
    specialize IHssf with (1 := Logic.eq_refl).
    destruct IHssf as [IHssf' IHssf] ; subst eb_scope_f.
    injection Heb ; clear Heb ; intros ; subst eb_connmap eb_scope.
    split ; first by reflexivity.
    intro Hcm_sub_tm.
    specialize (IHsst Hcm_sub_tm).
    assert (IHssf_precondition : connmap_sub_tm old_connmap tm_tmap_t).
          destruct Hsc_tm_t as [_ [Hsc_tm_t _]].
          specialize type_of_expr_submap with (1 := Hsc_tm_t) ; intro Hexpr.
          intro k ; specialize (Hcm_sub_tm k) ; specialize (Hsc_tm_t k).
          destruct (CEP.find k old_connmap) as [[| |expr]|] ; last by exact Hcm_sub_tm.
          3: specialize (Hexpr expr) ;
             destruct (type_of_expr expr old_tmap) as [[[gt_expr| |] ]|] ;
                   try (by contradiction Hcm_sub_tm) ;
             rewrite Hexpr //.
          1-3: destruct (CEP.find k old_tmap) ; last by contradiction Hcm_sub_tm.
          1-3: rewrite (Hsc_tm_t _ Logic.eq_refl) ; exact Hcm_sub_tm.
    specialize (IHssf IHssf_precondition) ; clear IHssf_precondition.
    intro k ; specialize (IHsst k) ; specialize (IHssf k).
    specialize (Hcm_sub_tm k).
    rewrite /combine_when_connections CEP.Lemmas.map2_1bis //.
    destruct (CEP.find k eb_connmap_t) as [[| |expr_t]|].
    - destruct Hsc_tm_f as [_ [Hsc_tm_f _]] ; specialize (Hsc_tm_f k).
      by destruct (CEP.find k tm_tmap_t) as [[ft [| | | |]]|] ;
         try (by contradiction IHsst) ;
         rewrite (Hsc_tm_f _ Logic.eq_refl) //.
    - destruct (CEP.find k eb_connmap_f) as [[| |expr_f]|] ; try done.
      destruct Hsc_tm_f as [_ [Hsc_tm_f _]] ; specialize (Hsc_tm_f k).
      by destruct (CEP.find k tm_tmap_t) as [[ft [| | | |]]|] ;
                try (by contradiction IHsst) ;
                rewrite (Hsc_tm_f _ Logic.eq_refl) //.
    - generalize (type_of_expr_submap expr_t tm_tmap_t tm_tmap (proj1 (proj2 Hsc_tm_f))) ; intro.
      destruct (CEP.find k eb_connmap_f) as [[| |expr_f]|] ; try done.
      * 2: destruct (expr_t == expr_f) ; simpl.
      * 1,2: destruct (type_of_expr expr_t tm_tmap_t) as [[[gt_expr_t| |] ]|] ; try by contradiction IHsst.
        1,2: rewrite H.
        1,2: destruct Hsc_tm_f as [_ [Hsc_tm_f _]] ; specialize (Hsc_tm_f k).
        1,2: destruct (CEP.find k tm_tmap_t) as [[[gt_ref| |] [| | | |]]|] ;
                  try (by contradiction IHsst) ;
             by rewrite (Hsc_tm_f _ Logic.eq_refl) //.
      * generalize (type_of_expr_submap cond _ _ (CEP.Lemmas.submap_trans (proj2 (proj2 Hsc_tm_f)) (proj1 Hsc_tm_f))) ;
              intro ; rewrite Hcond in H0 ; rewrite H0 ; clear H0.
        destruct (type_of_expr expr_t tm_tmap_t) as [[[gt_expr_t| |] ]|] ; try by contradiction IHsst.
        rewrite H ; clear H.
        destruct (type_of_expr expr_f tm_tmap) as [[[gt_expr_f| |] ]|] ; try by contradiction IHssf.
        rewrite /ftype_mux /sval /proj2_sig /ftype_mux' /fgtyp_mux.
        destruct Hsc_tm_f as [_ [Hsc_tm_f _]] ; specialize (Hsc_tm_f k) ; specialize (Htm_t_inf k).
        destruct (CEP.find k tm_tmap_t) as [[[gt_ref| |] [| | | |]]|] ;
              try (by contradiction IHsst) ;
        rewrite (Hsc_tm_f _ Logic.eq_refl) in IHssf ; rewrite (Hsc_tm_f _ Logic.eq_refl) ;
        destruct gt_ref, gt_expr_t, gt_expr_f ; done.
      * destruct Hsc_tm_f as [_ [Hsc_tm_f _]].
        generalize (type_of_expr_submap expr_t tm_tmap_t tm_tmap Hsc_tm_f) ; intro.
        destruct (type_of_expr expr_t tm_tmap_t) as [[[gt_expr_t| |] ]|] ; try by contradiction IHsst.
        rewrite H ; clear H.
        specialize (Hsc_tm_f k).
        destruct (CEP.find k tm_tmap_t) as [[[gt_ref| |] [| | | |]]|] ;
              try (by contradiction IHsst) ;
        rewrite (Hsc_tm_f _ Logic.eq_refl) //.
    - destruct (CEP.find k eb_connmap_f) as [[| |expr_f]|] ; by exact IHssf.
Qed.

Lemma Sem_frag_stmts_component :
forall (ss : HiFP.hfstmt_seq) (vm_old : CEP.t vertex_type) (ct_old : CEP.t def_expr)
       (vm_new : CEP.t vertex_type) (ct_new : CEP.t def_expr) (tmap : CEP.t (ftype * HiF.forient)),
        ct_sub_vm ct_old vm_old tmap
    ->
        Sem_frag_stmts vm_old ct_old (component_stmts_of ss) vm_new ct_new tmap
    ->
            ct_sub_vm ct_new vm_new tmap
        /\
            CEP.submap vm_old vm_new
        /\
            CEP.submap ct_old ct_new
with Sem_frag_stmt_component :
forall (s : HiFP.hfstmt) (vm_old : CEP.t vertex_type) (ct_old : CEP.t def_expr)
       (vm_new : CEP.t vertex_type) (ct_new : CEP.t def_expr) (tmap : CEP.t (ftype * HiF.forient)),
        ct_sub_vm ct_old vm_old tmap
    ->
        Sem_frag_stmts vm_old ct_old (component_stmt_of s) vm_new ct_new tmap
    ->
            ct_sub_vm ct_new vm_new tmap
        /\
            CEP.submap vm_old vm_new
        /\
            CEP.submap ct_old ct_new.
Proof.
* clear Sem_frag_stmts_component.
  induction ss as [|s ss] ; simpl ; intros vm_old ct_old vm_new ct_new tmap Hct_sub_vm Hsf.
  + split.
    - intro k ; specialize (Hct_sub_vm k).
      by rewrite (proj1 Hsf) (proj2 Hsf) // in Hct_sub_vm.
    - split ; by apply CEP.Lemmas.Equal_submap, Hsf.
  + rename Sem_frag_stmt_component into IHs ; specialize (IHs s).
    apply Sem_frag_stmts_cat in Hsf.
    destruct Hsf as [vm_temp [ct_temp [Hsf_s Hsf_ss]]].
    specialize IHs with (1 := Hct_sub_vm) (2 := Hsf_s).
    specialize IHss with (1 := proj1 IHs) (2 := Hsf_ss).
    split.
    - by apply IHss.
    split ; destruct IHs as [_ IHs].
    - by apply (CEP.Lemmas.submap_trans (proj1 IHs)), IHss.
    - by apply (CEP.Lemmas.submap_trans (proj2 IHs)), IHss.
* clear Sem_frag_stmt_component.
  destruct s as [|var ft|var reg|var mem|var1 var2|var expr|ref expr|ref|cond sst ssf] ; simpl ;
        intros vm_old ct_old vm_new ct_new tmap Hct_sub_vm Hsf.
  + (* Sskip *)
    split.
    - intro k ; specialize (Hct_sub_vm k).
      by rewrite (proj1 Hsf) (proj2 Hsf) // in Hct_sub_vm.
    - split ; by apply CEP.Lemmas.Equal_submap, Hsf.
  + (* Swire *)
    destruct Hsf as [vm' [ct' [Hsf Heq]]].
    destruct (CEP.find var tmap) as [[newft [| | | |]]|] ; try by contradiction Hsf.
    split.
    - intro k ; specialize (Hct_sub_vm k).
      destruct (fst k == fst var) eqn: Hfst ; move /eqP : Hfst => Hfst ;
            last  by (destruct Hsf as [_ [Hsf_vm [Hsf_ct _]]] ;
                      specialize (Hsf_vm (fst k) (snd k)) ;
                      specialize (Hsf_ct (fst k) (snd k)) ;
                      rewrite -surjective_pairing (proj1 Heq) (proj2 Heq) in Hsf_vm, Hsf_ct ;
                      rewrite Hsf_vm in Hct_sub_vm ; last (by left ; exact Hfst) ;
                      rewrite Hsf_ct // in Hct_sub_vm ; last (by left ; exact Hfst)).
      destruct (snd k < snd var) eqn: Hsnd_small ;
            first by (destruct Hsf as [_ [Hsf_vm [Hsf_ct _]]] ;
                      specialize (Hsf_vm (fst k) (snd k)) ;
                      specialize (Hsf_ct (fst k) (snd k)) ;
                      rewrite -surjective_pairing (proj1 Heq) (proj2 Heq) in Hsf_vm, Hsf_ct ;
                      rewrite Hsf_vm in Hct_sub_vm ; last (by right ; left ; exact Hsnd_small) ;
                      rewrite Hsf_ct // in Hct_sub_vm ; last (by right ; left ; exact Hsnd_small)).
      destruct (size_of_ftype newft + snd var <= snd k) eqn: Hsnd_large ;
            first by (destruct Hsf as [_ [Hsf_vm [Hsf_ct _]]] ;
                      specialize (Hsf_vm (fst k) (snd k)) ;
                      specialize (Hsf_ct (fst k) (snd k)) ;
                      rewrite -surjective_pairing (proj1 Heq) (proj2 Heq) in Hsf_vm, Hsf_ct ;
                      rewrite Hsf_vm in Hct_sub_vm ; last (by right ; right ; exact Hsnd_large) ;
                      rewrite Hsf_ct // in Hct_sub_vm ; last (by right ; right ; exact Hsnd_large)).
      destruct Hsf as [Hsf_vm [_ [_ Hsf_ct]]].
      specialize (Hsf_vm (snd k - snd var)) ; specialize (Hsf_ct (snd k - snd var)).
      generalize (List.nth_error_Some (list_rhs_type_p newft) (snd k - snd var)) ; intro.
      replace (length (list_rhs_type_p newft)) with (size_of_ftype newft) in H
            by (rewrite -list_rhs_type_p_size ; reflexivity).
      rewrite ltnNge in Hsnd_small ; apply negbFE in Hsnd_small.
      rewrite leqNgt addnC -ltn_subLR // in Hsnd_large ; apply negbFE in Hsnd_large.
      specialize (Hsf_ct Hsnd_large).
      destruct H as [_ H] ; specialize (H (simplssrlib.Nats.ltn_lt Hsnd_large)).
      destruct (List.nth_error (list_rhs_type_p newft) (snd k - snd var)) ; last by contradiction H.
      rewrite -Hfst subnK // nat_of_binK -surjective_pairing in Hsf_vm, Hsf_ct.
      by rewrite -(proj1 Heq) -(proj2 Heq) (proj2 Hsf_vm) Hsf_ct //.
    split.
    - intros k v H0.
      destruct (fst k == fst var) eqn: Hfst ; move /eqP : Hfst => Hfst ;
            last  by (destruct Hsf as [_ [Hsf_vm _]] ;
                      specialize (Hsf_vm (fst k) (snd k)) ;
                      rewrite -surjective_pairing (proj1 Heq) in Hsf_vm ;
                      rewrite -Hsf_vm // ; last (by left ; exact Hfst)).
      destruct (snd k < snd var) eqn: Hsnd_small ;
            first by (destruct Hsf as [_ [Hsf_vm _]] ;
                      specialize (Hsf_vm (fst k) (snd k)) ;
                      rewrite -surjective_pairing (proj1 Heq) in Hsf_vm ;
                      rewrite -Hsf_vm // ; last (by right ; left ; exact Hsnd_small)).
      destruct (size_of_ftype newft + snd var <= snd k) eqn: Hsnd_large ;
            first by (destruct Hsf as [_ [Hsf_vm _]] ;
                      specialize (Hsf_vm (fst k) (snd k)) ;
                      rewrite -surjective_pairing (proj1 Heq) in Hsf_vm ;
                      rewrite -Hsf_vm // ; last (by right ; right ; exact Hsnd_large)).
      destruct Hsf as [Hsf_vm _].
      specialize (Hsf_vm (snd k - snd var)).
      generalize (List.nth_error_Some (list_rhs_type_p newft) (snd k - snd var)) ; intro.
      replace (length (list_rhs_type_p newft)) with (size_of_ftype newft) in H
            by (rewrite -list_rhs_type_p_size ; reflexivity).
      rewrite ltnNge in Hsnd_small ; apply negbFE in Hsnd_small.
      rewrite leqNgt addnC -ltn_subLR // in Hsnd_large ; apply negbFE in Hsnd_large.
      destruct H as [_ H] ; specialize (H (simplssrlib.Nats.ltn_lt Hsnd_large)).
      destruct (List.nth_error (list_rhs_type_p newft) (snd k - snd var)) ; last by contradiction H.
      rewrite -Hfst subnK // nat_of_binK -surjective_pairing in Hsf_vm.
      rewrite H0 in Hsf_vm ; by discriminate (proj1 Hsf_vm).
    - intros k v H0.
      destruct (fst k == fst var) eqn: Hfst ; move /eqP : Hfst => Hfst ;
            last  by (destruct Hsf as [_ [_ [Hsf_ct _]]] ;
                      specialize (Hsf_ct (fst k) (snd k)) ;
                      rewrite -surjective_pairing (proj2 Heq) in Hsf_ct ;
                      rewrite -Hsf_ct // ; last (by left ; exact Hfst)).
      destruct (snd k < snd var) eqn: Hsnd_small ;
            first by (destruct Hsf as [_ [_ [Hsf_ct _]]] ;
                      specialize (Hsf_ct (fst k) (snd k)) ;
                      rewrite -surjective_pairing (proj2 Heq) in Hsf_ct ;
                      rewrite -Hsf_ct // ; last (by right ; left ; exact Hsnd_small)).
      destruct (size_of_ftype newft + snd var <= snd k) eqn: Hsnd_large ;
            first by (destruct Hsf as [_ [_ [Hsf_ct _]]] ;
                      specialize (Hsf_ct (fst k) (snd k)) ;
                      rewrite -surjective_pairing (proj2 Heq) in Hsf_ct ;
                      rewrite -Hsf_ct // ; last (by right ; right ; exact Hsnd_large)).
      destruct Hsf as [Hsf_vm _].
      specialize (Hsf_vm (snd k - snd var)).
      generalize (List.nth_error_Some (list_rhs_type_p newft) (snd k - snd var)) ; intro.
      replace (length (list_rhs_type_p newft)) with (size_of_ftype newft) in H
            by (rewrite -list_rhs_type_p_size ; reflexivity).
      rewrite ltnNge in Hsnd_small ; apply negbFE in Hsnd_small.
      rewrite leqNgt addnC -ltn_subLR // in Hsnd_large ; apply negbFE in Hsnd_large.
      destruct H as [_ H] ; specialize (H (simplssrlib.Nats.ltn_lt Hsnd_large)).
      destruct (List.nth_error (list_rhs_type_p newft) (snd k - snd var)) ; last by contradiction H.
      rewrite -Hfst subnK // nat_of_binK -surjective_pairing in Hsf_vm.
      specialize (Hct_sub_vm k) ; rewrite H0 (proj1 Hsf_vm) in Hct_sub_vm.
      destruct v ; contradiction Hct_sub_vm.
  + (* Sreg -- should be similar to Swire *)
    admit.
  + (* Smem *)
    destruct Hsf as [vm' [ct' [Hsf _]]] ; contradiction Hsf.
  + (* Sinst *)
    destruct Hsf as [vm' [ct' [Hsf _]]] ; contradiction Hsf.
  + (* Snode -- should be similar to Swire *)
    admit.
  + (* Sfcnct *)
    split.
    - intro k ; specialize (Hct_sub_vm k).
      by rewrite (proj1 Hsf) (proj2 Hsf) // in Hct_sub_vm.
    - split ; by apply CEP.Lemmas.Equal_submap, Hsf.
  + (* Sinvalid *)
    split.
    - intro k ; specialize (Hct_sub_vm k).
      by rewrite (proj1 Hsf) (proj2 Hsf) // in Hct_sub_vm.
    - split ; by apply CEP.Lemmas.Equal_submap, Hsf.
  + (* Swhen *)
    apply Sem_frag_stmts_cat in Hsf.
    destruct Hsf as [vm_true [ct_true [Hsf_t Hsf_f]]].
    rename Sem_frag_stmts_component into IHsst.
    generalize (IHsst ssf) ; intro IHssf.
    specialize (IHsst sst) with (1 := Hct_sub_vm) (2 := Hsf_t).
    specialize IHssf with (1 := proj1 IHsst) (2 := Hsf_f).
    split.
    - by apply IHssf.
    - destruct IHsst as [_ IHsst], IHssf as [_ IHssf].
      split.
      - by apply (CEP.Lemmas.submap_trans (proj1 IHsst)), IHssf.
      - by apply (CEP.Lemmas.submap_trans (proj2 IHsst)), IHssf.
Admitted.

Definition subdomain_undef (m1 m2 : CEP.t def_expr) : Prop :=
forall (k : CEP.key),
    match CEP.find k m1, CEP.find k m2 with
    | None, _ => True
    | _, None => False
    | Some D_undefined, _ => True
    | _, Some D_undefined => False
    | _, _ => True
    end.

Lemma subdomain_undef_refl :
forall m : CEP.t def_expr,
    subdomain_undef m m.
Proof.
intros m k.
destruct (CEP.find k m) as [[| |expr]|] ; done.
Qed.

Lemma subdomain_undef_trans :
forall m2 m1 m3 : CEP.t def_expr,
        subdomain_undef m1 m2
    ->
        subdomain_undef m2 m3
    ->
        subdomain_undef m1 m3.
Proof.
intros m2 m1 m3 H12 H23 k.
specialize (H12 k) ; specialize (H23 k).
destruct (CEP.find k m1) as [[| |expr1]|] ; try done ;
destruct (CEP.find k m2) as [[| |expr2]|] ; try done ;
destruct (CEP.find k m3) ; done.
Qed.

Lemma subdomain_undef_none_add {m1 m2 : CEP.t def_expr} {k : CEP.key} (e : def_expr) :
        subdomain_undef m1 m2
    ->
        CEP.find k m1 = None
    ->
        subdomain_undef m1 (CEP.add k e m2).
Proof.
intros Hsd Hnone k0.
destruct (k0 == k) eqn: Hk0k.
* move /eqP : Hk0k => Hk0k ; subst k0.
  rewrite Hnone //.
* rewrite (CEP.Lemmas.find_add_neq (elimT negP (negbT Hk0k))) //.
  by apply Hsd.
Qed.

Definition old_ct_sub_new_ct
    (* The predicate checks whether the old and new connection map are in a correct relationship:
       - what was out of scope (but already declared) cannot be changed
       - if the old value was defined (D_invalidated or D_fexpr), the new value cannot be D_undefined *)
    (old_scope new_scope : CEP.t (ftype * HiF.forient)) (old_ct new_ct : CEP.t def_expr) (old_tmap : CEP.t (ftype * HiF.forient))
:   Prop
:=  forall k : CEP.key,
        match CEP.find k old_scope, CEP.find k new_scope, CEP.find k old_tmap with
        | None, _, None => (* k is not yet declared (it may become declared and immediately fall out of scope again) *)
            CEP.find k old_ct = None
        | None, None, Some _ => (* k was declared earlier but is now out of scope *)
            CEP.find k old_ct = CEP.find k new_ct
        | Some s, Some t, Some u => (* k is declared and in scope. It can be changed. *)
                s = t
            /\
                t = u
            /\
                match CEP.find k old_ct, CEP.find k new_ct with
                | None, _ => True
                | _, None => False
                | Some D_undefined, _ => True
                | _, Some D_undefined => False
                | _, _ => True
                end
        | _, _, _ => False
        end.

(*
Lemma old_ct_sub_new_ct_refl :
forall (scope : CEP.t (ftype * HiF.forient)) (ct : CEP.t def_expr) (tmap: CEP.t (ftype * HiF.forient)),
        CEP.submap scope tmap
    ->
        subdomain ct tmap
    ->
        old_ct_sub_new_ct scope scope ct ct tmap.
Proof.
intros scope ct tmap Hsc_sm_tm Hct_sd_tm k.
specialize (Hsc_sm_tm k) ; specialize (Hct_sd_tm k).
destruct (CEP.find k scope).
- rewrite (Hsc_sm_tm _ Logic.eq_refl).
  split ; first by reflexivity.
  destruct (CEP.find k ct) as [[]|] ; done.
- destruct (CEP.find k tmap) ; done.
Qed. *)

(* Does not hold...
Lemma old_ct_sub_new_ct_trans :
forall (old_scope new_scope : CEP.t (ftype * HiF.forient)) (m2 m1 m3 : CEP.t def_expr),
        CEP.submap old_scope new_scope
    ->
        old_ct_sub_new_ct old_scope m1 m2
    ->
        old_ct_sub_new_ct new_scope m2 m3
    ->
        old_ct_sub_new_ct old_scope m1 m3.
Proof.
intros old_scope new_scope m2 m1 m3 Hsub H12 H23 k.
specialize (Hsub k) ; specialize (H12 k) ; specialize (H23 k).
destruct (CEP.find k old_scope).
* rewrite (Hsub _ Logic.eq_refl) in H23.
  destruct (CEP.find k m1) as [[| |expr1]|] ; try done ;
  destruct (CEP.find k m2) as [[| |expr2]|] ; try done ;
  destruct (CEP.find k m3) ; done.
* destruct (CEP.find k m1) ; try done ;
  destruct (CEP.find k m2) ; try done ; subst d0.
  destruct (CEP.find k new_scope) ; try done.
  -- unresolved.
*)

Lemma stmts_tmap_and_Sem_frag_stmts :
forall (vm_for_tmap : CEP.t vertex_type) (tmap : CEP.t (ftype * HiF.forient)),
        tmap_has_fully_inferred_ground_types tmap
    ->
        vm_sub_tmap vm_for_tmap tmap
    ->
        forall (ss : HiFP.hfstmt_seq) (old_vm : CEP.t vertex_type) (old_ct : CEP.t def_expr)
               (old_tmap old_scope : CEP.t (ftype * HiF.forient))
               (new_vm : CEP.t vertex_type) (new_ct : CEP.t def_expr) (new_tmap new_scope : CEP.t (ftype * HiF.forient)),
                stmts_tmap (old_tmap, old_scope) ss vm_for_tmap = Some (new_tmap, new_scope)
            ->
                stmts_have_fully_inferred_ground_types ss
            ->
                Sem_frag_stmts old_vm old_ct ss new_vm new_ct tmap
            ->
                CEP.submap new_tmap tmap
            ->
                all_fit_together old_scope old_ct old_ct old_vm old_tmap
            ->
                    all_fit_together new_scope new_ct new_ct new_vm new_tmap
                /\
                    old_ct_sub_new_ct old_scope new_scope old_ct new_ct old_tmap
with stmt_tmap_and_Sem_frag_stmt :
forall (vm_for_tmap : CEP.t vertex_type) (tmap : CEP.t (ftype * HiF.forient)),
        tmap_has_fully_inferred_ground_types tmap
    ->
        vm_sub_tmap vm_for_tmap tmap
    ->
        forall (s : HiFP.hfstmt) (old_vm : CEP.t vertex_type) (old_ct : CEP.t def_expr)
               (old_tmap old_scope : CEP.t (ftype * HiF.forient))
               (new_vm : CEP.t vertex_type) (new_ct : CEP.t def_expr) (new_tmap new_scope : CEP.t (ftype * HiF.forient)),
                stmt_tmap (old_tmap, old_scope) s vm_for_tmap = Some (new_tmap, new_scope)
            ->
                stmt_has_fully_inferred_ground_types s
            ->
                Sem_frag_stmt old_vm old_ct s new_vm new_ct tmap
            ->
                CEP.submap new_tmap tmap
            ->
                all_fit_together old_scope old_ct old_ct old_vm old_tmap
            ->
                    all_fit_together new_scope new_ct new_ct new_vm new_tmap
                /\
                    old_ct_sub_new_ct old_scope new_scope old_ct new_ct old_tmap.
Proof.
* clear stmts_tmap_and_Sem_frag_stmts.
  intros vm_for_tmap tmap Htm_inf Hvmtm_sub_tm.
  induction ss as [|s ss] ; simpl ; intros old_vm old_ct old_tmap old_scope new_vm new_ct new_tmap new_scope Htm Hss_inf Hsf Hnew_sub_tm Haft.
  + (* Qnil *)
    injection Htm ; clear Htm ; intros ; subst new_tmap new_scope.
    split.
    - repeat (split ; first (destruct Haft as [Haft _]) ;
                      last  (destruct Haft as [_ Haft])) ;
      intro k ; try rewrite -(proj1 Hsf) ; try rewrite -(proj2 Hsf) ;
      by apply Haft.
    - intro k ; rewrite -(proj2 Hsf).
      generalize (aft_scope_submap_tmap _ _ _ _ _ Haft k) ; intro Hsc_sub_tm.
      destruct (CEP.find k old_scope).
      - rewrite (Hsc_sub_tm _ Logic.eq_refl).
        split ; first by reflexivity.
        split ; first by reflexivity.
        by apply subdomain_undef_refl.
      - destruct Haft as [_ [_ [Hct_sub_vm [Hvm_sub_tm _]]]].
        specialize (Hct_sub_vm k) ; specialize (Hvm_sub_tm k).
        destruct (CEP.find k old_tmap) ; first by reflexivity.
        destruct (CEP.find k old_vm) as [[]|] ; try by discriminate Hvm_sub_tm.
        destruct (CEP.find k old_ct) as [[]|] ; done.
  + (* Qcons *)
    rename stmt_tmap_and_Sem_frag_stmt into IHs ;
    specialize (IHs vm_for_tmap tmap Htm_inf Hvmtm_sub_tm s old_vm old_ct old_tmap old_scope).
    move /andP : Hss_inf => Hss_inf.
    (* simplify stmts_tmap *)
    generalize (aft_scope_submap_tmap _ _ _ _ _ Haft) ; intro Holdsc_sub_tm.
    generalize (stmt_submap vm_for_tmap s old_tmap old_scope Holdsc_sub_tm) ; intro Htm_sub_s.
    destruct (stmt_tmap (old_tmap, old_scope) s vm_for_tmap) as [[s_tmap s_scope]|] ; last by discriminate Htm.
    specialize IHs with (1 := Logic.eq_refl) (2 := proj1 Hss_inf).
    generalize (stmts_submap vm_for_tmap ss s_tmap s_scope (proj1 Htm_sub_s)) ;
          rewrite Htm ; intro Htm_sub_ss.
    specialize IHss with (1 := Htm) (2 := proj2 Hss_inf).
    (* simplify Sem_frag_stmts *)
    destruct Hsf as [s_vm [s_ct [Hsf_s Hsf_ss]]].
    specialize IHs with (1 := Hsf_s) (2 := CEP.Lemmas.submap_trans (proj1 (proj2 Htm_sub_ss)) Hnew_sub_tm) (3 := Haft).
    specialize IHss with (1 := Hsf_ss) (2 := Hnew_sub_tm) (3 := proj1 IHs).
    split ; first by apply IHss.
    intro k.
    destruct Htm_sub_s as [Hssc_sub_stm [Hotm_sub_stm Htm_sub_s]] ;
    specialize (Hssc_sub_stm k) ; specialize (Hotm_sub_stm k) ; specialize (Htm_sub_s k).
    destruct IHs as [_ IHs] ; specialize (IHs k).
    destruct IHss as [_ IHss] ; specialize (IHss k).
    destruct (CEP.find k old_scope).
    - specialize (Htm_sub_s _ Logic.eq_refl).
      rewrite Htm_sub_s in IHs, IHss.
      rewrite (proj2 (proj2 Htm_sub_ss) k _ Htm_sub_s) in IHss.
      rewrite (proj2 (proj2 Htm_sub_ss) k _ Htm_sub_s).
      destruct (CEP.find k old_tmap) ; last by contradiction IHs.
      destruct IHs as [_ [IHs' IHs]] ; subst p0.
      split ; first by reflexivity.
      split ; first by reflexivity.
      rewrite (Hssc_sub_stm _ Htm_sub_s) in IHss.
      destruct IHss as [_ [_ IHss]].
      destruct (CEP.find k old_ct) as [[| |expr_old]|],
               (CEP.find k s_ct) as [[| |expr_s]|],
               (CEP.find k new_ct) as [[| |expr_new]|] ; by done.
    - destruct Htm_sub_ss as [_ [_ Hssc_sub_newsc]] ;
      specialize (Hssc_sub_newsc k).
      destruct (CEP.find k s_scope) ; first by rewrite (Hssc_sub_newsc _ Logic.eq_refl) //.
      destruct (CEP.find k new_scope).
      * destruct (CEP.find k old_tmap) ; last by apply IHs.
        by rewrite (Hotm_sub_stm _ Logic.eq_refl) // in IHss.
      * destruct (CEP.find k old_tmap).
        + rewrite IHs.
          by rewrite (Hotm_sub_stm _ Logic.eq_refl) // in IHss.
        + by apply IHs.
* clear stmt_tmap_and_Sem_frag_stmt.
  intros vm_for_tmap tmap Htm_inf Hvmtm_sub_tm.
  destruct s as [|var ft|var reg|var mem|var1 var2|var expr|ref expr|ref|cond sst ssf] ;
  simpl ; intros old_vm old_ct old_tmap old_scope new_vm new_ct new_tmap new_scope Htm Hs_inf Hsf Hnew_sub_tm Haft.
  + (* Sskip *)
    injection Htm ; clear Htm ; intros ; subst new_tmap new_scope.
    split.
    - repeat (split ; first (destruct Haft as [Haft _]) ;
                      last  (destruct Haft as [_ Haft])) ;
      intro k ; try rewrite -(proj1 Hsf) ; try rewrite -(proj2 Hsf) ;
      by apply Haft.
    - intro k ; rewrite -(proj2 Hsf).
      generalize (aft_scope_submap_tmap _ _ _ _ _ Haft k) ; intro Hsc_sub_tm.
      destruct (CEP.find k old_scope).
      - rewrite (Hsc_sub_tm _ Logic.eq_refl).
        split ; first by reflexivity.
        split ; first by reflexivity.
        by apply subdomain_undef_refl.
      - destruct Haft as [_ [_ [Hct_sub_vm [Hvm_sub_tm _]]]].
        specialize (Hct_sub_vm k) ; specialize (Hvm_sub_tm k).
        destruct (CEP.find k old_tmap) ; first by reflexivity.
        destruct (CEP.find k old_vm) as [[]|] ; try by discriminate Hvm_sub_tm.
        destruct (CEP.find k old_ct) as [[]|] ; done.
  + (* Swire *)
    destruct ft as [gt| |] ; try by discriminate Hs_inf.
    specialize (Hnew_sub_tm var).
    destruct (CEP.find var tmap) as [[newft [| | | |]]|] ;
          try (by contradiction Hsf).
    generalize (fully_inferred_does_not_change gt var vm_for_tmap Hs_inf) ; intro Hfidnc.
    generalize (CEP.Lemmas.submap_none_add (k := var) (Gtyp gt, HiF.Duplex) (CEP.Lemmas.submap_refl old_tmap)) ; intro Hadd_submap.
    generalize (aft_scope_submap_tmap _ _ _ _ _ Haft) ; intro Holdsc_sub_tm.
    destruct (CEP.find var old_tmap) eqn: Hold_tm ; first by discriminate Htm.
    specialize (Hadd_submap Logic.eq_refl).
    destruct (code_type_find_vm_widths (Gtyp gt) var vm_for_tmap) as [[[gt'| |] _]|] ;
          try (by discriminate Htm) ;
          try (by contradiction Hfidnc) ;
          subst gt'.
    injection Htm ; clear Htm ; intros ; subst new_tmap new_scope.
    rewrite (CEP.Lemmas.find_add_eq (eq_refl _)) in Hnew_sub_tm ;
    specialize (Hnew_sub_tm _ Logic.eq_refl).
    injection Hnew_sub_tm ; clear Hnew_sub_tm ; intros ; subst newft.
    simpl in Hsf ; rewrite add1n in Hsf.
    split.
    - repeat (split ; first (destruct Haft as [Haft _]) ;
                      last  (destruct Haft as [_ Haft])) ;
      intro k ; specialize (Haft k) ;
      try (by destruct (CEP.find k new_ct) ; done) ;
      (destruct (k == var) eqn: Hkvar ;
            first (move /eqP : Hkvar => Hkvar ; subst k ;
                   try rewrite (CEP.Lemmas.find_add_eq (eq_refl _)) ;
                   destruct Hsf as [Hvm [_ [_ Hct]]] ;
                   specialize (Hvm 0) ; specialize (Hct 0 (ltn0Sn _)) ; simpl in Hvm ;
                   rewrite add0n nat_of_binK -surjective_pairing in Hvm, Hct ;
                   try rewrite (proj2 Hvm) // ;
                   try rewrite Hct //) ;
            last  (try rewrite (CEP.Lemmas.find_add_neq (elimT negP (negbT Hkvar))) ;
                   destruct Hsf as [_ [Hvm [Hct _]]] ;
                   specialize (Hvm k.1 k.2 (Hneq_12small_large _ _ Hkvar)) ; specialize (Hct k.1 k.2 (Hneq_12small_large _ _ Hkvar)) ;
                   rewrite -surjective_pairing in Hvm, Hct ;
                   try rewrite -Hvm // ;
                   try rewrite -Hct //)).
      * destruct (CEP.find k old_scope) as [[ft_tgt [| | | |]]|] ; try by done.
        1,2: destruct (CEP.find k old_ct) as [[| |expr]|] ; try by done.
        1,2: generalize (type_of_expr_submap expr old_tmap (CEP.add var (Gtyp gt, HiF.Duplex) old_tmap) Hadd_submap) ; intro Htype_expr.
        1,2: destruct (type_of_expr expr old_tmap) as [[ft_src Hft_src_exp]|] ; try by contradiction Haft.
        1,2: by rewrite Htype_expr //.
      * destruct (CEP.find k old_ct) as [[| |expr]|] ; try by exact Haft.
        destruct (CEP.find k old_vm) as [[gto|gto|gto|gto|gto]|] ; try by exact Haft.
        1-3: generalize (type_of_expr_submap expr old_tmap (CEP.add var (Gtyp gt, HiF.Duplex) old_tmap) Hadd_submap) ; intro Htype_expr.
        1-3: destruct (type_of_expr expr old_tmap) as [[[gt_expr| |] Hgt_expr_exp]|] ; try by contradiction Haft.
        1-3: by rewrite Htype_expr //.
      * destruct (CEP.find k old_ct) as [[| |expr]|] ; try by exact Haft.
        generalize (type_of_expr_submap expr old_tmap (CEP.add var (Gtyp gt, HiF.Duplex) old_tmap) Hadd_submap) ; intro Htype_expr.
        destruct (type_of_expr expr old_tmap) as [[[gt_expr| |] Hgt_expr_exp]|] ; try by contradiction Haft.
        by rewrite Htype_expr //.
    - intro k.
      destruct (k == var) eqn: Hkvar.
      * rewrite (CEP.Lemmas.find_add_eq Hkvar).
        move /eqP : Hkvar => Hkvar ; subst k.
        specialize (Holdsc_sub_tm var) ; rewrite Hold_tm in Holdsc_sub_tm.
        destruct (CEP.find var old_scope) ; first by discriminate (Holdsc_sub_tm _ Logic.eq_refl).
        rewrite Hold_tm.
        destruct Hsf as [Hvm _(*[_ [_ Hct]]*)].
        specialize (Hvm 0) ; simpl in Hvm.
        rewrite add0n nat_of_binK -surjective_pairing in Hvm.
        destruct Haft as [_ [_ [Hct_sub_vm _]]] ; specialize (Hct_sub_vm var).
        rewrite (proj1 Hvm) in Hct_sub_vm.
        destruct (CEP.find var old_ct) as [[]|] ; done.
      * rewrite (CEP.Lemmas.find_add_neq (elimT negP (negbT Hkvar))).
        destruct Hsf as [_ [Hvm [Hct _]]].
        specialize (Hct k.1 k.2 (Hneq_12small_large _ _ Hkvar)).
        rewrite -surjective_pairing in Hct ; rewrite -Hct.
        specialize (Holdsc_sub_tm k).
        destruct (CEP.find k old_scope).
        + rewrite (Holdsc_sub_tm _ Logic.eq_refl).
          split ; first by reflexivity.
          split ; first by reflexivity.
          destruct (CEP.find k old_ct) as [[]|] ; done.
        + destruct Haft as [_ [_ [Hct_sub_vm [Hvm_sub_tm _]]]] ;
          specialize (Hct_sub_vm k) ; specialize (Hvm_sub_tm k).
          destruct (CEP.find k old_tmap) ; first by reflexivity.
          destruct (CEP.find k old_vm) as [[]|] ; try by discriminate Hvm_sub_tm.
          destruct (CEP.find k old_ct) as [[]|] ; done.
  + (* Sreg *)
    destruct (type reg) as [gt| |] ; try by discriminate Hs_inf.
    specialize (Hnew_sub_tm var).
    generalize (aft_scope_submap_tmap _ _ _ _ _ Haft) ; intro Holdsc_sub_tm.
    destruct (CEP.find var tmap) as [[newft [| | | |]]|] ;
          try (by contradiction Hsf).
    generalize (CEP.Lemmas.submap_none_add (k := var) (Gtyp gt, HiF.Duplex) (CEP.Lemmas.submap_refl old_tmap)) ; intro Hadd_submap.
    destruct (CEP.find var old_tmap) eqn: Hold_tm ; first by discriminate Htm.
    specialize (Hadd_submap Logic.eq_refl).
    destruct (type_of_expr (clock reg) old_scope) ; last by discriminate Htm.
    destruct (reset reg) as [|rst_sig rst_val] ; first last.
    1-2: move /andP : Hs_inf => Hs_inf.
    1-2: generalize (fully_inferred_does_not_change gt var vm_for_tmap (proj2 Hs_inf)) ; intro Hfidnc.
    1-2: destruct (code_type_find_vm_widths (Gtyp gt) var vm_for_tmap) as [[[gt'| |] _]|] ;
          try (by discriminate Htm) ;
          try (by contradiction Hfidnc) ;
          subst gt'.
    destruct (type_of_expr rst_sig old_scope) as [[[[[|[|]]| | | | | |]| |] ]|] eqn: Hrst_sig ; try by discriminate Htm.
    destruct (type_of_expr rst_val (CEP.add var (Gtyp gt, HiF.Duplex) old_scope)) ; last by discriminate Htm.
    2: destruct (type_of_expr rst_val old_scope) ; last by discriminate Htm.
    1-3: injection Htm ; clear Htm ; intros ; subst new_tmap new_scope.
    1-3: rewrite (CEP.Lemmas.find_add_eq (eq_refl _)) in Hnew_sub_tm ;
         specialize (Hnew_sub_tm _ Logic.eq_refl).
    1-3: injection Hnew_sub_tm ; clear Hnew_sub_tm ; intros ; subst newft.
    1-3: simpl in Hsf ; rewrite add1n in Hsf.
    1-3: split.
    - 1,3,5: repeat (split ; first (destruct Haft as [Haft _]) ;
                           last  (destruct Haft as [_ Haft])) ;
           intro k ; specialize (Haft k) ;
           try (by destruct (CEP.find k new_ct) ; done) ;
           (destruct (k == var) eqn: Hkvar ;
                 first (move /eqP : Hkvar => Hkvar ; subst k ;
                        try rewrite (CEP.Lemmas.find_add_eq (eq_refl _)) ;
                        destruct Hsf as [Hvm [_ [Hct [_ _]]]]) ;
                 last  (try rewrite (CEP.Lemmas.find_add_neq (elimT negP (negbT Hkvar))) ;
                        destruct Hsf as [_ [_ [_ [Hvm Hct]]]] ;
                        specialize (Hvm k.1 k.2 (Hneq_12small_large _ _ Hkvar)) ; specialize (Hct k.1 k.2 (Hneq_12small_large _ _ Hkvar)) ;
                        rewrite -surjective_pairing in Hvm, Hct ;
                        try rewrite -Hvm // ;
                        try rewrite -Hct //)).
      * 1,3,5-7,9,11,13-15:
        destruct (type_of_expr rst_val tmap) as [[rst_val_type _]|] ;
              last (by discriminate Hvm) ;
        destruct Hvm as [_ Hvm] ;
        destruct (list_rhs_expr_p rst_val rst_val_type) as [rst_val_list|] ;
              last (by contradiction Hvm).
      * 17,19,21,22,23: destruct Hvm as [_ Hvm].
      * 1-10,17-21: specialize (Hvm 0) ; specialize (Hct 0) ; simpl in Hvm ; simpl in Hct ;
                   rewrite add0n nat_of_binK -surjective_pairing in Hvm, Hct.
      * 1-10: destruct rst_val_list as [|rst_val_elt _] ; first by contradiction Hvm.
      * 1-15: try rewrite (proj2 Hvm) // ;
              try rewrite Hct //.
      * 1-9: simpl type_of_expr ;
                rewrite (CEP.Lemmas.find_add_eq (eq_refl _)) ;
                destruct gt ; try (by discriminate (proj2 Hs_inf)) ; done.
      * 1,3,4,6,7,9: destruct (CEP.find k old_scope) as [[ft_tgt [| | | |]]|] ; try (by trivial) ;
           destruct (CEP.find k old_ct) as [[| |expr]|] ; try (by exact Haft) ;
           generalize (type_of_expr_submap expr old_tmap (CEP.add var (Gtyp gt, HiF.Duplex) old_tmap) Hadd_submap) ; intro Htype_expr ;
           destruct (type_of_expr expr old_tmap) as [[ft_src Hft_src_exp]|] ; try (by contradiction Haft) ;
           by rewrite Htype_expr //.
      * 1,2,3: destruct (CEP.find k old_ct) as [[| |expr]|] ; try (by exact Haft) ;
           destruct (CEP.find k old_vm) as [[gto|gto|gto|gto|gto]|] ; try (by contradiction Haft) ;
           generalize (type_of_expr_submap expr old_tmap (CEP.add var (Gtyp gt, HiF.Duplex) old_tmap) Hadd_submap) ; intro Htype_expr ;
           destruct (type_of_expr expr old_tmap) as [[ft_src Hft_src_exp]|] ; try (by contradiction Haft) ;
           by rewrite Htype_expr //.
    - 1-3: intro k ;
           destruct (k == var) eqn: Hkvar.
      * 1,3,5: rewrite (CEP.Lemmas.find_add_eq Hkvar) ;
               move /eqP : Hkvar => Hkvar ; subst k ;
               specialize (Holdsc_sub_tm var) ; rewrite Hold_tm in Holdsc_sub_tm ;
               destruct (CEP.find var old_scope) ; first (by discriminate (Holdsc_sub_tm _ Logic.eq_refl)) ;
               rewrite Hold_tm.
        1-3: destruct Hsf as [Hvm _(*[_ [Hct _]]*)].
        1-2: destruct (type_of_expr rst_val tmap) as [[rst_val_type _]|] ; last by discriminate Hvm.
        1-3: destruct Hvm as [_ Hvm].
        1-2: destruct (list_rhs_expr_p rst_val rst_val_type) as [rst_val_list|] ; last by contradiction Hvm.
        1-3: specialize (Hvm 0) ; simpl in Hvm ;
             rewrite add0n nat_of_binK -surjective_pairing in Hvm.
        1-2: destruct rst_val_list as [|rst_val_elt _] ; first by contradiction Hvm.
        1-3: destruct Haft as [_ [_ [Hct_sub_vm _]]] ; specialize (Hct_sub_vm var) ;
               rewrite (proj1 Hvm) in Hct_sub_vm ;
               destruct (CEP.find var old_ct) as [[]|] ; done.
      * 1-3: rewrite (CEP.Lemmas.find_add_neq (elimT negP (negbT Hkvar))) ;
             destruct Hsf as [_ [_ [_ [_ Hct]]]] ;
             specialize (Hct k.1 k.2 (Hneq_12small_large _ _ Hkvar)) ;
             rewrite -surjective_pairing in Hct ;
             rewrite -Hct.
        1-3: specialize (Holdsc_sub_tm k) ; destruct (CEP.find k old_scope).
        + 1,3,5: rewrite (Holdsc_sub_tm _ Logic.eq_refl) ;
                 split ; first (by reflexivity) ;
                 split ; first (by reflexivity) ;
                 destruct (CEP.find k old_ct) as [[]|] ; done.
        + 1-3: destruct Haft as [_ [_ [Hct_sub_vm [Hvm_sub_tm _]]]] ;
               specialize (Hct_sub_vm k) ; specialize (Hvm_sub_tm k) ;
               destruct (CEP.find k old_tmap) ; first by reflexivity.
          1-3: destruct (CEP.find k old_vm) as [[]|] ; try by discriminate Hvm_sub_tm.
          1-3: destruct (CEP.find k old_ct) as [[]|] ; done.
  + (* Smem *)
    by discriminate Htm.
  + (* Sinst *)
    by discriminate Htm.
  + (* Snode *)
    (*destruct ft as [gt| |] ; try by discriminate Hs_inf.*)
    (*generalize (Hnew_sub_tm var) ; intro Hnew_sub_tm'.
    destruct (CEP.find var tmap) as [[newft [| | | |]]|] ;
          try (by contradiction Hsf).*)
    (*generalize (fully_inferred_does_not_change gt var vm_for_tmap Hs_inf) ; intro Hfidnc.*)
    specialize (CEP.Lemmas.submap_none_add (m1 := old_tmap) (m2 := old_tmap) (k := var))
          with (1 := (CEP.Lemmas.submap_refl old_tmap)) ; intro Hadd_submap.
    generalize (aft_scope_submap_tmap _ _ _ _ _ Haft) ; intro Holdsc_sub_tm.
    destruct (CEP.find var old_tmap) eqn: Hfindk_old ; first by discriminate Htm.
    generalize (type_of_expr_submap expr old_scope tmap) ; intro Htype_expr.
    destruct (type_of_expr expr old_scope) as [[newft Hexpr_exp]|] ; last by discriminate Htm.
    injection Htm ; clear Htm ; intros ; subst new_tmap new_scope.
    specialize (Hadd_submap (newft, HiF.Source) Logic.eq_refl).
    specialize (Htype_expr (CEP.Lemmas.submap_trans (CEP.Lemmas.submap_trans (aft_scope_submap_tmap _ _ _ _ _ Haft) Hadd_submap) Hnew_sub_tm)).
    rewrite Htype_expr in Hsf.
    generalize (expr_preserves_fully_inferred tmap Htm_inf expr Hs_inf) ; intro Hexpr_inf.
    rewrite Htype_expr in Hexpr_inf, Hsf.
    destruct newft as [newgt| |] ; try by contradiction Hexpr_inf.
    simpl in Hsf ; rewrite add1n in Hsf.
    replace (list_rhs_expr_p expr (Gtyp newgt)) with (Some [:: expr]) in Hsf by (destruct expr ; done).
    (*rewrite (CEP.Lemmas.find_add_eq (eq_refl _)) in Hnew_sub_tm' ;
    specialize (Hnew_sub_tm' _ Logic.eq_refl).
    injection Hnew_sub_tm' ; clear Hnew_sub_tm' ; intros ; subst newt.*)
    split.
    - repeat (split ; first (destruct Haft as [Haft Haft']) ;
                      last  (destruct Haft as [_ Haft])) ;
      intro k ; specialize (Haft k) ;
      try (by destruct (CEP.find k new_ct) ; done) ;
      try rewrite -(proj2 (proj2 Hsf)) // ;
      (destruct (k == var) eqn: Hkvar ;
          first (move /eqP : Hkvar => Hkvar ; subst k ;
                 try rewrite (CEP.Lemmas.find_add_eq (eq_refl _)) ;
                 destruct Hsf as [Hvm [_ _]] ;
                 specialize (Hvm 0) ; simpl in Hvm ;
                 rewrite add0n nat_of_binK -surjective_pairing // in Hvm ;
                 try rewrite (proj2 Hvm) //) ;
          last  (try rewrite (CEP.Lemmas.find_add_neq (elimT negP (negbT Hkvar))) ;
                 destruct Hsf as [_ [Hvm _]] ;
                 specialize (Hvm k.1 k.2 (Hneq_12small_large _ _ Hkvar)) ;
                 rewrite -surjective_pairing // in Hvm ;
                 try rewrite -Hvm //)).
      * destruct Haft' as [_ [Haft' _]] ; specialize (Haft' var).
        rewrite (proj1 Hvm) in Haft'.
        destruct (CEP.find var old_ct) as [[]|] ; done.
      * destruct (CEP.find k old_scope) as [[ft_tgt [| | | |]]|] ; try by trivial.
        1-2: destruct (CEP.find k old_ct) as [[| |ct_expr]|] ; try by exact Haft.
        1-2: generalize (type_of_expr_submap ct_expr old_tmap (CEP.add var (Gtyp newgt, HiF.Source) old_tmap) Hadd_submap) ; intro Htype_ct_expr.
        1-2: destruct (type_of_expr ct_expr old_tmap) as [[ft_src Hct_expr_exp]|] ; try by contradiction Haft.
        1-2: by rewrite Htype_ct_expr //.
      * by rewrite (proj1 Hvm) // in Haft.
      * destruct (CEP.find k old_ct) as [[| |ct_expr]|] ; try by exact Haft.
        destruct (CEP.find k old_vm) as [[gto|gto|gto|gto|gto]|] ; try by exact Haft.
        1-3: generalize (type_of_expr_submap ct_expr old_tmap (CEP.add var (Gtyp newgt, HiF.Source) old_tmap) Hadd_submap) ; intro Htype_ct_expr.
        1-3: destruct (type_of_expr ct_expr old_tmap) as [[[gt_src| |] Hct_expr_exp]|] ; try by contradiction Haft.
        1-3: by rewrite Htype_ct_expr //.
      * rewrite Hfindk_old // in Haft.
        destruct (CEP.find var old_ct) as [[| |ct_expr]|] ; try by exact Haft.
        destruct (type_of_expr ct_expr old_tmap) as [[[gt_expr| |] Hct_expr_exp]|] ; by contradiction Haft.
      * destruct (CEP.find k old_ct) as [[| |ct_expr]|] ; try by exact Haft.
        generalize (type_of_expr_submap ct_expr old_tmap (CEP.add var (Gtyp newgt, HiF.Source) old_tmap) Hadd_submap) ; intro Htype_ct_expr.
        destruct (type_of_expr ct_expr old_tmap) as [[[gt_expr| |] Hct_expr_exp]|] ; try by contradiction Haft.
        by rewrite Htype_ct_expr //.
    - intro k.
      destruct (k == var) eqn: Hkvar.
      * rewrite (CEP.Lemmas.find_add_eq Hkvar).
        move /eqP : Hkvar => Hkvar ; subst k.
        specialize (Holdsc_sub_tm var) ; rewrite Hfindk_old in Holdsc_sub_tm.
        destruct (CEP.find var old_scope) ; first by discriminate (Holdsc_sub_tm _ Logic.eq_refl).
        rewrite Hfindk_old.
        destruct Hsf as [Hvm _(*[_ Hct]*)].
        specialize (Hvm 0) ; simpl in Hvm.
        rewrite add0n nat_of_binK -surjective_pairing in Hvm.
        destruct Haft as [_ [_ [Hct_sub_vm _]]] ; specialize (Hct_sub_vm var).
        rewrite (proj1 Hvm) in Hct_sub_vm.
        destruct (CEP.find var old_ct) as [[]|] ; done.
      * rewrite (CEP.Lemmas.find_add_neq (elimT negP (negbT Hkvar))).
        rewrite -(proj2 (proj2 Hsf)).
        specialize (Holdsc_sub_tm k).
        destruct (CEP.find k old_scope).
        + rewrite (Holdsc_sub_tm _ Logic.eq_refl).
          split ; first by reflexivity.
          split ; first by reflexivity.
          destruct (CEP.find k old_ct) as [[]|] ; done.
        + destruct Haft as [_ [_ [Hct_sub_vm [Hvm_sub_tm _]]]] ;
          specialize (Hct_sub_vm k) ; specialize (Hvm_sub_tm k).
          destruct (CEP.find k old_tmap) ; first by reflexivity.
          destruct (CEP.find k old_vm) as [[]|] ; try by discriminate Hvm_sub_tm.
          destruct (CEP.find k old_ct) as [[]|] ; done.
  * (* Sfcnct *)
    (*generalize (list_lhs_ref_p_type tmap ref) -- later *)
    generalize (aft_scope_submap_tmap _ _ _ _ _ Haft) ; intro Holdsc_sub_tm.
    generalize (type_of_ref_submap ref old_scope tmap) ; intro Htype_ref.
    destruct (type_of_ref ref old_scope) as [[ft_tgt ori_tgt]|] eqn: Htype_ref_scope ; last by discriminate Htm.
    destruct expr eqn: Hexpr.
    1-6: generalize (type_of_expr_submap expr old_scope old_tmap) ; intro Htype_expr ;
         rewrite -Hexpr in Htm ;
         destruct (type_of_expr expr old_scope) as [[ft_src Hft_src_inf]|] ; last by discriminate Htm.
    7: simpl type_of_expr in Htm ;
       generalize (type_of_ref_submap h old_scope old_tmap) ; intro Htype_expr ;
       destruct (type_of_ref h old_scope) as [[ft_src ori_src]|] ; last (by discriminate Htm) ;
       destruct ori_src ; try (by discriminate Htm) ; (* leads to two goals *)
       destruct (ftype_is_passive ft_src) ; try (by discriminate Htm).
    1-8: injection Htm ; clear Htm ; intros ; subst new_tmap new_scope ;
         specialize (Htype_ref (CEP.Lemmas.submap_trans Holdsc_sub_tm Hnew_sub_tm)) ;
         specialize (Htype_expr Holdsc_sub_tm).
    1-8: move /andP : Hs_inf => Hs_inf ;
         generalize (ref_preserves_fully_inferred tmap Htm_inf ref (proj1 Hs_inf)) ; intro Href_inf ;
         rewrite Htype_ref in Href_inf ;
         destruct ft_tgt as [gt_tgt| |] ; try (by contradiction Href_inf).
    1-6: generalize (type_of_expr_submap expr old_tmap tmap Hnew_sub_tm) ; intro Htype_expr' ;
         rewrite Htype_expr in Htype_expr' ;
         generalize (expr_preserves_fully_inferred tmap Htm_inf expr) ; intro Hexpr_inf ;
         rewrite Htype_expr' Hexpr in Hexpr_inf ; specialize (Hexpr_inf (proj2 Hs_inf)).
    7-8: generalize (type_of_ref_submap h old_tmap tmap Hnew_sub_tm) ; intro Htype_expr' ;
         rewrite Htype_expr in Htype_expr' ;
         generalize (ref_preserves_fully_inferred tmap Htm_inf h) ; intro Hexpr_inf ;
         rewrite Htype_expr'       in Hexpr_inf ; specialize (Hexpr_inf (proj2 Hs_inf)).
    1-8: assert (Hold_sc_inf: tmap_has_fully_inferred_ground_types old_scope)
                     by (intro k0 ; specialize (Htm_inf k0) ; specialize (Holdsc_sub_tm k0) ;
                         destruct (CEP.find k0 old_scope) as [[ft ori]|] ; last (by trivial) ;
                         specialize (Holdsc_sub_tm _ Logic.eq_refl) ;
                         apply Hnew_sub_tm in Holdsc_sub_tm ;
                         rewrite Holdsc_sub_tm // in Htm_inf).
    1-8: assert (Hic_tmap: match list_lhs_ref_p ref tmap with
                 | Some ([:: ic], ft) => CEP.find ic old_scope = Some ft
                 | _ => False
                 end)
               by (destruct ref as [var|ref' v|ref' n|ref' expr'] eqn: Hrefffff ; simpl ;
                   simpl ref_has_fully_inferred_ground_types in Hs_inf ;
                   try (by discriminate (proj1 Hs_inf)) ;
                   simpl type_of_ref in Htype_ref_scope ;
                   try (by specialize (Holdsc_sub_tm var _ Htype_ref_scope) ;
                           apply Hnew_sub_tm in Holdsc_sub_tm ;
                           rewrite Holdsc_sub_tm /mkseq ; simpl ;
                           rewrite N.add_0_r -surjective_pairing //) ;
                   generalize (ref_preserves_fully_inferred old_scope Hold_sc_inf ref' (proj1 Hs_inf)) ;
                   intro ;
                   destruct (type_of_ref ref' old_scope) as [[[| |] ori]|] ;
                   done).
    1-8: destruct ft_src as [gt_src| |] ; try (by contradiction Hexpr_inf) ;
         generalize (list_lhs_ref_p_type tmap ref) ; intro Hlist_ref ;
         rewrite Htype_ref in Hlist_ref ;
         destruct (list_lhs_ref_p ref tmap) as [[lst_tgt list_ft]|] ; last (by contradiction Hlist_ref) ;
         subst list_ft.
    1-8: destruct lst_tgt as [|ic [|]] ; try (by contradiction Hic_tmap).
    1-6: rewrite Hexpr in Htype_expr, Htype_expr' ; rewrite Htype_expr' in Hsf ; simpl list_rhs_expr_p in Hsf.
    7-8: generalize (list_lhs_ref_p_type tmap h) ; intro Hlist_expr ;
         generalize (list_lhs_ref_p_size tmap h) ; intro Hsize_expr ;
         rewrite Htype_expr' in Hlist_expr ;
         destruct (list_lhs_ref_p h tmap) as [[lst_src list_ft]|] ; last (by contradiction Hlist_expr) ;
         subst list_ft ;
         destruct lst_src as [|oc [|]] ; try (by discriminate Hsize_expr).
    1-8: destruct Hsf as [Hvm Hsf] ;
         destruct ori_tgt ; try (by contradiction Hsf) ;
         destruct Hsf as [Hcomp Hct].
    1-12: split.
    1,3,5,7,9,11,13,15,17,19,21,23:
         repeat (split ; first (destruct Haft as [Haft Haft']) ;
                         last  (destruct Haft as [_ Haft])) ;
         intro k ; specialize (Haft k) ; try rewrite -Hvm ;
         try (by destruct (CEP.find k new_ct) ; done) ;
         (destruct (k == ic) eqn: Hkic ;
               first (move /eqP : Hkic => Hkic ; subst k ;
                      destruct Hct as [Hct _] ;
                      specialize (Hct 0) ; simpl in Hct ;
                      try rewrite (proj2 Hct) // ;
                      try rewrite Htype_expr //) ;
               last  (destruct Hct as [_ Hct] ;
                      specialize (Hct k) ;
                      rewrite mem_seq1 Hkic in Hct ;
                      try rewrite -Hct //)).
    - 1,4,7,10,13,16,19,22,25,28,31,34:
      by rewrite Hic_tmap //.
    - 1,3,5,7,9,11,13,15,17,19,21,23:
      destruct Haft' as [_ [Haft_sc_vm _]] ; specialize (Haft_sc_vm ic) ;
      rewrite Hic_tmap in Haft_sc_vm ;
      destruct (CEP.find ic old_vm) as [[gt|gt|gt|gt|gt]|] ;
      try (by contradiction Haft_sc_vm) ;
      injection Haft_sc_vm ; clear Haft_sc_vm ; intro ; subst gt ;
      exact Hcomp.
    - 1-12:
      rewrite (Holdsc_sub_tm ic _ Hic_tmap) //.
    (* old_ct_sub_new_ct for normal expressions *)
    1-12: intro k ;
          destruct (k == ic) eqn: Hkic ;
          first (by move /eqP : Hkic => Hkic ; subst k ;
                    rewrite Hic_tmap (Holdsc_sub_tm ic _ Hic_tmap) ;
                    split ; first (by reflexivity) ;
                    split ; first (by reflexivity) ;
                    destruct Hct as [Hct _] ;
                    specialize (Hct 0) ; simpl in Hct ;
                    rewrite (proj2 Hct) ;
                    destruct (CEP.find ic old_ct) as [[]|] ; done).
    1-12: destruct Hct as [_ Hct] ;
          specialize (Hct k) ;
          rewrite mem_seq1 Hkic in Hct ;
          rewrite -Hct ;
          specialize (Holdsc_sub_tm k) ;
          destruct (CEP.find k old_scope) ;
          first (by rewrite (Holdsc_sub_tm _ Logic.eq_refl) ;
                    split ; first (by reflexivity) ;
                    split ; first (by reflexivity) ;
                    destruct (CEP.find k old_ct) as [[]|] ; done).
    1-12: destruct Haft as [_ [_ [Hct_sub_vm [Hvm_sub_tm _]]]] ;
          specialize (Hct_sub_vm k) ; specialize (Hvm_sub_tm k) ;
          destruct (CEP.find k old_tmap) ; first by reflexivity.
    1-12: destruct (CEP.find k old_vm) as [[]|] ; try by discriminate Hvm_sub_tm.
    1-12: destruct (CEP.find k old_ct) as [[]|] ; done.
    (* Now remain the goals for references *)
    1-4: split.
    1,3,5,7:
         repeat (split ; first (destruct Haft as [Haft Haft']) ;
                         last  (destruct Haft as [_ Haft])) ;
         intro k ; specialize (Haft k) ; try rewrite -Hvm ;
         try (by destruct (CEP.find k new_ct) ; done) ;
         destruct ((k \in [:: ic]) || (k \in [:: oc])) eqn: Hkicoc ;
               try by (destruct Hct as [_ Hct] ;
                       specialize (Hct k) ;
                       rewrite Hkicoc in Hct ;
                       by rewrite -Hct //).
     1-12: destruct Hct as [Hct _] ; simpl in Hct.
     1-12: destruct (ic == oc) eqn: Hic ;
                  first (move /eqP : Hic => Hic ; subst oc ;
                         rewrite orbb mem_seq1 in Hkicoc ;
                         move /eqP : Hkicoc => Hkic) ;
                  last  (rewrite mem_seq1 mem_seq1 in Hkicoc ;
                         rewrite orFb in Hct ;
                         move /orP : Hkicoc => Hkicoc ;
                         destruct Hkicoc as [Hkic|Hkoc] ;
                         first (move /eqP : Hkic => Hkic) ;
                         last  (move /eqP : Hkoc => Hkoc)).
    3,6,9,12,15,18,21,24,27,30,33,36: subst k ;
         move /andP : Hct => [_ /eqP Hct] ; by rewrite Hct //.
    1,2,7,8,13,14,19,20: subst k ;
         move /andP : Hct => [/andP [Hct_old /eqP Hct_new] _] ;
         rewrite Hct_new /type_of_expr // Htype_expr Hic_tmap ;
         destruct gt_src ; done.
    1,2,5,6,9,10,13,14: subst k ;
         move /andP : Hct => [/andP [Hct_old /eqP Hct_new] _] ;
         rewrite Hct_new /type_of_expr Htype_expr ;
         destruct Haft' as [_ [Hsc_vm _]] ; specialize (Hsc_vm ic) ;
         rewrite Hic_tmap in Hsc_vm ;
         destruct (CEP.find ic old_vm) as [[gt|gt|gt|gt|gt]|] ; try (by contradiction Hsc_vm) ;
         injection Hsc_vm ; clear Hsc_vm ; intro ; subst gt ;
         destruct gt_src ; done.
    1-8: subst k ;
         move /andP : Hct => [/andP [Hct_old /eqP Hct_new] _] ;
         rewrite Hct_new /type_of_expr Htype_expr (Holdsc_sub_tm ic _ Hic_tmap) ;
         destruct gt_src ; done.
    1-4: intro k ;
         destruct ((k \in [:: ic]) || (k \in [:: oc])) eqn: Hkicoc ;
         last (destruct Hct as [_ Hct] ;
               specialize (Hct k) ;
               rewrite Hkicoc in Hct ;
               rewrite -Hct).
    - 1,3,5,7: destruct Hct as [Hct _] ; simpl in Hct ;
         destruct (ic == oc) eqn: Hic ;
                  first (move /eqP : Hic => Hic ; subst oc ;
                         rewrite orbb mem_seq1 in Hkicoc ;
                         move /eqP : Hkicoc => Hkic ; subst ic ;
                         rewrite orTb andbT in Hct ;
                         move /andP : Hct => [_ /eqP Hct] ; rewrite Hct) ;
                  last  (rewrite mem_seq1 mem_seq1 in Hkicoc ;
                         rewrite orFb in Hct ;
                         move /orP : Hkicoc => Hkicoc ;
                         destruct Hkicoc as [Hkic|Hkoc] ;
                         first (move /eqP : Hkic => Hkic ; subst ic ;
                                move /andP : Hct => [/andP [_ /eqP Hct] _] ; rewrite Hct) ;
                         last  (move /eqP : Hkoc => Hkoc ; subst oc ;
                                move /andP : Hct => [_ /eqP Hct]) ; try rewrite Hct).
      1,2,4,5,7,8,10,11:
         rewrite Hic_tmap (Holdsc_sub_tm k _ Hic_tmap) ;
         split ; first (by reflexivity) ;
         split ; first (by reflexivity) ;
         destruct (CEP.find k old_ct) as [[]|] ; done.
    1-8: specialize (Holdsc_sub_tm k) ;
           destruct (CEP.find k old_scope) ;
           first (rewrite (Holdsc_sub_tm _ Logic.eq_refl) ;
                  split ; first (by reflexivity) ;
                  split ; first (by reflexivity) ;
                  destruct (CEP.find k old_ct) as [[]|] ; done).
    1-8: destruct Haft as [_ [_ [Hct_sub_vm [Hvm_sub_tm _]]]] ;
           specialize (Hct_sub_vm k) ; specialize (Hvm_sub_tm k) ;
           destruct (CEP.find k old_tmap) ; first by reflexivity.
    1-8: destruct (CEP.find k old_vm) as [[]|] ; try by discriminate Hvm_sub_tm.
    1-8: destruct (CEP.find k old_ct) as [[]|] ; done.
  + (* Sinvalid *)
    admit.
  + (* Swhen *)
    (* prepare induction hypotheses *)
    rename stmts_tmap_and_Sem_frag_stmts into IHsst ; specialize (IHsst vm_for_tmap tmap Htm_inf Hvmtm_sub_tm).
    generalize (IHsst ssf) ; intro IHssf.
    specialize (IHsst sst old_vm old_ct old_tmap old_scope).
    move /andP : Hs_inf => [/andP [_ Hsst_inf] Hssf_inf].
    specialize IHsst with (2 := Hsst_inf) ; specialize IHssf with (2 := Hssf_inf).
    generalize (aft_scope_submap_tmap _ _ _ _ _ Haft) ; intro Holdsc_sub_tm.
    (* stmts_tmap *)
    generalize (type_of_expr_submap cond old_scope old_tmap Holdsc_sub_tm) ; intro Hcond.
    destruct (type_of_expr cond old_scope) as [[ft_cond Hft_cond_exp]|]; last by discriminate Htm.
    generalize (stmts_submap vm_for_tmap sst old_tmap old_scope Holdsc_sub_tm) ; intro Htm_sub_t.
    destruct (stmts_tmap (old_tmap, old_scope) sst vm_for_tmap) as [[tmap_t scope_t]|] ; last by discriminate Htm.
    specialize IHsst with (1 := Logic.eq_refl).
    specialize IHssf with (old_tmap := tmap_t) (old_scope := old_scope).
    generalize (stmts_submap vm_for_tmap ssf tmap_t old_scope (CEP.Lemmas.submap_trans Holdsc_sub_tm (proj1 (proj2 Htm_sub_t)))) ; intro Htm_sub_f.
    destruct (stmts_tmap (tmap_t, old_scope) ssf vm_for_tmap) as [[tmap_f scope_f]|] ; last by discriminate Htm.
    specialize IHssf with (1 := Logic.eq_refl).
    injection Htm ; clear Htm ; intros ; subst new_tmap new_scope.
    (* Sem_frag_stmts *)
    generalize (type_of_expr_submap cond old_tmap tmap (CEP.Lemmas.submap_trans (CEP.Lemmas.submap_trans (proj1 (proj2 Htm_sub_t)) (proj1 (proj2 Htm_sub_f))) Hnew_sub_tm)) ;
          intro Hcond' ; rewrite Hcond in Hcond'.
    destruct (type_of_expr cond tmap) as [[[[[|[|]]| | | | | |]| |] ]|] ; try by contradiction Hsf.
    injection Hcond' ; clear Hcond' f ; intros ; subst ft_cond.
    destruct Hsf as [vm_true [ct_true [ct_false [Hsf_t [Hsf_f Hnewct]]]]].
    specialize (Sem_frag_stmts_compatible sst old_vm old_ct vm_true ct_true tmap Hsf_t) ; intros Hsf_sub_t.
    specialize (Sem_frag_stmts_compatible ssf vm_true (extend_map_with old_ct ct_true) new_vm ct_false tmap Hsf_f) ; intros Hsf_sub_f.
    specialize IHsst with (1 := Hsf_t) (2 := CEP.Lemmas.submap_trans (proj1 (proj2 Htm_sub_f)) Hnew_sub_tm) (3 := Haft).
    destruct IHsst as [IHsst IHsst_sdu].
    assert (Haft_f_precondition: all_fit_together old_scope (extend_map_with old_ct ct_true) (extend_map_with old_ct ct_true) vm_true tmap_t).
          repeat (split ; first (destruct Haft as [Haft _], IHsst as [IHsst _]) ;
                          last  (destruct Haft as [?Haft' Haft], IHsst as [_ IHsst])) ;
          intro k ; specialize (Haft k) ; specialize (IHsst k) ;
          try done.
          - specialize (proj2 (proj2 Htm_sub_t) k) ; intro H.
            destruct (CEP.find k old_scope) as [[ft_tgt [| | | |]]|] ; try (by trivial) ;
            first (rewrite (H _ Logic.eq_refl) in IHsst ;
                   by rewrite /extend_map_with CEP.Lemmas.map2_1bis // Haft IHsst //) ;
            clear H.
            1-2: rewrite /extend_map_with CEP.Lemmas.map2_1bis // ;
            destruct (CEP.find k old_ct) as [[| |ct_expr]|] ; try done ;
            generalize (type_of_expr_submap ct_expr old_tmap tmap_t (proj1 (proj2 Htm_sub_t))) ; intro Hct_expr ;
            destruct (type_of_expr ct_expr old_tmap) as [[ft_src Hft_src_exp]|] ; try (by contradiction Haft) ;
            by rewrite Hct_expr //.
          - rewrite /extend_map_with CEP.Lemmas.map2_1bis // ;
            destruct (CEP.find k old_ct) ; done.
          - rewrite /extend_map_with CEP.Lemmas.map2_1bis // ;
            destruct (CEP.find k old_ct) as [[| |ct_old_expr]|] ; try done ;
            destruct (CEP.find k ct_true) as [[| |ct_true_expr]|] ; try done ;
            destruct Hsf_sub_t as [Hsf_sub_t _] ; specialize (Hsf_sub_t k) ;
            destruct (CEP.find k old_vm) as [[gt|gt|gt|gt|gt]|] ; try done ;
            rewrite (Hsf_sub_t _ Logic.eq_refl) // ;
            rewrite (Hsf_sub_t _ Logic.eq_refl) // in IHsst ;
            generalize (type_of_expr_submap ct_old_expr old_tmap tmap_t (proj1 (proj2 Htm_sub_t))) ; intro Hct_old_expr ;
            destruct (type_of_expr ct_old_expr old_tmap) as [[ft_src Hft_src_exp]|] ; try (by contradiction Haft) ;
            rewrite Hct_old_expr //.
          - destruct Htm_sub_t as [_ [_ Htm_sub_t]] ; specialize (Htm_sub_t k) ;
            destruct (CEP.find k old_scope) as [[ft [| | | |]]|] ; try (by trivial) ;
            rewrite (Htm_sub_t _ Logic.eq_refl) // in IHsst.
          - rewrite /extend_map_with CEP.Lemmas.map2_1bis //.
            clear Haft' Haft'0 Haft'3 ; specialize (Haft'1 k) ; specialize (Haft'2 k).
            destruct (CEP.find k old_ct) as [[| |ct_old_expr]|] ; try (by done).
            3: generalize (type_of_expr_submap ct_old_expr old_tmap tmap_t (proj1 (proj2 Htm_sub_t))) ;
               intro Htype_ct_old_expr ;
               destruct (type_of_expr ct_old_expr old_tmap) as [[[gt_expr| |] Hgt_expr_exp]|] ;
                     try (by contradiction Haft) ;
               rewrite Htype_ct_old_expr.
            1-3: destruct Htm_sub_t as [_ [Htm_sub_t _]] ; specialize (Htm_sub_t k) ;
            destruct (CEP.find k old_tmap) as [[ft [| | | |]]|] ; try done ;
            destruct (CEP.find k old_vm) as [[gt|gt|gt|gt|gt]|] ; try done ;
            injection Haft'2 ; clear Haft'2 ; intro ; subst ft ;
            rewrite (Htm_sub_t _ Logic.eq_refl) //.
    specialize IHssf with (1 := Hsf_f) (2 := Hnew_sub_tm) (3 := Haft_f_precondition).
    destruct IHssf as [IHssf IHssf_sdu].
    split.
    - repeat (split ; first (destruct Haft as [Haft _], IHsst as [IHsst IHsst'], IHssf as [IHssf _]) ;
                      last  (destruct Haft as [_ Haft], IHsst as [_ IHsst], IHssf as [_ IHssf])) ;
      intro k ; specialize (Haft k) ; specialize (IHsst k) ; specialize (IHssf k) ;
      try done ; try rewrite Hnewct.
      * destruct Htm_sub_t as [_ [Htm_sub_tmt Hsc_sub_t]], Htm_sub_f as [Hscf_sub_tmf [Htmt_sub_tmf Hsc_sub_f]].
        specialize (Hsc_sub_t k) ; specialize (Hsc_sub_f k).
        destruct (CEP.find k old_scope) as [[ft_tgt [| | | |]]|] ; try (by trivial) ;
        specialize (Hsc_sub_t _ Logic.eq_refl) ; specialize (Hsc_sub_f _ Logic.eq_refl).
        1-3: rewrite Hsc_sub_t in IHsst.
        1-3: rewrite Hsc_sub_f in IHssf.
        1-3: rewrite CEP.Lemmas.map2_1bis // /Swhen_map2_helper.
        1: rewrite IHsst IHssf //.
        1,2: destruct (CEP.find k ct_true) as [[| |expr_t]|] ; try done ;
             destruct (CEP.find k ct_false) as [[| |expr_f]|] ; try done.
        2,4: destruct (expr_t == expr_f) ;
                   last (simpl type_of_expr ;
                         generalize (type_of_expr_submap cond old_tmap tmap_f (CEP.Lemmas.submap_trans Htm_sub_tmt Htmt_sub_tmf)) ;
                         intro Hcond' ; rewrite Hcond in Hcond' ; rewrite Hcond').
        1-6: generalize (type_of_expr_submap expr_t tmap_t tmap_f Htmt_sub_tmf) ; intro Htype_expr_t ;
             destruct (type_of_expr expr_t tmap_t) as [[ft_src_t Hft_src_t_exp]|] ; last (by contradiction IHsst) ;
             rewrite Htype_expr_t //.
        (* What remains are multiplexer expressions.
           We should be able to prove that they are ground-type expressions. *)
        1-2: specialize (Htm_inf k) ;
             specialize (Hscf_sub_tmf k _ Hsc_sub_f) ; apply Hnew_sub_tm in Hscf_sub_tmf ;
             rewrite Hscf_sub_tmf in Htm_inf ; destruct ft_tgt as [gt_tgt| |] ; try (by contradiction Htm_inf) ;
             destruct (type_of_expr expr_f tmap_f) as [[ft_src_f Hft_src_f_exp]|] ; last (by contradiction IHssf).
        1-2: destruct ft_src_t as [gt_src_t| |] ; try (by destruct gt_tgt ; discriminate IHsst) ;
             destruct ft_src_f as [gt_src_f| |] ; try (by destruct gt_tgt ; discriminate IHssf) ;
             rewrite /ftype_mux /sval /proj2_sig ; simpl ftype_mux'.
        1-2: destruct gt_tgt ; try (by discriminate Htm_inf) ;
             destruct gt_src_t ; try (by contradiction Hft_src_t_exp) ;
             destruct gt_src_f ; try (by contradiction Hft_src_f_exp) ;
             done.
      * rewrite CEP.Lemmas.map2_1bis // /Swhen_map2_helper.
        destruct (CEP.find k ct_true) as [[| |expr_t]|] ; try done ;
        destruct (CEP.find k ct_false) as [[| |expr_f]|] ; try done ;
        destruct (expr_t == expr_f) ; done.
      * rewrite CEP.Lemmas.map2_1bis // /Swhen_map2_helper.
        destruct IHsst' as [Hvmt_sub_tmt [_ _]] ; specialize (Hvmt_sub_tmt k).
        destruct (CEP.find k ct_true) as [[| |expr_t]|],
                 (CEP.find k ct_false) as [[| |expr_f]|] ; try done ;
        destruct Hsf_sub_f as [Hvmt_sub_vmn _] ;
        specialize (Hvmt_sub_vmn k) ;
        destruct (CEP.find k vm_true) as [[gtt|gtt|gtt|gtt|gtt]|] eqn: Htrue_vm ; try done ;
        rewrite (Hvmt_sub_vmn _ Logic.eq_refl) // ; rewrite (Hvmt_sub_vmn _ Logic.eq_refl) // in IHssf ;
        destruct Htm_sub_t as [_ [Htm_sub_tmt _]], Htm_sub_f as [_ [Htmt_sub_tmf _]].
        4-6: destruct (expr_t == expr_f) ;
                   last (simpl type_of_expr ;
                         generalize (type_of_expr_submap cond old_tmap tmap_f (CEP.Lemmas.submap_trans Htm_sub_tmt Htmt_sub_tmf)) ;
                         intro Hcond' ; rewrite Hcond in Hcond' ; rewrite Hcond').
        1-9: generalize (type_of_expr_submap expr_t tmap_t tmap_f Htmt_sub_tmf) ; intro Htype_expr_t ;
             destruct (type_of_expr expr_t tmap_t) as [[[gt_src_t| |] Hgt_src_t_exp]|] ; try (by contradiction IHsst) ;
             rewrite Htype_expr_t //.
        (* What remains are multiplexer expressions.
           We should be able to prove that they are ground-type expressions. *)
        1-3: destruct (type_of_expr expr_f tmap_f) as [[[gt_src_f| |] Hgt_src_f_exp]|] ; try (by contradiction IHssf) ;
             rewrite /ftype_mux /sval /proj2_sig ; simpl ftype_mux'.
        1-3: apply Htmt_sub_tmf, Hnew_sub_tm in Hvmt_sub_tmt ;
             specialize (Htm_inf k) ; rewrite Hvmt_sub_tmt in Htm_inf ;
             destruct gtt ; try (by discriminate Htm_inf) ;
             destruct gt_src_t ; try (by contradiction Hgt_src_t_exp) ;
             destruct gt_src_f ; try (by contradiction Hgt_src_f_exp) ;
             done.
      * destruct Hsf_sub_t as [Hvmo_sub_vmt _] ; specialize (Hvmo_sub_vmt k).
        destruct (CEP.find k old_scope) as [[ft [| | | |]]|] ; try done ;
        destruct (CEP.find k old_vm) as [[gt|gt|gt|gt|gt]|] ; try done ;
        specialize (Hvmo_sub_vmt _ Logic.eq_refl) ;
        apply (proj1 Hsf_sub_f) in Hvmo_sub_vmt ;
        rewrite Hvmo_sub_vmt //.
      * rewrite CEP.Lemmas.map2_1bis // /Swhen_map2_helper.
        destruct Htm_sub_t as [_ [Htm_sub_tmt _]], Htm_sub_f as [_ [Htmt_sub_tmf _]].
        destruct (CEP.find k ct_true) as [[| |expr_t]|],
                 (CEP.find k ct_false) as [[| |expr_f]|] ; try done.
        5: destruct (expr_t == expr_f) ;
                   last (simpl type_of_expr ;
                         generalize (type_of_expr_submap cond old_tmap tmap_f (CEP.Lemmas.submap_trans Htm_sub_tmt Htmt_sub_tmf)) ;
                         intro Hcond' ; rewrite Hcond in Hcond' ; rewrite Hcond').
        4-7: generalize (type_of_expr_submap expr_t tmap_t tmap_f Htmt_sub_tmf) ; intro Htype_tf ;
             destruct (type_of_expr expr_t tmap_t) as [[[gt_expr_t| |] Hgt_expr_t_inf]|] ; try (by contradiction IHsst) ;
             rewrite Htype_tf.
        1,5,6: destruct (type_of_expr expr_f tmap_f) as [[[gt_expr_f| |] Hgt_expr_f_inf]|] ; try (by contradiction IHssf).
        1-7: specialize (Htmt_sub_tmf k) ;
             destruct (CEP.find k tmap_t) as [[[gt| |] [| | | |]]|] ; try (by contradiction IHsst) ;
             specialize (Htmt_sub_tmf _ Logic.eq_refl) ;
             rewrite Htmt_sub_tmf // /ftype_mux /sval /proj2_sig ; simpl ftype_mux'.
        1-2: rewrite Htmt_sub_tmf in IHssf ;
             apply Hnew_sub_tm in Htmt_sub_tmf ;
             specialize (Htm_inf k) ; rewrite Htmt_sub_tmf in Htm_inf ;
             destruct gt ; try (by discriminate Htm_inf) ;
             destruct gt_expr_t ; try (by contradiction Hgt_expr_t_exp) ;
             destruct gt_expr_f ; try (by contradiction Hgt_expr_f_exp) ;
             done.
    - intro k ; rewrite Hnewct CEP.Lemmas.map2_1bis // /Swhen_map2_helper.
      specialize (IHsst_sdu k) ; specialize (IHssf_sdu k).
      rewrite /extend_map_with CEP.Lemmas.map2_1bis // in IHssf_sdu.
      destruct Htm_sub_t as [Hsct_sub_tmt [Hotm_sub_tmt Htm_sub_t]] ; specialize (Htm_sub_t k).
      destruct Htm_sub_f as [Hscf_sub_tmf [_ Htm_sub_f]] ; specialize (Htm_sub_f k).
      specialize (Holdsc_sub_tm k).
      destruct (CEP.find k old_scope).
      * specialize (Holdsc_sub_tm _ Logic.eq_refl) ; rewrite Holdsc_sub_tm.
        split ; first by reflexivity.
        split ; first by reflexivity.
        rewrite (Htm_sub_t _ Logic.eq_refl) Holdsc_sub_tm in IHsst_sdu ; destruct IHsst_sdu as [_ [_ IHsst_sdu]].
        rewrite (Htm_sub_f _ Logic.eq_refl) (Hotm_sub_tmt k _ Holdsc_sub_tm) in IHssf_sdu ; destruct IHssf_sdu as [_ [_ IHssf_sdu]].
        destruct (CEP.find k old_ct  ) as [[| |expr_o]|],
                 (CEP.find k ct_true ) as [[| |expr_t]|],
                 (CEP.find k ct_false) as [[| |expr_f]|] ;
        try (destruct (expr_t == expr_f)) ;
        done.
      * destruct (CEP.find k scope_t).
        + destruct (CEP.find k old_tmap) ; first by contradiction IHsst_sdu.
          by exact IHsst_sdu.
        + specialize (Hotm_sub_tmt k).
          destruct (CEP.find k old_tmap) ; last by exact IHsst_sdu.
          rewrite (Hotm_sub_tmt _ Logic.eq_refl) in IHssf_sdu.
          destruct (CEP.find k scope_f) ; first by contradiction IHssf_sdu.
          rewrite -IHssf_sdu -IHsst_sdu.
          destruct (CEP.find k old_ct) as [[]|] ; try done.
          rewrite eq_refl //.
Admitted.

Lemma ExpandBranches_funs_and_Sem_frag_stmts :
forall (vm_for_tmap : CEP.t vertex_type) (tmap : CEP.t (ftype * HiF.forient)),
        tmap_has_fully_inferred_ground_types tmap
    ->
        vm_sub_tmap vm_for_tmap tmap
    ->
        forall (ss : HiFP.hfstmt_seq)
               (old_tmap old_scope tm_tmap tm_scope : CEP.t (ftype * HiF.forient))
               (old_connmap : CEP.t def_expr)
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
                ExpandBranches_funs ss old_connmap old_scope = Some (eb_connmap, eb_scope)
            ->
                Sem_frag_stmts old_vm old_ct (component_stmts_of ss) vm_comp ct_comp tmap
            ->
                all_fit_together old_scope old_connmap old_ct old_vm old_tmap
            ->
                    all_fit_together eb_scope eb_connmap ct_comp vm_comp tm_tmap
                /\
                    old_ct_sub_new_ct old_scope eb_scope old_connmap eb_connmap old_tmap
with ExpandBranch_fun_and_Sem_frag_stmt :
forall (vm_for_tmap : CEP.t vertex_type) (tmap : CEP.t (ftype * HiF.forient)),
        tmap_has_fully_inferred_ground_types tmap
    ->
        vm_sub_tmap vm_for_tmap tmap
    ->
        forall (s : HiFP.hfstmt)
               (old_tmap old_scope tm_tmap tm_scope : CEP.t (ftype * HiF.forient))
               (old_connmap : CEP.t def_expr)
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
                ExpandBranch_fun s old_connmap old_scope = Some (eb_connmap, eb_scope)
            ->
                Sem_frag_stmts old_vm old_ct (component_stmt_of s) vm_comp ct_comp tmap
            ->
                all_fit_together old_scope old_connmap old_ct old_vm old_tmap
            ->
                    all_fit_together eb_scope eb_connmap ct_comp vm_comp tm_tmap
                /\
                    old_ct_sub_new_ct old_scope eb_scope old_connmap eb_connmap old_tmap.
Proof.
* clear ExpandBranches_funs_and_Sem_frag_stmts.
  intros vm_for_tmap tmap Htm_inf Hvmtm_sub_tm.
  induction ss as [|s ss] ; simpl ; intros old_tmap old_scope tm_tmap tm_scope old_connmap eb_connmap eb_scope old_vm old_ct vm_comp ct_comp Hss_inf Hsc_sub_tm Hst Htm_sub_vm Heb Hsf Haft.
  + injection Hst ; clear Hst ; intros ; subst tm_tmap tm_scope.
    injection Heb ; clear Heb ; intros ; subst eb_connmap eb_scope.
    split.
    - repeat (split ; first (destruct Haft as [Haft _] ; try by apply Haft) ;
                      last  (destruct Haft as [_ Haft])) ;
      intro k ; specialize (Haft k) ;
      try rewrite -(proj1 Hsf) ; try rewrite -(proj2 Hsf) ;
      by apply Haft.
    - intro k.
      specialize (Hsc_sub_tm k).
      destruct (CEP.find k old_scope).
      * rewrite (Hsc_sub_tm _ Logic.eq_refl).
        split ; first by reflexivity.
        split ; first by reflexivity.
        destruct (CEP.find k old_connmap) as [[]|] ; done.
      * destruct Haft as [_ [_ [_ [_ [_ Hcm_sub_tm]]]]].
        specialize (Hcm_sub_tm k).
        destruct (CEP.find k old_tmap) ; first by reflexivity.
        destruct (CEP.find k old_connmap) as [[| |expr]|] ; try by done.
        destruct (type_of_expr expr old_tmap) as [[[| |] _]|] ; done.
  + rename ExpandBranch_fun_and_Sem_frag_stmt into IHs ;
    move /andP : Hss_inf => Hss_inf.
    specialize (IHs vm_for_tmap tmap Htm_inf Hvmtm_sub_tm s old_tmap old_scope)
               with (old_connmap := old_connmap) (old_vm := old_vm) (old_ct := old_ct) (1 := proj1 Hss_inf) (2 := Hsc_sub_tm).
    (* stmt_tmap *)
    generalize (stmt_submap vm_for_tmap s old_tmap old_scope Hsc_sub_tm) ; intro Htm_s.
    specialize (stmt_tmap_and_ExpandBranch_fun s old_scope old_connmap old_tmap vm_for_tmap)
               with (2 := Hsc_sub_tm) (3 := proj1 Hss_inf) ; intro Htm_eb.
    destruct (stmt_tmap (old_tmap, old_scope) s vm_for_tmap) as [[tm_tmap_s tm_scope_s]|] ; last by discriminate Hst.
    specialize (Htm_eb tm_tmap_s tm_scope_s) with (2 := Logic.eq_refl).
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
          intro k ; specialize (Htm_ss k) ; specialize (Htm_sub_vm k) ; specialize (Hvmtm_sub_tm k) ; specialize (Htm_inf k).
          destruct (CEP.find k tm_tmap_s) as [[ft ori]|] ; last by trivial.
          specialize Htm_ss with (1 := Logic.eq_refl).
          rewrite Htm_ss in Htm_sub_vm.
          destruct ori ; try (by contradiction Htm_sub_vm) ;
                destruct (CEP.find k vm_for_tmap) as [[gt|gt|gt|gt|gt]|] ;
                try (by contradiction Htm_sub_vm) ;
                subst ft ;
                rewrite Hvmtm_sub_tm // in Htm_inf.
    assert (Hold_tm_inf: tmap_has_fully_inferred_ground_types old_tmap).
          destruct Htm_s as [_ [Htm_s _]].
          intro k ; specialize (Htm_s k) ; specialize (Htm_tm_inf k).
          destruct (CEP.find k old_tmap) as [[ft ori]|] ; last by trivial.
          specialize Htm_s with (1 := Logic.eq_refl).
          rewrite Htm_s // in Htm_tm_inf.
    specialize Htm_eb with (1 := Hold_tm_inf).
    clear Hst.
    (* ExpandBranch_fun *)
    generalize (ExpandBranch_fun_submap s old_connmap old_scope) ; intro Heb_s.
    destruct (ExpandBranch_fun s old_connmap old_scope) as [[eb_connmap_s eb_scope_s]|] ; last by discriminate Heb.
    specialize Htm_eb with (1 := Logic.eq_refl) ; destruct Htm_eb as [Htm_eb _].
    subst eb_scope_s.
    specialize IHs with (1 := Logic.eq_refl).
    specialize (IHss eb_connmap_s).
    generalize (ExpandBranches_funs_submap ss eb_connmap_s tm_scope_s) ; intro Heb_ss.
    rewrite Heb in Heb_ss.
    destruct Heb_ss as [_ Heb_ss].
    specialize IHss with (1 := Heb).
    clear Heb.
    (* Sem_frag_stmts: *)
    rewrite Sem_frag_stmts_cat in Hsf.
    destruct Hsf as [vm_comp_s [ct_comp_s Hsf]].
    specialize IHs with (1 := proj1 Hsf) (2 := Haft).
    specialize IHss with (1 := proj2 Hsf) (2 := proj1 IHs).
    split ; first by apply IHss.
    destruct IHs as [_ IHs] ; destruct IHss as [_ IHss] ;
    destruct Heb_s as [_ Heb_s] ; destruct Htm_s as [Hscs_sub_tms [Holdtm_sub_tms _]].
    intro k ; specialize (IHs k) ; specialize (IHss k) ;
              specialize (Heb_s k) ; specialize (Heb_ss k) ;
              specialize (Hsc_sub_tm k).
    destruct (CEP.find k old_scope).
    - specialize (Heb_s _ Logic.eq_refl) ; specialize (Hsc_sub_tm _ Logic.eq_refl).
      rewrite Heb_s Hsc_sub_tm in IHs ; destruct IHs as [_ [_ IHs]].
      rewrite Heb_s (Heb_ss _ Heb_s) (Holdtm_sub_tms k _ Hsc_sub_tm) in IHss ; destruct IHss as [_ [_ IHss]].
      rewrite (Heb_ss _ Heb_s) Hsc_sub_tm.
      split ; first by reflexivity.
      split ; first by reflexivity.
      destruct (CEP.find k old_connmap) as [[| |expr_o]|],
               (CEP.find k eb_connmap_s) as [[| |expr_s]|],
               (CEP.find k eb_connmap) as [[| |expr_ss]|] ;
      done.
    - specialize (Hscs_sub_tms k).
      destruct (CEP.find k tm_scope_s).
      * destruct (CEP.find k old_tmap), (CEP.find k eb_scope) ; done.
      * specialize (Holdtm_sub_tms k).
        destruct (CEP.find k old_tmap).
        + rewrite (Holdtm_sub_tms _ Logic.eq_refl) -IHs // in IHss.
        + destruct (CEP.find k eb_scope) ; exact IHs.
* clear ExpandBranch_fun_and_Sem_frag_stmt.
  intros vm_for_tmap tmap Htm_inf Hvm_sub_tm.
  induction s as [|var ft|var reg|var mem|var1 var2|var expr|ref expr|ref|cond sst ssf] ; simpl ;
        intros old_tmap old_scope tm_tmap tm_scope old_connmap eb_connmap eb_scope old_vm old_ct vm_comp ct_comp Hs_inf Hsc_sub_tm Hst Htm_sub_vm Heb Hsf Haft.
  + (* Sskip *)
    injection Hst ; clear Hst ; intros ; subst tm_tmap tm_scope.
    injection Heb ; clear Heb ; intros ; subst eb_connmap eb_scope.
    split.
    - repeat (split ; first (destruct Haft as [Haft _] ; try by apply Haft) ;
                      last  (destruct Haft as [_ Haft])) ;
      intro k ; specialize (Haft k) ;
      try rewrite -(proj1 Hsf) ; try rewrite -(proj2 Hsf) ;
      by apply Haft.
    - intro k ; specialize (Hsc_sub_tm k).
      destruct (CEP.find k old_scope).
      * rewrite (Hsc_sub_tm _ Logic.eq_refl).
        split ; first by reflexivity.
        split ; first by reflexivity.
        destruct (CEP.find k old_connmap) as [[]|] ; done.
      * destruct Haft as [_ [_ [_ [_ [_ Hcm_sub_tm]]]]].
        specialize (Hcm_sub_tm k).
        destruct (CEP.find k old_tmap) ; first by reflexivity.
        destruct (CEP.find k old_connmap) as [[| |expr]|] ; try by done.
        destruct (type_of_expr expr old_tmap) as [[[| |] _]|] ; by contradiction Hcm_sub_tm.
  + (* Swire *)
    destruct ft as [gt| |] ; try by discriminate Hs_inf.
    generalize (fully_inferred_does_not_change gt var vm_for_tmap Hs_inf) ; intro Htm_s.
    simpl in Htm_s ; simpl in Hst.
    destruct (CEP.find var old_tmap) eqn: Hnot_find_var ; first by discriminate Hst.
    destruct (match CEP.find var vm_for_tmap with
        | Some (OutPort newgt) | Some (InPort newgt) |
          Some (Register newgt _ _ _) | Some (Wire newgt) |
          Some (Node newgt _) =>
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
              by apply Hneq_12small_large, Hkvar.
          - destruct (k == var) eqn: Hkvar.
            * destruct Hsf as [_ [_ [_ Hsf]]] ; specialize (Hsf 0 (ltn0Sn _)).
              rewrite add0n nat_of_binK -surjective_pairing in Hsf.
              by rewrite (CEP.Lemmas.find_add_eq Hkvar)
                      -(proj2 Hcomp) (elimT eqP Hkvar) Hsf //.
            * destruct Hsf as [_ [_ [Hsf _]]] ; specialize (Hsf k.1 k.2).
              rewrite (CEP.Lemmas.find_add_neq (elimT negP (negbT Hkvar)))
                      -(proj2 Hcomp) (surjective_pairing k) Hsf //.
              by apply Hneq_12small_large, Hkvar.
    split ; last first.
    - intro k.
      destruct (k == var) eqn: Hkvar.
      * rewrite (CEP.Lemmas.find_add_eq Hkvar) (CEP.Lemmas.find_add_eq Hkvar).
        move /eqP : Hkvar => Hkvar ; subst k.
        generalize (aft_scope_submap_tmap _ _ _ _ _ Haft var) ; intro Holdsc_sub_tm.
        rewrite Hnot_find_var in Holdsc_sub_tm.
        destruct (CEP.find var old_scope) ; first by discriminate (Holdsc_sub_tm _ Logic.eq_refl).
        rewrite Hnot_find_var.
        destruct Haft as [_ [_ [_ [_ [_ Hcm_sub_tm]]]]].
        specialize (Hcm_sub_tm var).
        rewrite Hnot_find_var in Hcm_sub_tm.
        destruct (CEP.find var old_connmap) as [[]|] ; try by done.
        destruct (type_of_expr h old_tmap) as [[[| |] _]|] ; by contradiction Hcm_sub_tm.
      * apply negbT in Hkvar ; move /negP : Hkvar => Hkvar.
        rewrite (CEP.Lemmas.find_add_neq Hkvar) (CEP.Lemmas.find_add_neq Hkvar).
        specialize (Hsc_sub_tm k).
        destruct (CEP.find k old_scope).
        + rewrite (Hsc_sub_tm _ Logic.eq_refl).
          split ; first by reflexivity.
          split ; first by reflexivity.
          destruct (CEP.find k old_connmap) as [[]|] ; done.
        + destruct Haft as [_ [_ [_ [_ [_ Hcm_sub_tm]]]]] ; specialize (Hcm_sub_tm k).
          destruct (CEP.find k old_tmap) ; first by reflexivity.
          destruct (CEP.find k old_connmap) as [[| |expr]|] ; try by done.
          destruct (type_of_expr expr old_tmap) as [[[| |] _]|] ; done.
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
      * by rewrite (CEP.Lemmas.find_add_eq Hkvar) //.
      * apply negbT in Hkvar ; move /negP : Hkvar => Hkvar.
        by rewrite (CEP.Lemmas.find_add_neq Hkvar) (CEP.Lemmas.find_add_neq Hkvar) //.
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
      destruct (k == var) eqn: Hkvar.
      * rewrite (CEP.Lemmas.find_add_eq Hkvar) (CEP.Lemmas.find_add_eq Hkvar) //.
      * apply negbT in Hkvar ; move /negP : Hkvar => Hkvar.
        rewrite (CEP.Lemmas.find_add_neq Hkvar) (CEP.Lemmas.find_add_neq Hkvar).
        destruct (PVM.find k old_connmap) as [[| |cm_expr]|] ; try by exact Haft.
        generalize (type_of_expr_submap cm_expr old_tmap (CEP.add var (Gtyp gt, HiF.Duplex) old_tmap)
                         (CEP.Lemmas.submap_none_add (Gtyp gt, HiF.Duplex) (CEP.Lemmas.submap_refl old_tmap) Hnot_find_var)) ;
              intro H.
        destruct (type_of_expr cm_expr old_tmap) as [[[cm_gt| |] cm_p]|] ; try by contradiction Haft.
        by rewrite H //.
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
    1,2: injection Heb ; clear Heb ; intros ; subst eb_connmap eb_scope.
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
         destruct (CEP.find var old_connmap) as [[]|] ; try (by discriminate Hvar_cm') ;
         by contradiction Hvar_cm.
    1-3: split ; last first.
    - 1,3,5: intro k.
      1-3: destruct (k == var) eqn: Hkvar.
      * 1,3,5: rewrite (CEP.Lemmas.find_add_eq Hkvar) (elimT eqP Hkvar) Hvar_sc Hvar_tm.
        1-3: split ; first by reflexivity.
        1-3: split ; first by reflexivity.
        1-3: destruct (CEP.find var old_connmap) as [[]|] ; by trivial.
      * 1-3: rewrite (CEP.Lemmas.find_add_neq (elimT negP (negbT Hkvar))).
        1-3: specialize (Hsc_sub_tm k).
        1-3: destruct (CEP.find k old_scope).
        + 1,3,5: rewrite (Hsc_sub_tm _ Logic.eq_refl).
          1-3: split ; first by reflexivity.
          1-3: split ; first by reflexivity.
          1-3: destruct (CEP.find k old_connmap) as [[]|] ; done.
        + 1-3: destruct Haft as [_ [_ [_ [_ [_ Hcm_sub_tm]]]]] ; specialize (Hcm_sub_tm k).
          1-3: destruct (CEP.find k old_tmap) ; first by reflexivity.
          1-3: destruct (CEP.find k old_connmap) as [[| |cm_expr]|] ; try by done.
          1-3: destruct (type_of_expr cm_expr old_tmap) as [[[| |] _]|] ; done.
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
        1-3: destruct (CEP.find var old_ct) as [[| |ct_expr]|] eqn: Hoct ;
                   try (by contradiction Hvar_ct) ;
                   by trivial.
      * 1-3: rewrite (CEP.Lemmas.find_add_neq (elimT negP (negbT Hkvar))) -(proj2 Hsf k) //.
    1-3: destruct Haft as [_ Haft] ; split.
    - 1,3,5: destruct Haft as [Haft _].
      1-3: intro k ; specialize (Haft k).
      1-3: by rewrite -(proj1 Hsf k) -(proj2 Hsf k) //.
    1-3: destruct Haft as [_ Haft] ; split.
    - 1,3,5: destruct Haft as [Haft _].
      1-3: intro k ; specialize (Haft k).
      1-3: by rewrite -(proj1 Hsf k) //.
    1-3: destruct Haft as [_ Haft] ; split.
    - 1,3,5: destruct Haft as [Haft _].
      1-3: intro k ; specialize (Haft k).
      1-3: by rewrite -(proj1 Hsf k) //.
    - 1-3: destruct Haft as [_ Haft].
      1-3: intro k ; specialize (Haft k).
      1-3: destruct (k == var) eqn: Hkvar.
      * 1,3,5: rewrite (CEP.Lemmas.find_add_eq Hkvar).
        1-3: move /eqP : Hkvar => Hkvar ; subst k.
        1-3: rewrite Hexpr_tm Hvar_tm //.
      * 1-3: rewrite (CEP.Lemmas.find_add_neq (elimT negP (negbT Hkvar))) //.
  + (* Sinvalid should be similar to Sfcnct but simpler *)
    admit.
  + (* Swhen *)
    move /andP : Hs_inf => [/andP [_ Hsst_inf] Hssf_inf].
    rename ExpandBranches_funs_and_Sem_frag_stmts into IHsst.
    specialize (IHsst vm_for_tmap tmap Htm_inf Hvm_sub_tm).
    generalize (IHsst ssf) ; intro IHssf ; specialize IHssf with (1 := Hssf_inf).
    specialize (IHsst sst old_tmap old_scope) with (old_connmap := old_connmap) (old_vm := old_vm) (old_ct := old_ct)
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
    generalize (ExpandBranches_funs_submap sst old_connmap old_scope) ; intro Heb_t.
    destruct (ExpandBranches_funs sst old_connmap old_scope) as [[eb_connmap_t eb_scope_t]|] ; last by discriminate Heb.
    specialize IHsst with (1 := Logic.eq_refl).
    specialize (IHssf old_connmap).
    generalize (ExpandBranches_funs_submap ssf old_connmap old_scope) ; intro Heb_f.
    destruct (ExpandBranches_funs ssf old_connmap old_scope) as [[eb_connmap_f eb_scope_f]|] ; last by discriminate Heb.
    specialize IHssf with (1 := Logic.eq_refl).
    injection Heb ; clear Heb ; intros ; subst eb_connmap eb_scope.
    (* Sem_frag_stmts: *)
    apply Sem_frag_stmts_cat in Hsf.
    destruct Hsf as [vm_comp_t [ct_comp_t Hsf]].
    specialize IHsst with (1 := proj1 Hsf) (2 := Haft).
    specialize IHssf with (1 := proj2 Hsf).
    assert (Htm_tm_sub_tm : CEP.submap tm_tmap tmap).
          apply scope_vm_submap_tmap with (vm := vm_for_tmap) ; try by assumption.
    assert (Htmt_sub_tm: CEP.submap tm_tmap_t tmap) by (apply (CEP.Lemmas.submap_trans (proj1 (proj2 Htm_f)) Htm_tm_sub_tm)).
    assert (Holdtm_sub_tm: CEP.submap old_tmap tmap) by (apply (CEP.Lemmas.submap_trans (proj1 (proj2 Htm_t)) Htmt_sub_tm)).
    assert (Hsf_t : ct_sub_vm old_ct old_vm tmap).
          destruct Haft as [_ [_ [Haft _]]].
          intro k ; specialize (Haft k).
          destruct (CEP.find k old_ct) as [[| |expr]|] ; try by exact Haft.
          destruct (CEP.find k old_vm) as [[gt|gt|gt|gt|gt]|] ; try by exact Haft.
          1-3: generalize (type_of_expr_submap expr old_tmap tmap Holdtm_sub_tm) ; intro.
          1-3: destruct (type_of_expr expr old_tmap) as [[[gt_expr| |] ]|] ; try by contradiction Haft.
          1-3: by rewrite H //.
    apply (Sem_frag_stmts_component) with (2 := proj1 Hsf) in Hsf_t.
    assert (Hsf_f: ct_sub_vm ct_comp_t vm_comp_t tmap).
          destruct IHsst as [[_ [_ [IHsst _]]] _].
          intro k ; specialize (IHsst k).
          destruct (CEP.find k ct_comp_t) as [[| |expr]|] ; try by exact IHsst.
          destruct (CEP.find k vm_comp_t) as [[gt|gt|gt|gt|gt]|] ; try by exact IHsst.
          1-3: generalize (type_of_expr_submap expr tm_tmap_t tmap Htmt_sub_tm) ; intro.
          1-3: destruct (type_of_expr expr tm_tmap_t) as [[[gt_expr| |] ]|] ; try by contradiction IHsst.
          1-3: by rewrite H //.
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
          - destruct Haft as [Haft _], Hsf_t as [_ [_ Hsf_t]].
            intro k ; specialize (Haft k) ; specialize (Hsf_t k).
            destruct (CEP.find k old_connmap) ; last by (destruct (CEP.find k ct_comp_t) ; done).
            destruct (CEP.find k old_ct) ; last by discriminate Haft.
            by rewrite (Hsf_t _ Logic.eq_refl) //.
          destruct Haft as [_ Haft] ; split.
          - by apply IHsst.
          destruct Haft as [_ Haft] ; split.
          - by apply IHsst.
          destruct Haft as [_ Haft] ; split.
          - destruct Haft as [Haft _].
            generalize (proj1 Hsf) ; intro Hvm_comp_t ; apply Sem_frag_stmts_compatible in Hvm_comp_t.
            destruct Hvm_comp_t as [Hvm_comp_t _].
            intro k ; specialize (Haft k) ; specialize (Hvm_comp_t k).
            destruct (CEP.find k old_scope) as [[ft ori]|] ; last by trivial.
            destruct ori, (PVM.find k old_vm) as [[gt|gt|gt|gt|gt]|] ;
                  try (by contradiction Haft) ;
                  subst ft ;
                  specialize Hvm_comp_t with (1 := Logic.eq_refl) ;
                  rewrite Hvm_comp_t //.
          - destruct Haft as [_ Haft].
            intro k ; specialize (Haft k).
            destruct Htm_t as [_ [Htm_t _]].
            destruct (CEP.find k old_connmap) as [[| |expr]|] ; try by exact Haft.
            * 3: generalize (type_of_expr_submap expr old_tmap tm_tmap_t Htm_t) ; intro ;
              destruct (type_of_expr expr old_tmap) as [[[gt_expr| |] p]|] ; try (by contradiction Haft) ;
              rewrite H.
            1-3: specialize (Htm_t k).
            1-3: destruct (CEP.find k old_tmap) as [[ft [| | | |]]|] ;
                         try (by contradiction Haft) ;
                 rewrite (Htm_t _ Logic.eq_refl) //.
    specialize (IHssf Haft_f) ; clear Haft_f.
    split ; last first.
    - destruct IHsst as [_ IHsst], IHssf as [_ IHssf].
      intro k ; specialize (IHsst k) ; specialize (IHssf k).
      rewrite /combine_when_connections CEP.Lemmas.map2_1bis //.
      destruct Heb_t as [_ Heb_t] ; specialize (Heb_t k).
      destruct Heb_f as [_ Heb_f] ; specialize (Heb_f k).
      specialize (Hsc_sub_tm k).
      destruct (CEP.find k old_scope).
      * specialize (Hsc_sub_tm _ Logic.eq_refl).
        rewrite Hsc_sub_tm.
        split ; first by reflexivity.
        split ; first by reflexivity.
        rewrite (Heb_t _ Logic.eq_refl) Hsc_sub_tm in IHsst ; destruct IHsst as [_ [_ IHsst]].
        rewrite (Heb_f _ Logic.eq_refl) (proj1 (proj2 Htm_t) k _ Hsc_sub_tm) in IHssf ; destruct IHssf as [_ [_ IHssf]].
        destruct (CEP.find k old_connmap) as [[| |expr_o]|],
                 (CEP.find k eb_connmap_t) as [[| |expr_t]|],
                 (CEP.find k eb_connmap_f) as [[| |expr_f]|] ;
        try done ;
        destruct (expr_t == expr_f) ; done.
      * destruct (CEP.find k eb_scope_t).
        + destruct (CEP.find k old_tmap) ; first by contradiction IHsst.
          by exact IHsst.
        + destruct Htm_t as [_ [Htm_t _]] ; specialize (Htm_t k).
          destruct (CEP.find k old_tmap) ; last by exact IHsst.
          rewrite (Htm_t _ Logic.eq_refl) in IHssf.
          destruct (CEP.find k eb_scope_f) ; first by contradiction IHssf.
          rewrite -IHsst -IHssf.
          destruct (CEP.find k old_connmap) as [[| |expr]|] ; try done.
          by rewrite eq_refl //.
    destruct IHsst as [IHsst _], IHssf as [IHssf _] ; split.
    - destruct IHsst as [IHsst _], IHssf as [IHssf _].
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
      1: rewrite IHsst IHssf //.
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
    destruct Haft as [_ Haft], IHsst as [_ IHsst], IHssf as [_ IHssf] ; split.
    - destruct IHsst as [IHsst _], IHssf as [IHssf _], Hsf_t as [_ [_ Hsf_t]], Hsf_f as [_ [_ Hsf_f]].
      intro k ; specialize (IHsst k) ; specialize (IHssf k) ; specialize (Hsf_t k) ; specialize (Hsf_f k).
      rewrite /combine_when_connections CEP.Lemmas.map2_1bis //.
      destruct (CEP.find k eb_connmap_t) as [[| |expr_t]|],
               (CEP.find k eb_connmap_f) as [[| |expr_f]|],
               (CEP.find k ct_comp_t), (CEP.find k ct_comp) ; try (by done) ;
               try specialize Hsf_f with (1 := Logic.eq_refl) ; try (by discriminate Hsf_f).
    destruct Haft as [_ Haft], IHsst as [_ IHsst], IHssf as [_ IHssf] ; split.
    - by apply IHssf.
    destruct Haft as [_ Haft], IHsst as [_ IHsst], IHssf as [_ IHssf] ; split.
    - by apply IHssf.
    destruct Haft as [_ Haft], IHsst as [_ IHsst], IHssf as [_ IHssf] ; split.
    - destruct Haft as [Haft _], IHssf as [IHssf _].
      destruct Heb_f as [_ Heb_f].
      intro ; specialize (Heb_f k) ; specialize (IHssf k).
      destruct (CEP.find k old_scope) as [[ft ori]|] ; last by trivial.
      specialize Heb_f with (1 := Logic.eq_refl) ; rewrite Heb_f // in IHssf.
    - destruct Haft as [_ Haft], IHsst as [_ IHsst], IHssf as [_ IHssf].
      intro k ; specialize (Haft k) ; specialize (IHsst k) ; specialize (IHssf k).
      rewrite /combine_when_connections CEP.Lemmas.map2_1bis //.
      destruct (CEP.find k eb_connmap_t) as [[| |expr_t]|] eqn: Hfind_eb_t,
               (CEP.find k eb_connmap_f) as [[| |expr_f]|] eqn: Hfind_eb_f ;
            try (by done) ;
            try (by destruct Htm_f as [_ [Htm_f _]] ; specialize (Htm_f k) ;
                    destruct (CEP.find k tm_tmap_t) as [[ft [| | | |]]|] ;
                          try (by contradiction IHsst) ;
                    rewrite (Htm_f _ Logic.eq_refl) //).
      2: destruct (expr_t == expr_f) ;
         last (simpl ;
               generalize (type_of_expr_submap cond old_tmap tm_tmap (CEP.Lemmas.submap_trans (proj1 (proj2 Htm_t)) (proj1 (proj2 Htm_f)))) ;
               intro H ;
               rewrite Hcond_tm in H ;
               rewrite H ; clear H).
      1-4: generalize (type_of_expr_submap expr_t tm_tmap_t tm_tmap (proj1 (proj2 Htm_f))) ;
           intro H ;
           destruct (type_of_expr expr_t tm_tmap_t) as [[[gt_expr_t| |] ]|] ;
                 try (by contradiction IHsst) ;
           rewrite H ; clear H.
      1-4: destruct Htm_f as [_ [Htm_f _]] ; specialize (Htm_f k).
      1-4: destruct (CEP.find k tm_tmap_t) as [[[gt_ref| |] [| | | |]]|] ;
           try (by contradiction IHsst) ;
           specialize (Htm_f _ Logic.eq_refl) ;
           rewrite Htm_f // ;
           rewrite Htm_f // in IHssf.
      1-2: specialize (Htm_inf k) ;
           apply (scope_vm_submap_tmap tm_tmap vm_for_tmap tmap Htm_sub_vm Hvm_sub_tm) in Htm_f ;
           rewrite Htm_f in Htm_inf.
      1-2: destruct (type_of_expr expr_f tm_tmap) as [[[gt_expr_f| |] ]|] ;
                 try (by contradiction IHssf) ;
           rewrite /ftype_mux /sval /proj2_sig /ftype_mux' /fgtyp_mux.
      1-2: destruct gt_ref, gt_expr_t, gt_expr_f ; done.
Admitted.

Lemma Sem_frag_stmts_component_Equal :
forall (ss : HiFP.hfstmt_seq) (vm_old1 vm_old2 : CEP.t vertex_type) (ct_old1 ct_old2 : CEP.t def_expr) (vm_new1 vm_new2 : CEP.t vertex_type) (ct_new : CEP.t def_expr) (tmap1 tmap2 : CEP.t (ftype * HiF.forient)),
        ct_sub_vm ct_old1 vm_old1 tmap1
    ->
        ct_sub_vm ct_old2 vm_old2 tmap2
    ->
        CEP.Equal vm_old1 vm_old2
    ->
        CEP.Equal vm_new1 vm_new2
    ->
        CEP.Equal tmap1 tmap2
    ->
        Sem_frag_stmts vm_old1 ct_old1 (component_stmts_of ss) vm_new1 ct_new tmap1
    ->
        Sem_frag_stmts vm_old2 ct_old2 (component_stmts_of ss) vm_new2 (extend_map_with ct_old2 ct_new) tmap2
with Sem_frag_stmt_component_Equal :
forall (s : HiFP.hfstmt) (vm_old1 vm_old2 : CEP.t vertex_type) (ct_old1 ct_old2 : CEP.t def_expr) (vm_new1 vm_new2 : CEP.t vertex_type) (ct_new : CEP.t def_expr) (tmap1 tmap2 : CEP.t (ftype * HiF.forient)),
        ct_sub_vm ct_old1 vm_old1 tmap1
    ->
        ct_sub_vm ct_old2 vm_old2 tmap2
    ->
        CEP.Equal vm_old1 vm_old2
    ->
        CEP.Equal vm_new1 vm_new2
    ->
        CEP.Equal tmap1 tmap2
    ->
        Sem_frag_stmts vm_old1 ct_old1 (component_stmt_of s) vm_new1 ct_new tmap1
    ->
        Sem_frag_stmts vm_old2 ct_old2 (component_stmt_of s) vm_new2 (extend_map_with ct_old2 ct_new) tmap2.
Proof.
* clear Sem_frag_stmts_component_Equal.
  induction ss as [|s ss] ; simpl ; intros.
  + split.
    - apply (CEP.Lemmas.Equal_trans (CEP.Lemmas.Equal_sym H1)).
      exact (CEP.Lemmas.Equal_trans (proj1 H4) H2).
    - intro ; rewrite /extend_map_with CEP.Lemmas.map2_1bis //.
      specialize (H0 y).
      destruct (CEP.find y ct_old2) ; first by reflexivity.
      specialize (H y) ; rewrite (H1 y) (proj2 H4 y) in H.
      destruct (CEP.find y ct_new) as [[]|] ; last (by reflexivity) ;
      destruct (CEP.find y vm_old2) as [[]|] ; done.
  + rename Sem_frag_stmt_component_Equal into IHs ; specialize (IHs s).
    apply Sem_frag_stmts_cat.
    apply Sem_frag_stmts_cat in H4.
    destruct H4 as [vm_temp [ct_temp [H4 H5]]].
    exists vm_temp, (extend_map_with ct_old2 ct_temp).
    specialize (IHs vm_old1 vm_old2 ct_old1 ct_old2 vm_temp vm_temp ct_temp tmap1 tmap2
                    H H0 H1 (CEP.Lemmas.Equal_refl _) H3 H4).
    split.
    * by apply IHs.
    * generalize (Sem_frag_stmt_component s vm_old1 ct_old1 vm_temp ct_temp tmap1 H H4) ; intro Hold1_sub_temp.
      generalize (Sem_frag_stmt_component s vm_old2 ct_old2 vm_temp (extend_map_with ct_old2 ct_temp) tmap2 H0 IHs) ; intro Hold2_sub_temp.
      specialize IHss with (1 := proj1 Hold1_sub_temp) (2 := proj1 Hold2_sub_temp) (3 := CEP.Lemmas.Equal_refl vm_temp) (4 := H2) (5 := H3) (6 := H5).
      generalize (Sem_frag_stmts_component ss vm_temp ct_temp vm_new1 ct_new tmap1 (proj1 Hold1_sub_temp) H5) ; intro Htemp_sub_new1.
      generalize (extend_map_with_submap ct_old2 ct_temp ct_new (proj2 (proj2 Htemp_sub_new1))) ; intro.
      apply Sem_frag_stmts_Equal with (vm_old1 := vm_temp) (ct_old1 := extend_map_with ct_old2 ct_temp)
                                      (vm_new1 := vm_new2) (ct_new1 := extend_map_with (extend_map_with ct_old2 ct_temp) ct_new)
                                      (tmap1 := tmap2) ;
            try assumption ; apply CEP.Lemmas.Equal_refl.
* clear Sem_frag_stmt_component_Equal.
  destruct s as [|var ft|var reg|var mem|var1 var2|var expr|ref expr|ref|cond sst ssf] ; intros.
  + (* Sskip *)
    simpl ; split ;
        first by apply (CEP.Lemmas.Equal_trans (CEP.Lemmas.Equal_sym H1)),
                       (CEP.Lemmas.Equal_trans (proj1 H4)), H2.
    simpl in H4.
    intro y ; rewrite CEP.Lemmas.map2_1bis // -(proj2 H4).
    specialize (H0 y).
    destruct (CEP.find y ct_old2) ; first by reflexivity.
    rewrite -H1 in H0.
    specialize (H y).
    destruct (CEP.find y ct_old1) as [[]|], (CEP.find y vm_old1) as [[]|] ;
          done.
  + (* Swire *)
    simpl ; simpl in H4.
    destruct H4 as [vm' [ct' [H4 [H5 H6]]]].
    exists vm_new2, (extend_map_with ct_old2 ct_new).
    split ; last by split ; apply CEP.Lemmas.Equal_refl.
    apply (CEP.Lemmas.Equal_trans) with (2 := H2) in H5.
    clear H2 vm_new1.
    specialize (H3 var).
    destruct (CEP.find var tmap1) as [[newft [| | | |]]|] ; try by contradiction H4.
    rewrite -H3 ; clear H3.
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
      specialize (H (v0, n0)) ;
      destruct (CEP.find (v0, n0) ct_old1) as [[]|] ;
      by rewrite H1 // in H.
    - destruct H4 as [H7 [_ [_ H4]]].
      intros ; specialize (H4 n0 H2) ; specialize (H7 n0).
      rewrite -(list_rhs_type_p_size newft) in H2.
      move /ltP : H2 => H2.
      generalize (proj2 (List.nth_error_Some (list_rhs_type_p newft) n0) H2) ; intro.
      destruct (List.nth_error (list_rhs_type_p newft) n0) ; last by contradiction H3.
      rewrite H1 in H7.
      specialize (H0 (var.1, bin_of_nat (n0 + var.2))).
      rewrite (proj1 H7) in H0.
      destruct (CEP.find (var.1, bin_of_nat (n0 + var.2)) ct_old2) as [[]|] eqn: Hct2 ;
            try by contradiction H0.
      by rewrite CEP.Lemmas.map2_1bis // -H6 H4 Hct2 //.
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
    simpl in H4.
    intro y ; rewrite CEP.Lemmas.map2_1bis // -(proj2 H4).
    specialize (H0 y).
    destruct (CEP.find y ct_old2) ; first by reflexivity.
    rewrite -H1 in H0.
    specialize (H y).
    destruct (CEP.find y ct_old1) as [[]|], (CEP.find y vm_old1) as [[]|] ;
          done.
  + (* Sinvalid, similar to Sskip *)
    simpl ; split ;
        first by apply (CEP.Lemmas.Equal_trans (CEP.Lemmas.Equal_sym H1)),
                       (CEP.Lemmas.Equal_trans (proj1 H4)), H2.
    simpl in H4.
    intro y ; rewrite CEP.Lemmas.map2_1bis // -(proj2 H4).
    specialize (H0 y).
    destruct (CEP.find y ct_old2) ; first by reflexivity.
    rewrite -H1 in H0.
    specialize (H y).
    destruct (CEP.find y ct_old1) as [[]|], (CEP.find y vm_old1) as [[]|] ;
          done.
  + (* Swhen *)
    rename Sem_frag_stmts_component_Equal into IHss.
    simpl component_stmt_of in H4 ; simpl component_stmt_of.
    apply Sem_frag_stmts_cat in H4 ; apply Sem_frag_stmts_cat.
    destruct H4 as [vm_temp [ct_temp [H4 H5]]].
    exists vm_temp, (extend_map_with ct_old2 ct_temp).
    split.
    - by apply (IHss sst vm_old1 vm_old2 ct_old1 ct_old2 vm_temp vm_temp ct_temp tmap1 tmap2
                                              H H0 H1 (CEP.Lemmas.Equal_refl _) H3 H4).
    - generalize (Sem_frag_stmts_component sst vm_old1 ct_old1 vm_temp ct_temp tmap1 H H4) ; intro.
      generalize (Sem_frag_stmts_component ssf vm_temp ct_temp vm_new1 ct_new tmap1 (proj1 H6) H5) ; intro.
      generalize (extend_map_with_submap ct_old2 ct_temp ct_new (proj2 (proj2 H7))) ; intro.
      apply Sem_frag_stmts_Equal with (vm_old1 := vm_temp) (ct_old1 := extend_map_with ct_old2 ct_temp)
                                      (vm_new1 := vm_new2) (ct_new1 := extend_map_with (extend_map_with ct_old2 ct_temp) ct_new)
                                      (tmap1 := tmap2) ;
            try assumption ; try apply CEP.Lemmas.Equal_refl.
      apply IHss with (vm_old1 := vm_temp) (ct_old1 := ct_temp)
                      (vm_new1 := vm_new1)
                      (tmap1 := tmap1) ;
            try assumption ; try apply CEP.Lemmas.Equal_refl.
      - by apply H6.
      - intro v.
        rewrite /extend_map_with CEP.Lemmas.map2_1bis //.
        specialize (H0 v) ; specialize (H1 v).
        destruct H6 as [H6' [H6 _]] ; specialize (H6 v) ; rewrite H1 in H6.
        (*specialize (H8 v) ; rewrite /extend_map_with CEP.Lemmas.map2_1bis // CEP.Lemmas.map2_1bis // CEP.Lemmas.map2_1bis // in H8.*)
        destruct (CEP.find v ct_old2) as [[| |expr2]|] eqn: Hct2, (CEP.find v vm_old2) eqn: Hvm2 ;
              try rewrite (H6 _ Logic.eq_refl) ;
              try done.
        - specialize (H6' v) ; rewrite (H6 _ Logic.eq_refl) in H6'.
          destruct (PVM.find v ct_temp) as [[]|], v0 ; done.
        - specialize (H6' v).
          destruct (CEP.find v ct_temp) as [[| |expr]|] ; try by exact H6'.
          destruct (CEP.find v vm_temp) as [[gt|gt|gt|gt|gt]|] ; try (by exact H6') ;
          generalize (type_of_expr_submap expr tmap1 tmap2 (CEP.Lemmas.Equal_submap H3)) ; intro ;
          destruct (type_of_expr expr tmap1) as [[[gt_expr| |] Hgt_expr_inf]|] ; try (by contradiction H6') ;
          rewrite H9 //.
Admitted.

Lemma ExpandWhen_correct_inductive :
forall (vm_for_tmap : CEP.t vertex_type) (tmap : CEP.t (ftype * HiF.forient)),
        tmap_has_fully_inferred_ground_types tmap (* perhaps not needed, as it may be included in all_fit_together *)
    ->
        vm_sub_tmap vm_for_tmap tmap
    ->
        forall s : HiFP.hfstmt,
                stmt_has_fully_inferred_ground_types s
            ->
                forall (old_scope : CEP.t (ftype * HiF.forient)) (old_connmap : CEP.t def_expr)
                       (old_ct : CEP.t def_expr) (old_vm : CEP.t vertex_type) (old_tmap: CEP.t (ftype * HiF.forient))
                       (tm_tmap tm_scope : CEP.t (ftype * HiF.forient))
                       (eb_connmap : CEP.t def_expr)
                       (sf_vm : CEP.t vertex_type) (sf_ct : CEP.t def_expr),
                            all_fit_together old_scope old_connmap old_ct old_vm old_tmap
                        ->
                            CEP.submap old_connmap old_ct
                        ->
                            stmt_tmap (old_tmap, old_scope) s vm_for_tmap = Some (tm_tmap, tm_scope)
                        ->
                            ExpandBranch_fun s old_connmap old_scope =
                            Some (eb_connmap, tm_scope)
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
                            /\
                                CEP.submap sf_ct (extend_map_with eb_connmap old_ct)
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
                       (eb_connmap : CEP.t def_expr)
                       (sf_vm : CEP.t vertex_type) (sf_ct : CEP.t def_expr),
                            all_fit_together old_scope old_connmap old_ct old_vm old_tmap
                        ->
                            CEP.submap old_connmap old_ct
                        ->
                            stmts_tmap (old_tmap, old_scope) ss vm_for_tmap = Some (tm_tmap, tm_scope)
                        ->
                            ExpandBranches_funs ss old_connmap old_scope =
                            Some (eb_connmap, tm_scope)
                        ->
                            Sem_frag_stmts old_vm old_ct (Qcat (component_stmts_of ss)
                                           (convert_to_connect_stmts eb_connmap))
                                           sf_vm sf_ct tmap
                        ->
                            scope_sub_vm tm_tmap vm_for_tmap (* perhaps not needed here *)
                        ->
                                Sem_frag_stmts old_vm old_ct ss sf_vm sf_ct tmap
                            /\
                                all_fit_together tm_scope eb_connmap sf_ct sf_vm tm_tmap
                            /\
                                CEP.submap sf_ct (extend_map_with eb_connmap old_ct).
Proof.
* clear ExpandWhen_correct_inductive.
  intros vm_for_tmap tmap Htm_inf Hvm_tm s.
  generalize (ExpandWhens_correct_simple vm_for_tmap tmap Htm_inf Hvm_tm s) ; intro Hsimple.
  induction s as [| | | | | | | |cond sst ssf]; try (by apply Hsimple).
  (* only Swhen is left *)
  clear Hsimple.
  simpl.
  intros Hs_inf old_scope old_connmap old_ct old_vm old_tmap tm_tmap tm_scope eb_connmap sf_vm sf_ct
         Haft Hcm_submap_ct Hst Heb Hsf Htm_sub_vm.
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
  generalize (ExpandWhens_correct_inductive ssf Hssf_inf old_scope old_connmap) ; intro IHssf.
  specialize (ExpandWhens_correct_inductive sst Hsst_inf old_scope old_connmap old_ct old_vm old_tmap)
             with (1 := Haft) (2 := Hcm_submap_ct) ; rename ExpandWhens_correct_inductive into IHsst.
  (* work further on the induction hypotheses *)
  destruct (type_of_expr cond old_scope) as [[[[[|[|]]| | | | | |]| |] p_cond]|] eqn: Htyp_cond ; try by discriminate Heb.
  (* stmts_tmap: *)
  generalize (aft_scope_submap_tmap _ _ _ _ _ Haft) ; intro Hsc_tm.
  generalize (stmts_submap vm_for_tmap sst old_tmap old_scope Hsc_tm) ; intro Hst_sub_t.
  specialize (stmts_tmap_and_ExpandBranches_funs sst old_scope old_connmap old_tmap vm_for_tmap)
        with (2 := Hsc_tm) (3 := Hsst_inf) ; intro Htm_eb_t.
  specialize (ExpandBranches_funs_and_Sem_frag_stmts vm_for_tmap tmap Htm_inf Hvm_tm sst old_tmap old_scope)
              with (old_connmap := old_connmap) (old_vm := old_vm) (old_ct := old_ct)
              (1 := Hsst_inf) (2 := Hsc_tm) ; intro Haft_comp_t.
  specialize (stmts_tmap_and_Sem_frag_stmts vm_for_tmap tmap Htm_inf Hvm_tm (component_stmts_of sst) old_vm old_ct old_tmap old_scope)
             with  (2 := (components_preserve_fully_inferred _ Hsst_inf)) ; intro Hsdu_t.
  specialize (stmts_tmap_components vm_for_tmap sst old_tmap old_scope old_scope
              (aft_scope_submap_tmap _ _ _ _ _ Haft) (aft_scope_submap_tmap _ _ _ _ _ Haft) (CEP.Lemmas.submap_refl _)) ; intro Htm_comp_t.
  destruct (stmts_tmap (old_tmap, old_scope) sst vm_for_tmap) as [[tm_tmap_t tm_scope_t]|] eqn: Hst_t ; last by discriminate Hst.
  specialize IHsst with (1 := Logic.eq_refl).
  specialize Htm_eb_t with (2 := Logic.eq_refl).
  specialize Haft_comp_t with (1 := Logic.eq_refl).
  destruct (stmts_tmap (old_tmap, old_scope) (component_stmts_of sst) vm_for_tmap) as [[tm_tmap_t' tm_scope_comp_t]|] ;
        last by contradiction Htm_comp_t.
  destruct Htm_comp_t as [Htm_comp' Htm_comp] ; subst tm_tmap_t'.
  specialize Hsdu_t with (1 := Logic.eq_refl).
  specialize IHssf with (old_tmap := tm_tmap_t).
  generalize (stmts_submap vm_for_tmap ssf tm_tmap_t old_scope (CEP.Lemmas.submap_trans (proj2 (proj2 Hst_sub_t)) (proj1 Hst_sub_t))) ; intro Hst_f.
  specialize (stmts_tmap_and_ExpandBranches_funs ssf old_scope old_connmap tm_tmap_t vm_for_tmap)
        with (2 := CEP.Lemmas.submap_trans (proj2 (proj2 Hst_sub_t)) (proj1 Hst_sub_t)) (3 := Hssf_inf) ; intro Htm_eb_f.
  specialize (ExpandBranches_funs_and_Sem_frag_stmts vm_for_tmap tmap Htm_inf Hvm_tm ssf tm_tmap_t old_scope)
              with (old_connmap := old_connmap)
              (1 := Hssf_inf) (2 := CEP.Lemmas.submap_trans (proj2 (proj2 Hst_sub_t)) (proj1 Hst_sub_t)) ;
              intro Haft_comp_f.
  specialize (stmts_tmap_and_Sem_frag_stmts vm_for_tmap tmap Htm_inf Hvm_tm (component_stmts_of ssf)) with (old_tmap := tm_tmap_t) (old_scope := old_scope); intro Hsdu_f.
  specialize (stmts_tmap_components vm_for_tmap ssf tm_tmap_t old_scope old_scope
              (CEP.Lemmas.submap_trans Hsc_tm (proj1 (proj2 Hst_sub_t))) (CEP.Lemmas.submap_trans Hsc_tm (proj1 (proj2 Hst_sub_t)))
              (CEP.Lemmas.submap_refl _)) ; intro Htm_comp_f.
  destruct (stmts_tmap (tm_tmap_t, old_scope) ssf vm_for_tmap) as [[tm_tmap_f tm_scope_f]|] ; last by discriminate Hst.
  specialize IHssf with (3 := Logic.eq_refl).
  specialize Htm_eb_f with (2 := Logic.eq_refl).
  injection Hst ; clear Hst ; intros ; subst tm_tmap_f tm_scope.
  specialize Haft_comp_f with (1 := Logic.eq_refl) (2 := Htm_sub_vm).
  destruct (stmts_tmap (tm_tmap_t, old_scope) (component_stmts_of ssf) vm_for_tmap) as [[tm_tmap' tm_scope_comp_f]|] ;
        last by contradiction Htm_comp_f.
  destruct Htm_comp_f as [Htm_comp_f' Htm_comp_f] ; subst tm_tmap'.
  specialize Hsdu_f with (1 := Logic.eq_refl) (2 := (components_preserve_fully_inferred _ Hssf_inf)).
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
  generalize (ExpandBranches_funs_submap sst old_connmap old_scope) ; intro Heb_t.
  destruct (ExpandBranches_funs sst old_connmap old_scope) as [[eb_connmap_t eb_scope_t]|] ; last by discriminate Heb.
  specialize Htm_eb_t with (1 := Logic.eq_refl).
  specialize Haft_comp_t with (2 := Logic.eq_refl).
  destruct Htm_eb_t as [Htm_eb_t' Htm_eb_t] ; subst eb_scope_t.
  specialize IHsst with (1 := Logic.eq_refl).
  generalize (ExpandBranches_funs_submap ssf old_connmap old_scope) ; intro Heb_f.
  destruct (ExpandBranches_funs ssf old_connmap old_scope) as [[eb_connmap_f eb_scope_f]|] ; last by discriminate Heb.
  specialize Htm_eb_f with (1 := Logic.eq_refl).
  specialize Haft_comp_f with (1 := Logic.eq_refl).
  destruct Htm_eb_f as [Htm_eb_f' Htm_eb_f] ; subst eb_scope_f.
  specialize IHssf with (3 := Logic.eq_refl).
  injection Heb ; clear Heb ; intro ; subst eb_connmap.
  (* Sem_frag_stmts: *)
  apply Sem_frag_stmts_cat in Hsf.
  destruct Hsf as [vm_comp [ct_comp [Hsf_comp Hsf_conn]]].
  apply Sem_frag_stmts_cat in Hsf_comp.
  destruct Hsf_comp as [vm_comp_t [ct_comp_t [Hsf_comp_t Hsf_comp_f]]].
  assert (Htmt_sub_tm: CEP.submap tm_tmap_t tmap) by (apply (CEP.Lemmas.submap_trans (proj1 (proj2 Hst_f)) Htm_tm_sub_tm)).
  assert (Holdtm_sub_tm: CEP.submap old_tmap tmap) by (apply (CEP.Lemmas.submap_trans (proj1 (proj2 Hst_sub_t)) Htmt_sub_tm)).
  assert (Hct_sub_vm_tmap: ct_sub_vm old_ct old_vm tmap).
        destruct Haft as [_ [_ [Hct_sub_vm _]]].
        intro k ; specialize (Hct_sub_vm k).
        destruct (CEP.find k old_ct) as [[| |expr]|] ; try by exact Hct_sub_vm.
        destruct (CEP.find k old_vm) as [[gt|gt|gt|gt|gt]|] ; try by exact Hct_sub_vm.
        1-3: generalize (type_of_expr_submap expr old_tmap tmap Holdtm_sub_tm) ; intro.
        1-3: destruct (type_of_expr expr old_tmap) as [[gt_expr p]|] ; last by contradiction Hct_sub_vm.
        1-3: rewrite H //.
  specialize Sem_frag_stmts_component with (1 := Hct_sub_vm_tmap) (2 := Hsf_comp_t) ; intro Hsf_comp_sub_t.
  assert (Hstmt_sub_vm: scope_sub_vm tm_tmap_t vm_for_tmap).
        destruct Hst_f as [_ [Hst_f _]].
        intro k ; specialize (Hst_f k) ; specialize (Htm_sub_vm k).
        destruct (CEP.find k tm_tmap_t) as [[ft ori]|] ; last by trivial.
        specialize Hst_f with (1 := Logic.eq_refl).
        rewrite Hst_f // in Htm_sub_vm.
  specialize IHsst with (2 := Hstmt_sub_vm).
  specialize Haft_comp_t with (1 := Hstmt_sub_vm) (2 := Hsf_comp_t) (3 := Haft) ; clear Hstmt_sub_vm.
  assert (Hsdu_t_precondition: all_fit_together old_scope old_ct old_ct old_vm old_tmap).
        split.
        - destruct Haft as [_ [_ [Hct_sub_vm [_ [Hsc_sub_vm _]]]]].
          intro k ; specialize (Hct_sub_vm k) ; specialize (Hsc_sub_vm k).
          destruct (CEP.find k old_scope) as [[ft_tgt [| | | |]]|],
                   (CEP.find k old_ct) as [[| |expr]|],
                   (CEP.find k old_vm) as [[gt|gt|gt|gt|gt]|] ; try done ;
          subst ft_tgt ;
          destruct (type_of_expr expr old_tmap) as [[[gt_expr| |] ]|] ; done.
        destruct Haft as [_ Haft] ; split.
        - apply subdomain_refl.
        destruct Haft as [_ Haft] ; split.
        - apply Haft.
        destruct Haft as [Hct_sub_vm Haft] ; split.
        - apply Haft.
        destruct Haft as [Hvm_sub_tm Haft] ; split.
        - apply Haft.
        - intro k ; specialize (Hct_sub_vm k) ; specialize (Hvm_sub_tm k).
          destruct (CEP.find k old_ct) as [[| |expr]|],
                   (CEP.find k old_vm) as [[gt|gt|gt|gt|gt]|] ; try done ;
          rewrite Hvm_sub_tm //.
  specialize Hsdu_t with (1 := Hsf_comp_t) (2 := Htmt_sub_tm) (3 := Hsdu_t_precondition) ;
  clear Hsdu_t_precondition.
  specialize Haft_comp_f with (1 := Hsf_comp_f).
  assert (Haft_comp_f_precondition: all_fit_together old_scope old_connmap ct_comp_t vm_comp_t tm_tmap_t).
        split.
        - destruct Haft as [Haft _].
          intro k ; specialize (Haft k).
          destruct (CEP.find k old_scope) as [[ft_tgt [| | | |]]|] ; try by exact Haft.
          1,2: destruct (CEP.find k old_connmap) as [[| |expr]|] ; try by exact Haft.
          1,2: generalize (type_of_expr_submap expr old_tmap tm_tmap_t (proj1 (proj2 Hst_sub_t))) ; intro.
          1,2: destruct (type_of_expr expr old_tmap) as [[ft_src ori]|] ; last by contradiction Haft.
          1,2: rewrite H //.
        destruct Haft as [_ Haft], Haft_comp_t as [[_ Haft_comp_t] _] ; split.
        - destruct Haft as [Haft _].
          intro k ; specialize (Haft k).
          destruct (CEP.find k old_connmap) ; last by (destruct (CEP.find k ct_comp_t) ; done).
          destruct Hsf_comp_sub_t as [_ [_ Hsf_comp_sub_t]] ; specialize (Hsf_comp_sub_t k).
          destruct (CEP.find k old_ct) ; last by discriminate Haft.
          by rewrite (Hsf_comp_sub_t _ Logic.eq_refl) //.
        destruct Haft as [_ Haft], Haft_comp_t as [_ Haft_comp_t] ; split.
        - by apply Haft_comp_t.
        destruct Haft as [_ Haft], Haft_comp_t as [_ Haft_comp_t] ; split.
        - by apply Haft_comp_t.
        destruct Haft as [_ Haft], Haft_comp_t as [_ Haft_comp_t] ; split.
        - destruct Haft as [Haft _], Hsf_comp_sub_t as [_ [Hsf_comp_sub_t _]].
          intro k ; specialize (Haft k) ; specialize (Hsf_comp_sub_t k).
          destruct (CEP.find k old_scope) as [[ft [| | | |]]|] ; try by exact Haft.
          1-3: destruct (CEP.find k old_vm) ; last by contradiction Haft.
          1-3: rewrite (Hsf_comp_sub_t _ Logic.eq_refl) //.
        - destruct Haft as [_ Haft].
          intro k ; specialize (Haft k).
          destruct (CEP.find k old_connmap) as [[| |expr]|] ;
                try (by exact Haft) ;
          destruct Hst_sub_t as [_ [Hst_sub_t _]].
          * 3: generalize (type_of_expr_submap expr old_tmap tm_tmap_t Hst_sub_t) ; intro.
            3: destruct (type_of_expr expr old_tmap) as [[[gt_expr| |] p]|]; try (by contradiction Haft).
            3: rewrite H ; clear H.
          1-3: specialize (Hst_sub_t k).
          1-3: destruct (CEP.find k old_tmap) as [[ft [| | | |]]|] ;
                     try (by contradiction Haft) ;
               by rewrite (Hst_sub_t _ Logic.eq_refl) //.
  specialize (Haft_comp_f Haft_comp_f_precondition) ; clear Haft_comp_f_precondition.
  assert (Hsdu_f_precondition: all_fit_together old_scope ct_comp_t ct_comp_t vm_comp_t tm_tmap_t).
        destruct Haft_comp_t as [Haft_comp_t _] ; split.
        - destruct Haft_comp_t as [_ [_ [Hct_sub_vm [_ [Hsc_sub_vm _]]]]].
          destruct Hst_sub_t as [_ [_ Hst_sub_t]].
          intro k ; specialize (Hst_sub_t k) ; specialize (Hct_sub_vm k) ; specialize (Hsc_sub_vm k).
          destruct (CEP.find k old_scope) as [[ft_tgt [| | | |]]|] ; try done ;
          rewrite (Hst_sub_t _ Logic.eq_refl) in Hsc_sub_vm ;
          destruct (CEP.find k ct_comp_t) as [[| |expr]|],
                   (CEP.find k vm_comp_t) as [[gt|gt|gt|gt|gt]|] ; try done ;
          subst ft_tgt ;
          destruct (type_of_expr expr tm_tmap_t) as [[[gt_expr| |] ]|] ; done.
        destruct Haft_comp_t as [_ Haft_comp_t] ; split.
        - apply subdomain_refl.
        destruct Haft_comp_t as [_ Haft_comp_t] ; split.
        - apply Haft_comp_t.
        destruct Haft_comp_t as [Hct_sub_vm Haft_comp_t] ; split.
        - apply Haft_comp_t.
        destruct Haft_comp_t as [Hvm_sub_tm Haft_comp_t] ; split.
        - destruct Haft_comp_t as [Haft_comp_t _] ; destruct Hst_sub_t as [_ [_ Hst_sub_t]].
          intro ; specialize (Hst_sub_t k) ; specialize (Haft_comp_t k).
          destruct (CEP.find k old_scope) as [[ft ori]|] ; last by trivial.
          by rewrite (Hst_sub_t _ Logic.eq_refl) // in Haft_comp_t.
        - intro k ; specialize (Hct_sub_vm k) ; specialize (Hvm_sub_tm k).
          destruct (CEP.find k ct_comp_t) as [[| |expr]|],
                   (CEP.find k vm_comp_t) as [[gt|gt|gt|gt|gt]|] ; try done ;
          rewrite Hvm_sub_tm //.
  specialize Hsdu_f with (1 := Hsf_comp_f) (2 := Htm_tm_sub_tm) (3 := Hsdu_f_precondition) ;
  clear Hsdu_f_precondition.
  assert (Hsf_t : Sem_frag_stmts old_vm old_ct
                        (Qcat (component_stmts_of sst) (convert_to_connect_stmts eb_connmap_t))
                        vm_comp_t (extend_defined_map_with eb_connmap_t ct_comp_t) tmap).
        apply Sem_frag_stmts_cat.
        exists vm_comp_t, ct_comp_t.
        split ; first by exact Hsf_comp_t.
        apply Sem_frag_stmts_connect ; first by exact Htm_inf.
        (* Now we can use Haft_comp_t to prove this *)
        destruct Haft_comp_t as [Haft_comp_t _] ; split.
        + intro k ; rewrite CEP.Lemmas.empty_o //.
        destruct Haft_comp_t as [_ Haft_comp_t] ; split.
        + by apply Haft_comp_t.
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
        destruct Haft_comp_t as [_ Haft_comp_t] ; split.
        + intro k ; rewrite CEP.Lemmas.empty_o //.
        + destruct Haft_comp_t as [_ Haft_comp_t].
          intro k ; specialize (Haft_comp_t k).
          destruct (CEP.find k eb_connmap_t) as [[| |expr]|] ; try by exact Haft_comp_t.
          - 3: generalize (type_of_expr_submap expr tm_tmap_t tmap Htmt_sub_tm) ; intro.
            3: destruct (type_of_expr expr tm_tmap_t) as [[[gt_expr| |] p]|] ; try by contradiction Haft_comp_t.
            3: rewrite H ; clear H.
          1-3: specialize (Htmt_sub_tm k).
          1-3: destruct (CEP.find k tm_tmap_t) as [[[gt_ref| |] [| | | |]]|] ;
                     try (by contradiction Haft_comp_t) ;
               by rewrite (Htmt_sub_tm _ Logic.eq_refl) //.
  specialize IHsst with (1 := Hsf_t) ; clear Hsf_t.
  specialize Sem_frag_stmts_component with (1 := proj1 Hsf_comp_sub_t) (2 := Hsf_comp_f) ; intro Hsf_comp_sub_f.
  specialize Sem_frag_stmts_compatible with (1 := proj1 IHsst) ; intro Hsf_sub_t.
  (*assert (Hsf_comp0_f : exists (vm_comp_f : CEP.t vertex_type) (ct_comp_f : CEP.t def_expr),
        Sem_frag_stmts old_vm old_ct (component_stmts_of ssf) vm_comp_f ct_comp_f tmap).
        (* This should hold because old_vm is a subset of vm_comp_t
           and based on Hsf_comp_f. *)
        admit.
  destruct Hsf_comp0_f as [vm_comp_f [ct_comp_f Hsf_comp0_f]].*)
  assert (Hsf_f : Sem_frag_stmts vm_comp_t (extend_map_with old_ct (extend_defined_map_with eb_connmap_t ct_comp_t))
                        (Qcat (component_stmts_of ssf) (convert_to_connect_stmts eb_connmap_f))
                        vm_comp (extend_defined_map_with eb_connmap_f (extend_map_with
     (extend_map_with old_ct (extend_defined_map_with eb_connmap_t ct_comp_t))
     ct_comp)) tmap).
        apply Sem_frag_stmts_cat.
        exists vm_comp, (extend_map_with (extend_map_with old_ct (extend_defined_map_with eb_connmap_t ct_comp_t)) ct_comp).
        split.
        + assert (H_precondition: ct_sub_vm (extend_map_with old_ct (extend_defined_map_with eb_connmap_t ct_comp_t)) vm_comp_t tmap).
                intro k.
                rewrite /extend_map_with CEP.Lemmas.map2_1bis // CEP.Lemmas.map2_1bis //.
                destruct Hsf_comp_sub_t as [Hctct_sub_vmct [_ Hoct_sub_ctct]] ;
                specialize (Hctct_sub_vmct k) ; specialize (Hoct_sub_ctct k).
                destruct Haft_comp_t as [[_ [Hctct_sub_ct [_ [Hvmct_sub_tm [_ Hebcm_sub_tm]]]]] _] ;
                specialize (Hctct_sub_ct k).
                destruct (CEP.find k old_ct) ;
                       first (by specialize (Hoct_sub_ctct _ Logic.eq_refl) ;
                                 rewrite Hoct_sub_ctct // in Hctct_sub_vmct).
                specialize (Hvmct_sub_tm k) ; specialize (Hebcm_sub_tm k).
                destruct (CEP.find k ct_comp_t) as [[| |ctct_expr]|] ;
                      last (by rewrite Hctct_sub_ct //) ;
                destruct (CEP.find k eb_connmap_t) as [[| |ebct_expr]|] ;
                      try done ;
                destruct (CEP.find k vm_comp_t) as [[gt|gt|gt|gt|gt]|] ;
                      try done ;
                rewrite Hvmct_sub_tm in Hebcm_sub_tm ;
                generalize (type_of_expr_submap ebct_expr tm_tmap_t tmap Htmt_sub_tm) ; intro H0 ;
                destruct (type_of_expr ebct_expr tm_tmap_t) as [[[gt_expr| |] Hgt_expr_inf]|] ;
                      try (by contradiction Hebcm_sub_tm) ;
                by rewrite H0 //.
          apply (Sem_frag_stmts_component_Equal ssf vm_comp_t vm_comp_t ct_comp_t
                                           (extend_map_with old_ct (extend_defined_map_with eb_connmap_t ct_comp_t))
                                           vm_comp vm_comp ct_comp tmap tmap
                                           (proj1 Hsf_comp_sub_t)) in H_precondition ;
                try (by apply CEP.Lemmas.Equal_refl) ;
                done.
        + apply Sem_frag_stmts_connect ; first by exact Htm_inf.
          destruct Haft_comp_t as [Haft_comp_t _], Haft_comp_f as [Haft_comp_f _] ; split.
          + intro k ; by rewrite CEP.Lemmas.empty_o //.
          destruct Haft as [_ Haft], Haft_comp_f as [_ Haft_comp_f], Haft_comp_t as [_ Haft_comp_t] ; split.
          + destruct Haft_comp_f as [Haft_comp_f _].
            intro k ; specialize (Haft_comp_f k).
            rewrite /extend_map_with CEP.Lemmas.map2_1bis // CEP.Lemmas.map2_1bis // /extend_defined_map_with CEP.Lemmas.map2_1bis //.
            destruct (CEP.find k old_ct) ; first by trivial.
            destruct (CEP.find k eb_connmap_t) as [[]|] ; try by trivial.
            1,2: destruct (CEP.find k ct_comp_t) ; by trivial.
          destruct Haft as [_ Haft], Haft_comp_t as [Hebcmt_sub_ctct Haft_comp_t], Haft_comp_f as [_ Haft_comp_f] ; split.
          + destruct Haft as [Haft _], Haft_comp_t as [Haft_comp_t [Hvmct_sub_tmt [_ Hebcmt_sub_tmt]]], Haft_comp_f as [Haft_comp_f _].
            intro k ; specialize (Haft k) ; specialize (Haft_comp_t k) ; specialize (Haft_comp_f k).
            rewrite /extend_map_with CEP.Lemmas.map2_1bis // CEP.Lemmas.map2_1bis // /extend_defined_map_with CEP.Lemmas.map2_1bis //.
            destruct (CEP.find k old_ct) as [[| |oldexpr]|].
            - 1-3: destruct Hsf_sub_t as [Hsf_sub_t _] ; specialize (Hsf_sub_t k) ;
                   destruct (CEP.find k old_vm) as [[gt|gt|gt|gt|gt]|] ;
                         try (by contradiction Haft) ;
                   rewrite (proj1 (proj2 Hsf_comp_sub_f) k _ (Hsf_sub_t _ Logic.eq_refl)) //.
              1-3: generalize (type_of_expr_submap oldexpr old_tmap tmap Holdtm_sub_tm) ; intro Htyp_oldexpr ;
                   destruct (type_of_expr oldexpr old_tmap) as [[[gt_oldexpr| |] Hgt_oldexpr_exp]|] ;
                         try (by contradiction Haft) ;
                   by rewrite Htyp_oldexpr //.
            - specialize (Hebcmt_sub_ctct k) ; specialize (Hebcmt_sub_tmt k).
              destruct (CEP.find k eb_connmap_t) as [[| |cmt_expr]|] ;
              destruct Hsf_comp_sub_f as [_ [Hvmct_sub_vmc Hsf_comp_sub_f]] ; specialize (Hsf_comp_sub_f k) ;
              destruct (CEP.find k ct_comp_t) as [[| |ctct_expr]|] ; try done.
              * 1-12: specialize (Hsf_comp_sub_f _ Logic.eq_refl).
                1,2,4,5,10,11: by rewrite Hsf_comp_sub_f // in Haft_comp_f.
                1-6: rewrite Hsf_comp_sub_f in Haft_comp_f.
              * 1: destruct (CEP.find k vm_comp) as [[gt|gt|gt|gt|gt]|] ; try done ;
                   generalize (type_of_expr_submap ctct_expr tm_tmap tmap Htm_tm_sub_tm) ; intro ;
                   destruct (type_of_expr ctct_expr tm_tmap) as [[[gt_ctct_expr| |] Hgt_ctct_expr_exp]|] ;
                         try (by contradiction Haft_comp_f) ;
                   rewrite H ; done.
              * 1: destruct (CEP.find k vm_comp) as [[gt|gt|gt|gt|gt]|] ; done.
              * 1-3: specialize (Hvmct_sub_vmc k) ; specialize (Hvmct_sub_tmt k).
                1-3: destruct (CEP.find k vm_comp_t) as [[gt|gt|gt|gt|gt]|] ;
                         try (by contradiction Haft_comp_t) ;
                   generalize (type_of_expr_submap cmt_expr tm_tmap_t tmap Htmt_sub_tm) ; intro ;
                   destruct (type_of_expr cmt_expr tm_tmap_t) as [[[gt_ctm_expr| |] Hgt_cmt_expr_exp]|] ;
                         try (by contradiction Hebcmt_sub_tmt) ;
                   rewrite (Hvmct_sub_vmc _ Logic.eq_refl) H // ; clear H ;
                   by rewrite Hvmct_sub_tmt // in Hebcmt_sub_tmt.
              * generalize (type_of_expr_submap ctct_expr tm_tmap tmap Htm_tm_sub_tm) ; intro.
                destruct (CEP.find k vm_comp) as [[gt|gt|gt|gt|gt]|] ; try done ;
                destruct (type_of_expr ctct_expr tm_tmap) as [[[gt_ctct_expr| |] Hgt_ctct_expr_exp]|] ; try done ;
                by rewrite H //.
              * destruct (CEP.find k ct_comp) as [[| |ctc_expr]|] ; try done.
                generalize (type_of_expr_submap ctc_expr tm_tmap tmap Htm_tm_sub_tm) ; intro.
                destruct (CEP.find k vm_comp) as [[gt|gt|gt|gt|gt]|] ; try done ;
                destruct (type_of_expr ctc_expr tm_tmap) as [[[gt_ctct_expr| |] Hgt_ctct_expr_exp]|] ; try done ;
                by rewrite H //.
          destruct Haft as [_ Haft], Haft_comp_t as [_ Haft_comp_t], Haft_comp_f as [_ Haft_comp_f] ; split.
          + destruct Haft_comp_f as [Haft_comp_f _].
            intro k ; specialize (Haft_comp_f k).
            destruct (CEP.find k vm_comp) as [[gt|gt|gt|gt|gt]|] ;
                  last (by trivial) ;
            apply Htm_tm_sub_tm in Haft_comp_f ;
            by rewrite Haft_comp_f //.
          destruct Haft_comp_f as [_ Haft_comp_f], Haft_comp_t as [_ Haft_comp_t] ; split.
          + intro k ; by rewrite CEP.Lemmas.empty_o //.
          + destruct Haft_comp_f as [_ Haft_comp_f].
            intro k ; specialize (Haft_comp_f k).
            destruct (CEP.find k eb_connmap_f) as [[| |expr]|] ; try by exact Haft_comp_f.
            * 3: generalize (type_of_expr_submap expr tm_tmap tmap Htm_tm_sub_tm) ; intro.
              3: destruct (type_of_expr expr tm_tmap) as [[[gt_expr| |] ]|] ; try by contradiction Haft_comp_f.
              3: rewrite H ; clear H.
            1-3: specialize (Htm_tm_sub_tm k) ;
                 destruct (CEP.find k tm_tmap) as [[ft [| | | |]]|] ;
                       last (by contradiction Haft_comp_f) ;
                 by rewrite (Htm_tm_sub_tm _ Logic.eq_refl) //.
  specialize IHssf with (3 := Hsf_f) (4 := Htm_sub_vm) ; clear Hsf_f.
  assert (Hsubmap_f : CEP.submap old_connmap (extend_map_with old_ct (extend_defined_map_with eb_connmap_t ct_comp_t))).
        intros k v Hold_cm.
        apply Hcm_submap_ct in Hold_cm.
        rewrite /extend_map_with CEP.Lemmas.map2_1bis // Hold_cm //.
  specialize IHssf with (2 := Hsubmap_f) ; clear Hsubmap_f.
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
          destruct (CEP.find k old_connmap) ;
                last by (destruct (CEP.find k (extend_map_with old_ct (extend_defined_map_with eb_connmap_t ct_comp_t))) ; done).
          rewrite /extend_map_with CEP.Lemmas.map2_1bis //.
          destruct (CEP.find k old_ct) ;
                last by discriminate Hcm_ct.
          by trivial.
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
        destruct Haft as [_ Haft] ; split.
        + intro k.
          destruct Hst_sub_t as [_ [_ Hst_sub_t]] ; specialize (Hst_sub_t k).
          destruct (CEP.find k old_scope) as [[ft sc_ori]|] ; last by trivial.
          destruct IHsst as [_ [[_ [_ [_ [_ [IHsst _]]]]] _]] ; specialize (IHsst k).
          by specialize Hst_sub_t with (1 := Logic.eq_refl) ; rewrite Hst_sub_t // in IHsst.
        + destruct Haft as [_ Haft].
          intro k ; specialize (Haft k).
          destruct (CEP.find k old_connmap) as [[| |expr]|] ; try by exact Haft.
          * 3: generalize (type_of_expr_submap expr old_tmap tm_tmap_t (proj1 (proj2 Hst_sub_t))) ; intro.
            3: destruct (type_of_expr expr old_tmap) as [[[gt_expr| |] ]|] ; try by contradiction Haft.
            3: rewrite H // ; clear H.
          1-3: destruct Hst_sub_t as [_ [Hst_sub_t _]] ; specialize (Hst_sub_t k).
          1-3: destruct (CEP.find k old_tmap) as [[[gt_ref| |] [| | | |]]|] ;
                     try (by contradiction Haft) ;
               by rewrite (Hst_sub_t _ Logic.eq_refl) //.
  specialize IHssf with (1 := Haft_f) ; clear Haft_f.
  apply convert_to_connect_stmts_Sem in Hsf_conn.
  + split.
    - exists vm_comp_t, (extend_defined_map_with eb_connmap_t ct_comp_t),
             (extend_defined_map_with eb_connmap_f
             (extend_map_with
                (extend_map_with old_ct
                   (extend_defined_map_with eb_connmap_t ct_comp_t)) ct_comp)).
      split.
      - by apply IHsst.
      split.
      - apply Sem_frag_stmts_Equal with (vm_old1 := vm_comp_t)
                    (ct_old1 := (extend_map_with old_ct (extend_defined_map_with eb_connmap_t ct_comp_t)))
                    (vm_new1 := vm_comp) (ct_new1 := (extend_defined_map_with eb_connmap_f
             (extend_map_with
                (extend_map_with old_ct
                   (extend_defined_map_with eb_connmap_t ct_comp_t)) ct_comp)))
                    (tmap1 := tmap) ;
              try (by apply CEP.Lemmas.Equal_refl) ;
              first (by apply Hsf_conn).
        by apply IHssf.
      - intro k.
        rewrite (proj2 Hsf_conn) /extend_defined_map_with /combine_when_connections /Swhen_map2_helper.
        repeat (rewrite CEP.Lemmas.map2_1bis //).
        destruct (CEP.find k eb_connmap_t) as [[| |expr_cm_t]|] eqn: Heb_cm_t.
        * specialize (proj2 (proj2 Hsf_comp_sub_f) k) ; intro Hctct_sub_ctc.
          specialize (proj2 (proj2 IHsst) k) ; intro Hcmt_sub_ctct.
          rewrite /extend_defined_map_with CEP.Lemmas.map2_1bis // /extend_map_with CEP.Lemmas.map2_1bis // Heb_cm_t in Hcmt_sub_ctct.
          specialize (proj2 (proj2 IHssf) k) ; intro Hcmf_sub_ctct.
          rewrite /extend_defined_map_with /extend_map_with CEP.Lemmas.map2_1bis // CEP.Lemmas.map2_1bis // CEP.Lemmas.map2_1bis // CEP.Lemmas.map2_1bis // CEP.Lemmas.map2_1bis // CEP.Lemmas.map2_1bis // CEP.Lemmas.map2_1bis // Heb_cm_t in Hcmf_sub_ctct.
          destruct (CEP.find k ct_comp_t) as [[| |expr_ctct]|] eqn: Hctct ;
          try by discriminate (Hcmt_sub_ctct _ Logic.eq_refl).
          + rewrite (Hctct_sub_ctc _ Logic.eq_refl).
            destruct (match PVM.find k eb_connmap_f with
                      | Some D_invalidated | Some (D_fexpr _) => PVM.find k eb_connmap_f
                      | _ =>
                          match
                            match PVM.find k old_ct with
                            | Some e => Some e
                            | None => Some D_undefined
                            end
                          with
                          | Some e => Some e
                          | None => Some D_undefined
                          end
                      end) as [[]|] ; by reflexivity.
          + (* CEP.find k ct_comp_t = None, but eb_connmap_t <> None. *)
            destruct Haft_comp_t as [[_ [Haft_comp_t _]] _].
            specialize (Haft_comp_t k).
            by rewrite Heb_cm_t Hctct // in Haft_comp_t.
        * 1,2: specialize (proj2 (proj2 Hsf_comp_sub_f) k) ; intro Hctct_sub_ctc.
          1,2: specialize (proj2 (proj2 IHssf) k) ; intro Hcmf_sub_ctct.
          1,2: rewrite /extend_defined_map_with /extend_map_with CEP.Lemmas.map2_1bis // CEP.Lemmas.map2_1bis // CEP.Lemmas.map2_1bis // CEP.Lemmas.map2_1bis // CEP.Lemmas.map2_1bis // CEP.Lemmas.map2_1bis // CEP.Lemmas.map2_1bis // Heb_cm_t in Hcmf_sub_ctct.
          1,2: destruct (CEP.find k ct_comp_t) as [[| |expr_ctct]|] eqn: Hctct.
          + 1-3,5-7: rewrite (Hctct_sub_ctc _ Logic.eq_refl) ;
                     rewrite (Hctct_sub_ctc _ Logic.eq_refl) in Hcmf_sub_ctct.
            1,4: destruct (CEP.find k eb_connmap_f) as [[| |expr_cm_f]|] eqn: Heb_cm_f ; try by reflexivity.
            - 1,3: destruct (CEP.find k old_ct) as [[]|] eqn: Holdct ; try by discriminate (Hcmf_sub_ctct _ Logic.eq_refl).
              1,2: by reflexivity.
            - (* CEP.find k eb_connmap_f = None. So k is not declared in ssf.
                 From proj2 Haft_comp_f we can conclude that CEP.find k old_scope = CEP.find k tm_scope_f
                 and that CEP.find k old_connmap = None.
                 We know that if CEP.find k old_ct = None, the proof is completed;
                 but otherwise we must have CEP.find k old_ct = Some D_undefined.
                 Now because CEP.find k eb_connmap_t = Some D_invalidated, k must be in scope.
                 But then we cannot have CEP.find eb_connmap_f = None. *)
              1,3: destruct Hsf_comp_sub_t as [_ [_ Hsf_comp_sub_t]] ; specialize (Hsf_comp_sub_t k) ;
              destruct (CEP.find k old_ct) as [[| |old_ct_expr]|] eqn: Hold_ct ; last (by rewrite // eq_refl //) ;
              try by rewrite (Hsf_comp_sub_t _ Logic.eq_refl) // in Hctct.
              1,2: specialize (proj2 Haft_comp_t k) ; intro ; rewrite Heb_cm_t in H.
              1,2: specialize (Hcm_submap_ct k) ; destruct (CEP.find k old_connmap) as [[| |oldcm_expr]|] eqn: Holdcm ;
                    try (by rewrite (Hcm_submap_ct _ Logic.eq_refl) // in Hold_ct).
              * (* old_connmap = Some D_undefined, so eb_connmap_f <> None *)
                1,3: destruct Heb_f as [Heb_f _] ; specialize (Heb_f k).
                1,2: by rewrite Holdcm Heb_cm_f // in Heb_f.
              * (* old_connmap = None, so k is not in old_scope, so it cannot be changed in the true branch. *)
                1,2: destruct Haft as [H1 [_ [H2 [H3 _]]]] ; specialize (H1 k) ; rewrite Holdcm in H1.
                1,2: destruct (CEP.find k old_scope) as [[ft [| | | |]]|] eqn: Holdsc ; try by contradiction H1.
                + (* well, actually the scope has source orientation, but then it cannot be connected at all *)
                  1,3: destruct Haft_comp_t as [[Haft_comp_t _] _] ; specialize (Haft_comp_t k).
                  1,2: destruct (CEP.find k tm_scope_t) as [[ft_t [| | | |]]|] ; try done ;
                  destruct (CEP.find k old_tmap) as [[ft_otm [| | | |]]|] ; try done ;
                  destruct H as [H [H' _]] ; try (by discriminate H) ; try (by discriminate H').
                  1,2: by rewrite Haft_comp_t // in Heb_cm_t.
                + (* out of scope but defined in old_tmap... *)
                  1,2: specialize (H2 k) ; specialize (H3 k).
                  1,2: rewrite Hold_ct in H2.
                  1,2: destruct (CEP.find k old_vm) as [[gt|gt|gt|gt|gt]|] ;
                        try (by contradiction H2) ;
                  rewrite H3 in H ;
                  destruct (CEP.find k tm_scope_t) ; done.
          + destruct (expr_cm_t == expr_cm_f) ; by reflexivity.
          + 1-7: destruct (CEP.find k eb_connmap_f) as [[| |expr_cm_f]|] eqn: Heb_cm_f ; try by done.
            (* The above line also touches the goal with eb_connmap_t = None *)
            - 1,3,5,8,11,13: destruct Hsf_comp_sub_t as [_ [_ Hsf_comp_sub_t]] ; specialize (Hsf_comp_sub_t k) ;
              destruct (CEP.find k old_ct) as [[]|] eqn: Holdct ; try (by discriminate (Hcmf_sub_ctct _ Logic.eq_refl)) ;
              by rewrite (Hsf_comp_sub_t _ Logic.eq_refl) // in Hctct.
            - (* CEP.find k eb_connmap_f = None. So k is not declared in ssf.
                 From proj2 Haft_comp_f we can conclude that CEP.find k old_scope = CEP.find k tm_scope_f
                 and that CEP.find k old_connmap = None.
                 We know that if CEP.find k old_ct = None, the proof is completed;
                 but otherwise we must have CEP.find k old_ct = Some D_undefined.
                 Now because CEP.find k eb_connmap_t = Some D_invalidated, k must be in scope.
                 But then we cannot have CEP.find eb_connmap_f = None. *)
              1,7: destruct Hsf_comp_sub_t as [_ [_ Hsf_comp_sub_t]] ; specialize (Hsf_comp_sub_t k) ;
              destruct (CEP.find k old_ct) as [[| |old_ct_expr]|] eqn: Hold_ct ; last (by reflexivity) ;
              by rewrite (Hsf_comp_sub_t _ Logic.eq_refl) // in Hctct.
            - (* CEP.find k eb_connmap_f = None. So k is not declared in ssf.
                 From proj2 Haft_comp_f we can conclude that CEP.find k old_scope = CEP.find k tm_scope_f
                 and that CEP.find k old_connmap = None.
                 We know that if CEP.find k old_ct = None, the proof is completed;
                 but otherwise we must have CEP.find k old_ct = Some D_undefined.
                 Now because CEP.find k eb_connmap_t = Some D_invalidated, k must be in scope.
                 But then we cannot have CEP.find eb_connmap_f = None. *)
              1,3,5,7: destruct Hsf_comp_sub_t as [_ [_ Hsf_comp_sub_t]] ; specialize (Hsf_comp_sub_t k) ;
              destruct (CEP.find k old_ct) as [[| |old_ct_expr]|] eqn: Hold_ct ; last (by rewrite // eq_refl //) ;
              try by rewrite (Hsf_comp_sub_t _ Logic.eq_refl) // in Hctct.
              (* The above already solves two goals. *)
              1,2: specialize (proj2 Haft_comp_t k) ; intro ; rewrite Heb_cm_t in H ;
              specialize (Hcm_submap_ct k) ; destruct (CEP.find k old_connmap) as [[| |oldcm_expr]|] eqn: Holdcm ;
                    try (by rewrite (Hcm_submap_ct _ Logic.eq_refl) // in Hold_ct).
              * (* old_connmap = Some D_undefined, so eb_connmap_f <> None *)
                1,3: destruct Heb_f as [Heb_f _] ; specialize (Heb_f k) ;
                by rewrite Holdcm Heb_cm_f // in Heb_f.
              * (* old_connmap = None, so k is not in old_scope, so it cannot be changed in the true branch. *)
                1,2: destruct Haft as [H1 [_ [H2 [H3 _]]]] ; specialize (H1 k) ; rewrite Holdcm in H1 ;
                destruct (CEP.find k old_scope) as [[ft [| | | |]]|] eqn: Holdsc ; try by contradiction H1.
                + (* well, actually the scope has source orientation, but then it cannot be connected at all *)
                  1,3: destruct Haft_comp_t as [[Haft_comp_t _] _] ; specialize (Haft_comp_t k) ;
                  destruct (CEP.find k tm_scope_t) as [[ft_t [| | | |]]|] ; try done ;
                  destruct (CEP.find k old_tmap) as [[ft_otm [| | | |]]|] ; try done ;
                  destruct H as [H [H' _]] ; try (by discriminate H) ; try (by discriminate H') ;
                  by rewrite Haft_comp_t // in Heb_cm_t.
                + (* out of scope but defined in old_tmap... *)
                  1,2: specialize (H2 k) ; specialize (H3 k) ;
                  rewrite Hold_ct in H2 ;
                  destruct (CEP.find k old_vm) as [[gt|gt|gt|gt|gt]|] ;
                        try (by contradiction H2) ;
                  rewrite H3 in H ;
                  destruct (CEP.find k tm_scope_t) ; done.
            - 1-3: destruct (expr_cm_t == expr_cm_f) ; by reflexivity.
          + specialize (proj2 (proj2 Hsf_comp_sub_f) k) ; intro Hctct_sub_ctc.
            specialize (proj2 (proj2 IHssf) k) ; intro Hcmf_sub_ctct.
            rewrite /extend_defined_map_with /extend_map_with CEP.Lemmas.map2_1bis // CEP.Lemmas.map2_1bis // CEP.Lemmas.map2_1bis // CEP.Lemmas.map2_1bis // CEP.Lemmas.map2_1bis // CEP.Lemmas.map2_1bis // CEP.Lemmas.map2_1bis // Heb_cm_t in Hcmf_sub_ctct.
            destruct (CEP.find k ct_comp_t) as [[| |expr_ctct]|] eqn: Hctct.
            - 1-3: rewrite (Hctct_sub_ctc _ Logic.eq_refl) ;
                   rewrite (Hctct_sub_ctc _ Logic.eq_refl) in Hcmf_sub_ctct.
              * destruct (match
                            match PVM.find k old_ct with
                            | Some e => Some e
                            | None => Some D_undefined
                            end
                          with
                          | Some e => Some e
                          | None => Some D_undefined
                          end) as [[]|] ; by reflexivity.
              * destruct Hsf_comp_sub_t as [_ [_ Hsf_comp_sub_t]] ; specialize (Hsf_comp_sub_t k).
                destruct (CEP.find k old_ct) as [[]|] eqn: Holdct ; try by rewrite (Hsf_comp_sub_t _ Logic.eq_refl) // in Hctct.
                by reflexivity.
              * destruct Hsf_comp_sub_t as [_ [_ Hsf_comp_sub_t]] ; specialize (Hsf_comp_sub_t k).
                destruct (PVM.find k old_ct) as [[| |old_expr]|] eqn: Holdct ; try done ;
                try rewrite (Hsf_comp_sub_t _ Logic.eq_refl) // in Hctct.
                + injection Hctct ; intro ; subst expr_ctct ; rewrite eq_refl //.
                + by rewrite eq_refl //.
              * destruct Hsf_comp_sub_t as [_ [_ Hsf_comp_sub_t]] ; specialize (Hsf_comp_sub_t k).
                destruct (CEP.find k old_ct) as [[]|] eqn: Holdct ; try by rewrite (Hsf_comp_sub_t _ Logic.eq_refl) // in Hctct.
                destruct (CEP.find k ct_comp) ; done.
          + (*specialize (proj2 (proj2 Hsf_comp_sub_f) k) ; intro Hctct_sub_ctc.*)
            1,2: specialize (proj2 (proj2 IHsst) k) ; intro Hcmt_sub_ctc.
            1,2: rewrite /extend_defined_map_with /extend_map_with CEP.Lemmas.map2_1bis // CEP.Lemmas.map2_1bis // Heb_cm_t in Hcmt_sub_ctc.
            1,2: destruct (CEP.find k ct_comp_t) as [[| |expr_ctct]|] eqn: Hctct ; try done.
            - (* CEP.find k old_ct = D_undefined and CEP.find k eb_connmap_f = D_invalidated,
               so it must be in scope. But then CEP.find k eb_connmap_t <> None. *)
              1-4: destruct Heb_t as [Heb_t _] ; specialize (Heb_t k).
              1-4: rewrite Heb_cm_t // in Heb_t.
              1-4: destruct Haft as [H1 [_ [H2 [H3 [H4 _]]]]] ; specialize (H1 k) ; rewrite Heb_t in H1.
              1-4: destruct (CEP.find k old_scope) as [[ft [| | | |]]|] eqn: Holdsc ; try by contradiction H1.
              * (* well, actually the scope has source orientation, but then it cannot be connected at all *)
                1,3,5,7: specialize (H2 k) ; rewrite (Hcmt_sub_ctc _ Logic.eq_refl) in H2.
                1-4: specialize (H4 k) ; rewrite Holdsc in H4.
                1-4: destruct (CEP.find k old_vm) as [[]|] ; done.
              * (* out of scope but defined in old_tmap... so it cannot be redefined. *)
                1-4: specialize (proj2 Haft_comp_f k) ; intro H.
                1-4: rewrite Holdsc Heb_t Heb_cm_f in H.
                1-4: specialize (H2 k) ; specialize (H3 k).
                1-4: rewrite (Hcmt_sub_ctc _ Logic.eq_refl) in H2.
                1-4: destruct (CEP.find k old_vm) as [[gt|gt|gt|gt|gt]|] ;
                      try (by contradiction H2) ;
                rewrite (proj1 (proj2 Hst_sub_t) k _ H3) in H ;
                destruct (CEP.find k tm_scope_f) ; done.
          + specialize (proj2 (proj2 IHsst) k) ; intro Hcmt_sub_ctc.
            rewrite /extend_defined_map_with /extend_map_with CEP.Lemmas.map2_1bis // CEP.Lemmas.map2_1bis // Heb_cm_t in Hcmt_sub_ctc.
            destruct (CEP.find k ct_comp_t) as [[| |expr_ctct]|] eqn: Hctct ;
            try rewrite (proj2 (proj2 Hsf_comp_sub_f) k _ Hctct) (Hcmt_sub_ctc _ Logic.eq_refl) //.
            - by rewrite eq_refl //.
            - destruct Hsf_comp_sub_t as [_ [_ Hsf_comp_sub_t]] ; specialize (Hsf_comp_sub_t k) ;
              rewrite Hctct in Hsf_comp_sub_t.
              destruct (CEP.find k old_ct) as [[]|] ; try by discriminate (Hsf_comp_sub_t _ Logic.eq_refl).
              destruct (CEP.find k ct_comp) ; by reflexivity.
    split.
    - destruct IHsst as [_ [IHsst _]], IHssf as [_ [IHssf _]],
               Haft_comp_t as [Haft_comp_t _], Haft_comp_f as [Haft_comp_f _].
      split.
      * destruct IHsst as [IHsst _], IHssf as [IHssf _].
        intro k.
        specialize (IHsst k) ; specialize (IHssf k).
        destruct Hst_sub_t as [_ [Holdtm_sub_tmt Hst_sub_t]] ; specialize (Hst_sub_t k).
        destruct Hst_f as [Hscf_sub_tmtm [Htmt_sub_tmtm Hst_f]] ; specialize (Hst_f k).
        specialize (Hsc_tm k).
        destruct (CEP.find k old_scope) as [[ft_tgt [| | | |]]|] ;
              last (by trivial) ;
        rewrite (Hst_sub_t _ Logic.eq_refl) in IHsst ;
        rewrite (Hst_f _ Logic.eq_refl) in IHssf ;
        try done ;
        rewrite /combine_when_connections CEP.Lemmas.map2_1bis //.
        + by rewrite IHsst IHssf //.
        + 1,2: destruct (CEP.find k eb_connmap_t) as [[| |eb_expr_t]|],
                        (CEP.find k eb_connmap_f) as [[| |eb_expr_f]|] ;
               try done.
        + 2,4: destruct (eb_expr_t == eb_expr_f).
        + 1,2,4,6: generalize (type_of_expr_submap eb_expr_t tm_tmap_t tm_tmap Htmt_sub_tmtm) ; intro ;
                 destruct (type_of_expr eb_expr_t tm_tmap_t) as [[ft_src Hft_src_inf]|] ;
                       last (by contradiction IHsst) ;
                 by rewrite H //.
        + 1,2: simpl type_of_expr ;
               generalize (type_of_expr_submap cond old_scope tm_tmap (CEP.Lemmas.submap_trans (proj2 Heb_f) Hscf_sub_tmtm)) ; intro ;
               rewrite Htyp_cond in H ; rewrite H ; clear H ;
               generalize (type_of_expr_submap eb_expr_t tm_tmap_t tm_tmap Htmt_sub_tmtm) ; intro ;
               destruct (type_of_expr eb_expr_t tm_tmap_t) as [[ft_src_t Hft_src_t_inf]|] ;
                     last (by contradiction IHsst).
          1,2: rewrite H ; clear H ;
               destruct (type_of_expr eb_expr_f tm_tmap) as [[ft_src_f Hft_src_f_inf]|] ;
                     last (by contradiction IHssf).
          1,2: rewrite /ftype_mux /sval /proj2_sig ;
               specialize (Hsc_tm _ Logic.eq_refl) ;
               apply Holdtm_sub_tm in Hsc_tm ;
               specialize (Htm_inf k) ; rewrite Hsc_tm in Htm_inf ;
               destruct ft_tgt as [gt_tgt| |] ; try by contradiction Htm_inf.
          1,2: destruct ft_src_t as [gt_src_t| |] ; try by (destruct gt_tgt ; discriminate IHsst).
          1,2: destruct ft_src_f as [gt_src_f| |] ; try by (destruct gt_tgt ; discriminate IHssf).
          1,2: destruct gt_tgt, gt_src_t, gt_src_f ; done.
      destruct IHsst as [_ IHsst], IHssf as [_ IHssf],
               Haft_comp_t as [_ Haft_comp_t], Haft_comp_f as [_ Haft_comp_f] ;
      split.
      * destruct Haft_comp_t as [Haft_comp_t _], Haft_comp_f as [Haft_comp_f _].
        intro k.
        specialize (Haft_comp_t k) ; specialize (Haft_comp_f k).
        rewrite (proj2 Hsf_conn)
                /extend_defined_map_with CEP.Lemmas.map2_1bis //
                /combine_when_connections CEP.Lemmas.map2_1bis //.
        destruct (CEP.find k eb_connmap_t) as [[| |eb_expr_t]|],
                 (CEP.find k eb_connmap_f) as [[| |eb_expr_f]|] ; try done ;
        try (by destruct (CEP.find k ct_comp) ; done).
        + destruct Hsf_comp_sub_f as [_ [_ Hsf_comp_sub_f]] ; specialize (Hsf_comp_sub_f k) ;
          destruct (CEP.find k ct_comp) ; first (by trivial) ;
          destruct (CEP.find k ct_comp_t) ; last (by exact Haft_comp_t) ;
          by discriminate (Hsf_comp_sub_f _ Logic.eq_refl).
        + destruct (eb_expr_t == eb_expr_f) ; by trivial.
      destruct IHsst as [_ IHsst], IHssf as [_ IHssf],
               Haft_comp_t as [Hebt_sub_ctct Haft_comp_t], Haft_comp_f as [Hebf_sub_ctc Haft_comp_f] ;
      split.
      * destruct IHsst as [IHsst _], IHssf as [IHssf _],
                 Haft_comp_t as [Haft_comp_t _], Haft_comp_f as [Haft_comp_f _].
        intro k.
        specialize (IHsst k) ; specialize (IHssf k) ;
        specialize (Haft_comp_t k) ; specialize (Haft_comp_f k).
        rewrite (proj2 Hsf_conn)
                /extend_defined_map_with CEP.Lemmas.map2_1bis //
                /combine_when_connections CEP.Lemmas.map2_1bis //
                -(proj1 Hsf_conn).
        rewrite /extend_defined_map_with CEP.Lemmas.map2_1bis // in IHsst, IHssf.
        rewrite CEP.Lemmas.map2_1bis // CEP.Lemmas.map2_1bis // in IHssf.
        destruct Hsf_comp_sub_f as [_ [Hvmct_sub_vmc Hctct_sub_ctc]].
        specialize (Hvmct_sub_vmc k) ; specialize (Hctct_sub_ctc k).
        specialize (Hebt_sub_ctct k) ; specialize (Hebf_sub_ctc k).
        destruct (CEP.find k eb_connmap_t) as [[| |eb_expr_t]|] eqn: Heb_cm_t,
                 (CEP.find k eb_connmap_f) as [[| |eb_expr_f]|] eqn: Heb_cm_f,
                 (CEP.find k ct_comp_t) as [[| |ct_expr]|] eqn: Hctct,
                 (CEP.find k vm_comp_t) as [[gt|gt|gt|gt|gt]|] eqn: Hvmct ;
        try rewrite (Hvmct_sub_vmc _ Logic.eq_refl) ;
        try rewrite (Hvmct_sub_vmc _ Logic.eq_refl) in Haft_comp_f, IHssf ;
        try rewrite (Hctct_sub_ctc _ Logic.eq_refl) ;
        try rewrite (Hctct_sub_ctc _ Logic.eq_refl) in Haft_comp_f, Hebf_sub_ctc ;
        try done ;
        try (destruct (eb_expr_t == eb_expr_f)) ;
        try (generalize (type_of_expr_submap eb_expr_t tm_tmap_t tm_tmap (proj1 (proj2 Hst_f))) ; intro ;
             destruct (type_of_expr eb_expr_t tm_tmap_t) as [[[gt_expr_t| |] Hgt_expr_t_inf]|] ;
                   try (by contradiction IHsst) ;
             by rewrite H //) ;
        simpl type_of_expr ;
        generalize (type_of_expr_submap cond old_scope tm_tmap (CEP.Lemmas.submap_trans (proj2 Heb_f) (proj1 Hst_f))) ; intro ;
        rewrite Htyp_cond in H ; rewrite H ; clear H ;
        generalize (type_of_expr_submap eb_expr_t tm_tmap_t tm_tmap (proj1 (proj2 Hst_f))) ; intro ;
        destruct (type_of_expr eb_expr_t tm_tmap_t) as [[[gt_expr_t| |] Hgt_expr_t_inf]|] ;
              try (by contradiction IHsst) ;
        rewrite H // ; clear H ;
        destruct (type_of_expr eb_expr_f tm_tmap) as [[[gt_expr_f| |] Hgt_expr_f_inf]|] ;
              try (by contradiction IHssf) ;
        rewrite /ftype_mux /sval /proj2_sig /ftype_mux' ;
        destruct Hsdu_t as [[_ [_ [_ [Hvmct_sub_tmt _]]]] _] ;
        specialize (Hvmct_sub_tmt k) ; rewrite Hvmct in Hvmct_sub_tmt ;
        specialize (Htm_t_inf k) ; rewrite Hvmct_sub_tmt in Htm_t_inf ;
        destruct gt, gt_expr_t, gt_expr_f ; done.
      destruct IHsst as [_ IHsst], IHssf as [_ IHssf],
               Haft_comp_t as [_ Haft_comp_t], Haft_comp_f as [_ Haft_comp_f] ;
      split.
      * destruct IHssf as [IHssf _].
        intro k.
        specialize (IHssf k).
        by rewrite -(proj1 Hsf_conn) //.
      destruct IHsst as [_ IHsst], IHssf as [_ IHssf],
               Haft_comp_t as [_ Haft_comp_t], Haft_comp_f as [_ Haft_comp_f] ;
      split.
      * destruct IHssf as [IHssf _].
        intro k.
        specialize (IHssf k).
        destruct Heb_f as [_ Heb_f] ; specialize (Heb_f k).
        destruct (CEP.find k old_scope) ; last by trivial.
        by rewrite (Heb_f _ Logic.eq_refl) (proj1 Hsf_conn) // in IHssf.
      * destruct IHsst as [_ IHsst], IHssf as [_ IHssf],
               Haft_comp_t as [_ Haft_comp_t], Haft_comp_f as [_ Haft_comp_f].
        intro k.
        specialize (IHsst k) ; specialize (IHssf k).
        rewrite /combine_when_connections CEP.Lemmas.map2_1bis //.
        destruct (CEP.find k eb_connmap_t) as [[| |eb_expr_t]|] eqn: Heb_cm_t,
                 (CEP.find k eb_connmap_f) as [[| |eb_expr_f]|] eqn: Heb_cm_f ;
        try done.
        + 1-3: destruct Hst_f as [_ [Hst_f _]] ; specialize (Hst_f k) ;
               destruct (CEP.find k tm_tmap_t) ; last (by contradiction IHsst) ;
               by rewrite (Hst_f _ Logic.eq_refl) //.
        + 2: destruct (eb_expr_t == eb_expr_f).
        + 1,2,4: destruct Hst_f as [_ [Hst_f _]] ;
                 generalize (type_of_expr_submap eb_expr_t tm_tmap_t tm_tmap Hst_f) ;
                 intro ;
                 destruct (type_of_expr eb_expr_t tm_tmap_t) as [[[gt_expr_t| |] Hgt_expr_t_inf]|] ;
                       try (by contradiction IHsst) ;
                 rewrite H // ; clear H ;
                 specialize (Hst_f k) ;
                 destruct (CEP.find k tm_tmap_t) ; last (by contradiction IHsst) ;
                 by rewrite (Hst_f _ Logic.eq_refl) //.
        + simpl type_of_expr.
          generalize (type_of_expr_submap cond old_scope tm_tmap (CEP.Lemmas.submap_trans (proj2 Heb_f) (proj1 Hst_f))) ; intro ;
          rewrite Htyp_cond in H ; rewrite H ; clear H.
          destruct Hst_f as [_ [Hst_f _]].
          generalize (type_of_expr_submap eb_expr_t tm_tmap_t tm_tmap Hst_f) ;
          intro ;
          destruct (type_of_expr eb_expr_t tm_tmap_t) as [[[gt_expr_t| |] Hgt_expr_t_inf]|] ;
                try (by contradiction IHsst) ;
          rewrite H // ; clear H.
          destruct (type_of_expr eb_expr_f tm_tmap) as [[[gt_expr_f| |] Hgt_expr_f_inf]|] ;
                try (by contradiction IHssf).
          rewrite /ftype_mux /sval /proj2_sig /ftype_mux'.
          specialize (Hst_f k) ; specialize (Htm_t_inf k).
          destruct (CEP.find k tm_tmap_t) as [[[gt_ref| |] [| | | |]]|] ;
                try (by contradiction IHsst).
          1,2: specialize (Hst_f _ Logic.eq_refl) ; rewrite Hst_f in IHssf, Htm_t_inf ; rewrite Hst_f.
          1,2: destruct gt_ref, gt_expr_t, gt_expr_f ; done.
    - intros k v Hsfct.
      destruct Hsf_conn as [_ Hsf_conn].
      specialize (Hsf_conn k).
      rewrite -Hsfct Hsf_conn.
      rewrite /extend_map_with CEP.Lemmas.map2_1bis //
              /combine_when_connections CEP.Lemmas.map2_1bis //
              /extend_defined_map_with CEP.Lemmas.map2_1bis // CEP.Lemmas.map2_1bis //.
      destruct IHsst as [_ [_ IHsst]] ; specialize (IHsst k).
      rewrite /extend_defined_map_with CEP.Lemmas.map2_1bis //
              /extend_map_with CEP.Lemmas.map2_1bis // in IHsst.
      destruct IHssf as [_ [_ IHssf]] ; specialize (IHssf k).
      rewrite /extend_defined_map_with CEP.Lemmas.map2_1bis // CEP.Lemmas.map2_1bis //
              /extend_map_with CEP.Lemmas.map2_1bis // CEP.Lemmas.map2_1bis // CEP.Lemmas.map2_1bis // CEP.Lemmas.map2_1bis // CEP.Lemmas.map2_1bis // in IHssf.
      destruct (CEP.find k eb_connmap_t) as [[| |eb_expr_t]|] eqn: Heb_cm_t,
               (CEP.find k eb_connmap_f) as [[| |eb_expr_f]|] eqn: Heb_cm_f ;
            try by reflexivity.
      (* Now a number of goals have that one of the connmaps in D_undefined. Then ct_comp should also be D_undefined. *)
      * destruct Haft_comp_f as [[_ [Hebcmf_sub_ctc _]] _] ;
        specialize (Hebcmf_sub_ctc k) ; rewrite Heb_cm_f in Hebcmf_sub_ctc.
        destruct Hsf_comp_sub_t as [_ [_ Hsf_comp_sub_t]] ; specialize (Hsf_comp_sub_t k) ;
        destruct Hsf_comp_sub_f as [_ [_ Hsf_comp_sub_f]] ; specialize (Hsf_comp_sub_f k).
        destruct (CEP.find k ct_comp_t) as [[]|] eqn: Hctct ;
        try (by discriminate (IHsst _ Logic.eq_refl)).
        + by rewrite (Hsf_comp_sub_f _ Logic.eq_refl) //.
        + destruct (CEP.find k old_ct) ; try (by discriminate (Hsf_comp_sub_t _ Logic.eq_refl)).
          destruct (CEP.find k ct_comp) as [[]|] ; last (by discriminate Hebcmf_sub_ctc) ;
          try (by discriminate (IHssf _ Logic.eq_refl)).
          by reflexivity.
      * 1-3: destruct Haft_comp_t as [[_ [Hebcmt_sub_ctct _]] _] ;
             specialize (Hebcmt_sub_ctct k) ; rewrite Heb_cm_t in Hebcmt_sub_ctct ;
             destruct Hsf_comp_sub_f as [_ [_ Hsf_comp_sub_f]] ; specialize (Hsf_comp_sub_f k) ;
             destruct (CEP.find k ct_comp_t) ; last (by discriminate Hebcmt_sub_ctct) ;
             rewrite (Hsf_comp_sub_f _ Logic.eq_refl) ;
             apply IHsst ; by reflexivity.
      * 1,2: generalize (CEP.Lemmas.submap_trans (proj2 (proj2 Hsf_comp_sub_t)) (proj2 (proj2 Hsf_comp_sub_f)) k) ; intro H ;
        destruct (PVM.find k old_ct) as [[]|] ; try (by discriminate (IHssf _ Logic.eq_refl)) ;
        by rewrite (H _ Logic.eq_refl) //.
      * destruct (eb_expr_t == eb_expr_f) ; by reflexivity.
      * destruct Haft_comp_f as [[_ [Hebcmf_sub_ctc _]] _] ;
        specialize (Hebcmf_sub_ctc k) ; rewrite Heb_cm_f in Hebcmf_sub_ctc.
        destruct Hsf_comp_sub_t as [_ [_ Hsf_comp_sub_t]] ; specialize (Hsf_comp_sub_t k) ;
        destruct Hsf_comp_sub_f as [_ [_ Hsf_comp_sub_f]] ; specialize (Hsf_comp_sub_f k).
        destruct (CEP.find k old_ct) as [[]|] eqn: Holdct ;
        try (by discriminate (IHssf _ Logic.eq_refl)).
        + by rewrite (Hsf_comp_sub_f _ (Hsf_comp_sub_t _ Logic.eq_refl)) //.
        + destruct (CEP.find k ct_comp_t) ; try (by discriminate (IHsst _ Logic.eq_refl)).
          destruct (CEP.find k ct_comp) as [[]|] ; last (by discriminate Hebcmf_sub_ctc) ;
          try (by discriminate (IHssf _ Logic.eq_refl)).
          by reflexivity.
      * destruct Hsf_comp_sub_t as [_ [_ Hsf_comp_sub_t]] ; specialize (Hsf_comp_sub_t k).
        destruct Hsf_comp_sub_f as [_ [_ Hsf_comp_sub_f]] ; specialize (Hsf_comp_sub_f k).
        destruct (CEP.find k old_ct) ;
              first by rewrite (Hsf_comp_sub_f _ (Hsf_comp_sub_t _ Logic.eq_refl)) //.
        destruct (CEP.find k ct_comp_t) ; first by discriminate (IHsst _ Logic.eq_refl).
        destruct (CEP.find k ct_comp) ; first by discriminate (IHssf _ Logic.eq_refl).
        by reflexivity.
  + destruct Haft_comp_t as [Haft_comp_t Holdcm_sub_cmt].
    destruct Haft_comp_f as [Haft_comp_f Holdcm_sub_cmf].
    split.
    - intro k ; rewrite CEP.Lemmas.empty_o //.
    destruct Haft as [_ Haft], Haft_comp_t as [_ Haft_comp_t], Haft_comp_f as [_ Haft_comp_f] ;
    split.
    - destruct Haft_comp_t as [Haft_comp_t _], Haft_comp_f as [Haft_comp_f _].
      intro k.
      specialize (Haft_comp_t k) ; specialize (Haft_comp_f k).
      destruct Hsf_comp_sub_f as [_ [_ Hsf_comp_sub_f]] ; specialize (Hsf_comp_sub_f k).
      destruct (CEP.find k ct_comp) ; first by trivial.
      destruct (CEP.find k ct_comp_t) ; first by discriminate (Hsf_comp_sub_f _ Logic.eq_refl).
      by rewrite /combine_when_connections CEP.Lemmas.map2_1bis // Haft_comp_t Haft_comp_f //.
    destruct Haft as [_ Haft], Haft_comp_t as [_ Haft_comp_t], Haft_comp_f as [_ Haft_comp_f] ;
    split.
    - destruct Haft_comp_t as [Haft_comp_t _], Haft_comp_f as [Haft_comp_f _].
      intro k.
      specialize (Haft_comp_t k) ; specialize (Haft_comp_f k).
      destruct Hsf_comp_sub_f as [_ [_ Hsf_comp_sub_f]] ; specialize (Hsf_comp_sub_f k).
      destruct (CEP.find k ct_comp) as [[| |ctc_expr]|] ; try done.
      (* almost Haft_comp_f; there is a difference between tm_tmap and tmap *)
      generalize (type_of_expr_submap ctc_expr tm_tmap tmap Htm_tm_sub_tm) ; intro.
      destruct (type_of_expr ctc_expr tm_tmap) as [ft|] ;
              last by destruct (CEP.find k vm_comp) as [[gt|gt|gt|gt|gt]|] ; done.
      by rewrite H //.
    destruct Haft as [_ Haft], Haft_comp_t as [_ Haft_comp_t], Haft_comp_f as [_ Haft_comp_f] ;
    split.
    - destruct Haft_comp_t as [Haft_comp_t _], Haft_comp_f as [Haft_comp_f _].
      intro k.
      specialize (Haft_comp_t k) ; specialize (Haft_comp_f k).
      (* almost Haft_comp_f; there is a difference between tm_tmap and tmap *)
      specialize (Htm_tm_sub_tm k).
      destruct (CEP.find k vm_comp) as [[gt|gt|gt|gt|gt]|] ; try (by trivial) ;
      by rewrite (Htm_tm_sub_tm _ Haft_comp_f) //.
    destruct Haft as [_ Haft], Haft_comp_t as [_ Haft_comp_t], Haft_comp_f as [_ Haft_comp_f] ;
    split.
    - intro k ; rewrite CEP.Lemmas.empty_o //.
    - destruct Haft_comp_t as [_ Haft_comp_t], Haft_comp_f as [_ Haft_comp_f].
      intro k.
      specialize (Haft_comp_t k) ; specialize (Haft_comp_f k).
      rewrite /combine_when_connections CEP.Lemmas.map2_1bis //.
      destruct (CEP.find k eb_connmap_t) as [[| |eb_expr_t]|] eqn: Heb_cm_t.
      * specialize (Htmt_sub_tm k).
        destruct (CEP.find k tm_tmap_t) as [[ft [| | | |]]|] ; try (by contradiction Haft_comp_t) ;
        by rewrite (Htmt_sub_tm _ Logic.eq_refl) //.
      * (* similar to Haft_comp_f, I think *)
        destruct (CEP.find k eb_connmap_f) as [[| |eb_expr_f]|] eqn: Heb_cm_f.
        + 1,2: specialize (Htm_tm_sub_tm k) ;
               destruct (CEP.find k tm_tmap) as [[ft [| | | |]]|] ; try (by contradiction Haft_comp_f) ;
               by rewrite (Htm_tm_sub_tm _ Logic.eq_refl) //.
        + generalize (type_of_expr_submap eb_expr_f tm_tmap tmap Htm_tm_sub_tm) ; intro.
          destruct (type_of_expr eb_expr_f tm_tmap) as [[[gt_expr| |] Hgt_expr_inf]|] ; try by contradiction Haft_comp_f.
          rewrite H ; clear H.
          specialize (Htm_tm_sub_tm k).
          destruct (CEP.find k tm_tmap) as [[[gt_ref| |] [| | | |]]|] ; try (by contradiction Haft_comp_f) ;
          by rewrite (Htm_tm_sub_tm _ Logic.eq_refl) //.
        + (* similar to Haft_comp_t actually *)
          specialize (Htmt_sub_tm k).
          destruct (CEP.find k tm_tmap_t) as [[ft [| | | |]]|] ; try (by contradiction Haft_comp_t) ;
          by rewrite (Htmt_sub_tm _ Logic.eq_refl) //.
      * destruct (CEP.find k eb_connmap_f) as [[| |eb_expr_f]|] eqn: Heb_cm_f.
        + specialize (Htm_tm_sub_tm k).
          destruct (CEP.find k tm_tmap) as [[ft [| | | |]]|] ; try (by contradiction Haft_comp_f) ;
          by rewrite (Htm_tm_sub_tm _ Logic.eq_refl) //.
        + 2: destruct (eb_expr_t == eb_expr_f).
        + 1,2: generalize (type_of_expr_submap eb_expr_t tm_tmap_t tmap Htmt_sub_tm) ; intro.
          1,2: destruct (type_of_expr eb_expr_t tm_tmap_t) as [[[gt_expr| |] Hgt_expr_inf]|] ; try by contradiction Haft_comp_t.
          1,2: rewrite H ; clear H.
          1,2: specialize (Htmt_sub_tm k).
          1,2: destruct (CEP.find k tm_tmap_t) as [[[gt_ref| |] [| | | |]]|] ; try (by contradiction Haft_comp_t) ;
               by rewrite (Htmt_sub_tm _ Logic.eq_refl) //.
        + simpl type_of_expr.
          generalize (type_of_expr_submap cond old_scope tmap (CEP.Lemmas.submap_trans Hsc_tm Holdtm_sub_tm)) ; intro.
          rewrite Htyp_cond in H ; rewrite H ; clear H.
          generalize (type_of_expr_submap eb_expr_t tm_tmap_t tmap Htmt_sub_tm) ; intro.
          destruct (type_of_expr eb_expr_t tm_tmap_t) as [[[gt_expr_t| |] Hgt_expr_t_inf]|] ; try by contradiction Haft_comp_t.
          rewrite H ; clear H.
          generalize (type_of_expr_submap eb_expr_f tm_tmap tmap Htm_tm_sub_tm) ; intro.
          destruct (type_of_expr eb_expr_f tm_tmap) as [[[gt_expr_f| |] Hgt_expr_f_inf]|] ; try by contradiction Haft_comp_f.
          rewrite H /ftype_mux /sval /proj2_sig /ftype_mux' ; clear H.
          destruct Hst_f as [_ [Hst_f _]] ; specialize (Hst_f k) ; specialize (Htm_tm_sub_tm k).
          specialize (Htm_inf k).
          destruct (CEP.find k tm_tmap_t) as [[[gt_ref| |] [| | | |]]|] ; try (by contradiction Haft_comp_t) ;
          specialize (Hst_f _ Logic.eq_refl) ; rewrite Hst_f in Haft_comp_f ;
          rewrite (Htm_tm_sub_tm _ Hst_f) ; rewrite (Htm_tm_sub_tm _ Hst_f) in Htm_inf ;
          destruct gt_expr_t, gt_expr_f, gt_ref ; simpl ; done.
        + generalize (type_of_expr_submap eb_expr_t tm_tmap_t tmap Htmt_sub_tm) ; intro.
          destruct (type_of_expr eb_expr_t tm_tmap_t) as [[[gt_expr| |] Hgt_expr_inf]|] ; try by contradiction Haft_comp_t.
          rewrite H ; clear H.
          specialize (Htmt_sub_tm k).
          destruct (CEP.find k tm_tmap_t) as [[[gt_ref| |] [| | | |]]|] ; try (by contradiction Haft_comp_t) ;
          by rewrite (Htmt_sub_tm _ Logic.eq_refl) //.
      * destruct (CEP.find k eb_connmap_f) as [[| |eb_expr_f]|] eqn: Heb_cm_f ; try by done.
        + 1,2: specialize (Htm_tm_sub_tm k) ;
               destruct (CEP.find k tm_tmap) as [[ft [| | | |]]|] ; try (by contradiction Haft_comp_f) ;
               by rewrite (Htm_tm_sub_tm _ Logic.eq_refl) //.
        + generalize (type_of_expr_submap eb_expr_f tm_tmap tmap Htm_tm_sub_tm) ; intro.
          destruct (type_of_expr eb_expr_f tm_tmap) as [[[gt_expr| |] Hgt_expr_inf]|] ;
                  try by contradiction Haft_comp_f.
          rewrite H ; clear H.
          specialize (Htm_tm_sub_tm k).
          destruct (CEP.find k tm_tmap) as [[[gt_ref| |] [| | | |]]|] ; try (by contradiction Haft_comp_f) ;
          by rewrite (Htm_tm_sub_tm _ Logic.eq_refl) //.
* admit.
Admitted.

Lemma ports_fit_together :
forall (vm_for_tmap : CEP.t vertex_type) (m_ports : seq HiFP.hfport)
       (pmap port_scope tmap : CEP.t (ftype * HiF.forient)) (port_ct ct : CEP.t def_expr)
       (vm : CEP.t vertex_type),
        ports_have_fully_inferred_ground_types m_ports
    ->
        ports_tmap m_ports vm_for_tmap = Some pmap
    ->
        ExpandPorts_fun m_ports = Some (port_ct, port_scope)
    ->
        Sem_frag_ports (CEP.empty vertex_type) (CEP.empty def_expr) m_ports vm ct tmap
    ->
        CEP.submap pmap tmap
    ->
            pmap = port_scope
        /\
            CEP.Equal port_ct ct
        /\
            all_fit_together port_scope port_ct ct vm pmap.
Proof.
induction m_ports as [|p pp] ; simpl ; intros pmap port_scope tmap port_ct ct vm Hpp_inf Htm Hep Hsf Hpm_sub_tm.
* injection Htm ; clear Htm ; intros ; subst pmap.
  injection Hep ; clear Hep ; intros ; subst port_ct port_scope.
  destruct Hsf ; subst vm ct.
  split ; first by reflexivity.
  split ; first by apply CEP.Lemmas.Equal_refl.
  split.
  * intro k ; by rewrite CEP.Lemmas.empty_o //.
  split.
  * intro k ; by rewrite CEP.Lemmas.empty_o //.
  split.
  * intro k ; by rewrite CEP.Lemmas.empty_o //.
  split.
  * intro k ; by rewrite CEP.Lemmas.empty_o //.
  split.
  * intro k ; by rewrite CEP.Lemmas.empty_o //.
  * intro k ; by rewrite CEP.Lemmas.empty_o //.
* move /andP : Hpp_inf => [Hp_inf Hpp_inf].
  destruct p as [var ft|var ft] ; simpl in Hp_inf ; destruct ft as [gt| |] ; try by discriminate Hp_inf.
  1,2: generalize (fully_inferred_does_not_change gt var vm_for_tmap Hp_inf) ; intro ;
       destruct (code_type_find_vm_widths (Gtyp gt) var vm_for_tmap) as [[[gt'| |] _]|] ;
             last (by discriminate Htm) ;
             try (by contradiction H) ;
       subst gt'.
  1,2: destruct (ports_tmap pp vm_for_tmap) as [old_pmap|] ;
             last (by discriminate Htm) ;
       specialize IHpp with (1 := Hpp_inf) (2 := Logic.eq_refl).
  1,2: destruct (CEP.find var old_pmap) eqn: Hfind_var ;
             first (by discriminate Htm) ;
       injection Htm ; clear Htm ; intros ; subst pmap.
  1,2: destruct (ExpandPorts_fun pp) as [[old_ct old_scope]|] ;
             last (by discriminate Hep) ;
       specialize IHpp with (1 := Logic.eq_refl) ;
       injection Hep ; clear Hep ; intros ; subst port_ct port_scope.
  1,2: destruct Hsf as [vm_temp [ct_temp [Hsf_pp Hsf_p]]].
  1,2: specialize IHpp with (1 := Hsf_pp) (2 := CEP.Lemmas.submap_add_find_none Hpm_sub_tm Hfind_var).
  1,2: destruct IHpp as [IHpp' IHpp] ; subst old_scope.
  1,2: simpl in Hsf_p ;
       specialize (Hpm_sub_tm var) ;
       rewrite (CEP.Lemmas.find_add_eq (eqxx _)) in Hpm_sub_tm ;
       specialize (Hpm_sub_tm _ Logic.eq_refl) ;
       rewrite Hpm_sub_tm in Hsf_p.
  1,2: split ; first by reflexivity.
  1,2: split.
  + 1,3: intro k ; destruct (k == var) eqn: Hkvar.
    - 1,3: destruct Hsf_p as [Hsf_p _] ;
           rewrite /connect_port in Hsf_p ;
           move /andP : Hsf_p => [_ /andP [/eqP Hct_temp /eqP Hct]].
      1: by rewrite (elimT eqP Hkvar) (proj1 IHpp) Hct_temp Hct //.
      1: by rewrite (CEP.Lemmas.find_add_eq Hkvar) (elimT eqP Hkvar) Hct //.
    - 1,2: destruct Hsf_p as [_ Hsf_p] ;
           specialize (Hsf_p k.1 k.2 (Hneq_12small_large _ _ Hkvar)) ;
           rewrite -surjective_pairing in Hsf_p.
      2: rewrite (CEP.Lemmas.find_add_neq (elimT negP (negbT Hkvar))).
      1,2: by rewrite (proj1 IHpp) (proj2 Hsf_p) //.
  + 1,2: destruct IHpp as [Holdct_eq_ctt IHpp] ;
         split.
    - 1,3: intro k ; destruct IHpp as [IHpp [_ [_ [_ [_ Holdct_sub_tm]]]]] ; specialize (IHpp k).
      1,2: destruct (k == var) eqn: Hkvar.
      * 1,3: rewrite (CEP.Lemmas.find_add_eq Hkvar) // (elimT eqP Hkvar).
        1: specialize (Holdct_sub_tm var) ;
           rewrite Hfind_var in Holdct_sub_tm ;
           destruct (CEP.find var old_ct) as [[| |oldct_expr]|] ; try done ;
           destruct (type_of_expr oldct_expr old_pmap) as [[[| |] _]|] ;
           by contradiction Holdct_sub_tm.
        1: by rewrite (CEP.Lemmas.find_add_eq (eqxx _)) //.
      * 1,2: rewrite (CEP.Lemmas.find_add_neq (elimT negP (negbT Hkvar))).
        1: destruct (CEP.find k old_pmap) as [[ft_tgt [| | | |]]|] ; try done ;
           destruct (CEP.find k old_ct) as [[| |oldct_expr]|] ; try done ;
           generalize (type_of_expr_submap oldct_expr old_pmap (CEP.add var (Gtyp gt, HiF.Source) old_pmap) (CEP.Lemmas.submap_none_add (Gtyp gt, HiF.Source) (CEP.Lemmas.submap_refl old_pmap) Hfind_var)) ;
           intro H ;
           destruct (type_of_expr oldct_expr old_pmap) ; try done ;
           by rewrite H //.
        1: destruct (CEP.find k old_pmap) as [[ft_tgt [| | | |]]|] ; try done ;
           rewrite (CEP.Lemmas.find_add_neq (elimT negP (negbT Hkvar))) ;
           destruct (CEP.find k old_ct) as [[| |oldct_expr]|] ; try done ;
           generalize (type_of_expr_submap oldct_expr old_pmap (CEP.add var (Gtyp gt, HiF.Sink) old_pmap) (CEP.Lemmas.submap_none_add (Gtyp gt, HiF.Sink) (CEP.Lemmas.submap_refl old_pmap) Hfind_var)) ;
           intro H ;
           destruct (type_of_expr oldct_expr old_pmap) ; try done ;
           by rewrite H //.
  + 1,2: destruct IHpp as [_ IHpp] ;
         split.
    1,3: intro k ; destruct IHpp as [IHpp [_ [_ [_ Holdct_sub_tm]]]] ; specialize (IHpp k) ;
         destruct (k == var) eqn: Hkvar.
    - 1,3: destruct Hsf_p as [Hsf_p _] ;
           rewrite /connect_port in Hsf_p ;
           move /andP : Hsf_p => [_ /andP [/eqP Hct_temp /eqP Hct]].
      1: rewrite (elimT eqP Hkvar) Hct_temp in IHpp ;
         destruct (CEP.find k ct) as [|] ; by rewrite // (elimT eqP Hkvar) //.
      1: by rewrite (elimT eqP Hkvar) Hct //.
    - 1,2: destruct Hsf_p as [_ Hsf_p] ;
           specialize (Hsf_p k.1 k.2 (Hneq_12small_large _ _ Hkvar)) ;
           rewrite -surjective_pairing in Hsf_p.
      1,2: rewrite -(proj2 Hsf_p) // (CEP.Lemmas.find_add_neq (elimT negP (negbT Hkvar))) //.
  + 1,2: destruct IHpp as [_ IHpp] ;
         split.
    1,3: intro k ; destruct IHpp as [IHpp _] ; specialize (IHpp k) ;
         destruct (k == var) eqn: Hkvar.
    - 1,3: destruct Hsf_p as [Hsf_p _] ; simpl in Hsf_p ;
           move /andP : Hsf_p => [/andP [_ /eqP Hvm] /andP [_ /eqP Hct]] ;
           by rewrite (elimT eqP Hkvar) Hvm Hct //.
    - 1,2: destruct Hsf_p as [_ Hsf_p] ; specialize (Hsf_p k.1 k.2 (Hneq_12small_large _ _ Hkvar)) ;
           rewrite -surjective_pairing in Hsf_p ;
           rewrite -(proj1 Hsf_p) -(proj2 Hsf_p).
      1,2: destruct (CEP.find k ct_temp) as [[| |ctt_expr]|] ; try done.
      1: generalize (type_of_expr_submap ctt_expr old_pmap (CEP.add var (Gtyp gt, HiF.Source) old_pmap)) ; intro H.
      2: generalize (type_of_expr_submap ctt_expr old_pmap (CEP.add var (Gtyp gt, HiF.Sink) old_pmap)) ; intro H.
      1,2: specialize (H (CEP.Lemmas.submap_none_add (Gtyp gt, _) (CEP.Lemmas.submap_refl old_pmap) Hfind_var)).
      1,2: destruct (type_of_expr ctt_expr old_pmap) as [[[gt_expr| |] Hgt_expr_exp]|] ;
                 try (by destruct (CEP.find k vm_temp) as [[]|] ; contradiction IHpp).
      1,2: rewrite H ; clear H.
      1,2: destruct (CEP.find k vm_temp) as [[gt'|gt'|gt'|gt'|gt']|] ; done.
  + 1,2: destruct IHpp as [_ IHpp] ;
         split.
    1,3: intro k ; destruct IHpp as [IHpp _] ; specialize (IHpp k) ;
         destruct (k == var) eqn: Hkvar.
    - 1,3: rewrite (CEP.Lemmas.find_add_eq Hkvar).
      1,2: destruct Hsf_p as [Hsf_p _] ; simpl in Hsf_p ;
           move /andP : Hsf_p => [/andP [_ /eqP Hvm] _] ;
           rewrite (elimT eqP Hkvar) Hvm //.
    - 1,2: rewrite (CEP.Lemmas.find_add_neq (elimT negP (negbT Hkvar))).
      1,2: destruct Hsf_p as [_ Hsf_p] ; specialize (Hsf_p k.1 k.2 (Hneq_12small_large _ _ Hkvar)) ;
           rewrite -surjective_pairing in Hsf_p ;
           by rewrite -(proj1 Hsf_p) //.
  + 1,2: destruct IHpp as [_ IHpp] ;
         split.
    1,3: intro k ; destruct IHpp as [IHpp _] ; specialize (IHpp k) ;
         destruct (k == var) eqn: Hkvar.
    - 1,3: destruct Hsf_p as [Hsf_p _] ; simpl in Hsf_p ;
           move /andP : Hsf_p => [/andP [_ /eqP Hvm] _] ;
           by rewrite (CEP.Lemmas.find_add_eq Hkvar) (elimT eqP Hkvar) Hvm //.
    - 1,2: destruct Hsf_p as [_ Hsf_p] ; specialize (Hsf_p k.1 k.2 (Hneq_12small_large _ _ Hkvar)) ;
           rewrite -surjective_pairing in Hsf_p ;
           by rewrite (CEP.Lemmas.find_add_neq (elimT negP (negbT Hkvar))) -(proj1 Hsf_p) //.
  + 1,2: destruct IHpp as [_ IHpp] ; intro k ; specialize (IHpp k) ;
         destruct (k == var) eqn: Hkvar.
    - 1,3: move /eqP : Hkvar => Hkvar ; subst k.
      1,2: rewrite Hfind_var in IHpp.
      1: destruct (CEP.find var old_ct) as [[| |oldct_expr]|] ; try done ;
         destruct (type_of_expr oldct_expr old_pmap) as [[[| |] _]|] ; done.
      1: by rewrite (CEP.Lemmas.find_add_eq (eqxx _)) (CEP.Lemmas.find_add_eq (eqxx _)) //.
    - 2: rewrite (CEP.Lemmas.find_add_neq (elimT negP (negbT Hkvar))).
      1,2: rewrite (CEP.Lemmas.find_add_neq (elimT negP (negbT Hkvar))).
      1,2: destruct (CEP.find k old_ct) as [[| |oldct_expr]|] ; try done.
      1: generalize (type_of_expr_submap oldct_expr old_pmap (CEP.add var (Gtyp gt, HiF.Source) old_pmap)) ; intro H.
      2: generalize (type_of_expr_submap oldct_expr old_pmap (CEP.add var (Gtyp gt, HiF.Sink) old_pmap)) ; intro H.
      1,2: specialize (H (CEP.Lemmas.submap_none_add (Gtyp gt, _) (CEP.Lemmas.submap_refl old_pmap) Hfind_var)).
      1,2: destruct (type_of_expr oldct_expr old_pmap) as [[[gt_expr| |] Hgt_expr_exp]|] ; try done.
      1,2: by rewrite H //.
Qed.

Lemma ExpandBranch_stmt_tmap :
(* When comparing stmt_tmap and ExpandBranch_fun:
   if the first function gets a larger scope as input,
   it will produce a larger scope as output.

   This lemma is used by the next theorem (ExpandBranch_funs_checks_scopes). *)
forall (vm : CEP.t vertex_type) (s : HiFP.hfstmt)
       (old_tmap new_tmap old_scope1 new_scope1 old_scope2 new_scope2 : CEP.t (ftype * HiF.forient))
       (old_conn_map new_conn_map : CEP.t def_expr),
   stmt_tmap (old_tmap, old_scope1) s vm = Some (new_tmap, new_scope1) ->
   ExpandBranch_fun s old_conn_map old_scope2 = Some (new_conn_map, new_scope2) ->
   CEP.submap old_scope2 old_scope1 ->
   stmt_has_fully_inferred_ground_types s ->
      CEP.submap new_scope2 new_scope1
with ExpandBranch_stmts_tmap :
forall (vm : CEP.t vertex_type) (ss : HiFP.hfstmt_seq)
       (old_tmap new_tmap old_scope1 new_scope1 old_scope2 new_scope2 : CEP.t (ftype * HiF.forient))
       (old_conn_map new_conn_map : CEP.t def_expr),
   stmts_tmap (old_tmap, old_scope1) ss vm = Some (new_tmap, new_scope1) ->
   ExpandBranches_funs ss old_conn_map old_scope2 = Some (new_conn_map, new_scope2) ->
   CEP.submap old_scope2 old_scope1 ->
   stmts_have_fully_inferred_ground_types ss ->
      CEP.submap new_scope2 new_scope1.
Proof.
* clear ExpandBranch_stmt_tmap.
  destruct s as [|var ft|var reg|var mem|var1 var2|var expr|ref expr|ref|cond sst ssf] ;
  simpl ; intros old_tmap new_tmap old_scope1 new_scope1 old_scope2 new_scope2 old_conn_map new_conn_map Htm Heb Holdsc2_sub_oldsc1 Hs_inf.
  + (* Sskip *)
    injection Htm ; clear Htm ; intros ; subst new_scope1 new_tmap.
    injection Heb ; clear Heb ; intros ; subst new_scope2 new_conn_map.
    by exact Holdsc2_sub_oldsc1.
  + (* Swire *)
    destruct (CEP.find var old_scope2) ; first by discriminate Heb.
    injection Heb ; clear Heb ; intros ; subst new_conn_map new_scope2.
    destruct ft as [gt| |] ; try by discriminate Hs_inf.
    destruct (CEP.find var old_tmap) ; first by discriminate Htm.
    generalize (fully_inferred_does_not_change gt var vm Hs_inf) ;
          intro.
    destruct (code_type_find_vm_widths (Gtyp gt) var vm) as [[[gt'| |] _]|]; try done.
    subst gt'.
    injection Htm ; clear Htm ; intros ; subst new_tmap new_scope1.
    apply submap_add_add, Holdsc2_sub_oldsc1.
  + (* Sreg *)
    destruct (type reg) as [gt| |] ; try done.
    destruct (CEP.find var old_scope2) ; first by discriminate Heb.
    destruct (CEP.find var old_tmap) ; first by discriminate Htm.
    destruct (type_of_expr (clock reg) old_scope2) as [_|] ; last by discriminate Heb.
    destruct (type_of_expr (clock reg) old_scope1) as [_|] ; last by discriminate Htm.
    destruct (reset reg) as [|rst_sig rst_val] ; last first.
    1,2: move /andP : Hs_inf => [_ Hs_inf].
    1,2: generalize (fully_inferred_does_not_change gt var vm Hs_inf) ;
          intro.
    1,2: destruct (code_type_find_vm_widths (Gtyp gt) var vm) as [[[gt'| |] _]|] ; try done ;
         subst gt'.
    1: generalize (type_of_expr_submap rst_sig old_scope2 old_scope1 Holdsc2_sub_oldsc1) ; intro.
    1: destruct (type_of_expr rst_sig old_scope2) as [[[[[|[]]| | | | | |]| |] Hrst_sig_inf]|] ; try by discriminate Heb.
    1,2: rewrite H in Htm ; clear H.
    1: destruct (type_of_expr rst_val (CEP.add var (Gtyp gt, HiF.Duplex) old_scope2)) as [_|] ; last by discriminate Heb.
    1: destruct (type_of_expr rst_val (CEP.add var (Gtyp gt, HiF.Duplex) old_scope1)) as [_|] ; last by discriminate Htm.
    2: destruct (type_of_expr rst_val old_scope2) as [_|] ; last by discriminate Heb.
    2: destruct (type_of_expr rst_val old_scope1) as [_|] ; last by discriminate Htm.
    1-3: injection Heb ; clear Heb ; intros ; subst new_conn_map new_scope2.
    1-3: injection Htm ; clear Htm ; intros ; subst new_tmap new_scope1.
    1-3: by apply submap_add_add, Holdsc2_sub_oldsc1.
  + (* Smem *)
    by discriminate Htm.
  + (* Sinst *)
    by discriminate Htm.
  + (* Snode *)
    destruct (CEP.find var old_tmap) ; first by discriminate Htm.
    destruct (CEP.find var old_scope2) ; first by discriminate Heb.
    generalize (type_of_expr_submap expr old_scope2 old_scope1 Holdsc2_sub_oldsc1) ;
          intro.
    destruct (type_of_expr expr old_scope1) as [[ft1 p1]|] ; last by discriminate Htm.
    destruct (type_of_expr expr old_scope2) as [[ft2 p2]|] ; last by discriminate Heb.
    injection H ; clear H ; intros ; subst ft2 ; clear p2.
    injection Htm ; clear Htm ; intros ; subst new_tmap new_scope1.
    injection Heb ; clear Heb ; intros ; subst new_conn_map new_scope2.
    by apply submap_add_add, Holdsc2_sub_oldsc1.
  + (* Sfcnct *)
    destruct (type_of_ref ref old_scope1) ; last by discriminate Htm.
    destruct (type_of_expr expr old_scope1) ; last by discriminate Htm.
    injection Htm ; clear Htm ; intros ; subst new_tmap new_scope1.
    destruct ref as [var| | |] ; try by discriminate Heb.
    destruct (CEP.find var old_scope2) as [[[gt_ref| |] [| | | |]]|] ; try by discriminate Heb.
    1,2: destruct (type_of_expr expr old_scope2) as [[[gt_expr| |] _]|] ; try by discriminate Heb.
    1,2: destruct (match gt_ref with
                   | Fuint _ => match gt_expr with | Fuint _ | Fuint_implicit _ => true | _ => false end
                   | Fsint _ => match gt_expr with | Fsint _ | Fsint_implicit _ => true | _ => false end
                   | Fuint_implicit w_tgt => match gt_expr with | Fuint w_src | Fuint_implicit w_src => w_src <= w_tgt | _ => false end
                   | Fsint_implicit w_tgt => match gt_expr with | Fsint w_src | Fsint_implicit w_src => w_src <= w_tgt | _ => false end
                   | Fclock => match gt_expr with | Fclock => true | _ => false end
                   | Freset => false
                   | Fasyncreset => match gt_expr with | Fasyncreset => true | _ => false end
                   end) ; last by discriminate Heb.
    1,2: injection Heb ; clear Heb ; intros ; subst new_conn_map new_scope2.
    1,2: by exact Holdsc2_sub_oldsc1.
  + (* Sinvalid *)
    destruct (type_of_ref ref old_scope1) ; last by discriminate Htm.
    injection Htm ; clear Htm ; intros ; subst new_tmap new_scope1.
    destruct ref as [var| | |] ; try by discriminate Heb.
    destruct (CEP.find var old_scope2) as [[_ [| | | |]]|]; try by discriminate Heb.
    1,2: injection Heb ; clear Heb ; intros ; subst new_conn_map new_scope2.
    1,2: by exact Holdsc2_sub_oldsc1.
  + (* Swhen *)
    destruct (type_of_expr cond old_scope1) ; last by discriminate Htm.
    destruct (type_of_expr cond old_scope2) as [[[[[|[|]]| | | | | |]| |] _]|] ; try by discriminate Heb.
    destruct (stmts_tmap (old_tmap, old_scope1) sst vm) as [[tmap_true scope1_true]|] ; last by discriminate Htm.
    destruct (ExpandBranches_funs sst old_conn_map old_scope2) as [[true_conn_map true_scope2]|] ; last by discriminate Heb.
    destruct (stmts_tmap (tmap_true, old_scope1) ssf vm) as [[tmap_false scope1_false]|] ; last by discriminate Htm.
    injection Htm ; clear Htm ; intros ; subst new_tmap new_scope1.
    destruct (ExpandBranches_funs ssf old_conn_map old_scope2) as [[false_conn_map false_scope2]|] ; last by discriminate Heb.
    injection Heb ; clear Heb ; intros ; subst new_conn_map new_scope2.
    by exact Holdsc2_sub_oldsc1.
* clear ExpandBranch_stmts_tmap.
  induction ss as [|s ss] ; simpl ;
  intros old_tmap new_tmap old_scope1 new_scope1 old_scope2 new_scope2 old_conn_map new_conn_map Htm Heb Holdsc2_sub_oldsc1 Hss_inf.
  + injection Htm ; clear Htm ; intros ; subst new_tmap new_scope1.
    injection Heb ; clear Heb ; intros ; subst new_conn_map new_scope2.
    by exact Holdsc2_sub_oldsc1.
  + rename ExpandBranch_stmt_tmap into IHs.
    move /andP : Hss_inf => [Hs_inf Hss_inf].
    specialize (IHs vm s old_tmap)
          with (old_scope1 := old_scope1) (old_scope2 := old_scope2) (old_conn_map := old_conn_map).
    destruct (stmt_tmap (old_tmap, old_scope1) s vm) as [[tmap' scope']|] ; last by discriminate Htm.
    specialize IHs with (new_tmap := tmap') (new_scope1 := scope').
    destruct (ExpandBranch_fun s old_conn_map old_scope2) as [[temp_conn_map temp_scope]|]; last by discriminate Heb.
    specialize (IHs temp_scope temp_conn_map Logic.eq_refl Logic.eq_refl Holdsc2_sub_oldsc1 Hs_inf).
    by apply (IHss tmap' new_tmap scope' new_scope1 temp_scope new_scope2 temp_conn_map new_conn_map
                   Htm Heb IHs Hss_inf).
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
            forall (old_conn_map : CEP.t def_expr) (old_scope : CEP.t (ftype * HiF.forient)),
               CEP.submap old_scope scope1 ->
                  ExpandBranches_funs ss old_conn_map old_scope = None
with ExpandBranch_fun_checks_scopes :
forall (s : HiFP.hfstmt) (tmap scope1 scope2 : CEP.t (ftype * HiF.forient)) (vm : CEP.t vertex_type),
   stmt_has_fully_inferred_ground_types s ->
   tmap_has_fully_inferred_ground_types tmap ->
   CEP.submap scope1 tmap ->
   CEP.submap scope2 tmap ->
   CEP.submap scope1 scope2 ->
      stmt_tmap (tmap, scope1) s vm = None ->
         stmts_tmap (tmap, scope2) (component_stmt_of s) vm <> None ->
            forall (old_conn_map : CEP.t def_expr) (old_scope : CEP.t (ftype * HiF.forient)),
               CEP.submap old_scope scope1 ->
                  ExpandBranch_fun s old_conn_map old_scope (* or scope1? *) = None.
Proof.
* clear ExpandBranch_funs_checks_scopes.
  induction ss as [|s ss] ; simpl ; intros tmap scope1 scope2 vm Hss_inf Htm_inf Hsc1_sub_tm Hsc2_sub_tm Hsc1_sub_sc2 Htm_ss Htm_comp_ss old_conn_map old_scope Holdsc_sub_sc1.
  + by discriminate Htm_ss.
  + rename ExpandBranch_fun_checks_scopes into IHs.
    move /andP : Hss_inf => [Hs_inf Hss_inf].
    rewrite stmts_tmap_cat in Htm_comp_ss.
    specialize (IHs s tmap scope1 scope2 vm Hs_inf Htm_inf Hsc1_sub_tm Hsc2_sub_tm Hsc1_sub_sc2)
          with (old_conn_map := old_conn_map) (old_scope := old_scope) (3 := Holdsc_sub_sc1).
    generalize (ExpandBranch_stmt_tmap vm s tmap) ;
          intro Heb_s ;
          specialize Heb_s with (3 := Holdsc_sub_sc1) (4 := Hs_inf) (old_scope1 := scope1) (old_conn_map := old_conn_map) (old_scope2 := old_scope).
    destruct (ExpandBranch_fun s old_conn_map old_scope) as [[temp_conn_map temp_scope]|] ; last by reflexivity.
    specialize Heb_s with (new_conn_map := temp_conn_map) (new_scope2 := temp_scope) (2 := Logic.eq_refl).
    generalize (stmt_submap vm s tmap scope1 Hsc1_sub_tm) ;
          intro Htm_sub1_s.
    generalize (stmt_tmap_components vm s tmap scope1 scope2 Hsc1_sub_tm Hsc2_sub_tm Hsc1_sub_sc2) ;
          intro Hsc1s_sub_sc2s.
    generalize (stmt_tmap_preserves_fully_inferred vm tmap scope1 s Hs_inf Htm_inf Hsc1_sub_tm) ;
          intro Htms_inf.
    destruct (stmt_tmap (tmap, scope1) s vm) as [[tmap_s scope1_s]|] ;
          last by (destruct (stmts_tmap (tmap, scope2) (component_stmt_of s) vm) ;
                   last (by contradiction Htm_ss) ;
                   first (by discriminate IHs ; done)).
    specialize (Heb_s tmap_s scope1_s Logic.eq_refl).
    clear IHs.
    generalize (stmts_submap vm (component_stmt_of s) tmap scope2 Hsc2_sub_tm) ;
          intro Htm_sub2_s.
    destruct (stmts_tmap (tmap, scope2) (component_stmt_of s) vm) as [[tmap_s' scope2_s]|] ; last by contradiction Htm_comp_ss.
    destruct Hsc1s_sub_sc2s as [Hsc1s_sub_sc2s' Hsc1s_sub_sc2s] ; subst tmap_s'.
    by apply (IHss tmap_s scope1_s scope2_s vm Hss_inf Htms_inf (proj1 Htm_sub1_s) (proj1 Htm_sub2_s)
                Hsc1s_sub_sc2s Htm_ss Htm_comp_ss temp_conn_map temp_scope Heb_s).
* clear ExpandBranch_fun_checks_scopes.
  destruct s as [|var ft|var reg|var mem|var1 var2|var expr|ref expr|ref|cond sst ssf] ;
  simpl ; intros tmap scope1 scope2 vm Hs_inf Htm_inf Hsc1_sub_tm Hsc2_sub_tm Hsc1_sub_sc2 Htm_s1 Htm_s2 old_conn_map old_scope Holdsc_sub_sc1 ; try done.
  + (* Swire *)
    specialize (Hsc1_sub_tm var).
    destruct (CEP.find var tmap) ; first by contradiction Htm_s2.
    destruct (code_type_find_vm_widths ft var vm) as [[]|]; last by contradiction Htm_s2.
    by discriminate Htm_s1.
  + (* Sreg *)
    generalize (Hsc2_sub_tm var) ; intro.
    destruct (CEP.find var old_scope) ; first by reflexivity.
    destruct (CEP.find var tmap) ; first by contradiction Htm_s2.
    destruct (type reg) as [gt| |] ; try by discriminate Hs_inf.
    destruct (type_of_expr (clock reg) scope2) ; last by contradiction Htm_s2.
    generalize (fully_inferred_does_not_change gt var vm) ; intro.
    destruct (code_type_find_vm_widths (Gtyp gt) var vm) as [[newft _]|]; last by contradiction Htm_s2.
    destruct (reset reg) as [|rst_sig rst_val].
    1,2: move /andP : Hs_inf => [Hs_inf Hs_inf'] ; apply H0 in Hs_inf' ; clear H0.
    1,2: destruct newft as [gt'| |] ; try by contradiction (Hs_inf').
    1,2: subst gt'.
    1,2: generalize (type_of_expr_submap (clock reg) old_scope scope1 Holdsc_sub_sc1) ; intro.
    1,2: destruct (type_of_expr (clock reg) old_scope) ; last by reflexivity.
    - by rewrite H0 // in Htm_s1.
    - rewrite H0 in Htm_s1 ; clear H0.
      generalize (type_of_expr_submap rst_sig old_scope scope1 Holdsc_sub_sc1) ;
            intro.
      destruct (type_of_expr rst_sig old_scope) as [[[[[|[|]]| | | | | |]| |] po]|] ; try by reflexivity.
      1,2: rewrite H0 in Htm_s1 ; clear H0.
      * generalize (type_of_expr_submap rst_val (CEP.add var (Gtyp gt, HiF.Duplex) old_scope) (CEP.add var (Gtyp gt, HiF.Duplex) scope1) (submap_add_add old_scope scope1 var (Gtyp gt, HiF.Duplex) Holdsc_sub_sc1)) ; intro.
        destruct (type_of_expr rst_val (CEP.add var (Gtyp gt, HiF.Duplex) old_scope)) ; last by reflexivity.
        by rewrite H0 // in Htm_s1.
      * generalize (type_of_expr_submap rst_val old_scope scope1 Holdsc_sub_sc1) ; intro.
        destruct (type_of_expr rst_val old_scope) ; last by reflexivity.
        by rewrite H0 // in Htm_s1.
  + (* Snode *)
    destruct (CEP.find var old_scope) ; first by reflexivity.
    destruct (CEP.find var tmap) ; first by contradiction Htm_s2.
    generalize (type_of_expr_submap expr old_scope scope1 Holdsc_sub_sc1) ;
            intro.
    destruct (type_of_expr expr old_scope) as [[ft_expr p]|] ; last by reflexivity.
    rewrite H in Htm_s1 ; clear H p.
    by discriminate Htm_s1.
  + (* Sfcnct *)
    destruct ref as [var| | |] ; try reflexivity.
    simpl type_of_ref in Htm_s1.
    generalize (Holdsc_sub_sc1 var) ; intro.
    destruct (CEP.find var old_scope) as [[[gt_ref| |] [| | | |]]|] ; try by reflexivity.
    1,2: rewrite (H _ Logic.eq_refl) in Htm_s1 ; clear H.
    1,2: generalize (type_of_expr_submap expr old_scope scope1 Holdsc_sub_sc1) ;
            intro.
    1,2: destruct (type_of_expr expr old_scope) as [[ft_expr p]|] ; last by reflexivity.
    1,2: by rewrite H // in Htm_s1.
  + (* Sinvalid *)
    destruct ref as [var| | |] ; try reflexivity.
    simpl type_of_ref in Htm_s1.
    specialize (Holdsc_sub_sc1 var).
    destruct (CEP.find var old_scope) as [[ft_ref [| | | |]]|] ; try by reflexivity.
    1,2: by rewrite (Holdsc_sub_sc1 _ Logic.eq_refl) // in Htm_s1.
  + (* Swhen *)
    move /andP : Hs_inf => [/andP [_ Hsst_inf] Hssf_inf].
    generalize (type_of_expr_submap cond old_scope scope1 Holdsc_sub_sc1) ;
          intro.
    destruct (type_of_expr cond old_scope) as [[[[[|[|]]| | | | | |]| |] p]|] ; try by reflexivity.
    rewrite H in Htm_s1 ; clear H p.
    rewrite stmts_tmap_cat in Htm_s2.
    (* General line of the argument:
       Based on Htm_s1, we cannot have both
       a) isSome (stmts_tmap (tmap, scope1) sst vm) and
       b) isSome (stmts_tmap (tmap_true, scope1) ssf vm).
       However, based on Htm_s2, we do have both
       - isSome (stmts_tmap (tmap, scope2) (component_stmts_of sst) vm) and
       - isSome (stmts_tmap (tmap_true, scope2_true) (component_stmts_of ssf) vm).
       In case a), we can use ExpandBranch_funs_checks_scopes
       to prove that ExpandBranch_funs ss_true ... = None.
       In case b), we can use ExpandBranch_funs_checks_scopes
       to prove that ExpandBranch_funs ssf ... = None.
       *)
    generalize (stmts_tmap_components vm sst tmap scope1 scope2 Hsc1_sub_tm Hsc2_sub_tm Hsc1_sub_sc2) ;
          intro Hcomp.
    generalize (stmts_tmap_preserves_fully_inferred vm sst tmap scope1 Hsst_inf Htm_inf Hsc1_sub_tm) ;
          intro Htmt_inf.
    generalize (stmts_submap vm sst tmap scope1 Hsc1_sub_tm) ;
          intro Htm_sub_t.
    generalize (ExpandBranch_funs_checks_scopes sst tmap scope1 scope2 vm Hsst_inf Htm_inf Hsc1_sub_tm Hsc2_sub_tm Hsc1_sub_sc2) ;
          intro.
    destruct (stmts_tmap (tmap, scope1) sst vm) as [[tmap_true scope1_true]|].
    - rename ExpandBranch_funs_checks_scopes into IHss.
      generalize (stmts_submap vm (component_stmts_of sst) tmap scope2 Hsc2_sub_tm) ;
            intro Htm_sub_f.
      destruct (stmts_tmap (tmap, scope2) (component_stmts_of sst) vm) as [[tmap_true' scope2_true]|] ; last by contradiction Htm_s2.
      destruct Hcomp as [H' Hcomp] ; subst tmap_true'.
      destruct (ExpandBranches_funs sst old_conn_map old_scope) as [[true_conn_map _]|] ; last by reflexivity.
      generalize (CEP.Lemmas.submap_trans (proj2 (proj2 Htm_sub_t)) (proj1 Htm_sub_t)) ;
            intro Hsc1_sub_tmt.
      generalize (CEP.Lemmas.submap_trans Hsc1_sub_sc2 (proj2 (proj2 Htm_sub_f))) ;
            intro Hsc1_sub_sc2t.
      specialize (IHss ssf tmap_true scope1 scope2_true vm
                  Hssf_inf Htmt_inf Hsc1_sub_tmt (proj1 Htm_sub_f) Hsc1_sub_sc2t)
            with (old_conn_map := old_conn_map) (old_scope := old_scope).
      destruct (stmts_tmap (tmap_true, scope1) ssf vm) as [[]|] ; first by discriminate Htm_s1.
      by rewrite (IHss Logic.eq_refl Htm_s2 Holdsc_sub_sc1) //.
    - destruct (stmts_tmap (tmap, scope2) (component_stmts_of sst) vm) ; last by contradiction Htm_s2.
      specialize (H Logic.eq_refl) with (old_conn_map := old_conn_map) (old_scope := old_scope).
      by rewrite H //.
Qed.

Lemma stmts_tmap_submap :
forall (vm : CEP.t vertex_type) (ss : HiFP.hfstmt_seq) (tmap scope : CEP.t (ftype * HiF.forient)),
        CEP.submap scope tmap
    ->
        match stmts_tmap (tmap, scope) ss vm with
        | Some (tmap', scope') => CEP.submap scope' tmap' /\ CEP.submap tmap tmap' /\ CEP.submap scope scope'
        | None => True
        end
with stmt_tmap_submap :
forall (vm : CEP.t vertex_type) (s : HiFP.hfstmt) (tmap scope : CEP.t (ftype * HiF.forient)),
        CEP.submap scope tmap
    ->
        match stmt_tmap (tmap, scope) s vm with
        | Some (tmap', scope') => CEP.submap scope' tmap' /\ CEP.submap tmap tmap' /\ CEP.submap scope scope'
        | None => True
        end.
Proof.
* clear stmts_tmap_submap.
  induction ss as [|s ss] ; simpl ; intros tmap scope Hsc_sub_tm.
  + split.
    - exact Hsc_sub_tm.
    - split ; by apply CEP.Lemmas.submap_refl.
  + rename stmt_tmap_submap into IHs.
    specialize (IHs vm s tmap scope Hsc_sub_tm).
    destruct (stmt_tmap (tmap, scope) s vm) as [[tmap_s scope_s]|] ; last by trivial.
    specialize (IHss tmap_s scope_s (proj1 IHs)).
    destruct (stmts_tmap (tmap_s, scope_s) ss vm) as [[tmap_s_ss scope_s_ss]|] ; last by trivial.
    split.
    - by apply IHss.
    - destruct IHs as [_ IHs] ; split.
      * by apply (CEP.Lemmas.submap_trans (proj1 IHs)), IHss.
      * by apply (CEP.Lemmas.submap_trans (proj2 IHs)), IHss.
* clear stmt_tmap_submap.
  destruct s as [|var ft|var reg|var mem|var1 var2|var expr|ref expr|ref|cond sst ssf] ;
        simpl ; intros tmap scope Hsc_sub_tm.
  + (* Sskip *)
    split.
    - exact Hsc_sub_tm.
    - split ; by apply CEP.Lemmas.submap_refl.
  + (* Swire *)
    destruct (CEP.find var tmap) eqn: Hvar_tmap ; first by trivial.
    destruct (code_type_find_vm_widths ft var vm) as [[newft _]|] ; last by trivial.
    split.
    - by apply submap_add_add, Hsc_sub_tm.
    - split ;
      apply CEP.Lemmas.submap_none_add ;
            try (by apply CEP.Lemmas.submap_refl) ;
            try exact Hvar_tmap.
      specialize (Hsc_sub_tm var).
      destruct (CEP.find var scope) ; last by reflexivity.
      by rewrite (Hsc_sub_tm _ Logic.eq_refl) // in Hvar_tmap.
  + (* Sreg *)
    destruct (CEP.find var tmap) eqn: Hvar_tmap ; first by trivial.
    destruct (type_of_expr (clock reg) scope) as [_|] ; last by trivial.
    destruct (code_type_find_vm_widths (type reg) var vm) as [[newt _]|] ; last by trivial.
    destruct (reset reg) as [|rst_sig rst_val] ; first last.
    1: destruct (type_of_expr rst_sig scope) as [[[[[|[|]]| | | | | |]| |] _]|] ; try by trivial.
    1: destruct (type_of_expr rst_val (CEP.add var (newt, HiF.Duplex) scope)) as [_|] ; last by trivial.
    2: destruct (type_of_expr rst_val scope) as [_|] ; last by trivial.
    1-3: split.
    - 1,3,5: by apply submap_add_add, Hsc_sub_tm.
    - 1-3: split ;
           apply CEP.Lemmas.submap_none_add ;
                 try (by apply CEP.Lemmas.submap_refl) ;
                 try exact Hvar_tmap.
      1-3: specialize (Hsc_sub_tm var).
      1-3: destruct (CEP.find var scope) ; last by reflexivity.
      1-3: by rewrite (Hsc_sub_tm _ Logic.eq_refl) // in Hvar_tmap.
  + (* Smem *)
    by trivial.
  + (* Sinst *)
    by trivial.
  + (* Snode *)
    destruct (CEP.find var tmap) eqn: Hvar_tmap ; first by trivial.
    destruct (type_of_expr expr scope) as [[newt _]|] ; last by trivial.
    split.
    - by apply submap_add_add, Hsc_sub_tm.
    - split ;
      apply CEP.Lemmas.submap_none_add ;
            try (by apply CEP.Lemmas.submap_refl) ;
            try exact Hvar_tmap.
      specialize (Hsc_sub_tm var).
      destruct (CEP.find var scope) ; last by reflexivity.
      by rewrite (Hsc_sub_tm _ Logic.eq_refl) // in Hvar_tmap.
  + (* Sfcnct *)
    destruct (type_of_ref ref scope) as [_|] ; last by trivial.
    destruct (type_of_expr expr scope) as [_|] ; last by trivial.
    split.
    - exact Hsc_sub_tm.
    - split ; by apply CEP.Lemmas.submap_refl.
  + (* Sinvalid *)
    destruct (type_of_ref ref scope) as [_|] ; last by trivial.
    split.
    - exact Hsc_sub_tm.
    - split ; by apply CEP.Lemmas.submap_refl.
  + (* Swhen *)
    generalize (stmts_tmap_submap vm sst tmap scope Hsc_sub_tm) ; intro IHsst.
    rename stmts_tmap_submap into IHssf ; specialize (IHssf vm ssf).
    destruct (type_of_expr cond scope) as [_|] ; last by trivial.
    destruct (stmts_tmap (tmap, scope) sst vm) as [[tmap_true scope_true]|] ; last by trivial.
    specialize (IHssf tmap_true scope (CEP.Lemmas.submap_trans Hsc_sub_tm (proj1 (proj2 IHsst)))).
    destruct (stmts_tmap (tmap_true, scope) ssf vm) as [[tmap_false scope_false]|] ; last by trivial.
    split.
    - by apply (CEP.Lemmas.submap_trans Hsc_sub_tm), (CEP.Lemmas.submap_trans (proj1 (proj2 IHsst))), IHssf.
    - split.
      * by apply (CEP.Lemmas.submap_trans (proj1 (proj2 IHsst))), IHssf.
      * by apply CEP.Lemmas.submap_refl.
Qed.

Lemma stmts_tmap_connect :
forall (vm : CEP.t vertex_type) (conn_map : CEP.t def_expr) (tmap scope : CEP.t (ftype * HiF.forient)),
    match stmts_tmap (tmap, scope) (convert_to_connect_stmts conn_map) vm with
    | Some (tmap', scope') => tmap = tmap' /\ scope = scope'
    | None => True
    end.
Proof.
intros.
rewrite /convert_to_connect_stmts CEP.Lemmas.P.fold_spec_right.
generalize (List.rev (PVM.elements conn_map)).
induction l.
* simpl.
  split ; by reflexivity.
* destruct a as [k expr] ;
  rewrite {1}/CEP.Lemmas.P.uncurry {1}/convert_to_connect_stmt ;
  simpl.
  destruct expr.
  + exact IHl.
  + 1,2: simpl stmts_tmap.
    1,2: destruct (CEP.find k scope) ; last by reflexivity.
    2: destruct (type_of_expr h scope) ; last by reflexivity.
    1,2: exact IHl.
Qed.

Lemma stmts_tmap_vm_and_tmap_fit_together:
forall (ss : HiFP.hfstmt_seq) (old_vm new_vm final_vm : CEP.t vertex_type) (old_ct new_ct : CEP.t def_expr)
       (old_tmap old_scope new_tmap new_scope final_tmap : CEP.t (ftype * HiF.forient)),
        tmap_has_fully_inferred_ground_types final_tmap (* old_scope would be enough *)
    ->
        stmts_have_fully_inferred_ground_types ss
    ->
        scope_sub_vm old_tmap old_vm
    ->
        ct_sub_vm old_ct old_vm final_tmap
    ->
        vm_sub_tmap old_vm old_tmap
    ->
        CEP.submap old_scope old_tmap
    ->
        stmts_tmap (old_tmap, old_scope) ss final_vm = Some (new_tmap, new_scope)
    ->
        Sem_frag_stmts old_vm old_ct (component_stmts_of ss) new_vm new_ct final_tmap
    ->
        CEP.submap new_tmap final_tmap
    ->
        CEP.submap new_vm final_vm
    ->
        scope_sub_vm new_tmap new_vm /\ vm_sub_tmap new_vm new_tmap
with stmt_tmap_vm_and_tmap_fit_together:
forall (s : HiFP.hfstmt) (old_vm new_vm final_vm : CEP.t vertex_type) (old_ct new_ct : CEP.t def_expr)
       (old_tmap old_scope new_tmap new_scope final_tmap : CEP.t (ftype * HiF.forient)),
        tmap_has_fully_inferred_ground_types final_tmap (* old_scope would be enough *)
    ->
        stmt_has_fully_inferred_ground_types s
    ->
        scope_sub_vm old_tmap old_vm
    ->
        ct_sub_vm old_ct old_vm final_tmap
    ->
        vm_sub_tmap old_vm old_tmap
    ->
        CEP.submap old_scope old_tmap
    ->
        stmt_tmap (old_tmap, old_scope) s final_vm = Some (new_tmap, new_scope)
    ->
        Sem_frag_stmts old_vm old_ct (component_stmt_of s) new_vm new_ct final_tmap
    ->
        CEP.submap new_tmap final_tmap
    ->
        CEP.submap new_vm final_vm
    ->
        scope_sub_vm new_tmap new_vm /\ vm_sub_tmap new_vm new_tmap.
Proof.
* clear stmts_tmap_vm_and_tmap_fit_together.
  induction ss as [|s ss] ; simpl ; intros old_vm new_vm final_vm old_ct new_ct old_tmap old_scope new_tmap new_scope final_tmap
                                           Htm_inf Hss_inf Htm_sub_vm Hct_sub_vm Hvm_sub_tm Holdsc_sub_oldtm Htm Hsf Htm_sub_finaltm Hvm_sub_finalvm.
  + injection Htm ; clear Htm ; intros ; subst new_tmap new_scope.
    split.
    - intro k ; rewrite -(proj1 Hsf) ; by apply Htm_sub_vm.
    - intro k ; rewrite -(proj1 Hsf) ; by apply Hvm_sub_tm.
  + rename stmt_tmap_vm_and_tmap_fit_together into IHs.
    move /andP : Hss_inf => Hss_inf.
    apply Sem_frag_stmts_cat in Hsf.
    destruct Hsf as [vm_s [ct_s [Hsf_s Hsf_ss]]].
    generalize (Sem_frag_stmt_component s old_vm old_ct vm_s ct_s final_tmap Hct_sub_vm Hsf_s) ; intro Hsf_sub_s.
    specialize (IHs s old_vm) with (final_vm := final_vm) (old_ct := old_ct) (old_tmap := old_tmap)
               (old_scope := old_scope) (final_tmap := final_tmap)
               (1 := Htm_inf) (2 := proj1 Hss_inf) (3 := Htm_sub_vm) (4 := Hct_sub_vm) (5 := Hvm_sub_tm) (6 := Holdsc_sub_oldtm) (8 := Hsf_s).
    generalize (stmt_tmap_submap final_vm s old_tmap old_scope Holdsc_sub_oldtm) ; intro Htm_sub_s.
    destruct (stmt_tmap (old_tmap, old_scope) s final_vm) as [[tmap_s scope_s]|] ;
        last by discriminate Htm.
    generalize (Sem_frag_stmts_component ss vm_s ct_s new_vm new_ct final_tmap (proj1 Hsf_sub_s) Hsf_ss) ; intro Hsf_sub_ss.
    generalize (stmts_tmap_submap final_vm ss tmap_s scope_s (proj1 Htm_sub_s)) ;
          intro Htm_sub_ss ; rewrite Htm in Htm_sub_ss.
    specialize IHs with (1 := Logic.eq_refl) (2 := CEP.Lemmas.submap_trans (proj1 (proj2 Htm_sub_ss)) Htm_sub_finaltm)
                        (3 := CEP.Lemmas.submap_trans (proj1 (proj2 Hsf_sub_ss)) Hvm_sub_finalvm).
    by apply (IHss vm_s new_vm final_vm ct_s new_ct tmap_s scope_s new_tmap new_scope final_tmap
                     Htm_inf (proj2 Hss_inf) (proj1 IHs) (proj1 Hsf_sub_s) (proj2 IHs) (proj1 Htm_sub_s) Htm Hsf_ss Htm_sub_finaltm Hvm_sub_finalvm).
* clear stmt_tmap_vm_and_tmap_fit_together.
  destruct s as [|var ft|var reg|var mem|var1 var2|var expr|ref expr|ref|cond sst ssf] ;
        simpl ; intros old_vm new_vm final_vm old_ct new_ct old_tmap old_scope new_tmap new_scope final_tmap
                       Htm_inf Hs_inf Htm_sub_vm Hct_sub_vm Hvm_sub_tm Holdsc_sub_oldtm Htm Hsf Htm_sub_finaltm Hvm_sub_finalvm.
  + (* Sskip *)
    injection Htm ; clear Htm ; intros ; subst new_tmap new_scope.
    split.
    - intro k ; rewrite -(proj1 Hsf) ; by apply Htm_sub_vm.
    - intro k ; rewrite -(proj1 Hsf) ; by apply Hvm_sub_tm.
  + (* Swire *)
    destruct Hsf as [new_vm' [new_ct' [Hsf [Hnew_vm_equal Hnew_ct_equal]]]].
    destruct (CEP.find var old_tmap) eqn: Hvar_tmap ; first by discriminate Htm.
    destruct ft as [gt| |] ; try by discriminate Hs_inf.
    simpl code_type_find_vm_widths in Htm.
    destruct (CEP.find var final_vm) eqn: Hvar_final_vm ; last by discriminate Htm.
    assert (CEP.add var (Gtyp gt, HiF.Duplex) old_tmap = new_tmap /\ CEP.add var (Gtyp gt, HiF.Duplex) old_scope = new_scope).
         destruct v as [gt'|gt'|gt'|gt'|gt'], (code_vm_type_equivalent gt gt') eqn: Hequiv ;
                  try done ;
                  injection Htm ; intros ; subst new_tmap new_scope ;
                  destruct gt, gt' ; rewrite /code_vm_type_equivalent // in Hequiv ;
                  rewrite (elimT eqP Hequiv) ; split ; reflexivity.
    destruct H ; subst new_tmap new_scope.
    specialize (Htm_sub_finaltm var) ; rewrite (CEP.Lemmas.find_add_eq (eqxx _)) in Htm_sub_finaltm.
    rewrite (Htm_sub_finaltm _ Logic.eq_refl) in Hsf.
    split.
    - intro k ; destruct (k == var) eqn: Hkvar.
      * rewrite (CEP.Lemmas.find_add_eq Hkvar) (elimT eqP Hkvar).
        destruct Hsf as [Hsf _] ; specialize (Hsf 0) ; simpl in Hsf.
        rewrite add0n nat_of_binK -surjective_pairing Hnew_vm_equal in Hsf.
        by rewrite (proj2 Hsf) //.
      * rewrite (CEP.Lemmas.find_add_neq (elimT negP (negbT Hkvar))).
        destruct Hsf as [_ [Hsf _]] ; specialize (Hsf k.1 k.2 (Hneq_12small_large k var Hkvar)).
        rewrite -surjective_pairing in Hsf.
        rewrite -Hnew_vm_equal -Hsf //.
        by apply Htm_sub_vm.
    - intro k ; destruct (k == var) eqn: Hkvar.
      * rewrite (CEP.Lemmas.find_add_eq Hkvar) (elimT eqP Hkvar).
        destruct Hsf as [Hsf _] ; specialize (Hsf 0) ; simpl in Hsf.
        rewrite add0n nat_of_binK -surjective_pairing Hnew_vm_equal in Hsf.
        by rewrite (proj2 Hsf) //.
      * rewrite (CEP.Lemmas.find_add_neq (elimT negP (negbT Hkvar))).
        destruct Hsf as [_ [Hsf _]] ; specialize (Hsf k.1 k.2 (Hneq_12small_large k var Hkvar)).
        rewrite -surjective_pairing in Hsf.
        rewrite -Hnew_vm_equal -Hsf //.
        by apply Hvm_sub_tm.
  + (* Sreg *)
    destruct Hsf as [new_vm' [new_ct' [Hsf [Hnew_vm_equal Hnew_ct_equal]]]].
    destruct (CEP.find var old_tmap) eqn: Hvar_tmap ; first by discriminate Htm.
    destruct (type_of_expr (clock reg) old_scope) ; last by discriminate Htm.
    destruct (type reg) as [gt| |] ; try by discriminate Hs_inf.
    simpl code_type_find_vm_widths in Htm.
    destruct (CEP.find var final_vm) eqn: Hvar_final_vm ; last by discriminate Htm.
    assert (CEP.add var (Gtyp gt, HiF.Duplex) old_tmap = new_tmap /\ CEP.add var (Gtyp gt, HiF.Duplex) old_scope = new_scope).
          destruct (reset reg) as [|rst_sig rst_val].
          1,2: move /andP : Hs_inf => [_ Hs_inf].
          1: destruct v as [gt'|gt'|gt'|gt'|gt'], (code_vm_type_equivalent gt gt') eqn: Hequiv ;
                  try done ;
                  injection Htm ; intros ; subst new_tmap new_scope ;
                  destruct gt, gt' ; rewrite /code_vm_type_equivalent // in Hequiv ;
                  rewrite (elimT eqP Hequiv) ; split ; reflexivity.
          1: destruct v as [gt'|gt'|gt'|gt'|gt'], (code_vm_type_equivalent gt gt') eqn: Hequiv,
                     (type_of_expr rst_sig old_scope) as [[[[[|[|]]| | | | | |]| |] _]|] ; try done.
          1,3,5,7,9: destruct (type_of_expr rst_val (CEP.add var (Gtyp gt', HiF.Duplex) old_scope)) ; last by discriminate Htm.
          6-10: destruct (type_of_expr rst_val old_scope) ; last by discriminate Htm.
          1-10: injection Htm ; intros ; subst new_tmap new_scope.
          1-10: destruct gt, gt' ; rewrite /code_vm_type_equivalent // in Hequiv ;
                rewrite (elimT eqP Hequiv) ; split ; reflexivity.
    destruct H ; subst new_tmap new_scope.
    specialize (Htm_sub_finaltm var) ; rewrite (CEP.Lemmas.find_add_eq (eqxx _)) in Htm_sub_finaltm.
    rewrite (Htm_sub_finaltm _ Logic.eq_refl) in Hsf.
    split.
    - intro k ; destruct (k == var) eqn: Hkvar.
      * rewrite (CEP.Lemmas.find_add_eq Hkvar) (elimT eqP Hkvar).
        destruct Hsf as [Hsf _] ; destruct (reset reg) as [|rst_sig rst_val] ; first last.
        1: destruct (type_of_expr rst_val final_tmap) as [[rst_val_type _]|] ; last by discriminate Hsf.
        1: destruct (list_rhs_expr_p rst_val rst_val_type) as [rst_val_lst|] ; last by contradiction (proj2 Hsf).
        1,2: destruct Hsf as [_ Hsf] ; specialize (Hsf 0) ; simpl in Hsf.
        1: destruct rst_val_lst as [|rst_val_elt _] ; first by contradiction Hsf.
        1,2: rewrite add0n nat_of_binK -surjective_pairing Hnew_vm_equal in Hsf.
        1,2: by rewrite (proj2 Hsf) //.
      * rewrite (CEP.Lemmas.find_add_neq (elimT negP (negbT Hkvar))).
        destruct Hsf as [_ [_ [_ [Hsf _]]]] ; specialize (Hsf k.1 k.2 (Hneq_12small_large k var Hkvar)).
        rewrite -surjective_pairing in Hsf.
        rewrite -Hnew_vm_equal -Hsf //.
        by apply Htm_sub_vm.
    - intro k ; destruct (k == var) eqn: Hkvar.
      * rewrite (CEP.Lemmas.find_add_eq Hkvar) (elimT eqP Hkvar).
        destruct Hsf as [Hsf _] ; destruct (reset reg) as [|rst_sig rst_val] ; first last.
        1: destruct (type_of_expr rst_val final_tmap) as [[rst_val_type _]|] ; last by discriminate Hsf.
        1: destruct (list_rhs_expr_p rst_val rst_val_type) as [rst_val_lst|] ; last by contradiction (proj2 Hsf).
        1,2: destruct Hsf as [_ Hsf] ; specialize (Hsf 0) ; simpl in Hsf.
        1: destruct rst_val_lst as [|rst_val_elt _] ; first by contradiction Hsf.
        1,2: rewrite add0n nat_of_binK -surjective_pairing Hnew_vm_equal in Hsf.
        1,2: by rewrite (proj2 Hsf) //.
      * rewrite (CEP.Lemmas.find_add_neq (elimT negP (negbT Hkvar))).
        destruct Hsf as [_ [_ [_ [Hsf _]]]] ; specialize (Hsf k.1 k.2 (Hneq_12small_large k var Hkvar)).
        rewrite -surjective_pairing in Hsf.
        rewrite -Hnew_vm_equal -Hsf //.
        by apply Hvm_sub_tm.
  + (* Smem *)
    by discriminate Htm.
  + (* Sinst *)
    by discriminate Htm.
  + (* Snode *)
    destruct Hsf as [new_vm' [new_ct' [Hsf [Hnew_vm_equal Hnew_ct_equal]]]].
    destruct (CEP.find var old_tmap) eqn: Hvar_tmap ; first by discriminate Htm.
    specialize (expr_preserves_fully_inferred old_scope) with (expr := expr) (2 := Hs_inf) ; intro Hexpr_inf.
    generalize (type_of_expr_submap expr old_scope final_tmap) ; intro H0.
    destruct (type_of_expr expr old_scope) as [[ft Hft_exp]|] ; last by discriminate Htm.
    injection Htm ; clear Htm ; intros ; subst new_tmap new_scope.
    assert (Holdsc_sub_finaltm: CEP.submap old_scope final_tmap)
          by apply (CEP.Lemmas.submap_trans Holdsc_sub_oldtm),
                   (CEP.Lemmas.submap_trans (CEP.Lemmas.submap_none_add (ft, HiF.Source) (CEP.Lemmas.submap_refl old_tmap) Hvar_tmap)),
                   Htm_sub_finaltm.
    assert (tmap_has_fully_inferred_ground_types old_scope).
          intro k ; specialize (Htm_inf k).
          specialize (Holdsc_sub_finaltm k).
          destruct (CEP.find k old_scope) ; last by trivial.
          by rewrite (Holdsc_sub_finaltm _ Logic.eq_refl) // in Htm_inf.
    specialize (Hexpr_inf H) ; clear H.
    destruct ft as [gt| |] ; try by contradiction Hexpr_inf.
    rewrite (H0 Holdsc_sub_finaltm) in Hsf.
    replace (list_rhs_expr_p expr (Gtyp gt)) with (Some [:: expr]) in Hsf by (destruct expr ; done).
    split.
    - intro k ; destruct (k == var) eqn: Hkvar.
      * rewrite (CEP.Lemmas.find_add_eq Hkvar) (elimT eqP Hkvar).
        destruct Hsf as [Hsf _] ; specialize (Hsf 0) ; simpl in Hsf.
        rewrite add0n nat_of_binK -surjective_pairing Hnew_vm_equal in Hsf.
        by rewrite (proj2 Hsf) //.
      * rewrite (CEP.Lemmas.find_add_neq (elimT negP (negbT Hkvar))).
        destruct Hsf as [_ [Hsf _]] ; specialize (Hsf k.1 k.2 (Hneq_12small_large k var Hkvar)).
        rewrite -surjective_pairing in Hsf.
        rewrite -Hnew_vm_equal -Hsf //.
        by apply Htm_sub_vm.
    - intro k ; destruct (k == var) eqn: Hkvar.
      * rewrite (CEP.Lemmas.find_add_eq Hkvar) (elimT eqP Hkvar).
        destruct Hsf as [Hsf _] ; specialize (Hsf 0) ; simpl in Hsf.
        rewrite add0n nat_of_binK -surjective_pairing Hnew_vm_equal in Hsf.
        by rewrite (proj2 Hsf) //.
      * rewrite (CEP.Lemmas.find_add_neq (elimT negP (negbT Hkvar))).
        destruct Hsf as [_ [Hsf _]] ; specialize (Hsf k.1 k.2 (Hneq_12small_large k var Hkvar)).
        rewrite -surjective_pairing in Hsf.
        rewrite -Hnew_vm_equal -Hsf //.
        by apply Hvm_sub_tm.
  + (* Sfcnct *)
    destruct (type_of_ref ref old_scope), (type_of_expr expr old_scope) ; try by discriminate Htm.
    injection Htm ; clear Htm ; intros ; subst new_tmap new_scope.
    split.
    - intro k ; rewrite -(proj1 Hsf).
      by apply Htm_sub_vm.
    - intro k ; rewrite -(proj1 Hsf).
      by apply Hvm_sub_tm.
  + (* Sinvalid *)
    destruct (type_of_ref ref old_scope) ; try by discriminate Htm.
    injection Htm ; clear Htm ; intros ; subst new_tmap new_scope.
    split.
    - intro k ; rewrite -(proj1 Hsf).
      by apply Htm_sub_vm.
    - intro k ; rewrite -(proj1 Hsf).
      by apply Hvm_sub_tm.
  + (* Swhen *)
    rename stmts_tmap_vm_and_tmap_fit_together into IHsst.
    specialize IHsst with (old_scope := old_scope) (final_vm := final_vm) (final_tmap := final_tmap) (1 := Htm_inf).
    generalize (IHsst ssf) ; intro IHssf.
    move /andP : Hs_inf => [/andP [_ Hsst_inf] Hssf_inf].
    apply Sem_frag_stmts_cat in Hsf.
    destruct Hsf as [vm_true [ct_true [Hsf_t Hsf_f]]].
    specialize (IHsst sst old_vm) with (old_ct := old_ct) (old_tmap := old_tmap)
               (1 := Hsst_inf) (2 := Htm_sub_vm) (3 := Hct_sub_vm) (4 := Hvm_sub_tm) (5 := Holdsc_sub_oldtm) (7 := Hsf_t).
    destruct (type_of_expr cond old_scope) ; last by discriminate Htm.
    generalize (stmts_tmap_submap final_vm sst old_tmap old_scope Holdsc_sub_oldtm) ; intro Htm_sub_t.
    destruct (stmts_tmap (old_tmap, old_scope) sst final_vm) as [[tmap_true scope_true]|] ; last by discriminate Htm.
    specialize IHsst with (1 := Logic.eq_refl).
    specialize (Sem_frag_stmts_component sst old_vm old_ct) with (tmap := final_tmap) (1 := Hct_sub_vm) (2 := Hsf_t) ; intro Hsf_sub_t.
    specialize IHssf with (old_tmap := tmap_true) (1 := Hssf_inf) (3 := proj1 Hsf_sub_t) (5 := CEP.Lemmas.submap_trans Holdsc_sub_oldtm (proj1 (proj2 Htm_sub_t))) (7 := Hsf_f).
    generalize (stmts_tmap_submap final_vm ssf tmap_true old_scope (CEP.Lemmas.submap_trans Holdsc_sub_oldtm (proj1 (proj2 Htm_sub_t)))) ; intro Htm_sub_f.
    destruct (stmts_tmap (tmap_true, old_scope) ssf final_vm) as [[tmap_false scope_false]|] ;
          last by discriminate Htm.
    injection Htm ; clear Htm ; intros ; subst tmap_false new_scope.
    generalize (Sem_frag_stmts_component ssf vm_true ct_true new_vm new_ct final_tmap (proj1 Hsf_sub_t) Hsf_f) ;
          intro Hsf_sub_f.
    specialize (IHsst (CEP.Lemmas.submap_trans (proj1 (proj2 Htm_sub_f)) Htm_sub_finaltm)
                      (CEP.Lemmas.submap_trans (proj1 (proj2 Hsf_sub_f)) Hvm_sub_finalvm)).
    exact (IHssf new_tmap scope_false (proj1 IHsst) (proj2 IHsst) Logic.eq_refl Htm_sub_finaltm Hvm_sub_finalvm).
Qed.

Theorem ExpandWhens_correct :
(* if ExpandWhens creates a new module and it has a certain semantic,
   then the previous module also has the same semantic. *)
forall (m m' : HiFP.hfmodule)
           (vm : CEP.t vertex_type) (ct : CEP.t def_expr),
        module_has_fully_inferred_ground_types m
    ->
        ExpandWhens_fun m = Some m'
    ->
        Sem m' vm ct
    ->
        Sem m vm ct.
Proof.
intros m m' vm ct Hm_inf Hexpwhen Hsem.
unfold ExpandWhens_fun in Hexpwhen.
unfold Sem, ports_stmts_tmap in Hsem.
unfold Sem, ports_stmts_tmap.
destruct m as [m_name m_ports m_stmts|]; last by discriminate Hexpwhen.
simpl in Hm_inf ; move /andP : Hm_inf => Hm_inf.
generalize (ports_fit_together vm m_ports) ; intro Hpft.
destruct (ExpandPorts_fun m_ports) as [[port_ct pmap']|] eqn: HExpandPorts ; last by discriminate Hexpwhen.
generalize (ExpandBranch_funs_checks_scopes m_stmts) ; intro Hebfcs.
specialize Hebfcs with (vm := vm) (1 := proj2 Hm_inf) (old_conn_map := port_ct) (old_scope := pmap').
specialize (stmts_tmap_and_ExpandBranches_funs m_stmts pmap' port_ct pmap' vm)
      with (2 := CEP.Lemmas.submap_refl _) (3 := proj2 Hm_inf) ; intro Heb_tm.
destruct (ExpandBranches_funs m_stmts port_ct pmap')
         as [[conn_map tm_scope2']|] eqn: HexpandBranches ; last by discriminate Hexpwhen.
specialize Heb_tm with (3 := Logic.eq_refl).
injection Hexpwhen ; clear Hexpwhen ; intros ; subst m'.
generalize (ports_tmap_preserves_fully_inferred m_ports vm (proj1 Hm_inf)) ; intro Hpmap_inf.
destruct (ports_tmap m_ports vm) as [pmap|] ; last by contradiction Hsem.
specialize Hpft with (1 := proj1 Hm_inf) (2 := Logic.eq_refl) (3 := Logic.eq_refl).
specialize (Hebfcs pmap pmap pmap Hpmap_inf (CEP.Lemmas.submap_refl _) (CEP.Lemmas.submap_refl _) (CEP.Lemmas.submap_refl _)).
rewrite stmts_tmap_cat in Hsem.
generalize (stmts_tmap_components vm m_stmts pmap pmap pmap
            (CEP.Lemmas.submap_refl pmap) (CEP.Lemmas.submap_refl pmap) (CEP.Lemmas.submap_refl pmap)) ; intro.
generalize (stmts_tmap_submap vm (component_stmts_of m_stmts) pmap pmap (CEP.Lemmas.submap_refl _)) ;
      intro Htm_sub_comp.
destruct (stmts_tmap (pmap, pmap) (component_stmts_of m_stmts) vm) as [[tm_tmap1 tm_scope1]|] ;
      last by contradiction Hsem.
generalize (stmts_tmap_connect vm conn_map tm_tmap1 tm_scope1) ;
      intro Htm_sub_conn.
destruct (stmts_tmap (tm_tmap1, tm_scope1) (convert_to_connect_stmts conn_map) vm) as [[tm_tmap1' tm_scope1']|] ;
      last by contradiction Hsem.
destruct Htm_sub_conn ; subst tm_tmap1' tm_scope1'.
destruct Hsem as [Htm_no_overlap [vm_ports [ct_ports [Hsem_ports Hsem_stmts]]]].
specialize Hpft with (1 := Hsem_ports) (2 := proj1 (proj2 Htm_sub_comp)).
destruct Hpft as [Hpft' Hpft] ; subst pmap'.
specialize Heb_tm with (1 := Hpmap_inf).
specialize Hebfcs with (3 := CEP.Lemmas.submap_refl _).
generalize (stmts_tmap_submap vm m_stmts pmap pmap (CEP.Lemmas.submap_refl _)) ;
      intro Htm_sub.
generalize (stmts_tmap_preserves_fully_inferred vm m_stmts pmap pmap (proj2 Hm_inf) Hpmap_inf (CEP.Lemmas.submap_refl _)) ;
      intro Htmtm_inf.
specialize (ExpandWhens_correct_inductive vm) with (3 := proj2 Hm_inf) (4 := proj2 Hpft)
           (5 := CEP.Lemmas.Equal_submap (proj1 Hpft)) (7 := HexpandBranches) (8 := Hsem_stmts) ;
      intro Hinductive.
apply Sem_frag_stmts_cat in Hsem_stmts.
destruct Hsem_stmts as [vm_comp [ct_comp Hsem_stmts]].
generalize (stmts_tmap_vm_and_tmap_fit_together m_stmts vm_ports vm_comp vm ct_ports ct_comp pmap pmap) ; intro Hvm_and_tmap.
destruct (stmts_tmap (pmap, pmap) m_stmts vm) as [[tm_tmap tm_scope2]|] eqn: Htm ;
      last by (discriminate (Hebfcs Logic.eq_refl) ; done).
destruct H as [H' H] ; subst tm_tmap1.
specialize Heb_tm with (1 := Logic.eq_refl).
destruct Heb_tm as [Heb_tm' Heb_tm] ; subst tm_scope2'.
specialize (Hinductive Htmtm_inf) with (2 := Logic.eq_refl).
split ; first exact Htm_no_overlap.
exists vm_ports, ct_ports.
split ; first by apply Hsem_ports.
specialize (Sem_frag_stmts_compatible) with (1 := proj2 Hsem_stmts) ; intro Hsf_sub.
assert (ct_sub_vm ct_ports vm_ports tm_tmap).
      intro k ; destruct Hpft as [_ [_ [_ [Hpft _]]]] ; specialize (Hpft k).
      destruct (CEP.find k ct_ports) as [[| |expr]|] ; try by exact Hpft.
      destruct (CEP.find k vm_ports) as [[gt|gt|gt|gt|gt]|] ; try by exact Hpft.
      1-3: generalize (type_of_expr_submap expr pmap tm_tmap (proj1 (proj2 Htm_sub))) ; intro H0.
      1-3: destruct (type_of_expr expr pmap) as [[[gt_expr| |] Hgt_expr_exp]|] ; try by contradiction Hpft.
      1-3: by rewrite H0 //.
specialize Hvm_and_tmap with (1 := Htmtm_inf) (2 := proj2 Hm_inf) (3 := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 Hpft)))))) (4 := H0) (5 := proj1 (proj2 (proj2 (proj2 (proj2 Hpft)))))
           (6 := CEP.Lemmas.submap_refl _) (7 := Logic.eq_refl) (8 := proj1 Hsem_stmts) (9 := CEP.Lemmas.submap_refl _) (10 := proj1 Hsf_sub) ;
      clear H0.
apply Hinductive.
* (* This is almost (proj2 Hvm_and_tmap);
     the only difference is between vm_comp and vm,
     but that can be shown to be the same using Lemma convert_to_connect_stmts_Sem.
  *)
  intro k.
  destruct Hvm_and_tmap as [Htmtm_sub_vm Hvm_sub_tmtm] ; specialize (Htmtm_sub_vm k) ; specialize (Hvm_sub_tmtm k).
  destruct Hsf_sub as [Hsf_sub _] ; specialize (Hsf_sub k).
  destruct (CEP.find k tm_tmap) as [[ft [| | | |]]|] ; try done.
  1-4: destruct (CEP.find k vm_comp) as [[gt|gt|gt|gt|gt]|] ; try done.
  1-5: by rewrite (Hsf_sub _ Logic.eq_refl) Htmtm_sub_vm //.
  (* Here I need that CEP.find k vm = None because CEP.find k vm_comp = None;
     this can be proven e.g. using Lemma convert_to_connect_stmts_Sem. *)
  admit.
* intro k.
  destruct Hvm_and_tmap as [Htmtm_sub_vm _] ; specialize (Htmtm_sub_vm k).
  destruct Hsf_sub as [Hsf_sub _] ; specialize (Hsf_sub k).
  destruct (CEP.find k tm_tmap) as [[ft [| | | |]]|] ; try done.
  1-3: destruct (CEP.find k vm_comp) as [[gt|gt|gt|gt|gt]|] ; try done.
  1-5: by rewrite (Hsf_sub _ Logic.eq_refl) //.
Admitted.
