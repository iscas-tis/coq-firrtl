From Coq Require Import FunInd FMaps FMapAVL OrderedType ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat ssrint eqtype seq ssrfun.
From simplssrlib Require Import Types SsrOrder FSets FMaps Tactics Var Store.
From nbits Require Import NBits.
From firrtl Require Import Firrtl Env HiEnv HiFirrtl ModuleGraph TopoSort. 

(* Correctness theorem for stmts_tmap:
- All of the below holds if the output is Some (tmap, var2exprsmap).
  - The tmap contains exactly the entries for all components that appear in the statement sequence
    (in addition to the input parameter). [“contains at least” is needed for correctness; “contains
    at most” is only needed to show minimality.]
  - The var2exprsmap contains all connections to implicit-width components declared in the statement sequence.
  * The var2exprsmap does not contain any connection that is not present in the statement sequence
    (if the input parameter var2exprsmap is the empty map).
    [This is only needed to show minimality.] *)

Fixpoint stmt_tmap_is_correct (t_in : CEP.t ftype) (v2e_in : var2exprsmap) (s : HiFP.hfstmt) (t_out: CEP.t ftype) (v2e_out: var2exprsmap) : Prop :=
   match s with
   | Swire v t => CEP.find v t_in = None ->
                        CEP.find v t_out = Some t
                     /\ (forall v' : ProdVarOrder.t, v != v' -> CEP.find v' t_in = CEP.find v' t_out)
                     /\ module_graph_vertex_set_p.Equal v2e_in v2e_out
   | Sreg v r => CEP.find v t_in = None ->
                       CEP.find v t_out = Some (type r)
                    /\ (forall v' : ProdVarOrder.t, v != v' -> CEP.find v' t_in = CEP.find v' t_out)
                    /\ (reset r = NRst ProdVarOrder.T -> module_graph_vertex_set_p.Equal v2e_in v2e_out)
   | Snode v e => CEP.find v t_in = None ->
                  (type_of_hfexpr e t_in != None) ->
                       CEP.find v t_out = type_of_hfexpr e t_in
                    /\ (forall v' : ProdVarOrder.t, v != v' -> CEP.find v' t_in = CEP.find v' t_out)
                    /\ (module_graph_vertex_set_p.Equal v2e_in v2e_out)
   | Sfcnct v e =>    CEP.Equal t_in t_out
                   /\ (* forall t : ftype, CEP.find v t_in = Some t -> the connection is in v2e*) True
   | Swhen c ss_t ss_f => exists (t_internal : CEP.t ftype) (v2e_internal : var2exprsmap),
                                stmts_tmap_is_correct t_in v2e_in ss_t t_internal v2e_internal
                             /\ stmts_tmap_is_correct t_internal v2e_internal ss_f t_out v2e_out
   | _ =>    CEP.Equal t_in t_out
          /\ module_graph_vertex_set_p.Equal v2e_in v2e_out
   end
with stmts_tmap_is_correct (t_in : CEP.t ftype) (v2e_in : var2exprsmap) (ss : HiFP.hfstmt_seq) (t_out: CEP.t ftype) (v2e_out: var2exprsmap) : Prop :=
   match ss with
   | Qnil => CEP.Equal t_in t_out /\ module_graph_vertex_set_p.Equal v2e_in v2e_out
   | Qcons s ss' => exists (t_internal : CEP.t ftype) (v2e_internal : var2exprsmap),
                          stmt_tmap_is_correct t_in v2e_in s t_internal v2e_internal
                       /\ stmts_tmap_is_correct t_internal v2e_internal ss' t_out v2e_out
   end.

Theorem stmts_tmap_correct :
   forall (ss : HiFP.hfstmt_seq) (t_in : CEP.t ftype) (v2e_in: var2exprsmap) (t_out: CEP.t ftype) (v2e_out: var2exprsmap),
      stmts_tmap (t_in, v2e_in) ss = Some (t_out, v2e_out) ->
         stmts_tmap_is_correct t_in v2e_in ss t_out v2e_out.
Proof.
induction ss as [|s ss'].
* intros.
  simpl stmts_tmap_is_correct.
  simpl stmts_tmap in H.
  injection H ; intros.
  split.
  + unfold CEP.Equal ; intro ; rewrite H1 ; reflexivity.
  + unfold module_graph_vertex_set_p.Equal ; intro ; rewrite H0 ; reflexivity.
* intros.
  simpl stmts_tmap_is_correct.
  simpl stmts_tmap in H.
  destruct (stmt_tmap (t_in, v2e_in) s) eqn: H0.
  + destruct p as [t_internal v2e_internal].
    exists t_internal, v2e_internal.
    split.
    - destruct s.
      * (* Sskip *)
        simpl stmt_tmap_is_correct.
        simpl stmt_tmap in H0.
        injection H0 ; intros.
        split.
        + intro ; rewrite H2 ; reflexivity.
        + unfold module_graph_vertex_set_p.Equal ; intro ; rewrite H1 ; reflexivity.
      * (* Swire *)
        simpl stmt_tmap_is_correct.
        simpl stmt_tmap in H0.
        intro.
        rewrite H1 in H0.
        injection H0 ; intros.
        split.
        + rewrite -H3 CEP.Lemmas.find_add_eq // /HiFirrtl.PVM.SE.eq eq_refl //.
        split.
        + intros.
          apply negbTE in H4.
          rewrite -H3 CEP.Lemmas.find_add_neq // /HiFirrtl.PVM.SE.eq eq_sym H4 //.
        + unfold module_graph_vertex_set_p.Equal ; intro ; rewrite H2 ; reflexivity.
      * (* Sreg *)
        simpl stmt_tmap_is_correct.
        simpl stmt_tmap in H0.
        intro.
        rewrite H1 in H0.
        destruct (reset h).
        + injection H0 ; intros.
          split.
          - rewrite -H3 CEP.Lemmas.find_add_eq // /HiFirrtl.PVM.SE.eq eq_refl //.
          split.
          - intros.
            apply negbTE in H4.
            rewrite -H3 CEP.Lemmas.find_add_neq // /HiFirrtl.PVM.SE.eq eq_sym H4 //.
          - unfold module_graph_vertex_set_p.Equal ; intro ; rewrite H2 ; reflexivity.
        +(* destruct (tmap_add_expr_connect (v2e_in, s.2) s.1 h1 (type h)) eqn: Htmap ; rewrite Htmap in H0 ; try done.
          injection H0 ; intros.
          split.
          - rewrite -H3 CEP.Lemmas.find_add_eq // /HiFirrtl.PVM.SE.eq eq_refl //.
          - split ; try done.
            intros.
            apply negbTE in H4.
            rewrite -H3 CEP.Lemmas.find_add_neq // /HiFirrtl.PVM.SE.eq eq_sym H4 //.
      * (* Smem has not yet been implemented *)
        unfold stmt_tmap in H0 ; done.
      * (* Sinst has not yet been implemented *)
        unfold stmt_tmap in H0 ; done.
      * (* Snode *)
        simpl stmt_tmap_is_correct.
        simpl stmt_tmap in H0.
        destruct (CEP.find s t_in) eqn: H1 ; try done.
        destruct (type_of_hfexpr h t_in) eqn: H2 ; try done.
        destruct (tmap_add_expr_connect (v2e_in, s.2) s.1 h f) eqn: H3 ; try done ; rewrite H3 in H0.
        injection H0 ; intros.
        split.
        + intro.

    - apply IHss ; exact H.
  + discriminate H.*)
Admitted.

(* return a fgtyp with the larger width for gtyp *)
Definition max_fgtyp (ft1 : fgtyp) (ft2 : fgtyp) : option fgtyp :=
  match ft1, ft2 with
  | Fuint w1, Fuint_implicit w2 => Some (Fuint_implicit (max w1 w2))
  | Fsint w1, Fsint_implicit w2 => Some (Fsint_implicit (max w1 w2))
  | Fuint_implicit w1, Fuint_implicit w2 => Some (Fuint_implicit (max w1 w2))
  | Fsint_implicit w1, Fsint_implicit w2 => Some (Fsint_implicit (max w1 w2))
  | _,_ => None
  end.
  
Fixpoint expr2varlist (expr : HiFP.hfexpr) (tmap : CEP.t ftype) : option (seq ProdVarOrder.t) :=
   (* Prepends to ls the list of variable/component identifiers accessed by the expression expr.
      tmap is used to look up the identifiers.
      DNJ: I think parameter ls is superfluous, it seems to be never used.  It could be replaced by [::]. *)
   match expr with
   | Econst _ _ => Some nil
   | Eref ref => match base_ref ref tmap with
                | Some (pv,_) => Some [:: pv]
                | None => None
                end
  | Eprim_unop _ e1 => expr2varlist e1 tmap
  | Eprim_binop _ e1 e2 => match expr2varlist e1 tmap, expr2varlist e2 tmap with
                          | Some ls', Some ls'' => Some (ls' ++ ls'')
                          | _,_ => None
                          end
  | Emux e1 e2 e3 => match expr2varlist e1 tmap, expr2varlist e2 tmap, expr2varlist e3 tmap with
                    | Some ls', Some ls'', Some ls''' => Some (ls' ++ ls'' ++ ls''')
                    | _,_,_ => None
                    end
  | Evalidif e1 e2 => match expr2varlist e1 tmap, expr2varlist e2 tmap with
                      | Some ls', Some ls'' => Some (ls' ++ ls'')
                      | _,_ => None
                      end
  | Ecast _ e => expr2varlist e tmap
   end.

Definition updg (key : ProdVarOrder.t) (v : seq ProdVarOrder.t) (map : ProdVarOrder.t -> seq ProdVarOrder.t) : ProdVarOrder.t -> seq ProdVarOrder.t :=
    fun (y : ProdVarOrder.t) => if y == key then v else map y.

Fixpoint drawel (v : ProdVarOrder.t) (el : seq HiFP.hfexpr) (tmap : CEP.t ftype) (newg : ProdVarOrder.t -> seq ProdVarOrder.t) (vertices : seq ProdVarOrder.t) : option ((ProdVarOrder.t -> seq ProdVarOrder.t) * (seq ProdVarOrder.t)) :=
   (* recursively draw dependencies in el for element v *)
   (* v: vertex in the dependency graph that is updated
      el: list of expressions that need to be considered for adding dependency edges
      tmap: map of (known) types of components
      newg: current edges in the dependency graph
      vertices: current vertices in the dependency graph
      Return value: a pair (edges in the dependency graph, vertices in the dependency graph)
      containing additionally the dependencies from el *)
   match el with
   | nil => Some (newg, vertices)
   | e :: etl => let vl := expr2varlist e tmap in
                 match vl with (* all elements appearing in e *)
                 | Some ls => let g' := List.fold_left (fun tempg tempv => updg tempv (cons v (tempg tempv)) tempg) ls newg in
                              drawel v etl tmap g' (vertices ++ ls)
                 | None => None
                 end
   end.

Fixpoint drawg depandencyls (tmap : CEP.t ftype) (expli_reg : seq ProdVarOrder.t) (newg : ProdVarOrder.t -> seq ProdVarOrder.t) (vertices : seq ProdVarOrder.t) : option ((ProdVarOrder.t -> seq ProdVarOrder.t) * (seq ProdVarOrder.t)) :=
   (* construct the dependency graph:
      depandencyls: list of pairs (vertex in the module graph, list of expressions)
      tmap: map of (known) types of components
      expli_reg: list of completely explicit-width components; they can be ignored
      newg: current edges in the dependency graph (will be extended by drawel)
      vertices: current vertices in the dependency graph (will be extended by drawel)
      Return value: a pair (edges in the dependency graph, vertices in the dependency graph)
      *)
   match depandencyls with
   (* list of all pairs (element as key, its connections as value) *)
   | nil => Some (newg, vertices)
  | (v, el) :: vtl => if ((fst v, N0) \in expli_reg) then drawg vtl tmap expli_reg newg vertices
                      else match drawel v el tmap newg vertices with (* for a certain element v, draw dependencies in the el to newg *)
                      | Some (g', vertices') => drawg vtl tmap expli_reg g' vertices'
                      | None => None
                      end
  end.

(* init 应该是implicit，l中无所谓 *)
Fixpoint max_ftlist (l : seq fgtyp) (init : fgtyp): option fgtyp :=
  match l with
  | nil => Some init
  | t :: tl => match max_ftlist tl init with
              | Some t' => max_fgtyp t t'
              | None => None
              end
  end.
  
Fixpoint fil_ftlist (l : seq (option ftype)) : option (seq fgtyp) :=
  match l with
  | nil => Some [::]
  | (Some (Gtyp gt)) :: tl => match fil_ftlist tl with
                      | Some tl' => Some (gt :: tl')
                      | None => None
                      end
  | _ :: tl => None
  end.

Definition InferWidth_fun (v : ProdVarOrder.t) (el : seq HiFP.hfexpr) (tmap : CEP.t ftype) : option (CEP.t ftype) :=
(* updates the width of v in tmap so that it is at least the width of the expressions in list el. *)
  match fil_ftlist (map (fun e => type_of_hfexpr e tmap) el) with
  | Some eftl => match CEP.find (fst v, N0) tmap with
                | Some init => match ft_find_sub init v.2 with
                                | Some initt => if not_implicit initt then Some tmap
                                                       else match max_ftlist eftl initt with
                                                        | Some nt => match ft_set_sub init nt v.2 with
                                                                    | Some nt0 => Some (CEP.add (fst v, N0) nt0 tmap)
                                                                    | None => None
                                                                    end
                                                        | None => None
                                                        end
                                | _ => None
                                end
                | None => None
                end
  | None => None
  end.
  
Fixpoint InferWidths_fun (od : seq ProdVarOrder.t) (var2exprs : var2exprsmap) (tmap : CEP.t ftype) : option (CEP.t ftype) :=
(* od contains the (implicit-width) ground-type subcomponents in topological order.
   (It is ok if od contains other components, but it is not necessary.)
   var2exprs is a map that maps every ground-type subcomponent to a list of expressions (namely expressions that the (sub)component is connected from).
   tmap is the map of types for every component that has been defined (but there are no separate entries for subcomponents);
   the result is a modified tmap, which ensures that the width of every implicit-width component is large enough. *)
  match od with
  | nil => Some tmap
  | vhd :: vtl => match module_graph_vertex_set_p.find vhd var2exprs with 
                  | Some el => match InferWidth_fun vhd el tmap with
                          | Some tm => InferWidths_fun vtl var2exprs tm
                          | None => None
                          end
                  | None => None
                  end
  end.

Fixpoint list_expligref (n : nat) (pv : ProdVarOrder.t) (checkt : ftype) : option (seq ProdVarOrder.t) := 
  match n with
  | 0 => Some nil
  | S m => match list_expligref m pv checkt, ft_find_sub checkt (N.of_nat m) with
          | Some ls, Some gt => if not_implicit gt then Some ls
                                else Some ((fst pv, N.add (snd pv) (N.of_nat m)) :: ls)
          | _, _ => None
          end
  end.

Fixpoint explireg_stmt (st : HiFP.hfstmt) : option (seq ProdVarOrder.t) :=
  match st with
  | Sskip => Some nil 
  | Swire v t => Some nil
  | Sreg v r => let len := tmap_type_size (type r) in 
                list_expligref len v (type r)
  | Smem v m => (*TBD*) Some nil
  | Sinst v inst => (*TBD*) Some nil
  | Snode v e => Some nil
  | Sfcnct v e => Some nil
  | Sinvalid _ => Some nil
  | Swhen _ s1 s2 => match explireg_stmts s1 , explireg_stmts s2 with
                    | Some ls, Some ls' => Some (ls ++ ls')
                    | _,_ => None
                    end
  end
with explireg_stmts (sts : HiFP.hfstmt_seq) :=
  match sts with
  | Qnil => Some nil
  | Qcons s ss => match explireg_stmt s, explireg_stmts ss with
                  | Some ls, Some ls' => Some (ls ++ ls')
                  | _,_ => None
                  end
  end.

Definition emptyg : (ProdVarOrder.t -> seq ProdVarOrder.t) := (fun _ => [::]).

Definition InferWidths_stage1 (F : HiFP.hfmodule) : option (CEP.t ftype) :=
(* infer widths of implicit-width components among the ports and statements in F.
   A full version would not work on one module alone but on all modules in a circuit together,
   but the principle remains the same. Therefore, let’s just run the algorithm on a single module for now. *)
match F with
| FExmod _ _ _ => None
| FInmod v ps ss =>
    match stmts_tmap (ports_tmap ps, module_graph_vertex_set_p.empty (seq HiFP.hfexpr)) ss, explireg_stmts ss with
    | Some (tmap', var2exprs), Some expli_reg => (* tmap' : all the expli/uninferred impli aggr&gtyp are stored here
                                            var2exprs : every connected elements are stored *)
           match drawg (module_graph_vertex_set_p.elements var2exprs) tmap' expli_reg emptyg nil with
           | Some (theg, vertices) => (* theg : new drawn graph
                                         vertices : set for topo sort to start with *)
               match TopoSort.topo_sort vertices theg with
               | TopoSort.Sorted inferorder => InferWidths_fun inferorder var2exprs tmap'
               | _ => None
               end
           | None => None
           end
       | _,_ => None
       end
end.

Fixpoint expli_ftype (t : ftype) : ftype :=
  match t with
  | Gtyp (Fuint_implicit w) => Gtyp (Fuint w)
  | Gtyp (Fsint_implicit w) => Gtyp (Fsint w)
  | Gtyp _ => t
  | Atyp t_ref n_ref => Atyp (expli_ftype t_ref) n_ref
  | Btyp ff_ref => Btyp (expli_ftype_ff ff_ref)
  end
with expli_ftype_ff (ff_ref : ffield) : ffield :=
  match ff_ref with
  | Fflips v_ref Nflip t_ref ff_ref' => Fflips v_ref Nflip (expli_ftype t_ref) (expli_ftype_ff ff_ref') 
  | Fflips v_ref Flipped t_ref ff_ref' => Fflips v_ref Flipped (expli_ftype t_ref) (expli_ftype_ff ff_ref') 
  | Fnil => Fnil
  end.

Definition InferWidths_transp (p : HiFP.hfport) (tmap : CEP.t ftype) : option HiFP.hfport :=
  (* changes the type in one port declaration, depending on the information in tmap, to an explicit-width type *)
  match p with
  | Finput v t => if (ftype_not_implicit t) then Some p
                  else (match CEP.find v tmap with
                  | Some ft => (* if t has implicit width, update the hfport with ft and change it to explicit width *)
                                Some (Finput v (expli_ftype ft))
                  | _ => None
                  end)
  | Foutput v t => if (ftype_not_implicit t) then Some p
                  else (match CEP.find v tmap with
                  | Some ft => (* if t has implicit width, update the hfport with ft and change it to explicit width *)
                                Some (Foutput v (expli_ftype ft))
                  | _ => None
                  end)
  end.

Fixpoint InferWidths_transps (ps : seq HiFP.hfport) (tmap : CEP.t ftype) : option (seq HiFP.hfport) :=
  (* changes the types in a sequence of port declarations, depending on the information in tmap, to explicit-width types *)
  match ps with
  | nil => Some nil
  | p :: tl => match InferWidths_transp p tmap, InferWidths_transps tl tmap with
                  | Some n, Some nss => Some (n :: nss)
                  | _, _ => None
                  end
  end.

Fixpoint InferWidths_transs (s : HiFP.hfstmt) (tmap : CEP.t ftype) : option HiFP.hfstmt :=
(* with infered tmap, transform the ports and declarations *)
  match s with
  | Sskip => Some s
  | Swire v t => if (ftype_not_implicit t) then Some s
                  else (match CEP.find v tmap with
                  | Some ft => (* if t has implicit width, update the hfstmt with ft and change it to explicit width *)
                                Some (Swire v (expli_ftype ft))
                  | _ => None
                  end)
  | Sreg v r => if (ftype_not_implicit (type r)) then Some s
                else (match CEP.find v tmap with
                | Some ft => (* if t has implicit width, update the hfstmt with ft and change it to explicit width *)
                              Some (Sreg v (mk_freg (expli_ftype ft) (clock r) (reset r)))
                | _ => None
                end)
  | Smem v m => (*TBD*) Some s
  | Sinst v inst => (*TBD*) Some s
  | Snode v e => Some s
  | Sfcnct v e => Some s
  | Sinvalid _ => Some s
  | Swhen c s1 s2 => match InferWidths_transss s1 tmap, InferWidths_transss s2 tmap with
                    | Some n1, Some n2 => Some (Swhen c n1 n2)
                    | _, _ => None
                    end
  end
with InferWidths_transss (sts : HiFP.hfstmt_seq) (tmap : CEP.t ftype) : option HiFP.hfstmt_seq :=
  match sts with
  | Qnil => Some (Qnil ProdVarOrder.T)
  | Qcons s ss => match InferWidths_transs s tmap, InferWidths_transss ss tmap with
                  | Some n, Some nss => Some (Qcons n nss)
                  | _, _ => None
                  end
  end.

Definition InferWidths_stage2 (F : HiFP.hfmodule) (tmap : CEP.t ftype) : option HiFP.hfmodule :=
match F with
  | FExmod _ _ _ => None
  | FInmod v ps ss => match InferWidths_transps ps tmap, InferWidths_transss ss tmap with
                      | Some nps, Some nss => Some (FInmod v nps nss)
                      | _, _ => None
                      end
  end.

Lemma num_ref_eq : forall checkt nt0, ftype_equiv checkt nt0 -> tmap_type_size checkt = tmap_type_size nt0
with num_ref_eq_f : forall checkf nf0, fbtyp_equiv checkf nf0 -> tmap_type_size_fields checkf = tmap_type_size_fields nf0.
Proof.
  clear num_ref_eq.
  elim.
  intro gt.
  elim.
  intros gt0 Heq.
  simpl; done.
  intros; simpl in H0; discriminate.
  intros; simpl in H; discriminate.

  intros f H n.
  elim.
  intros; simpl in H0; discriminate.
  intros f0 H' n0 Heq; clear H'.
  simpl; simpl in Heq.
  move /andP : Heq => [_ Heq].
  apply H in Heq; rewrite Heq; done.
  intros; simpl in H; discriminate.

  intro f. 
  elim.
  intros; simpl in H; discriminate.
  intros; simpl in H; discriminate.
  intro f0.
  simpl; intro Heq; apply num_ref_eq_f in Heq.
  rewrite Heq; done.

  clear num_ref_eq_f.
  elim.
  intros.
  simpl in H.
  case Hnf0 : nf0; rewrite Hnf0 in H; try discriminate; try done.
  intros v fl ft ff Heq.
  elim.
  intros.
  simpl in H. 
  case Hfl : fl; rewrite Hfl in H; discriminate.
  intros v0 fl0 ft0 ff0 H' Heq0; clear H'.
  simpl.
  simpl in Heq0.
  case Hfl : fl; rewrite Hfl in Heq0.
  case Hfl0 : fl0; rewrite Hfl0 in Heq0; try discriminate.
  move /andP : Heq0 => [Heq0 Heq1].
  move /andP : Heq0 => [_ Heq2].
  apply num_ref_eq in Heq2.
  apply Heq in Heq1.
  rewrite Heq1 Heq2; done.
  case Hfl0 : fl0; rewrite Hfl0 in Heq0; try discriminate.
  move /andP : Heq0 => [Heq0 Heq1].
  move /andP : Heq0 => [_ Heq2].
  apply num_ref_eq in Heq2.
  apply Heq in Heq1.
  rewrite Heq1 Heq2; done.
Qed.

Lemma ft_set_sub_eq : forall checkt nt' nt0 n init, ft_find_sub checkt n = Some init -> fgtyp_equiv init nt' -> ft_set_sub checkt nt' n = Some nt0 -> ftype_equiv checkt nt0
with ft_set_sub_eq_f : forall checkf nf' nf0 n init, ft_find_ff checkf n = Some init -> fgtyp_equiv init nf' -> ft_set_sub_f checkf nf' n = Some nf0 -> fbtyp_equiv checkf nf0.
Proof.
  clear ft_set_sub_eq.
  elim.
  intros f nt nt0 n init Hfind Heq Hset.
  simpl in Hfind; simpl in Hset.
  case Ha : (n == 0%num); rewrite Ha in Hfind Hset; try discriminate.
  inversion Hfind; clear Hfind H0.
  inversion Hset; clear Hset.
  simpl; done.
  
  (* set aggt *)
  intros f H n.
  intros nt nt0 cnt init Hfind Heq Hset.
  simpl in Hset.
  simpl in Hfind.
  case Hset' : (ft_set_sub f nt cnt) => [natyp|]; rewrite Hset' in Hset; try discriminate.
  inversion Hset; clear Hset H1.
  simpl.
  apply rwP with (P := (n == n) /\ ftype_equiv f natyp).
  apply andP.
  split; try done.
  move : Hfind Heq Hset'.
  apply H.

  (* set btyp *)
  intros f nt nt0 cnt init Hfind Heq Hset.
  simpl in Hfind.
  simpl in Hset.
  case Ha : (tmap_type_size_fields f <= cnt); rewrite Ha in Hfind Hset; try discriminate.
  case Hset' : (ft_set_sub_f f nt cnt) => [newf|]; rewrite Hset' in Hset; try discriminate.
  inversion Hset; clear Hset.
  simpl.
  move : Hfind Heq Hset'.
  apply ft_set_sub_eq_f.

  (* field *)
  clear ft_set_sub_eq_f.
  induction checkf.
  intros.
  simpl in H; discriminate.
  intros nt nf0 cnt init Hfind Heq Hset.
  simpl in Hfind.
  simpl in Hset.
  case Ha : (N.of_nat (tmap_type_size f0) <= cnt); rewrite Ha in Hfind Hset.
  case Hset' : (ft_set_sub_f checkf nt (cnt - N.of_nat (tmap_type_size f0))) => [newf|]; rewrite Hset' in Hset; try discriminate.
  inversion Hset; clear Hset.
  simpl.
  case Hf : f.
  apply rwP with (P := (v == v) && ftype_equiv f0 f0 /\ fbtyp_equiv checkf newf).
  apply andP.
  split; try done.
  apply rwP with (P := (v == v) /\ ftype_equiv f0 f0).
  apply andP.
  split; try done.
  admit.
  move : Hfind Heq Hset'.
  apply IHcheckf.
  apply rwP with (P := (v == v) && ftype_equiv f0 f0 /\ fbtyp_equiv checkf newf).
  apply andP.
  split; try done.
  apply rwP with (P := (v == v) /\ ftype_equiv f0 f0).
  apply andP.
  split; try done.
  admit.
  move : Hfind Heq Hset'.
  apply IHcheckf.
  case Hset' : (ft_set_sub f0 nt cnt) => [newt'|]; rewrite Hset' in Hset; try discriminate.
  inversion Hset; clear Hset.
  simpl.
  case Hf : f.
  apply rwP with (P := (v == v) && ftype_equiv f0 newt' /\ fbtyp_equiv checkf checkf).
  apply andP.
  split; try done.
  apply rwP with (P := (v == v) /\ ftype_equiv f0 newt').
  apply andP.
  split; try done.
  move : Hfind Heq Hset'.
  apply ft_set_sub_eq.
  admit.
  apply rwP with (P := (v == v) && ftype_equiv f0 newt' /\ fbtyp_equiv checkf checkf).
  apply andP.
  split; try done.
  apply rwP with (P := (v == v) /\ ftype_equiv f0 newt').
  apply andP.
  split; try done.
  move : Hfind Heq Hset'.
  apply ft_set_sub_eq.
  admit.
Admitted.

Lemma set_find_sub : forall checkt nt nt0 n, ft_set_sub checkt nt n = Some nt0 -> ftype_equiv checkt nt0 -> ft_find_sub nt0 n = Some nt
with set_find_sub_f : forall checkf nf nf0 n, ft_set_sub_f checkf nf n = Some nf0 -> fbtyp_equiv checkf nf0 -> ft_find_ff nf0 n = Some nf.
Proof.
  clear set_find_sub.
  elim.
  intro f.
  intros nt nt0 n Hset Heq.
  simpl in Heq.
  simpl in Hset.
  case Ha : (n == N0); rewrite Ha in Hset; try discriminate.
  inversion Hset; clear Hset H0.
  case Hnt0 : (nt0) => [f0||]; rewrite Hnt0 in Heq; try discriminate.
  simpl; rewrite Ha; done.

  intros f Hg fn. 
  intros nt nt0 n Hset Heq.
  simpl in Hset.
  case Hset' : (ft_set_sub f nt n) => [natyp|]; rewrite Hset' in Hset; try discriminate.
  inversion Hset; clear Hset.
  simpl.
  rewrite -H0 in Heq; simpl in Heq.
  move /andP : Heq => [_ Heq].
  apply Hg; try done.

  intros f nt nt0 n Hset Heq.
  simpl in Hset.
  case Ha : (tmap_type_size_fields f <= n); rewrite Ha in Hset; try discriminate.
  case Hset' : (ft_set_sub_f f nt n) => [newf|]; rewrite Hset' in Hset; try discriminate.
  inversion Hset; clear Hset.
  simpl.
  assert (tmap_type_size_fields f = tmap_type_size_fields newf).
  apply num_ref_eq_f.
  rewrite -H0 in Heq; simpl in Heq; done.
  rewrite -H; clear H; rewrite Ha.
  rewrite -H0 in Heq; simpl in Heq.
  apply set_find_sub_f with (checkf := f); try done.

  clear set_find_sub_f.
  intros checkf.
  induction checkf.
  intros nf nf0 n Hset Heq.
  simpl in Hset; discriminate.

  intros nf hf0 n Hset Heq.
  simpl in Hset.
  case Ha : (N.of_nat (tmap_type_size f0) <= n); rewrite Ha in Hset.
  case Hset' : (ft_set_sub_f checkf nf (n - N.of_nat (tmap_type_size f0))) => [newf|]; rewrite Hset' in Hset; try discriminate.
  inversion Hset; clear Hset.
  assert (fbtyp_equiv checkf newf).
  rewrite -H0 in Heq.
  simpl in Heq.
  case Hf : f; rewrite Hf in Heq.
  move /andP : Heq => [_ Heq]; done.
  move /andP : Heq => [_ Heq]; done.
  apply IHcheckf in Hset'; try done.
  rewrite -Hset'.
  simpl; rewrite Ha; done.

  case Hset' : (ft_set_sub f0 nf n) => [newt'|]; rewrite Hset' in Hset; try discriminate.
  inversion Hset; clear Hset.
  simpl. 
  assert ((tmap_type_size f0) = (tmap_type_size newt')).
  rewrite -H0 in Heq.
  simpl in Heq.
  case Hf : f; rewrite Hf in Heq.
  move /andP : Heq => [Heq _].
  move /andP : Heq => [_ Heq].
  apply num_ref_eq; done.
  move /andP : Heq => [Heq _].
  move /andP : Heq => [_ Heq].
  apply num_ref_eq; done.
  rewrite H in Ha; clear H.
  simpl; rewrite Ha.
  apply set_find_sub with (checkt := f0); try done.
  rewrite -H0 in Heq.
  simpl in Heq.
  case Hf : f; rewrite Hf in Heq.
  move /andP : Heq => [Heq _].
  move /andP : Heq => [_ Heq]; done.
  move /andP : Heq => [Heq _].
  move /andP : Heq => [_ Heq]; done.
Qed.

Lemma infer_compatible : forall te otype nt, max_fgtyp te otype = Some nt -> connect_fgtyp_compatible nt otype /\ connect_fgtyp_compatible nt te.
Proof.
  intros.
  (* ground match ground *)
  case Hgt : te => [w'|w'|w'|w'|||]; rewrite Hgt in H.
  (* te = Gtyp (uint w') *)
  - case Hogt : otype => [ow'|ow'|ow'|ow'|||]; rewrite Hogt in H; simpl in H; try discriminate.
    (* otype = Gtyp (uint ow') *)
    inversion H; clear H. 
    rewrite /connect_fgtyp_compatible.
    simpl.
    rewrite Nat.max_comm.
    split.
    apply rwP with (P := (ow' <= Nat.max ow' w') /\ true).
    apply andP.
    split; try done. 
    (* rewrite <- Nat.le_max_l. *)
    admit.
    admit.
  - case Hogt : otype => [ow'|ow'|ow'|ow'|||]; rewrite Hogt in H; simpl in H; try discriminate.
    (* otype = Gtyp (uint ow') *)
    inversion H; clear H. 
    rewrite /connect_fgtyp_compatible.
    simpl.
    rewrite Nat.max_comm.
    (*specialize Nat.le_max_l with (n := w') (m := ow').*)
    admit.
  - case Hogt : otype => [ow'|ow'|ow'|ow'|||]; rewrite Hogt in H; simpl in H; try discriminate.
    (* otype = Gtyp (uint ow') *)
    inversion H; clear H. 
    rewrite /connect_fgtyp_compatible.
    simpl.
    rewrite Nat.max_comm.
    (*specialize Nat.le_max_l with (n := w') (m := ow').*)
    admit.
  - case Hogt : otype => [ow'|ow'|ow'|ow'|||]; rewrite Hogt in H; simpl in H; try discriminate.
    (* otype = Gtyp (uint ow') *)
    inversion H; clear H. 
    rewrite /connect_fgtyp_compatible.
    simpl.
    rewrite Nat.max_comm.
    (*specialize Nat.le_max_l with (n := w') (m := ow').*)
    admit.
  - case Hogt : otype => [ow'|ow'|ow'|ow'|||]; rewrite Hogt in H; simpl in H; try discriminate.
  - case Hogt : otype => [ow'|ow'|ow'|ow'|||]; rewrite Hogt in H; simpl in H; try discriminate.
  - case Hogt : otype => [ow'|ow'|ow'|ow'|||]; rewrite Hogt in H; simpl in H; try discriminate.
Admitted.

Lemma fgtyp_equiv_dlvr : forall t1 t2 t3, fgtyp_equiv t1 t2 -> fgtyp_equiv t2 t3 -> fgtyp_equiv t1 t3.
Proof.
  intros.
  case Ht1 : t1; case Ht2 : t2; case Ht3 : t3; rewrite Ht1 Ht2 in H; rewrite Ht2 Ht3 in H0; simpl in H; simpl in H0; simpl; try done; try discriminate.
Qed.

Lemma ftype_equiv_dlvr : forall t1 t2 t3, ftype_equiv t1 t2 -> ftype_equiv t2 t3 -> ftype_equiv t1 t3
with ftype_equiv_dlvr_f : forall t1 t2 t3, fbtyp_equiv t1 t2 -> fbtyp_equiv t2 t3 -> fbtyp_equiv t1 t3.
Proof.
  elim.
  intros gt1 t2 t3 H H0.
  case Ht2 : t2 => [gt2|atyp2 n2|btyp2]; rewrite Ht2 in H H0; simpl in H; try discriminate.
  case Ht3 : t3 => [gt3|atyp3 n3|btyp3]; rewrite Ht3 in H H0; simpl in H0; simpl; try done; try discriminate.
  move : H H0; apply fgtyp_equiv_dlvr.

  intros atyp1 IH n1 t2 t3 H H0.
  case Ht2 : t2 => [gt2|atyp2 n2|btyp2]; rewrite Ht2 in H H0; simpl in H; try discriminate.
  case Ht3 : t3 => [gt3|atyp3 n3|btyp3]; rewrite Ht3 in H H0; simpl in H0; simpl; try done; try discriminate.
  move /andP : H => [H1 H].
  move /andP : H0 => [H2 H0].
  move /eqP : H1 => H1.
  move /eqP : H2 => H2.
  apply rwP with (P := (n1 == n3) /\ ftype_equiv atyp1 atyp3).
  apply andP.
  split.
  rewrite H1 -H2; try done.
  move : H H0; apply IH.

  intros btyp t2 t3 H H0.
  case Ht2 : t2 => [gt2|atyp2 n2|btyp2]; rewrite Ht2 in H H0; simpl in H; try discriminate.
  case Ht3 : t3 => [gt3|atyp3 n3|btyp3]; rewrite Ht3 in H H0; simpl in H0; simpl; try done; try discriminate.
  move : H H0; apply ftype_equiv_dlvr_f.

  elim.
  intros t2 t3 H H0.
  case Ht2 : t2 => [|v2 fl2 ft2 f2]; rewrite Ht2 in H H0; simpl in H; try discriminate.
  case Ht3 : t3 => [|v3 fl3 ft3 f3]; rewrite Ht3 in H0; simpl in H0; try discriminate.
  simpl; done.
  intros v1 fl1 ft1 f1 IH t2 t3 H H0.
  case Ht2 : t2 => [|v2 fl2 ft2 f2]; rewrite Ht2 in H H0; simpl in H; case Hf1 : fl1; rewrite Hf1 in H; try discriminate.
  case Hf2 : fl2; rewrite Hf2 in H; try discriminate.
  case Ht3 : t3 => [|v3 fl3 ft3 f3]; rewrite Ht3 Hf2 in H0; simpl in H0; try discriminate.
  case Hf3 : fl3; rewrite Hf3 in H0; try discriminate.
  simpl.
  move /andP : H => [H H1].
  move /andP : H => [H H']. 
  move /andP : H0 => [H0 H2].
  move /andP : H0 => [H0 H3].
  move /eqP : H => H.
  move /eqP : H0 => H0.
  apply rwP with (P := (v1 == v3) && ftype_equiv ft1 ft3 /\ fbtyp_equiv f1 f3).
  apply andP.
  split.
  apply rwP with (P := (v1 == v3) /\ ftype_equiv ft1 ft3).
  apply andP.
  split.
  rewrite H -H0; done.
  move : H' H3; apply ftype_equiv_dlvr.
  move : H1 H2; apply IH.
  case Hf2 : fl2; rewrite Hf2 in H; try discriminate.
  case Ht3 : t3 => [|v3 fl3 ft3 f3]; rewrite Ht3 Hf2 in H0; simpl in H0; try discriminate.
  case Hf3 : fl3; rewrite Hf3 in H0; try discriminate.
  simpl.
  move /andP : H => [H H1].
  move /andP : H => [H H']. 
  move /andP : H0 => [H0 H2].
  move /andP : H0 => [H0 H3].
  move /eqP : H => H.
  move /eqP : H0 => H0.
  apply rwP with (P := (v1 == v3) && ftype_equiv ft1 ft3 /\ fbtyp_equiv f1 f3).
  apply andP.
  split.
  apply rwP with (P := (v1 == v3) /\ ftype_equiv ft1 ft3).
  apply andP.
  split.
  rewrite H -H0; done.
  move : H' H3; apply ftype_equiv_dlvr.
  move : H1 H2; apply IH.
Qed.

Lemma max_compatible' : forall gte gt tmax, max_fgtyp gte gt = Some tmax -> (sizeof_fgtyp gte <= sizeof_fgtyp tmax) && fgtyp_equiv tmax gte && fgtyp_equiv tmax gt && (sizeof_fgtyp gt <= sizeof_fgtyp tmax).
Proof.
  intros.
  case Hgte : gte => [w'|w'|w'|w'|||]; rewrite Hgte in H.
  (* gte = Gtyp (uint w') *)
  - case Hgt : gt => [ow'|ow'|ow'|ow'|||]; rewrite Hgt in H; simpl in Hgt; simpl in H; try discriminate.
    inversion H; clear H.
    simpl.
    rewrite Nat.max_comm.
    admit. (* <= max *)
  - case Hgt : gt => [ow'|ow'|ow'|ow'|||]; rewrite Hgt in H; simpl in Hgt; simpl in H; try discriminate.
    inversion H; clear H.
    simpl.
    rewrite Nat.max_comm.
    admit. (* <= max *)
  - case Hgt : gt => [ow'|ow'|ow'|ow'|||]; rewrite Hgt in H; simpl in Hgt; simpl in H; try discriminate.
    inversion H; clear H.
    simpl.
    rewrite Nat.max_comm.
    admit. (* <= max *)
  - case Hgt : gt => [ow'|ow'|ow'|ow'|||]; rewrite Hgt in H; simpl in Hgt; simpl in H; try discriminate.
    inversion H; clear H.
    simpl.
    rewrite Nat.max_comm.
    admit. (* <= max *)
  - case Hgt : gt => [ow'|ow'|ow'|ow'|||]; rewrite Hgt in H; simpl in Hgt; simpl in H; try discriminate.
  - case Hgt : gt => [ow'|ow'|ow'|ow'|||]; rewrite Hgt in H; simpl in Hgt; simpl in H; try discriminate.
  - case Hgt : gt => [ow'|ow'|ow'|ow'|||]; rewrite Hgt in H; simpl in Hgt; simpl in H; try discriminate.
Admitted.

Lemma max_compatible : forall el tmap eftl initt tmax, fil_ftlist (map (fun e => type_of_hfexpr e tmap) el) = Some eftl -> forall expr gte, expr \in el -> type_of_hfexpr expr tmap = Some (Gtyp gte) -> max_ftlist eftl initt = Some tmax -> (sizeof_fgtyp gte <= sizeof_fgtyp tmax) && fgtyp_equiv tmax gte.
Proof.
  elim.
  intros.
  rewrite in_nil in H0; discriminate.
  intros hd tl IH tmap eftl initt tmax Hfil expr gte Hin Hgte Hmax.
  rewrite in_cons in Hin.
  case Heq : (expr == hd).
  (* case1 *)
  move /eqP : Heq => Heq.
  rewrite Heq in Hgte.
  simpl in Hfil. 
  rewrite Hgte in Hfil. 
  case Hfil' : (fil_ftlist [seq type_of_hfexpr e tmap | e <- tl]) => [eftl'|]; rewrite Hfil' in Hfil; try discriminate.
  inversion Hfil; clear Hfil.
  rewrite -H0 in Hmax.
  simpl in Hmax.
  case Hmax' : (max_ftlist eftl' initt) => [tmax'|]; rewrite Hmax' in Hmax; try discriminate.
  specialize max_compatible' with (gte := gte) (gt := tmax') (tmax := tmax); intro.
  apply H in Hmax; clear H.
  move /andP : Hmax => [H1 _].
  move /andP : H1 => [H1 _]; done.
  (* case2 *)
  rewrite Heq in Hin.
  rewrite orb_false_l in Hin; clear Heq.
  simpl in Hfil.
  case Hhd : (type_of_hfexpr hd tmap) => [t|]; rewrite Hhd in Hfil;  try discriminate.
  case Hgt : t =>[gt||]; rewrite Hgt in Hfil; try discriminate.
  case Hfil' : (fil_ftlist [seq type_of_hfexpr e tmap | e <- tl]) => [eftl'|]; rewrite Hfil' in Hfil; try discriminate.
  inversion Hfil; clear Hfil.
  rewrite -H0 in Hmax.
  simpl in Hmax.
  case Hmax' : (max_ftlist eftl' initt) => [tmax'|]; rewrite Hmax' in Hmax; try discriminate.
  apply IH with (initt := initt) (tmax := tmax') (expr := expr) (gte := gte) in Hfil'; try done.
  move /andP : Hfil' => [H1 H2].
  apply rwP with (P := (sizeof_fgtyp gte <= sizeof_fgtyp tmax) /\ fgtyp_equiv tmax gte).
  apply andP.
  split.
  specialize max_compatible' with (gte := gt) (gt := tmax') (tmax := tmax); intro H.
  apply H in Hmax; clear H.
  move /andP : Hmax => [_ H3].
  move : H1 H3.
  apply leq_trans.
  specialize max_compatible' with (gte := gt) (gt := tmax') (tmax := tmax); intro H.
  apply H in Hmax; clear H.
  move /andP : Hmax => [Hmax _].
  move /andP : Hmax => [_ H3].
  move : H3 H2.
  apply fgtyp_equiv_dlvr.
Qed.

Lemma inferwidths_a : forall a v expr_seq tmap tmap', InferWidth_fun v expr_seq tmap = Some tmap' -> 
  if (a != v) then 
  match CEP.find (fst a, N0) tmap, CEP.find (fst a, N0) tmap' with
        | Some ft, Some ft' => ft_find_sub ft (snd a) = ft_find_sub ft' (snd a)
        | _, _ => True
        end
  else True.
Proof.
  intros.
  case Heq : (a != v); try done.
  case Ha : (CEP.find (a.1, 0%num) tmap) => [ft|]; try done.
  case Ha' : (CEP.find (a.1, 0%num) tmap') => [ft'|]; try done.

  rewrite /InferWidth_fun in H.
  case Hel : (fil_ftlist [seq type_of_hfexpr e tmap | e <- expr_seq]) => [eftl|]; rewrite Hel in H; try discriminate.
  case Hfindv0 : (CEP.find (v.1, 0%num) tmap) => [init|]; rewrite Hfindv0 in H; try discriminate.
  case Hsub : (ft_find_sub init v.2) => [initt|]; rewrite Hsub in H; try discriminate.
  case Himpli : (not_implicit initt); rewrite Himpli in H.
  (* case1 *)
  inversion H; clear H.
  rewrite H1 in Ha.
  rewrite Ha in Ha'.
  inversion Ha'; done.
  (* case2 *)
  case Hmax : (max_ftlist eftl initt) => [nt|]; rewrite Hmax in H; try discriminate.
  case Hinfer : (ft_set_sub init nt v.2) => [nt0|]; rewrite Hinfer in H; try discriminate.
  inversion H; clear H.
  rewrite -H1 in Ha'.
  rewrite HiFP.PCELemmas.OP.P.F.add_neq_o in Ha'.
  rewrite Ha' in Ha. 
  inversion Ha; done.
Admitted.

Lemma inferwidths_ls : forall el a var2exprs tmap tmap' checkt checkt', InferWidths_fun el var2exprs tmap = Some tmap' -> 
  ~~(a \in el) -> CEP.find (fst a, N0) tmap' = Some checkt' -> CEP.find (fst a, N0) tmap = Some checkt -> ft_find_sub checkt (snd a) = ft_find_sub checkt' (snd a).
Proof.
  elim.
  intros.
  simpl in H. 
  inversion H; clear H. 
  rewrite H4 in H2.
  rewrite H2 in H1.
  inversion H1; done.
  intros hd tl IH a var2exprs tmap tmap' checkt checkt' Hinfer Hin Hcheckt' Hcheckt.
  rewrite in_cons in Hin.
  rewrite negb_or in Hin.
  move /andP : Hin => [H H1].
  simpl in Hinfer.
  case Hel : (module_graph_vertex_set_p.find hd var2exprs) => [el|]; rewrite Hel in Hinfer; try discriminate.
  case Hinfer' : (InferWidth_fun hd el tmap) => [newtm|]; rewrite Hinfer' in Hinfer; try discriminate.
  specialize inferwidths_a with (v := hd) (a := a) (expr_seq := el) (tmap := tmap) (tmap' := newtm); intro.
  apply H0 in Hinfer'; clear H0.
  rewrite H Hcheckt in Hinfer'.
  case Hnewtm : (CEP.find (a.1, 0%num) newtm) => [newt|]; rewrite Hnewtm in Hinfer'.
  apply IH with (a:= a) (checkt := newt) (checkt' := checkt') in Hinfer; try done.
  rewrite Hinfer' -Hinfer; done.
  admit. (* Hnewtm 不是None *)
Admitted.

Lemma max_ftlist_correct : forall eftl initt tmax, max_ftlist eftl initt = Some tmax -> (not_implicit initt = false -> not_implicit tmax = false) /\ fgtyp_equiv initt tmax.
Proof.
  elim.
  intros.
  split.
  intros.
  simpl in H. 
  inversion H.
  rewrite -H2; done.
  simpl in H. 
  inversion H.
  admit.

  intros hd tl H init nt Hl.
  split.
  intro Himpli.
  simpl in Hl. 
  case Htl : (max_ftlist tl init) => [nt'|]; rewrite Htl in Hl; try discriminate.
  apply H in Htl; try done.
  rewrite /max_fgtyp in Hl.
  case Hhd : hd; rewrite Hhd in Hl; try discriminate.
  case Hnt' : nt'; rewrite Hnt' in Hl Htl; try discriminate; inversion Hl; simpl; try done.
  case Hnt' : nt'; rewrite Hnt' in Hl Htl; try discriminate; inversion Hl; simpl; try done.
  case Hnt' : nt'; rewrite Hnt' in Hl Htl; try discriminate; inversion Hl; simpl; try done.
  case Hnt' : nt'; rewrite Hnt' in Hl Htl; try discriminate; inversion Hl; simpl; try done.

  simpl in Hl. 
  case Htl : (max_ftlist tl init) => [nt'|]; rewrite Htl in Hl; try discriminate.
  apply H in Htl; try done.
  move : Htl => [_ Htl].
  specialize max_compatible' with (gte := hd) (gt := nt') (tmax := nt); intro.
  apply H0 in Hl; clear H0.
  move /andP : Hl => [H1 _].
  move /andP : H1 => [_ H1].
  assert (fgtyp_equiv nt' nt).
  admit.
  move : Htl H0.
  apply fgtyp_equiv_dlvr.
Admitted.

Lemma type_of_hfexpr_eq : forall (expr : HiFP.hfexpr) (pv : ProdVarOrder.t) (nt0 : ftype) (tmap : CEP.t ftype), type_of_hfexpr expr (CEP.add (pv.1, 0%num) nt0 tmap) = type_of_hfexpr expr tmap.
Proof.
  elim. 
  - intros.
    simpl; done.
  - (*intros.
    case Hu : u.
    simpl.*)
    admit.
    admit.
    admit.
    admit.
    admit.
  - (* ref *)
    intros ref pv nt0 tmap. 
    simpl.
    move : ref.
    elim. 
    intro ref.
    rewrite /base_ref.
Admitted.

Lemma InferWidth_fun_correct : forall pv el tmap newtm, InferWidth_fun pv el tmap = Some newtm -> forall expr, expr \in el -> 
      match CEP.find (fst pv, N0) newtm with
      | Some checkt => match ft_find_sub checkt pv.2, type_of_hfexpr expr newtm with
                              | Some nt, Some te => ftype_equiv (Gtyp nt) te -> connect_type_compatible (Gtyp nt) te
                              | _,_ => true
                              end
      | _ => true
      end.
Proof.
  intros pv el tmap newtm Hinfer expr Hin.
  rewrite /InferWidth_fun in Hinfer.
  case Hel : (fil_ftlist [seq type_of_hfexpr e tmap | e <- el]) => [eftl|]; rewrite Hel in Hinfer; try discriminate.
  case Hinit : (CEP.find (pv.1, 0%num) tmap) => [init|]; rewrite Hinit in Hinfer; try discriminate.
  case Hinitt : (ft_find_sub init pv.2) => [initt|]; rewrite Hinitt in Hinfer; try discriminate.
  case Hcheckt : (CEP.find (pv.1, 0%num) newtm) => [checkt|]; try done.
  case Hnt : (ft_find_sub checkt pv.2) => [nt|]; try done.
  case Hte : (type_of_hfexpr expr newtm) => [te|]; try done.
  intro Heq.
  case Himpli : (not_implicit initt); rewrite Himpli in Hinfer.
  (* case 1 *)
  rewrite /connect_type_compatible.
  apply rwP with (P := ftype_equiv (Gtyp nt) te /\ check_connect_fgtyp_compatible (Gtyp nt) te (tmap_type_size (Gtyp nt))).
  apply andP.
  split; try done.
  simpl.
  case He : te => [gt||]; rewrite He in Heq; simpl in Heq; try discriminate.
  simpl.
  rewrite /connect_fgtyp_compatible.
  inversion Hinfer; clear Hinfer.
  rewrite H0 in Hinit; rewrite Hinit in Hcheckt; inversion Hcheckt; clear Hcheckt H0 Hinit.
  rewrite H1 in Hinitt; rewrite Hinitt in Hnt; inversion Hnt; clear Hnt Hinitt H1.
  rewrite H0 in Himpli; rewrite Himpli; done.
  (* case2 *)
  case Hmax : (max_ftlist eftl initt) => [tmax|]; rewrite Hmax in Hinfer; try discriminate.
  case Hset : (ft_set_sub init tmax pv.2) => [nt0|]; rewrite Hset in Hinfer; try discriminate.
  inversion Hinfer; clear Hinfer.
  rewrite -H0 in Hte Hcheckt; clear H0.
  rewrite HiFP.PCELemmas.OP.P.F.add_eq_o in Hcheckt.
  inversion Hcheckt; clear Hcheckt.
  rewrite -H0 in Hnt; clear H0.
  apply set_find_sub in Hset; try done.
  rewrite Hset in Hnt; clear Hset.
  inversion Hnt; clear Hnt.
  rewrite -H0.
  rewrite /connect_type_compatible.
  simpl.
  case Hgte : te => [gte||]; rewrite Hgte in Heq; simpl in Heq; try discriminate.
  apply rwP with (P := fgtyp_equiv tmax gte /\
    match ft_find_sub (Gtyp gte) 0 with
    | Some gt_src => connect_fgtyp_compatible tmax gt_src && true
    | None => false
    end).
  apply andP. 
  split.
  rewrite -H0 in Heq; done.
  simpl.
  apply rwP with (P := connect_fgtyp_compatible tmax gte /\ true).
  apply andP. 
  split; try done.
  rewrite /connect_fgtyp_compatible.
  specialize max_ftlist_correct with (eftl := eftl) (initt := initt) (tmax := tmax); intro.
  generalize Hmax.
  apply H in Hmax; clear H.
  move => Hmax'.
  move : Hmax => [Hmax _].
  apply Hmax in Himpli.
  rewrite Himpli.
  assert (type_of_hfexpr expr (CEP.add (pv.1, 0%num) nt0 tmap) = type_of_hfexpr expr tmap).
  admit.
  rewrite H in Hte; clear H.
  rewrite Hgte in Hte.
  apply max_compatible with (el := el) (tmap := tmap) (eftl := eftl) (initt := initt) (expr := expr); try done.
  apply ft_set_sub_eq with (nt' := tmax) (n := pv.2) (init := initt); try done.
  specialize max_ftlist_correct with (eftl := eftl) (initt := initt) (tmax := tmax); intro.
  apply H in Hmax; clear H.
  move : Hmax => [_ Hmax]; done.
Admitted.

Lemma ftype_eq_find_some : forall t1 t2 n te, ftype_equiv t1 t2 -> ft_find_sub t1 n = Some te -> 
  exists b, ft_check_flip t1 n false = Some b /\ exists te', ft_find_sub t2 n = Some te'.
Proof.
Admitted.

Lemma ftype_eq_check_flip : forall t1 t2 n, ftype_equiv t1 t2 -> ft_check_flip t1 n = ft_check_flip t2 n. 
Proof.
Admitted.


Lemma check_connect_fgtyp_compatible4n ft te : forall n, (forall n0, n0 < n -> ft_check_flip ft (N.of_nat n0) false = Some false) -> (forall n0 gt gte, n0 < n -> ft_check_flip ft (N.of_nat n0) false = Some false -> ft_find_sub ft (N.of_nat n0) = Some gt -> ft_find_sub te (N.of_nat n0) = Some gte ->
  connect_fgtyp_compatible gt gte) -> ftype_equiv ft te -> check_connect_fgtyp_compatible ft te n.
Proof.
  induction n. 
  intros.
  simpl; done.
  intros Hnflip H Heq. 
  simpl.
  generalize Hnflip; specialize Hnflip with (n0 := n).
  rewrite Hnflip; try done.
  intro Hnflip'.
  case Htgt : (ft_find_sub ft (N.of_nat n)) => [gt_tgt|].
  case Hsrc : (ft_find_sub te (N.of_nat n)) => [gt_src|].
  apply rwP with (P := connect_fgtyp_compatible gt_tgt gt_src /\ check_connect_fgtyp_compatible ft te n).
  apply andP. 
  split.
  apply H with (n0 := n); try done.
  apply Hnflip; try done.
  apply IHn; try done.
  intros.
  apply Hnflip'.
  rewrite -(addn1 n).
  move : H0.
  apply ltn_addr.
  intros.
  apply H with (n0 := n0); try done.
  rewrite -(addn1 n).
  move : H0.
  apply ltn_addr.
  apply ftype_eq_find_some with (t2 := te) in Htgt; try done.
  destruct Htgt as [b [Hb [te' Htgt]]].
  rewrite Htgt in Hsrc; discriminate.
  case Hsrc : (ft_find_sub te (N.of_nat n)) => [te'|]; try done.
  apply ftype_eq_find_some with (t2 := ft) in Hsrc; try done.
  destruct Hsrc as [b [Hb [ft' Hsrc]]].
  rewrite Htgt in Hsrc; discriminate.
Admitted.

Lemma check_connect_non_passive_fgtyp4n ft te : forall n, (forall n0 gt gte, n0 < n -> ft_find_sub ft (N.of_nat n0) = Some gt -> ft_find_sub te (N.of_nat n0) = Some gte ->
        match ft_check_flip ft (N.of_nat n0) false with
        | Some false => connect_fgtyp_compatible gt gte
        | Some true => connect_fgtyp_compatible gte gt
        | None => true
        end) -> ftype_equiv ft te ->
        check_connect_non_passive_fgtyp ft te n.
Proof.
  induction n. 
  intros.
  simpl; done.
  intros H Heq. 
  simpl.
  case Hflip : (ft_check_flip ft (N.of_nat n) false) => [b|].
  case Hb : b; rewrite Hb in Hflip.
  (* case1 : flip *)
  case Htgt : (ft_find_sub ft (N.of_nat n)) => [gt_tgt|].
  case Hsrc : (ft_find_sub te (N.of_nat n)) => [gt_src|].
  apply rwP with (P := connect_fgtyp_compatible gt_src gt_tgt /\ check_connect_non_passive_fgtyp ft te n).
  apply andP. 
  split.
  specialize H with (n0 := n) (gt := gt_tgt) (gte := gt_src).
  rewrite Hflip in H. 
  apply H; try done.
  apply IHn; try done.
  intros.
  case Hflip' : (ft_check_flip ft (N.of_nat n0) false) => [b0|]; try done.
  apply H with (n0 := n0) (gt := gt) (gte := gte) in H1; try done.
  rewrite Hflip' in H1; done.
  rewrite -(addn1 n).
  move : H0.
  apply ltn_addr.
  apply ftype_eq_find_some with (t2 := te) in Htgt; try done.
  destruct Htgt as [b' [Hb' [te' Htgt]]].
  rewrite Htgt in Hsrc; discriminate.
  case Hsrc : (ft_find_sub te (N.of_nat n)) => [te'|]; try done.
  apply ftype_eq_find_some with (t2 := ft) in Hsrc; try done.
  destruct Hsrc as [b' [Hb' [ft' Hsrc]]].
  rewrite Htgt in Hsrc; discriminate.
  admit.
  (* case2 : nflip *)
  case Htgt : (ft_find_sub ft (N.of_nat n)) => [gt_tgt|].
  case Hsrc : (ft_find_sub te (N.of_nat n)) => [gt_src|].
  apply rwP with (P := connect_fgtyp_compatible gt_tgt gt_src /\ check_connect_non_passive_fgtyp ft te n).
  apply andP. 
  split.
  specialize H with (n0 := n) (gt := gt_tgt) (gte := gt_src).
  rewrite Hflip in H. 
  apply H; try done.
  apply IHn; try done.
  intros.
  case Hflip' : (ft_check_flip ft (N.of_nat n0) false) => [b0|]; try done.
  apply H with (n0 := n0) (gt := gt) (gte := gte) in H1; try done.
  rewrite Hflip' in H1; done.
  rewrite -(addn1 n).
  move : H0.
  apply ltn_addr.
  apply ftype_eq_find_some with (t2 := te) in Htgt; try done.
  destruct Htgt as [b' [Hb' [te' Htgt]]].
  rewrite Htgt in Hsrc; discriminate.
  case Hsrc : (ft_find_sub te (N.of_nat n)) => [te'|]; try done.
  apply ftype_eq_find_some with (t2 := ft) in Hsrc; try done.
  destruct Hsrc as [b' [Hb' [ft' Hsrc]]].
  rewrite Htgt in Hsrc; discriminate.
  admit.
  case Hsrc : (ft_find_sub te (N.of_nat n)) => [te'|]; try done.
  apply ftype_eq_find_some with (t2 := ft) in Hsrc; try done.
  destruct Hsrc as [b' [Hb' [ft' Hsrc]]].
  apply ftype_eq_check_flip with (n := N.of_nat n) in Heq.
  rewrite Heq in Hflip.
  rewrite Hflip in Hb'; discriminate.
  admit.
  case Htgt : (ft_find_sub ft (N.of_nat n)) => [ft'|]; try done.
  apply ftype_eq_find_some with (t2 := te) in Htgt; try done.
  destruct Htgt as [b' [Hb' [te' Htgt]]].
  rewrite Htgt in Hsrc; discriminate.
Admitted.

Lemma infer_cons_order : forall order1 order2 var2exprs tmap tmap' newtm, InferWidths_fun (order1 ++ order2) var2exprs tmap = Some newtm -> InferWidths_fun order1 var2exprs tmap = Some tmap' ->
  InferWidths_fun order2 var2exprs tmap' = Some newtm.
Proof.
  elim. 
  intros.
  simpl in H0.
  inversion H0; clear H0.
  rewrite H2 in H.
  simpl in H; done.
  intros hd tl IH order2 var2exprs tmap tmap' newtm H H0.
  simpl in H; simpl in H0.
  case Hhd : (module_graph_vertex_set_p.find hd var2exprs) => [el|]; rewrite Hhd in H H0; try discriminate.
  case Hinfer : (InferWidth_fun hd el tmap) => [tm|]; rewrite Hinfer in H H0; try discriminate.
  move : H H0.
  apply IH.
Qed.

Lemma find_mux_types_n : forall n t1 t2 t_expr tt1 tt2, mux_types t1 t2 = Some t_expr -> ft_find_sub t1 n = Some tt1 -> 
  ft_find_sub t2 n = Some tt2 -> mux_gtyp tt1 tt2 = ft_find_sub t_expr n.
Proof.
  
Admitted.

Lemma combine_mux_expr_n : forall c el1 el2 rhs_expr_ls n e1 e2, combine_mux_expr c el1 el2 = Some rhs_expr_ls -> 
  nth_error el1 n = Some e1 -> nth_error el2 n = Some e2 -> nth_error rhs_expr_ls n = Some (Emux c e1 e2).
Proof.

Admitted.

Lemma split_expr_correct : forall s1 tmap t1 el1 e1 n gt, type_of_hfexpr s1 tmap = Some t1 -> split_expr_connect s1 t1 = Some el1 -> nth_error el1 n = Some e1 -> ft_find_sub t1 (N.of_nat n) = Some gt -> type_of_hfexpr e1 tmap = Some (Gtyp gt).
Proof.
Admitted.

Lemma ftype_equiv_split_eq : forall s t1 t2, ftype_equiv t1 t2 -> split_expr_connect s t1 = split_expr_connect s t2.
Proof.
Admitted.

Lemma mux_expr_type_equiv : forall c s1 s2 tmap te te1 te2, type_of_hfexpr (Emux c s1 s2) tmap = Some te -> type_of_hfexpr s1 tmap = Some te1 -> 
  type_of_hfexpr s2 tmap = Some te2 -> ftype_equiv te te1 /\ ftype_equiv te te2.
Proof.
Admitted.

Lemma split_expr_type_correct : (forall expr rhs_expr_ls t_expr newtm, type_of_hfexpr expr newtm = Some t_expr -> split_expr_connect expr t_expr = Some rhs_expr_ls ->  (* 这里可以加bool list用来判断flip *)
  forall n, match ft_find_sub t_expr (N.of_nat n), List.nth_error rhs_expr_ls n with
                        | Some gt, Some texpr => type_of_hfexpr texpr newtm = Some (Gtyp gt)
                        | _, _ => true
                        end).
Proof.
  elim.
  intros.
  simpl in H0.
  inversion H0; clear H0.
  move : n.
  induction n as [|n]; simpl.
  simpl in H. 
  inversion H.
  simpl; done.
  simpl in H.
  inversion H.
  simpl; done.

  admit.
  admit.
  admit.

  (* mux case *)
  intros c Hc s1 Hs1 s2 Hs2.
  intros rhs_expr_ls t_expr tmap Hte Hsplit.
  simpl in Hsplit.
  case Hsplit1 : (split_expr_connect s1 t_expr) => [el1|]; rewrite Hsplit1 in Hsplit; try discriminate.
  case Hsplit2 : (split_expr_connect s2 t_expr) => [el2|]; rewrite Hsplit2 in Hsplit; try discriminate.

  generalize Hte.
  simpl in Hte.
  move => Hte'. 
  case Hce : (type_of_hfexpr c tmap) => [f|]; rewrite Hce in Hte; try discriminate.
  case Hcf : f => [cgt||]; rewrite Hcf in Hte; try discriminate.
  case Hcgt : cgt => [w|w|w||||]; rewrite Hcgt in Hcf Hte; try discriminate.
  case Hw : w => [|n0]; rewrite Hw in Hte; try discriminate.
  case Hw' : n0; rewrite Hw' in Hte Hw; try discriminate.
  rewrite Hw in Hcf; clear Hw Hw' Hcgt w n0 cgt.
  case Hs1e : (type_of_hfexpr s1 tmap) => [t1|]; rewrite Hs1e in Hte; try discriminate.
  case Hs2e : (type_of_hfexpr s2 tmap) => [t2|]; rewrite Hs2e in Hte; try discriminate.

  intro n. 
  case Hten : (ft_find_sub t_expr (N.of_nat n)) => [gte|]; try done.
  case Hs1n : (ft_find_sub t1 (N.of_nat n)) => [tt1|].
  case Hs2n : (ft_find_sub t2 (N.of_nat n)) => [tt2|].
  apply find_mux_types_n with (n := N.of_nat n) (tt1 := tt1) (tt2 := tt2) in Hte; try done.
  rewrite Hten in Hte; clear Hten.

  assert (exists e1, nth_error el1 n = Some e1).
  admit.
  destruct H as [e1 He1].
  assert (exists e2, nth_error el2 n = Some e2).
  admit.
  destruct H as [e2 He2].
  apply combine_mux_expr_n with (n := n) (el1 := el1) (el2 := el2) (e1 := e1) (e2 := e2) in Hsplit; try done.
  rewrite Hsplit.
  simpl.
  rewrite Hce Hcf.
  case Hte1 : (type_of_hfexpr e1 tmap) => [te1|].
  case Hte2 : (type_of_hfexpr e2 tmap) => [te2|].
  generalize Hs1e.
  apply split_expr_correct with (el1 := el1) (e1 := e1) (n := n) (gt := tt1) in Hs1e; try done.
  rewrite Hs1e in Hte1; clear Hs1e.
  move => Hs1e.
  inversion Hte1; clear Hte1.
  apply split_expr_correct with (el1 := el2) (e1 := e2) (n := n) (gt := tt2) in Hs2e; try done.
  rewrite Hs2e in Hte2; clear Hs2e.
  inversion Hte2; clear Hte2.
  simpl; rewrite Hte; done.
  specialize ftype_equiv_split_eq with (s := s2) (t1 := t_expr) (t2 := t2); intro.
  rewrite H in Hsplit2.
  done.
  apply mux_expr_type_equiv with (c := c) (s1 := s1) (s2 := s2) (te := t_expr) (te1 := t1) (te2 := t2) in Hte'; try done.
  move : Hte' => [_ Hte']; done.
  specialize ftype_equiv_split_eq with (s := s1) (t1 := t_expr) (t2 := t1); intro.
  rewrite H in Hsplit1.
  done.
  apply mux_expr_type_equiv with (c := c) (s1 := s1) (s2 := s2) (te := t_expr) (te1 := t1) (te2 := t2) in Hte'; try done.
  move : Hte' => [Hte' _]; done.
  admit. (* not None *)
  admit. (* not None *)
  admit. (* not None *)
  admit. (* not None *)

  admit. (* 与Fuint w的case完全一样 *)

  admit. (* validif *)
  admit. (* ref *)
Admitted.

(*Lemma add_non_passive2exprmap : forall lhsl rhsl v_tgt v_src var2exprs0 var2exprs refl bl refr br n, add_expr_connect_non_passive v_tgt v_src lhsl rhsl var2exprs0 = Some var2exprs ->
  nth_error lhsl n = Some (refl, bl) -> nth_error rhsl n = Some (refr, br) -> match bl, br with
  | true, true => match module_graph_vertex_set_p.find (v_src.1, N.add v_src.2 (N.of_nat n)) var2exprs with
                | Some el => (Eref refl) \in el
                | None => false
                end
  | false, false => match module_graph_vertex_set_p.find (v_tgt.1, N.add v_tgt.2 (N.of_nat n)) var2exprs with
                | Some el => (Eref refr) \in el
                | None => false
                end
  | _,_ => true
  end.
Proof.
  elim.
  admit.
  intros hdl tll IH.
  elim.
  admit.
  intros hdr tlr H; clear H.
  specialize IH with (rhsl := tlr).
  intros v_tgt v_src var2exprs0 var2exprs refl bl refr br.
  simpl in Hadd.*)

(* TBD!!重要 *)
Lemma split_non_passive_correct : forall (ref_tgt ref_src : HiFP.href) (t_tgt t_src : ftype) (v_tgt v_src : ProdVarOrder.t) (tmap0 tmap : CEP.t ftype) (var2exprs0 var2exprs : var2exprsmap),
  stmt_tmap (tmap0, var2exprs0) (Sfcnct ref_tgt (Eref ref_src)) = Some (tmap, var2exprs) ->
  base_ref ref_tgt tmap0 = Some (v_tgt, t_tgt) -> base_ref ref_src tmap0 = Some (v_src, t_src) ->
  match split_expr_non_passive ref_tgt t_tgt false, split_expr_non_passive ref_src t_src false with
  | Some lhsl, Some rhsl => (forall n, n < length lhsl -> match List.nth_error lhsl n, List.nth_error rhsl n with
                            | Some (_, false), Some (ref2, false) => match module_graph_vertex_set_p.find (v_tgt.1, N.add v_tgt.2 (N.of_nat n)) var2exprs with
                                                          | Some el => (Eref ref2) \in el
                                                          | None => false
                                                          end
                            | Some (ref1, true), Some (_, true) => match module_graph_vertex_set_p.find (v_src.1, N.add v_src.2 (N.of_nat n)) var2exprs with
                                                          | Some el => (Eref ref1) \in el
                                                          | None => false
                                                          end
                            | _,_ => false
                            end)
  | _, _ => false
  end.
Proof.
  intros.
  simpl in H.
  rewrite H0 H1 in H.
  case Hsplitl : (split_expr_non_passive ref_tgt t_tgt false) => [lhsl|]; rewrite Hsplitl in H; try discriminate.
  case Hsplitr : (split_expr_non_passive ref_src t_src false) => [rhsl|]; rewrite Hsplitr in H; try discriminate.
  case Hadd : (add_expr_connect_non_passive v_tgt v_src lhsl rhsl var2exprs0) => [newv2e|]; rewrite Hadd in H; try discriminate.
  inversion H; clear H.
  rewrite H4 in Hadd; clear H4.
  intros n Hn.
  case Hnthl : (nth_error lhsl n) => [[refl bl]|].
  case Hb : bl.
  case Hnthr : (nth_error rhsl n) => [[refr br]|].
  assert (br = bl).
  admit.
  rewrite H Hb.

  (*apply nth_error_Some in Hn.*)
Admitted.

Lemma base_ref_cepfind : forall ref n pv ft tmap checkt, base_ref ref tmap = Some (pv, ft) -> CEP.find (pv.1, 0%num) tmap = Some checkt -> 
  ft_find_sub checkt (pv.2 + N.of_nat n) = ft_find_sub ft (N.of_nat n).
Proof.
Admitted.

Lemma InferWidths_fun_correct : forall (hfs : HiFP.hfstmt) (inferorder : seq ProdVarOrder.t) (var2exprs : var2exprsmap) (tmap newtm : CEP.t ftype),
  InferWidths_fun inferorder var2exprs tmap = Some newtm -> match hfs with
    | Sfcnct ref_tgt (Eref ref_src) => match base_ref ref_tgt newtm, base_ref ref_src newtm with
                                      | Some (pv_tgt, t_tgt), Some (pv_src, t_src) => connect_non_passive_type t_tgt t_src
                                      | _, _ => True
                                      end 
    | Sfcnct ref_tgt expr_src => match base_ref ref_tgt newtm, type_of_hfexpr expr_src newtm with
                                      | Some tgt, Some t_expr => connect_type_compatible tgt.2 t_expr
                                      | _, _ => True
                                      end
    | _ => True
    end.
Proof.
  intros hfs inferorder var2exprs tmap newtm Hinfer.
  case Hs : hfs => [||||||ref expr||]; try done.
  case He : expr => [ct c| c e1 | u e1 | op e1 e2 | c e1 e2 | c e1 | ref0 ]. 
  (* const *)
  rewrite -He.
  case Hbase : (base_ref ref newtm) => [tgt|]; try done.
  case Hte : (type_of_hfexpr expr newtm) => [t_expr|] ; try done.
  rewrite /connect_type_compatible.
  apply rwP with (P := ftype_equiv tgt.2 t_expr /\
    check_connect_fgtyp_compatible tgt.2 t_expr (tmap_type_size tgt.2)).
  apply andP.
  split. 
  admit. (* 对connection语句的要求 *)

  specialize check_connect_fgtyp_compatible4n as H.
  apply H; clear H.
  admit. (* tgt为false不允许flip是正确连接的要求 *)
  intros n gt gte Hn Hflip Hlhs Hrhs.
  assert (exists order1 order2, (inferorder = order1 ++ ((tgt.1.1, N.add tgt.1.2 (N.of_nat n)) :: order2)) 
    /\ ((tgt.1.1, N.add tgt.1.2 (N.of_nat n)) \notin order1) 
    /\ ((tgt.1.1, N.add tgt.1.2 (N.of_nat n)) \notin order2)).
  admit. (* inferorder 的正确性，是展开时的标号 *)
  move : H => [order1 [order2 [H [Horder1 Horder2]]]].
  rewrite H in Hinfer.
  case Hinfer1 : (InferWidths_fun order1 var2exprs tmap) => [tmap'|].

  assert (Hinfer2 : InferWidths_fun ((tgt.1.1, N.add tgt.1.2 (N.of_nat n)) :: order2) var2exprs tmap' = Some newtm).
  move : Hinfer Hinfer1.
  apply infer_cons_order.
  clear Hinfer.
  simpl in Hinfer2.
  case Hel : (module_graph_vertex_set_p.find (tgt.1.1, N.add tgt.1.2 (N.of_nat n)) var2exprs) => [el|]; rewrite Hel in Hinfer2; try done.
  case Hinfer : (InferWidth_fun (tgt.1.1, N.add tgt.1.2 (N.of_nat n)) el tmap') => [newtm'|]; rewrite Hinfer in Hinfer2; try discriminate.

  specialize split_expr_type_correct; intro.
  case Hsplit : (split_expr_connect expr t_expr) => [rhs_expr_ls|].
  apply H0 with (expr := expr) (rhs_expr_ls := rhs_expr_ls) (t_expr := t_expr) (newtm := newtm) (n := n) in Hsplit; try done; clear H0.
  case Htexpr : (nth_error rhs_expr_ls n) => [texpr|]; rewrite Htexpr in Hsplit.
  rewrite Hrhs in Hsplit.

  apply InferWidth_fun_correct with (pv := (tgt.1.1, N.add tgt.1.2 (N.of_nat n))) (el := el) (tmap := tmap') (newtm := newtm') (expr := texpr) in Hinfer.
  simpl in Hinfer.
  case Htgt0 : (CEP.find (tgt.1.1, 0%num) newtm') => [checkt'|]; rewrite Htgt0 in Hinfer.
  case Hsub0 : (ft_find_sub checkt' (tgt.1.2 + N.of_nat n)) => [nt|]; rewrite Hsub0 in Hinfer.
  case Htgt : (CEP.find (tgt.1.1, 0%num) newtm) => [checkt|].
  apply inferwidths_ls with (var2exprs := var2exprs) (tmap := newtm') (tmap' := newtm) (checkt := checkt') (checkt' := checkt) in Horder2; try done.
  rewrite Hsub0 in Horder2; clear Hsub0.
  simpl in Horder2.

  specialize base_ref_cepfind with (ref := ref) (n := n) (pv := tgt.1) (ft := tgt.2) (tmap := newtm); intro.
  apply H0 in Htgt; clear H0; try done.
  rewrite Htgt in Horder2; clear Htgt.
  rewrite Hlhs in Horder2; clear Hlhs.
  inversion Horder2; clear Horder2.

  case Hte' : (type_of_hfexpr texpr newtm') => [te|]; rewrite Hte' in Hinfer.
  assert (type_of_hfexpr texpr newtm = Some te).
  admit. (* 由于拓扑排序，texpr不受order2中的位宽更新影响。由Hte' Hinfer2 *)
  clear Hte'.
  rewrite H0 in Hsplit.
  inversion Hsplit; clear Hsplit.
  rewrite H3 H1 in Hinfer.
  rewrite /connect_type_compatible in Hinfer.
  assert (fgtyp_equiv gt gte).
  admit. (* 从某个地方来的连接合法的前提 *)
  apply Hinfer in H2; clear Hinfer.
  move /andP : H2 => [_ Hinfer].
  simpl in Hinfer. 
  move /andP : Hinfer => [Hinfer _]; done.

  admit. (* type_of_hfexpr 不为None，由Htgt0 *)
  rewrite -surjective_pairing; done.
  admit. (* 由Htgt0不为None *)
  admit. (* 由 n < tmap_type_size tgt.2 知Hsub0不为None *)
  admit. (* 被连接的应该已被声明，find不为None *)
  admit. (* var2exprs应当满足的性质，由add_expr_connect *)
  admit. (* n 不超过 rhs_expr_ls 的长度，不为None *)
  admit. (* expr应该与t_expr匹配，不会出错 *)
  admit. (* 若infer order1有错误，则infer没有结果 *)
  admit. (* 正确连接的前提 *)

  (* 所有passive的expr都一样 *)
  admit.
  admit.
  admit.
  admit.
  admit.

  (* ref non_passive *)
  case Htgt : (base_ref ref newtm) => [[v_tgt t_tgt]|]; try done.
  case Hsrc : (base_ref ref0 newtm) => [[v_src t_src]|]; try done.
  rewrite /connect_non_passive_type.
  apply rwP with (P := ftype_equiv t_tgt t_src /\ check_connect_non_passive_fgtyp t_tgt t_src (tmap_type_size t_tgt)).
  apply andP.
  split. 
  admit. (* 对connection语句的要求 *)

  apply check_connect_non_passive_fgtyp4n.
  intros n gt gte Hn Hlhs Hrhs.
  (* TBD!! stop here *)
  assert (forall ref_tgt ref_src t_tgt t_src v_tgt v_src tmap, base_ref ref_tgt tmap = Some (v_tgt, t_tgt) -> base_ref ref_src tmap = Some (v_src, t_src) ->
              match split_expr_non_passive ref_tgt t_tgt false, split_expr_non_passive ref_src t_src false with
              | Some lhsl, Some rhsl => (forall n, n < length lhsl -> match List.nth_error lhsl n, List.nth_error rhsl n with
                                        | Some (_, false), Some (ref2, false) => match module_graph_vertex_set_p.find (v_tgt.1, N.add v_tgt.2 (N.of_nat n)) var2exprs with
                                                          | Some el => (Eref ref2) \in el
                                                          | None => false
                                                          end
                                        | Some (ref1, true), Some (_, true) => match module_graph_vertex_set_p.find (v_src.1, N.add v_src.2 (N.of_nat n)) var2exprs with
                                                          | Some el => (Eref ref1) \in el
                                                          | None => false
                                                          end
                                        | _,_ => false
                                        end)
              | _, _ => false
              end). 
  admit. (* split和存var2exprs的性质 *)
  (*specialize split_non_passive_correct as H.*)
  generalize Htgt.
  apply H with (ref_tgt := ref) (t_tgt := t_tgt) (v_tgt := v_tgt) (ref_src := ref0) (t_src := t_src) (v_src := v_src) in Htgt; try done; clear H.
  case Hsplit_lhs : (split_expr_non_passive ref t_tgt false) => [lhsl|]; rewrite Hsplit_lhs in Htgt.
  case Hsplit_rhs : (split_expr_non_passive ref0 t_src false) => [rhsl|]; rewrite Hsplit_rhs in Htgt.
  assert (length lhsl = tmap_type_size t_tgt).
  admit.
  rewrite H in Htgt; clear H.
  apply Htgt in Hn; clear Htgt.
  move => Htgt.
  
  case Hlhsl : (nth_error lhsl n) => [[ref1 b1]|]; rewrite Hlhsl in Hn.
  case Hrhsl : (nth_error rhsl n) => [[ref2 b2]|]; rewrite Hrhsl in Hn.
  case Hcheckfl : (ft_check_flip t_tgt (N.of_nat n) false) => [b1'|].
  assert (b1 = b1').
  admit. (* 两种不同的算flip方法应当结果相同 *)
  assert (b1 = b2). (* tgt和src类型相同 *)
  admit.

  case Hb : b1; rewrite Hb in H0 Hn H; rewrite -H; rewrite -H0 in Hn.
  (* case1 : flip field *)
  assert ((v_src.1, N.add v_src.2 (N.of_nat n)) \in inferorder).
  admit. (* inferorder 的正确性，是展开时的标号 *)
  assert (exists order1 order2, inferorder = order1 ++ ((v_src.1, N.add v_src.2 (N.of_nat n)) :: order2) /\ ~ (v_src.1, N.add v_src.2 (N.of_nat n)) \in order1 /\ ~ (v_src.1, N.add v_src.2 (N.of_nat n)) \in order2).
  admit. (* 由H1推出 *)
  clear H1.
  move : H2 => [order1 [order2 [H2 [Horder1 Horder2]]]].
  rewrite H2 in Hinfer; rewrite /InferWidths_fun in Hinfer.
  case Hinfer1 : (InferWidths_fun order1 var2exprs tmap) => [tmap'|].
  assert (Hinfer2 : InferWidths_fun ((v_src.1, N.add v_src.2 (N.of_nat n)) :: order2) var2exprs tmap' = Some newtm).
  admit. (* 由 Hinfer Hinfer1 *)
  clear Hinfer.
  simpl in Hinfer2.
  case Hel : (module_graph_vertex_set_p.find (v_src.1, N.add v_src.2 (N.of_nat n)) var2exprs) => [el|]; rewrite Hel in Hinfer2; try done.
  case Hinfer : (InferWidth_fun (v_src.1, N.add v_src.2 (N.of_nat n)) el tmap') => [newtm'|]; rewrite Hinfer in Hinfer2; try discriminate.

  apply InferWidth_fun_correct with (pv := (v_src.1, (v_src.2 + N.of_nat n)%num)) (el := el) (tmap := tmap') (newtm := newtm') (expr := (Eref ref1)) in Hinfer.
  simpl in Hinfer.
  case Hsrc0 : (CEP.find (v_src.1, 0%num) newtm') => [checkt'|]; rewrite Hsrc0 in Hinfer.
  case Hsub0 : (ft_find_sub checkt' (v_src.2 + N.of_nat n)) => [nt|]; rewrite Hsub0 in Hinfer.
  case Htgt0 : (base_ref ref1 newtm') => [[v_tgt0 t_tgt0]|]; rewrite Htgt0 in Hinfer.

  (* 下面证t_tgt0 = gt和gte = Gtyp nt *)
  assert ((Gtyp gt) = t_tgt0).
  move : Htgt Hsplit_lhs Hlhs Hlhsl Htgt0.
  admit. (* split之后取算n个expr的类型 = 整个expr类型的第n个field *) (* base_ref ref1 newtm' = base_ref ref1 newtm, 由于v_tgt0不在order2中 *)
  assert (gte = nt).
  move : Hsrc Hsrc0 Hsub0 Hrhs.
  admit.
  rewrite -H1 -H3 in Hinfer; rewrite /connect_type_compatible in Hinfer.
  assert (fgtyp_equiv gte gt).
  admit. (* 由t_tgt t_src 应该ftype_equiv得到 *) 
  apply Hinfer in H4; clear Hinfer.
  move /andP : H4 => [_ H4].
  simpl in H4.
  move /andP : H4 => [H4 _]; done.

  admit.
  admit.
  admit.
  admit. (* var2exprs正确性的结论 *)
  admit.

  (* case2 : Nflip *)
  assert ((v_tgt.1, N.add v_tgt.2 (N.of_nat n)) \in inferorder).
  admit. (* inferorder 的正确性，是展开时的标号 *)
  assert (exists order1 order2, inferorder = order1 ++ ((v_tgt.1, N.add v_tgt.2 (N.of_nat n)) :: order2) /\ ~ (v_tgt.1, N.add v_tgt.2 (N.of_nat n)) \in order1 /\ ~ (v_tgt.1, N.add v_tgt.2 (N.of_nat n)) \in order2).
  admit. (* 由H推出 *)
  clear H1.
  move : H2 => [order1 [order2 [H2 [Horder1 Horder2]]]].
  rewrite H2 in Hinfer; rewrite /InferWidths_fun in Hinfer.
  case Hinfer1 : (InferWidths_fun order1 var2exprs tmap) => [tmap'|].
  assert (Hinfer2 : InferWidths_fun ((v_tgt.1, N.add v_tgt.2 (N.of_nat n)) :: order2) var2exprs tmap' = Some newtm).
  admit. (* 由 Hinfer Hinfer1 *)
  clear Hinfer.
  simpl in Hinfer2.
  case Hel : (module_graph_vertex_set_p.find (v_tgt.1, N.add v_tgt.2 (N.of_nat n)) var2exprs) => [el|]; rewrite Hel in Hinfer2; try done.
  case Hinfer : (InferWidth_fun (v_tgt.1, N.add v_tgt.2 (N.of_nat n)) el tmap') => [newtm'|]; rewrite Hinfer in Hinfer2; try discriminate.

  apply InferWidth_fun_correct with (pv := (v_tgt.1, N.add v_tgt.2 (N.of_nat n))) (el := el) (tmap := tmap') (newtm := newtm') (expr := (Eref ref2)) in Hinfer.
  simpl in Hinfer.
  case Htgt0 : (CEP.find (v_tgt.1, 0%num) newtm') => [checkt'|]; rewrite Htgt0 in Hinfer.
  case Hsub0 : (ft_find_sub checkt' (v_tgt.2 + N.of_nat n)) => [nt|]; rewrite Hsub0 in Hinfer.
  case Hsrc0 : (base_ref ref2 newtm') => [[v_src0 t_src0]|]; rewrite Hsrc0 in Hinfer.

  (* 下面证t_tgt0 = gt和gte = Gtyp nt *)
  assert ((Gtyp gte) = t_src0).
  admit. 
  assert (gt = nt).
  admit.
  rewrite -H1 -H3 in Hinfer; rewrite /connect_type_compatible in Hinfer.
  assert (fgtyp_equiv gt gte).
  admit. (* 由t_tgt t_src 应该ftype_equiv得到 *) 
  apply Hinfer in H4; clear Hinfer.
  move /andP : H4 => [_ H4].
  simpl in H4.
  move /andP : H4 => [H4 _]; done.

  admit.
  admit.
  admit.
  admit. (* var2exprs正确性的结论 *)
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
Admitted.

Definition InferWidths_m F :=
  match InferWidths_stage1 F with
  | Some newtm => InferWidths_stage2 F newtm 
  | None => None
  end.

Lemma InferWidths_correct : forall (F : HiFP.hfmodule) (vm' : module_graph_vertex_set_p.env) (ct : module_graph_connection_trees_p.env),
  match InferWidths_m F with
  | Some F' => Sem F' vm' ct -> Sem F (make_vm_implicit F vm') ct
  | _ => True
  end.
Proof.
  
Admitted.

Fixpoint unfold_Swhen (s : HiFP.hfstmt) : HiFP.hfstmt_seq :=
  match s with
  | Swhen _ ss_t ss_f => Qcat (unfold_Swhens ss_t) (unfold_Swhens ss_f)
  | _ => Qcons s (Qnil HiFirrtl.ProdVarOrder.T)
  end
  with unfold_Swhens (ss : HiFP.hfstmt_seq) : HiFP.hfstmt_seq :=
  match ss with
  | Qnil => (Qnil HiFirrtl.ProdVarOrder.T)
  | Qcons s ss' => Qcat (unfold_Swhen s) (unfold_Swhens ss')
  end.

Definition Sem_port' (p : HiFP.hfport) (vm : module_graph_vertex_set_p.env) : Prop :=
(* The predicate returns true if the vertex set V conforms to the sequence of ports pp. *)
  match p with
  | Foutput v t => (forall n : nat, if n < (tmap_type_size t) then
                    match ft_find_sub t (N.of_nat n) with
                    | Some nv => module_graph_vertex_set_p.find (fst v, N.of_nat n) vm = Some (InPort nv)
                    | None => false
                    end else true)
  | _ => true
   end.

Fixpoint Sem_frag_stmt' (vm : module_graph_vertex_set_p.env) (s : HiFP.hfstmt) (tmap : CEP.t ftype) : Prop :=
   (* The predicate returns True if vm_new/ct_new can be constructed from vm_old/ct_old by applying s. 
   type checking, constraints *)
  match s with
  | Sfcnct ref_tgt (Eref ref_src) => (* allow non-passive types *)
            match type_of_hfexpr_vm vm (Eref ref_tgt) tmap, type_of_hfexpr_vm vm (Eref ref_src) tmap with
            | Some t_tgt, Some t_src => connect_non_passive_type t_tgt t_src
            | _, _ => False
            end
  | Sfcnct ref expr => 
            match type_of_hfexpr_vm vm (Eref ref) tmap, type_of_hfexpr_vm vm expr tmap with
            | Some t_tgt, Some t_src => connect_type_compatible t_tgt t_src
            | _, _ => False
            end
  | Sreg v reg => (if (reset reg) is (Rst rst_sig rst_val)
                  then match type_of_hfexpr_vm vm rst_val tmap with
                  | Some t_src => connect_type_compatible (type reg) t_src
                  | _ => False
                  end
                  else True) /\
                  (forall n : nat, n < (tmap_type_size (type reg)) ->
                          match ft_find_sub (type reg) (N.of_nat n) with
                          | Some nv => match reset reg with
                                      | NRst => module_graph_vertex_set_p.find (fst v, N.of_nat n) vm = Some (Register nv)
                                      | Rst rst_sig _ => match type_of_hfexpr_vm vm rst_sig tmap with
                                                        | Some (Gtyp Fasyncreset) => module_graph_vertex_set_p.find (fst v, N.of_nat n) vm = Some (RegisterReset nv true)
                                                        | Some (Gtyp (Fuint 1)) => module_graph_vertex_set_p.find (fst v, N.of_nat n) vm = Some (RegisterReset nv false)
                                                        | _ => False
                                                        end
                                      end
                          | None => False
                          end)
  | Swire v t => (forall n : nat, if n < (tmap_type_size t) then
                          match ft_find_sub t (N.of_nat n) with
                          | Some nv => module_graph_vertex_set_p.find (fst v, N.of_nat n) vm = Some (Wire nv)
                          | None => False
                          end else True)
  | Snode v e => match type_of_hfexpr_vm vm e tmap with
                | Some te => (forall n : nat, if n < (tmap_type_size te) then
                          match ft_find_sub te (N.of_nat n) with
                          | Some nv => module_graph_vertex_set_p.find (fst v, N.of_nat n) vm = Some (Node nv)
                          | None => False
                          end else True)
                | None => False
                end
  | Swhen _ s1 s2 => Sem_frag_stmts' vm s1 tmap /\ Sem_frag_stmts' vm s2 tmap
  | _ => True 
  end
with Sem_frag_stmts' (vm : module_graph_vertex_set_p.env) (ss : HiFP.hfstmt_seq) (tmap : CEP.t ftype) : Prop :=
  match ss with
  | Qnil => True
  | Qcons s ss' => Sem_frag_stmt' vm s tmap /\ Sem_frag_stmts' vm ss' tmap
  end.

Lemma geq_conj2mux : forall vmap tmap (gt initt : fgtyp) (el : seq HiFP.hfexpr) eftl (nt : fgtyp), (forall (texpr : HiFP.hfexpr) (tge : fgtyp), texpr \in el -> type_of_hfexpr_vm vmap texpr tmap = Some (Gtyp tge) -> ((sizeof_fgtyp gt) >= (sizeof_fgtyp tge))) ->
        fil_ftlist [seq type_of_hfexpr_vm vmap e tmap | e <- el] = Some eftl -> sizeof_fgtyp initt = 0 -> max_ftlist eftl initt = Some nt -> ((sizeof_fgtyp gt) >= (sizeof_fgtyp nt)).
Proof.
  intros vmap tmap gt initt.
  elim.
  intros.
  simpl in H0.
  inversion H0; clear H0.
  rewrite -H4 in H2.
  simpl in H2.
  inversion H2; clear H2.
  rewrite -H3 H1.
  rewrite /sizeof_fgtyp.
  case Het : gt; try done.

  intros hd tl IH eftl nt H Heftl Hinitt Hmax.
  simpl in Heftl.
  case Hhd : (type_of_hfexpr_vm vmap hd tmap) => [f|]; rewrite Hhd in Heftl; try discriminate.
  case Hf : f => [hdt||]; rewrite Hf in Hhd Heftl; clear Hf; try discriminate.
  case Heftl' : (fil_ftlist [seq type_of_hfexpr_vm vmap e tmap | e <- tl]) => [eftl'|]; rewrite Heftl' in Heftl; try discriminate.
  inversion Heftl; clear Heftl.
  rewrite -H1 in Hmax.
  simpl in Hmax.
  case Hmax' : (max_ftlist eftl' initt) => [nt'|]; rewrite Hmax' in Hmax; try discriminate.

  assert (max_fgtyp hdt nt' = Some nt -> sizeof_fgtyp nt' <= sizeof_fgtyp gt -> sizeof_fgtyp hdt <= sizeof_fgtyp gt -> sizeof_fgtyp nt <= sizeof_fgtyp gt).
  clear.
  intros.
  rewrite /max_fgtyp in H.
  case Hhd : hdt => [w|w|w|w|||]; rewrite Hhd in H H1; try discriminate.
  case Hnt' : nt' => [w'|w'|w'|w'|||]; rewrite Hnt' in H H0; try discriminate.
  inversion H; clear H.
  simpl in H1; simpl in H0; simpl.
  move : H1 H0.
  admit.
  case Hnt' : nt' => [w'|w'|w'|w'|||]; rewrite Hnt' in H H0; try discriminate.
  inversion H; clear H.
  simpl in H1; simpl in H0; simpl.
  move : H1 H0.
  admit.
  case Hnt' : nt' => [w'|w'|w'|w'|||]; rewrite Hnt' in H H0; try discriminate.
  inversion H; clear H.
  simpl in H1; simpl in H0; simpl.
  move : H1 H0.
  admit.
  case Hnt' : nt' => [w'|w'|w'|w'|||]; rewrite Hnt' in H H0; try discriminate.
  inversion H; clear H.
  simpl in H1; simpl in H0; simpl.
  move : H1 H0.
  admit.

  apply H0 in Hmax; try done; clear H0.
  apply IH with (eftl := eftl'); try done.
  intros expr tge Hin.
  apply H.
  rewrite in_cons Hin.
  rewrite orb_true_r; done.
  apply H with (texpr := hd); try done.
  rewrite in_cons.
  rewrite eq_refl.
  rewrite orb_true_l; done.
Admitted.

Lemma split_expr_type_vm_correct : forall expr rhs_expr_ls t_expr newtm vm, 
  type_of_hfexpr_vm vm expr newtm = Some t_expr -> split_expr_connect expr t_expr = Some rhs_expr_ls ->
  forall n, match ft_find_sub t_expr (N.of_nat n), List.nth_error rhs_expr_ls n with
            | Some gt, Some texpr => type_of_hfexpr_vm vm texpr newtm = Some (Gtyp gt)
            | _, _ => true
            end.
Proof.
Admitted.

Fixpoint find_sub_expr (pv : ProdVarOrder.t) (s : HiFP.hfstmt) (tmap : CEP.t ftype) : option (seq HiFP.hfexpr) :=
  match s with
  | Sreg v r => if (pv.1 == v.1) then match reset r with
                | NRst => Some nil
                | Rst _ rst_val => match split_expr_connect rst_val (type r) with
                                  | Some rstl => match List.nth_error rstl (N.to_nat pv.2) with
                                                | Some e => Some [::e]
                                                | None => None
                                                end
                                  | None => None
                                  end
                end
                else Some nil
  | Snode v e => if (pv.1 == v.1) then match type_of_hfexpr e tmap with
                | Some t => match split_expr_connect e t with
                            | Some rstl => match List.nth_error rstl (N.to_nat pv.2) with
                                                | Some e => Some [::e]
                                                | None => None
                                                end
                            | None => None
                            end
                | _ => None
                end
                else Some nil
  | Sfcnct ref_tgt (Eref ref_src) =>
                match base_ref ref_tgt tmap, base_ref ref_src tmap with
                | Some (v_tgt, t_tgt), Some (v_src, t_src) =>
                  if (pv.1 == v_tgt.1) then match split_expr_non_passive ref_src t_src false with
                                          | Some rhsl => match List.nth_error rhsl ((N.to_nat pv.2) - (N.to_nat v_tgt.2)) with
                                                        | Some (refr, false) => Some [::(Eref refr)]
                                                        | Some (_, true) => Some nil
                                                        | _ => None
                                                        end
                                          | _ => None
                                          end
                  else if (pv.1 == v_src.1) then match split_expr_non_passive ref_tgt t_tgt false with
                                          | Some lhsl => match List.nth_error lhsl ((N.to_nat pv.2) - (N.to_nat v_src.2)) with
                                                        | Some (refl, true) => Some [::(Eref refl)]
                                                        | Some (_, false) => Some nil
                                                        | _ => None
                                                        end
                                          | _ => None
                                          end
                  else Some nil
                | _, _ => None
                end
  | Sfcnct ref_tgt expr_src =>
                match base_ref ref_tgt tmap, type_of_hfexpr expr_src tmap with
                | Some (v, t_tgt), Some t_src =>
                    if (pv.1 == v.1)
                      then match split_expr_connect expr_src t_src with
                      | Some rstl => match List.nth_error rstl ((N.to_nat pv.2) - (N.to_nat v.2)) with
                                    | Some e => Some [::e]
                                    | None => None
                                    end
                      | None => None
                      end
                    else Some nil
                | _,_ => None
                end
  | Swhen _ s1 s2 => match find_sub_exprs pv s1 tmap, find_sub_exprs pv s2 tmap with
                    | Some e1, Some e2 => Some (e1 ++ e2)
                    | _,_ => None
                    end
  | _ => Some nil
  end
with find_sub_exprs (v : ProdVarOrder.t) (ss : HiFP.hfstmt_seq) (tmap : CEP.t ftype) : option (seq HiFP.hfexpr) :=
  match ss with
  | Qnil => Some nil
  | Qcons s ss' => match find_sub_expr v s tmap, find_sub_exprs v ss' tmap with
                  | Some e, Some el => Some (e ++ el)
                  | _, _ => None
                  end
  end.

Lemma ftype2fgtyp_compatible : forall ft te n, connect_type_compatible ft te -> 
  match ft_check_flip ft n false, ft_find_sub ft n, ft_find_sub te n with
  | Some false, Some gt, Some gte => connect_fgtyp_compatible gt gte
  (*| Some true, Some gt, Some gte => connect_fgtyp_compatible gte gt*)
  | _,_,_ => true
  end.
Proof.
  
Admitted.

Lemma ftype2fgtyp_non_passive_compatible : forall ft te n, connect_non_passive_type ft te -> 
  match ft_check_flip ft n false, ft_find_sub ft n, ft_find_sub te n with
  | Some false, Some gt, Some gte => connect_fgtyp_compatible gt gte
  | Some true, Some gt, Some gte => connect_fgtyp_compatible gte gt
  | _,_,_ => true
  end.
Proof.
  
Admitted.

Lemma component_vx_type_vm : forall v r tmap vmap v_tgt t_tgt t_tgt' gte, base_ref r tmap = Some (v_tgt, t_tgt) -> if (v.1 == v_tgt.1) then fillft_vm (tmap_type_size t_tgt) t_tgt v_tgt vmap = Some t_tgt' -> ft_find_sub t_tgt' (N.sub v.2 v_tgt.2) = Some gte ->
  match module_graph_vertex_set_p.find v vmap with
  | Some (OutPort gt) 
  | Some (Register gt) 
  | Some (RegisterReset gt _) 
  | Some (Wire gt) 
  | Some (Node gt) => gt = gte
  | _ => true
  end
  else true.
Proof.
Admitted.

Lemma fillft_vm_nth_eq : forall r v t t' rstl refr b n vmap tmap gt, base_ref r tmap = Some (v, t) -> split_expr_non_passive r t false = Some rstl -> 
  nth_error rstl n = Some (refr, b) -> fillft_vm (tmap_type_size t) t v vmap = Some t' -> type_of_hfexpr_vm vmap (Eref refr) tmap = Some (Gtyp gt) -> ft_find_sub t' (N.of_nat n) = Some gt.
Proof.
Admitted.

Lemma type_of_hfexpr_vm_eq : forall e tmap vmap t_src tev, type_of_hfexpr e tmap = Some t_src -> type_of_hfexpr_vm vmap e tmap = Some tev -> ftype_equiv t_src tev.
Proof.
  
Admitted.

Lemma split_non_passive_flip_eq : forall r t n rstl p, split_expr_non_passive r t false = Some rstl -> nth_error rstl n = Some p -> Some p.2 = ft_check_flip t (N.of_nat n) false.
Proof.
Admitted.

Lemma fillft_vm_eq : forall t t' v vmap, fillft_vm (tmap_type_size t) t v vmap = Some t' -> ftype_equiv t t'.
Proof.
Admitted.

Lemma Sem_frag_stmt_correct4r : forall s vmap tmap, Sem_frag_stmt' vmap s tmap -> 
  forall (v : ProdVarOrder.t), match find_sub_expr v s tmap with
  | Some el => match module_graph_vertex_set_p.find v vmap with
              | Some (OutPort gt) 
              | Some (Register gt) 
              | Some (RegisterReset gt _) 
              | Some (Wire gt) 
              | Some (Node gt) => forall e te, e \in el -> type_of_hfexpr_vm vmap e tmap = Some (Gtyp te) -> connect_fgtyp_compatible gt te
              | _ => true
              end
  | _ => true
  end
with Sem_frag_stmts_correct4r : forall ss vmap tmap, Sem_frag_stmts' vmap ss tmap -> 
  forall (v : ProdVarOrder.t), match find_sub_exprs v ss tmap with
  | Some el => match module_graph_vertex_set_p.find v vmap with
              | Some (OutPort gt) 
              | Some (Register gt) 
              | Some (RegisterReset gt _) 
              | Some (Wire gt) 
              | Some (Node gt) => forall e te, e \in el -> type_of_hfexpr_vm vmap e tmap = Some (Gtyp te) -> connect_fgtyp_compatible gt te
              | _ => true
              end
  | _ => true
  end.
Proof.
  clear Sem_frag_stmt_correct4r.
  intros.
  case Hs : s => [|r t|r reg|||r e|r e|r|c s1 s2]; rewrite Hs in H; simpl in H; simpl.
  - (* skip *)
    clear Sem_frag_stmts_correct4r.
    case Hv : (module_graph_vertex_set_p.find v vmap) => [vx|]; try done.
    case Hgt : vx => [gt|||||||||||||||||||||||||||||||||||||gt|gt|gt|gt|]; try done.
  - (* wire *)
    clear Sem_frag_stmts_correct4r.
    case Hv : (module_graph_vertex_set_p.find v vmap) => [vx|]; try done.
    case Hgt : vx => [gt|||||||||||||||||||||||||||||||||||||gt|gt|gt|gt|]; try done.
  - (* reg *)
    clear Sem_frag_stmts_correct4r.
    case Hr : (v.1 == r.1); try done.
    case Hrst : (reset reg) => [|rst_sig rst_val]; rewrite Hrst in H; try done.
    (* Nrst *)
    case Hv : (module_graph_vertex_set_p.find v vmap) => [vx|]; try done.
    case Hgt : vx => [gt|||||||||||||||||||||||||||||||||||||gt|gt|gt|gt|]; try done.
    (* Rst *)
    move : H => [Hrst_val Hfind].
    specialize Hfind with (n := N.to_nat v.2).
    case Hsplit : (split_expr_connect rst_val (type reg)) => [rstl|]; try done.
    case Hnth : (nth_error rstl (N.to_nat v.2)) => [e|]; try done.
    case Hval : (type_of_hfexpr_vm vmap rst_val tmap) => [t_rst|]; rewrite Hval in Hrst_val;try done.
    apply split_expr_type_vm_correct with (rhs_expr_ls := rstl) (n := (N.to_nat v.2)) in Hval; try done.
    rewrite Nnat.N2Nat.id in Hval Hfind.
    assert (N.to_nat v.2 < tmap_type_size (type reg)).
    admit.
    apply Hfind in H; clear Hfind.
    case Hfindv : (ft_find_sub (type reg) v.2) => [gt|]; rewrite Hfindv in H; try done.
    case H' : (type_of_hfexpr_vm vmap rst_sig tmap) => [a|]; rewrite H' in H; try done; clear H'.
    case H' : (a) => [f0||]; rewrite H' in H; try done; clear H' a.
    case H' : f0 => [n0||||||]; rewrite H' in H;try done; clear H' f0.
    case H' : n0 => [|n1]; rewrite H' in H; try done; clear H' n0.
    case H' : n1; rewrite H' in H; try done; clear H' n1.
    move /eqP : Hr => Hr; rewrite -Hr in H.
    rewrite -surjective_pairing in H.
    rewrite H.
    intros.
    rewrite mem_seq1 in H0.
    move /eqP : H0 => H0.
    rewrite H0 in H1; clear H0.
    apply ftype2fgtyp_compatible with (n := v.2) in Hrst_val.
    assert (ft_check_flip (type reg) v.2 false = Some false).
    admit. (* 除了fcnct，不考虑flip？重要！！ *)
    rewrite H0 Hfindv in Hrst_val.
    case Ht_rst : (ft_find_sub t_rst v.2) => [gte|]; rewrite Ht_rst in Hrst_val Hval.
    rewrite Hnth H1 in Hval.
    inversion Hval; done.
    admit. (* must not be none *)
      (* the same as sync reset *)
      move /eqP : Hr => Hr; rewrite -Hr in H.
      rewrite -surjective_pairing in H.
      rewrite H.
      intros.
      rewrite mem_seq1 in H0.
      move /eqP : H0 => H0.
      rewrite H0 in H1; clear H0.
      apply ftype2fgtyp_compatible with (n := v.2) in Hrst_val.
      assert (ft_check_flip (type reg) v.2 false = Some false).
      admit. (* 除了fcnct，不考虑flip？重要！！ *)
      rewrite H0 Hfindv in Hrst_val.
      case Ht_rst : (ft_find_sub t_rst v.2) => [gte|]; rewrite Ht_rst in Hrst_val Hval.
      rewrite Hnth H1 in Hval.
      inversion Hval; done.
      admit. (* must not be none *)
    rewrite /connect_type_compatible in Hrst_val.
    move /andP : Hrst_val => [H _]. 
    apply ftype_equiv_split_eq with (s := rst_val) in H.
    rewrite -H Hsplit; done.
    case Hv : (module_graph_vertex_set_p.find v vmap) => [vx|]; try done.
    case Hgt : vx => [gt|||||||||||||||||||||||||||||||||||||gt|gt|gt|gt|]; try done.
  - (* mem *)
    admit.
  - (* inst *)
    admit.
  - (* node *)
    clear Sem_frag_stmts_correct4r.
    case Hr : (v.1 == r.1); try done.
    case Hte : (type_of_hfexpr e tmap) => [te|]; try done.
    case Htev : (type_of_hfexpr_vm vmap e tmap) => [tev|]; rewrite Htev in H; try done. 
    case Hsplit : (split_expr_connect e te) => [rstl|]; try done.
    case Hnth : (nth_error rstl (N.to_nat v.2)) => [e0|]; try done.
    specialize H with (n := N.to_nat v.2).
    rewrite Nnat.N2Nat.id in H.
    assert (N.to_nat v.2 < tmap_type_size tev).
    admit.
    rewrite H0 in H; clear H0.
    case Hfindv : (ft_find_sub tev v.2) => [gt|]; rewrite Hfindv in H; try done.
    move /eqP : Hr => Hr; rewrite -Hr in H.
    rewrite -surjective_pairing in H.
    rewrite H.
    intros.
    rewrite mem_seq1 in H0.
    move /eqP : H0 => H0.
    rewrite H0 in H1; clear H0.
    apply split_expr_type_vm_correct with (rhs_expr_ls := rstl) (n := N.to_nat v.2) in Htev; try done.
    rewrite Nnat.N2Nat.id in Htev.
    rewrite Hfindv Hnth in Htev.
    rewrite Htev in H1.
    inversion H1; clear H1.
    admit.
    assert (ftype_equiv te tev).
    admit.
    apply ftype_equiv_split_eq with (s := e) in H0; rewrite -H0; done.
    (* v.1 <> r.1 *)
    case Hv : (module_graph_vertex_set_p.find v vmap) => [vx|]; try done.
    case Hgt : vx => [gt|||||||||||||||||||||||||||||||||||||gt|gt|gt|gt|]; try done.
  - (* fcnct *)
    clear Sem_frag_stmts_correct4r.
    case He : e => [t c| c e1 | u e1 | op e1 e2 | c e1 e2 | c e1 | r2 ]; rewrite He in H; try done.
    - (* 普通connection *)
      rewrite -He; rewrite -He in H.
      case Hbase : (base_ref r tmap) => [[v_tgt t_tgt]|]; rewrite Hbase in H; try done.
      case Hte : (type_of_hfexpr e tmap) => [t_src|]; try done.
      case Hr : (v.1 == v_tgt.1); try done.
      case Hsplit : (split_expr_connect e t_src) => [rstl|]; try done.
      case Hnth : (nth_error rstl (N.to_nat v.2 - N.to_nat v_tgt.2)) => [e0|]; try done.
      case Hfill : (fillft_vm (tmap_type_size t_tgt) t_tgt v_tgt vmap) => [t_tgt'|]; rewrite Hfill in H; try done.
      case Hv : (module_graph_vertex_set_p.find v vmap) => [vx|]; try done.
      case Hgt : vx => [gt|||||||||||||||||||||||||||||||||||||gt|gt|gt|gt|]; try done.
      case Hgte : (ft_find_sub t_tgt' (N.sub v.2 v_tgt.2)) => [gte|].
      apply component_vx_type_vm with (v := v) (vmap := vmap) (t_tgt' := t_tgt') (gte := gte) in Hbase; try done.
      rewrite Hr in Hbase.
      apply Hbase in Hfill; clear Hbase.
      rewrite Hv Hgt in Hfill.
      case Htev : (type_of_hfexpr_vm vmap e tmap) => [tev|]; rewrite Htev in H; try done.
      intros.
      rewrite mem_seq1 in H0.
      move /eqP : H0 => H0.
      rewrite H0 in H1; clear H0.
      generalize Htev.
      apply split_expr_type_vm_correct with (rhs_expr_ls := rstl) (n := N.to_nat v.2 - N.to_nat v_tgt.2) in Htev; try done.
      rewrite <-Nnat.N2Nat.inj_sub in Htev; try done.
      rewrite Nnat.N2Nat.id in Htev; try done.
      move => Htev'.
      rewrite -Hfill in Hgte; clear Hfill gte.
      case Htnev : (ft_find_sub tev (v.2 - v_tgt.2)) => [gnt|]; rewrite Htnev in Htev.
      rewrite <-Nnat.N2Nat.inj_sub in Hnth.
      rewrite Hnth in Htev.
      rewrite H1 in Htev; clear H1.
      inversion Htev; clear Htev.
      apply ftype2fgtyp_compatible with (n := (N.sub v.2 v_tgt.2)) in H; try done.
      assert (ft_check_flip t_tgt' (v.2 - v_tgt.2) false = Some false).
      admit.
      rewrite H0 Hgte Htnev in H; done.
      admit. (* 不是None *)
      apply type_of_hfexpr_vm_eq with (vmap := vmap) (tev := tev) in Hte; try done.
      apply ftype_equiv_split_eq with (s := e) in Hte.
      rewrite Hte in Hsplit; done.
      done.
      admit. (* None *)

      (* 相同的vx case *)
      admit.
      admit. 
      admit. 
      admit.
      admit.
      
    - (* 同样的e case *)
      admit.
      admit.
      admit.
      admit.
      admit.
    - (* Eref *)
      case Hbase : (base_ref r tmap) => [[v_tgt t_tgt]|]; rewrite Hbase in H; try done.
      case Hbase2 : (base_ref r2 tmap) => [[v_src t_src]|]; rewrite Hbase2 in H; try done.
      case Hr : (v.1 == v_tgt.1); try done.
        (* lhs *)
        case Hsplit : (split_expr_non_passive r2 t_src false) => [rstl|]; try done.
        case Hnth : (nth_error rstl (N.to_nat v.2 - N.to_nat v_tgt.2)) => [[refr b]|]; try done.
        case Hb : b; try done.
        case Hv : (module_graph_vertex_set_p.find v vmap) => [vx|]; try done.
        case Hgt : vx => [gt|||||||||||||||||||||||||||||||||||||gt|gt|gt|gt|]; try done.
        case Hv : (module_graph_vertex_set_p.find v vmap) => [vx|]; try done.
        case Hgt : vx => [gt|||||||||||||||||||||||||||||||||||||gt|gt|gt|gt|]; try done.
        intros.
        rewrite mem_seq1 in H0.
        move /eqP : H0 => H0.
        rewrite H0 in H1; clear H0.
        case Hfill : (fillft_vm (tmap_type_size t_tgt) t_tgt v_tgt vmap) => [t_tgt'|]; rewrite Hfill in H; try done.
        case Hfill2 : (fillft_vm (tmap_type_size t_src) t_src v_src vmap) => [t_src'|]; rewrite Hfill2 in H; try done.
        apply ftype2fgtyp_non_passive_compatible with (n := (N.sub v.2 v_tgt.2)) in H; try done.
        generalize Hsplit.
        apply split_non_passive_flip_eq with (n := N.to_nat v.2 - N.to_nat v_tgt.2) (p := (refr, b)) in Hsplit; try done.
        move => Hsplit'.
        simpl in Hsplit.
        rewrite <-Nnat.N2Nat.inj_sub in Hsplit; try done.
        rewrite Nnat.N2Nat.id in Hsplit; try done.
        assert (ftype_equiv t_tgt t_src).
        admit.
        apply ftype_eq_check_flip with (n := N.sub v.2 v_tgt.2) in H0.
        rewrite -H0 in Hsplit; clear H0.
        generalize Hfill.
        apply fillft_vm_eq in Hfill.
        apply ftype_eq_check_flip with (n := N.sub v.2 v_tgt.2) in Hfill.
        rewrite Hfill in Hsplit; clear Hfill.
        rewrite -Hsplit Hb in H.
        case Htgtn : (ft_find_sub t_tgt' (v.2 - v_tgt.2)) => [gte|]; rewrite Htgtn in H.
        apply component_vx_type_vm with (v := v) (vmap := vmap) (t_tgt' := t_tgt') (gte := gte) in Hbase; try done.
        rewrite Hr in Hbase.
        move => Hfill.
        apply Hbase in Hfill; clear Hbase.
        rewrite Hv Hgt in Hfill.
        rewrite -Hfill in Htgtn H; clear Hfill.
        apply fillft_vm_nth_eq with (r := r2) (rstl := rstl) (refr := refr) (b := b) (n := N.to_nat v.2 - N.to_nat v_tgt.2) (tmap := tmap) (gt := te) in Hfill2; try done.
        rewrite <-Nnat.N2Nat.inj_sub in Hfill2; try done.
        rewrite Nnat.N2Nat.id in Hfill2; try done.
        rewrite Hfill2 in H; done.
        done.
        admit. (* None *)
        (* 和上面一样的case *)
        admit.
        admit.
        admit.
        admit.
      case Hr2 : (v.1 == v_src.1); try done.
        (* rhs *)
        case Hsplit : (split_expr_non_passive r t_tgt false) => [rstl|]; try done.
        case Hnth : (nth_error rstl (N.to_nat v.2 - N.to_nat v_src.2)) => [[refr b]|]; try done.
        case Hb : b; try done.
        case Hv : (module_graph_vertex_set_p.find v vmap) => [vx|]; try done.
        case Hgt : vx => [gt|||||||||||||||||||||||||||||||||||||gt|gt|gt|gt|]; try done.
        intros.
        rewrite mem_seq1 in H0.
        move /eqP : H0 => H0.
        rewrite H0 in H1; clear H0.
        case Hfill : (fillft_vm (tmap_type_size t_tgt) t_tgt v_tgt vmap) => [t_tgt'|]; rewrite Hfill in H; try done.
        case Hfill2 : (fillft_vm (tmap_type_size t_src) t_src v_src vmap) => [t_src'|]; rewrite Hfill2 in H; try done.
        generalize Hfill.
        apply ftype2fgtyp_non_passive_compatible with (n := (N.sub v.2 v_src.2)) in H; try done.
        generalize Hsplit.
        apply split_non_passive_flip_eq with (n := N.to_nat v.2 - N.to_nat v_src.2) (p := (refr, b)) in Hsplit; try done.
        move => Hsplit'.
        simpl in Hsplit.
        rewrite <-Nnat.N2Nat.inj_sub in Hsplit; try done.
        rewrite Nnat.N2Nat.id in Hsplit; try done.
        apply fillft_vm_eq in Hfill.
        apply ftype_eq_check_flip with (n := N.sub v.2 v_src.2) in Hfill.
        rewrite Hfill in Hsplit; clear Hfill.
        move => Hfill.
        rewrite -Hsplit Hb in H.
        case Hsrcn : (ft_find_sub t_src' (v.2 - v_src.2)) => [gte|]; rewrite Hsrcn in H.
        apply component_vx_type_vm with (v := v) (vmap := vmap) (t_tgt' := t_src') (gte := gte) in Hbase2; try done.
        rewrite Hr2 in Hbase2.
        apply Hbase2 in Hfill2; clear Hbase2.
        rewrite Hv Hgt in Hfill2.
        rewrite -Hfill2 in Hsrcn H; clear Hfill2.
        apply fillft_vm_nth_eq with (r := r) (rstl := rstl) (refr := refr) (b := b) (n := N.to_nat v.2 - N.to_nat v_src.2) (tmap := tmap) (gt := te) in Hfill; try done.
        rewrite <-Nnat.N2Nat.inj_sub in Hfill; try done.
        rewrite Nnat.N2Nat.id in Hfill; try done.
        rewrite Hfill in H; done.
        done.
        admit. (* None *)
        (* 和上面一样的case *)
        admit.
        admit.
        admit.
        admit.
        case Hv : (module_graph_vertex_set_p.find v vmap) => [vx|]; try done.
        case Hgt : vx => [gt|||||||||||||||||||||||||||||||||||||gt|gt|gt|gt|]; try done.
        case Hv : (module_graph_vertex_set_p.find v vmap) => [vx|]; try done.
        case Hgt : vx => [gt|||||||||||||||||||||||||||||||||||||gt|gt|gt|gt|]; try done.
  - (* invalid *)
    clear Sem_frag_stmts_correct4r.
    case Hv : (module_graph_vertex_set_p.find v vmap) => [vx|]; try done.
    case Hgt : vx => [gt|||||||||||||||||||||||||||||||||||||gt|gt|gt|gt|]; try done.
  - (* when *)
    move : H => [H0 H1].
    apply Sem_frag_stmts_correct4r with (v := v) in H0.
    case Hfind1 : (find_sub_exprs v s1 tmap) => [el1|]; rewrite Hfind1 in H0; try done.
    apply Sem_frag_stmts_correct4r with (v := v) in H1.
    case Hfind2 : (find_sub_exprs v s2 tmap) => [el2|]; rewrite Hfind2 in H1; try done.
    case Hv : (module_graph_vertex_set_p.find v vmap) => [vx|]; rewrite Hv in H0 H1; try done.
    case Hgt : vx => [gt|||||||||||||||||||||||||||||||||||||gt|gt|gt|gt|]; rewrite Hgt in H0 H1; try done.
    intros.
    rewrite mem_cat in H.
    case Hin1 : (e \in el1); rewrite Hin1 in H.
    apply H0 with (te := te) in Hin1; try done.
    rewrite orb_false_l in H.
    apply H1 with (te := te) in H; try done.
    (* 一样的vx case *)
    admit.
    admit.
    admit.
    admit.

  clear Sem_frag_stmts_correct4r.
  elim.
  admit.
  intros hd tl IH vmap tmap Hsem v.
  simpl.
  simpl in Hsem.
  move : Hsem => [Hsem0 Hsem].
  apply Sem_frag_stmt_correct4r with (v := v) in Hsem0.
  apply IH with (v := v) in Hsem.
  case Hhd : (find_sub_expr v hd tmap) => [el1|]; rewrite Hhd in Hsem0; try done.
  case Htl : (find_sub_exprs v tl tmap) => [el2|]; rewrite Htl in Hsem; try done.
  case Hv : (module_graph_vertex_set_p.find v vmap) => [vx|]; rewrite Hv in Hsem0 Hsem; try done.
  case Hgt : vx => [gt|||||||||||||||||||||||||||||||||||||gt|gt|gt|gt|]; rewrite Hgt in Hsem0 Hsem; try done.
  intros.
  rewrite mem_cat in H.
  case Hin1 : (e \in el1); rewrite Hin1 in H.
  apply Hsem0 with (te := te) in Hin1; try done.
  rewrite orb_false_l in H.
  apply Hsem with (te := te) in H; try done.
  (* 一样的vx case *)
  admit.
  admit.
  admit.
  admit.
Admitted.

Lemma add_expr_connect_findn : forall (r v : ProdVarOrder.t) rstl (var2exprs0 : var2exprsmap), 
  if (v.1 == r.1) then 
    if (v.2 <= N.add r.2 (N.of_nat (List.length rstl))) 
      then match module_graph_vertex_set_p.find v var2exprs0, List.nth_error rstl (N.to_nat (N.sub v.2 r.2)) with
      | Some el0, Some e => module_graph_vertex_set_p.find v (add_expr_connect r rstl var2exprs0) = Some (e :: el0)
      | None, Some e => module_graph_vertex_set_p.find v (add_expr_connect r rstl var2exprs0) = Some [::e]
      | _,_ => module_graph_vertex_set_p.find v var2exprs0 = module_graph_vertex_set_p.find v (add_expr_connect r rstl var2exprs0)
      end
    else
      module_graph_vertex_set_p.find v var2exprs0 = module_graph_vertex_set_p.find v (add_expr_connect r rstl var2exprs0)
  else 
    module_graph_vertex_set_p.find v var2exprs0 = module_graph_vertex_set_p.find v (add_expr_connect r rstl var2exprs0).
Proof.
Admitted.

Lemma add_expr_non_passive_findn : forall (v v_tgt v_src : ProdVarOrder.t) lhsl rhsl (var2exprs0 var2exprs : var2exprsmap), 
  add_expr_connect_non_passive v_tgt v_src lhsl rhsl var2exprs0 = Some var2exprs ->
  if (v.1 == v_tgt.1) then 
    if (v.2 <= N.add v_tgt.2 (N.of_nat (List.length rhsl))) 
      then match module_graph_vertex_set_p.find v var2exprs0, List.nth_error rhsl (N.to_nat (N.sub v.2 v_tgt.2)) with
      | Some el0, Some (e, false) => module_graph_vertex_set_p.find v var2exprs = Some ((Eref e) :: el0) 
      | None, Some (e, false) => module_graph_vertex_set_p.find v var2exprs = Some [::(Eref e)] 
      | _,_ => module_graph_vertex_set_p.find v var2exprs0 = module_graph_vertex_set_p.find v var2exprs
      end
    else
    module_graph_vertex_set_p.find v var2exprs0 = module_graph_vertex_set_p.find v var2exprs
  else if (v.1 == v_src.1) then
    if (v.2 <= N.add v_src.2 (N.of_nat (List.length lhsl))) 
      then match module_graph_vertex_set_p.find v var2exprs0, List.nth_error lhsl (N.to_nat (N.sub v.2 v_src.2)) with
      | Some el0, Some (e, true) => module_graph_vertex_set_p.find v var2exprs = Some ((Eref e) :: el0) 
      | None, Some (e, true) => module_graph_vertex_set_p.find v var2exprs = Some [::(Eref e)] 
      | _,_ => module_graph_vertex_set_p.find v var2exprs0 = module_graph_vertex_set_p.find v var2exprs
      end
    else
    module_graph_vertex_set_p.find v var2exprs0 = module_graph_vertex_set_p.find v var2exprs
  else
    module_graph_vertex_set_p.find v var2exprs0 = module_graph_vertex_set_p.find v var2exprs.
Proof.
Admitted.

Lemma find_sub_expr_eq : forall s tmap0 tmap var2exprs0 var2exprs, stmt_tmap (tmap0, var2exprs0) s = Some (tmap, var2exprs) ->
  forall (v : ProdVarOrder.t), match module_graph_vertex_set_p.find v var2exprs0, find_sub_expr v s tmap, module_graph_vertex_set_p.find v var2exprs with
  | Some el0, Some el', Some el => TopoSort.subset el (el' ++ el0) /\ TopoSort.subset (el' ++ el0) el
  | Some el0, None, Some el => TopoSort.subset el el0 /\ TopoSort.subset el0 el
  | None, Some el', Some el => TopoSort.subset el el' /\ TopoSort.subset el' el
  | None, Some nil, None => True
  | None, None, None => True
  | _,_, _ => False
  end
with find_sub_exprs_eq : forall ss tmap0 tmap var2exprs0 var2exprs, stmts_tmap (tmap0, var2exprs0) ss = Some (tmap, var2exprs) ->
  forall (v : ProdVarOrder.t), match module_graph_vertex_set_p.find v var2exprs0, find_sub_exprs v ss tmap, module_graph_vertex_set_p.find v var2exprs with
  | Some el0, Some el', Some el => TopoSort.subset el (el' ++ el0) /\ TopoSort.subset (el' ++ el0) el
  | Some el0, None, Some el => TopoSort.subset el el0 /\ TopoSort.subset el0 el
  | None, Some el', Some el => TopoSort.subset el el' /\ TopoSort.subset el' el
  | None, Some nil, None => True
  | None, None, None => True
  | _,_, _ => False
  end.
Proof.
  clear find_sub_expr_eq.
  intros.
  case Hs : s => [|r t|r reg|||r e|r e|r|c s1 s2]; rewrite Hs in H; simpl in H; simpl.
  - (* skip *)
    inversion H. 
    case Hfind : (module_graph_vertex_set_p.find v var2exprs) => [el0|]; try done.
    split; apply TopoSort.subset_refl.
  - (* wire *)
    case Hr : (CEP.find r tmap0); rewrite Hr in H; try discriminate.
    inversion H.
    case Hfind : (module_graph_vertex_set_p.find v var2exprs) => [el0|]; try done.
    split; apply TopoSort.subset_refl.
  - (* reg *)
    clear find_sub_exprs_eq.
    case Hr : (CEP.find r tmap0); rewrite Hr in H; try discriminate.
    case Hrst : (reset reg) => [|rst_sig rst_val]; rewrite Hrst in H.
    inversion H.
    case Hfind : (module_graph_vertex_set_p.find v var2exprs) => [el0|]; try done.
    case : (v.1 == r.1); simpl; split; apply TopoSort.subset_refl.
    case : (v.1 == r.1); simpl; done.
    case Hsplit : (split_expr_connect rst_val (type reg)) => [rstl|]; rewrite Hsplit in H; try discriminate.
    inversion H; clear H.
    specialize add_expr_connect_findn with (r := r) (v := v) (rstl := rstl) (var2exprs0 := var2exprs0); intro.
    case Hv : (v.1 == r.1); rewrite Hv in H.
    assert (Hv2 : v.2 <= (N.of_nat (length rstl))).
    admit.
    assert (r.2 = N0).
    admit.
    rewrite H0 in H; clear H0.
    rewrite Hv2 in H.
    case Hfind0 : (module_graph_vertex_set_p.find v var2exprs0) => [el0|]; rewrite Hfind0 in H.
    assert ((N.to_nat (v.2 - 0)) = (N.to_nat v.2)).
    admit.
    rewrite H0 in H; clear H0.
    case Hnth : (nth_error rstl (N.to_nat v.2)) => [e|]; rewrite Hnth in H.
    rewrite H.
    assert ((e :: el0) = ([:: e] ++ el0)).
    simpl; done.
    rewrite H0.
    split; rewrite TopoSort.subset_refl; done.
    rewrite -H.
    split; rewrite TopoSort.subset_refl; done.
    assert ((N.to_nat (v.2 - 0)) = (N.to_nat v.2)).
    admit.
    rewrite H0 in H; clear H0.
    case Hnth : (nth_error rstl (N.to_nat v.2)) => [e|]; rewrite Hnth in H.
    rewrite H.
    simpl.
    rewrite mem_seq1.
    rewrite eq_refl; done.
    rewrite -H; done.
    case Hfind0 : (module_graph_vertex_set_p.find v var2exprs0) => [el0|]; rewrite Hfind0 in H.
    rewrite -H.
    simpl.
    split; rewrite TopoSort.subset_refl; done.
    rewrite -H; done.
  discriminate.
  discriminate.
  - (* node *)
    clear find_sub_exprs_eq.
    case Hr : (CEP.find r tmap0); rewrite Hr in H; try discriminate.
    case Hte : (type_of_hfexpr e tmap0) => [te|]; rewrite Hte in H; try discriminate.
    case Hsplit : (split_expr_connect e te) => [rstl|]; rewrite Hsplit in H; try discriminate.
    inversion H.
    case Hfind : (module_graph_vertex_set_p.find v var2exprs0) => [el0|]; try done.
    specialize add_expr_connect_findn with (r := r) (v := v) (rstl := rstl) (var2exprs0 := var2exprs0); intro.
    case Hv : (v.1 == r.1); rewrite Hv in H0.
    assert (Hv2 : v.2 <= (N.of_nat (length rstl))).
    admit.
    assert (r.2 = N0).
    admit.
    rewrite H3 in H0.
    rewrite Hv2 in H0.
    rewrite Hfind in H0.
    assert (r = (r.1, N0)).
    rewrite -H3.
    apply surjective_pairing.
    rewrite {1}H4; clear H4 H3.
    rewrite type_of_hfexpr_eq Hte Hsplit.
    assert ((N.to_nat (v.2 - 0)) = (N.to_nat v.2)).
    admit.
    rewrite H3 in H0; clear H3.
    case Hnth : (nth_error rstl (N.to_nat v.2)) => [e0|]; rewrite Hnth in H0.
    rewrite H0.
    assert ((e0 :: el0) = ([:: e0] ++ el0)).
    simpl; done.
    rewrite H3.
    split; rewrite TopoSort.subset_refl; done.
    rewrite -H0.
    split; rewrite TopoSort.subset_refl; done.
    rewrite -H0 Hfind.
    simpl; rewrite TopoSort.subset_refl; done.
    specialize add_expr_connect_findn with (r := r) (v := v) (rstl := rstl) (var2exprs0 := var2exprs0); intro.
    case Hv : (v.1 == r.1); rewrite Hv in H0.
    assert (Hv2 : v.2 <= (N.of_nat (length rstl))).
    admit.
    assert (r.2 = N0).
    admit.
    rewrite H3 in H0.
    rewrite Hv2 in H0.
    rewrite Hfind in H0.
    assert (r = (r.1, N0)).
    rewrite -H3.
    apply surjective_pairing.
    rewrite {1}H4; clear H4 H3.
    rewrite type_of_hfexpr_eq Hte Hsplit.
    assert ((N.to_nat (v.2 - 0)) = (N.to_nat v.2)).
    admit.
    rewrite H3 in H0; clear H3.
    case Hnth : (nth_error rstl (N.to_nat v.2)) => [e0|]; rewrite Hnth in H0.
    rewrite H0.
    rewrite TopoSort.subset_refl; done.
    rewrite -H0; done.
    rewrite -H0 Hfind; done.
  - (* fcnct *)
    clear find_sub_exprs_eq.
    case He : e =>[t c| c e1 | u e1 | op e1 e2 | c e1 e2 | c e1 | r2 ]; rewrite He in H; try done.
    (* 一般connection *)
    rewrite -He; rewrite -He in H.
    case Hbase : (base_ref r tmap0) => [[v_tgt t_tgt]|]; rewrite Hbase in H; try discriminate.
    case Hte : (type_of_hfexpr e tmap0) => [t_src|]; rewrite Hte in H; try discriminate.
    case Hconnect : (connect_type_compatible t_tgt t_src); rewrite Hconnect in H; try discriminate.
    case Hsplit : (split_expr_connect e t_src) => [rstl|]; rewrite Hsplit in H; try discriminate.
    inversion H; clear H.
    specialize add_expr_connect_findn with (r := v_tgt) (v := v) (rstl := rstl) (var2exprs0 := var2exprs0); intro.
    case Hv : (v.1 == v_tgt.1); rewrite Hv in H.
    case Hv2 : (v.2 <= N.add v_tgt.2 (N.of_nat (length rstl))); rewrite Hv2 in H.
    case Hfind0 : (module_graph_vertex_set_p.find v var2exprs0) => [el0|]; rewrite Hfind0 in H.
    rewrite -H1 Hbase Hte Hv Hsplit.
    rewrite <-Nnat.N2Nat.inj_sub.
    case Hnth : (nth_error rstl (N.to_nat (v.2 - v_tgt.2))) => [e0|]; rewrite Hnth in H.
    rewrite H.
    assert ((e0 :: el0) = ([:: e0] ++ el0)).
    simpl; done.
    rewrite H0.
    split; rewrite TopoSort.subset_refl; done.
    rewrite -H.
    split; rewrite TopoSort.subset_refl; done.
      (* the same *)
      rewrite -H1 Hbase Hte Hv Hsplit.
      rewrite <-Nnat.N2Nat.inj_sub.
      case Hnth : (nth_error rstl (N.to_nat (v.2 - v_tgt.2))) => [e0|]; rewrite Hnth in H.
      rewrite H.
      split; rewrite TopoSort.subset_refl; done.
      rewrite -H.
      split; rewrite TopoSort.subset_refl; done.
    case Hfind0 : (module_graph_vertex_set_p.find v var2exprs0) => [el0|]; rewrite Hfind0 in H.
    rewrite -H1 Hbase Hte Hv Hsplit.
    rewrite <-Nnat.N2Nat.inj_sub.
    assert (nth_error rstl (N.to_nat (v.2 - v_tgt.2)) = None).
    admit. (* v.2超出range *)
    rewrite H0 -H.
    split; rewrite TopoSort.subset_refl; done.
    rewrite -H1 Hbase Hte Hv Hsplit.
    rewrite <-Nnat.N2Nat.inj_sub.
    assert (nth_error rstl (N.to_nat (v.2 - v_tgt.2)) = None).
    admit. (* v.2超出range *)
    rewrite H0 - H; done.
    case Hfind0 : (module_graph_vertex_set_p.find v var2exprs0) => [el0|]; rewrite Hfind0 in H.
    rewrite -H1 Hbase Hte Hv.
    rewrite -H.
    simpl.
    split; rewrite TopoSort.subset_refl; done.
    rewrite -H1 Hbase Hte Hv.
    rewrite -H.
    simpl.
    split; rewrite TopoSort.subset_refl; done.
    (* 同上的connection case *)
    admit.
    admit.
    admit.
    admit.
    admit.
    (* Eref connection *)
    case Hbase : (base_ref r tmap0) => [[v_tgt t_tgt]|]; rewrite Hbase in H; try discriminate.
    case Hbase2 : (base_ref r2 tmap0) => [[v_src t_src]|]; rewrite Hbase2 in H; try discriminate.
    case Hsplit : (split_expr_non_passive r t_tgt false) => [lhsl|]; rewrite Hsplit in H; try discriminate.
    case Hsplit2 : (split_expr_non_passive r2 t_src false) => [rhsl|]; rewrite Hsplit2 in H; try discriminate.
    case Hadd : (add_expr_connect_non_passive v_tgt v_src lhsl rhsl var2exprs0) => [newv2e|]; rewrite Hadd in H; try discriminate.
    inversion H; clear H.
    rewrite H2 in Hadd; clear H2 newv2e.
    rewrite -H1 Hbase Hbase2 Hsplit2 Hsplit.
    apply add_expr_non_passive_findn with (v := v) (v_tgt := v_tgt) (v_src := v_src) (lhsl := lhsl) (rhsl := rhsl) (var2exprs0 := var2exprs0) (var2exprs := var2exprs) in Hadd.
    (* Nflip *)
    case Hv : (v.1 == v_tgt.1); rewrite Hv in Hadd.
    case Hv2 : (v.2 <= N.add v_tgt.2 (N.of_nat (length rhsl))); rewrite Hv2 in Hadd.
    case Hfind0 : (module_graph_vertex_set_p.find v var2exprs0) => [el0|]; rewrite Hfind0 in Hadd.
    rewrite <-Nnat.N2Nat.inj_sub.
    case Hnth : (nth_error rhsl (N.to_nat (v.2 - v_tgt.2))) => [[refr b]|]; rewrite Hnth in Hadd.
    case Hb : b; rewrite Hb in Hadd; try done.
    rewrite -Hadd.
    split; rewrite TopoSort.subset_refl; done.
    rewrite Hadd.
    assert ((Eref refr :: el0) = ([:: Eref refr] ++ el0)).
    simpl; done.
    rewrite H.
    split; rewrite TopoSort.subset_refl; done.
    rewrite -Hadd.
    split; rewrite TopoSort.subset_refl; done.
      (* the same case *)
      rewrite <-Nnat.N2Nat.inj_sub.
      case Hnth : (nth_error rhsl (N.to_nat (v.2 - v_tgt.2))) => [[refr b]|]; rewrite Hnth in Hadd.
      case Hb : b; rewrite Hb in Hadd; try done.
      rewrite -Hadd; done.
      rewrite Hadd.
      split; rewrite TopoSort.subset_refl; done.
      rewrite -Hadd; done.
    case Hfind0 : (module_graph_vertex_set_p.find v var2exprs0) => [el0|].
    assert (nth_error rhsl (N.to_nat v.2 - N.to_nat v_tgt.2) = None).
    admit.
    rewrite H; clear H.
    rewrite -Hadd Hfind0.
    split; rewrite TopoSort.subset_refl; done.
    assert (nth_error rhsl (N.to_nat v.2 - N.to_nat v_tgt.2) = None).
    admit.
    rewrite H; clear H.
    rewrite -Hadd Hfind0; done.
    (* flipped *)
    clear Hv.
    case Hv : (v.1 == v_src.1); rewrite Hv in Hadd.
    case Hv2 : (v.2 <= N.add v_src.2 (N.of_nat (length lhsl))); rewrite Hv2 in Hadd.
    case Hfind0 : (module_graph_vertex_set_p.find v var2exprs0) => [el0|]; rewrite Hfind0 in Hadd.
    rewrite <-Nnat.N2Nat.inj_sub.
    case Hnth : (nth_error lhsl (N.to_nat (v.2 - v_src.2))) => [[refl b]|]; rewrite Hnth in Hadd.
    case Hb : b; rewrite Hb in Hadd; try done.
    rewrite Hadd.
    assert ((Eref refl :: el0) = ([:: Eref refl] ++ el0)).
    simpl; done.
    rewrite H.
    split; rewrite TopoSort.subset_refl; done.
    rewrite -Hadd.
    split; rewrite TopoSort.subset_refl; done.
    rewrite -Hadd.
    split; rewrite TopoSort.subset_refl; done.
      (* the same case *)
      rewrite <-Nnat.N2Nat.inj_sub.
      case Hnth : (nth_error lhsl (N.to_nat (v.2 - v_src.2))) => [[refl b]|]; rewrite Hnth in Hadd.
      case Hb : b; rewrite Hb in Hadd; try done.
      rewrite Hadd.
      split; rewrite TopoSort.subset_refl; done.
      rewrite -Hadd; done.
      rewrite -Hadd; done.
    case Hfind0 : (module_graph_vertex_set_p.find v var2exprs0) => [el0|].
    assert (nth_error lhsl (N.to_nat v.2 - N.to_nat v_src.2) = None).
    admit.
    rewrite H; clear H.
    rewrite -Hadd Hfind0.
    split; rewrite TopoSort.subset_refl; done.
    assert (nth_error lhsl (N.to_nat v.2 - N.to_nat v_src.2) = None).
    admit.
    rewrite H; clear H.
    rewrite -Hadd Hfind0; done.
    case Hfind0 : (module_graph_vertex_set_p.find v var2exprs0) => [el0|].
    rewrite -Hadd Hfind0; simpl.
    split; rewrite TopoSort.subset_refl; done.
    rewrite -Hadd Hfind0; done.
  - (* invalid *)
    inversion H. 
    case Hfind : (module_graph_vertex_set_p.find v var2exprs) => [el0|]; try done.
    split; apply TopoSort.subset_refl.
  - (* when *)
    case Hstmts : (stmts_tmap (tmap0, var2exprs0) s1) => [[tmap' var2exprs']|]; rewrite Hstmts in H. 
    apply find_sub_exprs_eq with (v := v) in Hstmts.
    apply find_sub_exprs_eq with (v := v) in H; clear find_sub_exprs_eq.
    case Hfind0 : (module_graph_vertex_set_p.find v var2exprs0) => [el0|]; rewrite Hfind0 in Hstmts; try done.
    case Hfind' : (module_graph_vertex_set_p.find v var2exprs') => [el'|]; rewrite Hfind' in H; try done.
    assert (find_sub_exprs v s1 tmap = find_sub_exprs v s1 tmap').
    admit.
    case Hexpr1 : (find_sub_exprs v s1 tmap) => [e1|]; rewrite -H0 Hexpr1 Hfind' in Hstmts.
    case Hexpr2 : (find_sub_exprs v s2 tmap) => [e2|]; rewrite Hexpr2 in H.
    case Hfind : (module_graph_vertex_set_p.find v var2exprs) => [el|]; rewrite Hfind in H; try done.
    admit.
    admit. (* 不是None *)
    admit. (* 不是None *)
    assert (find_sub_exprs v s1 tmap = find_sub_exprs v s1 tmap').
    admit.
    case Hexpr1 : (find_sub_exprs v s1 tmap) => [e1|]; rewrite -H0 Hexpr1 Hfind' in Hstmts.
    case Hexpr2 : (find_sub_exprs v s2 tmap) => [e2|]; rewrite Hexpr2 in H.
    case Hfind : (module_graph_vertex_set_p.find v var2exprs) => [el|]; rewrite Hfind in H; try done.
    done.
    done.
    (* same case *)
      case Hfind' : (module_graph_vertex_set_p.find v var2exprs') => [el'|]; rewrite Hfind' in H; try done.
      assert (find_sub_exprs v s1 tmap = find_sub_exprs v s1 tmap').
      admit.
      case Hexpr1 : (find_sub_exprs v s1 tmap) => [e1|]; rewrite -H0 Hexpr1 Hfind' in Hstmts.
      case Hexpr2 : (find_sub_exprs v s2 tmap) => [e2|]; rewrite Hexpr2 in H.
      case Hfind : (module_graph_vertex_set_p.find v var2exprs) => [el|]; rewrite Hfind in H; try done.
      admit.
      admit. (* 不是None *)
      done.
      assert (find_sub_exprs v s1 tmap = find_sub_exprs v s1 tmap').
      admit.
      case Hexpr1 : (find_sub_exprs v s1 tmap) => [e1|]; rewrite -H0 Hexpr1 Hfind' in Hstmts.
      case Hexpr2 : (find_sub_exprs v s2 tmap) => [e2|]; rewrite Hexpr2 in H.
      case Hfind : (module_graph_vertex_set_p.find v var2exprs) => [el|]; rewrite Hfind in H; try done.
      case He1 : e1; rewrite He1 in Hstmts; try done.
      case He1 : e1; rewrite He1 in Hstmts; try done.
      case He1 : e1; rewrite He1 in Hstmts; try done.
      admit. (* 不是None *)
      discriminate.

  clear find_sub_exprs_eq.
  elim.
  admit.
  intros hd tl IH tmap0 tmap var2exprs0 var2exprs H v.
  simpl in H.
  case Hstmts : (stmt_tmap (tmap0, var2exprs0) hd) => [[tmap' var2exprs']|]; rewrite Hstmts in H. 
  apply find_sub_expr_eq with (v := v) in Hstmts.
  apply IH with (v := v) in H; clear find_sub_expr_eq IH.
  case Hfind0 : (module_graph_vertex_set_p.find v var2exprs0) => [el0|]; rewrite Hfind0 in Hstmts; try done; simpl.
  case Hfind' : (module_graph_vertex_set_p.find v var2exprs') => [el'|]; rewrite Hfind' in H; try done; simpl.
  assert (find_sub_expr v hd tmap = find_sub_expr v hd tmap').
  admit.
  case Hexpr1 : (find_sub_expr v hd tmap) => [e1|]; rewrite -H0 Hexpr1 Hfind' in Hstmts.
  case Hexpr2 : (find_sub_exprs v tl tmap) => [e2|]; rewrite Hexpr2 in H.
  case Hfind : (module_graph_vertex_set_p.find v var2exprs) => [el|]; rewrite Hfind in H; try done.
  admit.
  admit. (* 不是None *)
  admit. (* 不是None *)
  case Hexpr1 : (find_sub_expr v hd tmap') => [e1|]; rewrite Hexpr1 Hfind' in Hstmts; try done.
  assert (find_sub_expr v hd tmap = find_sub_expr v hd tmap').
  admit.
    (* same case *)
    case Hfind' : (module_graph_vertex_set_p.find v var2exprs') => [el'|]; rewrite Hfind' in H; try done.
    assert (find_sub_expr v hd tmap = find_sub_expr v hd tmap').
    admit.
    case Hexpr1 : (find_sub_expr v hd tmap) => [e1|]; rewrite -H0 Hexpr1 Hfind' in Hstmts; try done.
    case Hexpr2 : (find_sub_exprs v tl tmap) => [e2|]; rewrite Hexpr2 in H; try done.
    case Hfind : (module_graph_vertex_set_p.find v var2exprs) => [el|]; rewrite Hfind in H; try done.
    admit.
    admit. (* 不是None *)
    case Hexpr1 : (find_sub_expr v hd tmap) => [e1|]; rewrite -H0 Hexpr1 Hfind' in Hstmts; try done.
    case Hexpr2 : (find_sub_exprs v tl tmap) => [e2|]; rewrite Hexpr2 in H; try done.
    case He1 : e1; rewrite He1 in Hstmts; try done.
    admit. (* 不是None *)
    discriminate.
Admitted.

Lemma InferWidths_fun_correct' : forall (vmap : module_graph_vertex_set_p.env) (var2exprs : var2exprsmap) (tmap : CEP.t ftype) (pp : seq HiFP.hfport) (ss : HiFP.hfstmt_seq), 
  stmts_tmap (ports_tmap pp, module_graph_vertex_set_p.empty (seq HiFP.hfexpr)) ss = Some (tmap, var2exprs) ->
  Sem_frag_stmts' vmap ss tmap -> 
  forall (v : ProdVarOrder.t), match module_graph_vertex_set_p.find v vmap with
  | Some (OutPort gt) 
  | Some (Register gt) 
  | Some (RegisterReset gt _) 
  | Some (Wire gt) 
  | Some (Node gt) => match module_graph_vertex_set_p.find v var2exprs, CEP.find (fst v, N0) tmap with
                    | Some el, Some init => match fil_ftlist (map (fun e => type_of_hfexpr_vm vmap e tmap) el), ft_find_sub init v.2 with
                                | Some eftl, Some initt => if (not_implicit gt) then true else
                                                          match max_ftlist eftl initt with
                                                          | Some nt => sizeof_fgtyp gt >= sizeof_fgtyp nt
                                                          | _ => true
                                                          end
                                | _,_ => true
                                end
                    | _,_ => true
                    end
  | _ => true
  end.
Proof.
  intros vmap var2exprs tmap pp ss Hprepro Hsem v.
  apply Sem_frag_stmts_correct4r with (v := v) in Hsem.
  case Hvx : (module_graph_vertex_set_p.find v vmap) => [vx|]; rewrite Hvx in Hsem; try done.
  case Hgt : vx => [gt|||||||||||||||||||||||||||||||||||||gt|gt|gt|gt|]; rewrite Hgt in Hsem; try done.
  apply find_sub_exprs_eq with (v := v) in Hprepro.
  case Hel : (module_graph_vertex_set_p.find v var2exprs) => [el|]; rewrite Hel in Hprepro; try done.

  case Hinit : (CEP.find (v.1, 0%num) tmap) => [init|]; try done.
  case Hfil : (fil_ftlist [seq type_of_hfexpr_vm vmap e tmap | e <- el]) => [eftl|]; try done.
  case Hinitt : (ft_find_sub init v.2) => [initt|]; try done.
  case Himpli : (not_implicit gt); try done.
  case Hmax : (max_ftlist eftl initt) => [nt|]; try done.
  apply geq_conj2mux with (vmap := vmap) (tmap := tmap) (initt := initt) (el := el) (eftl := eftl); try done.

  case Hel' : (find_sub_exprs v ss tmap) => [el'|]; rewrite Hel' in Hsem Hprepro; try done.
  intros texpr tge Hin Htge.
  apply Hsem in Htge.
  rewrite /connect_fgtyp_compatible Himpli in Htge.
  move /andP : Htge => [Htge _]; done.
  simpl in Hprepro.
  case Hel'' : el'; rewrite Hel'' in Hprepro.
  rewrite -Hel''; rewrite -Hel'' in Hprepro.
  move : Hprepro => [Hprepro _]. 
  apply TopoSort.in_subset_trans with (x := texpr) in Hprepro; try done.
  rewrite -Hel''; rewrite -Hel'' in Hprepro.
  move : Hprepro => [Hprepro _]. 
  apply TopoSort.in_subset_trans with (x := texpr) in Hprepro; try done.

  admit. (* 最初tmap中应该所有implicit为0 *)

  (*assert (exists t0, Qin (@Swire ProdVarOrder.T (v.1, N0) t0) ss).

   assert (((Finput (v.1, N0) init) \in pp) \/ 
          (Qin (Swire (v.1, N0) init) ss \/
          (exists reg0, Qin (Sreg (v.1, N0) reg0) ss /\ (type reg0 = init)) \/
          (exists e0, Qin (Snode (v.1, N0) e0) ss /\ (type_of_hfexpr_vm vmap e0 tmap = init))).
  *) (* 但也可能存在在when？ *)

  

  (* case1 : 是flip的v *)
  (*assert (forall texpr, texpr \in el -> 
  (exists r0 r1 v_ref rhsl, base_ref r1 tmap = Some v_ref -> split_expr_non_passive r0 v_ref.2 = Some lhsl -> 
                 (v_ref.1.1 = v.1) /\ (List.nth_error lhsl (N.to_nat (N.sub v.2 v_ref.1.2)) = Some (texpr, true)) /\ (Qin (Sfcnct r0 (Eref r1)) ss))).
  *)
  admit.

  (* case2 : 不是flip的v *)
  (*assert (forall texpr, texpr \in el -> 
  (exists r0 e0 v_ref el, base_ref r0 tmap = Some v_ref -> split_expr_connect e0 v_ref.2 = Some el -> 
                 (v_ref.1.1 = v.1) /\ (List.nth_error el (N.to_nat (N.sub v.2 v_ref.1.2)) = Some texpr) /\ (Qin (Snode r0 e0) ss)) \/
  (exists r0 r1 v_ref rhsl, base_ref r0 tmap = Some v_ref -> split_expr_non_passive r1 v_ref.2 = Some rhsl -> 
                 (v_ref.1.1 = v.1) /\ (List.nth_error rhsl (N.to_nat (N.sub v.2 v_ref.1.2)) = Some (texpr, false)) /\ (Qin (Sfcnct r0 (Eref r1)) ss)) \/
  (exists r0 e0 v_ref el, base_ref r0 tmap = Some v_ref -> split_expr_connect e0 v_ref.2 = Some el -> 
                 (v_ref.1.1 = v.1) /\ (List.nth_error el (N.to_nat (N.sub v.2 v_ref.1.2)) = Some texpr) /\ (Qin (Sfcnct r0 e0) ss))).
  *) (* ??报错 *)

Admitted.

Theorem InferWidths_correct' :
  forall (F : HiFP.hfmodule) (vm' : module_graph_vertex_set_p.env) (ct : module_graph_connection_trees_p.env),
    match InferWidths_m F with
    | Some F' => Sem F' vm' ct -> Sem F (make_vm_implicit F vm') ct
    | _ => True
    end.
Proof.
  assert (Sem F' vm' ct -> Sem_frag_stmts' vm' ss tmap).
  assert (Sem_frag_stmts' vm' ss tmap -> InferWidths_fun inferorder var2exprs tmap = Some newtm -> Sem_frag_stmts' vm' ss' tmap).
  assert (Sem F' vm' ct -> Sem_frag_stmts' vm' ss' tmap -> Sem F (make_vm_implicit F vm') ct).
