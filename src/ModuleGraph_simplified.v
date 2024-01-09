From Coq Require Import ZArith (* for Nat.eq_dec *).
From simplssrlib Require Import SsrOrder FMaps Var ZAriths.
From nbits Require Import NBits.
From firrtl Require Import Env Firrtl HiEnv HiFirrtl. (* for hfmodule and its parts *)
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq fintype.

(* This file contains a simpler version of module graphs as a semantic structure for FIRRTL modules.
   The idea is to have vertices that correspond to ground-type components
   (mainly registers, wires, ports, nodes) in the graph,
   but instead of edges have expressions. *)

(* Type of vertices of a module graph *)

Inductive vertex_type :=
   (* what kind of vertices can be in the module graph *)
   OutPort : fgtyp (* within the module there is only an input
                                (the output goes to some place outside the module) *) -> vertex_type |
   InPort : fgtyp -> vertex_type | (* main module only at present *)
   (* register, wire etc. *)
   Register : fgtyp -> vertex_type | (* Register that is not reset *)
   RegisterReset : fgtyp -> bool -> vertex_type | (* Register with reset input. The boolean is true if it is Fasyncreset. *)
   Wire : fgtyp -> vertex_type |
   (*memory : ?
   inst : ?*)
   Node : fgtyp -> vertex_type.

(* equality of vertex_type is decidable *)
Lemma vertex_type_eq_dec : forall {x y : vertex_type}, {x = y} + {x <> y}.
Proof.  decide equality ; try apply fgtyp_eq_dec ; decide equality.  Qed.

Definition vertex_type_eqn (x y : vertex_type) : bool :=
match x, y with
| OutPort i, OutPort j
| InPort i, InPort j => i == j
(*| Reference a, Reference b*)
| Register a, Register b
| Wire a, Wire b
(*memory : ?
inst : ?*)
| Node a, Node b => a == b
| RegisterReset a r1, RegisterReset b r2 => (a == b) && (r1 == r2)
| _, _ => false
end.
Lemma vertex_type_eqP : Equality.axiom vertex_type_eqn.
Proof.
rewrite /Equality.axiom ; intros.
case: (@vertex_type_eq_dec x y) => H.
* rewrite H /vertex_type_eqn ; clear -y.
  destruct y ; rewrite eq_refl ; try rewrite eq_refl andTb ; apply ReflectT ; reflexivity.
* rewrite /vertex_type_eqn.
  destruct x, y ; try contradiction ; try (apply ReflectF ; exact H).
  + 4:
    destruct (b == b0) eqn: Hb ;
    try (rewrite andFb ; apply ReflectF ; exact H) ;
    move /eqP : Hb => Hb ; try rewrite Hb andbT ;
    try (rewrite andbF ; apply ReflectF ; injection ; intros ; done) ;
    rewrite Hb in H ; clear Hb.
  + all:
    assert (f <> f0) by (contradict H ; rewrite H ; reflexivity) ;
    move /eqP : H0 => H0 ; apply negbTE in H0 ;
    rewrite H0 ; apply ReflectF ; exact H.
Qed.
Canonical vertex_type_eqMixin := EqMixin vertex_type_eqP.
Canonical vertex_type_eqType := Eval hnf in EqType vertex_type vertex_type_eqMixin.

(* Some abbreviations for explicit-width data types *)

Definition Fsint_exp (w : nat) : fgtyp_explicit :=
   (* convert Fsint w to an fgtyp_explicit *)
   exist not_implicit_width (Fsint w) I.

Definition Fuint_exp (w : nat) : fgtyp_explicit :=
   (* convert Fuint w to an output data type *)
   exist not_implicit_width (Fuint w) I.

Definition Fclock_exp : fgtyp_explicit :=
   (* convert Fclock to an explicit-width data type *)
   exist not_implicit_width Fclock I.

Definition Fasyncreset_exp : fgtyp_explicit :=
   (* convert Fasyncreset to an explicit-width data type *)
   exist not_implicit_width Fasyncreset I.

(* Input and output connectors of vertices *)

Definition  input_connectors (v : vertex_type) : seq fgtyp :=
   (* calculates the list of data types of input connectors of a vertex.
      It should be a list because the function of different input connectors can be different
      (for example with the multiplexer). *)
   match v with
   | OutPort it => [:: it]
   | InPort _ => [::] (* An InPort has no input connector because the data comes from somewhere outside the module *)
   | Register it => [:: it; Fclock]
   | RegisterReset it true => [:: it; Fclock; Fasyncreset; it]
   | RegisterReset it false => [:: it; Fclock; Fuint 1; it]
   | Wire it
   (*
   reference it
   memory : ?
   inst : ? *)
   | Node it => [:: it]
   end.

Definition output_connectors (v : vertex_type) : seq fgtyp :=
(* a list of types of the output connectors of a vertex of type v. *)
   match v with
   | OutPort _ => [::] (* An OutPort has no output connector because the data is sent to somewhere outside the module *)
   | InPort it
   | Register it
   | RegisterReset it _
   | Wire it
   | Node it => [:: it]
   (*
   reference it
   memory : ?
   inst : ? *)
   end.

(* vertex set of a module graph (using pairs of natural numbers as keys) *)

Module MakeVtypFMap (V : SsrOrder) (VM : SsrFMapWithNew with Module SE := V)
<: SsrFMapWithNew with Module SE := V.
  Include VM.
  Include FMapLemmas VM.
  Definition env : Type := t vertex_type.
End MakeVtypFMap.

Module ProdVarOrder := MakeProdOrderWithDefaultSucc VarOrder VarOrder.
Module PVM <: SsrFMapWithNew := FMaps.MakeTreeMapWithNew ProdVarOrder.
Module module_graph_vertex_set_p <: SsrFMapWithNew := MakeVtypFMap ProdVarOrder PVM.

(* connections of a module graph:
   For every input connector of a module graph, there should be an associated expression.
   The expressions are based on the vertices in the module graph.
   Input connectors are identified by a triple of natural numbers:
   - a pair to identify the vertex of the module graph
   - a number to identify the input connector of the vertex.
   Actually we need a little more than an expression:
   we should be able to distinguish unconnected / invalidated / connected input ports. *)

Inductive def_expr : Type :=
  | D_undefined (* declared but not connected, no "is invalid" statement *)
  | D_invalidated (* declared but not connected, there is a "is invalid" statement *)
  | D_fexpr : HiFP.hfexpr -> def_expr (* declared and connected *)
  .

(* equality of def_expr is decidable [because equality of hfexpr is decidable] *)
Lemma def_expr_eq_dec : forall {x y : def_expr}, {x = y} + {x <> y}.
  Proof.
  decide equality.
  apply hfexpr_eq_dec.
Qed.

Definition def_expr_eqn (x y : def_expr) : bool :=
  match x, y with
  | D_undefined, D_undefined => true
  | D_invalidated, D_invalidated => true
  | D_fexpr expr1, D_fexpr expr2 => expr1 == expr2
  | _, _ => false
  end.

Lemma def_expr_eqP : Equality.axiom def_expr_eqn.
Proof.
  unfold Equality.axiom, def_expr_eqn.
  intros ; induction x, y ; try (apply ReflectF ; discriminate) ; try (apply ReflectT ; reflexivity).
  case Eq: (h == h0).
  all: move /hfexpr_eqP : Eq => Eq.
  apply ReflectT ; replace h0 with h ; reflexivity.
  apply ReflectF ; injection ; apply Eq.
Qed.

Canonical def_expr_eqMixin := EqMixin def_expr_eqP.
Canonical def_expr_eqType := Eval hnf in EqType def_expr def_expr_eqMixin.


(* for connection_tree, whose key is (N_pair, N) as input_connector_id
   here this module produce ProdOrder like ((N,N),N) *)
Module MakeProdOrderWithDefaultSucc2 (O1 O2 : SsrOrderWithDefaultSucc) <: SsrOrderWithDefaultSucc
    with Definition T := prod_eqType O1.T O2.T.
  Module M := MakeProdOrderMinimal O1 O2.
  Module P := MakeSsrOrder M.
  Include P.
  Definition default : t := (O1.default, O2.default).
  Definition succ (x : t) : t := (fst x, O2.succ (snd x)). (* succ of pair ((a,b),c) is ((a,b),c+1) *)
  Lemma ltn_succ (x : t) : ltn x (succ x).
  Proof.
    case: x => x y. rewrite /ltn /succ /=. rewrite /M.ltn /=.
    rewrite O2.ltn_succ andbT eqtype.eq_refl orbT //.
  Qed.
End MakeProdOrderWithDefaultSucc2.

(* can be identifier of a input/output_connector *)
Module PProdVarOrder := MakeProdOrderWithDefaultSucc2 ProdVarOrder VarOrder.

Module MakeCnctFMap (V : SsrOrder) (VM : SsrFMapWithNew with Module SE := V)
<: SsrFMapWithNew with Module SE := V.
  Include VM.
  Include FMapLemmas VM.
  Definition env : Type := t def_expr.
End MakeCnctFMap.

Module PPVM <: SsrFMapWithNew := FMaps.MakeTreeMapWithNew PProdVarOrder.
Module module_graph_connection_trees_p <: SsrFMapWithNew := MakeCnctFMap PProdVarOrder PPVM.

(* Semantics.
   In a module graph, identifiers of vertices are pairs of natural numbers.
   These numbers come from Sreg, Swire etc. statements.
   The pair satisfies this condition:
   if the type of the vertex is aggregate, then the pair has the form (v, 0);
   also, there is no other identifier used in the module of the form (v, w) (for any number w). *)

(* type of a tmap, which records the aggr_type for each element *)
Definition ft_pmap := (N*N) -> (option ftype).
Definition ft_find (v : N*N) (m : ft_pmap) := m v.
Definition ft_add (v : N*N) (ft : ftype) (m : ft_pmap) : ft_pmap :=
   fun (y : N*N) => if y == v then (Some ft) else (ft_find y m).
Definition ft_mem (v : N*N) (m : ft_pmap) : bool := if (m v == None) then false else true.
Definition ft_empty : ft_pmap := (fun _ => None).

Fixpoint select_field (f : VarOrder.t) (l : seq PProdVarOrder.t) (ff : ffield) : option (seq PProdVarOrder.t * ftype) :=
(* select field f from the list of input connectors l, which corresponds to type ff.
   ff does not need to be passive, but its direction is ignored.
   Return the corresponding output connectors, and also return the type of the field f. *)
match ff with
| Fflips v _ ft ff' =>
    let elsize := size_of_ftype ft in
    if size l < elsize then None
    else if f == v then Some (take elsize l, ft)
         else select_field f (drop elsize l) ff'
| _ => None
end.

Fixpoint list_lhs_ref_p (ref : HiFP.href) (tmap : ft_pmap) : option (seq PProdVarOrder.t * ftype) :=
(* find which input connectors of ground-type identifiers correspond to reference ref.
   ground-type identifiers are vertices in the module graph (identified by a pair of N);
   output connectors are always the triple (vertex identifier, N0).
   Also find the type of expression e. *)
match ref with
| Eid v =>
    (* Construct a list of identifiers and find the type of v *)
    match tmap v with
    | Some (Gtyp gt) => Some ([:: (v, N0)], Gtyp gt)
    | Some t =>
        if snd v == N0
        then Some (mkseq (fun i => (fst v, N.of_nat (i + 1), N0)) (size_of_ftype t), t)
        else None
    | None => None
    end
| Esubfield ref' f =>
    match list_lhs_ref_p ref' tmap with
    | Some (l, Btyp ff) =>
        (* Select from list l the relevant part for field f.
           Determine which part this is based on t *)
        select_field f l ff
    | _ => None
    end
| Esubindex ref' n =>
    match list_lhs_ref_p ref' tmap with
    | Some (l, Atyp t m) =>
        (* Select from list l the relevant part for array element n.
           Determine which part this is based on t *)
        let elsize := size_of_ftype t in
        if (n < m) && (size l == m * elsize)
        then Some (take elsize (drop (n * elsize) l), t)
        else None
    | _ => None
    end
| Esubaccess _ _ => None
end.

(* Semantics: *)

Definition connect_non_passive_fgtyp (ct_old : module_graph_connection_trees_p.env)
                                     (_ : HiFP.href) (lst_tgt : list PProdVarOrder.t) (gt_tgt : fgtyp)
                                     (ref_src : HiFP.href) (lst_src : list PProdVarOrder.t) (gt_src : fgtyp)
                                     (ct_new : module_graph_connection_trees_p.env) : bool :=
(* The predicate checks whether ct_new contains the correct connection that connects from lst_src to lst_tgt,
   and it does not change the connection into lst_src.
   These lists must be one-element lists for output and input connectors of compatible types. *)
      match lst_tgt, lst_src with
      | [:: ic], [:: oc] =>    (module_graph_connection_trees_p.find ic ct_new == Some (D_fexpr (Eref ref_src)))
                            &&
                               (module_graph_connection_trees_p.find oc ct_new == module_graph_connection_trees_p.find oc ct_old)
                               (* why this is compared?
                                  In Sem_frag_stmt, it is ensured that connection trees NOT related to tgt or src are not changed.
                                  Here, we need to ensure that the connection tree of tgt is changed
                                  and the connection tree of src remains the same. *)
      | _, _ => false
      end
   &&
      match gt_tgt, gt_src with
      | Fuint _, Fuint _
      | Fuint _, Fuint_implicit _
      | Fsint _, Fsint _
      | Fsint _, Fsint_implicit _
      | Fclock, Fclock
      | Fasyncreset, Fasyncreset => true
      | Fuint_implicit wt, Fuint ws
      | Fuint_implicit wt, Fuint_implicit ws
      | Fsint_implicit wt, Fsint ws
      | Fsint_implicit wt, Fsint_implicit ws => wt >= ws
      | _, _ => false
      end.

Fixpoint connect_non_passive (ct_old : module_graph_connection_trees_p.env)
                             (ref_tgt : HiFP.href) (lst_tgt : list PProdVarOrder.t) (ft_tgt : ftype)
                             (ref_src : HiFP.href) (lst_src : list PProdVarOrder.t) (ft_src : ftype)
                             (ct_new : module_graph_connection_trees_p.env) : bool :=
   (* The predicate returns true if the correct connection trees are in ct_new
      that connect from lst_src to lst_tgt, and that the connection trees that
      connect to lst_src are not changed.  Other connection trees are not checked.
      The type of lst_tgt is ft_tgt, and the type of lst_src is ft_src.
      These references are *not* required to have passive types.

      We copy the same code two times, to allow Coq to prove that the recursion is well-founded. *)
   match ft_tgt, ft_src with
   | Gtyp gt_tgt, Gtyp gt_src => connect_non_passive_fgtyp ct_old ref_tgt lst_tgt gt_tgt ref_src lst_src gt_src ct_new
   | Atyp elt_tgt n1, Atyp elt_src n2 => (n1 == n2) &&
      let type_len := size_of_ftype elt_tgt in
            (size lst_tgt == type_len * n1) && (size lst_src == type_len * n1)
         &&
            [forall n : ordinal n1,
               connect_non_passive ct_old
                                   (Esubindex ref_tgt n) (take type_len (drop (n * type_len) lst_tgt)) elt_tgt
                                   (Esubindex ref_src n) (take type_len (drop (n * type_len) lst_src)) elt_src
                                   ct_new]
   | Btyp ff_tgt, Btyp ff_src => connect_non_passive_fields ct_old ref_tgt lst_tgt ff_tgt ref_src lst_src ff_src ct_new
   | _, _ => false
   end
with connect_non_passive_fields (ct_old : module_graph_connection_trees_p.env)
                                (ref_tgt : HiFP.href) (lst_tgt : list PProdVarOrder.t) (ft_tgt : ffield)
                                (ref_src : HiFP.href) (lst_src : list PProdVarOrder.t) (ft_src : ffield)
                                (ct_new : module_graph_connection_trees_p.env) : bool :=
   (* The predicate returns true if the correct connection trees are in ct_new
      that connect from lst_src to lst_tgt, and that the connection trees that
      connect to lst_src are not changed.  Other connection trees are not checked.
      The type of lst_tgt is (Btyp ft_tgt), and the type of lst_src is (Btyp ft_src).
      These references are *not* required to have passive types.

      We copy the same code two times, to allow Coq to prove that the recursion is well-founded. *)
   match ft_tgt, ft_src with
   | Fnil, Fnil => true
   | Fflips v1 Nflip gtt ft, Fflips v2 Nflip gts fs => (v1 == v2) &&
         let type_len := size_of_ftype gtt in
               connect_non_passive ct_old (Esubfield ref_tgt v1) (take type_len lst_tgt) gtt (Esubfield ref_src v2) (take type_len lst_src) gts ct_new
            &&
               connect_non_passive_fields ct_old ref_tgt (drop type_len lst_tgt) ft ref_src (drop type_len lst_src) fs ct_new
   | Fflips v1 Flipped gtt ft, Fflips v2 Flipped gts fs => (v1 == v2) &&
         let type_len := size_of_ftype gts in
               connect_non_passive_flipped ct_old (Esubfield ref_src v2) (take type_len lst_src) gts (Esubfield ref_tgt v1) (take type_len lst_tgt) gtt ct_new
            &&
               connect_non_passive_fields ct_old ref_tgt (drop type_len lst_tgt) ft ref_src (drop type_len lst_src) fs ct_new
   | _, _ => false
   end
with connect_non_passive_flipped (ct_old : module_graph_connection_trees_p.env)
                                 (ref_tgt : HiFP.href) (lst_tgt : list PProdVarOrder.t) (ft_tgt : ftype)
                                 (ref_src : HiFP.href) (lst_src : list PProdVarOrder.t) (ft_src : ftype)
                                 (ct_new : module_graph_connection_trees_p.env) : bool :=
   (* The code in this predicate is the same as in connect_non_passive. *)
   match ft_tgt, ft_src with
   | Gtyp gt_tgt, Gtyp gt_src => connect_non_passive_fgtyp ct_old ref_tgt lst_tgt gt_tgt ref_src lst_src gt_src ct_new
   | Atyp elt_tgt n1, Atyp elt_src n2 => (n1 == n2) &&
      let type_len := size_of_ftype elt_tgt in
            (size lst_tgt == type_len * n1) && (size lst_src == type_len * n1)
         &&
            [forall n : ordinal n1,
               connect_non_passive_flipped ct_old
                                           (Esubindex ref_tgt n) (take type_len (drop (n * type_len) lst_tgt)) elt_tgt
                                           (Esubindex ref_src n) (take type_len (drop (n * type_len) lst_src)) elt_src
                                           ct_new]

   | Btyp ff_tgt, Btyp ff_src => connect_non_passive_fields_flipped ct_old ref_tgt lst_tgt ff_tgt ref_src lst_src ff_src ct_new
   | _, _ => false
   end
with connect_non_passive_fields_flipped (ct_old : module_graph_connection_trees_p.env)
                                        (ref_tgt : HiFP.href) (lst_tgt : list PProdVarOrder.t) (ft_tgt : ffield)
                                        (ref_src : HiFP.href) (lst_src : list PProdVarOrder.t) (ft_src : ffield)
                                        (ct_new : module_graph_connection_trees_p.env) : bool :=
   (* The code in this predicate is the same as in connect_non_passive_fields. *)
   match ft_tgt, ft_src with
   | Fnil, Fnil => true
   | Fflips v1 Nflip gtt ft, Fflips v2 Nflip gts fs => (v1 == v2) &&
         let type_len := size_of_ftype gtt in
               connect_non_passive_flipped ct_old (Esubfield ref_tgt v1) (take type_len lst_tgt) gtt (Esubfield ref_src v2) (take type_len lst_src) gts ct_new
            &&
               connect_non_passive_fields_flipped ct_old ref_tgt (drop type_len lst_tgt) ft ref_src (drop type_len lst_src) fs ct_new
   | Fflips v1 Flipped gtt ft, Fflips v2 Flipped gts fs => (v1 == v2) &&
         let type_len := size_of_ftype gts in
               connect_non_passive ct_old (Esubfield ref_src v2) (take type_len lst_src) gts (Esubfield ref_tgt v1) (take type_len lst_tgt) gtt ct_new
            &&
               connect_non_passive_fields_flipped ct_old ref_tgt (drop type_len lst_tgt) ft ref_src (drop type_len lst_src) fs ct_new
   | _, _ => false
   end.

Fixpoint connect_type_compatible (ft_ref : ftype) (ft_expr : ftype_explicit) : bool :=
(* returns true iff a signal of type ft_expr can be connected to ft_ref.
   It also ensures that the types are passive. *)
   match ft_ref, ft_expr with
   | Gtyp (Fuint _), exist (Gtyp (Fuint _)) _
   | Gtyp (Fsint _), exist (Gtyp (Fsint _)) _
   | Gtyp Fclock, exist (Gtyp Fclock) _
   | Gtyp Fasyncreset, exist (Gtyp Fasyncreset) _ => true
   | Gtyp (Fuint_implicit w_ref), exist (Gtyp (Fuint w_expr)) _
   | Gtyp (Fsint_implicit w_ref), exist (Gtyp (Fsint w_expr)) _ => w_ref >= w_expr
   | Atyp t_ref n_ref, exist (Atyp t_expr n_expr) p => connect_type_compatible t_ref (exist ftype_not_implicit_width t_expr p) && (n_ref == n_expr)
   | Btyp ff_ref, exist (Btyp ff_expr) p => connect_type_compatible_fields ff_ref (exist ffield_not_implicit_width ff_expr p)
   | _, _ => false
   end
with connect_type_compatible_fields (ff_ref : ffield) (ff_expr : ffield_explicit) : bool :=
   match ff_ref, ff_expr with
   | Fnil, exist Fnil _ => true
   | Fflips v_ref Nflip t_ref ff_ref', exist (Fflips v_expr Nflip t_expr ff_expr') p =>
          (v_ref == v_expr) && connect_type_compatible t_ref (exist ftype_not_implicit_width t_expr (proj1 p))
                            && connect_type_compatible_fields ff_ref' (exist ffield_not_implicit_width ff_expr' (proj2 p))
   | _, _ => false
   end.

Fixpoint list_rhs_ref_p (ref : HiFP.href) (ft : ftype) : option (seq HiFP.hfexpr) :=
(* Finds expressions for the ground-type components of the reference ref, which is of type ft.
   ft must be a passive type. *)
match ft with
| Gtyp _ => Some [:: Eref ref]
| Atyp t n =>
    iteri n (fun (i : nat) (ol : option (seq HiFP.hfexpr)) =>
                 match ol, list_rhs_ref_p (Esubindex ref i) t with
                 | Some l, Some li => Some (l ++ li)
                 | _, _ => None
                 end)
          (Some [::])
| Btyp ff => list_rhs_ref_p_fields ref ff
end
with list_rhs_ref_p_fields (ref : HiFP.href) (ff : ffield) : option (seq HiFP.hfexpr) :=
match ff with
| Fnil => Some [::]
| Fflips v Nflip t ff' =>
    match list_rhs_ref_p (Esubfield ref v) t, list_rhs_ref_p_fields ref ff' with
    | Some l1, Some l2 => Some (l1 ++ l2)
    | _, _ => None
    end
| Fflips _ Flipped _ _ => None
end.

Fixpoint list_rhs_expr_p (expr : HiFP.hfexpr) (ft : ftype) : option (seq HiFP.hfexpr) :=
(* Finds ground-type components of the expression expr, which is of type ft.
   Does not do type checking but just assumes that expr has type ft.
   If the type is not a ground type, then the expression must be either a reference or a multiplexer. *)
if ft is Gtyp _ then Some [:: expr]
else match expr with
     | Emux c e1 e2 =>
         match list_rhs_expr_p e1 ft, list_rhs_expr_p e2 ft with
         | Some l1, Some l2 =>
             if size l1 == size l2
             then Some (map (fun (e12 : HiFP.hfexpr * HiFP.hfexpr) => Emux c (fst e12) (snd e12)) (zip l1 l2))
             else None
         | _, _ => None
         end
   (*| Evalidif c e =>
         match list_rhs_expr_p e ft with
         | Some l =>
             Some (map (fun (ee : HiFP.hfexpr) => Evalidif c ee) l)
         | None => None
         end*)
     | Eref ref => list_rhs_ref_p ref ft
     | _ => None
     end.

Fixpoint list_rhs_type_p (ft : ftype) : seq fgtyp :=
(* Finds the types of ground-type components of type ft.
   (In contrast to the older function vtype_list, this function does not convert Freset to
   Fuint 1 or Fasyncreset.) *)
match ft with
| Gtyp gt => [:: gt]
| Atyp ft' m => let elt_list := list_rhs_type_p ft' in
                (* append m copies of elt_list to the empty list: *)
                iter m (fun (ll : seq fgtyp) => ll ++ elt_list) [::]
| Btyp ff => list_rhs_ffield_p ff
end
with list_rhs_ffield_p (ff : ffield) : seq fgtyp :=
match ff with
| Fnil => [::]
| Fflips _ _ ft' ff' => (list_rhs_type_p ft') ++ (list_rhs_ffield_p ff')
end.

(* Find the type of different kinds of expressions: *)

Fixpoint type_of_ffield (v : VarOrder.t) (ff : ffield) : option ftype :=
(* Find the type of field v in bundle type (Btyp ff). *)
match ff with
| Fnil => None
| Fflips v0 _ t ff' => if v == v0 then Some t else type_of_ffield v ff'
end.

Fixpoint type_of_ref (ref : HiFP.href) (tmap : ft_pmap) : option ftype :=
(* Find the type of reference ref, using the type information from tmap. *)
match ref with
| Eid v => ft_find v tmap
| Esubindex ref' n =>
    match type_of_ref ref' tmap with
    | Some (Atyp t m) => if n < m then Some t else None
    | _ => None
    end
| Esubfield ref' v =>
    match type_of_ref ref' tmap with
    | Some (Btyp ff) => type_of_ffield v ff
    | _ => None
    end
| Esubaccess _ _ => None
end.

Definition tmap_subset (t1 t2: ft_pmap) : Prop :=
forall v : ProdVarOrder.T,
   match ft_find v t1 with
   | Some ft => ft_find v t2 = Some ft
   | None => True
   end.

Lemma tmap_subset_refl : forall tmap : ft_pmap, tmap_subset tmap tmap.
Proof.
unfold tmap_subset ; intros.
destruct (ft_find v tmap) ; done.
Qed.

Lemma tmap_subset_trans : forall t2 t1 t3 : ft_pmap, tmap_subset t1 t2 -> tmap_subset t2 t3 -> tmap_subset t1 t3.
Proof.
unfold tmap_subset ; intros.
specialize H with (v := v) ; specialize H0 with (v := v).
destruct (ft_find v t1) ; last by trivial.
rewrite H in H0.
exact H0.
Qed.

Lemma tmap_subset_add : forall (tmap : ft_pmap) (v : N * N) (t : ftype),
   ft_find v tmap = None -> tmap_subset tmap (ft_add v t tmap).
Proof.
unfold ft_add, tmap_subset, ft_find at 3.
intros.
destruct (v0 == v) eqn: Hv ; rewrite Hv.
* move /eqP : Hv => Hv ; rewrite Hv H //.
* destruct (ft_find v0 tmap) ; by done.
Qed.

Lemma tmap_subset_add_add : forall (tmap1 tmap2 : ft_pmap) (v : N * N) (t : ftype),
   tmap_subset tmap1 tmap2 -> tmap_subset (ft_add v t tmap1) (ft_add v t tmap2).
Proof.
unfold ft_add, tmap_subset, ft_find at 3 5.
intros.
specialize H with (v := v0).
destruct (ft_find v0 tmap1) ; simpl.
* rewrite H.
  destruct (if v0 == v then Some t else Some f) eqn: H0 ; rewrite H0 ; done.
* destruct (v0 == v) eqn: H0 ; rewrite H0 ; done.
Qed.

Lemma type_of_ref_subset : forall (ref : HiFP.href) (tmap1 tmap2 : ft_pmap),
   tmap_subset tmap1 tmap2 ->
   match type_of_ref ref tmap1 with
   | Some ft => type_of_ref ref tmap2 = Some ft
   | None => True
   end.
Proof.
intros.
induction ref ; simpl ; try trivial.
* by apply H.
* destruct (type_of_ref ref tmap1) ; last by trivial.
  rewrite IHref.
  destruct f ; first (by trivial) ; first by trivial.
  destruct (type_of_ffield v f) ; last by trivial.
  by reflexivity.
* destruct (type_of_ref ref tmap1) ; last by trivial.
  rewrite IHref.
  destruct f ; first (by trivial) ; last by trivial.
  destruct (n < n0) ; last by trivial.
  by reflexivity.
Qed.

Definition fgtyp_mux (x y : fgtyp_explicit) : option fgtyp_explicit :=
(* Find the type of a multiplexer whose two inputs have types x and y, for ground types *)
    match x, y with
    | exist (Fuint wx) _, exist (Fuint wy) _ => Some (Fuint_exp (Nat.max wx wy))
    | exist (Fsint wx) _, exist (Fsint wy) _ => Some (Fsint_exp (Nat.max wx wy))
    | exist Fclock _, exist Fclock _ => Some Fclock_exp
  (*| exist Freset _, exist Freset _ => Some Freset_exp*)
    | exist Fasyncreset _, exist Fasyncreset _ => Some Fasyncreset_exp
    | _, _ => None
    end.

Fixpoint ftype_mux' (x : ftype) (px : ftype_not_implicit_width x) (y : ftype) (py : ftype_not_implicit_width y) : option ftype_explicit :=
(* Find the type of a multiplexer whose two inputs have types x and y, for ground types.
   The function needs to take apart the ftype_explicit so Coq can guess the decreasing argument *)
  match x, px, y, py with
  | Gtyp tx, px, Gtyp ty, py =>
       match fgtyp_mux (exist not_implicit_width tx px) (exist not_implicit_width ty py) with
       | Some (exist fgt p) => Some (exist ftype_not_implicit_width (Gtyp fgt) p)
       | None => None
       end
  | Atyp tx nx, px, Atyp ty ny, py =>
       if (nx == ny) then match ftype_mux' tx px ty py with
                          | Some (exist fat p) => Some (exist ftype_not_implicit_width (Atyp fat nx) p)
                          | None => None
                          end
                     else None
  | Btyp fx, px, Btyp fy, py => ffield_mux' fx px fy py
  | _, _, _, _ => None
  end
with ffield_mux' (f1 : ffield) (p1 : ffield_not_implicit_width f1) (f2 : ffield) (p2 : ffield_not_implicit_width f2) : option ftype_explicit :=
       match f1, p1, f2, p2 with
       | Fnil, _, Fnil, _ => Some (exist ftype_not_implicit_width (Btyp Fnil) I)
       | Fflips v1 Nflip t1 fs1, p1, Fflips v2 Nflip t2 fs2, p2
         => if v1 == v2 then
               match ftype_mux'  t1  (proj1 p1) t2  (proj1 p2),
                     ffield_mux' fs1 (proj2 p1) fs2 (proj2 p2) with
               | Some (exist ft pt), Some (exist (Btyp bf) pf) =>
                   Some (exist ftype_not_implicit_width (Btyp (Fflips v1 Nflip ft bf)) (conj pt pf))
               | _, _ => None
               end
            else None
       | _, _, _, _ => None
       end.

Definition ftype_mux (x : ftype_explicit) (y : ftype_explicit) : option ftype_explicit :=
(* return the type of mux expression on ftypes *)
   ftype_mux' (proj1_sig x) (proj2_sig x) (proj1_sig y) (proj2_sig y).

Fixpoint type_of_expr (expr : HiFP.hfexpr) (tmap: ft_pmap) : option ftype_explicit :=
   (* Find the type of expression expr *)
   match expr with
   | Econst t bs => match t with
                    | Fuint_implicit w => Some (exist ftype_not_implicit_width (Gtyp (Fuint w)) I)
                    | Fsint_implicit w => Some (exist ftype_not_implicit_width (Gtyp (Fsint w)) I)
                    | t => Some (exist ftype_not_implicit_width (Gtyp t) I)
                    end
   | Eref r => match type_of_ref r tmap with
               | Some t => Some (make_ftype_explicit t)
               | _ => None
               end
   | Ecast AsUInt e1 => match type_of_expr e1 tmap with
                         | Some (exist (Gtyp (Fsint w)) _)
                         | Some (exist (Gtyp (Fuint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint w)) I)
                         | Some (exist (Gtyp Fclock) _)
                         | Some (exist (Gtyp Freset) _)
                         | Some (exist (Gtyp Fasyncreset) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint 1)) I)
                         | _ => None
                         end
   | Ecast AsSInt e1 => match type_of_expr e1 tmap with
                         | Some (exist (Gtyp (Fsint w)) _)
                         | Some (exist (Gtyp (Fuint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint w)) I)
                         | Some (exist (Gtyp Fclock) _)
                         | Some (exist (Gtyp Freset) _)
                         | Some (exist (Gtyp Fasyncreset) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint 1)) I)
                         | _ => None
                         end
   | Ecast AsClock e1 => match type_of_expr e1 tmap with
                         | Some (exist (Gtyp _) _) => Some (exist ftype_not_implicit_width (Gtyp Fclock) I)
                         | _ => None
                         end
   | Ecast AsAsync e1 => match type_of_expr e1 tmap with
                         | Some (exist (Gtyp _) _) => Some (exist ftype_not_implicit_width (Gtyp Fasyncreset) I)
                         | _ => None
                         end
   | Eprim_unop (Upad n) e1 => match type_of_expr e1 tmap with
                                | Some (exist (Gtyp (Fsint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint (maxn w n))) I)
                                | Some (exist (Gtyp (Fuint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint (maxn w n))) I)
                                | _ => None
                                end
   | Eprim_unop (Ushl n) e1 => match type_of_expr e1 tmap with
                                | Some (exist (Gtyp (Fsint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint (w + n))) I)
                                | Some (exist (Gtyp (Fuint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint (w + n))) I)
                                | _ => None
                                end
   | Eprim_unop (Ushr n) e1 => match type_of_expr e1 tmap with
                                | Some (exist (Gtyp (Fsint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint (maxn (w - n) 1))) I)
                                | Some (exist (Gtyp (Fuint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint (maxn (w - n) 1))) I)
                                | _ => None
                                end
   | Eprim_unop Ucvt e1 => match type_of_expr e1 tmap with
                            | Some (exist (Gtyp (Fsint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint w)) I)
                            | Some (exist (Gtyp (Fuint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint (w + 1))) I)
                            | _ => None
                            end
   | Eprim_unop Uneg e1 => match type_of_expr e1 tmap with
                            | Some (exist (Gtyp (Fsint w)) _)
                            | Some (exist (Gtyp (Fuint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint (w + 1))) I)
                            | _ => None
                            end
   | Eprim_unop Unot e1 => match type_of_expr e1 tmap with
                            | Some (exist (Gtyp (Fsint w)) _)
                            | Some (exist (Gtyp (Fuint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint w)) I)
                            | _ => None
                            end
   | Eprim_unop (Uextr n1 n2) e1 => match type_of_expr e1 tmap with
                                     | Some (exist (Gtyp (Fsint w)) _)
                                     | Some (exist (Gtyp (Fuint w)) _) =>
                                          if (n2 <= n1) && (n1 < w) then Some (exist ftype_not_implicit_width (Gtyp (Fuint (n1 - n2 + 1))) I)
                                                                    else None
                                     | _ => None
                                     end
   | Eprim_unop (Uhead n) e1 => match type_of_expr e1 tmap with
                                 | Some (exist (Gtyp (Fsint w)) _)
                                 | Some (exist (Gtyp (Fuint w)) _) =>
                                      if n <= w then Some (exist ftype_not_implicit_width (Gtyp (Fuint n)) I)
                                                else None
                                 | _ => None
                                 end
   | Eprim_unop (Utail n) e1 => match type_of_expr e1 tmap with
                                 | Some (exist (Gtyp (Fsint w)) _)
                                 | Some (exist (Gtyp (Fuint w)) _) =>
                                      if n <= w then Some (exist ftype_not_implicit_width (Gtyp (Fuint (w - n))) I)
                                                else None
                                 | _ => None
                                 end
   | Eprim_unop _ e1 => match type_of_expr e1 tmap with
                         | Some (exist (Gtyp (Fsint _)) _)
                         | Some (exist (Gtyp (Fuint _)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint 1)) I)
                         | _ => None
                         end
   | Eprim_binop (Bcomp _) e1 e2 => match type_of_expr e1 tmap, type_of_expr e2 tmap with
                                     | Some (exist (Gtyp (Fsint _)) _), Some (exist (Gtyp (Fsint _)) _)
                                     | Some (exist (Gtyp (Fuint _)) _), Some (exist (Gtyp (Fuint _)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint 1)) I)
                                     | _, _ => None
                                     end
   | Eprim_binop Badd e1 e2
   | Eprim_binop Bsub e1 e2 => match type_of_expr e1 tmap, type_of_expr e2 tmap with
                                | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint (maxn w1 w2 + 1))) I)
                                | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fsint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint (maxn w1 w2 + 1))) I)
                                | _, _ => None
                                end
   | Eprim_binop Bmul e1 e2 => match type_of_expr e1 tmap, type_of_expr e2 tmap with
                                | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint (w1 + w2))) I)
                                | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fsint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint (w1 + w2))) I)
                                | _, _ => None
                                end
   | Eprim_binop Bdiv e1 e2  => match type_of_expr e1 tmap, type_of_expr e2 tmap with
                                 | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint w1)) I)
                                 | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fsint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint (w1 + 1))) I)
                                 | _, _ => None
                                 end
   | Eprim_binop Brem e1 e2 => match type_of_expr e1 tmap, type_of_expr e2 tmap with
                                 | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint (minn w1 w2))) I)
                                 | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fsint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint (minn w1 w2))) I)
                                 | _, _ => None
                                 end
   | Eprim_binop Bdshl e1 e2 => match type_of_expr e1 tmap, type_of_expr e2 tmap with
                                 | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint (w1 + 2 ^ w2 - 1))) I)
                                 | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fuint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint (w1 + 2 ^ w2 - 1))) I)
                                 | _, _ => None
                                 end
   | Eprim_binop Bdshr e1 e2 => match type_of_expr e1 tmap, type_of_expr e2 tmap with
                                 | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint w1)) I)
                                 | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fuint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint w1)) I)
                                 | _, _ => None
                                 end
   | Eprim_binop Bcat e1 e2 => match type_of_expr e1 tmap, type_of_expr e2 tmap with
                                | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _)
                                | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fsint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint (w1 + w2))) I)
                                | _, _ => None
                                end
   | Eprim_binop Band e1 e2
   | Eprim_binop Bor e1 e2
   | Eprim_binop Bxor e1 e2 => match type_of_expr e1 tmap, type_of_expr e2 tmap with
                                | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _)
                                | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fsint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint (maxn w1 w2))) I)
                                | _, _ => None
                                end
   | Emux c e1 e2 => match type_of_expr c tmap, type_of_expr e1 tmap, type_of_expr e2 tmap with
                      | Some (exist (Gtyp (Fuint 1)) _), Some t1, Some t2 => ftype_mux t1 t2
                      | _, _, _ => None
                      end
   | Evalidif c e1 => match type_of_expr c tmap with
                      | Some (exist (Gtyp (Fuint 1)) _) => type_of_expr e1 tmap
                      | _ => None
                      end
   | _ => None (* Some (exist ftype_not_implicit_width (Gtyp (Fuint 0)) I) *)
   end.

Lemma type_of_expr_subset : forall (expr : HiFP.hfexpr) (tmap1 tmap2 : ft_pmap),
   tmap_subset tmap1 tmap2 ->
   match type_of_expr expr tmap1 with
   | Some ft => type_of_expr expr tmap2 = Some ft
   | None => True
   end.
Proof.
intros.
induction expr ; simpl ; try trivial.
* destruct f ; by reflexivity.
* destruct (type_of_expr expr tmap1) as [[ft p]|] ;
        last by destruct u ; trivial.
  rewrite IHexpr.
  destruct u ; try done ;
  destruct ft ; try done ;
  destruct f ; by done.
* destruct (type_of_expr expr tmap1) as [[ft p]|] ;
        last by destruct e ; trivial.
  rewrite IHexpr.
  destruct e ;
        destruct ft ; try done ;
        destruct f ; try done.
  - 1,2: destruct (n0 <= n < n1) ; by done.
  - 1,2,3,4: destruct (n <= n0) ; by done.
* destruct (type_of_expr expr1 tmap1) as [[ft1 p1]|] ;
        last by destruct e ; trivial.
  rewrite IHexpr1.
  destruct (type_of_expr expr2 tmap1) as [[ft2 p2]|] ;
        last by destruct e, ft1 ; try trivial ; destruct f ; trivial.
  rewrite IHexpr2.
  destruct e ;
        destruct ft1 ; try done ;
        destruct f ; try done ;
        destruct ft2 ; try done ;
        destruct f ; by done.
* destruct (type_of_expr expr1 tmap1) as [[ft1 p1]|] ;
        last by trivial.
  rewrite IHexpr1.
  destruct (type_of_expr expr2 tmap1) as [[ft2 p2]|] ;
        last by destruct ft1 ; trivial ; destruct f ; trivial ; destruct n ; trivial ; destruct n ; trivial.
  rewrite IHexpr2.
  destruct (type_of_expr expr3 tmap1) as [[ft3 p3]|] ;
        last by destruct ft1 ; trivial ; destruct f ; trivial ; destruct n ; trivial ; destruct n ; trivial.
  rewrite IHexpr3.
  destruct ft1 ; last (by trivial) ; last by trivial.
  destruct f ; try by trivial.
  destruct n ; first by trivial.
  destruct n ; last by trivial.
  destruct (ftype_mux
    (exist (fun ft : ftype => ftype_not_implicit_width ft) ft2 p2)
    (exist (fun ft : ftype => ftype_not_implicit_width ft) ft3 p3)) ; last by trivial.
  by reflexivity.
* destruct (type_of_expr expr1 tmap1) as [[ft1 p1]|] ;
        last by trivial.
  rewrite IHexpr1.
  destruct (type_of_expr expr2 tmap1) as [[ft2 p2]|] ;
        last by destruct ft1 ; trivial ; destruct f ; trivial ; destruct n ; trivial ; destruct n ; trivial.
  rewrite IHexpr2.
  destruct ft1 ; last (by trivial) ; last by trivial.
  destruct f ; try by trivial.
  destruct n ; first by trivial.
  destruct n ; last by trivial.
  by reflexivity.
* apply type_of_ref_subset with (ref := h) in H.
  destruct (type_of_ref h tmap1) ; try by trivial.
  rewrite H.
  by reflexivity.
Qed.

Definition vtype_equivalent (code_type : fgtyp) (graph_type : fgtyp) : bool :=
(* check whether types code_type and graph_type are equivalent.
   graph_type should be allowed in a module graph (i.e. it cannot be Freset). *)
match code_type, graph_type with
| Fuint w1, Fuint w2
| Fsint w1, Fsint w2 => w1 == w2
| Fuint_implicit _, Fuint_implicit _
| Fsint_implicit _, Fsint_implicit _
| Fclock, Fclock
| Freset, Fuint 1
| Freset, Fuint_implicit 1 (* should this really be included? It might break the property that widening of implicit types is always ok. *)
| Freset, Fasyncreset
| Fasyncreset, Fasyncreset => true
| _, _ => false
end.

Fixpoint vtype_find_widths (code_t : ftype) (v n : N) (vm : module_graph_vertex_set_p.env) : option (ftype * N) :=
(* find the widths of types used in vm for a component that was declared with type code_t in the code.
   That means, the module graph vertices should contain ground-type elements as given by vtype_equivalent.
   The result is a pair:
   - the type with widths adapted
   - the new index for n (where the next subcomponent would be found after handling code_t)
   If there is some error, the result is None instead.
   We allow non-passive types.
   Note that in most cases, the type of the output of the component is used,
   but for OutPorts we use the type of the input (because an out-port has no output connector). *)
match code_t with
| Gtyp oldgt =>
    match module_graph_vertex_set_p.find (v, n) vm with
    | Some (OutPort newgt)
    | Some (InPort newgt)
    | Some (Register newgt)
    | Some (RegisterReset newgt _)
    | Some (Wire newgt)
    | Some (Node newgt) =>
        if vtype_equivalent oldgt newgt
        then Some (Gtyp newgt, N.of_nat (n + 1))
        else None
    | None => None
    end
| Atyp code_t' m =>
    (* check the first copy, and then verify that the next m-1 copies have exactly the same types *)
    match vtype_find_widths code_t' v n vm with
    | Some (graph_t', new_n) =>
        (* Now check that there are another m-1 copies that are identical *)
        let t'_size := new_n - n in
        if [forall i : ordinal ((m-1) * t'_size),
               module_graph_vertex_set_p.find (v, N.of_nat (    n + i * t'_size)) vm ==
               module_graph_vertex_set_p.find (v, N.of_nat (new_n + i * t'_size)) vm   ]
        then Some (Atyp graph_t' m, N.of_nat (n + m * t'_size))
        else None
    | None => None
    end
| Btyp code_ff => vfields_find_widths code_ff v n vm
end
with vfields_find_widths (code_ff : ffield) (v n : N) (vm : module_graph_vertex_set_p.env) : option (ftype * N) :=
match code_ff with
| Fnil => Some (Btyp Fnil, n)
| Fflips f flp code_t code_ff' =>
    match vtype_find_widths code_t v n vm with
    | Some (graph_t, n') =>
        match vfields_find_widths code_ff' v n' vm with
        | Some (Btyp graph_ff, n'') =>
            Some (Btyp (Fflips f flp graph_t graph_ff), n'')
        | _ => None
        end
    | None => None
    end
end.

Fixpoint ftype_is_passive (ft : ftype) : bool :=
(* returns true if ft is a passive type *)
match ft with
| Gtyp _ => true
| Atyp ft' _ => ftype_is_passive ft'
| Btyp ff => ffield_is_passive ff
end
with ffield_is_passive (ff : ffield) : bool :=
match ff with
| Fnil => true
| Fflips _ Nflip ft' ff' => ftype_is_passive ft' && ffield_is_passive ff'
| Fflips _ Flipped _ _ => false
end.

Definition Swhen_map2_helper (cond : HiFP.hfexpr) (d_true d_false : option def_expr) : option def_expr :=
match d_true, d_false with
| Some (D_fexpr expr_true), Some (D_fexpr expr_false) =>
    if expr_true == expr_false then d_true
    else Some (D_fexpr (Emux cond expr_true expr_false))
| _, None
| _, Some D_invalidated
| Some D_undefined, _ => d_true
| None, _
| Some D_invalidated, _
| _, Some D_undefined => d_false
end.

Fixpoint Sem_frag_stmt (vm_old : module_graph_vertex_set_p.env) (ct_old : module_graph_connection_trees_p.env) (s : HiFP.hfstmt) (vm_new : module_graph_vertex_set_p.env) (ct_new : module_graph_connection_trees_p.env) (tmap : ft_pmap) : Prop :=
   (* The predicate returns True if vm_new/ct_new can be constructed from vm_old/ct_old by applying s.
   type checking, constraints *)
   match s with
   | Sskip => vm_old = vm_new /\ ct_old = ct_new
   | Sfcnct ref_tgt (Eref ref_src) => (* allow non-passive types *)
          module_graph_vertex_set_p.Equal vm_old vm_new
       /\
          match list_lhs_ref_p ref_tgt tmap, list_lhs_ref_p ref_src tmap with
          | Some (lst_tgt, ft_tgt), Some (lst_src, ft_src) =>
                 connect_non_passive ct_old ref_tgt lst_tgt ft_tgt ref_src lst_src ft_src ct_new
              /\
                 forall v0 : PProdVarOrder.T,
                    if (v0 \in lst_tgt) || (v0 \in lst_src) then True (* already checked in connect_non_passive *)
                    else module_graph_connection_trees_p.find v0 ct_old = module_graph_connection_trees_p.find v0 ct_new
          | _, _ => False
          end
   | Sfcnct ref expr =>
          module_graph_vertex_set_p.Equal vm_old vm_new
       /\
          match list_lhs_ref_p ref tmap, type_of_expr expr tmap with
          | Some (input_list, ft_ref), Some ft_expr =>
                 connect_type_compatible ft_ref ft_expr
              /\
                 match list_rhs_expr_p expr (proj1_sig ft_expr) with
                 | Some expr_list =>
                        (forall n : nat,
                             match List.nth_error input_list n, List.nth_error expr_list n with
                             | Some ic, Some ex => module_graph_connection_trees_p.find ic ct_new = Some (D_fexpr ex)
                             (* connect_type_compatible already checked that the lists have the same length.
                                There is no need to add a check here:
                             | Some _, None | None, Some _ => False *)
                             | _, _ => True
                             end)
                     /\
                        forall v0 : PProdVarOrder.T,
                            if v0 \in input_list then True
                            else module_graph_connection_trees_p.find v0 ct_old = module_graph_connection_trees_p.find v0 ct_new
                 | None => False
                 end
          | _, _ => False
          end
   | Sinvalid ref =>
          module_graph_vertex_set_p.Equal vm_old vm_new
       /\
          match list_lhs_ref_p ref tmap with
          | Some (input_list, ft_ref) =>
                 (forall n : nat,
                      match List.nth_error input_list n with
                      | Some ic => module_graph_connection_trees_p.find ic ct_new = Some D_invalidated
                      | None => True
                      end)
              /\
                 forall v0 : PProdVarOrder.T,
                     if v0 \in input_list then True
                     else module_graph_connection_trees_p.find v0 ct_old = module_graph_connection_trees_p.find v0 ct_new
          | _ => False
          end
   | Swire v t =>
       match t with
       | Gtyp oldgt => (* only v changes *)
           if module_graph_vertex_set_p.find v vm_new is Some (Wire newgt)
           then    module_graph_vertex_set_p.Equal (module_graph_vertex_set_p.add v (Wire newgt) vm_old) vm_new
                /\
                   module_graph_connection_trees_p.Equal (module_graph_connection_trees_p.add (v, N0) D_undefined ct_old) ct_new
                /\
                   vtype_equivalent oldgt newgt
           else False
       | _ => (* (fst v, N0), ... all have changed *)
           (* find the type of (fst v, N0), ..., (fst v, ...) based on t. *)
           if vtype_find_widths t (fst v) N0 vm_new is Some (newft, newft_size)
           then    (* ground-type wires are defined *)
                   (forall n : nat,
                        match List.nth_error (list_rhs_type_p newft) n with
                        | Some gt => module_graph_vertex_set_p.find (fst v, N.of_nat n) vm_new = Some (Wire gt)
                        | None => True
                        end)
                /\ (* other vertices do not change *)
                   (forall (v0 n0 : N), v0 <> fst v \/ n0 >= newft_size ->
                        module_graph_vertex_set_p.find (v0, n0) vm_old =
                        module_graph_vertex_set_p.find (v0, n0) vm_new)
                /\ (* other connections do not change *)
                   (forall (v0 n0 o0 : N), v0 <> fst v \/ n0 >= newft_size \/ o0 > 0 ->
                        module_graph_connection_trees_p.find (v0, n0, o0) ct_old =
                        module_graph_connection_trees_p.find (v0, n0, o0) ct_new)
                /\ (* set wires to undefined *)
                   forall n0 : N, n0 < newft_size ->
                       module_graph_connection_trees_p.find (fst v, n0, N0) ct_new = Some D_undefined
           else False
       end
   | Sreg v reg =>
       match type reg, module_graph_vertex_set_p.find v vm_new with
       | Gtyp oldgt, Some (Register newgt)
       | Gtyp oldgt, Some (RegisterReset newgt _) => (* ground-type register, only v changes *)
              match reset reg with
              | Rst rst_sig rst_val =>
                     (* type check rst_sig *)
                     match type_of_expr rst_sig tmap with
                     | Some (exist (Gtyp (Fuint 1)) _) =>
                         (* module graph contains register with synchronous reset *)
                         module_graph_vertex_set_p.Equal (module_graph_vertex_set_p.add v (RegisterReset newgt false) vm_old) vm_new
                     | Some (exist (Gtyp Fasyncreset) _) =>
                         (* module graph contains register with asynchronous reset *)
                         module_graph_vertex_set_p.Equal (module_graph_vertex_set_p.add v (RegisterReset newgt true) vm_old) vm_new
                     | _ => False
                     end
                  /\ (* connect rst_sig *)
                     module_graph_connection_trees_p.find (v, 2%num) ct_new = Some (D_fexpr rst_sig)
                  /\ (* type check rst_val *)
                     match type_of_expr rst_val tmap with
                     | Some rst_val_type => connect_type_compatible (Gtyp newgt) rst_val_type
                     | None => False
                     end
                  /\ (* connect rst_val *)
                     module_graph_connection_trees_p.find (v, 3%num) ct_new = Some (D_fexpr rst_val)
              | NRst =>
                     (* module graph contains register without reset *)
                     module_graph_vertex_set_p.Equal (module_graph_vertex_set_p.add v (Register newgt) vm_old) vm_new
                  /\ (* input connectors reserved for rst_sig and rst_val do not change *)
                     module_graph_connection_trees_p.find (v, 2%num) ct_old = module_graph_connection_trees_p.find (v, 2%num) ct_new
                  /\
                     module_graph_connection_trees_p.find (v, 3%num) ct_old = module_graph_connection_trees_p.find (v, 3%num) ct_new
              end
           /\ (* type check clock *)
              match type_of_expr (clock reg) tmap with
              | Some (exist (Gtyp Fclock) _) => True
              | _ => False
              end
           /\ (* connect clock *)
              module_graph_connection_trees_p.find (v, 1%num) ct_new = Some (D_fexpr (clock reg))
           /\ (* connect default value for register *)
              module_graph_connection_trees_p.find (v, N0) ct_new = Some (D_fexpr (Eref (Eid v)))
           /\ (* other connections do not change *)
              (forall (v0 : ProdVarOrder.T) (o0 : N), v0 <> v \/ o0 > 3 ->
                  module_graph_connection_trees_p.find (v0, o0) ct_old =
                  module_graph_connection_trees_p.find (v0, o0) ct_new)
           /\ (* type check newgt *)
              vtype_equivalent oldgt newgt
       | Gtyp _, _ => False (* module graph does not contain correct component *)
       | _, _ => (* aggregate-type register *)
           if vtype_find_widths (type reg) (fst v) N0 vm_new is Some (newft, newft_size)
           then    match reset reg with
                   | Rst rst_sig rst_val =>
                          (* type check rst_sig *)
                          match type_of_expr rst_sig tmap with
                          | Some (exist (Gtyp (Fuint 1)) _) =>
                              (* module graph contains ground-type registers with synchronous reset *)
                              forall n : nat,
                                  match List.nth_error (list_rhs_type_p newft) n with
                                  | Some gt => module_graph_vertex_set_p.find (fst v, N.of_nat n) vm_new = Some (RegisterReset gt false)
                                  | None => True
                                  end
                          | Some (exist (Gtyp Fasyncreset) _) =>
                              (* module graph contains ground-type registers with asynchronous reset *)
                              forall n : nat,
                                  match List.nth_error (list_rhs_type_p newft) n with
                                  | Some gt => module_graph_vertex_set_p.find (fst v, N.of_nat n) vm_new = Some (RegisterReset gt true)
                                  | None => True
                                  end
                          | _ => False
                          end
                       /\ (* connect rst_sig *)
                          (forall n0 : N, n0 < newft_size ->
                              module_graph_connection_trees_p.find (fst v, n0, 2%num) ct_new = Some (D_fexpr rst_sig))
                       /\ (* type check rst_val -- also ensures that newft is passive *)
                          match type_of_expr rst_val tmap with
                          | Some rst_val_type => connect_type_compatible newft rst_val_type
                          | None => False
                          end
                       /\ (* connect rst_val *)
                          match list_rhs_expr_p rst_val newft with
                          | Some expr_list =>
                              forall n : nat,
                                  match List.nth_error expr_list n with
                                  | Some ex => module_graph_connection_trees_p.find (fst v, N.of_nat n, 3%num) ct_new = Some (D_fexpr ex)
                                  | None => True
                                  end
                          | None => False
                          end
                   | NRst =>
                          (* module graph contains ground-type registers without reset *)
                          (forall n : nat,
                               match List.nth_error (list_rhs_type_p newft) n with
                               | Some gt => module_graph_vertex_set_p.find (fst v, N.of_nat n) vm_new = Some (Register gt)
                               | None => True
                               end)
                       /\ (* input connectors reserved for rst_sig and rst_val do not change *)
                          (forall n0 : N, n0 < newft_size ->
                                  module_graph_connection_trees_p.find (fst v, n0, 2%num) ct_old = module_graph_connection_trees_p.find (fst v, n0, 2%num) ct_new
                               /\
                                  module_graph_connection_trees_p.find (fst v, n0, 3%num) ct_old = module_graph_connection_trees_p.find (fst v, n0, 3%num) ct_new)
                       /\ (* type check newft: most has been done by vtype_find_widths, we only need to ensure newft is passive *)
                          ftype_is_passive newft
                   end
                /\ (* type check clock *)
                   match type_of_expr (clock reg) tmap with
                   | Some (exist (Gtyp Fclock) _) => True
                   | _ => False
                   end
                /\ (* connect clock *)
                   (forall n0 : N, n0 < newft_size ->
                       module_graph_connection_trees_p.find (fst v, n0, 1%num) ct_new = Some (D_fexpr (clock reg)))
                /\ (* connect default value for register *)
                   match list_rhs_expr_p (Eref (Eid v)) newft with
                   | Some expr_list =>
                       forall n : nat,
                           match List.nth_error expr_list n with
                           | Some ex => module_graph_connection_trees_p.find (fst v, N.of_nat n, N0) ct_new = Some (D_fexpr ex)
                           | None => True
                           end
                   | None => False
                   end
                /\ (* other vertices do not change *)
                   (forall (v0 n0 : N), v0 <> fst v \/ n0 >= newft_size ->
                       module_graph_vertex_set_p.find (v0, n0) vm_old =
                       module_graph_vertex_set_p.find (v0, n0) vm_new)
                /\ (* other connections do not change *)
                   (forall (v0 n0 o0 : N), v0 <> fst v \/ n0 >= newft_size \/ o0 > 3 ->
                       module_graph_connection_trees_p.find (v0, n0, o0) ct_old =
                       module_graph_connection_trees_p.find (v0, n0, o0) ct_new)
           else False
       end
   | Snode v expr =>
       match type_of_expr expr tmap with
       | Some (exist (Gtyp oldgt) _) => (* only v changes *)
           if module_graph_vertex_set_p.find v vm_new is Some (Node newgt)
           then    module_graph_vertex_set_p.Equal (module_graph_vertex_set_p.add v (Node newgt) vm_old) vm_new
                /\
                   module_graph_connection_trees_p.Equal (module_graph_connection_trees_p.add (v, N0) (D_fexpr expr) ct_old) ct_new
                /\
                   vtype_equivalent oldgt newgt
           else False
       | Some (exist newft _) => (* (fst v, N0), ... all have changed *)
              (* ground-type nodes are defined *)
              (forall n : nat,
                   match List.nth_error (list_rhs_type_p newft) n with
                   | Some gt => module_graph_vertex_set_p.find (fst v, N.of_nat n) vm_new = Some (Node gt)
                   | None => True
                   end)
           /\ (* other vertices do not change *)
              (forall (v0 n0 : N), v0 <> fst v \/ n0 >= size_of_ftype newft ->
                   module_graph_vertex_set_p.find (v0, n0) vm_old =
                   module_graph_vertex_set_p.find (v0, n0) vm_new)
           /\ (* other connections do not change *)
              (forall (v0 n0 o0 : N), v0 <> fst v \/ n0 >= size_of_ftype newft \/ o0 > 0 ->
                   module_graph_connection_trees_p.find (v0, n0, o0) ct_old =
                   module_graph_connection_trees_p.find (v0, n0, o0) ct_new)
           /\ (* set nodes to the respective part of the expression *)
              match list_rhs_expr_p expr newft with
              | Some expr_list =>
                  forall n : nat,
                      match List.nth_error expr_list n with
                      | Some ex => module_graph_connection_trees_p.find (fst v, N.of_nat n, N0) ct_new = Some (D_fexpr ex)
                      | None => True
                      end
              | None => False
              end
       | None => False
       end
   | Smem v mem => False (* ? *)
   | Sinst var1 var2 => False (* ? *)
   | Swhen cond ss_true ss_false =>
       if type_of_expr cond tmap is Some (exist (Gtyp (Fuint 1)) _)
       then exists (vm_true : module_graph_vertex_set_p.env) (ct_true ct_false : module_graph_connection_trees_p.env),
                   Sem_frag_stmts vm_old ct_old ss_true vm_true ct_true tmap
                /\
                   Sem_frag_stmts vm_true ct_old ss_false vm_new ct_false tmap
                /\
                   module_graph_connection_trees_p.Equal ct_new
                       (module_graph_connection_trees_p.map2 (Swhen_map2_helper cond) ct_true ct_false)
       else False
end
with Sem_frag_stmts (vm_old : module_graph_vertex_set_p.env) (ct_old : module_graph_connection_trees_p.env) (ss : HiFP.hfstmt_seq) (vm_new : module_graph_vertex_set_p.env) (ct_new : module_graph_connection_trees_p.env) (tmap : ft_pmap) : Prop :=
match ss with
| Qnil =>
       module_graph_vertex_set_p.Equal vm_old vm_new
    /\
       module_graph_connection_trees_p.Equal ct_old ct_new
| Qcons s ss' =>
    exists (vm' : module_graph_vertex_set_p.env) (ct' : module_graph_connection_trees_p.env),
           Sem_frag_stmt vm_old ct_old s vm' ct' tmap
        /\
           Sem_frag_stmts vm' ct' ss' vm_new ct_new tmap
end.

Definition Sem_frag_port (vm_old : module_graph_vertex_set_p.env) (ct_old : module_graph_connection_trees_p.env) (p : HiFP.hfport) (vm_new : module_graph_vertex_set_p.env) (ct_new : module_graph_connection_trees_p.env) : Prop :=
(* returns True if the port in p defines the components in vm *)
match p with
| Finput v t =>
    match t with
    | Gtyp ft =>
           module_graph_vertex_set_p.Equal (module_graph_vertex_set_p.add v (InPort ft) vm_old) vm_new
        /\
           module_graph_connection_trees_p.Equal ct_old ct_new
    | _ =>
        if vtype_find_widths t (fst v) N0 vm_new is Some (newft, newft_size)
        then    (* ground-type input ports are defined *)
                (forall n : nat,
                     match List.nth_error (list_rhs_type_p newft) n with
                     | Some gt => module_graph_vertex_set_p.find (fst v, N.of_nat n) vm_new = Some (InPort gt)
                     | None => True
                     end)
             /\ (* other vertices do not change *)
                (forall (v0 n0 : N), v0 <> fst v \/ n0 >= newft_size ->
                     module_graph_vertex_set_p.find (v0, n0) vm_old =
                     module_graph_vertex_set_p.find (v0, n0) vm_new)
             /\ (* connections do not change *)
                module_graph_connection_trees_p.Equal ct_old ct_new
        else False
    end
| Foutput v t =>
    match t with
    | Gtyp ft =>
           module_graph_vertex_set_p.Equal (module_graph_vertex_set_p.add v (OutPort ft) vm_old) vm_new
        /\
           module_graph_connection_trees_p.Equal (module_graph_connection_trees_p.add (v, N0) D_undefined ct_old) ct_new
    | _ =>
        if vtype_find_widths t (fst v) N0 vm_new is Some (newft, newft_size)
        then    (* ground-type input ports are defined *)
                (forall n : nat,
                     match List.nth_error (list_rhs_type_p newft) n with
                     | Some gt => module_graph_vertex_set_p.find (fst v, N.of_nat n) vm_new = Some (OutPort gt)
                     | None => True
                     end)
             /\ (* other vertices do not change *)
                (forall (v0 n0 : N), v0 <> fst v \/ n0 >= newft_size ->
                     module_graph_vertex_set_p.find (v0, n0) vm_old =
                     module_graph_vertex_set_p.find (v0, n0) vm_new)
             /\ (* other connections do not change *)
                (forall (v0 n0 o0 : N), v0 <> fst v \/ n0 >= newft_size \/ o0 > 0 ->
                     module_graph_connection_trees_p.find (v0, n0, o0) ct_old =
                     module_graph_connection_trees_p.find (v0, n0, o0) ct_new)
             /\ (* set wires to undefined *)
                forall n0 : N, n0 < newft_size ->
                    module_graph_connection_trees_p.find (fst v, n0, N0) ct_new = Some D_undefined
        else False
    end
end.

Fixpoint Sem_frag_ports (vm_old : module_graph_vertex_set_p.env) (ct_old : module_graph_connection_trees_p.env) (pp : seq HiFP.hfport) (vm_new : module_graph_vertex_set_p.env) (ct_new : module_graph_connection_trees_p.env) : Prop :=
(* returns True if the ports in pp define the components in vm *)
match pp with
| [::] => vm_old = vm_new /\ ct_old = ct_new
| p :: pp' =>
    exists (vm' : module_graph_vertex_set_p.env) (ct' : module_graph_connection_trees_p.env),
           Sem_frag_port vm_old ct_old p vm' ct'
        /\
           Sem_frag_ports vm' ct' pp' vm_new ct_new
end.

Fixpoint ports_tmap (pp : seq HiFP.hfport) : ft_pmap :=
(* creates a tmap that contains exactly the types of the ports in pp. *)
match pp with
| [::] => ft_empty
| Finput v t :: pp'
| Foutput v t :: pp' => ft_add v t (ports_tmap pp')
end.

Fixpoint stmts_tmap (tmap_scope : ft_pmap * ft_pmap) (ss : HiFP.hfstmt_seq) : option (ft_pmap * ft_pmap) :=
(* extends tmap_scope with the types of the defined components in ss.
   The first part of tmap_scope contains all defined components
   (used to check for name clashes, and will also be used later in Sem_frag_stmt);
   the second part contains only the components in the current scope
   (used to check whether a component defined within a Swhen statement
   is illegally used outside it).
   Produces None if some component is defined more than once,
   if a component is accessed before it is defined,
   or if it is accessed out of scope.

   Problem: does not check the directionality of the component
   (e.g. a node can only be read, an output port can only be written).
   Should we replace the tmap with a component environment? *)
match ss with
| Qnil => Some tmap_scope
| Qcons s ss' =>
    match stmt_tmap tmap_scope s with
    | Some tmap_scope' => stmts_tmap tmap_scope' ss'
    | None => None
    end
end
with stmt_tmap (tmap_scope : ft_pmap * ft_pmap) (s : HiFP.hfstmt) : option (ft_pmap * ft_pmap) :=
(* extends tmap_scope with the type of the component defined in s.
   Produces None if s contains a definition of a component that is already in tmap. *)
match s with
| Sskip => Some tmap_scope
| Sfcnct ref expr =>
    match type_of_ref ref (snd tmap_scope), type_of_expr expr (snd tmap_scope) with
    | Some _, Some _ => Some tmap_scope
    | _, _ => None (* something undefined or out-of-scope is accessed *)
    end
| Sinvalid ref =>
    match type_of_ref ref (snd tmap_scope) with
    | Some _ => Some tmap_scope
    | None => None (* ref is undefined or out of scope *)
    end
| Swire v t =>
    if ft_find v (fst tmap_scope) == None
    then Some (ft_add v t (fst tmap_scope), ft_add v t (snd tmap_scope))
    else None
| Sreg v reg =>
    if ft_find v (fst tmap_scope) == None
    then if reset reg is Rst rst_sig rst_val
         then match type_of_expr rst_sig (snd tmap_scope), type_of_expr rst_val (snd tmap_scope) with
              | Some _, Some _ => Some (ft_add v (type reg) (fst tmap_scope), ft_add v (type reg) (snd tmap_scope))
              | _, _ => None (* something undefined or out-of-scope is accessed *)
              end
         else Some (ft_add v (type reg) (fst tmap_scope), ft_add v (type reg) (snd tmap_scope))
    else None
| Snode v expr =>
    match type_of_expr expr (snd tmap_scope) with
    | Some (exist t _) =>
        if ft_find v (fst tmap_scope) == None
        then Some (ft_add v t (fst tmap_scope), ft_add v t (snd tmap_scope))
        else None
    | None => None (* something undefined or out-of-scope is accessed *)
    end
| Smem _ _ => None
| Sinst _ _ => None
| Swhen _ ss_true ss_false =>
    match stmts_tmap tmap_scope ss_true with
    | Some (tmap_true, _) =>
        match stmts_tmap (tmap_true, snd tmap_scope) ss_false with
        | Some (tmap_false, _) =>
            Some (tmap_false, snd tmap_scope)
        | None => None
        end
    | None => None
    end
end.

Lemma stmts_tmap_subset :
   forall (ss : HiFP.hfstmt_seq) (tmap scope : ft_pmap),
      tmap_subset scope tmap ->
         match stmts_tmap (tmap, scope) ss with
         | Some (tmap', scope') => tmap_subset scope' tmap' /\ tmap_subset tmap tmap' /\ tmap_subset scope scope'
         | None => True
         end
with stmt_tmap_subset :
   forall (s : HiFP.hfstmt) (tmap scope : ft_pmap),
      tmap_subset scope tmap ->
         match stmt_tmap (tmap, scope) s with
         | Some (tmap', scope') => tmap_subset scope' tmap' /\ tmap_subset tmap tmap' /\ tmap_subset scope scope'
         | None => True
         end.
Proof.
* clear stmts_tmap_subset.
  induction ss.
  + unfold stmts_tmap.
    intros ; split ; first by exact H.
    by split ; apply tmap_subset_refl.
  + intros.
    simpl stmts_tmap.
    specialize stmt_tmap_subset with (s := h) (tmap := tmap) (scope := scope).
    destruct (stmt_tmap (tmap, scope) h) as [[tmap' scope']|] ; last by trivial.
    specialize IHss with (tmap := tmap') (scope := scope').
    destruct (stmts_tmap (tmap', scope') ss) as [[tmap'' scope'']|] ; last by trivial.
    split.
    - apply IHss, stmt_tmap_subset, H.
    split.
    - apply (tmap_subset_trans tmap') ; first by apply stmt_tmap_subset.
      by apply IHss, stmt_tmap_subset, H.
    - apply (tmap_subset_trans scope') ; first by apply stmt_tmap_subset.
      by apply IHss, stmt_tmap_subset, H.
* clear stmt_tmap_subset.
  intro.
  destruct s ; simpl ; intros ; try trivial.
  + (* Sskip *) split ; first by exact H.
    by split ; apply tmap_subset_refl.
  + (* Swire *)
    destruct (ft_find s tmap) eqn: Hfind ; simpl ; first by trivial.
    split.
    - by apply tmap_subset_add_add, H.
    split.
    - by apply tmap_subset_add, Hfind.
    - apply tmap_subset_add.
      unfold tmap_subset in H ; specialize H with (v := s).
      destruct (ft_find s scope) ; last by trivial.
      by rewrite -H -Hfind //.
  + (* Sreg *)
    destruct (ft_find s tmap) eqn: Hfind ; simpl ; first by trivial.
    destruct (reset h).
    - split.
      * by apply tmap_subset_add_add, H.
      split.
      * by apply tmap_subset_add, Hfind.
      * apply tmap_subset_add.
        unfold tmap_subset in H ; specialize H with (v := s).
        destruct (ft_find s scope) ; last by trivial.
        by rewrite -H -Hfind //.
    - destruct (type_of_expr h0 scope) ; last by trivial.
      destruct (type_of_expr h1 scope) ; last by trivial.
      split.
      * by apply tmap_subset_add_add, H.
      split.
      * by apply tmap_subset_add, Hfind.
      * apply tmap_subset_add.
        unfold tmap_subset in H ; specialize H with (v := s).
        destruct (ft_find s scope) ; last by trivial.
        by rewrite -H -Hfind //.
  + (* Snode *)
    destruct (type_of_expr h scope) as [[t p]|] ; last by trivial.
    destruct (ft_find s tmap) eqn: Hfind ; simpl ; first by trivial.
    split.
    - by apply tmap_subset_add_add, H.
    split.
    - by apply tmap_subset_add, Hfind.
    - apply tmap_subset_add.
      unfold tmap_subset in H ; specialize H with (v := s).
      destruct (ft_find s scope) ; last by trivial.
      by rewrite -H -Hfind //.
  + (* Sfcnct *)
    destruct (type_of_ref h scope) ; last by trivial.
    destruct (type_of_expr h0 scope) ; last by trivial.
    split.
    - by exact H.
    - split ; by apply tmap_subset_refl.
  + (* Sinvalid *)
    destruct (type_of_ref h scope) ; last by trivial.
    split.
    - by exact H.
    - split ; by apply tmap_subset_refl.
  + (* Swhen *)
    rename h0 into ss_true ; rename h1 into ss_false.
    generalize (stmts_tmap_subset ss_true tmap scope H) ; intro.
    destruct (stmts_tmap (tmap, scope) ss_true) as [[tmap_true scope_true]|] ; last by trivial.
    generalize (stmts_tmap_subset ss_false tmap_true scope (tmap_subset_trans tmap _ _ H (proj1 (proj2 H0)))) ; intro.
    destruct (stmts_tmap (tmap_true, scope) ss_false) as [[tmap_false scope_false]|] ; last by trivial.
    split.
    - apply (tmap_subset_trans tmap) ; first by apply H.
      apply (tmap_subset_trans tmap_true) ; first by apply H0.
      apply H1.
    split.
    - apply (tmap_subset_trans tmap_true) ; first by apply H0.
      apply H1.
    - apply tmap_subset_refl.
Qed.

Lemma stmts_tmap_cat :
   forall (ss1 ss2 : HiFP.hfstmt_seq) (tmap_scope : ft_pmap * ft_pmap),
      stmts_tmap tmap_scope (Qcat ss1 ss2) =
      match stmts_tmap tmap_scope ss1 with
      | Some tmap_scope' => stmts_tmap tmap_scope' ss2
      | None => None
      end.
Proof.
induction ss1.
* simpl Qcat ; simpl stmts_tmap ; simpl.
  by intro ; reflexivity.
* simpl Qcat ; simpl stmts_tmap.
  intros.
  destruct (stmt_tmap tmap_scope h) ; last by reflexivity.
  by apply IHss1.
Qed.

Fixpoint component_stmts_of (ss : HiFP.hfstmt_seq) : HiFP.hfstmt_seq :=
match ss with
| Qnil => ss
| Qcons s ss' => Qcat (component_stmt_of s) (component_stmts_of ss')
end
with component_stmt_of (s : HiFP.hfstmt) : HiFP.hfstmt_seq :=
match s with
| Sskip
| Sfcnct _ _
| Sinvalid _ => Qnil ProdVarOrder.T
| Swire _ _
| Sreg _ _
| Snode _ _
| Smem _ _
| Sinst _ _ => Qcons s (Qnil ProdVarOrder.T)
| Swhen _ ss_true ss_false => Qcat (component_stmts_of ss_true) (component_stmts_of ss_false)
end.

Definition tmap_scope_subset (ts1 ts2 : ft_pmap * ft_pmap) : Prop :=
fst ts1 = fst ts2 /\ tmap_subset (snd ts1) (snd ts2).

Lemma stmts_tmap_components :
   forall (ss : HiFP.hfstmt_seq) (tmap_scope1 tmap_scope2 : ft_pmap * ft_pmap),
      tmap_subset (snd tmap_scope1) (fst tmap_scope1) ->
      tmap_subset (snd tmap_scope2) (fst tmap_scope2) ->
      tmap_scope_subset tmap_scope1 tmap_scope2 ->
         match stmts_tmap tmap_scope1 ss, stmts_tmap tmap_scope2 (component_stmts_of ss) with
         | Some result1, Some result2 =>
              tmap_scope_subset result1 result2
         | Some _, None => False
         | _, _ => True
         end
with stmt_tmap_components :
   forall (s : HiFP.hfstmt) (tmap_scope1 tmap_scope2 : ft_pmap * ft_pmap),
      tmap_subset (snd tmap_scope1) (fst tmap_scope1) ->
      tmap_subset (snd tmap_scope2) (fst tmap_scope2) ->
      tmap_scope_subset tmap_scope1 tmap_scope2 ->
         match stmt_tmap tmap_scope1 s, stmts_tmap tmap_scope2 (component_stmt_of s) with
         | Some result1, Some result2 =>
              tmap_scope_subset result1 result2
         | Some _, None => False
         | _, _ => True
         end.
Proof.
* clear stmts_tmap_components.
  induction ss.
  + unfold component_stmts_of, stmts_tmap ; done.
  + intros.
    simpl stmts_tmap.
    rewrite stmts_tmap_cat.
    specialize stmt_tmap_components with (s := h) (tmap_scope1 := tmap_scope1) (tmap_scope2 := tmap_scope2).
    generalize (stmt_tmap_subset h (fst tmap_scope1) (snd tmap_scope1) H) ;
          intro ; rewrite -surjective_pairing in H2.
    destruct (stmt_tmap tmap_scope1 h) as [tmap_scope1'|] ;
          first rewrite (surjective_pairing tmap_scope1') in H2 ;
          last by trivial.
    generalize (stmts_tmap_subset (component_stmt_of h) (fst tmap_scope2) (snd tmap_scope2) H0) ;
          intro ; rewrite -surjective_pairing in H3.
    destruct (stmts_tmap tmap_scope2 (component_stmt_of h)) as [tmap_scope2'|] ;
          first rewrite (surjective_pairing tmap_scope2') in H3.
    - apply IHss, stmt_tmap_components ; try assumption.
      * by apply (proj1 H2).
      * by apply (proj1 H3).
    - specialize IHss with (tmap_scope1 := tmap_scope1').
      destruct (stmts_tmap tmap_scope1' ss) as [tmap_scope1''|] ; last by trivial.
      apply stmt_tmap_components ; by assumption.
* clear stmt_tmap_components.
  intros.
  destruct s ; simpl ; (try (by done)) ;
        unfold tmap_scope_subset, tmap_subset in H1 ; destruct H1 ; try rewrite -H1.
  + (* Swire *)
    destruct (ft_find s (fst tmap_scope1)) ; simpl ; first by trivial.
    unfold tmap_scope_subset ; split ; first by reflexivity.
    simpl snd.
    intro.
    unfold ft_find, ft_add.
    destruct (v == s) eqn: Hvs ; rewrite Hvs ; first by reflexivity.
    by apply H2.
  + (* Sreg *)
    destruct (ft_find s (fst tmap_scope1)) ; simpl ; first by trivial.
    destruct (reset h).
    - unfold tmap_scope_subset ; split ; first by reflexivity.
      simpl snd.
      intro.
      unfold ft_find, ft_add.
      destruct (v == s) eqn: Hvs ; rewrite Hvs ; first by reflexivity.
      by apply H2.
    - destruct (type_of_expr h0 (snd tmap_scope1)) eqn: Hte0 ; last by trivial.
      assert (type_of_expr h0 (snd tmap_scope2) = Some f).
            generalize (type_of_expr_subset h0 (snd tmap_scope1) (snd tmap_scope2)) ; intro.
            rewrite Hte0 in H3.
            apply H3.
            by exact H2.
      rewrite H3.
      destruct (type_of_expr h1 (snd tmap_scope1)) eqn: Hte1 ; last by trivial.
      assert (type_of_expr h1 (snd tmap_scope2) = Some f0).
            generalize (type_of_expr_subset h1 (snd tmap_scope1) (snd tmap_scope2)) ; intro.
            rewrite Hte1 in H4.
            apply H4.
            by exact H2.
      rewrite H4.
      unfold tmap_scope_subset ; split ; first by reflexivity.
      simpl snd.
      intro.
      unfold ft_find, ft_add.
      destruct (v == s) eqn: Hvs ; rewrite Hvs ; first by reflexivity.
      by apply H2.
  + (* Snode *)
    destruct (type_of_expr h (snd tmap_scope1)) as [[t p]|] eqn: Hte ; last by trivial.
    assert (type_of_expr h (snd tmap_scope2) = Some (exist ftype_not_implicit_width t p)).
          generalize (type_of_expr_subset h (snd tmap_scope1) (snd tmap_scope2)) ; intro.
          rewrite Hte in H3.
          apply H3.
          by exact H2.
    rewrite H3.
    destruct (ft_find s (fst tmap_scope1)) ; simpl ; first by trivial.
    unfold tmap_scope_subset ; split ; first by reflexivity.
    simpl snd.
    intro.
    unfold ft_find, ft_add.
    destruct (v == s) eqn: Hvs ; rewrite Hvs ; first by reflexivity.
    by apply H2.
  + (* Sfcnct *)
    destruct (type_of_ref h (snd tmap_scope1)) ; last by trivial.
    destruct (type_of_expr h0 (snd tmap_scope1)) ; last by trivial.
    unfold tmap_scope_subset ; split ; first by exact H1.
    by exact H2.
  + (* Sinvalid *)
    destruct (type_of_ref h (snd tmap_scope1)) ; last by trivial.
    unfold tmap_scope_subset ; split ; first by exact H1.
    by exact H2.
  + (* Swhen *)
    rename h0 into ss_true ; rename h1 into ss_false.
    rewrite stmts_tmap_cat.
    generalize (stmts_tmap_components ss_true tmap_scope1 tmap_scope2 H H0) ; intro.
    generalize (stmts_tmap_subset ss_true (fst tmap_scope1) (snd tmap_scope1) H) ;
          intro ; rewrite -surjective_pairing in H4.
    destruct (stmts_tmap tmap_scope1 ss_true) as [[tmap_true tmap_scope_true]|] eqn: Hss_true ; last by trivial.
    generalize (stmts_tmap_subset (component_stmts_of ss_true) (fst tmap_scope2) (snd tmap_scope2) H0) ;
          intro ; rewrite -surjective_pairing in H5.
    destruct (stmts_tmap tmap_scope2 (component_stmts_of ss_true)) as [[tmap_true' tmap_scope_true']|] eqn: Hss_true' ;
          last by contradict H3 ; unfold tmap_scope_subset ; split ;
                  first (by exact H1) ; exact H2.
    assert (tmap_subset (snd tmap_scope1) tmap_true).
          apply (tmap_subset_trans (fst tmap_scope1)) ; first (by exact H) ;
          apply H4.
    assert (tmap_scope_subset (tmap_true, snd tmap_scope1) (tmap_true', tmap_scope_true')).
          split.
          - simpl fst ; apply H3 ; exact (conj H1 H2).
          - simpl snd ; apply (tmap_subset_trans (snd tmap_scope2)) ; first by exact H2.
            by apply H5.
    generalize (stmts_tmap_components ss_false (tmap_true, snd tmap_scope1) (tmap_true', tmap_scope_true') H6 (proj1 H5) H7) ; intro.
    generalize (stmts_tmap_subset ss_false tmap_true (snd tmap_scope1) H6) ;
          intro.
    destruct (stmts_tmap (tmap_true, snd tmap_scope1) ss_false) as [[tmap_false tmap_scope_false]|] eqn: Hss_false ; last by trivial.
    destruct (stmts_tmap (tmap_true', tmap_scope_true') (component_stmts_of ss_false)) as [[tmap_false' tmap_scope_false']|] eqn: Hss_false' ;
          last by trivial.
    split.
    - simpl fst ; apply H8.
    - simpl snd.
      apply (tmap_subset_trans tmap_scope_false) ; first by apply H9.
      apply H8.
Qed.

Definition Sem (F : HiFP.hfmodule) (vm : module_graph_vertex_set_p.env) (ct : module_graph_connection_trees_p.env) : Prop :=
(* The predicate returns True if G = (vm, ct) conforms to F.
   (If F has errors, there is no such G.)
   (If F has implicit width components, then there are many such Gs.)

   Problem: I made some assumption about identifiers of aggregate-type components;
   is that what you need? *)
match F with
| FInmod n pp ss =>
    let pmap := ports_tmap pp in
    match stmts_tmap (pmap, pmap) ss with
    | Some (tmap, _) =>
           (forall v1 v2: N,
                match ft_find (v1, v2) tmap with
                | Some (Gtyp _)
                | None => True
                | _ => (* (v1, N0) identifies an aggregate-type component;
                          then there should not be any other component with the same v1 *)
                       v2 = N0
                    /\
                       forall v2' : N, v2' <> N0 -> ft_find (v1, v2') tmap = None
                end)
        /\
           exists (vm' : module_graph_vertex_set_p.env) (ct' : module_graph_connection_trees_p.env),
                  Sem_frag_ports (module_graph_vertex_set_p.empty vertex_type)
                                 (module_graph_connection_trees_p.empty def_expr)
                                 pp vm' ct'
               /\
                  Sem_frag_stmts vm' ct' ss vm ct tmap
    | None => False
    end
| FExmod _ _ _ => False
end.
