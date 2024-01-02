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

Definition output_connectors (v : vertex_type) : seq fgtyp_explicit :=
(* a list of types of the output connectors of a vertex of type v *)
   match v with
   | OutPort _ => [::] (* An OutPort has no output connector because the data is sent to somewhere outside the module *)
   | InPort (Fsint_implicit w) => [:: Fsint_exp w]
   | InPort (Fuint_implicit w) => [:: Fuint_exp w]
   | InPort it => [:: exist not_implicit_width it I] (* convert to fgtyp_explicit *)

   | Register (Fuint w) | Register (Fuint_implicit w)
   | RegisterReset (Fuint w) _ | RegisterReset (Fuint_implicit w) _ => [:: Fuint_exp w]
   | Register (Fsint w) | Register (Fsint_implicit w)
   | RegisterReset (Fsint w) _ | RegisterReset (Fsint_implicit w) _ => [:: Fsint_exp w]
   | Register Fclock | RegisterReset Fclock _ => [:: Fclock_exp]
   | Register Freset | RegisterReset Freset _ => [::] (* should not happen *)
   | Register Fasyncreset | RegisterReset Fasyncreset _ => [:: Fasyncreset_exp]
   | Wire (Fuint w) | Wire (Fuint_implicit w) => [:: Fuint_exp w]
   | Wire (Fsint w) | Wire (Fsint_implicit w) => [:: Fsint_exp w]
   | Wire Fclock => [:: Fclock_exp]
   | Wire Freset => [::] (* should not happen *)
   | Wire Fasyncreset => [:: Fasyncreset_exp]
   | Node (Fuint w) | Node (Fuint_implicit w) => [:: Fuint_exp w]
   | Node (Fsint w) | Node (Fsint_implicit w) => [:: Fsint_exp w]
   | Node Fclock => [:: Fclock_exp]
   | Node Freset => [::] (* should not happen *)
   | Node Fasyncreset => [:: Fasyncreset_exp]
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
   - a number to identify the input connector of the vertex *)

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
  Definition env : Type := t HiFP.hfexpr.
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
      | [:: ic], [:: oc] =>    (module_graph_connection_trees_p.find ic ct_new == Some (Eref ref_src))
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

(* Find the type of different kinds of expressions: *)

Fixpoint type_of_ffield (v : VarOrder.t) (ff : ffield) : option ftype :=
(* Find the type of field v in bundle type (Btyp ff) *)
match ff with
| Fnil => None
| Fflips v0 Nflip t ff' => if v == v0 then Some t else type_of_ffield v ff'
| Fflips _ Flipped _ _ => None
end.

Fixpoint type_of_ref (ref : HiFP.href) (tmap : ft_pmap) : option ftype :=
(* Find the type of reference ref, using the type information from tmap *)
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
                              match (List.nth_error input_list n), (List.nth_error expr_list n) with 
                              | Some ic, Some ex => module_graph_connection_trees_p.find ic ct_new = Some ex
                              (* connect_type_compatible already checked that the lists have the same length.
                                 There is no need to add a check here:
                              | Some _, None | None, Some _ => False *)
                              | _, _ => True
                              end)
                     /\
                        forall v0 : PProdVarOrder.T,
                              if (v0 \in input_list) then True
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
                              | Some ic => module_graph_connection_trees_p.find ic ct_new = None (* or better: a mark that indicates it’s been invalidated *)
                              | None => True
                              end)
                     /\
                        forall v0 : PProdVarOrder.T,
                              if (v0 \in input_list) then True
                              else module_graph_connection_trees_p.find v0 ct_old = module_graph_connection_trees_p.find v0 ct_new
          | _ => False
          end

(* The following cases of Sem_frag_stmt have not yet been adapted to the simplified semantics.
To make the function parse I add a catch-all case for the remaining statements here: *)

| _ => False
end.


   | Swire v t => exists tlist : seq fgtyp,
                        vtype_list t nil tlist
                     /\ (forall (v0 : VarOrder.T) (n0 : N),
                           if v0 != (fst v) then module_graph_vertex_set_p.find (v0, n0) vm_old = module_graph_vertex_set_p.find (v0, n0) vm_new
                        /\ module_graph_connection_trees_p.find ((v0, n0), 0%num) ct_new = module_graph_connection_trees_p.find ((v0, n0), 0%num) ct_old
                           else True)
                     /\ (forall n : nat,
                           match List.nth_error tlist n with
                           | Some nv => module_graph_vertex_set_p.find (fst v, N.of_nat n) vm_new = Some (Wire nv)
                                     /\ module_graph_connection_trees_p.find ((fst v, N.of_nat n), 0%num) ct_new = Some Not_connected
                           | None => module_graph_vertex_set_p.find (fst v, N.of_nat n) vm_new = module_graph_vertex_set_p.find (fst v, N.of_nat n) vm_old
                                     /\ module_graph_connection_trees_p.find ((fst v, N.of_nat n), 0%num) ct_new = module_graph_connection_trees_p.find ((fst v, N.of_nat n), 0%num) ct_old
                           end)
                     /\ (* ct *)
                        module_graph_connection_trees_p.Equal ct_old ct_new
   | Sreg v reg => exists tlist : seq fgtyp,
                   vtype_list (type reg) nil tlist /\
                   match list_rhs_expr_p (clock reg) vm_old ct_old tmap, type_of_expr (clock reg) tmap with
                   | Some ([:: clk_out], nvmap0, nctree0), Some (exist (Gtyp Fclock) _) =>
                        exists (nvmap : module_graph_vertex_set_p.env) (nctree : module_graph_connection_trees_p.env)
                               (rst_sig_is_async : bool) (rst_sig_out : PProdVarOrder.t) (rst_val_out_list : list PProdVarOrder.t),
                              (if (reset reg) is (Rst rst_sig rst_val)
                               then match list_rhs_expr_p rst_sig nvmap0 nctree0 tmap, type_of_expr rst_sig tmap with
                                    | Some ([:: rst_sig_out'], nvmap1, nctree1), Some (exist (Gtyp rst_sig_type) _) =>
                                           rst_sig_out = rst_sig_out'
                                        /\
                                           (rst_sig_type = if rst_sig_is_async then Fasyncreset else Fuint 1)
                                        /\
                                           match list_rhs_expr_p rst_val nvmap1 nctree1 tmap, type_of_expr rst_val tmap with
                                           | Some (rst_val_out_list', nvmap2, nctree2), Some rst_val_type =>
                                                   rst_val_out_list = rst_val_out_list'
                                                /\
                                                   rst_val_type = make_ftype_explicit (type reg)
                                                /\
                                                   nvmap = nvmap2 /\ nctree = nctree2
                                           | _, _ => False
                                           end
                                    | _, _ => False
                                    end
                               else nvmap = nvmap0 /\ nctree = nctree0)
                           /\
                              (forall (v0 : VarOrder.T) (n0 : N), v0 <> fst v ->
                                     module_graph_vertex_set_p.find (v0, n0) nvmap = module_graph_vertex_set_p.find (v0, n0) vm_new
                                  /\ forall (c : N),
                                        module_graph_connection_trees_p.find ((v0, n0), c) nctree = module_graph_connection_trees_p.find ((v0, n0), c) ct_new)
                           /\
                              (forall n : N,
                                  match List.nth_error tlist (N.to_nat n) with
                                  | Some nv =>
                                         module_graph_connection_trees_p.find ((fst v, n), 0%num) ct_new = Some (Leaf ((fst v, n), 0%num))
                                      /\
                                         module_graph_connection_trees_p.find ((fst v, n), 1%num) ct_new = Some (Leaf clk_out)
                                      /\
                                         match reset reg, List.nth_error rst_val_out_list n with
                                         | NRst, _ =>
                                                 module_graph_vertex_set_p.find (fst v, n) vm_new = Some (Register nv)
                                              /\
                                                 module_graph_connection_trees_p.find ((fst v, n), 2%num) nctree = module_graph_connection_trees_p.find ((fst v, n), 2%num) ct_new
                                              /\
                                                 module_graph_connection_trees_p.find ((fst v, n), 3%num) nctree = module_graph_connection_trees_p.find ((fst v, n), 3%num) ct_new
                                         | Rst _ _, Some nr =>
                                                 module_graph_vertex_set_p.find (fst v, n) vm_new = Some (RegisterReset nv rst_sig_is_async)
                                              /\
                                                 module_graph_connection_trees_p.find ((fst v, n), 2%num) ct_new = Some (Leaf rst_sig_out)
                                              /\
                                                 module_graph_connection_trees_p.find ((fst v, n), 3%num) ct_new = Some (Leaf nr)
                                         | _, _ => False
                                         end
                                      /\
                                         forall (c : N), c > 3%num ->
                                            module_graph_connection_trees_p.find ((fst v, n), c) nctree = module_graph_connection_trees_p.find ((fst v, n), c) ct_new
                                  | None => module_graph_vertex_set_p.find (fst v, n) vm_new = module_graph_vertex_set_p.find ((fst v), n) vm_old
                                  end)
                   | _, _ => False
                   end
   | Snode v expr => match list_rhs_expr_p expr vm_old ct_old tmap, type_of_expr expr tmap with
                     | Some (output_list, nvmap, nctree), Some ft0 =>
                           (forall (v0 : VarOrder.T) (n0 : N),
                              if v0 != (fst v) then module_graph_vertex_set_p.find (v0, n0) nvmap = module_graph_vertex_set_p.find (v0, n0) vm_new
                                         else True)
                        /\ (forall (v0 : ProdVarOrder.T) (n0 : N),
                              if v0 != v then module_graph_connection_trees_p.find (v0, n0) nctree = module_graph_connection_trees_p.find (v0, n0) ct_new
                                   else True)
                        /\ exists tlist : list fgtyp, vtype_list (proj1_sig ft0) nil tlist /\
                           forall n : nat,
                              match List.nth_error tlist n, List.nth_error output_list n with
                              | Some nv, Some oc => module_graph_vertex_set_p.find ((fst v), N.of_nat n) vm_new = Some (Node nv)
                                        /\ module_graph_connection_trees_p.find ((fst v, N.of_nat n), 0%num) ct_new = Some (Leaf oc)
                              | None, None => module_graph_vertex_set_p.find ((fst v), N.of_nat n) vm_new = module_graph_vertex_set_p.find ((fst v), N.of_nat n) nvmap
                                        /\ forall c : N,
                                               module_graph_connection_trees_p.find ((fst v, N.of_nat n), c) ct_new = module_graph_connection_trees_p.find ((fst v, N.of_nat n), c) nctree
                               | _, _ => False
                               (* let add_list (v : VarOrder.T) (vm : module_graph_connection_trees_p.env) (p : nat * fgtyp) := module_graph_vertex_set_p.add (v, fst p) (Wire (snd p)) vm in
                               module_graph_vertex_set_p.Equal vm_new (foldl add_list nvmap (zip (iota 1 (length tlist)) tlist)) *)
                               end
                     | _, _ => False
                     end
   | Smem v mem => False (* ? *)
                 (*exists data_tlist : seq fgtyp,
                         vtype_list (data_type mem) nil data_tlist
                     /\ (forall (v0 : VarOrder.T) (n0 : N),
                           if v0 != (fst v) then module_graph_vertex_set_p.find (v0, n0) vm_old = module_graph_vertex_set_p.find (v0, n0) vm_new
                                              /\ module_graph_connection_trees_p.find ((v0, n0), 0%num) ct_new = module_graph_connection_trees_p.find ((v0, n0), 0%num) ct_old
                           else True)
                     /\ (let tlist := (some type based on the ports of mem and data_tlist) in
                         forall n : nat,
                           match List.nth_error tlist n with
                           | Some nv => module_graph_vertex_set_p.find (fst v, N.of_nat n) vm_new = Some (Wire nv)
                                     /\ module_graph_connection_trees_p.find ((fst v, N.of_nat n), 0%num) ct_new = Some Not_connected
                           | None => module_graph_vertex_set_p.find (fst v, N.of_nat n) vm_new = module_graph_vertex_set_p.find (fst v, N.of_nat n) vm_old
                                     /\ module_graph_connection_trees_p.find ((fst v, N.of_nat n), 0%num) ct_new = module_graph_connection_trees_p.find ((fst v, N.of_nat n), 0%num) ct_old
                           end)
                     /\ (* ct *)
                        module_graph_connection_trees_p.Equal ct_old ct_new*)
   | Sinst var1 var2 => False (* ? *)
   | Swhen cond ss_true ss_false => match list_rhs_expr_p cond vm_old ct_old tmap, type_of_expr cond tmap with
                                    | Some ([:: oc], nvmap0, nctree0), Some (exist (Gtyp (Fuint 1)) _) => exists (vm' : module_graph_vertex_set_p.env) (ct_true ct_false : module_graph_connection_trees_p.env), 
                                          Sem_frag_stmts nvmap0 nctree0 ss_true vm' ct_true tmap
                                       /\ Sem_frag_stmts vm' nctree0 ss_false vm_new ct_false tmap
                                       /\ (*False*) 
                                          let ct0 := module_graph_connection_trees_p.map2 (map2_helper_ct oc) ct_old ct_new in
                                          module_graph_connection_trees_p.Equal ct_new ct0
                                        (*ct_new is a combination of ct_true and ct_false (probably using map2):
                                          * if a connection is defined in both and is equal, just copy it
                                          * if a connection is defined in both and is different, create a choice connection tree
                                          * if a connection is only present in ct_true / ct_false and the vertex of the input connector was not in vm_old, then it should be copied
                                          * if a connection is only present in ct_true / ct_false and the vertex of the input connector was in vm_old, then the new connection should be unconnected.
                                          Problem with the last two cases: it is unclear how to decide whether the input connector was in vm_old,
                                          because map2 does not provide the key. *)
                                    | _, _ => False
                                    end
   end with
Sem_frag_stmts (vm_old : module_graph_vertex_set_p.env) (ct_old : module_graph_connection_trees_p.env) (ss : HiFP.hfstmt_seq) (vm_new : module_graph_vertex_set_p.env) (ct_new : module_graph_connection_trees_p.env) (tmap : ft_pmap) : Prop :=
   match ss with
   | Qnil => module_graph_vertex_set_p.Equal vm_old vm_new /\ module_graph_connection_trees_p.Equal ct_old ct_new
   | Qcons s ss' => exists (vm' : module_graph_vertex_set_p.env) (ct' : module_graph_connection_trees_p.env), 
                     Sem_frag_stmt vm_old ct_old s vm' ct' tmap /\ Sem_frag_stmts vm' ct' ss' vm_new ct_new tmap
   end.

