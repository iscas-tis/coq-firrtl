From Coq Require Import FunInd FMaps FMapAVL OrderedType ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat ssrint eqtype seq ssrfun fintype.
From simplssrlib Require Import Types SsrOrder FSets FMaps Tactics Var Store.
(*From nbits Require Import NBits.*)
From firrtl Require Import Firrtl Env HiEnv HiFirrtl .


(* (*Set Printing Universes.*) *)
(* Variable E : nat -> Type. *)
(* Variable A : forall i :nat, E i. Check (A 1). *)
(* Check @list nat. Check @list. *)
(* Variable B: {x:nat|x<2}.  *)


Inductive vertex_type :=
   (* what kind of vertices can be in the module graph *)
   OutPort : fgtyp (* within the module there is only an input
                                (the output goes to some place outside the module) *) -> vertex_type |
   InPort : fgtyp -> vertex_type | (* main module only at present *)
   (* register, wire etc. *)
   Register : fgtyp -> HiFP.hfexpr (* clock *) -> HiFP.rst -> bool (* true if the reset is Fasyncreset *) -> vertex_type | (* Register, possibly with reset. The boolean is true if it is Fasyncreset. *)
   Wire : fgtyp -> vertex_type |
   (*memory : ?
   inst : ?*)
   Node : fgtyp -> vertex_type.

(* equality of vertex_type is decidable *)
Lemma vertex_type_eq_dec : forall {x y : vertex_type}, {x = y} + {x <> y}.
Admitted.
Lemma rst_eq_dec : forall {x y : HiFP.rst} , {x = y} + {x <> y}.
Admitted.

  Parameter rst_eqn : forall (x y : HiFP.rst), bool.
  Axiom rst_eqP : Equality.axiom rst_eqn.
  Canonical rst_eqMixin := EqMixin rst_eqP.
  Canonical rst_eqType := Eval hnf in EqType HiFP.rst rst_eqMixin.

Definition vertex_type_eqn (x y : vertex_type) : bool :=
match x, y with
| OutPort tx, OutPort ty
| InPort tx, InPort ty
(*| Reference a, Reference b*)
| Wire tx, Wire ty
(*memory : ?
inst : ?*)
| Node tx, Node ty => tx == ty
| Register tx cx rx bx, Register ty cy ry by_ =>
    (tx == ty) && (cx == cy) && (rx == ry)  && (bx == by_)
| _, _ => false
end.
Lemma vertex_type_eqP : Equality.axiom vertex_type_eqn.
Proof.
rewrite /Equality.axiom ; intros.
case: (@vertex_type_eq_dec x y) => H.
* rewrite H /vertex_type_eqn ; clear -y.
  destruct y ; rewrite eq_refl ; try rewrite andTb eq_refl ;
  try rewrite andTb eq_refl ; try rewrite andTb eq_refl ;
  apply ReflectT ; reflexivity.
* rewrite /vertex_type_eqn.
  destruct x, y ; try contradiction ; try (apply ReflectF ; exact H).
  + 3:
    destruct (b == b0) eqn: Hb ;
    last (by rewrite andbF ; apply ReflectF ; exact H) ;
    rewrite andbT ;
    destruct (r == r0) eqn: Hr ;
    last (by rewrite andbF ; apply ReflectF ; exact H) ;
    rewrite andbT ;
    destruct (h == h0) eqn: Hh ;
    last (by rewrite andbF ; apply ReflectF ; exact H) ;
    rewrite andbT ;
    destruct (f == f0) eqn: Hf ;
    last (by apply ReflectF ; exact H) ;
    apply ReflectT ; move /eqP : Hb => Hb ; move /eqP : Hr => Hr ;
    move /eqP : Hh => Hh ; move /eqP: Hf => Hf ;
    rewrite Hb Hr Hh Hf //.
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

(* vertex set of a module graph (using pairs of natural numbers as keys) *)

(* The vertex set should have type CEP.t vertex_type. *)
(*
Module MakeVtypFMap (V : SsrOrder) (VM : SsrFMap with Module SE := V)
<: SsrFMap with Module SE := V.
  Include VM.
  Include FMapLemmas VM.
  Definition env : Type := t vertex_type.
End MakeVtypFMap.

Module ProdVarOrder := MakeProdOrder VarOrder VarOrder.
Module PVM <: SsrFMap := FMaps.MakeTreeMap ProdVarOrder.
Module module_graph_vertex_set_p <: SsrFMap := MakeVtypFMap ProdVarOrder PVM.
*)


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


(*---------------------------------------------------------------------------*)
(* Helper functions for connecting                                           *)

Fixpoint connect_type_compatible (can_flip : bool) (ft_tgt ft_src : ftype) (flipped : bool) : bool :=
(* Returns true if a connection from ft_src to ft_tgt is allowed.
   flipped == true indicates that the connection should be the other way actually.
   If can_flip == false, no flipped fields are allowed in bundle types. *)
match ft_tgt, ft_src with
| Gtyp (Fuint _), Gtyp (Fuint _)
| Gtyp (Fsint _), Gtyp (Fsint _)
| Gtyp Fclock, Gtyp Fclock
| Gtyp Fasyncreset, Gtyp Fasyncreset => true
| Gtyp (Fuint_implicit w_tgt), Gtyp (Fuint w_src)
| Gtyp (Fsint_implicit w_tgt), Gtyp (Fsint w_src) => flipped || (w_tgt >= w_src)
| Gtyp (Fuint w_tgt), Gtyp (Fuint_implicit w_src)
| Gtyp (Fsint w_tgt), Gtyp (Fsint_implicit w_src) => (~~flipped) || (w_tgt <= w_src)
| Gtyp (Fuint_implicit w_tgt), Gtyp (Fuint_implicit w_src)
| Gtyp (Fsint_implicit w_tgt), Gtyp (Fsint_implicit w_src) =>
    if flipped then w_tgt <= w_src else w_tgt >= w_src
| Atyp ft_tgt' n_tgt, Atyp ft_src' n_src =>
       (n_tgt == n_src)
    &&
       connect_type_compatible can_flip ft_tgt' ft_src' flipped
| Btyp ff_tgt, Btyp ff_src => connect_type_compatible_fields can_flip ff_tgt ff_src flipped
| _, _ => false
end
with connect_type_compatible_fields (can_flip : bool) (ff_tgt ff_src : ffield) (flipped : bool) : bool :=
(* Returns true if a connection from (Btyp ff_src) to (Btyp ff_tgt) is allowed.
   flipped == true indicates that the connection should be the other way actually.
   If can_flip == false, no flipped fields are allowed in bundle types. *)
match ff_tgt, ff_src with
| Fnil, Fnil => true
| Fflips v_tgt Nflip ft_tgt ff_tgt', Fflips v_src Nflip ft_src ff_src' =>
       (v_tgt == v_src)
    &&
       connect_type_compatible can_flip ft_tgt ft_src flipped
    &&
       connect_type_compatible_fields can_flip ff_tgt' ff_src' flipped
| Fflips v_tgt Flipped ft_tgt ff_tgt', Fflips v_src Flipped ft_src ff_src' =>
       can_flip
    &&
       (v_tgt == v_src)
    &&
       connect_type_compatible can_flip ft_tgt ft_src (~~flipped)
    &&
       connect_type_compatible_fields can_flip ff_tgt' ff_src' flipped
| _, _ => false
end.

Definition connect_fgtyp (ct_old : CEP.t def_expr)
                         (ref_tgt : HiFP.href) (lst_tgt : list CEP.key)
                         (ref_src : HiFP.href) (lst_src : list CEP.key)
                         (flipped : bool)
                         (ct_new : CEP.t def_expr) : bool :=
(* The predicate checks whether ct_new contains the correct connection that connects from lst_src to lst_tgt,
   and it does not change the connection into lst_src.
   These lists must be one-element lists for output and input connectors of compatible types.
   It assumes that the types are compatible. *)
match flipped, ref_tgt, lst_tgt, ref_src, lst_src with
| false, _, [:: ic], ref_src, [:: oc]
| true,  ref_src, [:: oc], _, [:: ic] =>
       (CEP.find ic ct_new == Some (D_fexpr (Eref ref_src)))
    &&
       (CEP.find oc ct_new == CEP.find oc ct_old)
       (* why this is compared?
          In Sem_frag_stmt, it is ensured that connection trees NOT related to tgt or src are not changed.
          Here, we need to ensure that the connection tree of tgt is changed
          and the connection tree of src remains the same. *)
| _, _, _, _, _ => false
end.

Fixpoint connect (ct_old : CEP.t def_expr)
                 (ref_tgt : HiFP.href) (lst_tgt : list CEP.key) (ft_tgt : ftype)
                 (ref_src : HiFP.href) (lst_src : list CEP.key) (ft_src : ftype)
                 (flipped : bool)
                 (ct_new : CEP.t def_expr) : bool :=
(* The predicate returns true if the correct connection trees are in ct_new
   that connect from lst_src to lst_tgt, and that the connection trees that
   connect to lst_src are not changed.  Other connection trees are not checked.
   The type of lst_tgt is ft_tgt, and the type of lst_src is ft_src.
   These references are *not* required to have passive types. *)
match ft_tgt, ft_src with
| Gtyp gt_tgt, Gtyp gt_src => connect_fgtyp ct_old ref_tgt lst_tgt ref_src lst_src flipped ct_new
| Atyp elt_tgt n1, Atyp elt_src n2 =>
       (n1 == n2)
   &&
       let type_len := size_of_ftype elt_tgt in
       [forall n : ordinal n1,
          connect ct_old
                  (Esubindex ref_tgt n) (take type_len (drop (n * type_len) lst_tgt)) elt_tgt
                  (Esubindex ref_src n) (take type_len (drop (n * type_len) lst_src)) elt_src
                  flipped ct_new]
| Btyp ff_tgt, Btyp ff_src => connect_fields ct_old ref_tgt lst_tgt ff_tgt ref_src lst_src ff_src flipped ct_new
| _, _ => false
end
with connect_fields (ct_old : CEP.t def_expr)
                    (ref_tgt : HiFP.href) (lst_tgt : list CEP.key) (ft_tgt : ffield)
                    (ref_src : HiFP.href) (lst_src : list CEP.key) (ft_src : ffield)
                    (flipped : bool)
                    (ct_new : CEP.t def_expr) : bool :=
(* The predicate returns true if the correct connection trees are in ct_new
   that connect from lst_src to lst_tgt, and that the connection trees that
   connect to lst_src are not changed.  Other connection trees are not checked.
   The type of lst_tgt is (Btyp ft_tgt), and the type of lst_src is (Btyp ft_src).
   These references are *not* required to have passive types. *)
match ft_tgt, ft_src with
| Fnil, Fnil => true
| Fflips v1 Nflip gtt ft, Fflips v2 Nflip gts fs =>
       (v1 == v2)
    &&
       let type_len := size_of_ftype gtt in
              connect ct_old (Esubfield ref_tgt v1) (take type_len lst_tgt) gtt (Esubfield ref_src v2) (take type_len lst_src) gts flipped ct_new
           &&
              connect_fields ct_old ref_tgt (drop type_len lst_tgt) ft ref_src (drop type_len lst_src) fs flipped ct_new
| Fflips v1 Flipped gtt ft, Fflips v2 Flipped gts fs =>
       (v1 == v2)
    &&
       let type_len := size_of_ftype gts in
              connect ct_old (Esubfield ref_tgt v1) (take type_len lst_tgt) gtt (Esubfield ref_src v2) (take type_len lst_src) gts (~~flipped) ct_new
           &&
              connect_fields ct_old ref_tgt (drop type_len lst_tgt) ft ref_src (drop type_len lst_src) fs flipped ct_new
| _, _ => false
end.


Fixpoint type_of_ffield (v : VarOrder.T) (ff : ffield) : option ftype :=
(* Find the type of field v in bundle type (Btyp ff). *)
match ff with
| Fnil => None
| Fflips v0 _ t ff' => if v == v0 then Some t else type_of_ffield v ff'
end.

Fixpoint type_of_ref (ref : HiFP.href) (tmap : CEP.t ftype) : option ftype :=
(* Find the type of reference ref, using the type information from tmap.
   Note that widths of implicit-width components may be wrong.

   This function is similar to base_ref; check whether they can be made more similar. *)
match ref with
| Eid v => CEP.find v tmap
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
(* Find the type of a multiplexer whose two inputs have types (exist ftype_not_implicit_width x px)
   and (exist ftype_not_implicit_width y py).
   The function needs to take apart the ftype_explicit so Coq can guess the decreasing argument. *)
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
(* return the type of mux expression on ftypes

   Similar to mux_types in InferWidths *)
   ftype_mux' (proj1_sig x) (proj2_sig x) (proj1_sig y) (proj2_sig y).

Fixpoint type_of_expr (expr : HiFP.hfexpr) (tmap: CEP.t ftype) : option ftype_explicit :=
   (* Find the type of expression expr.

   Similar to type_of_hfexpr in InferWidths *)
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


(*---------------------------------------------------------------------------*)
(* Construct lists of input connectors and expressions (for connecting)      *)

Fixpoint select_field (f : VarOrder.t) (l : seq CEP.key) (ff : ffield) : option (seq CEP.key * ftype) :=
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

Lemma select_field_size :
forall (v : VarOrder.T) (ff : ffield) (input_list : seq CEP.key),
   size_of_fields ff <= size input_list ->
      match select_field v input_list ff with
      | Some (output_list, ft) => size output_list = size_of_ftype ft
      | None => True
      end.
Proof.
induction ff ; simpl ; first by trivial.
intros.
assert (size input_list < size_of_ftype f0 = false)
      by (apply negbTE ; rewrite -leqNgt ;
          apply (leq_trans (n := size_of_ftype f0 + size_of_fields ff)) ;
          try apply H ;
          apply leq_addr).
rewrite H0.
destruct (v == v0).
* rewrite size_take.
  destruct (size_of_ftype f0 < size input_list) eqn: H1 ; first by reflexivity.
  apply anti_leq.
  rewrite leqNgt H1 andTb leqNgt H0 //.
* specialize (IHff (drop (size_of_ftype f0) input_list)).
  destruct (select_field v (drop (size_of_ftype f0) input_list) ff) as [[output_list ff']|] ; last by trivial.
  apply IHff.
  rewrite size_drop leq_subRL ; first by exact H.
  rewrite leqNgt H0 //.
Qed.

Lemma list_rhs_ref_p_ffield :
forall (v : VarOrder.T) (ff : ffield) (input_list : seq CEP.key),
   match type_of_ffield v ff, select_field v input_list ff with
   | Some type_ff, Some (_, list_ff) => type_ff = list_ff
   | Some _, None => size input_list < size_of_fields ff
   | None, Some _ => False
   | None, None => True
   end.
Proof.
induction ff ; simpl ; first by trivial.
intro ; destruct (v == v0).
* destruct (size input_list < size_of_ftype f0) eqn: Hshort ;
        last by reflexivity.
  apply ltn_addr.
  rewrite Hshort //.
* destruct (type_of_ffield v ff).
  + destruct (size input_list < size_of_ftype f0) eqn: Hshort.
    - apply ltn_addr.
      rewrite Hshort //.
    - specialize (IHff (drop (size_of_ftype f0) input_list)).
      destruct (select_field v (drop (size_of_ftype f0) input_list) ff) as [[t list_ff]|] eqn: Hselect ;
            first by exact IHff.
      rewrite size_drop ltn_subLR in IHff ; first by exact IHff.
      apply negbT in Hshort.
      rewrite -leqNgt in Hshort.
      by exact Hshort.
  + destruct (size input_list < size_of_ftype f0) eqn: Hshort ;
          first by trivial.
    specialize (IHff (drop (size_of_ftype f0) input_list)).
    destruct (select_field v (drop (size_of_ftype f0) input_list) ff) as [[t list_ff]|] eqn: Hselect ;
          done.
Qed.

Fixpoint list_lhs_ref_p (ref : HiFP.href) (tmap : CEP.t ftype) : option (seq CEP.key * ftype) :=
(* find which input connectors of ground-type identifiers correspond to reference ref.
   ground-type identifiers are vertices in the module graph (identified by a pair of N);
   input connectors are always the triple (vertex identifier, N0).
   Also find the type of reference ref. *)
match ref with
| Eid v =>
    (* Construct a list of identifiers and find the type of v *)
    match CEP.find v tmap with
    | Some t =>
        Some (mkseq (fun i => (fst v, N.add (snd v) (N.of_nat i))) (size_of_ftype t), t)
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

Lemma list_lhs_ref_p_size :
forall (tmap : CEP.t ftype) (ref : HiFP.href),
match list_lhs_ref_p ref tmap with
| Some (input_list, ft) => size input_list = size_of_ftype ft
| None => True
end.
Proof.
induction ref ; simpl ; try done.
* destruct (CEP.find s tmap) as [ft|] ; last by trivial.
  rewrite size_mkseq //.
* destruct (list_lhs_ref_p ref tmap) as [[input_list [| |ff]]|] ; try apply IHref ; try done.
  generalize (select_field_size v ff input_list) ; intro.
  destruct (select_field v input_list ff) as [[output_list ft]|]; last by trivial.
  apply H, eq_leq.
  rewrite IHref //.
* destruct (list_lhs_ref_p ref tmap) as [[input_list [|t m|]]|] ; try by trivial.
  destruct ((n < m) && (size input_list == m * size_of_ftype t)) eqn: Hshort ; last by trivial.
  move /andP : Hshort => [Hnm /eqP Hshort].
  rewrite size_take size_drop Hshort -mulnBl.
  destruct (size_of_ftype t < (m - n) * size_of_ftype t) eqn: Hsize ; first by reflexivity.
  apply anti_leq.
  rewrite leqNgt Hsize andTb -subnSK // mulSn leq_addr //.
Qed.

Lemma list_lhs_ref_p_type :
forall (tmap : CEP.t ftype) (ref : HiFP.href),
   match type_of_ref ref tmap, list_lhs_ref_p ref tmap with
   | Some type_ft, Some (list_lst, list_ft) => type_ft = list_ft
   | Some _, None
   | None, Some _ => False
   | None, None => True
   end.
Proof.
intros.
induction ref ; simpl ; try by done.
* destruct (CEP.find s tmap) ; by done.
* destruct (type_of_ref ref tmap) as [type_ft|] ;
        last by destruct (list_lhs_ref_p ref tmap) ; done.
  generalize (list_lhs_ref_p_size tmap ref) ; intro.
  destruct (list_lhs_ref_p ref tmap) as [[input_list list_ft]|] ; try done.
  rewrite IHref ; clear type_ft IHref.
  destruct (list_ft) ; try done.
  generalize (list_rhs_ref_p_ffield v f input_list) ; intro.
  simpl size_of_ftype in H.
  destruct (type_of_ffield v f) as [type_ff|] eqn: Hfield ; try done.
  destruct (select_field v input_list f) ; try done.
  rewrite H ltnn // in H0.
* destruct (type_of_ref ref tmap) as [type_ft|] ;
        last by destruct (list_lhs_ref_p ref tmap) ; done.
  generalize (list_lhs_ref_p_size tmap ref) ; intro.
  destruct (list_lhs_ref_p ref tmap) as [[input_list list_ft]|] ; try done.
  rewrite IHref ; clear type_ft IHref.
  destruct (list_ft) ; try done.
  simpl size_of_ftype in H.
  destruct (n < n0) ; last by rewrite andFb //.
  rewrite andTb H mulnC eq_refl //.
Qed.

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

Lemma list_rhs_ref_p_size :
forall (ft : ftype) (ref : HiFP.href),
   match list_rhs_ref_p ref ft with
   | Some expr_list => size expr_list = size_of_ftype ft
   | None => True
   end
with list_rhs_ref_p_fields_size :
forall (ff : ffield) (ref : HiFP.href),
   match list_rhs_ref_p_fields ref ff with
   | Some expr_list => size expr_list = size_of_fields ff
   | None => True
   end.
Proof.
* clear list_rhs_ref_p_size.
  induction ft ; intro ; simpl ; first by done.
  + induction n ; simpl ; first by rewrite muln0 //.
    destruct (iteri n
              (fun (i : nat) (ol : option (seq HiFP.hfexpr)) =>
               match ol with
               | Some l =>
                   match list_rhs_ref_p (Esubindex ref i) ft with
                   | Some li => Some (l ++ li)
                   | None => None
                   end
               | None => None
               end) (Some [::])) ; last by done.
    specialize (IHft (Esubindex ref n)).
    destruct (list_rhs_ref_p (Esubindex ref n) ft) ; last by done.
    rewrite size_cat IHn IHft mulnSr //.
  + apply list_rhs_ref_p_fields_size.
* clear list_rhs_ref_p_fields_size.
  induction ff ; intro ; simpl ; first by done.
  destruct f ; first by done.
  specialize (list_rhs_ref_p_size f0 (Esubfield ref v)).
  destruct (list_rhs_ref_p (Esubfield ref v) f0) ; last by done.
  specialize (IHff ref).
  destruct (list_rhs_ref_p_fields ref ff) ; last by done.
  rewrite size_cat list_rhs_ref_p_size IHff //.
Qed.

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

Lemma list_rhs_expr_p_size :
forall (ft : ftype) (expr : HiFP.hfexpr),
   match list_rhs_expr_p expr ft with
   | Some expr_list => size expr_list = size_of_ftype ft
   | None => True
   end.
Proof.
induction ft ; intro ; first by destruct expr ; simpl ; done.
* induction expr ; simpl ; try done.
  + destruct (list_rhs_expr_p expr2 (Atyp ft n)) ; last by done.
    destruct (list_rhs_expr_p expr3 (Atyp ft n)) ; last by done.
    rewrite IHexpr2 IHexpr3 eq_refl.
    simpl size_of_ftype in IHexpr2, IHexpr3.
    rewrite size_map size_zip IHexpr2 IHexpr3 /minn ltnn //.
  + induction n ; simpl ; first by rewrite muln0 //.
    destruct (iteri n
          (fun (i : nat) (ol : option (seq HiFP.hfexpr)) =>
           match ol with
           | Some l =>
               match list_rhs_ref_p (Esubindex h i) ft with
               | Some li => Some (l ++ li)
               | None => None
               end
           | None => None
           end) (Some [::])) ; last by trivial.
    generalize (list_rhs_ref_p_size ft (Esubindex h n)) ; intro.
    destruct (list_rhs_ref_p (Esubindex h n) ft) ; last by done.
    rewrite size_cat IHn H mulnSr //.
* induction expr ; simpl ; try done.
  + destruct (list_rhs_expr_p expr2 (Btyp f)) ; last by done.
    destruct (list_rhs_expr_p expr3 (Btyp f)) ; last by done.
    rewrite IHexpr2 IHexpr3 eq_refl.
    simpl size_of_ftype in IHexpr2, IHexpr3.
    rewrite size_map size_zip IHexpr2 IHexpr3 /minn ltnn //.
  + induction f ; simpl ; first by done.
    destruct f ; first by done.
    generalize (list_rhs_ref_p_size f0 (Esubfield h v)) ; intro.
    destruct (list_rhs_ref_p (Esubfield h v) f0) ; last by done.
    destruct (list_rhs_ref_p_fields h f1) ; last by done.
    rewrite size_cat H IHf //.
Qed.

Fixpoint list_rhs_type_p (ft : ftype) : seq fgtyp :=
(* Finds the types of ground-type components of type ft.
   (In contrast to the older function vtype_list, this function does not convert Freset to
   Fuint 1 or Fasyncreset.)

   Probably the same as ft_find_sub. *)
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

Lemma list_rhs_type_p_size :
forall (ft : ftype),
   size (list_rhs_type_p ft) = size_of_ftype ft
with list_rhs_ffield_p_size :
forall (ff : ffield),
   size (list_rhs_ffield_p ff) = size_of_fields ff.
Proof.
* clear list_rhs_type_p_size.
  induction ft ; simpl ; try done.
  induction n ; simpl ; first by rewrite muln0 //.
  rewrite size_cat IHn IHft -mulnSr //.
* clear list_rhs_ffield_p_size.
  induction ff ; simpl ; first by done.
  rewrite size_cat list_rhs_type_p_size IHff //.
Qed.


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

Fixpoint Sem_frag_stmt (vm_old : CEP.t vertex_type) (ct_old : CEP.t def_expr) (s : HiFP.hfstmt) (vm_new : CEP.t vertex_type) (ct_new : CEP.t def_expr) (tmap : CEP.t ftype) : Prop :=
   (* The predicate returns True if vm_new/ct_new can be constructed from vm_old/ct_old by applying s.
   type checking, constraints *)
   match s with
   | Sskip => vm_old = vm_new /\ ct_old = ct_new
   | Sfcnct ref_tgt (Eref ref_src) => (* allow non-passive types *)
          CEP.Equal vm_old vm_new
       /\
          match list_lhs_ref_p ref_tgt tmap, list_lhs_ref_p ref_src tmap with
          | Some (lst_tgt, ft_tgt), Some (lst_src, ft_src) =>
                 connect_type_compatible true ft_tgt ft_src false
              /\
                 connect ct_old ref_tgt lst_tgt ft_tgt ref_src lst_src ft_src false ct_new
              /\
                 forall v0 : CEP.key,
                    if (v0 \in lst_tgt) || (v0 \in lst_src) then True (* already checked in connect_non_passive *)
                    else CEP.find v0 ct_old = CEP.find v0 ct_new
          | _, _ => False
          end
   | Sfcnct ref expr =>
          CEP.Equal vm_old vm_new
       /\
          match type_of_ref ref tmap, type_of_expr expr tmap with
          | Some ft_ref, Some (exist ft_expr _) =>
                 connect_type_compatible false ft_ref ft_expr false
              /\
                 match list_lhs_ref_p ref tmap, list_rhs_expr_p expr ft_expr with
                 | Some (input_list, _), Some expr_list =>
                        (forall n : nat,
                             match List.nth_error input_list n, List.nth_error expr_list n with
                             | Some ic, Some ex => CEP.find ic ct_new = Some (D_fexpr ex)
                             (* connect_type_compatible already checked that the lists have the same length.
                                There is no need to add a check here:
                             | Some _, None | None, Some _ => False *)
                             | _, _ => True
                             end)
                     /\
                        forall v0 : CEP.key,
                            if v0 \in input_list then True
                            else CEP.find v0 ct_old = CEP.find v0 ct_new
                 | _, _ => False
                 end
          | _, _ => False
          end
   | Sinvalid ref =>
          CEP.Equal vm_old vm_new
       /\
          match list_lhs_ref_p ref tmap with
          | Some (input_list, ft_ref) =>
                 (forall n : nat,
                      match List.nth_error input_list n with
                      | Some ic => CEP.find ic ct_new = Some D_invalidated
                      | None => True
                      end)
              /\
                 forall v0 : CEP.key,
                     if v0 \in input_list then True
                     else CEP.find v0 ct_old = CEP.find v0 ct_new
          | _ => False
          end
   | Swire v _ =>
       match CEP.find v tmap with
       | Some newft =>
              (* ground-type wires are defined *)
              (forall n : nat,
                   match List.nth_error (list_rhs_type_p newft) n with
                   | Some gt => CEP.find (fst v, N.add (snd v) (N.of_nat n)) vm_new = Some (Wire gt)
                   | None => True
                   end)
           /\ (* other vertices do not change *)
              (forall (v0 n0 : N), v0 <> fst v \/ n0 < snd v \/ n0 >= N.add (snd v) (N.of_nat (size_of_ftype newft)) ->
                   CEP.find (v0, n0) vm_old =
                   CEP.find (v0, n0) vm_new)
           /\ (* other connections do not change *)
              (forall (v0 n0 : N), v0 <> fst v \/ n0 < snd v \/ n0 >= N.add (snd v) (N.of_nat (size_of_ftype newft)) ->
                   CEP.find (v0, n0) ct_old =
                   CEP.find (v0, n0) ct_new)
           /\ (* set wires to undefined *)
              forall n0 : N, n0 < size_of_ftype newft ->
                  CEP.find (fst v, N.add (snd v) n0) ct_new = Some D_undefined
       | None => False (* should not happen *)
       end
   | Sreg v reg =>
       match CEP.find v tmap with
       | Some newft => (* aggregate-type register *)
              match reset reg with
              | Rst rst_sig rst_val => (* type check rst_sig *)
                     match type_of_expr rst_sig tmap with
                     | Some (exist (Gtyp (Fuint 1)) _)
                     | Some (exist (Gtyp Fasyncreset) _) => true
                     | _ => false
                     end
                  /\ (* type check rst_val -- also ensures that newft is passive *)
                     match type_of_expr rst_val tmap with
                     | Some (exist rst_val_type _) => connect_type_compatible false newft rst_val_type false
                     | None => false
                     end
              | NRst => (* type check newft: we only need to verify newft is passive *)
                   ftype_is_passive newft
              end
           /\ (* module graph contains ground-type registers *)
              (forall n : nat,
                   match List.nth_error (list_rhs_type_p newft) n with
                   | Some gt => CEP.find (fst v, N.add (snd v) (N.of_nat n)) vm_new =
                       Some (Register gt (clock reg) (reset reg)
                                      (if reset reg is Rst rst_sig rst_val
                                       then if type_of_expr rst_sig tmap is Some (exist (Gtyp Fasuncreset) _)
                                            then true else false
                                       else false))
                   | None => True
                   end)
           /\ (* type check clock *)
              match type_of_expr (clock reg) tmap with
              | Some (exist (Gtyp Fclock) _) => True
              | _ => False
              end
           /\ (* connect default value for register *)
              match list_rhs_expr_p (Eref (Eid v)) newft with
              | Some expr_list =>
                  forall n : nat,
                      match List.nth_error expr_list n with
                      | Some ex => CEP.find (fst v, N.add (snd v) (N.of_nat n)) ct_new = Some (D_fexpr ex)
                      | None => True
                      end
              | None => False
              end
           /\ (* other vertices do not change *)
              (forall (v0 n0 : N), v0 <> fst v \/ n0 < snd v \/ n0 >= N.add (snd v) (N.of_nat (size_of_ftype newft)) ->
                  CEP.find (v0, n0) vm_old =
                  CEP.find (v0, n0) vm_new)
           /\ (* other connections do not change *)
              (forall (v0 n0 : N), v0 <> fst v \/ n0 < snd v \/ n0 >= N.add (snd v) (N.of_nat (size_of_ftype newft)) ->
                  CEP.find (v0, n0) ct_old =
                  CEP.find (v0, n0) ct_new)
       | None => False (* should not happen *)
       end
   | Snode v expr =>
       match type_of_expr expr tmap with
       | Some (exist newft _) => (* (fst v, N0), ... all have changed *)
              (* ground-type nodes are defined *)
              (forall n : nat,
                   match List.nth_error (list_rhs_type_p newft) n with
                   | Some gt => CEP.find (fst v, N.add (snd v) (N.of_nat n)) vm_new = Some (Node gt)
                   | None => True
                   end)
           /\ (* other vertices do not change *)
              (forall (v0 n0 : N), v0 <> fst v \/ n0 < snd v \/ n0 >= N.add (snd v) (N.of_nat (size_of_ftype newft)) ->
                   CEP.find (v0, n0) vm_old =
                   CEP.find (v0, n0) vm_new)
           /\ (* other connections do not change *)
              (forall (v0 n0 : N), v0 <> fst v \/ n0 < snd v \/ n0 >= N.add (snd v) (N.of_nat (size_of_ftype newft)) ->
                   CEP.find (v0, n0) ct_old =
                   CEP.find (v0, n0) ct_new)
           /\ (* set nodes to the respective part of the expression *)
              match list_rhs_expr_p expr newft with
              | Some expr_list =>
                  forall n : nat,
                      match List.nth_error expr_list n with
                      | Some ex => CEP.find (fst v, N.add (snd v) (N.of_nat n)) ct_new = Some (D_fexpr ex)
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
       then exists (vm_true : CEP.t vertex_type) (ct_true ct_false : CEP.t def_expr),
                   Sem_frag_stmts vm_old ct_old ss_true vm_true ct_true tmap
                /\
                   Sem_frag_stmts vm_true ct_old ss_false vm_new ct_false tmap
                /\
                   CEP.Equal ct_new
                       (CEP.map2 (Swhen_map2_helper cond) ct_true ct_false)
       else False
end
with Sem_frag_stmts (vm_old : CEP.t vertex_type) (ct_old : CEP.t def_expr) (ss : HiFP.hfstmt_seq) (vm_new : CEP.t vertex_type) (ct_new : CEP.t def_expr) (tmap : CEP.t ftype) : Prop :=
match ss with
| Qnil =>
       CEP.Equal vm_old vm_new
    /\
       CEP.Equal ct_old ct_new
| Qcons s ss' =>
    exists (vm' : CEP.t vertex_type) (ct' : CEP.t def_expr),
           Sem_frag_stmt vm_old ct_old s vm' ct' tmap
        /\
           Sem_frag_stmts vm' ct' ss' vm_new ct_new tmap
end.


(** Pass ExpandConnect *)
Section ExpandConnectsP.


(* use type of expressions, returns optional ftype (from inferwidth_rewritten by ky) *)

From firrtl Require Import InferWidth_rewritten.
  

  Fixpoint ftype_list_all (ft : ftype) (l : list ftype) : list ftype :=
    match ft with
    | Gtyp t => cons ft l
    | Atyp t n => cons ft (flatten (repeat (ftype_list_all t l) n))
    | Btyp b => cons ft (ftype_list_btyp_all b l)
    end
  with ftype_list_btyp_all (b : ffield) (l : list ftype) : list ftype :=
         match b with
         | Fnil => l
         | Fflips v fl t fs => ftype_list_all t (ftype_list_btyp_all fs l)
         end.

  Fixpoint ftype_list' (ft : ftype) (l : list ftype) : list ftype :=
    match ft with
    | Gtyp t => rcons l ft
    | Atyp t n => l ++ flatten (repeat (ftype_list' t nil) n)
    | Btyp b => ftype_list_btyp' b l
    end
  with ftype_list_btyp' (b : ffield) (l : list ftype) : list ftype :=
         match b with
         | Fnil => l
         | Fflips v fl t fs => ftype_list_btyp' fs (ftype_list' t l)
         end.

  Fixpoint ftype_list_all_c (ft : ftype) (l : list ftype) : list ftype :=
    match ft with
    | Gtyp t => cons ft l
    | Atyp t n => cons ft (l ++ flatten (repeat (ftype_list_all_c t nil) n))
    | Btyp b => cons ft (ftype_list_btyp_all_c b l)
    end
  with ftype_list_btyp_all_c (b : ffield) (l : list ftype) : list ftype :=
         match b with
         | Fnil => l
         | Fflips v fl t fs => ftype_list_btyp_all_c fs (ftype_list_all_c t l)
         end.
  
  Fixpoint ftype_list_all_r (ft : ftype) (l : list ftype) : list ftype :=
    match ft with
    | Gtyp t => rcons l ft
    | Atyp t n => rcons (l ++ flatten (repeat (ftype_list_all_r t nil) n)) ft
    | Btyp b => rcons (ftype_list_btyp_all_r b l) ft
    end
  with ftype_list_btyp_all_r (b : ffield) (l : list ftype) : list ftype :=
         match b with
         | Fnil => l
         | Fflips v fl t fs => ftype_list_btyp_all_r fs (ftype_list_all_r t l)
         end.
  
  Definition is_gtyp t := match t with | Gtyp _ => true | _ => false end.

  Fixpoint ftype_list_flip (ft : ftype) f (l : list (ftype * bool)) : list (ftype * bool) :=
    match ft with
    | Gtyp t => cons (ft, f) l
    | Atyp t n => cons (ft, f) (flatten (repeat (ftype_list_flip t f l) n))
    | Btyp b => cons (ft, f) (ftype_list_btyp_flip b f l)
    end
  with ftype_list_btyp_flip (b : ffield) f (l : list (ftype * bool)) : list (ftype *bool) :=
         match b with
         | Fnil => l
         | Fflips v Flipped t fs => ftype_list_flip t (~~ f) (ftype_list_btyp_flip fs f l)
         | Fflips v Nflip t fs => ftype_list_flip t f (ftype_list_btyp_flip fs f l)
         end.

  Definition agt := (Atyp (Btyp (Fflips 5%num Flipped (Gtyp (Fsint_implicit 1)) (Fflips 6%num Nflip (Atyp (Gtyp (Fsint 2)) 2) Fnil))) 3).
  Compute (ftype_list_flip agt false nil).
  Compute (ftype_list_all agt nil).

  Notation ft_pmap := (CEP.t ftype).
  Notation ft_flp_pmap := (CEP.t (ftype * bool)).
  Notation ft_find := CEP.find.
  Definition ft_find_def v m := match ft_find v m with
                                | Some t => t
                                | None => (Gtyp (Fuint_implicit 1))
                                end.
  
  (* Record types from the output of inferwidth *)

  Fixpoint gen_pmap r cnt (tls : list ftype) (mt : ft_pmap) :=
    match tls with
    | nil => mt
    | cons t ts => (CEP.add (r.1, r.2+N.of_nat cnt)%num t (gen_pmap r (cnt.+1) ts mt))
    end.

  Fixpoint rcd_pmap_st (st: HiFP.hfstmt) (inf_mp : ft_pmap) (mt : ft_pmap) : ft_pmap :=
    match st with
    | Swire v t => gen_pmap v 0 (ftype_list_all (ft_find_def v inf_mp) nil) mt
    | Sreg v r => gen_pmap v 0 (ftype_list_all (ft_find_def v inf_mp) nil) mt
    | Snode v e => match (type_of_hfexpr e inf_mp) with
                   | Some et => gen_pmap v 0 (ftype_list_all et nil) mt
                   | None => mt
                   end
    | Swhen c s1 s2 => rcd_pmap_sts s2 inf_mp (rcd_pmap_sts s1 inf_mp mt)
    |_ => mt
    end
  with rcd_pmap_sts (st: HiFP.hfstmt_seq) (inf_mp : ft_pmap) (mt : ft_pmap) :=
         match st with
         | Qnil => mt
         | Qcons s sts => rcd_pmap_sts sts inf_mp (rcd_pmap_st s inf_mp mt)
         end.

  Definition rcd_pmap_p (inf_mp : ft_pmap) (ps: HiFP.hfport) (mt : ft_pmap) : ft_pmap :=
    match ps with
    | Finput v t => gen_pmap v 0 (ftype_list_all (ft_find_def v inf_mp) nil) mt
    | Foutput v t => gen_pmap v 0 (ftype_list_all (ft_find_def v inf_mp) nil) mt
    end.

  Definition rcd_pmap_ps (ps: seq HiFP.hfport) (inf_mp : ft_pmap) (mt : ft_pmap) : ft_pmap :=
    fold_right (rcd_pmap_p inf_mp) mt ps.

  Definition rcd_pmap_m m inf_mp mt : ft_pmap :=
    match m with
    | FInmod v ps sts => rcd_pmap_sts sts inf_mp (rcd_pmap_ps ps inf_mp mt)
    | _ => mt
    end.

  (* Record types according to firrtl modules *)
  
  Fixpoint rcd_pmap_from_st (st: HiFP.hfstmt) (mt : ft_pmap) : ft_pmap :=
    match st with
    | Swire v t => gen_pmap v 0 (ftype_list_all t nil) mt
    | Sreg v r => gen_pmap v 0 (ftype_list_all (type r) nil) mt
    | Snode v e =>  match (type_of_hfexpr e mt) with
                   | Some et => gen_pmap v 0 (ftype_list_all et nil) mt
                   | None => mt
                   end
    | Swhen c s1 s2 => rcd_pmap_from_sts s2 (rcd_pmap_from_sts s1 mt)
    |_ => mt
    end
  with rcd_pmap_from_sts (st: HiFP.hfstmt_seq) (mt : ft_pmap) :=
         match st with
         | Qnil => mt
         | Qcons s sts => rcd_pmap_from_sts sts (rcd_pmap_from_st s mt)
         end.

  Definition rcd_pmap_from_p (ps: HiFP.hfport) (mt : ft_pmap) : ft_pmap :=
    match ps with
    | Finput v t => gen_pmap v 0 (ftype_list_all t nil) mt
    | Foutput v t => gen_pmap v 0 (ftype_list_all t nil) mt
    end.

  Definition rcd_pmap_from_ps (ps: seq HiFP.hfport) (mt : ft_pmap) : ft_pmap :=
    fold_right rcd_pmap_from_p mt ps.

  Definition rcd_pmap_from_m m mt : ft_pmap :=
    match m with
    | FInmod v ps sts => rcd_pmap_from_sts sts (rcd_pmap_from_ps ps mt)
    | _ => mt
    end.
  
  Fixpoint qcat (s1 s2: HiFP.hfstmt_seq) : HiFP.hfstmt_seq :=
    match s1 with
    | Qnil => s2
    | Qcons x ss1 => Qcons x (qcat ss1 s2)
    end.

  (* Record flip info from the output of inferwidth *)
  
  Fixpoint gen_ft_pmap r cnt (tls : list (ftype * bool)) (mt : ft_flp_pmap) :=
    match tls with
    | nil => mt
    | cons t ts => (CEP.add (r.1, r.2+N.of_nat cnt)%num t (gen_ft_pmap r (cnt.+1) ts mt))
    end.

  Fixpoint rcd_flip_st (st: HiFP.hfstmt) (inf_mp : ft_pmap) (mt : ft_flp_pmap) : ft_flp_pmap :=
    match st with
    | Swire v t => gen_ft_pmap v 0 (ftype_list_flip (ft_find_def v inf_mp) false nil) mt
    | Sreg v r => gen_ft_pmap v 0 (ftype_list_flip (ft_find_def v inf_mp) false nil) mt
    | Snode v e => mt
    | Swhen c s1 s2 => rcd_flip_sts s2 inf_mp (rcd_flip_sts s1 inf_mp mt)
    |_ => mt
    end
  with rcd_flip_sts (st: HiFP.hfstmt_seq) (inf_mp : ft_pmap) (mt : ft_flp_pmap) :=
         match st with
         | Qnil => mt
         | Qcons s sts => rcd_flip_sts sts inf_mp (rcd_flip_st s inf_mp mt)
         end.

  Definition rcd_flip_p (inf_mp : ft_pmap) (ps: HiFP.hfport) (mt : ft_flp_pmap) : ft_flp_pmap :=
    match ps with
    | Finput v t => gen_ft_pmap v 0 (ftype_list_flip (ft_find_def v inf_mp) false nil) mt
    | Foutput v t => gen_ft_pmap v 0 (ftype_list_flip (ft_find_def v inf_mp) false nil) mt
    end.

  Definition rcd_flip_ps (ps: seq HiFP.hfport) (inf_mp : ft_pmap) (mt : ft_flp_pmap) : ft_flp_pmap :=
    fold_right (rcd_flip_p inf_mp) mt ps.

  Definition rcd_flip_m m inf_mp mt : ft_flp_pmap :=
    match m with
    | FInmod v ps sts => rcd_flip_sts sts inf_mp (rcd_flip_ps ps inf_mp mt)
    | _ => mt
    end.

  (* Record flip info according to firrtl module *)
  
  Fixpoint rcd_flip_from_st (st: HiFP.hfstmt) (mt : ft_flp_pmap) : ft_flp_pmap :=
    match st with
    | Swire v t => gen_ft_pmap v 0 (ftype_list_flip t false nil) mt
    | Sreg v r => gen_ft_pmap v 0 (ftype_list_flip (type r) false nil) mt
    | Snode v e => mt
    | Swhen c s1 s2 => rcd_flip_from_sts s2 (rcd_flip_from_sts s1 mt)
    |_ => mt
    end
  with rcd_flip_from_sts (st: HiFP.hfstmt_seq) (mt : ft_flp_pmap) :=
         match st with
         | Qnil => mt
         | Qcons s sts => rcd_flip_from_sts sts (rcd_flip_from_st s mt)
         end.
  
  Definition rcd_flip_from_p (ps: HiFP.hfport) (mt : ft_flp_pmap) : ft_flp_pmap :=
    match ps with
    | Finput v t => gen_ft_pmap v 0 (ftype_list_flip t false nil) mt
    | Foutput v t => gen_ft_pmap v 0 (ftype_list_flip t false nil) mt
    end.

  Definition rcd_flip_from_ps (ps: seq HiFP.hfport) (mt : ft_flp_pmap) : ft_flp_pmap :=
    fold_right rcd_flip_from_p mt ps.

  Definition rcd_flip_from_m m mt : ft_flp_pmap :=
    match m with
    | FInmod v ps sts => rcd_flip_from_sts sts (rcd_flip_from_ps ps mt)
    | _ => mt
    end.  

  (* Compute (ft_find (100,2)%num (rcd_flip_from_sts (Qcons (HiFP.swire (100,0)%num agt) (Qcons (HiFP.swire (101,0)%num agt) HiFP.qnil)) (CEP.empty (ftype * bool)))). *)
  
  (*recursively expand reference on rhs with ft_pmap*) 
  Fixpoint expand_eref_aux_ft_pmap (r : pvar) (sz : nat) (cnt : nat) (ce : ft_pmap) (rs : seq HiFP.hfexpr) : seq HiFP.hfexpr :=
    match sz with
    | 0 => rs
    | S n => match (ft_find (r.1, (r.2 + N.of_nat cnt)%num) ce) with
             | Some t => if is_gtyp t
                              then expand_eref_aux_ft_pmap r n (cnt.+1) ce (rcons rs (HiFP.eref (HiFP.eid (r.1, r.2 + N.of_nat cnt)%num)))
                              else expand_eref_aux_ft_pmap r n (cnt.+1) ce rs
             | None => rs
             end                                              
    end.

  Definition expand_eref_ft_pmap (r : pvar) (ce : ft_pmap) l : seq HiFP.hfexpr :=
    match (ft_find r ce) with
    | Some t =>
        let ts := ftype_list_all t nil in
        let sz := size ts in
        expand_eref_aux_ft_pmap r sz 0 ce l
    | None => l
    end.


  (*recursively expand mux, output a sequence of expressions*) 
  Fixpoint expand_emux (c : HiFP.hfexpr) (ze : seq (HiFP.hfexpr * HiFP.hfexpr)) (es : seq HiFP.hfexpr) : seq HiFP.hfexpr :=
    match ze with
    | nil => es
    | (e1, e2) :: zes => expand_emux c zes (rcons es (HiFP.emux c e1 e2))
    end.
  
  (*recursively expand expr on rhs*) 
  Fixpoint expand_expr_ft_pmap (e : HiFP.hfexpr) (ce : ft_pmap) (es : seq HiFP.hfexpr) : seq HiFP.hfexpr :=
    match e with
    | Eref (Eid (r, o)) => expand_eref_ft_pmap (r, o) ce es
    | Emux c e1 e2 => expand_emux c (zip (* (HiFP.econst (Fuint 0) nil) (HiFP.econst (Fuint 0) nil) *) (expand_expr_ft_pmap e1 ce nil) (expand_expr_ft_pmap e2 ce nil)) es
    (* | Evalidif c e => expand_evalidif c (expand_expr e ce nil) es *)
    | Eref _ => rcons es (HiFP.econst (Fuint 0) [::])
    | e => rcons es e
    end.

  (* Expand connections by creating new connections from the lists of lhs and rhs *)
  Fixpoint expand_fcnct es1 es2 (mt : ft_flp_pmap) (l : HiFP.hfstmt_seq)  : HiFP.hfstmt_seq :=
    match es1, es2 with
    | cons (Eref (Eid v)) ess1, cons ee2 ess2 =>
        match (ft_find v mt) with
        | Some (t, true) =>
            match ee2 with
            | Eref (Eid v2) => expand_fcnct ess1 ess2 mt (Qrcons l (Sfcnct (Eid v2) (Eref (Eid v)) ))
            | _ => l
            end
        | Some (t, false) => expand_fcnct ess1 ess2 mt (Qrcons l (Sfcnct (Eid v) ee2) )
        | None => l
        end
    | _, _ => l
    end.

  (* Expand wires *)
  Fixpoint expand_wire_aux (r : pvar) (sz : nat) (cnt : nat) (ce : ft_pmap) (rs : HiFP.hfstmt_seq) : HiFP.hfstmt_seq :=
    match sz with
    | 0 => rs
    | S n => match (ft_find (r.1, (r.2 + N.of_nat cnt)%num) ce) with
             | Some t => if is_gtyp t
                              then expand_wire_aux r n (cnt.+1) ce (Qrcons rs (HiFP.swire (r.1, r.2 + N.of_nat cnt)%num t))
                              else expand_wire_aux r n (cnt.+1) ce rs
             | None => rs
             end                                              
    end.

  Definition expand_wire (r : pvar) t ce l : HiFP.hfstmt_seq :=
        let ts := ftype_list_all t nil in
        let sz := size ts in
        expand_wire_aux r sz 0 ce l.

  (* Expand registers *)
  Fixpoint expand_reg_aux_nrst (r : pvar) (sz : nat) (cnt : nat) cl (ce : ft_pmap) (rs : HiFP.hfstmt_seq) : HiFP.hfstmt_seq :=
    match sz with
    | 0 => rs
    | S n => match (ft_find (r.1, (r.2 + N.of_nat cnt)%num) ce) with
             | Some t => if is_gtyp t
                               then expand_reg_aux_nrst r n (cnt.+1) cl ce (Qrcons rs (HiFP.sreg (r.1, r.2 + N.of_nat cnt)%num (mk_freg t cl (NRst _))))
                               else expand_reg_aux_nrst r n (cnt.+1) cl ce rs
             | None => rs
             end                                              
    end.

  Fixpoint expand_reg_aux_rst (r : pvar) (sz : nat) (cnt : nat) cl c es (ce : ft_pmap) (rs : HiFP.hfstmt_seq) : HiFP.hfstmt_seq :=
    match sz with
    | 0 => rs
    | S n => match (ft_find (r.1, (r.2 + N.of_nat cnt)%num) ce) with
             | Some t => if is_gtyp t
                         then expand_reg_aux_rst r n (cnt.+1) cl c es ce (Qrcons rs (HiFP.sreg (r.1, r.2 + N.of_nat cnt)%num (mk_freg t cl (Rst c (nth (HiFP.eref (HiFP.eid (0,0)%num)) es cnt.-1)))))
                         else expand_reg_aux_rst r n (cnt.+1) cl c es ce rs
             | None => rs
             end                                              
    end.

  Definition expand_reg (r : pvar) t mt l : HiFP.hfstmt_seq :=
    match t with
    | mk_freg tp cl NRst => 
        let ts := ftype_list_all tp nil in
        let sz := size ts in
        expand_reg_aux_nrst r sz 0 cl mt l
    | mk_freg tp cl (Rst c re) =>
        let ts := ftype_list_all tp nil in
        let sz := size ts in
        expand_reg_aux_rst r sz 0 cl c (expand_expr_ft_pmap re mt nil) mt l
    end.

  (* Expand Nodes *)
  (* If the node is not of passive types, then return nil for the rest *)
  Fixpoint expand_node_aux r sz cnt es (ce : ft_pmap) (rs : HiFP.hfstmt_seq)  : HiFP.hfstmt_seq :=
    match sz with
    | 0 => rs
    | S n => match (ft_find (r.1, (r.2 + N.of_nat cnt)%num) ce) with
             | Some t => if is_gtyp t
                         then expand_node_aux r n (cnt.+1) es ce (Qrcons rs (HiFP.snode (r.1, r.2 + N.of_nat cnt)%num (nth (HiFP.eref (HiFP.eid (0,0)%num)) es cnt.-1)))
                         else expand_node_aux r n (cnt.+1) es ce rs
             | None => rs
             end
    end.
  
  Fixpoint expand_node v e (mt : ft_pmap) (l : HiFP.hfstmt_seq) : HiFP.hfstmt_seq :=
    match ft_find v mt with
    | Some t => if ftype_is_passive t then
                  let ts := ftype_list_all t nil in
                  let sz := size ts in
                  expand_node_aux v sz 0 (expand_expr_ft_pmap e mt nil) mt l
                else l
    | None => l
    end.
  
  (* Expand statements *)
  (* If types not match, then returns qnil for the connections sts *)
  Fixpoint expandconnects_stmt_ft_pmap (s : HiFP.hfstmt) (ce : ft_pmap) (mt : ft_flp_pmap) (sts : HiFP.hfstmt_seq) : HiFP.hfstmt_seq :=
    match s with
    | Sskip => Qrcons sts s
    | Swire v t => expand_wire v t ce sts
    | Sreg v r => expand_reg v r ce sts
    | Smem _ _ =>Qrcons sts s
    | Sinvalid _=> Qrcons sts s
    | Sinst _ _=>Qrcons sts s
    | Snode v e => expand_node v e ce sts
    | Sfcnct (Eid r1) e2 =>
        match (ft_find r1 ce), (ft_find r1 ce) with
        | Some t1, Some t2 =>
        if ((~~ is_gtyp t1) && (t1 != t2)) then Qrcons sts s
        else
        (match e2 with
         | Eref _
         | Emux _ _ _ =>
             expand_fcnct (expand_expr_ft_pmap (Eref (Eid r1)) ce nil) (expand_expr_ft_pmap e2 ce nil) mt sts
         (* | Econst _ _ => Qrcons sts s *)
         | _ => Qrcons  sts s
         end)
        | _, _ => sts
        end
    | Sfcnct _ _ => sts
    | Swhen c s1 s2 => Qrcons sts (Swhen c (expandconnects_stmt_seq_ft_pmap s1 ce mt HiFP.qnil) (expandconnects_stmt_seq_ft_pmap s2 ce mt HiFP.qnil))
    end
      with expandconnects_stmt_seq_ft_pmap (ss : HiFP.hfstmt_seq) (ce : ft_pmap) (mt : ft_flp_pmap) (sts : HiFP.hfstmt_seq) : HiFP.hfstmt_seq :=
      match ss with
      | Qnil => sts
      | Qcons s ss => expandconnects_stmt_seq_ft_pmap ss ce mt (expandconnects_stmt_ft_pmap s ce mt sts)
    end.

  (* Expand ports *)
  Fixpoint expand_inport_aux (r : pvar) (sz : nat) (cnt : nat) (mt : ft_flp_pmap) (rs : seq HiFP.hfport) : seq HiFP.hfport :=
    match sz with
    | 0 => rs
    | S n => match (ft_find (r.1, (r.2 + N.of_nat cnt)%num) mt) with
             | Some (t, false) => if is_gtyp t
                              then expand_inport_aux r n (cnt.+1) mt (rcons rs (HiFP.hinport (r.1, r.2 + N.of_nat cnt)%num t))
                              else expand_inport_aux r n (cnt.+1) mt rs
             | Some (t, true) => if is_gtyp t
                              then expand_inport_aux r n (cnt.+1) mt (rcons rs (HiFP.houtport (r.1, r.2 + N.of_nat cnt)%num t))
                              else expand_inport_aux r n (cnt.+1) mt rs
             | None => rs
             end                                              
    end.

  Definition expand_inport (r : pvar) t mt l : seq HiFP.hfport :=
    let ts := ftype_list_all t nil in
    let sz := size ts in
    expand_inport_aux r sz 0 mt l.
  
  Fixpoint expand_outport_aux (r : pvar) (sz : nat) (cnt : nat) (mt : ft_flp_pmap) (rs : seq HiFP.hfport) : seq HiFP.hfport :=
    match sz with
    | 0 => rs
    | S n => match (ft_find (r.1, (r.2 + N.of_nat cnt)%num) mt) with
             | Some (t, false) => if is_gtyp t
                              then expand_outport_aux r n (cnt.+1) mt (rcons rs (HiFP.houtport (r.1, r.2 + N.of_nat cnt)%num t))
                              else expand_outport_aux r n (cnt.+1) mt rs
             | Some (t, true) => if is_gtyp t
                              then expand_outport_aux r n (cnt.+1) mt (rcons rs (HiFP.hinport (r.1, r.2 + N.of_nat cnt)%num t))
                              else expand_outport_aux r n (cnt.+1) mt rs
             | None => rs
             end                                              
    end.

  Definition expand_outport (r : pvar) t mt l : seq HiFP.hfport :=
        let ts := ftype_list_all t nil in
        let sz := size ts in
        expand_outport_aux r sz 0 mt l.

  Definition expand_ports mt p l :=
    match p with
    | Finput v t => expand_inport v t mt l
    | Foutput v t => expand_outport v t mt l
    end.

 Definition ft_flp_pmap_empty := CEP.empty (ftype * bool).
 Definition ft_pmap_empty := CEP.empty (ftype).
 
 (* Output a firrtl module *)
  Definition expandconnects_fmodule (m : HiFP.hfmodule) (inf_mp : ft_pmap) : HiFP.hfmodule :=
    match m with
    | FInmod v ps ss =>
        let mt := rcd_flip_m m inf_mp (ft_flp_pmap_empty) in
        let ce := rcd_pmap_m m inf_mp (ft_pmap_empty) in
        FInmod v (fold_right (expand_ports mt) nil ps) (expandconnects_stmt_seq_ft_pmap ss ce mt (HiFP.qnil ))
    | m => m
    end.

  (* Output a ft_pmap *)
  Definition output_ft_pmap m (inf_mp : ft_pmap) : ft_pmap :=
    rcd_pmap_m m inf_mp (CEP.empty ftype).

(* Examples *)
  
Definition test_sts1 := (HiFP.qcons (HiFP.swire (10%num,0%num) (Atyp (Gtyp (Fsint 10)) 5))
                               (HiFP.qcons (HiFP.swire (11%num,0%num) (Atyp (Gtyp (Fsint 10)) 5))
                                  (HiFP.qcons (HiFP.sfcnct (HiFP.eid (10%num,0%num)) (HiFP.eref (HiFP.eid (9%num,0%num)))) HiFP.qnil))).

Definition test_sts2 := (HiFP.qcons (HiFP.swire (10%num,0%num) (Atyp (Gtyp (Fsint 10)) 5))
                               (HiFP.qcons (HiFP.snode (11%num,0%num) (HiFP.eref (HiFP.eid (10,0)%num)))
                                  (HiFP.qcons (HiFP.sfcnct (HiFP.eid (11%num,0%num)) (HiFP.eref (HiFP.eid (11%num,0%num)))) HiFP.qnil))).

Definition test_module := HiFP.hfinmod (100%num,0%num) nil test_sts2.

Compute (expandconnects_fmodule test_module (rcd_pmap_from_m test_module ft_pmap_empty)).

 Definition test_ports0 := [:: HiFP.hinport (9%num, 0%num) (Atyp (Gtyp (Fsint 10)) 5)].
 Definition test_ports_map := rcd_pmap_from_ps test_ports0 ft_pmap_empty.

 Definition test_module0 := HiFP.hfinmod (101%num,0%num) test_ports0 test_sts1.
 
 Compute (expandconnects_fmodule test_module0 (rcd_pmap_from_m test_module0 ft_pmap_empty)).

 Definition test_flip_ports := [:: HiFP.houtport (8%num, 0%num) agt].
 Definition test_flip_module := HiFP.hfinmod (102%num,0%num) test_flip_ports HiFP.qnil.
 
 Compute (expandconnects_fmodule test_flip_module (rcd_pmap_from_m test_flip_module ft_pmap_empty)).

 (* reg regVec : UInt<1>[8], clock with :
      reset => (UInt<1>("h0"), regVec) @[ScalaGen.scala 10:19] *)
 Definition test_ports7 := [:: HiFP.hinport (8%num, 0%num) (Gtyp Fclock)].
 Definition test_sts7 :=
   (HiFP.qcons
      (HiFP.sreg (10%num,0%num)
         (mk_freg (Atyp (Gtyp (Fuint 2)) 8)
            (Eref (HiFP.eid (8%num, N0)))
            (Rst (HiFP.econst (Fuint 1) [:: true])
               (Eref (HiFP.eid (10%num, N0))))))
      HiFP.qnil).

 Definition test_module7 := HiFP.hfinmod (101%num,0%num) test_ports7 test_sts7.
 Compute (expandconnects_fmodule test_module7 (rcd_pmap_from_m test_module7 ft_pmap_empty)).

 (* wire signed : SInt<3> @[UIntVsU.scala 15:27]
    signed <= asSInt(UInt<3>("h7")) @[UIntVsU.scala 15:27] *)
 Definition test_sts8 :=
   (HiFP.qcons
      (HiFP.swire (10%num,0%num) (Gtyp (Fsint 3)))
      (HiFP.qcons (HiFP.sfcnct (HiFP.eid (10%num,0%num))
         (HiFP.ecast AsSInt (HiFP.econst (Fuint 3) [:: true; true; true])))
         HiFP.qnil)).
 Definition test_module8 := HiFP.hfinmod (101%num,0%num) [::] test_sts8.
 Compute (expandconnects_fmodule test_module8 (rcd_pmap_from_m test_module8 ft_pmap_empty)).
 
End ExpandConnectsP.
(* (vm_old : module_graph_vertex_set_p.env) (ct_old : module_graph_connection_trees_p.env) (s : HiFP.hfstmt) (vm_new : module_graph_vertex_set_p.env) (ct_new : module_graph_connection_trees_p.env) (tmap : ft_pmap) *)
  
(*   Lemma ExpandConnects_skip_correct : *)
(*     forall vm_old ct_old vm_new ct_new tmap tfmap ss0, *)
(*       Sem_frag_stmts vm_old ct_old (expandconnects_stmt_ft_pmap HiFP.sskip tmap tfmap ss0) vm_new ct_new tmap -> *)
(*       Sem_frag_stmts vm_old ct_old (Qrcons ss0 HiFP.sskip) vm_new ct_new tmap. *)
(*   Proof. *)
(*     rewrite /=//. *)
(*   Qed. *)

(*   Lemma expand_fcnct_rcons : *)
(*     forall v1 sz1 v2 sz2 ofs1 ofs2 tm ss0 tfm ss, *)
(*     expand_fcnct *)
(*        (expand_eref_aux_ft_pmap v1 sz1 ofs2 tm ss0) *)
(*        (expand_eref_aux_ft_pmap v2 sz2 ofs2 tm ss0) *)
(*        tfm ss = *)
(*       qcat ss (expand_fcnct *)
(*               (expand_eref_aux_ft_pmap v1 sz1 ofs1 tm ss0) *)
(*               (expand_eref_aux_ft_pmap v2 sz2 ofs2 tm ss0) *)
(*               tfm HiFP.qnil). *)
(*   Proof. Admitted. *)

(*   Lemma sem_frag_stmts_cat : *)
(*     forall vm0 ct0 s1 s2 vm1 ct1 tm vm' ct', *)
(*       Sem_frag_stmts vm0 ct0 (qcat s1 s2) vm1 ct1 tm <-> *)
(*         (* exists vm' ct' , *) Sem_frag_stmts vm0 ct0 s1 vm' ct' tm /\ Sem_frag_stmts vm' ct' s2 vm1 ct1 tm. *)
(*   Proof. Admitted. *)

(*   Lemma sem_frag_stmts_rcons : *)
(*     forall vm0 ct0 ss st vm' ct' tm vm1 ct1, *)
(*     Sem_frag_stmts vm0 ct0 *)
(*     (Qrcons ss st) *)
(*     vm' ct' tm <-> *)
(*       (* exists vm1 ct1,  *)Sem_frag_stmt vm1 ct1 st vm' ct' tm /\ Sem_frag_stmts vm0 ct0 ss vm1 ct1 tm. *)
(*   Proof. Admitted. *)
  
(*   Lemma ExpandConnects_fcnct_eideid_correct : *)
(*     forall ct0 vm0 ct1 vm_new ct_new tmap tfmap ss0 r1 o1 r2 o2 , *)
(*       Sem_frag_stmt vm_new ct1 ((HiFP.sfcnct (HiFP.eid (r1, o1)) (HiFP.eref(HiFP.eid (r2, o2))))) vm_new ct_new tmap -> *)
(*       Sem_frag_stmts vm0 ct0 ss0 vm_new ct1 tmap -> *)
(*       Sem_frag_stmts vm0 ct0 (expandconnects_stmt_ft_pmap (HiFP.sfcnct (HiFP.eid (r1, o1)) (HiFP.eref(HiFP.eid (r2, o2)))) tmap tfmap ss0) vm_new ct_new tmap -> *)
(*       Sem_frag_stmts vm0 ct0 (Qrcons ss0 (HiFP.sfcnct (HiFP.eid (r1, o1)) (HiFP.eref(HiFP.eid (r2, o2))))) vm_new ct_new tmap. *)
(*   Proof. *)
(*     intros ct0 vm0 ct1 vm' ct' tm tfm ss0 r1 o1 r2 o2. rewrite /=.  *)
(*     move => [Hequal]. *)
(*     case Hfd1 : (ft_find (r1, o1) tm ) => [tr1|]; rewrite /=//. *)
(*     case Hfd2 : (ft_find (r2, o2) tm ) => [tr2|]; rewrite /=//. *)
(*     move => [Hcc [Hc Hin]]. *)
(*     rewrite /expand_eref_ft_pmap Hfd1 Hfd2/=. *)
(*     intro Hsfsex. *)
(*     rewrite (sem_frag_stmts_rcons _ _ _ _ _ _ _ vm' ct1). *)
(*     intros Hexp. *)
(*     split; last exact Hsfsex. *)
(*     move : Hexp. *)
(*     rewrite (expand_fcnct_rcons _ _ _ _ 0 0 _ _ _ _). *)
(*     rewrite (sem_frag_stmts_cat _ _ _ _ _ _ _ vm' ct1). *)
(*     move => [Hred Hexp]. *)
(*     rewrite /=. *)
(*     split; try done. *)
(*     rewrite Hfd1 Hfd2. *)
(*     split. exact Hcc. *)
(*     split. exact Hc. *)
(*     exact Hin. *)
(*   Qed. *)
  
(* Print ftype_explicit. Print ftype_not_implicit_width. *)
(*   Lemma ExpandConnects_fcnct_eidemux_correct : *)
(*     forall ct0 vm0 ct1 vm_new ct_new tmap tfmap ss0 r1 o1 ec e1 e2 et1 et2, *)
(*       Sem_frag_stmt vm_new ct1 (HiFP.sfcnct (HiFP.eid (r1, o1)) (HiFP.emux ec e1 e2)) vm_new ct_new tmap -> *)
(*       (type_of_expr ec tmap) = Some (exist ftype_not_implicit_width (Gtyp (Fuint 1)) I)-> *)
(*       type_of_expr e1 tmap  = Some et1 -> *)
(*       type_of_expr e2 tmap  = Some et2 -> *)
(*       Sem_frag_stmts vm0 ct0 ss0 vm_new ct1 tmap -> *)
(*       Sem_frag_stmts vm0 ct0 (expandconnects_stmt_ft_pmap (HiFP.sfcnct (HiFP.eid (r1, o1)) (HiFP.emux ec e1 e2)) tmap tfmap ss0) vm_new ct_new tmap -> *)
(*       Sem_frag_stmts vm0 ct0 (Qrcons ss0 (HiFP.sfcnct (HiFP.eid (r1, o1)) (HiFP.emux ec e1 e2))) vm_new ct_new tmap. *)
(*   Proof. *)
(*     intros ct0 vm0 ct1 vm' ct' tm tfm ss0 r1 o1 ec e1 e2 te1 te2; rewrite /=. *)
(*     move => [Hequal]. *)
(*     case Hfd1 : (ft_find (r1, o1) tm ) => [tr1|]; rewrite /=//. *)
(*     intros Hmod Htyp Htyp1 Htyp2.  *)
(*     move : Hmod. rewrite Htyp Htyp1 Htyp2/=. *)
(*     case Htypm : (ftype_mux te1 te2 ) => [[typm Hm]|].  *)
(*     move => [Hmod Hin]. *)
(*     move : Hin. *)
(*     move : Hmod Htypm. *)
(*     destruct typm => Hmg. rewrite /=. *)
(*     rewrite /expand_eref_ft_pmap Hfd1 Hfd2/=. *)
(*     intro Hsfsex. *)
(*     rewrite (sem_frag_stmts_rcons _ _ _ _ _ _ _ vm' ct1). *)
(*     intros Hexp. *)
(*     split; last exact Hsfsex. *)
(*     move : Hexp. *)
(*     rewrite (expand_fcnct_rcons _ _ _ _ 0 0 _ _ _ _). *)
(*     rewrite (sem_frag_stmts_cat _ _ _ _ _ _ _ vm' ct1). *)
(*     move => [Hred Hexp]. *)
(*     rewrite /=. *)
(*     split; try done. *)
(*     rewrite Hfd1 Hfd2. *)
(*     split. exact Hcc. *)
(*     split. exact Hc. *)
(*     exact Hin. *)
(*   Qed. *)
