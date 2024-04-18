From Coq Require Import ZArith (* for Nat.eq_dec *).
From simplssrlib Require Import SsrOrder FMaps Nats Var ZAriths.
From nbits Require Import NBits.
From firrtl Require Import Env Firrtl HiEnv HiFirrtl. (* for hfmodule and its parts *)
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq fintype div.

(* This file contains a simpler version of module graphs as a semantic structure for FIRRTL modules.
   The idea is to have vertices that correspond to ground-type components
   (mainly registers, wires, ports, nodes) in the graph,
   but instead of edges have expressions. *)




(*****************************************************************************)
(*                                                                           *)
(*                          M O D U L E   G R A P H S                        *)
(*                                                                           *)
(*****************************************************************************)


(*---------------------------------------------------------------------------*)
(* Vertices                                                                  *)

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
Proof.  decide equality ; try apply fgtyp_eq_dec. decide equality. apply rst_eq_dec. apply hfexpr_eq_dec. Qed.
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
    (tx == ty) && (cx == cy) && (rx == ry) && (bx == by_)
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




(*---------------------------------------------------------------------------*)
(* Connection expressions                                                    *)

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


(* The type of a connection tree is CEP.t def_expr.
   Note that an input/output connector is now just identified with CEP.key,
   no longer with PProdVarOrder.T. *)
(* for connection_tree, whose key is (N_pair, N) as input_connector_id
   here this module produce ProdOrder like ((N,N),N) *)
(*Module MakeProdOrderWithDefaultSucc2 (O1 O2 : SsrOrderWithDefaultSucc) <: SsrOrderWithDefaultSucc
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
End MakeProdOrderWithDefaultSucc2.*)

(* can be identifier of a input/output_connector *)

(*
Module PProdVarOrder := MakeProdOrder ProdVarOrder VarOrder.

Module MakeCnctFMap (V : SsrOrder) (VM : SsrFMap with Module SE := V)
<: SsrFMap with Module SE := V.
  Include VM.
  Include FMapLemmas VM.
  Definition env : Type := t def_expr.
End MakeCnctFMap.

Module PPVM <: SsrFMap := FMaps.MakeTreeMap PProdVarOrder.
Module module_graph_connection_trees_p <: SsrFMap := MakeCnctFMap PProdVarOrder PPVM.
*)



(*****************************************************************************)
(*                                                                           *)
(*             E X P R E S S I O N S   A N D   T Y P E   M A P S             *)
(*                                                                           *)
(*****************************************************************************)


(*---------------------------------------------------------------------------*)
(* Find the type of different kinds of expressions                           *)

(* The functions in this part mostly rely on the tmap, the type map based on
   the ports and statements in the module.  Note that the module graph might
   contain different widths for implicit-width components. *)

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
(* Find the tmap of ports and of statements                                  *)

(* Tmaps store the type of every component in a module.  The type information
   is taken from the module, but the width is corrected according to the
   module graph. *)

Definition code_vm_type_equivalent (code_type : fgtyp) (graph_type : fgtyp) : bool :=
(* check whether types code_type and graph_type are equivalent.
   graph_type should be allowed in a module graph (i.e. it cannot be Freset). *)
match code_type, graph_type with
| Fuint w1, Fuint w2
| Fsint w1, Fsint w2 => w1 == w2
| Fuint_implicit _, Fuint_implicit _
| Fsint_implicit _, Fsint_implicit _
| Fclock, Fclock
| Freset, Fuint 1
| Freset, Fasyncreset
| Fasyncreset, Fasyncreset => true
| _, _ => false
end.

Fixpoint code_type_find_vm_widths (code_t : ftype) (v : ProdVarOrder.T) (vm : CEP.t vertex_type) : option (ftype * N) :=
(* find the widths of types used in vm for a component that was declared with type code_t in the code.
   The module graph vertices (v, n), (v, n+1), (v, n+2), ... contain the relevant ground-type subcomponents.
   That means, the module graph vertices should contain ground-type elements as given by code_vm_type_equivalent.
   The result is a pair:
   - the type with widths adapted
   - the new index for n (where the next subcomponent would be found after handling code_t)
     (i.e. n + size_of_ftype code_t)
   If there is some error, the result is None instead.
   We allow non-passive types.
   Note that in most cases, the type of the output of the component is used,
   but for OutPorts we use the type of the input (because an out-port has no output connector). *)
match code_t with
| Gtyp oldgt =>
    match CEP.find v vm with
    | Some (OutPort newgt)
    | Some (InPort newgt)
    | Some (Register newgt _ _ _)
    | Some (Wire newgt)
    | Some (Node newgt) =>
        if code_vm_type_equivalent oldgt newgt
        then Some (Gtyp newgt, bin_of_nat (snd v + 1))
        else None
    | None => None
    end
| Atyp code_t' m =>
    (* check the first copy, and then verify that the next m-1 copies have exactly the same types *)
    match code_type_find_vm_widths code_t' v vm with
    | Some (graph_t', new_n) =>
        (* Now check that there are another m-1 copies that are identical *)
        let elsize := N.sub new_n (snd v) in
        if [forall i : ordinal ((m-1) * elsize),
               CEP.find (fst v, N.add (snd v) (bin_of_nat i)) vm ==
               CEP.find (fst v, N.add new_n   (bin_of_nat i)) vm   ]
        then Some (Atyp graph_t' m, N.add (snd v) (N.mul (bin_of_nat m) elsize))
        else None
    | None => None
    end
| Btyp code_ff => code_ffield_find_vm_widths code_ff v vm
end
with code_ffield_find_vm_widths (code_ff : ffield) (v : ProdVarOrder.T) (vm : CEP.t vertex_type) : option (ftype * N) :=
match code_ff with
| Fnil => Some (Btyp Fnil, snd v)
| Fflips f flp code_t code_ff' =>
    match code_type_find_vm_widths code_t v vm with
    | Some (graph_t, n') =>
        match code_ffield_find_vm_widths code_ff' (fst v, n') vm with
        | Some (Btyp graph_ff, n'') =>
            Some (Btyp (Fflips f flp graph_t graph_ff), n'')
        | _ => None
        end
    | None => None
    end
end.

Fixpoint ports_tmap (pp : seq HiFP.hfport) (vm : CEP.t vertex_type) : option (CEP.t ftype) :=
(* creates a tmap that contains exactly the types of the ports in pp. *)
match pp with
| [::] => Some (CEP.empty ftype)
| Finput v t :: pp'
| Foutput v t :: pp' =>
    match code_type_find_vm_widths t v vm, ports_tmap pp' vm with
    | Some (newt, _), Some tmap' =>
        match CEP.find v tmap' with
        | Some _ => None
        | None => Some (CEP.add v newt tmap')
        end
    | _, _ => None
    end
end.

Fixpoint ports_names (pp : seq HiFP.hfport) : seq CEP.key :=
match pp with
| [::] => [::]
| Finput  v _ :: pp'
| Foutput v _ :: pp' => v :: (ports_names pp')
end.

Lemma ports_tmap_names :
forall (vm : CEP.t vertex_type) (pp : seq HiFP.hfport),
    match ports_tmap pp vm with
    | Some tmap =>
        (* the domain of tmap is ports_names pp *)
        forall y : CEP.key,
            y \in ports_names pp <-> CEP.find y tmap <> None
    | None => True
    end.
Proof.
induction pp.
* unfold ports_tmap, ports_names.
  intro ; rewrite in_nil ; split ; first by done.
  intro ; contradict H.
  specialize (CEP.empty_1 (elt := ftype) (a := y)) ; intro.
  specialize (CEP.find_2 (m := CEP.empty ftype) (x := y)) ; intro.
  destruct (CEP.find y (CEP.empty ftype)) ; try by done.
  specialize (H f) ; specialize (H0 f Logic.eq_refl) ; by contradiction.
* simpl ports_tmap ; simpl ports_names.
  destruct a, (code_type_find_vm_widths f s vm) ; try by done.
  1,2: destruct p as [newt _].
  1,2: destruct (ports_tmap pp vm) as [tmap|] ; try by done.
  1,2: destruct (CEP.find s tmap) eqn: Hfind ; try by done.
  1,2: intro ; specialize (IHpp y).
  1,2: rewrite in_cons.
  1,2: destruct (y == s) eqn: Hys.
  1,3: move /eqP : Hys => Hys ;
       rewrite orTb Hys CEP.Lemmas.find_add_eq // /PVM.SE.eq eq_refl //.
  1,2: rewrite orFb CEP.Lemmas.find_add_neq // /PVM.SE.eq Hys //.
Qed.

Lemma ports_tmap_uniq :
forall (vm : CEP.t vertex_type) (pp : seq HiFP.hfport),
    match ports_tmap pp vm with
    | Some _ => uniq (ports_names pp)
    | None => true
    end.
Proof.
induction pp ; first by (unfold ports_tmap, ports_names, uniq ; done).
simpl ports_tmap ; simpl ports_names.
destruct a, (code_type_find_vm_widths f s vm) ; try by done.
1,2: destruct p as [newt _].
1,2: specialize (ports_tmap_names vm pp) ; intro.
1,2: destruct (ports_tmap pp vm) ; try by done.
1,2: specialize (H s).
1,2: destruct (CEP.find s t) ; try by done.
1,2: destruct H as [H _].
1,2: simpl uniq.
1,2: rewrite IHpp andbT.
1,2: destruct (s \in ports_names pp) eqn: Hpn ; try by done.
1,2,3,4: rewrite Hpn ; try by done.
1,2: rewrite Hpn in H ; specialize (H is_true_true) ; done.
Qed.

Fixpoint stmts_tmap (tmap_scope : CEP.t ftype * CEP.t ftype) (ss : HiFP.hfstmt_seq) (vm : CEP.t vertex_type) : option (CEP.t ftype * CEP.t ftype) :=
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
    match stmt_tmap tmap_scope s vm with
    | Some tmap_scope' => stmts_tmap tmap_scope' ss' vm
    | None => None
    end
end
with stmt_tmap (tmap_scope : CEP.t ftype * CEP.t ftype) (s : HiFP.hfstmt) (vm : CEP.t vertex_type) : option (CEP.t ftype * CEP.t ftype) :=
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
    match CEP.find v (fst tmap_scope), code_type_find_vm_widths t v vm with
    | None, Some (newt, _) =>
        Some (CEP.add v newt (fst tmap_scope), CEP.add v newt (snd tmap_scope))
    | _, _ => None (* identifier v is used multiple times, or the module graph does not fit *)
    end
| Sreg v reg =>
    match CEP.find v (fst tmap_scope), type_of_expr (clock reg) (snd tmap_scope), code_type_find_vm_widths (type reg) v vm with
    | None, Some _, Some (newt, _) =>
        if reset reg is Rst rst_sig rst_val
        then match type_of_expr rst_sig (snd tmap_scope), type_of_expr rst_val (snd tmap_scope) with
             | Some _, Some _ => Some (CEP.add v newt (fst tmap_scope), CEP.add v newt (snd tmap_scope))
             | _, _ => None (* something undefined or out-of-scope is accessed *)
             end
        else Some (CEP.add v newt (fst tmap_scope), CEP.add v newt (snd tmap_scope))
    | _, _, _ => None (* identifier v is used multiple times, or the clock is out of scope, or the module graph does not fit *)
    end
| Snode v expr =>
    match CEP.find v (fst tmap_scope), type_of_expr expr (snd tmap_scope) with
    | None, Some (exist newt _) =>
        Some (CEP.add v newt (fst tmap_scope), CEP.add v newt (snd tmap_scope))
    | _, _ => None (* something undefined or out-of-scope is accessed, or identifier v is used multiple times *)
    end
| Smem _ _ => None
| Sinst _ _ => None
| Swhen cond ss_true ss_false =>
    match type_of_expr cond (snd tmap_scope), stmts_tmap tmap_scope ss_true vm with
    | Some _, Some (tmap_true, _) =>
        if stmts_tmap (tmap_true, snd tmap_scope) ss_false vm is Some (tmap_false, _)
        then Some (tmap_false, snd tmap_scope)
        else None (* there is an error in ss_false *)
    | _, _ => None (* cond accesses something undefined or out-of-scope, or there is an error in ss_true *)
    end
end.


(*---------------------------------------------------------------------------*)
(* Submaps                                                                   *)

(* Most of this has already been defined as CEP.submap etc.

Definition submap {T : Type} (t1 t2: CEP.t T) : Prop :=
forall v : ProdVarOrder.T,
   match CEP.find v t1 with
   | Some ft => CEP.find v t2 = Some ft
   | None => True
   end.

Lemma submap_refl {T : Type} : forall tmap : CEP.t T, submap tmap tmap.
Proof.
unfold submap ; intros.
destruct (CEP.find v tmap) ; done.
Qed.

Lemma submap_trans {T : Type} : forall t2 t1 t3 : CEP.t T, submap t1 t2 -> submap t2 t3 -> submap t1 t3.
Proof.
unfold submap ; intros.
specialize H with (v := v) ; specialize H0 with (v := v).
destruct (CEP.find v t1) ; last by trivial.
rewrite H in H0.
exact H0.
Qed.

Lemma submap_add {T : Type} : forall (tmap : CEP.t T) (v : CEP.key) (t : T),
   CEP.find v tmap = None -> submap tmap (CEP.add v t tmap).
Proof.
unfold submap.
intros.
destruct (v0 == v) eqn: Hv.
* rewrite CEP.Lemmas.find_add_eq ; last by rewrite /PVM.SE.eq Hv //.
  move /eqP : Hv => Hv ; rewrite Hv H //.
* rewrite CEP.Lemmas.find_add_neq ; last by rewrite /PVM.SE.eq Hv //.
  destruct (CEP.find v0 tmap) ; done.
Qed.

(* The following lemma is the same as CEP.Lemmas.submap_add_find_none. *)
Lemma submap_addl {T : Type} : forall (tmap1 tmap2 : CEP.t T) (v : CEP.key) (t : T),
    CEP.find v tmap1 = None -> submap (CEP.add v t tmap1) tmap2 -> submap tmap1 tmap2.
Proof.
unfold submap.
intros.
specialize (H0 v0).
destruct (v0 == v) eqn: Hv.
* move /eqP : Hv => Hv ; rewrite Hv H //.
* rewrite CEP.Lemmas.find_add_neq in H0 ; last by rewrite /PVM.SE.eq Hv //.
  exact H0.
Qed. *)

Lemma submap_add_add {T : Type} : forall (tmap1 tmap2 : CEP.t T) (v : CEP.key) (t : T),
   CEP.submap tmap1 tmap2 -> CEP.submap (CEP.add v t tmap1) (CEP.add v t tmap2).
Proof.
unfold CEP.submap, CEP.Lemmas.submap.
intros until 1 ; intro.
destruct (k == v) eqn: Hv.
* rewrite CEP.Lemmas.find_add_eq ; last by rewrite /HiFirrtl.PVM.SE.eq Hv //.
  rewrite CEP.Lemmas.find_add_eq ; last by rewrite /HiFirrtl.PVM.SE.eq Hv //.
  done.
* rewrite CEP.Lemmas.find_add_neq ; last by rewrite /HiFirrtl.PVM.SE.eq Hv //.
  rewrite CEP.Lemmas.find_add_neq ; last by rewrite /HiFirrtl.PVM.SE.eq Hv //.
  apply H.
Qed.

(*Lemma Equal_submap {T : Type} : forall (tmap1 tmap2 : CEP.t T),
    CEP.Equal tmap1 tmap2 -> submap tmap1 tmap2.
Proof.
intros.
intro.
specialize (H v).
rewrite H.
destruct (CEP.find v tmap2) ; done.
Qed.*)

Definition subdomain {T1 T2 : Type} (t1 : CEP.t T1) (t2 : CEP.t T2) : Prop :=
forall k : ProdVarOrder.T,
   match CEP.find k t2 with
   | None => CEP.find k t1 = None
   | Some _ => True
   end.

Lemma subdomain_refl {T : Type} : forall tmap : CEP.t T, subdomain tmap tmap.
Proof.
unfold subdomain ; intros.
destruct (CEP.find k tmap) ; done.
Qed.

Lemma subdomain_trans {T1 T2 T3 : Type} : forall (t2 : CEP.t T2) (t1 : CEP.t T1) (t3 : CEP.t T3), subdomain t1 t2 -> subdomain t2 t3 -> subdomain t1 t3.
Proof.
unfold subdomain ; intros.
specialize (H k) ; specialize (H0 k).
destruct (CEP.find k t3) ; first by trivial.
rewrite H0 in H.
exact H.
Qed.

(*---------------------------------------------------------------------------*)
(* Properties of type_of_ref and of type_of_expr                             *)

Lemma type_of_ref_submap : forall (ref : HiFP.href) (tmap1 tmap2 : CEP.t ftype),
   CEP.submap tmap1 tmap2 ->
   match type_of_ref ref tmap1 with
   | Some ft => type_of_ref ref tmap2 = Some ft
   | None => True
   end.
Proof.
intros.
induction ref ; simpl ; try trivial.
* specialize (H s).
  destruct (CEP.find s tmap1) ; last by trivial.
  specialize (H f Logic.eq_refl).
  exact H.
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

Lemma type_of_expr_submap : forall (expr : HiFP.hfexpr) (tmap1 tmap2 : CEP.t ftype),
   CEP.submap tmap1 tmap2 ->
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
* apply type_of_ref_submap with (ref := h) in H.
  destruct (type_of_ref h tmap1) ; try by trivial.
  rewrite H.
  by reflexivity.
Qed.

Lemma type_of_expr_Equal : forall (expr : HiFP.hfexpr) (tmap1 tmap2 : CEP.t ftype),
   CEP.Equal tmap1 tmap2 ->
   type_of_expr expr tmap1 = type_of_expr expr tmap2.
Proof.
intros.
generalize (type_of_expr_submap expr tmap1 tmap2
            (CEP.Lemmas.Equal_submap H)) ; intro.
apply CEP.Lemmas.Equal_sym in H.
generalize (type_of_expr_submap expr tmap2 tmap1
            (CEP.Lemmas.Equal_submap H)) ; intro.
destruct (type_of_expr expr tmap1) ; first by rewrite H0 //.
destruct (type_of_expr expr tmap2) ; done.
Qed.


Lemma stmts_submap:
   forall (vm : CEP.t vertex_type) (ss : HiFP.hfstmt_seq) (tmap scope : CEP.t ftype),
      CEP.submap scope tmap ->
         match stmts_tmap (tmap, scope) ss vm with
         | Some (tmap', scope') => CEP.submap scope' tmap' /\ CEP.submap tmap tmap' /\ CEP.submap scope scope'
         | None => True
         end
with stmt_submap :
   forall (vm : CEP.t vertex_type) (s : HiFP.hfstmt) (tmap scope : CEP.t ftype),
      CEP.submap scope tmap ->
         match stmt_tmap (tmap, scope) s vm with
         | Some (tmap', scope') => CEP.submap scope' tmap' /\ CEP.submap tmap tmap' /\ CEP.submap scope scope'
         | None => True
         end.
Proof.
* clear stmts_submap.
  induction ss.
  + unfold stmts_tmap.
    intros ; split ; first by exact H.
    by split ; apply CEP.Lemmas.submap_refl.
  + intros.
    simpl stmts_tmap.
    specialize stmt_submap with (vm := vm) (s := h) (tmap := tmap) (scope := scope).
    destruct (stmt_tmap (tmap, scope) h vm) as [[tmap' scope']|] ; last by trivial.
    specialize IHss with (tmap := tmap') (scope := scope').
    destruct (stmts_tmap (tmap', scope') ss vm) as [[tmap'' scope'']|] ; last by trivial.
    split.
    - apply IHss, stmt_submap, H.
    split.
    - apply (CEP.Lemmas.submap_trans (m2 := tmap')) ; first by apply stmt_submap.
      by apply IHss, stmt_submap, H.
    - apply (CEP.Lemmas.submap_trans (m2 := scope')) ; first by apply stmt_submap.
      by apply IHss, stmt_submap, H.
* clear stmt_submap.
  destruct s ; simpl ; intros ; try trivial.
  + (* Sskip *) split ; first by exact H.
    by split ; apply CEP.Lemmas.submap_refl.
  + (* Swire *)
    destruct (CEP.find s tmap) eqn: Hfind ; first by trivial.
    destruct (code_type_find_vm_widths f s vm) as [[newt _]|] ; last by trivial.
    split.
    - apply submap_add_add, H.
    split.
    - apply CEP.Lemmas.submap_none_add ; first by apply CEP.Lemmas.submap_refl.
      exact Hfind.
    - apply CEP.Lemmas.submap_none_add ; first by apply CEP.Lemmas.submap_refl.
      specialize (H s).
      destruct (CEP.find s scope) ; last by trivial.
      by rewrite -Hfind (H f0) //.
  + (* Sreg *)
    destruct (CEP.find s tmap) eqn: Hfind ; first by trivial.
    destruct (type_of_expr (clock h) scope) ; last by trivial.
    destruct (code_type_find_vm_widths (type h) s vm) as [[newt _]|] ; last by trivial.
    destruct (reset h).
    - split.
      * by apply submap_add_add, H.
      split.
      * apply CEP.Lemmas.submap_none_add ; first by apply CEP.Lemmas.submap_refl.
        exact Hfind.
      * apply CEP.Lemmas.submap_none_add ; first by apply CEP.Lemmas.submap_refl.
        specialize (H s).
        destruct (CEP.find s scope) ; last by trivial.
        by rewrite -Hfind (H f0) //.
    - destruct (type_of_expr h0 scope) ; last by trivial.
      destruct (type_of_expr h1 scope) ; last by trivial.
      split.
      * by apply submap_add_add, H.
      split.
      * apply CEP.Lemmas.submap_none_add ; first by apply CEP.Lemmas.submap_refl.
        exact Hfind.
      * apply CEP.Lemmas.submap_none_add ; first by apply CEP.Lemmas.submap_refl.
        specialize (H s).
        destruct (CEP.find s scope) ; last by trivial.
        by rewrite -Hfind (H f2) //.
  + (* Snode *)
    destruct (CEP.find s tmap) eqn: Hfind ; first by trivial.
    destruct (type_of_expr h scope) as [[newt _]|] ; last by trivial.
    split.
    - by apply submap_add_add, H.
    split.
    - apply CEP.Lemmas.submap_none_add ; first by apply CEP.Lemmas.submap_refl.
      exact Hfind.
    - apply CEP.Lemmas.submap_none_add ; first by apply CEP.Lemmas.submap_refl.
      specialize (H s).
      destruct (CEP.find s scope) ; last by trivial.
      by rewrite -Hfind (H f) //.
  + (* Sfcnct *)
    destruct (type_of_ref h scope) ; last by trivial.
    destruct (type_of_expr h0 scope) ; last by trivial.
    split.
    - by exact H.
    - split ; by apply CEP.Lemmas.submap_refl.
  + (* Sinvalid *)
    destruct (type_of_ref h scope) ; last by trivial.
    split.
    - by exact H.
    - split ; by apply CEP.Lemmas.submap_refl.
  + (* Swhen *)
    rename h0 into ss_true ; rename h1 into ss_false.
    destruct (type_of_expr h scope) ; last by trivial.
    generalize (stmts_submap vm ss_true tmap scope H) ; intro.
    destruct (stmts_tmap (tmap, scope) ss_true vm) as [[tmap_true scope_true]|] ; last by trivial.
    generalize (stmts_submap vm ss_false tmap_true scope (CEP.Lemmas.submap_trans H (proj1 (proj2 H0)))) ; intro.
    destruct (stmts_tmap (tmap_true, scope) ss_false vm) as [[tmap_false scope_false]|] ; last by trivial.
    split.
    - apply (CEP.Lemmas.submap_trans H).
      apply (CEP.Lemmas.submap_trans (proj1 (proj2 H0))).
      apply H1.
    split.
    - apply (CEP.Lemmas.submap_trans (proj1 (proj2 H0))).
      apply H1.
    - apply CEP.Lemmas.submap_refl.
Qed.

Lemma stmts_tmap_cat :
   forall (vm : CEP.t vertex_type) (ss1 ss2 : HiFP.hfstmt_seq) (tmap_scope : CEP.t ftype * CEP.t ftype),
      stmts_tmap tmap_scope (Qcat ss1 ss2) vm =
      match stmts_tmap tmap_scope ss1 vm with
      | Some tmap_scope' => stmts_tmap tmap_scope' ss2 vm
      | None => None
      end.
Proof.
induction ss1.
* simpl Qcat ; simpl stmts_tmap ; simpl.
  by intro ; reflexivity.
* simpl Qcat ; simpl stmts_tmap.
  intros.
  destruct (stmt_tmap tmap_scope h vm) ; last by reflexivity.
  by apply IHss1.
Qed.


(*---------------------------------------------------------------------------*)
(* component defining statements and their properties                        *)

Fixpoint component_stmts_of (ss : HiFP.hfstmt_seq) : HiFP.hfstmt_seq :=
(* extracts from ss the statements that define components *)
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

Lemma stmts_tmap_components :
   forall (vm : CEP.t vertex_type) (ss : HiFP.hfstmt_seq) (tmap scope1 scope2 : CEP.t ftype),
      CEP.submap scope1 tmap ->
      CEP.submap scope2 tmap ->
      CEP.submap scope1 scope2 ->
         match stmts_tmap (tmap, scope1) ss vm, stmts_tmap (tmap, scope2) (component_stmts_of ss) vm with
         | Some (tmap1', scope1'), Some (tmap2', scope2') =>
              tmap1' = tmap2' /\ CEP.submap scope1' scope2'
         | Some _, None => False
         | _, _ => True
         end
with stmt_tmap_components :
   forall (vm : CEP.t vertex_type) (s : HiFP.hfstmt) (tmap scope1 scope2 : CEP.t ftype),
      CEP.submap scope1 tmap ->
      CEP.submap scope2 tmap ->
      CEP.submap scope1 scope2 ->
         match stmt_tmap (tmap, scope1) s vm, stmts_tmap (tmap, scope2) (component_stmt_of s) vm with
         | Some (tmap1', scope1'), Some (tmap2', scope2') =>
              tmap1' = tmap2' /\ CEP.submap scope1' scope2'
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
    specialize (stmt_tmap_components vm h tmap scope1 scope2 H H0 H1).
    generalize (stmt_submap vm h tmap scope1 H) ;
          intro.
    destruct (stmt_tmap (tmap, scope1) h vm) as [[tmap'' scope1'']|] ;
          last by trivial.
    generalize (stmts_submap vm (component_stmt_of h) tmap scope2 H0) ;
          intro.
    destruct (stmts_tmap (tmap, scope2) (component_stmt_of h) vm) as [[tmap2'' scope2'']|].
    - rewrite -(proj1 stmt_tmap_components) ;
      rewrite -(proj1 stmt_tmap_components) in H3.
      apply IHss, stmt_tmap_components ; try assumption.
      * by apply (proj1 H2).
      * by apply (proj1 H3).
    - destruct (stmts_tmap (tmap'', scope1'') ss vm) as [[tmap1' scope1']|] ; last by trivial.
      contradiction stmt_tmap_components.
* clear stmt_tmap_components.
  intros.
  destruct s ; simpl ; try by done.
  + (* Swire *)
    destruct (CEP.find s tmap) ; first by trivial.
    destruct (code_type_find_vm_widths f s vm) as [[newt _]|] ; last by trivial.
    split ; first by reflexivity.
    intro.
    destruct (k == s) eqn: Hvs.
    - rewrite CEP.Lemmas.find_add_eq ; last by rewrite /HiFirrtl.PVM.SE.eq Hvs //.
      rewrite CEP.Lemmas.find_add_eq ; last by rewrite /HiFirrtl.PVM.SE.eq Hvs //.
      by done.
    - rewrite CEP.Lemmas.find_add_neq ; last by rewrite /HiFirrtl.PVM.SE.eq Hvs //.
      rewrite CEP.Lemmas.find_add_neq ; last by rewrite /HiFirrtl.PVM.SE.eq Hvs //.
      by apply H1.
  + (* Sreg *)
    destruct (CEP.find s tmap) ; first by trivial.
    destruct (type_of_expr (clock h) scope1) eqn: Hclk ; last by trivial.
    generalize (type_of_expr_submap (clock h) scope1 scope2 H1) ; intro ;
          rewrite Hclk in H2.
    destruct (code_type_find_vm_widths (type h) s vm) as [[newt _]|] ; last by trivial.
    destruct (reset h).
    - rewrite H2.
      split ; first by reflexivity.
      intro.
      destruct (k == s) eqn: Hvs.
      * rewrite CEP.Lemmas.find_add_eq ; last by rewrite /HiFirrtl.PVM.SE.eq Hvs //.
        rewrite CEP.Lemmas.find_add_eq ; last by rewrite /HiFirrtl.PVM.SE.eq Hvs //.
        by done.
      * rewrite CEP.Lemmas.find_add_neq ; last by rewrite /HiFirrtl.PVM.SE.eq Hvs //.
        rewrite CEP.Lemmas.find_add_neq ; last by rewrite /HiFirrtl.PVM.SE.eq Hvs //.
        by apply H1.
    - destruct (type_of_expr h0 scope1) eqn: Hte0 ; last by trivial.
      generalize (type_of_expr_submap h0 scope1 scope2 H1) ;
            intro ; rewrite Hte0 in H3.
      destruct (type_of_expr h1 scope1) eqn: Hte1 ; last by trivial.
      generalize (type_of_expr_submap h1 scope1 scope2 H1) ;
            intro ; rewrite Hte1 in H4.
      rewrite H2 H3 H4.
      split ; first by reflexivity.
      intro.
      destruct (k == s) eqn: Hvs.
      * rewrite CEP.Lemmas.find_add_eq ; last by rewrite /HiFirrtl.PVM.SE.eq Hvs //.
        rewrite CEP.Lemmas.find_add_eq ; last by rewrite /HiFirrtl.PVM.SE.eq Hvs //.
        by done.
      * rewrite CEP.Lemmas.find_add_neq ; last by rewrite /HiFirrtl.PVM.SE.eq Hvs //.
        rewrite CEP.Lemmas.find_add_neq ; last by rewrite /HiFirrtl.PVM.SE.eq Hvs //.
        by apply H1.
  + (* Snode *)
    destruct (CEP.find s tmap) ; first by trivial.
    destruct (type_of_expr h scope1) as [[newt p]|] eqn: Hte ; last by trivial.
    generalize (type_of_expr_submap h scope1 scope2 H1) ;
          intro ; rewrite Hte in H2.
    rewrite H2.
    split ; first by reflexivity.
    intro.
    destruct (k == s) eqn: Hvs.
    - rewrite CEP.Lemmas.find_add_eq ; last by rewrite /HiFirrtl.PVM.SE.eq Hvs //.
      rewrite CEP.Lemmas.find_add_eq ; last by rewrite /HiFirrtl.PVM.SE.eq Hvs //.
      by done.
    - rewrite CEP.Lemmas.find_add_neq ; last by rewrite /HiFirrtl.PVM.SE.eq Hvs //.
      rewrite CEP.Lemmas.find_add_neq ; last by rewrite /HiFirrtl.PVM.SE.eq Hvs //.
      by apply H1.
  + (* Sfcnct *)
    destruct (type_of_ref h scope1) ; last by trivial.
    destruct (type_of_expr h0 scope1) ; last by trivial.
    split ; first by reflexivity.
    by exact H1.
  + (* Sinvalid *)
    destruct (type_of_ref h scope1) ; last by trivial.
    split ; first by reflexivity.
    by exact H1.
  + (* Swhen *)
    rename h0 into ss_true ; rename h1 into ss_false.
    destruct (type_of_expr h scope1) ; last by trivial.
    rewrite stmts_tmap_cat.
    generalize (stmts_tmap_components vm ss_true tmap scope1 scope2 H H0 H1) ;
          intro.
    generalize (stmts_submap vm ss_true tmap scope1 H) ;
          intro.
    destruct (stmts_tmap (tmap, scope1) ss_true vm) as [[tmap_true scope_true]|] eqn: Hss_true ; last by trivial.
    generalize (stmts_submap vm (component_stmts_of ss_true) tmap scope2 H0) ;
          intro.
    destruct (stmts_tmap (tmap, scope2) (component_stmts_of ss_true) vm) as [[tmap_true' scope_true']|] eqn: Hss_true' ;
          last by contradict H2.
    rewrite -(proj1 H2) ; rewrite -(proj1 H2) in Hss_true', H4.
    destruct H2 as [_ H2] ; clear tmap_true'.
    assert (CEP.submap scope1 tmap_true)
          by apply (CEP.Lemmas.submap_trans H), H3.
    assert (CEP.submap scope1 scope_true')
          by apply (CEP.Lemmas.submap_trans (proj2 (proj2 H3)) H2).
    generalize (stmts_tmap_components vm ss_false tmap_true scope1 scope_true' H5 (proj1 H4) H6) ; intro.
    generalize (stmts_submap vm ss_false tmap_true scope1 H5) ;
          intro.
    destruct (stmts_tmap (tmap_true, scope1) ss_false vm) as [[tmap_false scope_false]|] eqn: Hss_false ; last by trivial.
    destruct (stmts_tmap (tmap_true, scope_true') (component_stmts_of ss_false) vm) as [[tmap_false' scope_false']|] eqn: Hss_false' ;
          last by trivial.
    split ; first by apply H7.
    apply (CEP.Lemmas.submap_trans (proj2 (proj2 H8))), H7.
Qed.


(*---------------------------------------------------------------------------*)
(* connection updating statements and their properties                       *)

Fixpoint connection_stmts_of (ss : HiFP.hfstmt_seq) : HiFP.hfstmt_seq :=
(* extracts from ss the statements that update connections.
   Note that this command does not change the structure of Shwen statements. *)
match ss with
| Qnil => ss
| Qcons s ss' => Qcat (connection_stmt_of s) (connection_stmts_of ss')
end
with connection_stmt_of (s : HiFP.hfstmt) : HiFP.hfstmt_seq :=
match s with
| Sskip => Qnil ProdVarOrder.T
| Sfcnct _ _
| Sinvalid _ => Qcons s (Qnil ProdVarOrder.T)
| Swire _ _
| Sreg _ _
| Snode _ _
| Smem _ _
| Sinst _ _ => Qnil ProdVarOrder.T
| Swhen cond ss_true ss_false =>
    Qcons (Swhen cond (connection_stmts_of ss_true) (connection_stmts_of ss_false)) (Qnil ProdVarOrder.T)
end.




(*****************************************************************************)
(*                                                                           *)
(*                             S E M A N T I C S                             *)
(*                                                                           *)
(*****************************************************************************)


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
        Some (mkseq (fun i => (fst v, N.add (snd v) (bin_of_nat i))) (size_of_ftype t), t)
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

(*---------------------------------------------------------------------------*)
(* Semantics of ports                                                        *)

Fixpoint connect_port (vm_old : CEP.t vertex_type) (ct_old : CEP.t def_expr)
                      (p : HiFP.hfport) (ft : ftype)
                      (vm_new : CEP.t vertex_type) (ct_new : CEP.t def_expr) : bool :=
(* The predicate returns true if the correct port definitions are in vm_new
   and the correct D_undefined connections are made in ct_new.
   Only the elements where p should define something are checked,
   i.e. (size_of_ftype ft) identifiers.
   The port name and flow direction are taken from p, but its type is taken from ft.
   (In most cases the port type is also ft, but that is not necessary.
   It is clumsy to take ft from p because that disallows Coq from
   determining the decreasing argument of the recursion.) *)
match ft, p with
| Gtyp gt, Finput v _ =>
            (   (CEP.find v vm_old == None)
            &&
                (CEP.find v vm_new == Some (InPort gt)))
        &&
            (   (CEP.find v ct_old == None)
            &&
                (CEP.find v ct_new == None))
| Gtyp gt, Foutput v _ =>
            (   (CEP.find v vm_old == None)
            &&
                (CEP.find v vm_new == Some (OutPort gt)))
        &&
            (   (CEP.find v ct_old == None)
            &&
                (CEP.find v ct_new == Some (D_undefined)))
| Atyp elt n, Finput v _ =>
    let type_len := size_of_ftype elt in
        [forall i : ordinal n, connect_port vm_old ct_old (Finput  (fst v, bin_of_nat (i * type_len + snd v)) elt) elt vm_new ct_new]
| Atyp elt n, Foutput v _ =>
    let type_len := size_of_ftype elt in
        [forall i : ordinal n, connect_port vm_old ct_old (Foutput (fst v, bin_of_nat (i * type_len + snd v)) elt) elt vm_new ct_new]
| Btyp ff, _ => connect_port_fields vm_old ct_old p ff vm_new ct_new
end
with connect_port_fields (vm_old : CEP.t vertex_type) (ct_old : CEP.t def_expr)
                         (p : HiFP.hfport) (ff : ffield)
                         (vm_new : CEP.t vertex_type) (ct_new : CEP.t def_expr) : bool :=
(* The predicate returns true if the correct port definitions are in vm_new
   and the correct D_undefined connections are made in ct_new.
   Only the elements where p should define something are checked,
   i.e. (size_of_ffield ff) identifiers.
   The port name and flow direction are taken from p, but its type is taken to be (Btyp ff). *)
match ff with
| Fnil => true
| Fflips v flp gt ff' =>
    let type_len := size_of_ftype gt in
            match flp with
            | Nflip => connect_port vm_old ct_old p gt vm_new ct_new
            | Flipped =>
                match p with
                | Finput  v _ => connect_port vm_old ct_old (Foutput v gt) gt vm_new ct_new
                | Foutput v _ => connect_port vm_old ct_old (Finput  v gt) gt vm_new ct_new
                end
            end
        &&
            match p with
            | Finput  v _ =>
                connect_port_fields vm_old ct_old (Finput  (fst v, bin_of_nat (type_len + snd v)) (Btyp ff')) ff' vm_new ct_new
            | Foutput v _ =>
                connect_port_fields vm_old ct_old (Foutput (fst v, bin_of_nat (type_len + snd v)) (Btyp ff')) ff' vm_new ct_new
            end
end.


Lemma connect_port_submap :
(* Helper lemma to prove that Sem_frag_ports adds new definitions
   but does not change existing ones. *)
forall (ft : ftype)
       (vm_old : CEP.t vertex_type) (ct_old : CEP.t def_expr)
       (p : HiFP.hfport)
       (vm_new : CEP.t vertex_type) (ct_new : CEP.t def_expr),
           connect_port vm_old ct_old p ft vm_new ct_new ->
               match p with
               | Finput  v _
               | Foutput v _ =>
                   forall (n0 : N), n0 >= snd v -> n0 < (size_of_ftype ft) + (snd v) ->
                           (forall el : vertex_type, CEP.find (fst v, n0) vm_old = Some el -> CEP.find (fst v, n0) vm_new = Some el)
                       /\
                           (forall el : def_expr,    CEP.find (fst v, n0) ct_old = Some el -> CEP.find (fst v, n0) ct_new = Some el)
               end
with connect_port_fields_submap :
forall (ff : ffield)
       (vm_old : CEP.t vertex_type) (ct_old : CEP.t def_expr)
       (p : HiFP.hfport)
       (vm_new : CEP.t vertex_type) (ct_new : CEP.t def_expr),
           connect_port_fields vm_old ct_old p ff vm_new ct_new ->
               match p with
               | Finput  v _
               | Foutput v _ =>
                   forall (n0 : N), n0 >= snd v -> n0 < (size_of_fields ff) + (snd v) ->
                           (forall el : vertex_type, CEP.find (fst v, n0) vm_old = Some el -> CEP.find (fst v, n0) vm_new = Some el)
                       /\
                           (forall el : def_expr,    CEP.find (fst v, n0) ct_old = Some el -> CEP.find (fst v, n0) ct_new = Some el)
               end.
Proof.
* clear connect_port_submap.
  induction ft ; simpl ; intros ; destruct p ; intros ; split ; intro.
  + (* Gtyp *)
    1-4: rewrite -add1n leq_add2l in H1.
    1-4: assert (nat_of_bin (snd s) == nat_of_bin n0)
          by rewrite eqn_leq H0 H1 //.
    1-4: move /eqP : H2 => H2.
    1,3: move /andP : H => [/andP [/eqP H _] _].
    3,4: move /andP : H => [_ /andP [/eqP H _]].
    1-4: rewrite -(nat_of_binK n0) -H2 nat_of_binK -surjective_pairing H //.
  + (* Atyp *)
    1-4: assert (0 < size_of_ftype ft /\ 0 < n)
               by (apply (leq_ltn_trans H0) in H1 ;
                   rewrite -subn_gt0 -addnBA // subnn addn0 muln_gt0 in H1 ;
                   move /andP : H1 => H1 ; exact H1).
    1-4: assert ((n-1).+1 = n)
               by (rewrite subn1 ; apply prednK ; apply H2).
    1-4: move /forallP : H => H.
    1-4: specialize (H (cast_ord H3 (inord ((n0 - snd s) %/ size_of_ftype ft)))).
    1-4: simpl nat_of_ord in H ;
         rewrite inordK in H ;
               last by (rewrite H3 ltn_divLR ; last (by apply H2) ;
                        rewrite mulnC ltn_subLR // addnC //).
    1-4: apply IHft in H ; rewrite bin_of_natK in H ; simpl in H.
    1-4: apply H ;
               first (by rewrite -(addn0 ((n0 - snd s) %/ size_of_ftype ft * size_of_ftype ft))
                                 -(subnn ((n0 - snd s) %% size_of_ftype ft)) addnBA // -divn_eq
                                 addnBAC ; last (by rewrite leq_mod //) ;
                         rewrite -addnABC // subnn addn0 leq_subr //).
    1-4: rewrite addnA addnC -ltn_subLR //
                 -{1}(mul1n (size_of_ftype ft)) -mulnDl -ltn_divLR ;
         last (by apply H2) ;
         by apply leq_div2r, leqnn.
  + (* Btyp *)
    1-4: apply connect_port_fields_submap in H.
    1-4: specialize (H n0 H0 H1) ; apply H.
* clear connect_port_fields_submap.
  induction ff ; simpl ; intros ; destruct p ; intros ; split ; intro.
  + (* Fnil *)
    1-4: apply (leq_ltn_trans H0) in H1.
    1-4: rewrite add0n ltnn // in H1.
  + (* Fflips *)
    1-4: destruct (n0 < size_of_ftype f0 + snd s) eqn: Hns.
    1,3,5,7: destruct f ; move /andP : H => [H _] ;
             apply connect_port_submap in H ;
             specialize (H n0 H0 Hns) ;
             apply H.
    1-4: destruct f ; move /andP : H => [_ H].
    1-8: apply IHff in H.
    1-8: specialize (H n0) ; simpl in H.
    1-8: rewrite bin_of_natK addnA (addnC (size_of_fields ff)) in H.
    1-8: apply negbT in Hns ; rewrite -leqNgt in Hns.
    1-8: by apply (H Hns H1).
Qed.


Definition vm_and_ct_compatible (vm : CEP.t vertex_type) (ct : CEP.t def_expr) :=
forall (v : CEP.key),
    match CEP.find v vm with
    | None
    | Some (InPort _)
    | Some (Node _) => CEP.find v ct = None
    | _ => CEP.find v ct <> None
    end.


Lemma connect_port_compatible :
(* Helper lemma to prove that Sem_frag_ports
   keeps the compatibility between vm and ct. *)
forall (ft : ftype)
       (vm_old : CEP.t vertex_type) (ct_old : CEP.t def_expr)
       (p : HiFP.hfport)
       (vm_new : CEP.t vertex_type) (ct_new : CEP.t def_expr),
           connect_port vm_old ct_old p ft vm_new ct_new ->
               match p with
               | Finput  v _
               | Foutput v _ =>
                   forall (n0 : N), n0 >= snd v -> n0 < (size_of_ftype ft) + (snd v) ->
                       match CEP.find (fst v, n0) vm_old with
                       | None | Some (InPort _) | Some (Node _) => CEP.find (fst v, n0) ct_old = None
                       | _ => CEP.find (fst v, n0) ct_old <> None
                       end ->
                           match CEP.find (fst v, n0) vm_new with
                           | None | Some (InPort _) | Some (Node _) => CEP.find (fst v, n0) ct_new = None
                           | _ => CEP.find (fst v, n0) ct_new <> None
                           end
               end
with connect_port_fields_compatible :
forall (ff : ffield)
       (vm_old : CEP.t vertex_type) (ct_old : CEP.t def_expr)
       (p : HiFP.hfport)
       (vm_new : CEP.t vertex_type) (ct_new : CEP.t def_expr),
           connect_port_fields vm_old ct_old p ff vm_new ct_new ->
               match p with
               | Finput  v _
               | Foutput v _ =>
                   forall (n0 : N), n0 >= snd v -> n0 < (size_of_fields ff) + (snd v) ->
                       match CEP.find (fst v, n0) vm_old with
                       | None | Some (InPort _) | Some (Node _) => CEP.find (fst v, n0) ct_old = None
                       | _ => CEP.find (fst v, n0) ct_old <> None
                       end ->
                           match CEP.find (fst v, n0) vm_new with
                           | None | Some (InPort _) | Some (Node _) => CEP.find (fst v, n0) ct_new = None
                           | _ => CEP.find (fst v, n0) ct_new <> None
                           end
               end.
Proof.
* clear connect_port_compatible.
  induction ft ; simpl ; intros ; destruct p ; intros.
  + (* Gtyp *)
    1-2: rewrite -add1n leq_add2l in H1.
    1-2: assert (nat_of_bin (snd s) == nat_of_bin n0)
          by rewrite eqn_leq H0 H1 //.
    1-2: move /eqP : H3 => H3.
    1-2: move /and3P : H => [/andP [_ /eqP H] _ /eqP H4].
    1-2: rewrite -(nat_of_binK n0) -H3 nat_of_binK -surjective_pairing H H4 //.
  + (* Atyp *)
    1-2: assert (0 < size_of_ftype ft /\ 0 < n)
               by (apply (leq_ltn_trans H0) in H1 ;
                   rewrite -subn_gt0 -addnBA // subnn addn0 muln_gt0 in H1 ;
                   move /andP : H1 => H1 ; exact H1).
    1-2: assert ((n-1).+1 = n)
               by (rewrite subn1 ; apply prednK ; apply H3).
    1-2: move /forallP : H => H.
    1-2: specialize (H (cast_ord H4 (inord ((n0 - snd s) %/ size_of_ftype ft)))).
    1-2: simpl nat_of_ord in H ;
         rewrite inordK in H ;
               last by (rewrite H4 ltn_divLR ; last (by apply H3) ;
                        rewrite mulnC ltn_subLR // addnC //).
    1-2: apply IHft in H ; rewrite bin_of_natK in H ; simpl in H.
    1-2: apply H ;
               first (by rewrite -(addn0 ((n0 - snd s) %/ size_of_ftype ft * size_of_ftype ft))
                                 -(subnn ((n0 - snd s) %% size_of_ftype ft)) addnBA // -divn_eq
                                 addnBAC ; last (by rewrite leq_mod //) ;
                         rewrite -addnABC // subnn addn0 leq_subr //) ;
               last by apply H2.
    1-2: rewrite addnA addnC -ltn_subLR //
                 -{1}(mul1n (size_of_ftype ft)) -mulnDl -ltn_divLR ;
         last (by apply H3) ;
         by apply leq_div2r, leqnn.
  + (* Btyp *)
    1-2: apply connect_port_fields_compatible in H.
    1-2: specialize (H n0 H0 H1 H2) ; apply H.
* clear connect_port_fields_compatible.
  induction ff ; simpl ; intros ; destruct p ; intros.
  + (* Fnil *)
    1-2: apply (leq_ltn_trans H0) in H1.
    1-2: rewrite add0n ltnn // in H1.
  + (* Fflips *)
    1-2: destruct (n0 < size_of_ftype f0 + snd s) eqn: Hns.
    1,3: destruct f ; move /andP : H => [H _] ;
         apply connect_port_compatible in H ;
         specialize (H n0 H0 Hns H2) ;
         apply H.
    1-2: move /andP : H => [_ H].
    1-2: apply IHff in H.
    1-2: specialize (H n0) ; simpl in H.
    1-2: rewrite bin_of_natK addnA (addnC (size_of_fields ff)) in H.
    1-2: apply negbT in Hns ; rewrite -leqNgt in Hns.
    1-2: by apply (H Hns H1 H2).
Qed.


Definition Sem_frag_port (vm_old : CEP.t vertex_type) (ct_old : CEP.t def_expr) (p : HiFP.hfport) (vm_new : CEP.t vertex_type) (ct_new : CEP.t def_expr) (tmap : CEP.t ftype) : Prop :=
(* returns True if the port in p defines the components in vm *)
match p with
| Finput v _
| Foutput v _ =>
    match CEP.find v tmap with
    | Some ft =>
            connect_port vm_old ct_old p ft vm_new ct_new
        /\ (* other vertices and connections do not change *)
           forall (v0 n0 : N), v0 <> fst v \/ n0 < snd v \/ n0 >= (size_of_ftype ft) + (snd v) ->
                   CEP.find (v0, n0) vm_old = CEP.find (v0, n0) vm_new
               /\
                   CEP.find (v0, n0) ct_old = CEP.find (v0, n0) ct_new
    | None => False
    end
end.


Fixpoint Sem_frag_ports (vm_old : CEP.t vertex_type) (ct_old : CEP.t def_expr) (pp : seq HiFP.hfport) (vm_new : CEP.t vertex_type) (ct_new : CEP.t def_expr) (tmap : CEP.t ftype) : Prop :=
(* returns True if the ports in pp define the components in vm *)
match pp with
| [::] => vm_old = vm_new /\ ct_old = ct_new
| p :: pp' =>
    exists (vm' : CEP.t vertex_type) (ct' : CEP.t def_expr),
           Sem_frag_ports vm_old ct_old pp' vm' ct' tmap
        /\
           Sem_frag_port vm' ct' p vm_new ct_new tmap
end.


Lemma Sem_frag_ports_submap :
forall (pp : seq HiFP.hfport) (vm_old : CEP.t vertex_type) (ct_old : CEP.t def_expr)
       (vm_new : CEP.t vertex_type) (ct_new : CEP.t def_expr) (tmap : CEP.t ftype),
    Sem_frag_ports vm_old ct_old pp vm_new ct_new tmap ->
        CEP.submap vm_old vm_new /\ CEP.submap ct_old ct_new.
Proof.
induction pp ; simpl ; intros ;
      first by (destruct H ; rewrite H H0 ; split ; apply CEP.Lemmas.submap_refl).
destruct H as [vm' [ct' [H H0]]].
specialize (IHpp vm_old ct_old vm' ct' tmap H).
unfold Sem_frag_port in H0.
destruct a.
1,2: destruct (CEP.find s tmap) ; last by contradiction H0.
1,2: split.
1-4: intro.
1-4: destruct H0 as [H0 H1].
1-4: specialize (H1 (fst k) (snd k)) ; rewrite -surjective_pairing in H1.
1-4: destruct (fst k != fst s) eqn: Hks1 ; move /eqP : Hks1 => Hks1.
* 1,3,5,7: specialize (H1 (or_introl Hks1)).
  1,3: destruct H1 as [H1 _].
  3,4: destruct H1 as [_ H1].
  1-4: rewrite -H1 ; apply IHpp.
* 1-4: destruct (snd k < snd s) eqn: Hksmall.
  + 1,3,5,7: specialize (H1 (or_intror (or_introl is_true_true))).
    1,3: destruct H1 as [H1 _].
    3,4: destruct H1 as [_ H1].
    1-4: rewrite -H1 ; apply IHpp.
  + 1-4: destruct (size_of_ftype f0 + snd s <= snd k) eqn: Hklarge.
    - 1,3,5,7: specialize (H1 (or_intror (or_intror is_true_true))).
      1,3: destruct H1 as [H1 _].
      3,4: destruct H1 as [_ H1].
      1-4: rewrite -H1 ; apply IHpp.
    - 1-4: apply connect_port_submap in H0.
      1-4: apply negbT in Hksmall ; rewrite -leqNgt in Hksmall.
      1-4: apply negbT in Hklarge ; rewrite -ltnNge in Hklarge.
      1-4: specialize (H0 (snd k) Hksmall Hklarge).
      1,3: destruct H0 as [H0 _] ; destruct IHpp as [IHpp _].
      3,4: destruct H0 as [_ H0] ; destruct IHpp as [_ IHpp].
      1-4: specialize (IHpp k).
      1-2: destruct (CEP.find k vm_old) as [v|] ; try by (intros ; discriminate H2).
      3-4: destruct (CEP.find k ct_old) as [v|] ; try by (intros ; discriminate H2).
      1-4: specialize (IHpp v Logic.eq_refl).
      1-4: rewrite -Hks1 -surjective_pairing IHpp in H0.
      1-4: specialize (H0 v Logic.eq_refl).
      1-4: intros.
      1-4: rewrite H0 H2 //.
Qed.


Lemma Sem_frag_ports_compatible :
forall (pp : seq HiFP.hfport) (vm_old : CEP.t vertex_type) (ct_old : CEP.t def_expr)
       (vm_new : CEP.t vertex_type) (ct_new : CEP.t def_expr) (tmap : CEP.t ftype),
    Sem_frag_ports vm_old ct_old pp vm_new ct_new tmap ->
        vm_and_ct_compatible vm_old ct_old ->
           vm_and_ct_compatible vm_new ct_new.
Proof.
induction pp ; simpl ; intros ; first by (rewrite -(proj1 H) -(proj2 H) ; exact H0).
destruct H as [vm' [ct' [H H1]]].
intro.
specialize (IHpp vm_old ct_old vm' ct' tmap H H0 v).
unfold Sem_frag_port in H1.
destruct a.
1,2: destruct (CEP.find s tmap) ; last by contradiction H1.
1,2: destruct H1 as [H1 H2].
1,2: specialize (H2 (fst v) (snd v)) ; rewrite -surjective_pairing in H2.
1,2: destruct (fst v != fst s) eqn: Hvs1 ; move /eqP : Hvs1 => Hvs1.
* 1,3: specialize (H2 (or_introl Hvs1)).
  1,2: rewrite -(proj1 H2) -(proj2 H2) //.
* 1,2: destruct (snd v < snd s) eqn: Hvsmall.
  + 1,3: specialize (H2 (or_intror (or_introl is_true_true))).
    1,2: rewrite -(proj1 H2) -(proj2 H2) //.
  + 1,2: destruct (size_of_ftype f0 + snd s <= snd v) eqn: Hvlarge.
    - 1,3: specialize (H2 (or_intror (or_intror is_true_true))).
      1,2: rewrite -(proj1 H2) -(proj2 H2) //.
    - 1,2: apply connect_port_compatible in H1.
      1,2: apply negbT in Hvsmall ; rewrite -leqNgt in Hvsmall.
      1,2: apply negbT in Hvlarge ; rewrite -ltnNge in Hvlarge.
      1,2: specialize (H1 (snd v) Hvsmall Hvlarge).
      1,2: rewrite -Hvs1 -surjective_pairing in H1.
      1,2: apply H1, IHpp.
Qed.

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

Lemma connect_type_compatible_size :
    forall (can_flip : bool) (ft_tgt ft_src : ftype) (flipped : bool),
        connect_type_compatible can_flip ft_tgt ft_src flipped ->
            size_of_ftype ft_tgt = size_of_ftype ft_src
with connect_type_compatible_fields_size :
    forall (can_flip : bool) (ff_tgt ff_src : ffield) (flipped : bool),
        connect_type_compatible_fields can_flip ff_tgt ff_src flipped ->
            size_of_fields ff_tgt = size_of_fields ff_src.
Proof.
* clear connect_type_compatible_size.
  induction ft_tgt ; simpl.
  + (* Gtyp *) destruct ft_src ; simpl ; try done ; by (destruct f ; done).
  + (* Atyp *) destruct ft_src ; simpl ; try done.
    move => flipped /andP [/eqP H1 H2].
    apply IHft_tgt in H2.
    rewrite H1 H2 //.
  + (* Btyp *) destruct ft_src ; simpl ; try done.
    apply connect_type_compatible_fields_size.
* clear connect_type_compatible_fields_size.
  induction ff_tgt ; simpl.
  + (* Fnil *) destruct ff_src ; simpl ; done.
  + (* Fflips *) destruct ff_src ; simpl ; first by (destruct f ; done).
    destruct f, f1 ; simpl ; try done.
    1,2: move => flipped /andP [/andP [_ Ht] Hf].
    1,2: apply connect_type_compatible_size in Ht.
    1,2: apply IHff_tgt in Hf.
    1,2: rewrite Ht Hf //.
Qed.

Definition connect_fgtyp (ct_old : CEP.t def_expr)
                         (ref_tgt : HiFP.href) (lst_tgt : list CEP.key)
                         (ref_src : HiFP.href) (lst_src : list CEP.key)
                         (flipped : bool)
                         (ct_new : CEP.t def_expr) : bool :=
(* The predicate checks whether ct_new contains the correct connection that connects from lst_src to lst_tgt,
   and it does not change the connection into lst_src.
   These lists must be one-element lists for output and input connectors of compatible types.
   It assumes that the types are compatible. *)
match lst_tgt, lst_src, flipped, ref_tgt, ref_src with
| [:: ic], [:: oc], false, _, ref_src
| [:: oc], [:: ic], true , ref_src, _ =>
       (CEP.find ic ct_old != None)
    &&
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

Lemma connect_subdomain : forall (ct_old ct_new : CEP.t def_expr) (ft_tgt ft_src : ftype) (ref_tgt ref_src : HiFP.href) (lst_tgt lst_src : seq CEP.key) (can_flip flipped : bool) (v : CEP.key),
(* This lemma is used in the theorem Sem_frag_stmts_subset;
   it proves that a connect statement only extends the domain.
   We prove it as a separate lemma because we need a mutual recursion over ftype and ffield. *)
connect ct_old ref_tgt lst_tgt ft_tgt ref_src lst_src ft_src flipped ct_new ->
connect_type_compatible can_flip ft_tgt ft_src flipped ->
    size_of_ftype ft_tgt = size lst_tgt ->
    size_of_ftype ft_src = size lst_src ->
    v \in lst_tgt \/ v \in lst_src ->
        match CEP.find v ct_new with
        | None => CEP.find v ct_old = None
        | Some _ => True
        end
with connect_fields_subdomain : forall (ct_old ct_new : CEP.t def_expr) (ff_tgt ff_src : ffield) (ref_tgt ref_src : HiFP.href) (lst_tgt lst_src : seq CEP.key) (can_flip flipped : bool) (v : CEP.key),
connect_fields ct_old ref_tgt lst_tgt ff_tgt ref_src lst_src ff_src flipped ct_new ->
connect_type_compatible_fields can_flip ff_tgt ff_src flipped ->
    size_of_fields ff_tgt = size lst_tgt ->
    size_of_fields ff_src = size lst_src ->
    v \in lst_tgt \/ v \in lst_src ->
        match CEP.find v ct_new with
        | None => CEP.find v ct_old = None
        | Some _ => True
        end.
Proof.
* clear connect_subdomain.
  induction ft_tgt as [gt_tgt|ft'_tgt|ff_tgt] ; simpl connect ;
  destruct ft_src as [ft_src|ft'_src|ff_src] ; try (by done) ;
  simpl connect_type_compatible ; simpl size_of_ftype ; intros.
  + (* Gtyp *)
    unfold connect_fgtyp in H.
    destruct lst_tgt as [|el_tgt [|]] ; try by done.
    destruct lst_src as [|el_src [|]] ; try by done.
    destruct H3 ; rewrite mem_seq1 in H3 ; move /eqP : H3 => H3 ; rewrite -H3 in H.
    1,2: destruct flipped ; move /andP : H => [/andP [_ /eqP H] /eqP H4] ; try (by rewrite H //).
    1,2: rewrite H4 ; destruct (CEP.find v ct_old) ; by done.
  + (* Atyp *)
    specialize (IHft'_tgt ft'_src).
    move /andP : H => [/eqP H4 /forallP H] ; rewrite -H4 in H0, H2 ; clear n0 H4.
    rewrite eq_refl andTb in H0.
    generalize (connect_type_compatible_size can_flip ft'_tgt ft'_src flipped H0) ; intro.
    assert (n <> 0).
          destruct H3 as [H3|H3].
          - by contradict H3 ; rewrite H3 muln0 in H1 ; symmetry in H1 ;
               apply size0nil in H1 ; rewrite H1 in_nil //.
          - by contradict H3 ; rewrite H3 muln0 in H2 ; symmetry in H2 ;
               apply size0nil in H2 ; rewrite H2 in_nil //.
      assert (size_of_ftype ft'_tgt <> 0).
          destruct H3 as [H3|H3].
          - by contradict H3 ; rewrite H3 mul0n in H1 ; symmetry in H1 ;
               apply size0nil in H1 ; rewrite H1 in_nil //.
          - by contradict H3 ; rewrite -H4 H3 mul0n in H2 ; symmetry in H2 ;
               apply size0nil in H2 ; rewrite H2 in_nil //.
    move /eqP : H6 => H6 ; apply negbTE in H6.
    assert ((n-1).+1 = n)
           by (rewrite subn1 ; apply prednK ; rewrite lt0n ;
               move /eqP : H5 => H5 ; exact H5).
    (* Now find out which array element contains v,
       and then apply the induction hypothesis to this element. *)
    destruct H3 as [H3|H3].
    - assert (index v lst_tgt %/ size_of_ftype ft'_tgt < n)
            by (rewrite -index_mem -H1 mulnC -ltn_divLR // in H3 ;
                rewrite lt0n H6 //).
      specialize (H (cast_ord H7 (inord (index v lst_tgt %/ size_of_ftype ft'_tgt)))) ;
      simpl nat_of_ord in H ;
      rewrite inordK in H ; last by rewrite H7 H8 //.
      specialize (IHft'_tgt
            (Esubindex ref_tgt (index v lst_tgt %/ size_of_ftype ft'_tgt))
            (Esubindex ref_src (index v lst_tgt %/ size_of_ftype ft'_tgt))
            (take (size_of_ftype ft'_tgt)
                  (drop (index v lst_tgt %/ size_of_ftype ft'_tgt * size_of_ftype ft'_tgt)
                        lst_tgt))
            (take (size_of_ftype ft'_tgt)
                  (drop (index v lst_tgt %/ size_of_ftype ft'_tgt * size_of_ftype ft'_tgt)
                        lst_src))
            can_flip flipped v H H0).
      apply IHft'_tgt.
      * rewrite size_takel ; first by reflexivity.
        by rewrite size_drop -H1 -(mulnC n) -mulnBl -{1}(mul1n (size_of_ftype ft'_tgt))
                   leq_mul2r H6 orFb subn_gt0 H8 //.
      * rewrite size_takel ; first by rewrite H4 //.
        by rewrite size_drop -H2 -H4 -(mulnC n) -mulnBl -{1}(mul1n (size_of_ftype ft'_tgt))
                   leq_mul2r H6 orFb subn_gt0 H8 //.
      * left.
        rewrite in_take_leq ;
              last by rewrite size_drop -H1 -(mulnC n) -mulnBl -{1}(mul1n (size_of_ftype ft'_tgt))
                              leq_mul2r H6 orFb subn_gt0 H8 //.
        assert (index v lst_tgt = (index v lst_tgt %/ size_of_ftype ft'_tgt *
                         size_of_ftype ft'_tgt) + index v (drop
                        (index v lst_tgt %/ size_of_ftype ft'_tgt *
                         size_of_ftype ft'_tgt) lst_tgt)).
              rewrite -{1}(cat_take_drop (index v lst_tgt %/ size_of_ftype ft'_tgt *
                               size_of_ftype ft'_tgt) lst_tgt) index_cat.
              destruct (v \in take
                        (index v lst_tgt %/ size_of_ftype ft'_tgt *
                         size_of_ftype ft'_tgt) lst_tgt) eqn: Hin_take ;
                    first by (apply index_ltn in Hin_take ; rewrite ltnNge leq_trunc_div // in Hin_take).
              rewrite Hin_take size_take -{1}H1 -(mulnC n) ltn_mul2r.
              rewrite lt0n H6 andTb H8 //.
        rewrite -(ltn_add2l (index v lst_tgt %/ size_of_ftype ft'_tgt * size_of_ftype ft'_tgt)) -H9.
        rewrite {1}(divn_eq (index v lst_tgt) (size_of_ftype ft'_tgt)) ltn_add2l ltn_mod lt0n H6 //.
    - assert (index v lst_src %/ size_of_ftype ft'_tgt < n)
            by (rewrite -index_mem -H2 -H4 mulnC -ltn_divLR // in H3 ;
                rewrite lt0n H6 //).
      specialize (H (cast_ord H7 (inord (index v lst_src %/ size_of_ftype ft'_tgt)))) ;
      simpl nat_of_ord in H ;
      rewrite inordK in H ; last by rewrite H7 H8 //.
      specialize (IHft'_tgt
            (Esubindex ref_tgt (index v lst_src %/ size_of_ftype ft'_tgt))
            (Esubindex ref_src (index v lst_src %/ size_of_ftype ft'_tgt))
            (take (size_of_ftype ft'_tgt)
                  (drop (index v lst_src %/ size_of_ftype ft'_tgt * size_of_ftype ft'_tgt)
                        lst_tgt))
            (take (size_of_ftype ft'_tgt)
                  (drop (index v lst_src %/ size_of_ftype ft'_tgt * size_of_ftype ft'_tgt)
                        lst_src))
            can_flip flipped v H H0).
      apply IHft'_tgt.
      * rewrite size_takel ; first by reflexivity.
         rewrite size_drop -H1 -(mulnC n) -mulnBl -{1}(mul1n (size_of_ftype ft'_tgt))
                   leq_mul2r H6 orFb subn_gt0 H8 //.
      * rewrite size_takel ; first by rewrite H4 //.
        by rewrite size_drop -H2 -H4 -(mulnC n) -mulnBl -{1}(mul1n (size_of_ftype ft'_tgt))
                   leq_mul2r H6 orFb subn_gt0 H8 //.
      * right.
        rewrite in_take_leq ;
              last by rewrite size_drop -H2 -H4 -(mulnC n) -mulnBl -{1}(mul1n (size_of_ftype ft'_tgt))
                              leq_mul2r H6 orFb subn_gt0 H8 //.
        assert (index v lst_src = (index v lst_src %/ size_of_ftype ft'_tgt *
                         size_of_ftype ft'_tgt) + index v (drop
                        (index v lst_src %/ size_of_ftype ft'_tgt *
                         size_of_ftype ft'_tgt) lst_src)).
              rewrite -{1}(cat_take_drop (index v lst_src %/ size_of_ftype ft'_tgt *
                               size_of_ftype ft'_tgt) lst_src) index_cat.
              destruct (v \in take
                        (index v lst_src %/ size_of_ftype ft'_tgt *
                         size_of_ftype ft'_tgt) lst_src) eqn: Hin_take ;
                    first by (apply index_ltn in Hin_take ; rewrite ltnNge leq_trunc_div // in Hin_take).
              rewrite Hin_take size_take -{1}H2 -{1}H4 -(mulnC n) ltn_mul2r.
              rewrite lt0n H6 andTb H8 //.
        rewrite -(ltn_add2l (index v lst_src %/ size_of_ftype ft'_tgt * size_of_ftype ft'_tgt)) -H9.
        rewrite {1}(divn_eq (index v lst_src) (size_of_ftype ft'_tgt)) ltn_add2l ltn_mod lt0n H6 //.
  + (* Btyp *)
    apply (connect_fields_subdomain ct_old ct_new ff_tgt ff_src ref_tgt ref_src lst_tgt lst_src can_flip flipped) ;
    by assumption.
* clear connect_fields_subdomain.
  induction ff_tgt as [|v_tgt flipped_tgt ft_tgt ff'_tgt] ; simpl connect_fields ;
  destruct ff_src as [|v_src flipped_src ft_src ff'_src] ;
  try done ; try (by destruct flipped_tgt ; done) ;
  simpl size_of_fields ; intros.
  + (* Fnil *)
    symmetry in H1, H2.
    apply size0nil in H1, H2.
    rewrite H1 H2 in_nil in H3.
    by destruct H3 ; discriminate H3.
  + (* Fflips *)
    simpl connect_type_compatible_fields in H0.
    (* Now find out whether v is in the first part of lst_tgt / lst_src,
       and decide based on that whether to use connect_subdomain or IHff'_tgt *)
    destruct H3 as [H3|H3].
    - rewrite -(cat_take_drop (size_of_ftype ft_tgt) lst_tgt) mem_cat in H3.
      move /orP : H3 => H3.
      destruct H3 as [H3|H3] ;
      destruct flipped_tgt, flipped_src ; try done.
      1,2: move /andP : H => [/eqP H4 /andP [H _]] ;
           move /andP : H0 => [/andP [_ H0] _] ;
           rewrite -H4 in H, H0 ; clear v_src H4 ;
           specialize (connect_subdomain ct_old ct_new ft_tgt ft_src
                                         (Esubfield ref_tgt v_tgt)
                                         (Esubfield ref_src v_tgt)) with (v := v) (1 := H) (2 := H0) ;
           apply connect_type_compatible_size in H0 ;
           first rewrite -H0 in connect_subdomain ;
           apply connect_subdomain.
      1,4: by rewrite size_takel // -H1 leq_addr //.
      1,3: by rewrite size_takel H0 // -H2 leq_addr //.
      1,2: by left ; rewrite H3 //.
      1,2: move /andP : H => [_ /andP [_ H]] ;
           move /andP : H0 => [/andP [_ H0] H4] ;
           specialize (IHff'_tgt ff'_src) with (v := v) (1 := H) (2 := H4) ;
           apply connect_type_compatible_size in H0 ;
           try rewrite -H0 in IHff'_tgt ;
           apply IHff'_tgt.
      1,4: by rewrite size_drop -H1 addKn //.
      1,3: by rewrite size_drop -H2 H0 addKn //.
      1,2: by left ; rewrite H3 //.
    - rewrite -(cat_take_drop (size_of_ftype ft_src) lst_src) mem_cat in H3.
      move /orP : H3 => H3.
      destruct H3 as [H3|H3] ;
      destruct flipped_tgt, flipped_src ; try done.
      1,2: move /andP : H => [/eqP H4 /andP [H _]] ;
           move /andP : H0 => [/andP [_ H0] _] ;
           rewrite -H4 in H, H0 ; clear v_src H4 ;
           specialize (connect_subdomain ct_old ct_new ft_tgt ft_src
                                         (Esubfield ref_tgt v_tgt)
                                         (Esubfield ref_src v_tgt)) with (v := v) (1 := H) (2 := H0) ;
           apply connect_type_compatible_size in H0 ;
           first rewrite -H0 in connect_subdomain ;
           apply connect_subdomain.
      1,4: by rewrite size_takel // -H1 leq_addr //.
      1,3: by rewrite size_takel H0 // -H2 leq_addr //.
      1,2: by right ; rewrite H0 H3 //.
      1,2: move /andP : H => [_ /andP [_ H]] ;
           move /andP : H0 => [/andP [_ H0] H4] ;
           specialize (IHff'_tgt ff'_src) with (v := v) (1 := H) (2 := H4) ;
           apply connect_type_compatible_size in H0 ;
           try rewrite -H0 in IHff'_tgt ;
           apply IHff'_tgt.
      1,4: by rewrite size_drop -H1 addKn //.
      1,3: by rewrite size_drop -H2 H0 addKn //.
      1,2: by right ; rewrite H0 H3 //.
Qed.

Lemma connect_preserves_compatibility :
forall (ct_old ct_new : CEP.t def_expr) (ft_tgt ft_src : ftype) (ref_tgt ref_src : HiFP.href) (lst_tgt lst_src : seq CEP.key) (can_flip flipped : bool) (v : CEP.key),
connect ct_old ref_tgt lst_tgt ft_tgt ref_src lst_src ft_src flipped ct_new ->
connect_type_compatible can_flip ft_tgt ft_src flipped ->
    size_of_ftype ft_tgt = size lst_tgt ->
    size_of_ftype ft_src = size lst_src ->
    v \in lst_tgt \/ v \in lst_src ->
        CEP.find v ct_old = None <-> CEP.find v ct_new = None
with connect_preserves_compatibility_fields :
forall (ct_old ct_new : CEP.t def_expr) (ff_tgt ff_src : ffield) (ref_tgt ref_src : HiFP.href) (lst_tgt lst_src : seq CEP.key) (can_flip flipped : bool) (v : CEP.key),
connect_fields ct_old ref_tgt lst_tgt ff_tgt ref_src lst_src ff_src flipped ct_new ->
connect_type_compatible_fields can_flip ff_tgt ff_src flipped ->
    size_of_fields ff_tgt = size lst_tgt ->
    size_of_fields ff_src = size lst_src ->
    v \in lst_tgt \/ v \in lst_src ->
        CEP.find v ct_old = None <-> CEP.find v ct_new = None.
Proof.
* clear connect_preserves_compatibility.
  induction ft_tgt as [gt_tgt|ft'_tgt|ff_tgt] ; simpl connect ;
  destruct ft_src as [ft_src|ft'_src|ff_src] ; try (by done) ;
  simpl connect_type_compatible ; simpl size_of_ftype ; intros.
  + (* Gtyp *)
    unfold connect_fgtyp in H.
    destruct lst_tgt as [|el_tgt [|]] ; try by done.
    destruct lst_src as [|el_src [|]] ; try by done.
    destruct H3 ; rewrite mem_seq1 in H3 ; move /eqP : H3 => H3 ; rewrite -H3 in H.
    1,2: destruct flipped ; move /andP : H => [/andP [/eqP H4 /eqP H5] /eqP H] ; try by rewrite H //.
    1,2: destruct (CEP.find v ct_old) ; last (by contradiction H4).
    1,2: rewrite H5 ; split ; intro ; discriminate H6.
  + (* Atyp *)
    specialize (IHft'_tgt ft'_src).
    move /andP : H => [/eqP H4 /forallP H] ; rewrite -H4 in H0, H2 ; clear n0 H4.
    rewrite eq_refl andTb in H0.
    generalize (connect_type_compatible_size can_flip ft'_tgt ft'_src flipped H0) ; intro.
    assert (n <> 0).
          destruct H3 as [H3|H3].
          - by contradict H3 ; rewrite H3 muln0 in H1 ; symmetry in H1 ;
               apply size0nil in H1 ; rewrite H1 in_nil //.
          - by contradict H3 ; rewrite H3 muln0 in H2 ; symmetry in H2 ;
               apply size0nil in H2 ; rewrite H2 in_nil //.
      assert (size_of_ftype ft'_tgt <> 0).
          destruct H3 as [H3|H3].
          - by contradict H3 ; rewrite H3 mul0n in H1 ; symmetry in H1 ;
               apply size0nil in H1 ; rewrite H1 in_nil //.
          - by contradict H3 ; rewrite -H4 H3 mul0n in H2 ; symmetry in H2 ;
               apply size0nil in H2 ; rewrite H2 in_nil //.
    move /eqP : H6 => H6 ; apply negbTE in H6.
    assert ((n-1).+1 = n)
           by (rewrite subn1 ; apply prednK ; rewrite lt0n ;
               move /eqP : H5 => H5 ; exact H5).
    (* Now find out which array element contains v,
       and then apply the induction hypothesis to this element. *)
    destruct H3 as [H3|H3].
    - assert (index v lst_tgt %/ size_of_ftype ft'_tgt < n)
            by (rewrite -index_mem -H1 mulnC -ltn_divLR // in H3 ;
                rewrite lt0n H6 //).
      specialize (H (cast_ord H7 (inord (index v lst_tgt %/ size_of_ftype ft'_tgt)))) ;
      simpl nat_of_ord in H ;
      rewrite inordK in H ; last by rewrite H7 H8 //.
      specialize (IHft'_tgt
            (Esubindex ref_tgt (index v lst_tgt %/ size_of_ftype ft'_tgt))
            (Esubindex ref_src (index v lst_tgt %/ size_of_ftype ft'_tgt))
            (take (size_of_ftype ft'_tgt)
                  (drop (index v lst_tgt %/ size_of_ftype ft'_tgt * size_of_ftype ft'_tgt)
                        lst_tgt))
            (take (size_of_ftype ft'_tgt)
                  (drop (index v lst_tgt %/ size_of_ftype ft'_tgt * size_of_ftype ft'_tgt)
                        lst_src))
            can_flip flipped v H H0).
      apply IHft'_tgt.
      * rewrite size_takel ; first by reflexivity.
        by rewrite size_drop -H1 -(mulnC n) -mulnBl -{1}(mul1n (size_of_ftype ft'_tgt))
                   leq_mul2r H6 orFb subn_gt0 H8 //.
      * rewrite size_takel ; first by rewrite H4 //.
        by rewrite size_drop -H2 -H4 -(mulnC n) -mulnBl -{1}(mul1n (size_of_ftype ft'_tgt))
                   leq_mul2r H6 orFb subn_gt0 H8 //.
      * left.
        rewrite in_take_leq ;
              last by rewrite size_drop -H1 -(mulnC n) -mulnBl -{1}(mul1n (size_of_ftype ft'_tgt))
                              leq_mul2r H6 orFb subn_gt0 H8 //.
        assert (index v lst_tgt = (index v lst_tgt %/ size_of_ftype ft'_tgt *
                         size_of_ftype ft'_tgt) + index v (drop
                        (index v lst_tgt %/ size_of_ftype ft'_tgt *
                         size_of_ftype ft'_tgt) lst_tgt)).
              rewrite -{1}(cat_take_drop (index v lst_tgt %/ size_of_ftype ft'_tgt *
                               size_of_ftype ft'_tgt) lst_tgt) index_cat.
              destruct (v \in take
                        (index v lst_tgt %/ size_of_ftype ft'_tgt *
                         size_of_ftype ft'_tgt) lst_tgt) eqn: Hin_take ;
                    first by (apply index_ltn in Hin_take ; rewrite ltnNge leq_trunc_div // in Hin_take).
              rewrite Hin_take size_take -{1}H1 -(mulnC n) ltn_mul2r.
              rewrite lt0n H6 andTb H8 //.
        rewrite -(ltn_add2l (index v lst_tgt %/ size_of_ftype ft'_tgt * size_of_ftype ft'_tgt)) -H9.
        rewrite {1}(divn_eq (index v lst_tgt) (size_of_ftype ft'_tgt)) ltn_add2l ltn_mod lt0n H6 //.
    - assert (index v lst_src %/ size_of_ftype ft'_tgt < n)
            by (rewrite -index_mem -H2 -H4 mulnC -ltn_divLR // in H3 ;
                rewrite lt0n H6 //).
      specialize (H (cast_ord H7 (inord (index v lst_src %/ size_of_ftype ft'_tgt)))) ;
      simpl nat_of_ord in H ;
      rewrite inordK in H ; last by rewrite H7 H8 //.
      specialize (IHft'_tgt
            (Esubindex ref_tgt (index v lst_src %/ size_of_ftype ft'_tgt))
            (Esubindex ref_src (index v lst_src %/ size_of_ftype ft'_tgt))
            (take (size_of_ftype ft'_tgt)
                  (drop (index v lst_src %/ size_of_ftype ft'_tgt * size_of_ftype ft'_tgt)
                        lst_tgt))
            (take (size_of_ftype ft'_tgt)
                  (drop (index v lst_src %/ size_of_ftype ft'_tgt * size_of_ftype ft'_tgt)
                        lst_src))
            can_flip flipped v H H0).
      apply IHft'_tgt.
      * rewrite size_takel ; first by reflexivity.
         rewrite size_drop -H1 -(mulnC n) -mulnBl -{1}(mul1n (size_of_ftype ft'_tgt))
                   leq_mul2r H6 orFb subn_gt0 H8 //.
      * rewrite size_takel ; first by rewrite H4 //.
        by rewrite size_drop -H2 -H4 -(mulnC n) -mulnBl -{1}(mul1n (size_of_ftype ft'_tgt))
                   leq_mul2r H6 orFb subn_gt0 H8 //.
      * right.
        rewrite in_take_leq ;
              last by rewrite size_drop -H2 -H4 -(mulnC n) -mulnBl -{1}(mul1n (size_of_ftype ft'_tgt))
                              leq_mul2r H6 orFb subn_gt0 H8 //.
        assert (index v lst_src = (index v lst_src %/ size_of_ftype ft'_tgt *
                         size_of_ftype ft'_tgt) + index v (drop
                        (index v lst_src %/ size_of_ftype ft'_tgt *
                         size_of_ftype ft'_tgt) lst_src)).
              rewrite -{1}(cat_take_drop (index v lst_src %/ size_of_ftype ft'_tgt *
                               size_of_ftype ft'_tgt) lst_src) index_cat.
              destruct (v \in take
                        (index v lst_src %/ size_of_ftype ft'_tgt *
                         size_of_ftype ft'_tgt) lst_src) eqn: Hin_take ;
                    first by (apply index_ltn in Hin_take ; rewrite ltnNge leq_trunc_div // in Hin_take).
              rewrite Hin_take size_take -{1}H2 -{1}H4 -(mulnC n) ltn_mul2r.
              rewrite lt0n H6 andTb H8 //.
        rewrite -(ltn_add2l (index v lst_src %/ size_of_ftype ft'_tgt * size_of_ftype ft'_tgt)) -H9.
        rewrite {1}(divn_eq (index v lst_src) (size_of_ftype ft'_tgt)) ltn_add2l ltn_mod lt0n H6 //.
  + (* Btyp *)
    apply (connect_preserves_compatibility_fields ct_old ct_new ff_tgt ff_src ref_tgt ref_src lst_tgt lst_src can_flip flipped) ;
    by assumption.
* clear connect_preserves_compatibility_fields.
  induction ff_tgt as [|v_tgt flipped_tgt ft_tgt ff'_tgt] ; simpl connect_fields ;
  destruct ff_src as [|v_src flipped_src ft_src ff'_src] ;
  try done ; try (by destruct flipped_tgt ; done) ;
  simpl size_of_fields ; intros.
  + (* Fnil *)
    symmetry in H1, H2.
    apply size0nil in H1, H2.
    rewrite H1 H2 in_nil in H3.
    by destruct H3 ; discriminate H3.
  + (* Fflips *)
    simpl connect_type_compatible_fields in H0.
    (* Now find out whether v is in the first part of lst_tgt / lst_src,
       and decide based on that whether to use connect_subdomain or IHff'_tgt *)
    destruct H3 as [H3|H3].
    - rewrite -(cat_take_drop (size_of_ftype ft_tgt) lst_tgt) mem_cat in H3.
      move /orP : H3 => H3.
      destruct H3 as [H3|H3] ;
      destruct flipped_tgt, flipped_src ; try done.
      1,2: move /andP : H => [/eqP H4 /andP [H _]] ;
           move /andP : H0 => [/andP [_ H0] _] ;
           rewrite -H4 in H, H0 ; clear v_src H4 ;
           specialize (connect_preserves_compatibility ct_old ct_new ft_tgt ft_src
                                         (Esubfield ref_tgt v_tgt)
                                         (Esubfield ref_src v_tgt)) with (v := v) (1 := H) (2 := H0) ;
           apply connect_type_compatible_size in H0 ;
           first rewrite -H0 in connect_preserves_compatibility ;
           apply connect_preserves_compatibility.
      1,4: by rewrite size_takel // -H1 leq_addr //.
      1,3: by rewrite size_takel H0 // -H2 leq_addr //.
      1,2: by left ; rewrite H3 //.
      1,2: move /andP : H => [_ /andP [_ H]] ;
           move /andP : H0 => [/andP [_ H0] H4] ;
           specialize (IHff'_tgt ff'_src) with (v := v) (1 := H) (2 := H4) ;
           apply connect_type_compatible_size in H0 ;
           try rewrite -H0 in IHff'_tgt ;
           apply IHff'_tgt.
      1,4: by rewrite size_drop -H1 addKn //.
      1,3: by rewrite size_drop -H2 H0 addKn //.
      1,2: by left ; rewrite H3 //.
    - rewrite -(cat_take_drop (size_of_ftype ft_src) lst_src) mem_cat in H3.
      move /orP : H3 => H3.
      destruct H3 as [H3|H3] ;
      destruct flipped_tgt, flipped_src ; try done.
      1,2: move /andP : H => [/eqP H4 /andP [H _]] ;
           move /andP : H0 => [/andP [_ H0] _] ;
           rewrite -H4 in H, H0 ; clear v_src H4 ;
           specialize (connect_preserves_compatibility ct_old ct_new ft_tgt ft_src
                                         (Esubfield ref_tgt v_tgt)
                                         (Esubfield ref_src v_tgt)) with (v := v) (1 := H) (2 := H0) ;
           apply connect_type_compatible_size in H0 ;
           first rewrite -H0 in connect_preserves_compatibility ;
           apply connect_preserves_compatibility.
      1,4: by rewrite size_takel // -H1 leq_addr //.
      1,3: by rewrite size_takel H0 // -H2 leq_addr //.
      1,2: by right ; rewrite H0 H3 //.
      1,2: move /andP : H => [_ /andP [_ H]] ;
           move /andP : H0 => [/andP [_ H0] H4] ;
           specialize (IHff'_tgt ff'_src) with (v := v) (1 := H) (2 := H4) ;
           apply connect_type_compatible_size in H0 ;
           try rewrite -H0 in IHff'_tgt ;
           apply IHff'_tgt.
      1,4: by rewrite size_drop -H1 addKn //.
      1,3: by rewrite size_drop -H2 H0 addKn //.
      1,2: by right ; rewrite H0 H3 //.
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
| Some D_undefined, _ => d_true
| None, _
| Some D_invalidated, _
| _, Some D_undefined => d_false
| _, Some D_invalidated => d_true
end.

Definition extend_map_with {T : Type} (m dflt : CEP.t T) : CEP.t T :=
(* Returns map m, except that undefined elements are copied from dflt *)
CEP.map2 (fun (elm eld : option T) => if elm is Some e then Some e else eld) m dflt.

Lemma extend_map_with_submap {T : Type} :
forall (base dflt1 dflt2 : CEP.t T),
    CEP.submap dflt1 dflt2 ->
        CEP.Equal (extend_map_with (extend_map_with base dflt1) dflt2) (extend_map_with base dflt2).
Proof.
intros.
intro ; specialize (H y).
rewrite CEP.Lemmas.map2_1bis // CEP.Lemmas.map2_1bis // CEP.Lemmas.map2_1bis //.
destruct (PVM.find y base) ; first by reflexivity.
destruct (PVM.find y dflt1) ; last by reflexivity.
by rewrite (H t) //.
Qed.

(*---------------------------------------------------------------------------*)
(* Semantics of statements                                                   *)

Fixpoint Sem_frag_stmt (vm_old : CEP.t vertex_type) (ct_old : CEP.t def_expr) (s : HiFP.hfstmt) (vm_new : CEP.t vertex_type) (ct_new : CEP.t def_expr) (tmap : CEP.t ftype) : Prop :=
   (* The predicate returns True if vm_new/ct_new can be constructed from vm_old/ct_old by applying s.
   type checking, constraints *)
   match s with
   | Sskip => CEP.Equal vm_old vm_new /\ CEP.Equal ct_old ct_new
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
                             | Some ic, Some ex =>
                                    CEP.find ic ct_old <> None
                                 /\ CEP.find ic ct_new = Some (D_fexpr ex)
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
                      | Some ic =>
                             CEP.find ic ct_old <> None
                          /\ CEP.find ic ct_new = Some D_invalidated
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
                   | Some gt =>
                          CEP.find (fst v, bin_of_nat (n + snd v)) vm_old = None
                       /\ CEP.find (fst v, bin_of_nat (n + snd v)) vm_new = Some (Wire gt)
                   | None => True
                   end)
           /\ (* other vertices do not change *)
              (forall (v0 n0 : N), v0 <> fst v \/ n0 < snd v \/ n0 >= (size_of_ftype newft) + (snd v) ->
                   CEP.find (v0, n0) vm_old =
                   CEP.find (v0, n0) vm_new)
           /\ (* other connections do not change *)
              (forall (v0 n0 : N), v0 <> fst v \/ n0 < snd v \/ n0 >= (size_of_ftype newft) + (snd v) ->
                   CEP.find (v0, n0) ct_old =
                   CEP.find (v0, n0) ct_new)
           /\ (* set wires to undefined *)
              forall n0 : nat, n0 < size_of_ftype newft ->
                     (*CEP.find (fst v, bin_of_nat (n0 + snd v)) ct_old = None
                  /\*) CEP.find (fst v, bin_of_nat (n0 + snd v)) ct_new = Some D_undefined
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
                   | Some gt =>
                          CEP.find (fst v, bin_of_nat (n + snd v)) vm_old = None
                       /\ CEP.find (fst v, bin_of_nat (n + snd v)) vm_new =
                             Some (Register gt (clock reg) (reset reg)
                                      (if reset reg is Rst rst_sig rst_val
                                       then if type_of_expr rst_sig tmap is Some (exist (Gtyp Fasyncreset) _)
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
                      | Some ex =>
                             (*CEP.find (fst v, bin_of_nat (n + snd v)) ct_old = None
                          /\*) CEP.find (fst v, bin_of_nat (n + snd v)) ct_new = Some (D_fexpr ex)
                      | None => True
                      end
              | None => False
              end
           /\ (* other vertices do not change *)
              (forall (v0 n0 : N), v0 <> fst v \/ n0 < snd v \/ n0 >= size_of_ftype newft + snd v ->
                  CEP.find (v0, n0) vm_old =
                  CEP.find (v0, n0) vm_new)
           /\ (* other connections do not change *)
              (forall (v0 n0 : N), v0 <> fst v \/ n0 < snd v \/ n0 >= size_of_ftype newft + snd v ->
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
                   | Some gt =>
                          CEP.find (fst v, bin_of_nat (n + snd v)) vm_old = None
                       /\ CEP.find (fst v, bin_of_nat (n + snd v)) vm_new = Some (Node gt)
                   | None => True
                   end)
           /\ (* other vertices do not change *)
              (forall (v0 n0 : N), v0 <> fst v \/ n0 < snd v \/ n0 >= size_of_ftype newft + snd v ->
                   CEP.find (v0, n0) vm_old =
                   CEP.find (v0, n0) vm_new)
           /\ (* connections do not change *)
              CEP.Equal ct_old ct_new
         (*/\ (* also ensure that the type is passive?
                 This is what we infer from the FIRRTL specification,
                 although it is not completely clear to us. *)
              ftype_is_passive newft *)
       | None => False
       end
   | Smem v mem => False (* ? *)
   | Sinst var1 var2 => False (* ? *)
   | Swhen cond ss_true ss_false =>
       if type_of_expr cond tmap is Some (exist (Gtyp (Fuint 1)) _)
       then exists (vm_true : CEP.t vertex_type) (ct_true ct_false : CEP.t def_expr),
                   Sem_frag_stmts vm_old ct_old ss_true vm_true ct_true tmap
                /\
                   Sem_frag_stmts vm_true (extend_map_with ct_old ct_true) ss_false vm_new ct_false tmap
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

Lemma Sem_frag_stmts_Equal :
forall (ss : HiFP.hfstmt_seq) (vm_old1 vm_old2 : CEP.t vertex_type) (ct_old1 ct_old2 : CEP.t def_expr) (vm_new1 vm_new2 : CEP.t vertex_type) (ct_new1 ct_new2 : CEP.t def_expr) (tmap1 tmap2 : CEP.t ftype),
    CEP.Equal vm_old1 vm_old2 ->
    CEP.Equal ct_old1 ct_old2 ->
    CEP.Equal vm_new1 vm_new2 ->
    CEP.Equal ct_new1 ct_new2 ->
    CEP.Equal tmap1 tmap2 ->
    Sem_frag_stmts vm_old1 ct_old1 ss vm_new1 ct_new1 tmap1 ->
    Sem_frag_stmts vm_old2 ct_old2 ss vm_new2 ct_new2 tmap2
with Sem_frag_stmt_Equal :
forall (s : HiFP.hfstmt) (vm_old1 vm_old2 : CEP.t vertex_type) (ct_old1 ct_old2 : CEP.t def_expr) (vm_new1 vm_new2 : CEP.t vertex_type) (ct_new1 ct_new2 : CEP.t def_expr) (tmap1 tmap2 : CEP.t ftype),
    CEP.Equal vm_old1 vm_old2 ->
    CEP.Equal ct_old1 ct_old2 ->
    CEP.Equal vm_new1 vm_new2 ->
    CEP.Equal ct_new1 ct_new2 ->
    CEP.Equal tmap1 tmap2 ->
    Sem_frag_stmt vm_old1 ct_old1 s vm_new1 ct_new1 tmap1 ->
    Sem_frag_stmt vm_old2 ct_old2 s vm_new2 ct_new2 tmap2.
Proof.
* clear Sem_frag_stmts_Equal.
  induction ss ; simpl Sem_frag_stmts.
  + split.
    - apply CEP.Lemmas.Equal_trans with (m' := vm_new1) ; last by exact H1.
      apply CEP.Lemmas.Equal_trans with (m' := vm_old1) ; last by apply H4.
      apply CEP.Lemmas.Equal_sym ; exact H.
    - apply CEP.Lemmas.Equal_trans with (m' := ct_new1) ; last by exact H2.
      apply CEP.Lemmas.Equal_trans with (m' := ct_old1) ; last by apply H4.
      apply CEP.Lemmas.Equal_sym ; exact H0.
  + intros.
    destruct H4 as [vm' [ct' H4]].
    exists vm', ct'.
    split ;
          first by apply (Sem_frag_stmt_Equal h vm_old1 vm_old2 ct_old1 ct_old2 vm' vm' ct' ct' tmap1 tmap2) ;
                   try assumption ; try apply CEP.Lemmas.Equal_refl ; apply H4.
    by apply (IHss vm' vm' ct' ct' vm_new1 vm_new2 ct_new1 ct_new2 tmap1 tmap2) ;
          try assumption ; try apply CEP.Lemmas.Equal_refl ; apply H4.
* clear Sem_frag_stmt_Equal.
  destruct s ; simpl ; intros ; try by done.
  + (* Sskip *)
    split.
    - apply CEP.Lemmas.Equal_trans with (m' := vm_new1) ; last by exact H1.
      apply CEP.Lemmas.Equal_trans with (m' := vm_old1) ; last by apply H4.
      by apply CEP.Lemmas.Equal_sym, H.
    - apply CEP.Lemmas.Equal_trans with (m' := ct_new1) ; last by exact H2.
      apply CEP.Lemmas.Equal_trans with (m' := ct_old1) ; last by apply H4.
      by apply CEP.Lemmas.Equal_sym, H0.
  + (* Swire *)
    specialize (H3 s).
    destruct (CEP.find s tmap1) ; last by contradiction H4.
    rewrite -H3 ; clear tmap1 tmap2 H3.
    split.
    - destruct H4 as [H4 _].
      intro ; specialize (H4 n).
      destruct (List.nth_error (list_rhs_type_p f0) n) ; last by trivial.
      by rewrite -H -H1 ; exact H4.
    destruct H4 as [_ H4] ; split.
    - destruct H4 as [H4 _].
      intro ; intro.
      by rewrite -H -H1 ; apply H4.
    destruct H4 as [_ H4] ; split.
    - destruct H4 as [H4 _].
      intro ; intro.
      by rewrite -H0 -H2 ; apply H4.
    - destruct H4 as [_ H4].
      intro.
      by rewrite -H2 ; apply H4.
  + (* Sreg *)
    generalize (H3 s) ; intro.
    destruct (CEP.find s tmap1) ; last by contradiction H4.
    rewrite -H5 ; clear H5.
    split.
    - destruct H4 as [H4 _].
      destruct (reset h) ; first by exact H4.
      rewrite (type_of_expr_Equal h0 tmap1 tmap2 H3) in H4.
      rewrite (type_of_expr_Equal h1 tmap1 tmap2 H3) in H4.
      by exact H4.
    destruct H4 as [_ H4] ; split.
    - destruct H4 as [H4 _].
      intro ; specialize (H4 n).
      destruct (List.nth_error (list_rhs_type_p f) n) ; last by trivial.
      rewrite -H -H1.
      destruct (reset h) ; first by exact H4.
      rewrite (type_of_expr_Equal h0 tmap1 tmap2 H3) in H4.
      by exact H4.
    destruct H4 as [_ H4] ; split.
    - destruct H4 as [H4 _].
      rewrite (type_of_expr_Equal (clock h) tmap1 tmap2 H3) in H4.
      by exact H4.
    destruct H4 as [_ H4] ; split.
    - destruct H4 as [H4 _].
      destruct (match f with
                | Gtyp _ => Some [:: Eref (Eid (var:=ProdVarOrder.T) s)]
                | _ => list_rhs_ref_p (Eid (var:=ProdVarOrder.T) s) f
                end) eqn: Hf ; rewrite Hf ; rewrite Hf in H4 ; clear Hf ;
            last by contradiction H4.
      intro ; specialize (H4 n).
      destruct (List.nth_error l n) eqn: Hl ; rewrite Hl ; rewrite Hl in H4 ; clear Hl ;
            last by trivial.
      by rewrite -H2 ; exact H4.
    destruct H4 as [_ H4] ; split.
    - destruct H4 as [H4 _].
      intro ; intro.
      by rewrite -H -H1 ; apply H4.
    - destruct H4 as [_ H4].
      intro ; intro.
      by rewrite -H0 -H2 ; apply H4.
  + (* Snode *)
    rewrite (type_of_expr_Equal h tmap1 tmap2 H3) in H4.
    destruct (type_of_expr h tmap2) as [[newft _]|] ; last by contradiction H4.
    clear tmap1 tmap2 H3.
    split.
    - destruct H4 as [H4 _].
      intro ; specialize (H4 n).
      destruct (List.nth_error (list_rhs_type_p newft) n) ; last by trivial.
      by rewrite -H -H1 ; exact H4.
    destruct H4 as [_ H4] ; split.
    - destruct H4 as [H4 _].
      intro ; intro.
      by rewrite -H -H1 ; apply H4.
    - destruct H4 as [_ H4].
      apply CEP.Lemmas.Equal_trans with (m' := ct_new1) ; last by exact H2.
      apply CEP.Lemmas.Equal_trans with (m' := ct_old1) ; last by exact H4.
      by apply CEP.Lemmas.Equal_sym, H0.
  + (* Sfcnct *)
    admit.
  + (* Sinvalid *)
    admit.
  + (* Swhen *)
    admit.
Admitted.

Lemma Sem_frag_stmts_cat :
forall (ss1 ss2 : HiFP.hfstmt_seq) (vm_old : CEP.t vertex_type) (ct_old : CEP.t def_expr)
       (vm_new : CEP.t vertex_type) (ct_new : CEP.t def_expr) (tmap : CEP.t ftype),
        Sem_frag_stmts vm_old ct_old (Qcat ss1 ss2) vm_new ct_new tmap
    <->
        exists (vm_temp : CEP.t vertex_type) (ct_temp : CEP.t def_expr),
                Sem_frag_stmts vm_old ct_old ss1 vm_temp ct_temp tmap
            /\
                Sem_frag_stmts vm_temp ct_temp ss2 vm_new ct_new tmap.
Proof.
induction ss1.
* split ; intro.
  + exists vm_old, ct_old.
    split.
    - simpl ; split ; apply CEP.Lemmas.Equal_refl.
    - simpl Qcat in H ; exact H.
  + destruct H as [vm_temp [ct_temp [H H0]]].
    simpl Sem_frag_stmts in H.
    apply Sem_frag_stmts_Equal with (vm_old1 := vm_temp) (vm_old2 := vm_old)
                                    (ct_old1 := ct_temp) (ct_old2 := ct_old)
                                    (vm_new1 := vm_new) (ct_new1 := ct_new) (tmap1 := tmap) ;
          try by apply CEP.Lemmas.Equal_refl.
    - 1,2: apply CEP.Lemmas.Equal_sym, H.
    - exact H0.
* split ; intro.
  + simpl Sem_frag_stmts in H.
    destruct H as [vm' [ct' [H H0]]].
    apply IHss1 in H0.
    destruct H0 as [vm_temp [ct_temp [H0 H1]]].
    exists vm_temp, ct_temp.
    split ; last by exact H1.
    simpl Sem_frag_stmts.
    exists vm', ct'.
    split ; assumption.
  + destruct H as [vm_temp [ct_temp [H H1]]].
    simpl Sem_frag_stmts in H.
    destruct H as [vm' [ct' [H H0]]].
    simpl Sem_frag_stmts.
    exists vm', ct'.
    split ; first by exact H.
    specialize (IHss1 ss2 vm' ct' vm_new ct_new tmap).
    apply IHss1.
    exists vm_temp, ct_temp.
    split ; assumption.
Qed.

Lemma Sem_frag_stmts_compatible :
forall (ss : HiFP.hfstmt_seq) (vm_old : CEP.t vertex_type) (ct_old : CEP.t def_expr)
       (vm_new : CEP.t vertex_type) (ct_new : CEP.t def_expr) (tmap : CEP.t ftype),
    Sem_frag_stmts vm_old ct_old ss vm_new ct_new tmap ->
           CEP.submap vm_old vm_new /\ subdomain ct_old ct_new
        /\ (vm_and_ct_compatible vm_old ct_old ->
                vm_and_ct_compatible vm_new ct_new)
with Sem_frag_stmt_compatible :
forall (s : HiFP.hfstmt) (vm_old : CEP.t vertex_type) (ct_old : CEP.t def_expr)
       (vm_new : CEP.t vertex_type) (ct_new : CEP.t def_expr) (tmap : CEP.t ftype),
    Sem_frag_stmt vm_old ct_old s vm_new ct_new tmap ->
           CEP.submap vm_old vm_new /\ subdomain ct_old ct_new
        /\ (vm_and_ct_compatible vm_old ct_old ->
                vm_and_ct_compatible vm_new ct_new).
Proof.
* clear Sem_frag_stmts_compatible.
  induction ss ; simpl Sem_frag_stmts ; intros.
  + split.
    - intro ; rewrite (proj1 H k) ; destruct (CEP.find k vm_new) ; done.
    split.
    - intro ; rewrite (proj2 H k) ; destruct (CEP.find k ct_new) ; done.
    - intro ; intro.
      rewrite -(proj1 H) -(proj2 H).
      apply H0.
  + destruct H as [vm' [ct' [Hh Hss]]].
    specialize (Sem_frag_stmt_compatible h vm_old ct_old vm' ct' tmap Hh).
    specialize (IHss vm' ct' vm_new ct_new tmap Hss).
    split.
    - apply (CEP.Lemmas.submap_trans (proj1 Sem_frag_stmt_compatible)), IHss.
    split.
    - apply (subdomain_trans ct') ; first by apply Sem_frag_stmt_compatible.
      apply IHss.
    - intro ; intro.
      destruct Sem_frag_stmt_compatible as [_ [_ Sem_frag_stmt_compatible]].
      destruct IHss as [_ [_ IHss]].
      apply IHss, Sem_frag_stmt_compatible, H.
* clear Sem_frag_stmt_compatible.
  induction s ; simpl Sem_frag_stmt ; intros.
  + (* Sskip *)
    split.
    - intro.
      rewrite (proj1 H) ; destruct (CEP.find k vm_new) ; done.
    split.
    - intro.
      rewrite (proj2 H) ; destruct (CEP.find k ct_new) ; done.
    - intro ; intro.
      rewrite -(proj1 H) -(proj2 H).
      by apply H0.
  + (* Swire *)
    destruct (CEP.find s tmap) as [newft|] ; last by contradiction H.
    split ; last (split ; last intro) ; intro k.
    1-3: destruct (fst k == fst s) eqn: Hfst ; move /eqP : Hfst => Hfst ;
          last (destruct H as [_ [Hvm [Hct _]]] ;
                   specialize (Hvm (fst k) (snd k)) ; specialize (Hct (fst k) (snd k)) ;
                   rewrite -surjective_pairing in Hvm, Hct ;
                   try (rewrite -Hvm ; last (by left ; done)) ;
                   try (rewrite -Hct ; last (by left ; done))).
    2: by destruct (CEP.find k vm_old) ; done.
    3: by destruct (CEP.find k ct_old) ; done.
    4: by apply H0.
    1-3: destruct (snd k < snd s) eqn: Hsnd_small ;
          first (destruct H as [_ [Hvm [Hct _]]] ;
                    specialize (Hvm (fst k) (snd k)) ; specialize (Hct (fst k) (snd k)) ;
                    rewrite Hsnd_small -surjective_pairing in Hvm, Hct ;
                    try (rewrite -Hvm ; last (by right ; left ; done)) ;
                    try (rewrite -Hct ; last (by right ; left ; done))).
    1: by destruct (CEP.find k vm_old) ; done.
    2: by destruct (CEP.find k ct_old) ; done.
    3: by apply H0.
    1-3: destruct (size_of_ftype newft + snd s <= snd k) eqn: Hsnd_large ;
          first (destruct H as [_ [Hvm [Hct _]]] ;
                    specialize (Hvm (fst k) (snd k)) ; specialize (Hct (fst k) (snd k)) ;
                    rewrite Hsnd_small -surjective_pairing in Hvm, Hct ;
                    try (rewrite -Hvm ; last (by right ; right ; done)) ;
                    try (rewrite -Hct ; last (by right ; right ; done))).
    1: by destruct (CEP.find k vm_old) ; done.
    2: by destruct (CEP.find k ct_old) ; done.
    3: by apply H0.
    1-3: destruct H as [Hvm [_ [_ Hct]]].
    1-3: specialize (Hvm (snd k - snd s)) ; specialize (Hct (snd k - snd s)).
    1-3: apply negbT in Hsnd_small.
    1-3: rewrite -leqNgt in Hsnd_small.
    1-3: apply negbT in Hsnd_large.
    1-3: rewrite -ltnNge addnC -ltn_subLR // in Hsnd_large.
    1-3: specialize (Hct Hsnd_large).
    1-3: rewrite -(list_rhs_type_p_size newft) in Hsnd_large.
    1-3: move /ltP : Hsnd_large => Hsnd_large.
    1-3: generalize (proj2 (List.nth_error_Some (list_rhs_type_p newft) (snd k - snd s)) Hsnd_large) ; intro.
    1-3: destruct (List.nth_error (list_rhs_type_p newft) (snd k - snd s)) ; last by contradiction H.
    1-3: rewrite -Hfst subnK // nat_of_binK -surjective_pairing in Hvm, Hct.
    rewrite (proj1 Hvm) //.
    rewrite Hct //.
    rewrite (proj2 Hvm) Hct //.
  + (* Sreg *)
    destruct (CEP.find s tmap) as [newft|] ; last by contradiction H.
    destruct H as [_ H].
    split ; last (split ; last intro) ; intro k.
    1-3: destruct (fst k == fst s) eqn: Hfst ; move /eqP : Hfst => Hfst ;
          last (destruct H as [_ [_ [_ [Hvm Hct]]]] ;
                   specialize (Hvm (fst k) (snd k)) ; specialize (Hct (fst k) (snd k)) ;
                   rewrite -surjective_pairing in Hvm, Hct ;
                   try (rewrite -Hvm ; last (by left ; done)) ;
                   try (rewrite -Hct ; last (by left ; done))).
    2: by destruct (CEP.find k vm_old) ; done.
    3: by destruct (CEP.find k ct_old) ; done.
    4: by apply H0.
    1-3: destruct (snd k < snd s) eqn: Hsnd_small ;
          first (destruct H as [_ [_ [_ [Hvm Hct]]]] ;
                    specialize (Hvm (fst k) (snd k)) ; specialize (Hct (fst k) (snd k)) ;
                    rewrite Hsnd_small -surjective_pairing in Hvm, Hct ;
                    try (rewrite -Hvm ; last (by right ; left ; done)) ;
                    try (rewrite -Hct ; last (by right ; left ; done))).
    1: by destruct (CEP.find k vm_old) ; done.
    2: by destruct (CEP.find k ct_old) ; done.
    3: by apply H0.
    1-3: destruct (size_of_ftype newft + snd s <= snd k) eqn: Hsnd_large ;
          first (destruct H as [_ [_ [_ [Hvm Hct]]]] ;
                    specialize (Hvm (fst k) (snd k)) ; specialize (Hct (fst k) (snd k)) ;
                    rewrite Hsnd_small -surjective_pairing in Hvm, Hct ;
                    try (rewrite -Hvm ; last (by right ; right ; done)) ;
                    try (rewrite -Hct ; last (by right ; right ; done))).
    1: by destruct (CEP.find k vm_old) ; done.
    2: by destruct (CEP.find k ct_old) ; done.
    3: by apply H0.
    1-3: destruct H as [Hvm [_ [Hct _]]].
    1-3: specialize (list_rhs_expr_p_size newft (Eref (Eid (var:=ProdVarOrder.T) s))) ; intro.
    1-3: destruct (list_rhs_expr_p (Eref (Eid (var:=ProdVarOrder.T) s)) newft) eqn: H1 ;
          simpl in H1 ; rewrite H1 in Hct ; last by contradiction Hct.
    1-3: specialize (Hvm (snd k - snd s)) ; specialize (Hct (snd k - snd s)).
    1-3: apply negbT in Hsnd_small.
    1-3: rewrite -leqNgt in Hsnd_small.
    1-3: apply negbT in Hsnd_large.
    1-3: rewrite -ltnNge addnC -ltn_subLR // -H in Hsnd_large.
    (*specialize (Hct Hsnd_large).
    rewrite -(list_rhs_type_p_size f) in H.*)
    1-3: move /ltP : Hsnd_large => Hsnd_large.
    1-3: generalize (proj2 (List.nth_error_Some l (snd k - snd s)) Hsnd_large) ; intro.
    1-3: rewrite H -(list_rhs_type_p_size newft) in Hsnd_large.
    1-3: generalize (proj2 (List.nth_error_Some (list_rhs_type_p newft) (snd k - snd s)) Hsnd_large) ; intro.
    1-3: destruct (List.nth_error (list_rhs_type_p newft) (snd k - snd s)) ; last by done.
    1-3: destruct (List.nth_error l (snd k - snd s)) ; last by done.
    1-3: rewrite -Hfst subnK // nat_of_binK -surjective_pairing in Hvm, Hct.
    rewrite (proj1 Hvm) //.
    rewrite Hct //.
    rewrite (proj2 Hvm) Hct //.
  + (* Smem: TBD *)
    contradiction H.
  + (* Sinst *)
    contradiction H.
  + (* Snode *)
    destruct (type_of_expr h tmap) as [[newft _]|] ; last by contradiction H.
    split ; last (split ; last intro) ; intro k.
    1-3: destruct (fst k == fst s) eqn: Hfst ; move /eqP : Hfst => Hfst ;
          last (destruct H as [_ [Hvm Hct]] ;
                specialize (Hvm (fst k) (snd k)) ;
                rewrite -surjective_pairing in Hvm ;
                try rewrite -(Hvm (or_introl Hfst)) // ;
                try rewrite -Hct).
    3: by destruct (CEP.find k ct_old) ; done.
    4: by apply H0.
    1-3: destruct (snd k < snd s) eqn: Hsnd_small ;
          first (destruct H as [_ [Hvm Hct]] ;
                 specialize (Hvm (fst k) (snd k)) ;
                 rewrite -surjective_pairing in Hvm ;
                 try rewrite -(Hvm (or_intror (or_introl Hsnd_small))) // ;
                 try rewrite -Hct).
    2: by destruct (CEP.find k ct_old) ; done.
    3: by apply H0.
    1-3: destruct (size_of_ftype newft + snd s <= snd k) eqn: Hsnd_large ;
          first (destruct H as [_ [Hvm Hct]] ;
                 specialize (Hvm (fst k) (snd k)) ;
                 rewrite -surjective_pairing in Hvm ;
                 try rewrite -(Hvm (or_intror (or_intror Hsnd_large))) // ;
                 try rewrite -Hct).
    2: by destruct (CEP.find k ct_old) ; done.
    3: by apply H0.
    1-3: destruct H as [Hvm [_ Hct]].
    1-3: generalize (list_rhs_type_p_size newft) ; intro.
    1-3: specialize (Hvm (snd k - snd s)).
    1-3: apply negbT in Hsnd_small.
    1-3: rewrite -leqNgt in Hsnd_small.
    1-3: apply negbT in Hsnd_large.
    1-3: rewrite -ltnNge addnC -ltn_subLR // -H in Hsnd_large.
    (*specialize (Hct Hsnd_large).*)
    1-3: move /ltP : Hsnd_large => Hsnd_large.
    1-3: generalize (proj2 (List.nth_error_Some (list_rhs_type_p newft) (snd k - snd s)) Hsnd_large) ; intro.
    1-3: destruct (List.nth_error (list_rhs_type_p newft) (snd k - snd s)) ; last by done.
    1-3: rewrite -Hfst subnK // nat_of_binK -surjective_pairing in Hvm.
    - by rewrite (proj1 Hvm) //.
    - by rewrite Hct ; destruct (CEP.find k ct_new) ; done.
    - specialize (H0 k) ; rewrite (proj1 Hvm) Hct in H0.
      rewrite (proj2 Hvm) //.
  + (* Sfcnct *)
    destruct h0.
    1-6: destruct H.
    1-6: split ;
          first by (intro ; rewrite H ; destruct (CEP.find k vm_new) ; done).
    1-6: generalize (list_lhs_ref_p_size tmap h) ; intro.
    1-6: generalize (list_lhs_ref_p_type tmap h) ; intro.
    1-6: destruct (type_of_ref h tmap) as [ft_ref|] ; last by done.
    1: destruct (type_of_expr (Econst ProdVarOrder.T f b) tmap) as [[ft_expr _]|] ; last by done.
    2: destruct (type_of_expr (Ecast u h0) tmap) as [[ft_expr _]|] ; last by done.
    3: destruct (type_of_expr (Eprim_unop e h0) tmap) as [[ft_expr _]|] ; last by done.
    4: destruct (type_of_expr (Eprim_binop e h0_1 h0_2) tmap) as [[ft_expr _]|] ; last by done.
    5: destruct (type_of_expr (Emux h0_1 h0_2 h0_3) tmap) as [[ft_expr _]|] ; last by done.
    6: destruct (type_of_expr (Evalidif h0_1 h0_2) tmap) as [[ft_expr _]|] ; last by done.
    1-6: destruct H0.
    1-6: apply connect_type_compatible_size in H0.
    1-6: destruct (list_lhs_ref_p h tmap) as [[input_list ft_ref']|] ; last by done.
    1-6: rewrite -H2 in H1 ; clear ft_ref' H2.
    1: generalize (list_rhs_expr_p_size ft_expr (Econst ProdVarOrder.T f b)) ; intro ;
       destruct (list_rhs_expr_p (Econst ProdVarOrder.T f b) ft_expr) as [expr_list|] ; last by done.
    2: generalize (list_rhs_expr_p_size ft_expr (Ecast u h0)) ; intro ;
       destruct (list_rhs_expr_p (Ecast u h0) ft_expr) as [expr_list|] ; last by done.
    3: generalize (list_rhs_expr_p_size ft_expr (Eprim_unop e h0)) ; intro ;
       destruct (list_rhs_expr_p (Eprim_unop e h0) ft_expr) as [expr_list|] ; last by done.
    4: generalize (list_rhs_expr_p_size ft_expr (Eprim_binop e h0_1 h0_2)) ; intro ;
       destruct (list_rhs_expr_p (Eprim_binop e h0_1 h0_2) ft_expr) as [expr_list|] ; last by done.
    5: generalize (list_rhs_expr_p_size ft_expr (Emux h0_1 h0_2 h0_3)) ; intro ;
       destruct (list_rhs_expr_p (Emux h0_1 h0_2 h0_3) ft_expr) as [expr_list|] ; last by done.
    6: generalize (list_rhs_expr_p_size ft_expr (Evalidif h0_1 h0_2)) ; intro ;
       destruct (list_rhs_expr_p (Evalidif h0_1 h0_2) ft_expr) as [expr_list|] ; last by done.
    1-6: split ; intro ; last (intro k ; specialize (H4 k)).
    1-12: specialize (H k) ; try rewrite -H.
    1-12: destruct (k \in input_list) eqn: Hv;
          last by (destruct H3 as [_ H3] ;
                   specialize (H3 k) ; rewrite Hv in H3 ;
                   rewrite -H3 ; destruct (CEP.find k ct_old) ; done).
    1-12: destruct H3 as [H3 _] ;
          specialize (H3 (index k input_list)).
    1-12: generalize (nth_index k Hv) ; intro Hnth_index ;
          rewrite -index_mem in Hv ;
          move /ltP : Hv => Hv ;
          generalize (proj2 (List.nth_error_Some input_list (index k input_list)) Hv) ; intro ;
          rewrite H1 H0 -H2 in Hv ;
          apply List.nth_error_Some in Hv.
    1-12: destruct (List.nth_error input_list (index k input_list)) eqn: Hi ; last (by done).
    1-12: destruct (List.nth_error expr_list (index k input_list)) ; last (by done).
    1-12: replace k0 with k in H3
          by (clear -Hnth_index Hi ;
              induction input_list ; simpl in Hnth_index ; simpl in Hi ; first (by done) ;
              destruct (a == k) ; simpl nth in Hnth_index ; simpl List.nth_error in Hi ;
              first (by rewrite -Hnth_index ; injection Hi ; done) ;
              last (by apply IHinput_list ; assumption)).
    1-12: rewrite (proj2 H3) //.
    1-6:  destruct (CEP.find k vm_old) as [[]|] ; try (by done).
    1-18: rewrite H4 in H3 ; by contradiction (proj1 H3).
    (* Remains the case of a Sfcnct between two references (may be bidirectional) *)
    destruct H.
    split ; first by (intro ; rewrite H ; destruct (CEP.find k vm_new) ; done).
    generalize (list_lhs_ref_p_size tmap h) ; intro.
    generalize (list_lhs_ref_p_type tmap h) ; intro.
    destruct (list_lhs_ref_p h tmap) as [[lst_tgt ft_tgt]|] ; last by contradiction H0.
    generalize (list_lhs_ref_p_size tmap h0) ; intro.
    generalize (list_lhs_ref_p_type tmap h0) ; intro.
    destruct (list_lhs_ref_p h0 tmap) as [[lst_src ft_src]|] ; last by contradiction H0.
    destruct H0 as [H0 [H5 H6]].
    (*apply connect_type_compatible_size in H1.*)
    (*rewrite H1 -H4 in H2. ?? *)
    split ; intro ; last (intro k ; specialize (H k) ; rewrite -H ; specialize (H7 k)).
    1-2: clear H vm_new.
    1-2: specialize (H6 k).
    1-2: destruct ((k \in lst_tgt) || (k \in lst_src)) eqn: Hv ; rewrite Hv in H6 ;
          last by (rewrite -H6 ; destruct (CEP.find k ct_old) ; done).
    1-2: clear H6 ; move /orP : Hv => Hv.
    1-2: symmetry in H1, H3.
    1-2: generalize (connect_preserves_compatibility ct_old ct_new ft_tgt ft_src
                     h h0 lst_tgt lst_src true false k H5 H0 H1 H3 Hv) ; intro.
    - destruct (CEP.find k ct_new) ; first by done.
      by apply H ; reflexivity.
    - destruct (CEP.find k vm_old) as [[]|] ; try apply H, H7 ;
      by contradict H7 ; apply H, H7.
  + (* Sinvalid *)
    destruct H.
    split ; first by (intro ; rewrite H ; destruct (CEP.find k vm_new) ; done).
    generalize (list_lhs_ref_p_size tmap h) ; intro.
    generalize (list_lhs_ref_p_type tmap h) ; intro.
    destruct (list_lhs_ref_p h tmap) as [[input_list ft_tgt]|] ; last by contradiction H0.
    destruct H0 as [H0 H3].
    split ; intro ; last (intro k ; specialize (H k) ; rewrite -H ; specialize (H4 k)).
    1-2: clear vm_new H.
    1-2: specialize (H3 k).
    1-2: destruct (k \in input_list) eqn: Hv ; rewrite Hv in H3 ;
          last by (rewrite -H3 ; destruct (CEP.find k ct_old) ; done).
    1-2: specialize (H0 (index k input_list)).
    1-2: generalize (nth_index k Hv) ; intro.
    1-2: rewrite -index_mem in Hv.
    1-2: move /ltP : Hv => Hv.
    1-2: destruct (List.nth_error input_list (index k input_list)) eqn: Hi ;
          last by (apply List.nth_error_Some in Hv ;
                   rewrite Hi // in Hv).
    1-2: apply List.nth_error_nth with (d := k) in Hi.
    1-2: replace k0 with k in H0 ;
               last by (clear -Hi H ;
                   induction input_list ; simpl in Hi ; first (by rewrite Hi //) ;
                   simpl in H ; destruct (a == k) ; first (by simpl nth in H ; rewrite -Hi -H //) ;
                   simpl nth in H ; apply IHinput_list ; assumption).
    1-2: rewrite (proj2 H0) //.
    destruct (CEP.find k vm_old) as [[]|]; try (by done) ;
    rewrite H4 in H0 ; contradiction (proj1 H0) ; reflexivity.
  + (* Swhen *)
    rename h into cond ; rename h0 into ss_true ; rename h1 into ss_false.
    destruct (type_of_expr cond tmap) as [[[[[|[|]]| | | | | |]| |] _]|] ; try by contradiction H.
    destruct H as [vm_true [ct_true [ct_false [Ht [Hf H]]]]].
    generalize (Sem_frag_stmts_compatible ss_true vm_old ct_old vm_true ct_true tmap Ht) ; intro.
    assert (vm_and_ct_compatible vm_old ct_old -> vm_and_ct_compatible vm_true (extend_map_with ct_old ct_true)).
          intro ; intro.
          destruct H0 as [H0 [_ H2]].
          specialize (H0 v) ; specialize (H2 H1 v).
          specialize (H1 v).
          rewrite /extend_map_with CEP.Lemmas.map2_1bis //.
          by destruct (CEP.find v vm_true) as [[]|] ;
             destruct (CEP.find v vm_old) as [[]|] ;
             destruct (CEP.find v ct_old) ; try done ;
             specialize (H0 _ Logic.eq_refl) ; done.
    specialize (Sem_frag_stmts_compatible ss_false vm_true (extend_map_with ct_old ct_true) vm_new ct_false tmap Hf).
    split ;
          first by apply (CEP.Lemmas.submap_trans (proj1 H0)), Sem_frag_stmts_compatible.
    split.
    - intro.
      destruct H0 as [_ [H0 _]].
      destruct Sem_frag_stmts_compatible as [_ [Sem_frag_stmts_compatible _]].
      specialize (H k) ; specialize (H0 k) ; specialize (Sem_frag_stmts_compatible k).
      rewrite H CEP.Lemmas.map2_1bis /Swhen_map2_helper //.
      rewrite /extend_map_with CEP.Lemmas.map2_1bis // in Sem_frag_stmts_compatible.
      destruct (CEP.find k ct_true) as [[]|] ;
      destruct (CEP.find k ct_false) as [[]|] ; try by done.
      destruct (h == h0) ; by done.
    - intro ; intro.
      destruct H0 as [_ [_ H0]].
      destruct Sem_frag_stmts_compatible as [H4 [_ Sem_frag_stmts_compatible]].
      specialize (H v) ; specialize (H0 H2 v) ;
      specialize (H4 v) ;
      specialize (Sem_frag_stmts_compatible (H1 H2) v).
      rewrite H CEP.Lemmas.map2_1bis // /Swhen_map2_helper.
      destruct (CEP.find v vm_new) as [[]|] eqn: Hvm_new ;
      destruct (CEP.find v vm_true) as [[]|] eqn: Hvm_true ;
      destruct (CEP.find v ct_true) as [[]|] eqn: Hct_true ;
      destruct (CEP.find v ct_false) as [[]|] eqn: Hct_false ; try done ;
      try (by specialize (H4 _ Logic.eq_refl) ; done) ;
      try (by destruct (h == h0) ; done).
      by destruct (h1 == h2) ; done.
Qed.

Lemma Sem_frag_stmts_component :
forall (ss : HiFP.hfstmt_seq) (vm_old : CEP.t vertex_type) (ct_old : CEP.t def_expr)
       (vm_new : CEP.t vertex_type) (ct_new : CEP.t def_expr) (tmap : CEP.t ftype),
    vm_and_ct_compatible vm_old ct_old ->
        Sem_frag_stmts vm_old ct_old (component_stmts_of ss) vm_new ct_new tmap ->
           CEP.submap ct_old ct_new
with Sem_frag_stmt_component :
forall (s : HiFP.hfstmt) (vm_old : CEP.t vertex_type) (ct_old : CEP.t def_expr)
       (vm_new : CEP.t vertex_type) (ct_new : CEP.t def_expr) (tmap : CEP.t ftype),
    vm_and_ct_compatible vm_old ct_old ->
        Sem_frag_stmts vm_old ct_old (component_stmt_of s) vm_new ct_new tmap ->
           CEP.submap ct_old ct_new.
Proof.
* clear Sem_frag_stmts_component.
  induction ss ; simpl ; intros ; first by apply CEP.Lemmas.Equal_submap, H0.
  apply Sem_frag_stmts_cat in H0.
  destruct H0 as [vm_temp [ct_temp [H0 H1]]].
  generalize (proj2 (proj2 (Sem_frag_stmts_compatible (component_stmt_of h) vm_old ct_old vm_temp ct_temp tmap H0)) H) ; intro.
  apply Sem_frag_stmt_component in H0 ; last by exact H.
  apply IHss in H1 ; last by exact H2.
  by apply (CEP.Lemmas.submap_trans H0 H1).
* clear Sem_frag_stmt_component.
  destruct s ; simpl ; intros ; try by (apply CEP.Lemmas.Equal_submap, H0).
  + (* Swire *)
    destruct H0 as [vm' [ct' [H0 [_ H1]]]].
    destruct (CEP.find s tmap) as [newft|] ; last by contradiction H0.
    intro.
    destruct (fst k == fst s) eqn: Hfst ; move /eqP : Hfst => Hfst ;
          last by (destruct H0 as [_ [_ [H0 _]]] ;
                   specialize (H0 (fst k) (snd k)) ;
                   rewrite -surjective_pairing H1 in H0 ;
                   rewrite H0 ; last (by left ; exact Hfst) ;
                   destruct (CEP.find k ct_new) ; by done).
    destruct (snd k < snd s) eqn: Hsnd_small ;
          first by (destruct H0 as [_ [_ [H0 _]]] ;
                    specialize (H0 (fst k) (snd k)) ;
                    rewrite -surjective_pairing H1 in H0 ;
                    rewrite H0 ; last (by right ; left ; exact Hsnd_small) ;
                    destruct (CEP.find k ct_new) ; by done).
    destruct (size_of_ftype newft + snd s <= snd k) eqn: Hsnd_large ;
          first by (destruct H0 as [_ [_ [H0 _]]] ;
                    specialize (H0 (fst k) (snd k)) ;
                    rewrite -surjective_pairing H1 in H0 ;
                    rewrite H0 ; last (by right ; right ; exact Hsnd_large) ;
                    destruct (CEP.find k ct_new) ; by done).
    destruct H0 as [H0 _].
    specialize (H k).
    specialize (H0 (snd k - snd s)).
    generalize (List.nth_error_Some (list_rhs_type_p newft) (snd k - snd s)) ; intro.
    replace (length (list_rhs_type_p newft)) with (size_of_ftype newft) in H2
          by (rewrite -list_rhs_type_p_size ; reflexivity).
    rewrite ltnNge in Hsnd_small ; apply negbFE in Hsnd_small.
    rewrite leqNgt addnC -ltn_subLR // in Hsnd_large ; apply negbFE in Hsnd_large.
    destruct H2 as [_ H2] ; specialize (H2 (simplssrlib.Nats.ltn_lt Hsnd_large)).
    destruct (List.nth_error (list_rhs_type_p newft) (snd k - snd s)) ; last by contradiction H2.
    rewrite -Hfst subnK // nat_of_binK -surjective_pairing in H0.
    rewrite (proj1 H0) in H.
    rewrite H //.
  + (* Sreg -- should be similar to Swire *)
    admit.
  + (* Smem *)
    destruct H0 as [vm' [ct' [H0 _]]] ; contradiction H0.
  + (* Sinst *)
    destruct H0 as [vm' [ct' [H0 _]]] ; contradiction H0.
  + (* Snode -- should be similar to Swire *)
    admit.
  + (* Swhen *)
    rename h into cond ; rename h0 into ss_true ; rename h1 into ss_false.
    apply Sem_frag_stmts_cat in H0.
    destruct H0 as [vm_true [ct_true [H0_true H0_false]]].
    generalize (proj2 (proj2 (Sem_frag_stmts_compatible (component_stmts_of ss_true) vm_old ct_old vm_true ct_true tmap H0_true)) H) ; intro.
    apply Sem_frag_stmts_component in H0_true ; last by exact H.
    apply Sem_frag_stmts_component in H0_false ; last by exact H0.
    by apply (CEP.Lemmas.submap_trans H0_true H0_false).
Admitted.

(*---------------------------------------------------------------------------*)
(* Semantics of module                                                       *)

Definition ports_stmts_tmap (pp : seq HiFP.hfport) (ss : HiFP.hfstmt_seq) (vm : CEP.t vertex_type) : option (CEP.t ftype) :=
match ports_tmap pp vm with
| Some pmap =>
    match stmts_tmap (pmap, pmap) ss vm with
    | Some (tmap, _) => Some tmap
    | None => None
    end
| None => None
end.

Definition Sem (F : HiFP.hfmodule) (vm : CEP.t vertex_type) (ct : CEP.t def_expr) : Prop :=
(* The predicate returns True if G = (vm, ct) conforms to F.
   (If F has errors, there is no such G.)
   (If F has implicit width components, then there are many such Gs.)

   Problem: I made some assumption about identifiers of aggregate-type components;
   is that what you need? *)
match F with
| FInmod n pp ss =>
    match ports_stmts_tmap pp ss vm with
    | Some tmap =>
           (forall v1 v2: N,
                match CEP.find (v1, v2) tmap with
                | Some (Gtyp _)
                | None => True
                | _ => (* (v1, v2) identifies an aggregate-type component;
                          then there should not be any other component with the same v1 *)
                       forall v2' : N, v2' <> v2 -> CEP.find (v1, v2') tmap = None
                end)
        /\
           (exists (vm' : CEP.t vertex_type) (ct' : CEP.t def_expr),
                  Sem_frag_ports (CEP.empty vertex_type)
                                 (CEP.empty def_expr)
                                 pp vm' ct' tmap
               /\
                  Sem_frag_stmts vm' ct' ss vm ct tmap)
    | None => False
    end
| FExmod _ _ _ => False
 end.
