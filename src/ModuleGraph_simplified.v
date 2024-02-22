From Coq Require Import ZArith (* for Nat.eq_dec *).
From simplssrlib Require Import SsrOrder FMaps Nats Var ZAriths.
From nbits Require Import NBits.
From firrtl Require Import Env Firrtl HiEnv HiFirrtl. (* for hfmodule and its parts *)
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq fintype.

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
* rewrite CEP.Lemmas.find_add_eq ; last by rewrite /HiFirrtl.PVM.SE.eq Hv //.
  move /eqP : Hv => Hv ; rewrite Hv H //.
* rewrite CEP.Lemmas.find_add_neq ; last by rewrite /HiFirrtl.PVM.SE.eq Hv //.
  destruct (CEP.find v0 tmap) ; done.
Qed.

Lemma submap_add_add {T : Type} : forall (tmap1 tmap2 : CEP.t T) (v : CEP.key) (t : T),
   submap tmap1 tmap2 -> submap (CEP.add v t tmap1) (CEP.add v t tmap2).
Proof.
unfold submap.
intros.
destruct (v0 == v) eqn: Hv.
* rewrite CEP.Lemmas.find_add_eq ; last by rewrite /HiFirrtl.PVM.SE.eq Hv //.
  rewrite CEP.Lemmas.find_add_eq ; last by rewrite /HiFirrtl.PVM.SE.eq Hv //.
  reflexivity.
* rewrite CEP.Lemmas.find_add_neq ; last by rewrite /HiFirrtl.PVM.SE.eq Hv //.
  rewrite CEP.Lemmas.find_add_neq ; last by rewrite /HiFirrtl.PVM.SE.eq Hv //.
  apply H.
Qed.

(*---------------------------------------------------------------------------*)
(* Properties of type_of_ref and of type_of_expr                             *)

Lemma type_of_ref_submap : forall (ref : HiFP.href) (tmap1 tmap2 : CEP.t ftype),
   submap tmap1 tmap2 ->
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

Lemma type_of_expr_submap : forall (expr : HiFP.hfexpr) (tmap1 tmap2 : CEP.t ftype),
   submap tmap1 tmap2 ->
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

Lemma stmts_submap:
   forall (vm : CEP.t vertex_type) (ss : HiFP.hfstmt_seq) (tmap scope : CEP.t ftype),
      submap scope tmap ->
         match stmts_tmap (tmap, scope) ss vm with
         | Some (tmap', scope') => submap scope' tmap' /\ submap tmap tmap' /\ submap scope scope'
         | None => True
         end
with stmt_submap :
   forall (vm : CEP.t vertex_type) (s : HiFP.hfstmt) (tmap scope : CEP.t ftype),
      submap scope tmap ->
         match stmt_tmap (tmap, scope) s vm with
         | Some (tmap', scope') => submap scope' tmap' /\ submap tmap tmap' /\ submap scope scope'
         | None => True
         end.
Proof.
* clear stmts_submap.
  induction ss.
  + unfold stmts_tmap.
    intros ; split ; first by exact H.
    by split ; apply submap_refl.
  + intros.
    simpl stmts_tmap.
    specialize stmt_submap with (vm := vm) (s := h) (tmap := tmap) (scope := scope).
    destruct (stmt_tmap (tmap, scope) h vm) as [[tmap' scope']|] ; last by trivial.
    specialize IHss with (tmap := tmap') (scope := scope').
    destruct (stmts_tmap (tmap', scope') ss vm) as [[tmap'' scope'']|] ; last by trivial.
    split.
    - apply IHss, stmt_submap, H.
    split.
    - apply (submap_trans tmap') ; first by apply stmt_submap.
      by apply IHss, stmt_submap, H.
    - apply (submap_trans scope') ; first by apply stmt_submap.
      by apply IHss, stmt_submap, H.
* clear stmt_submap.
  destruct s ; simpl ; intros ; try trivial.
  + (* Sskip *) split ; first by exact H.
    by split ; apply submap_refl.
  + (* Swire *)
    destruct (CEP.find s tmap) eqn: Hfind ; first by trivial.
    destruct (code_type_find_vm_widths f s vm) as [[newt _]|] ; last by trivial.
    split.
    - by apply submap_add_add, H.
    split.
    - by apply submap_add, Hfind.
    - apply submap_add.
      unfold submap in H ; specialize H with (v := s).
      destruct (CEP.find s scope) ; last by trivial.
      by rewrite -H -Hfind //.
  + (* Sreg *)
    destruct (CEP.find s tmap) eqn: Hfind ; first by trivial.
    destruct (type_of_expr (clock h) scope) ; last by trivial.
    destruct (code_type_find_vm_widths (type h) s vm) as [[newt _]|] ; last by trivial.
    destruct (reset h).
    - split.
      * by apply submap_add_add, H.
      split.
      * by apply submap_add, Hfind.
      * apply submap_add.
        unfold submap in H ; specialize H with (v := s).
        destruct (CEP.find s scope) ; last by trivial.
        by rewrite -H -Hfind //.
    - destruct (type_of_expr h0 scope) ; last by trivial.
      destruct (type_of_expr h1 scope) ; last by trivial.
      split.
      * by apply submap_add_add, H.
      split.
      * by apply submap_add, Hfind.
      * apply submap_add.
        unfold submap in H ; specialize H with (v := s).
        destruct (CEP.find s scope) ; last by trivial.
        by rewrite -H -Hfind //.
  + (* Snode *)
    destruct (CEP.find s tmap) eqn: Hfind ; first by trivial.
    destruct (type_of_expr h scope) as [[newt _]|] ; last by trivial.
    split.
    - by apply submap_add_add, H.
    split.
    - by apply submap_add, Hfind.
    - apply submap_add.
      unfold submap in H ; specialize H with (v := s).
      destruct (CEP.find s scope) ; last by trivial.
      by rewrite -H -Hfind //.
  + (* Sfcnct *)
    destruct (type_of_ref h scope) ; last by trivial.
    destruct (type_of_expr h0 scope) ; last by trivial.
    split.
    - by exact H.
    - split ; by apply submap_refl.
  + (* Sinvalid *)
    destruct (type_of_ref h scope) ; last by trivial.
    split.
    - by exact H.
    - split ; by apply submap_refl.
  + (* Swhen *)
    rename h0 into ss_true ; rename h1 into ss_false.
    destruct (type_of_expr h scope) ; last by trivial.
    generalize (stmts_submap vm ss_true tmap scope H) ; intro.
    destruct (stmts_tmap (tmap, scope) ss_true vm) as [[tmap_true scope_true]|] ; last by trivial.
    generalize (stmts_submap vm ss_false tmap_true scope (submap_trans tmap _ _ H (proj1 (proj2 H0)))) ; intro.
    destruct (stmts_tmap (tmap_true, scope) ss_false vm) as [[tmap_false scope_false]|] ; last by trivial.
    split.
    - apply (submap_trans tmap) ; first by apply H.
      apply (submap_trans tmap_true) ; first by apply H0.
      apply H1.
    split.
    - apply (submap_trans tmap_true) ; first by apply H0.
      apply H1.
    - apply submap_refl.
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

Definition eq_submap (ts1 ts2 : CEP.t ftype * CEP.t ftype) : Prop :=
fst ts1 = fst ts2 /\ submap (snd ts1) (snd ts2).

Lemma eq_submap_refl :
forall ts : CEP.t ftype * CEP.t ftype, eq_submap ts ts.
Proof.
intro ; unfold eq_submap ; split ; first by reflexivity.
apply submap_refl.
Qed.

Lemma stmts_tmap_components :
   forall (vm : CEP.t vertex_type) (ss : HiFP.hfstmt_seq) (tmap scope1 scope2 : CEP.t ftype),
      submap scope1 tmap ->
      submap scope2 tmap ->
      submap scope1 scope2 ->
         match stmts_tmap (tmap, scope1) ss vm, stmts_tmap (tmap, scope2) (component_stmts_of ss) vm with
         | Some (tmap1', scope1'), Some (tmap2', scope2') =>
              tmap1' = tmap2' /\ submap scope1' scope2'
         | Some _, None => False
         | _, _ => True
         end
with stmt_tmap_components :
   forall (vm : CEP.t vertex_type) (s : HiFP.hfstmt) (tmap scope1 scope2 : CEP.t ftype),
      submap scope1 tmap ->
      submap scope2 tmap ->
      submap scope1 scope2 ->
         match stmt_tmap (tmap, scope1) s vm, stmts_tmap (tmap, scope2) (component_stmt_of s) vm with
         | Some (tmap1', scope1'), Some (tmap2', scope2') =>
              tmap1' = tmap2' /\ submap scope1' scope2'
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
    destruct (v == s) eqn: Hvs.
    - rewrite CEP.Lemmas.find_add_eq ; last by rewrite /HiFirrtl.PVM.SE.eq Hvs //.
      rewrite CEP.Lemmas.find_add_eq ; last by rewrite /HiFirrtl.PVM.SE.eq Hvs //.
      by reflexivity.
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
      destruct (v == s) eqn: Hvs.
      * rewrite CEP.Lemmas.find_add_eq ; last by rewrite /HiFirrtl.PVM.SE.eq Hvs //.
        rewrite CEP.Lemmas.find_add_eq ; last by rewrite /HiFirrtl.PVM.SE.eq Hvs //.
        by reflexivity.
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
      destruct (v == s) eqn: Hvs.
      * rewrite CEP.Lemmas.find_add_eq ; last by rewrite /HiFirrtl.PVM.SE.eq Hvs //.
        rewrite CEP.Lemmas.find_add_eq ; last by rewrite /HiFirrtl.PVM.SE.eq Hvs //.
        by reflexivity.
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
    destruct (v == s) eqn: Hvs.
    - rewrite CEP.Lemmas.find_add_eq ; last by rewrite /HiFirrtl.PVM.SE.eq Hvs //.
      rewrite CEP.Lemmas.find_add_eq ; last by rewrite /HiFirrtl.PVM.SE.eq Hvs //.
      by reflexivity.
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
    unfold eq_submap ; split ; first by reflexivity.
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
    assert (submap scope1 tmap_true).
          apply (submap_trans tmap) ; first (by exact H) ;
          apply H3.
    assert (submap scope1 scope_true').
          apply (submap_trans scope_true) ; first (by apply H3) ;
          apply H2.
    generalize (stmts_tmap_components vm ss_false tmap_true scope1 scope_true' H5 (proj1 H4) H6) ; intro.
    generalize (stmts_submap vm ss_false tmap_true scope1 H5) ;
          intro.
    destruct (stmts_tmap (tmap_true, scope1) ss_false vm) as [[tmap_false scope_false]|] eqn: Hss_false ; last by trivial.
    destruct (stmts_tmap (tmap_true, scope_true') (component_stmts_of ss_false) vm) as [[tmap_false' scope_false']|] eqn: Hss_false' ;
          last by trivial.
    split ; first by apply H7.
    apply (submap_trans scope_false) ; first by apply H8.
    apply H7.
Qed.




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

Definition Sem_frag_port (vm_old : CEP.t vertex_type) (ct_old : CEP.t def_expr) (p : HiFP.hfport) (vm_new : CEP.t vertex_type) (ct_new : CEP.t def_expr) (tmap : CEP.t ftype) : Prop :=
(* returns True if the port in p defines the components in vm *)
match p with
| Finput v t =>
    match CEP.find v tmap with
    | Some newft =>
           (* ground-type input ports are defined *)
           (forall n : nat,
                match List.nth_error (list_rhs_type_p newft) n with
                | Some gt =>
                       CEP.find (fst v, bin_of_nat (n + snd v)) vm_old = None
                    /\
                       CEP.find (fst v, bin_of_nat (n + snd v)) vm_new = Some (InPort gt)
                | None => True
                end)
        /\ (* other vertices do not change *)
           (forall (v0 n0 : N), v0 <> fst v \/ n0 < snd v \/ n0 >= (size_of_ftype newft) + (snd v) ->
                CEP.find (v0, n0) vm_old =
                CEP.find (v0, n0) vm_new)
        /\ (* connections do not change *)
           CEP.Equal ct_old ct_new
    | None => False
    end
| Foutput v t =>
    match CEP.find v tmap with
    | Some newft =>
           (* ground-type output ports are defined *)
           (forall n : nat,
                match List.nth_error (list_rhs_type_p newft) n with
                | Some gt => 
                       CEP.find (fst v, bin_of_nat (n + snd v)) vm_old = None
                    /\
                       CEP.find (fst v, bin_of_nat (n + snd v)) vm_new = Some (OutPort gt)
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
        /\ (* set input connectors to undefined *)
           forall n0 : nat, n0 < size_of_ftype newft ->
                  CEP.find (fst v, bin_of_nat (n0 + snd v)) ct_old = None
               /\
                  CEP.find (fst v, bin_of_nat (n0 + snd v)) ct_new = Some D_undefined
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
        submap vm_old vm_new /\ submap ct_old ct_new.
Proof.
induction pp ; simpl ; intros ;
      first by (destruct H ; rewrite H H0 ; split ; apply submap_refl).
destruct H as [vm' [ct' [H H0]]].
specialize (IHpp vm_old ct_old vm' ct' tmap H).
destruct IHpp as [IHpp_vm IHpp_ct].
unfold Sem_frag_port in H0.
destruct a.
1,2: destruct (CEP.find s tmap) ; last by contradiction H0.
1,2: split.
1,2,3,4: intro.
1,2,3,4: destruct H0 as [H0 [H1 H2]].
* 2: specialize (IHpp_ct v) ;
     specialize (H2 v) ;
     destruct (CEP.find v ct_old) ; last (by done) ;
     rewrite -H2 ;
     exact IHpp_ct.
* 1,2: specialize (H0 (snd v - snd s)) ; specialize (H1 (fst v) (snd v)).
  1,2: rewrite -surjective_pairing in H1.
  1,2: specialize (IHpp_vm v).
  1,2: destruct (fst v == fst s) eqn: Hfst.
  1,2,3,4: move /eqP : Hfst => Hfst.
  + 1,3: destruct (snd v < snd s) eqn: Hsnd_small ;
               first by (destruct (CEP.find v vm_old) ; last (by done) ;
                         rewrite -IHpp_vm ; symmetry ; apply H1 ; right ; left ; done).
    1,2: destruct (size_of_ftype f0 + snd s <= snd v) eqn: Hsnd_large ;
               first by (destruct (CEP.find v vm_old) ; last (by done) ;
                         rewrite -IHpp_vm ; symmetry ; apply H1 ; right ; right ; done).
    1,2: generalize (List.nth_error_Some (list_rhs_type_p f0) (snd v - snd s)) ; intro.
    1,2: replace (length (list_rhs_type_p f0)) with (size_of_ftype f0) in H3
               by (rewrite -list_rhs_type_p_size ; reflexivity).
    1,2: rewrite ltnNge in Hsnd_small ; apply negbFE in Hsnd_small.
    1,2: rewrite leqNgt addnC -ltn_subLR // in Hsnd_large ; apply negbFE in Hsnd_large.
    1,2: apply simplssrlib.Nats.ltn_lt in Hsnd_large.
    1,2: destruct H3 as [_ H3] ; specialize (H3 Hsnd_large).
    1,2: destruct (List.nth_error (list_rhs_type_p f0) (snd v - snd s)) ; last by contradiction H3.
    1,2: rewrite subnK // -Hfst nat_of_binK -surjective_pairing in H0.
    1,2: destruct (CEP.find v vm') ; first by discriminate (proj1 H0).
    1,2: destruct (CEP.find v vm_old) ; first by discriminate IHpp_vm.
    1,2: by done.
  + 1,2: destruct (CEP.find v vm_old) ; last by done.
    1,2: rewrite -H1 ; last by (left ; exact Hfst).
    1,2: by exact IHpp_vm.
* clear H0 H1 ; destruct H2 as [H1 H0].
  specialize (H0 (snd v - snd s)) ; specialize (H1 (fst v) (snd v)).
  destruct (fst v == fst s) eqn: Hfst.
  1,2: move /eqP : Hfst => Hfst.
  1,2: rewrite -surjective_pairing in H1.
  1,2: specialize (IHpp_ct v).
  + destruct (snd v < snd s) eqn: Hsnd_small ;
          first by (destruct (CEP.find v ct_old) ; last (by done) ;
                    rewrite -IHpp_ct ; symmetry ; apply H1 ; right ; left ; done).
    destruct (size_of_ftype f0 + snd s <= snd v) eqn: Hsnd_large ;
          first by (destruct (CEP.find v ct_old) ; last (by done) ;
                    rewrite -IHpp_ct ; symmetry ; apply H1 ; right ; right ; done).
    (*generalize (List.nth_error_Some (list_rhs_type_p f0) (snd v - snd s)) ; intro H3.
    replace (length (list_rhs_type_p f0)) with (size_of_ftype f0) in H3
          by (rewrite -list_rhs_type_p_size ; reflexivity).*)
    rewrite ltnNge in Hsnd_small ; apply negbFE in Hsnd_small.
    rewrite leqNgt addnC -ltn_subLR // in Hsnd_large ; apply negbFE in Hsnd_large.
    specialize (H0 Hsnd_large).
    (*apply simplssrlib.Nats.ltn_lt in Hsnd_large.
    destruct H3 as [_ H3] ; specialize (H3 Hsnd_large).
    destruct (List.nth_error (list_rhs_type_p f0) (snd v - snd s)) ; last by contradiction H3.*)
    rewrite subnK // -Hfst nat_of_binK -surjective_pairing in H0.
    destruct (CEP.find v ct') ; first by discriminate (proj1 H0).
    destruct (CEP.find v ct_old) ; first by discriminate IHpp_ct.
    by done.
  + destruct (CEP.find v ct_old) ; last by done.
    rewrite -H1 ; last by (left ; exact Hfst).
    by exact IHpp_ct.
Qed.

Definition vm_and_ct_compatible (vm : CEP.t vertex_type) (ct : CEP.t def_expr) :=
forall (v : CEP.key),
    match CEP.find v vm with
    | None
    | Some (InPort _) => CEP.find v ct = None
    | _ => CEP.find v ct <> None
    end.

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
destruct a ; try done ; destruct (CEP.find s tmap) ; try by contradiction H1.
* destruct H1 as [H1 [H2 H3]].
  specialize (H1 (snd v - snd s)) ; specialize (H2 (fst v) (snd v)).
  specialize (H3 v) ; rewrite H3 in IHpp.
  rewrite -surjective_pairing in H2.
  destruct (fst v == fst s) eqn: Hfst ; move /eqP : Hfst => Hfst ;
        last by (rewrite -H2 ; first (by exact IHpp) ;
                 left ; done).
  destruct (snd v < snd s) eqn: Hsnd_small ;
        first by (rewrite -H2 ; first (by exact IHpp) ;
                  right ; left ; done).
  destruct (size_of_ftype f0 + snd s <= snd v) eqn: Hsnd_large ;
        first by (rewrite -H2 ; first (by exact IHpp) ;
                  right ; right ; done).
  generalize (List.nth_error_Some (list_rhs_type_p f0) (snd v - snd s)) ; intro.
  replace (length (list_rhs_type_p f0)) with (size_of_ftype f0) in H4
        by (rewrite -list_rhs_type_p_size ; reflexivity).
  rewrite ltnNge in Hsnd_small ; apply negbFE in Hsnd_small.
  rewrite leqNgt addnC -ltn_subLR // in Hsnd_large ; apply negbFE in Hsnd_large.
  apply simplssrlib.Nats.ltn_lt in Hsnd_large.
  destruct H4 as [_ H4] ; specialize (H4 Hsnd_large).
  destruct (List.nth_error (list_rhs_type_p f0) (snd v - snd s)) ; last by contradiction H4.
  rewrite subnK // -Hfst nat_of_binK -surjective_pairing in H1.
  rewrite (proj1 H1) in IHpp ; rewrite (proj2 H1).
  by exact IHpp.
* destruct H1 as [H1 [H2 [H4 H3]]].
  specialize (H1 (snd v - snd s)) ; specialize (H2 (fst v) (snd v)).
  rewrite -surjective_pairing in H2.
  specialize (H3 (snd v - snd s)) ; specialize (H4 (fst v) (snd v)).
  rewrite -surjective_pairing in H4.
  destruct (fst v == fst s) eqn: Hfst ; move /eqP : Hfst => Hfst ;
        last by (rewrite -H2 ; last (by left ; done) ;
                 rewrite -H4 ; last (by left ; done) ;
                 exact IHpp).
  destruct (snd v < snd s) eqn: Hsnd_small ;
        first by (rewrite -H2 ; last (by right ; left ; done) ;
                  rewrite -H4 ; last (by right ; left ; done) ;
                  exact IHpp).
  destruct (size_of_ftype f0 + snd s <= snd v) eqn: Hsnd_large ;
        first by (rewrite -H2 ; last (by right ; right ; done) ;
                  rewrite -H4 ; last (by right ; right ; done) ;
                  exact IHpp).
  generalize (List.nth_error_Some (list_rhs_type_p f0) (snd v - snd s)) ; intro.
  replace (length (list_rhs_type_p f0)) with (size_of_ftype f0) in H5
        by (rewrite -list_rhs_type_p_size ; reflexivity).
  rewrite ltnNge in Hsnd_small ; apply negbFE in Hsnd_small.
  rewrite leqNgt addnC -ltn_subLR // in Hsnd_large ; apply negbFE in Hsnd_large.
  specialize (H3 Hsnd_large).
  apply simplssrlib.Nats.ltn_lt in Hsnd_large.
  destruct H5 as [_ H5] ; specialize (H5 Hsnd_large).
  destruct (List.nth_error (list_rhs_type_p f0) (snd v - snd s)) ; last by contradiction H5.
  rewrite subnK // -Hfst nat_of_binK -surjective_pairing in H1, H3.
  rewrite (proj2 H1) (proj2 H3).
  discriminate.
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


(*---------------------------------------------------------------------------*)
(* Semantics of statements                                                   *)

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


(*---------------------------------------------------------------------------*)
(* Semantics of module                                                       *)

Definition Sem (F : HiFP.hfmodule) (vm : CEP.t vertex_type) (ct : CEP.t def_expr) : Prop :=
(* The predicate returns True if G = (vm, ct) conforms to F.
   (If F has errors, there is no such G.)
   (If F has implicit width components, then there are many such Gs.)

   Problem: I made some assumption about identifiers of aggregate-type components;
   is that what you need? *)
match F with
| FInmod n pp ss =>
    match ports_tmap pp vm with
    | Some pmap =>
        match stmts_tmap (pmap, pmap) ss vm with
        | Some (tmap, _) =>
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
    | None => False
    end
| FExmod _ _ _ => False
 end.
