From Coq Require Import FunInd FMaps FMapAVL OrderedType ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat ssrint eqtype seq ssrfun fintype.
From simplssrlib Require Import Types SsrOrder FSets FMaps Tactics Var Store.
(*From nbits Require Import NBits.*)
From firrtl Require Import Firrtl Env HiEnv HiFirrtl .
(* From firrtl Require Import InferWidth_rewritten. *)

(* Inductive vertex_type := *)
(*    (* what kind of vertices can be in the module graph *) *)
(*    OutPort : fgtyp (* within the module there is only an input *)
(*                                 (the output goes to some place outside the module) *) -> vertex_type | *)
(*    InPort : fgtyp -> vertex_type | (* main module only at present *) *)
(*    (* register, wire etc. *) *)
(*    Register : fgtyp -> HiFP.hfexpr (* clock *) -> HiFP.rst -> bool (* true if the reset is Fasyncreset *) -> vertex_type | (* Register, possibly with reset. The boolean is true if it is Fasyncreset. *) *)
(*    Wire : fgtyp -> vertex_type | *)
(*    (*memory : ? *)
(*    inst : ?*) *)
(*    Node : fgtyp -> vertex_type. *)

(* (* equality of vertex_type is decidable *) *)
(* Lemma vertex_type_eq_dec : forall {x y : vertex_type}, {x = y} + {x <> y}. *)
(* Admitted. *)
(* Lemma rst_eq_dec : forall {x y : HiFP.rst} , {x = y} + {x <> y}. *)
(* Admitted. *)

(*   Parameter rst_eqn : forall (x y : HiFP.rst), bool. *)
(*   Axiom rst_eqP : Equality.axiom rst_eqn. *)
(*   Canonical rst_eqMixin := EqMixin rst_eqP. *)
(*   Canonical rst_eqType := Eval hnf in EqType HiFP.rst rst_eqMixin. *)

(* Definition vertex_type_eqn (x y : vertex_type) : bool := *)
(* match x, y with *)
(* | OutPort tx, OutPort ty *)
(* | InPort tx, InPort ty *)
(* (*| Reference a, Reference b*) *)
(* | Wire tx, Wire ty *)
(* (*memory : ? *)
(* inst : ?*) *)
(* | Node tx, Node ty => tx == ty *)
(* | Register tx cx rx bx, Register ty cy ry by_ => *)
(*     (tx == ty) && (cx == cy) && (rx == ry)  && (bx == by_) *)
(* | _, _ => false *)
(* end. *)
(* Lemma vertex_type_eqP : Equality.axiom vertex_type_eqn. *)
(* Proof. *)
(* rewrite /Equality.axiom ; intros. *)
(* case: (@vertex_type_eq_dec x y) => H. *)
(* * rewrite H /vertex_type_eqn ; clear -y. *)
(*   destruct y ; rewrite eq_refl ; try rewrite andTb eq_refl ; *)
(*   try rewrite andTb eq_refl ; try rewrite andTb eq_refl ; *)
(*   apply ReflectT ; reflexivity. *)
(* * rewrite /vertex_type_eqn. *)
(*   destruct x, y ; try contradiction ; try (apply ReflectF ; exact H). *)
(*   + 3: *)
(*     destruct (b == b0) eqn: Hb ; *)
(*     last (by rewrite andbF ; apply ReflectF ; exact H) ; *)
(*     rewrite andbT ; *)
(*     destruct (r == r0) eqn: Hr ; *)
(*     last (by rewrite andbF ; apply ReflectF ; exact H) ; *)
(*     rewrite andbT ; *)
(*     destruct (h == h0) eqn: Hh ; *)
(*     last (by rewrite andbF ; apply ReflectF ; exact H) ; *)
(*     rewrite andbT ; *)
(*     destruct (f == f0) eqn: Hf ; *)
(*     last (by apply ReflectF ; exact H) ; *)
(*     apply ReflectT ; move /eqP : Hb => Hb ; move /eqP : Hr => Hr ; *)
(*     move /eqP : Hh => Hh ; move /eqP: Hf => Hf ; *)
(*     rewrite Hb Hr Hh Hf //. *)
(*   + all: *)
(*     assert (f <> f0) by (contradict H ; rewrite H ; reflexivity) ; *)
(*     move /eqP : H0 => H0 ; apply negbTE in H0 ; *)
(*     rewrite H0 ; apply ReflectF ; exact H. *)
(* Qed. *)
(* Canonical vertex_type_eqMixin := EqMixin vertex_type_eqP. *)
(* Canonical vertex_type_eqType := Eval hnf in EqType vertex_type vertex_type_eqMixin. *)

(* (* Some abbreviations for explicit-width data types *) *)

(* Definition Fsint_exp (w : nat) : fgtyp_explicit := *)
(*    (* convert Fsint w to an fgtyp_explicit *) *)
(*    exist not_implicit_width (Fsint w) I. *)

(* Definition Fuint_exp (w : nat) : fgtyp_explicit := *)
(*    (* convert Fuint w to an output data type *) *)
(*    exist not_implicit_width (Fuint w) I. *)

(* Definition Fclock_exp : fgtyp_explicit := *)
(*    (* convert Fclock to an explicit-width data type *) *)
(*    exist not_implicit_width Fclock I. *)

(* Definition Fasyncreset_exp : fgtyp_explicit := *)
(*    (* convert Fasyncreset to an explicit-width data type *) *)
(*    exist not_implicit_width Fasyncreset I. *)

(* (* vertex set of a module graph (using pairs of natural numbers as keys) *) *)

(* (* The vertex set should have type CEP.t vertex_type. *) *)
(* (* *)
(* Module MakeVtypFMap (V : SsrOrder) (VM : SsrFMap with Module SE := V) *)
(* <: SsrFMap with Module SE := V. *)
(*   Include VM. *)
(*   Include FMapLemmas VM. *)
(*   Definition env : Type := t vertex_type. *)
(* End MakeVtypFMap. *)

(* Module ProdVarOrder := MakeProdOrder VarOrder VarOrder. *)
(* Module PVM <: SsrFMap := FMaps.MakeTreeMap ProdVarOrder. *)
(* Module module_graph_vertex_set_p <: SsrFMap := MakeVtypFMap ProdVarOrder PVM. *)
(* *) *)


(* Inductive def_expr : Type := *)
(*   | D_undefined (* declared but not connected, no "is invalid" statement *) *)
(*   | D_invalidated (* declared but not connected, there is a "is invalid" statement *) *)
(*   | D_fexpr : HiFP.hfexpr -> def_expr (* declared and connected *) *)
(*   . *)

(* (* equality of def_expr is decidable [because equality of hfexpr is decidable] *) *)
(* Lemma def_expr_eq_dec : forall {x y : def_expr}, {x = y} + {x <> y}. *)
(*   Proof. *)
(*   decide equality. *)
(*   apply hfexpr_eq_dec. *)
(* Qed. *)

(* Definition def_expr_eqn (x y : def_expr) : bool := *)
(*   match x, y with *)
(*   | D_undefined, D_undefined => true *)
(*   | D_invalidated, D_invalidated => true *)
(*   | D_fexpr expr1, D_fexpr expr2 => expr1 == expr2 *)
(*   | _, _ => false *)
(*   end. *)

(* Lemma def_expr_eqP : Equality.axiom def_expr_eqn. *)
(* Proof. *)
(*   unfold Equality.axiom, def_expr_eqn. *)
(*   intros ; induction x, y ; try (apply ReflectF ; discriminate) ; try (apply ReflectT ; reflexivity). *)
(*   case Eq: (h == h0). *)
(*   all: move /hfexpr_eqP : Eq => Eq. *)
(*   apply ReflectT ; replace h0 with h ; reflexivity. *)
(*   apply ReflectF ; injection ; apply Eq. *)
(* Qed. *)

(* Canonical def_expr_eqMixin := EqMixin def_expr_eqP. *)
(* Canonical def_expr_eqType := Eval hnf in EqType def_expr def_expr_eqMixin. *)


(* (*---------------------------------------------------------------------------*) *)
(* (* Helper functions for connecting                                           *) *)

(* Fixpoint connect_type_compatible (can_flip : bool) (ft_tgt ft_src : ftype) (flipped : bool) : bool := *)
(* (* Returns true if a connection from ft_src to ft_tgt is allowed. *)
(*    flipped == true indicates that the connection should be the other way actually. *)
(*    If can_flip == false, no flipped fields are allowed in bundle types. *) *)
(* match ft_tgt, ft_src with *)
(* | Gtyp (Fuint _), Gtyp (Fuint _) *)
(* | Gtyp (Fsint _), Gtyp (Fsint _) *)
(* | Gtyp Fclock, Gtyp Fclock *)
(* | Gtyp Fasyncreset, Gtyp Fasyncreset => true *)
(* | Gtyp (Fuint_implicit w_tgt), Gtyp (Fuint w_src) *)
(* | Gtyp (Fsint_implicit w_tgt), Gtyp (Fsint w_src) => flipped || (w_tgt >= w_src) *)
(* | Gtyp (Fuint w_tgt), Gtyp (Fuint_implicit w_src) *)
(* | Gtyp (Fsint w_tgt), Gtyp (Fsint_implicit w_src) => (~~flipped) || (w_tgt <= w_src) *)
(* | Gtyp (Fuint_implicit w_tgt), Gtyp (Fuint_implicit w_src) *)
(* | Gtyp (Fsint_implicit w_tgt), Gtyp (Fsint_implicit w_src) => *)
(*     if flipped then w_tgt <= w_src else w_tgt >= w_src *)
(* | Atyp ft_tgt' n_tgt, Atyp ft_src' n_src => *)
(*        (n_tgt == n_src) *)
(*     && *)
(*        connect_type_compatible can_flip ft_tgt' ft_src' flipped *)
(* | Btyp ff_tgt, Btyp ff_src => connect_type_compatible_fields can_flip ff_tgt ff_src flipped *)
(* | _, _ => false *)
(* end *)
(* with connect_type_compatible_fields (can_flip : bool) (ff_tgt ff_src : ffield) (flipped : bool) : bool := *)
(* (* Returns true if a connection from (Btyp ff_src) to (Btyp ff_tgt) is allowed. *)
(*    flipped == true indicates that the connection should be the other way actually. *)
(*    If can_flip == false, no flipped fields are allowed in bundle types. *) *)
(* match ff_tgt, ff_src with *)
(* | Fnil, Fnil => true *)
(* | Fflips v_tgt Nflip ft_tgt ff_tgt', Fflips v_src Nflip ft_src ff_src' => *)
(*        (v_tgt == v_src) *)
(*     && *)
(*        connect_type_compatible can_flip ft_tgt ft_src flipped *)
(*     && *)
(*        connect_type_compatible_fields can_flip ff_tgt' ff_src' flipped *)
(* | Fflips v_tgt Flipped ft_tgt ff_tgt', Fflips v_src Flipped ft_src ff_src' => *)
(*        can_flip *)
(*     && *)
(*        (v_tgt == v_src) *)
(*     && *)
(*        connect_type_compatible can_flip ft_tgt ft_src (~~flipped) *)
(*     && *)
(*        connect_type_compatible_fields can_flip ff_tgt' ff_src' flipped *)
(* | _, _ => false *)
(* end. *)

(* Definition connect_fgtyp (ct_old : CEP.t def_expr) *)
(*                          (ref_tgt : HiFP.href) (lst_tgt : list CEP.key) *)
(*                          (ref_src : HiFP.href) (lst_src : list CEP.key) *)
(*                          (flipped : bool) *)
(*                          (ct_new : CEP.t def_expr) : bool := *)
(* (* The predicate checks whether ct_new contains the correct connection that connects from lst_src to lst_tgt, *)
(*    and it does not change the connection into lst_src. *)
(*    These lists must be one-element lists for output and input connectors of compatible types. *)
(*    It assumes that the types are compatible. *) *)
(* match flipped, ref_tgt, lst_tgt, ref_src, lst_src with *)
(* | false, _, [:: ic], ref_src, [:: oc] *)
(* | true,  ref_src, [:: oc], _, [:: ic] => *)
(*        (CEP.find ic ct_new == Some (D_fexpr (Eref ref_src))) *)
(*     && *)
(*        (CEP.find oc ct_new == CEP.find oc ct_old) *)
(*        (* why this is compared? *)
(*           In Sem_frag_stmt, it is ensured that connection trees NOT related to tgt or src are not changed. *)
(*           Here, we need to ensure that the connection tree of tgt is changed *)
(*           and the connection tree of src remains the same. *) *)
(* | _, _, _, _, _ => false *)
(* end. *)

(* Fixpoint connect (ct_old : CEP.t def_expr) *)
(*                  (ref_tgt : HiFP.href) (lst_tgt : list CEP.key) (ft_tgt : ftype) *)
(*                  (ref_src : HiFP.href) (lst_src : list CEP.key) (ft_src : ftype) *)
(*                  (flipped : bool) *)
(*                  (ct_new : CEP.t def_expr) : bool := *)
(* (* The predicate returns true if the correct connection trees are in ct_new *)
(*    that connect from lst_src to lst_tgt, and that the connection trees that *)
(*    connect to lst_src are not changed.  Other connection trees are not checked. *)
(*    The type of lst_tgt is ft_tgt, and the type of lst_src is ft_src. *)
(*    These references are *not* required to have passive types. *) *)
(* match ft_tgt, ft_src with *)
(* | Gtyp gt_tgt, Gtyp gt_src => connect_fgtyp ct_old ref_tgt lst_tgt ref_src lst_src flipped ct_new *)
(* | Atyp elt_tgt n1, Atyp elt_src n2 => *)
(*        (n1 == n2) *)
(*    && *)
(*        let type_len := size_of_ftype elt_tgt in *)
(*        [forall n : ordinal n1, *)
(*           connect ct_old *)
(*                   (Esubindex ref_tgt n) (take type_len (drop (n * type_len) lst_tgt)) elt_tgt *)
(*                   (Esubindex ref_src n) (take type_len (drop (n * type_len) lst_src)) elt_src *)
(*                   flipped ct_new] *)
(* | Btyp ff_tgt, Btyp ff_src => connect_fields ct_old ref_tgt lst_tgt ff_tgt ref_src lst_src ff_src flipped ct_new *)
(* | _, _ => false *)
(* end *)
(* with connect_fields (ct_old : CEP.t def_expr) *)
(*                     (ref_tgt : HiFP.href) (lst_tgt : list CEP.key) (ft_tgt : ffield) *)
(*                     (ref_src : HiFP.href) (lst_src : list CEP.key) (ft_src : ffield) *)
(*                     (flipped : bool) *)
(*                     (ct_new : CEP.t def_expr) : bool := *)
(* (* The predicate returns true if the correct connection trees are in ct_new *)
(*    that connect from lst_src to lst_tgt, and that the connection trees that *)
(*    connect to lst_src are not changed.  Other connection trees are not checked. *)
(*    The type of lst_tgt is (Btyp ft_tgt), and the type of lst_src is (Btyp ft_src). *)
(*    These references are *not* required to have passive types. *) *)
(* match ft_tgt, ft_src with *)
(* | Fnil, Fnil => true *)
(* | Fflips v1 Nflip gtt ft, Fflips v2 Nflip gts fs => *)
(*        (v1 == v2) *)
(*     && *)
(*        let type_len := size_of_ftype gtt in *)
(*               connect ct_old (Esubfield ref_tgt v1) (take type_len lst_tgt) gtt (Esubfield ref_src v2) (take type_len lst_src) gts flipped ct_new *)
(*            && *)
(*               connect_fields ct_old ref_tgt (drop type_len lst_tgt) ft ref_src (drop type_len lst_src) fs flipped ct_new *)
(* | Fflips v1 Flipped gtt ft, Fflips v2 Flipped gts fs => *)
(*        (v1 == v2) *)
(*     && *)
(*        let type_len := size_of_ftype gts in *)
(*               connect ct_old (Esubfield ref_tgt v1) (take type_len lst_tgt) gtt (Esubfield ref_src v2) (take type_len lst_src) gts (~~flipped) ct_new *)
(*            && *)
(*               connect_fields ct_old ref_tgt (drop type_len lst_tgt) ft ref_src (drop type_len lst_src) fs flipped ct_new *)
(* | _, _ => false *)
(* end. *)


(* Fixpoint type_of_ffield (v : VarOrder.T) (ff : ffield) : option ftype := *)
(* (* Find the type of field v in bundle type (Btyp ff). *) *)
(* match ff with *)
(* | Fnil => None *)
(* | Fflips v0 _ t ff' => if v == v0 then Some t else type_of_ffield v ff' *)
(* end. *)

(* Fixpoint type_of_ref (ref : HiFP.href) (tmap : CEP.t ftype) : option ftype := *)
(* (* Find the type of reference ref, using the type information from tmap. *)
(*    Note that widths of implicit-width components may be wrong. *)

(*    This function is similar to base_ref; check whether they can be made more similar. *) *)
(* match ref with *)
(* | Eid v => CEP.find v tmap *)
(* | Esubindex ref' n => *)
(*     match type_of_ref ref' tmap with *)
(*     | Some (Atyp t m) => if n < m then Some t else None *)
(*     | _ => None *)
(*     end *)
(* | Esubfield ref' v => *)
(*     match type_of_ref ref' tmap with *)
(*     | Some (Btyp ff) => type_of_ffield v ff *)
(*     | _ => None *)
(*     end *)
(* | Esubaccess _ _ => None *)
(* end. *)

(* Definition fgtyp_mux (x y : fgtyp_explicit) : option fgtyp_explicit := *)
(* (* Find the type of a multiplexer whose two inputs have types x and y, for ground types *) *)
(*     match x, y with *)
(*     | exist (Fuint wx) _, exist (Fuint wy) _ => Some (Fuint_exp (Nat.max wx wy)) *)
(*     | exist (Fsint wx) _, exist (Fsint wy) _ => Some (Fsint_exp (Nat.max wx wy)) *)
(*     | exist Fclock _, exist Fclock _ => Some Fclock_exp *)
(*   (*| exist Freset _, exist Freset _ => Some Freset_exp*) *)
(*     | exist Fasyncreset _, exist Fasyncreset _ => Some Fasyncreset_exp *)
(*     | _, _ => None *)
(*     end. *)

(* Fixpoint ftype_mux' (x : ftype) (px : ftype_not_implicit_width x) (y : ftype) (py : ftype_not_implicit_width y) : option ftype_explicit := *)
(* (* Find the type of a multiplexer whose two inputs have types (exist ftype_not_implicit_width x px) *)
(*    and (exist ftype_not_implicit_width y py). *)
(*    The function needs to take apart the ftype_explicit so Coq can guess the decreasing argument. *) *)
(*   match x, px, y, py with *)
(*   | Gtyp tx, px, Gtyp ty, py => *)
(*        match fgtyp_mux (exist not_implicit_width tx px) (exist not_implicit_width ty py) with *)
(*        | Some (exist fgt p) => Some (exist ftype_not_implicit_width (Gtyp fgt) p) *)
(*        | None => None *)
(*        end *)
(*   | Atyp tx nx, px, Atyp ty ny, py => *)
(*        if (nx == ny) then match ftype_mux' tx px ty py with *)
(*                           | Some (exist fat p) => Some (exist ftype_not_implicit_width (Atyp fat nx) p) *)
(*                           | None => None *)
(*                           end *)
(*                      else None *)
(*   | Btyp fx, px, Btyp fy, py => ffield_mux' fx px fy py *)
(*   | _, _, _, _ => None *)
(*   end *)
(* with ffield_mux' (f1 : ffield) (p1 : ffield_not_implicit_width f1) (f2 : ffield) (p2 : ffield_not_implicit_width f2) : option ftype_explicit := *)
(*        match f1, p1, f2, p2 with *)
(*        | Fnil, _, Fnil, _ => Some (exist ftype_not_implicit_width (Btyp Fnil) I) *)
(*        | Fflips v1 Nflip t1 fs1, p1, Fflips v2 Nflip t2 fs2, p2 *)
(*          => if v1 == v2 then *)
(*                match ftype_mux'  t1  (proj1 p1) t2  (proj1 p2), *)
(*                      ffield_mux' fs1 (proj2 p1) fs2 (proj2 p2) with *)
(*                | Some (exist ft pt), Some (exist (Btyp bf) pf) => *)
(*                    Some (exist ftype_not_implicit_width (Btyp (Fflips v1 Nflip ft bf)) (conj pt pf)) *)
(*                | _, _ => None *)
(*                end *)
(*             else None *)
(*        | _, _, _, _ => None *)
(*        end. *)

(* Definition ftype_mux (x : ftype_explicit) (y : ftype_explicit) : option ftype_explicit := *)
(* (* return the type of mux expression on ftypes *)

(*    Similar to mux_types in InferWidths *) *)
(*    ftype_mux' (proj1_sig x) (proj2_sig x) (proj1_sig y) (proj2_sig y). *)

(* Fixpoint type_of_expr (expr : HiFP.hfexpr) (tmap: CEP.t ftype) : option ftype_explicit := *)
(*    (* Find the type of expression expr. *)

(*    Similar to type_of_hfexpr in InferWidths *) *)
(*    match expr with *)
(*    | Econst t bs => match t with *)
(*                     | Fuint_implicit w => Some (exist ftype_not_implicit_width (Gtyp (Fuint w)) I) *)
(*                     | Fsint_implicit w => Some (exist ftype_not_implicit_width (Gtyp (Fsint w)) I) *)
(*                     | t => Some (exist ftype_not_implicit_width (Gtyp t) I) *)
(*                     end *)
(*    | Eref r => match type_of_ref r tmap with *)
(*                | Some t => Some (make_ftype_explicit t) *)
(*                | _ => None *)
(*                end *)
(*    | Ecast AsUInt e1 => match type_of_expr e1 tmap with *)
(*                          | Some (exist (Gtyp (Fsint w)) _) *)
(*                          | Some (exist (Gtyp (Fuint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint w)) I) *)
(*                          | Some (exist (Gtyp Fclock) _) *)
(*                          | Some (exist (Gtyp Freset) _) *)
(*                          | Some (exist (Gtyp Fasyncreset) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint 1)) I) *)
(*                          | _ => None *)
(*                          end *)
(*    | Ecast AsSInt e1 => match type_of_expr e1 tmap with *)
(*                          | Some (exist (Gtyp (Fsint w)) _) *)
(*                          | Some (exist (Gtyp (Fuint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint w)) I) *)
(*                          | Some (exist (Gtyp Fclock) _) *)
(*                          | Some (exist (Gtyp Freset) _) *)
(*                          | Some (exist (Gtyp Fasyncreset) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint 1)) I) *)
(*                          | _ => None *)
(*                          end *)
(*    | Ecast AsClock e1 => match type_of_expr e1 tmap with *)
(*                          | Some (exist (Gtyp _) _) => Some (exist ftype_not_implicit_width (Gtyp Fclock) I) *)
(*                          | _ => None *)
(*                          end *)
(*    | Ecast AsAsync e1 => match type_of_expr e1 tmap with *)
(*                          | Some (exist (Gtyp _) _) => Some (exist ftype_not_implicit_width (Gtyp Fasyncreset) I) *)
(*                          | _ => None *)
(*                          end *)
(*    | Eprim_unop (Upad n) e1 => match type_of_expr e1 tmap with *)
(*                                 | Some (exist (Gtyp (Fsint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint (maxn w n))) I) *)
(*                                 | Some (exist (Gtyp (Fuint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint (maxn w n))) I) *)
(*                                 | _ => None *)
(*                                 end *)
(*    | Eprim_unop (Ushl n) e1 => match type_of_expr e1 tmap with *)
(*                                 | Some (exist (Gtyp (Fsint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint (w + n))) I) *)
(*                                 | Some (exist (Gtyp (Fuint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint (w + n))) I) *)
(*                                 | _ => None *)
(*                                 end *)
(*    | Eprim_unop (Ushr n) e1 => match type_of_expr e1 tmap with *)
(*                                 | Some (exist (Gtyp (Fsint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint (maxn (w - n) 1))) I) *)
(*                                 | Some (exist (Gtyp (Fuint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint (maxn (w - n) 1))) I) *)
(*                                 | _ => None *)
(*                                 end *)
(*    | Eprim_unop Ucvt e1 => match type_of_expr e1 tmap with *)
(*                             | Some (exist (Gtyp (Fsint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint w)) I) *)
(*                             | Some (exist (Gtyp (Fuint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint (w + 1))) I) *)
(*                             | _ => None *)
(*                             end *)
(*    | Eprim_unop Uneg e1 => match type_of_expr e1 tmap with *)
(*                             | Some (exist (Gtyp (Fsint w)) _) *)
(*                             | Some (exist (Gtyp (Fuint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint (w + 1))) I) *)
(*                             | _ => None *)
(*                             end *)
(*    | Eprim_unop Unot e1 => match type_of_expr e1 tmap with *)
(*                             | Some (exist (Gtyp (Fsint w)) _) *)
(*                             | Some (exist (Gtyp (Fuint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint w)) I) *)
(*                             | _ => None *)
(*                             end *)
(*    | Eprim_unop (Uextr n1 n2) e1 => match type_of_expr e1 tmap with *)
(*                                      | Some (exist (Gtyp (Fsint w)) _) *)
(*                                      | Some (exist (Gtyp (Fuint w)) _) => *)
(*                                           if (n2 <= n1) && (n1 < w) then Some (exist ftype_not_implicit_width (Gtyp (Fuint (n1 - n2 + 1))) I) *)
(*                                                                     else None *)
(*                                      | _ => None *)
(*                                      end *)
(*    | Eprim_unop (Uhead n) e1 => match type_of_expr e1 tmap with *)
(*                                  | Some (exist (Gtyp (Fsint w)) _) *)
(*                                  | Some (exist (Gtyp (Fuint w)) _) => *)
(*                                       if n <= w then Some (exist ftype_not_implicit_width (Gtyp (Fuint n)) I) *)
(*                                                 else None *)
(*                                  | _ => None *)
(*                                  end *)
(*    | Eprim_unop (Utail n) e1 => match type_of_expr e1 tmap with *)
(*                                  | Some (exist (Gtyp (Fsint w)) _) *)
(*                                  | Some (exist (Gtyp (Fuint w)) _) => *)
(*                                       if n <= w then Some (exist ftype_not_implicit_width (Gtyp (Fuint (w - n))) I) *)
(*                                                 else None *)
(*                                  | _ => None *)
(*                                  end *)
(*    | Eprim_unop _ e1 => match type_of_expr e1 tmap with *)
(*                          | Some (exist (Gtyp (Fsint _)) _) *)
(*                          | Some (exist (Gtyp (Fuint _)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint 1)) I) *)
(*                          | _ => None *)
(*                          end *)
(*    | Eprim_binop (Bcomp _) e1 e2 => match type_of_expr e1 tmap, type_of_expr e2 tmap with *)
(*                                      | Some (exist (Gtyp (Fsint _)) _), Some (exist (Gtyp (Fsint _)) _) *)
(*                                      | Some (exist (Gtyp (Fuint _)) _), Some (exist (Gtyp (Fuint _)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint 1)) I) *)
(*                                      | _, _ => None *)
(*                                      end *)
(*    | Eprim_binop Badd e1 e2 *)
(*    | Eprim_binop Bsub e1 e2 => match type_of_expr e1 tmap, type_of_expr e2 tmap with *)
(*                                 | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint (maxn w1 w2 + 1))) I) *)
(*                                 | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fsint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint (maxn w1 w2 + 1))) I) *)
(*                                 | _, _ => None *)
(*                                 end *)
(*    | Eprim_binop Bmul e1 e2 => match type_of_expr e1 tmap, type_of_expr e2 tmap with *)
(*                                 | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint (w1 + w2))) I) *)
(*                                 | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fsint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint (w1 + w2))) I) *)
(*                                 | _, _ => None *)
(*                                 end *)
(*    | Eprim_binop Bdiv e1 e2  => match type_of_expr e1 tmap, type_of_expr e2 tmap with *)
(*                                  | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint w1)) I) *)
(*                                  | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fsint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint (w1 + 1))) I) *)
(*                                  | _, _ => None *)
(*                                  end *)
(*    | Eprim_binop Brem e1 e2 => match type_of_expr e1 tmap, type_of_expr e2 tmap with *)
(*                                  | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint (minn w1 w2))) I) *)
(*                                  | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fsint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint (minn w1 w2))) I) *)
(*                                  | _, _ => None *)
(*                                  end *)
(*    | Eprim_binop Bdshl e1 e2 => match type_of_expr e1 tmap, type_of_expr e2 tmap with *)
(*                                  | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint (w1 + 2 ^ w2 - 1))) I) *)
(*                                  | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fuint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint (w1 + 2 ^ w2 - 1))) I) *)
(*                                  | _, _ => None *)
(*                                  end *)
(*    | Eprim_binop Bdshr e1 e2 => match type_of_expr e1 tmap, type_of_expr e2 tmap with *)
(*                                  | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint w1)) I) *)
(*                                  | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fuint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint w1)) I) *)
(*                                  | _, _ => None *)
(*                                  end *)
(*    | Eprim_binop Bcat e1 e2 => match type_of_expr e1 tmap, type_of_expr e2 tmap with *)
(*                                 | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _) *)
(*                                 | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fsint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint (w1 + w2))) I) *)
(*                                 | _, _ => None *)
(*                                 end *)
(*    | Eprim_binop Band e1 e2 *)
(*    | Eprim_binop Bor e1 e2 *)
(*    | Eprim_binop Bxor e1 e2 => match type_of_expr e1 tmap, type_of_expr e2 tmap with *)
(*                                 | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _) *)
(*                                 | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fsint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint (maxn w1 w2))) I) *)
(*                                 | _, _ => None *)
(*                                 end *)
(*    | Emux c e1 e2 => match type_of_expr c tmap, type_of_expr e1 tmap, type_of_expr e2 tmap with *)
(*                       | Some (exist (Gtyp (Fuint 1)) _), Some t1, Some t2 => ftype_mux t1 t2 *)
(*                       | _, _, _ => None *)
(*                       end *)
(*    | Evalidif c e1 => match type_of_expr c tmap with *)
(*                       | Some (exist (Gtyp (Fuint 1)) _) => type_of_expr e1 tmap *)
(*                       | _ => None *)
(*                       end *)
(*    (* | _ => None (* Some (exist ftype_not_implicit_width (Gtyp (Fuint 0)) I) *) *) *)
(*    end. *)


(* (*---------------------------------------------------------------------------*) *)
(* (* Construct lists of input connectors and expressions (for connecting)      *) *)

(* Fixpoint select_field (f : VarOrder.t) (l : seq CEP.key) (ff : ffield) : option (seq CEP.key * ftype) := *)
(* (* select field f from the list of input connectors l, which corresponds to type ff. *)
(*    ff does not need to be passive, but its direction is ignored. *)
(*    Return the corresponding output connectors, and also return the type of the field f. *) *)
(* match ff with *)
(* | Fflips v _ ft ff' => *)
(*     let elsize := size_of_ftype ft in *)
(*     if size l < elsize then None *)
(*     else if f == v then Some (take elsize l, ft) *)
(*          else select_field f (drop elsize l) ff' *)
(* | _ => None *)
(* end. *)

(* Lemma select_field_size : *)
(* forall (v : VarOrder.T) (ff : ffield) (input_list : seq CEP.key), *)
(*    size_of_fields ff <= size input_list -> *)
(*       match select_field v input_list ff with *)
(*       | Some (output_list, ft) => size output_list = size_of_ftype ft *)
(*       | None => True *)
(*       end. *)
(* Proof. *)
(* induction ff ; simpl ; first by trivial. *)
(* intros. *)
(* assert (size input_list < size_of_ftype f0 = false) *)
(*       by (apply negbTE ; rewrite -leqNgt ; *)
(*           apply (leq_trans (n := size_of_ftype f0 + size_of_fields ff)) ; *)
(*           try apply H ; *)
(*           apply leq_addr). *)
(* rewrite H0. *)
(* destruct (v == v0). *)
(* * rewrite size_take. *)
(*   destruct (size_of_ftype f0 < size input_list) eqn: H1 ; first by reflexivity. *)
(*   apply anti_leq. *)
(*   rewrite leqNgt H1 andTb leqNgt H0 //. *)
(* * specialize (IHff (drop (size_of_ftype f0) input_list)). *)
(*   destruct (select_field v (drop (size_of_ftype f0) input_list) ff) as [[output_list ff']|] ; last by trivial. *)
(*   apply IHff. *)
(*   rewrite size_drop leq_subRL ; first by exact H. *)
(*   rewrite leqNgt H0 //. *)
(* Qed. *)

(* Lemma list_rhs_ref_p_ffield : *)
(* forall (v : VarOrder.T) (ff : ffield) (input_list : seq CEP.key), *)
(*    match type_of_ffield v ff, select_field v input_list ff with *)
(*    | Some type_ff, Some (_, list_ff) => type_ff = list_ff *)
(*    | Some _, None => size input_list < size_of_fields ff *)
(*    | None, Some _ => False *)
(*    | None, None => True *)
(*    end. *)
(* Proof. *)
(* induction ff ; simpl ; first by trivial. *)
(* intro ; destruct (v == v0). *)
(* * destruct (size input_list < size_of_ftype f0) eqn: Hshort ; *)
(*         last by reflexivity. *)
(*   apply ltn_addr. *)
(*   rewrite Hshort //. *)
(* * destruct (type_of_ffield v ff). *)
(*   + destruct (size input_list < size_of_ftype f0) eqn: Hshort. *)
(*     - apply ltn_addr. *)
(*       rewrite Hshort //. *)
(*     - specialize (IHff (drop (size_of_ftype f0) input_list)). *)
(*       destruct (select_field v (drop (size_of_ftype f0) input_list) ff) as [[t list_ff]|] eqn: Hselect ; *)
(*             first by exact IHff. *)
(*       rewrite size_drop ltn_subLR in IHff ; first by exact IHff. *)
(*       apply negbT in Hshort. *)
(*       rewrite -leqNgt in Hshort. *)
(*       by exact Hshort. *)
(*   + destruct (size input_list < size_of_ftype f0) eqn: Hshort ; *)
(*           first by trivial. *)
(*     specialize (IHff (drop (size_of_ftype f0) input_list)). *)
(*     destruct (select_field v (drop (size_of_ftype f0) input_list) ff) as [[t list_ff]|] eqn: Hselect ; *)
(*           done. *)
(* Qed. *)

(* Fixpoint list_lhs_ref_p (ref : HiFP.href) (tmap : CEP.t ftype) : option (seq CEP.key * ftype) := *)
(* (* find which input connectors of ground-type identifiers correspond to reference ref. *)
(*    ground-type identifiers are vertices in the module graph (identified by a pair of N); *)
(*    input connectors are always the triple (vertex identifier, N0). *)
(*    Also find the type of reference ref. *) *)
(* match ref with *)
(* | Eid v => *)
(*     (* Construct a list of identifiers and find the type of v *) *)
(*     match CEP.find v tmap with *)
(*     | Some t => *)
(*         Some (mkseq (fun i => (fst v, N.add (snd v) (N.of_nat i))) (size_of_ftype t), t) *)
(*     | None => None *)
(*     end *)
(* | Esubfield ref' f => *)
(*     match list_lhs_ref_p ref' tmap with *)
(*     | Some (l, Btyp ff) => *)
(*         (* Select from list l the relevant part for field f. *)
(*            Determine which part this is based on t *) *)
(*         select_field f l ff *)
(*     | _ => None *)
(*     end *)
(* | Esubindex ref' n => *)
(*     match list_lhs_ref_p ref' tmap with *)
(*     | Some (l, Atyp t m) => *)
(*         (* Select from list l the relevant part for array element n. *)
(*            Determine which part this is based on t *) *)
(*         let elsize := size_of_ftype t in *)
(*         if (n < m) && (size l == m * elsize) *)
(*         then Some (take elsize (drop (n * elsize) l), t) *)
(*         else None *)
(*     | _ => None *)
(*     end *)
(* | Esubaccess _ _ => None *)
(* end. *)

(* Lemma list_lhs_ref_p_size : *)
(* forall (tmap : CEP.t ftype) (ref : HiFP.href), *)
(* match list_lhs_ref_p ref tmap with *)
(* | Some (input_list, ft) => size input_list = size_of_ftype ft *)
(* | None => True *)
(* end. *)
(* Proof. *)
(* induction ref ; simpl ; try done. *)
(* * destruct (CEP.find s tmap) as [ft|] ; last by trivial. *)
(*   rewrite size_mkseq //. *)
(* * destruct (list_lhs_ref_p ref tmap) as [[input_list [| |ff]]|] ; try apply IHref ; try done. *)
(*   generalize (select_field_size v ff input_list) ; intro. *)
(*   destruct (select_field v input_list ff) as [[output_list ft]|]; last by trivial. *)
(*   apply H, eq_leq. *)
(*   rewrite IHref //. *)
(* * destruct (list_lhs_ref_p ref tmap) as [[input_list [|t m|]]|] ; try by trivial. *)
(*   destruct ((n < m) && (size input_list == m * size_of_ftype t)) eqn: Hshort ; last by trivial. *)
(*   move /andP : Hshort => [Hnm /eqP Hshort]. *)
(*   rewrite size_take size_drop Hshort -mulnBl. *)
(*   destruct (size_of_ftype t < (m - n) * size_of_ftype t) eqn: Hsize ; first by reflexivity. *)
(*   apply anti_leq. *)
(*   rewrite leqNgt Hsize andTb -subnSK // mulSn leq_addr //. *)
(* Qed. *)

(* Lemma list_lhs_ref_p_type : *)
(* forall (tmap : CEP.t ftype) (ref : HiFP.href), *)
(*    match type_of_ref ref tmap, list_lhs_ref_p ref tmap with *)
(*    | Some type_ft, Some (list_lst, list_ft) => type_ft = list_ft *)
(*    | Some _, None *)
(*    | None, Some _ => False *)
(*    | None, None => True *)
(*    end. *)
(* Proof. *)
(* intros. *)
(* induction ref ; simpl ; try by done. *)
(* * destruct (CEP.find s tmap) ; by done. *)
(* * destruct (type_of_ref ref tmap) as [type_ft|] ; *)
(*         last by destruct (list_lhs_ref_p ref tmap) ; done. *)
(*   generalize (list_lhs_ref_p_size tmap ref) ; intro. *)
(*   destruct (list_lhs_ref_p ref tmap) as [[input_list list_ft]|] ; try done. *)
(*   rewrite IHref ; clear type_ft IHref. *)
(*   destruct (list_ft) ; try done. *)
(*   generalize (list_rhs_ref_p_ffield v f input_list) ; intro. *)
(*   simpl size_of_ftype in H. *)
(*   destruct (type_of_ffield v f) as [type_ff|] eqn: Hfield ; try done. *)
(*   destruct (select_field v input_list f) ; try done. *)
(*   rewrite H ltnn // in H0. *)
(* * destruct (type_of_ref ref tmap) as [type_ft|] ; *)
(*         last by destruct (list_lhs_ref_p ref tmap) ; done. *)
(*   generalize (list_lhs_ref_p_size tmap ref) ; intro. *)
(*   destruct (list_lhs_ref_p ref tmap) as [[input_list list_ft]|] ; try done. *)
(*   rewrite IHref ; clear type_ft IHref. *)
(*   destruct (list_ft) ; try done. *)
(*   simpl size_of_ftype in H. *)
(*   destruct (n < n0) ; last by rewrite andFb //. *)
(*   rewrite andTb H mulnC eq_refl //. *)
(* Qed. *)

(* Fixpoint list_rhs_ref_p (ref : HiFP.href) (ft : ftype) : option (seq HiFP.hfexpr) := *)
(* (* Finds expressions for the ground-type components of the reference ref, which is of type ft. *)
(*    ft must be a passive type. *) *)
(* match ft with *)
(* | Gtyp _ => Some [:: Eref ref] *)
(* | Atyp t n => *)
(*     iteri n (fun (i : nat) (ol : option (seq HiFP.hfexpr)) => *)
(*                  match ol, list_rhs_ref_p (Esubindex ref i) t with *)
(*                  | Some l, Some li => Some (l ++ li) *)
(*                  | _, _ => None *)
(*                  end) *)
(*           (Some [::]) *)
(* | Btyp ff => list_rhs_ref_p_fields ref ff *)
(* end *)
(* with list_rhs_ref_p_fields (ref : HiFP.href) (ff : ffield) : option (seq HiFP.hfexpr) := *)
(* match ff with *)
(* | Fnil => Some [::] *)
(* | Fflips v Nflip t ff' => *)
(*     match list_rhs_ref_p (Esubfield ref v) t, list_rhs_ref_p_fields ref ff' with *)
(*     | Some l1, Some l2 => Some (l1 ++ l2) *)
(*     | _, _ => None *)
(*     end *)
(* | Fflips _ Flipped _ _ => None *)
(* end. *)

(* Lemma list_rhs_ref_p_size : *)
(* forall (ft : ftype) (ref : HiFP.href), *)
(*    match list_rhs_ref_p ref ft with *)
(*    | Some expr_list => size expr_list = size_of_ftype ft *)
(*    | None => True *)
(*    end *)
(* with list_rhs_ref_p_fields_size : *)
(* forall (ff : ffield) (ref : HiFP.href), *)
(*    match list_rhs_ref_p_fields ref ff with *)
(*    | Some expr_list => size expr_list = size_of_fields ff *)
(*    | None => True *)
(*    end. *)
(* Proof. *)
(* * clear list_rhs_ref_p_size. *)
(*   induction ft ; intro ; simpl ; first by done. *)
(*   + induction n ; simpl ; first by rewrite muln0 //. *)
(*     destruct (iteri n *)
(*               (fun (i : nat) (ol : option (seq HiFP.hfexpr)) => *)
(*                match ol with *)
(*                | Some l => *)
(*                    match list_rhs_ref_p (Esubindex ref i) ft with *)
(*                    | Some li => Some (l ++ li) *)
(*                    | None => None *)
(*                    end *)
(*                | None => None *)
(*                end) (Some [::])) ; last by done. *)
(*     specialize (IHft (Esubindex ref n)). *)
(*     destruct (list_rhs_ref_p (Esubindex ref n) ft) ; last by done. *)
(*     rewrite size_cat IHn IHft mulnSr //. *)
(*   + apply list_rhs_ref_p_fields_size. *)
(* * clear list_rhs_ref_p_fields_size. *)
(*   induction ff ; intro ; simpl ; first by done. *)
(*   destruct f ; first by done. *)
(*   specialize (list_rhs_ref_p_size f0 (Esubfield ref v)). *)
(*   destruct (list_rhs_ref_p (Esubfield ref v) f0) ; last by done. *)
(*   specialize (IHff ref). *)
(*   destruct (list_rhs_ref_p_fields ref ff) ; last by done. *)
(*   rewrite size_cat list_rhs_ref_p_size IHff //. *)
(* Qed. *)

(* Fixpoint list_rhs_expr_p (expr : HiFP.hfexpr) (ft : ftype) : option (seq HiFP.hfexpr) := *)
(* (* Finds ground-type components of the expression expr, which is of type ft. *)
(*    Does not do type checking but just assumes that expr has type ft. *)
(*    If the type is not a ground type, then the expression must be either a reference or a multiplexer. *) *)
(* if ft is Gtyp _ then Some [:: expr] *)
(* else match expr with *)
(*      | Emux c e1 e2 => *)
(*          match list_rhs_expr_p e1 ft, list_rhs_expr_p e2 ft with *)
(*          | Some l1, Some l2 => *)
(*              if size l1 == size l2 *)
(*              then Some (map (fun (e12 : HiFP.hfexpr * HiFP.hfexpr) => Emux c (fst e12) (snd e12)) (zip l1 l2)) *)
(*              else None *)
(*          | _, _ => None *)
(*          end *)
(*    (*| Evalidif c e => *)
(*          match list_rhs_expr_p e ft with *)
(*          | Some l => *)
(*              Some (map (fun (ee : HiFP.hfexpr) => Evalidif c ee) l) *)
(*          | None => None *)
(*          end*) *)
(*      | Eref ref => list_rhs_ref_p ref ft *)
(*      | _ => None *)
(*      end. *)

(* Lemma list_rhs_expr_p_size : *)
(* forall (ft : ftype) (expr : HiFP.hfexpr), *)
(*    match list_rhs_expr_p expr ft with *)
(*    | Some expr_list => size expr_list = size_of_ftype ft *)
(*    | None => True *)
(*    end. *)
(* Proof. *)
(* induction ft ; intro ; first by destruct expr ; simpl ; done. *)
(* * induction expr ; simpl ; try done. *)
(*   + destruct (list_rhs_expr_p expr2 (Atyp ft n)) ; last by done. *)
(*     destruct (list_rhs_expr_p expr3 (Atyp ft n)) ; last by done. *)
(*     rewrite IHexpr2 IHexpr3 eq_refl. *)
(*     simpl size_of_ftype in IHexpr2, IHexpr3. *)
(*     rewrite size_map size_zip IHexpr2 IHexpr3 /minn ltnn //. *)
(*   + induction n ; simpl ; first by rewrite muln0 //. *)
(*     destruct (iteri n *)
(*           (fun (i : nat) (ol : option (seq HiFP.hfexpr)) => *)
(*            match ol with *)
(*            | Some l => *)
(*                match list_rhs_ref_p (Esubindex h i) ft with *)
(*                | Some li => Some (l ++ li) *)
(*                | None => None *)
(*                end *)
(*            | None => None *)
(*            end) (Some [::])) ; last by trivial. *)
(*     generalize (list_rhs_ref_p_size ft (Esubindex h n)) ; intro. *)
(*     destruct (list_rhs_ref_p (Esubindex h n) ft) ; last by done. *)
(*     rewrite size_cat IHn H mulnSr //. *)
(* * induction expr ; simpl ; try done. *)
(*   + destruct (list_rhs_expr_p expr2 (Btyp f)) ; last by done. *)
(*     destruct (list_rhs_expr_p expr3 (Btyp f)) ; last by done. *)
(*     rewrite IHexpr2 IHexpr3 eq_refl. *)
(*     simpl size_of_ftype in IHexpr2, IHexpr3. *)
(*     rewrite size_map size_zip IHexpr2 IHexpr3 /minn ltnn //. *)
(*   + induction f ; simpl ; first by done. *)
(*     destruct f ; first by done. *)
(*     generalize (list_rhs_ref_p_size f0 (Esubfield h v)) ; intro. *)
(*     destruct (list_rhs_ref_p (Esubfield h v) f0) ; last by done. *)
(*     destruct (list_rhs_ref_p_fields h f1) ; last by done. *)
(*     rewrite size_cat H IHf //. *)
(* Qed. *)

(* Fixpoint list_rhs_type_p (ft : ftype) : seq fgtyp := *)
(* (* Finds the types of ground-type components of type ft. *)
(*    (In contrast to the older function vtype_list, this function does not convert Freset to *)
(*    Fuint 1 or Fasyncreset.) *)

(*    Probably the same as ft_find_sub. *) *)
(* match ft with *)
(* | Gtyp gt => [:: gt] *)
(* | Atyp ft' m => let elt_list := list_rhs_type_p ft' in *)
(*                 (* append m copies of elt_list to the empty list: *) *)
(*                 iter m (fun (ll : seq fgtyp) => ll ++ elt_list) [::] *)
(* | Btyp ff => list_rhs_ffield_p ff *)
(* end *)
(* with list_rhs_ffield_p (ff : ffield) : seq fgtyp := *)
(* match ff with *)
(* | Fnil => [::] *)
(* | Fflips _ _ ft' ff' => (list_rhs_type_p ft') ++ (list_rhs_ffield_p ff') *)
(* end. *)

(* Lemma list_rhs_type_p_size : *)
(* forall (ft : ftype), *)
(*    size (list_rhs_type_p ft) = size_of_ftype ft *)
(* with list_rhs_ffield_p_size : *)
(* forall (ff : ffield), *)
(*    size (list_rhs_ffield_p ff) = size_of_fields ff. *)
(* Proof. *)
(* * clear list_rhs_type_p_size. *)
(*   induction ft ; simpl ; try done. *)
(*   induction n ; simpl ; first by rewrite muln0 //. *)
(*   rewrite size_cat IHn IHft -mulnSr //. *)
(* * clear list_rhs_ffield_p_size. *)
(*   induction ff ; simpl ; first by done. *)
(*   rewrite size_cat list_rhs_type_p_size IHff //. *)
(* Qed. *)


(* Fixpoint ftype_is_passive (ft : ftype) : bool := *)
(* (* returns true if ft is a passive type *) *)
(* match ft with *)
(* | Gtyp _ => true *)
(* | Atyp ft' _ => ftype_is_passive ft' *)
(* | Btyp ff => ffield_is_passive ff *)
(* end *)
(* with ffield_is_passive (ff : ffield) : bool := *)
(* match ff with *)
(* | Fnil => true *)
(* | Fflips _ Nflip ft' ff' => ftype_is_passive ft' && ffield_is_passive ff' *)
(* | Fflips _ Flipped _ _ => false *)
(* end. *)


(* Definition Swhen_map2_helper (cond : HiFP.hfexpr) (d_true d_false : option def_expr) : option def_expr := *)
(* match d_true, d_false with *)
(* | Some (D_fexpr expr_true), Some (D_fexpr expr_false) => *)
(*     if expr_true == expr_false then d_true *)
(*     else Some (D_fexpr (Emux cond expr_true expr_false)) *)
(* | _, None *)
(* | _, Some D_invalidated *)
(* | Some D_undefined, _ => d_true *)
(* | None, _ *)
(* | Some D_invalidated, _ *)
(* | _, Some D_undefined => d_false *)
(* end. *)

(* Fixpoint Sem_frag_stmt (vm_old : CEP.t vertex_type) (ct_old : CEP.t def_expr) (s : HiFP.hfstmt) (vm_new : CEP.t vertex_type) (ct_new : CEP.t def_expr) (tmap : CEP.t ftype) : Prop := *)
(*    (* The predicate returns True if vm_new/ct_new can be constructed from vm_old/ct_old by applying s. *)
(*    type checking, constraints *) *)
(*    match s with *)
(*    | Sskip => vm_old = vm_new /\ ct_old = ct_new *)
(*    | Sfcnct ref_tgt (Eref ref_src) => (* allow non-passive types *) *)
(*           CEP.Equal vm_old vm_new *)
(*        /\ *)
(*           match list_lhs_ref_p ref_tgt tmap, list_lhs_ref_p ref_src tmap with *)
(*           | Some (lst_tgt, ft_tgt), Some (lst_src, ft_src) => *)
(*                  connect_type_compatible true ft_tgt ft_src false *)
(*               /\ *)
(*                  connect ct_old ref_tgt lst_tgt ft_tgt ref_src lst_src ft_src false ct_new *)
(*               /\ *)
(*                  forall v0 : CEP.key, *)
(*                     if (v0 \in lst_tgt) || (v0 \in lst_src) then True (* already checked in connect_non_passive *) *)
(*                     else CEP.find v0 ct_old = CEP.find v0 ct_new *)
(*           | _, _ => False *)
(*           end *)
(*    | Sfcnct ref expr => *)
(*           CEP.Equal vm_old vm_new *)
(*        /\ *)
(*           match type_of_ref ref tmap, type_of_expr expr tmap with *)
(*           | Some ft_ref, Some (exist ft_expr _) => *)
(*                  connect_type_compatible false ft_ref ft_expr false *)
(*               /\ *)
(*                  match list_lhs_ref_p ref tmap, list_rhs_expr_p expr ft_expr with *)
(*                  | Some (input_list, _), Some expr_list => *)
(*                         (forall n : nat, *)
(*                              match List.nth_error input_list n, List.nth_error expr_list n with *)
(*                              | Some ic, Some ex => CEP.find ic ct_new = Some (D_fexpr ex) *)
(*                              (* connect_type_compatible already checked that the lists have the same length. *)
(*                                 There is no need to add a check here: *)
(*                              | Some _, None | None, Some _ => False *) *)
(*                              | _, _ => True *)
(*                              end) *)
(*                      /\ *)
(*                         forall v0 : CEP.key, *)
(*                             if v0 \in input_list then True *)
(*                             else CEP.find v0 ct_old = CEP.find v0 ct_new *)
(*                  | _, _ => False *)
(*                  end *)
(*           | _, _ => False *)
(*           end *)
(*    | Sinvalid ref => *)
(*           CEP.Equal vm_old vm_new *)
(*        /\ *)
(*           match list_lhs_ref_p ref tmap with *)
(*           | Some (input_list, ft_ref) => *)
(*                  (forall n : nat, *)
(*                       match List.nth_error input_list n with *)
(*                       | Some ic => CEP.find ic ct_new = Some D_invalidated *)
(*                       | None => True *)
(*                       end) *)
(*               /\ *)
(*                  forall v0 : CEP.key, *)
(*                      if v0 \in input_list then True *)
(*                      else CEP.find v0 ct_old = CEP.find v0 ct_new *)
(*           | _ => False *)
(*           end *)
(*    | Swire v _ => *)
(*        match CEP.find v tmap with *)
(*        | Some newft => *)
(*               (* ground-type wires are defined *) *)
(*               (forall n : nat, *)
(*                    match List.nth_error (list_rhs_type_p newft) n with *)
(*                    | Some gt => CEP.find (fst v, N.add (snd v) (N.of_nat n)) vm_new = Some (Wire gt) *)
(*                    | None => True *)
(*                    end) *)
(*            /\ (* other vertices do not change *) *)
(*               (forall (v0 n0 : N), v0 <> fst v \/ n0 < snd v \/ n0 >= N.add (snd v) (N.of_nat (size_of_ftype newft)) -> *)
(*                    CEP.find (v0, n0) vm_old = *)
(*                    CEP.find (v0, n0) vm_new) *)
(*            /\ (* other connections do not change *) *)
(*               (forall (v0 n0 : N), v0 <> fst v \/ n0 < snd v \/ n0 >= N.add (snd v) (N.of_nat (size_of_ftype newft)) -> *)
(*                    CEP.find (v0, n0) ct_old = *)
(*                    CEP.find (v0, n0) ct_new) *)
(*            /\ (* set wires to undefined *) *)
(*               forall n0 : N, n0 < size_of_ftype newft -> *)
(*                   CEP.find (fst v, N.add (snd v) n0) ct_new = Some D_undefined *)
(*        | None => False (* should not happen *) *)
(*        end *)
(*    | Sreg v reg => *)
(*        match CEP.find v tmap with *)
(*        | Some newft => (* aggregate-type register *) *)
(*               match reset reg with *)
(*               | Rst rst_sig rst_val => (* type check rst_sig *) *)
(*                      match type_of_expr rst_sig tmap with *)
(*                      | Some (exist (Gtyp (Fuint 1)) _) *)
(*                      | Some (exist (Gtyp Fasyncreset) _) => true *)
(*                      | _ => false *)
(*                      end *)
(*                   /\ (* type check rst_val -- also ensures that newft is passive *) *)
(*                      match type_of_expr rst_val tmap with *)
(*                      | Some (exist rst_val_type _) => connect_type_compatible false newft rst_val_type false *)
(*                      | None => false *)
(*                      end *)
(*               | NRst => (* type check newft: we only need to verify newft is passive *) *)
(*                    ftype_is_passive newft *)
(*               end *)
(*            /\ (* module graph contains ground-type registers *) *)
(*               (forall n : nat, *)
(*                    match List.nth_error (list_rhs_type_p newft) n with *)
(*                    | Some gt => CEP.find (fst v, N.add (snd v) (N.of_nat n)) vm_new = *)
(*                        Some (Register gt (clock reg) (reset reg) *)
(*                                       (if reset reg is Rst rst_sig rst_val *)
(*                                        then if type_of_expr rst_sig tmap is Some (exist (Gtyp Fasuncreset) _) *)
(*                                             then true else false *)
(*                                        else false)) *)
(*                    | None => True *)
(*                    end) *)
(*            /\ (* type check clock *) *)
(*               match type_of_expr (clock reg) tmap with *)
(*               | Some (exist (Gtyp Fclock) _) => True *)
(*               | _ => False *)
(*               end *)
(*            /\ (* connect default value for register *) *)
(*               match list_rhs_expr_p (Eref (Eid v)) newft with *)
(*               | Some expr_list => *)
(*                   forall n : nat, *)
(*                       match List.nth_error expr_list n with *)
(*                       | Some ex => CEP.find (fst v, N.add (snd v) (N.of_nat n)) ct_new = Some (D_fexpr ex) *)
(*                       | None => True *)
(*                       end *)
(*               | None => False *)
(*               end *)
(*            /\ (* other vertices do not change *) *)
(*               (forall (v0 n0 : N), v0 <> fst v \/ n0 < snd v \/ n0 >= N.add (snd v) (N.of_nat (size_of_ftype newft)) -> *)
(*                   CEP.find (v0, n0) vm_old = *)
(*                   CEP.find (v0, n0) vm_new) *)
(*            /\ (* other connections do not change *) *)
(*               (forall (v0 n0 : N), v0 <> fst v \/ n0 < snd v \/ n0 >= N.add (snd v) (N.of_nat (size_of_ftype newft)) -> *)
(*                   CEP.find (v0, n0) ct_old = *)
(*                   CEP.find (v0, n0) ct_new) *)
(*        | None => False (* should not happen *) *)
(*        end *)
(*    | Snode v expr => *)
(*        match type_of_expr expr tmap with *)
(*        | Some (exist newft _) => (* (fst v, N0), ... all have changed *) *)
(*               (* ground-type nodes are defined *) *)
(*               (forall n : nat, *)
(*                    match List.nth_error (list_rhs_type_p newft) n with *)
(*                    | Some gt => CEP.find (fst v, N.add (snd v) (N.of_nat n)) vm_new = Some (Node gt) *)
(*                    | None => True *)
(*                    end) *)
(*            /\ (* other vertices do not change *) *)
(*               (forall (v0 n0 : N), v0 <> fst v \/ n0 < snd v \/ n0 >= N.add (snd v) (N.of_nat (size_of_ftype newft)) -> *)
(*                    CEP.find (v0, n0) vm_old = *)
(*                    CEP.find (v0, n0) vm_new) *)
(*            /\ (* other connections do not change *) *)
(*               (forall (v0 n0 : N), v0 <> fst v \/ n0 < snd v \/ n0 >= N.add (snd v) (N.of_nat (size_of_ftype newft)) -> *)
(*                    CEP.find (v0, n0) ct_old = *)
(*                    CEP.find (v0, n0) ct_new) *)
(*            /\ (* set nodes to the respective part of the expression *) *)
(*               match list_rhs_expr_p expr newft with *)
(*               | Some expr_list => *)
(*                   forall n : nat, *)
(*                       match List.nth_error expr_list n with *)
(*                       | Some ex => CEP.find (fst v, N.add (snd v) (N.of_nat n)) ct_new = Some (D_fexpr ex) *)
(*                       | None => True *)
(*                       end *)
(*               | None => False *)
(*               end *)
(*        | None => False *)
(*        end *)
(*    | Smem v mem => False (* ? *) *)
(*    | Sinst var1 var2 => False (* ? *) *)
(*    | Swhen cond ss_true ss_false => *)
(*        if type_of_expr cond tmap is Some (exist (Gtyp (Fuint 1)) _) *)
(*        then exists (vm_true : CEP.t vertex_type) (ct_true ct_false : CEP.t def_expr), *)
(*                    Sem_frag_stmts vm_old ct_old ss_true vm_true ct_true tmap *)
(*                 /\ *)
(*                    Sem_frag_stmts vm_true ct_old ss_false vm_new ct_false tmap *)
(*                 /\ *)
(*                    CEP.Equal ct_new *)
(*                        (CEP.map2 (Swhen_map2_helper cond) ct_true ct_false) *)
(*        else False *)
(* end *)
(* with Sem_frag_stmts (vm_old : CEP.t vertex_type) (ct_old : CEP.t def_expr) (ss : HiFP.hfstmt_seq) (vm_new : CEP.t vertex_type) (ct_new : CEP.t def_expr) (tmap : CEP.t ftype) : Prop := *)
(* match ss with *)
(* | Qnil => *)
(*        CEP.Equal vm_old vm_new *)
(*     /\ *)
(*        CEP.Equal ct_old ct_new *)
(* | Qcons s ss' => *)
(*     exists (vm' : CEP.t vertex_type) (ct' : CEP.t def_expr), *)
(*            Sem_frag_stmt vm_old ct_old s vm' ct' tmap *)
(*         /\ *)
(*            Sem_frag_stmts vm' ct' ss' vm_new ct_new tmap *)
(* end. *)


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


Fixpoint type_of_ffield (v : VarOrder.T) (ff : ffield) (ori : HiFP.forient) : option (ftype * HiFP.forient) :=
(* Find the type of field v in bundle type (Btyp ff). *)
match ff with
| Fnil => None
| Fflips v0 flp t ff' =>
    if v != v0 then type_of_ffield v ff' ori
    else match flp, ori with
         | Nflip, _
         | Flipped, HiFP.Duplex => Some (t, ori)
         | Flipped, HiFP.Source => Some (t, HiFP.Sink)
         | Flipped, HiFP.Sink => Some (t, HiFP.Source)
         | _, _ => None
         end
end.

Fixpoint type_of_ref (ref : HiFP.href) (tmap : CEP.t (ftype * HiFP.forient)) : option (ftype * HiFP.forient) :=
(* Find the type of reference ref, using the type information from tmap.

   This function is similar to base_ref; check whether they can be made more similar. *)
match ref with
| Eid v => CEP.find v tmap
| Esubindex ref' n =>
    match type_of_ref ref' tmap with
    | Some (Atyp t m, ori) => if n < m then Some (t, ori) else None
    | _ => None
    end
| Esubfield ref' v =>
    match type_of_ref ref' tmap with
    | Some (Btyp ff, ori) => type_of_ffield v ff ori
    | _ => None
    end
| Esubaccess _ _ => None
end.

Definition fgtyp_mux (x y : fgtyp_explicit) : option fgtyp_explicit :=
(* Find the type of a multiplexer whose two inputs have types x and y, for ground types *)
    match x, y with
    | exist (Fuint wx) _, exist (Fuint wy) _ => Some (Fuint_exp (maxn wx wy))
    | exist (Fsint wx) _, exist (Fsint wy) _ => Some (Fsint_exp (maxn wx wy))
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
  | Btyp fx, px, Btyp fy, py =>
       match ffield_mux' fx px fy py with
       | Some (exist ff pf) => Some (exist ftype_not_implicit_width (Btyp ff) pf)
       | _ => None
       end
  | _, _, _, _ => None
  end
with ffield_mux' (f1 : ffield) (p1 : ffield_not_implicit_width f1) (f2 : ffield) (p2 : ffield_not_implicit_width f2) : option ffield_explicit :=
       match f1, p1, f2, p2 with
       | Fnil, _, Fnil, _ => Some (exist ffield_not_implicit_width Fnil I)
       | Fflips v1 Nflip t1 fs1, p1, Fflips v2 Nflip t2 fs2, p2
         => if v1 == v2 then
               match ftype_mux'  t1  (proj1 p1) t2  (proj1 p2),
                     ffield_mux' fs1 (proj2 p1) fs2 (proj2 p2) with
               | Some (exist ft pt), Some (exist bf pf) =>
                   Some (exist ffield_not_implicit_width (Fflips v1 Nflip ft bf) (conj pt pf))
               | _, _ => None
               end
            else None
       | _, _, _, _ => None
       end.

Definition ftype_mux (x : ftype_explicit) (y : ftype_explicit) : option ftype_explicit :=
(* return the type of mux expression on ftypes

   Similar to mux_types in InferWidths *)
   ftype_mux' (proj1_sig x) (proj2_sig x) (proj1_sig y) (proj2_sig y).

Fixpoint type_of_expr (expr : HiFP.hfexpr) (tmap: CEP.t (ftype * HiFP.forient)) : option ftype_explicit :=
   (* Find the type of expression expr for reading.

   Similar to type_of_hfexpr in InferWidths *)
   match expr with
   | Econst t bs => match t with
                    | Fuint_implicit w => Some (exist ftype_not_implicit_width (Gtyp (Fuint w)) I)
                    | Fsint_implicit w => Some (exist ftype_not_implicit_width (Gtyp (Fsint w)) I)
                    | t => Some (exist ftype_not_implicit_width (Gtyp t) I)
                    end
   | Eref r => match type_of_ref r tmap with
               | Some (t, HiFP.Source)
               | Some (t, HiFP.Duplex) => Some (make_ftype_explicit t)
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
                                | Some (exist (Gtyp (Fuint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint (maxn (w - n) 0))) I)
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
                                 | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint (2 ^ w2 + w1 - 1))) I)
                                 | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fuint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint (2 ^ w2 + w1 - 1))) I)
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
   end.


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

Fixpoint ports_tmap (pp : seq HiFP.hfport) (vm : CEP.t vertex_type) : option (CEP.t (ftype * HiFP.forient)) :=
(* creates a tmap that contains exactly the types of the ports in pp. *)
match pp with
| [::] => Some (CEP.empty (ftype * HiFP.forient))
| Finput v t :: pp' =>
    match code_type_find_vm_widths t v vm, ports_tmap pp' vm with
    | Some (newt, _), Some tmap' =>
        match CEP.find v tmap' with
        | Some _ => None
        | None => Some (CEP.add v (newt, HiFP.Source) tmap')
        end
    | _, _ => None
    end
| Foutput v t :: pp' =>
    match code_type_find_vm_widths t v vm, ports_tmap pp' vm with
    | Some (newt, _), Some tmap' =>
        match CEP.find v tmap' with
        | Some _ => None
        | None => Some (CEP.add v (newt, HiFP.Sink) tmap')
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


Fixpoint stmts_tmap (tmap_scope : CEP.t (ftype * HiFP.forient) * CEP.t (ftype * HiFP.forient)) (ss : HiFP.hfstmt_seq) (vm : CEP.t vertex_type) : option (CEP.t (ftype * HiFP.forient) * CEP.t (ftype * HiFP.forient)) :=
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
with stmt_tmap (tmap_scope : CEP.t (ftype * HiFP.forient) * CEP.t (ftype * HiFP.forient)) (s : HiFP.hfstmt) (vm : CEP.t vertex_type) : option (CEP.t (ftype * HiFP.forient) * CEP.t (ftype * HiFP.forient)) :=
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
        Some (CEP.add v (newt, HiFP.Duplex) (fst tmap_scope), CEP.add v (newt, HiFP.Duplex) (snd tmap_scope))
    | _, _ => None (* identifier v is used multiple times, or the module graph does not fit *)
    end
| Sreg v reg =>
    match CEP.find v (fst tmap_scope), type_of_expr (clock reg) (snd tmap_scope), code_type_find_vm_widths (type reg) v vm with
    | None, Some _, Some (newt, _) =>
        match reset reg with
        | NRst => Some (CEP.add v (newt, HiFP.Duplex) (fst tmap_scope), CEP.add v (newt, HiFP.Duplex) (snd tmap_scope))
        | Rst rst_sig rst_val =>
            (* We already complete the type checking of rst_sig here;
               there will be no repeated type check in Sem_frag_stmt. *)
            match type_of_expr rst_sig (snd tmap_scope) with
            | Some (exist (Gtyp Fasyncreset) _) =>
                (* rst_val needs to be constant. At least it cannot be the register itself.
                   Otherwise we do not check whether the value is actually constant. *)
                match type_of_expr rst_val (snd tmap_scope) with
                | Some _ => Some (CEP.add v (newt, HiFP.Duplex) (fst tmap_scope), CEP.add v (newt, HiFP.Duplex) (snd tmap_scope))
                | None => None (* something undefined or out-of-scope is accessed *)
                end
             | Some (exist (Gtyp (Fuint 1)) _) =>
                (* rst_val can be variable. For example, it can be an expression containing the register itself *)
                match type_of_expr rst_val (CEP.add v (newt, HiFP.Duplex) (snd tmap_scope)) with
                | Some _ => Some (CEP.add v (newt, HiFP.Duplex) (fst tmap_scope), CEP.add v (newt, HiFP.Duplex) (snd tmap_scope))
                | None => None (* something undefined or out-of-scope is accessed *)
                end
             | _ => None (* something undefined or out-of-scope is accessed *)
             end
        end
    | _, _, _ => None (* identifier v is used multiple times, or the clock is out of scope, or the module graph does not fit *)
    end
| Snode v expr =>
    match CEP.find v (fst tmap_scope), type_of_expr expr (snd tmap_scope) with
    | None, Some (exist newt _) =>
        Some (CEP.add v (newt, HiFP.Source) (fst tmap_scope), CEP.add v (newt, HiFP.Source) (snd tmap_scope))
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


Fixpoint select_field (f : VarOrder.t) (l : seq CEP.key) (ff : ffield) (ori : HiFP.forient) : option (seq CEP.key * (ftype * HiFP.forient)) :=
(* select field f from the list of input connectors l, which corresponds to type ff.
   ff does not need to be passive.
   Return the corresponding output connectors, and also return the type of the field f. *)
match ff with
| Fflips v flp ft ff' =>
    let elsize := size_of_ftype ft in
    if size l < elsize then None
    else if f != v then select_field f (drop elsize l) ff' ori
         else match flp, ori with
              | Nflip, _
              | Flipped, HiFP.Duplex => Some (take elsize l, (ft, ori))
              | Flipped, HiFP.Source => Some (take elsize l, (ft, HiFP.Sink))
              | Flipped, HiFP.Sink => Some (take elsize l, (ft, HiFP.Source))
              | Flipped, _ => None
              end
| _ => None
end.


Definition list_lhs_ref_p (ref : pvar) (tmap : CEP.t (ftype * HiFP.forient)) : option (seq pvar * (ftype * HiFP.forient)) :=
(* find which input connectors of ground-type identifiers correspond to reference ref.
   ground-type identifiers are vertices in the module graph (identified by a pair of N);
   input connectors are always the triple (vertex identifier, N0).
   Also find the type of reference ref. *)
(* If orientation information is added to the tmap, the function can
   be modified to also return the orientation of the reference.
   The case Eid would return what is stored in the tmap,
   and the case Esubfield would swap this around in case the field is flipped.
   If, however, the orientation information has to be gathered from
   the vm, it appears more advantageous to me to write a wrapper
   that finds that information. *)
match ref with
| v =>
    (* Construct a list of identifiers and find the type of v *)
    match CEP.find v tmap with
    | Some (t, ori) =>
        Some (mkseq (fun i => (fst v, N.add (snd v) (bin_of_nat i))) (size_of_ftype t), (t, ori))
    | None => None
    end
(* | Esubfield ref' f => *)
(*     match list_lhs_ref_p ref' tmap with *)
(*     | Some (l, (Btyp ff, ori)) => *)
(*         (* Select from list l the relevant part for field f. *)
(*            Determine which part this is based on t *) *)
(*         select_field f l ff ori *)
(*     | _ => None *)
(*     end *)
(* | Esubindex ref' n => *)
(*     match list_lhs_ref_p ref' tmap with *)
(*     | Some (l, (Atyp t m, ori)) => *)
(*         (* Select from list l the relevant part for array element n. *)
(*            Determine which part this is based on t *) *)
(*         let elsize := size_of_ftype t in *)
(*         if (n < m) && (size l == m * elsize) *)
(*         then Some (take elsize (drop (n * elsize) l), (t, ori)) *)
(*         else None *)
(*     | _ => None *)
(*     end *)
(* |  Esubaccess _ _ => None *)
end.


Fixpoint list_rhs_ref_p (ref : pvar) (ft : ftype) : option (seq HiFP.hfexpr) :=
(* Finds expressions for the ground-type components of the reference ref, which is of type ft.
   ft must be a passive type. *)
(* The caller has to verify whether the orientation is correct. *)
match ft with
| Gtyp _ =>
    Some [:: Eref (Eid ref)]
| Atyp t n =>
    iteri n (fun (i : nat) (ol : option (seq HiFP.hfexpr)) =>
                 match ol, list_rhs_ref_p ref t with
                 | Some l, Some li => Some (l ++ li)
                 | _, _ => None
                 end)
          (Some [::])
| Btyp ff => list_rhs_ref_p_fields ref ff
end
with list_rhs_ref_p_fields (ref : pvar) (ff : ffield) : option (seq HiFP.hfexpr) :=
match ff with
| Fnil => Some [::]
| Fflips v Nflip t ff' =>
    match list_rhs_ref_p ref t, list_rhs_ref_p_fields ref ff' with
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
     | Eref (Eid ref) => list_rhs_ref_p ref ft
     | _ => None
     end.


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
        [forall i : ordinal n, connect_port vm_old ct_old (HiFP.hinport  (fst v, bin_of_nat (i * type_len + snd v)) elt) elt vm_new ct_new]
| Atyp elt n, Foutput v _ =>
    let type_len := size_of_ftype elt in
        [forall i : ordinal n, connect_port vm_old ct_old (HiFP.houtport (fst v, bin_of_nat (i * type_len + snd v)) elt) elt vm_new ct_new]
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
                connect_port_fields vm_old ct_old (HiFP.hinport  (fst v, bin_of_nat (type_len + snd v)) (Btyp ff')) ff' vm_new ct_new
            | Foutput v _ =>
                connect_port_fields vm_old ct_old (HiFP.houtport (fst v, bin_of_nat (type_len + snd v)) (Btyp ff')) ff' vm_new ct_new
            end
end.


Definition vm_and_ct_compatible (vm : CEP.t vertex_type) (ct : CEP.t def_expr) :=
forall (v : CEP.key),
    match CEP.find v vm with
    | None
    | Some (InPort _)
    | Some (Node _) => CEP.find v ct = None
    | _ => CEP.find v ct <> None
    end.



Definition Sem_frag_port (vm_old : CEP.t vertex_type) (ct_old : CEP.t def_expr) (p : HiFP.hfport) (vm_new : CEP.t vertex_type) (ct_new : CEP.t def_expr) (tmap : CEP.t (ftype * HiFP.forient)) : Prop :=
(* returns True if the port in p defines the components in vm *)
match p with
| Finput v _
| Foutput v _ =>
    match CEP.find v tmap with
    | Some (ft, _) =>
            connect_port vm_old ct_old p ft vm_new ct_new
        /\ (* other vertices and connections do not change *)
           forall (v0 n0 : N), v0 <> fst v \/ n0 < snd v \/ n0 >= (size_of_ftype ft) + (snd v) ->
                   CEP.find (v0, n0) vm_old = CEP.find (v0, n0) vm_new
               /\
                   CEP.find (v0, n0) ct_old = CEP.find (v0, n0) ct_new
    | None => False
    end
end.


Fixpoint Sem_frag_ports (vm_old : CEP.t vertex_type) (ct_old : CEP.t def_expr) (pp : seq HiFP.hfport) (vm_new : CEP.t vertex_type) (ct_new : CEP.t def_expr) (tmap : CEP.t (ftype * HiFP.forient)) : Prop :=
(* returns True if the ports in pp define the components in vm *)
match pp with
| [::] => vm_old = vm_new /\ ct_old = ct_new
| p :: pp' =>
    exists (vm' : CEP.t vertex_type) (ct' : CEP.t def_expr),
           Sem_frag_ports vm_old ct_old pp' vm' ct' tmap
        /\
           Sem_frag_port vm' ct' p vm_new ct_new tmap
end.


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
                         (flipped : bool)
                         (ct_new : CEP.t def_expr)
                         (ref_tgt : pvar) 
                         (ref_src : pvar) 
                         (* (lst_tgt : CEP.key) (lst_src : CEP.key) *)
  : bool :=
(* The predicate checks whether ct_new contains the correct connection that connects from lst_src to lst_tgt,
   and it does not change the connection into lst_src.
   These lists must be one-element lists for output and input connectors of compatible types.
   It assumes that the types are compatible. *)
match (* lst_tgt, lst_src, flipped,*) ref_tgt, ref_src, flipped with
| ic, oc, false (* , _, ref_src *)
| oc, ic, true (* , ref_src, _ *) =>
       (CEP.find ic ct_old != None)
    &&
       (CEP.find ic ct_new == Some (D_fexpr (Eref (Eid oc))))
    &&
       ((ic == oc) || (CEP.find oc ct_new == CEP.find oc ct_old))
       (* why this is compared?
          In Sem_frag_stmt, it is ensured that connection trees NOT related to tgt or src are not changed.
          Here, we need to ensure that the connection tree of tgt is changed
          and the connection tree of src remains the same. *)
(* | _, _, _, _, _ => false *)
end.

Fixpoint connect (ct_old : CEP.t def_expr)
                 (ref_tgt : pvar) (lst_tgt : list pvar) (ft_tgt : ftype)
                 (ref_src : pvar) (lst_src : list pvar) (ft_src : ftype)
                 (flipped : bool)
                 (ct_new : CEP.t def_expr) : bool :=
(* The predicate returns true if the correct connection trees are in ct_new
   that connect from lst_src to lst_tgt, and that the connection trees that
   connect to lst_src are not changed.  Other connection trees are not checked.
   The type of lst_tgt is ft_tgt, and the type of lst_src is ft_src.
   These references are *not* required to have passive types. *)
match ft_tgt, ft_src with
| Gtyp gt_tgt, Gtyp gt_src => connect_fgtyp ct_old flipped ct_new ref_tgt ref_src 
| Atyp elt_tgt n1, Atyp elt_src n2 =>
       (n1 == n2)
   &&
     let type_len := size_of_ftype elt_tgt in
     all2 (connect_fgtyp ct_old (* ref_tgt ref_src *) flipped ct_new) lst_tgt lst_src
       (* [forall n : ordinal n1, *)
       (*    connect ct_old *)
       (*            ref_tgt (take type_len (drop (n * type_len) lst_tgt)) elt_tgt *)
       (*            ref_src (take type_len (drop (n * type_len) lst_src)) elt_src *)
       (*            flipped ct_new] *)
| Btyp ff_tgt, Btyp ff_src => connect_fields ct_old ref_tgt lst_tgt ff_tgt ref_src lst_src ff_src flipped ct_new
| _, _ => false
end
with connect_fields (ct_old : CEP.t def_expr)
                    (ref_tgt : pvar) (lst_tgt : list CEP.key) (ft_tgt : ffield)
                    (ref_src : pvar) (lst_src : list CEP.key) (ft_src : ffield)
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
              connect ct_old ref_tgt (take type_len lst_tgt) gtt ref_src (take type_len lst_src) gts flipped ct_new
           &&
              connect_fields ct_old ref_tgt (drop type_len lst_tgt) ft ref_src (drop type_len lst_src) fs flipped ct_new
| Fflips v1 Flipped gtt ft, Fflips v2 Flipped gts fs =>
       (v1 == v2)
    &&
       let type_len := size_of_ftype gts in
              connect ct_old ref_tgt (take type_len lst_tgt) gtt ref_src (take type_len lst_src) gts (~~flipped) ct_new
           &&
              connect_fields ct_old ref_tgt (drop type_len lst_tgt) ft ref_src (drop type_len lst_src) fs flipped ct_new
| _, _ => false
end.

Definition invalidate_fgtyp (ct_old : CEP.t def_expr)
                            (lst_tgt : list CEP.key)
                            (ori : HiFP.forient)
                            (ct_new : CEP.t def_expr) : bool :=
(* The predicate checks whether ct_new contains the correct connection that sets lst_tgt to D_invalidated.
   The list must be a one-element list for output (flipped) or an input (~~flipped) connector. *)
match lst_tgt, ori with
| [:: ic], HiFP.Sink
| [:: ic], HiFP.Duplex =>
       (CEP.find ic ct_old != None)
    &&
       (CEP.find ic ct_new == Some D_invalidated)
| [:: oc], HiFP.Source =>
       CEP.find oc ct_new == CEP.find oc ct_old
       (* why this is compared?
          In Sem_frag_stmt, it is ensured that connection trees NOT related to tgt or src are not changed.
          Here, we need to ensure that the connection tree of tgt is changed
          and the connection tree of src remains the same. *)
| _, _ => false
end.

Definition flip_ori (ori : HiFP.forient) : HiFP.forient :=
match ori with
| HiFP.Sink => HiFP.Source
| HiFP.Source => HiFP.Sink
| ori => ori
end.

Fixpoint invalidate (ct_old : CEP.t def_expr)
                    (lst_tgt : list CEP.key) (ft_tgt : ftype)
                    (ori : HiFP.forient)
                    (ct_new : CEP.t def_expr) : bool :=
(* The predicate returns true if the correct connection trees are in ct_new
   that set lst_tgt to D_invalidated.  Other connection trees are not checked.
   The type of lst_tgt is ft_tgt.
   This reference is *not* required to have passive types. *)
match ft_tgt with
| Gtyp gt_tgt => invalidate_fgtyp ct_old lst_tgt ori ct_new
| Atyp elt_tgt n1 =>
       let type_len := size_of_ftype elt_tgt in
       [forall n : ordinal n1,
          invalidate ct_old
                  (take type_len (drop (n * type_len) lst_tgt)) elt_tgt
                  ori ct_new]
| Btyp ff_tgt => invalidate_fields ct_old lst_tgt ff_tgt ori ct_new
end
with invalidate_fields (ct_old : CEP.t def_expr)
                       (lst_tgt : list CEP.key) (ft_tgt : ffield)
                       (ori : HiFP.forient)
                       (ct_new : CEP.t def_expr) : bool :=
(* The predicate returns true if the correct connection trees are in ct_new
   that set lst_tgt to D_invalidated.  Other connection trees are not checked.
   The type of lst_tgt is (Btyp ft_tgt).
   This reference is *not* required to have passive types. *)
match ft_tgt with
| Fnil => true
| Fflips v1 Nflip gtt ft =>
       let type_len := size_of_ftype gtt in
              invalidate ct_old (take type_len lst_tgt) gtt ori ct_new
           &&
              invalidate_fields ct_old (drop type_len lst_tgt) ft ori ct_new
| Fflips v1 Flipped gtt ft =>
       let type_len := size_of_ftype gtt in
              invalidate ct_old (take type_len lst_tgt) gtt (flip_ori ori) ct_new
           &&
              invalidate_fields ct_old (drop type_len lst_tgt) ft ori ct_new
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
| Some D_undefined, _ => d_true
| None, _
| Some D_invalidated, _
| _, Some D_undefined => d_false
| _, Some D_invalidated => d_true
end.

Definition extend_map_with {T : Type} (m dflt : CEP.t T) : CEP.t T :=
(* Returns map m, except that undefined elements are copied from dflt *)
CEP.map2 (fun (elm eld : option T) => if elm is Some e then Some e else eld) m dflt.


  Fixpoint ftype_list_all (ft : ftype) (l : list ftype) : list ftype :=
    match ft with
    | Gtyp t => cons ft l
    | Atyp t n => cons ft (flatten (repeat (ftype_list_all t l) n))
    | Btyp Fnil => nil
    | Btyp b => cons ft (ftype_list_btyp_all b l)
    end
  with ftype_list_btyp_all (b : ffield) (l : list ftype) : list ftype :=
         match b with
         | Fnil => l
         | Fflips v fl t fs => (ftype_list_all t l) ++ (ftype_list_btyp_all fs nil)
         end.

  (* Fixpoint ftype_list' (ft : ftype) (l : list ftype) : list ftype := *)
  (*   match ft with *)
  (*   | Gtyp t => rcons l ft *)
  (*   | Atyp t n => l ++ flatten (repeat (ftype_list' t nil) n) *)
  (*   | Btyp b => ftype_list_btyp' b l *)
  (*   end *)
  (* with ftype_list_btyp' (b : ffield) (l : list ftype) : list ftype := *)
  (*        match b with *)
  (*        | Fnil => l *)
  (*        | Fflips v fl t fs => ftype_list_btyp' fs (ftype_list' t l) *)
  (*        end. *)
  (* Fixpoint ftype_list_all_c (ft : ftype) (l : list ftype) : list ftype := *)
  (*   match ft with *)
  (*   | Gtyp t => cons ft l *)
  (*   | Atyp t n => cons ft (l ++ flatten (repeat (ftype_list_all_c t nil) n)) *)
  (*   | Btyp b => cons ft (ftype_list_btyp_all_c b l) *)
  (*   end *)
  (* with ftype_list_btyp_all_c (b : ffield) (l : list ftype) : list ftype := *)
  (*        match b with *)
  (*        | Fnil => l *)
  (*        | Fflips v fl t fs => ftype_list_btyp_all_c fs (ftype_list_all_c t l) *)
  (*        end. *)  
  (* Fixpoint ftype_list_all_r (ft : ftype) (l : list ftype) : list ftype := *)
  (*   match ft with *)
  (*   | Gtyp t => rcons l ft *)
  (*   | Atyp t n => rcons (l ++ flatten (repeat (ftype_list_all_r t nil) n)) ft *)
  (*   | Btyp b => rcons (ftype_list_btyp_all_r b l) ft *)
  (*   end *)
  (* with ftype_list_btyp_all_r (b : ffield) (l : list ftype) : list ftype := *)
  (*        match b with *)
  (*        | Fnil => l *)
  (*        | Fflips v fl t fs => ftype_list_btyp_all_r fs (ftype_list_all_r t l) *)
  (*        end. *)

  Definition is_gtyp t := match t with | Gtyp _ => true | _ => false end.

  Fixpoint ftype_list_flip (ft : ftype) f (l : list (ftype * bool * bool)) : list (ftype * bool * bool) :=
    match ft with
    | Gtyp t => cons (ft, f, true) l
    | Atyp t n => cons (ft, f, true) (flatten (repeat (ftype_list_flip t f l) n))
    | Btyp Fnil => nil
    | Btyp b => cons (ft, f, true) (ftype_list_btyp_flip b f l)
    end
  with ftype_list_btyp_flip (b : ffield) f (l : list (ftype * bool * bool)) : list (ftype *bool * bool) :=
         match b with
         | Fnil => l
         | Fflips v Flipped t fs => ftype_list_flip t (~~ f) l ++ (ftype_list_btyp_flip fs f nil)
         | Fflips v Nflip t fs => ftype_list_flip t f l ++ (ftype_list_btyp_flip fs f nil)
         end.

  Definition agt := (Atyp (Btyp (Fflips 5%num Flipped (Gtyp (Fsint_implicit 1)) (Fflips 6%num Nflip (Atyp (Gtyp (Fsint 2)) 2) Fnil))) 3).
  Compute (ftype_list_flip agt false nil).
  Compute (ftype_list_all agt nil).
  Compute (ftype_list_all (Btyp Fnil) nil).



Fixpoint Sem_frag_stmt (vm_old : CEP.t vertex_type) (ct_old : CEP.t def_expr) (s : HiFP.hfstmt) (vm_new : CEP.t vertex_type) (ct_new : CEP.t def_expr) (tmap : CEP.t (ftype * HiFP.forient)) : Prop :=
   (* The predicate returns True if vm_new/ct_new can be constructed from vm_old/ct_old by applying s.
   type checking, constraints *)
   match s with
   | Sskip => CEP.Equal vm_old vm_new /\ CEP.Equal ct_old ct_new
   | Sfcnct (Eid ref_tgt) (Eref (Eid ref_src)) => (* allow non-passive types *)
          CEP.Equal vm_old vm_new
       /\
          match list_lhs_ref_p ref_tgt tmap with
          | Some (lst_tgt, (ft_tgt, HiFP.Duplex))
          | Some (lst_tgt, (ft_tgt, HiFP.Sink)) =>
              match list_lhs_ref_p ref_src tmap with
              | Some (lst_src, (ft_src, HiFP.Duplex))
              | Some (lst_src, (ft_src, HiFP.Source)) =>
                     (* we should allow flipped fields even if the orientation is “Sink” and “Source”
                        because the flip will turn around the orientation as well *)
                     connect_type_compatible true ft_tgt ft_src false
                  /\
                     connect ct_old ref_tgt lst_tgt ft_tgt ref_src lst_src ft_src false ct_new
                  /\
                     forall v0 : CEP.key,
                        if (v0 \in lst_tgt) || (v0 \in lst_src) then True (* already checked in connect_non_passive *)
                        else CEP.find v0 ct_old = CEP.find v0 ct_new
              | _ => False
              end
          | _ => False
          end
   | Sfcnct (Eid ref) expr =>
          CEP.Equal vm_old vm_new
       /\
          match list_lhs_ref_p ref tmap with
          | Some (input_list, (ft_ref, HiFP.Sink))
          | Some (input_list, (ft_ref, HiFP.Duplex)) =>
              match type_of_expr expr tmap with
              | Some (exist ft_expr _) =>
                     connect_type_compatible false ft_ref ft_expr false
                  /\
                     match list_rhs_expr_p expr ft_expr with
                     | Some expr_list =>
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
                     | _ => False
                     end
              | _ => False
              end
          | _ => False
          end
   | Sfcnct _ _ => False
   | Sinvalid (Eid ref_tgt) =>
          CEP.Equal vm_old vm_new
       /\
          match list_lhs_ref_p ref_tgt tmap with
          | Some (lst_tgt, (ft_tgt, ori)) =>
                     invalidate ct_old lst_tgt ft_tgt ori ct_new
                  /\
                     forall v0 : CEP.key,
                        if (v0 \in lst_tgt) then True (* already checked in invalidate *)
                        else CEP.find v0 ct_old = CEP.find v0 ct_new
          | _ => False
          end
   | Sinvalid _ => False
   | Swire v _ =>
       match CEP.find v tmap with
       | Some (newft, _) =>
           (* ground-type wires are defined *)

              (let n := size (ftype_list_all newft nil) in
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
       | Some (newft, _) => (* aggregate-type register *)
              match reset reg with
              | Rst rst_sig rst_val =>
                     (* type check rst_sig -- already done when constructing tmap *)
                     (* type check rst_val -- also ensures that newft is passive *)
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
with Sem_frag_stmts (vm_old : CEP.t vertex_type) (ct_old : CEP.t def_expr) (ss : HiFP.hfstmt_seq) (vm_new : CEP.t vertex_type) (ct_new : CEP.t def_expr) (tmap : CEP.t (ftype * HiFP.forient)) : Prop :=
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


  (* similar type of exp*)
  
Definition type_ref (v : ProdVarOrder.t) (tmap : CEP.t ftype) : option ftype :=
  CEP.find (fst v, snd v) tmap .

(* type of mux expression *)
Definition mux_gtyp (t1 : fgtyp) (t2 : fgtyp) : option fgtyp :=
      match t1, t2 with
      | Fuint w1, Fuint w2 => Some (Fuint (maxn w1 w2))
      | Fuint w1, Fuint_implicit w2 => Some (Fuint (maxn w1 w2))
      | Fuint_implicit w1, Fuint w2 => Some (Fuint (maxn w1 w2))
      | Fuint_implicit w1, Fuint_implicit w2 => Some (Fuint (maxn w1 w2))
      | Fsint w1, Fsint w2 => Some (Fsint (maxn w1 w2))
      | Fsint w1, Fsint_implicit w2 => Some (Fsint (maxn w1 w2))
      | Fsint_implicit w1, Fsint w2 => Some (Fsint (maxn w1 w2))
      | Fsint_implicit w1, Fsint_implicit w2 => Some (Fsint (maxn w1 w2))
      | Fclock, Fclock => Some (Fclock)
      | Freset, Freset => Some (Freset)
      | Fasyncreset, Fasyncreset => Some (Fasyncreset)
      | _,_ => None
      end.

Fixpoint mux_types (t1 : ftype) (t2 : ftype) : option ftype :=
      match t1, t2 with
      | Gtyp gt1, Gtyp gt2 => match mux_gtyp gt1 gt2 with
                              | Some gt => Some (Gtyp gt)
                              | _ => None
                              end
      | Atyp t1' n1, Atyp t2' n2 => match n1 == n2, mux_types t1' t2' with
                                    | true, Some t => Some (Atyp t n1)
                                    | _, _ => None
                                    end
      | Btyp bs1, Btyp bs2 =>
          match mux_btyps bs1 bs2 with
          | Some ff => Some (Btyp ff)
          | None => None
          end
      | _, _ => None
      end
with mux_btyps (bs1 : ffield) (bs2 : ffield) : option ffield :=
      match bs1, bs2 with
      | Fnil, Fnil => Some Fnil
      | Fflips v1 Nflip t1 fs1, Fflips v2 Nflip t2 fs2 =>
          if v1 == v2 then match mux_types t1 t2, mux_btyps fs1 fs2 with
                           | Some t, Some fs => Some (Fflips v1 Nflip t fs)
                           | _, _ => None
                           end
                      else None
      (* mux types must be passive, so Flipped is not allowed *)
      | _, _ => None
    end.


Fixpoint type_of_hfexpr (e : HiFP.hfexpr) (ce : CEP.t ftype) : option ftype :=
match e with
| Econst t bs => match t with
               | Fuint_implicit w => Some (Gtyp (Fuint (Nat.max (size bs) w)))
               | Fsint_implicit w => Some (Gtyp (Fsint (Nat.max (size bs) w)))
               | t => Some (Gtyp t)
               end
| Eref (Eid r) => type_ref r ce
| Eref _ => None
| Ecast AsUInt e1 => match type_of_hfexpr e1 ce with
                     | Some (Gtyp (Fsint w)) | Some (Gtyp (Fuint w)) => Some (Gtyp (Fuint w))
                     | Some (Gtyp (Fsint_implicit w)) | Some (Gtyp (Fuint_implicit w)) => Some (Gtyp (Fuint_implicit w))
                     | Some (Gtyp Fclock) | Some (Gtyp Freset) | Some (Gtyp Fasyncreset) => Some (Gtyp (Fuint 1))
                     | _ => None
                     end
| Ecast AsSInt e1 => match type_of_hfexpr e1 ce with
                     | Some (Gtyp (Fsint w)) | Some (Gtyp (Fuint w)) => Some (Gtyp (Fsint w))
                     | Some (Gtyp (Fsint_implicit w)) | Some (Gtyp (Fuint_implicit w)) => Some (Gtyp (Fsint_implicit w))
                     | Some (Gtyp Fclock) | Some (Gtyp Freset) | Some (Gtyp Fasyncreset) => Some (Gtyp (Fsint 1))
                     | _ => None
                     end
| Ecast AsClock e1 => match type_of_hfexpr e1 ce with
                      | Some (Gtyp _) => Some (Gtyp Fclock)
                      | _ => None
                      end
| Ecast AsReset e1 => match type_of_hfexpr e1 ce with
                      | Some (Gtyp _) => Some (Gtyp Freset)
                      | _ => None
                      end
(* | Ecast AsAsync e1 => match type_of_hfexpr e1 ce  with *)
(*                       | Some (Gtyp _) => Some (Gtyp Fasyncreset) *)
(*                       | _ => None *)
(*                       end *)
| Eprim_unop (Upad n) e1 => match type_of_hfexpr e1 ce with
                            | Some (Gtyp (Fsint w)) => Some (Gtyp (Fsint (maxn w n)))
                            | Some (Gtyp (Fuint w)) => Some (Gtyp (Fuint (maxn w n)))
                            | Some (Gtyp (Fsint_implicit w)) => Some (Gtyp (Fsint_implicit (maxn w n)))
                            | Some (Gtyp (Fuint_implicit w)) => Some (Gtyp (Fuint_implicit (maxn w n)))
                            | _ => None
                            end
| Eprim_unop (Ushl n) e1 => match type_of_hfexpr e1 ce with
                            | Some (Gtyp (Fsint w)) => Some (Gtyp (Fsint (w + n)))
                            | Some (Gtyp (Fuint w)) => Some (Gtyp (Fuint (w + n)))
                            | Some (Gtyp (Fsint_implicit w)) => Some (Gtyp (Fsint_implicit (w + n)))
                            | Some (Gtyp (Fuint_implicit w)) => Some (Gtyp (Fuint_implicit (w + n)))
                            | _ => None
                            end
| Eprim_unop (Ushr n) e1 => match type_of_hfexpr e1 ce with
                            | Some (Gtyp (Fsint w)) => Some (Gtyp (Fsint (maxn (w - n) 1)))
                            | Some (Gtyp (Fuint w)) => Some (Gtyp (Fuint (maxn (w - n) 1)))
                            | Some (Gtyp (Fsint_implicit w)) => Some (Gtyp (Fsint_implicit (maxn (w - n) 1)))
                            | Some (Gtyp (Fuint_implicit w)) => Some (Gtyp (Fuint_implicit (maxn (w - n) 1)))
                            | _ => None
                            end
| Eprim_unop Ucvt e1 => match type_of_hfexpr e1 ce with
                        | Some (Gtyp (Fsint w)) => Some (Gtyp (Fsint w))
                        | Some (Gtyp (Fuint w)) => Some (Gtyp (Fsint (w + 1)))
                        | Some (Gtyp (Fsint_implicit w)) => Some (Gtyp (Fsint_implicit w))
                        | Some (Gtyp (Fuint_implicit w)) => Some (Gtyp (Fsint_implicit (w + 1)))
                        | _ => None
                        end
| Eprim_unop Uneg e1 => match type_of_hfexpr e1 ce with
                        | Some (Gtyp (Fsint w)) | Some (Gtyp (Fuint w)) => Some (Gtyp (Fsint (w + 1)))
                        | Some (Gtyp (Fsint_implicit w)) | Some (Gtyp (Fuint_implicit w)) => Some (Gtyp (Fsint_implicit (w + 1)))
                        | _ => None
                        end
| Eprim_unop Unot e1 => match type_of_hfexpr e1 ce with
                        | Some (Gtyp (Fsint w)) | Some (Gtyp (Fuint w)) => Some (Gtyp (Fuint w))
                        | Some (Gtyp (Fsint_implicit w)) | Some (Gtyp (Fuint_implicit w)) => Some (Gtyp (Fuint_implicit w))
                        | _ => None
                        end
| Eprim_unop (Uextr n1 n2) e1 => match type_of_hfexpr e1 ce with
                                 | Some (Gtyp (Fsint w)) | Some (Gtyp (Fuint w))
                                 | Some (Gtyp (Fsint_implicit w)) | Some (Gtyp (Fuint_implicit w)) =>
                                      if (n2 <= n1) && (n1 < w) then Some (Gtyp (Fuint (n1 - n2 + 1)))
                                                                else None
                                 | _ => None
                                 end
| Eprim_unop (Uhead n) e1 => match type_of_hfexpr e1 ce with
                             | Some (Gtyp (Fsint w)) | Some (Gtyp (Fuint w))
                             | Some (Gtyp (Fsint_implicit w)) | Some (Gtyp (Fuint_implicit w)) =>
                                 if n <= w then Some (Gtyp (Fuint n))
                                           else None
                             | _ => None
                             end
| Eprim_unop (Utail n) e1 => match type_of_hfexpr e1 ce with
                             | Some (Gtyp (Fsint w)) | Some (Gtyp (Fuint w))
                             | Some (Gtyp (Fsint_implicit w)) | Some (Gtyp (Fuint_implicit w)) =>
                                 if n <= w then Some (Gtyp (Fuint (w - n)))
                                           else None
                             | _ => None
                             end
| Eprim_unop _ e1 => match type_of_hfexpr e1 ce with
                     | Some (Gtyp (Fsint _)) | Some (Gtyp (Fuint _))
                     | Some (Gtyp (Fsint_implicit _)) | Some (Gtyp (Fuint_implicit _)) => Some (Gtyp (Fuint 1))
                     | _ => None
                     end
| Eprim_binop (Bcomp _) e1 e2 => match type_of_hfexpr e1 ce, type_of_hfexpr e2 ce with
                                 | Some (Gtyp (Fsint _)), Some (Gtyp (Fsint _))
                                 | Some (Gtyp (Fsint _)), Some (Gtyp (Fsint_implicit _))
                                 | Some (Gtyp (Fsint_implicit _)), Some (Gtyp (Fsint _))
                                 | Some (Gtyp (Fsint_implicit _)), Some (Gtyp (Fsint_implicit _))
                                 | Some (Gtyp (Fuint _)), Some (Gtyp (Fuint _))
                                 | Some (Gtyp (Fuint _)), Some (Gtyp (Fuint_implicit _))
                                 | Some (Gtyp (Fuint_implicit _)), Some (Gtyp (Fuint _))
                                 | Some (Gtyp (Fuint_implicit _)), Some (Gtyp (Fuint_implicit _)) =>
                                     Some (Gtyp (Fuint 1))
                                 | _, _ => None
                                 end
| Eprim_binop Badd e1 e2
| Eprim_binop Bsub e1 e2 => match type_of_hfexpr e1 ce, type_of_hfexpr e2 ce with
                            | Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint w2)) => Some (Gtyp (Fuint (maxn w1 w2 + 1)))
                            | Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint_implicit w2))
                            | Some (Gtyp (Fuint_implicit w1)), Some (Gtyp (Fuint w2))
                            | Some (Gtyp (Fuint_implicit w1)), Some (Gtyp (Fuint_implicit w2)) =>
                                Some (Gtyp (Fuint_implicit (maxn w1 w2 + 1)))
                            | Some (Gtyp (Fsint w1)), Some (Gtyp (Fsint w2)) => Some (Gtyp (Fsint (maxn w1 w2 + 1)))
                            | Some (Gtyp (Fsint w1)), Some (Gtyp (Fsint_implicit w2))
                            | Some (Gtyp (Fsint_implicit w1)), Some (Gtyp (Fsint w2))
                            | Some (Gtyp (Fsint_implicit w1)), Some (Gtyp (Fsint_implicit w2)) =>
                                Some (Gtyp (Fsint_implicit (maxn w1 w2 + 1)))
                            | _, _ => None
                            end
| Eprim_binop Bmul e1 e2 => match type_of_hfexpr e1 ce, type_of_hfexpr e2 ce with
                            | Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint w2)) => Some (Gtyp (Fuint (w1 + w2)))
                            | Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint_implicit w2))
                            | Some (Gtyp (Fuint_implicit w1)), Some (Gtyp (Fuint w2))
                            | Some (Gtyp (Fuint_implicit w1)), Some (Gtyp (Fuint_implicit w2)) =>
                                Some (Gtyp (Fuint_implicit (w1 + w2)))
                            | Some (Gtyp (Fsint w1)), Some (Gtyp (Fsint w2)) => Some (Gtyp (Fsint (w1 + w2)))
                            | Some (Gtyp (Fsint w1)), Some (Gtyp (Fsint_implicit w2))
                            | Some (Gtyp (Fsint_implicit w1)), Some (Gtyp (Fsint w2))
                            | Some (Gtyp (Fsint_implicit w1)), Some (Gtyp (Fsint_implicit w2)) =>
                                Some (Gtyp (Fsint_implicit (w1 + w2)))
                            | _, _ => None
                            end
| Eprim_binop Bdiv e1 e2  => match type_of_hfexpr e1 ce, type_of_hfexpr e2 ce with
                             | Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint _))
                             | Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint_implicit _)) => Some (Gtyp (Fuint w1))
                             | Some (Gtyp (Fuint_implicit w1)), Some (Gtyp (Fuint _))
                             | Some (Gtyp (Fuint_implicit w1)), Some (Gtyp (Fuint_implicit _)) => Some (Gtyp (Fuint_implicit w1))
                             | Some (Gtyp (Fsint w1)), Some (Gtyp (Fsint _))
                             | Some (Gtyp (Fsint w1)), Some (Gtyp (Fsint_implicit _)) => Some (Gtyp (Fsint (w1 + 1)))
                             | Some (Gtyp (Fsint_implicit w1)), Some (Gtyp (Fsint _))
                             | Some (Gtyp (Fsint_implicit w1)), Some (Gtyp (Fsint_implicit _)) => Some (Gtyp (Fsint_implicit (w1 + 1)))
                             | _, _ => None
                             end
| Eprim_binop Brem e1 e2 => match type_of_hfexpr e1 ce, type_of_hfexpr e2 ce with
                            | Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint w2)) => Some (Gtyp (Fuint (minn w1 w2)))
                            | Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint_implicit w2))
                            | Some (Gtyp (Fuint_implicit w1)), Some (Gtyp (Fuint w2))
                            | Some (Gtyp (Fuint_implicit w1)), Some (Gtyp (Fuint_implicit w2)) =>
                                Some (Gtyp (Fuint_implicit (minn w1 w2)))
                            | Some (Gtyp (Fsint w1)), Some (Gtyp (Fsint w2)) => Some (Gtyp (Fsint (minn w1 w2)))
                            | Some (Gtyp (Fsint w1)), Some (Gtyp (Fsint_implicit w2))
                            | Some (Gtyp (Fsint_implicit w1)), Some (Gtyp (Fsint w2))
                            | Some (Gtyp (Fsint_implicit w1)), Some (Gtyp (Fsint_implicit w2)) =>
                                Some (Gtyp (Fsint_implicit (minn w1 w2)))
                            | _, _ => None
                            end
| Eprim_binop Bdshl e1 e2 => match type_of_hfexpr e1 ce, type_of_hfexpr e2 ce with
                             | Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint w2)) => Some (Gtyp (Fuint (w1 + 2 ^ w2 - 1)))
                             | Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint_implicit w2))
                             | Some (Gtyp (Fuint_implicit w1)), Some (Gtyp (Fuint w2))
                             | Some (Gtyp (Fuint_implicit w1)), Some (Gtyp (Fuint_implicit w2)) => Some (Gtyp (Fuint_implicit (w1 + 2 ^ w2 - 1)))
                             | Some (Gtyp (Fsint w1)), Some (Gtyp (Fuint w2)) => Some (Gtyp (Fsint (w1 + 2 ^ w2 - 1)))
                             | Some (Gtyp (Fsint w1)), Some (Gtyp (Fsint_implicit w2))
                             | Some (Gtyp (Fsint_implicit w1)), Some (Gtyp (Fsint w2))
                             | Some (Gtyp (Fsint_implicit w1)), Some (Gtyp (Fsint_implicit w2)) => Some (Gtyp (Fsint_implicit (w1 + 2 ^ w2 - 1)))
                             | _, _ => None
                             end
| Eprim_binop Bdshr e1 e2 => match type_of_hfexpr e1 ce, type_of_hfexpr e2 ce with
                             | Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint _))
                             | Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint_implicit _)) => Some (Gtyp (Fuint w1))
                             | Some (Gtyp (Fuint_implicit w1)), Some (Gtyp (Fuint _))
                             | Some (Gtyp (Fuint_implicit w1)), Some (Gtyp (Fuint_implicit _)) => Some (Gtyp (Fuint_implicit w1))
                             | Some (Gtyp (Fsint w1)), Some (Gtyp (Fuint _))
                             | Some (Gtyp (Fsint w1)), Some (Gtyp (Fuint_implicit _)) => Some (Gtyp (Fsint w1))
                             | Some (Gtyp (Fsint_implicit w1)), Some (Gtyp (Fuint _))
                             | Some (Gtyp (Fsint_implicit w1)), Some (Gtyp (Fuint_implicit _)) => Some (Gtyp (Fsint_implicit w1))
                             | _, _ => None
                             end
| Eprim_binop Bcat e1 e2 => match type_of_hfexpr e1 ce, type_of_hfexpr e2 ce with
                            | Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint w2))
                            | Some (Gtyp (Fsint w1)), Some (Gtyp (Fsint w2)) => Some (Gtyp (Fuint (w1 + w2)))
                            | Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint_implicit w2))
                            | Some (Gtyp (Fuint_implicit w1)), Some (Gtyp (Fuint w2))
                            | Some (Gtyp (Fuint_implicit w1)), Some (Gtyp (Fuint_implicit w2))
                            | Some (Gtyp (Fsint w1)), Some (Gtyp (Fsint_implicit w2))
                            | Some (Gtyp (Fsint_implicit w1)), Some (Gtyp (Fsint w2))
                            | Some (Gtyp (Fsint_implicit w1)), Some (Gtyp (Fsint_implicit w2)) =>
                                Some (Gtyp (Fuint_implicit (w1 + w2)))
                            | _, _ => None
                            end
| Eprim_binop Band e1 e2
| Eprim_binop Bor e1 e2
| Eprim_binop Bxor e1 e2 => match type_of_hfexpr e1 ce, type_of_hfexpr e2 ce with
                            | Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint w2))
                            | Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint_implicit w2))
                            | Some (Gtyp (Fuint_implicit w1)), Some (Gtyp (Fuint w2))
                            | Some (Gtyp (Fuint_implicit w1)), Some (Gtyp (Fuint_implicit w2))
                            | Some (Gtyp (Fsint w1)), Some (Gtyp (Fsint w2))
                            | Some (Gtyp (Fsint w1)), Some (Gtyp (Fsint_implicit w2))
                            | Some (Gtyp (Fsint_implicit w1)), Some (Gtyp (Fsint w2))
                            | Some (Gtyp (Fsint_implicit w1)), Some (Gtyp (Fsint_implicit w2)) => Some (Gtyp (Fuint (maxn w1 w2)))
                            | _, _ => None
                            end
| Emux c e1 e2 => match type_of_hfexpr c ce, type_of_hfexpr e1 ce, type_of_hfexpr e2 ce with
                  | Some (Gtyp (Fuint 1)), Some t1, Some t2 => mux_types t1 t2
                  | Some (Gtyp (Fuint_implicit 1)), Some t1, Some t2 =>
                      mux_types t1 t2
                  | _, _, _ => None
                  end
| Evalidif c e1 => match type_of_hfexpr c ce with
                   | Some (Gtyp (Fuint 1)) | Some (Gtyp (Fuint_implicit 1)) => type_of_hfexpr e1 ce
                   | _ => None
                   end
end.

  
  Notation ft_pmap := (CEP.t ftype).
  Notation ft_flp_pmap := (CEP.t (ftype * bool * bool)).
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
  
  Fixpoint gen_ft_pmap r cnt (tls : list (ftype * bool *bool)) (mt : ft_flp_pmap) :=
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
        | Some (t, true, _) =>
            match ee2 with
            | Eref (Eid v2) =>
                match (ft_find v2 mt) with
                | Some (t2, true, true) =>
                    expand_fcnct ess1 ess2 mt (Qrcons l (Sfcnct (Eid v2) (Eref (Eid v)) ))
                | _ =>
                    expand_fcnct ess1 ess2 mt (Qrcons l (Sfcnct (Eid v) ee2))
                end
            | _ => l
            end
        | Some (t, _ , _) => expand_fcnct ess1 ess2 mt (Qrcons l (Sfcnct (Eid v) ee2))
        | None => l
        end
    | _, _ => l
    end.

  (* Expand invalid *)
  Fixpoint expand_invalid_aux (r : pvar) (sz : nat) (cnt : nat) (mt : ft_flp_pmap) (rs : HiFP.hfstmt_seq) : HiFP.hfstmt_seq :=
    match sz with
    | 0 => rs
    | S n => match (ft_find (r.1, (r.2 + N.of_nat cnt)%num) mt) with
             | Some (t, _, b) =>
                 if is_gtyp t then
                   if b then
                     expand_invalid_aux r n (cnt.+1) mt (Qrcons rs (HiFP.sinvalid (HiFP.eid (r.1, r.2 + N.of_nat cnt)%num)))
                   else expand_invalid_aux r n (cnt.+1) mt rs
                 else expand_invalid_aux r n (cnt.+1) mt rs
             | None => rs
             end                                              
    end.

  Definition expand_invalid (r : pvar) mt l : HiFP.hfstmt_seq :=
    match ft_find r mt with
    | None => l
    | Some (t, _, _) =>
      let ts := ftype_list_all t nil in
      let sz := size ts in
      expand_invalid_aux r sz 0 mt l
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
  
  Definition expand_node v e (mt : ft_pmap) (l : HiFP.hfstmt_seq) : HiFP.hfstmt_seq :=
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
    | Sinvalid (Eid v) => expand_invalid v mt sts
    | Sinvalid _ => Qrcons sts s
    | Sinst _ _=> Qrcons sts s
    | Snode v e => expand_node v e ce sts
    | Sfcnct (Eid r1) e2 =>
        match (ft_find r1 ce), type_of_hfexpr e2 ce (* , (ft_find r1 ce) *) with
        | Some t1, Some t2 =>

        if (is_gtyp t1 && is_gtyp t2) || (t1 == t2) then
        (match e2 with
         | Eref _
         | Emux _ _ _ =>
             expand_fcnct (expand_expr_ft_pmap (Eref (Eid r1)) ce nil) (expand_expr_ft_pmap e2 ce nil) mt sts
         (* | Econst _ _ => Qrcons sts s *)
         | _ => Qrcons  sts s
         end)
        else (*(~~(is_gtyp t1) && (t1 != t2)) then*) Qrcons sts s
        | _  , _ => sts
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
  Fixpoint expand_inport_aux (r : pvar) (sz : nat) (cnt : nat) (mt : ft_flp_pmap) (rs : seq HiFP.hfport) : seq HiFP.hfport * ft_flp_pmap :=
    match sz with
    | 0 => (rs, mt)
    | S n => match (ft_find (r.1, (r.2 + N.of_nat cnt)%num) mt) with
             | Some (t, false, _) => if is_gtyp t
                              then expand_inport_aux r n (cnt.+1) (CEP.add (r.1, (r.2 + N.of_nat cnt)%num) (t, false, false) mt) (rcons rs (HiFP.hinport (r.1, r.2 + N.of_nat cnt)%num t))
                              else expand_inport_aux r n (cnt.+1) mt rs
             | Some (t, true, _) => if is_gtyp t
                                 then expand_inport_aux r n (cnt.+1) (CEP.add (r.1, (r.2 + N.of_nat cnt)%num) (t, true, true) mt)
                                        (rcons rs (HiFP.houtport (r.1, r.2 + N.of_nat cnt)%num t))
                              else expand_inport_aux r n (cnt.+1) mt rs
             | None => (rs, mt)
             end                                              
    end.

  Definition expand_inport (r : pvar) (t: ftype) mt l : seq HiFP.hfport * ft_flp_pmap :=
    let ts := ftype_list_all t nil in
    let sz := size ts in
    expand_inport_aux r sz 0 mt l.
  
  Fixpoint expand_outport_aux (r : pvar) (sz : nat) (cnt : nat) (mt : ft_flp_pmap) (rs : seq HiFP.hfport) : seq HiFP.hfport * ft_flp_pmap :=
    match sz with
    | 0 => (rs, mt)
    | S n => match (ft_find (r.1, (r.2 + N.of_nat cnt)%num) mt) with
             | Some (t, false, _) => if is_gtyp t
                              then expand_outport_aux r n (cnt.+1) (CEP.add (r.1, (r.2 + N.of_nat cnt)%num) (t, false, true) mt) (rcons rs (HiFP.houtport (r.1, r.2 + N.of_nat cnt)%num t))
                              else expand_outport_aux r n (cnt.+1) mt rs
             | Some (t, true, _) => if is_gtyp t
                              then expand_outport_aux r n (cnt.+1) (CEP.add (r.1, (r.2 + N.of_nat cnt)%num) (t, true, false) mt) (rcons rs (HiFP.hinport (r.1, r.2 + N.of_nat cnt)%num t))
                              else expand_outport_aux r n (cnt.+1) mt rs
             | None => (rs, mt)
             end                                              
    end.

  Definition expand_outport (r : pvar) t mt l : seq HiFP.hfport * ft_flp_pmap :=
        let ts := ftype_list_all t nil in
        let sz := size ts in
        expand_outport_aux r sz 0 mt l.

  Definition expand_port p l mt :seq HiFP.hfport * ft_flp_pmap :=
    match p with
    | Finput v t => expand_inport v t mt l
    | Foutput v t => expand_outport v t mt l
    end.

  Fixpoint expand_ports (ps : seq HiFP.hfport) l mt : seq HiFP.hfport * ft_flp_pmap :=
    match ps with
    | nil => (l, mt)
    | hd :: tl =>
        let (l', mt') := expand_port hd l mt in
        expand_ports tl l' mt'
    end.

  Definition ft_flp_pmap_empty := CEP.empty (ftype * bool * bool).
  Definition ft_pmap_empty := CEP.empty (ftype).
 
 (* Output a firrtl module *)
  Definition expandconnects_fmodule (m : HiFP.hfmodule) (inf_mp : ft_pmap) : HiFP.hfmodule :=
    match m with
    | FInmod v ps ss =>
        let mt := rcd_flip_m m inf_mp (ft_flp_pmap_empty) in
        let ce := rcd_pmap_m m inf_mp (ft_pmap_empty) in
        let (exp_ps, mt') := expand_ports ps nil mt in
        FInmod v exp_ps (expandconnects_stmt_seq_ft_pmap ss ce mt' HiFP.qnil)
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

(* output io : { flip in : UInt<10>[5], res : UInt<10>} *)
 Definition test_ports1 := [:: HiFP.houtport (9%num, 0%num) (Btyp (Fflips (1%num) Flipped (Atyp (Gtyp (Fuint 10)) 5) (Fflips (2%num) Nflip (Gtyp (Fuint 9)) Fnil)))].
 Definition test_ports_map1 := rcd_pmap_from_ps test_ports1 ft_pmap_empty.

 Definition test_module1 := HiFP.hfinmod (101%num,0%num) test_ports1 HiFP.qnil.
 
 Compute (expandconnects_fmodule test_module1 (rcd_pmap_from_m test_module1 ft_pmap_empty)).

 (* wire io_out_out : { flip ready : UInt<1>, valid : UInt<1>, bits_wky : UInt<8>} *)
 Definition test_sts9 :=  (HiFP.qcons
      (HiFP.swire (10%num,0%num) ((Btyp (Fflips (1%num) Flipped (Gtyp (Fuint 1)) (Fflips (2%num) Nflip (Gtyp (Fuint 1)) Fnil)))))
      (HiFP.qcons (HiFP.snode (11%num,0%num)
         (HiFP.econst (Fuint 1) [:: true]))
      (HiFP.qcons (HiFP.sfcnct (HiFP.eid (10%num,1%num)) (HiFP.eref (HiFP.eid (11%num,0%num))))
         HiFP.qnil))).
 Definition test_module9 := HiFP.hfinmod (101%num,0%num) [::] test_sts9.
 Compute (expandconnects_fmodule test_module9 (rcd_pmap_from_m test_module9 ft_pmap_empty)).
 
 Definition test_sts10 :=  (HiFP.qcons
      (HiFP.swire (10%num,0%num) ((Btyp (Fflips (1%num) Flipped (Gtyp (Fuint 1)) (Fflips (2%num) Nflip (Gtyp (Fuint 1)) Fnil)))))
      (HiFP.qcons (HiFP.swire (12%num,0%num) ((Btyp (Fflips (1%num) Flipped (Gtyp (Fuint 1)) (Fflips (2%num) Nflip (Gtyp (Fuint 1)) Fnil)))))
      (HiFP.qcons (HiFP.snode (11%num,0%num)
         (HiFP.econst (Fuint 1) [:: true]))
      (HiFP.qcons (HiFP.sfcnct (HiFP.eid (10%num,1%num)) (HiFP.eref (HiFP.eid (12%num,2%num))))
         HiFP.qnil)))).
 Definition test_module10 := HiFP.hfinmod (101%num,0%num) [::] test_sts10.
 Compute (expandconnects_fmodule test_module10 (rcd_pmap_from_m test_module10 ft_pmap_empty)).

(* output b: {a: UInt<1>, flip b: UInt<1> }
 wire x: {a: UInt<1>, flip b: UInt<1> }
 x.b <= b.b *)
 Definition test_sts11 :=  
      (HiFP.qcons (HiFP.swire (12%num,0%num) ((Btyp (Fflips (1%num) Nflip (Gtyp (Fuint 1)) (Fflips (2%num) Flipped (Gtyp (Fuint 1)) Fnil)))))
      (HiFP.qcons (HiFP.sfcnct (HiFP.eid (12%num,2%num)) (HiFP.eref (HiFP.eid (11%num,2%num))))
      HiFP.qnil)).
 Definition test_ports11 := [:: HiFP.houtport (11%num, 0%num) (Btyp (Fflips (1%num) Nflip (Gtyp (Fuint 1)) (Fflips (2%num) Flipped (Gtyp (Fuint 1)) Fnil)))].
 Definition test_ports_map11 := rcd_pmap_from_ps test_ports11 ft_pmap_empty.

 Definition test_module11 := HiFP.hfinmod (101%num,0%num) test_ports11 test_sts11.
 
 Compute (expandconnects_fmodule test_module11 (rcd_pmap_from_m test_module11 ft_pmap_empty)).

 (* input a: {a: UInt<1>, flip b: UInt<1>}
    wire _x: {a: UInt<1>, flip b: UInt<1>}
    _x <= a *)
 Definition test_sts12 :=  
      (HiFP.qcons (HiFP.swire (12%num,0%num) ((Btyp (Fflips (1%num) Nflip (Gtyp (Fuint 1)) (Fflips (2%num) Flipped (Gtyp (Fuint 1)) Fnil)))))
      (HiFP.qcons (HiFP.sfcnct (HiFP.eid (12%num,0%num)) (HiFP.eref (HiFP.eid (11%num,0%num))))
      HiFP.qnil)).
 Definition test_ports12 := [:: HiFP.hinport (11%num, 0%num) (Btyp (Fflips (1%num) Nflip (Gtyp (Fuint 1)) (Fflips (2%num) Flipped (Gtyp (Fuint 1)) Fnil)))].
 Definition test_ports_map12 := rcd_pmap_from_ps test_ports12 ft_pmap_empty.

 Definition test_module12 := HiFP.hfinmod (101%num,0%num) test_ports12 test_sts12.
 
 Compute (expandconnects_fmodule test_module12 (rcd_pmap_from_m test_module12 ft_pmap_empty)).

 Definition test_sts13 :=  
   (HiFP.qcons (HiFP.sinvalid (HiFP.eid (11%num,0%num)))
      HiFP.qnil).
 Definition test_ports13 := [:: HiFP.hinport (11%num, 0%num) (Btyp (Fflips (1%num) Nflip (Gtyp (Fuint 1)) (Fflips (2%num) Flipped (Gtyp (Fuint 1)) Fnil)))].
 Definition test_ports_map13 := rcd_pmap_from_ps test_ports13 ft_pmap_empty.

 Definition test_module13 := HiFP.hfinmod (101%num,0%num) test_ports13 test_sts13.
 
 Compute (expandconnects_fmodule test_module13 (rcd_pmap_from_m test_module12 ft_pmap_empty)).
 
(* End ExpandConnectsP. *)
(* (vm_old : module_graph_vertex_set_p.env) (ct_old : module_graph_connection_trees_p.env) (s : HiFP.hfstmt) (vm_new : module_graph_vertex_set_p.env) (ct_new : module_graph_connection_trees_p.env) (tmap : ft_pmap) *)


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


  Definition rel_tfmap_tomap (tf:ft_flp_pmap) (to: CEP.t (ftype * HiFP.forient)) :=
    forall v,
      match CEP.find v tf with
      | Some (t, f, true) =>
          CEP.find v to = Some (t, HiFP.Sink) \/ CEP.find v to = Some (t, HiFP.Duplex)
      | Some (t, f, false) =>
          CEP.find v to = Some (t, HiFP.Source) \/ CEP.find v to = Some (t, HiFP.Duplex)
      | None => CEP.find v to = None
      end.

  Definition rel_tmap_tfmap (t:ft_pmap) (tf: ft_flp_pmap) :=
    forall v s f,
      match CEP.find v t with
      | Some t =>
          CEP.find v tf = Some (t, s, f)
      | None => CEP.find v tf = None
      end.

  Definition rel_tomap_ct (to: CEP.t (ftype * HiFP.forient)) (ct : CEP.t def_expr) :=
    forall v t exp, CEP.find v to = Some (t, HiFP.Sink) ->
                    CEP.find v ct = Some exp. 
 
  Lemma ExpandConnects_skip_correct :
    forall vm_old ct_old vm_new ct_new tmap tfmap tm ss0,
      Sem_frag_stmts vm_old ct_old (expandconnects_stmt_ft_pmap HiFP.sskip tmap tfmap ss0) vm_new ct_new tm ->
      Sem_frag_stmts vm_old ct_old (Qrcons ss0 HiFP.sskip) vm_new ct_new tm.
  Proof.
    rewrite /=//.
  Qed.
    
  Lemma expandConnects_smem_correct :
    forall (s : ProdVarOrder.T) (h : hfmem ProdVarOrder.T) (ct0 : CEP.t def_expr)
    (vm0 : CEP.t vertex_type) (ct1 : CEP.t def_expr) (vm1 : CEP.t vertex_type)
    (tmap : ft_pmap) (tfmap : ft_flp_pmap) (tomap : CEP.t (ftype * HiFP.forient)) ss0,
      Sem_frag_stmts vm0 ct0 (expandconnects_stmt_ft_pmap (Smem s h) tmap tfmap ss0)
    vm1 ct1 tomap -> Sem_frag_stmts vm0 ct0 (Qrcons ss0 (HiFP.smem s h)) vm1 ct1 tomap.
  Proof. rewrite /=//. Qed.

  Lemma expandConnects_sinst_correct :
    forall (s s0 : ProdVarOrder.T) (ct0 : CEP.t def_expr) (vm0 : CEP.t vertex_type)
    (ct1 : CEP.t def_expr) (vm1 : CEP.t vertex_type) (tmap : ft_pmap)
    (tfmap : ft_flp_pmap) (tomap : CEP.t (ftype * HiFP.forient)) ss0,
  Sem_frag_stmts vm0 ct0
    (expandconnects_stmt_ft_pmap (Sinst (var:=ProdVarOrder.T) s s0) tmap tfmap
       ss0) vm1 ct1 tomap ->
  Sem_frag_stmts vm0 ct0 (Qrcons ss0 (Sinst (var:=ProdVarOrder.T) s s0)) vm1 ct1 tomap.
    Proof. rewrite /=//. Qed.
    
  (* Lemma expand_fcnct_rcons : *)
  (*   forall v1 sz1 v2 sz2 ofs1 ofs2 tm ss0 tfm ss, *)
  (*   expand_fcnct *)
  (*      (expand_eref_aux_ft_pmap v1 sz1 ofs2 tm ss0) *)
  (*      (expand_eref_aux_ft_pmap v2 sz2 ofs2 tm ss0) *)
  (*      tfm ss = *)
  (*     qcat ss (expand_fcnct *)
  (*             (expand_eref_aux_ft_pmap v1 sz1 ofs1 tm ss0) *)
  (*             (expand_eref_aux_ft_pmap v2 sz2 ofs2 tm ss0) *)
  (*             tfm HiFP.qnil). *)
  (* Proof. Admitted. *)

  (* Lemma sem_frag_stmts_cat : *)
  (*   forall vm0 ct0 s1 s2 vm1 ct1 tm vm' ct', *)
  (*     Sem_frag_stmts vm0 ct0 (qcat s1 s2) vm1 ct1 tm <-> *)
  (*       (* exists vm' ct' , *) Sem_frag_stmts vm0 ct0 s1 vm' ct' tm /\ Sem_frag_stmts vm' ct' s2 vm1 ct1 tm. *)
  (* Proof. Admitted. *)
 

  (* Lemma sem_frag_stmts_rcons : *)
  (*   forall vm0 ct0 ss st vm' ct' tm vm1 ct1, *)
  (*   Sem_frag_stmts vm0 ct0 *)
  (*   (Qrcons ss st) *)
  (*   vm' ct' tm <-> *)
  (*     (* exists vm1 ct1,  *)Sem_frag_stmt vm1 ct1 st vm' ct' tm /\ Sem_frag_stmts vm0 ct0 ss vm1 ct1 tm. *)
  (* Proof. Admitted. *)

  Lemma expand_wire_cat_aux :
    forall sz r cnt tmap a l,
    expand_wire_aux r sz cnt tmap (Qcons a l) =
      Qcons a (Qcat l (expand_wire_aux r sz cnt tmap HiFP.qnil)).
  Proof.
    elim; intros.
    - rewrite /= Qcats0//.
    - intros; rewrite /=.
      case Hfd : (ft_find (r.1, (r.2 + N.of_nat cnt)%num) tmap) => [t|]; last rewrite Qcats0//.
      case Hisg : (is_gtyp t).
      + rewrite (H r cnt.+1 tmap (HiFP.swire (r.1, (r.2 + N.of_nat cnt)%num) t) HiFP.qnil).
        rewrite qcat0s.
        rewrite (H r cnt.+1 tmap a (Qrcons l (HiFP.swire (r.1, (r.2 + N.of_nat cnt)%num) t))).
        rewrite Qcat_rcons//.
      + rewrite (H r cnt.+1 tmap a l)//.
  Qed.
  
  Lemma expand_wire_cat :
    forall s f tmap a l ,
      expand_wire s f tmap (Qcons a l) = Qcons a (Qcat l (expand_wire s f tmap HiFP.qnil)).
  Proof.
    intros. rewrite /expand_wire expand_wire_cat_aux//.
  Qed.

  Lemma expandconnects_stmt_cat :
    forall s tmap tfmap l,
      expandconnects_stmt_ft_pmap s tmap tfmap l = Qcat l (expandconnects_stmt_ft_pmap s tmap tfmap HiFP.qnil)
  with expandconnects_stmt_seq_cat :
    forall ss tmap tfmap sts,
      expandconnects_stmt_seq_ft_pmap ss tmap tfmap sts = Qcat sts (expandconnects_stmt_seq_ft_pmap ss tmap tfmap HiFP.qnil).
  Proof.
    intros. move : l. elim; first done.
    move : s tmap tfmap.
    elim.
    - admit.
    - intros. rewrite/= expand_wire_cat//.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
  Admitted.

  Lemma expandconnects_sfcnct_gtyp_nflip :
    forall r1 o1 t1 s1 r2 o2 t2 f2 s2 tmap tfmap ss0,
      CEP.find (r1, o1) tmap = Some (Gtyp t1) ->
      CEP.find (r2, o2) tmap = Some (Gtyp t2) ->
      CEP.find (r1, o1) tfmap = Some (Gtyp t1, false, s1) ->
      CEP.find (r2, o2) tfmap = Some (Gtyp t2, f2, s2) ->
      expandconnects_stmt_ft_pmap (HiFP.sfcnct (HiFP.eid (r1, o1)) (HiFP.eref(HiFP.eid (r2, o2)))) tmap tfmap ss0 = 
      Qrcons ss0 (HiFP.sfcnct (HiFP.eid (r1, o1)) (HiFP.eref(HiFP.eid (r2, o2)))).
  Proof.
    intros. rewrite /= H/=. rewrite /type_ref/= H0.
    rewrite /= /expand_eref_ft_pmap H H0/= !N.add_0_r H/= H0/= H1//.
  Qed.

  Lemma expandconnects_sfcnct_gtyp_flip :
    forall r1 o1 t1 s1 r2 o2 t2 tmap tfmap ss0,
      CEP.find (r1, o1) tmap = Some (Gtyp t1) ->
      CEP.find (r2, o2) tmap = Some (Gtyp t2) ->
      CEP.find (r1, o1) tfmap = Some (Gtyp t1, true, s1) ->
      CEP.find (r2, o2) tfmap = Some (Gtyp t2, true, true) ->
      expandconnects_stmt_ft_pmap (HiFP.sfcnct (HiFP.eid (r1, o1)) (HiFP.eref(HiFP.eid (r2, o2)))) tmap tfmap ss0 = 
      Qrcons ss0 (HiFP.sfcnct (HiFP.eid (r2, o2)) (HiFP.eref(HiFP.eid (r1, o1)))).
  Proof.
    intros. rewrite /=H/= /expand_eref_ft_pmap /type_ref/= H0/= !N.add_0_r H H0/= N.add_0_r H/= H1 H2//.
  Qed.

   (* Lemma expandconnects_sfcnct_atyp_nflip : *)
   (*  forall r1 o1 t1 n s1 r2 o2 t2 f2 s2 tmap tfmap ss0, *)
   (*    CEP.find (r1, o1) tmap = Some (Atyp t1 n) -> *)
   (*    CEP.find (r2, o2) tmap = Some (Atyp t2 n) -> *)
   (*    CEP.find (r1, o1) tfmap = Some (Atyp t1 n, false, s1) -> *)
   (*    CEP.find (r2, o2) tfmap = Some (Atyp t2 n, f2, s2) -> *)
   (*    expandconnects_stmt_ft_pmap (HiFP.sfcnct (HiFP.eid (r1, o1)) (HiFP.eref(HiFP.eid (r2, o2)))) tmap tfmap ss0 = (mkseq (fun i => (HiFP.sfcnct (HiFP.eid (r2, bin_of_nat i)) (HiFP.eref(HiFP.eid (r1, bin_of_nat i))))) (size_of_ftype (Atyp t1 n))). *)

  Lemma sem_frag_stmts_sfcnct_refs_vm_same :
    forall vm0 ct0 ct1 tm r1 r2 t1 t2 o2 oe1,
      CEP.find r1 tm = Some (t1, HiFP.Sink) ->
      CEP.find r2 tm = Some (t2, o2) ->
      (o2 = HiFP.Source) \/ (o2 = HiFP.Duplex) ->
      connect_type_compatible true t1 t2 false ->
      CEP.find r1 ct0 = Some oe1 ->
      CEP.find r2 ct0 = CEP.find r2 ct1 ->
      CEP.find r1 ct1 = Some (D_fexpr (HiFP.eref (HiFP.eid r2))) ->
      Sem_frag_stmt vm0 ct0 (HiFP.sfcnct (HiFP.eid r1) (HiFP.eref (HiFP.eid r2))) vm0 ct1 tm.
  Proof. 
    intros. rewrite /=. 
    split; first done.
    rewrite /list_lhs_ref_p H H0. move : H1.
    case Ho2: o2; intros [Ho21| Ho22]; try (inversion Ho21 || inversion Ho22).
    - split; first done.
      split. move : H2.
      case t1, t2; try (done || by case f) ; try rewrite /= !N.add_0_r -!surjective_pairing. 
      (* + rewrite H3 -H4 H5/= !eq_refl andTb orbT//. *)
      (* rewrite /= => /andP [Hnn0 Hcp]. rewrite/eqP Hnn0 andTb. *)
      + move => Hcp. rewrite /= H3 H4 H5/= !eq_refl andTb orbT//.
      + rewrite/= all2E/=. move/andP => [/eqP Hnn0 Hcp].
        rewrite Hnn0 eq_refl !size_mkseq/=.
        move : (connect_type_compatible_size _ _ _ _ Hcp) => Hsz.
        rewrite Hsz eq_refl andTb.
   (*      ft_find r1 ct = Some (D_fexpr (HiFP.eref (HiFP.eid r2))) -> *)
   (* all *)
   (*  [pred xy | *)
   (*    (ft_find xy.1 ct0 != None) && *)
   (*    (ft_find xy.1 ct1 == Some (D_fexpr (Eref (Eid (var:=ProdVarOrder.T) xy.2)))) & *)
   (*    (xy.1 == xy.2) || (ft_find xy.2 ct1 == ft_find xy.2 ct0)] *)
   (*  (zip *)
   (*     (mkseq (fun i : nat => (r1.1, (r1.2 + bin_of_nat i)%num)) (size_of_ftype t2 * n0)) *)
   (*     (mkseq (fun i : nat => (r2.1, (r2.2 + bin_of_nat i)%num)) (size_of_ftype t2 * n0))) *)
  Admitted.

  Axiom sem_frag_stmts_qrcons :
    forall vm0 ct0 vm1 ct1 vm2 ct2 tomap ss0 s,
      Sem_frag_stmts vm0 ct0 (Qrcons ss0 s) vm2 ct2 tomap <->
      Sem_frag_stmts vm0 ct0 ss0 vm1 ct1 tomap /\ Sem_frag_stmt vm1 ct1 s vm2 ct2 tomap.

  Axiom sem_frag_stmts_qcat :
    forall vm0 ct0 vm1 ct1 vm2 ct2 tomap ss1 ss2,
      Sem_frag_stmts vm0 ct0 (Qcat ss1 ss2) vm2 ct2 tomap <->
      Sem_frag_stmts vm0 ct0 ss1 vm1 ct1 tomap /\ Sem_frag_stmts vm1 ct1 ss2 vm2 ct2 tomap.

  Lemma expandConnects_sfcnct_eideid_gtyp_correct :
    forall vm00 ct00 ct0 ct1 vm0 tmap tfmap tomap ss0 r1 o1 r2 o2 t1 t2 f2 s2,
      ft_find (r1, o1) tmap = Some (Gtyp t1) ->
      ft_find (r2, o2) tmap = Some (Gtyp t2) ->
      ft_find (r1, o1) tfmap = Some (Gtyp t1, false, true) ->
      ft_find (r2, o2) tfmap = Some (Gtyp t2, f2, s2) ->
      rel_tfmap_tomap tfmap tomap ->
      connect_type_compatible true (Gtyp t1) (Gtyp t2) false ->
      Sem_frag_stmts vm00 ct00 ss0 vm0 ct0 tomap ->
      Sem_frag_stmts vm00 ct00 (expandconnects_stmt_ft_pmap (HiFP.sfcnct (HiFP.eid (r1, o1)) (HiFP.eref(HiFP.eid (r2, o2)))) tmap tfmap ss0) vm0 ct1 tomap ->
      Sem_frag_stmt vm0 ct0 (HiFP.sfcnct (HiFP.eid (r1, o1)) (HiFP.eref(HiFP.eid (r2, o2)))) vm0 ct1 tomap.
  Proof.
    intros; rewrite /=. split; first done. move : H6; rewrite /= H /type_ref/=.
    rewrite H0/=.
    have -> : expand_fcnct (expand_eref_ft_pmap (r1, o1) tmap [::])
                (expand_eref_ft_pmap (r2, o2) tmap [::]) tfmap ss0 =
                expandconnects_stmt_ft_pmap (Sfcnct (HiFP.eid (r1, o1)) (HiFP.eref (HiFP.eid (r2, o2)))) tmap tfmap ss0.
    by rewrite /= H /type_ref H0//.
    rewrite (expandconnects_sfcnct_gtyp_nflip r1 o1 t1 true r2 o2 t2 f2 s2)//.
    move : (H3 (r1, o1)). rewrite H1 => Ho. move : (H3 (r2, o2)). rewrite H2 => Ho2.
    intro Hsfs.
    rewrite (sem_frag_stmts_qrcons vm00 ct00 vm0 ct0 vm0 ct1 tomap ss0 _) in Hsfs. move : Hsfs  => [_ Hs0 ].
    (* move : (sem_frag_stmts_qrcons vm00 ct00 vm0 ct0 vm0 ct1 tomap ss0 _ Hsfs). *) rewrite /= in Hs0.
    move : Hs0 => [_ Hs0]. move : Hs0.
    move : Ho => [Hs| Hd]. 
    rewrite /list_lhs_ref_p Hs. move : Ho2 H2. case Hs2b: s2. move => [Hs2 | Hd2] Ho2.
    rewrite Hs2//. rewrite Hd2 H4. split; first done.
    move : Hs0 => [_ Hs0]. 
    move : Hs0 => [Hcn Hin]. done.
    move => [Hs2| Hd2] Hfd2; first rewrite Hs2 H4//; last rewrite Hd2 H4//.
    rewrite /list_lhs_ref_p Hd. move : Ho2 H2. case Hs2b: s2. move => [Hs2 | Hd2] Ho2; first rewrite Hs2 //; last rewrite Hd2 H4//.
    move => [Hs2| Hd2] Hfd2; first rewrite Hs2 H4//; last rewrite Hd2 H4//.
  Qed.

    Lemma expandConnects_sfcnct_eideid_gtyp_flip_correct :
    forall vm00 ct00 ct0 ct1 vm0 tmap tfmap tomap ss0 r1 o1 r2 o2 t1 t2 f2 ,
      ft_find (r1, o1) tmap = Some (Gtyp t1) ->
      ft_find (r2, o2) tmap = Some (Gtyp t2) ->
      ft_find (r1, o1) tfmap = Some (Gtyp t1, true, true) ->
      ft_find (r2, o2) tfmap = Some (Gtyp t2, f2, true) ->
      rel_tfmap_tomap tfmap tomap ->
      connect_type_compatible true (Gtyp t1) (Gtyp t2) false ->
      Sem_frag_stmts vm00 ct00 ss0 vm0 ct0 tomap ->
      Sem_frag_stmts vm00 ct00 (expandconnects_stmt_ft_pmap (HiFP.sfcnct (HiFP.eid (r2, o2)) (HiFP.eref(HiFP.eid (r1, o1)))) tmap tfmap ss0) vm0 ct1 tomap ->
      Sem_frag_stmt vm0 ct0 (HiFP.sfcnct (HiFP.eid (r1, o1)) (HiFP.eref(HiFP.eid (r2, o2)))) vm0 ct1 tomap.
  Proof.
    intros; rewrite /=. split; first done. move : H6; rewrite /= H0 /type_ref/=H/=.
    have -> : expand_fcnct (expand_eref_ft_pmap (r2, o2) tmap [::])
                (expand_eref_ft_pmap (r1, o1) tmap [::]) tfmap ss0 =
                expandconnects_stmt_ft_pmap (Sfcnct (HiFP.eid (r1, o1)) (HiFP.eref (HiFP.eid (r2, o2)))) tmap tfmap ss0.
  Admitted.

  Lemma expandconnects_sfcnct_eideid_r1r2 :
    forall vm1 ct1 r2 o2 r1 o1 tmap tfmap ct_new tomap,
  Sem_frag_stmts vm1 ct1
 (expand_fcnct (expand_eref_ft_pmap (r1, o1) tmap [::])
                (expand_eref_ft_pmap (r2, o2) tmap [::]) tfmap HiFP.qnil) vm1 ct_new tomap ->
  (ft_find (r1, o1) ct1 != None) &&
  (ft_find (r1, o1) ct_new ==
   Some (D_fexpr (Eref (Eid (var:=ProdVarOrder.T) (r2, o2))))) &&
  (((r1, o1) == (r2, o2)) || (ft_find (r2, o2) ct_new == ft_find (r2, o2) ct1)) /\
  (forall v0 : CEP.key,
   if
    (v0 \in mkseq (fun i : nat => (r1, (o1 + bin_of_nat i)%num)) 1)
    || (v0 \in mkseq (fun i : nat => (r2, (o2 + bin_of_nat i)%num)) 1)
   then True
   else ft_find v0 ct1 = ft_find v0 ct_new).
  Proof. Admitted.

Lemma expandconnects_sfcnct_eideid_r1r2_atyp_t :
    forall vm1 ct1 r1 o1 r2 o2 ct_new tomap tmap tfmap f0 f n,
  Sem_frag_stmts vm1 ct1
    (expand_fcnct (expand_eref_ft_pmap (r1, o1) tmap [::])
       (expand_eref_ft_pmap (r2, o2) tmap [::]) tfmap HiFP.qnil) vm1 ct_new tomap ->
  all2 (connect_fgtyp ct1 false ct_new)
    (mkseq (fun i : nat => (r1, (o1 + bin_of_nat i)%num)) (size_of_ftype f0 * n))
    (mkseq (fun i : nat => (r2, (o2 + bin_of_nat i)%num)) (size_of_ftype f * n)) /\
  (forall v0 : CEP.key,
   if
    (v0 \in mkseq (fun i : nat => (r1, (o1 + bin_of_nat i)%num)) (size_of_ftype f0 * n))
    || (v0
          \in mkseq (fun i : nat => (r2, (o2 + bin_of_nat i)%num))
                (size_of_ftype f * n))
   then True
   else ft_find v0 ct1 = ft_find v0 ct_new).  Proof. Admitted.
  
  Lemma expandconnects_sfcnct_eideid_r1r2_atyp_f :
    forall vm1 ct1 r1 o1 r2 o2 ct_new tomap f0 f n0 n,
  Sem_frag_stmts vm1 ct1
    (Qcons (Sfcnct (HiFP.eid (r1, o1)) (HiFP.eref (HiFP.eid (r2, o2))))
       (Qnil ProdVarOrder.T)) vm1 ct_new tomap ->
  all2 (connect_fgtyp ct1 false ct_new)
    (mkseq (fun i : nat => (r1, (o1 + bin_of_nat i)%num)) (size_of_ftype f0 * n0))
    (mkseq (fun i : nat => (r2, (o2 + bin_of_nat i)%num)) (size_of_ftype f * n)) /\
  (forall v0 : CEP.key,
   if
    (v0 \in mkseq (fun i : nat => (r1, (o1 + bin_of_nat i)%num)) (size_of_ftype f0 * n))
    || (v0
          \in mkseq (fun i : nat => (r2, (o2 + bin_of_nat i)%num))
                (size_of_ftype f * n))
   then True
   else ft_find v0 ct1 = ft_find v0 ct_new).
  Proof. Admitted.

  Lemma expandconnects_sfcnct_eideid_r1r2_btyp_t :
    forall vm1 ct1 r1 o1 r2 o2 ct_new tomap tmap tfmap f0 f ,
  Sem_frag_stmts vm1 ct1
    (expand_fcnct (expand_eref_ft_pmap (r1, o1) tmap [::])
       (expand_eref_ft_pmap (r2, o2) tmap [::]) tfmap HiFP.qnil) vm1 ct_new tomap ->
  connect_fields ct1 (r1, o1)
    (mkseq (fun i : nat => (r1, (o1 + bin_of_nat i)%num)) (size_of_fields f0)) f0
    (r2, o2) (mkseq (fun i : nat => (r2, (o2 + bin_of_nat i)%num)) (size_of_fields f))
    f false ct_new /\
  (forall v0 : CEP.key,
   if
    (v0 \in mkseq (fun i : nat => (r1, (o1 + bin_of_nat i)%num)) (size_of_fields f0))
    || (v0 \in mkseq (fun i : nat => (r2, (o2 + bin_of_nat i)%num)) (size_of_fields f))
   then True
   else ft_find v0 ct1 = ft_find v0 ct_new). Proof. Admitted.

  Lemma expandconnects_sfcnct_eideid_r1r2_btyp_f :
    forall vm1 ct1 r1 o1 r2 o2 ct_new tomap  f0 f ,
      Sem_frag_stmts vm1 ct1
        (Qcons (Sfcnct (HiFP.eid (r1, o1)) (HiFP.eref (HiFP.eid (r2, o2))))
           (Qnil ProdVarOrder.T)) vm1 ct_new tomap ->
      connect_fields ct1 (r1, o1)
        (mkseq (fun i : nat => (r1, (o1 + bin_of_nat i)%num)) (size_of_fields f0)) f0
        (r2, o2) (mkseq (fun i : nat => (r2, (o2 + bin_of_nat i)%num)) (size_of_fields f))
        f false ct_new /\
        (forall v0 : CEP.key,
            if
              (v0 \in mkseq (fun i : nat => (r1, (o1 + bin_of_nat i)%num)) (size_of_fields f0))
              || (v0 \in mkseq (fun i : nat => (r2, (o2 + bin_of_nat i)%num)) (size_of_fields f))
            then True
            else ft_find v0 ct1 = ft_find v0 ct_new). Proof. Admitted.

  Lemma expandconnects_swire_atyp :
    forall vm0 ct0 r o gt n tmap tomap vm1 ct1,
    Sem_frag_stmts vm0 ct0
    (expand_wire_aux (r, o) (size (ftype_list_all (Atyp gt n) [::])) 0 tmap HiFP.qnil)
    vm1 ct1 tomap ->
  match
    nth_error (list_rhs_type_p (Atyp gt n)) (size (ftype_list_all (Atyp gt n) [::]))
  with
  | Some gt0 =>
      ft_find (r, bin_of_nat (size (ftype_list_all (Atyp gt n) [::]) + o)) vm0 = None /\
      ft_find (r, bin_of_nat (size (ftype_list_all (Atyp gt n) [::]) + o)) vm1 =
      Some (Wire gt0)
  | None => True
  end /\
  (forall v0 n0 : N,
   v0 <> r \/ n0 < o \/ size_of_ftype (Atyp gt n) + o <= n0 ->
   ft_find (v0, n0) vm0 = ft_find (v0, n0) vm1) /\
  (forall v0 n0 : N,
   v0 <> r \/ n0 < o \/ size_of_ftype (Atyp gt n) + o <= n0 ->
   ft_find (v0, n0) ct0 = ft_find (v0, n0) ct1) /\
  (forall n0 : nat,
   n0 < size_of_ftype (Atyp gt n) ->
   ft_find (r, bin_of_nat (n0 + o)) ct1 = Some D_undefined). Proof. Admitted.

  Lemma expandconnects_swire_btyp : 
    forall vm0 ct0 r o f tmap tomap vm1 ct1,
    Sem_frag_stmts vm0 ct0
    (expand_wire_aux (r, o) (size (ftype_list_all (Btyp f) [::])) 0 tmap HiFP.qnil)
    vm1 ct1 tomap ->
  match
    nth_error (list_rhs_type_p (Btyp f)) (size (ftype_list_all (Btyp f) [::]))
  with
  | Some gt =>
      ft_find (r, bin_of_nat (size (ftype_list_all (Btyp f) [::]) + o)) vm0 = None /\
      ft_find (r, bin_of_nat (size (ftype_list_all (Btyp f) [::]) + o)) vm1 =
      Some (Wire gt)
  | None => True
  end /\
  (forall v0 n0 : N,
   v0 <> r \/ n0 < o \/ size_of_ftype (Btyp f) + o <= n0 ->
   ft_find (v0, n0) vm0 = ft_find (v0, n0) vm1) /\
  (forall v0 n0 : N,
   v0 <> r \/ n0 < o \/ size_of_ftype (Btyp f) + o <= n0 ->
   ft_find (v0, n0) ct0 = ft_find (v0, n0) ct1) /\
  (forall n0 : nat,
   n0 < size_of_ftype (Btyp f) ->
   ft_find (r, bin_of_nat (n0 + o)) ct1 = Some D_undefined). Proof. Admitted.

  (*   Lemma expandConnects_sfcnct_eideid_atyp_correct : *)
  (*   forall vm00 ct00 ct0 ct1 vm0 tmap tfmap tomap ss0 r1 o1 r2 o2 t1 n1 f1 s1 t2 n2 f2 s2, *)
  (*     ft_find (r1, o1) tmap = Some (Atyp t1 n1) -> *)
  (*     ft_find (r2, o2) tmap = Some (Atyp t2 n2) -> *)
  (*     ft_find (r1, o1) tfmap = Some (Atyp t1 n1, f1, s1) -> *)
  (*     ft_find (r2, o2) tfmap = Some (Atyp t2 n2, f2, s2) -> *)
  (*     rel_tfmap_tomap tfmap tomap -> *)
  (*     connect_type_compatible true (Atyp t1 n1) (Atyp t2 n2) false -> *)
  (*     Sem_frag_stmts vm00 ct00 ss0 vm0 ct0 tomap -> *)
  (*     Sem_frag_stmts vm00 ct00 (expandconnects_stmt_ft_pmap (HiFP.sfcnct (HiFP.eid (r1, o1)) (HiFP.eref(HiFP.eid (r2, o2)))) tmap tfmap ss0) vm0 ct1 tomap -> *)
  (*     Sem_frag_stmt vm0 ct0 (HiFP.sfcnct (HiFP.eid (r1, o1)) (HiFP.eref(HiFP.eid (r2, o2)))) vm0 ct1 tomap. *)
  (* Proof. *)
  (* Admitted. *)
  Lemma sem_frag_stmt_qcons_qnil :
    forall vm0 ct0 vm1 ct1 s tomap,
      Sem_frag_stmts vm0 ct0 (Qcons s (Qnil ProdVarOrder.T))
        vm1 ct1 tomap = Sem_frag_stmt vm0 ct0 s vm1 ct1 tomap.
  Proof. Admitted.
    
  Lemma expandConnects_fcnct_eideid_correct :
    forall ct0 vm0 ct1 vm1 ct_new tmap tfmap tomap ss0 r1 o1 r2 o2 t1 t2 ,
      (* Sem_frag_stmt vm_new ct1 ((HiFP.sfcnct (HiFP.eid (r1, o1)) (HiFP.eref(HiFP.eid (r2, o2))))) vm_new ct_new tmap -> *)
      rel_tfmap_tomap tfmap tomap ->
      rel_tmap_tfmap tmap tfmap ->
      ft_find (r1, o1) tmap = Some (t1) ->
      ft_find (r2, o2) tmap = Some (t2) ->
      connect_type_compatible true t1 t2 false ->
      Sem_frag_stmts vm0 ct0 ss0 vm1 ct1 tomap ->
      Sem_frag_stmts vm0 ct0 (expandconnects_stmt_ft_pmap (HiFP.sfcnct (HiFP.eid (r1, o1)) (HiFP.eref(HiFP.eid (r2, o2)))) tmap tfmap ss0) vm1 ct_new tomap ->
      Sem_frag_stmts vm0 ct0 (Qrcons ss0 (HiFP.sfcnct (HiFP.eid (r1, o1)) (HiFP.eref(HiFP.eid (r2, o2))))) vm1 ct_new tomap.
  Proof.
    intros.
    move : H5.
    rewrite (expandconnects_stmt_cat (HiFP.sfcnct (HiFP.eid (r1, o1)) (HiFP.eref (HiFP.eid (r2, o2)))) tmap tfmap ss0).
    move => Hexpcat.
    rewrite (sem_frag_stmts_qcat vm0 ct0 vm1 ct1 vm1 ct_new tomap ss0 _) in Hexpcat.
    move : Hexpcat =>[Hsemss0 Hsemfc].
    rewrite (sem_frag_stmts_qrcons vm0 ct0 vm1 ct1 vm1 ct_new tomap _). split; first done.
    rewrite /=. split; first done.
    move : Hsemfc. rewrite /= /list_lhs_ref_p.
    move : (H0 (r1, o1) false true). rewrite H1 => Htfm1.
    move : (H (r1, o1)). rewrite Htfm1 => Hs1. move : Hs1 => [Hs1 | Hd1].
    move : (H0 (r2, o2) false false). rewrite H2 => Htfm2.
    move : (H (r2, o2)). rewrite Htfm2 => Hs2. move : Hs2 => [Hs2 | Hd2].
    rewrite /type_ref/= H2 Hs1 Hs2.  
    move : H1 H2 H3 Htfm1 Htfm2 Hs1 Hs2.
    case t1; case t2; intros; move : H3; rewrite /=//. move => Hcom . rewrite Hcom; split; first done.
    move : Hsemfc; rewrite/=. intro. apply expandconnects_sfcnct_eideid_r1r2 with vm1 tmap tfmap tomap. done.
    case f0; done. case f0; done.
    move => Hcom . rewrite Hcom; split; first done.
    move : Hcom Hsemfc; rewrite/=. move => /andP[/eqP Hnn0 Hcmp]. rewrite Hnn0/= eq_refl andTb.
    case Hatyp : (Atyp f0 n == Atyp f n); rewrite (lock Sem_frag_stmts)/=-lock.
    exact : expandconnects_sfcnct_eideid_r1r2_atyp_t .
    exact : expandconnects_sfcnct_eideid_r1r2_atyp_f .
    move => Hcom . rewrite Hcom; split; first done.
    move : Hsemfc; rewrite/=.
    case Hbtyp : (Btyp f0 == Btyp f).
    exact : expandconnects_sfcnct_eideid_r1r2_btyp_t .
    exact : expandconnects_sfcnct_eideid_r1r2_btyp_f .
    rewrite /type_ref/= H2 Hs1 Hd2.  
    move : H1 H2 H3 Htfm1 Htfm2 Hs1 Hd2.
    case t1; case t2; intros; move : H3; rewrite /=//. move => Hcom . rewrite Hcom; split; first done.
    move : Hsemfc; rewrite/=. intro. apply expandconnects_sfcnct_eideid_r1r2 with vm1 tmap tfmap tomap. done.
    case f0; done. case f0; done.
    move => Hcom . rewrite Hcom; split; first done.
    move : Hcom Hsemfc; rewrite/=. move => /andP[/eqP Hnn0 Hcmp]. rewrite Hnn0/= eq_refl andTb.
    case Hatyp : (Atyp f0 n == Atyp f n); rewrite (lock Sem_frag_stmts)/=-lock.
    exact : expandconnects_sfcnct_eideid_r1r2_atyp_t .
    exact : expandconnects_sfcnct_eideid_r1r2_atyp_f .
    move => Hcom . rewrite Hcom; split; first done.
    move : Hsemfc; rewrite/=.
    case Hbtyp : (Btyp f0 == Btyp f).
    exact : expandconnects_sfcnct_eideid_r1r2_btyp_t .
    exact : expandconnects_sfcnct_eideid_r1r2_btyp_f .
    rewrite /type_ref/= H2 Hd1 .
    move : (H0 (r2, o2) false false). rewrite H2 => Htfm2.
    move : (H (r2, o2)). rewrite Htfm2 => Hs2. move : Hs2 => [Hs2 | Hd2].
    rewrite Hs2.  
    move : H1 H2 H3 Htfm1 Htfm2 Hd1 Hs2.
    case t1; case t2; intros; move : H3; rewrite /=//. move => Hcom . rewrite Hcom; split; first done.
    move : Hsemfc; rewrite/=. intro. apply expandconnects_sfcnct_eideid_r1r2 with vm1 tmap tfmap tomap. done.
    case f0; done. case f0; done.
    move => Hcom . rewrite Hcom; split; first done.
    move : Hcom Hsemfc; rewrite/=. move => /andP[/eqP Hnn0 Hcmp]. rewrite Hnn0/= eq_refl andTb.
    case Hatyp : (Atyp f0 n == Atyp f n); rewrite (lock Sem_frag_stmts)/=-lock.
    exact : expandconnects_sfcnct_eideid_r1r2_atyp_t .
    exact : expandconnects_sfcnct_eideid_r1r2_atyp_f .
    move => Hcom . rewrite Hcom; split; first done.
    move : Hsemfc; rewrite/=.
    case Hbtyp : (Btyp f0 == Btyp f).
    exact : expandconnects_sfcnct_eideid_r1r2_btyp_t .
    exact : expandconnects_sfcnct_eideid_r1r2_btyp_f .
    rewrite Hd2.
    move : H1 H2 H3 Htfm1 Htfm2 Hd1 Hd2.
    case t1; case t2; intros; move : H3; rewrite /=//. move => Hcom . rewrite Hcom; split; first done.
    move : Hsemfc; rewrite/=. intro. apply expandconnects_sfcnct_eideid_r1r2 with vm1 tmap tfmap tomap. done.
    case f0; done. case f0; done.
    move => Hcom . rewrite Hcom; split; first done.
    move : Hcom Hsemfc; rewrite/=. move => /andP[/eqP Hnn0 Hcmp]. rewrite Hnn0/= eq_refl andTb.
    case Hatyp : (Atyp f0 n == Atyp f n); rewrite (lock Sem_frag_stmts)/=-lock.
    exact : expandconnects_sfcnct_eideid_r1r2_atyp_t .
    exact : expandconnects_sfcnct_eideid_r1r2_atyp_f .
    move => Hcom . rewrite Hcom; split; first done.
    move : Hsemfc; rewrite/=.
    case Hbtyp : (Btyp f0 == Btyp f).
    exact : expandconnects_sfcnct_eideid_r1r2_btyp_t .
    exact : expandconnects_sfcnct_eideid_r1r2_btyp_f .
  Qed.


  
  Definition corresponding_tmap (tm : ft_pmap) := forall r o t, ft_find (r, o) tm = Some t.

  Lemma expandConnects_sfcnct_correct :
  forall (h : ProdVarOrder.T) (h0 : hfexpr ProdVarOrder.T) 
    (ct0 : CEP.t def_expr) (vm0 : CEP.t vertex_type) (ct1 : CEP.t def_expr)
    (vm1 : CEP.t vertex_type) (tmap : ft_pmap) (tfmap : ft_flp_pmap)
    (tomap : CEP.t (ftype * HiFP.forient)),
  corresponding_tmap tmap ->
  rel_tfmap_tomap tfmap tomap ->
  rel_tmap_tfmap tmap tfmap ->
  Sem_frag_stmts vm0 ct0
    (expandconnects_stmt_ft_pmap (Sfcnct (Eid h) h0) tmap tfmap HiFP.qnil) vm1 ct1 tomap ->
  Sem_frag_stmt vm0 ct0 (Sfcnct (Eid h) h0) vm1 ct1 tomap.
  Proof. Admitted.

                
  Lemma expandConnects_sreg_correct :
    forall (s : ProdVarOrder.T) (h : hfreg ProdVarOrder.T) (ct0 : CEP.t def_expr)
           (vm0 : CEP.t vertex_type) (ct1 : CEP.t def_expr) (vm1 : CEP.t vertex_type)
           (tmap : ft_pmap) (tfmap : ft_flp_pmap) (tomap : CEP.t (ftype * HiFP.forient)),
      (* corresponding_tmap tmap -> *)ft_find s tmap = Some (type h) ->
      rel_tfmap_tomap tfmap tomap ->
      rel_tmap_tfmap tmap tfmap ->
      Sem_frag_stmts vm0 ct0 (expandconnects_stmt_ft_pmap (Sreg s h) tmap tfmap HiFP.qnil)
        vm1 ct1 tomap -> Sem_frag_stmt vm0 ct0 (Sreg s h) vm1 ct1 tomap.
  Proof. Admitted.

  Lemma expandConnects_snode_correct :
  forall (s : ProdVarOrder.T) (h : hfexpr ProdVarOrder.T) (ct0 : CEP.t def_expr)
    (vm0 : CEP.t vertex_type) (ct1 : CEP.t def_expr) (vm1 : CEP.t vertex_type)
    (tmap : ft_pmap) (tfmap : ft_flp_pmap) (tomap : CEP.t (ftype * HiFP.forient)),
  corresponding_tmap tmap ->
  rel_tfmap_tomap tfmap tomap ->
  rel_tmap_tfmap tmap tfmap ->
  Sem_frag_stmts vm0 ct0 (expandconnects_stmt_ft_pmap (Snode s h) tmap tfmap HiFP.qnil)
    vm1 ct1 tomap -> Sem_frag_stmt vm0 ct0 (Snode s h) vm1 ct1 tomap.
  Proof. Admitted.

    Lemma expandConnects_sinvalid_correct :
    forall (h : ProdVarOrder.T) (ct0 : CEP.t def_expr) (vm0 : CEP.t vertex_type)
    (ct1 : CEP.t def_expr) (vm1 : CEP.t vertex_type) (tmap : ft_pmap)
    (tfmap : ft_flp_pmap) (tomap : CEP.t (ftype * HiFP.forient)),
  corresponding_tmap tmap ->
  rel_tfmap_tomap tfmap tomap ->
  rel_tmap_tfmap tmap tfmap ->
  Sem_frag_stmts vm0 ct0
    (expandconnects_stmt_ft_pmap (Sinvalid (Eid h)) tmap tfmap HiFP.qnil) vm1 ct1 tomap ->
  Sem_frag_stmt vm0 ct0 (Sinvalid (Eid h)) vm1 ct1 tomap.
      Proof. Admitted.

  
  Lemma expandConnects_swire_correct :
    forall ct0 vm0 ct1 vm1 tmap tfmap tomap r o t ,
      rel_tfmap_tomap tfmap tomap ->
      rel_tmap_tfmap tmap tfmap ->
      ft_find (r, o) tmap = Some (t) ->
      (* Sem_frag_stmts vm0 ct0 ss0 vm1 ct1 tomap -> *)
      Sem_frag_stmts vm0 ct0 (expandconnects_stmt_ft_pmap (HiFP.swire (r, o) t) tmap tfmap HiFP.qnil) vm1 ct1 tomap ->
      Sem_frag_stmt vm0 ct0 (HiFP.swire (r, o) t) vm1 ct1 tomap.
  Proof.
    intros. move : H2. 
    (* rewrite (sem_frag_stmts_qcat vm0 ct0 vm1 ct1 vm1 ct1 tomap ss0 _). move  => [_ Hsw].  *)
    (* rewrite  (sem_frag_stmts_qrcons vm0 ct0 vm1 ct1 vm1 ct1 tomap ss0 _). *)
    (* split; first done. *)
    rewrite/= /expand_wire.  move : (H0 (r,o) true false). rewrite H1 => Hftm.
    move : (H (r,o)). rewrite Hftm. move => [Hs|Hd]. rewrite Hs.
    move : H1 Hftm Hs.
    case Ht : t =>[gt|gt n|].
    rewrite /= N.add_0_r. 
    move => H1 Hftm Hs.  rewrite H1 (lock Sem_frag_stmts)/=-lock. 
    rewrite sem_frag_stmt_qcons_qnil/= Hs/=. done.
    move => H1 Hftm Hs. 
    apply : expandconnects_swire_atyp.
    move => H1 Hftm Hs. apply : expandconnects_swire_btyp.
    rewrite Hd.
    move : H1 Hftm Hd.
    case Ht : t =>[gt|gt n|].
    rewrite /= N.add_0_r. 
    move => H1 Hftm Hs.  rewrite H1 (lock Sem_frag_stmts)/=-lock. 
    rewrite sem_frag_stmt_qcons_qnil/= Hs/=. done.
    move => H1 Hftm Hs. 
    apply : expandconnects_swire_atyp.
    move => H1 Hftm Hs. apply : expandconnects_swire_btyp.
  Qed.

  Lemma expandConnects_correct :
    forall s ct0 vm0 ct1 vm1 tmap tfmap tomap ,
      corresponding_tmap tmap ->
      rel_tfmap_tomap tfmap tomap ->
      rel_tmap_tfmap tmap tfmap ->
      (* Sem_frag_stmts vm0 ct0 ss0 vm1 ct1 tomap -> *)
      Sem_frag_stmts vm0 ct0 (expandconnects_stmt_ft_pmap s tmap tfmap HiFP.qnil) vm1 ct1 tomap ->
      Sem_frag_stmt vm0 ct0 s vm1 ct1 tomap
    with  expandConnects_seq_correct :
      forall ss ct0 vm0 ct1 vm1 tmap tfmap tomap ,
      rel_tfmap_tomap tfmap tomap ->
      rel_tmap_tfmap tmap tfmap ->
      (* Sem_frag_stmts vm0 ct0 ss0 vm1 ct1 tomap -> *)
      Sem_frag_stmts vm0 ct0 (expandconnects_stmt_seq_ft_pmap ss tmap tfmap HiFP.qnil) vm1 ct1 tomap ->
      Sem_frag_stmts vm0 ct0 ss vm1 ct1 tomap.
  Proof.
    elim.
    - intros. move : (ExpandConnects_skip_correct vm0 ct0 vm1 ct1 tmap tfmap tomap HiFP.qnil H2).
      rewrite sem_frag_stmt_qcons_qnil//.
    - intros. move : H2.
      case s => [r o].
      apply (expandConnects_swire_correct ct0 vm0 ct1 vm1 tmap tfmap tomap r o f); try done.
    - intros. move : H2.
      case s => [r o].
      apply (expandConnects_sreg_correct (r, o) h ct0 vm0 ct1 vm1 tmap tfmap tomap); try done.
    - intros. move : (expandConnects_smem_correct s h ct0 vm0 ct1 vm1 tmap tfmap tomap HiFP.qnil H2).
      rewrite sem_frag_stmt_qcons_qnil//.
    - intros. move : (expandConnects_sinst_correct s s0 ct0 vm0 ct1 vm1 tmap tfmap tomap HiFP.qnil H2).
      rewrite sem_frag_stmt_qcons_qnil//.
    - intros. move : H2.
      case s => [r o].
      apply (expandConnects_snode_correct (r, o) h ct0 vm0 ct1 vm1 tmap tfmap tomap); try done.
    - intros. move : H2. case h. intros. move : H2. case s. intros.
      apply (expandConnects_sfcnct_correct (s0, s1) h0 ct0 vm0 ct1 vm1 tmap tfmap tomap); try done.
      + admit. + admit. admit.
    - elim. intros.
      apply (expandConnects_sinvalid_correct s ct0 vm0 ct1 vm1 tmap tfmap tomap); try done.
      + admit. + admit. +admit.
    - admit.

      elim.
      intros. move : H1. rewrite /=//. 
      intros. move : H2. rewrite /=.
      rewrite expandconnects_stmt_cat.
  Admitted.
      
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
