(* This file describes a formal FIRRTL semantics.
   The basic idea is to define a function that assigns a formal expression to every component;
   this is what the component is connected from.
   Then, we iterate through evaluating this expression for every component simultaneously
   until the evaluations stabilize; that gives the combinatorial semantics of the calculations in the module.

   For a temporal semantics, we would then have to define something like a state-transition system,
   where upon every clock tick the registers are set to their new value, and then the combinatorial evaluation restarts.
   But this temporal semantics is not (yet) part of this file.

   The Coq code is based on ideas of and written mostly in August 2025 by David N. Jansen.
   The original idea to iterate the calculation is from Yicheng Liu.
   Also Keyin Wang and Xiaomu Shi have contributed to the discussion. *)

From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat ssralg ssrint eqtype seq div.

(* abstract syntax of HiFIRRTL *)

(******************************)
(*         identifiers        *)
(******************************)

Variable var : eqType.

(******************************)
(*         data types         *)
(******************************)

(* ground data types of FIRRTL. We assume that all widths have been inferred already. *)
Inductive fgtyp : Type :=
  | Fuint : nat -> fgtyp
  | Fsint : nat -> fgtyp
  | Fclock
  | Freset (* HiFIRRTL only *)
  | Fasyncreset.

(* Equality of ground data types is decidable *)
Lemma fgtyp_eq_dec (x y : fgtyp) : {x = y} + {x <> y}.
  Proof. decide equality ; decide equality. Qed.

(* Boolean equality of ground data types *)
Definition fgtyp_eqn (x y : fgtyp) : bool :=
  match x, y with
  | Fuint wx, Fuint wy | Fsint wx, Fsint wy => wx == wy
  | Fclock, Fclock | Freset, Freset | Fasyncreset, Fasyncreset => true
  | _, _ => false
  end.

(* reflection predicate for ground data types *)
Lemma fgtyp_eqP : forall (x y : fgtyp), reflect (x = y) (fgtyp_eqn x y).
  Proof.
    destruct x, y ; simpl fgtyp_eqn ;
          try (apply ReflectF ; discriminate) ;
          try (apply ReflectT ; reflexivity).
    all: destruct (n == n0) eqn: H ; move /eqP : H => H ;
          try (rewrite H ; apply ReflectT ; reflexivity) ;
          apply ReflectF ; injection ; apply H.
  Qed.

(* eqType for ground data types *)
Definition fgtyp_eqMixin := EqMixin fgtyp_eqP.
Canonical fgtyp_eqType := Eval hnf in EqType fgtyp fgtyp_eqMixin.

(* unify two ground data types, e.g. to find the result type of a multiplexer *)
Definition unified_fgtyp (t1 t2 : fgtyp) : option fgtyp :=
  match t1, t2 with
  | Fuint n1, Fuint n2 => Some (Fuint (max n1 n2))
  | Fsint n1, Fsint n2 => Some (Fsint (max n1 n2))
  | Fclock, Fclock => Some Fclock
  | Freset, Freset => Some Freset
  | Fasyncreset, Fasyncreset => Some Fasyncreset
  | _, _ => None
  end.

(* flipped direction for subfields *)
Inductive fflip : Type := Flipped | Nflip.

(* flipped direction type equality is decidable *)
Lemma fflip_eq_dec (x y : fflip) : {x = y} + {x <> y}.
  Proof. decide equality. Qed.

(* Boolean equality of flipped direction type *)
Definition fflip_eqn (x y : fflip) : bool :=
  match x, y with
  | Flipped, Flipped | Nflip, Nflip => true
  | _, _ => false
  end.

(* reflection predicate for flipped direction type *)
Lemma fflip_eqP : forall (x y : fflip), reflect (x = y) (fflip_eqn x y).
  Proof.
    destruct x, y ; simpl fflip_eqn ;
          try (apply ReflectF ; discriminate) ;
          try (apply ReflectT ; reflexivity).
  Qed.

(* eqType for flipped direction type *)
Definition fflip_eqMixin := EqMixin fflip_eqP.
Canonical fflip_eqType := Eval hnf in EqType fflip fflip_eqMixin.

(* general data types, including aggregate types, for HiFIRRTL *)
Inductive ftype : Type :=
  | Gtyp : fgtyp -> ftype
  | Atyp : ftype -> nat -> ftype
  | Btyp : ffield -> ftype
with ffield : Type :=
  | Fnil : ffield
  | Fflips : var -> fflip -> ftype -> ffield -> ffield
.

(* general data type equality is decidable *)
Lemma ftype_eq_dec (x y : ftype) : {x = y} + {x <> y}
with ffield_eq_dec (x y : ffield) : {x = y} + {x <> y}.
  Proof. decide equality ; decide equality ; decide equality.
  decide equality ; first decide equality.
  apply eq_comparable.
Qed.

(* Boolean equality for general data types *)
Fixpoint ftype_eqn (x y : ftype) : bool :=
  match x, y with
  | Gtyp ft1, Gtyp ft2 => ft1 == ft2
  | Atyp t1 n1, Atyp t2 n2 => (ftype_eqn t1 t2) && (n1 == n2)
  | Btyp ff1, Btyp ff2 => ffield_eqn ff1 ff2
  | _, _ => false
  end
with ffield_eqn (x y : ffield) : bool :=
  match x, y with
  | Fnil, Fnil => true
  | Fflips v1 fl1 t1 ff1, Fflips v2 fl2 t2 ff2 => (v1 == v2) && (fl1 == fl2) && (ftype_eqn t1 t2) && (ffield_eqn ff1 ff2)
  | _, _ => false
  end.

(* reflection predicate for general data types *)
Lemma ftype_eqP : forall (x y : ftype), reflect (x = y) (ftype_eqn x y)
with ffield_eqP : forall (x y : ffield), reflect (x = y) (ffield_eqn x y).
  Proof.
    destruct x, y ; simpl ftype_eqn ;
          try (apply ReflectF ; discriminate).
    - destruct (f == f0) eqn: H ; move /eqP : H => H ;
            try (rewrite H ; apply ReflectT ; reflexivity) ;
            apply ReflectF ; injection ; apply H.
    - destruct (n == n0) eqn: H ; move /eqP : H => H.
      - rewrite H andbT.
        specialize (ftype_eqP x y) ; destruct (ftype_eqn x y) ; apply Bool.reflect_iff in ftype_eqP.
        - apply ReflectT.
          rewrite (proj2 ftype_eqP) //.
        - apply ReflectF ; injection.
          intro H1 ; apply ftype_eqP in H1.
          contradict H1 ; discriminate.
      - rewrite andbF ; apply ReflectF ; injection.
        intro H1 ; contradict H1 ; exact H.
    - specialize (ffield_eqP f f0) ; destruct (ffield_eqn f f0) ; apply Bool.reflect_iff in ffield_eqP.
      - apply ReflectT ; rewrite (proj2 ffield_eqP) //.
      - apply ReflectF ; injection.
        intro H1 ; apply ffield_eqP in H1.
        contradict H1 ; discriminate.
    destruct x, y ; simpl ffield_eqn ;
          try (apply ReflectF ; discriminate).
    - apply ReflectT ; reflexivity.
      specialize (ffield_eqP x y) ; destruct (ffield_eqn x y) ; apply Bool.reflect_iff in ffield_eqP ;
            last by (rewrite andbF ; apply ReflectF ; injection ;
                     intro H1 ; apply ffield_eqP in H1 ; contradict H1 ; discriminate).
      rewrite (proj2 ffield_eqP) // andbT.
      specialize (ftype_eqP f0 f2) ; destruct (ftype_eqn f0 f2) ; apply Bool.reflect_iff in ftype_eqP ;
            last by (rewrite andbF ; apply ReflectF ; injection ;
                     intro H1 ; apply ftype_eqP in H1 ; contradict H1 ; discriminate).
      rewrite (proj2 ftype_eqP) // andbT.
      destruct (f == f1) eqn: Hf ; move /eqP : Hf => Hf ;
            last by (rewrite andbF ; apply ReflectF ; injection ;
                     intro H1 ; contradict H1 ; exact Hf).
      rewrite Hf andbT.
      destruct (s == s0) eqn: Hs ; move /eqP : Hs => Hs ;
            last by (apply ReflectF ; injection ;
                     intro H1 ; contradict H1 ; exact Hs).
      apply ReflectT ; rewrite Hs ; reflexivity.
  Qed.

(* eqType for general data types *)
Definition ftype_eqMixin := EqMixin ftype_eqP.
Definition ffield_eqMixin := EqMixin ffield_eqP.
Canonical ftype_eqType := Eval hnf in EqType ftype ftype_eqMixin.
Canonical ffield_eqType := Eval hnf in EqType ffield ffield_eqMixin.

(* unify two general data types, e.g. to find the output type of a multiplexer *)
Fixpoint unified_type (t1 t2 : ftype) : option ftype :=
  match t1, t2 with
  | Gtyp ft1, Gtyp ft2 => match unified_fgtyp ft1 ft2 with
                          | Some ft => Some (Gtyp ft)
                          | _ => None
                          end
  | Atyp t1 n1, Atyp t2 n2 => if n1 == n2
                              then match unified_type t1 t2 with
                                   | Some t => Some (Atyp t n1)
                                   | _ => None
                                   end
                              else None
  | Btyp ff1, Btyp ff2 => match unified_ffield ff1 ff2 with
                          | Some ff => Some (Btyp ff)
                          | _ => None
                          end
  | _, _ => None
  end
with unified_ffield (ff1 ff2 : ffield) : option ffield :=
  match ff1, ff2 with
  | Fnil, Fnil => Some (Fnil)
  | Fflips v1 fl1 t1 ff1', Fflips v2 fl2 t2 ff2' => if (v1 == v2) && (fl1 == fl2)
                                                    then match unified_type t1 t2, unified_ffield ff1' ff2' with
                                                         | Some t, Some f => Some (Fflips v1 fl1 t f)
                                                         | _, _ => None
                                                         end
                                                    else None
  | _, _ => None
  end.

(* check whether a general data type is passive, i.e. whether it does not contain any flipped fields *)
Fixpoint is_passive (t : ftype) : bool :=
  match t with
  | Gtyp _ => true
  | Atyp t' _ => is_passive t'
  | Btyp ff => is_passive_fields ff
  end
with is_passive_fields (ff : ffield) : bool :=
  match ff with
  | Fnil => true
  | Fflips _ Nflip t ff' => is_passive t && is_passive_fields ff'
  | Fflips _ Flipped _ _ => false
  end.

(******************************)
(* expressions and references *)
(******************************)

(* cast-to type (for the type cast expression) *)
Inductive ucast : Type :=
  | AsUInt | AsSInt | AsClock | AsAsync.

(* Equality of ucast is decidable *)
Lemma ucast_eq_dec (x y : ucast) : {x = y} + {x <> y}.
  Proof. decide equality. Qed.

(* Boolean equality of ucast *)
Definition ucast_eqn (x y : ucast) : bool :=
  match x, y with
  | AsUInt, AsUInt | AsSInt, AsSInt | AsClock, AsClock | AsAsync, AsAsync => true
  | _, _ => false
  end.

(* reflection predicate for ucast *)
Lemma ucast_eqP : forall (x y : ucast), reflect (x = y) (ucast_eqn x y).
  Proof.
    destruct x, y ; simpl ucast_eqn ;
          try (apply ReflectF ; discriminate) ;
          apply ReflectT ; reflexivity.
  Qed.

(* eqType for ucast *)
Definition ucast_eqMixin := EqMixin ucast_eqP.
Canonical ucast_eqType := Eval hnf in EqType ucast ucast_eqMixin.


(* unary operators *)
Inductive eunop : Type :=
  | Upad : nat -> eunop
  | Ushl : nat -> eunop
  | Ushr : nat -> eunop
  | Ucvt
  | Uneg
  | Unot
  | Uandr
  | Uorr
  | Uxorr
  | Uextr : nat -> nat -> eunop
  | Uhead : nat -> eunop
  | Utail : nat -> eunop.

(* Equality of unary operators is decidable *)
Lemma eunop_eq_dec (x y : eunop) : {x = y} + {x <> y}.
  Proof. decide equality ; decide equality. Qed.

(* Boolean equality of unary operators *)
Definition eunop_eqn (x y : eunop) : bool :=
  match x, y with
  | Uextr n1x n2x, Uextr n1y n2y => (n1x==n1y) && (n2x==n2y)
  | Upad nx, Upad ny | Ushl nx, Ushl ny | Ushr nx, Ushr ny | Uhead nx, Uhead ny | Utail nx, Utail ny => nx==ny
  | Ucvt, Ucvt | Uneg, Uneg | Unot, Unot | Uandr, Uandr | Uorr, Uorr | Uxorr, Uxorr => true
  | _, _ => false
  end.

(* reflection predicate for unary operators *)
Lemma eunop_eqP : forall (x y : eunop), reflect (x = y) (eunop_eqn x y).
  Proof.
    destruct x, y ; simpl eunop_eqn ;
          try (apply ReflectF ; discriminate) ;
          try (apply ReflectT ; reflexivity).
    4: destruct (n == n1) eqn: H ; move /eqP : H => H ;
          last (by rewrite andFb ; apply ReflectF ; injection ;
                   intro ; apply H) ;
       rewrite H andTb ; destruct (n0 == n2) eqn: H0 ; move /eqP : H0 => H0 ;
          last (by apply ReflectF ; injection ; apply H0) ;
          first (by apply ReflectT ; rewrite H0 //).
    all: destruct (n == n0) eqn: H ; move /eqP : H => H ;
          try (rewrite H ; apply ReflectT ; reflexivity) ;
          apply ReflectF ; injection ; apply H.
  Qed.

(* eqType for unary operators *)
Definition eunop_eqMixin := EqMixin eunop_eqP.
Canonical eunop_eqType := Eval hnf in EqType eunop eunop_eqMixin.


(* comparison operators *)
Inductive bcmp : Type :=
  | Blt | Bleq | Bgt | Bgeq | Beq | Bneq.

(* Equality of comparison operators is decidable *)
Lemma bcmp_eq_dec (x y : bcmp) : {x = y} + {x <> y}.
  Proof. decide equality. Qed.

(* Boolean equality of comparison operators *)
Definition bcmp_eqn (x y : bcmp) : bool :=
  match x, y with
  | Blt, Blt | Bleq, Bleq | Bgt, Bgt | Bgeq, Bgeq | Beq, Beq | Bneq, Bneq => true
  | _, _ => false
  end.

(* reflection predicate for comparison operators *)
Lemma bcmp_eqP : forall (x y : bcmp), reflect (x = y) (bcmp_eqn x y).
  Proof.
    destruct x, y ; simpl bcmp_eqn ;
          try (apply ReflectF ; discriminate) ;
          apply ReflectT ; reflexivity.
  Qed.

(* eqType for comparison operators *)
Definition bcmp_eqMixin := EqMixin bcmp_eqP.
Canonical bcmp_eqType := Eval hnf in EqType bcmp bcmp_eqMixin.


(* binary operators *)
Inductive ebinop : Type :=
  | Badd
  | Bsub
  | Bmul
  | Bdiv
  | Brem
  | Bcomp: bcmp -> ebinop
  | Bdshl
  | Bdshr
  | Band
  | Bor
  | Bxor
  | Bcat .

(* Equality of binary operators is decidable *)
Lemma ebinop_eq_dec (x y : ebinop) : {x = y} + {x <> y}.
  Proof. decide equality ; decide equality. Qed.

(* Boolean equality of binary operators *)
Definition ebinop_eqn (x y : ebinop) : bool :=
  match x, y with
  | Bcomp cx, Bcomp cy => cx==cy
  | Badd, Badd | Bsub, Bsub | Bmul, Bmul | Bdiv, Bdiv | Brem, Brem
  | Bdshl, Bdshl | Bdshr, Bdshr | Band, Band | Bor, Bor | Bxor, Bxor | Bcat, Bcat => true
  | _, _ => false
  end.

(* reflection predicate for binary operators *)
Lemma ebinop_eqP : forall (x y : ebinop), reflect (x = y) (ebinop_eqn x y).
  Proof.
    destruct x, y ; simpl ebinop_eqn ;
          try (apply ReflectF ; discriminate) ;
          try (apply ReflectT ; reflexivity).
    destruct (b == b0) eqn: H ; move /eqP : H => H ;
          try (rewrite H ; apply ReflectT ; reflexivity) ;
          apply ReflectF ; injection ; apply H.
  Qed.

(* eqType for binary operators *)
Definition ebinop_eqMixin := EqMixin ebinop_eqP.
Canonical ebinop_eqType := Eval hnf in EqType ebinop ebinop_eqMixin.


(* general expression type.
     This can be a ground expression or an aggregate expression.
     It is difficult to distinguish between the two;
     if really needed, one would have to introduce a dependent pair
     (hfexpr, proof that the expression is ground),
     which often leads to additional proof difficulties.

   We use array and bundle expressions so one can assign a single expression to an aggregate-type component.
   The "Earray" and "Ebundle" operators are not part of FIRRTL syntax but this is the simplest way to include these expressions. *)
Inductive hfexpr : Type := 
  | Econst : fgtyp -> int -> hfexpr
  | Ecast : ucast -> hfexpr -> hfexpr
  | Eprim_unop : eunop -> hfexpr -> hfexpr
  | Eprim_binop : ebinop -> hfexpr -> hfexpr -> hfexpr
  | Emux : hfexpr -> hfexpr -> hfexpr -> hfexpr
  (*| Evalidif : hfexpr -> hfexpr -> hfexpr*)
  | Eref : href -> hfexpr
  | Earray : array_expr -> hfexpr
  | Ebundle : bundle_expr -> hfexpr
  | Etobedefined : ftype -> hfexpr
  | Eundefinedonpurpose : ftype -> hfexpr (* also used for empty expressions of flipped fields *)
with array_expr : Type :=
  | Aone : hfexpr -> array_expr
  | Acons : hfexpr -> array_expr -> array_expr
with bundle_expr : Type :=
  | Bnil
  | Bflips : var -> fflip -> hfexpr -> bundle_expr -> bundle_expr
with href : Type :=
  | Eid : var -> href
  | Esubfield : href -> var -> href (* HiFirrtl *)
  | Esubindex : href -> nat -> href (* HiFirrtl *)
  | Esubaccess : href -> hfexpr -> href (* HiFirrtl *)
.

(* Equality of expressions is decidable *)
Lemma hfexpr_eq_dec (x y : hfexpr) : {x = y} + {x <> y}
with array_expr_eq_dec (x y : array_expr) : {x = y} + {x <> y}
with bundle_expr_eq_dec (x y : bundle_expr) : {x = y} + {x <> y}
with href_eq_dec (x y : href) : {x = y} + {x <> y}.
Proof.
(* href_expr *)
decide equality ;
      try (by apply fgtyp_eq_dec) ;
      try (by apply ucast_eq_dec) ;
      try (by apply eunop_eq_dec) ;
      try (by apply ebinop_eq_dec) ;
      try (by apply ftype_eq_dec) ;
      by (decide equality ; decide equality).
(* array_expr *)
decide equality.
(* bundle_expr *)
decide equality ;
      try (by apply fflip_eq_dec) ;
      by apply eq_comparable.
(* href *)
decide equality ;
      by apply eq_comparable.
Qed.

(* Boolean equality of expressions *)
Fixpoint hfexpr_eqn (x y : hfexpr) : bool :=
  match x, y with
  | Econst tx ix, Econst ty iy => (tx==ty) && (ix==iy)
  | Ecast ux ex, Ecast uy ey => (ux==uy) && (hfexpr_eqn ex ey)
  | Eprim_unop ox ex, Eprim_unop oy ey => (ox==oy) && (hfexpr_eqn ex ey)
  | Eprim_binop ox e1x e2x, Eprim_binop oy e1y e2y => (ox==oy) && (hfexpr_eqn e1x e1y) && (hfexpr_eqn e2x e2y)
  | Emux cx e1x e2x, Emux cy e1y e2y => (hfexpr_eqn cx cy) && (hfexpr_eqn e1x e1y) && (hfexpr_eqn e2x e2y)
  | Eref rx, Eref ry => href_eqn rx ry
  | Earray ax, Earray ay => array_expr_eqn ax ay
  | Ebundle bux, Ebundle buy => bundle_expr_eqn bux buy
  | Etobedefined tx, Etobedefined ty
  | Eundefinedonpurpose tx, Eundefinedonpurpose ty => tx==ty
  | _, _ => false
  end
with array_expr_eqn (x y : array_expr) : bool :=
  match x, y with
  | Aone ex, Aone ey => hfexpr_eqn ex ey
  | Acons ex ax, Acons ey ay => (hfexpr_eqn ex ey) && (array_expr_eqn ax ay)
  | _, _ => false
  end
with bundle_expr_eqn (x y : bundle_expr) : bool :=
  match x, y with
  | Bnil, Bnil => true
  | Bflips vx fx ex bux, Bflips vy fy ey buy => (vx==vy) && (fx==fy) && (hfexpr_eqn ex ey) && (bundle_expr_eqn bux buy)
  | _, _ => false
  end
with href_eqn (x y : href) : bool :=
  match x, y with
  | Eid vx, Eid vy => vx==vy
  | Esubfield rx vx, Esubfield ry vy => (href_eqn rx ry) && (vx==vy)
  | Esubindex rx nx, Esubindex ry ny => (href_eqn rx ry) && (nx==ny)
  | Esubaccess rx ix, Esubaccess ry iy => (href_eqn rx ry) && (hfexpr_eqn ix iy)
  | _, _ => false
  end.

(* reflection predicate for expressions *)
Lemma hfexpr_eqP : forall (x y : hfexpr), reflect (x = y) (hfexpr_eqn x y)
with array_expr_eqP : forall (x y : array_expr), reflect (x = y) (array_expr_eqn x y)
with bundle_expr_eqP : forall (x y : bundle_expr), reflect (x = y) (bundle_expr_eqn x y)
with href_eqP : forall (x y : href), reflect (x = y) (href_eqn x y).
Proof.
(* hfexpr *)
destruct x, y ; simpl hfexpr_eqn ;
       try (apply ReflectF ; discriminate).
* destruct (i==i0) eqn : Hi ; move /eqP : Hi => Hi ;
      last (by rewrite andbF ; apply ReflectF ; injection ;
               intro H0 ; contradict Hi ; exact H0).
  rewrite andbT Hi.
  1,9,10: destruct (f==f0) eqn : Hf ; move /eqP : Hf => Hf ;
      first (by rewrite Hf ; apply ReflectT ; reflexivity) ;
      last (by apply ReflectF ; injection ; apply Hf).
* destruct (u==u0) eqn : Hu ; move /eqP : Hu => Hu ;
      last (by rewrite andFb ; apply ReflectF ; injection ; intro ; apply Hu) ;
      first (rewrite andTb Hu).
* 2: destruct (e==e0) eqn : Ho ; move /eqP : Ho => Ho ;
        last (by rewrite andFb ; apply ReflectF ; injection ; intro ; apply Ho) ;
        first (rewrite andTb Ho).
  1,2: specialize (hfexpr_eqP x y) ; apply Bool.reflect_iff in hfexpr_eqP ;
       destruct (hfexpr_eqn x y) eqn : He ;
             first (by rewrite (proj2 hfexpr_eqP Logic.eq_refl) ; apply ReflectT ; reflexivity) ;
             last (by apply ReflectF ; injection ;
                      intro H0 ; apply hfexpr_eqP in H0 ;
                      contradict H0 ; discriminate).
* destruct (e==e0) eqn : Ho ; move /eqP : Ho => Ho ;
        last (by rewrite andFb ; apply ReflectF ; injection ; intros _ _ ; apply Ho) ;
        first (rewrite andTb Ho).
  generalize (hfexpr_eqP x1 y1) ; intro hfexpr_eqP1 ; apply Bool.reflect_iff in hfexpr_eqP1 ;
  destruct (hfexpr_eqn x1 y1) eqn: H1 ;
        last (by rewrite andFb ; apply ReflectF ; injection ;
                 intros _ H0 ; apply hfexpr_eqP1 in H0 ;
                 contradict H0 ; discriminate).
  rewrite andTb (proj2 hfexpr_eqP1 Logic.eq_refl).
  specialize (hfexpr_eqP x2 y2) ; apply Bool.reflect_iff in hfexpr_eqP ;
  destruct (hfexpr_eqn x2 y2) eqn : H2 ;
             first (by rewrite (proj2 hfexpr_eqP Logic.eq_refl) ; apply ReflectT ; reflexivity) ;
             last (by apply ReflectF ; injection ;
                      intro H0 ; apply hfexpr_eqP in H0 ;
                      contradict H0 ; discriminate).
* generalize (hfexpr_eqP x1 y1) ; intro hfexpr_eqP1 ; apply Bool.reflect_iff in hfexpr_eqP1 ;
  destruct (hfexpr_eqn x1 y1) ;
        last (by rewrite andFb ; apply ReflectF ; injection ;
                 intros _ _ H0 ; apply hfexpr_eqP1 in H0 ;
                 contradict H0 ; discriminate).
  rewrite andTb (proj2 hfexpr_eqP1 Logic.eq_refl).
  generalize (hfexpr_eqP x2 y2) ; intro hfexpr_eqP2 ; apply Bool.reflect_iff in hfexpr_eqP2 ;
  destruct (hfexpr_eqn x2 y2) ;
        last (by rewrite andFb ; apply ReflectF ; injection ;
                 intros _ H0 ; apply hfexpr_eqP2 in H0 ;
                 contradict H0 ; discriminate).
  rewrite andTb (proj2 hfexpr_eqP2 Logic.eq_refl).
  specialize (hfexpr_eqP x3 y3) ; apply Bool.reflect_iff in hfexpr_eqP ;
  destruct (hfexpr_eqn x3 y3) ;
        last (by apply ReflectF ; injection ;
                 intro H0 ; apply hfexpr_eqP in H0 ;
                 contradict H0 ; discriminate).
  rewrite (proj2 hfexpr_eqP Logic.eq_refl).
  apply ReflectT ; reflexivity.
* specialize (href_eqP h h0) ; apply Bool.reflect_iff in href_eqP ;
  destruct (href_eqn h h0) ;
        last (by apply ReflectF ; injection ;
                 intro H0 ; apply href_eqP in H0 ;
                 contradict H0 ; discriminate).
  rewrite (proj2 href_eqP Logic.eq_refl).
  apply ReflectT ; reflexivity.
* specialize (array_expr_eqP a a0) ; apply Bool.reflect_iff in array_expr_eqP ;
  destruct (array_expr_eqn a a0) ;
        last (by apply ReflectF ; injection ;
                 intro H0 ; apply array_expr_eqP in H0 ;
                 contradict H0 ; discriminate).
  rewrite (proj2 array_expr_eqP Logic.eq_refl).
  apply ReflectT ; reflexivity.
* specialize (bundle_expr_eqP b b0) ; apply Bool.reflect_iff in bundle_expr_eqP ;
  destruct (bundle_expr_eqn b b0) ;
        last (by apply ReflectF ; injection ;
                 intro H0 ; apply bundle_expr_eqP in H0 ;
                 contradict H0 ; discriminate).
  rewrite (proj2 bundle_expr_eqP Logic.eq_refl).
  apply ReflectT ; reflexivity.
(* array_expr *)
destruct x, y ; simpl array_expr_eqn ;
      try (apply ReflectF ; discriminate).
* specialize (hfexpr_eqP h h0) ; apply Bool.reflect_iff in hfexpr_eqP ;
  destruct (hfexpr_eqn h h0) ;
        last (by apply ReflectF ; injection ;
                 intro H0 ; apply hfexpr_eqP in H0 ;
                 contradict H0 ; discriminate).
  rewrite (proj2 hfexpr_eqP Logic.eq_refl).
  apply ReflectT ; reflexivity.
* specialize (hfexpr_eqP h h0) ; apply Bool.reflect_iff in hfexpr_eqP ;
  destruct (hfexpr_eqn h h0) ;
        last (by rewrite andFb ; apply ReflectF ; injection ;
                 intros _ H0 ; apply hfexpr_eqP in H0 ;
                 contradict H0 ; discriminate).
  rewrite andTb (proj2 hfexpr_eqP Logic.eq_refl).
  specialize (array_expr_eqP x y) ; apply Bool.reflect_iff in array_expr_eqP ;
  destruct (array_expr_eqn x y) ;
        last (by apply ReflectF ; injection ;
                 intro H0 ; apply array_expr_eqP in H0 ;
                 contradict H0 ; discriminate).
  rewrite (proj2 array_expr_eqP Logic.eq_refl) ; apply ReflectT ; reflexivity.
(* bundle expression *)
destruct x, y ; simpl bundle_expr_eqn ;
      try (apply ReflectF ; discriminate).
* apply ReflectT ; reflexivity.
* destruct (s==s0) eqn: Hs ; move /eqP : Hs => Hs ;
        last (by rewrite andFb ; apply ReflectF ; injection ;
                 intros _ _ _ ; apply Hs).
  rewrite andTb Hs.
  destruct (f==f0) eqn: Hf ; move /eqP : Hf => Hf ;
        last (by rewrite andFb ; apply ReflectF ; injection ;
                 intros _ _ ; apply Hf).
  rewrite andTb Hf.
  specialize (hfexpr_eqP h h0) ; apply Bool.reflect_iff in hfexpr_eqP ;
  destruct (hfexpr_eqn h h0) ;
        last (by rewrite andFb ; apply ReflectF ; injection ;
                 intros _ H0 ; apply hfexpr_eqP in H0 ;
                 contradict H0 ; discriminate).
  rewrite andTb (proj2 hfexpr_eqP Logic.eq_refl).
  specialize (bundle_expr_eqP x y) ; apply Bool.reflect_iff in bundle_expr_eqP ;
  destruct (bundle_expr_eqn x y) ;
        last (by apply ReflectF ; injection ;
                 intro H0 ; apply bundle_expr_eqP in H0 ;
                 contradict H0 ; discriminate).
  rewrite (proj2 bundle_expr_eqP Logic.eq_refl).
  apply ReflectT ; reflexivity.
(* href *)
destruct x, y ; simpl href_eqn ;
      try (apply ReflectF ; discriminate).
* destruct (s==s0) eqn: Hs ; move /eqP : Hs => Hs ;
        last (by apply ReflectF ; injection ; apply Hs).
  rewrite Hs ; apply ReflectT ; reflexivity.
1-3:specialize (href_eqP x y) ; apply Bool.reflect_iff in href_eqP ;
    destruct (href_eqn x y) ;
            last (by rewrite andFb ; apply ReflectF ; injection ;
                     intros _ H0 ; apply href_eqP in H0 ;
                     contradict H0 ; discriminate) ;
            first rewrite andTb (proj2 href_eqP Logic.eq_refl).
* destruct (s==s0) eqn: Hs ; move /eqP : Hs => Hs ;
        last (by apply ReflectF ; injection ; apply Hs).
  rewrite Hs ; apply ReflectT ; reflexivity.
* destruct (n==n0) eqn: Hn ; move /eqP : Hn => Hn ;
        last (by apply ReflectF ; injection ; apply Hn).
  rewrite Hn ; apply ReflectT ; reflexivity.
* specialize (hfexpr_eqP h h0) ; apply Bool.reflect_iff in hfexpr_eqP ;
  destruct (hfexpr_eqn h h0) ;
        last (by apply ReflectF ; injection ;
                 intro H0 ; apply hfexpr_eqP in H0 ;
                 contradict H0 ; discriminate).
  rewrite (proj2 hfexpr_eqP Logic.eq_refl).
  apply ReflectT ; reflexivity.
Qed.

(* eqType for expressions *)
Definition hfexpr_eqMixin := EqMixin hfexpr_eqP.
Canonical hfexpr_eqType := Eval hnf in EqType hfexpr hfexpr_eqMixin.

Definition array_expr_eqMixin := EqMixin array_expr_eqP.
Canonical array_expr_eqType := Eval hnf in EqType array_expr array_expr_eqMixin.

Definition bundle_expr_eqMixin := EqMixin bundle_expr_eqP.
Canonical bundle_expr_eqType := Eval hnf in EqType bundle_expr bundle_expr_eqMixin.

Definition href_eqMixin := EqMixin href_eqP.
Canonical href_eqType := Eval hnf in EqType href href_eqMixin.

(* orientation of a component (how can it be accessed? read and/or write? *)
Inductive forient : Type :=
  | Source | Sink | Duplex | Passive | Illegal_orient.

(* flips the orientation *)
Definition flip_orient (o : forient) : forient :=
  match o with
  | Source => Sink
  | Sink => Source
  | Duplex => Duplex
  | Passive | Illegal_orient => Illegal_orient
  end.

(* check whether an orientation is readable *)
Definition readable_orient (o : forient) : bool :=
  match o with
  | Source | Duplex | Passive => true
  | _ => false
  end.

(* check whether an orientation is writable *)
Definition writable_orient (o : forient) : bool :=
  match o with
  | Sink | Duplex => true
  | _ => false
  end.

(* find the type of subfield with name v in bundle type ff *)
Fixpoint type_of_subfield (ff : ffield) (v : var) : option (fflip * ftype) :=
  match ff with
  | Fnil => None
  | Fflips v' fl ft ff' => if v==v' then Some (fl, ft) else type_of_subfield ff' v
  end.

Inductive kind := Inport | Outport | Wire | Register | Node.

(* equality of kind is decidable *)
Lemma kind_eq_dec (x y : kind) : {x = y} + {x <> y}.
  Proof. decide equality. Qed.

(* Boolean equality of kind *)
Definition kind_eqn (x y : kind) : bool :=
  match x, y with
  | Inport, Inport | Outport, Outport | Wire, Wire | Register, Register | Node, Node => true
  | _, _ => false
  end.

(* reflection predicate for kind *)
Lemma kind_eqP : forall (x y : kind), reflect (x = y) (kind_eqn x y).
  Proof.
    destruct x, y ; simpl kind_eqn ;
          try (apply ReflectF ; discriminate) ;
          apply ReflectT ; reflexivity.
  Qed.

(* eqType for kind *)
Definition kind_eqMixin := EqMixin kind_eqP.
Canonical kind_eqType := Eval hnf in EqType kind kind_eqMixin.

(**********************)
(* connection summary *)
(**********************)

(* A connection summary is a map that indicates for every component some information.
   It is used to define the context of an expression and later to give the semantics
   of a module. *)

Definition summaryType : Type := var -> option (kind * ftype * hfexpr * hfexpr).
(* kind of the component, datatype of the component,
   then an expression for the unflipped parts of the component (parts of this expression that correspond to flipped parts of the component are ignored),
   then an expression for every flipped subfield that can be written *)

Definition empty_summary : summaryType := (fun _ => None).

(* find the type of expression e, when it is accessed as o [e.g. as source].
   The types of defined identifiers are indicated by dict. *)
Fixpoint type_of_hfexpr (o : forient) (e : hfexpr) (dict : summaryType) : option ftype :=
  match e with
  | Econst t _ => if readable_orient o then Some (Gtyp t) else None
  | Ecast u e' => if readable_orient o
                  then match u, type_of_hfexpr Passive e' dict with
                       | AsUInt, Some (Gtyp (Fsint w))
                       | AsUInt, Some (Gtyp (Fuint w)) => Some (Gtyp (Fuint w))
                       | AsUInt, Some (Gtyp _) => Some (Gtyp (Fuint 1))
                       | AsSInt, Some (Gtyp (Fsint w))
                       | AsSInt, Some (Gtyp (Fuint w)) => Some (Gtyp (Fsint w))
                       | AsSInt, Some (Gtyp _) => Some (Gtyp (Fsint 1))
                       | AsClock, Some (Gtyp _) => Some (Gtyp Fclock)
                       | AsAsync, Some (Gtyp _) => Some (Gtyp Fasyncreset)
                       | _, _ => None
                       end
                  else None
  | Eprim_unop op e' => if readable_orient o
                        then match op, type_of_hfexpr Passive e' dict with
                             | Upad n, Some (Gtyp (Fuint w)) => Some (Gtyp (Fuint (max n w)))
                             | Upad n, Some (Gtyp (Fsint w)) => Some (Gtyp (Fsint (max n w)))
                             | Ushl n, Some (Gtyp (Fuint w)) => Some (Gtyp (Fuint (w+n)))
                             | Ushl n, Some (Gtyp (Fsint w)) => Some (Gtyp (Fsint (w+n)))
                             | Ushr n, Some (Gtyp (Fuint w)) => Some (Gtyp (Fuint (w-n)))
                             | Ushr n, Some (Gtyp (Fsint w)) => Some (Gtyp (Fsint (w-n-1+1)))
                             | Ucvt, Some (Gtyp (Fuint w)) => Some (Gtyp (Fsint (w+1)))
                             | Ucvt, Some (Gtyp (Fsint w)) => Some (Gtyp (Fsint w))
                             | Uneg, Some (Gtyp (Fuint w))
                             | Uneg, Some (Gtyp (Fsint w)) => Some (Gtyp (Fsint (w+1)))
                             | Unot, Some (Gtyp (Fuint w))
                             | Unot, Some (Gtyp (Fsint w)) => Some (Gtyp (Fuint w))
                             | Uandr, Some (Gtyp (Fuint _))
                             | Uandr, Some (Gtyp (Fsint _))
                             | Uorr, Some (Gtyp (Fuint _))
                             | Uorr, Some (Gtyp (Fsint _))
                             | Uxorr, Some (Gtyp (Fuint _))
                             | Uxorr, Some (Gtyp (Fsint _)) => Some (Gtyp (Fuint 1))
                             | Uextr hi lo, Some (Gtyp (Fuint w))
                             | Uextr hi lo, Some (Gtyp (Fsint w)) => if (0 <= lo) && (lo <= hi) && (hi < w)
                                                                     then Some (Gtyp (Fuint (hi-lo+1)))
                                                                     else None
                             | Uhead n, Some (Gtyp (Fuint w))
                             | Uhead n, Some (Gtyp (Fsint w)) => if n <= w
                                                                 then Some (Gtyp (Fuint n))
                                                                 else None
                             | Utail n, Some (Gtyp (Fuint w))
                             | Utail n, Some (Gtyp (Fsint w)) => if w >= n
                                                                 then Some (Gtyp (Fuint (w-n)))
                                                                 else None
                             | _, _ => None
                             end
                        else None
  | Eprim_binop op e1 e2 => if readable_orient o
                            then match op, type_of_hfexpr Passive e1 dict, type_of_hfexpr Passive e2 dict with
                                 | Badd, Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint w2)) => Some (Gtyp (Fuint (max w1 w2+1)))
                                 | Badd, Some (Gtyp (Fsint w1)), Some (Gtyp (Fsint w2)) => Some (Gtyp (Fsint (max w1 w2+1)))
                                 | Bsub, Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint w2)) => Some (Gtyp (Fuint (max w1 w2+1)))
                                 | Bsub, Some (Gtyp (Fsint w1)), Some (Gtyp (Fsint w2)) => Some (Gtyp (Fsint (max w1 w2+1)))
                                 | Bmul, Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint w2)) => Some (Gtyp (Fuint (w1+w2)))
                                 | Bmul, Some (Gtyp (Fsint w1)), Some (Gtyp (Fsint w2)) => Some (Gtyp (Fsint (w1+w2)))
                                 | Bdiv, Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint _)) => Some (Gtyp (Fsint w1))
                                 | Bdiv, Some (Gtyp (Fsint w1)), Some (Gtyp (Fsint _)) => Some (Gtyp (Fsint (w1+1)))
                                 | Brem, Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint w2)) => Some (Gtyp (Fuint (min w1 w2)))
                                 | Brem, Some (Gtyp (Fsint w1)), Some (Gtyp (Fsint w2)) => Some (Gtyp (Fsint (min w1 w2)))
                                 | Bcomp _, Some (Gtyp (Fuint _)), Some (Gtyp (Fuint _))
                                 | Bcomp _, Some (Gtyp (Fsint _)), Some (Gtyp (Fsint _)) => Some (Gtyp (Fuint 1))
                                 | Bdshl, Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint w2)) => Some (Gtyp (Fuint (2^w2 + w1 - 1)))
                                 | Bdshl, Some (Gtyp (Fsint w1)), Some (Gtyp (Fuint w2)) => Some (Gtyp (Fsint (2^w2 + w1 - 1)))
                                 | Bdshr, Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint _)) => Some (Gtyp (Fuint w1))
                                 | Bdshr, Some (Gtyp (Fsint w1)), Some (Gtyp (Fuint _)) => Some (Gtyp (Fsint w1))
                                 | Band, Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint w2))
                                 | Band, Some (Gtyp (Fsint w1)), Some (Gtyp (Fsint w2))
                                 | Bor, Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint w2))
                                 | Bor, Some (Gtyp (Fsint w1)), Some (Gtyp (Fsint w2))
                                 | Bxor, Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint w2))
                                 | Bxor, Some (Gtyp (Fsint w1)), Some (Gtyp (Fsint w2)) => Some (Gtyp (Fuint (max w1 w2)))
                                 | Bcat, Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint w2))
                                 | Bcat, Some (Gtyp (Fsint w1)), Some (Gtyp (Fsint w2)) => Some (Gtyp (Fuint (w1+w2)))
                                 | _, _, _ => None
                                 end
                            else None
  | Emux c e1 e2 => if readable_orient o
                    (* multiplexers in FIRRTL must be passive. But we use them also to store expressions of
                       when statements; these connections may not all be passive. *)
                    then match type_of_hfexpr o c dict, type_of_hfexpr o e1 dict, type_of_hfexpr o e2 dict with
                         | Some (Gtyp (Fuint 1)), Some t1, Some t2 => match unified_type t1 t2 with
                                                                      | Some t => Some t
                                                                      | _ => None
                                                                      end
                         | _, _, _ => None
                         end
                    else None
  | Eref r => match type_of_href r dict with
              | Some (ro, t) => match ro, o with
                                | Source, Source | Source, Passive
                                | Sink, Sink
                                | Duplex, Source | Duplex, Sink | Duplex, Duplex | Duplex, Passive
                                | Passive, Passive => Some t
                                | _, _ => None
                                end
              | None => None
              end
  | Earray ar => type_of_array_expr o ar dict
  | Ebundle b => type_of_bundle_expr o b dict
  | Etobedefined t
  | Eundefinedonpurpose t => match o with
                             | Source | Sink | Duplex => Some t
                             | Passive => if is_passive t then Some t else None
                             | Illegal_orient => None
                             end
  end
with type_of_array_expr (o : forient) (ar : array_expr)  (dict : summaryType) : option ftype :=
  match ar with
  | Aone e => match type_of_hfexpr o e dict with
              | Some t => Some (Atyp t 1)
              | _ => None
              end
  | Acons e ar' => match type_of_hfexpr o e dict, type_of_array_expr o ar' dict with
                   | Some te, Some (Atyp ta n) => match unified_type te ta with
                                                  | Some t => Some (Atyp t (n+1))
                                                  | _ => None
                                                  end
                   | _, _ => None
                   end
  end
with type_of_bundle_expr (o : forient) (b : bundle_expr)  (dict : summaryType) : option ftype :=
  match b with
  | Bnil => Some (Btyp Fnil)
  | Bflips v Nflip e b' => match type_of_hfexpr o e dict, type_of_bundle_expr o b' dict with
                           | Some te, Some (Btyp tb) => Some (Btyp (Fflips v Nflip te tb))
                           | _, _ => None
                           end
  | Bflips v Flipped e b' => match type_of_hfexpr (flip_orient o) e dict, type_of_bundle_expr o b' dict with
                             | Some te, Some (Btyp tb) => Some (Btyp (Fflips v Flipped te tb))
                             | _, _ => None
                             end
  end
with type_of_href (r : href) (dict : summaryType) : option (forient * ftype) :=
  match r with
  | Eid v => match dict v with
             | Some (Inport, t, _, _) => Some (Source, t)
             | Some (Outport, t, _, _)
             | Some (Wire, t, _, _) => Some (Duplex, t)
             | Some (Register, t, _, _)
             | Some (Node, t, _, _) => Some (Passive, t)
             | None => None
             end
  | Esubfield r' v =>  match type_of_href r' dict with
                       | Some (o, Btyp ff) => match type_of_subfield ff v with
                                              | Some (Nflip, t) => Some (o, t)
                                              | Some (Flipped, t) => Some (flip_orient o, t)
                                              | None => None
                                              end
                       | _ => None
                       end
  | Esubindex r' n => match type_of_href r' dict with
                      | Some (o, Atyp t' m) => if n < m then Some (o, t') else None
                      | _ => None
                      end
  | Esubaccess r' e => match type_of_href r' dict, type_of_hfexpr Passive e dict with
                       | Some (o, Atyp t' _), Some (Gtyp (Fuint _))
                       | Some (o, Atyp t' _), Some (Gtyp (Fsint _)) => Some (o, t')
                       | _, _ => None
                       end
  end.



(*********************************)
(* statements and FIRRTL modules *)
(*********************************)



(* statement in a FIRRTL program *)
Inductive hfstmt : Type :=
  | Sskip
  | Swire : var -> ftype -> hfstmt
  | Sreg : var -> ftype -> hfstmt
  (*| Sregreset : var -> ftype -> ... -> hfstmt*)
  (*| Smem : var -> hfmem -> hfstmt*)
  (*| Sinst : var -> var -> hfstmt*)
  | Snode : var -> hfexpr -> hfstmt
  | Sfcnct : href -> hfexpr -> hfstmt
  | Sinvalid : href -> hfstmt
  | Swhen : hfexpr -> hfstmt_seq -> hfstmt_seq -> hfstmt
(* statement sequences in a FIRRTL program *)
with hfstmt_seq : Type :=
  | Qnil
  | Qcons : hfstmt -> hfstmt_seq -> hfstmt_seq
.

(* modules and circuits *)

(* Port of a FIRRTL module *)
Inductive hfport : Type :=
  | Finput : var -> ftype -> hfport
  | Foutput : var -> ftype -> hfport
.

(* FIRRTL module *)
Inductive hfmodule : Type :=
  | FInmod : var -> seq hfport -> hfstmt_seq -> hfmodule
.

(* connection summary *)

(* calculates the size of array s *)
Fixpoint array_size (s : array_expr) : nat :=
  match s with
  | Aone _ => 1
  | Acons _ s' => array_size s' + 1
  end.

(* The following functions were intended to be used to initialize a component, but they can be simplified.

(* Makes an array expression by repeating expression e exactly n times *)
Fixpoint make_array_expr (e : hfexpr) (n : nat) : option array_expr :=
  match n with
  | 0 => None
  | 1 => Some (Aone e)
  | n'.+1 => match make_array_expr e n' with
             | Some e' => Some (Acons e e')
             | _ => None
             end
  end.

(* create an expression "Etobedefined t" but take into account that some parts of t may be flipped.
   The flipped parts should be "Eundefinedonpurpose t'" instead. *)
Fixpoint assign_tobedefined (t : ftype) : option hfexpr :=
  match t with
  | Gtyp ft => Some (Etobedefined t)
  | Atyp t' n => match assign_tobedefined t' with
                 | Some (Etobedefined _) => Some (Etobedefined (Atyp t' n))
                 | Some e => match make_array_expr e n with
                             | Some e' => Some (Earray e')
                             | _ => None
                             end
                 | None => None
                 end
  | Btyp ff => assign_tobedefined_fields ff
  end
with assign_tobedefined_fields (ff : ffield) : option hfexpr :=
  match ff with
  | Fnil => Some (Etobedefined (Btyp ff))
  | Fflips v Nflip t ff' => match assign_tobedefined t, assign_tobedefined_fields ff' with
                            | Some (Etobedefined _), Some (Etobedefined (Btyp _)) => Some (Etobedefined (Btyp ff))
                            | Some te, Some (Ebundle ffe) => Some (Ebundle (Bflips v Nflip te ffe))
                            | _, _ => None
                            end
  | Fflips v Flipped t ff' => match assign_undefinedonpurpose t, assign_tobedefined_fields ff' with
                              | Some te, Some (Ebundle ffe) => Some (Ebundle (Bflips v Flipped te ffe))
                              | _, _ => None
                              end
  end
(* create an expression "Eundefinedonpurpose t" but take into account that some parts of t may be flipped.
   The flipped parts should be "Etobedefined t'" instead. *)
with assign_undefinedonpurpose (t : ftype) : option hfexpr :=
  match t with
  | Gtyp ft => Some (Eundefinedonpurpose t)
  | Atyp t' n => match assign_undefinedonpurpose t' with
                 | Some (Eundefinedonpurpose _) => Some (Eundefinedonpurpose (Atyp t' n))
                 | Some e => match make_array_expr e n with
                             | Some e' => Some (Earray e')
                             | _ => None
                             end
                 | None => None
                 end
  | Btyp ff => assign_undefinedonpurpose_fields ff
  end
with assign_undefinedonpurpose_fields (ff : ffield) : option hfexpr :=
  match ff with
  | Fnil => Some (Eundefinedonpurpose (Btyp ff))
  | Fflips v Nflip t ff' => match assign_undefinedonpurpose t, assign_undefinedonpurpose_fields ff' with
                            | Some (Eundefinedonpurpose _), Some (Eundefinedonpurpose (Btyp _)) => Some (Eundefinedonpurpose (Btyp ff))
                            | Some te, Some (Ebundle ffe) => Some (Ebundle (Bflips v Nflip te ffe))
                            | _, _ => None
                            end
  | Fflips v Flipped t ff' => match assign_tobedefined t, assign_undefinedonpurpose_fields ff' with
                              | Some te, Some (Ebundle ffe) => Some (Ebundle (Bflips v Flipped te ffe))
                              | _, _ => None
                              end
  end.
*)


(**************************************)
(*       summary of connections       *)
(**************************************)

(* The type has been defined already. *)
(* This is the first central step of our semantics. The "summarizing" functions extract
   connections from the FIRRTL module and stores them as formal expressions. *)

(* create the connection summary for the sequence of ports pp.
   Obviously, this does not yet contain any actual connections, but only "Etobedefined _" and "Eundefinedonpurpose _" *)
Fixpoint PortSumm (pp : seq hfport) : option summaryType :=
  match pp with 
  | [::] => Some empty_summary
  | Finput vi ti :: pp' => match PortSumm pp' with
                           | Some ps => Some (fun v : var => if v == vi then Some (Inport, ti, Etobedefined ti, Etobedefined ti) else ps v)
                           | None => None
                           end
  | Foutput vo to :: pp' => match PortSumm pp' with
                            | Some ps => Some (fun v : var => if v == vo then Some (Outport, to, Etobedefined to, Etobedefined to) else ps v)
                            | None => None
                            end
  end.
(*
The following function was intended to create a multiplexer expression,
where all multiplexers are at the ground level.
Now instead we would create a multiplexer expression with possibly array expressions
or bundle expressions as its inputs.
---
Fixpoint create_mux_expr (c : hfexpr) (e1 e2 : aggr_expr) : option aggr_expr :=
    (* translate "Emux c e1 e2" to an aggregate expression of type t *)
    match e1, e2 with
    | Gexpr ft1 e1', Gexpr ft2 e2' => match unified_fgtyp ft1 ft2 with
                                      | Some ft => Some (Gexpr ft (Emux c e1' e2'))
                                      | _ => None
                                      end
    | Aexpr s1, Aexpr s2 => match create_array_mux_expr c s1 s2 with
                            | Some s => Some (Aexpr s)
                            | _ => None
                            end
    | Bexpr b1, Bexpr b2 => match create_bundle_mux_expr c b1 b2 with
                            | Some b => Some (Bexpr b)
                            | _ => None
                            end
    | _, _ => None
    end
with create_array_mux_expr (c : hfexpr) (s1 s2 : array_expr) : option array_expr :=
  match s1, s2 with
  | Eone e1, Eone e2 => match create_mux_expr c e1 e2 with
                        | Some e => Some (Eone e)
                        | _ => None
                        end
  | Econs e1 s1', Econs e2 s2' => match create_mux_expr c e1 e2, create_array_mux_expr c s1' s2' with
                                  | Some e, Some s => Some (Econs e s)
                                  | _, _ => None
                                  end
  | _, _ => None
  end
with create_bundle_mux_expr (c : hfexpr) (b1 b2 : bundle_expr) : option bundle_expr :=
  match b1, b2 with
  | Enil, Enil => Some Enil
  | Enflip v1 e1 b1', Enflip v2 e2 b2' => if (v1 == v2)
                                          then match create_mux_expr c e1 e2, create_bundle_mux_expr c b1' b2' with
                                               | Some e, Some b => Some (Enflip v1 e b)
                                               | _, _ => None
                                               end
                                          else None
  | Eflipped v1 e1 b1', Eflipped v2 e2 b2' => if (v1 == v2)
                                              then match create_fmux_expr c e1 e2, create_bundle_mux_expr c b1' b2' with
                                                   | Some e, Some b => Some (Eflipped v1 e b)
                                                   | _, _ => None
                                                   end
                                              else None
  | _, _ => None
  end
with create_fmux_expr (c : hfexpr) (e1 e2 : faggr_expr) : option faggr_expr :=
    (* translate "Emux c e1 e2" to an aggregate expression of type t *)
    match e1, e2 with
    | fGexpr ft1, fGexpr ft2 => match unified_fgtyp ft1 ft2 with
                                | Some ft => Some (fGexpr ft)
                                | _ => None
                                end
    | fAexpr s1, fAexpr s2 => match create_farray_mux_expr c s1 s2 with
                              | Some s => Some (fAexpr s)
                              | _ => None
                              end
    | fBexpr b1, fBexpr b2 => match create_fbundle_mux_expr c b1 b2 with
                              | Some b => Some (fBexpr b)
                              | _ => None
                              end
    | _, _ => None
    end
with create_farray_mux_expr (c : hfexpr) (s1 s2 : farray_expr) : option farray_expr :=
  match s1, s2 with
  | fEone e1, fEone e2 => match create_fmux_expr c e1 e2 with
                          | Some e => Some (fEone e)
                          | _ => None
                          end
  | fEcons e1 s1', fEcons e2 s2' => match create_fmux_expr c e1 e2, create_farray_mux_expr c s1' s2' with
                                    | Some e, Some s => Some (fEcons e s)
                                    | _, _ => None
                                    end
  | _, _ => None
  end
with create_fbundle_mux_expr (c : hfexpr) (b1 b2 : fbundle_expr) : option fbundle_expr :=
  match b1, b2 with
  | fEnil, fEnil => Some fEnil
  | fEnflip v1 e1 b1', fEnflip v2 e2 b2' => if (v1 == v2)
                                            then match create_fmux_expr c e1 e2, create_fbundle_mux_expr c b1' b2' with
                                                 | Some e, Some b => Some (fEnflip v1 e b)
                                                 | _, _ => None
                                                 end
                                            else None
  | fEflipped v1 e1 b1', fEflipped v2 e2 b2' => if (v1 == v2)
                                                then match create_mux_expr c e1 e2, create_fbundle_mux_expr c b1' b2' with
                                                     | Some e, Some b => Some (fEflipped v1 e b)
                                                     | _, _ => None
                                                     end
                                                else None
  | _, _ => None
  end
.

Fixpoint create_aggr_expr (t : ftype) (e : hfexpr) : aggr_expr :=
  match t, e with
  | Gtyp ft, _ => Gexpr ft e
  | Atyp t' n, Emux c e1 e2 => match create_aggr_expr t e1, create_aggr_expr e2 with
        | Aexpr sq1, Aexpr sq2 => Aexpr (mkseq (fun i => ) n)
        (Aexpr (mkseq  

Aexpr (mkseq (fun i => create_aggr_expr () ...) n)
  | Atyp t' n, Eref ... => Aexpr (mkseq (fun i => create_aggr_expr () ...) n)
  | Btyp ff, _ => Bexpr (create_bundle_expr e ff)
  | _, _ => tobedefined t (* error *)
  end
with create_bundle_expr (e: hfexpr) (ff : ffield) : bundle_expr :=
  match e, ff with
  | _, Fnil => Enil
  | Emux ..., Fflips v' Nflip t' ff' => ...
  | Eref ..., Fflips v' Nflip t' ff' => ...
  | Emux ..., Fflips v' Flipped t' ff' => ...
  | Eref ..., Fflips v' Flipped t' ff' => ...
  | _, _ => Enil (* error *)
  .
*)

Fixpoint make_bundle_mux (c : hfexpr) (b1 b2 : bundle_expr) : option bundle_expr :=
  match b1, b2 with
  | Bnil, Bnil => Some Bnil
  | Bflips v1 fl1 e1 b1', Bflips v2 fl2 e2 b2' => if (v1==v2) && (fl1==fl2)
                                                  then match make_bundle_mux c b1' b2' with
                                                       | Some b' => Some (Bflips v1 fl1 (Emux c e1 e2) b')
                                                       | None => None
                                                       end
                                                  else None
  | _, _ => None
  end.

(* splits reference r, which has type ff, into a bundle expression
   (so that later one part of that bundle can be changed) *)
Fixpoint split_ref_into_subfields (r : href) (ff : ffield) : bundle_expr :=
  match ff with
  | Fnil => Bnil
  | Fflips v fl t ff' => Bflips v fl (Eref (Esubfield r v)) (split_ref_into_subfields r ff')
  end.

Fixpoint make_bundle_tobedefined (ff : ffield) : bundle_expr :=
  match ff with
  | Fnil => Bnil
  | Fflips v fl t ff' => Bflips v fl (Etobedefined t) (make_bundle_tobedefined ff')
  end.

Fixpoint make_bundle_undefinedonpurpose (ff : ffield) : bundle_expr :=
  match ff with
  | Fnil => Bnil
  | Fflips v fl t ff' => Bflips v fl (Eundefinedonpurpose t) (make_bundle_undefinedonpurpose ff')
  end.

Fixpoint split_into_subfields (e : hfexpr) (ff : ffield) : option bundle_expr :=
  match e with
  | Ebundle b => Some b (* we assume that the type is right *)
  | Emux c e1 e2 => match split_into_subfields e1 ff, split_into_subfields e2 ff with
                    | Some b1, Some b2 => make_bundle_mux c b1 b2
                    | _, _ => None
                    end
  | Eref r => Some (split_ref_into_subfields r ff)
  | Etobedefined (Btyp _) => Some (make_bundle_tobedefined ff)
  | Eundefinedonpurpose (Btyp _) => Some (make_bundle_undefinedonpurpose ff)
  | _ => None
  end.

(*
(* replaces one subfield of the expression with the new expression *)
Fixpoint connect_subfield_fields (b : bundle_expr) (subfield : var) (new_subfield : hfexpr) : option bundle_expr :=
  match b with
  | Bnil => None
  | Bflips v' Nflip e' ff' => if subfield==v'
                             then Some (Bflips subfield Nflip new_subfield ff')
                             else match connect_subfield_fields ff' subfield new_subfield with
                                  | Some b' => Some (Bflips v' Nflip e' b')
                                  | None => None
                                  end
  | Bflips v' Flipped e' ff' => match connect_subfield_fields ff' subfield new_subfield with
                                | Some b' => Some (Bflips v' Flipped e' b')
                                | None => None
                                end
  end.

(* wrapper for the previous function: replaces one subfield of the expression with the new_subfield expression *)
Definition connect_subfield (e : hfexpr) (subfield : var) (new_subfield : hfexpr) (dict : summaryType) : option hfexpr :=
  match e with
  | Eref r => match type_of_href r dict with
              | Some (o, Btyp ff) => match connect_subfield_fields (split_ref_into_subfields r ff) subfield new_subfield with
                                     | Some b' => Some (Ebundle b')
                                     | None => None
                                     end
              | _ => None
              end
  | Ebundle b => match connect_subfield_fields b subfield new_subfield with
                 | Some b' => Some (Ebundle b')
                 | None => None
                 end
  | _ => None
  end.
*)

(* splits reference r, which has an array type with size elements,
   into an array expression containing r[i], r[i+1], ..., r[size-1].
   This to prepare for replacing one of these expressions with a new value. *)
Fixpoint split_ref_into_subindex (r : href) (i : nat) (size : nat) : option array_expr :=
  match size with
  | 0 => None
  | 1 => Some (Aone (Eref (Esubindex r i)))
  | size'.+1 => match split_ref_into_subindex r (i+1) size' with
                | Some ar => Some (Acons (Eref (Esubindex r i)) ar)
                | _ => None
                end
  end.

Fixpoint make_array_mux (c : hfexpr) (ar1 ar2 : array_expr) : option array_expr :=
  match ar1, ar2 with
  | Aone e1, Aone e2 => Some (Aone (Emux c e1 e2))
  | Acons e1 ar1', Acons e2 ar2' => match make_array_mux c ar1' ar2' with
                                    | Some ar => Some (Acons (Emux c e1 e2) ar)
                                    | None => None
                                    end
  | _, _ => None
  end.

(* Make an array expression that contains size copies of "Etobedefined t" *)
Fixpoint make_array_tobedefined (t : ftype) (size : nat) : option array_expr :=
  match size with
  | 0 => None
  | 1 => Some (Aone (Etobedefined t))
  | size'.+1 => match make_array_tobedefined t size' with
                | Some ar => Some (Acons (Etobedefined t) ar)
                | None => None
                end
  end.

(* Make an array expression that contains size copies of "Eundefinedonpurpose t" *)
Fixpoint make_array_undefinedonpurpose (t : ftype) (size : nat) : option array_expr :=
  match size with
  | 0 => None
  | 1 => Some (Aone (Eundefinedonpurpose t))
  | size'.+1 => match make_array_undefinedonpurpose t size' with
                | Some ar => Some (Acons (Eundefinedonpurpose t) ar)
                | None => None
                end
  end.

(* splits an array expression into parts *)
Fixpoint split_into_subindex (e : hfexpr) (size : nat) : option array_expr :=
  match e with
  | Earray ar => Some ar (* we assume that the size is right *)
  | Emux c e1 e2 => match split_into_subindex e1 size, split_into_subindex e2 size with
                    | Some ar1, Some ar2 => make_array_mux c ar1 ar2
                    | _, _ => None
                    end
  | Eref r => split_ref_into_subindex r 0 size
  | Etobedefined (Atyp t _) => make_array_tobedefined t size
  | Eundefinedonpurpose (Atyp t _) => make_array_undefinedonpurpose t size
  | _ => None
  end.

(* The following functions were an older version of an implementation of connect statements.

(* replaces one element of the array ar, namely ar[n], with new_subexpr *)
Fixpoint connect_subindex_array (ar : array_expr) (n : nat) (new_subexpr : hfexpr) : option array_expr :=
  match n, ar with
  | 0, Aone _ => Some (Aone new_subexpr)
  | 0, Acons _ ar' => Some (Acons new_subexpr ar')
  | n'.+1, Acons e ar' => match connect_subindex_array ar' n' new_subexpr with
                          | Some ar'' => Some (Acons e ar'')
                          | _ => None
                          end
  | _, _ => None
  end.

(* wrapper function for the above: replaces one element of the array indicated by e with new_subexpr *)
Definition connect_subindex (e : hfexpr) (n : nat) (new_subexpr : hfexpr) (dict : summaryType) : option hfexpr :=
  match type_of_hfexpr Source e dict with
  | Some (Atyp _ size) => match split_into_subindex e size with
                          | Some ar => match connect_subindex_array ar n new_subexpr with
                                       | Some ar' => Some (Earray ar')
                                       | None => None
                                       end
                          | None => None
                          end
  | _ => None
  end.

(* replaces one element of the array ar, namely ar[index], with new_subexpr.
   ar is assumed to be the tail end of an array, starting at ar[i], ar[i+1], etc.
   (The specification requires that index has type Fuint, so we do not need to type-convert it.) *)
Fixpoint connect_subaccess_array (ar : array_expr) (i : nat) (index : hfexpr) (new_subexpr : hfexpr) : option array_expr :=
  match ar with
  | Aone e => Some (Aone (Emux (Eprim_binop (Bcomp Beq) index (Econst (Fuint (1 + Nat.log2 i)) i)) new_subexpr e))
  | Acons e ar' => match connect_subaccess_array ar' (i+1) index new_subexpr with
                   | Some ar'' => Some (Acons (Emux (Eprim_binop (Bcomp Beq) index (Econst (Fuint (1 + Nat.log2 i)) i)) new_subexpr e) ar'')
                   | _ => None
                   end
  end.

(* replaces one element of the array indicated by e[index] with new_subexpr.
   This is done through making each array entry a multiplexer expression. *)
Definition connect_subaccess (e : hfexpr) (index : hfexpr) (new_subexpr : hfexpr) (dict : summaryType) : option hfexpr :=
  match type_of_hfexpr Source e dict with
  | Some (Atyp _ size) => match split_into_subindex e size with
                          | Some ar => match connect_subaccess_array ar 0 index new_subexpr with
                                       | Some ar' => Some (Earray ar')
                                       | None => None
                                       end
                          | None => None
                          end
  | _ => None
  end.
*)

(* dependency relation -- to avoid creating cyclic dependencies.
   However, we cannot use "well_founded (depends_on summ)" just anywhere
   because this is in Prop and not in bool.  So, in hindsight it turns out
   to be less useful than we would want. *)

(* A correct program has this property: there is never a combinatorial loop, i.e. a ground-level component part that is connected indirectly to itself.
   (One does not look further down than ground-level component parts, e.g. when doing bit manipulation.)

   This can be expressed as follows:
   - define a relation between ground-level component parts; if the expression for part p1 contains a reference to part p2, then p1 depends on p2
     (except if p1 is (part of) a register, then it's not a combinatorial dependency).
   - state that this relation (or its transitive closure) is well-founded.
     If a module would lead to a non-well-founded relation, it is illegal and has no semantics.

   - To define this relation, one has to assign identifiers to ground-level parts of every component.
*)

Definition component_part : Type := var * nat.

Fixpoint number_of_parts (t : ftype) : nat :=
  match t with
  | Gtyp _ => 1
  | Atyp t' n => n * (number_of_parts t')
  | Btyp ff => number_of_bundle_parts ff
  end
with number_of_bundle_parts (ff : ffield) : nat :=
  match ff with
  | Fnil => 0
  | Fflips _ _ t' ff' => number_of_parts t' + number_of_bundle_parts ff'
  end.

Fixpoint select_array_element (ar : array_expr) (i : nat) : option hfexpr :=
  match ar, i with
  | Aone e, 0 => Some e
  | Aone _, _ => None
  | Acons e _, 0 => Some e
  | Acons _ ar', i'.+1 => select_array_element ar' i'
  end.

Fixpoint select_part (t : ftype) (e : hfexpr) (p : nat) : option (fflip * hfexpr) :=
  match t with
  | Gtyp _ => Some (Nflip, e)
  | Atyp t' size => match split_into_subindex e size with
                    | Some ar => let elementsize := number_of_parts t'
                                 in match select_array_element ar (p %/ elementsize) with
                                    | Some e' => select_part t' e' (p %% elementsize)
                                    | None => None
                                    end
                    | None => None
                    end
  | Btyp ff => match split_into_subfields e ff with
               | Some bu => select_bundle_part ff bu p
               | None => None
               end
  end
with select_bundle_part (ff : ffield) (b : bundle_expr) (p : nat) : option (fflip * hfexpr) :=
  match ff, b with
  | Fflips _ Nflip t' ff', Bflips _ Nflip e' b' => let siz := number_of_parts t'
                                                   in if p<siz
                                                      then select_part t' e' p
                                                      else select_bundle_part ff' b' (p - siz)
  | Fflips _ Flipped t' ff', Bflips _ Flipped e' b' => let siz := number_of_parts t'
                                                       in if p<siz
                                                          then match select_part t' e' p with
                                                               | Some (Nflip, e'') => Some (Flipped, e'')
                                                               | Some (Flipped, e'') => Some (Nflip, e'')
                                                               | None => None
                                                               end
                                                          else select_bundle_part ff' b' (p - siz)
  | _, _ => None
  end.

(* find which part of bundle type ff contains the subfield with name v *)
Fixpoint part_of_subfield (ff : ffield) (v : var) : option (ftype * nat) :=
  match ff with
  | Fnil => None
  | Fflips v' _ ft ff' => if v==v'
                          then Some (ft, 0)
                          else match part_of_subfield ff' v with
                               | Some (ft', i) => Some (ft', i + number_of_parts ft)
                               | None => None
                               end
  end.

Fixpoint depends_on_href (r : href) (p2 : component_part) (base_type : ftype) : option (ftype * nat) :=
(* checks whether reference r depends on p2.
The result is Some (t, i1), meaning that reference r has type t and describes the parts [i1, i1 + number_of_parts t) of the base reference of p2.
The result only looks at the reference, not at the expression in the subaccess part. *)
  match r with
  | Eid v => if v==fst p2
             then Some (base_type, 0)
             else None
  | Esubfield r' v => match depends_on_href r' p2 base_type with
                      | Some (Btyp ff, f) => match part_of_subfield ff v with
                                             | Some (t, offset) => if f + offset <= snd p2 < f + offset + number_of_parts t
                                                                   then Some (t, f + offset)
                                                                   else None
                                             | None => None
                                             end
                      | _ => None
                      end
  | Esubindex r' i => match depends_on_href r' p2 base_type with
                      | Some (Atyp t' siz, f) => let elementsize := number_of_parts t'
                                                 in if f + i * elementsize <= snd p2 < f + (i+1) * elementsize
                                                    then Some (t', f + i * elementsize)
                                                    else None
                      | _ => None
                      end
  | Esubaccess r' e' => match depends_on_href r' p2 base_type with
                        | Some (Atyp t' siz, f) => let elementsize := number_of_parts t'
                                                   in let i := (snd p2 - f) %/ elementsize (* we assume that the accessed element contains p2 *)
                                                      in Some (t', f + i * elementsize)
                        | _ => None
                        end
  end.

Fixpoint depends_on_expr (e : hfexpr) (p2 : component_part) (base_type : ftype) : bool :=
(* checks whether expression e depends on p2. *)
  match e with
  | Econst _ _ => false
  | Ecast _ e' => depends_on_expr e' p2 base_type
  | Eprim_unop _ e' => depends_on_expr e' p2 base_type
  | Eprim_binop _ e1 e2 => depends_on_expr e1 p2 base_type || depends_on_expr e2 p2 base_type
  | Emux c e1 e2 => depends_on_expr c p2 base_type || depends_on_expr e1 p2 base_type || depends_on_expr e2 p2 base_type
  | Eref r => depends_on_subaccess_index r p2 base_type || depends_on_href r p2 base_type
  | Earray _ => false (* should not happen *)
  | Ebundle _ => false (* should not happen *)
  | Etobedefined _ => false
  | Eundefinedonpurpose _ => false
  end
with depends_on_subaccess_index (r : href) (p2 : component_part) (base_type : ftype) : bool :=
(* checks whether a subaccess index expression in r depends on p2. *)
  match r with
  | Eid _ => false
  | Esubfield r' _ => depends_on_subaccess_index r' p2 base_type
  | Esubindex r' _ => depends_on_subaccess_index r' p2 base_type
  | Esubaccess r' e => depends_on_expr e p2 base_type || depends_on_subaccess_index r' p2 base_type
  end.

Definition depends_on (summ : summaryType) (p1 p2 : component_part) : bool :=
(* defines whether p1 depends on p2. This happens if component part p1, according to summ, is connected to component part p2. *)
  match summ (fst p1), summ (fst p2) with
  | Some (Inport, t1, _, ew), Some (_, t2, _, _) => match select_part t1 ew (snd p1) with
                                                    | Some (Flipped, e) => depends_on_expr e p2 t2
                                                    | _ => false
                                                    end
  | Some (Outport, t1, er, _), Some (_, t2, _, _) => match select_part t1 er (snd p1) with
                                                     | Some (Nflip, e) => depends_on_expr e p2 t2
                                                     | _ => false
                                                     end
  | Some (Wire, t1, er, ew), Some (_, t2, _, _) => match select_part t1 er (snd p1) with
                                                   | Some (Nflip, e) => depends_on_expr e p2 t2
                                                   | Some (Flipped, _) => match select_part t1 ew (snd p1) with
                                                                          | Some (Flipped, e) => depends_on_expr e p2 t2
                                                                          | _ => false
                                                                          end
                                                   | None => false
                                                   end
  | Some (Node, t1, er, _), Some (_, t2, _, _) => match select_part t1 er (snd p1) with
                                                  | Some (Nflip, e) => depends_on_expr e p2 t2
                                                  | _ => false
                                                  end
  | _, _ => false (* includes the case that p1 is a part of a register *)
  end.

(* the transitive closure of depends_on can be constructed in a finite number of steps, as the relation is finite.
   However, to use well-foundedness, it is not necessary to construct the transitive closure. *)

(* Find the base of reference r. Return also whether it is a flipped subfield or not. *)
Fixpoint base_ref (r : href) : option var :=
   match r with
   | Eid v => Some v
   | Esubfield r' _ | Esubindex r' _ | Esubaccess r' _ => base_ref r'
   end.

(* Replace the subexpression of old_e (which is of type t) indicated by r by new_e *)
Fixpoint replace_subexpr (old_e : hfexpr) (r : href) (t : ftype) (new_e : hfexpr) : option hfexpr :=
   match r, t with
   | Eid v, _ => Some new_e
   | Esubfield r' v, Btyp ff => match split_into_subfields old_e ff with
                                | Some b => match replace_subfield b r' v ff new_e with
                                            | Some b' => Some (Ebundle b')
                                            | None => None
                                            end
                                | None => None
                                end
   | Esubindex r' n, Atyp t' m => match split_into_subindex old_e m with
                                  | Some ar => let fix replace_subindex (ar : array_expr) (n : nat) : option hfexpr :=
                                                       match n, ar with
                                                       | 0, Aone old_e => match replace_subexpr old_e r' t' new_e with
                                                                          | Some e' => Some (Earray (Aone e'))
                                                                          | None => None
                                                                          end
                                                       | 0, Acons old_e ar' => match replace_subexpr old_e r' t' new_e with
                                                                               | Some e' => Some (Earray (Acons e' ar'))
                                                                               | None => None
                                                                               end
                                                       | n'.+1, Acons old_e ar' => match replace_subindex ar' n' with
                                                                                   | Some (Earray ar'') => Some (Earray (Acons old_e ar''))
                                                                                   | _ => None
                                                                                   end
                                                       | _, _ => None
                                                       end
                                               in replace_subindex ar n
                                  | None => None
                                  end
   | Esubaccess r' index, Atyp t' m => match split_into_subindex old_e m with
                                       | Some ar => let fix replace_subaccess (ar : array_expr) (i : nat) : option hfexpr :=
                                                            match ar with
                                                            | Aone old_e => match replace_subexpr old_e r' t' new_e with
                                                                            | Some e' => Some (Earray (Aone (Emux (Eprim_binop (Bcomp Beq) index (Econst (Fuint (1 + Nat.log2 i)) i)) e' old_e)))
                                                                            | None => None
                                                                            end
                                                            | Acons old_e ar' => match replace_subexpr old_e r' t' new_e, replace_subaccess ar' (i.+1) with
                                                                                 | Some e', Some (Earray ar'') => Some (Earray (Acons (Emux (Eprim_binop (Bcomp Beq) index (Econst (Fuint (1 + Nat.log2 i)) i)) e' old_e) ar''))
                                                                                 | _, _ => None
                                                                                 end
                                                            end
                                                    in replace_subaccess ar 0
                                       | None => None
                                       end
   | _, _ => None
   end
(* replaces the subexpression of subfield field of old_e (which is of type Btyp ff) indicated by r by new_e *)
with replace_subfield (old_e : bundle_expr) (r : href) (field: var) (ff : ffield) (new_e : hfexpr) : option bundle_expr :=
   match old_e, ff with
   | Bflips v fl e old_e', Fflips v' fl' t ff' => if v==v' 
                                                  then if v==field
                                                       then match replace_subexpr e r t new_e with
                                                            | Some new_e' => Some (Bflips v fl new_e' old_e')
                                                            | None => None
                                                            end
                                                       else match replace_subfield old_e' r field ff' new_e with
                                                            | Some b' => Some (Bflips v fl e b')
                                                            | _ => None
                                                            end
                                                  else None
   | _, _ => None
   end.

(* returns the type of r, if the base reference of r has type base_type. 
   Also returns whether r is a flipped subfield of the base. *)
Fixpoint type_of_href_base (r : href) (base_type : ftype) : option (fflip * ftype) :=
  match r with
  | Eid _ => Some (Nflip, base_type)
  | Esubfield r' v => match type_of_href_base r' base_type with
                      | Some (fl, Btyp ff) => match type_of_subfield ff v with
                                              | Some (fl', t) => Some (if fl==fl' then Nflip else Flipped, t)
                                              | None => None
                                              end
                      | _ => None
                      end
  | Esubindex r' _ 
  | Esubaccess r' _ => match type_of_href_base r' base_type with
                       | Some (fl, Atyp t _) => Some (fl, t)
                       | _ => None
                       end
  end.

Definition unidirectional_connect (oldsumm : summaryType) (r : href) (new_e : hfexpr) : option summaryType :=
(* unidirectional connect statement: reference r is assigned new_e as value. *)
  match base_ref r with
  | Some br => match oldsumm br with
               | Some (k, t, enf, efl) => if k==Node
                                          then None
                                          else match type_of_href_base r t with
                                               | Some (fl, _) => match (if fl==Nflip
                                                                        then (replace_subexpr enf r t new_e, Some efl)
                                                                        else (Some enf, replace_subexpr efl r t new_e)) with
                                                                 | (Some enf', Some efl') => Some (fun v : var => if v==br then Some (k, t, enf', efl') else oldsumm v)
                                                                 | _ => None
                                                                 end
                                               | None => None
                                               end
               | None => None
               end
  | None => None
  end.

Definition bidirectional_connect (oldsumm : summaryType) (r1 r2 : href) : option summaryType :=
(* bidirectional connect statement: the writable parts of r1 and r2 are assigned the corresponding part of the other.
   (This obviously only works if the types of r1 and r2 are compatible. *)
  match base_ref r1, base_ref r2 with
  | Some br1,
    Some br2 => match oldsumm br1, oldsumm br2 with
                | Some (k1, t1, enf1, efl1),
                  Some (k2, t2, enf2, efl2) => if (k1==Node) || (k2==Node)
                                               then None
                                               else match type_of_href_base r1 t2, type_of_href_base r2 t2 with
                                                    | Some (fl1, rt1),
                                                      Some (fl2, rt2) => match (if fl1==Nflip
                                                                                then (replace_subexpr enf1 r1 t1 (Eref r2), Some efl1)
                                                                                else (Some enf1, replace_subexpr efl1 r1 t1 (Eref r2))),
                                                                               (if fl2==Flipped
                                                                                then (replace_subexpr enf2 r2 t2 (Eref r1), Some efl2)
                                                                                else (Some enf2, replace_subexpr efl2 r2 t2 (Eref r1))) with
                                                                         | (Some enf1', Some efl1'), 
                                                                           (Some enf2', Some efl2') => Some (fun v : var => if v==br1
                                                                                                                            then Some (k1, t1, enf1', efl1')
                                                                                                                            else if v==br2
                                                                                                                                 then Some (k2, t2, enf2', efl2')
                                                                                                                                 else oldsumm v)
                                                                         | _, _ => None
                                                                         end
                                                    | _, _ => None
                                                    end
                | _, _ => None
                end
  | _, _ => None
  end.

Definition invalidate (oldsumm : summaryType) (r : href) : option summaryType :=
  (* makes reference r "undefined on purpose".
     This is an undefined value that does not raise errors or warnings. *)
  match base_ref r with
  | Some br => match oldsumm br with
               | Some (k, t, enf, efl) => if k==Node
                                          then None
                                          else match type_of_href_base r t with
                                               | Some (fl, rt) => match (if fl==Nflip
                                                                         then (replace_subexpr enf r t (Eundefinedonpurpose rt), Some efl)
                                                                         else (Some enf, replace_subexpr efl r t (Eundefinedonpurpose rt))) with
                                                                  | (Some enf', Some efl') => Some (fun v : var => if v==br then Some (k, t, enf', efl') else oldsumm v)
                                                                  | _ => None
                                                                  end
                                               | None => None
                                               end
               | None => None
               end
  | None => None
  end.

Fixpoint StmtSumm (oldsumm : summaryType) (p : has_finite_support oldsumm) (ss : hfstmt_seq) : option summaryType :=
  (* statement summary: construct the function that contains all connections mandated by the statements in ss *)
  match ss with
  | Qnil => Some oldsumm
  | Qcons Sskip ss' => StmtSumm oldsumm ss'
  | Qcons (Swire vw t) ss' => if oldsumm vw == None
                              then StmtSumm (fun v : var => if v == vw then Some (Wire, t, Etobedefined t, Etobedefined t) else oldsumm v) ss'
                              else None
  | Qcons (Sreg vr t) ss' => if oldsumm vr == None
                             then StmtSumm (fun v : var => if v == vr then Some (Register, t, Eref (Eid v), Eref (Eid v)) else oldsumm v) ss'
                             else None
        (* note that t must be passive *)
  | Qcons (Snode vn e) ss' => if oldsumm vn == None
                              then match type_of_hfexpr Passive e oldsumm (* this requires that widths are already inferred; otherwise, the width of the node may be too small *) with
                                   | Some t => StmtSumm (fun v : var => if v == vn then Some (Node, t, e, Eundefinedonpurpose t) else oldsumm v) ss'
                                   | None => None
                                   end
                              else None
        (* the expression must be passive *)
  | Qcons (Sfcnct r1 (Eref r2)) ss' =>
        match bidirectional_connect oldsumm r1 r2 with
        | Some summ => (* if ~well_founded (depends_on summ) then None else *)
                       StmtSumm summ ss'
        | None => None
        end
  | Qcons (Sfcnct r e) ss' =>
        match unidirectional_connect oldsumm r e with
        | Some summ => (* if ~well_founded (depends_on summ) then None else *)
                       StmtSumm summ ss'
        | None => None
        end
  | Qcons (Sinvalid r) ss' =>
        match invalidate oldsumm r with
        | Some summ => StmtSumm summ ss'
        | None => None
        end
  | Qcons (Swhen c sst ssf) ss' =>
        match StmtSumm oldsumm sst, StmtSumm oldsumm ssf with
        | Some truesumm, Some falsesumm => StmtSumm (fun v : var => match oldsumm v, truesumm v, falsesumm v with
                                                                    | Some (k, t, _, _), Some (_, _, enft, eflt), Some (_, _, enff, eflf) => Some (k, t, if enft==enff then enft else Emux c enft enff, if eflt==eflf then eflt else Emux c eflt eflf)
                                                                    | None, Some tv, None => Some tv
                                                                    | None, None, Some fv => Some fv
                                                                    | _, _, _ => None
                                                                    end) ss'
        | _, _ => None
        end
  end.


(**************************************)
(*       Evaluating expressions       *)
(**************************************)

(* now make the fixpoint of the summary. 
   We need a type of evaluations, i.e. functions that assign a concrete value (in N or Z)
   to every ground element of the defined components.
   These evaluations can be array or bundle expressions...
   So we now make a subtype of hfexpr / a sigma-type.
   Basically, evaluated expressions can be constants or undefined on purpose. *)

Fixpoint expr_is_evaluated (e : hfexpr) : bool :=
  match e with
  | Econst _ _ => true
  | Ecast _ _ => false
  | Eprim_unop _ _ => false
  | Eprim_binop _ _ _ => false
  | Emux _ _ _ => false
  | Eref _ => false
  | Earray ar => array_expr_is_evaluated ar
  | Ebundle bu => bundle_expr_is_evaluated bu
  | Etobedefined _ => false
  | Eundefinedonpurpose _ => true
  end
with array_expr_is_evaluated (ar : array_expr) : bool :=
  match ar with
  | Aone e => expr_is_evaluated e
  | Acons e ar' => expr_is_evaluated e && array_expr_is_evaluated ar'
  end
with bundle_expr_is_evaluated (bu : bundle_expr) : bool :=
  match bu with
  | Bnil => true
  | Bflips _ _ e bu' => expr_is_evaluated e && bundle_expr_is_evaluated bu'
  end.

Definition evaluated_hfexpr := sigT expr_is_evaluated.
Definition evaluated_array_expr := sigT array_expr_is_evaluated.
Definition evaluated_bundle_expr := sigT bundle_expr_is_evaluated.

Definition evalType := var -> option evaluated_hfexpr.

Fixpoint parity (w : nat) (n : nat) : bool :=
(* parity of a w-bit natural number. false == 0 *)
  match w with
  | 0 => false
  | w'.+1 => if odd n then ~~(parity w' (n / 2)) else parity w' (n / 2)
  end.

Definition two_comp (w : nat) (i : int) : nat :=
(* The natural number corresponding to i, if it is given in two's complement in w bits. *)
   match i with
   | Posz n => n
   | Negz n => 2^w - n - 1
   end.

Definition ev_Fuint (w : nat) (n : nat) : evaluated_hfexpr :=
  existT expr_is_evaluated (Econst (Fuint w) n) isT.

Definition ev_Fsint (w : nat) (i : int) : evaluated_hfexpr :=
  existT expr_is_evaluated (Econst (Fsint w) i) isT.

Definition ev_int_to_Fuint (w : nat) (i : int) : evaluated_hfexpr :=
existT expr_is_evaluated (Econst (Fuint w) (two_comp w i)) isT.

Definition oddz (i : int) : bool :=
  match i with
  | Posz n => odd n
  | Negz n => ~~odd n
  end.

Definition int_shr (i : int) (n : nat) : int :=
  match i with
  | Posz n => Posz (n %/ (2^n))
  | Negz n => Negz (n.+1 %/ (2^n) - 1)
  end.

Definition int_div (num den : int) : int :=
  match num, den with
  | Posz n, Posz d => Posz (n %/ d)
  | Posz n, Negz d => Negz (n %/ d.+1) + 1
  | Negz n, Posz d => Negz (n.+1 %/ d) + 1
  | Negz n, Negz d => Posz (n.+1 %/ d.+1)
  end.

Definition int_rem (num den : int) : int :=
  match num, den with
  | Posz n, Posz d => Posz (n %% d)
  | Posz n, Negz d => Posz (n %% d.+1)
  | Negz n, Posz d => Negz (n.+1 %% d) + 1
  | Negz n, Negz d => Negz (n.+1 %% d.+1) + 1
  end.

(* I want the following property to be true:
    5/ 3 =  1 Remainder  2, i.e.  1* 3+2= 5
   -5/ 3 = -1 Remainder -2, i.e. -1* 3-2=-5
    5/-3 = -1 Remainder  2, i.e. -1*-3+2= 5
   -5/-3 =  1 Remainder -2, i.e.  1*-3-2=-5 *)

Lemma int_divn_eq (n d : int) : d<>0 -> n = intZmod.addz (intRing.mulz (int_div n d) d) (int_rem n d).
Proof.
intro Hdnz.
destruct n as [n|n], d as [d|d] ; simpl.
* by rewrite -divn_eq //.
* unfold intRing.mulz.
  destruct (n %/d.+1) eqn: Hnsmall ; simpl.
  + rewrite add0n modn_small //.
    move /eqP : Hnsmall => Hnsmall.
    by rewrite -leqn0 -ltnS ltn_divLR // mul1n // in Hnsmall.
  + by rewrite subSS subn0 -Hnsmall -divn_eq //.
* unfold intRing.mulz.
  destruct (n.+1 %/ d) eqn: Hnsmall ; simpl.
  + rewrite modn_small.
    - simpl ; rewrite subSS mul0n subn0 subn0 //.
    - move /eqP : Hnsmall => Hnsmall.
      destruct d as [|d] ; first by (contradict Hdnz ; reflexivity).
      rewrite -leqn0 -ltnS ltn_divLR // mul1n // in Hnsmall.
  + rewrite subSS subn0.
    destruct (d * n0.+1) eqn: T ;
          first by (destruct d ; first (by contradict Hdnz ; reflexivity) ;
                                 last  (by move /eqP : T => T ; rewrite muln_eq0 // in T)).
    simpl.
    destruct (n.+1 %% d) eqn: H ; simpl.
    - rewrite subnn subn0.
      assert (n.+1 == n1.+1)
            by rewrite -T -Hnsmall mulnC -(addn0 (n.+1 %/ d * d)) -H -divn_eq //.
      rewrite eqSS in H0 ; move /eqP : H0 => H0 ; rewrite H0 //.
    - assert (n.+1 == n1.+1 + n2.+1)
            by (rewrite -T -Hnsmall -H mulnC -divn_eq //).
      rewrite -(addn1 n2) addnA addn1 eqSS in H0.
      move /eqP : H0 => H0 ; rewrite H0 subSS subn0 addSn //.
* destruct (n.+1 %/ d.+1 * d.+1) eqn: H ; simpl.
  + move /eqP : H => H ; rewrite -(eqn_add2r (n.+1 %% d.+1)) add0n -divn_eq in H.
    move /eqP : H => H ; rewrite -H ; simpl.
    rewrite subSS subn0 subn0 //.
  + destruct (n.+1 %% d.+1) eqn: H0 ; simpl.
    - assert (n.+1 == n0.+1)
            by rewrite -(addn0 n0.+1) -H -H0 -divn_eq //.
      rewrite eqSS in H1 ; move /eqP : H1 => H1 ; rewrite H1 subSS subn0 subn0 //.
    - assert (n.+1 == n0.+1 + n1.+1)
            by rewrite -H -H0 -divn_eq //.
      rewrite -(addn1 n1) addnA addn1 eqSS in H1.
      move /eqP : H1 => H1 ; rewrite H1 subSS subn0 addSn //.
Qed.

Fixpoint bit_and (w : nat) (n1 n2 : nat) : nat :=
  match w with
  | 0 => 0
  | w'.+1 => 2 * (bit_and w' (n1 %/ 2) (n2 %/ 2)) + (odd n1 && odd n2)
  end.

Fixpoint bit_or (w : nat) (n1 n2 : nat) : nat :=
  match w with
  | 0 => 0
  | w'.+1 => 2 * (bit_or w' (n1 %/ 2) (n2 %/ 2)) + (odd n1 || odd n2)
  end.

Fixpoint bit_xor (w : nat) (n1 n2 : nat) : nat :=
  match w with
  | 0 => 0
  | w'.+1 => 2 * (bit_xor w' (n1 %/ 2) (n2 %/ 2)) + (odd n1 != odd n2)
  end.

Fixpoint unify_mux_type' (e : hfexpr) (p : expr_is_evaluated e) (t : ftype) : option (evaluated_hfexpr * ftype) :=
  (* unfies types for multiplexers:
     returns expression e, with types widened according to t *)
  match e, p, t with
  | Econst t n, _, Gtyp t' => match unified_fgtyp t t' with
                              | Some tu => Some (existT expr_is_evaluated (Econst tu n) isT, Gtyp tu)
                              | None => None
                              end
  | Earray ar, p, Atyp t' n => match unify_mux_array_type ar p (Atyp t' n) with
                               | Some (existT ar pa, t) => Some (existT expr_is_evaluated (Earray ar) pa, t)
                               | None => None
                               end
  | Ebundle bu, p, Btyp ff => match unify_mux_bundle_type bu p ff with
                              | Some (existT bu pbu, ff) => Some (existT expr_is_evaluated (Ebundle bu) pbu, Btyp ff)
                              | None => None
                              end
  | Eundefinedonpurpose t, _, t' => match unified_type t t' with
                                    | Some tu => Some (existT expr_is_evaluated (Eundefinedonpurpose tu) isT, tu)
                                    | None => None
                                    end
  (*| _, p, _ => False_rec (option (evaluated_hfexpr * ftype)) p*)
  | _, _, _ => None
  end
with unify_mux_array_type (ar : array_expr) (p : array_expr_is_evaluated ar) (t : ftype) : option (evaluated_array_expr * ftype) :=
  match ar, p, t with
  | Aone e, p, Atyp t' 1 => match unify_mux_type' e p t' with
                            | Some (existT eu pu, tu) => Some (existT array_expr_is_evaluated (Aone eu) pu, (Atyp tu 1))
                            | None => None
                            end
  | Acons e ar', p, Atyp t' n.+1 => match unify_mux_array_type ar' (proj2 (andP p)) (Atyp t' n) with
                                    | Some (existT au pau, Atyp tu _) => match unify_mux_type' e (proj1 (andP p)) tu with
                                                                         | Some (existT eu peu, tu') => Some (existT array_expr_is_evaluated (Acons eu au) (proj1 (rwP andP) (conj peu pau)), Atyp tu' n.+1)
                                                                         | None => None
                                                                         end
                                    | _ => None
                                    end
  | _, _, _ => None
  end
with unify_mux_bundle_type (bu : bundle_expr) (p : bundle_expr_is_evaluated bu) (ff : ffield) : option (evaluated_bundle_expr * ffield) :=
  match bu, p, ff with
  | Bnil, p, Fnil => Some (existT bundle_expr_is_evaluated Bnil isT, Fnil)
  | Bflips v Nflip e bu', p, Fflips vt Nflip et ff' => if v==vt
                                                       then match unify_mux_type' e (proj1 (andP p)) et, unify_mux_bundle_type bu' (proj2 (andP p)) ff' with
                                                            | Some (existT eu peu, teu), Some (existT buu pbuu, ffu) => Some (existT bundle_expr_is_evaluated (Bflips v Nflip eu buu) (proj1 (rwP andP) (conj peu pbuu)), Fflips v Nflip teu ffu)
                                                            | _, _ => None
                                                            end
                                                       else None
  | _, _, _ => None
  end.

Definition unify_mux_type (e : evaluated_hfexpr) (t : ftype) : option evaluated_hfexpr :=
  match e with
  | existT e' p => match unify_mux_type' e' p t with
                   | Some (eu, _) => Some eu
                   | None => None
                   end
  end.

Fixpoint select_array_el (ar : evaluated_array_expr) (n : nat) : option evaluated_hfexpr :=
  match ar, n with
  | existT (Aone e) p, 0 => Some (existT expr_is_evaluated e p)
  | existT (Acons e _) p, 0 => Some (existT expr_is_evaluated e (proj1 (andP p)))
  | existT (Acons _ ar') p, n'.+1 => select_array_el (existT array_expr_is_evaluated ar' (proj2 (andP p))) n'
  | _, _ => None
  end.

Fixpoint select_bundle_field (bu : bundle_expr) (p : bundle_expr_is_evaluated bu) (v : var) : option evaluated_hfexpr :=
  match bu, p with
  | Bnil, _ => None
  | Bflips vb fl e bu', p => if v==vb
                             then Some (existT expr_is_evaluated e (proj1 (andP p)))
                             else select_bundle_field bu' (proj2 (andP p)) v
  end.

Fixpoint eval_expr (inputs : evalType) (e : hfexpr) : option evaluated_hfexpr :=
  match e with
  | Econst t n => Some (existT expr_is_evaluated (Econst t n) isT)
  | Ecast u e' => match u, eval_expr inputs e' with
                  | AsUInt, Some (existT (Econst (Fuint w) (Posz n)) _) => Some (ev_Fuint w n)
                  | AsUInt, Some (existT (Econst (Fsint w) i) _) => Some (ev_int_to_Fuint w i)
                  | AsUInt, Some (existT (Econst _ (Posz n)) _) => Some (ev_Fuint 1 n)
                  | AsSInt, Some (existT (Econst (Fuint w) (Posz n)) _) => Some (ev_Fsint w n)
                  | AsSInt, Some (existT (Econst (Fsint w) i) _) => Some (ev_Fsint w i)
                  | AsSInt, Some (existT (Econst _ (Posz n)) _) => Some (ev_Fuint 1 n)
                  | AsClock, Some (existT (Econst _ i) _) => Some (existT expr_is_evaluated (Econst Fclock (oddz i)) isT)
                  | AsAsync, Some (existT (Econst _ i) _) => Some (existT expr_is_evaluated (Econst Fasyncreset (oddz i)) isT)
                  | _, _ => None
                  end
  | Eprim_unop op e' => match op, eval_expr inputs e' with
                        | Upad w, Some (existT (Econst (Fuint w') (Posz n)) _) => Some (ev_Fuint (max w w') n)
                        | Upad w, Some (existT (Econst (Fsint w') i) _) => Some (ev_Fsint (max w w') i)
                        | Ushl d, Some (existT (Econst (Fuint w) (Posz n)) _) => Some (ev_Fuint (w+d) (n * 2^d))
                        | Ushl d, Some (existT (Econst (Fsint w) i) _) => Some (ev_Fsint (w+d) (GRing.natmul i (2^d)))
                        | Ushr d, Some (existT (Econst (Fuint w) (Posz n)) _) => Some (ev_Fuint (w-d) (n %/ (2^d)))
                        | Ushr d, Some (existT (Econst (Fsint w) i) _) => Some (ev_Fsint (w-d) (int_shr i d))
                        | Ucvt, Some (existT (Econst (Fuint w) (Posz n)) _) => Some (ev_Fsint (w+1) n)
                        | Ucvt, Some (existT (Econst (Fsint w) i) _) => Some (ev_Fsint w i)
                        | Uneg, Some (existT (Econst (Fuint w) (Posz n)) _) => Some (ev_Fsint (w+1) (-(Posz n)))
                        | Uneg, Some (existT (Econst (Fsint w) i) _) => Some (ev_Fsint (w+1) (-i))
                        | Unot, Some (existT (Econst (Fuint w) (Posz n)) _) => Some (ev_Fuint w (2^w-n-1))
                        | Unot, Some (existT (Econst (Fsint w) i) _) => Some (ev_int_to_Fuint w (-i-1))
                        | Uandr, Some (existT (Econst (Fuint w) (Posz n)) _) => Some (ev_Fuint 1 (if (w==0) || (n==2^w-1) then 1 else 0))
                        | Uandr, Some (existT (Econst (Fsint w) i) _) => Some (ev_Fuint 1 (if (w==0) || (i==(-1)%Z) then 1 else 0))
                        | Uorr, Some (existT (Econst (Fuint w) (Posz n)) _) => Some (ev_Fuint 1 (if (w==0) || (n==0) then 0 else 1))
                        | Uorr, Some (existT (Econst (Fsint w) i) _) => Some (ev_Fuint 1 (if (w==0) || (i==0) then 0 else 1))
                        | Uxorr, Some (existT (Econst (Fuint w) (Posz n)) _) => Some (ev_Fuint 1 (parity w n))
                        | Uxorr, Some (existT (Econst (Fsint w) i) _) => Some (ev_Fuint 1 (parity w (two_comp w i)))
                        | Uextr hi lo, Some (existT (Econst (Fuint w) (Posz n)) _) => Some (ev_Fuint (hi+1-lo) (n %% 2^(hi+1) / 2^lo))
                        | Uextr hi lo, Some (existT (Econst (Fsint w) i) _) => Some (ev_Fuint (hi+1-lo) ((two_comp w i) %% 2^(hi+1) / 2^lo))
                        | Uhead h, Some (existT (Econst (Fuint w) (Posz n)) _) => Some (ev_Fuint h (n / 2^(w-h)))
                        | Uhead h, Some (existT (Econst (Fsint w) i) _) => Some (ev_Fuint h ((two_comp w i) / 2^(w-h)))
                        | Utail t, Some (existT (Econst (Fuint w) (Posz n)) _) => Some (ev_Fuint (w-t) (n %% 2^(w-t)))
                        | Utail t, Some (existT (Econst (Fsint w) i) _) => Some (ev_Fuint (w-t) ((two_comp w i) %% 2^(w-t)))
                        | _, _ => None
                        end
  | Eprim_binop o e1 e2 => match o, eval_expr inputs e1, eval_expr inputs e2 with
                           | Badd, Some (existT (Econst (Fuint w1) (Posz n1)) _), Some (existT (Econst (Fuint w2) (Posz n2)) _) => Some (ev_Fuint (1+max w1 w2) (n1 + n2))
                           | Badd, Some (existT (Econst (Fsint w1) i1) _), Some (existT (Econst (Fsint w2) i2) _) => Some (ev_Fsint (1+max w1 w2) (i1 + i2))
                           | Bsub, Some (existT (Econst (Fuint w1) (Posz n1)) _), Some (existT (Econst (Fuint w2) (Posz n2)) _) => Some (ev_Fuint (1+max w1 w2) (if n1<n2 then 2^(1+max w1 w2) + n1 - n2 else n1 - n2))
                           | Bsub, Some (existT (Econst (Fsint w1) i1) _), Some (existT (Econst (Fsint w2) i2) _) => Some (ev_Fsint (1+max w1 w2) (i1 - i2))
                           | Bmul, Some (existT (Econst (Fuint w1) (Posz n1)) _), Some (existT (Econst (Fuint w2) (Posz n2)) _) => Some (ev_Fuint (w1+w2) (n1 * n2))
                           | Bmul, Some (existT (Econst (Fsint w1) i1) _), Some (existT (Econst (Fsint w2) i2) _) => Some (ev_Fsint (w1+w2) (i1 *~ i2))
                           | Bdiv, Some (existT (Econst (Fuint w1) (Posz n1)) _), Some (existT (Econst (Fuint _ ) (Posz n2)) _) => Some (ev_Fuint w1 (n1 %/ n2))
                           | Bdiv, Some (existT (Econst (Fsint w1) i1) _), Some (existT (Econst (Fsint _ ) i2) _) => Some (ev_Fsint (w1+1) (int_div i1 i2))
                           | Brem, Some (existT (Econst (Fuint w1) (Posz n1)) _), Some (existT (Econst (Fuint w2) (Posz n2)) _) => Some (ev_Fuint (min w1 w2) (w1 %% w2))
                           | Brem, Some (existT (Econst (Fsint w1) i1) _), Some (existT (Econst (Fsint w2) i2) _) => Some (ev_Fsint (min w1 w2) (int_rem i1 i2))
                           | Bcomp Blt,  Some (existT (Econst (Fuint _ ) (Posz n1)) _), Some (existT (Econst (Fuint _ ) (Posz n2)) _) => Some (ev_Fuint 1 (if n1<n2 then 1 else 0))
                           | Bcomp Blt,  Some (existT (Econst (Fsint w1) i1) _), Some (existT (Econst (Fsint w2) i2) _) => Some (ev_Fuint 1 (if intOrdered.ltz i1 i2 then 1 else 0))
                           | Bcomp Bleq, Some (existT (Econst (Fuint _ ) (Posz n1)) _), Some (existT (Econst (Fuint _ ) (Posz n2)) _) => Some (ev_Fuint 1 (if n1<=n2 then 1 else 0))
                           | Bcomp Bleq, Some (existT (Econst (Fsint w1) i1) _), Some (existT (Econst (Fsint w2) i2) _) => Some (ev_Fuint 1 (if intOrdered.lez i1 i2 then 1 else 0))
                           | Bcomp Bgt,  Some (existT (Econst (Fuint _ ) (Posz n1)) _), Some (existT (Econst (Fuint _ ) (Posz n2)) _) => Some (ev_Fuint 1 (if n1<=n2 then 0 else 1))
                           | Bcomp Bgt,  Some (existT (Econst (Fsint w1) i1) _), Some (existT (Econst (Fsint w2) i2) _) => Some (ev_Fuint 1 (if intOrdered.lez i1 i2 then 0 else 1))
                           | Bcomp Bgeq, Some (existT (Econst (Fuint _ ) (Posz n1)) _), Some (existT (Econst (Fuint _ ) (Posz n2)) _) => Some (ev_Fuint 1 (if n1<n2 then 0 else 1))
                           | Bcomp Bgeq, Some (existT (Econst (Fsint w1) i1) _), Some (existT (Econst (Fsint w2) i2) _) => Some (ev_Fuint 1 (if intOrdered.ltz i1 i2 then 0 else 1))
                           | Bcomp Beq,  Some (existT (Econst (Fuint _ ) (Posz n1)) _), Some (existT (Econst (Fuint _ ) (Posz n2)) _) => Some (ev_Fuint 1 (if n1==n2 then 1 else 0))
                           | Bcomp Beq,  Some (existT (Econst (Fsint w1) i1) _), Some (existT (Econst (Fsint w2) i2) _) => Some (ev_Fuint 1 (if i1==i2 then 1 else 0))
                           | Bcomp Bneq, Some (existT (Econst (Fuint _ ) (Posz n1)) _), Some (existT (Econst (Fuint _ ) (Posz n2)) _) => Some (ev_Fuint 1 (if n1==n2 then 0 else 1))
                           | Bcomp Bneq, Some (existT (Econst (Fsint w1) i1) _), Some (existT (Econst (Fsint w2) i2) _) => Some (ev_Fuint 1 (if i1==i2 then 0 else 1))
                           | Bdshl, Some (existT (Econst (Fuint w1) (Posz n1)) _), Some (existT (Econst (Fuint w2) (Posz n2)) _) => Some (ev_Fuint (w1 + 2^w2 - 1) (n1 * 2^n2))
                           | Bdshl, Some (existT (Econst (Fsint w1) i1) _), Some (existT (Econst (Fuint w2) (Posz n2)) _) => Some (ev_Fsint (w1 + 2^w2-1) (i1 * 2^n2))
                           | Bdshr, Some (existT (Econst (Fuint w1) (Posz n1)) _), Some (existT (Econst (Fuint _) (Posz n2)) _) => Some (ev_Fuint w1 (n1 %/ 2^n2))
                           | Bdshr, Some (existT (Econst (Fsint w1) i1) _), Some (existT (Econst (Fuint _) (Posz n2)) _) => Some (ev_Fsint w1 (int_div i1 (2^n2)))
                           | Band, Some (existT (Econst (Fuint w1) (Posz n1)) _), Some (existT (Econst (Fuint w2) (Posz n2)) _) => let w := maxn w1 w2
                                                                                                                                   in Some (ev_Fuint w (bit_and w n1 n2))
                           | Band, Some (existT (Econst (Fsint w1) i1) _), Some (existT (Econst (Fsint w2) i2) _) => let w := maxn w1 w2
                                                                                                                     in Some (ev_Fuint w (bit_and w (two_comp w i1) (two_comp w i2)))
                           | Bor, Some (existT (Econst (Fuint w1) (Posz n1)) _), Some (existT (Econst (Fuint w2) (Posz n2)) _) => let w := maxn w1 w2
                                                                                                                                  in Some (ev_Fuint w (bit_or w n1 n2))
                           | Bor, Some (existT (Econst (Fsint w1) i1) _), Some (existT (Econst (Fsint w2) i2) _) => let w := maxn w1 w2
                                                                                                                    in Some (ev_Fuint w (bit_or w (two_comp w i1) (two_comp w i2)))
                           | Bxor, Some (existT (Econst (Fuint w1) (Posz n1)) _), Some (existT (Econst (Fuint w2) (Posz n2)) _) => let w := maxn w1 w2
                                                                                                                                   in Some (ev_Fuint w (bit_xor w n1 n2))
                           | Bxor, Some (existT (Econst (Fsint w1) i1) _), Some (existT (Econst (Fsint w2) i2) _) => let w := maxn w1 w2
                                                                                                                     in Some (ev_Fuint w (bit_xor w (two_comp w i1) (two_comp w i2)))
                           | Bcat, Some (existT (Econst (Fuint w1) (Posz n1)) _), Some (existT (Econst (Fuint w2) (Posz n2)) _) => Some (ev_Fuint (w1+w2) (n1 * 2^w2 + n2))
                           | Bcat, Some (existT (Econst (Fsint w1) i1) _), Some (existT (Econst (Fsint w2) i2) _) => Some (ev_Fuint (w1+w2) ((two_comp w1 i1) * 2^w2 + (two_comp w2 i2)))
                           | _, _, _ => None
                           end
  | Emux c e1 e2 => match eval_expr inputs c, eval_expr inputs e1, eval_expr inputs e2 with
                    | Some (existT (Econst (Fuint 1) c') _), Some (existT e1' p1'), Some (existT e2' p2') => if c'!=0
                                                                                                             then match type_of_hfexpr Passive e2' empty_summary with
                                                                                                                  | Some t2 => unify_mux_type (existT expr_is_evaluated e1' p1') t2
                                                                                                                  | None => None
                                                                                                                  end
                                                                                                             else match type_of_hfexpr Passive e1' empty_summary with
                                                                                                                  | Some t1 => unify_mux_type (existT expr_is_evaluated e2' p2') t1
                                                                                                                  | None => None
                                                                                                                  end
                    | _, _, _ => None
                    end
  (*|Evalidif c e => *)
  | Eref r => eval_ref inputs r
  | Earray ar => match eval_array_expr inputs ar with
                 | Some (existT ar' p) => Some (existT expr_is_evaluated (Earray ar') p)
                 | None => None
                 end
  | Ebundle bu => match eval_bundle_expr inputs bu with
                  | Some (existT bu' p) => Some (existT expr_is_evaluated (Ebundle bu') p)
                  | None => None
                  end
  | Etobedefined _ => None
  | Eundefinedonpurpose t => Some (existT expr_is_evaluated (Eundefinedonpurpose t) isT)
  end
with eval_array_expr (inputs: evalType) (ar : array_expr) : option evaluated_array_expr :=
  match ar with
  | Aone e => match eval_expr inputs e with
              | Some (existT e' p) => Some (existT array_expr_is_evaluated (Aone e') p)
              | None => None
              end
  | Acons e ar' => match eval_expr inputs e, eval_array_expr inputs ar' with
                   | Some (existT e' pe), Some (existT ar'' pa) => Some (existT array_expr_is_evaluated (Acons e' ar'') (proj1 (rwP andP) (conj pe pa)))
                   | _, _ => None
                   end
  end
with eval_bundle_expr (inputs : evalType) (bu : bundle_expr) : option evaluated_bundle_expr :=
  match bu with
  | Bnil => Some (existT bundle_expr_is_evaluated Bnil isT)
  | Bflips v fl e bu' => match eval_expr inputs e, eval_bundle_expr inputs bu' with
                         | Some (existT e' pe), Some (existT bu'' pb) => Some (existT bundle_expr_is_evaluated (Bflips v fl e' bu'') (proj1 (rwP andP) (conj pe pb)))
                         | _, _ => None
                         end
  end
with eval_ref (inputs : evalType) (r : href) : option evaluated_hfexpr :=
  match r with
  | Eid v => inputs v
  | Esubfield r' v => match eval_ref inputs r' with
                      | Some (existT (Ebundle bu) p) => select_bundle_field bu p v
                      | _ => None
                      end
  | Esubindex r' n => match eval_ref inputs r' with
                      | Some (existT (Earray ar) p) => select_array_el (existT array_expr_is_evaluated ar p) n
                      | _ => None
                      end
  | Esubaccess r' i => match eval_ref inputs r', eval_expr inputs i with
                       | Some (existT (Earray ar) p), Some (existT (Econst (Fuint _) (Posz n)) _) => select_array_el (existT array_expr_is_evaluated ar p) n
                       | _, _ => None
                       end
  end.

Fixpoint make_evaluated_array_undefinedonpurpose (t : ftype) (size : nat) : option evaluated_array_expr :=
  match size with
  | 0 => None
  | 1 => Some (existT array_expr_is_evaluated (Aone (Eundefinedonpurpose t)) isT)
  | size'.+1 => match make_evaluated_array_undefinedonpurpose t size' with
                | Some (existT ar p) => Some (existT array_expr_is_evaluated (Acons (Eundefinedonpurpose t) ar) (introT andP (conj isT p)))
                | None => None
                end
  end.

Definition evaluated_split_into_subindex (e : evaluated_hfexpr) : option evaluated_array_expr :=
(* the same as split_into_subindex, but specialized to evaluated expressions.
   Because the only evaluated expressions designating arrays are Earray and Eundefinedonpurpose,
   the function is much simpler. In particular there is no need to look at multiplexers. *)
  match e with
  | existT (Earray ar) p => Some (existT array_expr_is_evaluated ar p) (* we assume that the size is right *)
  | existT (Eundefinedonpurpose (Atyp t size)) _ => make_evaluated_array_undefinedonpurpose t size
  | _ => None
  end.

Fixpoint make_evaluated_bundle_undefinedonpurpose (ff : ffield) : evaluated_bundle_expr :=
  match ff with
  | Fnil => existT bundle_expr_is_evaluated Bnil isT
  | Fflips v fl t ff' => match make_evaluated_bundle_undefinedonpurpose ff' with
                         | existT bu' p' => existT bundle_expr_is_evaluated (Bflips v fl (Eundefinedonpurpose t) bu') (introT andP (conj isT p'))
                         end
  end.

Definition evaluated_split_into_subfields (e : evaluated_hfexpr) (ff : ffield) : option evaluated_bundle_expr :=
(* the same as split_into_subfields, but specialized to evaluated expressions.
   Because the only evaluated expressions designating bundles are Ebundle and Eundefinedonpurpose,
   the function is much simpler. *)
  match e with
  | existT (Ebundle b) p => Some (existT bundle_expr_is_evaluated b p) (* we assume that the type is right *)
  | existT (Eundefinedonpurpose (Btyp _)) _ => Some (make_evaluated_bundle_undefinedonpurpose ff)
  | _ => None
  end.

(* We now have to do the work to combine the unflipped and flipped expressions for a component.
   (For example, the unflipped parts of an input port are taken from the input evaluation,
   while its flipped parts are taken from the assigned connection.)
   It might look easier to do this already further above, and simplify the summary type to
   var -> option (kind * ftype * hfexpr), where the single hfexpr already combines the unflipped
   and flipped expressions. But even if we did so, we still have to combine here again the
   input and output ports. *)

Fixpoint combine_flip_evaluations (t : ftype) (nfl flp : evaluated_hfexpr) : option evaluated_hfexpr :=
  if is_passive t 
  then Some nfl
  else match t with
       | Gtyp _ => Some nfl
       | Atyp t' n => match evaluated_split_into_subindex nfl, evaluated_split_into_subindex flp with
                      | Some nfl', Some flp' => let fix combine_array_flip_evaluations (size : nat) (nfl flp : evaluated_array_expr) : option evaluated_array_expr :=
                                                        match size, nfl, flp with
                                                        | 0, _, _ => None
                                                        | 1, existT (Aone nfl') p_nfl, existT (Aone flp') p_flp => match combine_flip_evaluations t' (existT expr_is_evaluated nfl' p_nfl) (existT expr_is_evaluated flp' p_flp) with
                                                                                                                   | Some (existT e' p') => Some (existT array_expr_is_evaluated (Aone e') p')
                                                                                                                   | None => None
                                                                                                                   end
                                                        | size'.+1, existT (Acons e_nfl nfl'') p_nfl, existT (Acons e_flp flp'') p_flp => match combine_flip_evaluations t' (existT expr_is_evaluated e_nfl (proj1 (andP p_nfl))) (existT expr_is_evaluated e_flp (proj1 (andP p_flp))), combine_array_flip_evaluations size' (existT array_expr_is_evaluated nfl'' (proj2 (andP p_nfl))) (existT array_expr_is_evaluated flp'' (proj2 (andP p_flp))) with
                                                                                                                                          | Some (existT e' p'), Some (existT ar' par') => Some (existT array_expr_is_evaluated (Acons e' ar') (introT andP (conj p' par')))
                                                                                                                                          | _, _ => None
                                                                                                                                          end
                                                        | _, _, _ => None
                                                        end
                                                in match combine_array_flip_evaluations n nfl' flp' with
                                                   | Some (existT ar p) => Some (existT expr_is_evaluated (Earray ar) p)
                                                   | None => None
                                                   end
                      | _, _ => None
                      end
       | Btyp ff => match evaluated_split_into_subfields nfl ff, evaluated_split_into_subfields flp ff with
                    | Some nfl', Some flp' => match combine_bundle_flip_evaluations ff nfl' flp' with
                                              | Some (existT bu p) => Some (existT expr_is_evaluated (Ebundle bu) p)
                                              | None => None
                                              end
                    | _, _ => None
                    end
       end
with combine_bundle_flip_evaluations (ff : ffield) (nfl flp : evaluated_bundle_expr) : option evaluated_bundle_expr :=
  match ff, nfl, flp with
  | Fnil, existT Bnil _, existT Bnil _ => Some (existT bundle_expr_is_evaluated Bnil isT)
  | Fflips v fl t ff', existT (Bflips vn fln en nfl') pn, existT (Bflips vf flf ef flp') pf => if (v==vn) && (v==vf) && (fl==fln) && (fl==flf)
                                                                                               then match combine_flip_evaluations t (existT expr_is_evaluated en (proj1 (andP pn))) (existT expr_is_evaluated ef (proj1 (andP pf))), combine_bundle_flip_evaluations ff' (existT bundle_expr_is_evaluated nfl' (proj2 (andP pn))) (existT bundle_expr_is_evaluated flp' (proj2 (andP pf))) with
                                                                                                    | Some (existT e' pe'), Some (existT b' pb') => Some (existT bundle_expr_is_evaluated (Bflips v fl e' b') (introT andP (conj pe' pb')))
                                                                                                    | _, _ => None
                                                                                                    end
                                                                                               else None
  | _, _, _ => None
  end.

Fixpoint iterate (inputs : evalType) (summ : summaryType) (n : nat) : evalType :=
  (* iterates the evaluation of expressions in the summary, so that all values from inputs will be propagated through
     to every component. The number n should be at least the combinatorial depth of the module. 
     inputs should define the unflipped parts of the input ports, the flipped parts of the output ports, and the register values.
     (Register values are needed because reading from a register produces its "old" value.) *)
   match n with
   | 0 => inputs
   | n'.+1 => iterate (fun v : var => match summ v with
                                      | Some (Inport, ft, _, ew) => match inputs v, eval_expr inputs ew with
                                                                    | Some in', Some ew' => combine_flip_evaluations ft in' ew'
                                                                    | _, _ => None
                                                                    end
                                      | Some (Outport, ft, ew, _) => match eval_expr inputs ew, inputs v with
                                                                     | Some ew', Some in' => combine_flip_evaluations ft ew' in'
                                                                     | _, _ => None
                                                                     end
                                      | Some (Wire, ft, er, ew) => match eval_expr inputs er, eval_expr inputs ew with
                                                                   | Some er', Some ew' => combine_flip_evaluations ft er' ew'
                                                                   | _, _ => None
                                                                   end
                                      | Some (Register, ft, er, _) => if n'!=0
                                                                      then inputs v (* if it's not the last iteration, keep reading the old/input value *)
                                                                      else eval_expr inputs er (* should always be passive *)
                                      | Some (Node, ft, er, _) => eval_expr inputs er (* should always be passive *)
                                      | None => None
                                      end) summ n'
   end.

(* Now determine how often we should iterate: that depends on the longest connection path,
   but to simplify we can just count the number of connections.

   Proving that this suffices formally is probably not simple;
   we have to check the connections at the level of the individual ground-level component.

   A correct program has this property: there is never a combinatorial loop, i.e. a ground-level component part that is connected indirectly to itself.
   (One does not look further down than ground-level component parts, e.g. when doing bit manipulation.)
   This is expressed as "well_founded (depends_on summary)".

   As we did not check the well-foundedness of connect statements above,
   we will be unable to prove the well-foundedness of the program.
   Therefore, we shall assume that in the future.
   Still, we can prove the well-foundedness of the port summary:
*)

Lemma empty_summary_is_well_founded : forall p : component_part, Acc (depends_on empty_summary) p.
Proof.
intros [p2 n2].
apply Acc_intro.
intros [p1 n1] H.
contradict H.
unfold depends_on ; simpl ; done.
Qed.

Lemma PortSumm_is_tobedefined :
forall (pp : seq hfport) (summ : summaryType),
      PortSumm pp = Some summ
   ->
      forall (c : var) (k : kind) (t : ftype) (e1 e2 : hfexpr),
            summ c = Some (k, t, e1, e2)
         ->
            (k = Inport \/ k = Outport) /\ e1 = Etobedefined t /\ e2 = Etobedefined t.
Proof.
induction pp.
* intros summ Hp c k t e1 e2 Hsumm.
  simpl PortSumm in Hp.
  inversion Hp.
  by rewrite -H0 // in Hsumm.
* intros summ Hp c k t e1 e2 Hsumm.
  simpl PortSumm in Hp.
  destruct a as [v' t'|v' t'].
  1,2: destruct (PortSumm pp) as [summ'|] ; last by discriminate.
  1,2: specialize (IHpp summ' Logic.eq_refl c k t e1 e2).
  1,2: inversion Hp ; rewrite -H0 // in Hsumm ; clear Hp H0 summ.
  1,2: destruct (c == v') ; last by apply IHpp, Hsumm.
  1,2: inversion Hsumm ; split ; last by split ; reflexivity.
  + by left ; reflexivity.
  + by right ; reflexivity.
Qed.

Fixpoint array_elements_are_Etbd (ar : array_expr) (t : ftype) : bool :=
   match ar with
   | Aone (Etobedefined t') => t==t'
   | Acons (Etobedefined t') ar' => (t==t') && array_elements_are_Etbd ar' t
   | _ => false
   end.

Lemma Etbd_part_is_Etbd :
   forall (t : ftype) (n : nat),
      match select_part t (Etobedefined t) n with
      | Some (_, Etobedefined _)
      | None => True
      | _ => False
      end
with Btbd_part_is_Etbd :
   forall (ff : ffield) (n : nat),
      match select_bundle_part ff (make_bundle_tobedefined ff) n with
      | Some (_, Etobedefined _)
      | None => True
      | _ => False
      end.
Proof.
induction t ; simpl.
* trivial.
* intro.
  assert (Haie: match make_array_tobedefined t n return Prop with
          | Some ar => array_elements_are_Etbd ar t
          | None => True
          end).
        induction n ; simpl ; first by trivial.
        destruct n ; first by apply eq_refl.
        destruct (make_array_tobedefined t n.+1) ; last by done.
        simpl ; rewrite eq_refl andTb //.
  destruct (make_array_tobedefined t n) as [ar|] ; last by done.
  assert (Hselectie: forall (n1 : nat) (ar1 : array_expr),
                array_elements_are_Etbd ar1 t
             ->
                match select_array_element ar1 n1 with
                | Some (Etobedefined t') => t==t'
                | None => true
                | _ => false
                end).
        induction n1.
        + destruct ar1 ; intro Haie1 ; simpl ; first by exact Haie1.
          destruct h ; try (by exact Haie1).
          move /andP : Haie1 => [Haie1 _] ; by exact Haie1.
        + destruct ar1 ; intro Haie1 ; simpl ; first by reflexivity.
          simpl in Haie1 ; destruct h ; try by done.
          apply IHn1.
          move /andP : Haie1 => [_ Haie1] ; by exact Haie1.
  specialize (Hselectie (n0 %/ number_of_parts t) ar Haie).
  destruct (select_array_element ar (n0 %/ number_of_parts t)) ; try by done.
  destruct h ; try by done.
  move /eqP : Hselectie => Hselectie ; rewrite -Hselectie ; clear Hselectie f.
  by apply IHt.
* by apply Btbd_part_is_Etbd.
(* Btbd_part_is_Etbd *)
induction ff ; first by simpl.
* intro n ; simpl.
  destruct f.
  1,2: destruct (n < number_of_parts f0) ; last by apply IHff.
  1,2: specialize (Etbd_part_is_Etbd f0 n).
  + destruct (select_part f0 (Etobedefined f0) n) as [[[]]|] ; by done.
  + exact Etbd_part_is_Etbd.
Qed.

Lemma PortSumm_is_well_founded :
   forall (pp : seq hfport) (summ : summaryType),
         PortSumm pp = Some summ
      ->
         well_founded (depends_on summ).
intros pp summ Hps p2.
apply Acc_intro.
intros p1 H.
contradict H.
generalize (PortSumm_is_tobedefined pp summ Hps (fst p1)) ; intro Htbd.
unfold depends_on.
destruct (summ (fst p1)) as [[[[k t] e1] e2]|] ; last by done.
specialize (Htbd k t e1 e2 Logic.eq_refl).
destruct Htbd as [[Hk|Hk] [He1 He2]] ; rewrite He1 He2 Hk // ; clear He1 He2 Hk k e1 e2.
1,2: destruct (summ (fst p2)) as [[[[_ t2] _] _]|] ; last by done.
1,2: generalize (Etbd_part_is_Etbd t (snd p1)) ; intro Heie.
1,2: destruct (select_part t (Etobedefined t) (snd p1)) as [[[] []]|]; by done.
Qed.

(* This lemma cannot be proved.
Lemma StmtSumm_is_well_founded :
   forall (ss : hfstmt_seq) (old_summ new_summ : summaryType),
         well_founded (depends_on old_summ)
      ->
         StmtSumm old_summ ss = Some new_summ
      ->
         well_founded (depends_on new_summ).
induction ss ; intros old_summ new_summ Hoswf Hss.
* simpl in Hss.
  injection Hss ; clear Hss ; intro Hss.
  rewrite -Hss //.
* destruct h ; simpl in Hss.
  + (* Sskip *)
    by apply (IHss old_summ _ Hoswf Hss).
  + (* Wire *)
    apply (IHss (fun v : var => if v == s
                                then Some (Wire, f, Etobedefined f, Etobedefined f)
                                else old_summ v) new_summ) ;
          last by apply Hss.
    clear IHss Hss new_summ ss.
    unfold well_founded.
    apply well_founded_ind with (R := (depends_on old_summ)) ;
          first (by apply Hoswf).
    intros p2 IHdepends_on.
    apply Acc_intro.
    intros p1 H.
    apply IHdepends_on.
    destruct (fst p1 == s) eqn: Hp1s.
    - contradict H.
      unfold depends_on.
      rewrite Hp1s // ; clear Hp1s.
      destruct (if fst p2 == s
                then Some (Wire, f, Etobedefined f, Etobedefined f)
                else old_summ (fst p2)) as [[[[]]]|] ; last by done.
      generalize (Etbd_part_is_Etbd f (snd p1)) ; intro Hp1.
      destruct (select_part f (Etobedefined f) (snd p1)) as [[[] []]|] ; by done.
    - unfold depends_on in H ; rewrite Hp1s // in H ; clear Hp1s.
      unfold depends_on.
      destruct (old_summ (fst p1)) as [[[[[] t1] er1] ew1]|] ; try by done.
      destruct (fst p2 == s) eqn: Hp2s.
      * contradict H.
        Now we need that p2 does not appear anywhere in expressions.
        We can prove this because s was not a defined identifier before.
        (Basically, an expression may only depend on defined identifiers---so we need to check the summary for that.)
*)

(* Lemma: If iterate has a fixed point, then it will be reached in at most (path_length ss) steps.
How could one prove such a lemma?

The inductive property could be something like:
If the longest path to component c is ≤ n steps, then iterate will stabilize the result for c within n steps.
As combinatorial cycles are forbidden, every path is simple and finite, and it is at most (path_length ss) steps long.

* define path of connections
* state that there are no cycles in these paths (can be assumed, does not need to be proven)
* therefore all paths are finite *)

