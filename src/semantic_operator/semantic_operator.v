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
From mathcomp Require Import fintype finfun choice fingraph.

(* abstract syntax of HiFIRRTL *)

(******************************)
(*         identifiers        *)
(******************************)

Variable var : choiceType.

(* We may need the following fact that var is infinite.
   The formulation will allow any finfun defined on a subset of var easily
   to find a var that is not in the domain. 

   xchoose (var_is_infinite (domain of summary)) *)
Hypothesis var_is_infinite : forall s : seq var, exists v : var, v \notin s.

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

(* equality of orientations is decidable *)
Lemma forient_eq_dec (x y : forient) : {x = y} + {x <> y}.
Proof. decide equality. Qed.

(* Boolean equality of orientations *)
Definition forient_eqn (x y : forient) : bool :=
  match x, y with
  | Source, Source
  | Sink, Sink
  | Duplex, Duplex
  | Passive, Passive
  | Illegal_orient, Illegal_orient => true
  | _, _ => false
  end.

(* reflection predicate for orientations *)
Lemma forient_eqP : forall (x y : forient), reflect (x = y) (forient_eqn x y).
  Proof.
    destruct x, y ; simpl forient_eqn ;
          try (apply ReflectF ; discriminate) ;
          try (apply ReflectT ; reflexivity).
  Qed.

(* eqType for orientations *)
Definition forient_eqMixin := EqMixin forient_eqP.
Canonical forient_eqType := Eval hnf in EqType forient forient_eqMixin.

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


(**********************************)
(* connection summary, dependency *)
(**********************************)


(* A connection summary is a finite function that indicates for every component some information.
   It is used to define the context of an expression and later to give the semantics
   of a module. *)

Definition summaryType_func (dom : seq var) : Type := {ffun (seq_sub dom) -> kind * ftype * hfexpr * hfexpr}.
(* The information given per component is:
   kind of the component, datatype of the component,
   then an expression for the unflipped parts of the component (parts of this expression that correspond to flipped parts of the component are ignored),
   then an expression for every flipped subfield that can be written. *)

(* We explicitly include the domain of the summary to make it easier to handle. 
   So our connection summaries are actually dependent pairs: *)
Definition summaryType := { dom : seq var & summaryType_func dom }.

(* empty_summary is the empty function, defined on the empty sequence of variables *)
Definition empty_summary : summaryType := existT summaryType_func [::] (ffun0 (card_seq_sub (s := @nil var) is_true_true)).

(* Definition is_sub_summary (oldsumm newsumm : summaryType) : Prop := is_subset (projT1 oldsumm) (projT1 newsumm). *)

(* function application: look up the value assoctiated with v in dict *)
Definition app_summ_p (dict : summaryType) (v : var) (p : v \in projT1 dict) : kind * ftype * hfexpr * hfexpr :=
    projT2 dict (SeqSub p).

Definition app_summ (summ : summaryType) (v : var) : option (kind * ftype * hfexpr * hfexpr) :=
match insub (sT := (seq_sub (projT1 summ))) v with
| Some w => Some (projT2 summ w)
| None => None
end.

(* Some alternative definitions follow.
The above definition has the advantage that there exists a proof rule for insub,
namely insubP, that allows us to easily formulate correctness properties.
The alternatives below have some proof dependencies that make it difficult to handle.

Definition app_summ_alt (summ : summaryType) (v : var) :  kind * ftype * hfexpr * hfexpr * (v \in projT1 summ) + (v \notin projT1 summ) :=
    (if v \in projT1 summ as b 
        return v \in projT1 summ = b -> kind * ftype * hfexpr * hfexpr * (v \in projT1 summ) + (v \notin projT1 summ)
     then fun p => inl (projT2 summ (SeqSub p), p)
     else fun p => inr (negbT p)) Logic.eq_refl.

Lemma app_summ_alt_some {summ : summaryType} {v : var} :
    v \in projT1 summ -> app_summ_alt summ v.
Proof.
intro Hvs.
destruct (app_summ_alt summ v) as [p | Hvns].
(* left branch *)
  by done.
(* right branch *)
  exfalso.
  by rewrite Hvs // in Hvns.
Qed.

Lemma app_summ_alt_none {summ : summaryType} {v : var} :
    v \notin projT1 summ -> ~~app_summ_alt summ v.
Proof.
intro Hvns.
destruct (app_summ_alt summ v) as [[kfee Hvs]|p].
(* left branch *)
  exfalso.
  by rewrite Hvs // in Hvns.
(* right branch *)
  by done.
Qed.

Definition app_summ' (summ : summaryType) (v : var) : option (kind * ftype * hfexpr * hfexpr) :=
    match app_summ_alt summ v with
    | inl (kfee, _) => Some kfee
    | inr _ => None
    end.

Lemma app_summ'_some {summ : summaryType} {v : var} :
    v \in projT1 summ -> app_summ' summ v.
Proof.
intro Hvs.
unfold app_summ'.
destruct (app_summ_alt summ v) as [[kfee _] | Hvns].
(* left branch *)
  by done.
(* right branch *)
  by rewrite Hvs // in Hvns.
Qed.

Lemma app_summ'_none {summ : summaryType} {v : var} :
    v \notin projT1 summ -> ~~app_summ' summ v.
Proof.
intro Hvns.
unfold app_summ'.
destruct (app_summ_alt summ v) as [[kfee Hvs]|p].
(* left branch *)
  by rewrite Hvs // in Hvns.
(* right branch *)
  by done.
Qed.

Lemma notin_cons_imp [T : eqType] (y : T) (s : seq T) (x : T) :
    x != y -> x \notin s -> x \notin y :: s.
Proof.
intros Hxnoty Hxnis.
by rewrite in_cons negb_or Hxnoty Hxnis //.
Qed.

Definition notin_cons' [T : eqType] (y : T) (s : seq T) (x : T) :=
    eq_ind_r (fun b : bool => ~~ b = (x != y) && (x \notin s))
             (eq_ind_r (fun b : bool => b = (x != y) && (x \notin s)) 
                       Logic.eq_refl
                       (negb_or (x == y) (x \in s)))
             (in_cons y s x).
*)

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
                    then match type_of_hfexpr Passive c dict, type_of_hfexpr o e1 dict, type_of_hfexpr o e2 dict with
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
  | Eid v => match app_summ dict v with
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

Lemma orientation_cannot_change_type_of_hfexpr (o1 o2 : forient) (e : hfexpr) (summ : summaryType) :
    match type_of_hfexpr o1 e summ, type_of_hfexpr o2 e summ with
    | Some t1, Some t2 => t1 == t2
    | _, _ => true
    end
with orientation_cannot_change_type_of_array_expr (o1 o2 : forient) (ar : array_expr) (summ : summaryType) :
    match type_of_array_expr o1 ar summ, type_of_array_expr o2 ar summ with
    | Some t1, Some t2 => t1 == t2
    | _, _ => true
    end
with orientation_cannot_change_type_of_bundle_expr (o1 o2 : forient) (bu : bundle_expr) (summ : summaryType) :
    match type_of_bundle_expr o1 bu summ, type_of_bundle_expr o2 bu summ with
    | Some t1, Some t2 => t1 == t2
    | _, _ => true
    end.
Proof.
* clear orientation_cannot_change_type_of_hfexpr.
  induction e ; simpl.
  + (* Econst *)
    by destruct (readable_orient o1), (readable_orient o2) ; done.
  + (* Ecast *)
    by destruct (readable_orient o1), (readable_orient o2) ;
       try done ;
       destruct u, (type_of_hfexpr Passive e summ) as [[[| | | |]| |]|] ;
       done.
  + (* Eunop *)
    by destruct (readable_orient o1), (readable_orient o2) ;
       try done ;
       destruct e, (type_of_hfexpr Passive e0 summ) as [[[| | | |]| |]|] ;
       try done ;
       try (by destruct (n0 <= n < n1) ; done) ;
       destruct (n <= n0) ; done.
  + (* Ebinop *)
    by destruct (readable_orient o1), (readable_orient o2) ;
       try done ;
       destruct e1, (type_of_hfexpr Passive e2 summ) as [[[| | | |]| |]|],
                    (type_of_hfexpr Passive e3 summ) as [[[| | | |]| |]|] ;
       done.
  + (* Emux *)
    clear IHe1.
    destruct (readable_orient o1), (readable_orient o2) ;
    try done ;
    destruct (type_of_hfexpr Passive e1 summ) as [[[[|[|]]| | | |]| |]|] ;
    try done.
    1-2: destruct (type_of_hfexpr o1 e2 summ) as [|] ; last by done.
    1-2: destruct (type_of_hfexpr o1 e3 summ) as [|] ; last by done.
    1-2: destruct (type_of_hfexpr o2 e2 summ) as [|] ; last (by destruct (unified_type f f0) ; done).
    1-2: destruct (type_of_hfexpr o2 e3 summ) as [|] ; last (by destruct (unified_type f f0) ; done).
    1-2: move /eqP : IHe2 => IHe2 ; subst f1 ;
         move /eqP : IHe3 => IHe3 ; subst f2 ;
         destruct (unified_type f f0) ; done.
  + (* Eref *)
    destruct (type_of_href h summ) as [[[| | | |] t]|] ;
    try done ;
    destruct o1 ; try done ;
    destruct o2 ; done.
  + (* Earray *)
    by apply orientation_cannot_change_type_of_array_expr.
  + (* Ebundle *)
    by apply orientation_cannot_change_type_of_bundle_expr.
  + (* Etobedefined, Eundefinedonpurpose *)
    1-2: destruct o1 ; try done ;
         destruct o2 ; try done ;
         destruct (is_passive f) ; done.
* clear orientation_cannot_change_type_of_array_expr.
  induction ar ; simpl.
  + (* Aone *)
    specialize (orientation_cannot_change_type_of_hfexpr o1 o2 h summ).
    destruct (type_of_hfexpr o1 h summ), (type_of_hfexpr o2 h summ) ; try done.
    move /eqP : orientation_cannot_change_type_of_hfexpr => orientation_cannot_change_type_of_hfexpr ;
    subst f0 ; done.
  + (* Acons *)
    specialize (orientation_cannot_change_type_of_hfexpr o1 o2 h summ).
    destruct (type_of_hfexpr o1 h summ), (type_of_hfexpr o2 h summ) ;
          try done ;
          last by destruct (type_of_array_expr o1 ar summ) as [[| |]|] ;
               try done ;
               destruct (unified_type f f0) ; done.
    move /eqP : orientation_cannot_change_type_of_hfexpr => orientation_cannot_change_type_of_hfexpr ;
    subst f0.
    destruct (type_of_array_expr o1 ar summ) as [[|ta1 n1|]|] ; try done.
    destruct (type_of_array_expr o2 ar summ) as [[|ta2 n2|]|] ; try by (destruct (unified_type f ta1) ; done).
    move /eqP : IHar => IHar ; inversion IHar ; subst ta2 n2.
    destruct (unified_type f ta1) ; done.
* (* orientation_cannot_change_type_of_bundle_expr *)
  clear orientation_cannot_change_type_of_bundle_expr.
  induction bu ; simpl ; first by done.
  destruct (type_of_bundle_expr o1 bu summ) as [[| |ff1]|], (type_of_bundle_expr o2 bu summ) as [[| |ff2]|] ;
        try done ;
        (destruct f ;
         first try (by destruct (type_of_hfexpr (flip_orient o1) h summ) ; try done ;
                       destruct (type_of_hfexpr (flip_orient o2) h summ) ; done) ;
         last  try (by destruct (type_of_hfexpr o1 h summ) ; try done ;
                       destruct (type_of_hfexpr o2 h summ) ; done)).
  1-2: move /eqP : IHbu => IHbu ; inversion IHbu ; subst ff2.
  + (* Flipped *)
    specialize (orientation_cannot_change_type_of_hfexpr (flip_orient o1) (flip_orient o2) h summ).
    destruct (type_of_hfexpr (flip_orient o1) h summ) ; last by done.
    destruct (type_of_hfexpr (flip_orient o2) h summ) ; last by done.
    move /eqP : orientation_cannot_change_type_of_hfexpr => orientation_cannot_change_type_of_hfexpr ;
    subst f0 ; done.
  + (* Nflip *)
    specialize (orientation_cannot_change_type_of_hfexpr o1 o2 h summ).
    destruct (type_of_hfexpr o1 h summ) ; last by done.
    destruct (type_of_hfexpr o2 h summ) ; last by done.
    move /eqP : orientation_cannot_change_type_of_hfexpr => orientation_cannot_change_type_of_hfexpr ;
    subst f0 ; done.
Qed.

(* dependency relation -- to avoid creating cyclic dependencies.
   However, we cannot use "well_founded (depends_on summ)" just anywhere
   because this is in Prop and not in bool.  So, instead we will use
   finite graphs to define acyclicity.  This is also the main reason
   why we insist on summaries to be finite functions. *)

(* A correct program has this property: there is never a combinatorial loop, i.e. a ground-level component part that is connected indirectly to itself.
   (One does not look further down than ground-level component parts, e.g. when doing bit manipulation.)

   This can be expressed as follows:
   - define a relation between ground-level component parts; if the expression for part p1 contains a reference to part p2, then p1 depends on p2
     (except if p1 is (part of) a register, then it's not a combinatorial dependency).
   - state that this relation (or its transitive closure) is well-founded.
     If a module would lead to a non-well-founded relation, it is illegal and has no semantics.

   - To define this relation, one has to assign identifiers to ground-level parts of every component.
*)

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

(* calculates the size of array s *)
Fixpoint array_size (s : array_expr) : nat :=
  match s with
  | Aone _ => 1
  | Acons _ s' => array_size s' + 1
  end.

Fixpoint number_of_parts_of_expr (e : hfexpr) (summ : summaryType) : option nat :=
    match e with
    | Econst _ _ => Some 1
    | Ecast _ _ => (* if number_of_parts_of_expr e' != Some 1 then None else *)
                   Some 1
    | Eprim_unop _ _ => (* if number_of_parts_of_expr e' != Some 1 then None else *)
                        Some 1
    | Eprim_binop _ _ _ => (* if (number_of_parts_of_expr e1 != Some 1) || (number_of_parts_of_expr e2 != Some 1) then None else *)
                           Some 1
    | Emux _ e1 _ => (* if (number_of_parts_of_expr c != Some 1) || (number_of_parts_of_expr e1 != number_of_parts_of_expr e2) then None else *)
                     number_of_parts_of_expr e1 summ
    | Eref r => match type_of_href r summ with
                | Some (_, ft) => Some (number_of_parts ft)
                | None => None
                end
    | Earray ar => number_of_parts_of_array ar summ
    | Ebundle bu => number_of_parts_of_bundle bu summ
    | Etobedefined t => Some (number_of_parts t)
    | Eundefinedonpurpose t => Some (number_of_parts t)
    end
with number_of_parts_of_array (ar : array_expr) (summ : summaryType) : option nat :=
    match ar with
    | Aone e => number_of_parts_of_expr e summ
    | Acons e _ => match number_of_parts_of_expr e summ with
                   | Some s => Some (s * array_size ar)
                   | None => None
                   end
    end
with number_of_parts_of_bundle (bu : bundle_expr) (summ : summaryType) : option nat :=
    match bu with
    | Bnil => Some 0
    | Bflips _ _ e bu' => match number_of_parts_of_expr e summ, number_of_parts_of_bundle bu' summ with
                          | Some s1, Some s2 => Some (s1 + s2)
                          | _, _ => None
                          end
    end.

Definition parts_of (summ : summaryType) : seq (var * nat) :=
    (* flatten [seq parts_of_component summ v | v <- (enum [finType of seq_sub (projT1 summ)])]. *)
    [seq (val v, i) | v <- (enum [finType of seq_sub (projT1 summ)]), 
                      i <- iota 0 (number_of_parts (snd (fst (fst (projT2 summ v)))))].

(* type of all ground-type parts of components.
   The graph of dependencies uses this as its vertex set. *)
Definition component_part (summ : summaryType) : Type := [finType of seq_sub (parts_of summ)].

Definition is_defined_part (summ : summaryType) (p : var * nat) : bool :=
    match app_summ summ (fst p) with
    | Some (_, t, _, _) => (snd p) < number_of_parts t
    | None => false
    end.

(* Every component part in the sequence (parts_of summ) is defined *)
Lemma parts_of_is_defined (summ : summaryType) :
    forall p : var * nat, (p \in parts_of summ) ->
        is_defined_part summ p.
Proof.
intros [v n].
rewrite /parts_of.
move /flattenP => [s /mapP [v' Hv' Hs] Hvns].
assert (val v' = v).
      rewrite Hs in Hvns.
      move /mapP : Hvns => [vi _ Hvns2].
      apply pair_equal_spec in Hvns2.
      by rewrite (proj1 Hvns2) //.
subst v.
rewrite /is_defined_part /fst /snd /app_summ /insub.
destruct idP ;
      last by contradict n0 ;
              rewrite enumT unlock in Hv' ; simpl in Hv' ;
              rewrite /seq_sub_enum mem_undup mem_pmap /insub in Hv' ;
              move /mapP : Hv' => [w _ Hsome] ;
              (destruct idP in Hsome ; last by discriminate) ;
              inversion Hsome ;
              apply valP.
rewrite (val_inj (SubK (seq_sub (projT1 summ)) i)).
destruct (projT2 summ v') as [[[k t] enf] efl].
rewrite Hs /snd /fst in Hvns.
move /mapP : Hvns => [n' Hn_iota Hnn'].
apply pair_equal_spec in Hnn'.
rewrite -(proj2 Hnn') mem_iota // in Hn_iota.
Qed.

(* All defined parts are in parts_of *)
Lemma defined_is_in_parts_of (summ : summaryType) :
    forall p : var * nat, is_defined_part summ p ->
        p \in parts_of summ.
Proof.
rewrite /is_defined_part /fst /snd.
intros [v n] Hn.
destruct (app_summ summ v) as [[[[k t] enf] efl]|] eqn: Has ;
      last by done.
rewrite /parts_of.
apply (introT flattenP).
exists [seq (v, i) | i <- iota 0 (number_of_parts t)] ;
      last by (rewrite mem_map ;
                    last by intros x1 x2 ; apply pair_equal_spec) ;
              rewrite mem_iota //.

rewrite /app_summ /insub in Has.
destruct idP in Has ; last by discriminate.
inversion Has as [Has'] ; clear Has.
apply (introT mapP).
exists (Sub (sT := seq_sub (projT1 summ)) v i).
* rewrite enumT unlock ; simpl.
  by apply mem_seq_sub_enum.
* rewrite Has' SubK /fst /snd //.
Qed.

(* Select the ith array element from array expression ar *)
Fixpoint select_array_element (ar : array_expr) (i : nat) : option hfexpr :=
  match ar, i with
  | Aone e, 0 => Some e
  | Aone _, _ => None
  | Acons e _, 0 => Some e
  | Acons _ ar', i'.+1 => select_array_element ar' i'
  end.

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

(* splits a multiplexer expression "Emux c ar1 ar2", where ar1 and ar2 are array expressions,
   into an array expression containing as many multiplexers as there are elements
   (so that later one part of the array can be extracted or changed). *)
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

(* splits an expression that has an array type into an array expression over its parts
   (so that later one part of that array can be extracted or changed) *)
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

(* splits a multiplexer expression "Emux c b1 b2", where b1 and b2 are bundle expressions,
   into a bundle expression containing as many multiplexers as there are elements
   (so that later one part of that bundle can be extracted or changed). *)
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
   (so that later one part of that bundle can be extracted or changed) *)
Fixpoint split_ref_into_subfields (r : href) (ff : ffield) : bundle_expr :=
  match ff with
  | Fnil => Bnil
  | Fflips v fl t ff' => Bflips v fl (Eref (Esubfield r v)) (split_ref_into_subfields r ff')
  end.

(* Make a bundle expression that contains suitable "Etobedefined t" expressions *)
Fixpoint make_bundle_tobedefined (ff : ffield) : bundle_expr :=
  match ff with
  | Fnil => Bnil
  | Fflips v fl t ff' => Bflips v fl (Etobedefined t) (make_bundle_tobedefined ff')
  end.

(* Make a bundle expression that contains suitable "Eundefinedonpurpose t" expressions *)
Fixpoint make_bundle_undefinedonpurpose (ff : ffield) : bundle_expr :=
  match ff with
  | Fnil => Bnil
  | Fflips v fl t ff' => Bflips v fl (Eundefinedonpurpose t) (make_bundle_undefinedonpurpose ff')
  end.

(* Split an expression that has a bundle type into a bundle expression over its parts
   (so that later one part of that bundle can be extracted or changed) *)
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

(* From expression e, which has type t, select part p.
   It is assumed that p is in range. *)
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

Lemma type_and_part_of_subfield :
    forall (ff : ffield) (v : var),
        match part_of_subfield ff v, type_of_subfield ff v with
        | Some (tp, _), Some (_, ty) => tp == ty
        | None, None => true
        | _, _ => false
        end.
Proof.
intros ff v.
induction ff ; simpl ; first by done.
destruct (v == s) ; first by rewrite eq_refl.
destruct (part_of_subfield ff v) as [[ft' i]|],
         (type_of_subfield ff v) as [[_ ty]|] ;
    by done.
Qed.

Fixpoint href_depends_on {summ : summaryType} (r : href) (p2 : component_part summ) (error_result : option (ftype * nat)) : option (ftype * nat) :=
(* checks whether reference r depends on p2.
The result is Some (t, i1), meaning that reference r has type t and describes the parts [i1, i1 + number_of_parts t) of the base reference of p2.
The result only looks at the reference, not at the expression in the subaccess part. 
If the result is None, there is no (direct) dependency;
however, the *value* of r could still be dependent on p2.
But that should be handled by a transitive closure of expr_depends_on.

If some type error happens, error_result is returned. *)
  match r with
  | Eid v => if v==fst (val p2)
             then match (app_summ summ v) with
                  | Some (_, t, _, _) => Some (t, 0)
                  | None => error_result (* cannot happen *)
                  end
             else None
  | Esubfield r' v => match href_depends_on r' p2 (Some (Gtyp (Fuint 0), 0)) with
                      | Some (Btyp ff, f) => match part_of_subfield ff v with
                                             | Some (t, offset) => if f + offset <= snd (val p2) < f + offset + number_of_parts t
                                                                   then Some (t, f + offset)
                                                                   else None
                                             | None => None
                                             end
                      | Some _ => error_result
                      | None => None
                      end
  | Esubindex r' i => match href_depends_on r' p2 (Some (Gtyp (Fuint 0), 0)) with
                      | Some (Atyp t' siz, f) => let elementsize := number_of_parts t'
                                                 in if f + i * elementsize <= snd (val p2) < f + (i+1) * elementsize
                                                    then Some (t', f + i * elementsize)
                                                    else None
                      | Some _ => error_result
                      | None => None
                      end
  | Esubaccess r' e' => match href_depends_on r' p2 (Some (Gtyp (Fuint 0), 0)) with
                        | Some (Atyp t' siz, f) => let elementsize := number_of_parts t'
                                                   in let i := (snd (val p2) - f) %/ elementsize (* we assume that the accessed element contains p2 *)
                                                      in Some (t', f + i * elementsize)
                        | Some _ => error_result
                        | None => None
                        end
  end.

Fixpoint subaccesses_in_href_type_correct (r : href) (summ : summaryType) : bool :=
    match r with
    | Eid _ => true
    | Esubfield r' _
    | Esubindex r' _ => subaccesses_in_href_type_correct r' summ
    | Esubaccess r' e => match type_of_hfexpr Passive e summ with
                         | Some (Gtyp (Fuint _))
                         | Some (Gtyp (Fsint _)) => subaccesses_in_href_type_correct r' summ
                         | _ => false
                         end
    end.

(* checks whether a href overlaps with a component part.
   The result is Some (begin, end, type) if the reference may refer to component parts (fst p, begin), (fst p, begin+1), ..., (fst p, end-1),
   and this overlaps with component part p. 
   If an error happens, a nonsensical result (a Gtyp having size 99) is returned. *)
Fixpoint href_overlaps {summ : summaryType} (r : href) (p : component_part summ) : option (nat * nat * ftype) :=
    match r with
    | Eid v => if (v == fst (val p))
               then match app_summ summ v with
                    | Some (_, t, _, _) => Some (0, number_of_parts t, t)
                    | _ => Some (0, 99, Gtyp (Fuint 0)) (* should not happen *)
                    end
               else None
    | Esubfield r' v => match href_overlaps r' p with
                        | Some (b, e, Btyp ff) => match part_of_subfield ff v with
                                                  | Some (ft, offset) => if b + offset <= snd (val p) < b + offset + number_of_parts ft
                                                                         then Some (b + offset, b + offset + number_of_parts ft, ft)
                                                                         else None
                                                  | None => None
                                                  end
                        | Some _ => Some (0, 99, Gtyp (Fuint 0)) (* error *)
                        | None => None
                        end
    | Esubindex r' n => match href_overlaps r' p with
                        | Some (b, e, Atyp t' m) => if (n < m) && (b + n * number_of_parts t' <= snd (val p) < b + n.+1 * number_of_parts t')
                                                    then Some (b + n * number_of_parts t', b + n.+1 * number_of_parts t', t')
                                                    else None
                        | Some _ => Some (0, 99, Gtyp (Fuint 0)) (* error *)
                        | None => None
                        end
    | Esubaccess r' e => match href_overlaps r' p with
                        | Some (b, e, Atyp t' _) => Some (b + (snd (val p) - b) %/ number_of_parts t' * number_of_parts t', b + ((snd (val p) - b) %/ number_of_parts t').+1 * number_of_parts t', t')
                        | Some _ => Some (0, 99, Gtyp (Fuint 0)) (* error *)
                        | None => None
                        end
    end.

Fixpoint base_ref (r : href) : var :=
    match r with
    | Eid v => v
    | Esubfield r' _ | Esubindex r' _ | Esubaccess r' _ => base_ref r'
    end.

Lemma href_overlaps_is_correct {summ : summaryType} :
    forall (r : href) (p : component_part summ),
                (base_ref r <> fst (val p) -> href_overlaps r p = None)
            /\
                (base_ref r = fst (val p) ->
                match href_overlaps r p with
                | Some (0, _.+2, Gtyp (Fuint 0)) => type_of_href r summ == None
                | Some (b, e, t) => (b <= snd (val p) < e) &&
                                    (b + number_of_parts t == e) &&
                                    match type_of_href r summ with
                                    | Some (_, t') => t == t'
                                    | None => ~~subaccesses_in_href_type_correct r summ
                                    end
                | None => true
                end).
Proof.
intros r p.
induction r ; simpl ; split ; intro Hbr.
* (* Eid, first part *)
  rewrite (introF eqP Hbr) //.
* (* Eid, second part *)
  rewrite (introT eqP Hbr) //.
  generalize (valP p) ; move /flattenP => [ps /mapP [p1 _ Hp2] Hp3].
  subst ps.
  move /mapP : Hp3 => [p2 Hp1 Hp2].
  rewrite /app_summ Hbr Hp2 /fst valK.
  destruct (projT2 summ p1) as [[[k t] enf] efl].
  rewrite mem_iota add0n /fst /snd in Hp1.
  destruct (number_of_parts t) as [|[|]] eqn: Hnp.
  + (* number_of_parts == 0 *)
    by rewrite ltn0 andbF // in Hp1.
  + (* number_of_parts == 1 *)
    rewrite /snd Hp1 add0n eq_refl andTb andTb.
    destruct k ; done.
  + (* number_of_parts >= 2 *)
    destruct t as [[[|]| | | |]| |] ; 
          first ((* t = Gtyp (Fuint 0) *)
                 by discriminate Hnp) ;
          rewrite /snd Hp1 add0n eq_refl andTb andTb ;
          destruct k ; done.
* (* Esubfield, Esubindex and Esubaccess, first part *)
  1,3,5: destruct IHr as [IHr _] ; specialize (IHr Hbr) ;
         by rewrite IHr //.
* (* Esubfield, second part *)
  1-3: destruct IHr as [_ IHr] ; specialize (IHr Hbr).
  1-3: destruct (href_overlaps r p) as [[[b e] t]|] eqn: Hro ; last by done.
  (* e should be larger than 0: *)
  1-3: destruct e as [|e'] ;
             first by destruct b ; rewrite ltn0 andbF andFb andFb // in IHr.
  (* t should be Btyp _: *)
  1-3: destruct t as [[[|]| | | |]|eltyp arsiz|ff] ;
       try by destruct b, e', (type_of_href r summ) as [[o t']|] ; try (by done) ;
              move /andP : IHr => [_ /eqP IHr] ; subst t' ; done.
  (* We now have that t is a Btyp: *)
  assert (IHr' : (b <= snd (val p) < e'.+1) &&
                 (b + number_of_parts (Btyp ff) == e'.+1) &&
                 match type_of_href r summ with
                 | Some (_, t') => Btyp ff == t'
                 | None => ~~ subaccesses_in_href_type_correct r summ
                 end) by (destruct b as [|b'] ; first destruct e' as [|e''] ; exact IHr).
  clear IHr.
  destruct (type_of_href r summ) as [[o t']|].
  + (* type_of_href r summ = Some (o, t') *)
    move /andP : IHr' => [IHr /eqP IHr2] ; subst t' ;
    generalize (type_and_part_of_subfield ff s) ; intro Htypa ;
    destruct (part_of_subfield ff s) as [[ft offset]|] ; last (by done) ;
    destruct (type_of_subfield ff s) as [[fl ty]|] ; last (by done) ;
    move /eqP : Htypa => Htypa ; subst ty.
    destruct (b + offset <= snd (ssval p) < b + offset + number_of_parts ft) eqn: Hoffset ;
    rewrite Hoffset //.
    rewrite Hoffset eq_refl andTb andTb.
    destruct fl.
    1,2: destruct (b + offset) ; last (by done).
    1,2: destruct (0 + number_of_parts ft) as [|[|]] eqn: Hnop ; try by done.
    1,2: destruct ft as [[[|]| | | |]| |] ; by done.
  + (* type_of_href r summ = None *)
    move /andP : IHr' => [IHr IHr2] ;
    destruct (part_of_subfield ff s) as [[ft offset]|] ; last by done.
    destruct (b + offset <= snd (ssval p) < b + offset + number_of_parts ft) eqn: Hoffset ;
    rewrite Hoffset // Hoffset eq_refl andTb andTb IHr2 eq_refl.
    destruct (b + offset) ; last by done.
    destruct (0 + number_of_parts ft) as [|[|]] ; try by done.
    destruct ft as [[[|]| | | |]| |] ; by done.
* (* Esubindex, first part -- already handled *)
* (* Esubindex, second part *)
  (* We already ensured that t is Atyp eltyp arsiz above. *)
  1,2: assert (IHr' : (b <= snd (val p) < e'.+1) &&
                 (b + number_of_parts (Atyp eltyp arsiz) == e'.+1) &&
                 match type_of_href r summ with
                 | Some (_, t') => Atyp eltyp arsiz == t'
                 | None => ~~ subaccesses_in_href_type_correct r summ
                 end) by (destruct b as [|b'] ; first destruct e' as [|e''] ; exact IHr).
  1,2: clear IHr.
  destruct (type_of_href r summ) as [[o t']|].
  + (* type_of_href r summ = Some (o, t') *)
    move /andP : IHr' => [IHr /eqP IHr2] ; subst t'.
    destruct (n < arsiz) ; last by done.
    rewrite andTb.
    destruct (b + n * number_of_parts eltyp <= snd (ssval p) < b + n.+1 * number_of_parts eltyp) eqn: Hoffset ;
    rewrite Hoffset // Hoffset eq_refl andTb andbT -addnA -mulSnr eq_refl.
    destruct (b + n * number_of_parts eltyp) eqn: Helt1 ; last by done.
    destruct (b + n.+1 * number_of_parts eltyp) as [|[|]] eqn: Helt2 ; try by done.
    destruct eltyp as [[[|]| | | |]| |] ; try done.
    (* The remaining case was to handle an error: *)
    simpl in Helt1, Helt2.
    move /eqP : Helt1 => Helt1.
    rewrite addn_eq0 muln_eq0 orbF in Helt1.
    move /andP : Helt1 => [/eqP Helt1 /eqP Helt1'].
    move /eqP : Helt2 => Helt2.
    rewrite Helt1 Helt1' eqSS // in Helt2.
  + (* type_of_href r summ = None *)
    move /andP : IHr' => [IHr IHr2].
    destruct (n < arsiz) ; last by done.
    rewrite andTb.
    destruct (b + n * number_of_parts eltyp <= snd (ssval p) < b + n.+1 * number_of_parts eltyp) eqn: Hoffset ;
    rewrite Hoffset // Hoffset eq_refl andTb -addnA -mulSnr eq_refl andTb IHr2.
    destruct (b + n * number_of_parts eltyp) ; last by done.
    destruct (b + n.+1 * number_of_parts eltyp) as [|[|]] ; try by done.
    destruct eltyp as [[[|]| | | |]| |] ; by done.
* (* Esubaccess, first part -- already handled earlier *)
* (* Esubaccess, second part *)
  (* We already ensured that t is Atyp eltyp arsiz above. *)
  assert (0 < number_of_parts eltyp).
        move /andP : IHr' => [/andP [/andP [IHr IHr0] /eqP IHr1] _].
        generalize (leq_ltn_trans IHr IHr0) ; intro.
        simpl number_of_parts in IHr1.
        rewrite -IHr1 -addn1 leq_add2l muln_gt0 in H.
        move /andP : H => [_ H] ; done.
  destruct (type_of_href r summ) as [[o t']|].
  + (* type_of_href r summ = Some (Atyp eltyp arsiz) *)
    move /andP : IHr' => [/andP [/andP [IHr IHr0] IHr1] /eqP IHr2] ; subst t'.
    rewrite -(leq_subRL _ IHr) leq_trunc_div -(ltn_subLR _ IHr) (ltn_ceil _ H) andTb andTb -addnA -mulSnr eq_refl andTb.
    destruct (b + (snd (ssval p) - b) %/ number_of_parts eltyp * number_of_parts eltyp) eqn: Hoffset ;
    rewrite Hoffset ;
    last by destruct (type_of_hfexpr Passive h summ) as [[[[|]| | | |]| |]|] ; done.
    destruct (b + ((snd (ssval p) - b) %/ number_of_parts eltyp).+1 * number_of_parts eltyp) as [|[|]] eqn: Hoffset2 ;
    rewrite Hoffset2 ;
    try by destruct (type_of_hfexpr Passive h summ) as [[[[|]| | | |]| |]|] ; done.
    destruct eltyp as [[[|]| | | |]| |] ;
    try by destruct (type_of_hfexpr Passive h summ) as [[[[|]| | | |]| |]|] ; done.
    (* now remains an erroneous case *)
    by rewrite mulSnr addnA Hoffset add0n /number_of_parts // in Hoffset2.
  + (* type_of_href r summ = None *)
    move /andP : IHr' => [/andP [/andP [IHr IHr0] IHr1] IHr2].
    apply negbTE in IHr2.
    rewrite eq_refl -(leq_subRL _ IHr) leq_trunc_div -(ltn_subLR _ IHr) (ltn_ceil _ H) andTb andTb -addnA -mulSnr eq_refl andTb IHr2.
    destruct (b + (snd (ssval p) - b) %/ number_of_parts eltyp * number_of_parts eltyp) eqn: Hoffset ;
    rewrite Hoffset // ;
    last by destruct (type_of_hfexpr Passive h summ) as [[[[|]| | | |]| |]|] ; done.
    destruct (b + ((snd (ssval p) - b) %/ number_of_parts eltyp).+1 * number_of_parts eltyp) as [|[|]] eqn: Hoffset2 ;
    rewrite Hoffset2 // ;
    try by destruct (type_of_hfexpr Passive h summ) as [[[[|]| | | |]| |]|] ; done.
    destruct eltyp as [[[|]| | | |]| |] ; try by done.
    all: by destruct (type_of_hfexpr Passive h summ) as [[[[|]| | | |]| |]|] ; done.
Qed.

Lemma href_depends_on_and_overlaps_agree {summ : summaryType} :
    forall (r : href) (p : component_part summ) (err : option (ftype * nat)),
        match href_depends_on r p err, href_overlaps r p with
        | err', Some (0, _.+2, Gtyp (Fuint 0)) => err' == err
        | Some (ftd, n), Some (b, e, fto) => (ftd == fto) && (n == b) && (n + number_of_parts ftd == e)
        | None, None => true
        | _, _ => false
        end.
Proof.
intros r p ; induction r ; intro err ; simpl.
* (* Eid *)
  destruct (s == fst (ssval p)) eqn: Hs ; rewrite Hs //.
  generalize (parts_of_is_defined summ (val p) (valP p)) ; intro Hp.
  unfold is_defined_part in Hp ; simpl in Hp ; rewrite -(elimT eqP Hs) in Hp.
  destruct (app_summ summ s) as [[[[k t] enf] efl]|] ; last by done.
  rewrite eq_refl andTb eq_refl andTb add0n eq_refl.
  destruct (number_of_parts t) as [|[|]] eqn: Hnop ; try done.
  destruct t as [[[|]| | | |]| |] ; by done.
* (* Esubfield *)
  1-3: specialize (IHr (Some (Gtyp (Fuint 0), 0))).
  1-3: destruct (href_depends_on r p (Some (Gtyp (Fuint 0), 0))) as [[ftd nd]|] eqn: Hdo,
           (href_overlaps r p) as [[[b e] fto]|] eqn: Hro ; try done ;
        last by destruct b ; last done ;
                destruct e as [|[|]] ; try done ;
                destruct fto as [[[|]| | | |]| |] ; done.
  1-3: assert (IHr': (ftd == fto) && (nd == b) && (nd + number_of_parts ftd == e) \/
          exists e, href_overlaps r p = Some (0, e.+2, Gtyp (Fuint 0)))
        by (destruct b ; last (by left ; exact IHr) ;
            destruct e as [|[|e'']] ; try (by left ; exact IHr) ;
            destruct fto as [[[|]| | | |]| |] ; try (by left ; exact IHr) ;
            right ; exists e'' ; exact Hro).
  1-3: destruct IHr' as [IHr'|[e'' IHr']] ;
       last by (rewrite Hro in IHr' ;
                inversion IHr' ; subst b e fto ;
                move /eqP : IHr => IHr ; inversion IHr ; subst ftd nd ;
                destruct err as [[]|] ; done).
  1-3: move /andP : IHr' => [/andP [/eqP IHr1 /eqP IHr2] /eqP IHr3].
  1-3: subst fto b e ; clear IHr.
  1-3: destruct ftd as [|eltype arsize|ff] ; try by destruct err as [[]|] ; rewrite /eq_refl //.
  + (* Esubfield, first part *)
    destruct (part_of_subfield ff s) as [[t offset]|] ; last by done.
    destruct (nd + offset <= snd (ssval p) < nd + offset + number_of_parts t) eqn: Hp ; rewrite Hp //.
    rewrite eq_refl eq_refl eq_refl andTb.
    destruct (nd + offset) ; last by done.
    rewrite add0n.
    destruct (number_of_parts t) as [|[|]] eqn: Hnp ; try by done.
    destruct t as [[[|]| | | |]| |] ; by done.
  + (* Esubindex, first part *)
    rewrite addn1.
    destruct (nd + n * number_of_parts eltype <= snd (ssval p) < nd + n.+1 * number_of_parts eltype) eqn: Hp ;
          rewrite Hp ;
          last by rewrite andbF //.
    assert (Helt_ars : (0 < number_of_parts eltype) && (n < arsize)).
          generalize (href_overlaps_is_correct r p) ; move => [Hcorrf Hcorrt].
          destruct (eq_comparable (base_ref r) (fst (val p))) as [Heq|Heq] ;
                last by rewrite (Hcorrf Heq) // in Hro.
          specialize (Hcorrt Heq) ; clear Hcorrf Heq.
          rewrite Hro in Hcorrt.
          move /andP : Hp => [Hp _].
          apply (leq_ltn_trans (p := nd + number_of_parts (Atyp eltype arsize))) in Hp ;
                first by simpl number_of_parts in Hp ; rewrite ltn_add2l ltn_mul2r // in Hp.
          destruct nd as [|nd'] ;
                last by move /andP : Hcorrt => [/andP [/andP [_ Hcorrt] _] _] ;
                        exact Hcorrt.
          destruct (0 + number_of_parts (Atyp eltype arsize)) as [|[|np'']] ;
                by move /andP : Hcorrt => [/andP [/andP [_ Hcorrt] _] _] ;
                   exact Hcorrt.
    move /andP : Helt_ars => Helt_ars.
    rewrite (proj2 Helt_ars) andTb eq_refl eq_refl andTb andTb -addnA -mulSnr eq_refl.
    destruct (nd + n * number_of_parts eltype) eqn: Hn_parts ; last by done.
    destruct (nd + n.+1 * number_of_parts eltype) as [|[|]] eqn: Hn1_parts ; try by done.
    rewrite mulSnr addnA Hn_parts add0n in Hn1_parts.
    destruct eltype as [[[|]| | | |]| |] ; by done.
  + (* Esubaccess, first part *)
    rewrite eq_refl eq_refl -addnA -mulSnr eq_refl andTb.
    destruct (nd + (snd (ssval p) - nd) %/ number_of_parts eltype * number_of_parts eltype) eqn: Hnp ;
          rewrite Hnp //.
    destruct (nd + ((snd (ssval p) - nd) %/ number_of_parts eltype).+1 * number_of_parts eltype) as [|[|]] eqn: Hnp1 ;
          rewrite Hnp1 //.
    rewrite mulSnr addnA Hnp add0n in Hnp1.
    destruct eltype as [[[|]| | | |]| |] ; by done.
Qed.

(* type_of_href checks that subaccesses are type correct;
   href_depends_on does not check it and returns sometimes a result that makes no sense. *)

Lemma type_of_href_no_error {summ : summaryType} :
    forall (p : component_part summ) (r : href) (err1 err2 : option (ftype * nat)),
        match type_of_href r summ, href_depends_on r p err1, href_depends_on r p err2 with
        | Some (_, tr), Some (t1, n1), Some (t2, n2) => (base_ref r == fst (val p)) &&
                                                        (n1 <= snd (val p) < n1 + number_of_parts t1) &&
                                                        (tr == t1) && (t1 == t2) && (n1 == n2)
        | Some _, None, None => ~~href_overlaps r p
        | Some _, _, _ => false
        | None, None, None => true (* there was some error that href_depends_on did not detect:
                                      it has a type error but does not overlap *)
        | None, res1, res2 => ((res1 == err1) && (res2 == err2)) ||
                              (~~subaccesses_in_href_type_correct r summ &&
                               match res1, res2 with
                               | Some (t1, n1), Some (t2, n2) => (n1 <= snd (val p) < n1 + number_of_parts t1) &&
                                                                 (t1 == t2) && (n1 == n2)
                               | _, _ => false
                               end)
        end.
Proof.
induction r ; simpl ; intros err1 err2.
* (* Eid *)
  destruct (app_summ summ s) as [[[[[| | | |] t] enf] efl]|] eqn: Happ.
  1-6: destruct (s == fst (ssval p)) eqn: Hs ; rewrite Hs //.
  + (* app_summ summ s = Some _ *)
    1-5: rewrite andTb eq_refl eq_refl andbT andbT andbT.
    1-5: specialize (valP p) ; move /flattenP => [p1 /mapP [p2 _ Hp2] Hp3].
    1-5: rewrite Hp2 in Hp3 ; clear Hp2 p1.
    1-5: move /mapP : Hp3 => [p1 Hp3 Hp4].
    1-5: rewrite mem_iota in Hp3.
    1-5: rewrite Hp4 /snd.
    1-5: rewrite Hp4 /fst in Hs.
    1-5: rewrite (elimT eqP Hs) /app_summ valK in Happ.
    1-5: inversion Happ ; by rewrite H0 /fst /snd // in Hp3.
  + (* app_summ summ s = None, s == fst (ssval p)) *)
    by destruct err1, err2 ; rewrite // eq_refl eq_refl //.
* (* Esubfield r s *)
  specialize (IHr (Some (Gtyp (Fuint 0), 0)) (Some (Gtyp (Fuint 0), 0))).
  generalize (href_depends_on_and_overlaps_agree r p (Some (Gtyp (Fuint 0), 0))) ; intro Hagree.
  destruct (type_of_href r summ) as [[o [| |]]|] eqn: Htr.
  1-4: destruct (href_depends_on r p (Some (Gtyp (Fuint 0), 0))) as [[t1 n1]|] eqn: Hdo ; try done.
  + (* type_of_href r summ = Some _ *)
    1-3: rewrite eq_refl eq_refl andbT andbT in IHr.
    1-3: move /andP : IHr => [IHr /eqP IHr'] ; subst t1.
  + (* type_of_href r summ = Some _
       href_depends_on r p ... = Some (Gtyp _, _) or Some (Atyp _ _, _) *)
    1-2: destruct err1, err2 ; by rewrite // eq_refl eq_refl //.
  + (* type_of_href r summ = Some (_, Btyp _)
       href_depends_on r p ... = Some (Btyp _, _) *)
    generalize (type_and_part_of_subfield f s) ; intro Htypa.
    destruct (type_of_subfield f s) as [[[|] tt]|] eqn: Htos,
             (part_of_subfield f s) as [[tp offs]|] eqn: Hpos ; try done.
    1,2: move /eqP : Htypa => Htypa ; subst tt.
    1,2: destruct (n1 + offs <= snd (ssval p) < n1 + offs + number_of_parts tp) eqn: Hn1p ;
            rewrite Hn1p ;
            first by rewrite Hn1p eq_refl eq_refl (proj1 (elimT andP IHr)) //.
    1,2: move /andP : IHr => [/eqP IHr1 IHr].
    1,2: generalize (proj2 (href_overlaps_is_correct r p) IHr1) ; intro Hro.
    1,2: destruct (href_overlaps r p) as [[[b e] to]|] ; last by done.
    1,2: destruct b as [|b'] ;
            last by rewrite Htr in Hro ;
                    move /andP : Hro => [Hro1 /eqP Hro2] ; subst to ;
                    rewrite Hpos ;
                    move /andP : Hagree => [/andP [_ /eqP Hagree] _] ;
                    rewrite -Hagree Hn1p //.
    1,2: destruct e as [|[|e'']] ;
            try done ;
            first by rewrite Htr in Hro ;
                    move /andP : Hro => [Hro1 /eqP Hro2] ; subst to ;
                    rewrite Hpos ;
                    move /andP : Hagree => [/andP [_ /eqP Hagree] _] ;
                    rewrite -Hagree Hn1p //.
    1,2: destruct to as [[[|]| | | |]| |] ; try done.
    1,2: rewrite Htr in Hro ; move /andP : Hro => [_ /eqP Hro].
    1,2: inversion Hro ; subst f0.
    1,2: move /andP : Hagree => [/andP [_ /eqP Hagree] _] ; subst n1.
    1,2: by rewrite Hpos Hn1p //.
  + (* type_of_href r summ = Some _
       href_depends_on r p ... = None *)
    destruct (type_of_subfield f s) as [[[|] _]|] ; last by done.
    1,2: destruct (href_overlaps r p) ; by done.
  + (* type_of_href r summ = None 
       href_depends_on r p ... = Some _ *)
    simpl in IHr.
    move /orP : IHr => [/andP [/eqP IHr _]|/and3P [IHr1 /andP [IHr2 _] _]] ;
          first by inversion IHr ;
                   destruct err1, err2 ;
                   rewrite // eq_refl eq_refl //.
    rewrite IHr1 andTb.
    destruct t1 as [| |ff1] ;
          try by destruct err1, err2 ; rewrite // eq_refl eq_refl //.
    destruct (part_of_subfield ff1 s) as [[t offset]|] ; last by done.
    destruct (n1 + offset <= snd (ssval p) < n1 + offset + number_of_parts t) eqn: Hoffs ;
    by rewrite Hoffs // Hoffs eq_refl eq_refl andTb andTb orbT //.
* (* Esubindex r n (and partly Esubaccess r h) *)
  1,2: specialize (IHr (Some (Gtyp (Fuint 0), 0)) (Some (Gtyp (Fuint 0), 0))).
  1,2: generalize (href_depends_on_and_overlaps_agree r p (Some (Gtyp (Fuint 0), 0))) ; intro Hagree.
  1,2: destruct (type_of_href r summ) as [[o [|eltype arsize|]]|] eqn: Htr.
  + (* type_of_href r summ = Some (_, Gtyp _) -- with Esubaccess *)
    1,5: destruct (href_depends_on r p (Some (Gtyp (Fuint 0), 0))) as [[[|eltype' arsize'|] offs]|] ; try done.
    - (* href_depends_on r p ... = Some (Gtyp _, _) *)
      1,3,4,6: by destruct err1, err2 ; rewrite // eq_refl eq_refl //.
    - (* href_depends_on r p ... = Some (Atyp _, _) or Some (Btyp _, _) *)
      1,2: destruct r as [v|r' n0|r' v'|r' e'].
      4,8: destruct (type_of_hfexpr Passive e' summ) as [[[| | | |]| |]|].
      1-22: try (by move /andP : IHr => [/eqP IHr _] ;
                    discriminate IHr) ;
            by move /andP : IHr => [/andP [/andP [_ /eqP IHr] _] _] ;
               discriminate IHr.
  + (* type_of_href r summ = Some (_, Atyp _) -- without Esubaccess *)
    destruct (href_depends_on r p (Some (Gtyp (Fuint 0), 0))) as [[[|eltype' arsize'|] offs]|] eqn: Hrdo ; try done.
    - (* href_depends_on r p ... = Some (Gtyp _, _) or Some (Btyp _, _) *)
      1,3: destruct r as [v|r' n0|r' v'|r' e'] eqn: Hr.
      4,8: destruct (type_of_hfexpr Passive e' summ) as [[[| | | |]| |]|] eqn:He'.
      1-22: try (by move /andP : IHr => [/andP [/andP [_ /eqP IHr] _] _] ;
                    discriminate IHr).
    - (* href_depends_on r p ... = Some (Atyp _ _, _) *)
      move /andP : IHr => [/andP [/andP [/and3P [IHr1 _ IHr2] /eqP IHr'] _] _] ;
      inversion IHr' ; subst eltype' arsize' ; clear IHr'.
      destruct (offs + n * number_of_parts eltype <= snd (ssval p) < offs + (n + 1) * number_of_parts eltype) eqn: Hp ;
            rewrite Hp.
      * move /andP : Hp => [Hp Hp1].
        apply (leq_ltn_trans Hp) in IHr2 ; simpl number_of_parts in IHr2.
        rewrite ltn_add2l ltn_mul2r in IHr2.
        move /andP : IHr2 => [_ IHr2].
        by rewrite IHr2 IHr1 Hp -addnA -mulSnr -(addn1 n) Hp1 eq_refl eq_refl //.
      * destruct (n < arsize) eqn: Harsize ; last (by done).
        destruct (href_overlaps r p) as [[[b e] [gt| |ff]]|] ; try done.
        1,3: destruct b ; last (by move /andP : Hagree => [/andP [/eqP Hagree _] _] ; discriminate Hagree) ;
             destruct e as [|[|e'']] ; try (by move /andP : Hagree => [/andP [/eqP Hagree _] _] ; discriminate Hagree) ;
             by destruct gt as [[|]| | | |] ; try (by move /andP : Hagree => [/andP [/eqP Hagree _] _] ; discriminate Hagree) ;
                discriminate (elimT eqP Hagree).
        destruct b, e as [|[|e'']] ;
              move /andP : Hagree => [/andP [/eqP Hagree1 /eqP Hagree2] _] ;
              inversion Hagree1 ; subst f n0 offs ; clear Hagree1 ;
              by rewrite -(addn1 n) Hp andbF //.
    - (* href_depends_on r p ... = None *)
      destruct (href_overlaps r p) ; first (by done).
      destruct (n < arsize) ; by done.
  + (* type_of_href r summ = Some (_, Btyp _) -- with Esubaccess *)
    1,4: destruct (href_depends_on r p (Some (Gtyp (Fuint 0), 0))) as [[[|eltype' arsize'|] offs]|] ; last by done.
    - (* href_depends_on r p ... = Some (Gtyp _, _) or Some (Btyp _, _) *)
      1,3,4,6: by destruct err1, err2 ; rewrite // eq_refl eq_refl //.
    - (* href_depends_on r p ... = Some (Atyp _, _) *)
      1,2: move /andP : IHr => [/andP [/andP [_ /eqP IHr] _] _] ;
      by discriminate IHr.
  + (* type_of_href r summ = None -- with Esubaccess *)
    1,3: destruct (href_depends_on r p (Some (Gtyp (Fuint 0), 0))) as [[[|eltype' arsize'|] offs]|] ; last by done.
    - (* href_depends_on r p ... = Some (Gtyp _, _) or Some (Btyp _, _) *)
      1,3,4,6: by destruct err1, err2 ; rewrite // eq_refl eq_refl //.
    - (* href_depends_on r p ... = Some (Atyp _, _) *)
      1,2: move /orP : IHr => [/andP[/eqP IHr _]|/and3P [IHr1 /andP [/andP [IHr2 IHr3] _] _]] ;
           first by discriminate IHr.
      1,2: rewrite (negbTE IHr1).
      * (* Esubindex *)
        destruct (offs + n * number_of_parts eltype' <= snd (ssval p) < offs + (n + 1) * number_of_parts eltype') eqn: Hp ;
        by rewrite Hp // -addnA -mulSnr -(addn1 n) Hp eq_refl eq_refl orbT //.
* (* Esubaccess r h -- partly handled by the above case *)
      * (* type_of_href r summ = None and href_depends_on r p ... = Some (Atyp _, _) *)
        assert (Hnot0 : (0 < arsize') && (0 < number_of_parts eltype'))
              by rewrite -muln_gt0 -(ltn_add2l offs) addn0 (leq_ltn_trans IHr2 IHr3) //.
        move /andP : Hnot0 => [_ Hnot0].
        rewrite eq_refl eq_refl andbT andbT
                -(leq_subRL _ IHr2) leq_trunc_div andTb
                -addnA -mulSnr -(ltn_subLR _ IHr2) (ltn_ceil _ Hnot0) andbT.
        destruct (type_of_hfexpr Passive h summ) as [[[| | | |]| |]|] ;
        by rewrite orbT //.
  + (* type_of_href r summ = Some (_, Atyp _) *)
    destruct (href_depends_on r p (Some (Gtyp (Fuint 0), 0))) as [[[|eltype' arsize'|] offs]|] eqn: Hdo.
    - (* href_depends_on r p ... = Some (Gtyp _, _) or Some (Btyp _, _) *)
      1,3: move /andP : IHr => [/andP [/andP [_ /eqP IHr] _] _] ;
           by discriminate IHr.
    - (* href_depends_on r p ... = Some (Atyp _ _, _) *)
      move /andP : IHr => [/andP [/andP [/and3P [IHr1 IHr2 IHr3] /eqP IHr'] _] _].
      inversion IHr' ; subst eltype' arsize' ; clear IHr'.
      assert (Hnot0 : (0 < arsize) && (0 < number_of_parts eltype))
            by rewrite -muln_gt0 -(ltn_add2l offs) addn0 (leq_ltn_trans IHr2 IHr3) //.
      move /andP : Hnot0 => [_ Hnot0].
      destruct (type_of_hfexpr Passive h summ) as [[[_|_| | |]|_ _|_]|].
      * (* type_of_hfexpr Passive h summ = Some (Gtyp (Fuint _)) or Some (Gtyp (Fsint _)) *)
        1,2: rewrite IHr1 andTb eq_refl eq_refl andbT andbT andbT.
        1,2: apply (introT andP) ; split ;
             first by rewrite -(leq_subRL _ IHr2) leq_trunc_div //.
        1,2: rewrite -addnA mulnC -mulnSr -(ltn_subLR _ IHr2) mulnC.
        1,2: apply ltn_ceil.
        1,2: generalize (leq_ltn_trans IHr2 IHr3) ; intro H0.
        1,2: simpl number_of_parts in H0.
        1,2: rewrite -addn1 leq_add2l muln_gt0 in H0.
        1,2: by apply (elimT andP H0).
      * (* type_of_hfexpr Passive h summ = Some (other type) *)
        1-6: by rewrite andTb eq_refl eq_refl andbT andbT
                        -(leq_subRL _ IHr2) leq_trunc_div andTb
                        -addnA -mulSnr -(ltn_subLR _ IHr2) (ltn_ceil _ Hnot0) orbT //.
    - (* href_depends_on r p ... = None *)
      destruct (href_overlaps r p) ; first by done.
      destruct (type_of_hfexpr Passive h summ) as [[[[|]| | | |]| |]|] ; by done.
Qed.

Fixpoint expr_depends_on {summ : summaryType} (e : hfexpr) (p2 : component_part summ) : bool :=
(* checks whether any part of expression e depends on p2.
   expr must be passive, i.e. it may not contain flipped bundle parts. *)
  match e with
  | Econst _ _ => false
  | Ecast _ e' => expr_depends_on e' p2
  | Eprim_unop _ e' => expr_depends_on e' p2
  | Eprim_binop _ e1 e2 => expr_depends_on e1 p2 ||
                           expr_depends_on e2 p2
  | Emux c e1 e2 => expr_depends_on c p2 ||
                    expr_depends_on e1 p2 ||
                    expr_depends_on e2 p2
  | Eref r => subaccess_index_in_expr_depends_on r p2 || 
              href_depends_on r p2 (Some (Gtyp (Fuint 0), 0)) (* if an error happens, we return "true", i.e. the "bad" value *)
  | Earray ar => array_expr_depends_on ar p2
  | Ebundle bu => bundle_expr_depends_on bu p2
  | Etobedefined _ => false
  | Eundefinedonpurpose _ => false
  end
with array_expr_depends_on {summ : summaryType} (ar : array_expr) (p2 : component_part summ) : bool :=
  match ar with
  | Aone e => expr_depends_on e p2
  | Acons e ar' => expr_depends_on e p2 ||
                   array_expr_depends_on ar' p2
  end
with bundle_expr_depends_on {summ : summaryType} (bu : bundle_expr) (p2 : component_part summ) : bool :=
  match bu with
  | Bnil => false
  | Bflips _ Nflip e bu' => expr_depends_on e p2 ||
                            bundle_expr_depends_on bu' p2
  | Bflips _ Flipped _ _ => true (* should not happen, so we return the "bad" value *)
  end
with subaccess_index_in_expr_depends_on {summ : summaryType} (r : href) (p2 : component_part summ): bool :=
(* checks whether a subaccess index expression in r depends on p2. *)
  match r with
  | Eid _ => false
  | Esubfield r' _ => subaccess_index_in_expr_depends_on r' p2
  | Esubindex r' _ => subaccess_index_in_expr_depends_on r' p2
  | Esubaccess r' e => expr_depends_on e p2 || subaccess_index_in_expr_depends_on r' p2
  end.

Definition depends_on {summ : summaryType} (p1 p2 : component_part summ) : bool :=
(* defines whether p1 combinatorially depends on p2. 
   This happens if component part p1, according to summ, is connected to component part p2. 
   Later we shall need to take the transitive closure of (depends_on summ). *)
  match app_summ summ (fst (val p1)), app_summ summ (fst (val p2)) with
  | Some _, Some (Register, _, _, _)
  | Some (Register, _, _, _), Some _ => false
  | Some (Inport, t1, _, ew), Some (_, t2, _, _) => match select_part t1 ew (snd (val p1)) with
                                                    | Some (Flipped, e) => expr_depends_on e p2
                                                    | _ => false
                                                    end
  | Some (Outport, t1, er, _), Some (_, t2, _, _) => match select_part t1 er (snd (val p1)) with
                                                     | Some (Nflip, e) => expr_depends_on e p2
                                                     | _ => false
                                                     end
  | Some (Wire, t1, er, ew), Some (_, t2, _, _) => match select_part t1 er (snd (val p1)) with
                                                   | Some (Nflip, e) => expr_depends_on e p2
                                                   | Some (Flipped, _) => match select_part t1 ew (snd (val p1)) with
                                                                          | Some (Flipped, e) => expr_depends_on e p2
                                                                          | _ => false
                                                                          end
                                                   | None => false
                                                   end
  | Some (Node, t1, er, _), Some (_, t2, _, _) => match select_part t1 er (snd (val p1)) with
                                                  | Some (Nflip, e) => expr_depends_on e p2
                                                  | _ => false
                                                  end
  | Some _, None
  | None, _ => true (* error --- should not happen, so we return the "bad" value *)
                    (* another possibility would have been to write a False_rec expression,
                       i.e. a proof that this case does not occur. *)
  end.

(* So we now can define the finite graph,
with vertices defined_parts, and edges defined by depends_on. *)

Definition dep_graph (summ : summaryType) := rgraph (@depends_on summ).
(* the transitive closure of depends_on can be constructed in a finite number of steps, as the relation is finite.
   However, to use well-foundedness, it is not necessary to construct the transitive closure. *)

Fixpoint href_is_not_cyclic {summ : summaryType} (r : href) (fl : fflip) (t : ftype) (p2 : component_part summ) : bool :=
    match t with
    | Gtyp _ => if fl == Nflip
                then [forall p1 : component_part summ, match href_depends_on r p1 (Some (Btyp Fnil, 0)) with
                                                       | Some (Gtyp _, n1) => (n1 == snd (val p1)) && ~~connect (grel (dep_graph summ)) p1 p2
                                                       | Some _ => (* error, so we return the "bad" value *) false
                                                       | None => ~~(subaccess_index_in_expr_depends_on r p1 &&
                                                                    connect (grel (dep_graph summ)) p1 p2)
                                                       end]
                else true
    | Atyp t' n => match split_ref_into_subindex r 0 n with
                   | Some ar => (fix array_href_is_not_cyclic (ar : array_expr) (p2 : component_part summ) : bool :=
                                     (* Check for every ground-type part of the array expression ar
                                        (which consists or references and whose elements have type t)
                                        whether it depends on the corresponding part of p2, p2+1, ... *)
                                         match ar with
                                         | Aone (Eref r') => href_is_not_cyclic r' fl t' p2
                                         | Acons (Eref r') ar' => match insub (sT := component_part summ) (fst (val p2), snd (val p2) + number_of_parts t) with
                                                          | Some p2' => href_is_not_cyclic r' fl t' p2 && array_href_is_not_cyclic ar' p2'
                                                          | None => (* error, so we return the "bad" value *) false
                                                          end
                                         | _ => (* error, so we return the "bad" value *) false
                                         end) ar p2
                   | None => (* error, so we return the "bad" value *) false
                   end
    | Btyp ff => bundle_href_is_not_cyclic (split_ref_into_subfields r ff) fl ff p2
    end
with bundle_href_is_not_cyclic {summ : summaryType} (bu : bundle_expr) (fl : fflip) (ff : ffield) (p2 : component_part summ) : bool :=
(* Check for every ground-type part of the bundle expression bu
   (which consists of references)
   whether it depends on the corresponding part of p2, p2+1, ... *)
    match ff, bu with
    | Fnil, Bnil => true
    | Fflips v2 fl2 t' ff', Bflips v1 fl1 (Eref r') bu' => if (v1 == v2) && (fl1 == fl2)
                                                           then match insub (sT := component_part summ) (fst (val p2), snd (val p2) + number_of_parts t') with
                                                                | Some p2' => href_is_not_cyclic r' (if fl == fl1 then Nflip else Flipped) t' p2 &&
                                                                              bundle_href_is_not_cyclic bu' fl ff' p2'
                                                                | None => (* error, so we return the "bad" value *) false
                                                                end
                                                           else (* error, so we return the "bad" value *) false
    | _, _ => (* error, so we return the "bad" value *) false
    end.



Fixpoint expr_is_not_cyclic {summ : summaryType} (e : hfexpr) (fl : fflip) (p2 : component_part summ) : option nat :=
(* Check for every ground-type part of e, whether it depends on the corresponding part of p2 cyclically --
   for those parts that are fl-flipped.
   The result is "Some i" if the expression is not cyclic and has i parts 
   or "None" if the expression is cyclic. *)
    match e with
    | Econst _ _ => Some 1
    | Ecast _ e'
    | Eprim_unop _ e'
    | Eprim_binop _ _ _ as e' => if (fl == Flipped) ||
                                       [forall p1 : component_part summ, ~~(expr_depends_on e' p1 &&
                                                                            connect (grel (dep_graph summ)) p1 p2)]
                                    then Some 1
                                    else None
   | Emux c e1 e2 => match expr_is_not_cyclic e1 fl p2 with
                     (* also needs to take into account that c might depend on p2. But c is a ground-type expression,
                        while e1/e2 may be aggregate types.
                        Example : a <= Emux (Eprim_binop (Bcmp Beq) (Esubindex a 2) 0) b c, 
                                  where a b c are arrays of integers. Then the condition depends on a[2],
                                  so there is a cyclic dependency for the element a[2] (not for the other elements).
                                  a[0] <= Emux (...a[2]...) b[0] c[0] would be ok. *)
                      | Some siz => if [forall (p2' : component_part summ | (fst (val p2) == fst (val p2')) && 
                                                              (snd (val p2) <= snd (val p2') < snd (val p2) + siz)), 
                                                              expr_is_not_cyclic c fl p2'] &&
                                       expr_is_not_cyclic e2 fl p2
                                    then Some siz else None
                      | None => None
                      end
    | Eref r => match type_of_href r summ with
                | Some (_, t) => if href_is_not_cyclic r fl t p2
                                 then Some (number_of_parts t)
                                 else None
                | _ => None
                end
    | Earray ar => array_expr_is_not_cyclic ar fl p2
    | Ebundle bu => bundle_expr_is_not_cyclic bu fl p2
    | Etobedefined t => Some (number_of_parts t)
    | Eundefinedonpurpose t => Some (number_of_parts t)
    end
with array_expr_is_not_cyclic {summ : summaryType} (ar : array_expr) (fl : fflip) (p2 : component_part summ) : option nat :=
(* Check for every ground-type part of the array expression ar whether it depends on the corresponding part of p2, p2+1, ... *)
    match ar with
    | Aone e => expr_is_not_cyclic e fl p2
    | Acons e ar' => match expr_is_not_cyclic e fl p2 with
                     | Some siz => match insub (sT := component_part summ) (fst (val p2), snd (val p2) + siz) with
                                   | Some p2' => match array_expr_is_not_cyclic ar' fl p2' with
                                                 | Some siz' => Some (siz + siz')
                                                 | None => None
                                                 end
                                   | None => (* error, so we return the "bad" value *) None
                                   end
                     | None => None
                     end
    end
with bundle_expr_is_not_cyclic {summ : summaryType} (bu : bundle_expr) (fl : fflip) (p2 : component_part summ) : option nat :=
    match bu with
    | Bnil => Some 0
    | Bflips v1 fl1 e bu' => match expr_is_not_cyclic e (if fl == fl1 then Nflip else Flipped) p2 with
                             | Some siz => match insub (sT := component_part summ) (fst (val p2), snd (val p2) + siz) with
                                           | Some p2' => match bundle_expr_is_not_cyclic bu' fl p2' with
                                                         | Some siz' => Some (siz + siz')
                                                         | None => None
                                                         end
                                           | None => (* error, so we return the "bad" value *) None
                                           end
                             | None => None
                             end
    end.

(* Probably we need a theorem here: if expr_is_not_cyclic, then no subexpression is cyclic.
   This theorem may require that the expression is type-correct (so that should be checked) *)

Fixpoint subexpr (e1 e2 : hfexpr) : bool :=
    if e1 == e2 
    then true
    else match e2 with
         | Econst _ _ => false
         | Ecast _ e2'
         | Eprim_unop _ e2' => subexpr e1 e2'
         | Eprim_binop _ e2a e2b => subexpr e1 e2a || subexpr e1 e2b
         | Emux c e2a e2b => subexpr e1 c || subexpr e1 e2a || subexpr e1 e2b
         | Eref r => subexpr_ref e1 r
         | Earray ar => subexpr_array e1 ar
         | Ebundle bu => subexpr_bundle e1 bu
         | Etobedefined _ => false
         | Eundefinedonpurpose _ => false
         end
with subexpr_array (e : hfexpr) (ar : array_expr) : bool :=
    match ar with
    | Aone e' => subexpr e e'
    | Acons e' ar' => subexpr e e' || subexpr_array e ar'
    end
with subexpr_bundle (e : hfexpr) (bu : bundle_expr) : bool :=
    match bu with
    | Bnil => false
    | Bflips _ _ e' bu' => subexpr e e' || subexpr_bundle e bu'
    end
with subexpr_ref (e : hfexpr) (r : href) : bool :=
    match r with
    | Eid _ => false
    | Esubfield r' _ => subexpr_ref e r'
    | Esubindex r' _ => subexpr_ref e r'
    | Esubaccess r' e' => subexpr_ref e r' || subexpr e e'
    end.


Lemma acyclic_Gtyp (summ : summaryType) :
    forall (e : hfexpr) (o : forient),
        match type_of_hfexpr o e summ with
        | Some (Gtyp _) => forall (fl : fflip) (p : component_part summ),
                               expr_is_not_cyclic e fl p =
                               if (fl == Flipped) ||
                                  [forall p1, ~~ (expr_depends_on e p1 &&
                                                  connect (grel (dep_graph summ)) p1 p)]
                               then Some 1
                               else None
        | _ => True
        end.
Proof.
induction e as [ft n|u e|op e|op e1 IHe1 e2 IHe2|c IHc e1 IHe1 e2 IHe2|r| | | |] ; simpl.
* (* Econst *)
  intro o.
  destruct (readable_orient o) ; last by done.
  destruct fl ; first by done.
  rewrite orFb.
  destruct ([forall p1 : component_part summ, true]) eqn: Hforall ; rewrite Hforall ; first by reflexivity.
  move /forallP : Hforall => Hforall ; done.
* (* Ecast *)
  intro o.
  destruct (readable_orient o) ; last by done.
  specialize (IHe Passive).
  by destruct u, (type_of_hfexpr Passive e summ) as [[[w|w| | |]| |]|] ;
        done.
* (* Eunop *)
  intro o.
  destruct (readable_orient o) ; last by done.
  specialize (IHe Passive).
  by destruct op, (type_of_hfexpr Passive e summ) as [[[w|w| | |]| |]|] ;
        try (by done) ;
        try (destruct (n0 <= n < w) ; by done) ;
        destruct (n <= w) ; done.
* (* Ebinop *)
  intro o.
  destruct (readable_orient o) ; last by done.
  specialize (IHe1 Passive) ; specialize (IHe2 Passive).
  by destruct op, (type_of_hfexpr Passive e1 summ) as [[[w1|w1| | |]| |]|],
                  (type_of_hfexpr Passive e2 summ) as [[[w2|w2| | |]| |]|] ;
        done.
* (* Emux *)
  intro o.
  destruct (readable_orient o) ; last by done.
  specialize (IHc Passive).
  destruct (type_of_hfexpr Passive c summ) as [[[[|[|]]| | | |]| |]|] ; try by done.
  specialize (IHe1 o) ; specialize (IHe2 o).
  destruct (type_of_hfexpr o e1 summ) as [[[w1|w1| | |]| |]|],
           (type_of_hfexpr o e2 summ) as [[[w2|w2| | |]| |]|] ;
        simpl ;
        try (by done) ;
        try (destruct (n == n0), (unified_type f f0) ; by trivial) ;
        try (destruct (unified_ffield f f0) ; by trivial) ;
  intros fl p ;
  specialize (IHc fl p) ; specialize (IHe1 fl p) ; specialize (IHe2 fl p) ;
  rewrite IHe1 //.
  1-5: destruct fl.
  + (* Flipped *)
    1,3,5,7,9: rewrite orTb in IHc ; rewrite orTb in IHe1 ; rewrite orTb in IHe2.
    1-5: rewrite orTb orTb IHe2 andbT.
    1-5: destruct ([forall (p2' | [&& fst (ssval p) == fst (ssval p2'),
                                 snd (ssval p) <= snd (ssval p2')
                               & snd (ssval p2') < snd (ssval p) + 1]),
                      expr_is_not_cyclic (summ := summ) c Flipped p2']) eqn: Hp2 ; rewrite Hp2 //.
    1-5: move /forallP : Hp2 => Hp2.
    1-5: contradict Hp2.
    1-5: intro p2.
    1-5: apply (introT implyP).
    1-5: intro.
    1-5: move /and3P : H => [H1 H2 H3].
    1-5: assert (p = p2)
          by (apply val_inj, injective_projections ;
                    first (by simpl ; exact (elimT eqP H1)) ;
                    apply (elimT eqP) ;
                    rewrite eqn_leq H2 andTb -ltnS -(addn1 (snd (val p))) ; simpl ; exact H3).
    1-5: by rewrite -H IHc //.
  + (* Nflip *)
    1-5: rewrite orFb in IHc ; rewrite orFb in IHe1 ; rewrite orFb in IHe2.
    1-5: rewrite orFb orFb.
    1-5: destruct ([forall p1, ~~((expr_depends_on c p1 ||
                                   expr_depends_on e1 p1 ||
                                   expr_depends_on e2 p1) &&
                                  connect (grel (dep_graph summ)) p1 p)]) eqn: Hforallr ;
          rewrite Hforallr ;
          move /forallP : Hforallr => Hforallr.
    - (* acyclicity is true, according to Hforallr *)
      1,3,5,7,9: destruct ([forall p1, ~~(expr_depends_on e1 p1 &&
                                          connect (grel (dep_graph summ)) p1 p)]) eqn: Hforall1 ;
            move /forallP : Hforall1 => Hforall1 ;
            last by (contradict Hforall1 ;
                     intro p1 ; specialize (Hforallr p1) ;
                     apply (elimT negP) in Hforallr ; apply (introT negP) ;
                     contradict Hforallr ;
                     rewrite (proj1 (elimT andP Hforallr)) (proj2 (elimT andP Hforallr)) orbT //).
      1-5: destruct ([forall (p2' | [&& fst (ssval p) == fst (ssval p2'),
                                   snd (ssval p) <= snd (ssval p2')
                                 & snd (ssval p2') < snd (ssval p) + 1]),
                        expr_is_not_cyclic (summ := summ) c Nflip p2'] &&
                expr_is_not_cyclic e2 Nflip p) eqn: Hforall2 ;
            rewrite Hforall2 ; first by reflexivity.
      1-5: move /andP : Hforall2 => Hforall2.
      1-5: contradict Hforall2.
      1-5: split.
      * 1,3,5,7,9: apply (introT forallP) ; intro p1 ; generalize (Hforallr p1) ; intro Hforallr_p1.
        1-5: apply (introT implyP) ; intro Hp1.
        1-5: move /and3P : Hp1 => [H1 H2 H3].
        1-5: assert (p = p1)
                  by (apply val_inj, injective_projections ; first (by simpl ; exact (elimT eqP H1)) ;
                      apply (elimT eqP) ;
                      rewrite eqn_leq H2 andTb -ltnS -(addn1 (snd (val p))) ; simpl ; exact H3).
        1-5: rewrite -H IHc.
        1-5: destruct ([forall p0, ~~(expr_depends_on c p0 &&
                                      connect (grel (dep_graph summ)) p0 p)]) eqn: Hforallc ; first by done.
        1-5: move /forallP : Hforallc => Hforallc.
        1-5: contradict Hforallc.
        1-5: intro p0 ; specialize (Hforallr p0).
        1-5: apply (elimT negP) in Hforallr ; apply (introT negP) ; contradict Hforallr.
        1-5: by rewrite (proj1 (elimT andP Hforallr)) (proj2 (elimT andP Hforallr)) //.
      * 1-5: rewrite IHe2.
        1-5: destruct ([forall p1, ~~(expr_depends_on e2 p1 &&
                                      connect (grel (dep_graph summ)) p1 p)]) eqn: Hforall2 ; first by done.
        1-5: move /forallP : Hforall2 => Hforall2.
        1-5: contradict Hforall2.
        1-5: intro p1 ; specialize (Hforallr p1).
        1-5: apply (elimT negP) in Hforallr ; apply (introT negP) ; contradict Hforallr.
        1-5: by rewrite (proj1 (elimT andP Hforallr)) (proj2 (elimT andP Hforallr)) orbT //.
    - (* acyclicity is false, according to Hforallr *)
      1-5: destruct ([forall p1, ~~(expr_depends_on e1 p1 &&
                                    connect (grel (dep_graph summ)) p1 p)]) eqn: Hforall1 ; last by done.
      1-5: move /forallP : Hforall1 => Hforall1.
      1-5: destruct ([forall (p2' | [&& fst (ssval p) == fst (ssval p2'),
                                   snd (ssval p) <= snd (ssval p2')
                                 & snd (ssval p2') < snd (ssval p) + 1]),
                        expr_is_not_cyclic (summ := summ) c Nflip p2'] &&
                expr_is_not_cyclic e2 Nflip p) eqn: Hforallc ;
            rewrite Hforallc ; last by done.
      1-5: move /andP : Hforallc => [/forallP Hforallc He2nc].
      1-5: specialize (Hforallc p).
      1-5: rewrite eq_refl andTb addn1 ltnS -eqn_leq eq_refl implyTb in Hforallc.
      1-5: rewrite IHc in Hforallc.
      1-5: destruct ([forall p1, ~~(expr_depends_on c p1 &&
                                    connect (grel (dep_graph summ)) p1 p)]) eqn: Hforallc' ; last by done.
      1-5: move /forallP : Hforallc' => Hforallc'.
      1-5: rewrite IHe2 in He2nc.
      1-5: destruct ([forall p1, ~~(expr_depends_on e2 p1 &&
                                    connect (grel (dep_graph summ)) p1 p)]) eqn: Hforall2 ; last by done.
      1-5: move /forallP : Hforall2 => Hforall2.
      1-5: contradict Hforallr.
      1-5: intro p1 ; specialize (Hforallc' p1) ; specialize (Hforall1 p1) ; specialize (Hforall2 p1).
      1-5: rewrite negb_and in Hforallc'.
      1-5: move /orP : Hforallc' => [Hforallc' | Hforallc'] ;
            last by rewrite (negbTE Hforallc') andbF //.
      1-5: rewrite negb_and in Hforall1.
      1-5: move /orP : Hforall1 => [Hforall1 | Hforall1] ;
            last by rewrite (negbTE Hforall1) andbF //.
      1-5: rewrite negb_and in Hforall2.
      1-5: move /orP : Hforall2 => [Hforall2 | Hforall2] ;
            last by rewrite (negbTE Hforall2) andbF //.
      1-5: by rewrite (negbTE Hforallc') (negbTE Hforall1) (negbTE Hforall2) //.
* (* Eref *)
  intro o.
  generalize (@type_of_href_no_error summ) ; intro Hne ; specialize Hne with (r := r).
  destruct (type_of_href r summ) as [[[| | | |] [| |]]|] eqn: Ht, o ; try by done.
  1-8: intros fl p ; simpl.
  1-8: destruct fl ; first (by reflexivity) ; rewrite eq_refl orFb //.
  1-8: destruct ([forall p1, match href_depends_on r p1 (Some (Btyp Fnil, 0)) with
                             | Some (Gtyp _, n1) => (n1 == snd (ssval p1)) && ~~connect (grel (dep_graph summ)) p1 p
                             | None => ~~(subaccess_index_in_expr_depends_on r p1 &&
                                          connect (grel (dep_graph summ)) p1 p)
                             | _ => false
                             end]) eqn: Hl,
                ([forall p1, ~~((subaccess_index_in_expr_depends_on r p1 || 
                                 href_depends_on r p1 (Some (Gtyp (Fuint 0), 0))) &&
                                connect (grel (dep_graph summ)) p1 p)]) eqn: Hr ;
       rewrite Hl Hr //.
  1-16: move /forallP : Hl => Hl ; move /forallP : Hr => Hr.
  + 1,3,5,7,9,11,13,15: contradict Hr.
    1-8: intro p1 ; specialize (Hl p1) ; specialize (Hne p1 (Some (Btyp Fnil, 0)) (Some (Gtyp (Fuint 0), 0))).
    1-8: destruct (href_depends_on r p1 (Some (Btyp Fnil, 0))) as [[[| |] n1]|],
                  (href_depends_on r p1 (Some (Gtyp (Fuint 0), 0))) as [[t2 n2]|] ;
         try rewrite orbF ;
         try done.
    1-8: by move /andP : Hl => [_ Hl] ; rewrite (negbTE Hl) andbF //.
  + 1-8: contradict Hl ; intro p1 ; specialize (Hr p1) ; specialize (Hne p1 (Some (Btyp Fnil, 0)) (Some (Gtyp (Fuint 0), 0))).
    1-8: destruct (href_depends_on r p1 (Some (Btyp Fnil, 0))) as [[[| |] n1]|] eqn: Hdo1,
                  (href_depends_on r p1 (Some (Gtyp (Fuint 0), 0))) as [[t2 n2]|] eqn: Hdo2 ;
         try rewrite orbF in Hr ;
         try done ;
         try (by move /andP : Hne => [/andP [/andP [_ /eqP Hne4] _] _] ;
                 discriminate Hne4).
    1-8: by rewrite negb_and in Hr ; move /orP : Hr => [Hr|Hr] ;
                first (by rewrite orbT // in Hr) ;
            move /andP : Hne => [/andP [/andP [/and3P [_ Hne2 Hne3] _] _] _] ;
            simpl in Hne3 ;
            rewrite Hr andbT eqn_leq Hne2 andTb -ltnS -(addn1 n1) //.
* (* Earray *)
  intro o.
  destruct (type_of_array_expr o a summ) as [[| |]|] eqn: Harray ; try done.
  contradict Harray.
  destruct a ; simpl ; destruct (type_of_hfexpr o h summ) ; try by discriminate.
  destruct (type_of_array_expr o a summ) as [[| |]|] ; try by discriminate.
  destruct (unified_type f0 f1) ; by discriminate.
* (* Ebundle *)
  intro o.
  destruct (type_of_bundle_expr o b summ) as [[| |]|] eqn: Hbundle ; try by done.
  contradict Hbundle.
  destruct b ; simpl ; try by discriminate.
  destruct f0, type_of_hfexpr ; try by discriminate.
  1,2: destruct (type_of_bundle_expr o b summ) as [[| |]|] ; by discriminate.
* (* Etobedefined and Eundefinedonpurpose *)
  1,2: destruct o ; try done.
  4,8: destruct (is_passive f) ; last by done.
  1-8: destruct f ; try done.
  1-8: intros fl _ ; simpl number_of_parts.
  1-8: destruct ((fl == Flipped) || [forall p1 : component_part summ, true]) eqn: Hc ;
       rewrite Hc //.
  1-8: apply negbT in Hc ; rewrite negb_or in Hc ; move /andP : Hc => [_ /forallP Hc].
  1-8: contradict Hc ; intros _ ; done.
Qed.

(* "Subexpressions of non-cyclic expressions are also non-cyclic."
   The problem with the following lemma is that for references,
   (Eid v) may indicate a larger reference than Esubfield (Eid v) ...
   So this kind of lemma does not work for references.
   To solve this problem, I restricted the lemma to ground-type component parts. *)
Lemma acyclic_subexpressions {summ : summaryType} (fl : fflip) (p : component_part summ) :
    forall (e2 e1 : hfexpr) (o : forient),
        match type_of_hfexpr o e2 summ with
        | Some (Gtyp _) => subexpr e1 e2 -> expr_is_not_cyclic e2 fl p -> expr_is_not_cyclic e1 fl p
        | _ => True
        end.
Proof.
intros ; destruct (type_of_hfexpr o e2 summ) as [[gt2| |]|] eqn: Hte2 ; try by done.
revert e1 o gt2 Hte2 ; induction e2 ; simpl ; intros e1 o gt2 Hte2 Hsub Hnce2.
+ (* Econst *)
  destruct (e1 == Econst f i) eqn: He1 ; last by done.
  by rewrite (elimT eqP He1) //.
+ (* Ecast *)
  destruct (e1 == Ecast u e2) eqn: He1 ; first by rewrite (elimT eqP He1) //.
  destruct (readable_orient o) ; last by discriminate Hte2.
  specialize (IHe2 e1 Passive).
  generalize (@acyclic_Gtyp summ e2 Passive) ; intro Hgt.
  destruct u, (type_of_hfexpr Passive e2 summ) as [[gt2'| |]|] ;
        try by discriminate Hte2.
  1-4: apply (IHe2 gt2' Logic.eq_refl Hsub) ;
       by rewrite Hgt //.
+ (* Eunop *)
  destruct (e1 == Eprim_unop e e2) eqn: He1 ; first by rewrite (elimT eqP He1) //.
  destruct (readable_orient o) ; last by discriminate Hte2.
  specialize (IHe2 e1 Passive).
  generalize (@acyclic_Gtyp summ e2 Passive) ; intro Hgt.
  destruct e, (type_of_hfexpr Passive e2 summ) as [[gt2'| |]|] ;
        try by discriminate Hte2.
  1-12: apply (IHe2 gt2' Logic.eq_refl Hsub) ;
        by rewrite Hgt //.
+ (* Ebinop *)
  destruct (e1 == Eprim_binop e e2_1 e2_2) eqn: He1 ; first by rewrite (elimT eqP He1) //.
  destruct (readable_orient o) ; last by discriminate Hte2.
  specialize (IHe2_1 e1 Passive) ; specialize (IHe2_2 e1 Passive).
  generalize (@acyclic_Gtyp summ e2_1 Passive) ; intro Hgt_1.
  generalize (@acyclic_Gtyp summ e2_2 Passive) ; intro Hgt_2.
  destruct e, (type_of_hfexpr Passive e2_1 summ) as [[gt2_1| |]|] eqn: Hte2_1 ;
        try by discriminate Hte2.
  1-12: destruct (type_of_hfexpr Passive e2_2 summ) as [[gt2_2| |]|] eqn: Hte2_2 ;
        try by (destruct gt2_1 ; discriminate Hte2).
  1-12: move /orP : Hsub => [Hsub|Hsub].
  - (* subexpr e1 e2_1 *)
    1,3,5,7,9,11,13,15,17,19,21,23:
          apply (IHe2_1 gt2_1 Logic.eq_refl Hsub) ;
          rewrite Hgt_1 // ; clear IHe2_1 IHe2_2 Hgt_1 Hgt_2.
    1-12: destruct (fl == Flipped) ;
          first (by rewrite orTb in Hnce2 ; rewrite orTb //) ;
          last  (rewrite orFb in Hnce2 ; rewrite orFb).
    1-12: destruct [forall p1, ~~((expr_depends_on e2_1 p1 || expr_depends_on e2_2 p1) &&
                                  connect (grel (dep_graph summ)) p1 p)] eqn: Hf1,
                   [forall p1, ~~(expr_depends_on e2_1 p1 &&
                                  connect (grel (dep_graph summ)) p1 p)] eqn: Hf2 ;
          rewrite Hf1 // in Hnce2.
    1-12: move /forallP : Hf1 => Hf1 ; move /forallP : Hf2 => Hf2 ;
          contradict Hf2 ;
          intro p1 ; specialize (Hf1 p1).
    1-12: rewrite negb_and in Hf1 ; move /orP : Hf1 => [Hf1|Hf1] ;
          last by rewrite (negbTE Hf1) andbF //.
    1-12: rewrite negb_or in Hf1 ; move /andP : Hf1 => [Hf1 _] ;
          by rewrite (negbTE Hf1) andFb //.
  - (* subexpr e1 e2_2 *)
    1-12: apply (IHe2_2 gt2_2 Logic.eq_refl Hsub) ;
          rewrite Hgt_2 // ; clear IHe2_1 IHe2_2 Hgt_1 Hgt_2.
    1-12: destruct (fl == Flipped) ;
          first (by rewrite orTb in Hnce2 ; rewrite orTb //) ;
          last  (rewrite orFb in Hnce2 ; rewrite orFb).
    1-12: destruct [forall p1, ~~((expr_depends_on e2_1 p1 || expr_depends_on e2_2 p1) &&
                                  connect (grel (dep_graph summ)) p1 p)] eqn: Hf1,
                   [forall p1, ~~(expr_depends_on e2_2 p1 &&
                                  connect (grel (dep_graph summ)) p1 p)] eqn: Hf2 ;
          rewrite Hf1 // in Hnce2.
    1-12: move /forallP : Hf1 => Hf1 ; move /forallP : Hf2 => Hf2 ;
          contradict Hf2 ;
          intro p1 ; specialize (Hf1 p1).
    1-12: rewrite negb_and in Hf1 ; move /orP : Hf1 => [Hf1|Hf1] ;
          last by rewrite (negbTE Hf1) andbF //.
    1-12: rewrite negb_or in Hf1 ; move /andP : Hf1 => [_ Hf1] ;
          by rewrite (negbTE Hf1) andFb //.
+ (* Emux e2_1 e2_2 e2_3 *)
  destruct (e1 == Emux e2_1 e2_2 e2_3) eqn: He1 ; first by rewrite (elimT eqP He1) //.
  destruct (readable_orient o) ; last by discriminate Hte2.
  specialize (IHe2_1 e1 Passive) ; specialize (IHe2_2 e1 o) ; specialize (IHe2_3 e1 o).
  generalize (@acyclic_Gtyp summ e2_1 Passive) ; intro Hgt_1.
  generalize (@acyclic_Gtyp summ e2_2 o) ; intro Hgt_2.
  generalize (@acyclic_Gtyp summ e2_3 o) ; intro Hgt_3.
  destruct (type_of_hfexpr Passive e2_1 summ) as [[[[|[|]]| | | |]| |]|] ;
        try by discriminate Hte2.
  destruct (type_of_hfexpr o e2_2 summ) as [[gt2_2| |]|],
           (type_of_hfexpr o e2_3 summ) as [[gt2_3| |]|] ;
  simpl in Hte2 ; try (by discriminate Hte2) ;
        last (by destruct (unified_ffield f f0) ; discriminate Hte2) ;
        last (by destruct (n == n0), (unified_type f f0) ; discriminate Hte2).
  specialize (Hgt_2 fl p) ; destruct (expr_is_not_cyclic e2_2 fl p) as [siz|] ;
        last by discriminate Hnce2.
  destruct siz as [|[|]], ((fl == Flipped) ||
                           [forall p1, ~~(expr_depends_on e2_2 p1 &&
                                          connect (grel (dep_graph summ)) p1 p)]) eqn: Hf1 ;
        try by discriminate Hgt_2.
  destruct ([forall (p2'
           | [&& fst (ssval p) == fst (ssval p2'),
                 snd (ssval p) <= snd (ssval p2')
               & snd (ssval p2') <
                 snd (ssval p) + 1]),
          expr_is_not_cyclic (summ := summ) e2_1 fl p2'] &&
       expr_is_not_cyclic e2_3 fl p) eqn: Hf2 ; rewrite Hf2 // in Hnce2.
  move /orP : Hsub => [/orP [Hsub|Hsub]|Hsub].
  - (* subexpr e1 e2_1 *)
    apply (IHe2_1 (Fuint 1) Logic.eq_refl Hsub) ; clear IHe2_1 IHe2_2 IHe2_3.
    move /andP : Hf2 => [/forallP Hf2 _].
    specialize (Hf2 p) ; move /implyP : Hf2 => Hf2 ; apply Hf2.
    by rewrite eq_refl andTb addn1 ltnS -eqn_leq eq_refl //.
  - (* subexpr e1 e2_2 *)
    by apply (IHe2_2 gt2_2 Logic.eq_refl Hsub Logic.eq_refl).
  - (* subexpr e1 e2_3 *)
    apply (IHe2_3 gt2_3 Logic.eq_refl Hsub).
    move /andP : Hf2 => [_ Hf2].
    by exact Hf2.
* (* Eref *)
  (* perhaps need a separate lemma with a different induction
     (on type_of_href?) to prove this part. 
     Or need a more strict condition?

     Here I could use some help. But let's first see whether this lemma is actually needed. *)
  admit.
* (* Earray *)
  clear -Hte2.
  destruct a ; simpl in Hte2.
  + destruct (type_of_hfexpr o h summ) ; by discriminate Hte2.
  + destruct (type_of_hfexpr o h summ) ; last by discriminate Hte2.
    destruct (type_of_array_expr o a summ) as [[| |]|] ; try by discriminate Hte2.
    destruct (unified_type f f0) ; by discriminate Hte2.
* (* Ebundle *)
  clear -Hte2.
  destruct b ; simpl in Hte2.
  + by discriminate Hte2.
    destruct f ;
        first (destruct (type_of_hfexpr (flip_orient o) h summ)) ;
        last  (destruct (type_of_hfexpr o h summ)) ;
        try by discriminate Hte2.
    1,2: destruct (type_of_bundle_expr o b summ) as [[| |]|] ; by discriminate Hte2.
* (* Etobedefined *)
  destruct (e1 == Etobedefined f) eqn: He1 ; last by discriminate Hsub.
  by rewrite (elimT eqP He1) //.
* (* Eundefinedonpurpose *)
  destruct (e1 == Eundefinedonpurpose f) eqn: He1 ; last by discriminate Hsub.
  by rewrite (elimT eqP He1) //.
Admitted.

(**********************************)
(* modifying connection summaries *)
(**********************************)

(* assign a new value to variable v, which may or may not be defined in oldsumm *)
Definition chg_ext_summ_nocheck (oldsumm : summaryType) (v : var) (new_value : kind * ftype * hfexpr * hfexpr) : summaryType :=
    existT summaryType_func
           (v :: projT1 oldsumm)
           (finfun (fun w => (if val w == v then new_value
                              else match insub (sT := seq_sub (projT1 oldsumm)) (val w) with
                                   | Some w' => projT2 oldsumm w'
                                   | None => new_value (* a dummy value -- False_rect would be possible but is more difficult to handle in proofs *)
                                   end))).

Lemma chg_ext_summ_nocheck_is_correct (oldsumm : summaryType) (v : var) (new_value : kind * ftype * hfexpr * hfexpr) :
        app_summ (chg_ext_summ_nocheck oldsumm v new_value) v = Some new_value
    /\
        forall w : var, w <> v ->
            app_summ (chg_ext_summ_nocheck oldsumm v new_value) w = app_summ oldsumm w.
Proof.
split.
* (* first conjunct *)
  unfold app_summ, insub ; simpl.
  destruct idP ; simpl.
  + (* idP is ReflectT *)
    by rewrite ffunE /ssval eq_refl //.
  + (* idP is ReflectF *)
    by rewrite in_cons eq_refl orTb // in n.
* (* second conjunct *)
  intros w Hwnotv.
  unfold app_summ, insub at 1 ; simpl.
  destruct idP ; simpl.
  + (* idP is ReflectT *)
    rewrite ffunE /ssval (introF eqP Hwnotv).
    rewrite in_cons (introF eqP Hwnotv) orFb in i.
    by rewrite (insubT (T := var) _ i) //.
  + (* idP is ReflectF *)
    rewrite in_cons (introF eqP Hwnotv) orFb in n.
    by rewrite (insubN (seq_sub (projT1 oldsumm)) (introT negP n)) //.
Qed.

(* assign a new value to an element of oldsumm, or extend its domain with a new element *)
Definition chg_ext_summ (oldsumm : summaryType) (v : var) (new_value : kind * ftype * hfexpr * hfexpr) : option summaryType :=
    if number_of_parts (snd (fst (fst new_value))) == 0
    then None
    else let newsumm := chg_ext_summ_nocheck oldsumm v new_value
         in match insub (sT := component_part newsumm) (v, 0) with
            | Some v0 => if expr_is_not_cyclic (snd (fst new_value)) Nflip   v0 &&
                            expr_is_not_cyclic (snd      new_value ) Flipped v0
                         then Some newsumm
                         else None
            | None => None
            end.

Lemma chg_ext_summ_succeeds_correctly (oldsumm : summaryType) (v : var) (new_value : kind * ftype * hfexpr * hfexpr) :
    match chg_ext_summ oldsumm v new_value with
    | Some newsumm =>     app_summ newsumm v = Some new_value
                      /\
                          forall w : var, w <> v -> app_summ newsumm w = app_summ oldsumm w
    | None => True
    end.
Proof.
destruct (chg_ext_summ oldsumm v new_value) as [newsumm|] eqn: Happ_summ ; last by trivial.
unfold chg_ext_summ in Happ_summ.
destruct (number_of_parts (snd (fst (fst new_value))) == 0) ;
      first by discriminate.
destruct insub as [v0|] eqn: Hi_v0 in Happ_summ ;
      last by discriminate.
destruct (expr_is_not_cyclic (snd (fst new_value)) Nflip v0 &&
              expr_is_not_cyclic (snd new_value) Flipped v0) eqn: Hacyclic ;
      last by discriminate.
inversion Happ_summ as [Happ_summ'] ; clear Happ_summ Happ_summ' newsumm.
by apply chg_ext_summ_nocheck_is_correct.
Qed.

Lemma chg_ext_summ_fails_correctly (oldsumm : summaryType) (v : var) (new_value : kind * ftype * hfexpr * hfexpr) :
        (forall (p1 p2 : component_part oldsumm), connect (grel (dep_graph oldsumm)) p1 p2 -> connect (grel (dep_graph oldsumm)) p2 p1 -> p1 = p2)
    ->
        chg_ext_summ oldsumm v new_value = None
    <->
        let t := snd (fst (fst new_value)) in let enf := snd (fst new_value) in let efl := snd new_value
        in     number_of_parts t = 0
           \/
               let newsumm := chg_ext_summ_nocheck oldsumm v new_value
               in     type_of_hfexpr Source enf newsumm <> Some t
                  \/
                      type_of_hfexpr Sink efl newsumm <> Some t
                  \/
                      exists i : nat,
                          (* there is a cycle from the ith component of new_value to (v, i) *)
                          match insub (sT := component_part newsumm) (v, i) with
                          | Some vi => match select_part t enf i, select_part t efl i with
                                       | Some (Nflip, e'), Some (Nflip, _)
                                       | Some (Flipped, _), Some (Flipped, e') => exists p1 : component_part newsumm,
                                                                                          expr_depends_on e' p1
                                                                                      /\
                                                                                          connect (grel (dep_graph newsumm)) p1 vi
                                       | _, _ => False
                                       end
                          | None => False
                          end.
Proof.
intro Holdsumm_acyclic.
specialize (chg_ext_summ_nocheck_is_correct oldsumm v new_value) ; intros [Hchg_ext_summ_nocheck_v _].
destruct new_value as [[[k t] enf] efl] ; simpl fst ; simpl snd.
split.
* (* implication -> *)
  intro Hchg_ext_summ.
  (*destruct chg_ext_summ as [ces|] eqn: Hchg_ext_summ' in Hchg_ext_summ ;
        first by discriminate.
  clear Hchg_ext_summ.*)
  rewrite /chg_ext_summ /fst /snd in Hchg_ext_summ.
  destruct (number_of_parts t == 0) eqn: Hnp0 ;
        first by left ; exact (elimT eqP Hnp0).
  apply negbT in Hnp0.
  right.
  destruct insub as [v0|] eqn: Hi_v0 in Hchg_ext_summ ;
  unfold insub in Hi_v0 ;
  destruct idP in Hi_v0 ;
  try (by discriminate) ;
        last by specialize (defined_is_in_parts_of (chg_ext_summ_nocheck oldsumm v (k, t, enf, efl)) (v, 0)) ;
                intro H ;
                rewrite /is_defined_part /fst /snd Hchg_ext_summ_nocheck_v lt0n in H ;
                apply H, n in Hnp0.
  inversion Hi_v0 as [Hi_v0'].
  replace v0 with (Sub (sT := seq_sub (parts_of (chg_ext_summ_nocheck oldsumm v (k, t, enf, efl)))) (v, 0) i) in Hchg_ext_summ.
  clear v0 Hi_v0 Hi_v0'.
  destruct (expr_is_not_cyclic enf Nflip (Sub (v, 0) i) &&
            expr_is_not_cyclic efl Flipped (Sub (v, 0) i)) eqn: Hacyclic ;
        rewrite Hacyclic in Hchg_ext_summ ;
        first by discriminate.
  clear Hchg_ext_summ.
  apply negbT in Hacyclic.
  rewrite negb_and in Hacyclic.
  move /orP : Hacyclic => [Hacyclic | Hacyclic].
  * (* enf becomes cyclic *)
    clear Hchg_ext_summ_nocheck_v.
    induction enf ; simpl ; simpl in Hacyclic.
    - (* Econst *)
      by discriminate Hacyclic.
    - (* Ecast *)
      destruct [forall p1, ~~(expr_depends_on enf p1 &&
                              connect (grel (dep_graph (chg_ext_summ_nocheck oldsumm v (k, t, Ecast u enf, efl))))
                                      p1
                                      {| ssval := (v, 0); ssvalP := i |})] eqn: Hf ;
            rewrite Hf // in Hacyclic.
      rewrite -negb_exists in Hf ; move /existsP : Hf => [p1 /andP Hf].
      destruct t as [gt| |] ; simpl ;
            try (by left ;
                    destruct u, (type_of_hfexpr Passive enf) as [[[| | | |]| |]|] ;
                    done).
      right ; right.
      exists 0.
      rewrite insubT.
      exists p1.
      by exact Hf.
    - (* Eprim_unop *)
      destruct [forall p1, ~~(expr_depends_on enf p1 &&
                               connect (grel (dep_graph (chg_ext_summ_nocheck oldsumm v (k, t, Eprim_unop e enf, efl))))
                                       p1
                                       {| ssval := (v, 0); ssvalP := i |})] eqn: Hf ;
            rewrite Hf // in Hacyclic.
      rewrite -negb_exists in Hf ; move /existsP : Hf => [p1 /andP Hf].
      destruct t as [[w|w| | |]|t0 m|] ; simpl ;
            try (by left ;
                    destruct (type_of_hfexpr Passive enf) as [[[| | | |]| |]|], e ;
                    try (by done) ;
                    try (by destruct (n1 <= n0 < n) ; done) ;
                    destruct (n0 <= n) ; done).
      1,2: right ; right.
      1,2: exists 0.
      1,2: rewrite insubT.
      1,2: exists p1.
      1,2: by exact Hf.
    - (* Eprim_binop *)
      destruct [forall p1, ~~((expr_depends_on enf1 p1 || expr_depends_on enf2 p1) &&
                              connect (grel (dep_graph (chg_ext_summ_nocheck oldsumm v (k, t, Eprim_binop e enf1 enf2, efl))))
                                      p1
                                      {| ssval := (v, 0); ssvalP := i |})] eqn: Hf ;
            rewrite Hf // in Hacyclic.
      rewrite -negb_exists in Hf ; move /existsP : Hf => [p1 /andP Hf].
      destruct t as [[w|w| | |]|t0 m|] ; simpl ;
            try (by left ;
                    destruct (type_of_hfexpr Passive enf1) as [[[| | | |]| |]|], e ;
                    try (by done) ;
                    destruct (type_of_hfexpr Passive enf2) as [[[| | | |]| |]|] ;
                    done).
      1,2: right ; right.
      1,2: exists 0.
      1,2: rewrite insubT.
      1,2: exists p1.
      1,2: exact Hf.
    - (* Emux *)
      destruct (expr_is_not_cyclic enf2 Nflip {| ssval := (v, 0); ssvalP := i |}) as [siz2|] eqn: He2c ;
            rewrite He2c // in Hacyclic.
      destruct ([forall (p2' | (v == fst (ssval p2')) && (snd (ssval p2') < 0 + siz2)),
                             expr_is_not_cyclic (summ := chg_ext_summ_nocheck oldsumm v (k, t, Emux enf1 enf2 enf3, efl)) enf1 Nflip p2'] &&
                expr_is_not_cyclic enf3 Nflip {| ssval := (v, 0); ssvalP := i |}) eqn: Henf13 ;
            rewrite Henf13 // in Hacyclic.
      apply negbT in Henf13 ; rewrite negb_and in Henf13 ;
      move /orP : Henf13 => [He1c|He3c].
      (* now we have three cases: He1c, He3c, and He2c *)
      * (* enf1 is cyclic *)
        move /forallPn : He1c => [p2 He1c].
        rewrite negb_imply in He1c.
        move /andP : He1c => [/andP [/eqP Hp21 Hp22] He1c].
        destruct (type_of_hfexpr Passive enf1 (chg_ext_summ_nocheck oldsumm v (k, t, Emux enf1 enf2 enf3, efl))) as [[[[|[|]]| | | |]| |]|] eqn: Htypenf1 ;
              try (by left ; done).
        destruct (type_of_hfexpr Source enf2 (chg_ext_summ_nocheck oldsumm v (k, t, Emux enf1 enf2 enf3, efl))) as [t2|] eqn: Htypenf2 ;
              last (by left ; done).
        destruct (type_of_hfexpr Source enf3 (chg_ext_summ_nocheck oldsumm v (k, t, Emux enf1 enf2 enf3, efl))) as [t3|] eqn: Htypenf3 ;
              last (by left ; done).
        destruct (unified_type t2 t3 == Some t) eqn: Ht2t3 ;
              last (by left ;
                       destruct (unified_type t2 t3) ;
                       first exact (elimF eqP Ht2t3) ; last done).
        move /eqP : Ht2t3 => Ht2t3.
        right.
        destruct (type_of_hfexpr Sink efl (chg_ext_summ_nocheck oldsumm v (k, t, Emux enf1 enf2 enf3, efl)) == Some t) eqn: Htypefl ;
              last (by left ;
                       destruct (type_of_hfexpr Sink efl (chg_ext_summ_nocheck oldsumm v (k, t, Emux enf1 enf2 enf3, efl))) ;
                       first exact (elimF eqP Htypefl) ; last done).
        move /eqP : Htypefl => Htypefl.
        right.
        assert (Htypemux : type_of_hfexpr Source (Emux enf1 enf2 enf3) (chg_ext_summ_nocheck oldsumm v (k, t, Emux enf1 enf2 enf3, efl)) = Some t)
              by (simpl ; rewrite Htypenf1 Htypenf2 Htypenf3 Ht2t3 //).
        (*generalize (parts_of_is_defined (chg_ext_summ_nocheck oldsumm v (k, t, Emux enf1 enf2 enf3, efl)) (val p2) (valP p2)) ;
        intro Hp2 ; simpl in Hp2.
        unfold is_defined_part, app_summ in Hp2.
        destruct (insub (sT := seq_sub (projT1 (chg_ext_summ_nocheck oldsumm v (k, t, Emux enf1 enf2 enf3, efl)))) (fst (ssval p2))) eqn: Hins2 ;
              rewrite Hins2 // in Hp2.
        rewrite -Hp21 in Hins2.*)
        exists (snd (ssval p2)).
        rewrite {3}Hp21 -surjective_pairing valK.
        assert (forall (o1 o2 : forient) (e1 e2 : hfexpr) (summ : summaryType) (n : nat),
                type_of_hfexpr o1 e1 summ = Some t ->
                type_of_hfexpr o2 e2 summ = Some t ->
                match select_part t e1 n, select_part t e2 n with
                | Some (fl1, _), Some (fl2, _) => fl1 == fl2
                | _, _ => true
                end) by admit.
        specialize (H Source Sink (Emux enf1 enf2 enf3) efl
                      (chg_ext_summ_nocheck oldsumm v (k, t, Emux enf1 enf2 enf3, efl))
                      (snd (ssval p2))
                      Htypemux Htypefl).
        (* This is not yet sufficient, as the assertion does not cover the case
           that one (Emux ...) and efl allows to select a part while the other doesn't.
           This should be guarded against?
           Perhaps a lemma: all operations on summ preserve the type correctness? *)

(* More generally, while the above lemma is nice to have,
   let's first continue and see whether it is actually needed. 

   I could use some help here, but again let's first see if such a lemma is actually needed. *)
Admitted.

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
                           | Some ps => if vi \in projT1 ps then None
                                        else chg_ext_summ ps vi (Inport, ti, Etobedefined ti, Etobedefined ti)
                           | None => None
                           end
  | Foutput vo to :: pp' => match PortSumm pp' with
                            | Some ps => if vo \in projT1 ps then None
                                         else chg_ext_summ ps vo (Outport, to, Etobedefined to, Etobedefined to)
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
    let br := base_ref r
    in match app_summ oldsumm br with
       | Some (k, t, enf, efl) => if k==Node
                                  then None
                                  else match type_of_href_base r t with
                                       | Some (fl, _) => match (if fl==Nflip
                                                                then (replace_subexpr enf r t new_e, Some efl)
                                                                else (Some enf, replace_subexpr efl r t new_e)) with
                                                         | (Some enf', Some efl') => chg_ext_summ oldsumm br (k, t, enf', efl')
                                                         | _ => None
                                                         end
                                       | None => None
                                       end
       | None => None
       end.

Definition bidirectional_connect (oldsumm : summaryType) (r1 r2 : href) : option summaryType :=
(* bidirectional connect statement: the writable parts of r1 and r2 are assigned the corresponding part of the other.
   (This obviously only works if the types of r1 and r2 are compatible. *)
    let br1 := base_ref r1 in let br2 := base_ref r2
    in match app_summ oldsumm br1, app_summ oldsumm br2 with
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
                                                                  (Some enf2', Some efl2') => match chg_ext_summ oldsumm br1 (k1, t1, enf1', efl1') with
                                                                                              | Some newsumm => chg_ext_summ newsumm br2 (k2, t2, enf2', efl2')
                                                                                              | None => None
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
    let br := base_ref r
    in match app_summ oldsumm br with
       | Some (k, t, enf, efl) => if k==Node
                                  then None
                                  else match type_of_href_base r t with
                                       | Some (fl, rt) => match (if fl==Nflip
                                                                 then (replace_subexpr enf r t (Eundefinedonpurpose rt), Some efl)
                                                                 else (Some enf, replace_subexpr efl r t (Eundefinedonpurpose rt))) with
                                                          | (Some enf', Some efl') => chg_ext_summ oldsumm br (k, t, enf', efl')
                                                          | _ => None
                                                          end
                                       | None => None
                                       end
       | None => None
       end.

(*
Fixpoint seq_intersect (s1 s2 : seq var) : seq var :=
    match s1 with
    | [::] => [::]
    | v :: s1' => if v \in s2
                  then v :: seq_intersect s1' s2
                  else seq_intersect s1' s2
    end.

Lemma when_summ_helper {v : var} {truesumm falsesumm : summaryType} :
    v \in projT1 truesumm ++ projT1 falsesumm ->
    app_summ truesumm v = None ->
    app_summ falsesumm v = None -> False.
Proof.
intros vinconcat Ht Hf.
rewrite mem_cat in vinconcat.
move /orP : vinconcat => vinconcat.
destruct vinconcat as [vinsumm | vinsumm].
2 : rename falsesumm into summ ; rename Hf into H.
rename truesumm into summ ; rename Ht into H.
all: unfold app_summ in H.
all: rewrite (insubT (fun v : var => v \in projT1 summ) vinsumm) // in H.
Qed.

Lemma when_true_empty_helper {v : var} {oldsumm truesumm : summaryType} {x : kind * ftype * hfexpr * hfexpr} :
    is_subset (projT1 oldsumm) (projT1 truesumm) ->
    app_summ oldsumm v = Some x ->
    app_summ truesumm v = None -> False.
Proof.
intros Hsub Ho Ht.
destruct (v \in projT1 oldsumm) eqn: Hvino.
(* v \in projT1 oldsumm *)
  assert (v \in projT1 truesumm).
        revert Hsub Hvino.
        clear Ho Ht.
        generalize (projT1 oldsumm).
        induction l ; intros Hsub Hvino.
        (* base case *)
          by rewrite in_nil // in Hvino.
        (* induction step *)
          simpl is_subset in Hsub ; move /andP : Hsub => Hsub.
          rewrite in_cons in Hvino ; move /orP : Hvino => Hvino.
          destruct Hvino as [Hvino | Hvino].
          (* v == a *)
            move /eqP : Hvino => Hvino ; rewrite Hvino //.
            by apply Hsub.
          (* v \in l *)
            by apply (IHl (proj2 Hsub) Hvino).
  unfold app_summ in Ht.
  by rewrite (insubT (fun v : var => v \in projT1 truesumm) H) // in Ht.
(* v \notin projT1 oldsumm *)
  unfold app_summ in Ho.
  by rewrite (insubF (seq_sub (projT1 oldsumm)) Hvino) // in Ho.
Qed.

Lemma when_old_empty_helper {v : var} {oldsumm truesumm falsesumm : summaryType} {x y : kind * ftype * hfexpr * hfexpr} :
    [forall x : seq_sub (projT1 truesumm), (val x \in projT1 oldsumm) || (val x \notin projT1 falsesumm)] ->
    app_summ oldsumm v = None ->
    app_summ truesumm v = Some x ->
    app_summ falsesumm v = Some y -> False.
Proof.
intros Htos Ho Ht Hf.
move /forallP : Htos => Htos.
destruct (v \in projT1 truesumm) eqn: Hvint.
(* v \in projT1 truesumm *)
  specialize (Htos (Sub v Hvint)).
  rewrite SubK in Htos.
  move /orP : Htos => [Htos | Htos].
  (* v \in projT1 oldsumm *)
    unfold app_summ in Ho.
    by rewrite (insubT (fun v : var => v \in projT1 oldsumm) Htos) // in Ho.
  (* v \notin projT1 falsesumm *)
    unfold app_summ in Hf.
    by rewrite (insubN (seq_sub (projT1 falsesumm)) Htos) // in Hf.
(* v \notin projT1 truesumm *)
  unfold app_summ in Ht.
  by rewrite (insubF (seq_sub (projT1 truesumm)) Hvint) // in Ht.
Qed. *)

(* calculate the combination of true and false branches.
   This checks one dependency, namely that components defined anew in 
   the true branch are not defined in the false branch.  The present version
   uses the proof that this check passed to create a False_rect in one case.
   However, if this dependency leads to problems in proofs, one might just
   return an arbitrary value there instead. *)
Definition when_summ (c : hfexpr) (oldsumm truesumm falsesumm : summaryType) : option summaryType :=
    if [forall x : seq_sub (projT1 truesumm), (val x \in projT1 oldsumm) || (val x \notin projT1 falsesumm)] 
    then Some (existT summaryType_func (projT1 truesumm ++ projT1 falsesumm)
                      (finfun (fun w => match app_summ oldsumm (val w) as ov',
                                              app_summ truesumm (val w) as tv', 
                                              app_summ falsesumm (val w) as fv' with
                                        | Some (k, t, _, _), Some (_, _, enft, eflt), Some (_, _, enff, eflf) => (k, t, if enft==enff then enft else Emux c enft enff, if eflt==eflf then eflt else Emux c eflt eflf)
                                        | _, Some tv, _ => tv
                                        | _, _, Some fv => fv
                                        | _, _, _ => (Inport, Gtyp (Fuint 0), Etobedefined (Gtyp (Fuint 0)), Etobedefined (Gtyp (Fuint 0))) (* cannot happen, so just give back a dummy value *)
                                        end)))
     else None.

(* statement summary: construct the function that contains all connections mandated by the statements in ss *)
Fixpoint StmtSumm (oldsumm : summaryType) (ss : hfstmt_seq) : option summaryType :=
    match ss with
    | Qnil => Some oldsumm
    | Qcons s ss' => match StmtSumm_1 oldsumm s with
                     | Some intsumm => StmtSumm intsumm ss'
                     | None => None
                     end
    end
with StmtSumm_1 (oldsumm : summaryType) (s : hfstmt) : option summaryType :=
    match s with
    | Sskip => Some oldsumm
    | Swire vw t => if vw \notin projT1 oldsumm
                    then chg_ext_summ oldsumm vw (Wire, t, Etobedefined t, Etobedefined t)
                    else None
    | Sreg vr t => (* note that t must be passive *)
                   if vr \notin projT1 oldsumm
                   then chg_ext_summ oldsumm vr (Register, t, Eref (Eid vr), Eref (Eid vr))
                   else None
    | Snode vn e => (* the expression must be passive *)
                    if vn \notin projT1 oldsumm
                    then match type_of_hfexpr Passive e oldsumm (* this requires that widths are already inferred; otherwise, the width of the node may be too small *) with
                         | Some t => chg_ext_summ oldsumm vn (Node, t, e, Eundefinedonpurpose t)
                         | None => None
                         end
                    else None
    | Sfcnct r1 (Eref r2) => bidirectional_connect oldsumm r1 r2
    | Sfcnct r e => unidirectional_connect oldsumm r e
    | Sinvalid r => invalidate oldsumm r
    | Swhen c sst ssf => match StmtSumm oldsumm sst, StmtSumm oldsumm ssf with
                         | Some truesumm, Some falsesumm => when_summ c oldsumm truesumm falsesumm
                         | _, _ => None
                         end
    end.

Fixpoint is_subset (s1 s2 : seq var) : bool :=
    match s1 with
    | [::] => true
    | v :: s1' => (v \in s2) && is_subset s1' s2
    end.

Lemma is_subset_cat (s t : seq var) : is_subset s (t ++ s).
Proof.
generalize t ; clear t.
induction s ; simpl.
(* base case for s *)
  by done.
(* induction step for s *)
  intro t.
  apply (introT andP).
  split.
  (* left conjunct *)
    induction t ; simpl.
    (* base case for t *)
      by apply mem_head.
    (* induction step for t *)
      by rewrite in_cons IHt orbT //.
  (* right conjunct *)
    by rewrite -cat_rcons IHs //.
Qed.

Lemma is_subset_cons (a : var) (s : seq var) : is_subset s (a :: s).
Proof.
by rewrite -cat1s is_subset_cat //.
Qed.

Lemma is_subset_refl (s : seq var) : is_subset s s.
Proof.
induction s ; simpl.
(* base case *)
  by done.
(* induction step *)
  apply (introT andP).
  split.
  (* left conjunct *)
    by apply mem_head.
  (* right conjunct *)
    by apply is_subset_cons.
Qed.

Lemma in_subset_trans {a : var} {s t : seq var} : a \in s -> is_subset s t -> a \in t.
Proof.
generalize t ; clear t.
induction s ; simpl.
(* base case *)
  by rewrite in_nil //.
(* induction step *)
  rewrite in_cons.
  intros t Has Hst.
  move /andP : Hst => [Ha0t Hst].
  destruct (a == a0) eqn: Haa0.
  (* case a == a0 *)
    by rewrite (elimT eqP Haa0) //.
  (* case a != a0 *)
    rewrite orFb in Has.
    by exact (IHs t Has Hst).
Qed.

Lemma is_subset_trans {t s u : seq var} : is_subset s t -> is_subset t u -> is_subset s u.
Proof.
induction s ; simpl.
(* base case *)
  by done.
(* induction step for s *)
  intros Hast Htu.
  move /andP : Hast => [Hat Hst].
  apply (introT andP) ; split.
  (* left conjunct *)
    by exact (in_subset_trans Hat Htu).
  (* right conjunct *)
    by exact (IHs Hst Htu).
Qed.

Lemma test (x : var) (s : seq var) : x \in x :: s.
Proof.
rewrite in_cons eq_refl orTb //.
Qed.

Print test.

Check (fun (x : var) (s : seq var) =>
(eq_ind_r is_true
          (eq_ind_r (fun xisx => xisx || (x \in s))
                    (eq_ind_r is_true is_true_true (orTb (x \in s)))
                    (eq_refl x))
          (in_cons x s x))).

Lemma StmtSumm_only_extends (oldsumm : summaryType) (ss : hfstmt_seq) (newsumm : summaryType) :
    StmtSumm oldsumm ss = Some newsumm ->
    is_subset (projT1 oldsumm) (projT1 newsumm)
with StmtSumm_1_only_extends (oldsumm : summaryType) (s : hfstmt) (newsumm : summaryType) :
    StmtSumm_1 oldsumm s = Some newsumm ->
    is_subset (projT1 oldsumm) (projT1 newsumm).
Proof.
* clear StmtSumm_only_extends.
  revert oldsumm.
  induction ss as [|s ss'] ; intro oldsumm ; simpl.
  + (* base case *)
    intro Hss ; inversion Hss as [Hosns] ; clear Hss oldsumm Hosns.
    apply is_subset_refl.
  + (* induction step *)
    specialize (StmtSumm_1_only_extends oldsumm s).
    destruct (StmtSumm_1 oldsumm s) as [intsumm|] ; last by discriminate.
    specialize (StmtSumm_1_only_extends intsumm Logic.eq_refl).
    intro Hstmtsumm_ss'.
    specialize (IHss' intsumm Hstmtsumm_ss').
    by apply (is_subset_trans StmtSumm_1_only_extends), IHss'.
* clear StmtSumm_1_only_extends.
  destruct s as [|vw t|vr t|vn e|r e|r|c sst ssf] ; simpl.
  + (* Skip *)
    intro Hss ; inversion Hss as [Hosns] ; clear Hss oldsumm Hosns.
    apply is_subset_refl.
  + (* Swire *)
    intro Hss.
    destruct (vw \notin projT1 oldsumm) eqn: Hvw ; rewrite Hvw // in Hss.
    unfold chg_ext_summ in Hss ; simpl in Hss.
    destruct (number_of_parts t == 0) ; first by discriminate Hss.
    destruct (insub (vw, 0)) ; last by discriminate Hss.
    inversion Hss ; clear Hss H0 newsumm.
    unfold chg_ext_summ_nocheck ; simpl.
    by apply is_subset_cons.
  + (* Sreg *)
    intro Hss.
    destruct (vr \notin projT1 oldsumm) eqn: Hvr ; rewrite Hvr // in Hss.
    unfold chg_ext_summ in Hss ; simpl in Hss.
    destruct (number_of_parts t == 0) ; first by discriminate Hss.
    destruct (insub (vr, 0)) as [s|] ; last by discriminate Hss.
    rewrite (proj1 (chg_ext_summ_nocheck_is_correct oldsumm vr (Register, t, Eref (Eid vr), Eref (Eid vr)))) in Hss.
    destruct (href_is_not_cyclic (Eid vr) Nflip t s) ; last by rewrite andFb // in Hss.
    rewrite andTb in Hss.
    destruct (href_is_not_cyclic (Eid vr) Flipped t s) ; last by discriminate Hss.
    simpl in Hss ; inversion Hss ; clear Hss H0 newsumm s.
    unfold chg_ext_summ_nocheck ; simpl.
    by apply is_subset_cons.
  + (* Snode *)
    intro Hss.
    destruct (vn \notin projT1 oldsumm) eqn: Hvn ; rewrite Hvn // in Hss.
    destruct (type_of_hfexpr Passive e oldsumm) as [t|] ; last by discriminate Hss.
    unfold chg_ext_summ in Hss ; simpl in Hss.
    destruct (number_of_parts t == 0) ; first by discriminate Hss.
    destruct (insub (vn, 0)) as [s|] ; last by discriminate Hss.
    rewrite andbT in Hss.
    destruct (expr_is_not_cyclic e Nflip s) ; last by discriminate Hss.
    simpl in Hss ; inversion Hss ; clear Hss H0 newsumm s n.
    unfold chg_ext_summ_nocheck ; simpl.
    by apply is_subset_cons.
  + (* Sfcnct *)
    destruct e as [f t'|u e'|op e'|op e1 e2|c e1 e2|r'|ar|bu|t'|t'].
    - (* Econst, Ecast, Eprim_unop, Eprim_binop, Emux, Earray, Ebundle, Etobedefined, Eundefinedonpurpose *)
      1-5,7-10: intro Hss.
      1-9: unfold unidirectional_connect in Hss.
      1-9: destruct (app_summ oldsumm (base_ref r)) as [[[[[| | | |] t] enf] efl]|] ; simpl in Hss ; try by discriminate Hss.
      1-36: destruct (type_of_href_base r t) as [[fl _]|] ; simpl ; last by discriminate Hss.
      1-36: destruct (if fl == Nflip
                     then (replace_subexpr enf r t _, Some efl)
                     else (Some enf, replace_subexpr efl r t _)) as [[enf'|] [efl'|]] ; try by discriminate Hss.
      1-36: unfold chg_ext_summ in Hss ; simpl in Hss.
      1-36: destruct (number_of_parts t == 0) ; first by discriminate Hss.
      1-36: destruct (insub (base_ref r, 0)) as [s|] ; last by discriminate Hss.
      1-36: destruct (expr_is_not_cyclic enf' Nflip s) ; last by rewrite andFb // in Hss.
      1-36: rewrite andTb in Hss.
      1-36: destruct (expr_is_not_cyclic efl' Flipped s) ; last by discriminate Hss.
      1-36: simpl in Hss ; inversion Hss ; clear Hss H0 newsumm s n.
      1-36: unfold chg_ext_summ_nocheck ; simpl.
      1-36: by apply is_subset_cons.
    - (* Eref *)
      intro Hss.
      unfold bidirectional_connect in Hss.
      destruct (app_summ oldsumm (base_ref r)) as [[[[[| | | |] t] enf] efl]|],
               (app_summ oldsumm (base_ref r')) as [[[[[| | | |] t'] enf'] efl']|] ; simpl in Hss ; try by discriminate Hss.
      1-16: destruct (type_of_href_base r t') as [[fl _]|],
                     (type_of_href_base r' t') as [[fl' _]|] ; simpl ; try by discriminate Hss.
      1-16: destruct (if fl == Nflip
                      then (replace_subexpr enf r t (Eref r'), Some efl)
                      else (Some enf, replace_subexpr efl r t (Eref r'))) as [[enf1|] [efl1|]],
                     (if fl' == Flipped
                      then (replace_subexpr enf' r' t' (Eref r), Some efl')
                      else (Some enf', replace_subexpr efl' r' t' (Eref r))) as [[enf2|] [efl2|]] ;
            try by discriminate Hss.
      1-16: unfold chg_ext_summ at 1 in Hss ; simpl in Hss.
      1-16: destruct (number_of_parts t == 0) ; first by discriminate Hss.
      1-16: destruct (insub (base_ref r, 0)) as [s|] ; last by discriminate Hss.
      1-16: destruct (expr_is_not_cyclic enf1 Nflip s) ; last by rewrite andFb // in Hss.
      1-16: rewrite andTb in Hss.
      1-16: destruct (expr_is_not_cyclic efl1 Flipped s) ; last by discriminate Hss.
      1-16: simpl in Hss.
      1-16: unfold chg_ext_summ in Hss ; simpl in Hss.
      1-16: destruct (number_of_parts t' == 0) ; first by discriminate Hss.
      1-16: destruct (insub (base_ref r', 0)) as [s'|] ; last by discriminate Hss.
      1-16: destruct (expr_is_not_cyclic enf2 Nflip s') ; last by rewrite andFb // in Hss.
      1-16: rewrite andTb in Hss.
      1-16: destruct (expr_is_not_cyclic efl2 Flipped s') ; last by discriminate Hss.
      1-16: simpl in Hss ; inversion Hss ; clear Hss H0 newsumm s s' n n0 n1 n2.
      1-16: unfold chg_ext_summ_nocheck ; simpl.
      1-16: rewrite -cat1s -cat_rcons ; by apply is_subset_cat.
  + (* Sinvalid *)
    intro Hss.
    unfold invalidate in Hss.
    destruct (app_summ oldsumm (base_ref r)) as [[[[[| | | |] t] enf] efl]|] ; simpl in Hss ; try by discriminate Hss.
    1-4: destruct (type_of_href_base r t) as [[fl rt]|] ; last by discriminate Hss.
    1-4: destruct (if fl == Nflip
                   then (replace_subexpr enf r t (Eundefinedonpurpose rt), Some efl)
                   else (Some enf, replace_subexpr efl r t (Eundefinedonpurpose rt))) as [[enf'|] [efl'|]] ;
         try by discriminate Hss.
    1-4: unfold chg_ext_summ in Hss ; simpl in Hss.
    1-4: destruct (number_of_parts t == 0) ; first by discriminate Hss.
    1-4: destruct (insub (base_ref r, 0)) as [s|] ; last by discriminate Hss.
    1-4: destruct (expr_is_not_cyclic enf' Nflip s) ; last by rewrite andFb // in Hss.
    1-4: rewrite andTb in Hss.
    1-4: destruct (expr_is_not_cyclic efl' Flipped s) ; last by discriminate Hss.
    1-4: simpl in Hss ; inversion Hss ; clear Hss H0 newsumm s n n0.
    1-4: unfold chg_ext_summ_nocheck ; simpl.
    1-4: by apply is_subset_cons.
  + (* Swhen *)
    intro Hss.
    destruct (StmtSumm oldsumm sst) as [truesumm|] ; last by discriminate Hss.
    specialize (StmtSumm_only_extends oldsumm ssf) ; rename StmtSumm_only_extends into Hssf.
    destruct (StmtSumm oldsumm ssf) as [falsesumm|] ; last by discriminate Hss.
    specialize (Hssf falsesumm Logic.eq_refl).
    unfold when_summ in Hss.
    destruct [forall x : seq_sub (projT1 truesumm), (val x \in projT1 oldsumm) || (val x \notin projT1 falsesumm)] ; last by discriminate Hss.
    inversion Hss ; simpl.
    by apply (is_subset_trans Hssf), is_subset_cat.
Qed.

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
   | n'.+1 => iterate (fun v : var => match app_summ summ v with
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

(*
Lemma empty_summary_is_well_founded : forall p : component_part, Acc (depends_on empty_summary) p.
Proof.
intros [p2 n2].
apply Acc_intro.
intros [p1 n1] H.
contradict H.
rewrite /depends_on /app_summ insubF //.
Qed.
*)

Lemma PortSumm_is_tobedefined :
forall (pp : seq hfport) (summ : summaryType),
      PortSumm pp = Some summ
   ->
      forall (c : var) (k : kind) (t : ftype) (e1 e2 : hfexpr),
            app_summ summ c = Some (k, t, e1, e2)
         ->
            (k = Inport \/ k = Outport) /\ e1 = Etobedefined t /\ e2 = Etobedefined t.
Proof.
induction pp.
* intros summ Hp c k t e1 e2 Hsumm.
  simpl PortSumm in Hp.
  inversion Hp.
  by rewrite -H0 /app_summ insubF // in Hsumm.
* intros summ Hp c k t e1 e2 Hsumm.
  simpl PortSumm in Hp.
  destruct a as [v' t'|v' t'].
  1,2: destruct (PortSumm pp) as [intsumm|] ; last by discriminate.
  1,2: specialize (IHpp intsumm Logic.eq_refl c k t e1 e2).
  1,2: destruct (v' \in projT1 intsumm) eqn: Hv' ; rewrite Hv' in Hp ; first by discriminate Hp.
    destruct (chg_ext_summ intsumm v' (Inport, t', Etobedefined t', Etobedefined t')) as [newsumm|] eqn: Hext ;
        last by discriminate Hp.
  2: destruct (chg_ext_summ intsumm v' (Outport, t', Etobedefined t', Etobedefined t')) as [newsumm|] eqn: Hext ;
        last by discriminate Hp.
  1,2: inversion Hp ; subst summ ; clear Hp.
  1,2: unfold chg_ext_summ in Hext ; simpl in Hext.
  1,2: destruct (number_of_parts t' == 0) ; first by discriminate Hext.
  1,2: destruct (insub (v', 0)) eqn: Hins ; last by discriminate Hext.
  1,2: inversion Hext ; subst newsumm ; clear Hext.
     generalize (chg_ext_summ_nocheck_is_correct intsumm v' (Inport, t', Etobedefined t', Etobedefined t')) ; intro Hcesn.
  2: generalize (chg_ext_summ_nocheck_is_correct intsumm v' (Outport, t', Etobedefined t', Etobedefined t')) ; intro Hcesn.
  1,2: destruct (c == v') eqn: Hcv' ; move /eqP : Hcv' => Hcv' ;
        last (by rewrite (proj2 Hcesn c Hcv') in Hsumm ;
                 apply IHpp, Hsumm).
  1,2: subst c ; rewrite (proj1 Hcesn) in Hsumm ; inversion Hsumm.
  1,2: split ; last by (split ; reflexivity).
  + left ; by reflexivity.
  + right ; by reflexivity.
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

(* We'd need something like "the relation is acyclic". 
The definition is perhaps first in Prop, then we can show that with finiteness of domain, it is in bool? 

Would it be easier to define a graph of all defined points,
the edge relation on it, and reject it if it contains a cycle? 

When there is a connect statement Sfcnct r e,
we should have that there is no connection from (any part of) e to r.
As long as this holds, the connect statement should be allowed.

The code then becomes something like:
if connect (depends_on oldsumm) e r then None else ...

Because connect requires a fingraph, we must have that depends_on is defined on a finType.
So oldsum is a finfun.

*)

(* The following relation is generic, for any finite graph, and is not used currently.
Definition acyclic {S : Type} (R : rel S) : Prop :=
    forall (x : S) (p : seq S), ~~cycle R (x :: p).
*)

a <= max(a, b) is a cyclic dependency that poses no problems in InferWidths,
but if a is not a register, it is a 



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

(* Keyin brought up the idea of evaluating statements right away,
   without first creating a statement summary.
   Then I suggest this scheme:
   - there are two copies of every variable: one to be read, one to be written.
   - in a preparatory run go through the statements and create each 
   - we walk through the statements and change the write-copy as needed.
   - if after the walkthrough the write-copy of a component is different from the read-copy,
     the values have not yet stabilized, we copy the write-values to the read-values,
     and walk through the statements another time.
     (registers are disregarded in this check.)
   - acyclicity guarantees that the number of iterations is bounded.
     we can probably prove: in every iteration there will be at least one statement
     that does not change any more.

   - Problem: a program like
       a <= 3
       b <= a
       a <= 5
     If we just test whether a has changed after it has been read,
     we get a wrong result: the program would appear to never stabilize.
     The correct behaviour is to write value 5 to b.
     That is why we need a read- and a write-copy: the write-copy of a becomes 3
     temporarily but b will be set to the value in the read-copy of a.
   - we need the data type of every aggregate-level component,
     but we can store the values per ground-level component.
     (That may simplify LowerTypes: the choiceType of var changes but then
     every component part identifier just becomes a component identifier.)

0. generate the data type structure of every module
   by going through their component definition statements
1. generate the data type structure of the module instances
   by going throught their instance statements
   (This generates a tree of instances --- every instance has an access path.)
2. initialize the write-copy of the component data of every instance with "Etobedefined t"
   (or, for registers, with "Eid r")
2. repeat
   2a. set the read-copy to the write-copy values for every module instance
       (but for registers, top-level unflipped inputs, and top-level flipped outputs, use their old value)
   2b. for every module instance:
       walk through the connection statements of the module and execute them (in order)
       (i.e. change the write-copy of the variables)
   until the read-copy is equal to the write-copy

Data needed in walking through the statements:
- per component, its kind and type (to determine e.g. the size of an array element)
  depends on the module, not on the instance
- per readable ground-level component, its read value (a number, not an expression)
  needs one copy per instance
- per writable ground-level component, its written value (also a number)
  needs one copy per instance

Data needed elsewhere:
- per register/top-level unflipped input/top-level flipped output component, its read value.
  needs one copy per register instance

*)




