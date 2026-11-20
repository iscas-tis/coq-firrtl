From Coq Require Import FunInd FMaps FMapAVL OrderedType.
From mathcomp Require Import ssreflect ssrbool ssrnat ssrint eqtype seq.
From simplssrlib Require Import Types SsrOrder FSets FMaps Tactics Var Store.
From nbits Require Import NBits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

  (****** Types Environment ******)

  (****** Ground Types ******)

  From Coq Require Import ZArith.

  Inductive fgtyp : Set :=
    Fuint : nat -> fgtyp
  | Fsint : nat -> fgtyp
  | Fuint_implicit : nat -> fgtyp (* unsigned integer with implicit width; the width must be at least the parameter value *)
  | Fsint_implicit : nat -> fgtyp (* signed integer with implicit width *)
  | Fuint_implicit_eq1 : fgtyp (* unsigned integer with implicit width; the width must be inferred to be equal to 1 *)
  | Fclock
  | Freset (* HiFIRRTL only *)
  | Fasyncreset
  (*| Fanalog : nat -> fgtyp*) (* TBD, HiFirrtl *)
  .

  (* Size of types *)

  Definition sizeof_fgtyp (t : fgtyp) : nat :=
    match t with
    | Fuint w
    | Fsint w
    | Fuint_implicit w
    | Fsint_implicit w => w
    (* | Fanalog w => w *)
    | _ => 1
    end.

  (* Equality of types *)

  Lemma fgtyp_eq_dec (x y : fgtyp) : {x = y} + {x <> y}.
  Proof. decide equality ; apply Nat.eq_dec. Qed.

  Definition fgtyp_eqn (x y : fgtyp) : bool :=
    match x, y with
    | Fuint wx, Fuint wy
    | Fsint wx, Fsint wy
    | Fuint_implicit wx, Fuint_implicit wy
    | Fsint_implicit wx, Fsint_implicit wy => wx == wy
    (* | Fanalog wx, Fanalog wy => wx == wy *)
    | Fuint_implicit_eq1, Fuint_implicit_eq1
    | Fclock, Fclock
    | Freset, Freset
    | Fasyncreset, Fasyncreset => true
    | _, _ => false
    end.

  Notation "x =? y" := (fgtyp_eqn x y).

  Lemma fgtyp_eqn_refl (x : fgtyp) : x =? x.
  Proof.
    destruct x; try (exact: eqxx|| done).
  Qed.

  Lemma fgtyp_eqn_eq (x y : fgtyp) : x =? y <-> x = y.
  Proof.
    split; first (destruct x; destruct y; move=> /= H);
      try (discriminate|| rewrite (eqP H); reflexivity).
    - done. - done. - done. - done.
    - move=> ->. exact: fgtyp_eqn_refl.
  Qed.

  Lemma fgtyp_eqn_sym (x y : fgtyp) : x =? y -> y =? x.
  Proof.
    move/fgtyp_eqn_eq => H. apply/fgtyp_eqn_eq. symmetry. assumption.
  Qed.

  Lemma fgtyp_eqn_trans (x y z : fgtyp) : x =? y -> y =? z -> x =? z.
  Proof.
    move/fgtyp_eqn_eq => Hxy. move/fgtyp_eqn_eq => Hyz. apply/fgtyp_eqn_eq.
    rewrite Hxy. assumption.
  Qed.

  #[export] Instance fgtyp_eqn_Reflexive : Reflexive (@fgtyp_eqn) := @fgtyp_eqn_refl.
  #[export] Instance fgtyp_eqn_Symmetric : Symmetric (@fgtyp_eqn) := @fgtyp_eqn_sym.
  #[export] Instance fgtyp_eqn_Transitive : Transitive (@fgtyp_eqn) := @fgtyp_eqn_trans.
  #[export] Instance fgtyp_eqn_Equivalence : Equivalence (@fgtyp_eqn) :=
    { Equivalence_Reflexive := fgtyp_eqn_Reflexive;
      Equivalence_Symmetric := fgtyp_eqn_Symmetric;
      Equivalence_Transitive := fgtyp_eqn_Transitive }.

  Lemma fgtyp_eqP : forall (x y : fgtyp), reflect (x = y) (x =? y).
  Proof.
    move=> x y. case H: (x =? y).
    - apply: ReflectT. apply/fgtyp_eqn_eq. assumption.
    - apply: ReflectF. move=> Heq. move/fgtyp_eqn_eq: Heq => Heq. rewrite Heq in H.
      discriminate.
  Qed.

  Definition fgtyp_eqMixin := EqMixin fgtyp_eqP.
  Canonical fgtyp_eqType := Eval hnf in EqType fgtyp fgtyp_eqMixin.
