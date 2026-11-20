From Coq Require Import FunInd FMaps FMapAVL OrderedType ZArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat ssrint eqtype seq fintype fingraph.
From simplssrlib Require Import Types SsrOrder FSets FMaps Tactics Var Store.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Delimit Scope firrtl with firrtl.

Section LoFirrtl.

  (****** Syntax ******)

  (****** Expressions ******)

  Inductive ucast : Set :=
  | AsUInt | AsSInt (*| AsFixed*) | AsClock | AsAsync .

  Lemma ucast_eq_dec : forall {x y : ucast}, {x = y} + {x <> y}.
  Proof.  decide equality.  Qed.
  Definition ucast_eqn (x y : ucast) : bool :=
  match x, y with
  | AsUInt, AsUInt | AsSInt, AsSInt | AsClock, AsClock
  | AsAsync, AsAsync => true
  | _, _ => false
  end.
  Lemma ucast_eqP : Equality.axiom ucast_eqn.
  Proof.
  unfold Equality.axiom, ucast_eqn.
  destruct x, y ; simpl ;
        try (by apply ReflectF ; discriminate) ;
        by apply ReflectT ; reflexivity.
  Qed.
  Canonical ucast_eqMixin := EqMixin ucast_eqP.
  Canonical ucast_eqType := Eval hnf in EqType ucast ucast_eqMixin.

  Inductive eunop : Set :=
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

  Lemma eunop_eq_dec : forall {x y : eunop}, {x = y} + {x <> y}.
  Proof.  decide equality ; apply Nat.eq_dec.  Qed.
  Definition eunop_eqn (x y : eunop) : bool :=
  match x, y with
  | Upad n, Upad m | Ushl n, Ushl m | Ushr n, Ushr m | Uhead n, Uhead m | Utail n, Utail m =>
        n == m
  | Ucvt, Ucvt | Uneg, Uneg | Unot, Unot | Uandr, Uandr | Uorr, Uorr | Uxorr, Uxorr => true
  | Uextr n n0, Uextr m m0 => (n == m) && (n0 == m0)
  | _, _ => false
  end.
  Lemma eunop_eqP : Equality.axiom eunop_eqn.
  Proof.
  unfold Equality.axiom, eunop_eqn.
  destruct x, y ; simpl ;
        try (by apply ReflectF ; discriminate) ;
        try (by apply ReflectT ; reflexivity).
  1,2,3,5,6: destruct (n == n0) eqn: Hn ; move /eqP : Hn => Hn ;
        first (by rewrite Hn ; apply ReflectT ; reflexivity) ;
        last  (by apply ReflectF ; contradict Hn ; injection Hn ; done).
  destruct (n == n1) eqn: Hn ; move /eqP : Hn => Hn ;
        last (by apply ReflectF ; contradict Hn ; injection Hn ; done).
  rewrite Hn andTb.
  destruct (n0 == n2) eqn: Hn0 ; move /eqP : Hn0 => Hn0 ;
        last (by apply ReflectF ; contradict Hn0 ; injection Hn0 ; done).
  rewrite Hn0 ; apply ReflectT ; reflexivity.
  Qed.
  Canonical eunop_eqMixin := EqMixin eunop_eqP.
  Canonical eunop_eqType := Eval hnf in EqType eunop eunop_eqMixin.

  Inductive bcmp : Set :=
  | Blt | Bleq | Bgt | Bgeq | Beq | Bneq.

  Lemma bcmp_eq_dec : forall {x y : bcmp}, {x = y} + {x <> y}.
  Proof.  decide equality.  Qed.
  Definition bcmp_eqn (x y : bcmp) : bool :=
  match x, y with
  | Blt, Blt | Bleq, Bleq | Bgt, Bgt | Bgeq, Bgeq | Beq, Beq | Bneq, Bneq => true
  | _, _ => false
  end.
  Lemma bcmp_eqP : Equality.axiom bcmp_eqn.
  Proof.
  unfold Equality.axiom, bcmp_eqn.
  destruct x, y ; simpl ;
        try (by apply ReflectF ; discriminate) ;
        by apply ReflectT ; reflexivity.
  Qed.
  Canonical bcmp_eqMixin := EqMixin bcmp_eqP.
  Canonical bcmp_eqType := Eval hnf in EqType bcmp bcmp_eqMixin.

  Inductive ebinop : Set :=
  | Badd
  | Bsub
  | Bmul
  | Bdiv
  | Brem
  (* | Bsdiv *)
  (* | Bsrem *)
  | Bcomp: bcmp -> ebinop
  | Bdshl
  | Bdshr
  | Band
  | Bor
  | Bxor
  | Bcat .

  Lemma ebinop_eq_dec : forall {x y : ebinop}, {x = y} + {x <> y}.
  Proof.  decide equality ; apply bcmp_eq_dec.  Qed.
  Definition ebinop_eqn (x y : ebinop) : bool :=
  match x, y with
  | Badd, Badd | Bsub, Bsub | Bmul, Bmul | Bdiv, Bdiv | Brem, Brem
  | Bdshl, Bdshl | Bdshr, Bdshr | Band, Band | Bor, Bor | Bxor, Bxor | Bcat, Bcat => true
  | Bcomp b, Bcomp c => b == c
  | _, _ => false
  end.
  Lemma ebinop_eqP : Equality.axiom ebinop_eqn.
  Proof.
  unfold Equality.axiom, ebinop_eqn.
  destruct x, y ; simpl ;
        try (by apply ReflectF ; discriminate) ;
        try (by apply ReflectT ; reflexivity).
  destruct (b == b0) eqn: Hb ; move /eqP : Hb => Hb ;
        first (by apply ReflectT ; rewrite Hb ; reflexivity) ;
        last  (by apply ReflectF ; injection ; done).
  Qed.
  Canonical ebinop_eqMixin := EqMixin ebinop_eqP.
  Canonical ebinop_eqType := Eval hnf in EqType ebinop ebinop_eqMixin.

  (****** Statements ******)
  Inductive ruw : Set :=
  | old | new | undefined.

  Lemma ruw_eq_dec : forall {x y : ruw}, {x = y} + {x <> y}.
  Proof.  decide equality.  Qed.
  Definition ruw_eqn (x y : ruw) : bool :=
  match x, y with
  | old, old | new, new | undefined, undefined => true
  | _, _ => false
  end.
  Lemma ruw_eqP : Equality.axiom ruw_eqn.
  Proof.
  unfold Equality.axiom, ruw_eqn.
  destruct x, y ; simpl ;
        try (by apply ReflectF ; discriminate) ;
        by apply ReflectT ; reflexivity.
  Qed.
  Canonical ruw_eqMixin := EqMixin ruw_eqP.
  Canonical ruw_eqType := Eval hnf in EqType ruw ruw_eqMixin.

End LoFirrtl.