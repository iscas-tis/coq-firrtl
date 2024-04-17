From Coq Require Import FunInd FMaps FMapAVL OrderedType ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat ssrint eqtype seq.
From simplssrlib Require Import Types SsrOrder FSets FMaps Tactics Var Store.
From firrtl Require Import Env Firrtl.


Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.




(****** Aggregate type ******)

Section Ftype.

(* Variable var : eqType. *)

Inductive fflip : Type := Flipped | Nflip.

(* equality of fflip is decidable *)
Lemma fflip_eq_dec (x y : fflip) : {x = y} + {x <> y}.
Proof. decide equality. Qed.
Definition fflip_eqn (x y : fflip) : bool :=
  match x, y with
  | Flipped, Flipped => true
  | Nflip, Nflip => true
  | _, _ => false
  end.
Lemma fflip_eqP : Equality.axiom fflip_eqn.
Proof.
rewrite /Equality.axiom /fflip_eqn.
destruct x, y ; try (apply ReflectT ; reflexivity) ;
apply ReflectF ; discriminate.
Qed.
Definition fflip_eqMixin := EqMixin fflip_eqP.
Canonical fflip_eqType := Eval hnf in EqType fflip fflip_eqMixin.

Notation "x =? y" := (fflip_eqn x y).

Inductive ftype : Type :=
| Gtyp : fgtyp -> ftype
| Atyp : ftype -> nat -> ftype
| Btyp : ffield -> ftype

with ffield : Type :=
| Fnil : ffield
| Fflips : var -> fflip -> ftype -> ffield -> ffield
.

(* is passive type *)
Fixpoint is_passive (t : ftype) : bool :=
  match t with
  | Gtyp t => true
  | Atyp t _ => is_passive t
  | Btyp fs => is_passive_fields fs
  end
with is_passive_fields (fs : ffield) : bool :=
       match fs with
       | Fnil => true
       | Fflips _ Nflip t fs => is_passive t && (is_passive_fields fs)
       | Fflips _ Flipped t fs => false
       end.

(* Equality of types *)

Lemma ftype_eq_dec (x y : ftype) : {x = y} + {x <> y}
with ffield_eq_dec (fx fy : ffield) : {fx = fy} + {fx <> fy}.
Proof.
* decide equality. apply fgtyp_eq_dec. apply Nat.eq_dec.
* decide equality.
  decide equality. apply N.eq_dec.
Qed.

Fixpoint ftype_eqn (x y : ftype) : bool :=
  match x, y with
  | Gtyp tx, Gtyp ty => fgtyp_eqn tx ty
  | Atyp tx nx, Atyp ty ny => ftype_eqn tx ty && (nx == ny)
  | Btyp fx, Btyp fy => ffield_eqn fx fy
  | _, _ => false
  end
with ffield_eqn (f1 f2 : ffield) : bool :=
       match  f1, f2 with
       | Fnil, Fnil => true
       | Fflips v1 Nflip t1 fs1, Fflips v2 Nflip t2 fs2
         => (v1 == v2) && ftype_eqn t1 t2 && ffield_eqn fs1 fs2
       | Fflips v1 Flipped t1 fs1, Fflips v2 Flipped t2 fs2
         => (v1 == v2) && ftype_eqn t1 t2 && ffield_eqn fs1 fs2
       | _, _ => false
       end.

Notation "x =? y" := (ftype_eqn x y).

Lemma ftype_eqn_refl (x : ftype) : x =? x
with ffield_eqn_refl (fx : ffield) : ffield_eqn fx fx.
Proof.
* clear ftype_eqn_refl.
  induction x ; simpl ; try done.
  + apply fgtyp_eqn_refl.
  + rewrite IHx andTb eq_refl //.
* clear ffield_eqn_refl.
  induction fx ; simpl ; try done.
  destruct f.
  + 1,2: rewrite IHfx andbT (ftype_eqn_refl f0) andbT eq_refl //.
Qed.

Lemma ftype_eqn_eq (x y : ftype) : x =? y <-> x = y
with ffield_eqn_eq (fx fy : ffield) : ffield_eqn fx fy <-> fx = fy.
Proof.
* clear ftype_eqn_eq.
  split ; last by (intro ; rewrite H ; apply ftype_eqn_refl).
  revert x y ; induction x, y ; simpl ; try done.
  + generalize (fgtyp_eq_dec f f0) ; intro.
    destruct H ; first by (rewrite e ; intro ; reflexivity).
    intro ; apply fgtyp_eqn_eq in H ; contradiction.
  + intro ; move /andP : H => [H /eqP H0].
    apply IHx in H.
    rewrite H H0 ; by reflexivity.
  + intro ; apply ffield_eqn_eq in H.
    rewrite H ; by reflexivity.
* clear ffield_eqn_eq.
  split ; last by (intro ; rewrite H ; apply ffield_eqn_refl).
  revert fx fy ; induction fx, fy ; simpl ; try done.
  + destruct f ; done.
  + destruct f, f1 ; try done.
    1,2: destruct (v == v0) eqn: Hv ; last by rewrite andFb ; done.
    1,2: move /eqP : Hv => Hv ; rewrite andTb Hv.
    1,2: destruct (f0 =? f2) eqn: Hf ; last by rewrite andFb ; done.
    1,2: apply ftype_eqn_eq in Hf ; rewrite andTb Hf.
    1,2: intro ; apply IHfx in H.
    1,2: rewrite H //.
Qed.

Lemma ftype_eqn_sym (x y : ftype) : x =? y -> y =? x
with ffield_eqn_sym (fx fy : ffield) : ffield_eqn fx fy -> ffield_eqn fy fx.
Proof.
* clear ftype_eqn_sym.
  revert x y ; induction x, y ; simpl ; try done.
  + apply fgtyp_eqn_sym.
  + intro ; move /andP : H => [H H0].
    apply IHx in H ; rewrite eq_sym in H0.
    rewrite H andTb H0 //.
  + apply ffield_eqn_sym.
* clear ffield_eqn_sym.
  revert fx fy ; induction fx, fy ; simpl ; try done.
  + destruct f ; done.
  + destruct f, f1 ; try done.
    1,2: intro ; move /andP : H => [/andP [H H0] H1].
    1,2: rewrite eq_sym in H ; apply ftype_eqn_sym in H0 ; apply IHfx in H1.
    1,2: rewrite H andTb H0 andTb H1 //.
Qed.

Lemma ftype_eqn_trans (x y z : ftype) : x =? y -> y =? z -> x =? z.
Proof.
intros.
apply ftype_eqn_eq in H.
rewrite -H // in H0.
Qed.

Lemma ffield_eqn_trans (fx fy fz : ffield) : ffield_eqn fx fy -> ffield_eqn fy fz -> ffield_eqn fx fz.
Proof.
intros.
apply ffield_eqn_eq in H.
rewrite -H // in H0.
Qed.

Instance ftype_eqn_Reflexive : Reflexive (@ftype_eqn) := @ftype_eqn_refl.
Instance ftype_eqn_Symmetric : Symmetric (@ftype_eqn) := @ftype_eqn_sym.
Instance ftype_eqn_Transitive : Transitive (@ftype_eqn) := @ftype_eqn_trans.
Instance ftype_eqn_Equivalence : Equivalence (@ftype_eqn) :=
  { Equivalence_Reflexive := ftype_eqn_Reflexive;
    Equivalence_Symmetric := ftype_eqn_Symmetric;
    Equivalence_Transitive := ftype_eqn_Transitive }.
Instance ffield_eqn_Reflexive : Reflexive (@ffield_eqn) := @ffield_eqn_refl.
Instance ffield_eqn_Symmetric : Symmetric (@ffield_eqn) := @ffield_eqn_sym.
Instance ffield_eqn_Transitive : Transitive (@ffield_eqn) := @ffield_eqn_trans.
Instance ffield_eqn_Equivalence : Equivalence (@ffield_eqn) :=
  { Equivalence_Reflexive := ffield_eqn_Reflexive;
    Equivalence_Symmetric := ffield_eqn_Symmetric;
    Equivalence_Transitive := ffield_eqn_Transitive }.

Lemma ftype_eqP : forall (x y : ftype), reflect (x = y) (x =? y).
Proof.
intros.
generalize (ftype_eq_dec x y) ; intro.
destruct H.
* assert (x =? y) by (apply ftype_eqn_eq, e).
  rewrite H ; apply ReflectT, e.
* assert (~ (x =? y)) by (contradict n ; apply ftype_eqn_eq, n).
  move /negP : H => H ; apply negbTE in H.
  rewrite H ; apply ReflectF, n.
Qed.

Lemma ffield_eqP : forall (fx fy : ffield), reflect (fx = fy) (ffield_eqn fx fy).
Proof.
intros.
generalize (ffield_eq_dec fx fy) ; intro.
destruct H.
* assert (ffield_eqn fx fy) by (apply ffield_eqn_eq, e).
  rewrite H ; apply ReflectT, e.
* assert (~ ffield_eqn fx fy) by (contradict n ; apply ffield_eqn_eq, n).
  move /negP : H => H ; apply negbTE in H.
  rewrite H ; apply ReflectF, n.
Qed.

Definition ftype_eqMixin := EqMixin ftype_eqP.
Definition ffield_eqMixin := EqMixin ffield_eqP.
Canonical ftype_eqType := Eval hnf in EqType ftype ftype_eqMixin.
Canonical ffield_eqType := Eval hnf in EqType ffield ffield_eqMixin.


Fixpoint ftype_not_implicit_width (ft : ftype) : Prop :=
   match ft with
   | Gtyp (Fsint_implicit _) | Gtyp (Fuint_implicit _) => False
   | Gtyp _ => True
   | Atyp ft' _ => ftype_not_implicit_width ft'
   | Btyp fs => ffield_not_implicit_width fs
   end
with ffield_not_implicit_width (fs : ffield) : Prop :=
   match fs with
   | Fnil => True
   | Fflips _ _ ft fs' => ftype_not_implicit_width ft /\ ffield_not_implicit_width fs'
   end.

Fixpoint ftype_not_implicit (ft : ftype) : bool :=
   match ft with
   | Gtyp (Fsint_implicit _) | Gtyp (Fuint_implicit _) => false
   | Gtyp _ => true
   | Atyp ft' _ => ftype_not_implicit ft'
   | Btyp fs => ffield_not_implicit fs
   end
with ffield_not_implicit (fs : ffield) : bool :=
   match fs with
   | Fnil => true
   | Fflips _ _ ft fs' => ftype_not_implicit ft && ffield_not_implicit fs'
   end.
   
Fixpoint ftype_init_implicit (ft : ftype) : bool :=
  match ft with
  | Gtyp (Fsint_implicit 0) | Gtyp (Fuint_implicit 0) => true
  | Gtyp _ => false
  | Atyp ft' _ => ftype_init_implicit ft'
  | Btyp fs => ffield_init_implicit fs
  end
with ffield_init_implicit (fs : ffield) : bool :=
  match fs with
  | Fnil => true
  | Fflips _ _ ft fs' => ftype_init_implicit ft && ffield_init_implicit fs'
  end.

Definition ftype_explicit : Type :=
   (* disallow implicit widths *)
   { ft : ftype | ftype_not_implicit_width ft }.

Definition ffield_explicit : Type :=
   { fs : ffield | ffield_not_implicit_width fs }.

Fixpoint make_ftype_explicit (ft : ftype) : ftype_explicit :=
   match ft with
   | Gtyp (Fsint_implicit w) => exist ftype_not_implicit_width (Gtyp (Fsint w)) I
   | Gtyp (Fuint_implicit w) => exist ftype_not_implicit_width (Gtyp (Fuint w)) I
   | Gtyp ft' => exist ftype_not_implicit_width (Gtyp ft') I
   | Atyp ft' n => match make_ftype_explicit ft' with
                   exist fte p => exist ftype_not_implicit_width (Atyp fte n) p
                   end
   | Btyp fs => match make_ffield_explicit fs with
                exist fse p => exist ftype_not_implicit_width (Btyp fse) p
                end
   end
with make_ffield_explicit (fs: ffield) : ffield_explicit :=
   match fs with
   | Fnil => exist ffield_not_implicit_width Fnil I
   | Fflips v ff ft fs' => match make_ftype_explicit ft, make_ffield_explicit fs' with
                           exist fte pt, exist fse ps => exist ffield_not_implicit_width (Fflips v ff fte fse) (conj pt ps)
                           end
   end.

(* Definition explicit_to_ftype (fte : ftype_explicit) : ftype := proj1_sig fte. *)

Definition ftype_explicit_eqn (x y : ftype_explicit) : bool :=
proj1_sig x == proj1_sig y.
Definition ffield_explicit_eqn (x y : ffield_explicit) : bool :=
proj1_sig x == proj1_sig y.

Lemma ftype_explicit_proof_uniqueness (x : ftype) : forall (px1 px2 : ftype_not_implicit_width x), px1 = px2
with ffield_explicit_proof_uniqueness (f : ffield) : forall (pf1 pf2 : ffield_not_implicit_width f), pf1 = pf2.
Proof.
* clear ftype_explicit_proof_uniqueness.
  induction x ; simpl.
  + destruct f ; simpl ; try by (destruct px1, px2 ; reflexivity).
  + apply IHx.
  + apply ffield_explicit_proof_uniqueness.
* clear ffield_explicit_proof_uniqueness.
  induction f ; simpl.
  + destruct pf1, pf2 ; reflexivity.
  + destruct pf1, pf2.
    rewrite (ftype_explicit_proof_uniqueness f0 f2 f4)
            (IHf f3 f5) //.
Qed.

Lemma ftype_explicit_eqP : Equality.axiom ftype_explicit_eqn.
Proof.
rewrite /Equality.axiom /ftype_explicit_eqn.
intros.
destruct (eqVneq (proj1_sig x) (proj1_sig y)).
* apply ReflectT.
  destruct x, y.
  simpl proj1_sig in e.
  subst x0.
  rewrite (ftype_explicit_proof_uniqueness f0 f).
  reflexivity.
* apply ReflectF.
  destruct x, y.
  move /eqP : i => i.
  injection ; exact i.
Qed.

Lemma ffield_explicit_eqP : Equality.axiom ffield_explicit_eqn.
Proof.
rewrite /Equality.axiom /ffield_explicit_eqn.
intros.
destruct (eqVneq (proj1_sig x) (proj1_sig y)).
* apply ReflectT.
  destruct x, y.
  simpl proj1_sig in e.
  subst x0.
  rewrite (ffield_explicit_proof_uniqueness f0 f).
  reflexivity.
* apply ReflectF.
  destruct x, y.
  move /eqP : i => i.
  injection ; exact i.
Qed.

(* Equality of ftype_explicit is decidable *)
Lemma ftype_explicit_eq_dec : forall {x y : ftype_explicit}, {x = y} + {x <> y}.
Proof.
intros.
destruct x, y.
generalize (ftype_eq_dec x x0) ; intro.
destruct H.
* subst x0.
  left ; rewrite (ftype_explicit_proof_uniqueness f0 f) //.
* right ; injection ; done.
Qed.

Lemma ffield_explicit_eq_dec : forall {x y : ffield_explicit}, {x = y} + {x <> y}.
Proof.
intros.
destruct x, y.
generalize (ffield_eq_dec x x0) ; intro.
destruct H.
* subst x0.
  left ; rewrite (ffield_explicit_proof_uniqueness f0 f) //.
* right ; injection ; done.
Qed.

Canonical ftype_explicit_eqMixin := EqMixin ftype_explicit_eqP.
Canonical ftype_explicit_eqType := Eval hnf in EqType ftype_explicit ftype_explicit_eqMixin.
Canonical ffield_explicit_eqMixin := EqMixin ffield_explicit_eqP.
Canonical ffield_explicit_eqType := Eval hnf in EqType ffield_explicit ffield_explicit_eqMixin.

End Ftype.

Inductive fcomponent : Set :=
| In_port
| Instanceof
| Memory
| Node
| Out_port
| Register
| Wire
| Fmodule
.


(** eq dec *)
Lemma component_eq_dec : forall {x y : fcomponent}, {x = y} + {x <> y}.
Proof. decide equality. Qed.
Definition component_eqn (x y : fcomponent) : bool :=
match x, y with In_port, In_port | Instanceof, Instanceof | Memory, Memory | Node, Node
| Out_port, Out_port | Register, Register | Wire, Wire | Fmodule, Fmodule => true
| _, _ => false end.
Lemma component_eqP : Equality.axiom component_eqn.
Proof. unfold Equality.axiom, component_eqn. intros.
destruct x, y ; try (apply ReflectF ; discriminate).
all : (apply ReflectT ; reflexivity).
Qed.
Canonical component_eqMixin := EqMixin component_eqP.
Canonical component_eqType := Eval hnf in EqType fcomponent component_eqMixin.

