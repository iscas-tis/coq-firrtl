(*From Coq Require Import ZArith Arith RelationClasses OrderedType FMaps FSets FunInd FMapAVL.*)

From Coq Require Import FunInd FMaps FMapAVL OrderedType.
From mathcomp Require Import ssreflect ssrbool ssrnat ssrint eqtype seq.
From simplssrlib Require Import Types SsrOrder FSets FMaps Tactics Var Store.
From nbits Require Import NBits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


Delimit Scope firrtl with firrtl.

Section RawFirrtl.
  (****** Types Environment ******)

  (****** Ground Types ******)

  From Coq Require Import ZArith.

  Inductive fgtyp : Set :=
    Fuint : nat -> fgtyp
  | Fsint : nat -> fgtyp
  | Fclock.
  (* | Fanalog : nat -> fgtyp *) (* TBD, HiFirrtl *)
  (* | Fvector : fgtyp -> nat -> fgtyp *) (* TBD, HiFirrtl *)

  (* Size of types *)

  Definition sizeof_fgtyp (t : fgtyp) : nat :=
    match t with
    | Fuint w => w
    | Fsint w => w
    (* | Fanalog w => w *)
    | Fclock => 1
    end.

  Definition ftcast (bs : bits) (fty : fgtyp) (tty : fgtyp) : bits :=
    match fty with
    | Fuint w => ucastB bs (sizeof_fgtyp tty)
    | Fsint w => scastB bs (sizeof_fgtyp tty)
    | Fclock => ucastB bs 1
    end.
  
  (* Equality of types *)

  Lemma fgtyp_eq_dec (x y : fgtyp) : {x = y} + {x <> y}.
  Proof.
    destruct x; destruct y; try (intros; right; move=> []; discriminate).
    - intros; case: (Nat.eq_dec n n0) => H.
      + left; rewrite H; reflexivity.
      + right; move=> []; auto.
    - intros; case: (Nat.eq_dec n n0) => H.
      + left; rewrite H; reflexivity.
      + right; move=> []; auto.
    (* - intros; case: (Nat.eq_dec n n0) => H. *)
    (*   + left; rewrite H; reflexivity. *)
    (*   + right; move=> []; auto. *)
    - left; done.
  Qed.

  Definition fgtyp_eqn (x y : fgtyp) : bool :=
    match x, y with
    | Fuint wx, Fuint wy => wx == wy
    | Fsint wx, Fsint wy => wx == wy
    (* | Fanalog wx, Fanalog wy => wx == wy *)
    | Fclock, Fclock => true
    | _, _ => false
    end.

  Notation "x =? y" := (fgtyp_eqn x y).

  Lemma fgtyp_eqn_refl (x : fgtyp) : x =? x.
  Proof.
    destruct x; try (exact: eqxx).
    - done.
  Qed.

  Lemma fgtyp_eqn_eq (x y : fgtyp) : x =? y <-> x = y.
  Proof.
    split; first (destruct x; destruct y; move=> /= H);
      try (discriminate|| rewrite (eqP H); reflexivity).
    - done.
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

  Instance fgtyp_eqn_Reflexive : Reflexive (@fgtyp_eqn) := @fgtyp_eqn_refl.
  Instance fgtyp_eqn_Symmetric : Symmetric (@fgtyp_eqn) := @fgtyp_eqn_sym.
  Instance fgtyp_eqn_Transitive : Transitive (@fgtyp_eqn) := @fgtyp_eqn_trans.
  Instance fgtyp_eqn_Equivalence : Equivalence (@fgtyp_eqn) :=
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


  (*Delimit Scope fgtyp_scope with fgtyp.*)

  (* Integer, bitvector or ssrint, TBD *)

  (* Fix-point, TBD *)

  (* Analog, TBD *)

  (* Vector, TBD *)


  (****** Syntax ******)

  (****** Expressions ******)

  Inductive ucast : Set :=
  | AsUInt | AsSInt (*| AsFixed*) | AsClock.

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
  (* | Uincp *)
  (* | Udecp *)
  (* | Usetp . *)

  Inductive bcmp : Set :=
  | Blt | Bleq | Bgt | Bgeq | Beq | Bneq.

  Inductive ebinop : Set :=
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

  (*From simplssrlib Require Import Var.*)
  Variable var : Type.

  (* mux, valid, sub-xxx, TBD *)
  Inductive fexpr : Type :=
  | Econst : bits -> fexpr
  | Eref : var -> fexpr
  | Edeclare : var -> fgtyp -> fexpr
  (* | Efield : fexpr -> fexpr -> fexpr *) (* HiFirrtl *)
  (* | Esubfield : var -> nat -> fexpr *) (* HiFirrtl *)
  | Ecast : ucast -> fexpr -> fexpr
  | Eprim_unop : eunop -> fexpr -> fexpr
  | Eprim_binop : ebinop -> fexpr -> fexpr -> fexpr
  | Emux : fexpr -> fexpr -> fexpr -> fexpr
  | Evalidif : fexpr -> fexpr -> fexpr
  .

  (****** Statements ******)
  Inductive ruw : Set :=
  | old | new | undefined.

  Record fmem : Type :=
    mk_fmem
      {
        mid : var;
        data_type : fexpr;
        depth : nat;
        reader : seq var;
        writer : seq var;                    
        read_latency : nat;
        write_latency : nat;
        read_write : ruw
      }.

  Inductive rst : Type :=
  | NRst : rst
  | Rst : fexpr -> fexpr -> rst.
  
  Record freg : Type :=
    mk_freg
      {
        rid : var;
        type : fgtyp;
        clock : fexpr;
        reset : rst
      }.

  Inductive fstmt : Type :=
  | Sskip
  | Swire : var -> fgtyp -> fstmt
  | Sreg : freg -> fstmt
  | Smem : fmem -> fstmt
  | Sinst : var -> var -> fstmt
  | Snode : var -> fexpr -> fstmt
  | Sfcnct : fexpr -> fexpr -> fstmt
  | Spcnct : fexpr -> fexpr -> fstmt
  | Sinvalid : var -> fstmt
  (* | Sattach : seq var -> fstmt *)
  | Swhen : fexpr -> fstmt -> fstmt -> fstmt
  | Sstop : fexpr -> fexpr -> nat -> fstmt
  (* | Sprintf (* TBD *) *)
  (* | Sassert (* TBD *) *)
  (* | Sassume (* TBD *) *)
  (* | Sdefname : var -> fstmt *) (* TBD *)
  (* | Sparam : var -> fexpr -> fstmt *) (* TBD *)
  .

  Inductive fport : Type :=
  | Finput : var -> fgtyp -> fport
  | Foutput : var -> fgtyp -> fport
  .

  (* TBD *)
  Inductive fmodule : Type :=
  | FInmod : var -> seq fport -> seq fstmt -> fmodule
  | FExmod : var -> seq fport -> seq fstmt -> fmodule
  .

  Definition fcircuit := var -> seq fmodule.

End RawFirrtl.


(* A typing environment is a map from a variable to its type *)

Module Type TypEnv <: SsrFMap.

  Include SsrFMap.

  Definition env : Type := t fgtyp.

  (* The default type of a variable not in the typing environment *)
  Parameter deftyp : fgtyp.

  (* Find the type of a variable in a typing environment.
     If a variable is not in the typing environment, return the default type. *)
  Parameter vtyp : SE.t -> env -> fgtyp.

  (* Return the size of a variable in a typing environment.
     If a variable is not in the typing environment, return the size of the
     default type. *)
  Parameter vsize : SE.t -> env -> nat.

  Axiom find_some_vtyp :
    forall {x : SE.t} {ty : fgtyp} {e : env}, find x e = Some ty -> vtyp x e = ty.
  Axiom find_none_vtyp :
    forall {x : SE.t} {e : env}, find x e = None -> vtyp x e = deftyp.
  Axiom vtyp_find :
    forall {x : SE.t} {ty : fgtyp} {e : env},
      (vtyp x e == ty) = (find x e == Some ty) || ((find x e == None) && (ty == deftyp)).
  Axiom vtyp_add_eq :
    forall {x y : SE.t} {ty : fgtyp} {e : env}, x == y -> vtyp x (add y ty e) = ty.
  Axiom vtyp_add_neq :
    forall {x y : SE.t} {ty : fgtyp} {e : env},
      x != y -> vtyp x (add y ty e) = vtyp x e.
  Axiom vsize_add_eq :
    forall {x y : SE.t} {ty : fgtyp} {e : env},
      x == y -> vsize x (add y ty e) = sizeof_fgtyp ty.
  Axiom vsize_add_neq :
    forall {x y : SE.t} {ty : fgtyp} {e : env},
      x != y -> vsize x (add y ty e) = vsize x e.
  Axiom not_mem_vtyp :
    forall {v : SE.t} {e : env}, ~~ mem v e -> vtyp v e = deftyp.
  Axiom vtyp_vsize :
    forall {x : SE.t} {e : env} {ty : fgtyp},
      vtyp x e = ty -> vsize x e = sizeof_fgtyp ty.

End TypEnv.

Module MakeTypEnv (V : SsrOrder) (VM : SsrFMap with Module SE := V) <:
  TypEnv with Module SE := V.

  Include VM.
  Module Lemmas := FMapLemmas VM.

  Definition env : Type := t fgtyp.

  (* The default type of a variable not in the typing environment *)
  Definition deftyp : fgtyp := Fuint 0.

  (* Find the type of a variable in a typing environment.
     If a variable is not in the typing environment, return the default type. *)
  Definition vtyp (v : V.t) (e : env) : fgtyp :=
    match VM.find v e with
    | None => deftyp
    | Some ty => ty
    end.

  (* Return the size of a variable in a typing environment.
     If a variable is not in the typing environment, return the size of the
     default type. *)
  Definition vsize (v : V.t) (e : env) : nat := sizeof_fgtyp (vtyp v e).

  Lemma find_some_vtyp {x ty e} : find x e = Some ty -> vtyp x e = ty.
  Proof. move=> H. rewrite /vtyp H. reflexivity. Qed.

  Lemma find_none_vtyp {x e} : find x e = None -> vtyp x e = deftyp.
  Proof. move=> H. rewrite /vtyp H. reflexivity. Qed.

  Lemma vtyp_find {x ty e} :
    (vtyp x e == ty) = (find x e == Some ty) || ((find x e == None) && (ty == deftyp)).
  Proof.
    dcase (find x e); case.
    - move=> a Hfind. rewrite (find_some_vtyp Hfind) /= orbF. case Heq: (a == ty).
      + by rewrite (eqP Heq) eqxx.
      + symmetry. apply/eqP => H. case: H => H. rewrite H eqxx in Heq. discriminate.
    - move=> Hnone. rewrite (find_none_vtyp Hnone) eqxx /=. rewrite eq_sym.
      reflexivity.
  Qed.

  Lemma vtyp_add_eq {x y ty e} : x == y -> vtyp x (add y ty e) = ty.
  Proof. rewrite /vtyp /add => H. by rewrite (Lemmas.find_add_eq H). Qed.

  Lemma vtyp_add_neq {x y ty e} : x != y -> vtyp x (add y ty e) = vtyp x e.
  Proof.
    move/negP=> Hxy. rewrite /vtyp /add. by rewrite (Lemmas.find_add_neq Hxy).
  Qed.

  Lemma vsize_add_eq {x y ty e} : x == y -> vsize x (add y ty e) = sizeof_fgtyp ty.
  Proof. rewrite /vsize=> H. by rewrite (vtyp_add_eq H). Qed.

  Lemma vsize_add_neq {x y ty e} : x != y -> vsize x (add y ty e) = vsize x e.
  Proof. rewrite /vsize => H. by rewrite (vtyp_add_neq H). Qed.

  Lemma not_mem_vtyp v e : ~~ mem v e -> vtyp v e = deftyp.
  Proof. rewrite /vtyp => H. by rewrite Lemmas.not_mem_find_none. Qed.

  Lemma vtyp_vsize x e ty : vtyp x e = ty -> vsize x e = sizeof_fgtyp ty.
  Proof. rewrite /vsize /vtyp. move=> ->. reflexivity. Qed.

End MakeTypEnv.

Module TE <: TypEnv := MakeTypEnv VarOrder VM.

(* TBD *)
Variable structure : Type.

Module Type StrStore (V : SsrOrder) (TE : TypEnv with Module SE := V).
  Module Lemmas := FMapLemmas TE.

  Local Notation var := V.t.
  Local Notation value := structure.

  Parameter t : Type.
  Parameter acc : var -> t -> value.
  Parameter upd : var -> value -> t -> t.
  Parameter upd2 : var -> value -> var -> value -> t -> t.
  
End StrStore.

(* Module MakeStrStore (V : SsrOrder) (TE : TypEnv with Module SE := V) <: *)
(*   StrStore V TE. *)
(*   Module Lemmas := FMapLemmas TE. *)

(* End MakeStrStore. *)

(* Module StrStore := MakeStrStore VarOrder TE. *)

Module Type ValStore (V : SsrOrder) (TE : TypEnv with Module SE := V).
  Module Lemmas := FMapLemmas TE.

  Local Notation var := V.t.
  Local Notation value := bits.

  Parameter t : Type.
  Parameter acc : var -> t -> value.
  Parameter upd : var -> value -> t -> t.
  Parameter upd2 : var -> value -> var -> value -> t -> t.
    Parameter acc_upd_eq : forall {x y v s}, x == y -> acc x (upd y v s) = v.
  Parameter acc_upd_neq : forall {x y v s}, x != y -> acc x (upd y v s) = acc x s.
  Parameter acc_upd2_eq1 :
    forall {x y1 v1 y2 v2 s},
      x == y1 -> x != y2 -> acc x (upd2 y1 v1 y2 v2 s) = v1.
  Parameter acc_upd2_eq2 :
    forall {x y1 v1 y2 v2 s},
      x == y2 -> acc x (upd2 y1 v1 y2 v2 s) = v2.
  Parameter acc_upd2_neq :
    forall {x y1 v1 y2 v2 s},
      x != y1 -> x != y2 -> acc x (upd2 y1 v1 y2 v2 s) = acc x s.
  Parameter Upd : var -> value -> t -> t -> Prop.
  Definition Upd2 x1 v1 x2 v2 (s1 s2 : t) : Prop :=
    forall y, acc y s2 = acc y (upd x2 v2 (upd x1 v1 s1)).
  Parameter Equal : t -> t -> Prop.
  Parameter Upd_upd : forall x v s, Upd x v s (upd x v s).
  Parameter Upd2_upd :
    forall x1 v1 x2 v2 s, Upd2 x1 v1 x2 v2 s (upd x2 v2 (upd x1 v1 s)).
  Parameter Upd2_upd2 : forall x1 v1 x2 v2 s, Upd2 x1 v1 x2 v2 s (upd2 x1 v1 x2 v2 s).
  Parameter acc_Upd_eq : forall x y v s1 s2, x == y -> Upd y v s1 s2 -> acc x s2 = v.
  Parameter acc_Upd_neq :
    forall x y v s1 s2, x != y -> Upd y v s1 s2 -> acc x s2 = acc x s1.
  Parameter acc_Upd2_eq1 :
    forall x y1 v1 y2 v2 s1 s2,
      x == y1 -> x != y2 -> Upd2 y1 v1 y2 v2 s1 s2 -> acc x s2 = v1.
  Parameter acc_Upd2_eq2 :
    forall x y1 v1 y2 v2 s1 s2, x == y2 -> Upd2 y1 v1 y2 v2 s1 s2 -> acc x s2 = v2.
  Parameter acc_Upd2_neq :
    forall x y1 v1 y2 v2 s1 s2,
      x != y1 -> x != y2 -> Upd2 y1 v1 y2 v2 s1 s2 -> acc x s2 = acc x s1.
  Parameter Equal_def :
    forall s1 s2,
      Equal s1 s2 <-> (forall v, acc v s1 = acc v s2).
  Parameter Equal_refl : forall s, Equal s s.
  Parameter Equal_sym : forall s1 s2, Equal s1 s2 -> Equal s2 s1.
  Parameter Equal_trans : forall s1 s2 s3, Equal s1 s2 -> Equal s2 s3 -> Equal s1 s3.
  Parameter Equal_ST : RelationClasses.Equivalence Equal.
  Parameter Equal_upd_Equal :
    forall v e s1 s2, Equal s1 s2 -> Equal (upd v e s1) (upd v e s2).
  Parameter Equal_Upd_Equal :
    forall v e s1 s2 s3 s4,
      Upd v e s1 s2 -> Upd v e s3 s4 -> Equal s1 s3 -> Equal s2 s4.
  Parameter Upd_pred_Equal :
    forall v e s1 s2 s, Upd v e s1 s2 -> Equal s1 s -> Upd v e s s2.
  Parameter Upd_succ_Equal :
    forall v e s1 s2 s, Upd v e s1 s2 -> Equal s2 s -> Upd v e s1 s.

  Parameter conform : t -> TE.env -> Prop.
  Parameter conform_def :
    forall (s : t) (E : TE.env),
      (forall (v : V.t), TE.mem v E -> TE.vsize v E = size (acc v s)) ->
      conform s E.
  Parameter conform_mem :
    forall v s te, conform s te -> TE.mem v te -> TE.vsize v te = size (acc v s).
  Parameter conform_Upd :
    forall x ty v s1 s2 te,
      sizeof_fgtyp ty = size v -> Upd x v s1 s2 -> conform s1 te ->
      conform s2 (TE.add x ty te).
  Parameter conform_Upd2 :
    forall te s1 s2 ty1 ty2 x1 x2 v1 v2,
      x1 != x2 -> sizeof_fgtyp ty1 = size v1 -> sizeof_fgtyp ty2 = size v2 ->
      Upd2 x2 v2 x1 v1 s1 s2 -> conform s1 te ->
      conform s2 (TE.add x1 ty1 (TE.add x2 ty2 te)).
  Parameter conform_upd :
    forall x ty v s te,
      sizeof_fgtyp ty = size v -> conform s te -> conform (upd x v s) (TE.add x ty te).
  Parameter conform_upd2 :
    forall te s ty1 ty2 x1 x2 v1 v2,
      x1 != x2 -> sizeof_fgtyp ty1 = size v1 -> sizeof_fgtyp ty2 = size v2 ->
      conform s te ->
      conform (upd2 x2 v2 x1 v1 s) (TE.add x1 ty1 (TE.add x2 ty2 te)).
  Parameter conform_add_not_mem :
    forall E s x ty,
      conform s (TE.add x ty E) -> ~~ TE.mem x E -> conform s E.
  Parameter conform_submap :
    forall E1 E2 s,
      Lemmas.submap E1 E2 -> conform s E2 -> conform s E1.
  Parameter conform_equal :
    forall E1 E2 s,
      TE.Equal E1 E2 -> conform s E1 <-> conform s E2.
  Parameter equal_conform :
    forall E s1 s2,
      Equal s1 s2 -> conform s1 E <-> conform s2 E.
End ValStore.

Module BValueType <: HasDefaultTyp.
  Definition t : Type := bits.
  Definition default : t := [::].
End BValueType.

Module MakeValStore (V : SsrOrder) (TE : TypEnv with Module SE := V) <:
  ValStore V TE.

  Include MakeTStoreMap V BValueType.
  Module Lemmas := FMapLemmas TE.

  (* A store conforms to a typing environment if for every variable in the typing
     environment, the size of its type in the typing environment is the same as
     the size of its value in the store *)
  Definition conform (s : t) (te : TE.env) : Prop :=
    forall (v : V.t),
      TE.mem v te -> TE.vsize v te = size (acc v s).

  Lemma conform_def :
    forall (s : t) (E : TE.env),
      (forall (v : V.t), TE.mem v E -> TE.vsize v E = size (acc v s)) ->
      conform s E.
  Proof. move=> s E H. assumption. Qed.

  Lemma conform_mem v s te :
    conform s te -> TE.mem v te -> TE.vsize v te = size (acc v s).
  Proof. move=> H1 H2; exact: (H1 _ H2). Qed.

  Lemma conform_Upd x ty v s1 s2 te :
    sizeof_fgtyp ty = size v -> Upd x v s1 s2 -> conform s1 te ->
    conform s2 (TE.add x ty te).
  Proof.
    move=> Hs Hupd Hcon y. case Hyx: (y == x).
    - by rewrite (TE.vsize_add_eq Hyx) (acc_Upd_eq Hyx Hupd).
    - move/negP: Hyx => Hyx. rewrite (Lemmas.mem_add_neq Hyx) => Hmem.
      move/negP: Hyx => Hyx. rewrite (acc_Upd_neq Hyx Hupd) (TE.vsize_add_neq Hyx).
      exact: (Hcon _ Hmem).
  Qed.

  Lemma conform_Upd2 te s1 s2 ty1 ty2 x1 x2 v1 v2 :
    x1 != x2 -> sizeof_fgtyp ty1 = size v1 -> sizeof_fgtyp ty2 = size v2 ->
    Upd2 x2 v2 x1 v1 s1 s2 -> conform s1 te ->
    conform s2 (TE.add x1 ty1 (TE.add x2 ty2 te)).
  Proof.
    move => Hneq Hty1 Hty2 HUpd2 Hcon y Hmem .
    case Heq1 : (y == x1); case Heq2 : (y == x2) .
    - rewrite -(eqP Heq1) -(eqP Heq2) in Hneq . move : Hneq => /eqP // .
    - rewrite (acc_Upd2_eq2 Heq1 HUpd2) (TE.vsize_add_eq Heq1) // .
    - move/idP/negP: Heq1 => Hneq1.
      rewrite (acc_Upd2_eq1 Heq2 Hneq1 HUpd2)
              (TE.vsize_add_neq Hneq1) (TE.vsize_add_eq Heq2) // .
    - move/idP/negP: Heq1 => Hneq1.
      move/idP/negP: Heq2 => Hneq2.
      rewrite (acc_Upd2_neq Hneq2 Hneq1 HUpd2)
              (TE.vsize_add_neq Hneq1) (TE.vsize_add_neq Hneq2) Hcon // .
      move/negP: Hneq1 => Hneq1. move/negP: Hneq2 => Hneq2.
      rewrite (Lemmas.mem_add_neq Hneq1) (Lemmas.mem_add_neq Hneq2) in Hmem.
      assumption.
  Qed.

  Lemma conform_upd x ty v s te :
    sizeof_fgtyp ty = size v ->
    conform s te -> conform (upd x v s) (TE.add x ty te).
  Proof. move=> Hs Hcon. exact: (conform_Upd Hs (Upd_upd x v s) Hcon). Qed.

  Lemma conform_upd2 te s ty1 ty2 x1 x2 v1 v2 :
    x1 != x2 -> sizeof_fgtyp ty1 = size v1 -> sizeof_fgtyp ty2 = size v2 ->
    conform s te ->
    conform (upd2 x2 v2 x1 v1 s) (TE.add x1 ty1 (TE.add x2 ty2 te)).
  Proof.
    move=> Hne Hs1 Hs2 Hcon.
    exact: (conform_Upd2 Hne Hs1 Hs2 (Upd2_upd2 x2 v2 x1 v1 s) Hcon).
  Qed.

  Lemma conform_add_not_mem E s x ty :
    conform s (TE.add x ty E) -> ~~ TE.mem x E -> conform s E.
  Proof.
    move=> Hco Hmem y Hmemy. move: (Hco y). rewrite Lemmas.OP.P.F.add_b Hmemy orbT.
    move=> <-; last by exact: is_true_true. case Hyx: (y == x).
    - rewrite (eqP Hyx) in Hmemy. rewrite Hmemy in Hmem. discriminate.
    - move/idP/negP: Hyx => Hyx. rewrite (TE.vsize_add_neq Hyx). reflexivity.
  Qed.

  Lemma conform_submap E1 E2 s :
    Lemmas.submap E1 E2 -> conform s E2 -> conform s E1.
  Proof.
    move=> Hsubm Hco x Hmem1. move: (Lemmas.submap_mem Hsubm Hmem1) => Hmem2.
    move: (Lemmas.mem_find_some Hmem1) => [ty Hfind1].
    move: (Hsubm x ty Hfind1) => Hfind2. move: (TE.find_some_vtyp Hfind1) => Hty1.
     move: (TE.find_some_vtyp Hfind2) => Hty2. rewrite -(Hco _ Hmem2).
    rewrite (TE.vtyp_vsize Hty1) (TE.vtyp_vsize Hty2). reflexivity.
  Qed.

  Lemma conform_equal E1 E2 s :
    TE.Equal E1 E2 -> conform s E1 <-> conform s E2.
  Proof.
    move=> Heq. move: (Lemmas.Equal_submap Heq) => H12.
    move: (Lemmas.Equal_sym Heq) => {Heq} Heq.
    move: (Lemmas.Equal_submap Heq) => H21. split.
    - exact: (conform_submap H21).
    - exact: (conform_submap H12).
  Qed.

  Lemma equal_conform E s1 s2 :
    Equal s1 s2 -> conform s1 E <-> conform s2 E.
  Proof.
    move=> Heq. split.
    - move=> H1. apply: conform_def. move=> v Hmem.
      rewrite (conform_mem H1 Hmem). rewrite (Heq v). reflexivity.
    - move=> H2. apply: conform_def. move=> v Hmem.
      rewrite (conform_mem H2 Hmem). rewrite (Heq v). reflexivity.
  Qed.

End MakeValStore.

Module Store := MakeValStore VarOrder TE.

Section State.
  Variable t : Type.
  Inductive state : Type :=
  | OK of t
  | ERR.
End State.

Module State.
  Definition t : Type := state Store.t.
End State.

Module MakeFirrtl
       (V : SsrOrder)
       (VS : SsrFSet with Module SE := V)
       (VM : SsrFMap with Module SE := V)
       (TE : TypEnv with Module SE := V)
       (SS : StrStore V TE)
       (SV : ValStore V TE).
  Local Open Scope firrtl.
  Module TELemmas := FMapLemmas TE.
  Module VSLemmas := SsrFSetLemmas VS.
  Local Notation var := V.t.
  
  Local Notation vstate := SV.t.
  
(****** Semantics ******)

  (* small-step *)
  Definition fexpr := fexpr V.t.

  Definition to_Clock bs := Z.b2z (lsb bs).
  
  Definition eunop_ucast (o : ucast) : bits -> Z :=
    match o with
    | AsUInt => to_Zpos
    | AsSInt => to_Z
    | AsClock => to_Clock
    end.

  Definition eunop_op (o : eunop ) : bits -> bits :=
    match o with
    | Upad n => fun b => if msb b then scastB b n else ucastB b n
    | Ushl n => shlB n
    | Ushr n => shrB n
    | Ucvt =>  fun b => if msb b then b else ucastB b (size b + 1)
    | Uneg => negB
    | Unot => invB
    | Uandr => fun b => [::foldr andb b1 b]
    | Uorr => fun b => [::foldr orb b0 b]
    | Uxorr => fun b => [::foldr xorb b0 b]
    | Uextr n1 n2 => extract n1 n2
    | Uhead n => high n
    | Utail n => low n
    end.

  Definition binop_bcmp (o : bcmp) : bits -> bits -> bits :=
    match o with
    | Blt => fun b1 b2 => [::ltB b1 b2]
    | Bleq => fun b1 b2 => [::leB b1 b2]
    | Bgt => fun b1 b2 => [::gtB b1 b2]
    | Bgeq => fun b1 b2 => [::geB b1 b2]
    | Beq => fun b1 b2 => [::b1 == b2]
    | Bneq => fun b1 b2 => [::(~~ (b1 == b2))]
    end.
  
  Definition ebinop_op (o : ebinop) : bits -> bits -> bits :=
    match o with
    | Badd => addB
    | Bsub => subB
    | Bdiv => udivB'
    | Brem => uremB
    | Bmul => mulB
    | Bcomp c => binop_bcmp c
    | Band => andB
    | Bor => orB
    | Bxor => xorB
    | Bcat => cat
    | Bdshl => fun a b => shlB (to_nat b) a
    | Bdshr => fun a b => shrB (to_nat b) a
    end.

  
  Fixpoint eval_fexpr (e : fexpr) (s : vstate): bits :=
    match e with
    | Econst c => c
    | Eref v => SV.acc v s
    (* | Efield *)
    (* | Esubfield  *)
    | Eprim_binop b e1 e2 => (ebinop_op b) (eval_fexpr e1 s) (eval_fexpr e2 s)
    | Eprim_unop u e => (eunop_op u) (eval_fexpr e s)
    | Emux c e1 e2 => if (Z.gtb 0 (to_Z (eval_fexpr c s))) then (eval_fexpr e1 s) else (eval_fexpr e2 s)
    | Evalidif c e => if (Z.gtb 0 (to_Z (eval_fexpr c s))) then (eval_fexpr e s) else [::]
    | Edeclare v t => [::]
    | Ecast _ _ => [::]
    end.

  Definition upd_typenv_fexpr (e : fexpr) (te : TE.env) : TE.env :=
    match e with
    | Edeclare v t => TE.add v t te
    | Ecast AsUInt (Eref v) => TE.add v (Fuint (sizeof_fgtyp (TE.vtyp v te))) te
    | Ecast AsSInt (Eref v) => TE.add v (Fsint (sizeof_fgtyp (TE.vtyp v te))) te
    | Ecast AsClock (Eref v) => TE.add v (Fuint 1) te
    | _ => te
    end.

  Fixpoint type_of_fexpr (e : fexpr) (te : TE.env) (s : vstate) : fgtyp :=
    match e with
    | Econst c => Fuint (size c)
    | Eref v => TE.vtyp v te
    | Edeclare v t => t
    | Ecast AsUInt e => Fuint (sizeof_fgtyp (type_of_fexpr e te s))
    | Ecast AsSInt e => Fsint (sizeof_fgtyp (type_of_fexpr e te s))
    | Ecast AsClock e => Fuint 1
    | Eprim_unop u e => match u with
                        | Upad n => match (type_of_fexpr e te s) with
                                    | Fuint _ => Fuint n
                                    | Fsint _ => Fsint n
                                    | Fclock => Fuint n
                                    end
                        | Uandr | Uorr | Uxorr => Fuint 1
                        | Uextr n1 n2 => Fuint (n2 - n1 + 1)
                        | Uhead n => Fuint n
                        | Utail n => Fuint n
                        | _ => type_of_fexpr e te s
                        end
    | Eprim_binop b e1 e2 => match b with
                             | Bdshl | Bdshr => match (type_of_fexpr e1 te s) with
                                                | Fuint n => Fuint (n + sizeof_fgtyp (type_of_fexpr e2 te s))
                                                | Fsint n => Fsint (n + sizeof_fgtyp (type_of_fexpr e2 te s))
                                                | Fclock => TE.deftyp
                                                end
                             | _ => type_of_fexpr e1 te s
                             end
    | Emux c e1 e2 => if (Z.gtb 0 (to_Z (eval_fexpr c s)))
                      then (type_of_fexpr e1 te s) else (type_of_fexpr e2 te s)
    | Evalidif c e => (* if (Z.gtb 0 (to_Z (eval_fexpr c s))) then *)
                      (type_of_fexpr e te s)
    end.
  
  Definition freg := freg V.t.
  Definition fmem := fmem V.t.
  Definition fstmt := fstmt V.t.
  Definition fport := fport V.t.
  Definition fmodule := fmodule V.t.

  Fixpoint eval_fstmt (st : fstmt) (s : vstate) : vstate :=
    match st with
    | Sskip => s
    | Swire v t => SV.upd v [::] s
    | Sreg r => match reset r with
                  | NRst => SV.upd (rid r) [::] s
                  | Rst e1 e2 => if (Z.gtb 0 (to_Z (eval_fexpr e1 s)))
                                 then SV.upd (rid r) (eval_fexpr e2 s) s
                                 else s
                end
    | Smem m => s (* TBD *)
    | Sinst v1 v2 => s (* TBD, HiFirrtl *)
    | Snode v e => SV.upd v (eval_fexpr e s) s (* must be initialized *)
    | Sfcnct e1 e2 => match e1 with
                      | Eref v => match (eval_fexpr e2 s) with
                                  | [::] => s
                                  | _ => SV.upd v (eval_fexpr e2 s) s
                                  end
                      | _ => s (* TBD *)
                      end
    | Spcnct _ _ => s (* TBD, HiFirrtl *)
    | Sinvalid _ => s (* TBD *)
    (* | Swhen e st1 st2 => if (Z.gtb 0 (to_Z (eval_fexpr e s))) then eval_fstmt st1 s *)
    (*                      else eval_fstmt st2 s *) (* TBD, HiFirrtl *)
    | _ => s
    end.

  Fixpoint eval_fstmts st s :=
    match st with
    | [::] => s
    | h :: tl => eval_fstmts tl (eval_fstmt h s)
    end.

  Definition upd_typenv_fstmt (s : fstmt) (te : TE.env) (st : vstate) : TE.env :=
    match s with
    | Swire v t  => TE.add v t te
    | Sreg r => TE.add (rid r) (type r) te
    | Snode v e => TE.add v (type_of_fexpr e te st) te
    | _ => te
    end.

  Fixpoint upd_typenv_fstmts (ss : seq fstmt) (te : TE.env) (s : vstate) : TE.env :=
    match ss with
    | [::] => te
    | h :: tl => upd_typenv_fstmts tl (upd_typenv_fstmt h te s) s
    end.

  Definition eval_fport (p : fport) (s : vstate) : vstate :=
    match p with
    | Finput v t => SV.upd v [::] s
    | Foutput v t => SV.upd v [::] s
    end.
  
  Fixpoint eval_fports (ps : seq fport) (s : vstate) : vstate :=
    match ps with
    | [::] => s
    | h :: tl => eval_fports tl (eval_fport h s)
    end.

  Definition upd_typenv_fport (p : fport) (te : TE.env) : TE.env :=
    match p with
    | Finput v t => TE.add v t te
    | Foutput v t => TE.add v t te
    end.

  Fixpoint upd_typenv_fports (ps : seq fport) (te : TE.env) : TE.env :=
    match ps with
    | [::] => te
    | h :: tl => upd_typenv_fports tl (upd_typenv_fport h te)
    end.
  
  Fixpoint eval_fmodule (m : fmodule) (s : vstate) : vstate :=
    match m with
    | FInmod v ps st => eval_fstmts st (eval_fports ps (SV.upd v [::] s))
    | _ => s
    end.

  Definition upd_typenv_fmodule (m : fmodule) (te : TE.env) (s : vstate) : TE.env :=
    match m with
    | FInmod v ps ss => upd_typenv_fstmts ss (upd_typenv_fports ps te) s
    | _ => te
    end.

  (* fexpr eqn , TBD *)


  (* Well-typed *)

  (* well typed expr *)
  
  Fixpoint well_typed_fexpr (e : fexpr) (te : TE.env) : bool :=
    match e with
    | Econst _ => true
    | Eref v => 0 < sizeof_fgtyp (TE.vtyp v te)
    | Edeclare v t => 0 < sizeof_fgtyp t
    | Ecast _ _ => true
    | Eprim_unop _ e1 => well_typed_fexpr e1 te
    | Eprim_binop _ e1 e2 => (well_typed_fexpr e1 te) && (well_typed_fexpr e2 te)
    | Emux c e1 e2 => (well_typed_fexpr c te) && (well_typed_fexpr e1 te) && (well_typed_fexpr e2 te)
    | Evalidif c e1 => (well_typed_fexpr c te) && (well_typed_fexpr e1 te)
    end.


  (* Well-formness, is defined && well-typed *)
  
  (* Use TE.mem v te to determine if v is defined *)
  Definition is_defined (v : var) (te : TE.env) : bool :=
    TE.mem v te.

  Fixpoint is_defined_fexpr (e : fexpr) (te : TE.env) : bool :=
    match e with
    | Econst _ => true
    | Eref v => is_defined v te
    | Edeclare v t => true
    | Ecast _ e1 => is_defined_fexpr e1 te
    | Eprim_unop _ e1 => is_defined_fexpr e1 te
    | Eprim_binop _ e1 e2 => (is_defined_fexpr e1 te) && (is_defined_fexpr e2 te)
    | Emux c e1 e2 => (is_defined_fexpr c te) && (is_defined_fexpr e1 te) && (is_defined_fexpr e2 te)
    | Evalidif c e1 => (is_defined_fexpr c te) && (is_defined_fexpr e1 te)
    end.
  
  (* well formed expr *)
  Definition well_formed_fexpr e te := well_typed_fexpr e te && is_defined_fexpr e te.

  


  
End MakeFirrtl.
  
  (* Record fmod_state : Type := *)
  (* mk_state *)
  (*   { *)
  (*     fregs : seq freg; *)
  (*     fmems : seq fmem *)
  (*   }. *)

(* TBD *)
  (*Parameter eval_fstmt : fstate -> fstmt -> fstate.*)
  (* Module FIRRTL := MakeFirrtl VarOrder VS VM TE Store. *)
