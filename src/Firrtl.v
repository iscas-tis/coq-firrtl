(*From Coq Require Import ZArith Arith RelationClasses OrderedType FMaps FSets FunInd FMapAVL.*)

From Coq Require Import FunInd FMaps FMapAVL OrderedType.
From mathcomp Require Import ssreflect ssrbool ssrnat ssrint eqtype seq.
From simplssrlib Require Import Types Tactics .

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section RawFirrtl.
  (****** Types Environment ******)

  (****** Ground Types ******)

  From Coq Require Import ZArith.

  Inductive fgtyp : Set :=
    Fuint : nat -> fgtyp
  | Fsint : nat -> fgtyp
  | Fanalog : nat -> fgtyp
  | Fclock
  | Ffixed : nat -> Z -> fgtyp.
  (*| Fvector : fgtyp -> nat -> fgtyp.*)

  (* Size of types *)

  Definition sizeof_fgtyp (t : fgtyp) : nat :=
    match t with
    | Fuint w => w
    | Fsint w => w
    | Fanalog w => w
    | Fclock => 1
    | Ffixed n z => n
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
    - intros; case: (Nat.eq_dec n n0) => H.
      + left; rewrite H; reflexivity.
      + right; move=> []; auto.
    - left; done.
    - intros; case: (Nat.eq_dec n n0) => H;
                                           case: (Z.eq_dec z z0) => H0.
      + left; rewrite H H0; reflexivity.
      + right; move=> []; auto.
      + right; move=> []; auto. 
      + right; move=> []; auto.
  Qed.

  Definition fgtyp_eqn (x y : fgtyp) : bool :=
    match x, y with
    | Fuint wx, Fuint wy => wx == wy
    | Fsint wx, Fsint wy => wx == wy
    | Fanalog wx, Fanalog wy => wx == wy
    | Fclock, Fclock => true
    | Ffixed wx bpx, Ffixed wy bpy => (wx == wy) && (Zeq_bool bpx bpy)
    | _, _ => false
    end.

  Notation "x =? y" := (fgtyp_eqn x y).

  Lemma fgtyp_eqn_refl (x : fgtyp) : x =? x.
  Proof.
    destruct x; try (exact: eqxx).
    - done.
    - rewrite/=; rewrite eqxx andTb. by apply Zeq_is_eq_bool.
  Qed.

  Lemma fgtyp_eqn_eq (x y : fgtyp) : x =? y <-> x = y.
  Proof.
    split; first (destruct x; destruct y; move=> /= H);
      try (discriminate|| rewrite (eqP H); reflexivity).
    - done.
    - move/andP : H => [H1 H2]; by rewrite (eqP H1) (Zeq_bool_eq _ _ H2).
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


  Delimit Scope fgtyp_scope with fgtyp.

  (* Integer, bitvector or ssrint, TBD *)

  (* Fix-point, TBD *)

  (* Analog, TBD *)

  (* Vector, TBD *)


  (****** Syntax ******)

  (****** Expressions ******)

  Inductive ucast : Set :=
  | AsUInt | AsSInt | AsFixed | AsClock.

  Inductive eunop : Set :=
  | Upadding : nat -> eunop
  | Ucast : ucast -> eunop
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
  | Utail : nat -> eunop
  | Uincp
  | Udecp
  | Usetp .

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
  Variable var : eqType.

  (* mux, valid, sub-xxx, TBD *)
  Inductive fexpr : Type :=
  | Econst : int -> fexpr
  | Evar : var -> fexpr
  | Eref : var -> fgtyp -> fexpr
  | Efield : var -> fexpr -> fexpr
  | Esubacc : var -> nat -> fexpr
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

  Record freg : Type :=
    mk_freg
      {
        rid : var;
        type : fexpr;
        reset : seq fexpr
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
  | Sattach : seq var -> fstmt
  | Swhen : var -> fstmt -> fstmt -> fstmt
  | Sstop : fexpr -> fexpr -> nat -> fstmt
  | Sprintf (* TBD *)
  | Sassert (* TBD *)
  | Sassume (* TBD *)
  | Sdefname : var -> fstmt (* TBD *)
  | Sparam : var -> fexpr -> fstmt (* TBD *)
  .

  Inductive fport : Type :=
  | Finput : fexpr -> fport
  | Foutput : fexpr -> fport
  .

  (* TBD *)
  Inductive fmodule : Type :=
  | FInmod : var -> seq fport -> seq fstmt -> fmodule
  | FExmod : var -> seq fport -> seq fstmt -> fmodule
  .

  Definition fcircuit := var -> seq fmodule.
End RawFirrtl.


(* A typing environment is a map from a variable to its type *)
From simplssrlib Require Import SsrOrder FMaps.

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


(*Module TE <: TypEnv := MakeTypEnv VarOrder VM.*)
(*Module SSATE <: TypEnv := MakeTypEnv SSAVarOrder SSAVM.*)

(****** Semantics ******)

(*
Record fstate : Type :=
  mk_state
    {
      fregs : seq freg;
      fmems : seq fmem
    }.
*)
(* TBD *)

(* TBD *)
(*Parameter eval_fstmt : fstate -> fstmt -> fstate.*)
