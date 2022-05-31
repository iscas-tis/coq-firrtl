From Coq Require Import FunInd FMaps FMapAVL OrderedType ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat ssrint eqtype seq.
From simplssrlib Require Import Types SsrOrder FSets FMaps Tactics Var Store.
From firrtl Require Import Env Firrtl.


Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.




(****** Bundle type ******)
Inductive fflip : Type := Flipped | Nflip.

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
  decide equality. apply fgtyp_eq_dec. apply Nat.eq_dec.
  decide equality.
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
       | Fflips _ Nflip t1 fs1, Fflips _ Nflip t2 fs2
         => ftype_eqn t1 t2 && ffield_eqn fs1 fs2
       | Fflips _ Flipped t1 fs1, Fflips _ Flipped t2 fs2
         => ftype_eqn t1 t2 && ffield_eqn fs1 fs2
       | _, _ => false
       end.

Notation "x =? y" := (ftype_eqn x y).

Lemma ftype_eqn_refl (x : ftype) : x =? x
with ffield_eqn_refl (fx : ffield) : ffield_eqn fx fx.
Proof.
Admitted.

Lemma ftype_eqn_eq (x y : ftype) : x =? y <-> x = y
with ffield_eqn_eq (fx fy : ffield) : ffield_eqn fx fy <-> fx = fy.
Proof.
Admitted.

Lemma ftype_eqn_sym (x y : ftype) : x =? y -> y =? x
with ffield_eqn_sym (fx fy : ffield) : ffield_eqn fx fy -> ffield_eqn fy fx.
Proof.
Admitted.

Lemma ftype_eqn_trans (x y z : ftype) : x =? y -> y =? z -> x =? z
with ffield_eqn_trans (fx fy fz : ffield) : ffield_eqn fx fy -> ffield_eqn fy fz -> ffield_eqn fx fz.
Proof.
Admitted.

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

Lemma ftype_eqP : forall (x y : ftype), reflect (x = y) (x =? y)
with ffield_eqP : forall (fx fy : ffield), reflect (fx = fy) (ffield_eqn fx fy).
Proof.
Admitted.

Definition ftype_eqMixin := EqMixin ftype_eqP.
Definition ffield_eqMixin := EqMixin ffield_eqP.
Canonical ftype_eqType := Eval hnf in EqType ftype ftype_eqMixin.
Canonical ffield_eqType := Eval hnf in EqType ffield ffield_eqMixin.


(* Inductive fcomponent : Type := *)
(* | In_port : var -> fcomponent *)
(* | Instanceof : var -> fcomponent *)
(* | Memory : var -> fcomponent *)
(* | Node : var -> fcomponent *)
(* | Out_port : var -> fcomponent *)
(* | Register : var -> fcomponent *)
(* | Wire : var -> fcomponent *)
(* . *)

Inductive fcomponent : Set :=
| In_port | Instanceof | Memory | Node | Out_port
| Register | Wire.

(** eq dec *)
Axiom component_eq_dec : forall {x y : fcomponent}, {x = y} + {x <> y}.
Parameter component_eqn : forall (x y : fcomponent), bool.
Axiom component_eqP : Equality.axiom component_eqn. 
Canonical component_eqMixin := EqMixin component_eqP.
Canonical component_eqType := Eval hnf in EqType fcomponent component_eqMixin.


(* A mapping from a variable to its component type *)

Module Type CmpntEnv <: SsrFMap.

  Include SsrFMap.

  Definition env : Type := t fcomponent.

  (* The default type of a variable not in the typing environment *)
  Parameter deftyp : fcomponent.

  (* Find the type of a variable in a typing environment.
     If a variable is not in the typing environment, return the default type. *)
  Parameter vtyp : SE.t -> env -> fcomponent.

  (* Return the size of a variable in a typing environment.
     If a variable is not in the typing environment, return the size of the
     default type. *)
  (* Parameter vsize : SE.t -> env -> nat. *)

  Axiom find_some_vtyp :
    forall {x : SE.t} {ty : fcomponent} {e : env}, find x e = Some ty -> vtyp x e = ty.
  Axiom find_none_vtyp :
    forall {x : SE.t} {e : env}, find x e = None -> vtyp x e = deftyp.
  Axiom vtyp_find :
    forall {x : SE.t} {ty : fcomponent} {e : env},
      (vtyp x e == ty) = (find x e == Some ty) || ((find x e == None) && (ty == deftyp)).
  Axiom vtyp_add_eq :
    forall {x y : SE.t} {ty : fcomponent} {e : env}, x == y -> vtyp x (add y ty e) = ty.
  Axiom vtyp_add_neq :
    forall {x y : SE.t} {ty : fcomponent} {e : env},
      x != y -> vtyp x (add y ty e) = vtyp x e.
  (* Axiom vsize_add_eq : *)
  (*   forall {x y : SE.t} {ty : fgtyp} {e : env}, *)
  (*     x == y -> vsize x (add y ty e) = sizeof_fgtyp ty. *)
  (* Axiom vsize_add_neq : *)
  (*   forall {x y : SE.t} {ty : fgtyp} {e : env}, *)
  (*     x != y -> vsize x (add y ty e) = vsize x e. *)
  Axiom not_mem_vtyp :
    forall {v : SE.t} {e : env}, ~~ mem v e -> vtyp v e = deftyp.
  (* Axiom vtyp_vsize : *)
  (*   forall {x : SE.t} {e : env} {ty : fgtyp}, *)
  (*     vtyp x e = ty -> vsize x e = sizeof_fgtyp ty. *)

End CmpntEnv.

Module MakeCmpntEnv (V : SsrOrder) (VM : SsrFMap with Module SE := V) <:
  CmpntEnv with Module SE := V.

  Include VM.
  Module Lemmas := FMapLemmas VM.

  Definition env : Type := t fcomponent.

  (* The default type of a variable not in the typing environment *)
  Definition deftyp : fcomponent := Node.

  (* Find the type of a variable in a typing environment.
     If a variable is not in the typing environment, return the default type. *)
  Definition vtyp (v : V.t) (e : env) : fcomponent :=
    match VM.find v e with
    | None => deftyp
    | Some ty => ty
    end.

  (* Return the size of a variable in a typing environment.
     If a variable is not in the typing environment, return the size of the
     default type. *)
  (* Definition vsize (v : V.t) (e : env) : nat := sizeof_fgtyp (vtyp v e). *)

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

  (* Lemma vsize_add_eq {x y ty e} : x == y -> vsize x (add y ty e) = sizeof_fgtyp ty. *)
  (* Proof. rewrite /vsize=> H. by rewrite (vtyp_add_eq H). Qed. *)

  (* Lemma vsize_add_neq {x y ty e} : x != y -> vsize x (add y ty e) = vsize x e. *)
  (* Proof. rewrite /vsize => H. by rewrite (vtyp_add_neq H). Qed. *)

  Lemma not_mem_vtyp v e : ~~ mem v e -> vtyp v e = deftyp.
  Proof. rewrite /vtyp => H. by rewrite Lemmas.not_mem_find_none. Qed.

  (* Lemma vtyp_vsize x e ty : vtyp x e = ty -> vsize x e = sizeof_fgtyp ty. *)
  (* Proof. rewrite /vsize /vtyp. move=> ->. reflexivity. Qed. *)

End MakeCmpntEnv.

Module CE <: CmpntEnv := MakeCmpntEnv VarOrder VM.


