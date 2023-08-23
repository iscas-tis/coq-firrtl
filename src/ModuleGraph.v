From simplssrlib Require Import SsrOrder FMaps Var ZAriths.
From Coq Require Import ZArith (* for Nat.eq_dec *) FMaps.
From nbits Require Import NBits.
From firrtl Require Import Env Firrtl HiEnv HiFirrtl. (* for hfmodule and its parts *)
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.

(* This file contains first ideas on how to define a module graph as a semantic structure for FIRRTL modules.
   Many definitions are not yet complete but include only a few constructs so as to illustrate what the structure is. *)


Definition Fsint_exp (w : nat) : fgtyp_explicit :=
   (* convert Fsint w to an fgtyp_explicit *)
   exist not_implicit_width (Fsint w) I.

Definition Fuint_exp (w : nat) : fgtyp_explicit :=
   (* convert Fuint w to an output data type *)
   exist not_implicit_width (Fuint w) I.

Definition Freset_exp : fgtyp_explicit :=
   (* convert Freset to an output data type *)
   exist not_implicit_width Freset I.

Definition Fclock_exp : fgtyp_explicit :=
   (* convert Fclock to an output data type *)
   exist not_implicit_width Fclock I.

Definition Fasyncreset_exp : fgtyp_explicit :=
   (* convert Fasyncreset to an output data type *)
   exist not_implicit_width Fasyncreset I.

Definition is_arithmetic (x : fgtyp) : Prop :=
   match x with Fsint _ | Fuint _ => True
              | _ => False end.

Definition arithmetic_data_type : Type :=
   (* data type for arithmetic operations (mainly primitive operations):
      only Fsint and Fuint are allowed *)
   { x : fgtyp | is_arithmetic x }.

Definition Fsint_a (w : nat) : arithmetic_data_type :=
   (* convert Fsint w to an arithmetic_data_type *)
   exist is_arithmetic (Fsint w) I.

Definition Fuint_a (w : nat) : arithmetic_data_type :=
   (* convert Fuint w to an arithmetic_data_type *)
   exist is_arithmetic (Fuint w) I.

(* equality of arithmetic_data_type is decidable *)
Lemma arithmetic_data_type_eq_dec : forall {x y : arithmetic_data_type}, {x = y} + {x <> y}.
Proof.
intros.
destruct x, y.
case: (@fgtyp_eq_dec x x0) => H.
* left.
  destruct x, x0 ; try done ; destruct i, i0 ;
        injection H ; intro ; rewrite H0 ; reflexivity.
* right.
  destruct x, x0 ; try done ;
        injection ; destruct i, i0 ;
        contradict H ; rewrite H ; reflexivity.
Qed.
Definition arithmetic_data_type_eqn (x y : arithmetic_data_type) : bool :=
match x, y with
exist x' _, exist y' _ => fgtyp_eqn x' y'
end.
Lemma arithmetic_data_type_eqP : Equality.axiom arithmetic_data_type_eqn.
Proof.
rewrite /Equality.axiom /fgtyp_explicit_eqn.
intros.
destruct x, y.
destruct x, x0 ; destruct i, i0 ; simpl arithmetic_data_type_eqn ;
     try (apply ReflectF ; discriminate) ;
     try (apply ReflectT ; reflexivity) ;
     destruct (n == n0) eqn: Hnn0.
1, 3: apply ReflectT ;
      move /eqP : Hnn0 => Hnn0 ; rewrite Hnn0 ; reflexivity.
all: apply ReflectF ;
     move /eqP : Hnn0 => Hnn0 ; contradict Hnn0 ;
     injection Hnn0 ; intro ; done.
Qed.
Canonical arithmetic_data_type_eqMixin := EqMixin arithmetic_data_type_eqP.
Canonical arithmetic_data_type_eqType := Eval hnf in EqType arithmetic_data_type arithmetic_data_type_eqMixin.

Inductive vertex_type :=
   (* what kind of vertices can be in the module graph *)
   OutPort : fgtyp (* within the module there is only an input
                                (the output goes to some place outside the module) *) -> vertex_type |
   InPort : fgtyp_explicit -> vertex_type | (* main module only at present *)
   Constant : arithmetic_data_type -> bits (* value of the constant *) -> vertex_type |
   (* register, wire etc. *)

   Cast_UInt : fgtyp_explicit -> vertex_type |
   Cast_SInt : fgtyp_explicit -> vertex_type |
   Cast_Clock : fgtyp_explicit (* must be a 1-bit data type *) -> vertex_type |
   (*Cast_Reset : fgtyp_explicit -> vertex_type |*)
   Cast_Async : fgtyp_explicit (* must be a 1-bit data type *) -> vertex_type |

   Unop_pad : nat -> arithmetic_data_type -> vertex_type |
   Unop_shl : nat -> arithmetic_data_type -> vertex_type |
   Unop_shr : nat -> arithmetic_data_type -> vertex_type |
   Unop_cvt : arithmetic_data_type -> vertex_type |
   Unop_neg : arithmetic_data_type -> vertex_type |
   Unop_not : arithmetic_data_type -> vertex_type |
   Unop_andr : arithmetic_data_type -> vertex_type |
   Unop_orr : arithmetic_data_type -> vertex_type |
   Unop_xorr : arithmetic_data_type -> vertex_type |
   Unop_bits : nat -> nat -> arithmetic_data_type -> vertex_type |
   Unop_head : nat -> arithmetic_data_type -> vertex_type |
   Unop_tail : nat -> arithmetic_data_type -> vertex_type |
   Binop_add : arithmetic_data_type -> vertex_type |
   Binop_sub : arithmetic_data_type -> vertex_type |
   Binop_mul : arithmetic_data_type -> nat -> vertex_type |
   Binop_div : arithmetic_data_type -> vertex_type |
   Binop_rem : arithmetic_data_type -> nat -> vertex_type |
   Binop_lt : arithmetic_data_type -> vertex_type |
   Binop_leq : arithmetic_data_type -> vertex_type |
   Binop_gt : arithmetic_data_type -> vertex_type |
   Binop_geq : arithmetic_data_type -> vertex_type |
   Binop_eq : arithmetic_data_type -> vertex_type |
   Binop_neq : arithmetic_data_type -> vertex_type |
   Binop_dshl : arithmetic_data_type -> nat -> vertex_type |
   Binop_dshr : arithmetic_data_type -> nat -> vertex_type |
   Binop_and : arithmetic_data_type -> vertex_type |
   Binop_or : arithmetic_data_type -> vertex_type |
   Binop_xor : arithmetic_data_type -> vertex_type |
   Binop_cat : arithmetic_data_type -> nat -> vertex_type |
   Invalid : fgtyp_explicit(* unknow *) -> vertex_type |
   (*Reference : fgtyp -> vertex_type |*)
   
   Register : fgtyp -> vertex_type |
   Wire : fgtyp -> vertex_type |
   (*memory : ?
   inst : ?*)
   Node : fgtyp -> vertex_type |

   Mux : fgtyp_explicit (* data type of the input connectors *) -> vertex_type
   (* actually, more vertex types for every primitive operation *).

(* equality of vertex_type is decidable *)
Lemma vertex_type_eq_dec : forall {x y : vertex_type}, {x = y} + {x <> y}.
Proof.  decide equality ; try apply fgtyp_eq_dec ; try apply fgtyp_explicit_eq_dec ; try apply arithmetic_data_type_eq_dec.
Admitted.

Definition vertex_type_eqn (x y : vertex_type) : bool :=
match x, y with
| OutPort i, OutPort j
| InPort i, InPort j => i == j
| Constant a1 b1, Constant a2 b2 => (a1 == a2) && (b1 == b2)

| Cast_UInt a, Cast_UInt b
| Cast_SInt a, Cast_SInt b
| Cast_Clock a, Cast_Clock b
(*| Cast_Reset a, Cast_Reset b*)
| Cast_Async a, Cast_Async b
| Unop_cvt a, Unop_cvt b
| Unop_neg a, Unop_neg b
| Unop_not a, Unop_not b
| Unop_andr a, Unop_andr b
| Unop_orr a, Unop_orr b
| Unop_xorr a, Unop_xorr b
| Binop_sub a, Binop_sub b
| Binop_div a, Binop_div b
| Binop_lt a, Binop_lt b
| Binop_leq a, Binop_leq b
| Binop_gt a, Binop_gt b
| Binop_geq a, Binop_geq b
| Binop_eq a, Binop_eq b
| Binop_neq a, Binop_neq b
| Binop_and a, Binop_and b
| Binop_or a, Binop_or b
| Binop_xor a, Binop_xor b
| Invalid a, Invalid b
(*| Reference a, Reference b*)
| Register a, Register b
| Wire a, Wire b
(*memory : ?
inst : ?*)
| Node a, Node b
| Binop_add a, Binop_add b => a == b
| Mux o, Mux w => o == w
| Unop_pad n1 a, Unop_pad n2 b 
| Unop_shl n1 a, Unop_shl n2 b
| Unop_shr n1 a, Unop_shr n2 b
| Unop_head n1 a, Unop_head n2 b
| Unop_tail n1 a, Unop_tail n2 b => (a == b) && (n1 == n2)
| Unop_bits n1 n2 a, Unop_bits n3 n4 b => (a == b) && (n1 == n3) && (n2 == n4)
| Binop_mul a b, Binop_mul c d
| Binop_rem a b, Binop_rem c d 
| Binop_cat a b, Binop_cat c d 
| Binop_dshl a b, Binop_dshl c d
| Binop_dshr a b, Binop_dshr c d => (a == c) && (b == d)
| _, _ => false
end.
Lemma vertex_type_eqP : Equality.axiom vertex_type_eqn.
Proof.
rewrite /Equality.axiom ; intros.
case: (@vertex_type_eq_dec x y) => H.
* rewrite H /vertex_type_eqn ; clear -y.
  destruct y ; try rewrite eq_refl ; try rewrite eq_refl andTb ; try rewrite eq_refl andTb ; apply ReflectT ; try reflexivity.
* rewrite /vertex_type_eqn.
  destruct x, y ; try contradiction ; try (apply ReflectF ; exact H).
  + 1, 38, 39, 40:
    assert (f <> f0) by (contradict H ; rewrite H ; reflexivity) ;
    move /eqP : H0 => H0 ; apply negbTE in H0 ;
    rewrite H0 ; apply ReflectF ; exact H.
  + 1, 3, 4, 5, 6, 36, 37:
    assert (f <> f0) by (contradict H ; rewrite H ; reflexivity) ;
    move /eqP : H0 => H0 ; apply negbTE in H0 ;
    rewrite H0 ; apply ReflectF ; exact H.
  + destruct (b == b0) eqn: Hb ;
    try (rewrite andbF ; apply ReflectF ; exact H) ;
    move /eqP : Hb => Hb ; rewrite Hb andbT ; rewrite Hb in H ; clear Hb.
  + 2, 3, 4, 12, 13, 16, 18, 25, 26, 30:
    destruct (n == n0) eqn: Hn ;
    try (rewrite andbF ; apply ReflectF ; exact H) ;
    move /eqP : Hn => Hn ; rewrite Hn andbT ; rewrite Hn in H ; clear Hn.
  + 18:
    destruct (n0 == n2) eqn: Hn ;
    try (rewrite andbF ; apply ReflectF ; exact H) ;
    move /eqP : Hn => Hn ; rewrite Hn andbT ; rewrite Hn in H ; clear Hn ;
    destruct (n == n1) eqn: Hn ;
    try (rewrite andbF ; apply ReflectF ; exact H) ;
    move /eqP : Hn => Hn ; rewrite Hn andbT ; rewrite Hn in H ; clear Hn.
  + all:
    assert (a <> a0) by (contradict H ; rewrite H ; reflexivity) ;
    move /eqP : H0 => H0 ; apply negbTE in H0 ;
    rewrite H0 ; apply ReflectF ; exact H.
Qed.
Canonical vertex_type_eqMixin := EqMixin vertex_type_eqP.
Canonical vertex_type_eqType := Eval hnf in EqType vertex_type vertex_type_eqMixin.

Definition  input_connectors (v : vertex_type) : seq fgtyp :=
   (* calculates the list of data types of input connectors of a vertex.
      It should be a list because the function of different input connectors can be different
      (for example with the multiplexer). *)
   match v with
   | OutPort it => [:: it]
   | InPort _ (* An InPort has no input connector because the data comes from somewhere outside the module *)
   | Constant _ _

   | Invalid _ => [::]
   | Register it
   | Wire it
   (* 
   reference it
   memory : ?
   inst : ? *)
   | Node it => [:: it]

   | Cast_UInt (exist it _)
   | Cast_SInt (exist it _)
   | Cast_Clock (exist it _)
   (*| Cast_Reset (exist it _) => [:: it]*)
   | Cast_Async (exist it _)
   | Unop_cvt (exist it _)
   | Unop_neg (exist it _)
   | Unop_not (exist it _)
   | Unop_andr (exist it _)
   | Unop_orr (exist it _)
   | Unop_xorr (exist it _) => [:: it]
   | Unop_pad (*nat*) _ (exist it _)
   | Unop_shl _ (exist it _)
   | Unop_shr _ (exist it _) 
   | Unop_bits _ _ (exist it _) 
   | Unop_head _ (exist it _) 
   | Unop_tail _ (exist it _) => [:: it]
   | Binop_add (exist it _)
   | Binop_sub (exist it _)
   | Binop_div (exist it _)
   | Binop_lt (exist it _)
   | Binop_leq (exist it _)
   | Binop_gt (exist it _)
   | Binop_geq (exist it _)
   | Binop_eq (exist it _)
   | Binop_neq (exist it _)
   | Binop_and (exist it _)
   | Binop_or (exist it _)
   | Binop_xor (exist it _) => [:: it; it]
   | Binop_mul (exist (Fuint n1) _) n2 
   | Binop_cat (exist (Fuint n1) _) n2 
   | Binop_rem (exist (Fuint n1) _) n2 => [:: (Fuint n1); (Fuint n2)]
   | Binop_mul (exist (Fsint n1) _) n2 
   | Binop_cat (exist (Fsint n1) _) n2 
   | Binop_rem (exist (Fsint n1) _) n2 => [:: (Fsint n1); (Fsint n2)]
   (*| Multiplier (exist (Fsint w) _) n => [:: Fsint w ; Fsint n]
   | Multiplier (exist (Fuint w) _) n => [:: Fuint w ; Fuint n]
   | Multiplier (exist _ p) _ => False_rect (seq fgtyp) p *)
   | Binop_dshl (exist it _) n2
   | Binop_dshr (exist it _) n2 => [:: it; (Fuint n2)]

   | Mux (exist it _) => [:: Fuint 1 ; it ; it]
   | _ => [::]
   end.

Definition output_connectors (v : vertex_type) : seq fgtyp_explicit :=
(* a list of types of the output connectors of a vertex of type v *)
   match v with
   | OutPort _ => [::] (* An OutPort has no output connector because the data is sent to somewhere outside the module *)
   (*| InPort (Fsint_implicit w) => [:: Fsint_exp w]
   | InPort (Fuint_implicit w) => [:: Fuint_exp w]
   | InPort it => [:: exist not_implicit_width it I] (* convert to fgtyp_explicit *)
   *)
   | InPort it => [:: it]
   | Constant (exist (Fsint w) _) _ => [:: Fsint_exp w]
   | Constant (exist (Fuint w) _) _ => [:: Fuint_exp w]
   | Constant (exist _ p) _ => False_rect (seq fgtyp_explicit) p (* p is a proof of False, so this cannot happen in reality *)

   | Cast_UInt (exist (Fuint w) _)
   | Cast_UInt (exist (Fsint w) _) => [:: Fuint_exp w]
   | Cast_UInt (exist Fclock _)
   | Cast_UInt (exist Freset _)
   | Cast_UInt (exist Fasyncreset _) => [:: Fuint_exp 1]
   | Cast_UInt (exist _ p) => False_rect (seq fgtyp_explicit) p
   | Cast_SInt (exist (Fuint w) _)
   | Cast_SInt (exist (Fsint w) _) => [:: Fsint_exp w]
   | Cast_SInt (exist Fclock _)
   | Cast_SInt (exist Freset _)
   | Cast_SInt (exist Fasyncreset _) => [:: Fsint_exp 1]
   | Cast_SInt (exist _ p) => False_rect (seq fgtyp_explicit) p
   | Cast_Clock _ => [:: Fclock_exp]
   | Cast_Async _ => [:: Fasyncreset_exp]
   | Unop_cvt (exist (Fuint w) _) => [:: Fsint_exp (w+1)]
   | Unop_cvt (exist (Fsint w) _) => [:: Fsint_exp w]
   | Unop_cvt (exist _ p) => False_rect (seq fgtyp_explicit) p
   | Unop_neg (exist (Fuint w) _) => [:: Fsint_exp (w+1)]
   | Unop_neg (exist (Fsint w) _) => [:: Fsint_exp (w+1)]
   | Unop_neg (exist _ p) => False_rect (seq fgtyp_explicit) p
   | Unop_not (exist (Fuint w) _)
   | Unop_not (exist (Fsint w) _) => [:: Fuint_exp w]
   | Unop_not (exist _ p) => False_rect (seq fgtyp_explicit) p
   | Binop_and (exist (Fuint w) _) 
   | Binop_or (exist (Fuint w) _) 
   | Binop_xor (exist (Fuint w) _)
   | Binop_and (exist (Fsint w) _) 
   | Binop_or (exist (Fsint w) _) 
   | Binop_xor (exist (Fsint w) _) => [:: Fuint_exp w]
   | Binop_or (exist _ p)
   | Binop_xor (exist _ p)
   | Binop_and (exist _ p) => False_rect (seq fgtyp_explicit) p
   | Unop_andr _
   | Unop_orr _
   | Unop_xorr _ => [:: Fuint_exp 1]
   | Binop_add (exist (Fsint w) _)
   | Binop_sub (exist (Fsint w) _) => [:: Fsint_exp (w+1)]
   | Binop_add (exist (Fuint w) _)
   | Binop_sub (exist (Fuint w) _) => [:: Fuint_exp (w+1)]
   | Binop_add (exist _ p)
   | Binop_sub (exist _ p) => False_rect (seq fgtyp_explicit) p (* p is a proof of False, so this cannot happen in reality *)
   | Binop_div (exist (Fsint w) _) => [:: Fsint_exp (w+1)]
   | Binop_div (exist (Fuint w) _) => [:: Fuint_exp (w)]
   | Binop_div (exist _ p) => False_rect (seq fgtyp_explicit) p
   | Binop_lt (exist (Fuint _) _)
   | Binop_lt (exist (Fsint _) _)
   | Binop_leq (exist (Fuint _) _)
   | Binop_leq (exist (Fsint _) _)
   | Binop_gt (exist (Fuint _) _)
   | Binop_gt (exist (Fsint _) _)
   | Binop_geq (exist (Fuint _) _)
   | Binop_geq (exist (Fsint _) _)
   | Binop_eq (exist (Fuint _) _)
   | Binop_eq (exist (Fsint _) _)
   | Binop_neq (exist (Fuint _) _)
   | Binop_neq (exist (Fsint _) _) => [:: Fuint_exp 1]
   | Binop_lt (exist _ p)
   | Binop_leq (exist _ p)
   | Binop_gt (exist _ p)
   | Binop_geq (exist _ p)
   | Binop_eq (exist _ p)
   | Binop_neq (exist _ p) => False_rect (seq fgtyp_explicit) p

   | Invalid ot => [:: ot]
   | Register (Fuint w) | Register (Fuint_implicit w) => [:: Fuint_exp w]
   | Register (Fsint w) | Register (Fsint_implicit w) => [:: Fsint_exp w]
   | Register Fclock => [:: Fclock_exp]
   | Register Freset => [:: Freset_exp]
   | Register Fasyncreset => [:: Fasyncreset_exp]
   | Wire (Fuint w) | Wire (Fuint_implicit w) => [:: Fuint_exp w]
   | Wire (Fsint w) | Wire (Fsint_implicit w) => [:: Fsint_exp w]
   | Wire Fclock => [:: Fclock_exp]
   | Wire Freset => [:: Freset_exp]
   | Wire Fasyncreset => [:: Fasyncreset_exp]
   | Node (Fuint w) | Node (Fuint_implicit w) => [:: Fuint_exp w]
   | Node (Fsint w) | Node (Fsint_implicit w) => [:: Fsint_exp w]
   | Node Fclock => [:: Fclock_exp]
   | Node Freset => [:: Freset_exp]
   | Node Fasyncreset => [:: Fasyncreset_exp]
   (* 
   reference it
   memory : ?
   inst : ? *)

   | Binop_mul (exist (Fuint n1) _) n2 => [:: Fuint_exp (n1 + n2)]   
   | Binop_mul (exist (Fsint n1) _) n2 => [:: Fsint_exp (n1 + n2)]
   | Binop_cat (exist (Fuint n1) _) n2 => [:: Fuint_exp (n1 + n2)]   
   | Binop_cat (exist (Fsint n1) _) n2 => [:: Fsint_exp (n1 + n2)]   
   | Binop_rem (exist (Fuint n1) _) n2 => [:: Fuint_exp (Nat.min n1 n2)]
   | Binop_rem (exist (Fsint n1) _) n2 => [:: Fsint_exp (Nat.min n1 n2)]
   | Binop_rem (exist _ p) _ => False_rect (seq fgtyp_explicit) p
   | Binop_dshl (exist (Fuint n1) _) n2 => [:: Fuint_exp (n1 + (Nat.pow 2 n2) -1)] 
   | Binop_dshl (exist (Fsint n1) _) n2 => [:: Fsint_exp (n1 + (Nat.pow 2 n2) -1)]   
   | Binop_dshr (exist (Fuint n1) _) n2 => [:: Fuint_exp n1]
   | Binop_dshr (exist (Fsint n1) _) n2 => [:: Fsint_exp n1]
   | Binop_cat (exist _ p) _
   | Binop_dshl (exist _ p) _
   | Binop_dshr (exist _ p) _
   | Binop_mul (exist _ p) _ => False_rect (seq fgtyp_explicit) p
   | Unop_pad n (exist (Fuint n1) _) => [:: Fuint_exp (Nat.max n n1)]   
   | Unop_pad n (exist (Fsint n1) _) => [:: Fsint_exp (Nat.max n n1)]   
   | Unop_pad _ (exist _ p) => False_rect (seq fgtyp_explicit) p
   | Unop_shl n (exist (Fuint n1) _) => [:: Fuint_exp (n + n1)] 
   | Unop_shl n (exist (Fsint n1) _) => [:: Fsint_exp (n + n1)]   
   | Unop_shl _ (exist _ p) => False_rect (seq fgtyp_explicit) p
   | Unop_shr n (exist (Fuint n1) _) => [:: Fuint_exp (Nat.max (n1 - n) 1)] 
   | Unop_shr n (exist (Fsint n1) _) => [:: Fsint_exp (Nat.max (n1 - n) 1)] 
   | Unop_shr _ (exist _ p) => False_rect (seq fgtyp_explicit) p
   | Unop_bits hi lo (exist it _) => [:: Fuint_exp (hi - lo + 1)]
   | Unop_head n (exist it _) => [:: Fuint_exp n] 
   | Unop_tail n (exist (Fuint n1) _) => [:: Fuint_exp (n1 - n)]
   | Unop_tail n (exist (Fsint n1) _) => [:: Fuint_exp (n1 - n)]
   | Unop_tail _ (exist _ p) => False_rect (seq fgtyp_explicit) p

   | Mux ot => [:: ot]
   end.

(*
Fixpoint type_of_subfield (ff : ffield) (var : VarOrder.T) : option ftype :=
   match ff with
   | Fnil => None (* error *)
   | Fflips var' _ t ff' => if var == var' then Some t else type_of_subfield ff' var
   end.

Fixpoint type_of_ref (ref : href VarOrder.T) (env : CE.env) : option ftype :=
   (* produces the type of a (possibly non-trivial) reference.
      CE is a component environment that information about every aggregate
      (not about the ground elements contained in the aggregate). *)
   match ref with
   | Eid var => if CE.find var env is Some (Aggr_typ t, _) then Some t else None (* error *)
   | Esubfield ref' var => match type_of_ref ref' env with
                           | Some (Btyp ff) => type_of_subfield ff var
                           | _ => None (* error *)
                           end
   | Esubindex ref' _ => match type_of_ref ref' env with
                         | Some (Atyp t' _) => Some t'
                         | _ => None (* error *)
                         end
   | Esubaccess _ _ => None (* not implemented *)
   end.
*)

(*
Fixpoint offset_of_subfield (ff : ffield) (var : VarOrder.T) : option nat :=
   (* auxiliary function for offset_of_ref *)
   match ff with
   | Fnil => None (* error *)
   | Fflips var' _ t ff' => if var == var' then Some 0
                            else if offset_of_subfield ff' var is Some offset
                                 then Some (size_of_ftype t + offset)
                                 else None
   end.

Fixpoint offset_of_ref (ref : href VarOrder.T) (env : CE.env) : option nat :=
   (* produces the offset of a (possibly non-trivial) reference to a part of a variable of type t.
      However, this function may need to be changed because vtype_list is different. *)
   match ref with
   | Eid _ => Some 0
   | Esubfield ref' var => match type_of_ref ref' env with
                           | Some (Btyp ff) => match offset_of_ref ref' env, offset_of_subfield ff var with
                                               | Some n, Some m => Some (n + m)
                                               | _, _ => None
                                               end
                           | _ => None (* error *)
                           end
   | Esubindex ref' i => match type_of_ref ref' env, offset_of_ref ref' env with
                         | Some (Atyp t' _), Some n => Some (n + (size_of_ftype t' * i))
                         | _, _ => None (* error *)
                         end
   | Esubaccess _ _ => None (* not implemented *)
   end.
*)

(* Perhaps module_graph_vertices could be the type of FMap from VarOrder
   (or any other set of identifiers)
   to vertex_type instead of the set below.
   output_connectors_of_module_graph then is not a Type but a FSet containing pairs
   (element of the domain of module_graph_vertices, suitable number).
   Problem may be that then connection_tree is more difficult to define,
   see the type of the parameter of Leaf.
   Advantage of defining it as FMap is that it is easier to define Sem,
   because operators to add an element to a FMap are readily available. *)

(* Definition module_graph_vertex_set : Type := FMap VarOrder vertex_type. *)
(* keys: vertex identifiers, e.g. VarOrder; values : vertex_type *)

Module Type SFMap <: FMapInterface.S.
  Declare Module SE : OrderedType.OrderedType.
  Module E : OrderedType.OrderedType
  with Definition t := SE.t
  with Definition eq := SE.eq
  with Definition lt := SE.lt
    := SE.
  Include Sfun SE.
End SFMap.

Module Type VtypFMap <: SFMap.
  Include SFMap.
  Definition env : Type := t vertex_type.
  (* Parameter def_vtyp : vertex_type. *)
  
End VtypFMap.

Module MakeVtypFMap (V : SsrOrder) (VM : SFMap with Module SE := V)
<: VtypFMap with Module SE := V.
  Include VM.
  Definition env : Type := t vertex_type.
End MakeVtypFMap.

Module module_graph_vertex_set_s <: VtypFMap := MakeVtypFMap VarOrder VM. 
Module ProdVarOrder := MakeProdOrderWithDefaultSucc VarOrder VarOrder.
Module PVM <: SsrFMapWithNew := FMaps.MakeTreeMapWithNew ProdVarOrder.
Module module_graph_vertex_set_p <: VtypFMap := MakeVtypFMap ProdVarOrder PVM.

(* ... { V : Set & V -> vertex_type }. *)
   (* This is a type of pairs consisting of a set and a function from this set to vertex_type.
      Given V : module_graph_vertices, the set is (projT1 V) and the function is (projT2 V).
      I would like V to be a finite set but I don't know exactly how to specify that. *)

Definition module_graph_vertex_set : Type := { V : Set & V -> vertex_type }.
Definition output_connector_number_correct (V : module_graph_vertex_set_p.env) (x : module_graph_vertex_set_p.key * nat) : Prop :=
    if module_graph_vertex_set_p.find (fst x) V is Some elt
    then snd x < size (output_connectors elt)
    else False.

Definition output_connectors_of_module_graph (V : module_graph_vertex_set_p.env) : Type :=
   { x : module_graph_vertex_set_p.key * nat | output_connector_number_correct V x }.
   (* This is a type of pairs, where the first is an element of a module_graph_vertices set,
      and the second of the pair is a natural number that is < than the number of output connectors of that element. *)

Definition output_connector_type (V : module_graph_vertex_set_p.env) (oc : output_connectors_of_module_graph V) : fgtyp_explicit.
destruct oc as [x p].
unfold output_connector_number_correct in p.
destruct (module_graph_vertex_set_p.find (fst x) V) as [elt|].
clear -x elt ; exact (nth Freset_exp (output_connectors elt) (snd x)).
clear -p ; exact (False_rect fgtyp_explicit p).
Defined.

Inductive connection_tree (V: module_graph_vertex_set_p.env) :=
   Invalidated | Not_connected |
   Leaf : (output_connectors_of_module_graph V) -> connection_tree V |
   Choice : {cond : output_connectors_of_module_graph V |
                    output_connector_type V cond = Fuint_exp 1 }
                    (* the type of cond needs to be Fuint_exp 1 *)
            -> connection_tree V -> connection_tree V -> connection_tree V.

Definition input_connectors_of_module_graph (V : module_graph_vertex_set_p.env) : Type :=
   { x : module_graph_vertex_set_p.key * nat | if module_graph_vertex_set_p.find (fst x) V is Some elt
                                               then snd x < size (input_connectors elt)
                                               else False }.
   (* This is a set containing pairs, where the first is an element of a module_graph_vertices set,
      and the second of the pair is a natural number that is < than the number of input connectors of that element. *)

Definition input_connector_type (V : module_graph_vertex_set_p.env) (ic : input_connectors_of_module_graph V) : fgtyp.
destruct ic as [x p].
destruct (module_graph_vertex_set_p.find (fst x) V) as [elt|].
clear -x elt ; exact (nth Freset (input_connectors elt) (snd x)).
clear -p ; exact (False_rect fgtyp p).
Defined.

Definition module_graph_connection_trees (V: module_graph_vertex_set_p.env): Type :=
   input_connectors_of_module_graph V -> connection_tree V.

Definition module_graph : Type :=
(* a pair, namely a set of module_graph_vertices, together with a mapping that gives a connection tree
for every input connector of every module_graph_vertex. *)
   { V : module_graph_vertex_set_p.env & module_graph_connection_trees V }.

(* module_graph_vertex_set_p : pair identifier -> vertex_type *)
(*
Definition type_of_cmpnttyp ct :=
    match ct with
    | Aggr_typ t => t
    | Reg_typ r => type r
    | Mem_typ m => data_type m
    | Unknown_typ => Gtyp (Fuint 0)
    end. *)

(*Definition ftype2fgtyp_explicit (ft : ftype) : fgtyp_explicit :=
   match ft with
   | Gtyp (Fuint n) => Fuint_exp n 
   | Gtyp (Fsint n) => Fsint_exp n 
   | Gtyp Fclock => Fclock_exp
   | Gtyp Freset => Freset_exp
   | Gtyp Fasyncreset => Fasyncreset_exp
   | _ => Fuint_exp 0
   end.

Definition ftype2fgtyp (ft : ftype) : fgtyp :=
   match ft with
   | Gtyp (Fuint 0) => Fuint_implicit ?
   | Gtyp (Fuint n) => Fuint n 
   | Gtyp (Fsint n) => Fsint n 
   | Gtyp Fclock => Fclock
   | Gtyp Freset => Freset
   | Gtyp Fasyncreset => Fasyncreset
   | _ => Fuint 0
   end.
*)
(*
Inductive hfport : Type :=
| Finput : pvar -> ftype -> hfport
| Foutput : pvar -> ftype -> hfport.

Inductive hfexpr : Type :=
| Econst : fgtyp -> bits -> hfexpr
| Ecast : ucast -> hfexpr -> hfexpr
| Eprim_unop : eunop -> hfexpr -> hfexpr
| Eprim_binop : ebinop -> hfexpr -> hfexpr -> hfexpr
| Emux : hfexpr -> hfexpr -> hfexpr -> hfexpr
| Eref : href -> hfexpr
with href : Type :=
| Eid : pvar -> href
| Esubfield : href -> pvar -> href (* HiFirrtl *)
| Esubindex : href -> nat -> href (* HiFirrtl *)
| Esubaccess : href -> hfexpr -> href (* HiFirrtl *)
.*)

Fixpoint list_repeat_fn (f : list fgtyp -> list fgtyp) (n : nat) (l : list fgtyp) : list fgtyp :=
   (* Applies function f n times to list l *)
   match n with
   | 0 => l
   | S m => list_repeat_fn f m (f l)
   end.

Fixpoint vtype_list (ft : ftype) (l : list fgtyp) : list fgtyp :=
   (* appends to list l the ground type elements of type ft *)
   match ft with
   | Gtyp t => rcons l t
   | Atyp t n => list_repeat_fn (vtype_list t) n l
   | Btyp b => vtype_list_btyp b l
   end
   with vtype_list_btyp (b : ffield) (l : list fgtyp) : list fgtyp :=
   match b with
   | Fnil => l
   | Fflips v fl t fs => vtype_list_btyp fs (vtype_list t l)
   end.

Lemma vtype_list_cat : forall (ft : ftype) (l : list fgtyp), vtype_list ft l = l ++ vtype_list ft [::]
with vtype_list_btyp_cat : forall (b : ffield) (l : list fgtyp), vtype_list_btyp b l = l ++ vtype_list_btyp b [::].
Proof.
* clear vtype_list_cat.
  induction ft.
  + intro. rewrite /vtype_list {2}/rcons cats1 //.
  + simpl vtype_list.
    induction n.
    - intro. rewrite /list_repeat_fn cats0 //.
    - intro. simpl list_repeat_fn.
      rewrite (IHn (vtype_list ft l)) (IHn (vtype_list ft [::])).
      rewrite IHft -catA //.
  + intro. simpl vtype_list. apply vtype_list_btyp_cat.
* clear vtype_list_btyp_cat.
  induction b.
  + intro. rewrite /vtype_list_btyp cats0 //.
  + intro. simpl vtype_list_btyp.
    rewrite (IHb (vtype_list f0 l)) (IHb (vtype_list f0 [::])).
    rewrite (vtype_list_cat f0 l) -catA //.
Qed.

(*
Lemma vtype_list_size : forall ft : ftype, size (vtype_list ft [::]) = size_of_ftype ft
with vtype_list_btyp_size : forall ff : ffield, size (vtype_list_btyp ff) = size_of_fields ff.
Proof.
* clear vtype_list_size.
  induction t.
  + unfold vtype_list, size, size_of_ftype.
    reflexivity.
  + simpl vtype_list ; simpl size_of_ftype.
    rewrite nseq_seq_len IHt //.
  + apply vtype_list_btyp_size.
* clear vtype_list_btyp_size.
  induction ff.
  + unfold vtype_list_btyp, size, size_of_fields.
    reflexivity.
  + simpl vtype_list_btyp ; simpl size_of_fields.
    rewrite size_cat IHff vtype_list_size //.
Qed.
*)

Definition data_type_in2out (dt : fgtyp) : fgtyp_explicit :=
   match dt with
   | Fsint n => Fsint_exp n 
   | Fuint n => Fuint_exp n 
   | Freset => Freset_exp
   | Fasyncreset => Fasyncreset_exp
   | Fclock => Fclock_exp
   | Fsint_implicit _ 
   | Fuint_implicit _ => Fuint_exp 0
   end.

Definition data_type_out2in (dt : fgtyp_explicit) : fgtyp :=
   match dt with
   | exist (Fuint w) _ => Fuint 0
   | _ => Fuint 0
   end.

Definition data_type_out2arith (dt : fgtyp_explicit) : arithmetic_data_type :=
   match dt with
   | exist (Fsint w) _ => Fsint_a w
   | exist (Fuint w) _ => Fuint_a w
   | exist (Freset) _
   | exist (Fasyncreset) _
   | exist (Fclock) _ 
   | _ => Fuint_a 0
   end.

Fixpoint add_vertex_input (v : N (*pvar match(_,0)从(_,1)开始添加*)) (n : N (*index*)) (l: list fgtyp) (vmap : module_graph_vertex_set_p.env) :=
   match l with
   | nil => vmap
   | hd :: tl => let ohd := data_type_in2out hd in
                 let nvmap := module_graph_vertex_set_p.add (v, n) (InPort ohd) vmap in
                 add_vertex_input v (N.add n 1) tl nvmap
                 (* 添加 Not_connected *)
   end.

Fixpoint add_vertex_output (v : N) (N : N) (l: list fgtyp) (vmap : module_graph_vertex_set_p.env) :=
   match l with
   | nil => vmap
   | hd :: tl => let nvmap := module_graph_vertex_set_p.add (v, N) (OutPort hd) vmap in
                 add_vertex_output v (N.add N 1) tl nvmap
   end.

Definition add_vertex_port (p : hfport ProdVarOrder.T) (vmap : module_graph_vertex_set_p.env) : module_graph_vertex_set_p.env :=
   match p with
   | Finput (v,_) t => let vtl := vtype_list t nil in
                        add_vertex_input v 1 vtl vmap 
   | Foutput (v,_) t => let vtl := vtype_list t nil in
                        add_vertex_output v 1 vtl vmap 
   end.

(*Fixpoint add_vertex_asuint (v : N) (N : N) (l: list fgtyp_explicit) (vmap : module_graph_vertex_set_p.env) :=
   match l with
   | nil => vmap
   | hd :: tl => let nvmap := module_graph_vertex_set_p.add (v, N) (Cast_UInt hd) vmap in
                 add_vertex_asuint v (N.add N 1) tl nvmap
   end.

Fixpoint add_vertex_assint (v : N) (N : N) (l: list fgtyp_explicit) (vmap : module_graph_vertex_set_p.env) :=
   match l with
   | nil => vmap
   | hd :: tl => let nvmap := module_graph_vertex_set_p.add (v, N) (Cast_SInt hd) vmap in
                 add_vertex_assint v (N.add N 1) tl nvmap
   end.

Fixpoint add_vertex_asclock (v : N) (N : N) (l: list fgtyp_explicit) (vmap : module_graph_vertex_set_p.env) :=
   match l with
   | nil => vmap
   | hd :: tl => let nvmap := module_graph_vertex_set_p.add (v, N) (Cast_Clock hd) vmap in
                 add_vertex_asclock v (N.add N 1) tl nvmap
   end.

Fixpoint add_vertex_asasync (v : N) (N : N) (l: list fgtyp_explicit) (vmap : module_graph_vertex_set_p.env) :=
   match l with
   | nil => vmap
   | hd :: tl => let nvmap := module_graph_vertex_set_p.add (v, N) (Cast_Async hd) vmap in
                 add_vertex_asasync v (N.add N 1) tl nvmap
   end.*)

Fixpoint list_inputs (p : N) (n : N) (counts : nat) (l : list fgtyp) (vmap : module_graph_vertex_set_p.env) : list fgtyp :=
   match counts with 
   | 0 => l
   | S m => match (module_graph_vertex_set_p.find (p, N.of_nat (n - m)) vmap) with
            | Some v => l ++ (input_connectors v) ++ list_inputs p n m l vmap
            | None => l ++ list_inputs p n m l vmap
            end
   end. (* return 从(p,1)到(p,n)的input_connectors *)

Fixpoint list_outputs (p : N) (n : N) (counts : nat) (l : list fgtyp_explicit) (vmap : module_graph_vertex_set_p.env) : list fgtyp_explicit :=
   match counts with 
   | 0 => l
   | S m => match (module_graph_vertex_set_p.find (p, N.of_nat (n - m)) vmap) with
            | Some v => l ++ (output_connectors v) ++ list_outputs p n m l vmap
            | None => l ++ list_outputs p n m l vmap
            end
   end. (* return 从(p,1)到(p,n)的output_connectors *)

Definition add_vertex_cast (c : ucast) (l: list fgtyp_explicit) (vmap : module_graph_vertex_set_p.env) : vertex_type :=
   match c with
   | AsUInt => Cast_UInt (List.hd (Fuint_exp 0) l)
   | AsSInt => Cast_SInt (List.hd (Fsint_exp 0) l)
   | AsClock => Cast_Clock (List.hd Fclock_exp l)
   | AsAsync => Cast_Async (List.hd Fasyncreset_exp l)
   | AsReset => Cast_Async (List.hd Fasyncreset_exp l)(*? spec 中没有了*)
   end.

Definition add_vertex_unop (u : eunop) (l: list fgtyp_explicit) (vmap : module_graph_vertex_set_p.env) :=
   match u with
  | Upad n => Unop_pad n (data_type_out2arith (List.hd (Fuint_exp 0) l))
  | Ushl n => Unop_shl n (data_type_out2arith (List.hd (Fuint_exp 0) l))
  | Ushr n => Unop_shr n (data_type_out2arith (List.hd (Fuint_exp 0) l))
  | Ucvt => Unop_cvt (data_type_out2arith (List.hd (Fuint_exp 0) l))
  | Uneg => Unop_neg (data_type_out2arith (List.hd (Fuint_exp 0) l))
  | Unot => Unop_not (data_type_out2arith (List.hd (Fuint_exp 0) l))
  | Uandr => Unop_andr (data_type_out2arith (List.hd (Fuint_exp 0) l))
  | Uorr => Unop_orr (data_type_out2arith (List.hd (Fuint_exp 0) l))
  | Uxorr => Unop_xorr (data_type_out2arith (List.hd (Fuint_exp 0) l))
  | Uextr hi lo => Unop_bits hi lo (data_type_out2arith (List.hd (Fuint_exp 0) l))
  | Uhead n => Unop_head n (data_type_out2arith (List.hd (Fuint_exp 0) l))
  | Utail n => Unop_tail n (data_type_out2arith (List.hd (Fuint_exp 0) l))
   end.

(*
Definition add_vertex_binop (b : ebinop) (l1: list fgtyp_explicit) (l2: list fgtyp_explicit) (vmap : module_graph_vertex_set_p.env) :=
   match b with
   | Badd => match (data_type_out2arith (List.hd (Fuint_exp 0) l1)), (data_type_out2arith (List.hd (Fuint_exp 0) l2)) with
             | exist (Fsint w1) _, exist (Fsint w2) _ =>
             | exist (Fuint w1) _, exist (Fuint w2) _ =>
             | =>
             end
   
   Binop_add ( (List.hd (Fuint_exp 0) l1))
   | Bsub => 
   | Bdiv => 
   | Brem => 
   | Bmul => 
   | Bcomp c => 
   | Band => 
   | Bor => 
   | Bxor => 
   | Bcat => 
   | Bdshl => 
   | Bdshr => 
   end.

Fixpoint list_lhs_expr (e : hfexpr ProdVarOrder.T) (vmap : module_graph_vertex_set_p.env) (cs : list (input_connectors vmap)) (ts : list fgtyp) : list input_connectors * list fgtyp :=
   match e with
   | Eref (Eid (p, 0)) => let (keys, _) := List.split (elements vmap) (* list (key*value) *) in
                          let n := List.length (fst (List.split keys)) in
                          (* connectors' name * *)list_inputs p n 0 nil
   | Eref (Eid pv) => match (find pv vmap) with
                     | Some v => input_connectors v
                     | None => [::]
                     end
   | _ => [::]
   end.
*)

Fixpoint list_output' {mg : module_graph} (p : var) (n : nat) : option (seq (output_connectors_of_module_graph (projT1 mg))).
(* generates a list of output connectors of vertices (p,1), (p,2), ..., (p,n).
   If some of these output connectors doe not exist, the function returns None. *)
destruct n as [|n'].
exact (Some [::]).
destruct (list_output' mg p n') as [lst|].
destruct (module_graph_vertex_set_p.find (p,N.of_nat n'.+1) (projT1 mg)) as [elt|] eqn: vertex_found.
destruct (0 < size (output_connectors elt)) eqn: has_connectors.
assert (number_correct: output_connector_number_correct (projT1 mg) ((p, N.of_nat n'.+1), 0))
       by (rewrite /output_connector_number_correct vertex_found ; exact has_connectors).
exact (Some (rcons lst (exist (output_connector_number_correct (projT1 mg)) ((p,N.of_nat n'.+1),0) number_correct))).
exact None.
exact None.
exact None.
Defined.

Fixpoint list_output {mg : module_graph} (p : var) (n : nat) : option (seq (output_connectors_of_module_graph (projT1 mg))) :=
(* generates a list of output connectors of vertices (p,1), (p,2), ..., (p,n)
   If some of these output connectors do not exist, the function returns None.
   This definition is based on "Print list_output'.", with a few simplifications. *)
  match n with
  | 0 => Some [::]
  | S n' =>
      let V := projT1 mg in
      let vx_id := (p, N.of_nat n) in
      match list_output p n', module_graph_vertex_set_p.find vx_id V as o
            return module_graph_vertex_set_p.find vx_id V = o ->
                   option (seq (output_connectors_of_module_graph V)) with
      | Some lst, Some vx_typ =>
          fun vertex_found : module_graph_vertex_set_p.find vx_id V = Some vx_typ
          => (if 0 < size (output_connectors vx_typ) as b
                   return 0 < size (output_connectors vx_typ) = b ->
                          option (seq (output_connectors_of_module_graph V))
              then fun has_connectors : 0 < size (output_connectors vx_typ)
                   => let number_correct: output_connector_number_correct V (vx_id, 0) :=
                          eq_ind_r (x := Some vx_typ) (fun t : option vertex_type
                                                       => if t is Some vx_typ then 0 < size (output_connectors vx_typ)
                                                                              else False
                                                      ) has_connectors vertex_found
                      in Some (rcons lst (exist (output_connector_number_correct V) (vx_id, 0) number_correct))
              else fun _ => None
             ) Logic.eq_refl
      | _, _ => fun _ => None
      end Logic.eq_refl
  end.

Fixpoint select_list_rhs_ffield {mg : module_graph} (lst : list (output_connectors_of_module_graph mg)) (ff : ffield) (v : var) :
      option (list (output_connectors_of_module_graph mg) * ftype) :=
(* selects from list lst, which corresponds to type ff, the part for field v *)
match ff with
| Fflips v0 Nflips ft ff' => let len := size_of_ftype ft in
                             if v == v0 then Some (take len lst, ft)
                                        else select_list_rhs_ffield mg (drop len lst) v ff'
| _ => None
end.

Fixpoint list_rhs_ref {mg : module_graph} (e : href) (tmap: ...) : option (list (output_connectors_of_module_graph mg) * ftype) :=
(* generates a list of output connectors and a type corresponding to reference e,
   if e has a passive type *)
match e with
| Eid (p, 0) => match find p tmap with
                | Some ft => match list_output mg p (size_of_ftype ft) with
                             | Some lst => (lst, ft)
                             | _ => None
                             end
                | _ => None
                end
| Esubfield e' v => match list_rhs_ref e' mg tmap with
                    | Some (lst, Btyp ff) => select_list_rhs_ffield mg lst ff v
                    | _ => None
                    end
| Esubindex e' n => match list_rhs_ref e' mg tmap with
                    | Some (lst, Atyp t' m) => if n < m then let len := size_of_ftype t' in
                                                             Some (take len (drop (n * len) lst))
                                                        else None
                    | _ => None
                    end
| _ => None
end.

Fixpoint list_rhs_expr (e : hfexpr) (vmap : module_graph_vertex_set_p.env) (cs : list output_connectors) (ts : list fgtyp_explicit) (n : N) : list output_connectors * list fgtyp_explicit * G * N :=
   match e with
   | Econst t bs => let arith_typ := match t with
                                    | Fsint n => Fsint_a n 
                                    | Fuint n => Fuint_a n 
                                    | Freset 
                                    | Fasyncreset 
                                    | Fclock => Fuint_a 1
                                    | Fsint_implicit _ => Fsint_a (size bs)
                                    | Fuint_implicit _ => Fuint_a (size bs)
                                    end in
                    let nv := Constant arith_typ in 
                    let nvmap := module_graph_vertex_set_p.add (n,N0) nv vmap in
                    (output_connectors_name, output_connectors nv, (nvmap * connection_tree), (N.add n N1))
   | Eref ref => list_rhs_ref mg ref tmap
   | Ecast c e => let eotl := e 的 output_connectors 的typelist in 
                  let eonl := e 的 output_connectors 的namelist in 
                  let nv := add_vertex_cast c eotl vmap in
                  let nvmap := module_graph_vertex_set_p.add (v, N0) nv vmap in
                  let ncncttree := eonl 连接到 (n,0) in
                  let nconstraint := eotl 对应 (input_connectors nv) in
                  ((n,0)的output_connectors_name, output_connectors nv, (nvmap, ncncttree), (N.add n N1))
   | Eprim_unop u e => 同上 add_vertex_unop

   | Eprim_binop b e1 e2 =>let eotl1 := e1 的 output_connectors 的typelist in 
                           let eonl1 := e1 的 output_connectors 的namelist in 
                           let eotl2 := e2 的 output_connectors 的typelist in 
                           let eonl2 := e2 的 output_connectors 的namelist in 
                           let nv := add_vertex_binop b eotl1 eotl2 vmap in

                           let nvmap := module_graph_vertex_set_p.add (v, N0) nv vmap in
                           let ncncttree := eonl1\eonl2 连接到 (n,0) in
                           let nconstraint := eotl1\eotl2 对应 (input_connectors nv) in
                           ((n,0)的output_connectors_name, output_connectors nv, (nvmap, ncncttree), (N.add n N1))

   | Emux e1 e2 e3 => let (eotl1, eonl1, g1, n1) := list_rhs_expr e1 vmap cs ts n in
                      let (eotl2, eonl2, g2, n2) := list_rhs_expr e2 g2.vmap cs ts n1 in
                      let (eotl3, eonl3, g3, n3) := list_rhs_expr e3 g3.vmap cs ts n3 in
                      let nv := add_vertex_mux eotl1 eotl2 eotl3 vmap in (* 是list *)

                      let nvmap := module_graph_vertex_set_p.add (v, N0) nv vmap in
                           let ncncttree := eonl1\eonl2 连接到 (n,0) in
                           let nconstraint := eotl1\eotl2 对应 (input_connectors nv) in
                           ((n,0)的output_connectors_name, output_connectors nv, (nvmap, ncncttree), (N.add n N1))

   end.

Fixpoint trans_stmt (s : hfstmt) (G : module_graph) : module_graph := 
   match s with
   (* declaration like ports *)
   | Sreg (v, _) r => let vtl := vtype_list (type r) nil in
                      add_vertex_reg v 1 vtl vmap
   | Swire (v, _) t =>
   
   | Smem v m (* TBD *)
   | Sinst v1 v2 (* TBD *)
   | Sskip => vmap

   | Sinvalid (v, _) =>
   | Snode (v, _) e => 
   | Sfcnct (v, _) e =>
   
   | Swhen c s1 s2 =>
   end
with trans_stmts (ss : hfstmt_seq) (G : module_graph) : module_graph := 
   match ss with
   | Qnil =>
   | Qcons s st => 
   end.
(* For example, if a connect statement i <= e is added to FIRRTL program P,
then the module graph of P should be extended by a calculation of e
and the connection (output of e) ---> (input of i). *)

(* Keyin, please start with this... *)



(* Idea for semantics relation: the final semantic relation, Sem (F : hfmodule) (G: module_graph),
is defined using an auxiliary relation Sem_frag (G_old : module_graph) (ss : hfstmt_seq) (G_new : module_graph),
with the meaning: If ss is the final fragment of the statement sequence of a module,
then G_old can be transformed into G_new by ss.

It further uses an auxiliary relation Sem_port (pp : seq hfport) (G : module_graph),
that translates the ports of a module to graph elements. *)

Fixpoint remove_t (V : module_graph_vertex_set_p.env) (var : nat) (cnt : nat) : module_graph_vertex_set_p.env :=
   (* remove (var, 0), (var, 1), ..., (var, cnt-1) from the vertex set V *)
   match cnt with
   | 0 => V
   | S cnt' => remove_t (module_graph_vertex_set_p.remove (N.of_nat var, N.of_nat cnt') V) var cnt'
   end.

Fixpoint multi_conjunction_check (n : nat) (f : nat -> bool) : bool :=
   (* returns true if f 0 && f 1 && ... && f (n-1) holds *)
   match n with
   | 0 => true
   | S n' => f n' && multi_conjunction_check n' f
   end.

Fixpoint Sem_inport (t : ftype) (var : nat) (offset : nat) (V : module_graph_vertex_set_p.env) : bool :=
   (* The predicate returns true if the keys (var, offset), (var, offset + 1), (var, offset + 2), ...
      in map V contain type-correct inports or outports corresponding to type t
      (Non-flipped fields are in-ports, flipped fields are out-ports). *)
   match t with
   | Gtyp t' => match module_graph_vertex_set_p.find (N.of_nat var, N.of_nat offset) V with
                | Some (InPort it) => it == t'
                | _ => false
                end
   | Atyp t' n => multi_conjunction_check n (fun i : nat => Sem_inport t' var (offset + (i * size_of_ftype t')) V)
   | Btyp ff => Sem_inport_fields ff var offset V
   end
with Sem_inport_fields (ff : ffield) (var : nat) (offset : nat) (V : module_graph_vertex_set_p.env) : bool :=
   match ff with
   | Fnil => true
   | Fflips _ Nflip   t' ff' =>    Sem_inport t' var offset V
                                && Sem_inport_fields ff' var (offset + size_of_ftype t') V
   | Fflips _ Flipped t' ff' =>    Sem_outport t' var offset V
                                && Sem_inport_fields ff' var (offset + size_of_ftype t') V
   end
with Sem_outport (t : ftype) (var : nat) (offset : nat) (V : module_graph_vertex_set_p.env) : bool :=
   (* The predicate returns true if the keys (var, offset), (var, offset + 1), (var, offset + 2), ...
      in map V contain type-correct inports or outports corresponding to type t
      (Non-flipped fields are out-ports, flipped fields are in-ports). *)
   match t with
   | Gtyp t' => match module_graph_vertex_set_p.find (N.of_nat var, N.of_nat offset) V with
                | Some (OutPort it) => it == t'
                | _ => false
                end
   | Atyp t' n => multi_conjunction_check n (fun i : nat => Sem_outport t' var (offset + (i * size_of_ftype t')) V)
   | Btyp ff => Sem_outport_fields ff var offset V
   end
with Sem_outport_fields (ff : ffield) (var : nat) (offset : nat) (V : module_graph_vertex_set_p.env) : bool :=
   match ff with
   | Fnil => true
   | Fflips _ Nflip   t' ff' =>    Sem_outport t' var offset V
                                && Sem_outport_fields ff' var (offset + size_of_ftype t') V
   | Fflips _ Flipped t' ff' =>    Sem_inport t' var offset V
                                && Sem_outport_fields ff' var (offset + size_of_ftype t') V
   end.

Fixpoint Sem_port (pp : list (hfport VarOrder.T)) (V : module_graph_vertex_set_p.env) : bool :=
(* The predicate returns true if the vertex set V conforms to the sequence of ports pp. *)
   match pp with
   | [::] => module_graph_vertex_set_p.is_empty V
   | (Finput  var t) :: pp' => (* exists V' : module_graph_vertex_set_p.env,
                                              Sem_port pp' V' && some condition on the difference between V' and V *)
                                  Sem_port pp' (remove_t V var (size_of_ftype t))
                               && Sem_inport t var 0 V
   | (Foutput var t) :: pp' =>    Sem_port pp' (remove_t V var (size_of_ftype t))
                               && Sem_outport t var 0 V
   end.

Fixpoint Sem_frag (G_old : module_graph) (ss : hfstmt_seq VarOrder.T) (G_new : module_graph) : Prop :=
   (* ss is the final fragment of the statements of some module.
      The predicate returns True if G_new can be constructed from G_old by applying ss. *)
   match ss with
   | Qnil => G_old = G_new (* module_graph_vertex_set_p.equal vertex_type_eqn (projT1 G_old) (projT1 G_new) && (projT2 G_old and projT2 G_new correspond to each other as well) *)
   | Qcons s ss' => exists G' : module_graph, Sem_frag_stmt G_old s G' /\ Sem_frag G' ss' G_new
   end
with Sem_frag_stmt (G_old : module_graph) (s : hfstmt VarOrder.T) (G_new : module_graph) : Prop :=
   (* The predicate returns True if G_new can be constructed from G_old by applying s. *)
   match s with
   | Sskip => G_old = G_new
   | Swire var t => False (* G_new contains one vertex more than G_old;
                             the connection trees are the same,
                             except that the input connectors of the new wire are not connected. *)
   | Sreg var reg => False
   | Smem var mem => False
   | Sinst var1 var2 => False
   | Snode var expr => False
   | Sfcnct ref expr => False
                        (* The vertices of G_new extend the vertices of G_old by components needed by expr.
                           The connection trees extend the connection trees of G_old as needed by expr, except that
                           G_new contains a connection tree that flows from the output connector of expr to the input connector of ref.
                           If the types do not match, then the relation is False. (FresetWire <= FclockWire)
                           If ref has an implicit width, then the relation only holds if width(ref) >= width(expr). *)
   | Sinvalid ref => (* The vertices are the same;
                        the connection trees are almost the same, except that
                        G_new contains a connection tree "Invalidated" for every ground element of ref. *)
                     exists vertices_equal : module_graph_vertex_set_p.Equal (projT1 G_old) (projT1 G_new),
                        forall ic : input_connectors_of_module_graph (projT1 G_old),
                           match ic with
                           exist (v, n) p => (projT2 G_old) ic =
                                             (projT2 G_new) (exist (fun (x : input_connectors_of_module_graph (projT1 G_new) : if module_graph_vertex_set_p.find (fst x) (projT1 G_new) is Some elt
                                                                                         then snd x < size (input_connectors elt)
                                                                                         else False => ... p ... vertices_equal ...) (v, n) I)
                           end
   | Swhen cond ss_true ss_false => False
   end.

Fixpoint Sem (F : hfmodule) (G : module_graph) : Prop :=
(* The predicate returns True if G conforms to F.
   (If F has errors, there is no such G.)
   (If F has implicit width components, then there are many such Gs.) *)
   match F with
   | FInMod n pp ss => exists V : module_graph_vertex_set_p.env,
         Sem_port pp V /\ Sem_frag (existT module_graph_connection_trees V
                                           (fun (v : input_connectors_of_module_graph V) => Not_connected V))
                                   ss G
   | FExMod _ _ _ => False
   end.

Theorem InferWidths_correct :
(* Proves that InferWidth_fun preserves the semantics *)
   forall (F : hfmodule) (G : module_graph),
      match InferWidths_fun F with
      | OK F' => Sem F' G -> Sem F G (* implication is necessary because F may allow more graphs than F' *)
                 (* Additionally, we might require:
                    /\ ((exists G1, Sem F G1) -> exists G2, Sem F' G2)
                    /\ F' does not contain unspecified widths *)
      | Error _ => True
      end.

Theorem ExpandConnect_correct :
(* Proves that ExpandConnect_fun preserves the semantics *)
   forall (F : hfmodule) (G : module_graph),
      F does not contain unspecified widths ->
      match ExpandConnect_fun F with
      | OK F' => Sem F' G <-> Sem F G (* equivalence is ok because F does not contain unspecified widths *)
                 (* Additionally, we might require:
                    /\ F' does not contain aggregate types/connections *)
      | Error _ => True
      end.

(* If F allows multiple module graphs G, then it may happen that F' allows fewer module graphs.
   However, as the theorem requires that F does not contain unspecified widths, there should be only one conforming module graph,
   and so the equivalence is ok. *)
