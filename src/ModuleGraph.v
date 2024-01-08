From Coq Require Import ZArith (* for Nat.eq_dec *).
From simplssrlib Require Import SsrOrder FMaps Var ZAriths.
From nbits Require Import NBits.
From firrtl Require Import Env Firrtl HiEnv HiFirrtl. (* for hfmodule and its parts *)
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq fintype.

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
   
Definition arithmetic_to_fgtyp (H: arithmetic_data_type) : fgtyp := let (x, _) := H in x.

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
   InPort : fgtyp -> vertex_type | (* main module only at present *)
   Constant : arithmetic_data_type (* While a constant can have an implicit width, this width can immediately
                                      be calculated, based on the number of bits in the value; so it is not
                                      necessary to allow Fsint_implicit or Fuint_implicit here. *) ->
              bits (* value of the constant *) -> vertex_type |
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
   Invalid : fgtyp_explicit (* unknown *) -> vertex_type | (* TODO: Delete this? *)
   (*Reference : fgtyp -> vertex_type |*)
   
   Register : fgtyp -> vertex_type | (* Register that is not reset *)
   RegisterReset : fgtyp -> bool -> vertex_type | (* Register with reset input. The boolean is true if it is Fasyncreset. *)
   Wire : fgtyp -> vertex_type |
   (*memory : ?
   inst : ?*)
   Node : fgtyp -> vertex_type |

   Mux : fgtyp_explicit (* data type of the input connectors *) -> vertex_type.

(* equality of vertex_type is decidable *)
Lemma vertex_type_eq_dec : forall {x y : vertex_type}, {x = y} + {x <> y}.
Proof.  decide equality ;
        try apply fgtyp_eq_dec ;
        try apply fgtyp_explicit_eq_dec ;
        try apply arithmetic_data_type_eq_dec ;
        try apply Nat.eq_dec ;
        decide equality ; decide equality.
Qed.

Definition vertex_type_eqn (x y : vertex_type) : bool :=
match x, y with
| OutPort i, OutPort j
| InPort i, InPort j => i == j

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
| RegisterReset a r1, RegisterReset b r2 => (a == b) && (r1 == r2)
| Mux o, Mux w => o == w
| Constant n1 a, Constant n2 b
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
  + 39:
    destruct (b == b0) eqn: Hb ;
    try (rewrite andbF ; apply ReflectF ; exact H) ;
    move /eqP : Hb => Hb ; rewrite Hb andbT ; rewrite Hb in H ; clear Hb.
  + 1, 38, 39, 40, 41:
    assert (f <> f0) by (contradict H ; rewrite H ; reflexivity) ;
    move /eqP : H0 => H0 ; apply negbTE in H0 ;
    rewrite H0 ; apply ReflectF ; exact H.
  + 1, 3, 4, 5, 6, 36, 37:
    assert (f <> f0) by (contradict H ; rewrite H ; reflexivity) ;
    move /eqP : H0 => H0 ; apply negbTE in H0 ;
    rewrite H0 ; apply ReflectF ; exact H.
  + destruct (b == b0) eqn: Hb ;
    try (rewrite andFb ; apply ReflectF ; exact H) ;
    move /eqP : Hb => Hb ; rewrite Hb andTb ; rewrite Hb in H ; clear Hb.
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
   | Register it => [:: it; Fclock]
   | RegisterReset it true => [:: it; Fclock; Fasyncreset; it]
   | RegisterReset it false => [:: it; Fclock; Fuint 1; it]
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
   | Binop_mul (exist _ p) _
   | Binop_cat (exist _ p) _
   | Binop_rem (exist _ p) _ => False_rect (seq fgtyp) p
   | Binop_dshl (exist it _) n2
   | Binop_dshr (exist it _) n2 => [:: it; (Fuint n2)]

   | Mux (exist it _) => [:: Fuint 1 ; it ; it]
   end.

Definition output_connectors (v : vertex_type) : seq fgtyp_explicit :=
(* a list of types of the output connectors of a vertex of type v *)
   match v with
   | OutPort _ => [::] (* An OutPort has no output connector because the data is sent to somewhere outside the module *)
   | InPort (Fsint_implicit w) => [:: Fsint_exp w]
   | InPort (Fuint_implicit w) => [:: Fuint_exp w]
   | InPort it => [:: exist not_implicit_width it I] (* convert to fgtyp_explicit *)
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
   | Register (Fuint w) | Register (Fuint_implicit w)
   | RegisterReset (Fuint w) _ | RegisterReset (Fuint_implicit w) _ => [:: Fuint_exp w]
   | Register (Fsint w) | Register (Fsint_implicit w)
   | RegisterReset (Fsint w) _ | RegisterReset (Fsint_implicit w) _ => [:: Fsint_exp w]
   | Register Fclock | RegisterReset Fclock _ => [:: Fclock_exp]
   | Register Freset | RegisterReset Freset _ => [:: Freset_exp]
   | Register Fasyncreset | RegisterReset Fasyncreset _ => [:: Fasyncreset_exp]
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

(* type transform functions *)
(* transform a explicit data type to a with_implicit data type *)
Definition data_type_out2in (dt : fgtyp_explicit) : fgtyp :=
   match dt with
   | exist t _ => t
   end.

(* transform a explicit data type to a arithmetic data type, for arithmetic only operations *)
Definition data_type_out2arith (dt : fgtyp_explicit) : option arithmetic_data_type :=
   match dt with
   | exist (Fsint w) _ => Some (Fsint_a w)
   | exist (Fuint w) _ => Some (Fuint_a w)
   | _ => None
   end.

(* transform a with_implicit data type to a arithmetic data type, for const *)
Definition data_type_in2arith (dt : fgtyp) (bs : bits) : option arithmetic_data_type :=
   match dt with
   | Fsint w => Some (Fsint_a w)
   | Fuint w => Some (Fuint_a w)
   | Fsint_implicit _ => Some (Fsint_a (size bs))
   | Fuint_implicit _ => Some (Fuint_a (size bs))
   | _ => None
   end.

(* transform an arithmetic data type to a ftype *)
Definition data_type_arith2ftype (dt : arithmetic_data_type) : ftype :=
   match dt with
   | exist (Fsint w) _ => Gtyp (Fsint w)
   | exist (Fuint w) _ => Gtyp (Fuint w)
   | exist _ p => False_rect ftype p
   end.

(* transform an explicit data type list to a ftype, for expr. output_connector of a vertex return with a list of fgtyp_explicit *)
Definition data_type_out2ftype (dl : list fgtyp_explicit) : option ftype_explicit :=
   match dl with
   | [:: (exist t p)] => Some (exist ftype_not_implicit_width (Gtyp t) p)
   | _ => None
   end.

(* length of an explicit data type, used to build a binop vertex. *)
Definition len_output_data_type (dt : fgtyp_explicit) : nat :=
   match dt with
   | exist (Fsint w) _ => w
   | exist (Fuint w) _ => w
   | exist (Freset) _
   | exist (Fasyncreset) _
   | exist (Fclock) _ => 1
   | exist _ p => False_rect nat p
   end.

(* length of an arithmetic data type, used for build a binop vertex. *)
Definition len_arithmetic_data_type (dt : arithmetic_data_type) : nat :=
   match dt with
   | exist (Fsint w) _ => w
   | exist (Fuint w) _ => w
   | exist _ p => False_rect nat p
   end.

(* return true if two arithmetic type have the same ground type, used for type checking in binop operations.
   Note that this function does not compare the width of the types. *)
Definition typeq_arithmetic_data_type (dt1 : arithmetic_data_type) (dt2 : arithmetic_data_type) : bool :=
   match dt1, dt2 with
   | exist (Fsint _) _, exist (Fsint _) _ 
   | exist (Fuint _) _, exist (Fuint _) _ => true
   | _, _ => false
   end.

(* unfold aggr_type functions *)
Fixpoint list_repeat_fn {T : Type} (f : T -> T) (n : nat) (l : T) : T :=
   (* Applies function f n times to list l *)
   (* calculates f (f (...(f l)...)), i.e. n : nat applications of f : list ftype -> list ftype to l. *)
   match n with
   | 0 => l
   | S m => list_repeat_fn f m (f l)
   end.

Fixpoint list_repeat' {T : Type} (n : positive) (l : seq T) : seq T :=
   (* creates a list that contains n copies of l *)
   match n with
   | xH => l
   | xO n' => list_repeat' n' (l ++ l)
   | xI n' => l ++ list_repeat' n' (l ++ l)
   end.

Definition list_repeat {T : Type} (n : nat) (l : seq T) : seq T :=
   match N.of_nat n with
   | N0 => [::]
   | Npos p => list_repeat' p l
   end.

(*Lemma list_repeat_size :  *)
Fixpoint vtype_list (ft : ftype) (l : list fgtyp) (tlist : list fgtyp) : Prop :=
   (* is true iff tlist is the list l, with the ground type elements of type ft appended.
      For ground-type elements that are uninferred resets or implicit-width components,
      vtype_list also gives a possible guess. *)
   match ft with
   | Gtyp Freset => (tlist == rcons l (Fuint 1)) || (tlist == rcons l Fasyncreset)
   | Gtyp (Fuint_implicit _) =>
        if last Fclock tlist is Fuint_implicit w then tlist == rcons l (Fuint_implicit w)
                                                else false
   | Gtyp (Fsint_implicit _) =>
        if last Fclock tlist is Fsint_implicit w then tlist == rcons l (Fsint_implicit w)
                                                else false
   | Gtyp t => tlist == rcons l t
   | Atyp t n =>
        let difflist := drop (size l) tlist in
        let size_t := (size difflist) / n in
        let tlist' := take size_t difflist in
        vtype_list t [::] tlist' /\ (tlist == l ++ list_repeat n tlist')
   | Btyp b => vtype_list_btyp b l tlist
   end
with vtype_list_btyp (b : ffield) (l : list fgtyp) (tlist : list fgtyp) : Prop :=
   match b with
   | Fnil => tlist == l
   | Fflips v fl t fs => (exists tlist' : list fgtyp, vtype_list t l tlist' /\ vtype_list_btyp fs tlist' tlist)
   end.

Fixpoint num_ref (ft : ftype) : nat :=
   match ft with
   | Gtyp _ => 1
   | Atyp atyp n => (num_ref atyp) * n + 1
   | Btyp ff => num_ff ff + 1
   end
with num_ff (ff : ffield) : nat :=
   match ff with
   | Fnil => 0
   | Fflips _ _ ft ff' => (num_ref ft) + num_ff ff'
end.

Compute (num_ref (Btyp (Fflips (1%num) Nflip (Atyp (Gtyp (Fuint_implicit 0)) 2) (Fflips (1%num) Nflip (Atyp (Gtyp (Fuint_implicit 0)) 2) Fnil)))).

(*Fixpoint vtype_list (ft : ftype_explicit) (l : list fgtyp_explicit) : list fgtyp_explicit :=
   (* appends to list l the ground type elements of type ft *)
   match ft with
   | exist (Gtyp (Fuint n)) _ => rcons l (Fuint_exp n)
   | exist (Gtyp (Fsint n)) _ => rcons l (Fsint_exp n)
   | exist (Gtyp (Fuint_implicit n)) _ => rcons l (Fuint_exp n)
   | exist (Gtyp (Fsint_implicit n)) _ => rcons l (Fsint_exp n)
   | exist (Gtyp Fclock) _ => rcons l Fclock_exp
   | exist (Gtyp Freset) _ => rcons l Freset_exp
   | exist (Gtyp Fasyncreset) _ => rcons l Fasyncreset_exp
   | exist (Atyp t n) _ => list_repeat_fn (vtype_list (make_ftype_explicit t)) n l
   | exist (Btyp b) _ => vtype_list_btyp b l
   end
   with vtype_list_btyp (b : ffield) (l : list fgtyp_explicit) : list fgtyp_explicit :=
   match b with
   | Fnil => l
   | Fflips v fl t fs => vtype_list_btyp fs (vtype_list (make_ftype_explicit t) l)
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

Lemma vtype_list_size : forall (ft : ftype) (lst : seq fgtyp), size (vtype_list ft lst) = size lst + size_of_ftype ft
with vtype_list_btyp_size : forall (ff : ffield) (lst : seq fgtyp), size (vtype_list_btyp ff lst) = size lst + size_of_fields ff.
Proof.
* clear vtype_list_size.
  induction ft.
  + intro ; rewrite /vtype_list /size_of_ftype size_rcons addn1 //.
  + simpl vtype_list ; simpl size_of_ftype.
    induction n.
    - intro ; rewrite /list_repeat_fn muln0 addn0 //.
    - intro ; simpl list_repeat_fn.
      rewrite IHn IHft mulnS addnA //.
  + apply vtype_list_btyp_size.
* clear vtype_list_btyp_size.
  induction ff.
  + intro ; rewrite /vtype_list_btyp /size_of_fields addn0 //.
  + simpl vtype_list_btyp ; simpl size_of_fields.
    intro ; rewrite IHff vtype_list_size addnA //.
Qed.*)

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

(* Module Type VtypFMap <: SsrFMapWithNew.
  Include SsrFMapWithNew.
  (*Definition env : Type := t vertex_type.*)
  (* Parameter def_vtyp : vertex_type. *)
End VtypFMap. *)

Module MakeVtypFMap (V : SsrOrder) (VM : SsrFMapWithNew with Module SE := V)
<: SsrFMapWithNew with Module SE := V.
  Include VM.
  Include FMapLemmas VM.
  Definition env : Type := t vertex_type.
End MakeVtypFMap.

(* vertices set with natural number being the key *)
Module module_graph_vertex_set_s <: SsrFMapWithNew := MakeVtypFMap VarOrder VM. 
Module ProdVarOrder := MakeProdOrderWithDefaultSucc VarOrder VarOrder.
Module PVM <: SsrFMapWithNew := FMaps.MakeTreeMapWithNew ProdVarOrder.
(* vertices set with pair of natural number (n1, n2) being the key *)
Module module_graph_vertex_set_p <: SsrFMapWithNew := MakeVtypFMap ProdVarOrder PVM.

(* type of a tmap, which records the aggr_type for each element *)
Definition ft_pmap := (N*N) -> (option ftype).
Definition ft_find (v : N*N) (m : ft_pmap) := m v.
Definition ft_add (v : N*N) (ft : ftype) (m : ft_pmap) : ft_pmap :=
   fun (y : N*N) => if y == v then (Some ft) else (ft_find y m).
Definition ft_mem (v : N*N) (m : ft_pmap) : bool := if (m v == None) then false else true.
Definition ft_empty : ft_pmap := (fun _ => None).

(* for connection_tree, whose key is (N_pair, N) as input_connector_id 
   here this module produce ProdOrder like ((N,N),N) *)
Module MakeProdOrderWithDefaultSucc2 (O1 O2 : SsrOrderWithDefaultSucc) <: SsrOrderWithDefaultSucc
    with Definition T := prod_eqType O1.T O2.T.
  Module M := MakeProdOrderMinimal O1 O2.
  Module P := MakeSsrOrder M.
  Include P.
  Definition default : t := (O1.default, O2.default).
  Definition succ (x : t) : t := (fst x, O2.succ (snd x)). (* succ of pair ((a,b),c) is ((a,b),c+1) *)
  Lemma ltn_succ (x : t) : ltn x (succ x).
  Proof.
    case: x => x y. rewrite /ltn /succ /=. rewrite /M.ltn /=.
    rewrite O2.ltn_succ andbT eqtype.eq_refl orbT //.
  Qed.
End MakeProdOrderWithDefaultSucc2.

(* can be identifier of a input/output_connector *)
Module PProdVarOrder := MakeProdOrderWithDefaultSucc2 ProdVarOrder VarOrder.

Inductive connection_tree :=
   Invalidated | 
   Leaf : PProdVarOrder.t -> connection_tree |
   Not_connected |
   Choice : PProdVarOrder.t
                    (* the type of cond needs to be Fuint_exp 1 
                       how to check this? *)
            -> connection_tree -> connection_tree -> connection_tree.

Lemma connection_tree_eq_dec : forall {x y : connection_tree}, {x = y} + {x <> y}.
Proof.
induction x.
1,3: destruct y ; try (right ; discriminate) ; left ; reflexivity.
* destruct y ; try (right ; discriminate).
  destruct (t == t0) eqn: Ht.
  1,2: move /eqP: Ht => Ht.
  + rewrite -Ht ; clear Ht t0 ; left; reflexivity.
  + right ; injection ; done.
* destruct y ; try (right ; discriminate).
  destruct (t == t0) eqn: Ht.
  1,2: move /eqP: Ht => Ht.
  + rewrite -Ht ; clear Ht t0.
    specialize IHx1 with (y := y1).
    specialize IHx2 with (y := y2).
    destruct IHx1, IHx2 ; try (right ; injection ; done).
    rewrite -e -e0 ; clear e e0 y1 y2 ; left ; reflexivity.
  + right ; injection ; done.
Qed.
Fixpoint connection_tree_eqn (x y : connection_tree) : bool :=
match x, y with
| Invalidated, Invalidated => true
| Leaf p1, Leaf p2 => p1 == p2
| Not_connected , Not_connected => true
| Choice p1 t1 t2, Choice p2 t3 t4 => (p1 == p2) && (connection_tree_eqn t1 t3) && (connection_tree_eqn t2 t4)
| _, _ => false
end.
Lemma connection_tree_eqP : Equality.axiom connection_tree_eqn.
Proof.
rewrite /Equality.axiom.
induction x.
1,3: destruct y ; try (apply ReflectF ; discriminate) ;
     apply ReflectT ; reflexivity.
* destruct y ; try (apply ReflectF ; discriminate).
  destruct (t == t0) eqn: Ht.
  + rewrite /connection_tree_eqn Ht ; apply ReflectT.
    move /eqP : Ht => Ht ; rewrite -Ht //.
  + rewrite /connection_tree_eqn Ht ; apply ReflectF ; injection.
    move /eqP : Ht => Ht ; done.
* destruct y ; try (apply ReflectF ; discriminate).
  simpl connection_tree_eqn.
  specialize IHx1 with (y := y1).
  specialize IHx2 with (y := y2).
  destruct (t == t0) eqn: Ht.
  + move /eqP : Ht => Ht ; rewrite -Ht.
    destruct (connection_tree_eqn x1 y1) eqn: Hx1.
    - destruct (connection_tree_eqn x2 y2) eqn: Hx2.
      * rewrite andTb ; apply ReflectT.
        replace y1 with x1 by (apply Bool.reflect_iff in IHx1 ; apply IHx1 ; reflexivity).
        replace y2 with x2 by (apply Bool.reflect_iff in IHx2 ; apply IHx2 ; reflexivity).
        reflexivity.
      * rewrite andbF ; apply ReflectF ; injection ; intro.
        apply Bool.reflect_iff in IHx2 ; destruct IHx2 as [IHx2 _].
        discriminate IHx2 ; exact H0.
    - rewrite andbF andFb ; apply ReflectF ; injection ; intros.
      apply Bool.reflect_iff in IHx1 ; destruct IHx1 as [IHx1 _].
      discriminate IHx1 ; exact H1.
  + rewrite andFb ; apply ReflectF ; injection ; intros.
    move /eqP : Ht => Ht ; done.
Qed.
Canonical connection_tree_eqMixin := EqMixin connection_tree_eqP.
Canonical connection_tree_eqType := Eval hnf in EqType connection_tree connection_tree_eqMixin.

Module MakeCnctFMap (V : SsrOrder) (VM : SsrFMapWithNew with Module SE := V)
<: SsrFMapWithNew with Module SE := V.
  Include VM.
  Include FMapLemmas VM.
  Definition env : Type := t connection_tree.
End MakeCnctFMap.

Module PPVM <: SsrFMapWithNew := FMaps.MakeTreeMapWithNew PProdVarOrder.
Module module_graph_connection_trees_p <: SsrFMapWithNew := MakeCnctFMap PProdVarOrder PPVM.

(*Fixpoint ffield2pvar (pv : ProdVarOrder.t) (ff : ffield) (v : var) : option ProdVarOrder.t :=
  (* number the field ff in pv, when a field have aggr_typ, number all ground types in the previous field and then number the next field *)
  match ff with
  | Fflips v0 Nflip ft ff' => if v == v0 then Some (fst pv, N.add (snd pv) 1%num)
                              else ffield2pvar (fst pv, N.add (N.of_nat (size_of_ftype ft)) (N.add (snd pv) 1%num)) ff' v
  | _ => None
  end.

Fixpoint ref2pvar (e : HiFP.href) (tmap : ft_pmap) : option ProdVarOrder.t :=
  match e with
  | Eid p => Some p
  | Esubfield e' v => match ref2pvar e' tmap with
                      | Some pv' => match ft_find pv' tmap with
                                    | Some (Btyp bft) => ffield2pvar pv' bft v 
                                    | _ => None
                                    end
                      | None => None
                      end
  | Esubindex e' n => match ref2pvar e' tmap with
                      | Some pv' => Some (fst pv', N.of_nat ((N.to_nat (snd pv')) + 1 + n))
                      | _ => None
                      end
  | _ => None (* subaccess *)
  end.

Fixpoint ft_find_sub (v : ProdVarOrder.t) (checkt : ftype) (num : N) : option ftype :=
  match checkt with
  | Gtyp gt => if (snd v) == num then Some checkt else None
  | Atyp atyp n => if (snd v) == num then Some checkt
                   else if (((N.to_nat (snd v)) -1 - (N.to_nat num)) >= (num_ref atyp) * n) then None
                   else if (((N.to_nat (snd v)) - 1- (N.to_nat num)) mod (num_ref atyp)) == 0 (* 对应标号是atyp，可能agg *)
                   then Some atyp
                   else (* 继续找atyp中的结构 *)
                    let n' := ((N.to_nat (snd v)) - 1- (N.to_nat num)) / (num_ref atyp) in
                    ft_find_sub v atyp (N.add (N.add num (N.of_nat (n' * (num_ref atyp)))) 1%num)
  | Btyp ff => if (snd v) == num then Some checkt
               else match ft_find_ff v ff num with
              | Some newf => Some newf
              | None => None
              end
  end
with ft_find_ff (v : ProdVarOrder.t) (ff : ffield) (num : N) : option ftype :=
  match ff with
  | Fflips v0 _ ft ff' => if (snd v) == (N.add num 1%num) (* 找到被更新的标号, 所对应的field *)
                              then Some ft
                          else if (snd v) > (N.add num (N.of_nat (num_ref ft))) (* 不在该field中, 找下一个field *)
                              then ft_find_ff v ff' (N.add num (N.of_nat (num_ref ft)))
                           else (* 在field v0中 *)
                              ft_find_sub v ft (N.add num 1%num)
  | _ => None
  end.

Fixpoint ft_set_sub (v : ProdVarOrder.t) (checkt : ftype) (newt : ftype) (num : N) : option ftype :=
  match checkt with
  | Gtyp _ => if (snd v) == num then Some newt else None
  | Atyp atyp n => if (snd v) == num then Some newt
                    else if (((N.to_nat (snd v)) -1 - (N.to_nat num)) >= (num_ref atyp) * n) then None
                    else if (((N.to_nat (snd v)) - 1- (N.to_nat num)) mod (num_ref atyp)) == 0
                      then (* 比较atyp与newt是否match, 取较大的更新Atyp *)
                      Some (Atyp newt n)
                    else (* 继续找atyp中的结构 *)
                      let n' := ((N.to_nat (snd v)) - 1- (N.to_nat num)) / (num_ref atyp) in
                      match ft_set_sub v atyp newt (N.add (N.add num (N.of_nat (n' * (num_ref atyp)))) 1%num) with
                      | Some natyp => Some (Atyp natyp n)
                      | None => None
                      end
  | Btyp ff => if (snd v) == num then Some newt
                else match ft_set_sub_f v ff newt num with
                | Some newf => Some (Btyp newf)
                | None => None
                end
  end
with ft_set_sub_f (v : ProdVarOrder.t) (ff : ffield) (newt : ftype) (num : N) : option ffield :=
  (* changes the (v-num)th field of ff.
     If (v-num) == 1, then the first field is changed from implicit-width to explicit-width.
     If (v-num) == 2, 3, ... 1+size_of_ftype (type of first fieldd), then some subfield of the first field is changed.
     If (v-num) > 1+size_of_ftype (type of first field), then a subsequent field of ff is changed. *)
  match ff with
  | Fflips v0 Nflip ft ff' => if (snd v) == (N.add num 1%num) (* 找到被更新的标号, 所对应的field *)
                              then (* 比较Btyp现有对应位置上的ftype和待更新的newt是否match, 取较大的更新Btyp *)
                                Some (Fflips v0 Nflip newt ff') (* 修改当前field的type, ff'不变 *)
                              else if (snd v) > (N.add num (N.of_nat (num_ref ft))) (* 不在该field中, 找下一个field *)
                                   then match ft_set_sub_f v ff' newt (N.add num (N.of_nat (num_ref ft))) with
                                      | Some newf => Some (Fflips v0 Nflip ft newf)
                                      | None => None
                                      end
                                   else (* 在field v0中 *)
                                   match ft_set_sub v ft newt (N.add num 1%num) with
                                   | Some newt' => Some (Fflips v0 Nflip newt' ff')
                                   | None => None
                                   end
  | _ => None
  end.

Fixpoint list_gref (n : nat) (pv : ProdVarOrder.t) (checkt : ftype) : option (seq ProdVarOrder.t) := 
  match n with
  | 0 => Some nil
  | S m => match list_gref m pv checkt, ft_find_sub (fst pv, N.add (snd pv) (N.of_nat m)) checkt N0 with
          | Some ls, Some (Gtyp _) => Some ((fst pv, N.add (snd pv) (N.of_nat m)) :: ls)
          | Some ls, Some _ => Some ls
          | _, None => None
          | None, _ => None
          end
  end.

(* 有必要check这几个函数功能是否正确 *)
Definition testaty0 := (Atyp (Gtyp (Fuint_implicit 0)) 2).
Definition testaty := (Atyp (Atyp (Gtyp (Fuint 4)) 2) 2).
Definition testbty0 := (Btyp (Fflips (1%num) Nflip (Atyp (Gtyp (Fuint_implicit 0)) 2) (Fflips (1%num) Nflip (Atyp (Gtyp (Fuint_implicit 0)) 2) Fnil))).
Definition testbty := (Btyp (Fflips (1%num) Nflip (Btyp (Fflips (1%num) Nflip (Gtyp (Fuint_implicit 0)) (Fflips (1%num) Nflip (Atyp (Gtyp (Fuint_implicit 0)) 2) Fnil))) (Fflips (1%num) Nflip (Atyp (Gtyp (Fuint_implicit 0)) 2) Fnil))).
(* Compute (ft_find_upper (N0, 9%num) testbty N0 nil). *)
(* Compute (ft_find_sub (N0, 9%num) testbty N0). *)
(* Compute (ft_set_sub (N0, 3%num) testbty testaty0 N0). *)
(* Compute (list_gref (num_ref testbty) (N0,N0) testbty). *)
*)

Fixpoint tmap_type_size (t : ftype) : N :=
(* calculates how many entries in tmap.env would be created/affected by a variable of type t *)
   match t with
   | Gtyp _ => 1
   | Atyp t _ => tmap_type_size t (* only one entry is needed for the array *)
   | Btyp ff => tmap_type_size_fields ff
   end
   with tmap_type_size_fields (ff : ffield) : N :=
   match ff with
   | Fnil => 0
   | Fflips _ _ ft ff' => tmap_type_size ft + tmap_type_size_fields ff'
   end.

Fixpoint ft_set_sub (checkt : ftype) (newt : fgtyp) (num : N) : option ftype :=
  match checkt with
  | Gtyp _ => if num == N0 then Some (Gtyp newt) else None
  | Atyp atyp n => match ft_set_sub atyp newt num with
                      | Some natyp => Some (Atyp natyp n)
                      | None => None
                      end
  | Btyp ff => if num >= (tmap_type_size_fields) ff then None else
                match ft_set_sub_f ff newt num with
                | Some newf => Some (Btyp newf)
                | None => None
                end
  end
with ft_set_sub_f (ff : ffield) (newt : fgtyp) (num : N) : option ffield :=
  match ff with
  | Fflips v0 fl ft ff' => if num >= N.of_nat (tmap_type_size ft) (* 不在该field中, 找下一个field *)
                            then match ft_set_sub_f ff' newt (N.sub num (N.of_nat (tmap_type_size ft))) with
                                | Some newf => Some (Fflips v0 fl ft newf)
                                | None => None
                                end
                          else (* 在field v0中 *)
                            match ft_set_sub ft newt num with
                            | Some newt' => Some (Fflips v0 fl newt' ff')
                            | None => None
                            end
  | _ => None
  end.

  (* 以下函数都是只考虑gtyp的版本，并且array只考虑一个元素 *)
Fixpoint ft_find_sub (checkt : ftype) (num : N) : option fgtyp :=
  match checkt with
  | Gtyp gt => if num == N0 then Some gt else None
  | Atyp atyp n => ft_find_sub atyp num
  | Btyp ff => if num >= (tmap_type_size_fields) ff then None else ft_find_ff ff num 
  end
with ft_find_ff (ff : ffield) (num : N) : option fgtyp :=
  match ff with
  | Fflips v0 _ ft ff' => if num >= (N.of_nat (tmap_type_size ft)) (* 不在该field中, 找下一个field *)
                              then ft_find_ff ff' (N.sub num (N.of_nat (tmap_type_size ft)))
                           else (* 在field v0中 *)
                              ft_find_sub ft num
  | _ => None
  end.

Fixpoint ft_check_flip (checkt : ftype) (num : N) (fl : bool) : option bool :=
  match checkt with
  | Gtyp gt => if num == N0 then Some fl else None
  | Atyp atyp n => ft_check_flip atyp num fl
  | Btyp ff => if num >= (tmap_type_size_fields) ff then None else ft_check_flip_f ff num fl
  end
with ft_check_flip_f (ff : ffield) (num : N) (fl : bool) : option bool :=
  match ff with
  | Fflips v0 Flipped ft ff' => if num >= (N.of_nat (tmap_type_size ft)) (* 不在该field中, 找下一个field *)
                                  then ft_check_flip_f ff' (N.sub num (N.of_nat (tmap_type_size ft))) fl
                              else (* 在field v0中 *)
                                  ft_check_flip ft num (~~fl)
  | Fflips v0 Nflip ft ff' => if num >= (N.of_nat (tmap_type_size ft)) (* 不在该field中, 找下一个field *)
                                  then ft_check_flip_f ff' (N.sub num (N.of_nat (tmap_type_size ft))) fl
                              else (* 在field v0中 *)
                                  ft_check_flip ft num fl
  | _ => None
  end.

(* 有必要check这几个函数功能是否正确 *)
Definition testaty0 := (Atyp (Gtyp (Fuint_implicit 0)) 2).
Definition testaty := (Atyp (Atyp (Gtyp (Fuint 4)) 2) 2).
Definition testbty0 := (Btyp (Fflips (1%num) Nflip (Atyp (Gtyp (Fuint_implicit 0)) 2) (Fflips (1%num) Nflip (Atyp (Gtyp (Fuint_implicit 1)) 2) Fnil))).
Definition testbty := (Btyp (Fflips (1%num) Flipped (Btyp (Fflips (1%num) Nflip (Gtyp (Fuint_implicit 0)) (Fflips (1%num) Flipped (Atyp (Gtyp (Fuint_implicit 1)) 2) Fnil))) (Fflips (1%num) Nflip (Atyp (Gtyp (Fuint_implicit 2)) 2) Fnil))).
Definition testgt := (Fuint 4).
Compute (tmap_type_size testaty). 
Compute (ft_set_sub testbty testgt 3%num).
Compute (ft_find_sub testbty 2%num).
Compute (ft_check_flip testbty 2%num false).

(* helper functions for producing new vertices *)
(* return the new vertex and type of the cast expression if a correct ftype is given *)
Definition add_vertex_cast (c : ucast) (ft : ftype_explicit) : option vertex_type :=
   let vt := match ft with
            | exist (Gtyp (Fuint n)) _ => Some (Fuint_exp n)
            | exist (Gtyp (Fsint n)) _ => Some (Fsint_exp n)
            | exist (Gtyp Fclock) _ => Some (Fclock_exp)
            | exist (Gtyp Freset) _ => Some (Freset_exp)
            | exist (Gtyp Fasyncreset) _ => Some (Fasyncreset_exp)
            | _ => None
            end in
   match vt with 
   | Some vty => match c with
               | AsUInt => Some (Cast_UInt vty)
               | AsSInt => Some (Cast_SInt vty)
               | AsClock => Some (Cast_Clock vty)
               | AsAsync => Some (Cast_Async vty)
               | AsReset => None (* spec 中没有了? *)
               end
   | None => None
   end.

(* return the new unop vertex if the ftype is given correctly *)
Definition add_vertex_unop (u : eunop) (ft : ftype_explicit) : option vertex_type :=
   let vt := match ft with
            | exist (Gtyp (Fuint n)) _ => Some (Fuint_a n)
            | exist (Gtyp (Fsint n)) _ => Some (Fsint_a n)
            | _ => None 
            end in
   match vt with 
   | Some vty => match u with
            | Upad n => Some (Unop_pad n vty)
            | Ushl n => Some (Unop_shl n vty)
            | Ushr n => Some (Unop_shr n vty)
            | Ucvt => Some (Unop_cvt vty)
            | Uneg => Some (Unop_neg vty)
            | Unot => Some (Unop_not vty)
            | Uandr => Some (Unop_andr vty)
            | Uorr => Some (Unop_orr vty)
            | Uxorr => Some (Unop_xorr vty)
            | Uextr hi lo => Some (Unop_bits hi lo vty)
            | Uhead n => Some (Unop_head n vty)
            | Utail n => Some (Unop_tail n vty)
            end
   | None => None 
   end.

(* return the new binop vertex if the ftype is given correctly *)
Definition add_vertex_binop (b : ebinop) (ft0 ft1: ftype_explicit) : option vertex_type :=
   let vt0 := match ft0 with
            | exist (Gtyp (Fuint n)) _ => Some (Fuint_a n)
            | exist (Gtyp (Fsint n)) _ => Some (Fsint_a n)
            | _ => None 
            end in
   let vt1 := match ft1 with
            | exist (Gtyp (Fuint n)) _ => Some (Fuint_a n)
            | exist (Gtyp (Fsint n)) _ => Some (Fsint_a n)
            | _ => None 
            end in
   match vt0, vt1 with 
   | Some vty0, Some vty1 => match b with
                           | Badd => if typeq_arithmetic_data_type vty0 vty1
                                     then if (len_arithmetic_data_type vty0) > (len_arithmetic_data_type vty1)
                                          then Some (Binop_add vty0)
                                          else Some (Binop_add vty1)
                                     else None
                           | Bsub => if typeq_arithmetic_data_type vty0 vty1
                                     then if (len_arithmetic_data_type vty0) > (len_arithmetic_data_type vty1)
                                          then Some (Binop_sub vty0)
                                          else Some (Binop_sub vty1)
                                     else None
                           | Band => if typeq_arithmetic_data_type vty0 vty1
                                     then if (len_arithmetic_data_type vty0) > (len_arithmetic_data_type vty1)
                                          then Some (Binop_and vty0)
                                          else Some (Binop_and vty1)
                                     else None
                           | Bor => if typeq_arithmetic_data_type vty0 vty1
                                     then if (len_arithmetic_data_type vty0) > (len_arithmetic_data_type vty1)
                                          then Some (Binop_or vty0)
                                          else Some (Binop_or vty1)
                                     else None
                           | Bxor => if typeq_arithmetic_data_type vty0 vty1
                                     then if (len_arithmetic_data_type vty0) > (len_arithmetic_data_type vty1)
                                          then Some (Binop_xor vty0)
                                          else Some (Binop_xor vty1)
                                     else None
                           | Bmul => if typeq_arithmetic_data_type vty0 vty1
                                     then Some (Binop_mul vty0 (len_arithmetic_data_type vty1))
                                     else None
                           | Bdiv => if typeq_arithmetic_data_type vty0 vty1
                                     then Some (Binop_div vty0)
                                     else None
                           | Brem => if typeq_arithmetic_data_type vty0 vty1
                                     then Some (Binop_rem vty0 (len_arithmetic_data_type vty1))
                                     else None
                           | Bcat => if typeq_arithmetic_data_type vty0 vty1
                                     then Some (Binop_cat vty0 (len_arithmetic_data_type vty1))
                                     else None
                           | Bdshl => match vty1 with
                                      | exist (Fuint _) _ => Some (Binop_dshl vty0 (len_arithmetic_data_type vty1))
                                      | _ => None
                                      end
                           | Bdshr => match vty1 with
                                      | exist (Fuint _) _ => Some (Binop_dshr vty0 (len_arithmetic_data_type vty1))
                                      | _ => None
                                      end
                           | Bcomp c => if typeq_arithmetic_data_type vty0 vty1
                                       then let vty := if (len_arithmetic_data_type vty0) > (len_arithmetic_data_type vty1)
                                                       then vty0
                                                       else vty1 in match c with
                                                      | Blt => Some (Binop_lt vty)
                                                      | Bleq => Some (Binop_leq vty)
                                                      | Bgt => Some (Binop_gt vty)
                                                      | Bgeq => Some (Binop_geq vty)
                                                      | Beq => Some (Binop_eq vty)
                                                      | Bneq => Some (Binop_neq vty)
                                                      end
                                       else None
                           end
   | _, _ => None
   end.

(*
Fixpoint list_output_p (vmap : module_graph_vertex_set_p.env) (p : var) (n : nat) (ol : option (list PProdVarOrder.t)) : option (list PProdVarOrder.t) :=
(* prepends a list of output connector 0 of vertices (p,1), (p,2), ..., (p,n) to ol
   If some of these output connectors do not exist, the function returns None. *)
  match ol, n with
  | Some onl, 0 => ol
  | Some onl, S n' =>let vx_id := (p, N.of_nat n) in
                     match module_graph_vertex_set_p.find vx_id vmap with
                     | Some _ => list_output_p vmap p n' (Some ((vx_id, N0) :: onl))
                     | _ => None
                     end 
  | None, _ => None
  end.

Fixpoint select_list_lhs_ffield_p (lst : list PProdVarOrder.t) (ff : ffield) (v : var) :
      option (list PProdVarOrder.t * ftype) :=
(* selects from list lst, which corresponds to type ff, the part for field v *)
match ff with
| Fflips v0 Nflip ft ff' => let len := size_of_ftype ft in
                             if v == v0 then Some (take len lst, ft)
                                        else select_list_lhs_ffield_p (drop len lst) ff' v
| _ => None
end.

Fixpoint fillft_vm (ft : ftype) (gl : seq ProdVarOrder.t) (vmap : module_graph_vertex_set_p.env) : option ftype :=
   match gl with
   | nil => Some ft
   | hd :: tl => match module_graph_vertex_set_p.find hd vmap with
               | Some nt => match List.hd_error (input_connectors nt) with
                           | Some gt => match ft_set_sub hd ft (Gtyp gt) N0 with
                                       | Some nft => fillft_vm nft tl vmap
                                       | None => None
                                       end
                           | None => None
                           end
               | None => None
               end
   end.

Definition type_of_ref_vm (vmap : module_graph_vertex_set_p.env) (e : HiFP.href) (tmap : ft_pmap) : option ftype :=
   match ref2pvar e tmap with
   | Some pv => match ft_find (fst pv, N0) tmap with
               | Some checkt => match ft_find_sub pv checkt N0 with
                              | Some ft => match list_gref (num_ref ft) pv ft with
                                          | Some gl => match fillft_vm checkt gl vmap with
                                                      | Some ncheckt => ft_find_sub pv ncheckt N0
                                                      | None => None
                                                      end
                                          | None => None
                                          end
                              | None => None
                              end
               | None => None
               end
   | None => None
   end.

Definition list_lhs_ref_p (vmap : module_graph_vertex_set_p.env) (e : HiFP.href) (tmap : ft_pmap) : option (list PProdVarOrder.t * ftype) :=
   match ref2pvar e tmap with
   | Some pv => match ft_find (fst pv, N0) tmap with
               | Some checkt => match ft_find_sub pv checkt N0 with
                              | Some ft => match list_gref (num_ref ft) pv ft with
                                          | Some gl => match type_of_ref_vm vmap e tmap with
                                                      | Some nt => Some (map (fun v => (v, N0)) gl, nt)
                                                      | None => None
                                                      end
                                          | None => None
                                          end
                              | None => None
                              end
               | None => None
               end
   | None => None
   end.*)

Fixpoint base_ref_fields (base : VarOrder.t * N) (v : VarOrder.t) (ff : ffield) : option (VarOrder.t * N * ftype) :=
(* find field v in ff. If found, return its type as an auxiliary to base_ref. *)
match ff with
| Fnil => None
| Fflips v' _ t' ff' =>
    if v == v' then Some (base, t')
               else base_ref_fields ((fst base), ((snd base) + tmap_type_size t')%num) v ff'
end.

Fixpoint base_ref (ref : HiFP.href) (tmap : CEP.t ftype) : option (VarOrder.t * N * ftype) :=
(* For reference ref, finds the pair (v, n) and the type that corresponds to it.
(v,n) is the first item in the list of variables associated to ref that is affected by it.
This function counts n for tmap, i.e. all arrays are treated as having only one element. *)
match ref with
| Eid v =>
    match CEP.find v tmap with
    | Some t => Some (v, t)
    | None   => None
    end
| Esubfield ref' v' =>
    match base_ref ref' tmap with
    | Some (base, Btyp ff) => base_ref_fields base v' ff
    | _ => None
    end
| Esubindex ref' _
| Esubaccess ref' _ =>
    match base_ref ref' tmap with
    | Some (base, Atyp t' _) => Some (base, t')
    | _ => None
    end
end.

Fixpoint list_lhs_ref_p (pv : ProdVarOrder.t) (n : nat) : list PProdVarOrder.t :=
   match n with 
   | 0 => nil
   | S m => cons (fst pv, N.add (snd pv) (N.of_nat n), N0) (list_lhs_ref_p pv m)
   end.

Fixpoint fillft_vm (n : nat) (ft : ftype) (pv : ProdVarOrder.t) (vmap : module_graph_vertex_set_p.env) : option ftype :=
   match n with
   | 0 => Some ft
   | S m => match module_graph_vertex_set_p.find (fst pv, (N.add (snd pv) (N.of_nat m))) vmap with
            | Some nt => match List.hd_error (input_connectors nt) with
                        | Some gt => match ft_set_sub ft gt (N.of_nat m) with
                                   | Some nft => fillft_vm m nft pv vmap
                                   | None => None
                                   end
                       | None => None
                       end
           | None => None
           end
   end.

(* return the type of mux expression on fgtyps *)
(*Definition fgtyp_mux (x y : fgtyp_explicit) : option fgtyp_explicit :=
    match x, y with
    | exist (Fuint wx) _, exist (Fuint wy) _ => Some (Fuint_exp (Nat.max wx wy))
    | exist (Fsint wx) _, exist (Fsint wy) _ => Some (Fsint_exp (Nat.max wx wy))
    | exist Fclock _, exist Fclock _ => Some Fclock_exp
    | exist Freset _, exist Freset _ => Some Freset_exp
    | exist Fasyncreset _, exist Fasyncreset _ => Some Fasyncreset_exp
    | _, _ => None
    end.
(* return the type of mux expression on ftypes *)
(* HiFirrtl.mux_types' *)
(* The function needs to take apart the ftype_explicit so Coq can guess the decreasing argument *)
Fixpoint ftype_mux' (x : ftype) (px : ftype_not_implicit_width x) (y : ftype) (py : ftype_not_implicit_width y) : option ftype_explicit :=
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
  | Btyp fx, px, Btyp fy, py => ffield_mux' fx px fy py
  | _, _, _, _ => None
  end
with ffield_mux' (f1 : ffield) (p1 : ffield_not_implicit_width f1) (f2 : ffield) (p2 : ffield_not_implicit_width f2) : option ftype_explicit :=
       match f1, p1, f2, p2 with
       | Fnil, _, Fnil, _ => Some (exist ftype_not_implicit_width (Btyp Fnil) I)
       | Fflips v1 Nflip t1 fs1, p1, Fflips v2 Nflip t2 fs2, p2
         => if v1 == v2 then
               match ftype_mux'  t1  (proj1 p1) t2  (proj1 p2),
                     ffield_mux' fs1 (proj2 p1) fs2 (proj2 p2) with
               | Some (exist ft pt), Some (exist (Btyp bf) pf) =>
                   Some (exist ftype_not_implicit_width (Btyp (Fflips v1 Nflip ft bf)) (conj pt pf))
               | _, _ => None
               end
            else None
       | _, _, _, _ => None
       end.

Definition ftype_mux (x : ftype_explicit) (y : ftype_explicit) : option ftype_explicit :=
(* return the type of mux expression on ftypes *)
   ftype_mux' (proj1_sig x) (proj2_sig x) (proj1_sig y) (proj2_sig y).
*)

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

(*
Fixpoint type_of_e_vm (vmap : module_graph_vertex_set_p.env) (e : HiFP.hfexpr) (tmap : ft_pmap) : option ftype_explicit :=
   match e with
   | Econst t bs => match t with
                    | Fuint_implicit w => Some (exist ftype_not_implicit_width (Gtyp (Fuint w)) I)
                    | Fsint_implicit w => Some (exist ftype_not_implicit_width (Gtyp (Fsint w)) I)
                    | t => Some (exist ftype_not_implicit_width (Gtyp t) I)
                    end
   | Eref r => match type_of_ref_vm vmap r tmap with
               | Some t => Some (make_ftype_explicit t)
               | _ => None
               end
   | Ecast AsUInt e1 => match type_of_e_vm vmap e1 tmap with
                         | Some (exist (Gtyp (Fsint w)) _)
                         | Some (exist (Gtyp (Fuint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint w)) I)
                         | Some (exist (Gtyp Fclock) _)
                         | Some (exist (Gtyp Freset) _)
                         | Some (exist (Gtyp Fasyncreset) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint 1)) I)
                         | _ => None
                         end
   | Ecast AsSInt e1 => match type_of_e_vm vmap e1 tmap with
                         | Some (exist (Gtyp (Fsint w)) _)
                         | Some (exist (Gtyp (Fuint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint w)) I)
                         | Some (exist (Gtyp Fclock) _)
                         | Some (exist (Gtyp Freset) _)
                         | Some (exist (Gtyp Fasyncreset) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint 1)) I)
                         | _ => None
                         end
   | Ecast AsClock e1 => match type_of_e_vm vmap e1 tmap with
                         | Some (exist (Gtyp _) _) => Some (exist ftype_not_implicit_width (Gtyp Fclock) I)
                         | _ => None
                         end
   | Ecast AsAsync e1 => match type_of_e_vm vmap e1 tmap with
                         | Some (exist (Gtyp _) _) => Some (exist ftype_not_implicit_width (Gtyp Fasyncreset) I)
                         | _ => None
                         end
   | Eprim_unop (Upad n) e1 => match type_of_e_vm vmap e1 tmap with
                                | Some (exist (Gtyp (Fsint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint (maxn w n))) I)
                                | Some (exist (Gtyp (Fuint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint (maxn w n))) I)
                                | _ => None
                                end
   | Eprim_unop (Ushl n) e1 => match type_of_e_vm vmap e1 tmap with
                                | Some (exist (Gtyp (Fsint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint (w + n))) I)
                                | Some (exist (Gtyp (Fuint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint (w + n))) I)
                                | _ => None
                                end
   | Eprim_unop (Ushr n) e1 => match type_of_e_vm vmap e1 tmap with
                                | Some (exist (Gtyp (Fsint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint (maxn (w - n) 1))) I)
                                | Some (exist (Gtyp (Fuint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint (maxn (w - n) 1))) I)
                                | _ => None
                                end
   | Eprim_unop Ucvt e1 => match type_of_e_vm vmap e1 tmap with
                            | Some (exist (Gtyp (Fsint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint w)) I)
                            | Some (exist (Gtyp (Fuint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint (w + 1))) I)
                            | _ => None
                            end
   | Eprim_unop Uneg e1 => match type_of_e_vm vmap e1 tmap with
                            | Some (exist (Gtyp (Fsint w)) _)
                            | Some (exist (Gtyp (Fuint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint (w + 1))) I)
                            | _ => None
                            end
   | Eprim_unop Unot e1 => match type_of_e_vm vmap e1 tmap with
                            | Some (exist (Gtyp (Fsint w)) _)
                            | Some (exist (Gtyp (Fuint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint w)) I)
                            | _ => None
                            end
   | Eprim_unop (Uextr n1 n2) e1 => match type_of_e_vm vmap e1 tmap with
                                     | Some (exist (Gtyp (Fsint w)) _)
                                     | Some (exist (Gtyp (Fuint w)) _) =>
                                          if (n2 <= n1) && (n1 < w) then Some (exist ftype_not_implicit_width (Gtyp (Fuint (n1 - n2 + 1))) I)
                                                                    else None
                                     | _ => None
                                     end
   | Eprim_unop (Uhead n) e1 => match type_of_e_vm vmap e1 tmap with
                                 | Some (exist (Gtyp (Fsint w)) _)
                                 | Some (exist (Gtyp (Fuint w)) _) =>
                                      if n <= w then Some (exist ftype_not_implicit_width (Gtyp (Fuint n)) I)
                                                else None
                                 | _ => None
                                 end
   | Eprim_unop (Utail n) e1 => match type_of_e_vm vmap e1 tmap with
                                 | Some (exist (Gtyp (Fsint w)) _)
                                 | Some (exist (Gtyp (Fuint w)) _) =>
                                      if n <= w then Some (exist ftype_not_implicit_width (Gtyp (Fuint (w - n))) I)
                                                else None
                                 | _ => None
                                 end
   | Eprim_unop _ e1 => match type_of_e_vm vmap e1 tmap with
                         | Some (exist (Gtyp (Fsint _)) _)
                         | Some (exist (Gtyp (Fuint _)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint 1)) I)
                         | _ => None
                         end
   | Eprim_binop (Bcomp _) e1 e2 => match type_of_e_vm vmap e1 tmap, type_of_e_vm vmap e2 tmap with
                                     | Some (exist (Gtyp (Fsint _)) _), Some (exist (Gtyp (Fsint _)) _)
                                     | Some (exist (Gtyp (Fuint _)) _), Some (exist (Gtyp (Fuint _)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint 1)) I)
                                     | _, _ => None
                                     end
   | Eprim_binop Badd e1 e2
   | Eprim_binop Bsub e1 e2 => match type_of_e_vm vmap e1 tmap, type_of_e_vm vmap e2 tmap with
                                | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint (maxn w1 w2 + 1))) I)
                                | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fsint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint (maxn w1 w2 + 1))) I)
                                | _, _ => None
                                end
   | Eprim_binop Bmul e1 e2 => match type_of_e_vm vmap e1 tmap, type_of_e_vm vmap e2 tmap with
                                | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint (w1 + w2))) I)
                                | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fsint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint (w1 + w2))) I)
                                | _, _ => None
                                end
   | Eprim_binop Bdiv e1 e2  => match type_of_e_vm vmap e1 tmap, type_of_e_vm vmap e2 tmap with
                                 | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint w1)) I)
                                 | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fsint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint (w1 + 1))) I)
                                 | _, _ => None
                                 end
   | Eprim_binop Brem e1 e2 => match type_of_e_vm vmap e1 tmap, type_of_e_vm vmap e2 tmap with
                                 | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint (minn w1 w2))) I)
                                 | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fsint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint (minn w1 w2))) I)
                                 | _, _ => None
                                 end
   | Eprim_binop Bdshl e1 e2 => match type_of_e_vm vmap e1 tmap, type_of_e_vm vmap e2 tmap with
                                 | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint (w1 + 2 ^ w2 - 1))) I)
                                 | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fuint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint (w1 + 2 ^ w2 - 1))) I)
                                 | _, _ => None
                                 end
   | Eprim_binop Bdshr e1 e2 => match type_of_e_vm vmap e1 tmap, type_of_e_vm vmap e2 tmap with
                                 | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint w1)) I)
                                 | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fuint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint w1)) I)
                                 | _, _ => None
                                 end
   | Eprim_binop Bcat e1 e2 => match type_of_e_vm vmap e1 tmap, type_of_e_vm vmap e2 tmap with
                                | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _)
                                | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fsint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint (w1 + w2))) I)
                                | _, _ => None
                                end
   | Eprim_binop Band e1 e2
   | Eprim_binop Bor e1 e2
   | Eprim_binop Bxor e1 e2 => match type_of_e_vm vmap e1 tmap, type_of_e_vm vmap e2 tmap with
                                | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _)
                                | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fsint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint (maxn w1 w2))) I)
                                | _, _ => None
                                end
   | Emux c e1 e2 => match type_of_e_vm vmap c tmap, type_of_e_vm vmap e1 tmap, type_of_e_vm vmap e2 tmap with
                      | Some (exist (Gtyp (Fuint 1)) _), Some t1, Some t2 => ftype_mux t1 t2
                      | _, _, _ => None
                      end
   | Evalidif c e1 => match type_of_e_vm vmap c tmap with
                      | Some (exist (Gtyp (Fuint 1)) _) => type_of_e_vm vmap e1 tmap
                      | _ => None
                      end
   | _ => None (* Some (exist ftype_not_implicit_width (Gtyp (Fuint 0)) I) *)
   end.

Fixpoint list_lhs_ref_p (vmap : module_graph_vertex_set_p.env) (e : HiFP.href) (tmap: ft_pmap) : 
option (list PProdVarOrder.t * ftype) :=
(* generates a list of input connectors and a type corresponding to reference e,
   if e has a passive type *)
match e with
| Eid (p, N0) => match ft_find (p,N0) tmap with
                | Some ft => match list_output_p vmap p (size_of_ftype ft) (Some nil) with
                             | Some lst => Some (lst, ft)
                             | _ => None
                             end
                | _ => None
                end
| Esubfield e' v => match list_lhs_ref_p vmap e' tmap with
                    | Some (lst, Btyp ff) => select_list_lhs_ffield_p lst ff v
                    | _ => None
                    end
| Esubindex e' n => match list_lhs_ref_p vmap e' tmap with
                    | Some (lst, Atyp t' m) => if n < m then let len := size_of_ftype t' in
                                                             Some (take len (drop (n * len) lst), t')
                                                        else None
                    | _ => None
                    end
| _ => None
end.*)


Fixpoint type_of_hfexpr_vm (vmap : module_graph_vertex_set_p.env) (e : HiFP.hfexpr) (tmap : CEP.t ftype) : option ftype :=
   match e with
   | Econst t bs => match t with
                    | Fuint_implicit w => Some (Gtyp (Fuint (size bs)))
                    | Fsint_implicit w => Some (Gtyp (Fsint (size bs)))
                    | t => Some (Gtyp t)
                    end
   | Eref r => match base_ref r tmap with
              | Some (pv, checkt) => fillft_vm (tmap_type_size checkt) checkt pv vmap
              | None => None
              end
   | Ecast AsUInt e1 => match type_of_hfexpr_vm vmap e1 tmap with
                         | Some (Gtyp (Fsint w))
                         | Some (Gtyp (Fuint w)) => Some (Gtyp (Fuint w))
                         | Some (Gtyp Fclock)
                         | Some (Gtyp Freset)
                         | Some (Gtyp Fasyncreset) => Some (Gtyp (Fuint 1))
                         | _ => None
                         end
   | Ecast AsSInt e1 => match type_of_hfexpr_vm vmap e1 tmap with
                         | Some (Gtyp (Fsint w))
                         | Some (Gtyp (Fuint w)) => Some (Gtyp (Fsint w))
                         | Some (Gtyp Fclock)
                         | Some (Gtyp Freset)
                         | Some (Gtyp Fasyncreset) => Some (Gtyp (Fsint 1))
                         | _ => None
                         end
   | Ecast AsClock e1 => match type_of_hfexpr_vm vmap e1 tmap with
                         | Some (Gtyp _) => Some (Gtyp Fclock)
                         | _ => None
                         end
   | Ecast AsAsync e1 => match type_of_hfexpr_vm vmap e1 tmap with
                         | Some (Gtyp _) => Some (Gtyp Fasyncreset)
                         | _ => None
                         end
   | Eprim_unop (Upad n) e1 => match type_of_hfexpr_vm vmap e1 tmap with
                                | Some (Gtyp (Fsint w)) => Some (Gtyp (Fsint (maxn w n)))
                                | Some (Gtyp (Fuint w)) => Some (Gtyp (Fuint (maxn w n)))
                                | _ => None
                                end
   | Eprim_unop (Ushl n) e1 => match type_of_hfexpr_vm vmap e1 tmap with
                                | Some (Gtyp (Fsint w)) => Some (Gtyp (Fsint (w + n)))
                                | Some (Gtyp (Fuint w)) => Some (Gtyp (Fuint (w + n)))
                                | _ => None
                                end
   | Eprim_unop (Ushr n) e1 => match type_of_hfexpr_vm vmap e1 tmap with
                                | Some (Gtyp (Fsint w)) => Some (Gtyp (Fsint (maxn (w - n) 1)))
                                | Some (Gtyp (Fuint w)) => Some (Gtyp (Fuint (maxn (w - n) 1)))
                                | _ => None
                                end
   | Eprim_unop Ucvt e1 => match type_of_hfexpr_vm vmap e1 tmap with
                            | Some (Gtyp (Fsint w)) => Some (Gtyp (Fsint w))
                            | Some (Gtyp (Fuint w)) => Some (Gtyp (Fsint (w + 1)))
                            | _ => None
                            end
   | Eprim_unop Uneg e1 => match type_of_hfexpr_vm vmap e1 tmap with
                            | Some (Gtyp (Fsint w))
                            | Some (Gtyp (Fuint w)) => Some (Gtyp (Fsint (w + 1)))
                            | _ => None
                            end
   | Eprim_unop Unot e1 => match type_of_hfexpr_vm vmap e1 tmap with
                            | Some (Gtyp (Fsint w))
                            | Some (Gtyp (Fuint w)) => Some (Gtyp (Fuint w))
                            | _ => None
                            end
   | Eprim_unop (Uextr n1 n2) e1 => match type_of_hfexpr_vm vmap e1 tmap with
                                     | Some (Gtyp (Fsint w))
                                     | Some (Gtyp (Fuint w)) =>
                                          if (n2 <= n1) && (n1 < w) then Some (Gtyp (Fuint (n1 - n2 + 1)))
                                                                    else None
                                     | _ => None
                                     end
   | Eprim_unop (Uhead n) e1 => match type_of_hfexpr_vm vmap e1 tmap with
                                 | Some (Gtyp (Fsint w))
                                 | Some (Gtyp (Fuint w)) =>
                                      if n <= w then Some (Gtyp (Fuint n))
                                                else None
                                 | _ => None
                                 end
   | Eprim_unop (Utail n) e1 => match type_of_hfexpr_vm vmap e1 tmap with
                                 | Some (Gtyp (Fsint w))
                                 | Some (Gtyp (Fuint w)) =>
                                      if n <= w then Some (Gtyp (Fuint (w - n)))
                                                else None
                                 | _ => None
                                 end
   | Eprim_unop _ e1 => match type_of_hfexpr_vm vmap e1 tmap with
                         | Some (Gtyp (Fsint _))
                         | Some (Gtyp (Fuint _)) => Some (Gtyp (Fuint 1))
                         | _ => None
                         end
   | Eprim_binop (Bcomp _) e1 e2 => match type_of_hfexpr_vm vmap e1 tmap, type_of_hfexpr_vm vmap e2 tmap with
                                     | Some (Gtyp (Fsint _)), Some (Gtyp (Fsint _))
                                     | Some (Gtyp (Fuint _)), Some (Gtyp (Fuint _)) => Some (Gtyp (Fuint 1))
                                     | _, _ => None
                                     end
   | Eprim_binop Badd e1 e2
   | Eprim_binop Bsub e1 e2 => match type_of_hfexpr_vm vmap e1 tmap, type_of_hfexpr_vm vmap e2 tmap with
                                | Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint w2)) => Some (Gtyp (Fuint (maxn w1 w2 + 1)))
                                | Some (Gtyp (Fsint w1)), Some (Gtyp (Fsint w2)) => Some (Gtyp (Fsint (maxn w1 w2 + 1)))
                                | _, _ => None
                                end
   | Eprim_binop Bmul e1 e2 => match type_of_hfexpr_vm vmap e1 tmap, type_of_hfexpr_vm vmap e2 tmap with
                                | Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint w2)) => Some (Gtyp (Fuint (w1 + w2)))
                                | Some (Gtyp (Fsint w1)), Some (Gtyp (Fsint w2)) => Some (Gtyp (Fsint (w1 + w2)))
                                | _, _ => None
                                end
   | Eprim_binop Bdiv e1 e2  => match type_of_hfexpr_vm vmap e1 tmap, type_of_hfexpr_vm vmap e2 tmap with
                                 | Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint w2)) => Some (Gtyp (Fuint w1))
                                 | Some (Gtyp (Fsint w1)), Some (Gtyp (Fsint w2)) => Some (Gtyp (Fsint (w1 + 1)))
                                 | _, _ => None
                                 end
   | Eprim_binop Brem e1 e2 => match type_of_hfexpr_vm vmap e1 tmap, type_of_hfexpr_vm vmap e2 tmap with
                                 | Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint w2)) => Some (Gtyp (Fuint (minn w1 w2)))
                                 | Some (Gtyp (Fsint w1)), Some (Gtyp (Fsint w2)) => Some (Gtyp (Fsint (minn w1 w2)))
                                 | _, _ => None
                                 end
   | Eprim_binop Bdshl e1 e2 => match type_of_hfexpr_vm vmap e1 tmap, type_of_hfexpr_vm vmap e2 tmap with
                                 | Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint w2)) => Some (Gtyp (Fuint (w1 + 2 ^ w2 - 1)))
                                 | Some (Gtyp (Fsint w1)), Some (Gtyp (Fuint w2)) => Some (Gtyp (Fsint (w1 + 2 ^ w2 - 1)))
                                 | _, _ => None
                                 end
   | Eprim_binop Bdshr e1 e2 => match type_of_hfexpr_vm vmap e1 tmap, type_of_hfexpr_vm vmap e2 tmap with
                                 | Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint w2)) => Some (Gtyp (Fuint w1))
                                 | Some (Gtyp (Fsint w1)), Some (Gtyp (Fuint w2)) => Some (Gtyp (Fsint w1))
                                 | _, _ => None
                                 end
   | Eprim_binop Bcat e1 e2 => match type_of_hfexpr_vm vmap e1 tmap, type_of_hfexpr_vm vmap e2 tmap with
                                | Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint w2))
                                | Some (Gtyp (Fsint w1)), Some (Gtyp (Fsint w2)) => Some (Gtyp (Fuint (w1 + w2)))
                                | _, _ => None
                                end
   | Eprim_binop Band e1 e2
   | Eprim_binop Bor e1 e2
   | Eprim_binop Bxor e1 e2 => match type_of_hfexpr_vm vmap e1 tmap, type_of_hfexpr_vm vmap e2 tmap with
                                | Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint w2))
                                | Some (Gtyp (Fsint w1)), Some (Gtyp (Fsint w2)) => Some (Gtyp (Fuint (maxn w1 w2)))
                                | _, _ => None
                                end
   | Emux c e1 e2 => match type_of_hfexpr_vm vmap c tmap, type_of_hfexpr_vm vmap e1 tmap, type_of_hfexpr_vm vmap e2 tmap with
                      | Some (Gtyp (Fuint 1)), Some t1, Some t2 => mux_types t1 t2
                      | _, _, _ => None
                      end
   | Evalidif c e1 => match type_of_hfexpr_vm vmap c tmap with
                      | Some (Gtyp (Fuint 1)) => type_of_hfexpr_vm vmap e1 tmap
                      | _ => None
                      end
   | _ => None (* Some (Gtyp (Fuint 0)) *)
   end.

(*Definition list_rhs_ref_p (vmap : module_graph_vertex_set_p.env) (e : HiFP.href) (tmap: ft_pmap) : 
option (list PProdVarOrder.t * ftype_explicit) :=
(* generates a list of output connectors and a type corresponding to reference e,
   if e has a passive type.
   We can reuse list_lhs_ref_p because the input and output connectors use essentially the same numbering scheme. *)
match list_lhs_ref_p vmap e tmap with
| Some (v, t) => Some (v, make_ftype_explicit t)
| _ => None
end.*)

Fixpoint add_vertex_mux' (ft : ftype) (p : ftype_not_implicit_width ft) (l : list vertex_type) : list vertex_type :=
(* append to l a list of new Mux vertices corresponding to the ground type elements of ft *)
   match ft, p with
   | Gtyp t, p => rcons l (Mux (exist not_implicit_width t p))
   | Atyp t n, p => list_repeat_fn (add_vertex_mux' t p) n l
   | Btyp b, p => add_vertex_mux_fields' b p l
   end
with add_vertex_mux_fields' (b : ffield) (p : ffield_not_implicit_width b) (l : list vertex_type) : list vertex_type :=
   match b, p with
   | Fnil, _ => l
   | Fflips v fl t fs, p => add_vertex_mux_fields' fs (proj2 p) (add_vertex_mux' t (proj1 p) l)
   end.

Definition add_vertex_mux (ft : ftype_explicit) : list vertex_type :=
(* generate a list of new Mux vertices corresponding to the ground type elements of ft *)
   match ft with
   exist ft p => add_vertex_mux' ft p nil
   end.

Fixpoint add_vertex_mux_p' (vmap : module_graph_vertex_set_p.env) (ctree : module_graph_connection_trees_p.env) (ol : list PProdVarOrder.t) (vl : list vertex_type) (on : PProdVarOrder.t) (onl1 : list PProdVarOrder.t) (onl2 : list PProdVarOrder.t) : 
   option (module_graph_vertex_set_p.env * module_graph_connection_trees_p.env * list PProdVarOrder.t) :=
   match vl, onl1, onl2 with
   | nil, nil, nil => Some (vmap, ctree, ol)
   | Mux ot :: vtl, on1 :: ontl1, on2 :: ontl2 =>
      (* generate a new id for every mux vertex, and add it to vmap *)
      let mux_id := module_graph_vertex_set_p.new_key vmap in
      let nvmap := module_graph_vertex_set_p.add mux_id (Mux ot) vmap in
      (* add connection_trees for 3 input_connectors of the mux vertex *)
      let ctree0 := module_graph_connection_trees_p.add (mux_id, N0) (Leaf on) ctree in
      let ctree1 := module_graph_connection_trees_p.add (mux_id, 1%num) (Leaf on1) ctree0 in
      let ctree2 := module_graph_connection_trees_p.add (mux_id, 2%num) (Leaf on2) ctree1 in
      add_vertex_mux_p' nvmap ctree2 (rcons ol (mux_id, N0)) vtl on ontl1 ontl2
   | _,_,_ => None
   end.

Fixpoint list_rhs_expr_p (e : HiFP.hfexpr) (vmap : module_graph_vertex_set_p.env) (ctree : module_graph_connection_trees_p.env) (tmap : CEP.t ftype) : option (list PProdVarOrder.t * module_graph_vertex_set_p.env * module_graph_connection_trees_p.env) :=
   (* 
   1. list of output_connectors, which would be connected to the input_connectors of the vertices on the lhs
   2. ftype of the expr, which help produce constraints in the connection. --> should be an aggr type to distinguish UInt[10][2] and UInt[20].
   3. the expanded new module graph, the vertices set and connection tree can be edited.
   4. next identifier for a new vertex. *)
   match e with
   | Econst t bs => match (data_type_in2arith t bs) with
                    | Some arith_typ => 
                           let nv := Constant arith_typ bs in 
                           let nid := module_graph_vertex_set_p.new_key vmap in
                           let nvmap := module_graph_vertex_set_p.add nid nv vmap in
                           Some ([:: (nid, N0)], nvmap, ctree)
                    | None => None
                     end
   | Eref ref => match base_ref ref tmap with
               | Some (v, t) => let rl := list_lhs_ref_p v (tmap_type_size t) in Some (rl, vmap, ctree)
               | None => None
               end
   | Ecast c e => match list_rhs_expr_p e vmap ctree tmap, type_of_hfexpr_vm vmap e tmap with
                  (* have new vertex set 'nvmap' and connection tree 'ctree0' after first deal with the inner expr, the expr have a output_connector 'eon' *)
                  | Some ([:: eon], nvmap, ctree0), Some ft => 
                     match add_vertex_cast c (make_ftype_explicit ft) with 
                     (* if the inner expr return with a ground type 'ft', a new vertex 'nv' is produced and the cast expr return with type 'rty' *)
                     | Some nv => 
                        let nid := module_graph_vertex_set_p.new_key vmap in
                        let nvmap0 := module_graph_vertex_set_p.add nid nv nvmap in
                        let nct0 := module_graph_connection_trees_p.add (nid, N0) (Leaf eon) ctree0 in
                        Some ([:: (nid, N0)], nvmap0, nct0)
                     | None => None
                     end
                  | _, _ => None
                  end
   | Eprim_unop u e => match list_rhs_expr_p e vmap ctree tmap, type_of_hfexpr_vm vmap e tmap with
                  | Some ([:: eon], nvmap, ctree0), Some ft => 
                     match add_vertex_unop u (make_ftype_explicit ft) with 
                     | Some nv => 
                        match data_type_out2ftype (output_connectors nv) with
                        | Some rft =>
                           let nid := module_graph_vertex_set_p.new_key vmap in
                           let nvmap0 := module_graph_vertex_set_p.add nid nv nvmap in
                           let nct0 := module_graph_connection_trees_p.add (nid, N0) (Leaf eon) ctree0 in
                           Some ([:: (nid, N0)], nvmap0, nct0)
                        | None => None
                        end
                     | None => None
                     end
                  | _, _ => None
                  end
   | Eprim_binop b e1 e2 => match list_rhs_expr_p e1 vmap ctree tmap, type_of_hfexpr_vm vmap e1 tmap with
                  | Some ([:: eon0], nvmap0, ctree0), Some ft0 => 
                     match list_rhs_expr_p e2 nvmap0 ctree0 tmap, type_of_hfexpr_vm vmap e2 tmap with
                     | Some ([:: eon1], nvmap1, ctree1), Some ft1 => 
                        match (add_vertex_binop b (make_ftype_explicit ft0) (make_ftype_explicit ft1)) with 
                        | Some nv => 
                           match data_type_out2ftype (output_connectors nv) with
                           | Some rft => 
                              let nid := module_graph_vertex_set_p.new_key vmap in
                              let nvmap := module_graph_vertex_set_p.add nid nv nvmap1 in
                              let nct0 := module_graph_connection_trees_p.add (nid, N0) (Leaf eon0) ctree1 in
                              let nct1 := module_graph_connection_trees_p.add (nid, 1%num) (Leaf eon1) nct0 in
                              Some ([:: (nid, N0)], nvmap, nct1)
                           | None => None
                           end
                        | None => None
                        end
                     | _, _ => None
                     end
                  | _, _ => None 
                  end
   | Emux e1 e2 e3 => match list_rhs_expr_p e1 vmap ctree tmap, type_of_hfexpr_vm vmap e1 tmap with
                     | Some ([:: eon1], vmap0, ctree0), Some (Gtyp (Fuint 1)) =>
                        match list_rhs_expr_p e2 vmap0 ctree0 tmap, type_of_hfexpr_vm vmap e2 tmap with
                        | Some (eonl2, vmap1, ctree1), Some ft2 =>
                           match list_rhs_expr_p e3 vmap1 ctree1 tmap, type_of_hfexpr_vm vmap e3 tmap with
                           | Some (eonl3, vmap2, ctree2), Some ft3 =>
                              match mux_types ft2 ft3 with
                              | Some rft => 
                                 let nvl := add_vertex_mux (make_ftype_explicit rft) in
                                 match add_vertex_mux_p' vmap2 ctree2 nil nvl eon1 eonl2 eonl3 with
                                 | Some (nvmap, nct, rl) => Some (rl, nvmap, nct)
                                 | None => None
                                 end
                              | None => None
                              end
                           | _, _ => None
                           end
                        | _, _ => None
                        end
                     | _, _ => None
                     end
   | Evalidif c e => list_rhs_expr_p e vmap ctree tmap
   end.

Definition e0 := Eprim_binop Bcat (HiFP.econst (Fuint 4) [::true; true;true; true]) (HiFP.econst (Fuint 4) [:: true]).
Definition e1 := Eprim_unop (Uhead 2) (HiFP.econst (Fuint 4) [::true; true;true; true]).
Definition e2 := Ecast AsSInt (HiFP.econst (Fuint 4) [::true; true;true; true]).
Definition e4 := Emux (HiFP.econst (Fuint 1) [::true]) (HiFP.econst (Fuint 4) [::true; true;true; true]) (HiFP.econst (Fuint 2) [:: true;false]).

Definition ftm1 := ft_add (N0, N0) (Atyp (Gtyp (Fuint 4)) 2) ft_empty.
Definition vmap0 := module_graph_vertex_set_p.add (N0, 1%num) (Wire (Fuint 4)) (module_graph_vertex_set_p.empty vertex_type).
Definition vmap1 := module_graph_vertex_set_p.add (N0, 2%num) (Wire (Fuint 4)) vmap0.
Definition e3 := Eref (Eid (N0, N0)).
Definition e5 := Eref (Esubindex (Eid (N0, N0)) 1).

Definition ftm := ft_add (1%num, N0) (Btyp (Fflips 5%num Nflip (Gtyp (Fsint 1))(Fflips 6%num Nflip (Atyp (Gtyp (Fuint 2)) 2) Fnil))) ftm1.
Definition vmap2 := module_graph_vertex_set_p.add (1%num, 1%num) (Wire (Fsint 1)) vmap1.
Definition vmap3 := module_graph_vertex_set_p.add (1%num, 2%num) (Wire (Fuint 2)) vmap2.
Definition vmap4 := module_graph_vertex_set_p.add (1%num, 3%num) (Wire (Fuint 2)) vmap3.
Definition e6 := Eref (Eid (1%num, N0)).
Definition e7 := Eref (Esubfield (Eid (1%num, N0)) 6%num).

Definition e8 := Emux (HiFP.econst (Fuint 1) [::true]) e3 e7.

(* Definition nvm0 := match (list_rhs_expr_p e8 vmap4 (module_graph_connection_trees_p.empty connection_tree) ftm) with
                  | Some (_, ft, nvmap, nctree) => nvmap
                  | None => (module_graph_vertex_set_p.empty vertex_type)
end.
Definition v0 := match (module_graph_vertex_set_p.find (1%num,1%num) nvm0) with
               | Some v => v 
               | None => (Constant (exist (fun x : fgtyp => is_arithmetic x) (Fuint 0) I)
               [::])
               end.
Definition v3 := match (module_graph_vertex_set_p.find (3%num,N0) nvm0) with
               | Some v => v 
               | None => (Constant (exist (fun x : fgtyp => is_arithmetic x) (Fuint 0) I)
               [::])
               end.
Compute v0.
Compute (output_connectors v0).
Definition ft0 := match (list_rhs_expr_p e8 vmap4 (module_graph_connection_trees_p.empty connection_tree) ftm) with
                  | Some (_, ft, nvmap, nctree) => ft
                  | None => exist ftype_not_implicit_width (Gtyp (Fuint 0)) I
end.
Compute (ft0).
Definition oc0 := match (list_rhs_expr_p e8 vmap4 (module_graph_connection_trees_p.empty connection_tree) ftm) with
                  | Some (oc, ft, nvmap, nctree) => oc
                  | None => nil
end.
Compute (oc0).
Definition ct0 := match (list_rhs_expr_p e8 vmap4 (module_graph_connection_trees_p.empty connection_tree) ftm) with
                  | Some (oc, ft, nvmap, nctree) => nctree
                  | None => (module_graph_connection_trees_p.empty connection_tree)
end.
Compute (ct0).*)

(*Definition type_of_ref r tmap : option ftype :=
   (*match r with
   | Eid v => ft_find v tmap
   | Esubfield r v => let t := type_of_ref r tmap in
                      match t with
                      | Some (Btyp fs) => let fix aux fx := (
                                         match fx with
                                         | Fflips v' f t fxs =>
                                           if (v == v') then Some t
                                           else aux fxs
                                         | Fnil => None
                                         end )
                                   in aux fs
                      | _ => None
                      end
   | Esubindex r n => let t := type_of_ref r tmap in
                      match t with
                      | Some (Atyp ty n) => Some ty
                      | _ => None
                      end
   | Esubaccess r e => None*)
   match ref2pvar r tmap with
   | Some pv => match ft_find (fst pv, N0) tmap with
               | Some checkt => ft_find_sub pv checkt N0 
               | None => None
               end
   | None => None
   end.

Fixpoint type_of_e (e : HiFP.hfexpr) (tmap : ft_pmap) : option ftype_explicit :=
   match e with
   | Econst t bs => match t with
                    | Fuint_implicit w => Some (exist ftype_not_implicit_width (Gtyp (Fuint w)) I)
                    | Fsint_implicit w => Some (exist ftype_not_implicit_width (Gtyp (Fsint w)) I)
                    | t => Some (exist ftype_not_implicit_width (Gtyp t) I)
                    end
   | Eref r => match type_of_ref r tmap with
               | Some t => Some (make_ftype_explicit t)
               | _ => None
               end
   | Ecast AsUInt e1 => match type_of_e e1 tmap with
                         | Some (exist (Gtyp (Fsint w)) _)
                         | Some (exist (Gtyp (Fuint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint w)) I)
                         | Some (exist (Gtyp Fclock) _)
                         | Some (exist (Gtyp Freset) _)
                         | Some (exist (Gtyp Fasyncreset) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint 1)) I)
                         | _ => None
                         end
   | Ecast AsSInt e1 => match type_of_e e1 tmap with
                         | Some (exist (Gtyp (Fsint w)) _)
                         | Some (exist (Gtyp (Fuint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint w)) I)
                         | Some (exist (Gtyp Fclock) _)
                         | Some (exist (Gtyp Freset) _)
                         | Some (exist (Gtyp Fasyncreset) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint 1)) I)
                         | _ => None
                         end
   | Ecast AsClock e1 => match type_of_e e1 tmap with
                         | Some (exist (Gtyp _) _) => Some (exist ftype_not_implicit_width (Gtyp Fclock) I)
                         | _ => None
                         end
   | Ecast AsAsync e1 => match type_of_e e1 tmap with
                         | Some (exist (Gtyp _) _) => Some (exist ftype_not_implicit_width (Gtyp Fasyncreset) I)
                         | _ => None
                         end
   | Eprim_unop (Upad n) e1 => match type_of_e e1 tmap with
                                | Some (exist (Gtyp (Fsint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint (maxn w n))) I)
                                | Some (exist (Gtyp (Fuint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint (maxn w n))) I)
                                | _ => None
                                end
   | Eprim_unop (Ushl n) e1 => match type_of_e e1 tmap with
                                | Some (exist (Gtyp (Fsint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint (w + n))) I)
                                | Some (exist (Gtyp (Fuint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint (w + n))) I)
                                | _ => None
                                end
   | Eprim_unop (Ushr n) e1 => match type_of_e e1 tmap with
                                | Some (exist (Gtyp (Fsint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint (maxn (w - n) 1))) I)
                                | Some (exist (Gtyp (Fuint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint (maxn (w - n) 1))) I)
                                | _ => None
                                end
   | Eprim_unop Ucvt e1 => match type_of_e e1 tmap with
                            | Some (exist (Gtyp (Fsint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint w)) I)
                            | Some (exist (Gtyp (Fuint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint (w + 1))) I)
                            | _ => None
                            end
   | Eprim_unop Uneg e1 => match type_of_e e1 tmap with
                            | Some (exist (Gtyp (Fsint w)) _)
                            | Some (exist (Gtyp (Fuint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint (w + 1))) I)
                            | _ => None
                            end
   | Eprim_unop Unot e1 => match type_of_e e1 tmap with
                            | Some (exist (Gtyp (Fsint w)) _)
                            | Some (exist (Gtyp (Fuint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint w)) I)
                            | _ => None
                            end
   | Eprim_unop (Uextr n1 n2) e1 => match type_of_e e1 tmap with
                                     | Some (exist (Gtyp (Fsint w)) _)
                                     | Some (exist (Gtyp (Fuint w)) _) =>
                                          if (n2 <= n1) && (n1 < w) then Some (exist ftype_not_implicit_width (Gtyp (Fuint (n1 - n2 + 1))) I)
                                                                    else None
                                     | _ => None
                                     end
   | Eprim_unop (Uhead n) e1 => match type_of_e e1 tmap with
                                 | Some (exist (Gtyp (Fsint w)) _)
                                 | Some (exist (Gtyp (Fuint w)) _) =>
                                      if n <= w then Some (exist ftype_not_implicit_width (Gtyp (Fuint n)) I)
                                                else None
                                 | _ => None
                                 end
   | Eprim_unop (Utail n) e1 => match type_of_e e1 tmap with
                                 | Some (exist (Gtyp (Fsint w)) _)
                                 | Some (exist (Gtyp (Fuint w)) _) =>
                                      if n <= w then Some (exist ftype_not_implicit_width (Gtyp (Fuint (w - n))) I)
                                                else None
                                 | _ => None
                                 end
   | Eprim_unop _ e1 => match type_of_e e1 tmap with
                         | Some (exist (Gtyp (Fsint _)) _)
                         | Some (exist (Gtyp (Fuint _)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint 1)) I)
                         | _ => None
                         end
   | Eprim_binop (Bcomp _) e1 e2 => match type_of_e e1 tmap, type_of_e e2 tmap with
                                     | Some (exist (Gtyp (Fsint _)) _), Some (exist (Gtyp (Fsint _)) _)
                                     | Some (exist (Gtyp (Fuint _)) _), Some (exist (Gtyp (Fuint _)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint 1)) I)
                                     | _, _ => None
                                     end
   | Eprim_binop Badd e1 e2
   | Eprim_binop Bsub e1 e2 => match type_of_e e1 tmap, type_of_e e2 tmap with
                                | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint (maxn w1 w2 + 1))) I)
                                | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fsint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint (maxn w1 w2 + 1))) I)
                                | _, _ => None
                                end
   | Eprim_binop Bmul e1 e2 => match type_of_e e1 tmap, type_of_e e2 tmap with
                                | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint (w1 + w2))) I)
                                | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fsint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint (w1 + w2))) I)
                                | _, _ => None
                                end
   | Eprim_binop Bdiv e1 e2  => match type_of_e e1 tmap, type_of_e e2 tmap with
                                 | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint w1)) I)
                                 | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fsint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint (w1 + 1))) I)
                                 | _, _ => None
                                 end
   | Eprim_binop Brem e1 e2 => match type_of_e e1 tmap, type_of_e e2 tmap with
                                 | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint (minn w1 w2))) I)
                                 | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fsint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint (minn w1 w2))) I)
                                 | _, _ => None
                                 end
   | Eprim_binop Bdshl e1 e2 => match type_of_e e1 tmap, type_of_e e2 tmap with
                                 | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint (w1 + 2 ^ w2 - 1))) I)
                                 | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fuint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint (w1 + 2 ^ w2 - 1))) I)
                                 | _, _ => None
                                 end
   | Eprim_binop Bdshr e1 e2 => match type_of_e e1 tmap, type_of_e e2 tmap with
                                 | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint w1)) I)
                                 | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fuint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint w1)) I)
                                 | _, _ => None
                                 end
   | Eprim_binop Bcat e1 e2 => match type_of_e e1 tmap, type_of_e e2 tmap with
                                | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _)
                                | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fsint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint (w1 + w2))) I)
                                | _, _ => None
                                end
   | Eprim_binop Band e1 e2
   | Eprim_binop Bor e1 e2
   | Eprim_binop Bxor e1 e2 => match type_of_e e1 tmap, type_of_e e2 tmap with
                                | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _)
                                | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fsint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint (maxn w1 w2))) I)
                                | _, _ => None
                                end
   | Emux c e1 e2 => match type_of_e c tmap, type_of_e e1 tmap, type_of_e e2 tmap with
                      | Some (exist (Gtyp (Fuint 1)) _), Some t1, Some t2 => ftype_mux t1 t2
                      | _, _, _ => None
                      end
   | Evalidif c e1 => match type_of_e c tmap with
                      | Some (exist (Gtyp (Fuint 1)) _) => type_of_e e1 tmap
                      | _ => None
                      end
   | _ => None (* Some (exist ftype_not_implicit_width (Gtyp (Fuint 0)) I) *)
   end.
*)

Fixpoint type_of_hfexpr (e : HiFP.hfexpr) (ce : CEP.t ftype) : option ftype :=
(* calculates the type of the expression e.
   In contrast to HiFP.type_of_hfexpr, this function only needs the map of types,
   and it will preserve the information whether some ground type has an implicit width
   (I am not sure yet whether that information needs to be preserved at all.)
   Should the width of variables be preserved faithfully? Not sure at this moment;
   perhaps we need two versions. *)
match e with
| Econst t _ => Some (Gtyp t)
| Eref r => match base_ref r ce with
            | Some (_, ft) => Some ft
            | None => None
            end
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
| Ecast AsAsync e1 => match type_of_hfexpr e1 ce  with
                      | Some (Gtyp _) => Some (Gtyp Fasyncreset)
                      | _ => None
                      end
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

(*Fixpoint connect_type_compatible (ft_ref : ftype) (ft_expr : ftype_explicit) : bool :=
   match ft_ref, ft_expr with
   | Gtyp (Fuint _), exist (Gtyp (Fuint _)) _
   | Gtyp (Fsint _), exist (Gtyp (Fsint _)) _
   | Gtyp Fclock, exist (Gtyp Fclock) _
   | Gtyp Freset, exist (Gtyp Freset) _
   | Gtyp Fasyncreset, exist (Gtyp Fasyncreset) _ => true
   | Gtyp (Fuint_implicit w_ref), exist (Gtyp (Fuint w_expr)) _
   | Gtyp (Fsint_implicit w_ref), exist (Gtyp (Fsint w_expr)) _ => w_ref >= w_expr
   | Atyp t_ref n_ref, exist (Atyp t_expr n_expr) p => connect_type_compatible t_ref (exist ftype_not_implicit_width t_expr p) && (n_ref == n_expr)
   | Btyp ff_ref, exist (Btyp ff_expr) p => connect_type_compatible_fields ff_ref (exist ffield_not_implicit_width ff_expr p)
   | _, _ => false
   end
with connect_type_compatible_fields (ff_ref : ffield) (ff_expr : ffield_explicit) : bool :=
   match ff_ref, ff_expr with
   | Fnil, exist Fnil _ => true
   | Fflips v_ref Nflip t_ref ff_ref', exist (Fflips v_expr Nflip t_expr ff_expr') p =>
          (v_ref == v_expr) && connect_type_compatible t_ref (exist ftype_not_implicit_width t_expr (proj1 p))
                            && connect_type_compatible_fields ff_ref' (exist ffield_not_implicit_width ff_expr' (proj2 p))
   | _, _ => false
   end.

Definition connect_non_passive_fgtyp (ct_old : module_graph_connection_trees_p.env)
                                     (lst_tgt : list PProdVarOrder.t) (gt_tgt : fgtyp)
                                     (lst_src : list PProdVarOrder.t) (gt_src : fgtyp)
                                     (ct_new : module_graph_connection_trees_p.env) : bool :=
(* The predicate checks whether ct_new contains the correct connection that connects from lst_src to lst_tgt,
   and it does not change the connection into lst_src.
   These lists must be one-element lists for output and input connectors of compatible types. *)
      match lst_tgt, lst_src with
      | [:: ic], [:: oc] =>    (module_graph_connection_trees_p.find ic ct_new == Some (Leaf oc))
                            &&
                               (module_graph_connection_trees_p.find oc ct_new == module_graph_connection_trees_p.find oc ct_old)
                               (* why this is compared?
                                  In Sem_frag_stmt, it is ensured that connection trees NOT related to tgt or src are not changed.
                                  Here, we need to ensure that the connection tree of tgt is changed
                                  and the connection tree of src remains the same. *)
      | _, _ => false
      end
   &&
      match gt_tgt, gt_src with
      | Fuint _, Fuint _
      | Fuint _, Fuint_implicit _
      | Fsint _, Fsint _
      | Fsint _, Fsint_implicit _
      | Fclock, Fclock
      | Freset, Freset
      | Fasyncreset, Fasyncreset => true
      | Fuint_implicit wt, Fuint ws
      | Fuint_implicit wt, Fuint_implicit ws
      | Fsint_implicit wt, Fsint ws
      | Fsint_implicit wt, Fsint_implicit ws => wt >= ws
      | _, _ => false
      end.

Fixpoint connect_non_passive (ct_old : module_graph_connection_trees_p.env)
                             (lst_tgt : list PProdVarOrder.t) (ft_tgt : ftype)
                             (lst_src : list PProdVarOrder.t) (ft_src : ftype)
                             (ct_new : module_graph_connection_trees_p.env) : bool :=
   (* The predicate returns true if the correct connection trees are in ct_new
      that connect from lst_src to lst_tgt, and that the connection trees that
      connect to lst_src are not changed.  Other connection trees are not checked.
      The type of lst_tgt is ft_tgt, and the type of lst_src is ft_src.
      These references are *not* required to have passive types.

      We copy the same code two times, to allow Coq to prove that the recursion is well-founded. *)
   match ft_tgt, ft_src with
   | Gtyp gt_tgt, Gtyp gt_src => connect_non_passive_fgtyp ct_old lst_tgt gt_tgt lst_src gt_src ct_new
   | Atyp elt_tgt n1, Atyp elt_src n2 => (n1 == n2) &&
      let type_len := size_of_ftype elt_tgt in
            (size lst_tgt <= type_len * n1) && (size lst_src <= type_len * n1)
         &&
            [forall n : ordinal n1,
               connect_non_passive ct_old
                                   (take type_len (drop (n * type_len) lst_tgt)) elt_tgt
                                   (take type_len (drop (n * type_len) lst_src)) elt_src
                                   ct_new]
   | Btyp ft, Btyp fs => connect_non_passive_fields ct_old lst_tgt ft lst_src fs ct_new
   | _, _ => false
   end
with connect_non_passive_fields (ct_old : module_graph_connection_trees_p.env)
                                (lst_tgt : list PProdVarOrder.t) (ft_tgt : ffield)
                                (lst_src : list PProdVarOrder.t) (ft_src : ffield)
                                (ct_new : module_graph_connection_trees_p.env) : bool :=
   (* The predicate returns true if the correct connection trees are in ct_new
      that connect from lst_src to lst_tgt, and that the connection trees that
      connect to lst_src are not changed.  Other connection trees are not checked.
      The type of lst_tgt is (Btyp ft_tgt), and the type of lst_src is (Btyp ft_src).
      These references are *not* required to have passive types.

      We copy the same code two times, to allow Coq to prove that the recursion is well-founded. *)
   match ft_tgt, ft_src with
   | Fnil, Fnil => true
   | Fflips v1 Nflip gtt ft, Fflips v2 Nflip gts fs => (v1 == v2) &&
         let type_len := size_of_ftype gtt in
               connect_non_passive ct_old (take type_len lst_tgt) gtt (take type_len lst_src) gts ct_new
            &&
               connect_non_passive_fields ct_old (drop type_len lst_tgt) ft (drop type_len lst_src) fs ct_new
   | Fflips v1 Flipped gtt ft, Fflips v2 Flipped gts fs => (v1 == v2) &&
         let type_len := size_of_ftype gts in
               connect_non_passive_flipped ct_old (take type_len lst_src) gts (take type_len lst_tgt) gtt ct_new
            &&
               connect_non_passive_fields ct_old (drop type_len lst_tgt) ft (drop type_len lst_src) fs ct_new
   | _, _ => false
   end
with connect_non_passive_flipped (ct_old : module_graph_connection_trees_p.env)
                                 (lst_tgt : list PProdVarOrder.t) (ft_tgt : ftype)
                                 (lst_src : list PProdVarOrder.t) (ft_src : ftype)
                                 (ct_new : module_graph_connection_trees_p.env) : bool :=
   (* The code in this predicate is the same as in connect_non_passive. *)
   match ft_tgt, ft_src with
   | Gtyp gt_tgt, Gtyp gt_src => connect_non_passive_fgtyp ct_old lst_tgt gt_tgt lst_src gt_src ct_new
   | Atyp elt_tgt n1, Atyp elt_src n2 => (n1 == n2) &&
      let type_len := size_of_ftype elt_tgt in
            (size lst_tgt <= type_len * n1) && (size lst_src <= type_len * n1)
         &&
            [forall n : ordinal n1,
               connect_non_passive_flipped ct_old
                                           (take type_len (drop (n * type_len) lst_tgt)) elt_tgt
                                           (take type_len (drop (n * type_len) lst_src)) elt_src
                                           ct_new]

   | Btyp ft, Btyp fs => connect_non_passive_fields_flipped ct_old lst_tgt ft lst_src fs ct_new
   | _, _ => false
   end
with connect_non_passive_fields_flipped (ct_old : module_graph_connection_trees_p.env)
                                        (lst_tgt : list PProdVarOrder.t) (ft_tgt : ffield)
                                        (lst_src : list PProdVarOrder.t) (ft_src : ffield)
                                        (ct_new : module_graph_connection_trees_p.env) : bool :=
   (* The code in this predicate is the same as in connect_non_passive_fields. *)
   match ft_tgt, ft_src with
   | Fnil, Fnil => true
   | Fflips v1 Nflip gtt ft, Fflips v2 Nflip gts fs => (v1 == v2) &&
         let type_len := size_of_ftype gtt in
               connect_non_passive_flipped ct_old (take type_len lst_tgt) gtt (take type_len lst_src) gts ct_new
            &&
               connect_non_passive_fields_flipped ct_old (drop type_len lst_tgt) ft (drop type_len lst_src) fs ct_new
   | Fflips v1 Flipped gtt ft, Fflips v2 Flipped gts fs => (v1 == v2) &&
         let type_len := size_of_ftype gts in
               connect_non_passive ct_old (take type_len lst_src) gts (take type_len lst_tgt) gtt ct_new
            &&
               connect_non_passive_fields_flipped ct_old (drop type_len lst_tgt) ft (drop type_len lst_src) fs ct_new
   | _, _ => false
   end.
*)

Definition connect_fgtyp_compatible (t_tgt t_src : fgtyp) : bool :=
  if (not_implicit t_tgt) then true
  else (sizeof_fgtyp t_tgt >= sizeof_fgtyp t_src) && fgtyp_equiv t_tgt t_src.

Fixpoint check_connect_fgtyp_compatible (t_tgt t_src : ftype) (n : nat) : bool :=
  match n with
  | 0 => true
  | S m => match ft_check_flip t_tgt (N.of_nat m) false, ft_find_sub t_tgt (N.of_nat m), ft_find_sub t_src (N.of_nat m) with
          | Some false, Some gt_tgt, Some gt_src => connect_fgtyp_compatible gt_tgt gt_src && check_connect_fgtyp_compatible t_tgt t_src m
          | _,None,None => true
          | _,_,_ => false
          end
  end.

Fixpoint check_connect_non_passive_fgtyp (t_tgt t_src : ftype) (n : nat) : bool :=
  match n with
  | 0 => true
  | S m => match ft_check_flip t_tgt (N.of_nat m) false, ft_find_sub t_tgt (N.of_nat m), ft_find_sub t_src (N.of_nat m) with
          | Some false, Some gt_tgt, Some gt_src => connect_fgtyp_compatible gt_tgt gt_src && check_connect_non_passive_fgtyp t_tgt t_src m
          | Some true, Some gt_tgt, Some gt_src => connect_fgtyp_compatible gt_src gt_tgt && check_connect_non_passive_fgtyp t_tgt t_src m
          | _,None,None => true
          | _,_,_ => false
          end
  end.

Definition connect_non_passive_type (t_tgt : ftype) (t_src : ftype) : Prop :=
  ftype_equiv t_tgt t_src && check_connect_non_passive_fgtyp t_tgt t_src (tmap_type_size t_tgt).

Definition connect_type_compatible (t_tgt t_src : ftype) : bool :=
  ftype_equiv t_tgt t_src && check_connect_fgtyp_compatible t_tgt t_src (tmap_type_size t_tgt).


Definition map2_helper_ct (c : PProdVarOrder.t) (true_tree : option connection_tree) (false_tree : option connection_tree) : option connection_tree :=
match true_tree, false_tree with
| None, _ => None
| _, None => None
| Some Not_connected, _ => true_tree
| _, Some Not_connected => false_tree
| Some Invalidated, _ => false_tree
| _, Some Invalidated => true_tree
| Some a, Some b => if (a == b) then true_tree else Some (Choice c a b)
end.

Fixpoint Sem_frag_stmt (vm_old : module_graph_vertex_set_p.env) (ct_old : module_graph_connection_trees_p.env) (s : HiFP.hfstmt) (vm_new : module_graph_vertex_set_p.env) (ct_new : module_graph_connection_trees_p.env) (tmap : CEP.t ftype) : Prop :=
   (* The predicate returns True if vm_new/ct_new can be constructed from vm_old/ct_old by applying s. 
   type checking, constraints *)
   match s with
   | Sskip => vm_old = vm_new /\ ct_old = ct_new
   | Sfcnct ref_tgt (Eref ref_src) => (* allow non-passive types *)
          module_graph_vertex_set_p.Equal vm_old vm_new
       /\
         match base_ref ref_tgt tmap, base_ref ref_src tmap with
         | Some (v_tgt, t_tgt), Some (v_src, t_src) => 
            let lst_tgt := list_lhs_ref_p v_tgt (tmap_type_size t_tgt) in
            let lst_src := list_lhs_ref_p v_src (tmap_type_size t_src) in
               match fillft_vm (tmap_type_size t_tgt) t_tgt v_tgt vm_old, fillft_vm (tmap_type_size t_src) t_src v_src vm_old with
               | Some ft_tgt, Some ft_src => connect_non_passive_type ft_tgt ft_src
               | _, _ => False
               end
             /\
                 forall v0 : PProdVarOrder.T,
                    if (v0 \in lst_tgt) || (v0 \in lst_src) then True (* already checked in connect_non_passive *)
                    else module_graph_connection_trees_p.find v0 ct_old = module_graph_connection_trees_p.find v0 ct_new
         | _, _ => False
         end
   | Sfcnct ref expr => match base_ref ref tmap with
                        | Some (v_tgt, t_tgt) => let input_list := list_lhs_ref_p v_tgt (tmap_type_size t_tgt) in
                           match fillft_vm (tmap_type_size t_tgt) t_tgt v_tgt vm_old with
                           | Some ft_ref => match list_rhs_expr_p expr vm_old ct_old tmap, type_of_hfexpr_vm vm_old expr tmap with
                              | Some (output_list, nvmap, nctree), Some ft_expr =>
                           module_graph_vertex_set_p.Equal nvmap vm_new
                        /\
                           connect_type_compatible ft_ref ft_expr
                        /\
                           (forall n : nat,
                              match (List.nth_error output_list n), (List.nth_error input_list n) with 
                              | Some oc, Some ic => module_graph_connection_trees_p.find ic ct_new = Some (Leaf oc)
                              | _, _ => True
                              end)
                        /\
                           forall v0 : PProdVarOrder.T,
                              if (v0 \in input_list) then True
                              else module_graph_connection_trees_p.find v0 nctree = module_graph_connection_trees_p.find v0 ct_new
                              | _, _ => False
                              end
                           | _ => False
                           end
                     | _ => False
                     end
   | Sinvalid ref =>    module_graph_vertex_set_p.Equal vm_old vm_new
                     /\ (* ct *)
                        match base_ref ref tmap with
                        | Some (v_tgt, t_tgt) => let input_list := list_lhs_ref_p v_tgt (tmap_type_size t_tgt) in
                              (forall n : nat,
                                 match (List.nth_error input_list n) with 
                                 | Some ic => module_graph_connection_trees_p.find ic ct_new = Some Invalidated
                                 | _ => True
                                 end)
                           /\
                              forall (v0 : PProdVarOrder.T),
                                 if (v0 \in input_list) then True
                                 else module_graph_connection_trees_p.find v0 ct_old = module_graph_connection_trees_p.find v0 ct_new
                        | None => False
                        end
   | Swire v t => exists tlist : seq fgtyp,
                        vtype_list t nil tlist
                     /\ (forall (v0 : VarOrder.T) (n0 : N),
                           if v0 != (fst v) then module_graph_vertex_set_p.find (v0, n0) vm_old = module_graph_vertex_set_p.find (v0, n0) vm_new
                        /\ module_graph_connection_trees_p.find ((v0, n0), 0%num) ct_new = module_graph_connection_trees_p.find ((v0, n0), 0%num) ct_old
                           else True)
                     /\ (forall n : nat,
                           match List.nth_error tlist n with
                           | Some nv => module_graph_vertex_set_p.find (fst v, N.of_nat n) vm_new = Some (Wire nv)
                                     /\ module_graph_connection_trees_p.find ((fst v, N.of_nat n), 0%num) ct_new = Some Not_connected
                           | None => module_graph_vertex_set_p.find (fst v, N.of_nat n) vm_new = module_graph_vertex_set_p.find (fst v, N.of_nat n) vm_old
                                     /\ module_graph_connection_trees_p.find ((fst v, N.of_nat n), 0%num) ct_new = module_graph_connection_trees_p.find ((fst v, N.of_nat n), 0%num) ct_old
                           end)
                     /\ (* ct *)
                        module_graph_connection_trees_p.Equal ct_old ct_new
   | Sreg v reg => exists tlist : seq fgtyp,
                   vtype_list (type reg) nil tlist /\
                   match list_rhs_expr_p (clock reg) vm_old ct_old tmap, type_of_hfexpr_vm vm_old (clock reg) tmap with
                   | Some ([:: clk_out], nvmap0, nctree0), Some (Gtyp Fclock) =>
                        exists (nvmap : module_graph_vertex_set_p.env) (nctree : module_graph_connection_trees_p.env)
                               (rst_sig_is_async : bool) (rst_sig_out : PProdVarOrder.t) (rst_val_out_list : list PProdVarOrder.t),
                              (if (reset reg) is (Rst rst_sig rst_val)
                               then match list_rhs_expr_p rst_sig nvmap0 nctree0 tmap, type_of_hfexpr_vm vm_old rst_sig tmap with
                                    | Some ([:: rst_sig_out'], nvmap1, nctree1), Some (Gtyp rst_sig_type) =>
                                           rst_sig_out = rst_sig_out'
                                        /\
                                           (rst_sig_type = if rst_sig_is_async then Fasyncreset else Fuint 1)
                                        /\
                                           match list_rhs_expr_p rst_val nvmap1 nctree1 tmap, type_of_hfexpr_vm vm_old rst_val tmap with
                                           | Some (rst_val_out_list', nvmap2, nctree2), Some rst_val_type =>
                                                   rst_val_out_list = rst_val_out_list'
                                                /\
                                                   rst_val_type = type reg
                                                /\
                                                   nvmap = nvmap2 /\ nctree = nctree2
                                           | _, _ => False
                                           end
                                    | _, _ => False
                                    end
                               else nvmap = nvmap0 /\ nctree = nctree0)
                           /\
                              (forall (v0 : VarOrder.T) (n0 : N), v0 <> fst v ->
                                     module_graph_vertex_set_p.find (v0, n0) nvmap = module_graph_vertex_set_p.find (v0, n0) vm_new
                                  /\ forall (c : N),
                                        module_graph_connection_trees_p.find ((v0, n0), c) nctree = module_graph_connection_trees_p.find ((v0, n0), c) ct_new)
                           /\
                              (forall n : N,
                                  match List.nth_error tlist (N.to_nat n) with
                                  | Some nv =>
                                         module_graph_connection_trees_p.find ((fst v, n), 0%num) ct_new = Some (Leaf ((fst v, n), 0%num))
                                      /\
                                         module_graph_connection_trees_p.find ((fst v, n), 1%num) ct_new = Some (Leaf clk_out)
                                      /\
                                         match reset reg, List.nth_error rst_val_out_list n with
                                         | NRst, _ =>
                                                 module_graph_vertex_set_p.find (fst v, n) vm_new = Some (Register nv)
                                              /\
                                                 module_graph_connection_trees_p.find ((fst v, n), 2%num) nctree = module_graph_connection_trees_p.find ((fst v, n), 2%num) ct_new
                                              /\
                                                 module_graph_connection_trees_p.find ((fst v, n), 3%num) nctree = module_graph_connection_trees_p.find ((fst v, n), 3%num) ct_new
                                         | Rst _ _, Some nr =>
                                                 module_graph_vertex_set_p.find (fst v, n) vm_new = Some (RegisterReset nv rst_sig_is_async)
                                              /\
                                                 module_graph_connection_trees_p.find ((fst v, n), 2%num) ct_new = Some (Leaf rst_sig_out)
                                              /\
                                                 module_graph_connection_trees_p.find ((fst v, n), 3%num) ct_new = Some (Leaf nr)
                                         | _, _ => False
                                         end
                                      /\
                                         forall (c : N), c > 3%num ->
                                            module_graph_connection_trees_p.find ((fst v, n), c) nctree = module_graph_connection_trees_p.find ((fst v, n), c) ct_new
                                  | None => module_graph_vertex_set_p.find (fst v, n) vm_new = module_graph_vertex_set_p.find ((fst v), n) vm_old
                                  end)
                   | _, _ => False
                   end
   | Snode v expr => match list_rhs_expr_p expr vm_old ct_old tmap, type_of_hfexpr_vm vm_old expr tmap with
                     | Some (output_list, nvmap, nctree), Some ft0 =>
                           (forall (v0 : VarOrder.T) (n0 : N),
                              if v0 != (fst v) then module_graph_vertex_set_p.find (v0, n0) nvmap = module_graph_vertex_set_p.find (v0, n0) vm_new
                                         else True)
                        /\ (forall (v0 : ProdVarOrder.T) (n0 : N),
                              if v0 != v then module_graph_connection_trees_p.find (v0, n0) nctree = module_graph_connection_trees_p.find (v0, n0) ct_new
                                   else True)
                        /\ exists tlist : seq fgtyp,
                           vtype_list ft0 nil tlist /\
                           forall n : nat,
                              match List.nth_error tlist n, List.nth_error output_list n with
                              | Some nv, Some oc => module_graph_vertex_set_p.find ((fst v), N.of_nat n) vm_new = Some (Node nv)
                                        /\ module_graph_connection_trees_p.find ((fst v, N.of_nat n), 0%num) ct_new = Some (Leaf oc)
                              | None, None => module_graph_vertex_set_p.find ((fst v), N.of_nat n) vm_new = module_graph_vertex_set_p.find ((fst v), N.of_nat n) nvmap
                                        /\ forall c : N,
                                               module_graph_connection_trees_p.find ((fst v, N.of_nat n), c) ct_new = module_graph_connection_trees_p.find ((fst v, N.of_nat n), c) nctree
                               | _, _ => False
                               (* let add_list (v : VarOrder.T) (vm : module_graph_connection_trees_p.env) (p : nat * fgtyp) := module_graph_vertex_set_p.add (v, fst p) (Wire (snd p)) vm in
                               module_graph_vertex_set_p.Equal vm_new (foldl add_list nvmap (zip (iota 1 (length tlist)) tlist)) *)
                               end
                     | _, _ => False
                     end
   | Smem v mem => False (* ? *)
                 (*exists data_tlist : seq fgtyp,
                         vtype_list (data_type mem) nil data_tlist
                     /\ (forall (v0 : VarOrder.T) (n0 : N),
                           if v0 != (fst v) then module_graph_vertex_set_p.find (v0, n0) vm_old = module_graph_vertex_set_p.find (v0, n0) vm_new
                                              /\ module_graph_connection_trees_p.find ((v0, n0), 0%num) ct_new = module_graph_connection_trees_p.find ((v0, n0), 0%num) ct_old
                           else True)
                     /\ (let tlist := (some type based on the ports of mem and data_tlist) in
                         forall n : nat,
                           match List.nth_error tlist n with
                           | Some nv => module_graph_vertex_set_p.find (fst v, N.of_nat n) vm_new = Some (Wire nv)
                                     /\ module_graph_connection_trees_p.find ((fst v, N.of_nat n), 0%num) ct_new = Some Not_connected
                           | None => module_graph_vertex_set_p.find (fst v, N.of_nat n) vm_new = module_graph_vertex_set_p.find (fst v, N.of_nat n) vm_old
                                     /\ module_graph_connection_trees_p.find ((fst v, N.of_nat n), 0%num) ct_new = module_graph_connection_trees_p.find ((fst v, N.of_nat n), 0%num) ct_old
                           end)
                     /\ (* ct *)
                        module_graph_connection_trees_p.Equal ct_old ct_new*)
   | Sinst var1 var2 => False (* ? *)
   | Swhen cond ss_true ss_false => match list_rhs_expr_p cond vm_old ct_old tmap, type_of_hfexpr_vm vm_old cond tmap with
                                    | Some ([:: oc], nvmap0, nctree0), Some (Gtyp (Fuint 1)) => exists (vm' : module_graph_vertex_set_p.env) (ct_true ct_false : module_graph_connection_trees_p.env), 
                                          Sem_frag_stmts nvmap0 nctree0 ss_true vm' ct_true tmap
                                       /\ Sem_frag_stmts vm' nctree0 ss_false vm_new ct_false tmap
                                       /\ (*False*) 
                                          let ct0 := module_graph_connection_trees_p.map2 (map2_helper_ct oc) ct_old ct_new in
                                          module_graph_connection_trees_p.Equal ct_new ct0
                                        (*ct_new is a combination of ct_true and ct_false (probably using map2):
                                          * if a connection is defined in both and is equal, just copy it
                                          * if a connection is defined in both and is different, create a choice connection tree
                                          * if a connection is only present in ct_true / ct_false and the vertex of the input connector was not in vm_old, then it should be copied
                                          * if a connection is only present in ct_true / ct_false and the vertex of the input connector was in vm_old, then the new connection should be unconnected.
                                          Problem with the last two cases: it is unclear how to decide whether the input connector was in vm_old,
                                          because map2 does not provide the key. *)
                                    | _, _ => False
                                    end
   end with
Sem_frag_stmts (vm_old : module_graph_vertex_set_p.env) (ct_old : module_graph_connection_trees_p.env) (ss : HiFP.hfstmt_seq) (vm_new : module_graph_vertex_set_p.env) (ct_new : module_graph_connection_trees_p.env) (tmap : CEP.t ftype) : Prop :=
   match ss with
   | Qnil => module_graph_vertex_set_p.Equal vm_old vm_new /\ module_graph_connection_trees_p.Equal ct_old ct_new
   | Qcons s ss' => exists (vm' : module_graph_vertex_set_p.env) (ct' : module_graph_connection_trees_p.env), 
                     Sem_frag_stmt vm_old ct_old s vm' ct' tmap /\ Sem_frag_stmts vm' ct' ss' vm_new ct_new tmap
   end.
   
(* ... { V : Set & V -> vertex_type }. *)
   (* This is a type of pairs consisting of a set and a function from this set to vertex_type.
      Given V : module_graph_vertices, the set is (projT1 V) and the function is (projT2 V).
      I would like V to be a finite set but I don't know exactly how to specify that. *)
(*
Definition module_graph_vertex_set : Type := { V : Set & V -> vertex_type }.

(* property of a correct output connetor identifier, which is the natural number is smaller then the amount of output connectors of the vertex *)
Definition output_connector_number_correct (V : module_graph_vertex_set_p.env) (connector : module_graph_vertex_set_p.key * nat) : Prop :=
    if module_graph_vertex_set_p.find (fst connector) V is Some vx_typ
    then snd connector < size (output_connectors vx_typ)
    else False.

Definition output_connectors_of_module_graph (V : module_graph_vertex_set_p.env) : Type :=
   { x : module_graph_vertex_set_p.key * nat | output_connector_number_correct V x }.
   (* This is a type of pairs, where the first is an element of a module_graph_vertices set,
      and the second of the pair is a natural number that is < than the number of output connectors of that element. *)

Definition output_connector_type (V : module_graph_vertex_set_p.env) (oc : output_connectors_of_module_graph V) : fgtyp_explicit :=
(* finds the data type of output connector oc *)
match oc with
exist (vx_id, conn_nr) number_correct =>
match module_graph_vertex_set_p.find vx_id V as o
      return (if o is Some vx_typ return Prop
              then conn_nr < size (output_connectors vx_typ)
              else False) -> fgtyp_explicit with
| Some vx_typ => fun _ => nth Freset_exp (output_connectors vx_typ) conn_nr
| None => fun impossible : False => False_rect fgtyp_explicit impossible
end number_correct
end.

Inductive connection_tree {V: module_graph_vertex_set_p.env} :=
   Invalidated | Not_connected |
   Leaf : (output_connectors_of_module_graph V) -> connection_tree |
   Choice : forall cond : output_connectors_of_module_graph V,
                    output_connector_type V cond = Fuint_exp 1
                    (* the type of cond needs to be Fuint_exp 1 *)
            -> connection_tree -> connection_tree -> connection_tree.

(* property of a correct input connetor identifier, which is the natural number is smaller then the amount of input connectors of the vertex *)
Definition input_connector_number_correct (V : module_graph_vertex_set_p.env) (x : module_graph_vertex_set_p.key * nat) : Prop :=
    if module_graph_vertex_set_p.find (fst x) V is Some elt
    then snd x < size (input_connectors elt)
    else False.

Definition input_connectors_of_module_graph (V : module_graph_vertex_set_p.env) : Type :=
   { x : module_graph_vertex_set_p.key * nat | input_connector_number_correct V x}.
   (* This is a set containing pairs, where the first is an element of a module_graph_vertices set,
      and the second of the pair is a natural number that is < than the number of input connectors of that element. *)

Lemma input_connectors_eq_dec : forall {V : module_graph_vertex_set_p.env} {x y : input_connectors_of_module_graph V}, {x = y} + {x <> y}.
Proof.
Admitted.

Definition input_connectors_eqn (V : module_graph_vertex_set_p.env) (x y : input_connectors_of_module_graph V) : bool :=
match x, y with
| (exist ((a1,a2), a3) _), (exist ((b1,b2), b3) _) => (a1 == b1) && (a2 == b2) && (a3 == b3)
end.

Lemma input_connectors_eqP (V : module_graph_vertex_set_p.env) : Equality.axiom (input_connectors_eqn V).
Proof.
Admitted.

Canonical input_connectors_eqMixin {V : module_graph_vertex_set_p.env} := EqMixin (input_connectors_eqP V).
Canonical input_connectors_eqType {V : module_graph_vertex_set_p.env} := Eval hnf in EqType (input_connectors_of_module_graph V) input_connectors_eqMixin.

Definition input_connector_type (V : module_graph_vertex_set_p.env) (ic : input_connectors_of_module_graph V) : fgtyp :=
(* finds the data type of input connector ic *)
match ic with
exist (vx_id, conn_nr) number_correct =>
match module_graph_vertex_set_p.find vx_id V as i
      return (if i is Some vx_typ return Prop
              then conn_nr < size (input_connectors vx_typ)
              else False) -> fgtyp with
| Some vx_typ => fun _ => nth Freset (input_connectors vx_typ) conn_nr
| None => fun impossible : False => False_rect fgtyp impossible
end number_correct
end.

(* type of map of connection trees, a function from a input connector to a tree *)
Definition module_graph_connection_trees (V: module_graph_vertex_set_p.env): Type :=
   input_connectors_of_module_graph V -> @connection_tree V.

Definition module_graph : Type :=
(* a pair, namely a set of module_graph_vertices, together with a mapping that gives a connection tree
for every input connector of every module_graph_vertex. *)
   { V : module_graph_vertex_set_p.env & module_graph_connection_trees V }.

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
*)

(*
Fixpoint add_vertex_input (v : N (*pvar match(_,0)从(_,1)开始添加*)) (n : N (*index*)) (l: list fgtyp) (vmap : module_graph_vertex_set_p.env) :=
   match l with
   | nil => vmap
   | hd :: tl => let nvmap := module_graph_vertex_set_p.add (v, n) (InPort hd) vmap in
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

Fixpoint list_outputs (p : N) (keys : list (N * N)) (vmap : module_graph_vertex_set_p.env) (ls : option (list (output_connectors_of_module_graph vmap))) : option (list (output_connectors_of_module_graph vmap)) :=
   match keys with 
   | nil => ls
   | (p, n) :: tl => match list_outputs p tl vmap ls with 
               | Some lst => match (module_graph_vertex_set_p.find (p, n) vmap) with
                              | Some v => Some (cons ((p,n), 0) lst) (* 应该按1...n的顺序添加 *)
                              | None => None
                              end
               | None => None
               end
   | _ => ls
   end.*)
   (* return 从(p,1)到(p,n)的output_connectors name *)

(*Fixpoint list_lhs_expr (e : hfexpr) (vmap : module_graph_vertex_set_p.env) (cs : list input_connectors) (ts : seq fgtyp) : list input_connectors * seq fgtyp :=
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

Fixpoint list_output' {V : module_graph_vertex_set_p.env} (p : var) (n : nat) : option (list (output_connectors_of_module_graph V)).
(* generates a list of output connectors of vertices (p,1), (p,2), ..., (p,n).
   If some of these output connectors do not exist, the function returns None. *)
destruct n as [|n'].
exact (Some [::]).
destruct (list_output' V p n') as [lst|].
destruct (module_graph_vertex_set_p.find (p,N.of_nat n'.+1) V) as [vx_typ|] eqn: vertex_found.
destruct (0 < size (output_connectors vx_typ)) eqn: has_connectors.
assert (number_correct: output_connector_number_correct V ((p, N.of_nat n'.+1), 0))
       by (rewrite /output_connector_number_correct vertex_found ; exact has_connectors).
exact (Some (rcons lst (exist (output_connector_number_correct V) ((p,N.of_nat n'.+1),0) number_correct))).
exact None.
exact None.
exact None.
Defined.

Fixpoint list_output {V : module_graph_vertex_set_p.env} (p : var) (n : nat) : option (seq (output_connectors_of_module_graph V)) :=
(* generates a list of output connector 0 of vertices (p,1), (p,2), ..., (p,n)
   If some of these output connectors do not exist, the function returns None.
   This definition is based on "Print list_output'.", with a few simplifications. *)
  match n with
  | 0 => Some [::]
  | S n' =>
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

Fixpoint select_list_rhs_ffield {V : module_graph_vertex_set_p.env} (lst : list (output_connectors_of_module_graph V)) (ff : ffield) (v : var) :
      option (list (output_connectors_of_module_graph V) * ftype) :=
(* selects from list lst, which corresponds to type ff, the part for field v *)
match ff with
| Fflips v0 Nflip ft ff' => let len := size_of_ftype ft in
                             if v == v0 then Some (take len lst, ft)
                                        else select_list_rhs_ffield (drop len lst) ff' v
| _ => None
end.

Fixpoint list_rhs_ref {V : module_graph_vertex_set_p.env} (e : HiFP.href) (tmap: ft_pmap) : 
option (list (output_connectors_of_module_graph V) * ftype) :=
(* generates a list of output connectors and a type corresponding to reference e,
   if e has a passive type *)
match e with
| Eid (p, N0) => match ft_find (p,N0) tmap with
                | Some ft => match list_output p (size_of_ftype ft) with
                             | Some lst => Some (lst, ft)
                             | _ => None
                             end
                | _ => None
                end
| Esubfield e' v => match list_rhs_ref e' tmap with
                    | Some (lst, Btyp ff) => select_list_rhs_ffield lst ff v
                    | _ => None
                    end
| Esubindex e' n => match list_rhs_ref e' tmap with
                    | Some (lst, Atyp t' m) => if n < m then let len := size_of_ftype t' in
                                                             Some (take len (drop (n * len) lst), t')
                                                        else None
                    | _ => None
                    end
| _ => None
end.

(* functions for connection_tree to add or find in the map *)
Definition ct_find {V : module_graph_vertex_set_p.env} (ic : input_connectors_of_module_graph V) 
   (m : module_graph_connection_trees V) := m ic.
Definition ct_add {V : module_graph_vertex_set_p.env} (ic : input_connectors_of_module_graph V) (ct : connection_tree) 
   (m : module_graph_connection_trees V) : module_graph_connection_trees V :=
   fun (y : input_connectors_of_module_graph V) => if (y == ic) then ct else (ct_find y m).
Definition ct_empty {V : module_graph_vertex_set_p.env} : module_graph_connection_trees V := (fun _ => Not_connected).

(* The following functions change parts / objects belonging to a vertex set V
   to those belonging to (module_graph_vertex_set_p.add (module_graph_vertex_set_p.new_key V) new_vx_typ V). *)

Lemma add_new_vx_new_key_is_new {V : module_graph_vertex_set_p.env} (vx_id : module_graph_vertex_set_p.key) :
   (exists vx_typ : vertex_type, module_graph_vertex_set_p.find vx_id V = Some vx_typ) ->
   ~ module_graph_vertex_set_p.SE.eq vx_id (module_graph_vertex_set_p.new_key V).
Proof.
intros.
destruct H as [vx_typ].
apply module_graph_vertex_set_p.find_2,
      (ex_intro (fun t : vertex_type => module_graph_vertex_set_p.MapsTo vx_id t V) vx_typ),
      module_graph_vertex_set_p.mem_1,
      negbF in H.
contradict H.
move /eqP : H => H.
rewrite H
        module_graph_vertex_set_p.new_key_is_new.
discriminate.
Qed.

Lemma add_new_vx_connector_helper {V : module_graph_vertex_set_p.env}
{conn_id : module_graph_vertex_set_p.key * nat}
(find_vx_typ_and_number_correct : exists vx_typ : vertex_type,
                                        module_graph_vertex_set_p.MapsTo (fst conn_id) vx_typ V
                                     /\ snd conn_id < size (output_connectors vx_typ))
(new_vx_typ : vertex_type) :
(* helper lemma to find a proof of the following in the definition of add_new_vx_connector: *)
let nV := module_graph_vertex_set_p.add (module_graph_vertex_set_p.new_key V) new_vx_typ V in
output_connector_number_correct nV conn_id.
Proof.
destruct find_vx_typ_and_number_correct as [vx_typ [find_vx_typ number_correct]].
rewrite /output_connector_number_correct module_graph_vertex_set_p.find_add_neq.
* apply module_graph_vertex_set_p.find_1 in find_vx_typ.
  rewrite find_vx_typ.
  exact number_correct.
* apply (ex_intro (fun t : vertex_type => module_graph_vertex_set_p.MapsTo (fst conn_id) t V) vx_typ),
        module_graph_vertex_set_p.mem_1,
        negbF in find_vx_typ.
  contradict find_vx_typ.
  move /eqP : find_vx_typ => find_vx_typ.
  rewrite find_vx_typ
          module_graph_vertex_set_p.new_key_is_new.
  discriminate.
Qed.

Lemma add_new_vx_connector_helper2 {V : module_graph_vertex_set_p.env} {conn_id : module_graph_vertex_set_p.key * nat} :
output_connector_number_correct V conn_id
->
if module_graph_vertex_set_p.mem (fst conn_id) V
then exists vx_typ : vertex_type,
           module_graph_vertex_set_p.MapsTo (fst conn_id) vx_typ V
        /\ snd conn_id < size (output_connectors vx_typ)
else False.
Proof.
unfold output_connector_number_correct.
destruct (module_graph_vertex_set_p.find (fst conn_id) V) as [vx_typ|] eqn: Hfind.
* intro.
  generalize Hfind ; intro.
  apply module_graph_vertex_set_p.find_2,
        (ex_intro (fun t : vertex_type => module_graph_vertex_set_p.MapsTo (fst conn_id) t V) vx_typ),
        module_graph_vertex_set_p.mem_1
        in Hfind0.
  rewrite Hfind0.
  exists vx_typ.
  split.
  + apply module_graph_vertex_set_p.find_2.
    exact Hfind.
  + exact H.
* done.
Qed.

Definition add_new_vx_connector {V : module_graph_vertex_set_p.env} (new_vx_typ : vertex_type) (oc : output_connectors_of_module_graph V) :
 output_connectors_of_module_graph (module_graph_vertex_set_p.add (module_graph_vertex_set_p.new_key V) new_vx_typ V) :=
(* Transforms output connect oc into an output connector of the extended module graph *)
let nV := module_graph_vertex_set_p.add (module_graph_vertex_set_p.new_key V) new_vx_typ V in
let (conn_id, number_correct) := oc in
(if module_graph_vertex_set_p.mem (fst conn_id) V as b
    return (if b
            then exists vx_typ : vertex_type,
                       module_graph_vertex_set_p.MapsTo (fst conn_id) vx_typ V
                    /\ snd conn_id < size (output_connectors vx_typ)
            else False) -> output_connectors_of_module_graph nV
 then fun (find_vx_typ_and_number_correct : exists vx_typ : vertex_type,
                                                  module_graph_vertex_set_p.MapsTo (fst conn_id) vx_typ V
                                               /\ snd conn_id < size (output_connectors vx_typ))
       => exist (output_connector_number_correct nV)
                conn_id
                (add_new_vx_connector_helper find_vx_typ_and_number_correct new_vx_typ)
 else fun impossible : False
       => False_rect (output_connectors_of_module_graph nV) impossible
) (add_new_vx_connector_helper2 number_correct).

Lemma add_new_vx_output_connector_eq : forall {V : module_graph_vertex_set_p.env} (new_vx_typ : vertex_type) (oc : output_connectors_of_module_graph V),
let (new_conn_id, _) := add_new_vx_connector new_vx_typ oc in
let (conn_id, _) := oc in
new_conn_id = conn_id.
Proof.
intros.
rewrite /add_new_vx_connector.
destruct oc as [conn_id number_correct].
unfold output_connector_number_correct in number_correct.
(* The following command always gives a type error.
   I have tried several variants, using find / mem / MapsTo,
   but I could not find a way that avoids the type error.
destruct (module_graph_vertex_set_p.mem (fst conn_id) V).
*)
Admitted.

Lemma add_new_vx_output_connector_type : forall {V : module_graph_vertex_set_p.env} (new_vx_typ: vertex_type) (oc : output_connectors_of_module_graph V),
output_connector_type (module_graph_vertex_set_p.add (module_graph_vertex_set_p.new_key V) new_vx_typ V) (add_new_vx_connector new_vx_typ oc) = output_connector_type V oc.
Proof.
intros.
rewrite /output_connector_type.
destruct oc as [[vx_id conn_nr] number_correct].
unfold output_connector_number_correct, fst in number_correct.
destruct (add_new_vx_connector new_vx_typ
     (exist (fun x : module_graph_vertex_set_p.key * nat => output_connector_number_correct V x)
        (vx_id, conn_nr) number_correct)) as [[vx_id0 conn_nr0] new_number_correct] eqn: H1.
(* Perhaps try one of the following.

destruct (module_graph_vertex_set_p.find vx_id (module_graph_vertex_set_p.add (module_graph_vertex_set_p.new_key V) new_vx_typ V)) eqn: Hfind_new.
destruct (module_graph_vertex_set_p.find vx_id V).


assert (Hfind: exists vx_typ : vertex_type, module_graph_vertex_set_p.find vx_id V = Some vx_typ).
      rewrite /output_connector_number_correct /fst in number_correct.
      destruct (module_graph_vertex_set_p.find vx_id V) eqn: Hfind.
      * exists v ; reflexivity.
      * contradiction.
destruct Hfind as [vx_typ Hfind].

rewrite Hfind in number_correct.
*)
Admitted.

(*
Definition add_new_vx_output_connector_type (V : module_graph_vertex_set_p.env) (new_vx_typ : vertex_type) (oct : output_connector_type V) :
         output_connector_type (module_graph_vertex_set_p.add (module_graph_vertex_set_p.new_key V) new_vx_typ V).
(* The function changes an output_connector_type of V into an output_connector_type of
   (module_graph_vertex_set_p.add (module_graph_vertex_set_p.new_key V) new_vx_typ V). *)
*)

Fixpoint add_new_vx_connection_tree {V: module_graph_vertex_set_p.env} (new_vx_typ : vertex_type) (ct : @connection_tree V) :
         @connection_tree (module_graph_vertex_set_p.add (module_graph_vertex_set_p.new_key V) new_vx_typ V).
(* The function changes a connection tree of V into a connection tree of
   (module_graph_vertex_set_p.add (module_graph_vertex_set_p.new_key V) new_vx_typ V). *)
pose (nV := module_graph_vertex_set_p.add (module_graph_vertex_set_p.new_key V) new_vx_typ V).
destruct ct as [| | |cond cond_is_1bit c1 c2] eqn: Hct.
* exact (@Invalidated nV).
* exact (@Not_connected nV).
* exact (@Leaf nV (add_new_vx_connector new_vx_typ o)).
* pose (new_cond := add_new_vx_connector new_vx_typ cond).
  assert (new_cond_is_1bit: output_connector_type nV new_cond = Fuint_exp 1).
        rewrite /nV /output_connector_type.
        destruct new_cond as [[vx_id conn_nr] number_correct].
(* The following leads to a type error:
        destruct (module_graph_vertex_set_p.find vx_id
                  (module_graph_vertex_set_p.add (module_graph_vertex_set_p.new_key V) new_vx_typ V))
        eqn: Hfind.
*)
Admitted.

Definition module_graph_add (new_vx_id : module_graph_vertex_set_p.key) (new_vx_typ : vertex_type) (mg : module_graph) : module_graph.
destruct mg as [V E].
pose (nV := module_graph_vertex_set_p.add new_vx_id new_vx_typ V).
assert (number_correct: forall ic : input_connectors_of_module_graph nV,
                           match ic with
                           exist (vx_id, conn_nr) _ =>
                              if vx_id == new_vx_id then True else input_connector_number_correct V (vx_id, conn_nr)
                           end).
      intro ; destruct ic as [[vx_id conn_nr] new_number_correct].
      destruct (vx_id == new_vx_id) eqn: vx_id_is_new ; try done.
      rewrite /input_connector_number_correct /nV module_graph_vertex_set_p.find_add_neq in new_number_correct.
      * exact new_number_correct.
      * rewrite /PVM.SE.eq /fst vx_id_is_new //.
(* The following term containing E should be corrected...

pose (nE := fun ic : input_connectors_of_module_graph nV
             => match ic
                   return match ic with exist (vx_id, conn_nr) _
                          => if vx_id == new_vx_id then True else input_connector_number_correct V (vx_id, conn_nr)
                          end -> @connection_tree nV
                with exist (vx_id, conn_nr) _ =>
                   (if vx_id == new_vx_id as b
                       return (if b then True else input_connector_number_correct V (vx_id, conn_nr))
                              -> @connection_tree nV
                    then fun _ => Not_connected
                    else fun number_correct => E (exist (input_connector_number_correct V) (vx_id, conn_nr) number_correct)
                   )
              end (number_correct ic)).
*)
Admitted.

(* add vertices and connection_trees to the module graph following the list of new mux vertices *)
Fixpoint add_vertex_mux' (mg : module_graph) (vl : list vertex_type) (on : (output_connectors_of_module_graph (projT1 mg))) 
   (onl1 : list (output_connectors_of_module_graph (projT1 mg))) (onl2 : list (output_connectors_of_module_graph (projT1 mg))) : 
   option { nmg : module_graph & seq (output_connectors_of_module_graph (projT1 nmg)) } :=
   match vl, onl1, onl2 with
   | nil, nil, nil => Some (existT (fun nmg : module_graph => seq (output_connectors_of_module_graph (projT1 nmg)))
                                   mg nil)
   | Mux ot :: vtl, on1 :: ontl1, on2 :: ontl2 =>
        let V := projT1 mg in
        let mux_id := module_graph_vertex_set_p.new_key V in
        let nV := module_graph_vertex_set_p.add mux_id (Mux ot) V in
        let nct0_number_correct : input_connector_number_correct nV (mux_id, 0) :=
               eq_ind_r (x := Some (Mux ot)) (fun t : option vertex_type
                                               => if t is Some vx_typ then 0 < size (input_connectors vx_typ)
                                                                      else False
                                             ) (let (_,_) as ot return 0 < size (input_connectors (Mux ot)) := ot in is_true_true)
                                             (module_graph_vertex_set_p.find_add_eq (m := V) (x := mux_id) (y := mux_id) (e := Mux ot) (eqxx mux_id)) in
        let nct0 := ct_add (exist (input_connector_number_correct nV) (mux_id, 0) nct0_number_correct) (Leaf (add_new_vx_connector (Mux ot) on)) (projT2 mg) in
        let nct1_number_correct : input_connector_number_correct nV (mux_id, 1) :=
               eq_ind_r (x := Some (Mux ot)) (fun t : option vertex_type
                                               => if t is Some vx_typ then 1 < size (input_connectors vx_typ)
                                                                      else False
                                             ) (let (_,_) as ot return 1 < size (input_connectors (Mux ot)) := ot in is_true_true)
                                             (module_graph_vertex_set_p.find_add_eq (m := V) (x := mux_id) (y := mux_id) (e := Mux ot) (eqxx mux_id)) in
        let nct1 := ct_add (exist (input_connector_number_correct nV) (mux_id, 1) nct1_number_correct) (Leaf (add_new_vx_connector (Mux ot) on1)) nct0 in
        let nct2_number_correct : input_connector_number_correct nV (mux_id, 2) :=
               eq_ind_r (x := Some (Mux ot)) (fun t : option vertex_type
                                               => if t is Some vx_typ then 2 < size (input_connectors vx_typ)
                                                                      else False
                                             ) (let (_,_) as ot return 2 < size (input_connectors (Mux ot)) := ot in is_true_true)
                                             (module_graph_vertex_set_p.find_add_eq (m := V) (x := mux_id) (y := mux_id) (e := Mux ot) (eqxx mux_id)) in
        let nct2 := ct_add (exist (input_connector_number_correct nV) (mux_id, 2) nct2_number_correct) (Leaf (add_new_vx_connector (Mux ot) on2)) nct1 in
        Some (nct2, nil)
   | _, _, _ => None
   end.

Fixpoint list_rhs_expr (e : HiFP.hfexpr) (mg : module_graph) (*cs : list output_connectors) (ts : list output_data_type*) (n : N) : option (list (output_connectors_of_module_graph (projT1 mg)) * ftype * module_graph * N) :=
   (* 
   1. list of output_connectors, which would be connected to the input_connectors of the vertices on the lhs
   2. ftype of the expr, which help produce constraints in the connection. --> should be an aggr type to distinguish UInt[10][2] and UInt[20].
   3. the expanded new module graph, the vertices set and connection tree can be edited.
   4. next identifier for a new vertex. *)
   match e with
   | Econst t bs => match (data_type_in2arith t bs) with
                    | Some arith_typ => 
                           let nv := Constant arith_typ in 
                           let nvmap := module_graph_vertex_set_p.add (n,N0) nv (projT1 mg) in
                           Some ([::(exist (output_connector_number_correct nvmap) ((n,N0), 0) I)], data_type_arith2ftype arith_typ, (nvmap, (projT2 mg)), (N.add n 1%num))
                    | None => None
                     end
   | Ecast c e => match list_rhs_expr e mg n with
                  | Some ([:: eon], ft, nmg, n0) => 
                     match (add_vertex_cast c ft) with 
                     | Some (nv, rft) => 
                        let nvmap := module_graph_vertex_set_p.add (n, N0) nv (projT1 nmg) in
                        let nct0 := ct_add (exist (input_connector_number_correct nvmap) ((n, N0), 0) I) ((Leaf eon) (projT2 nmg)) (projT2 nmg) in

                        (*let (projT2 mg) ((n,N0),0)(* nv的input_connector name *) := Leaf eon in
                           ncncttree := eonl 连接到 (input_connectors nv)*)
                        Some ([::(exist (output_connector_number_correct nvmap) ((n,N0), 0) I)], rft, (nvmap, nct0), (N.add n 1%num))
                     | None => None
                     end
                  | _ => None
                  end
   | Eprim_unop u e => match list_rhs_expr e mg n with
                  | Some ([:: eon], ft, nmg, n0) => 
                     match (add_vertex_unop u ft) with 
                     | Some nv => 
                        match data_type_out2ftype (output_connectors nv) with
                        | Some rft =>
                           let nvmap := module_graph_vertex_set_p.add (n, N0) nv (projT1 nmg) in
                           let nct0 := ct_add (exist (input_connector_number_correct nvmap) ((n, N0), 0) I) ((Leaf eon) (projT2 nmg)) (projT2 nmg) in
                           (*let (projT2 mg) ((n,N0),0)(* nv的input_connector name *) := Leaf eon in
                              ncncttree := eonl 连接到 (input_connectors nv)*)
                           Some ([::(exist (output_connector_number_correct nvmap) ((n,N0), 0) I)], rft, (nvmap, nct0), (N.add n 1%num))
                        | None => None
                        end
                     | None => None
                     end
                  | _ => None
                  end
   | Eprim_binop b e1 e2 => match list_rhs_expr e1 mg n with
                           | Some ([:: eon0], ft0, mg0, n0) => 
                              match list_rhs_expr e2 mg0 n0 with
                              | Some ([:: eon1], ft1, mg1, n1) => 
                                 match (add_vertex_binop b ft0 ft1) with 
                                 | Some nv => 
                                    match data_type_out2ftype (output_connectors nv) with
                                    | Some rft => 
                                       let nvmap := module_graph_vertex_set_p.add (n1, N0) nv (projT1 mg1) in
                                       let nct0 := ct_add (exist (input_connector_number_correct nvmap) ((n1, N0), 0) I) ((Leaf eon0) (projT2 mg1)) (projT2 mmg) in
                                       let nct1 := ct_add (exist (input_connector_number_correct nvmap) ((n1, N0), 1) I) ((Leaf eon1) (projT2 mg1)) nct0 in
                                       (*let (projT2 mg) ((n,N0),0)(* nv的input_connector name *) := Leaf eon0 in
                                       let (projT2 mg) ((n,N0),1)(* nv的input_connector name *) := Leaf eon1 in
                                          ncncttree := eonl 连接到 (input_connectors nv)*)
                                       Some ([::(exist (output_connector_number_correct nvmap) ((n1,N0), 0) I)], rft, (nvmap, nct1), (N.add n 1%num))
                                    | None => None
                                    end
                                 | None => None
                                 end
                              | _ => None
                              end
                           | _ => None 
                           end
   | Eref ref => match list_rhs_ref mg ref tmap with
               | Some (rl, ft) => Some (rl, ft, mg, n)
               | None => None
               end
(*
   | Eref (Eid (p, 0)) => let (keys, _) := List.split (elements (projT1 mg)) (* list (key*value) *) in
                           (* 列出vertices map中已存的vertex identifiers, 在声明该Eid时, 应已展开所有gtyp的(p,0)->(p,1)
                                                                                              和agg的(p,0)->(p,1)..(p,n) *)
                           (* 在已有vertex identifiers中找到所有属于(p,0)的 *)
                          let onl := list_outputs p keys (Some nil) (projT1 mg) in
                          let ty := find (p,0) tmap in (* another parameter is need, a tmap to record the initial ftype of every element. module graph cannot record that. *) 
                          (onl, ty, mg, n)
                          (* Eid/Esubfield/Eindex is then transformed to (p,1)..(p,n) in pass LowerTypes
                             only Eid(p,0) and Esubfield/Eindex here. *)
   | Eref (Esubfield (Eid (p,0)) v) => match find (p,0) tmap with (* the same tmap in Eid *)
                                       | Btyp  => (* ? type of subfield may also be found in tmap *)
                                       | _ => None
                                       end
   | Eref (Esubindex (Eid (p,0)) v) => match find (p,0) tmap with (* the same tmap in Eid *)
                                       | Atyp typ n => if v <= n 
                                                       then (((p, v), 0), typ, mg, n)
                                                       else None (* index greater then the length of aggr_typ *)
                                       | _ => None
                                       end
*)
   | Emux e1 e2 e3 => match list_rhs_expr e1 mg n with
                     | Some ([:: eon1], Gtyp (Fuint 1), mg1, n1) =>
                        match list_rhs_expr e2 mg1 n1 with
                        | Some (eonl2, ft2, mg2, n2) =>
                           match list_rhs_expr e3 mg2 n2 with
                           | Some (eonl3, ft3, mg3, n3) =>
                              match ftype_mux ft2 ft3 with
                              | Some rft => 
                                 let tl1 := vtype_list ft1 nil in (* TODO: Check whether vtype_list is correctly used here *)
                                 let tl2 := vtype_list ft2 nil in
                                 match add_vertex_mux tl1 tl2 with
                                 | Some nvl => match add_vertex_mux' nvl eon1 eonl2 eonl3 mg n with
                                             | Some (rl, nmg, n0) => Some (rl, rft, nmg, 0)
                                             | None => None
                                             end
                                 | None => None
                                 end
                              | None => None
                              end
                           | None => None
                           end
                        | None => None
                        end
                     | _ => None
                     end         
   | _ => None
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
*)


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

Fixpoint Sem_inport (t : ftype) (var : nat) (offset : nat) (V : module_graph_vertex_set_p.env) : bool :=
   (* The predicate returns true if the keys (var, offset), (var, offset + 1), (var, offset + 2), ...
      in map V contain type-correct inports or outports corresponding to type t
      (Non-flipped fields are in-ports, flipped fields are out-ports). *)
   match t with
   | Gtyp t' => match module_graph_vertex_set_p.find (N.of_nat var, N.of_nat offset) V with
                | Some (InPort it) => it == t'
                | _ => false
                end
   | Atyp t' n => [forall i : ordinal n, Sem_inport t' var (offset + (i * size_of_ftype t')) V]
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
   | Atyp t' n => [forall i : ordinal n, Sem_outport t' var (offset + (i * size_of_ftype t')) V]
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

(* fixpoint definition error *)

Fixpoint Add_inport (t : ftype) (var : nat) (offset : nat) (V : module_graph_vertex_set_p.env) : module_graph_vertex_set_p.env :=
   match t with
   | Gtyp t' => module_graph_vertex_set_p.add (N.of_nat var, N.of_nat offset) (InPort t') V 
   | Atyp t' n => (*Add_inport_a t' n var offset V*)    list_repeat_fn (Add_inport t' var offset) n V
   | Btyp ff => Add_inport_fields ff var offset V
   end
(*with Add_inport_a (t : ftype) (n : nat) (var : nat) (offset : nat) (V : module_graph_vertex_set_p.env) : module_graph_vertex_set_p.env :=
   match n with
   | 0 => V
   | S n' => Add_inport_a t n' var offset (Add_inport t var (offset + (n' * size_of_ftype t)) V)
   end.*)


with Add_inport_fields (ff : ffield) (var : nat) (offset : nat) (V : module_graph_vertex_set_p.env) : module_graph_vertex_set_p.env :=
   match ff with
   | Fnil => V
   | Fflips _ Nflip   t' ff' => Add_inport_fields ff' var (offset + size_of_ftype t') (Add_inport t' var offset V)
   | Fflips _ Flipped t' ff' => Add_inport_fields ff' var (offset + size_of_ftype t') (Add_outport t' var offset V)
   end
with Add_outport (t : ftype) (var : nat) (offset : nat) (V : module_graph_vertex_set_p.env) : module_graph_vertex_set_p.env :=
   match t with
   | Gtyp t' => module_graph_vertex_set_p.add (N.of_nat var, N.of_nat offset) (OutPort t') V 
   | Atyp t' n => (*Add_outport_a t' n var offset V*) list_repeat_fn (Add_outport t' var offset) n V
   | Btyp ff => Add_outport_fields ff var offset V
   end
(*with Add_outport_a (t : ftype) (n : nat) (var : nat) (offset : nat) (V : module_graph_vertex_set_p.env) : module_graph_vertex_set_p.env :=
   match n with
   | 0 => V
   | S n' => Add_outport_a t n' var offset (Add_outport t var (offset + (n' * size_of_ftype t)) V)
   end*)
with Add_outport_fields (ff : ffield) (var : nat) (offset : nat) (V : module_graph_vertex_set_p.env) : module_graph_vertex_set_p.env :=
   match ff with
   | Fnil => V
   | Fflips _ Nflip   t' ff' => Add_outport_fields ff' var (offset + size_of_ftype t') (Add_outport t' var offset V)
   | Fflips _ Flipped t' ff' => Add_outport_fields ff' var (offset + size_of_ftype t') (Add_inport t' var offset V)
   end.
   
(*Fixpoint Add_wire
*)

Fixpoint Sem_port (pp : list HiFP.hfport) (V : module_graph_vertex_set_p.env) : bool :=
(* The predicate returns true if the vertex set V conforms to the sequence of ports pp. *)
   match pp with
   | [::] => module_graph_vertex_set_p.is_empty V
   | (Finput var t) :: pp' => (* exists V' : module_graph_vertex_set_p.env,
                                              Sem_port pp' V' && some condition on the difference between V' and V *)
                                  Sem_port pp' (remove_t V (fst var) (size_of_ftype t))
                               && Sem_inport t (fst var) 0 V
   | (Foutput var t) :: pp' =>    Sem_port pp' (remove_t V (fst var) (size_of_ftype t))
                               && Sem_outport t (fst var) 0 V
   end.

Fixpoint Add_ports (pp : list HiFP.hfport) (V : module_graph_vertex_set_p.env) : module_graph_vertex_set_p.env :=
   match pp with
   | [::] => V
   | (Finput v t) :: pp' => let nv := Add_inport t (N.to_nat (fst v)) 0 V in 
                              Add_ports pp' nv
   | (Foutput v t) :: pp' => let nv := Add_outport t (N.to_nat (fst v)) 0 V in 
                              Add_ports pp' nv
   end.

(* Fixpoint Sem_frag (G_old : module_graph) (ss : hfstmt_seq VarOrder.T) (G_new : module_graph) : Prop :=
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
                                                                                         else False => ... p ... vertices_equal ...) (v, n) I))
                           end
                        forall ic : input_connectors_of_module_graph (projT1 G_new),
                           match ic with
                           exist (v, n) p => v is one of the vertices of ref, 
                              module_graph_connection_tree.find ic (projT2 G_new) is Invalidated
   | Swhen cond ss_true ss_false => False
   end.*)

Definition var2exprsmap := module_graph_vertex_set_p.t (seq HiFP.hfexpr). (* key is pair *)  

(*Fixpoint prepro_stmt (st : HiFP.hfstmt) (tmap : ft_pmap) (var2exprs : var2exprsmap) (expli_reg : seq ProdVarOrder.t) : option (ft_pmap * var2exprsmap * seq ProdVarOrder.t) :=
  match st with
  | Sskip => Some (tmap, var2exprs, expli_reg) 
  | Swire v t => let tmap' := ft_add v t tmap in 
                 Some (tmap', var2exprs, expli_reg)
  | Sreg v r => let tmap' := ft_add v (type r) tmap in 
                let var2exprs' := if (reset r) is (Rst rst_sig rst_val) 
                            then module_graph_vertex_set_p.add v (List.cons rst_val nil) var2exprs
                            else var2exprs in
                let expli_reg' := if ftype_not_implicit (type r) then (cons v expli_reg)
                                  else expli_reg in
                 Some (tmap', var2exprs', expli_reg') 
  | Smem v m => (*TBD*) Some (tmap, var2exprs, expli_reg)
  | Sinst v inst => (*TBD*) Some (tmap, var2exprs, expli_reg)
  | Snode v e => let var2exprs' := match module_graph_vertex_set_p.find v var2exprs with
                                | Some ls => module_graph_vertex_set_p.add v (List.cons e ls) var2exprs
                                | None => module_graph_vertex_set_p.add v (List.cons e nil) var2exprs
                                end in
                                Some (tmap, var2exprs', expli_reg)
  | Sfcnct v e => match ref2pvar v tmap with
                  | Some vid => let var2exprs' := match module_graph_vertex_set_p.find vid var2exprs with
                                | Some ls => module_graph_vertex_set_p.add vid (List.cons e ls) var2exprs
                                | None => module_graph_vertex_set_p.add vid (List.cons e nil) var2exprs
                                end in
                                Some (tmap, var2exprs', expli_reg)
                  | None => None
                  end
  | Sinvalid _ => Some (tmap, var2exprs, expli_reg)
  | Swhen _ s1 s2 => match prepro_stmts s1 tmap var2exprs expli_reg with
                    | Some prepro => prepro_stmts s2 (fst (fst prepro)) (snd (fst prepro)) (snd prepro)
                    | None => None
                    end
  end
with prepro_stmts (sts : HiFP.hfstmt_seq) (tmap : ft_pmap) (var2exprs : var2exprsmap) (expli_reg : seq ProdVarOrder.t)
: option (ft_pmap * var2exprsmap * seq ProdVarOrder.t) :=
  match sts with
  | Qnil => Some (tmap, var2exprs, expli_reg)
  | Qcons s ss => match prepro_stmt s tmap var2exprs expli_reg with
                  | Some (tmap', var2exprs', expli_reg') => prepro_stmts ss tmap' var2exprs' expli_reg'
                  | None => None
                  end
  end.

Definition prepro_p (p : HiFP.hfport) (tmap : ft_pmap) : ft_pmap :=
  match p with
  | Finput v t => ft_add v t tmap
  | Foutput v t => ft_add v t tmap
  end.*)

Definition port_tmap (tmap : CEP.t ftype) (p : HiFP.hfport) : CEP.t ftype :=
(* Extend a tmap with one port
   tmap_expli: pair (tmap, names of fully-explicit ports)
   p: port
   output: a pair (tmap with the variables for p added, names of fully-explicit ports (possibly including p))
   This function assumes implicitly that if there is a port identifier (v, n),
   there is no other port with identifier (v, n') that clashes with it (i.e. the difference |n - n'|
   is too small to accommodate the ground-type elements of one of them). *)
match p with
| Finput (v, n) t | Foutput (v, n) t =>
    CEP.add (v, n) t tmap
end.

Definition ports_tmap (ps : seq HiFP.hfport) : CEP.t ftype :=
(* create a tmap containing the variables for the ports in ps *)
seq.foldl port_tmap (CEP.empty ftype) ps.

Fixpoint split_expr (ref_src : HiFP.href) (t : ftype) : option (seq HiFP.href) :=
  match t with
  | Gtyp _ => Some [:: ref_src]
  | Atyp atyp _ => split_expr (Esubindex ref_src 0) atyp
  | Btyp ff => split_expr_f ref_src ff 
  end
with split_expr_f (ref_src : HiFP.href) (ff : ffield) : option (seq HiFP.href) :=
  match ff with
  | Fnil => Some nil
  | Fflips v Nflip t ff' =>
    match split_expr_f ref_src ff', split_expr (Esubfield ref_src v) t with
    | Some ls, Some ls' => Some (ls' ++ ls)
    | _,_ => None
    end
  | Fflips v Flipped t ff' => None
  end.

Fixpoint split_expr_non_passive (ref_src : HiFP.href) (t : ftype) (fl : bool) : option (seq (HiFP.href * bool)) :=
  match t with
  | Gtyp _ => Some [:: (ref_src, fl)]
  | Atyp atyp _ => split_expr_non_passive (Esubindex ref_src 0) atyp fl
  | Btyp ff => split_expr_non_passive_f ref_src ff fl
  end
with split_expr_non_passive_f (ref_src : HiFP.href) (ff : ffield) (fl : bool) : option (seq (HiFP.href * bool)) :=
  match ff with
  | Fnil => Some nil
  | Fflips v Nflip t ff' =>
    match split_expr_non_passive_f ref_src ff' fl, split_expr_non_passive (Esubfield ref_src v) t fl with
    | Some ls, Some ls' => Some (ls' ++ ls)
    | _,_ => None
    end
  | Fflips v Flipped t ff' => 
    match split_expr_non_passive_f ref_src ff' fl, split_expr_non_passive (Esubfield ref_src v) t (~~fl) with
    | Some ls, Some ls' => Some (ls' ++ ls)
    | _,_ => None
    end
  end.

Fixpoint combine_mux_expr (c : HiFP.hfexpr) (el1 el2 : seq HiFP.hfexpr) : option (seq HiFP.hfexpr) :=
  match el1, el2 with
  | nil, nil => Some nil
  | hd1 :: tl1, hd2 :: tl2 => match combine_mux_expr c tl1 tl2 with
                            | Some muxl => Some ((Emux c hd1 hd2) :: muxl)
                            | None => None
                            end
  | _, _ => None
  end.

Fixpoint split_expr_connect (expr_src : HiFP.hfexpr) (t : ftype) : option (seq HiFP.hfexpr) :=
  match expr_src with
  | Eref ref => match split_expr ref t with
                | Some refl => Some (map (fun tref => (Eref tref)) refl)
                | None => None
                end
  | Emux c e1 e2 => match split_expr_connect e1 t, split_expr_connect e2 t with
                  | Some el1, Some el2 => combine_mux_expr c el1 el2
                  | _ ,_ => None
                  end
  | _ => Some [:: expr_src] 
  end.

Fixpoint add_expr_connect (v : ProdVarOrder.t) (el : seq HiFP.hfexpr) (var2exprs : var2exprsmap) : var2exprsmap :=
  match el with
  | nil => var2exprs
  | hd :: tl => match module_graph_vertex_set_p.find v var2exprs with
                | Some ls => add_expr_connect ((fst v), N.add (snd v) 1%num) tl (module_graph_vertex_set_p.add v (hd :: ls) var2exprs)
                | None => add_expr_connect ((fst v), N.add (snd v) 1%num) tl (module_graph_vertex_set_p.add v [::hd] var2exprs)
                end
  end.

Fixpoint add_expr_connect_non_passive (v_lhs v_rhs : ProdVarOrder.t) (el1 el2 : seq (HiFP.href * bool)) (var2exprs : var2exprsmap) : option var2exprsmap :=
  match el1, el2 with
  | nil, nil => Some var2exprs
  | (ref1, false) :: tl1, (ref2, false) :: tl2 => 
                match module_graph_vertex_set_p.find v_lhs var2exprs with
                | Some ls => add_expr_connect_non_passive (fst v_lhs, N.add (snd v_lhs) 1%num) (fst v_rhs, N.add (snd v_rhs) 1%num) tl1 tl2 (module_graph_vertex_set_p.add v_lhs ((Eref ref1) :: ls) var2exprs)
                | None => add_expr_connect_non_passive (fst v_lhs, N.add (snd v_lhs) 1%num) (fst v_rhs, N.add (snd v_rhs) 1%num) tl1 tl2 (module_graph_vertex_set_p.add v_lhs [::(Eref ref1)] var2exprs)
                end
  | (ref1, true) :: tl1, (ref2, true) :: tl2 => 
                match module_graph_vertex_set_p.find v_rhs var2exprs with
                | Some ls => add_expr_connect_non_passive (fst v_lhs, N.add (snd v_lhs) 1%num) (fst v_rhs, N.add (snd v_rhs) 1%num) tl1 tl2 (module_graph_vertex_set_p.add v_rhs ((Eref ref2) :: ls) var2exprs)
                | None => add_expr_connect_non_passive (fst v_lhs, N.add (snd v_lhs) 1%num) (fst v_rhs, N.add (snd v_rhs) 1%num) tl1 tl2 (module_graph_vertex_set_p.add v_rhs [::(Eref ref2)] var2exprs)
                end
  | _, _ => None
  end.

Fixpoint stmt_tmap (t_v : CEP.t ftype * var2exprsmap) (s: HiFP.hfstmt) : option (CEP.t ftype * var2exprsmap) :=
(* t_v is a pair: tmap of components defined before statement s;
                  map that indicates all expressions assigned to a certain ground-type part of a component.
   s is a statement.
   the result is the pair t_v expanded with the information from s *)
match s with
| Sskip => Some t_v
| Swire v t => if CEP.find v (fst t_v) is None
               then Some (CEP.add v t (fst t_v), (snd t_v))
               else None
| Sreg v r => match CEP.find v (fst t_v), reset r with
              | Some _, _ => None
              | None, Rst _ rst_val => match split_expr_connect rst_val (type r) with
                                      | Some rstl => Some (CEP.add v (type r) (fst t_v), add_expr_connect v rstl (snd t_v))
                                      | None => None
                                      end
              | None, NRst => Some (CEP.add v (type r) (fst t_v), (snd t_v))
              end
| Smem v m => (* TBD *) None
| Sinst v inst => (* TBD *) None
| Snode v e =>
    match CEP.find v (fst t_v), type_of_hfexpr e (fst t_v) with
    | None, Some t => match split_expr_connect e t with
                    | Some rstl => Some (CEP.add v t (fst t_v), add_expr_connect v rstl (snd t_v))
                    | None => None
                    end
    | _, _ => None
    end
| Sfcnct ref_tgt (Eref ref_src) =>
    match base_ref ref_tgt (fst t_v), base_ref ref_src (fst t_v) with
    | Some (v_tgt, t_tgt), Some (v_src, t_src) =>
      match split_expr_non_passive ref_tgt t_tgt false, split_expr_non_passive ref_src t_src false with
      | Some lhsl, Some rhsl => match add_expr_connect_non_passive v_tgt v_src lhsl rhsl (snd t_v) with
                                | Some newv2e => Some ((fst t_v), newv2e)
                                | None => None
                                end
      | _, _ => None
      end
    | _, _ => None
    end
| Sfcnct ref_tgt expr_src =>
    match base_ref ref_tgt (fst t_v), type_of_hfexpr expr_src (fst t_v) with
    | Some (v, t_tgt), Some t_src =>
        if connect_type_compatible t_tgt t_src
          then match split_expr_connect expr_src t_src with
          | Some rstl => Some ((fst t_v), add_expr_connect v rstl (snd t_v))
          | None => None
          end
        else None
    | _,_ => None
    end
| Sinvalid _ => Some t_v
| Swhen c ss_t ss_f =>
    match stmts_tmap t_v ss_t with
    | Some t_v' => stmts_tmap t_v' ss_f
    | None => None
    end
end
with stmts_tmap (t_v : CEP.t ftype * var2exprsmap) (ss: HiFP.hfstmt_seq) : option (CEP.t ftype * var2exprsmap) :=
match ss with
| Qnil => Some t_v
| Qcons s ss' =>
    match stmt_tmap t_v s with
    | Some t_v' => stmts_tmap t_v' ss'
    | None => None
    end
end.

Definition Sem (F : HiFP.hfmodule) (vm : module_graph_vertex_set_p.env) (ct : module_graph_connection_trees_p.env) : Prop :=
(* The predicate returns True if G conforms to F.
   (If F has errors, there is no such G.)
   (If F has implicit width components, then there are many such Gs.) *)
   match F with
   | FInmod n pp ss => let tmap := ports_tmap pp in 
                       match stmts_tmap (tmap, module_graph_vertex_set_p.empty (seq HiFP.hfexpr)) ss with 
                     | Some (tmap', _) => exists (vm' : module_graph_vertex_set_p.env) (ct' : module_graph_connection_trees_p.env),
                        Sem_port pp vm' /\ Sem_frag_stmts vm' ct' ss vm ct tmap'
                     | None => False
                     end
   | FExmod _ _ _ => False
   end. 

Definition make_vx_implicit (v : vertex_type) : vertex_type :=
(* change the type in the vertex to an implicit-width type *)
   match v with
   | OutPort it => OutPort (fgtyp_add_implicit it)
   | InPort it => InPort (fgtyp_add_implicit it)
   | Register it => Register (fgtyp_add_implicit it)
   | RegisterReset it tf => RegisterReset (fgtyp_add_implicit it) tf
   | Wire it => Wire (fgtyp_add_implicit it)
   | Node it => Node (fgtyp_add_implicit it)
   | _ => v
   end.

Fixpoint make_gtyp_implicit (vtl : seq fgtyp) (n : nat) (var : N) (vm : module_graph_vertex_set_p.env) : module_graph_vertex_set_p.env :=
(* change the components of element (var, n), (var, n+1), ... (var, n+(size vtl)-1) to implicit-width
   if the corresponding entry in vtl is implicit-width *)
   match vtl with
   | nil => vm
   | v :: tl => if not_implicit v then make_gtyp_implicit tl (n + 1) var vm
                else if module_graph_vertex_set_p.find (var, N.of_nat n) vm is Some value
                     then let vm' := module_graph_vertex_set_p.add (var, N.of_nat n) (make_vx_implicit value) vm in
                          make_gtyp_implicit tl (n + 1) var vm'
                     else make_gtyp_implicit tl (n + 1) var vm (* error *)
   end.

(* Because vtype_list has changed, the following functions do no longer work.

Definition make_p_implicit (vm : module_graph_vertex_set_p.env) (p : HiFP.hfport) : module_graph_vertex_set_p.env :=
(* change the vertices in vm to implicit-width if the corresponding port definition in p is implicit *)
   match p with
   | Finput v t => exists vtl : seq fgtyp,
                         vtype_list t nil vtl
                      /\ make_gtyp_implicit vtl 0 (fst v) vm (* 0: check whether identifier of aggr_typ in module_graph start from 0 or 1 *)
   | Foutput v t => exists vtl : seq fgtyp,
                          vtype_list t nil vtl
                       /\ make_gtyp_implicit vtl 0 (fst v) vm
   end.

Fixpoint make_s_implicit (vm : module_graph_vertex_set_p.env) (st : HiFP.hfstmt) : module_graph_vertex_set_p.env :=
(* change the vertex of statement st in vm to implicit-width if st defines an implicit-width component *)
   match st with
  | Sskip => vm
  | Swire v t => let vtl := vtype_list t nil in
                 make_gtyp_implicit vtl 0 (fst v) vm
  | Sreg v r => let vtl := vtype_list (type r) nil in
                make_gtyp_implicit vtl 0 (fst v) vm
  | Smem v m => (*TBD*) vm
  | Sinst v inst => (*TBD*) vm
  | Swhen _ s1 s2 => make_ss_implicit (make_ss_implicit vm s1) s2
  | _ => vm 
  end
with make_ss_implicit (vm : module_graph_vertex_set_p.env) (ss : HiFP.hfstmt_seq) : module_graph_vertex_set_p.env :=
(* change the vertices of statements ss in vm to implicit-width if ss defines implicit-width components *)
   match ss with
  | Qnil => vm
  | Qcons s st => make_ss_implicit (make_s_implicit vm s) st
  end.

Definition make_vm_implicit (F : HiFP.hfmodule) (vm : module_graph_vertex_set_p.env) : module_graph_vertex_set_p.env :=
   (* in vm, change the type of vertex (explicit to implicit) according to its declaration in F. *)
   match F with
   | FInmod _ pp ss => let vm' := List.fold_left make_p_implicit pp vm in
                       make_ss_implicit vm' ss
   | FExmod _ _ _ => vm
   end.

(*
Theorem ExpandConnect_correct :
(* Proves that ExpandConnect_fun preserves the semantics *)
   forall (F : hfmodule) (G : module_graph),
      F does not contain unspecified widths ->
      match ExpandConnect_fun F with
      | OK F' => Sem F' G <-> Sem F G (* equivalence is ok because F does not contain unspecified widths *)
                 (* Additionally, we might require:
                    /\ F' does not contain aggregate types/connections *)
      | Error _ => True
      end.*)

(* If F allows multiple module graphs G, then it may happen that F' allows fewer module graphs.
   However, as the theorem requires that F does not contain unspecified widths, there should be only one conforming module graph,
   and so the equivalence is ok. *)
*)