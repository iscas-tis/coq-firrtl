From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import SsrOrder FMaps Var ZAriths.
From Coq Require Import ZArith (* for Nat.eq_dec *).
From nbits Require Import NBits.
From firrtl Require Import HiFirrtl Firrtl Env HiEnv. (* for hfmodule and its parts *)

(* This file contains first ideas on how to define a module graph as a semantic structure for FIRRTL modules.
   Many definitions are not yet complete but include only a few constructs so as to illustrate what the structure is. *)

Inductive input_data_type :=
   (* data type of the data that can be transmitted through a connection
      This data type allows two constructors SInt_implicit and UInt_implicit that should be used
      if the width of some explicitly typed input connector is implicit.
      For input connectors of primitive operations, which are never explicitly typed,
      it is not needed. *)
   SInt : nat (* number of bits in the signed integer *) -> input_data_type |
   UInt : nat -> input_data_type |
   SInt_implicit : nat (* number of bits that is assumed, but it is implicit *) -> input_data_type |
   UInt_implicit : nat -> input_data_type |
   Reset |
   AsyncReset |
   Clock.

(* equality of input_data_type is decidable *)
Lemma input_data_type_eq_dec : forall {x y : input_data_type}, {x = y} + {x <> y}.
Proof.  decide equality ; apply Nat.eq_dec.  Qed.
Definition input_data_type_eqn (x y : input_data_type) : bool :=
match x, y with
| SInt n, SInt m
| UInt n, UInt m
| SInt_implicit n, SInt_implicit m
| UInt_implicit n, UInt_implicit m => n == m
| Reset, Reset
| AsyncReset, AsyncReset
| Clock, Clock => true
| _, _ => false
end.
Lemma input_data_type_eqP : Equality.axiom input_data_type_eqn.
Proof.
rewrite /Equality.axiom ; intros.
case: (@input_data_type_eq_dec x y) => H.
* rewrite H /input_data_type_eqn ; clear -y.
  destruct y ; try rewrite eq_refl ; apply ReflectT ; reflexivity.
* rewrite /input_data_type_eqn.
  destruct x, y ; try contradiction ; try (apply ReflectF ; exact H) ;
        assert (n <> n0) by (contradict H ; rewrite H ; reflexivity) ;
        move /eqP : H0 => H0 ;
        apply negbTE in H0 ;
        rewrite H0 ; apply ReflectF ; exact H.
Qed.
Canonical input_data_type_eqMixin := EqMixin input_data_type_eqP.
Canonical input_data_type_eqType := Eval hnf in EqType input_data_type input_data_type_eqMixin.

Definition not_implicit_width (x : input_data_type) : Prop :=
   match x with SInt_implicit _ | UInt_implicit _ => False
              | _ => True end.

Definition output_data_type : Type :=
   (* output connectors do not need to store that widths are implicit *)
   { x : input_data_type | not_implicit_width x }.

(* equality of output_data_type is decidable *)
Lemma output_data_type_eq_dec : forall {x y : output_data_type}, {x = y} + {x <> y}.
Proof.
intros.
destruct x, y.
case: (@input_data_type_eq_dec x x0) => H.
* left.
  destruct x, x0 ; try done ; destruct n, n0 ;
        try reflexivity ;
        injection H ; intro ; rewrite H0 ; reflexivity.
* right.
  destruct x, x0 ; try done ;
        injection ; destruct n, n0 ;
        contradict H ; rewrite H ; reflexivity.
Qed.
Definition output_data_type_eqn (x y : output_data_type) : bool :=
match x, y with
exist x' _, exist y' _ => input_data_type_eqn x' y'
end.
Lemma output_data_type_eqP : Equality.axiom output_data_type_eqn.
Proof.
rewrite /Equality.axiom /output_data_type_eqn.
intros.
destruct x, y.
destruct x, x0 ; destruct n, n0 ; simpl input_data_type_eqn ;
     try (apply ReflectF ; discriminate) ;
     try (apply ReflectT ; reflexivity) ;
     destruct (n1 == n2) eqn: Hn1n2.
1, 3: apply ReflectT ;
      move /eqP : Hn1n2 => Hn1n2 ; rewrite Hn1n2 ; reflexivity.
all: apply ReflectF ;
     move /eqP : Hn1n2 => Hn1n2 ; contradict Hn1n2 ;
     injection Hn1n2 ; intro ; done.
Qed.
Canonical output_data_type_eqMixin := EqMixin output_data_type_eqP.
Canonical output_data_type_eqType := Eval hnf in EqType output_data_type output_data_type_eqMixin.

Definition SInt_o (w : nat) : output_data_type :=
   (* convert SInt w to an output_data_type *)
   exist not_implicit_width (SInt w) I.

Definition UInt_o (w : nat) : output_data_type :=
   (* convert UInt w to an output data type *)
   exist not_implicit_width (UInt w) I.

Definition Reset_o : output_data_type :=
   (* convert Reset to an output data type *)
   exist not_implicit_width Reset I.

Definition Clock_o : output_data_type :=
   (* convert Clock to an output data type *)
   exist not_implicit_width Clock I.

Definition AsyncReset_o : output_data_type :=
   (* convert AsyncReset to an output data type *)
   exist not_implicit_width AsyncReset I.

Definition is_arithmetic (x : input_data_type) : Prop :=
   match x with SInt _ | UInt _ => True
              | _ => False end.

Definition arithmetic_data_type : Type :=
   (* data type for arithmetic operations (mainly primitive operations):
      only SInt and UInt are allowed *)
   { x : input_data_type | is_arithmetic x }.

Definition SInt_a (w : nat) : arithmetic_data_type :=
   (* convert SInt w to an arithmetic_data_type *)
   exist is_arithmetic (SInt w) I.

Definition UInt_a (w : nat) : arithmetic_data_type :=
   (* convert UInt w to an arithmetic_data_type *)
   exist is_arithmetic (UInt w) I.

(* equality of arithmetic_data_type is decidable *)
Lemma arithmetic_data_type_eq_dec : forall {x y : arithmetic_data_type}, {x = y} + {x <> y}.
Proof.
intros.
destruct x, y.
case: (@input_data_type_eq_dec x x0) => H.
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
exist x' _, exist y' _ => input_data_type_eqn x' y'
end.
Lemma arithmetic_data_type_eqP : Equality.axiom arithmetic_data_type_eqn.
Proof.
rewrite /Equality.axiom /output_data_type_eqn.
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
   OutPort : input_data_type (* within the module there is only an input
                                (the output goes to some place outside the module) *) -> vertex_type |
   InPort : output_data_type -> vertex_type | (* main moudle only at present *)
   Constant : arithmetic_data_type -> vertex_type |
   (* register, wire etc. *)

   Cast_UInt : output_data_type -> vertex_type |
   Cast_SInt : output_data_type -> vertex_type |
   Cast_Clock : output_data_type (* must be a 1-bit data type *) -> vertex_type |
   (*Cast_Reset : output_data_type -> vertex_type |*)
   Cast_Async : output_data_type (* must be a 1-bit data type *) -> vertex_type |

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
   Invalid : output_data_type(* unknow *) -> vertex_type |
   (*Reference : input_data_type -> vertex_type |*)
   
   Register : input_data_type -> vertex_type |
   Wire : input_data_type -> vertex_type |
   (*memory : ?
   inst : ?*)
   Node : input_data_type -> vertex_type |

   Mux : output_data_type (* data type of the input connectors *) -> vertex_type
   (* actually, more vertex types for every primitive operation *).

(* equality of vertex_type is decidable *)
Lemma vertex_type_eq_dec : forall {x y : vertex_type}, {x = y} + {x <> y}.
Proof.  decide equality ; try apply input_data_type_eq_dec ; try apply output_data_type_eq_dec ; try apply arithmetic_data_type_eq_dec ; apply Nat.eq_dec.  Qed.
Definition vertex_type_eqn (x y : vertex_type) : bool :=
match x, y with
| OutPort i, OutPort j
| InPort i, InPort j => i == j
| Constant a, Constant b

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
  + 1, 2, 38, 39, 40:
    assert (i <> i0) by (contradict H ; rewrite H ; reflexivity) ;
    move /eqP : H0 => H0 ; apply negbTE in H0 ;
    rewrite H0 ; apply ReflectF ; exact H.
  + 2, 3, 4, 5, 35, 36:
    assert (o <> o0) by (contradict H ; rewrite H ; reflexivity) ;
    move /eqP : H0 => H0 ; apply negbTE in H0 ;
    rewrite H0 ; apply ReflectF ; exact H.
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

Definition  input_connectors (v : vertex_type) : seq input_data_type :=
   (* calculates the list of data types of input connectors of a vertex.
      It should be a list because the function of different input connectors can be different
      (for example with the multiplexer). *)
   match v with
   | OutPort it => [:: it]
   | InPort _ (* An InPort has no input connector because the data comes from somewhere outside the module *)
   | Constant _

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
   | Binop_mul (exist (UInt n1) _) n2 
   | Binop_cat (exist (UInt n1) _) n2 
   | Binop_rem (exist (UInt n1) _) n2 => [:: (UInt n1); (UInt n2)]
   | Binop_mul (exist (SInt n1) _) n2 
   | Binop_cat (exist (SInt n1) _) n2 
   | Binop_rem (exist (SInt n1) _) n2 => [:: (SInt n1); (SInt n2)]
   (*| Multiplier (exist (SInt w) _) n => [:: SInt w ; SInt n]
   | Multiplier (exist (UInt w) _) n => [:: UInt w ; UInt n]
   | Multiplier (exist _ p) _ => False_rect (seq input_data_type) p *)
   | Binop_dshl (exist it _) n2
   | Binop_dshr (exist it _) n2 => [:: it; (UInt n2)]

   | Mux (exist it _) => [:: UInt 1 ; it ; it]
   | _ => [::]
   end.

Definition output_connectors (v : vertex_type) : seq output_data_type :=
(* a list of types of the output connectors of a vertex of type v *)
   match v with
   | OutPort _ => [::] (* An OutPort has no output connector because the data is sent to somewhere outside the module *)
   (*| InPort (SInt_implicit w) => [:: SInt_o w]
   | InPort (UInt_implicit w) => [:: UInt_o w]
   | InPort it => [:: exist not_implicit_width it I] (* convert to output_data_type *)
   *)
   | InPort it => [:: it]
   | Constant (exist (SInt w) _) => [:: SInt_o w]
   | Constant (exist (UInt w) _) => [:: UInt_o w]
   | Constant (exist _ p) => False_rect (seq output_data_type) p (* p is a proof of False, so this cannot happen in reality *)

   | Cast_UInt (exist (UInt w) _)
   | Cast_UInt (exist (SInt w) _) => [:: UInt_o w]
   | Cast_UInt (exist Clock _)
   | Cast_UInt (exist Reset _)
   | Cast_UInt (exist AsyncReset _) => [:: UInt_o 1]
   | Cast_UInt (exist _ p) => False_rect (seq output_data_type) p
   | Cast_SInt (exist (UInt w) _)
   | Cast_SInt (exist (SInt w) _) => [:: SInt_o w]
   | Cast_SInt (exist Clock _)
   | Cast_SInt (exist Reset _)
   | Cast_SInt (exist AsyncReset _) => [:: SInt_o 1]
   | Cast_SInt (exist _ p) => False_rect (seq output_data_type) p
   | Cast_Clock _ => [:: Clock_o]
   | Cast_Async _ => [:: AsyncReset_o]
   | Unop_cvt (exist (UInt w) _) => [:: SInt_o (w+1)]
   | Unop_cvt (exist (SInt w) _) => [:: SInt_o w]
   | Unop_cvt (exist _ p) => False_rect (seq output_data_type) p
   | Unop_neg (exist (UInt w) _) => [:: SInt_o (w+1)]
   | Unop_neg (exist (SInt w) _) => [:: SInt_o (w+1)]
   | Unop_neg (exist _ p) => False_rect (seq output_data_type) p
   | Unop_not (exist (UInt w) _)
   | Unop_not (exist (SInt w) _) => [:: UInt_o w]
   | Unop_not (exist _ p) => False_rect (seq output_data_type) p
   | Binop_and (exist (UInt w) _) 
   | Binop_or (exist (UInt w) _) 
   | Binop_xor (exist (UInt w) _)
   | Binop_and (exist (SInt w) _) 
   | Binop_or (exist (SInt w) _) 
   | Binop_xor (exist (SInt w) _) => [:: UInt_o w]
   | Binop_or (exist _ p)
   | Binop_xor (exist _ p)
   | Binop_and (exist _ p) => False_rect (seq output_data_type) p
   | Unop_andr _
   | Unop_orr _
   | Unop_xorr _ => [:: UInt_o 1]
   | Binop_add (exist (SInt w) _)
   | Binop_sub (exist (SInt w) _) => [:: SInt_o (w+1)]
   | Binop_add (exist (UInt w) _)
   | Binop_sub (exist (UInt w) _) => [:: UInt_o (w+1)]
   | Binop_add (exist _ p)
   | Binop_sub (exist _ p) => False_rect (seq output_data_type) p (* p is a proof of False, so this cannot happen in reality *)
   | Binop_div (exist (SInt w) _) => [:: SInt_o (w+1)]
   | Binop_div (exist (UInt w) _) => [:: UInt_o (w)]
   | Binop_div (exist _ p) => False_rect (seq output_data_type) p
   | Binop_lt (exist (UInt _) _)
   | Binop_lt (exist (SInt _) _)
   | Binop_leq (exist (UInt _) _)
   | Binop_leq (exist (SInt _) _)
   | Binop_gt (exist (UInt _) _)
   | Binop_gt (exist (SInt _) _)
   | Binop_geq (exist (UInt _) _)
   | Binop_geq (exist (SInt _) _)
   | Binop_eq (exist (UInt _) _)
   | Binop_eq (exist (SInt _) _)
   | Binop_neq (exist (UInt _) _)
   | Binop_neq (exist (SInt _) _) => [:: UInt_o 1]
   | Binop_lt (exist _ p)
   | Binop_leq (exist _ p)
   | Binop_gt (exist _ p)
   | Binop_geq (exist _ p)
   | Binop_eq (exist _ p)
   | Binop_neq (exist _ p) => False_rect (seq output_data_type) p

   | Invalid ot => [:: ot]
   | Register (UInt w) | Register (UInt_implicit w) => [:: UInt_o w]
   | Register (SInt w) | Register (SInt_implicit w) => [:: SInt_o w]
   | Register Clock => [:: Clock_o]
   | Register Reset => [:: Reset_o]
   | Register AsyncReset => [:: AsyncReset_o]
   | Wire (UInt w) | Wire (UInt_implicit w) => [:: UInt_o w]
   | Wire (SInt w) | Wire (SInt_implicit w) => [:: SInt_o w]
   | Wire Clock => [:: Clock_o]
   | Wire Reset => [:: Reset_o]
   | Wire AsyncReset => [:: AsyncReset_o]
   | Node (UInt w) | Node (UInt_implicit w) => [:: UInt_o w]
   | Node (SInt w) | Node (SInt_implicit w) => [:: SInt_o w]
   | Node Clock => [:: Clock_o]
   | Node Reset => [:: Reset_o]
   | Node AsyncReset => [:: AsyncReset_o]
   (* 
   reference it
   memory : ?
   inst : ? *)

   | Binop_mul (exist (UInt n1) _) n2 => [:: UInt_o (n1 + n2)]   
   | Binop_mul (exist (SInt n1) _) n2 => [:: SInt_o (n1 + n2)]
   | Binop_cat (exist (UInt n1) _) n2 => [:: UInt_o (n1 + n2)]   
   | Binop_cat (exist (SInt n1) _) n2 => [:: SInt_o (n1 + n2)]   
   | Binop_rem (exist (UInt n1) _) n2 => [:: UInt_o (Nat.min n1 n2)]
   | Binop_rem (exist (SInt n1) _) n2 => [:: SInt_o (Nat.min n1 n2)]
   | Binop_rem (exist _ p) _ => False_rect (seq output_data_type) p
   | Binop_dshl (exist (UInt n1) _) n2 => [:: UInt_o (n1 + (Nat.pow 2 n2) -1)] 
   | Binop_dshl (exist (SInt n1) _) n2 => [:: SInt_o (n1 + (Nat.pow 2 n2) -1)]   
   | Binop_dshr (exist (UInt n1) _) n2 => [:: UInt_o n1]
   | Binop_dshr (exist (SInt n1) _) n2 => [:: SInt_o n1]
   | Binop_cat (exist _ p) _
   | Binop_dshl (exist _ p) _
   | Binop_dshr (exist _ p) _
   | Binop_mul (exist _ p) _ => False_rect (seq output_data_type) p
   | Unop_pad n (exist (UInt n1) _) => [:: UInt_o (Nat.max n n1)]   
   | Unop_pad n (exist (SInt n1) _) => [:: SInt_o (Nat.max n n1)]   
   | Unop_pad _ (exist _ p) => False_rect (seq output_data_type) p
   | Unop_shl n (exist (UInt n1) _) => [:: UInt_o (n + n1)] 
   | Unop_shl n (exist (SInt n1) _) => [:: SInt_o (n + n1)]   
   | Unop_shl _ (exist _ p) => False_rect (seq output_data_type) p
   | Unop_shr n (exist (UInt n1) _) => [:: UInt_o (Nat.max (n1 - n) 1)] 
   | Unop_shr n (exist (SInt n1) _) => [:: SInt_o (Nat.max (n1 - n) 1)] 
   | Unop_shr _ (exist _ p) => False_rect (seq output_data_type) p
   | Unop_bits hi lo (exist it _) => [:: UInt_o (hi - lo + 1)]
   | Unop_head n (exist it _) => [:: UInt_o n] 
   | Unop_tail n (exist (UInt n1) _) => [:: UInt_o (n1 - n)]
   | Unop_tail n (exist (SInt n1) _) => [:: UInt_o (n1 - n)]
   | Unop_tail _ (exist _ p) => False_rect (seq output_data_type) p

   | Mux ot => [:: ot]
   end.

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

(* Xiaomu, please complete this definition of FMap. *)

From Coq Require Import FMaps.

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
Definition output_connectors_of_module_graph (V : module_graph_vertex_set) : Type :=
   { x : (projT1 V) * nat | snd x < size (output_connectors ((projT2 V) (fst x)))}.
   (* This is a type of pairs, where the first is an element of a module_graph_vertices set,
      and the second of the pair is a natural number that is < than the number of output connectors of that element. *)

Definition output_connector_type (V : module_graph_vertex_set) (oc : output_connectors_of_module_graph V) : output_data_type :=
   match oc with exist (v, i) _ => nth i (output_connectors ((projT2 V) v)) Reset_o end.

Inductive connection_tree (V: module_graph_vertex_set) :=
   Invalidated | Not_connected |
   Leaf : (output_connectors_of_module_graph V) -> connection_tree V |
   Choice : {cond : output_connectors_of_module_graph V |
                    output_connector_type V cond = UInt_o 1 }
                    (* the type of cond needs to be UInt_o 1 *)
            -> connection_tree V -> connection_tree V -> connection_tree V.

Definition input_connectors_of_module_graph (V : module_graph_vertex_set) : Type :=
   { x : (projT1 V) * nat | snd x < size (input_connectors ((projT2 V) (fst x)))}.
   (* This is a set containing pairs, where the first is an element of a module_graph_vertices set,
      and the second of the pair is a natural number that is < than the number of input connectors of that element. *)

Definition input_connector_type (V : module_graph_vertex_set) (ic : input_connectors_of_module_graph V) : input_data_type :=
   match ic with exist (v, i) _ => nth i (input_connectors ((projT2 V) v)) Reset end.

Definition module_graph_connection_trees (V: module_graph_vertex_set): Type :=
   input_connectors_of_module_graph V -> connection_tree V.

Definition module_graph : Type :=
(* a pair, namely a set of module_graph_vertices, together with a mapping that gives a connection tree
for every input connector of every module_graph_vertex. *)
   { V : module_graph_vertex_set & module_graph_connection_trees V }.

(* an example to test the typing ... *)
Definition Adder0 := Binop_add (exist is_arithmetic (SInt 2) I).

Lemma Adder0_inputs : input_connectors Adder0 = [:: SInt 2; SInt 2].
Proof.  done.  Qed.
Lemma Adder0_outputs : output_connectors Adder0 = [:: SInt_o 3].
Proof.  done.  Qed.

Definition MGV0' := { v : vertex_type | v = Adder0 }.

Definition MGV0 := existT (fun v : MGV0' => v) MGV0'.


(* module_graph_vertex_set_p : pair identifier -> vertex_type *)
(* 
  Inductive fgtyp : Set :=
    Fuint : nat -> fgtyp
  | Fsint : nat -> fgtyp
  | Fclock
  | Freset (* HiFIRRTL only *)
  | Fasyncreset.

  Inductive ftype : Type :=
   | Gtyp : fgtyp -> ftype
   | Atyp : ftype -> nat -> ftype
   | Btyp : ffield -> ftype

   with ffield : Type :=
   | Fnil : ffield
   | Fflips : var -> fflip -> ftype -> ffield -> ffield.

Definition type_of_cmpnttyp ct :=
    match ct with
    | Aggr_typ t => t
    | Reg_typ r => type r
    | Mem_typ m => data_type m
    | Unknown_typ => Gtyp (Fuint 0)
    end. *)

Inductive vtype : Type :=
   | vGtyp : input_data_type -> vtype
   | vAtyp : vtype -> nat -> vtype
   | vBtyp : vfield -> vtype 
   with vfield : Type :=
   | vFnil : vfield
   | vFflips : pvar -> fflip -> vtype -> vfield -> vfield.

(*Definition ftype2output_data_type (ft : ftype) : output_data_type :=
   match ft with
   | Gtyp (Fuint n) => UInt_o n 
   | Gtyp (Fsint n) => SInt_o n 
   | Gtyp Fclock => Clock_o
   | Gtyp Freset => Reset_o
   | Gtyp Fasyncreset => AsyncReset_o
   | _ => UInt_o 0
   end.

Definition ftype2input_data_type (ft : ftype) : input_data_type :=
   match ft with
   | Gtyp (Fuint 0) => UInt_implicit ?
   | Gtyp (Fuint n) => UInt n 
   | Gtyp (Fsint n) => SInt n 
   | Gtyp Fclock => Clock
   | Gtyp Freset => Reset
   | Gtyp Fasyncreset => AsyncReset
   | _ => UInt 0
   end.
*)

Inductive hfport : Type :=
| Finput : pvar -> vtype -> hfport
| Foutput : pvar -> vtype -> hfport.

Inductive hfexpr : Type :=
| Econst : input_data_type -> bits -> hfexpr
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
.

Fixpoint list_repeat_fn (f : list input_data_type -> list input_data_type) (n : nat) (l : list input_data_type) : list input_data_type :=
   match n with
   | 0 => l
   | S m => list_repeat_fn f m (f l)
   end.

Fixpoint vtype_list (ft : vtype) (l : list input_data_type) : list input_data_type :=
   match ft with
   | vGtyp t => rcons l t
   | vAtyp t n => list_repeat_fn (vtype_list t) n l
   | vBtyp b => vtype_list_btyp b l
   end
   with vtype_list_btyp (b : vfield) (l : list input_data_type) : list input_data_type :=
   match b with
   | vFnil => l
   | vFflips v fl t fs => vtype_list_btyp fs (vtype_list t l)
   end.

Definition data_type_in2out (dt : input_data_type) : output_data_type :=
   match dt with
   | SInt n => SInt_o n 
   | UInt n => UInt_o n 
   | Reset => Reset_o
   | AsyncReset => AsyncReset_o
   | Clock => Clock_o
   | SInt_implicit _ 
   | UInt_implicit _ => UInt_o 0
   end.

Definition data_type_out2in (dt : output_data_type) : input_data_type :=
   match dt with
   | _ => UInt 0
   end.

Definition data_type_out2arith (dt : output_data_type) : arithmetic_data_type :=
   match dt with
   | _ => UInt_a 0
   (* 
   SInt_o n => SInt n 
   | UInt_o n => UInt n 
   | Reset_o => Reset
   | AsyncReset_o => AsyncReset
   | Clock_o => Clock
   *)
   end.

Fixpoint add_vertex_input (v : N (*pvar match(_,0)从(_,1)开始添加*)) (n : N (*index*)) (l: list input_data_type) (vmap : module_graph_vertex_set_p.env) :=
   match l with
   | nil => vmap
   | hd :: tl => let ohd := data_type_in2out hd in
                 let nvmap := module_graph_vertex_set_p.add (v, n) (InPort ohd) vmap in
                 add_vertex_input v (N.add n 1) tl nvmap
   end.

Fixpoint add_vertex_output (v : N) (N : N) (l: list input_data_type) (vmap : module_graph_vertex_set_p.env) :=
   match l with
   | nil => vmap
   | hd :: tl => let nvmap := module_graph_vertex_set_p.add (v, N) (OutPort hd) vmap in
                 add_vertex_output v (N.add N 1) tl nvmap
   end.

Definition add_vertex_port (p : hfport) (vmap : module_graph_vertex_set_p.env) : module_graph_vertex_set_p.env :=
   match p with
   | Finput (v,_) t => let vtl := vtype_list t nil in
                        add_vertex_input v 1 vtl vmap 
   | Foutput (v,_) t => let vtl := vtype_list t nil in
                        add_vertex_output v 1 vtl vmap 
   end.

(*Fixpoint add_vertex_asuint (v : N) (N : N) (l: list output_data_type) (vmap : module_graph_vertex_set_p.env) :=
   match l with
   | nil => vmap
   | hd :: tl => let nvmap := module_graph_vertex_set_p.add (v, N) (Cast_UInt hd) vmap in
                 add_vertex_asuint v (N.add N 1) tl nvmap
   end.

Fixpoint add_vertex_assint (v : N) (N : N) (l: list output_data_type) (vmap : module_graph_vertex_set_p.env) :=
   match l with
   | nil => vmap
   | hd :: tl => let nvmap := module_graph_vertex_set_p.add (v, N) (Cast_SInt hd) vmap in
                 add_vertex_assint v (N.add N 1) tl nvmap
   end.

Fixpoint add_vertex_asclock (v : N) (N : N) (l: list output_data_type) (vmap : module_graph_vertex_set_p.env) :=
   match l with
   | nil => vmap
   | hd :: tl => let nvmap := module_graph_vertex_set_p.add (v, N) (Cast_Clock hd) vmap in
                 add_vertex_asclock v (N.add N 1) tl nvmap
   end.

Fixpoint add_vertex_asasync (v : N) (N : N) (l: list output_data_type) (vmap : module_graph_vertex_set_p.env) :=
   match l with
   | nil => vmap
   | hd :: tl => let nvmap := module_graph_vertex_set_p.add (v, N) (Cast_Async hd) vmap in
                 add_vertex_asasync v (N.add N 1) tl nvmap
   end.*)

Fixpoint list_inputs (p : N) (n : N) (counts : nat) (l : list input_data_type) (vmap : module_graph_vertex_set_p.env) : list input_data_type :=
   match counts with 
   | 0 => l
   | S m => match (module_graph_vertex_set_p.find (p, N.of_nat (n - m)) vmap) with
            | Some v => l ++ (input_connectors v) ++ list_inputs p n m l vmap
            | None => l ++ list_inputs p n m l vmap
            end
   end. (* return 从(p,1)到(p,n)的input_connectors *)

Fixpoint list_outputs (p : N) (n : N) (counts : nat) (l : list output_data_type) (vmap : module_graph_vertex_set_p.env) : list output_data_type :=
   match counts with 
   | 0 => l
   | S m => match (module_graph_vertex_set_p.find (p, N.of_nat (n - m)) vmap) with
            | Some v => l ++ (output_connectors v) ++ list_outputs p n m l vmap
            | None => l ++ list_outputs p n m l vmap
            end
   end. (* return 从(p,1)到(p,n)的output_connectors *)

Definition add_vertex_cast (c : ucast) (v : N) (l: list output_data_type) (vmap : module_graph_vertex_set_p.env) :=
   match c with
   | AsUInt => module_graph_vertex_set_p.add (v, N0) (Cast_UInt (List.hd (UInt_o 0) l)) vmap
   | AsSInt => module_graph_vertex_set_p.add (v, N0) (Cast_SInt (List.hd (SInt_o 0) l)) vmap
   | AsClock => module_graph_vertex_set_p.add (v, N0) (Cast_Clock (List.hd Clock_o l)) vmap
   | AsAsync => module_graph_vertex_set_p.add (v, N0) (Cast_Async (List.hd AsyncReset_o l)) vmap
   | AsReset => vmap(*? spec 中没有了*)
   end.

Definition add_vertex_unop (u : unop) (v : N) (l: list output_data_type) (vmap : module_graph_vertex_set_p.env) :=
   match u with
  | Upad n => module_graph_vertex_set_p.add (v, N0) (Unop_pad n (List.hd (UInt_o 0) l)) vmap
  | Ushl n =>
  | Ushr n =>
  | Ucvt =>
  | Uneg
  | Unot
  | Uandr
  | Uorr
  | Uxorr
  | Uextr hi lo =>
  | Uhead n =>
  | Utail n =>
   end.

Fixpoint list_rhs_expr (e : hfexpr) (vmap : module_graph_vertex_set_p.env) (es : list output_connectors) (n : N) : list output_connectors * G * N :=
   match e with
   | Econst t bs => if t 是explicit, rcons es t 
                    else 用bs推出长度, 转换data_type
   | Eref (Eid (p, 0)) => let (keys, _) := List.split (elements vmap) (* list (key*value) *) in
                          let n := List.length (fst (List.split keys)) in
                          list_outputs p n 0 nil
   | Eref (Eid pv) => match (find pv vmap) with
                     | Some v => output_connectors v
                     | None => [::]
                     end

   | Ecast c e => let vtl := e 的 output_connectors 的typelist in 
                  let nvmap := add_vertex_cast c n vtl vmap in
                  let ncncttree := e 的output_connectors 连接到 (n,0) ... in
                  ((n,0)的output_connector list, (nvmap, ncncttree), (N.add N 1))
   | Eprim_unop u e => 同上 add_vertex_unop

   | Eprim_binop b e1 e2 =>
   | Emux e1 e2 e3 =>
   end.

Fixpoint list_lhs_expr (e : hfexpr) (vmap : module_graph_vertex_set_p) (es : seq input_connectors) : seq input_connectors :=
   match e with
   | Econst _ _ => [::]
   | Eref (Eid (p, 0)) => let (keys, _) := List.split (elements vmap) (* list (key*value) *) in
                          let n := List.length (fst (List.split keys)) in
                          list_inputs p n 0 nil
   | Eref (Eid pv) => match (find pv vmap) with
                     | Some v => input_connectors v
                     | None => [::]
                     end
   | Ecast c e => let  
   
   -> hfexpr -> hfexpr
| Eprim_unop : eunop -> hfexpr -> hfexpr
| Eprim_binop : ebinop -> hfexpr -> hfexpr -> hfexpr
| Emux : hfexpr -> hfexpr -> hfexpr -> hfexpr
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



(* The following is not syntactically correct, as we haven't included hfmodule completely. *)

Fixpoint Sem (F : hfmodule) (G : module_graph) : bool :=
(* Indicates whether G conforms to F.
   (If F has errors, there is no such G.)
   (If F has implicit width components, then there are many such Gs.) *)

(* David will try to add something here. *)

   (* module graph G is a possible semantics of FIRRTL module F *)
   match F with
   | FInMod _ [::] [::] => Empty (projT1 G) (* G has no vertices *)
   | FInMod name (p :: pp) [::] => exists G' : module_graph, Sem (FInMod name pp [::]) G'
                                                             /\ the name of p is different from names in G'
                                                             /\ projT1 G = projT1 G' :+ p
                                                             /\ forall ic : input_connectors_of_module_graph (projT1 G), projT2 G ic = Not_connected
   | FInMod name ports (Qcons s ss) => exists G' : module_graph, Sem (FInMod name ports ss) G'
                                                                 /\ the difference between G' and G is the translation of s
     (* I think in the inductive statement above it would be easier if we could use Qrcons instead of Qcons. *)
   | FExMod _ _ _ => false
   end.

Theorem ExpandConnect_correct :
   forall (F : hfmodule) (G : module_graph),
      F does not contain unspecified widths ->
      match ExpandConnect_fun F with
      | OK F' => Sem F' G <-> Sem F G.
      | Error _ => true
      end.

(* If F allows multiple module graphs G, then it may happen that F' allows fewer module graphs. *)
