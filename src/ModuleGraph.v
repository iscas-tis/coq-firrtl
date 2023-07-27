From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import SsrOrder FMaps Var ZAriths.
From Coq Require Import ZArith (* for Nat.eq_dec *).
From firrtl Require Import HiFirrtl. (* for hfmodule and its parts *)

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
   InPort : input_data_type -> vertex_type |
   Constant : arithmetic_data_type -> vertex_type |
   (* register, wire etc. *)

   Cast_UInt : output_data_type -> vertex_type |
   Cast_SInt : output_data_type -> vertex_type |
   Cast_Clock : output_data_type -> vertex_type |
   (*Cast_Reset : output_data_type -> vertex_type |*)
   Cast_Async : output_data_type -> vertex_type |

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
   Invalid : input_data_type(* unknow *) -> vertex_type |
   (*Reference : input_data_type -> vertex_type |*)
   
   Register : input_data_type -> vertex_type |
   Wire : input_data_type -> vertex_type |
   (*memory : ?
   inst : ?*)
   Node : input_data_type -> vertex_type |

   Adder : arithmetic_data_type (* data type of the input connectors *) -> vertex_type |
   Multiplier : arithmetic_data_type (* first factor *) -> nat (* width of second factor *) -> vertex_type |
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
| Adder a, Adder b => a == b
| Multiplier a n, Multiplier b m => (a == b) && (n == m)
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
  destruct y ; try rewrite eq_refl ; try rewrite eq_refl andTb ; apply ReflectT ; try reflexivity.
* rewrite /vertex_type_eqn.
  destruct x, y ; try contradiction ; try (apply ReflectF ; exact H).
  + 1, 2:
    assert (i <> i0) by (contradict H ; rewrite H ; reflexivity) ;
    move /eqP : H0 => H0 ; apply negbTE in H0 ;
    rewrite H0 ; apply ReflectF ; exact H.
  + 3: destruct (n == n0) eqn: Hn.
    4: rewrite andbF ; apply ReflectF ; exact H.
    3: move /eqP : Hn => Hn ; rewrite Hn andbT ; rewrite Hn in H ; clear Hn.
  + 1, 2, 3:
    assert (a <> a0) by (contradict H ; rewrite H ; reflexivity) ;
    move /eqP : H0 => H0 ; apply negbTE in H0 ;
    rewrite H0 ; apply ReflectF ; exact H.
  + assert (o <> o0) by (contradict H ; rewrite H ; reflexivity) ;
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
   | InPort _ => [::] (* An InPort has no input connector because the data comes from somewhere outside the module *)
   | Constant _ => [::]

   | Invalid _ => [::]
   | Register it
   | Wire it
   (* 
   reference it
   memory : ?
   inst : ? *)
   | Node it => [:: it]

   | Cast_UInt (exist it _) => [:: it]
   | Cast_SInt (exist it _) => [:: it]
   | Cast_Clock (exist it _) => [:: it]
   (*| Cast_Reset (exist it _) => [:: it]*)
   | Cast_Async (exist it _) => [:: it]
   | Unop_cvt (exist it _)
   | Unop_neg (exist it _)
   | Unop_not (exist it _)
   | Unop_andr (exist it _)
   | Unop_orr (exist it _)
   | Unop_xorr (exist it _) => [:: it]
   | Unop_pad (*nat*) _ (exist it _) (* ? *)
   | Unop_shl _ (exist it _)
   | Unop_shr _ (exist it _) 
   | Unop_bits _ _ (exist it _) 
   | Unop_head _ (exist it _) 
   | Unop_tail _ (exist it _) => [:: it]
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

   | Adder (exist it _) => [:: it ; it] (* has two inputs of the same data type *)
   | Mux (exist it _) => [:: UInt 1 ; it ; it]
   | _ => [::]
   end.

Definition output_connectors (v : vertex_type) : seq output_data_type :=
   match v with
   | OutPort _ => [::] (* An OutPort has no output connector because the data is sent to somewhere outside the module *)
   | InPort (SInt_implicit w) => [:: SInt_o w]
   | InPort (UInt_implicit w) => [:: UInt_o w]
   | InPort it => [:: exist not_implicit_width it I] (* convert to output_data_type *)
   | Constant (exist (SInt w) _) => [:: SInt_o w]
   | Constant (exist (UInt w) _) => [:: UInt_o w]
   | Constant (exist _ p) => False_rect (seq output_data_type) p (* p is a proof of False, so this cannot happen in reality *)
   
   | Cast_UInt (exist (UInt w) _) => [:: UInt_o w]
   | Cast_UInt (exist (SInt w) _) => [:: UInt_o w]
   | Cast_UInt (exist Clock _) => [:: UInt_o 1]
   | Cast_UInt (exist Reset _) => [:: UInt_o 1]
   | Cast_UInt (exist AsyncReset _) => [:: UInt_o 1]
   | Cast_UInt (exist _ p) => False_rect (seq output_data_type) p
   | Cast_SInt (exist (UInt w) _) => [:: SInt_o w]
   | Cast_SInt (exist (SInt w) _) => [:: SInt_o w]
   | Cast_SInt (exist Clock _) => [:: SInt_o 1]
   | Cast_SInt (exist Reset _) => [:: SInt_o 1]
   | Cast_SInt (exist AsyncReset _) => [:: SInt_o 1]
   | Cast_SInt (exist _ p) => False_rect (seq output_data_type) p
   | Cast_Clock (exist it _) => [:: Clock_o]
   | Cast_Async (exist it _) => [:: AsyncReset_o]
   | Unop_cvt (exist (UInt w) _) => [:: SInt_o (w+1)]
   | Unop_cvt (exist (SInt w) _) => [:: SInt_o (w+1)]
   | Unop_cvt (exist _ p) => False_rect (seq output_data_type) p
   | Unop_neg (exist (UInt w) _) => [:: SInt_o (w+1)]
   | Unop_neg (exist (SInt w) _) => [:: SInt_o (w+1)]
   | Unop_neg (exist _ p) => False_rect (seq output_data_type) p
   | Unop_not (exist (UInt w) _) => [:: UInt_o w]
   | Unop_not (exist (SInt w) _) => [:: UInt_o w]
   | Unop_not (exist _ p) => False_rect (seq output_data_type) p
   | Binop_and (exist (UInt w) _) 
   | Binop_or (exist (UInt w) _) 
   | Binop_xor (exist (UInt w) _) => [:: UInt_o w]
   | Binop_and (exist (SInt w) _) 
   | Binop_or (exist (SInt w) _) 
   | Binop_xor (exist (SInt w) _) => [:: SInt_o w]
   | Binop_or (exist _ p)
   | Binop_xor (exist _ p)
   | Binop_and (exist _ p) => False_rect (seq output_data_type) p
   | Unop_andr (exist it _)
   | Unop_orr (exist it _)
   | Unop_xorr (exist it _) => [:: UInt_o 1]
   | Binop_sub (exist (SInt w) _) => [:: SInt_o (w+1)]
   | Binop_sub (exist (UInt w) _) => [:: UInt_o (w+1)]
   | Binop_sub (exist _ p) => False_rect (seq output_data_type) p (* p is a proof of False, so this cannot happen in reality *)
   | Binop_div (exist (SInt w) _) => [:: SInt_o (w+1)]
   | Binop_div (exist (UInt w) _) => [:: UInt_o (w)]
   | Binop_div (exist _ p) => False_rect (seq output_data_type) p
   | Binop_lt (exist (UInt w) _) 
   | Binop_lt (exist (SInt w) _) 
   | Binop_leq (exist (UInt w) _) 
   | Binop_leq (exist (SInt w) _) 
   | Binop_gt (exist (UInt w) _) 
   | Binop_gt (exist (SInt w) _) 
   | Binop_geq (exist (UInt w) _) 
   | Binop_geq (exist (SInt w) _) 
   | Binop_eq (exist (UInt w) _) 
   | Binop_eq (exist (SInt w) _) 
   | Binop_neq (exist (UInt w) _) 
   | Binop_neq (exist (SInt w) _) => [:: UInt_o 1]
   | Binop_lt (exist _ p) 
   | Binop_leq (exist _ p) 
   | Binop_gt (exist _ p) 
   | Binop_geq (exist _ p) 
   | Binop_eq (exist _ p) 
   | Binop_neq (exist _ p) => False_rect (seq output_data_type) p

   | Invalid (UInt w) => [:: UInt_o w]
   | Invalid (SInt w) => [:: SInt_o w]
   | Invalid Clock => [:: Clock_o]
   | Invalid Reset => [:: Reset_o]
   | Invalid AsyncReset => [:: AsyncReset_o]
   | Invalid _ => (*?*) [::]
   | Register (UInt w) => [:: UInt_o w]
   | Register (SInt w) => [:: SInt_o w]
   | Register Clock => [:: Clock_o]
   | Register Reset => [:: Reset_o]
   | Register AsyncReset => [:: AsyncReset_o]
   | Register _ => (*?*) [::]
   | Wire (UInt w) => [:: UInt_o w]
   | Wire (SInt w) => [:: SInt_o w]
   | Wire Clock => [:: Clock_o]
   | Wire Reset => [:: Reset_o]
   | Wire AsyncReset => [:: AsyncReset_o]
   | Wire _ => (*?*) [::]
   | Node (UInt w) => [:: UInt_o w]
   | Node (SInt w) => [:: SInt_o w]
   | Node Clock => [:: Clock_o]
   | Node Reset => [:: Reset_o]
   | Node AsyncReset => [:: AsyncReset_o]
   | Node _ => (*?*) [::]
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
   | Unop_pad n (exist _ p) => False_rect (seq output_data_type) p
   | Unop_shl n (exist (UInt n1) _) => [:: UInt_o (n + n1)] 
   | Unop_shl n (exist (SInt n1) _) => [:: SInt_o (n + n1)]   
   | Unop_shl n (exist _ p) => False_rect (seq output_data_type) p
   | Unop_shr n (exist (UInt n1) _) => [:: UInt_o (Nat.max (n1 - n) 1)] 
   | Unop_shr n (exist (SInt n1) _) => [:: SInt_o (Nat.max (n1 - n) 1)] 
   | Unop_shr n (exist _ p) => False_rect (seq output_data_type) p
   | Unop_bits hi lo (exist it _) => [:: UInt_o (hi - lo + 1)]
   | Unop_head n (exist it _) => [:: UInt_o n] 
   | Unop_tail n (exist (UInt n1) _) => [:: UInt_o (n1 - n)]
   | Unop_tail n (exist (SInt n1) _) => [:: UInt_o (n1 - n)]
   | Unop_tail n (exist _ p) => False_rect (seq output_data_type) p

   | Adder (exist (SInt w) _) => [:: SInt_o (w+1)]
   | Adder (exist (UInt w) _) => [:: UInt_o (w+1)]
   | Adder (exist _ p) => False_rect (seq output_data_type) p (* p is a proof of False, so this cannot happen in reality *)
   | Multiplier (exist (SInt w) _) n => [:: SInt_o (w+n)]
   | Multiplier (exist (UInt w) _) n => [:: UInt_o (w+n)]
   | Multiplier (exist _ p) _ => False_rect (seq output_data_type) p
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

Definition module_graph_vertices : Type := { V : Set & V -> vertex_type }.
   (* This is a type of pairs consisting of a set and a function from this set to vertex_type.
      Given V : module_graph_vertices, the set is (projT1 V) and the function is (projT2 V).
      I would like V to be a finite set but I don't know exactly how to specify that. *)

Definition output_connectors_of_module_graph (V : module_graph_vertices) : Type :=
   { x : (projT1 V) * nat | snd x < size (output_connectors ((projT2 V) (fst x)))}.
   (* This is a type of pairs, where the first is an element of a module_graph_vertices set,
      and the second of the pair is a natural number that is < than the number of output connectors of that element. *)

Definition output_connector_type (V : module_graph_vertices) (oc : output_connectors_of_module_graph V) : output_data_type :=
   match oc with exist (v, i) _ => nth Reset_o (output_connectors ((projT2 V) v)) i end.

Inductive connection_tree (V: module_graph_vertices) :=
   Invalidated | Not_connected |
   Leaf : (output_connectors_of_module_graph V) -> connection_tree V |
   Choice : {cond : output_connectors_of_module_graph V |
                    output_connector_type V cond = UInt_o 1 }
                    (* the type of cond needs to be UInt_o 1 *)
            -> connection_tree V -> connection_tree V -> connection_tree V.

Definition input_connectors_of_module_graph (V : module_graph_vertices) : Type :=
   { x : (projT1 V) * nat | snd x < size (input_connectors ((projT2 V) (fst x)))}.
   (* This is a set containing pairs, where the first is an element of a module_graph_vertices set,
      and the second of the pair is a natural number that is < than the number of input connectors of that element. *)

Definition input_connector_type (V : module_graph_vertices) (ic : input_connectors_of_module_graph V) : input_data_type :=
   match ic with exist (v, i) _ => nth Reset (input_connectors ((projT2 V) v)) i end.

Definition module_graph_connection_trees (V: module_graph_vertices): Type :=
   input_connectors_of_module_graph V -> connection_tree V.

Definition module_graph : Type :=
   { V : module_graph_vertices & module_graph_connection_trees V }.

(* an example to test the typing ... *)
Definition Adder0 := Adder (exist is_arithmetic (SInt 2) I).

Lemma Adder0_inputs : input_connectors Adder0 = [:: SInt 2; SInt 2].
Proof.  done.  Qed.
Lemma Adder0_outputs : output_connectors Adder0 = [:: SInt_o 3].
Proof.  done.  Qed.

Definition MGV0' := { v : vertex_type | v = Adder0 }.

Check existT.

Definition MGV0 := existT (fun v : MGV0' => v) MGV0'.

(*
Fixpoint trans_expr (e : hfexpr) (G : module_graph) : module_graph :=
*)

(* The following is not syntactically correct, as we haven't included hfmodule completely. *)

Fixpoint Sem (F : hfmodule) (G : module_graph) : bool :=
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
