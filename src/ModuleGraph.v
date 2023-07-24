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
  destruct x, x0 ; try done ;
        simpl not_implicit_width in n, n0 ; destruct n0, n ;
        try reflexivity ;
        injection H ; intro ; rewrite H0 ; reflexivity.
* right.
  destruct x, x0 ; try done ;
        simpl not_implicit_width in n, n0 ;
        injection ; destruct n0, n ;
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
destruct x, x0 ; simpl not_implicit_width in n, n0 ; destruct n, n0 ; simpl input_data_type_eqn ;
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

Definition arithmetic_data_type : Type :=
   (* data type for arithmetic operations (mainly primitive operations):
      only SInt and UInt are allowed *)
   { x : input_data_type | match x with SInt _ | UInt _ => True
                                      | _ => False end }.

(* equality of arithmetic_data_type is decidable *)
Lemma arithmetic_data_type_eq_dec : forall {x y : arithmetic_data_type}, {x = y} + {x <> y}.
Proof.
intros.
destruct x, y.
case: (@input_data_type_eq_dec x x0) => H.
* left.
  destruct x, x0 ; try done ;
        injection H ; intro ; rewrite H0 ;
        destruct y0, y ; reflexivity.
* right.
  destruct x, x0 ; try done ;
        injection ; destruct y0, y ;
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
destruct x, x0 ; destruct y, y0 ; simpl arithmetic_data_type_eqn ;
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
   Adder : arithmetic_data_type (* data type of the input connectors *) -> vertex_type |
   Multiplexer : output_data_type (* data type of the input connectors *) -> vertex_type
   (* actually, more vertex types for every primitive operation *).

(* equality of vertex_type is decidable *)
Lemma vertex_type_eq_dec : forall {x y : vertex_type}, {x = y} + {x <> y}.
Proof.  decide equality ; try apply input_data_type_eq_dec ; try apply output_data_type_eq_dec ; try apply arithmetic_data_type_eq_dec.  Qed.
Definition vertex_type_eqn (x y : vertex_type) : bool :=
match x, y with
| OutPort i, OutPort j
| InPort i, InPort j => i == j
| Constant a, Constant b
| Adder a, Adder b => a == b
| Multiplexer o, Multiplexer w => o == w
| _, _ => false
end.
Lemma vertex_type_eqP : Equality.axiom vertex_type_eqn.
Proof.
rewrite /Equality.axiom ; intros.
case: (@vertex_type_eq_dec x y) => H.
* rewrite H /vertex_type_eqn ; clear -y.
  destruct y ; try rewrite eq_refl ; apply ReflectT ; reflexivity.
* rewrite /vertex_type_eqn.
  destruct x, y ; try contradiction ; try (apply ReflectF ; exact H).
  - 1, 2:
    assert (i <> i0) by (contradict H ; rewrite H ; reflexivity) ;
    move /eqP : H0 => H0 ; apply negbTE in H0 ;
    rewrite H0 ; apply ReflectF ; exact H.
  - 1, 2:
    assert (a <> a0) by (contradict H ; rewrite H ; reflexivity) ;
    move /eqP : H0 => H0 ; apply negbTE in H0 ;
    rewrite H0 ; apply ReflectF ; exact H.
  - assert (o <> o0) by (contradict H ; rewrite H ; reflexivity) ;
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
   | Adder (exist it _) => [:: it ; it] (* has two inputs of the same data type *)
   | Multiplexer (exist it _) => [:: UInt 1 ; it ; it]
   end.

Definition output_connectors (v : vertex_type) : seq output_data_type :=
   match v with
   | OutPort _ => [::] (* An OutPort has no output connector because the data is sent to somewhere outside the module *)
   | InPort (SInt_implicit w) => [:: SInt_o w]
   | InPort (UInt_implicit w) => [:: UInt_o w]
   | InPort it => [:: exist not_implicit_width it I] (* convert to output_data_type *)
   | Constant (exist (SInt w) _) => [:: SInt_o w]
   | Constant (exist (UInt w) _) => [:: UInt_o w]
   | Constant (exist _ p) => False_rect (seq output_data_type) p (* p is a proof that this cannot happen *)
   | Adder (exist (SInt w) _) => [:: SInt_o (w+1)]
   | Adder (exist (UInt w) _) => [:: UInt_o (w+1)]
   | Adder (exist _ p) => False_rect (seq output_data_type) p (* p is a proof that this cannot happen *)
   | Multiplexer ot => [:: ot]
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
