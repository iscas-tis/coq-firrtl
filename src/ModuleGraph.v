From mathcomp Require Import ssrbool ssrnat eqtype seq.

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

Definition not_implicit_width (x : input_data_type) :=
   match x with SInt_implicit _ | UInt_implicit _ => False
              | _ => True end.

Definition output_data_type : Type :=
   (* output connectors do not need to store that widths are implicit *)
   { x : input_data_type | not_implicit_width x }.

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

(* should add axioms to state that equality of input_data_type is decidable *)

Inductive vertex_type :=
   (* what kind of vertices can be in the module graph *)
   OutPort : input_data_type (* within the module there is only an input
                                (the output goes to some place outside the module) *) -> vertex_type |
   InPort : output_data_type -> vertex_type |
   Constant : output_data_type -> vertex_type |
   (* register, wire etc. *)
   Adder : arithmetic_data_type (* data type of the input connectors *) -> vertex_type |
   Multiplexer : output_data_type (* data type of the input connectors *) -> vertex_type
   (* actually, more vertex types for every primitive operation *).

(* should add axioms to state that equality of vertex_type is decidable *)

Definition  input_connectors (v : vertex_type) : seq input_data_type :=
   (* calculates the list of data types of input connectors of a vertex.
      It should be a list because the function of different input connectors can be different
      (for example with the adder). *)
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
   | InPort ot => [:: ot]
   | Constant ot => [:: ot]
   | Adder (exist it p) => match it return (match it with | SInt _ | UInt _ => True
                                                          | _ => False end -> seq output_data_type) with
                          | SInt w => fun _ : True => [:: SInt_o (w+1)]
                          | UInt w => fun _ : True => [:: UInt_o (w+1)]
                          | _ => fun p : False => False_rect (seq output_data_type) p (* p is a proof that this cannot happen *)
                          end p
   | Multiplexer ot => [:: ot]
   end.

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
