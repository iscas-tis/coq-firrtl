From Coq Require Import BinNat ZArith.
From mathcomp Require Import ssreflect ssrbool eqtype seq fintype ssrnat div ssrfun.
From simplssrlib Require Import SsrOrder Var FMaps.
From firrtl Require Import Env Firrtl HiEnv HiFirrtl.

(* From Coq Require Import FunInd FMaps FMapAVL OrderedType ZArith.
From mathcomp Require Import ssrnat ssrint seq ssrfun.
From simplssrlib Require Import Types FSets FMaps Tactics Store.
From nbits Require Import NBits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits. *)

Include HiF.

(* DNJ: What follows is my proposal for error handling:
   a type that can store either an error message or some result. *)

Inductive error_info : Type :=
   | Esyntax (* syntax error *)
   | Etype (* a component of a different type is expected *)
   | Eflow_direction (* the component has the wrong flow direction, e.g. it is not passive while this is required *)
   | Euninitialized (* a component should be connected but isn't *)
   | Einternal (* e.g. if a pass receives input that should have been handled by earlier passes *)
   | Eunimplemented (* some functionality has not been implemented, e.g. external modules are not hadnled *)
   | Eundeclared (* a module (or component) should be declared but isn't *)
   | Ealready_declared
   .

   Lemma error_info_eq_dec : forall {x y : error_info}, {x = y} + {x <> y}.
   Proof. decide equality. Qed.
   Definition error_info_eqn (x y : error_info) : bool :=
   match x, y with Esyntax, Esyntax | Etype, Etype | Eflow_direction, Eflow_direction | Euninitialized, Euninitialized
   | Einternal, Einternal | Eunimplemented, Eunimplemented | Eundeclared, Eundeclared | Ealready_declared, Ealready_declared => true
   | _, _ => false end.
   Lemma error_info_eqP : Equality.axiom error_info_eqn.
   Proof. unfold Equality.axiom.
   induction x, y ; try (apply ReflectF ; discriminate) ; try (apply ReflectT ; reflexivity). Qed.
   Canonical error_info_eqMixin := EqMixin error_info_eqP.
   Canonical error_info_eqType := Eval hnf in EqType error_info error_info_eqMixin.

Inductive error_type {T : Type} : Type :=
   | OK : T -> error_type
   | Err : error_info -> error_type
   .

   Lemma error_type_eq_dec {T: eqType} : forall (x y: @error_type T), {x = y} + {x <> y}.
   Proof. decide equality.
   * case (t == s) eqn: Ht.
     1,2: move /eqP : Ht => Ht.
     + left ; exact Ht.
     + right ; exact Ht.
   * apply error_info_eq_dec.
   Qed.
   Definition error_type_eqn {T : eqType} (x y : @error_type T) : bool :=
   match x, y with OK t, OK s => t == s
                 | Err e, Err f => e == f
                 | _, _ => false end.
   Lemma error_type_eqP {T : eqType} : Equality.axiom (@error_type_eqn T).
   unfold Equality.axiom.
   induction x, y ; try (apply ReflectF ; discriminate).
   * case (t == s) eqn: Ht.
     + rewrite /error_type_eqn Ht.
       move /eqP : Ht => Ht ; replace s with t.
       apply ReflectT ; reflexivity.
     + rewrite /error_type_eqn Ht.
       move /eqP : Ht => Ht.
       apply ReflectF ; injection ; exact Ht.
   * case (e == e0) eqn: He.
     + rewrite /error_type_eqn He.
       move /eqP : He => He ; replace e0 with e.
       apply ReflectT ; reflexivity.
     + rewrite /error_type_eqn He.
       move /eqP : He => He.
       apply ReflectF ; injection ; exact He.
   Qed.

   Canonical error_type_eqMixin {T: eqType} := EqMixin (@error_type_eqP T).
   Canonical error_type_eqType {T: eqType} := Eval hnf in EqType (@error_type T) (@error_type_eqMixin T).

(* DNJ: What follows is my proposal to create a unique lowered index from a (high-level) reference.
   I do not know whether this is compatible with ExpandConnects or LowerTypes. *)

(* A bijection between pairs of natural numbers and natural numbers.
   There seems to be a library Coq.Arith.Cantor that contains a similar function but I cannot find it. *)
Definition pair (x y : nat) : nat :=
   (x + y) * (x + y + 1) %/ 2 + x.

Definition proj1 (p : nat) : nat :=
   let x_plus_y := (Nat.sqrt (8 * p + 1) - 1) %/ 2 (* rounded down *) in
   p - (x_plus_y * (x_plus_y + 1) %/ 2).

Definition proj2 (p : nat) : nat :=
   let x_plus_y := (Nat.sqrt (8 * p + 1) - 1) %/ 2 (* rounded down *) in
   (* x_plus_y - (proj1 p), which simplifies to: *)
   x_plus_y * (x_plus_y + 3) %/ 2 - p.

(* pair and (proj1, proj2) are each other's inverse functions. *)
Lemma sqrt_spec : forall n: nat, Nat.sqrt (n * n) = n.
Admitted. (* probably the proof can be based on something like
   forall p: positive, Pos.sqrtrem (p * p) = (p, IsNul). *)

Lemma proj1_pair : forall (x y : nat), x = proj1 (pair x y).
Admitted.

Lemma proj2_pair : forall (y x : nat), y = proj2 (pair x y).
Admitted.

Lemma pair_proj : forall p : nat, p = pair (proj1 p) (proj2 p).
Admitted.

Definition nat_to_var (n : nat) : VarOrder.T := bin_of_nat n.

Definition var_to_nat (id: VarOrder.T) : nat := (* nat_of_bin *) id.

(* mapping from a href that is not a subaccess to an index in CE.env *)
Fixpoint ref2var (ref : href) : @error_type VarOrder.T :=
match ref with
| Eid v => OK (nat_to_var (v * 3 + 1))
| Esubfield ref0 v => match ref2var ref0 with Err e => Err e
                      | OK n => OK (nat_to_var (pair (var_to_nat n) v * 3 + 2)) end
| Esubindex ref0 i => match ref2var ref0 with Err e => Err e
                      | OK n => OK (nat_to_var (pair (var_to_nat n) i * 3 + 3)) end
| Esubaccess _ _ => Err Einternal (* should have been changed in an earlier pass *)
end.

Fixpoint href_without_subaccess (ref : href) : bool :=
match ref with
| Eid _ => true
| Esubfield ref0 _
| Esubindex ref0 _ => href_without_subaccess ref0
| Esubaccess _ _ => false
end.

Lemma ref2var_OK :
   forall (ref : href), href_without_subaccess ref ->
      forall e : error_info, ref2var ref <> Err e.
Proof.
induction ref ; try discriminate.
* unfold href_without_subaccess ; fold href_without_subaccess.
  intros.
  unfold ref2var ; fold ref2var.
  induction (ref2var ref).
  + discriminate.
  + apply IHref.
    exact H.
* unfold href_without_subaccess ; fold href_without_subaccess.
  intros.
  unfold ref2var ; fold ref2var.
  induction (ref2var ref).
  + discriminate.
  + apply IHref.
    exact H.
Qed.

Lemma ref2var_inj :
   forall (ref1 ref2 : href),
      href_without_subaccess ref1 ->
      ref2var ref1 = ref2var ref2 -> ref1 = ref2.
Proof.
(* based on the injectivity of * 3 + 1 etc. *)
Admitted.

(* mapping from an index in CE.env to a href. *)

Fixpoint var2ref' (depth n : nat) : @error_type href :=
   match depth, n with
   | 0, _ | _, 0 => Err Einternal
   | S d', _ => match n %% 3 with
                | 1 => OK (Eid (nat_to_var ((n - 1) %/ 3)))
                | 2 => let p := (n - 2) %/ 3 in
                       match var2ref' d' (proj1 p) with Err e => Err e
                       | OK ref => OK (Esubfield ref (nat_to_var (proj2 p))) end
                | _ => let p := (n - 3) %/ 3 in
                       match var2ref' d' (proj1 p) with Err e => Err e
                       | OK ref => OK (Esubindex ref (proj2 p)) end
                end
   end.

Definition var2ref (id : VarOrder.T) : @error_type href := var2ref' (var_to_nat id) (var_to_nat id).

Lemma var2ref_ref2var :
   forall (id : VarOrder.T), if var2ref id is OK ref
                  then ref2var ref = OK id
                  else forall ref: href, ref2var ref <> OK id.
Proof.
(* difficult for me to find the relevant lemmas, they seem to be spread out over
   several libraries and the Coq documentation appears incomplete. Also difficult
   that there are two formalizations of N interacting here. *)
Admitted.

(* Note that we cannot get a lemma like n <> 0 -> var2ref n <> Err e.
There may be numbers that are projected to 0. *)



(** Pass ExpandWhens *)

(* The pass translates a FIRRTL statement sequence (without aggregate types/aggregate connects)
   to one where when statements are replaced by suitable multiplexers or validifs.
   It also handles the last connect semantics. *)

   (* a type to indicate connects *)
   Inductive def_expr : Type :=
   | D_undefined (* declared but not connected, no "is invalid" statement *)
   | D_invalidated (* declared but not connected, there is a "is invalid" statement *)
   | D_fexpr : hfexpr -> def_expr (* declared and connected *)
   .

   (* equality of def_expr is decidable [because equality of hfexpr is decidable] *)
   Lemma def_expr_eq_dec : forall {x y : def_expr}, {x = y} + {x <> y}.
   Proof.
   decide equality.
   apply hfexpr_eq_dec.
   Qed.

   Definition def_expr_eqn (x y : def_expr) : bool :=
   match x, y with
   | D_undefined, D_undefined => true
   | D_invalidated, D_invalidated => true
   | D_fexpr expr1, D_fexpr expr2 => expr1 == expr2
   | _, _ => false
   end.

   Lemma def_expr_eqP : Equality.axiom def_expr_eqn.
   Proof.
   unfold Equality.axiom, def_expr_eqn.
   intros ; induction x, y ; try (apply ReflectF ; discriminate) ; try (apply ReflectT ; reflexivity).
   case Eq: (h == h0).
   all: move /hfexpr_eqP : Eq => Eq.
   apply ReflectT ; replace h0 with h ; reflexivity.
   apply ReflectF ; injection ; apply Eq.
   Qed.

   Canonical def_expr_eqMixin := EqMixin def_expr_eqP.
   Canonical def_expr_eqType := Eval hnf in EqType def_expr def_expr_eqMixin.

   (* a map to store connects *)
   Definition cmap := CE.t def_expr.
   Definition empty_cmap : cmap := CE.empty def_expr.

   (* equality of cmaps is decidable. (We take extensional equality.) *)
   Axiom cmap_eq_dec : forall {x y : CE.t def_expr}, {x = y} + {x <> y}.
   Definition cmap_eqn : CE.t def_expr -> CE.t def_expr -> bool := CE.equal def_expr_eqn.
   Axiom cmap_eqP : Equality.axiom cmap_eqn.
   Canonical cmap_eqMixin := EqMixin cmap_eqP.
   Canonical cmap_eqType := Eval hnf in EqType (CE.t def_expr) cmap_eqMixin.

   Definition map2_helper_cs_tf (c : hfexpr)
                                (true_expr : option def_expr) (false_expr : option def_expr) : option def_expr :=
   (* helper function to join connections made in separate branches of a when statement *)
   match true_expr, false_expr with
   | Some (D_fexpr t), Some (D_fexpr f) => if t == f then true_expr (* both definitions match, no multiplexer needed *)
                                           else Some (D_fexpr (emux c t f)) (* defined differently in both branches *)
   | Some (D_fexpr t), Some D_invalidated => Some (D_fexpr (Evalidif c t)) (* declared before when, only defined in true branch *)
   | Some D_invalidated, Some (D_fexpr f) => Some (D_fexpr (Evalidif (Eprim_unop Unot c) f)) (* declared before when, only defined in false branch *)
   | None, _ (* only declared in the false branch *)
   | _, Some D_undefined => false_expr (* not properly connected in the false branch *)
   | _, _ => true_expr
   end.

   Definition combine_branches (c : hfexpr) (true_branch : (hfstmt_seq * cmap))
                                            (false_branch: (hfstmt_seq * cmap)) : (hfstmt_seq * cmap) :=
   (* combines the two branches of a when statement into one sequence of declaration statements
      and one map of connections.
      Input:  * c = condition of the when statement
              * true_branch = pair of (declaration statements, map of connections),
                the translation of the true branch of the when statement
              * false_branch = pair of (declaration statements, map of connections),
                the translation of the false branch of the when statement
              Both maps of connections also contain the connections *before* the when statement;
              this is used if a new connection is only made in one of the branches
              because the other branch then keeps the value connected to before the when statement.
      Output: a pair consisting of
              * declaration statements containing the declarations from both branches
              * map of connections containing definitions (if necessary using multiplexers/validifs
                to choose between the values defined in the branches) *)
   let combined_cm := CE.map2 (map2_helper_cs_tf c) (snd true_branch) (snd false_branch)
   in (Qcat (fst true_branch) (fst false_branch), combined_cm).

   (* Because nat and ftype are not mutually recursive types we cannot define a mutually recursive
      initialization function for registers including array types.
      Therefore we construct, in a mutual recursion, a function that initializes one element of the array.
      After that we call the constructed function for every element of the array. *)

   Fixpoint init_undefined_vector (v : nat -> @error_type href) (array_size : nat) (type : ftype) (orient : forient) (value : def_expr) : @error_type ((nat -> cmap -> @error_type cmap) * nat) :=
   (* Produces a function that initializes v to value (mostly D_undefined or D_invalidated).
      It can be used to initialize memory write ports (data and mask fields) and wires.
      Memory ports have to be passive, but wires allow flipped fields,
      so it does not check whether the type is passive.
      Input:  * v = href of the variable that needs to be initialized (possibly this is already an array)
              * array_size = size of the array v (if it's not an array, array_size == 1)
              * type = type of v <number>
              * orient = orientation of v (Sink, Duplex or Source)
                If the orientation of v is Source, only flipped fields will be initialized.
                If the orientation of v is Sink, only non-flipped fields will be initialized.
      Output: * nat -> cmap -> cmap : a function that initializes one element of the array (by modifying a cmap accordingly)
              * nat : size of the array *)
   match type with
   | Gtyp _ => match orient with
               | Sink | Duplex => OK ((fun (n : nat) (cm : cmap) =>
                                       match v n with Err e => Err e | OK vn
                                       => match ref2var vn with Err e => Err e | OK ref
                                          => OK (CE.add ref value cm) end end), array_size)
               | Source => OK ((fun (n : nat) (cm: cmap) => Err Einternal), 0)
               | _ => Err Einternal
               end
   | Atyp el_type n => init_undefined_vector (fun m : nat => match v (m / n) with Err e => Err e | OK vmn
                                                             => OK (Esubindex vmn (m mod n)) end)
                                             (array_size * n) el_type orient value
   | Btyp ff => init_undefined_bundle v array_size ff orient value
   end
   with init_undefined_bundle (v : nat -> @error_type href) (array_size : nat) (ff : ffield) (orient : forient) (value : def_expr) : @error_type ((nat -> cmap -> @error_type cmap) * nat) :=
   match ff with
   | Fnil => OK ((fun (n : nat) (cm : cmap) => Err Einternal), 0)
   | Fflips field_name fl field_type ff_tail =>
        let field_orient := match fl, orient with Flipped, Sink => Source
                                                | Flipped, Source => Sink
                                                | _, _ => orient end
        in match init_undefined_vector (fun n : nat => match v n with Err e => Err e | OK vn
                                        => OK (Esubfield vn field_name) end)
                                       array_size field_type field_orient value
           with Err e => Err e | OK init_field
           => match init_undefined_bundle v array_size ff_tail orient value with Err e => Err e | OK init_tail
              => OK ((fun (n : nat) (cm : cmap) => if n <? snd init_field then fst init_field n cm
                                                                          else fst init_tail (n - snd init_field) cm),
                     snd init_field + snd init_tail) end end
   end.

   Fixpoint init_apply_initializer (fn : nat -> cmap -> @error_type cmap) (array_size : nat) (cm : cmap) : @error_type cmap :=
   (* Applies initialization function fn, as produced by init_register_vector, to cm
      so as to initialize the array fn 0 ... fn (array_size - 1). *)
   match array_size with
   | 0 => OK cm
   | S m => match fn m cm with Err e => Err e
            | OK new_cm => init_apply_initializer fn m new_cm end
   end.

   Definition init_ref (id : VarOrder.T) (type : ftype) (orient : forient) (cm : cmap) : @error_type cmap :=
   (* sets all ground-type elements of (Eid id) to D_undefined. *)
   match init_undefined_vector (fun n : nat => OK (Eid id)) 1 type orient D_undefined with Err e => Err e | OK initializer
   => init_apply_initializer (fst initializer) (snd initializer) cm end.

   Fixpoint init_register_vector (v : nat -> @error_type href) (array_size : nat) (type : ftype) : @error_type ((nat -> cmap -> @error_type cmap) * nat) :=
   (* Produces a function that initializes v to itself.
      Input:  * v = href of the variable that needs to be initialized
                    (possibly this is already an array, that's why it is a function from nat to href)
              * array_size = size of the array v (if it's not an array, array_size == 1)
              * type = type of (a single element of the array) v <number>
              * ce = component environment
      Output: * nat -> cmap -> cmap : a function that initializes one element of the array (by modifying a cmap accordingly)
              * nat : size of the array *)
   match type with
   | Gtyp _ => OK ((fun (n : nat) (cm : cmap) =>
                             match v n with Err e => Err e
                             | OK vn => match ref2var vn with Err e => Err e
                                        | OK ref => OK (CE.add ref (D_fexpr (Eref vn)) cm) end end), array_size)
   | Atyp el_type n => init_register_vector (fun m : nat => match v (m %% array_size) with Err e => Err e
                                                            | OK vn => OK (Esubindex vn (m %/ array_size)) end) (array_size * n) el_type
   | Btyp ff => init_register_bundle v array_size ff
   end
   with init_register_bundle (v : nat -> @error_type href) (array_size : nat) (ff : ffield) : @error_type ((nat -> cmap -> @error_type cmap) * nat) :=
   match ff with
   | Fnil => OK ((fun (n : nat) (cm : cmap) => Err Einternal), 0)
   | Fflips field_name Nflip field_type ff_tail =>
        match init_register_vector (fun n : nat => match v n with Err e => Err e
                                                   | OK vn => OK (Esubfield vn field_name) end)
                                   array_size field_type with Err e => Err e
        | OK init_field =>
           match init_register_bundle v array_size ff_tail with Err e => Err e
           | OK init_tail => OK ((fun (n : nat) (cm : cmap) => if n < snd init_field then fst init_field n cm
                                                                                     else fst init_tail (n - snd init_field) cm),
                                 snd init_field + snd init_tail) end end
   | Fflips _ Flipped _ _ => Err Eflow_direction
   end.

   Definition init_register (id : VarOrder.T) (type : ftype) (cm : cmap) : @error_type cmap :=
   (* Initializes the register id, which is of type type. *)
   match init_register_vector (fun n : nat => OK (Eid id)) 1 type with Err e => Err e
   | OK initializer => init_apply_initializer (fst initializer) (snd initializer) cm end.

   Fixpoint mask_type (t : ftype) : @error_type ftype :=
   (* the type of the mask field of a write port of a memory with type t *)
   match t with
   | Gtyp _ => OK (Gtyp (Fuint 1))
   | Atyp t n => match mask_type t with Err e => Err e | OK mtt
                 => OK (Atyp mtt n) end
   | Btyp ff => match mask_type_fields ff with Err e => Err e | OK mtff
                => OK (Btyp mtff) end
   end
   with mask_type_fields (ff : ffield) : @error_type ffield :=
   match ff with
   | Fnil => OK Fnil
   | Fflips fieldname Nflip t ff_tail => match mask_type t, mask_type_fields ff_tail with Err e, _ | _, Err e => Err e | OK mtt, OK mtff_tail
                                         => OK (Fflips fieldname Nflip mtt mtff_tail) end
   | Fflips fieldname Flipped t ff_tail => Err Etype (* error: type should be passive *)
   end.

   (* Identifiers for the fields of a memory port *)
   Parameter mem_port_addr : VarOrder.T.
   Parameter mem_port_en : VarOrder.T.
   Parameter mem_port_clk : VarOrder.T.
   Parameter mem_port_data : VarOrder.T.
   Parameter mem_port_mask : VarOrder.T.

   Definition type_of_mem (m : hfmem) : @error_type ftype :=
      (* data type of memory. Most fields are flipped so the memory has a source orientation. *)
      let addr_size := if depth m <= 1 then 0 else Nat.log2 (depth m - 1) + 1
      in let read_ports :=
                     foldr (fun (r : mem_port) (tl : ffield) =>
                               Fflips (id r) Flipped
                                      (Btyp (Fflips mem_port_addr Nflip (Gtyp (Fuint addr_size))
                                            (Fflips mem_port_en Nflip (Gtyp (Fuint 1))
                                            (Fflips mem_port_clk Nflip (Gtyp Fclock)
                                            (Fflips mem_port_data Flipped (data_type m) Fnil))))) tl)
                                      Fnil (reader m)
         in match mask_type (data_type m) with Err e => Err e | OK mask_t
            => OK (Btyp (foldr (fun (w : mem_port) (tl : ffield) =>
                               Fflips (id w) Flipped
                                      (Btyp (Fflips mem_port_addr Nflip (Gtyp (Fuint addr_size))
                                            (Fflips mem_port_en Nflip (Gtyp (Fuint 1))
                                            (Fflips mem_port_clk Nflip (Gtyp Fclock)
                                            (Fflips mem_port_data Nflip (data_type m)
                                            (Fflips mem_port_mask Nflip mask_t Fnil)))))) tl)
                                      read_ports (writer m))) end.

   Definition init_instance (id: VarOrder.T) (mdl: VarOrder.T) (ce : CE.env) (cm : cmap) : @error_type cmap :=
   (* This function should initialize the ports that connect the current module with module mdl under the name id,
      which is instantiated here.
      It is assumed that the type of the module is stored in ce already. *)
   match CE.find mdl ce with
   | Some (Aggr_typ type, Fmodule) => init_ref id type Source cm
   | Some _ => Err Etype
   | _ => Err Eundeclared
   end.

   Definition invalidate_cmpnt (ref : href) (cm : cmap) : @error_type cmap :=
   (* Sets the component ref to invalid, to indicate that the programmer let it unconnected on purpose.
      ref must be a ground-type reference. *)
   match ref2var ref with Err e => Err e | OK v
   => OK (CE.add v D_invalidated cm) end.
   (*init_ref ref (type_of_ref ref ce) Sink D_invalidated cm.*)

   (* now follows a right-recursive version of ExpandWhens. *)
   Fixpoint expandBranch_fun (ss : hfstmt_seq) (ce_other_modules : CE.env) (cm_init : cmap) : @error_type (hfstmt_seq * cmap) :=
   (* This is the main function of ExpandWhens. It replaces when statements by expressions containing
      multiplexers/validifs where necessary.  It has the following interface:
      Input:  * ss = sequence of statements that form an initial fragment of a module definition
                or an initial fragment of a branch
                (not containing partial or aggregate connects;
                possibly containing repeated connects and when statements)
              * ce_other_modules = component environment, containing the port declarations of other modules
                (this has been found in earlier passes and is not updated)
              * cm_init = map of connections, containing the port declarations of this module.
                If ss is the initial fragment of a branch,
                it also contains declarations and definitions of code before the branch.
      Output: a pair consisting of
              * sequence of statements, mainly containing declarations of registers and wires,
                that should become part of the resulting code (because registers and wires etc.
                declared in one branch should be included always in the translated code)
              * cmap : map of connects that have been defined before or in the branch
                (i.e. this map extends parameter cm_init by the connects in ss). *)
   match ss with
   | Qnil => OK (qnil, cm_init)
   | Qrcons ss_butlast last =>
        match expandBranch_fun ss_butlast ce_other_modules cm_init with
        | OK (ss_result, cm_result) =>
             match last with
             | @Sskip _ => OK (ss_result, cm_result) (* no translation needed *)
             | @Swire _ id type => match init_ref id type Duplex cm_result with Err e => Err e | OK cm_wire
                                   => OK (Qrcons ss_result last, cm_wire) end
             | @Sreg _ id reg => match init_register id (type reg) cm_result with Err e => Err e | OK cm_reg
                                 => OK (Qrcons ss_result last, cm_reg) end
             | @Smem _ id mem => match type_of_mem mem with Err e => Err e | OK mem_type
                                 => match init_ref id mem_type Source cm_result with Err e => Err e | OK cm_mem
                                    => OK (Qrcons ss_result last, cm_mem) end end
             | @Sinst _ id mdl => match init_instance id mdl ce_other_modules cm_result with Err e => Err e | OK cm_inst
                                  => OK (Qrcons ss_result last, cm_inst) end
             | @Snode _ _ _ => OK (Qrcons ss_result last, cm_result)
             | @Sfcnct _ ref expr => match ref2var ref with Err e => Err e | OK v
                                     => OK (ss_result, CE.add v (D_fexpr expr) cm_result) end
             | @Spcnct _ _ _ => Err Einternal
             | @Sinvalid _ ref => match invalidate_cmpnt ref cm_result with Err e => Err e | OK cm_inv
                                  => OK (ss_result, cm_inv) end
             | @Swhen _ cond ss_true ss_false =>
                  match expandBranch_fun ss_true  ce_other_modules cm_result,
                        expandBranch_fun ss_false ce_other_modules cm_result with Err e, _ | _, Err e => Err e | OK cm_true, OK cm_false
                  => OK (combine_branches cond cm_true cm_false) end
             (* | @Sstop _ clk cond exit => let result := expandBranch_fun ss_tail ce cm simcond *)
             (*                             in (Qcons (Sstop clk (option_and simcond cond) exit) (fst result), snd result) *)
             end
        | Err e => Err e
        end
   end.

   (* Now that the translation is defined, we proceed with providing a semantic equivalence;
      the above function should maintain the equivalence.

      Specification of the semantics.
      The semantics of when statements and last connect is:

      +------------------------------------------------------------------------+
      | For every (ground-type) sink element, ExpandWhens produces the connect |
      | (= Sfcnct or Sinvalid) that appears last on any execution path through |
      | the module.  If there are multiple execution paths where the component |
      | containing this sink element is declared, ExpandWhens seleects between |
      | them using a multiplexer or validif expression.                        |
      |    (If there is some execution path where the sink element is declared |
      | but is neither declared invalid [Sinvalid] not connected [Sfcnct], the |
      | program is erroneous,  and ExpandWhens produces  an error message;  an |
      | alternative  might be to translate  to a circuit  containing a similar |
      | error.)                                                                |
      +------------------------------------------------------------------------+

      Example of an incorrect statement sequence and its translation:
         Wire a : UInt<16>
         when c : a <= b             // no connect statement for a if c is false

      Example of a correct statement sequence and its translation:
         Wire a : UInt<16>    --->   Wire a : UInt<16>
         when c : a <= b             a <= validif(c, b)
         else : a is invalid

      To simplify matters, we mainly concentrate on the correctness of expandBranch_fun,
      i.e., we specify that the correct cmap is created (which will be translated to
      the correct sequence of connect statements by recode_cmap).
      Further, we assume for now that all components have ground types, to avoid
      burdening the proofs with complex evaluations of composite types.
      The principle is this:
      1. A type expr_tree models the different connects that may appear on different
         execution paths.
      2. Function expandBranch_one_var_sem constructs an expr_tree for one ground-type
         element.
      3. Function expr_tree_to_def_expr translates this expr_tree to a def_expr
         (i.e. an entry in cmap).
         This corresponds to the semantics for a single ground-type element.

      4. Function expandBranch_one_component_sem_conform checks for every ground element
         of one component whether a cmap (typically, the return value of expandBranch_fun)
         satisfies the specification given through 1-3.
      5. Function expandBranch_sem_conform checks for all components declared anywhere
         in a module whether expandBranch_fun satisfies the specification.
         This function relies on CE.env to find which components are declared and their
         types. (In particular, for instance statements this could not be done without
         a CE.env.) *)

(* 1. expr_tree *)

   Inductive expr_tree : Type :=
   (* This data type describes the resulting value of a component depending on the execution path.
      Whenever there is a when statement (and the component has been declared before,
      so it is available in both execution paths), a T_choice node is inserted. *)
   | T_undeclared (* in this execution path, the component is not declared *)
   | T_undefined (* the component is erroneously not connected *)
   | T_invalidated (* the component is not connected but the programmer has
                      indicated with an "is invalid" statement that this is ok *)
   | T_fexpr : hfexpr -> expr_tree
   | T_choice : hfexpr (* condition *) ->
                expr_tree (* choice if condition is true *) ->
                expr_tree (* choice if condition is false *) -> expr_tree
   .

   (* equality of expr_trees is decidable *)
   Lemma expr_tree_eq_dec : forall {x y : expr_tree}, {x = y} + {x <> y}.
   Proof. decide equality ; apply hfexpr_eq_dec. Qed.
   Fixpoint expr_tree_eqn (x y : expr_tree) : bool :=
   match x, y with
   | T_undeclared, T_undeclared => true
   | T_undefined, T_undefined => true
   | T_invalidated, T_invalidated => true
   | T_fexpr expr1, T_fexpr expr2 => expr1 == expr2
   | T_choice cond1 true1 false1, T_choice cond2 true2 false2 => (cond1 == cond2) && (expr_tree_eqn true1 true2) && (expr_tree_eqn false1 false2)
   | _, _ => false
   end.
   Lemma expr_tree_eqP : Equality.axiom expr_tree_eqn.
   Proof.
   unfold Equality.axiom ; unfold expr_tree_eqn.
   induction x, y ; try (apply ReflectF ; discriminate) ; try (apply ReflectT ; reflexivity).
   case Eq: (h == h0).
   1, 2: move /hfexpr_eqP : Eq => Eq.
   apply ReflectT ; replace h0 with h ; reflexivity.
   apply ReflectF ; injection ; apply Eq.
   fold expr_tree_eqn ; fold expr_tree_eqn in IHx1 ; fold expr_tree_eqn in IHx2.
   case Eq: (h == h0).
   all: move /hfexpr_eqP : Eq => Eq.
   replace h0 with h.
   destruct IHx1 with (y := y1).
   replace y1 with x1.
   destruct IHx2 with (y := y2).
   replace y2 with x2.
   apply ReflectT ; reflexivity.
   all: apply ReflectF ; injection ; done.
   Qed.
   Canonical expr_tree_eqMixin := EqMixin expr_tree_eqP.
   Canonical expr_tree_eqType := Eval hnf in EqType expr_tree expr_tree_eqMixin.

(* 2. Function expandBranch_one_var_sem *)

   Fixpoint expandBranch_one_var_sem (ss : hfstmt_seq) (ref : href) (default : expr_tree) : expr_tree :=
   (* This function looks up to which value ref is connected in the code ss.
      It is assumed that ref has a ground type and is declared with sink or duplex flow.
      (If the flow is source, the function may erroneously produce "T_undefined" to indicate that it should be connected to,
      while this is not the case for sources.)
      If no connection is found, the function returns default. *)
   match ss with
   | Qnil => default
   | Qrcons ss_butlast last =>
        let default_result := expandBranch_one_var_sem ss_butlast ref default
        in match last with
           | @Sreg _ id _ => if base_ref ref == id then T_fexpr (Eref ref) else default_result
           (* In the three lines below we disregard that some subfields of a wire/instance may be flipped
              and therefore have source flow direction; similarly, <memory id>.<read port id>.data
              has source flow direction.  That is why we have the precondition
              that ref must have sink (or duplex) flow direction. *)
           | @Smem _ id _
           | @Swire _ id _
           | @Sinst _ id _ => if base_ref ref == id then T_undefined else default_result
           (* In the two lines below we assume that ref0 is a ground type and not a subaccess, as ExpandConnects has already been applied. *)
           | @Sfcnct _ ref0 expr => if ref == ref0 then T_fexpr expr else default_result
           | @Sinvalid _ ref0 => if ref == ref0 then T_invalidated else default_result
           | @Swhen _ cond ss_true ss_false => let true_result  := expandBranch_one_var_sem ss_true  ref default_result
                                            in let false_result := expandBranch_one_var_sem ss_false ref default_result
                                                  in match true_result, false_result with
                                                     (* ignore execution paths where ref is not declared *)
                                                     | T_undeclared, _ => false_result
                                                     | _, T_undeclared => true_result
                                                     (* create a choice if ref is declared in both execution paths: *)
                                                     | _, _ => if true_result == false_result then true_result
                                                                else T_choice cond true_result false_result
                                                     end
           | _ => default_result
           end
   end.

(* 3. Function expr_tree_to_def_expr *)

   Fixpoint expr_tree_to_def_expr (tree: expr_tree) : option def_expr :=
   (* This function translates an expression tree (that represents the value of a connect,
      depending on the execution path) to a def_expr (which should be the output of the
      ExpandWhen phase for this reference). *)
   match tree with
   | T_undeclared => None
   | T_undefined => Some D_undefined
   | T_invalidated => Some D_invalidated
   | T_fexpr e => Some (D_fexpr e)
   | T_choice cond true_tree false_tree => let true_expr := expr_tree_to_def_expr true_tree
                                           in let false_expr := expr_tree_to_def_expr false_tree
                                              in match true_expr, false_expr with
                                                 | None, _
                                                 | _, Some D_undefined => false_expr
                                                 | _, None
                                                 | Some D_undefined, _
                                                 | Some D_invalidated, Some D_invalidated => true_expr
                                                 | Some (D_fexpr te), Some D_invalidated => Some (D_fexpr (Evalidif cond te))
                                                 | Some D_invalidated, Some (D_fexpr fe) => Some (D_fexpr (Evalidif (Eprim_unop Unot cond) fe))
                                                 | Some (D_fexpr te), Some (D_fexpr fe) => if te == fe then Some (D_fexpr te)
                                                                                           else Some (D_fexpr (Emux cond te fe))
                                                 end
   end.

(* 4. Function expandBranch_one_component_sem_conform
   Here we simplify by assuming that the data type is always ground. *)

   Fixpoint expandBranch_one_component_sem_conform (ref : href) (t : ftype) (ss : hfstmt_seq) (cm : cmap) (default : cmap) : bool :=
   (* This function checks for every ground element of component ref, which has type t,
      whether cm satisfies the specification given by expandBranch_one_var_sem.
      cm should contain the connects for the ground elements produced by
      (ExpandBranch_fun ss ... default).

      It is assumed that ref has sink or duplex flow; flipped parts of ref are skipped.
      ref is a wire (duplex flow), a memory port (sink flow), or an output port (sink flow).
      Input ports (source flow) should be handled by the corresponding function for flipped data types.
      For wires, one should call both this function and the one for flipped data types to get a complete verification. *)
   match t with
   | Gtyp _ => match ref2var ref with Err _ => false | OK v
               => let default_value := match CE.find v default with
                                       | None => T_undeclared
                                       | Some D_undefined => T_undefined
                                       | Some D_invalidated => T_invalidated
                                       | Some (D_fexpr e) => T_fexpr e
                                       end
                  in CE.find v cm == expr_tree_to_def_expr (expandBranch_one_var_sem ss ref default_value) end
   | Atyp t' array_size => [forall n: ordinal array_size, expandBranch_one_component_sem_conform (Esubindex ref n) t' ss cm default]
   | Btyp ff => expandBranch_one_component_sem_conform_fields ref ff ss cm default
   end
   with expandBranch_one_component_sem_conform_fields (ref : href) (ff : ffield) (ss : hfstmt_seq) (cm : cmap) (default : cmap) : bool :=
   match ff with
   | Fnil => true
   | Fflips f Nflip   t' ff_tail =>    expandBranch_one_component_sem_conform (Esubfield ref f) t' ss cm default
                                    && expandBranch_one_component_sem_conform_fields ref ff_tail ss cm default
   | Fflips f Flipped t' ff_tail =>    expandBranch_one_component_sem_conform_flipped (Esubfield ref f) t' ss cm default
                                    && expandBranch_one_component_sem_conform_fields ref ff_tail ss cm default
   end
   with expandBranch_one_component_sem_conform_flipped (ref : href) (t : ftype) (ss : hfstmt_seq) (cm : cmap) (default : cmap) : bool :=
   (* This function checks for every ground element of component ref, which has type t,
      whether cm satisfies the specification given by expandBranch_one_var_sem.
      cm should contain the connects for the ground elements produced by
      (ExpandBranch_fun ss ... default).

      It is assumed that ref has source or duplex flow; only flipped parts of ref are checked.
      ref is a wire (duplex flow) or an input port.
      Memory ports and output port (sink flow) should be handled by the corresponding function for non-flipped data types.
      For wires, one should call both this function and the one for non-flipped data types to get a complete verification. *)
   match t with
   | Gtyp _ => true (* no requirement on flipped parts / source flow parts *)
   | Atyp t' array_size => [forall n: ordinal array_size, expandBranch_one_component_sem_conform_flipped (Esubindex ref n) t' ss cm default]
   | Btyp ff => expandBranch_one_component_sem_conform_flipped_fields ref ff ss cm default
   end
   with expandBranch_one_component_sem_conform_flipped_fields (ref : href) (ff : ffield) (ss : hfstmt_seq) (cm : cmap) (default : cmap) : bool :=
   match ff with
   | Fnil => true
   | Fflips f Nflip   t' ff_tail =>    expandBranch_one_component_sem_conform_flipped (Esubfield ref f) t' ss cm default
                                    && expandBranch_one_component_sem_conform_flipped_fields ref ff_tail ss cm default
   | Fflips f Flipped t' ff_tail =>    expandBranch_one_component_sem_conform (Esubfield ref f) t' ss cm default
                                    && expandBranch_one_component_sem_conform_flipped_fields ref ff_tail ss cm default
   end.

(* 5. Function expandBranch_sem_conform.
      To define this function we first need to formulate the preconditions of expandBranch_fun. *)

   Definition expandBranch_precondition_ce_helper (_ : VarOrder.T) (entry: (cmpnt_init_typs * fcomponent)) (in_bool : bool) : bool :=
   (* the entry is an input or output port, and it has a ground type *)
   match entry with
   | (Aggr_typ (Gtyp _), In_port)
   | (Aggr_typ (Gtyp _), Out_port) => in_bool
   | _ => false
   end.

   Definition expandBranch_precondition_ce (ce_other_modules : CE.env) : bool :=
   (* in/out ports of other modules are ground types:
      all entries in ce_other_modules are input or output ports,
      and they have ground types. *)
   CE.fold expandBranch_precondition_ce_helper ce_other_modules true.

   Fixpoint expandBranch_precondition_declarations (ss : hfstmt_seq) (ce_previous : CE.env) : @error_type CE.env :=
   (* If all declarations are ground types and there are no partial connects in ss
      then the result is a CE.env containing types for all declared components.
      (ce_previous is the map containing types for the code before ss.)
      (or possibly CE.empty (cmpnt_init_typs * fcomponent))
      Otherwise the result is an error message. *)
   match ss with
   | Qnil => OK ce_previous
   | Qrcons ss_butlast last =>
       match expandBranch_precondition_declarations ss_butlast ce_previous with Err e => Err e | OK ce_butlast_result
       => match last with
          | @Swire _ id t  => if t is Gtyp _
                              then match ref2var (Eid id) with Err e => Err e | OK var
                                   => if CE.find var ce_butlast_result is Some _
                                      then Err Ealready_declared
                                      else OK (CE.add var (aggr_typ t, Wire) ce_butlast_result)
                                   end
                              else Err Etype
          | @Sreg _ id reg => if type reg is Gtyp _
                              then match ref2var (Eid id) with Err e => Err e | OK var
                                   => if CE.find var ce_butlast_result is Some _
                                      then Err Ealready_declared
                                      else OK (CE.add var (Reg_typ reg, Register) ce_butlast_result)
                                   end
                              else Err Etype
          | @Smem _ id mem => if data_type mem is Gtyp _
                              then match ref2var (Eid id) with Err e => Err e | OK var
                                   => if CE.find var ce_butlast_result is Some _
                                      then Err Ealready_declared
                                      else OK (CE.add var (Mem_typ mem, Memory) ce_butlast_result)
                                   end
                              else Err Etype
          | @Spcnct _ _ _ => Err Einternal
          | @Swhen _ _ sst ssf =>
               match expandBranch_precondition_declarations sst ce_butlast_result with
               | Err e => Err e
               | OK ce_true_result =>
                    expandBranch_precondition_declarations ssf ce_true_result
               end
          | _ => OK ce_butlast_result
                 (* for Sinst, one has to check ce_other_modules as well.
                    This is done in expandBranch_precondition_ce. *)
          end
      end
   end.

   Lemma expandBranch_precondition_declarations_does_not_contain_modules :
      forall (ss : hfstmt_seq) (ce_previous : CE.env),
         if expandBranch_precondition_declarations ss ce_previous is OK ce_declarations
         then forall var : VarOrder.T,
                 match CE.find var ce_declarations with
                 | Some (_, Fmodule)
                 | Some (_, In_port)
                 | Some (_, Out_port)
                 | Some (_, Node)
                 | None => CE.find var ce_previous == CE.find var ce_declarations
                 | _ => true
                 end
         else True.
   Proof.
   (* proof by mutual induction over ss and hfstmt;
      below is a partial proof for the part that can be done
      without induction over hfstmt.

   intros.
   * unfold expandBranch_precondition_declarations.
     intro ; rewrite eq_refl.
     destruct (CE.find var ce_previous) ; try destruct p ; try destruct f ; try done.
   * simpl expandBranch_precondition_declarations.
     destruct (expandBranch_precondition_declarations ss ce_previous) ; try done.
     destruct h ; try apply IHss ; try done.
     + (* Swire *)
       destruct f ; try done.
       destruct (CE.find (nat_to_var (s * 3 + 1)) e) ; try done.
       intro.
       specialize IHss with (var := var).
       destruct (eqVneq var (nat_to_var (s * 3 + 1))).
       - rewrite -!e0.
         replace (CE.find var (CE.add var (aggr_typ (Gtyp f), Wire) e))
         with (Some (aggr_typ (Gtyp f), Wire)) by (symmetry ;
               apply CELemmas.find_add_eq ;
               rewrite /CE.SE.eq e0 eq_refl //) ; done.
       - replace (CE.find var (CE.add (nat_to_var (s * 3 + 1))
                  (aggr_typ (Gtyp f), Wire) e))
         with (CE.find var e) by (symmetry ;
               apply CELemmas.find_add_neq ;
               apply negbTE in i ;
               rewrite /CE.SE.eq i //).
         apply IHss.
     + (* Sreg, similar to Swire *)
       admit.
     + (* Smem, similar to Swire *)
       admit.
     + (* Swhen *)
       Swhen cannot be handled without mutual induction over hfstmt.
   *)
   Admitted.

   Definition expandBranch_sem_conform (ss : hfstmt_seq) (ce_other_modules : CE.env) (ce_previous_declarations : CE.env) (cm_previous : cmap) : Prop :=
   (* Checks for the components declared in the statement sequence whether expandBranch_fun satisfies the specification.
      * ss = statement sequence to be checked (an initial fragment of a module or of a branch)
      * ce_other_modules = component environment containing port declarations of other modules,
                     used in Sinst statements
      * ce_previous_declarations = information on declarations of components in the code
                      before ss, necessary for data types
                      (containing only port types at the beginning of a module)
      * cm_previous = (containing only port declarations at the beginning of a module)
                      definitions of components, based on code before the beginning of this branch *)
   expandBranch_precondition_ce ce_other_modules (* in/out ports of other modules are ground types *) ->
   match expandBranch_precondition_declarations ss ce_previous_declarations with Err e => true | OK ce_declarations =>
   match expandBranch_fun ss ce_other_modules cm_previous with Err e => true | OK (ss_result, cm_result)
   => forall id : VarOrder.T,
      if ref2var (Eid id) is OK var
      then match CE.find var ce_declarations with
           | Some (Aggr_typ t, _) => expandBranch_one_component_sem_conform (Eid id) t ss cm_result cm_previous
           | Some (Reg_typ reg, _) => expandBranch_one_component_sem_conform (Eid id) (type reg) ss cm_result cm_previous
           | Some (Mem_typ mem, _) => if type_of_mem mem is OK tom
                                      then expandBranch_one_component_sem_conform_flipped (Eid id) tom ss cm_result cm_previous
                                      else false
           | _ => true
           end
      else true
   end end.

(* Correctness theorem:
   If ...
   then expandBranch_sem_conform is true. *)

Definition expandBranch_correct_hfstmt_seq (ss : hfstmt_seq) : Prop :=
   forall (ce_other_modules ce_previous_declarations : CE.env),
      expandBranch_sem_conform ss ce_other_modules ce_previous_declarations empty_cmap.

Definition expandBranch_correct_hfstmt (s : hfstmt) : Prop :=
   if s is Swhen _ sst ssf
   then expandBranch_correct_hfstmt_seq sst /\ expandBranch_correct_hfstmt_seq ssf
   else True.

Theorem expandBranch_correct :
   forall (ss : hfstmt_seq), expandBranch_correct_hfstmt_seq ss.
(* Programs that cannot be handled by expandBranch_fun and generate an error message
   are always regarded as correct.
   Perhaps this will need to be refined later. *)
Proof.
apply hfstmt_seq_hfstmt_ind with (P := expandBranch_correct_hfstmt_seq)
                                 (P0 := expandBranch_correct_hfstmt)
      ; try done.
all: unfold expandBranch_correct_hfstmt_seq, expandBranch_correct_hfstmt.
all: unfold expandBranch_sem_conform.
all: intros.
* unfold expandBranch_precondition_declarations, expandBranch_fun, ref2var.
  intro.
  destruct (CE.find (nat_to_var (id * 3 + 1)) ce_previous_declarations) eqn: Hfind ; try done.
  destruct p as [comp_typ f].
  destruct comp_typ as [ft|reg|mem|]; try done.
  + assert (exists t : fgtyp, ft = Gtyp t) by admit.
    destruct H0 as [t].
    rewrite H0.
    simpl expandBranch_one_component_sem_conform.
    (* the empty map does not contain any elements *)
    done.
  + (* register is similar to variable *)
    admit.
  + (* memory is similar to variable *)
    admit.
* specialize H with (ce_other_modules := ce_other_modules)
                    (ce_previous_declarations := ce_previous_declarations).
  apply H in H1 ; clear H.
  simpl expandBranch_precondition_declarations.
  destruct (expandBranch_precondition_declarations h ce_previous_declarations) as [ce_declarations|] eqn: Hdeclarations ; try done.
  destruct h0 eqn: Hstmt.
  + (* Skip *)
    simpl expandBranch_fun.
    destruct (expandBranch_fun h ce_other_modules empty_cmap) ; try done.
    destruct p as [_ cm_result].
    intro.
    specialize H1 with (id := id).
    unfold ref2var ; unfold ref2var in H1.
    destruct (CE.find (nat_to_var (id * 3 + 1)) ce_declarations) eqn: Hfind ; try done.
    destruct p as [comp_typ fcomp].
    destruct comp_typ as [ft|reg|mem|] ; try done.
    - assert (exists t : fgtyp, ft = Gtyp t) by admit.
      destruct H.
      rewrite H ; rewrite H in H1.
      unfold expandBranch_one_component_sem_conform, ref2var ;
      unfold expandBranch_one_component_sem_conform, ref2var in H1.
      simpl expandBranch_one_var_sem.
      replace (CE.find (nat_to_var (id * 3 + 1)) empty_cmap) with (@None def_expr) in H1 by (done).
      exact H1.
    - (* register is similar to variable *)
      admit.
    - (* memory is similar to variable *)
      admit.
  + (* Swire *)
    assert (exists t : fgtyp, f = Gtyp t) by admit.
    destruct H.
    rewrite H.
    destruct (CE.find (nat_to_var (s * 3 + 1)) ce_declarations) eqn: Halready_declared ; try done.
    simpl expandBranch_fun.
    destruct (expandBranch_fun h ce_other_modules empty_cmap) ; try done.
    destruct p as [_ cm_result].
    intro.
    specialize H1 with (id := id).
    unfold ref2var ; unfold ref2var in H1.
    destruct (eqVneq s id).
    - rewrite e.
      replace (CE.find (nat_to_var (id * 3 + 1)) (CE.add (nat_to_var (id * 3 + 1))
               (aggr_typ (Gtyp x), Wire) ce_declarations))
      with (Some (aggr_typ (Gtyp x), Wire))
      by (symmetry ;
          apply CELemmas.find_add_eq ;
          rewrite /CE.SE.eq eq_refl //).
      unfold aggr_typ, expandBranch_one_component_sem_conform, ref2var.
      replace (CE.find (nat_to_var (id * 3 + 1))
              (CE.add (nat_to_var (id * 3 + 1)) D_undefined cm_result))
      with (Some D_undefined)
      by (symmetry ;
          apply CELemmas.find_add_eq ;
          rewrite /CE.SE.eq eq_refl //).
      simpl expandBranch_one_var_sem.
      rewrite eq_refl /expr_tree_to_def_expr eq_refl //.
    - assert (forall val (ce : CE.env), CE.find (nat_to_var (id * 3 + 1))
                      (CE.add (nat_to_var (s * 3 + 1)) val ce)
             = CE.find (nat_to_var (id * 3 + 1)) ce).
            intros.
            apply CELemmas.find_add_neq.
            clear -i.
            unfold CE.SE.eq, nat_to_var.
            move /eqP : i => i.
            contradict i.
            move /eqP : i => i.
            assert (injective bin_of_nat)
                  by (apply can_inj with (g := nat_of_bin),
                            bin_of_natK).
            unfold injective in H.
            apply H in i.
            move /eqP : i => i.
            rewrite eqn_add2r eqn_mul2r orFb in i.
            move /eqP : i => i.
            assert (injective nat_of_bin)
                  by (apply can_inj with (g := bin_of_nat),
                            nat_of_binK).
            unfold injective in H0.
            apply H0 in i.
            done.
      rewrite H2.
      destruct (CE.find (nat_to_var (id * 3 + 1)) ce_declarations) ; try done.
      destruct p as [comp_typ fcomp].
      destruct comp_typ as [ft|reg|mem|] ; try done.
      * assert (exists t : fgtyp, ft = Gtyp t) by admit.
        destruct H3.
        rewrite H3 ; rewrite H3 in H1.
        unfold expandBranch_one_component_sem_conform, ref2var ;
        unfold expandBranch_one_component_sem_conform, ref2var in H1.
        simpl expandBranch_one_var_sem.
        replace (CE.find (nat_to_var (id * 3 + 1)) empty_cmap) with (@None def_expr) in H1 by (done).
        replace (CE.find (nat_to_var (id * 3 + 1))
        (CE.add (nat_to_var (s * 3 + 1))
           D_undefined cm_result))
        with (CE.find (nat_to_var (id * 3 + 1)) cm_result)
        by admit. (* same proof as above, assertion H2 *)
        apply negbTE in i.
        rewrite (eq_sym id) i.
        exact H1.
      * (* register is similar to variable *)
        admit.
      * (* memory is similar to variable *)
        admit.
  + (* Sreg *)
    (* Sreg is similar to Swire *)
    admit.
  + (* Smem *)
    (* Smem is similar to Swire *)
    admit.
  + (* Sinst *)
    simpl expandBranch_fun.
    destruct (expandBranch_fun h ce_other_modules empty_cmap) ; try done.
    destruct p as [ss_result cm_result].
    destruct (init_instance s s0 ce_other_modules cm_result) eqn: Hinit_instance ; try done.
    intro.
    specialize H1 with (id := id).
    unfold ref2var ; unfold ref2var in H1.
    destruct (eqVneq s0 id).
    - (* id now does not have a ground type but is part of the instance.
         That means, it has type (Btyp ...) where each field has a ground type. *)
