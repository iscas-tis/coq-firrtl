From Coq Require Import BinNat ZArith.
From mathcomp Require Import ssreflect ssrbool eqtype seq fintype ssrnat div.
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
   Proof. induction x, y ; try (right ; discriminate) ; try (left ; reflexivity). Qed.
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
   Proof. induction x, y ; try (right ; discriminate).
   * case (t == s) eqn: Ht.
     + move /eqP : Ht => Ht ; left ; replace s with t ; reflexivity.
     + move /eqP : Ht => Ht ; right ; injection ; exact Ht.
   * case (e == e0) eqn: He.
     + move /eqP : He => He ; left ; replace e0 with e ; reflexivity.
     + move /eqP : He => He ; right ; injection ; exact He.
   Qed.
   Definition error_type_eqn {T : eqType} (x y : @error_type T) : bool :=
   match x, y with OK t, OK s => t == s
                 | Err e, Err f => e == f
                 | _, _ => false end.
   Lemma error_type_eqP {T : eqType} : Equality.axiom (@error_type_eqn T).
   unfold Equality.axiom.
   induction x, y ; try (apply ReflectF ; discriminate).
   * case (t == s) eqn: Ht.
     + unfold error_type_eqn ; replace (t == s) with true.
       move /eqP : Ht => Ht ; replace s with t.
       apply ReflectT ; reflexivity.
     + unfold error_type_eqn ; replace (t == s) with false.
       move /eqP : Ht => Ht.
       apply ReflectF ; injection ; exact Ht.
   * case (e == e0) eqn: He.
     + unfold error_type_eqn ; replace (e == e0) with true.
       move /eqP : He => He ; replace e0 with e.
       apply ReflectT ; reflexivity.
     + unfold error_type_eqn ; replace (e == e0) with false.
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

Definition nat_to_var (n : nat) : VarOrder.T := N.of_nat n.

Definition var_to_nat (id: VarOrder.T) : nat := N.to_nat id.

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

(* The pass translates a FIRRTL statement sequence (but one without aggregate types/aggregate connects)
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
   intros ; induction x, y ; try (right ; discriminate) ; try (left ; reflexivity).
   case Eq: (h == h0).
   all: move /hfexpr_eqP : Eq => Eq.
   left ; replace h0 with h ; reflexivity.
   right ; injection ; apply Eq.
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

   (* Definition option_and (simcond : option hfexpr) (cond : hfexpr) : hfexpr :=
   (* calculates the conjunction between two conditions if present.
      This function is only used if there are simulation statements like Sstop. *)
   match simcond with
   | None => cond
   | Some s => eprim_binop Band s cond
   end. *)

   (* Because nat and ftype are not mutually recursive types we cannot define a mutually recursive
      initialization function for registers including array types.
      Therefore we construct, in a mutual recursion, a function that initializes one element of the array.
      After that we call the constructed function for every element of the array. *)

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

   Lemma init_register_vector_nil :
      forall (type : ftype) (v : nat -> @error_type href),
         if init_register_vector v 0 type is OK (_, n)
         then n = 0
         else True
   with init_register_bundle_nil :
      forall (ff : ffield) (v : nat -> @error_type href),
         if init_register_bundle v 0 ff is OK (_, n)
         then n = 0
         else True.
   Proof.
   induction type.
   * unfold init_register_vector ; reflexivity.
   * unfold init_register_vector ; fold init_register_vector.
     rewrite mul0n.
     intro.
     apply IHtype.
   * unfold init_register_vector ; fold init_register_bundle.
     apply init_register_bundle_nil.
   induction ff.
   * unfold init_register_bundle ; intro.
     reflexivity.
   * unfold init_register_bundle ; fold init_register_vector ; fold init_register_bundle.
     destruct f.
     + trivial.
     + intro.
       destruct (init_register_vector
                 (fun n : nat => match v0 n with
                                 | OK vn => OK (Esubfield vn v)
                                 | Err e => Err e
                                 end) 0 f0) eqn: Hirv.
       - destruct p.
         unfold fst, snd.
         specialize init_register_vector_nil with (type := f0)
         (v := (fun n : nat => match v0 n with
                               | OK vn => OK (Esubfield vn v)
                               | Err e => Err e
                               end)).
         rewrite Hirv in init_register_vector_nil.
         rewrite init_register_vector_nil.
         destruct (init_register_bundle v0 0 ff) eqn: Hirb.
         * specialize IHff with (v := v0).
           rewrite Hirb in IHff.
           destruct p.
           rewrite add0n.
           exact IHff.
         * trivial.
       - trivial.
   Qed.

   Definition fn_array_is_OK (id: VarOrder.T) (fn : nat -> cmap -> @error_type cmap) (array_size : nat) : Prop :=
      forall n : nat, n < array_size ->
         (* forall e : error_info, fn n cm <> Err e *)
         exists (vn : href) (k : VarOrder.T) (elt : def_expr),
               base_ref vn = id
            /\ ref2var vn = OK k
            /\ forall (cm : cmap), fn n cm = OK (CE.add k elt cm).

   Definition vn_array_is_OK (id : VarOrder.T) (v : nat -> @error_type href) (array_size : nat) : Prop :=
      forall n : nat, n < array_size ->
         if v n is OK t then base_ref t = id /\ href_without_subaccess t
         else False.

   Lemma init_register_vector_OK :
      forall type : ftype, is_passive type ->
         forall (id : VarOrder.T) (v : nat -> @error_type href) (array_size : nat),
            vn_array_is_OK id v array_size ->
               if init_register_vector v array_size type is OK (fn, array_size0)
               then fn_array_is_OK id fn array_size0
               else False
   with init_register_bundle_OK :
      forall ff: ffield, is_passive_fields ff ->
         forall (id : VarOrder.T) (v : nat -> @error_type href) (array_size : nat),
            vn_array_is_OK id v array_size ->
               if init_register_bundle v array_size ff is OK (fn, array_size0)
               then fn_array_is_OK id fn array_size0
               else False.
   Proof.
   induction type.
   * intros.
     unfold init_register_vector.
     unfold vn_array_is_OK in H0.
     unfold fn_array_is_OK.
     intros.
     specialize H0 with (n).
     destruct (v n) eqn: Hvn.
     + exists h.
       assert (base_ref h = id /\ href_without_subaccess h).
         move : H1 ; exact H0.
       destruct (ref2var h) eqn: Href2var.
       - exists s, (D_fexpr (Eref h)).
         split.
         * apply H2.
         split.
         * reflexivity.
         * intro ; reflexivity.
       - contradict Href2var.
         apply ref2var_OK.
         apply H2.
     + contradict H0.
       exact H1.
   * unfold is_passive ; fold is_passive.
     unfold init_register_vector ; fold init_register_vector.
     intros.
     apply IHtype.
     exact H.
     unfold vn_array_is_OK.
     intro ; intro.
     unfold vn_array_is_OK in H0.
     enough (match v (n0 %% array_size) with
             | OK t => base_ref t = id /\ href_without_subaccess t
             | Err _ => False
             end).
     destruct (v (n0 %% array_size)) eqn: Hvn0n.
     + unfold base_ref ; fold base_ref.
       unfold href_without_subaccess ; fold href_without_subaccess.
       exact H2.
     + exact H2.
     apply H0.
     apply ltn_pmod.
     rewrite lt0n.
     move : H1 ; apply contraTneq ; intro.
     rewrite H1 mul0n ltn0.
     done.
   * unfold is_passive ; fold is_passive_fields.
     unfold init_register_vector ; fold init_register_bundle.
     apply init_register_bundle_OK.
   induction ff.
   * unfold init_register_bundle, fn_array_is_OK.
     intros.
     contradict H1.
     replace (n < 0) with false by (symmetry ; apply ltn0).
     done.
   * induction f.
     + unfold is_passive_fields.
       done.
     + unfold is_passive_fields ; fold is_passive_fields ; fold is_passive.
       intro ; intro ; intro.
       move /andP : H => H.
       unfold init_register_bundle ; fold init_register_bundle ; fold init_register_vector.
       intro.
       destruct (init_register_vector
                   (fun n : nat =>
                    match v0 n with
                    | OK vn => OK (Esubfield vn v)
                    | Err e => Err e
                    end) array_size f0) eqn: Hinit_vector_f0.
       - specialize IHff with (v := v0) (array_size := array_size).
         destruct (init_register_bundle v0 array_size ff) eqn: Hinit_bundle_ff.
         * unfold fn_array_is_OK.
           intros.
           destruct (n < snd p) eqn: Hnp.
           + specialize init_register_vector_OK with (v := (fun n : nat =>
                       match v0 n with
                       | OK vn => OK (Esubfield vn v)
                       | Err e => Err e
                       end)) (array_size := array_size) (type := f0).
             rewrite Hinit_vector_f0 in init_register_vector_OK.
             destruct p.
             apply init_register_vector_OK.
             - apply H.
             - unfold vn_array_is_OK.
               intro.
               unfold vn_array_is_OK in H0.
               specialize H0 with (n := n1).
               destruct (v0 n1) eqn: Hv0_n1.
               * unfold base_ref ; fold base_ref.
                 unfold href_without_subaccess ; fold href_without_subaccess.
                 exact H0.
               * exact H0.
             - unfold snd in Hnp.
               rewrite Hnp.
               done.
           + destruct p0.
             unfold fst.
             apply IHff.
             - apply H.
             - exact H0.
             - unfold snd at 2 in H1.
               rewrite <- subSn by (rewrite leqNgt Hnp ; done).
               rewrite leq_subLR.
               exact H1.
         * apply IHff.
           apply H.
       - specialize init_register_vector_OK with (id := id) (v := (fun n : nat =>
                     match v0 n with
                     | OK vn => OK (Esubfield vn v)
                     | Err e => Err e
                     end)) (array_size := array_size) (type  := f0).
         rewrite Hinit_vector_f0 in init_register_vector_OK.
         intro.
         apply init_register_vector_OK.
         * apply H.
         * unfold vn_array_is_OK.
           intro.
           unfold vn_array_is_OK in H0.
           specialize H0 with (n := n).
           destruct (v0 n) eqn: Hv0_n.
           + unfold base_ref ; fold base_ref.
             unfold href_without_subaccess ; fold href_without_subaccess.
             exact H0.
           + exact H0.
   Qed.

   Fixpoint init_apply_initializer (fn : nat -> cmap -> @error_type cmap) (array_size : nat) (cm : cmap) : @error_type cmap :=
   (* Applies initialization function fn, as produced by init_register_vector, to cm
      so as to initialize the array fn 0 ... fn (array_size - 1). *)
   match array_size with
   | 0 => OK cm
   | S m => match fn m cm with Err e => Err e
            | OK new_cm => init_apply_initializer fn m new_cm end
   end.

   Lemma init_apply_initializer_OK :
      forall (id : VarOrder.T) (fn : nat -> cmap -> @error_type cmap) (array_size : nat),
         fn_array_is_OK id fn array_size ->
               (forall (cm : cmap) (e : error_info), init_apply_initializer fn array_size cm <> Err e)

               (* for a suitable base_type and base_orient, this needs to become:
                forall (cm : cmap),
                   if init_apply_initializer fn array_size cm is OK cm_initialized
                   then (forall ref : href, base_ref ref = id ->
                            match type_and_dir_of_ref' ref base_type base_orient with
                            | OK (Gtyp _, Sink) | OK (Gtyp _, Duplex) | OK (Gtyp _, Passive) =>
                                if ref2var ref is OK v then CE.find v cm_initialized <> None
                                                       else True
                            | _=>  True end)
                   else False*)

            /\ exists (seq_k_e : seq (href * def_expr)),
                     (all (fun (k_e : href * def_expr) => base_ref (fst k_e) == id) seq_k_e)
                  /\ forall cm : cmap,
                        init_apply_initializer fn array_size cm =
                        foldl (fun (e_cm : @error_type cmap) (k_e : href * def_expr) =>
                                      match e_cm, ref2var (fst k_e) with Err e, _ | _, Err e => Err e
                                      | OK cm, OK k => OK (CE.add k (snd k_e) cm) end)
                              (OK cm) seq_k_e.
   Proof.
   induction array_size.
   * unfold init_apply_initializer.
     split.
     + discriminate.
     + exists [::].
       split.
       - rewrite all_nil ; done.
       - unfold foldl ; reflexivity.
   * unfold init_apply_initializer ; fold init_apply_initializer.
     intro.
     unfold fn_array_is_OK in H.
     assert (exists (vn : href) (k : VarOrder.T) (elt : def_expr),
                base_ref vn = id /\ ref2var vn = OK k /\
                forall cm : cmap, fn array_size cm = OK (CE.add k elt cm)).
       apply H, ltnSn.
     destruct H0, H0, H0, H0, H1.
     split.
     + intro.
       specialize H2 with (cm := cm).
       rewrite H2.
       apply IHarray_size.
       unfold fn_array_is_OK.
       intro ; intro.
       apply H, leqW ; exact H3.
     + assert (exists seq_k_e : seq (href * def_expr),
                  all (fun k_e : href * def_expr => base_ref (fst k_e) == id) seq_k_e /\
                  forall cm : cmap,
                     init_apply_initializer fn array_size cm =
                     foldl (fun (e_cm : error_type) (k_e : href * def_expr) =>
                            match e_cm with
                            | OK cm0 => match ref2var (fst k_e) with
                                        | OK k => OK (CE.add k (snd k_e) cm0)
                                        | Err e => Err e
                                        end
                            | Err e => Err e
                            end) (OK cm) seq_k_e).
         apply IHarray_size.
         unfold fn_array_is_OK.
         intro ; intro.
         apply H, leqW ; exact H3.
       destruct H3.
       exists ((x, x1) :: x2).
       split.
       + unfold all.
         enough ((base_ref (fst (x, x1)) == id) /\
                 (fix all (s : seq (href * def_expr)) : bool :=
                  match s with
                  | [::] => true
                  | x3 :: s' => (base_ref (fst x3) == id) && all s'
                  end) x2).
           move /andP : H4 => H4 ; exact H4.
         split.
         - rewrite H0 ; apply eq_refl.
         - apply H3.
       + intro.
         specialize H2 with (cm := cm).
         rewrite H2.
         unfold foldl.
         unfold fst at 2 ; unfold snd at 2.
         rewrite H1.
         apply H3.
   Qed.

   Definition init_register (id : VarOrder.T) (type : ftype) (cm : cmap) : @error_type cmap :=
   (* Initializes the register id, which is of type type. *)
   match init_register_vector (fun n : nat => OK (Eid id)) 1 type with Err e => Err e
   | OK initializer => init_apply_initializer (fst initializer) (snd initializer) cm end.

   Fixpoint type_and_dir_of_ref_fields (ref : href) (v : VarOrder.T) (ff : ffield) (ref_orient : forient) : @error_type (ftype * forient) :=
      (* calculates the type and flow direction of Esubfield ref v.
         * ref = some href
         * v = a field within this ref
         * ff = bundle type definition of ref
         * ref_orient = orientation of ref *)
      match ff with
      | Fnil => Err Etype
      | Fflips id Nflip t' ff_tail => if v == id then OK (t', ref_orient)
                                                 else type_and_dir_of_ref_fields ref v ff_tail ref_orient
      | Fflips id Flipped t' ff_tail => match ref_orient with
                                        | Source => if v == id then OK (t', Sink)
                                                               else type_and_dir_of_ref_fields ref v ff_tail ref_orient
                                        | Sink => if v == id then OK (t', Source)
                                                             else type_and_dir_of_ref_fields ref v ff_tail ref_orient
                                        | Duplex => if v == id then OK (t', Duplex)
                                                               else type_and_dir_of_ref_fields ref v ff_tail ref_orient
                                        | _ => Err Etype (* passive type should not contain flipped fields *)
                                        end
      end.

   Fixpoint type_and_dir_of_ref' (ref : href) (base_type : ftype) (base_orient : forient) : @error_type (ftype * forient) :=
      (* calculates the type and flow direction of ref.
         This is the internal helper function; the user should call type_and_dir_of_ref. *)
      match ref with
      | Eid _ => OK (base_type, base_orient)
      | Esubindex ref' i => match type_and_dir_of_ref' ref' base_type base_orient with Err e => Err e | OK (ref'_type, ref'_orient)
                            => match ref'_type with
                               | Atyp t' n => (* if i >= n then Err Etype else *)
                                              OK (t', ref'_orient)
                               | _ => Err Etype
                               end end
      | Esubfield ref' v => match type_and_dir_of_ref' ref' base_type base_orient with Err e => Err e | OK (ref'_type, ref'_orient)
                            => match ref'_type with
                               | Btyp ff => type_and_dir_of_ref_fields ref' v ff ref'_orient
                               | _ => Err Etype
                               end end
      | _ => Err Einternal (* subaccess should have been removed by an earlier pass *)
      end.


   Lemma init_register_OK :
      forall (id : VarOrder.T) (type : ftype),
         is_passive type ->
               (forall (cm : cmap),
                   if init_register id type cm is OK cm_reg
                   then (forall ref : href, base_ref ref = id ->
                            if type_and_dir_of_ref' ref type Passive is OK (Gtyp _, _)
                            then if ref2var ref is OK v then CE.find v cm_reg <> None
                                                       else True
                            else True)
                   else False)
            /\ (exists (seq_k_e : seq (href * def_expr)),
                     (all (fun (k_e : href * def_expr) => base_ref (fst k_e) == id) seq_k_e)
                  /\ forall cm : cmap,
                        init_register id type cm =
                        foldl (fun (e_cm : @error_type cmap) (k_e : href * def_expr) =>
                                      match e_cm, ref2var (fst k_e) with Err e, _ | _, Err e => Err e
                                      | OK cm, OK k => OK (CE.add k (snd k_e) cm) end)
                              (OK cm) seq_k_e).
   Proof.
   intros.
   unfold init_register.
   assert (if init_register_vector (fun _ : nat => OK (Eid id)) 1 type is OK (fn, array_size)
               then fn_array_is_OK id fn array_size
               else False).
     apply init_register_vector_OK.
     exact H.
     unfold vn_array_is_OK.
     split.
     * unfold base_ref ; fold base_ref ; reflexivity.
     * unfold href_without_subaccess ; fold href_without_subaccess ; done.
   destruct (init_register_vector (fun _ : nat => OK (Eid id)) 1 type) ;
         try contradiction.
   destruct p.
   unfold fst at 1 3, snd at 1 2.
   (* apply init_apply_initializer_OK.
   exact H0. *)
   Admitted.

   (* Identifiers for the fields of a memory port *)
   Parameter mem_port_addr : VarOrder.T.
   Parameter mem_port_en : VarOrder.T.
   Parameter mem_port_clk : VarOrder.T.
   Parameter mem_port_data : VarOrder.T.
   Parameter mem_port_mask : VarOrder.T.

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

   Lemma init_undefined_vector_OK :
      forall (type : ftype) (orient : forient) (id : VarOrder.T) (v : nat -> @error_type href) (array_size : nat),
         orient <> Passive -> orient <> Other -> vn_array_is_OK id v array_size ->
            forall value : def_expr,
               if init_undefined_vector v array_size type orient value is OK (fn, array_size0)
               then fn_array_is_OK id fn array_size0
               else False
   with init_undefined_bundle_OK :
      forall (ff: ffield) (orient : forient) (id : VarOrder.T) (v : nat -> @error_type href) (array_size : nat),
         orient <> Passive -> orient <> Other -> vn_array_is_OK id v array_size ->
            forall value : def_expr,
               if init_undefined_bundle v array_size ff orient value is OK (fn, array_size0)
               then fn_array_is_OK id fn array_size0
               else False.
   Proof.
   (* The proof is very similar to the one of init_register_vector_OK etc. *)
   Admitted.

   Definition init_ref (id : VarOrder.T) (type : ftype) (orient : forient) (cm : cmap) : @error_type cmap :=
   (* sets all ground-type elements of (Eid id) to D_undefined. *)
   match init_undefined_vector (fun n : nat => OK (Eid id)) 1 type orient D_undefined with Err e => Err e | OK initializer
   => init_apply_initializer (fst initializer) (snd initializer) cm end.

   Lemma init_ref_OK :
      forall (id : VarOrder.T) (type : ftype) (orient : forient),
         orient <> Passive -> orient <> Other ->
               (forall (cm : cmap) (e : error_info), init_ref id type orient cm <> Err e)
            /\ exists (seq_k_e : seq (href * def_expr)),
                     (all (fun (k_e : href * def_expr) => base_ref (fst k_e) == id) seq_k_e)
                  /\ forall cm : cmap,
                        init_ref id type orient cm =
                        foldl (fun (e_cm : @error_type cmap) (k_e : href * def_expr) =>
                                      match e_cm, ref2var (fst k_e) with Err e, _ | _, Err e => Err e
                                      | OK cm, OK k => OK (CE.add k (snd k_e) cm) end)
                              (OK cm) seq_k_e.
   Proof.
   intros.
   unfold init_ref.
   assert (if init_undefined_vector (fun _ : nat => OK (Eid id)) 1 type orient D_undefined is OK (fn, array_size)
               then fn_array_is_OK id fn array_size
               else False).
     apply init_undefined_vector_OK.
     exact H.
     exact H0.
     unfold vn_array_is_OK.
     split.
     * unfold base_ref ; fold base_ref ; reflexivity.
     * unfold href_without_subaccess ; fold href_without_subaccess ; done.
   destruct (init_undefined_vector (fun _ : nat => OK (Eid id)) 1 type orient D_undefined) ;
         try contradiction.
   destruct p.
   unfold fst at 1 3, snd at 1 2.
   apply init_apply_initializer_OK.
   exact H1.
   Qed.

   (*
   Lemma MapsTo_2 : forall (ce : cmap) (key1 key2 : VarOrder.T) (val1 val2 : def_expr),
      CE.MapsTo key1 val1 ce -> CE.MapsTo key2 val2 ce -> key1 == key2 -> val1 == val2.
   Proof.
   intros.
   enough (Some val1 = Some val2) by (injection H2 ; intros ; rewrite H3 ; apply eq_refl).
   rewrite <- CE.find_1 with (m := ce) (x := key1) by (exact H).
   rewrite <- CE.find_1 with (m := ce) (x := key2) by (exact H0).
   move /eqP : H1 => H1.
   rewrite H1.
   reflexivity.
   Qed.
   *)

   Definition foldl_helper (e_cm : @error_type cmap) (k_e : href * def_expr) :=
      match e_cm, ref2var (fst k_e) with Err e, _ | _, Err e => Err e
      | OK cm, OK k => OK (CE.add k (snd k_e) cm) end.

   Lemma add_seq_comm :
      forall (ref1 ref2 : href) (e1 e2 : def_expr) (seq_k_e1 seq_k_e2 : seq (href * def_expr)) (cm : cmap),
         href_without_subaccess ref1 ->
         href_without_subaccess ref2 ->
         ref1 != ref2 ->
            if foldl foldl_helper (OK cm) (seq_k_e1 ++ (ref1, e1) :: (ref2, e2) :: seq_k_e2) is OK cm12
            then
            if foldl foldl_helper (OK cm) (seq_k_e1 ++ (ref2, e2) :: (ref1, e1) :: seq_k_e2) is OK cm21
            then CE.Equal cm12 cm21
            else True else True.
   Proof.
   intros.
   destruct (foldl foldl_helper (OK cm) (seq_k_e1 ++ (ref1, e1) :: (ref2, e2) :: seq_k_e2)) as [cm12|] eqn: Hcm12 ;
         try trivial.
   destruct (foldl foldl_helper (OK cm) (seq_k_e1 ++ (ref2, e2) :: (ref1, e1) :: seq_k_e2)) as [cm21|] eqn: Hcm21 ;
         try trivial.
   destruct (ref2var ref1) as [id1|] eqn: Href1 ;
      try (assert (ref2var ref1 <> Err e) by (apply ref2var_OK ; exact H) ;
           contradiction).
   destruct (ref2var ref2) as [id2|] eqn: Href2 ;
      try (assert (ref2var ref2 <> Err e) by (apply ref2var_OK ; exact H0) ;
           contradiction).
   pose (OK_cm1 := foldl foldl_helper (OK cm) seq_k_e1).
   destruct OK_cm1 as [cm1|] eqn: Hcm1.
   rewrite foldl_cat in Hcm12 ; fold OK_cm1 in Hcm12.
   rewrite foldl_cat in Hcm21 ; fold OK_cm1 in Hcm21.
   replace (foldl foldl_helper OK_cm1 [:: (ref1, e1), (ref2, e2) & seq_k_e2]) with
   (foldl foldl_helper (foldl_helper OK_cm1 (ref1, e1)) ((ref2, e2) :: seq_k_e2)) in Hcm12 by reflexivity.
   replace (foldl_helper OK_cm1 (ref1, e1)) with (OK (CE.add id1 e1 cm1)) in Hcm12
         by (rewrite Hcm1 ;
             unfold foldl_helper, fst, snd ;
             rewrite Href1 ;
             reflexivity).
   replace (foldl foldl_helper (OK (CE.add id1 e1 cm1)) ((ref2, e2) :: seq_k_e2))
   with (foldl foldl_helper (foldl_helper (OK (CE.add id1 e1 cm1)) (ref2, e2)) seq_k_e2) in Hcm12 by reflexivity.
   replace (foldl_helper (OK (CE.add id1 e1 cm1)) (ref2, e2)) with (OK (CE.add id2 e2 (CE.add id1 e1 cm1))) in Hcm12
         by (unfold foldl_helper, fst, snd ;
             rewrite Href2 ;
             reflexivity).
   replace (foldl foldl_helper OK_cm1 [:: (ref2, e2), (ref1, e1) & seq_k_e2]) with
   (foldl foldl_helper (foldl_helper OK_cm1 (ref2, e2)) ((ref1, e1) :: seq_k_e2)) in Hcm21 by reflexivity.
   replace (foldl_helper OK_cm1 (ref2, e2)) with (OK (CE.add id2 e2 cm1)) in Hcm21
         by (rewrite Hcm1 ;
             unfold foldl_helper, fst, snd ;
             rewrite Href2 ;
             reflexivity).
   replace (foldl foldl_helper (OK (CE.add id2 e2 cm1)) ((ref1, e1) :: seq_k_e2))
   with (foldl foldl_helper (foldl_helper (OK (CE.add id2 e2 cm1)) (ref1, e1)) seq_k_e2) in Hcm21 by reflexivity.
   replace (foldl_helper (OK (CE.add id2 e2 cm1)) (ref1, e1)) with (OK (CE.add id1 e1 (CE.add id2 e2 cm1))) in Hcm21
         by (unfold foldl_helper, fst, snd ;
             rewrite Href1 ;
             reflexivity).
   move : cm1 Hcm1 Hcm12 Hcm21.
   induction seq_k_e2.
   * intros.
     unfold foldl in Hcm12.
     unfold foldl in Hcm21.
     injection Hcm12 ; injection Hcm21 ; intros.
     rewrite <- H2, <- H3.
     apply CELemmas.add_comm.
     unfold CE.SE.eq.
     move /eqP : H1 => H1.
     contradict H1.
     move /eqP : H1 => H1.
     apply ref2var_inj.
     exact H.
     rewrite Href1 Href2 H1.
     reflexivity.
   * destruct a as [ref3 e3].
     intros.
     replace (foldl foldl_helper (OK (CE.add id2 e2 (CE.add id1 e1 cm1))) ((ref3, e3) :: seq_k_e2))
     with (foldl foldl_helper (foldl_helper (OK (CE.add id2 e2 (CE.add id1 e1 cm1))) (ref3, e3)) seq_k_e2) in Hcm12 by reflexivity.
     replace (foldl foldl_helper (OK (CE.add id1 e1 (CE.add id2 e2 cm1))) ((ref3, e3) :: seq_k_e2))
     with (foldl foldl_helper (foldl_helper (OK (CE.add id1 e1 (CE.add id2 e2 cm1))) (ref3, e3)) seq_k_e2) in Hcm21 by reflexivity.
     unfold foldl_helper at 2, fst, snd in Hcm12.
     unfold foldl_helper at 2, fst, snd in Hcm21.
     destruct (ref2var ref3) as [id3|] eqn: Href3.
   Admitted.

   Lemma init_ref_transparant :
      forall (id1 id2 : VarOrder.T) (type1 type2 : ftype) (orient1 orient2 : forient) (cm : cmap),
         orient1 <> Passive -> orient1 <> Other -> orient2 <> Passive -> orient2 <> Other ->
            id1 <> id2 ->
               if init_ref id1 type1 orient1 cm is OK cm1
               then if init_ref id2 type2 orient2 cm is OK cm2
                    then if init_ref id2 type2 orient2 cm1 is OK cm12
                         then if init_ref id1 type1 orient1 cm2 is OK cm21
                              then CE.Equal cm12 cm21
                              else False
                         else False
                    else False
               else False.
   Proof.
   intros.
   destruct (init_ref id1 type1 orient1 cm) as [cm1|] eqn: Hir1 ;
         try (apply init_ref_OK with (id := id1) (type := type1) (orient := orient1) (cm := cm) (e := e) ;
              try done).
   destruct (init_ref id2 type2 orient2 cm) as [cm2|] eqn: Hir2 ;
         try (apply init_ref_OK with (id := id2) (type := type2) (orient := orient2) (cm := cm) (e := e) ;
              try done).
   destruct (init_ref id2 type2 orient2 cm1) as [cm12|] eqn: Hir12 ;
         try (apply init_ref_OK with (id := id2) (type := type2) (orient := orient2) (cm := cm1) (e := e) ;
              try done).
   destruct (init_ref id1 type1 orient1 cm2) as [cm21|] eqn: Hir21 ;
         try (apply init_ref_OK with (id := id1) (type := type1) (orient := orient1) (cm := cm2) (e := e) ;
              try done).
   (* Based on init_ref_OK, find the sequence of additions to CE that init_ref creates. *)
   assert (exists (seq_k_e : seq (href * def_expr)),
                     (all (fun (k_e : href * def_expr) => base_ref (fst k_e) == id1) seq_k_e)
                  /\ forall cm : cmap,
                        init_ref id1 type1 orient1 cm =
                        foldl (fun (e_cm : @error_type cmap) (k_e : href * def_expr) =>
                                      match e_cm, ref2var (fst k_e) with Err e, _ | _, Err e => Err e
                                      | OK cm, OK k => OK (CE.add k (snd k_e) cm) end)
                              (OK cm) seq_k_e).
     apply init_ref_OK.
     exact H.
     exact H0.
   assert (exists (seq_k_e : seq (href * def_expr)),
                     (all (fun (k_e : href * def_expr) => base_ref (fst k_e) == id2) seq_k_e)
                  /\ forall cm : cmap,
                        init_ref id2 type2 orient2 cm =
                        foldl (fun (e_cm : @error_type cmap) (k_e : href * def_expr) =>
                                      match e_cm, ref2var (fst k_e) with Err e, _ | _, Err e => Err e
                                      | OK cm, OK k => OK (CE.add k (snd k_e) cm) end)
                              (OK cm) seq_k_e).
     apply init_ref_OK.
     exact H1.
     exact H2.
   destruct H4 as [seq_k_e1], H4 as [H4_base_ref H4].
   destruct H5 as [seq_k_e2], H5 as [H5_base_ref H5].
   rewrite H4 in Hir1.
   rewrite H5 in Hir2.
   rewrite H4 in Hir21.
   rewrite H5 in Hir12.
   rewrite <- Hir2 in Hir21.
   rewrite <- Hir1 in Hir12.
   rewrite <- foldl_cat in Hir21.
   rewrite <- foldl_cat in Hir12.
   unfold CE.Equal.
   intro.
   destruct (var2ref y) eqn: Hvy.
   (* basically now I need to do induction over type1 and type2,
      to get down to ground elements. *)
   move : cm1 cm2 cm12 cm21 Hir1 Hir2 Hir12 Hir21.
   induction type1, type2.
   * (* Gtyp, Gtyp *)
     unfold init_ref, init_undefined_vector, ref2var.
     destruct orient1, orient2 ;
           try discriminate ;
           try (unfold fst, snd, init_apply_initializer ;
                intros ; injection Hir1 ; injection Hir2 ; injection Hir12 ; injection Hir21 ; intros ;
                rewrite <- H4, <- H5, <- H6, <- H7 ;
                unfold CE.Equal ; intros ; reflexivity).
   Admitted.

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

   Fixpoint type_of_ports (ports : seq hfport) : @error_type ftype :=
      (* provides the data type of a sequence of ports, meant for initialization *)
      match ports with
      | [::] => OK (Btyp Fnil)
      | Finput id type :: ports_tail => match type_of_ports ports_tail with Err e => Err e
                                        | OK (Btyp tail_ff) => OK (Btyp (Fflips id Flipped type tail_ff))
                                        | _ => Err Einternal end
      | Foutput id type :: ports_tail => match type_of_ports ports_tail with Err e => Err e
                                         | OK (Btyp tail_ff) => OK (Btyp (Fflips id Nflip type tail_ff))
                                         | _ => Err Einternal end
      end.

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

   Fixpoint expandBranch_fun (ss : hfstmt_seq) (ce : CE.env) (cm : cmap) : @error_type (hfstmt_seq * cmap) :=
   (* This is the main function of ExpandWhens. It replaces when statements by expressions containing
      multiplexers/validifs where necessary.  It has the following interface:
      Input:  * ss = sequence of statements that are a final fragment of a module definition
                or a final fragment of a branch
                (not containing partial or aggregate connects;
                possibly containing repeated connects and when statements)
              * ce = component environment, containing the port declarations of other modules
                (this has been found in earlier passes and is not updated)
              * cm = map of connections that have been defined in the previous statements of the module definition
                (including, when applicable, in the previous statements of the branch).
                This map is used in case a when statement only replaces a connect in one branch;
                in that case, the other branch has to copy the connect from this map.
      Output: a pair consisting of
              * sequence of statements, mainly containing declarations of registers and wires,
                that should become part of the resulting code (because registers and wires etc.
                declared in one branch should be included always in the translated code)
              * cmap : map of connects that have been defined before or in the branch
                (i.e. this map extends parameter cm by the connects in ss). *)
   match ss with
   | Qnil => OK (qnil, cm)
   | Qcons s ss_tail => match s with
                        | @Sskip _ => expandBranch_fun ss_tail ce cm (* no translation needed *)
                        | @Swire _ id type => match init_ref id type Duplex cm with Err e => Err e | OK cm_wire
                                              => match expandBranch_fun ss_tail ce cm_wire with Err e => Err e | OK result
                                                 => OK (Qcons s (fst result), snd result) end end
                        | @Sreg _ id reg => match init_register id (type reg) cm with Err e => Err e | OK cm_reg
                                            => match expandBranch_fun ss_tail ce cm_reg with Err e => Err e | OK result
                                               => OK (Qcons s (fst result), snd result) end end
                        | @Smem _ id mem => match type_of_mem mem with Err e => Err e | OK mem_type
                                            => match init_ref id mem_type Source cm with Err e => Err e | OK cm_mem
                                               => match expandBranch_fun ss_tail ce cm_mem with Err e => Err e | OK result
                                                  => OK (Qcons s (fst result), snd result) end end end
                        | @Sinst _ id mdl => match init_instance id mdl ce cm with Err e => Err e | OK cm_inst
                                             => match expandBranch_fun ss_tail ce cm_inst with Err e => Err e | OK result
                                                => OK (Qcons s (fst result), snd result) end end
                        | @Snode _ _ _ => match expandBranch_fun ss_tail ce cm with Err e => Err e | OK result
                                          => OK (Qcons s (fst result), snd result) end
                        | @Sfcnct _ ref expr => match ref2var ref with Err e => Err e | OK v
                                                => expandBranch_fun ss_tail ce (CE.add v (D_fexpr expr) cm) end
                        | @Spcnct _ _ _ => Err Einternal
                        | @Sinvalid _ ref => match invalidate_cmpnt ref cm with Err e => Err e | OK cm_inv
                                             => expandBranch_fun ss_tail ce cm_inv end
                        | @Swhen _ cond ss_true ss_false =>
                             match expandBranch_fun ss_true  ce cm,
                                   expandBranch_fun ss_false ce cm with Err e, _ | _, Err e => Err e | OK cm_true, OK cm_false
                             => let combined_branches := combine_branches cond cm_true cm_false
                                in match expandBranch_fun ss_tail ce (snd combined_branches) with Err e => Err e | OK result
                                   => OK (Qcat (fst combined_branches) (fst result), snd result) end end
                        (* | @Sstop _ clk cond exit => let result := expandBranch_fun ss_tail ce cm simcond *)
                        (*                             in (Qcons (Sstop clk (option_and simcond cond) exit) (fst result), snd result) *)
                        end
   end.

   Fixpoint init_ports (ports : seq hfport) (cm : cmap) (ce : CE.env) : @error_type (cmap * CE.env) :=
   (* This helper function sets the ports of a module to undefined.
      It also adds the port types to ce. *)
   match ports with
   | [::] => OK (cm, ce)
   | Finput  id type :: ports_tail =>
        match init_undefined_vector (fun n : nat => OK (Eid id)) 1 type Source D_undefined with Err e => Err e | OK initializer
        => match init_apply_initializer (fst initializer) (snd initializer) cm with Err e => Err e | OK cm_initialized
           => init_ports ports_tail cm_initialized (CE.add id (aggr_typ type, In_port) ce) end end
   | Foutput id type :: ports_tail =>
        match init_undefined_vector  (fun n : nat => OK (Eid id)) 1 type Sink D_undefined with Err e => Err e | OK initializer
        => match init_apply_initializer (fst initializer) (snd initializer) cm with Err e => Err e | OK cm_initialized
           => init_ports ports_tail cm_initialized (CE.add id (aggr_typ type, Out_port) ce) end end
   end.

   Lemma init_ports_OK :
      forall (ports : seq hfport) (cm : cmap) (ce : CE.env) (e : error_info),
         init_ports ports cm ce <> Err e.
   Proof.
   induction ports.
   * unfold init_ports.
     discriminate.
   * destruct a.
     + unfold init_ports ; fold init_ports.
       destruct (init_undefined_vector (fun _ : nat => OK (Eid s)) 1 f Source D_undefined) eqn: Hiuf.
       - intro.
         destruct (init_apply_initializer (fst p) (snd p) cm) eqn: Hiai.
         * intro.
           apply IHports.
           intros.
           contradict Hiai.
           apply init_apply_initializer_OK with (id := s).
           enough (if init_undefined_vector (fun _ : nat => OK (Eid s)) 1 f Source D_undefined is OK (fn, array_size0)
                    then fn_array_is_OK s fn array_size0
                    else False).
           rewrite Hiuf (surjective_pairing p) in H.
           exact H.
           apply init_undefined_vector_OK ; try discriminate.
           unfold vn_array_is_OK, href_without_subaccess, base_ref.
           done.
       - enough (if init_undefined_vector (fun _ : nat => OK (Eid s)) 1 f Source D_undefined is OK (fn, array_size0)
                    then fn_array_is_OK s fn array_size0
                    else False).
         rewrite Hiuf in H.
         contradiction.
         apply init_undefined_vector_OK ; try discriminate.
         unfold vn_array_is_OK, href_without_subaccess, base_ref.
         done.
     + unfold init_ports ; fold init_ports.
       destruct (init_undefined_vector (fun _ : nat => OK (Eid (var:=VarOrder.T) s)) 1 f Sink D_undefined) eqn: Hiuf.
       - intro.
         destruct (init_apply_initializer (fst p) (snd p) cm) eqn: Hiai.
         * intro.
           apply IHports.
           intros.
           contradict Hiai.
           apply init_apply_initializer_OK with (id := s).
           enough (if init_undefined_vector (fun _ : nat => OK (Eid s)) 1 f Sink D_undefined is OK (fn, array_size0)
                    then fn_array_is_OK s fn array_size0
                    else False).
           rewrite Hiuf (surjective_pairing p) in H.
           exact H.
           apply init_undefined_vector_OK ; try discriminate.
           unfold vn_array_is_OK, href_without_subaccess, base_ref.
           done.
       - enough (if init_undefined_vector (fun _ : nat => OK (Eid s)) 1 f Sink D_undefined is OK (fn, array_size0)
                    then fn_array_is_OK s fn array_size0
                    else False).
         rewrite Hiuf in H.
         contradiction.
         apply init_undefined_vector_OK ; try discriminate.
         unfold vn_array_is_OK, href_without_subaccess, base_ref.
         done.
   Qed.

   Fixpoint id_in_ports (id : VarOrder.T) (ports : seq hfport) : bool :=
      (* returns true iff id is the identifier of a port *)
      match ports with
      | [::] => true
      | Finput p _ :: ports_tail
      | Foutput p _ :: ports_tail => (id != p) && id_in_ports id ports_tail
      end.

   Lemma init_port_transparant:
      forall (ports : seq hfport) (cm : cmap) (ce : CE.env),
         forall (id : VarOrder.T) (value : def_expr),
            (forall ref : href, (var2ref id == OK ref) ==> ~~id_in_ports (base_ref ref) ports) ->
         forall (cm_ports : cmap) (ce_ports : CE.env),
            init_ports ports cm ce = OK (cm_ports, ce_ports) ->
            init_ports ports (CE.add id value cm) ce = OK (CE.add id value cm_ports, ce_ports).
   Proof.
   induction ports as [|port ports_tail].
   * unfold init_ports.
     intros.
     injection H0 ; intros.
     replace ce_ports with ce ; replace cm_ports with cm.
     reflexivity.
   * unfold init_ports ; fold init_ports.
     intros.
     destruct port eqn: Hport.
     + destruct (init_undefined_vector (fun _ : nat => OK (Eid s)) 1 f Source D_undefined) eqn: Hiuf;
             try discriminate.
       destruct p as [v n].
       unfold fst, snd ; unfold fst, snd in H0.
       destruct (init_apply_initializer v n (CE.add id value cm)) eqn: Hiai.
   Admitted.

   Definition recode_cmap_entry (id : VarOrder.T) (dexpr : def_expr) (ss' : @error_type hfstmt_seq) : @error_type hfstmt_seq :=
   (* This helper function for recode_map translates one entry of the cmap into a statement
      that is added to the statement sequence ss. *)
   match ss' with Err e => Err e | OK ss
   => match dexpr with
      | D_undefined => Err Euninitialized (* the user has forgotten to connect the component *)
      | D_invalidated => match var2ref id with Err e => Err e | OK ref
                         => OK (Qcons (sinvalid ref) ss) end (* the user has given an "is invalid" statement. Copy it. *)
      | D_fexpr expr => match var2ref id with Err e => Err e | OK ref
                        => OK (Qcons (sfcnct ref expr) ss) end
      end end.

   Definition recode_cmap (cm : cmap) : @error_type hfstmt_seq :=
   (* Translates the entries in cm to a sequence of statements (in a random order). *)
   CE.fold recode_cmap_entry cm (OK qnil).

(* The following functions are an attempt to create a statement sequence that is sorted
   according to dependencies between connect statements.  The idea is to repeatedly walk
   through the cmap and every time emit those connect statements whose dependencies have
   already been emitted earlier.  To do so, we need a proof that the dependency order is
   well-founded.

   However, in any case, the above expandBranch_fun does not do the job completely: it
   leaves node statements as they are.  To get the order completely correct, one would
   also have to move the node statements to the cmap and emit them in the correct position.
   Additionally, register declarations and stop statements contain expressions that
   may require some specific order.  (Stop statements do not influence any other statements,
   so they could be placed at the end of the module, in the same order as they appear in
   the original.  But registers cannot be handled that easily.)

   Fixpoint dependencies_present (expr : hfexpr) (ce : CE.env) (cm : cmap) : bool :=
   (* Returns true iff expr contains a non-register component that is present in cm.
      (Dependencies on registers can be disregarded because one always reads the old value
      and writes the new value to a register.) *)
   match expr with
   | Econst _ _ => false
   | Ecast _ expr0
   | Eprim_unop _ expr0 => dependencies_present expr0 cm
   | Eprim_binop _ expr0 expr1
   | Evalidif expr0 expr1 => dependencies_present expr0 cm || dependencies_present expr1 cm
   | Emux expr0 expr1 expr2 => dependencies_present expr0 cm || dependencies_present expr1 cm || dependencies_present expr2 cm
   | Eref ref => dependencies_present_ref ref cm
   end
   with dependencies_present_ref (ref : href) (ce : CE.env) (cm : cmap) : bool :=
   match ref with
   | Eid id => match find id ce with
               | None (* error: undeclared identifier used *)
               | Some (Reg_typ _, _) => false
               | _ => CE.In id cm
               end
   | Esubfield ref _
   | Esubindex ref _ => dependencies_present_ref ref cm
   | Esubaccess ref expr => dependencies_present_ref ref cm || dependencies_present expr cm
   end.

   Definition recode_cmap_sorted_entry (ce : CE.env) (id : VarOrder.T) (dexpr : def_expr) (ss_cm : hfstmt_seq * cmap) : hfstmt_seq * cmap :=
   (* This helper function for recode_map_sorted translates one entry of the cmap into a statement
      that is added to the statement sequence ss. However, the current entry is only added if all
      its dependencies have been handled earlier. To this end, snd ss_cm is the map without the
      entries that already have been copied to fst ss_cm. *)
   match dexpr with
   | D_undefined => (fst ss_cm, remove id (snd ss_cm)) (* the user has erroneously not connected to id *)
   | D_invalidated => (Qcons (sinvalid (Eid id)) (fst ss_cm), remove id (snd ss_cm))
   | D_fexpr expr => if dependencies_present expr ce (snd ss_cm) then ss_cm
                     else (Qcons (sfcnct (Eid id) expr) (fst ss_cm), remove id (snd ss_cm))
   end.

   Function recode_cmap_sorted (ce : CE.env) (cm : cmap) (ss : hfstmt_seq)
   (cm_is_well_founded : forall cm' : cmap, (forall (id : VarOrder.T) (dexpr : def_expr), CE.MapsTo id dexpr cm' -> CE.MapsTo id dexpr cm) ->
                                exists (id : VarOrder.T) (dexpr : def_expr),
                                       CE.MapsTo id dexpr cm' /\
                                       (dexpr = D_undefined \/
                                        dexpr = D_invalidated \/
                                        exists expr: hfexpr, dexpr = D_fexpr expr /\
                                               ~dependencies_present expr cm')
   { measure cardinal cm } : hfstmt_seq :=
   (* This recursive function produces a sorted list of connections.
      It requires that the connections in cmap are not circular---otherwise the recursion is infinite.
      The last parameter is a proof that this is the case.  Based on that parameter, one can prove the
      obligations that come with { measure cardinal cm }. *)
   if CE.empty cm then ss
   else let result := CE.fold (recode_cmap_sorted_entry ce) cm (ss, FSet.empty)
        in recode_cmap_sorted (snd result) (fst result) cm_is_well_founded. *)

   (* Perhaps a better way is to construct a dag.  The dag implicitly contains the proof
      that there are no cycles.  That reminds me: there are already some graph functions
      in some Coq library; in particular, the function to calculate sccs can be used for
      this end. *)

   Definition expandWhen_fun (mdl : hfmodule) (ce : CE.env) : @error_type hfmodule :=
   (* This function provides an interface to the main function.
      Input:  * mdl = module definition
                (its statements do not contain partial or aggregate connects;
                they may contain double connects and when statements)
              * ce = component environment, containing the input/output port declarations of all other modules
                (this has been found in earlier passes and is not updated)
      Output: translated statement sequence of the module *)
   match mdl with
   | FInmod id ports ss =>
        match init_ports ports empty_cmap (CE.empty (cmpnt_init_typs * fcomponent)) with Err e => Err e | OK (cm_initialized, _)
        => match expandBranch_fun ss ce cm_initialized with Err e => Err e | OK result
           => match recode_cmap (snd result) with Err e => Err e | OK ss
              => OK (FInmod id ports (Qcat (fst result) ss)) end end end
   | FExmod _ _ _ => Err Eunimplemented
   end.

   (* Specification of the semantics.
      The semantics of when statements and last connect is:

      +------------------------------------------------------------------------+
      | For every (ground-type) sink element, ExpandWhens produces the connect |
      | (= Sfcnct or Sinvalid) that appears last on any execution path through |
      | the module.  If there are multiple execution paths where the component |
      | containing this sink element is declared, ExpandWhens seleects between |
      | them using a multiplexer or validif expression.                        |
      |    (If there is some execution path where the sink element is declared |
      | but is neither declared invalid [Sinvalid] not connected [Sfcnct], the |
      | program is erroneous, and ExpandWhens produces an error message.)      |
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
         types. (In particular, for instances this could not be done without a CE.env.) *)

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
   Proof.
   induction x, y ; try (right ; discriminate) ; try (left ; reflexivity).
   case Eq: (h == h0).
   move /hfexpr_eqP : Eq => Eq.
   left ; replace h0 with h ; reflexivity.
   move /hfexpr_eqP : Eq => Eq.
   right ; injection ; apply Eq.
   case Eq: (h == h0).
   move /hfexpr_eqP : Eq => Eq.
   replace h0 with h.
   destruct IHx1 with (y := y1).
   replace y1 with x1.
   destruct IHx2 with (y := y2).
   left ; replace y2 with x2 ; reflexivity.
   right ; injection ; apply n.
   right ; injection ; intro ; apply n.
   move /hfexpr_eqP : Eq => Eq.
   right ; injection ; intros until 2 ; apply Eq.
   Qed.
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
   apply ReflectF ; injection ; apply n.
   apply ReflectF ; injection ; intro ; apply n.
   apply ReflectF ; injection ; intros until 2 ; apply Eq.
   Qed.
   Canonical expr_tree_eqMixin := EqMixin expr_tree_eqP.
   Canonical expr_tree_eqType := Eval hnf in EqType expr_tree expr_tree_eqMixin.

   Fixpoint expandBranch_one_var_sem (ss : hfstmt_seq) (ref : href) (default : expr_tree) : expr_tree :=
   (* This function looks up to which value ref is connected in the code ss.
      It is assumed that ref has a ground type and is declared with sink or duplex flow.
      (If the flow is source, the function may erroneously produce "T_undefined" to indicate that it should be connected to,
      while this is not the case for sources.)
      If no connection is found, the function returns default. *)
   match ss with
   | Qnil => default
   | Qcons s tl => match s with
                   | @Sreg _ id _ => (* In the then branch, ref must refer to a ground element that is stored in the register *)
                                     expandBranch_one_var_sem tl ref (if base_ref ref == id then T_fexpr (Eref ref) else default)
                   (* In the three lines below we disregard that some subfields of a wire/instance may be flipped
                      and therefore have source flow direction; similarly, <memory id>.<read port id>.data
                      has source flow direction.  That is why we have the precondition
                      that ref must have sink (or duplex) flow direction. *)
                   | @Smem _ id _
                   | @Swire _ id _
                   | @Sinst _ id _ => expandBranch_one_var_sem tl ref (if base_ref ref == id then T_undefined else default)
                   (* In the two lines below we assume that ref0 is a ground type and not a subaccess, as ExpandConnects has already been applied. *)
                   | @Sfcnct _ ref0 expr => expandBranch_one_var_sem tl ref (if ref == ref0 then T_fexpr expr else default)
                   | @Sinvalid _ ref0 => expandBranch_one_var_sem tl ref (if ref == ref0 then T_invalidated else default)
                   | @Swhen _ cond ss_true ss_false => let true_result  := expandBranch_one_var_sem ss_true  ref default
                                                       in let false_result := expandBranch_one_var_sem ss_false ref default
                                                          in let result := match true_result, false_result with
                                                                           (* ignore execution paths where ref is not declared *)
                                                                           | T_undeclared, _ => expandBranch_one_var_sem tl ref false_result
                                                                           | _, T_undeclared => expandBranch_one_var_sem tl ref true_result
                                                                           | _, _ => expandBranch_one_var_sem tl ref
                                                                                     (if true_result == false_result then true_result
                                                                                      else T_choice cond true_result false_result)
                                                                           end
                                                             in expandBranch_one_var_sem tl ref result
                   | _ => expandBranch_one_var_sem tl ref default
                   end
   end.

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

   Definition expandBranch_sem_conform_helper (ss : hfstmt_seq) (cm : cmap) (default : cmap)
                                     (id : VarOrder.T) (def : cmpnt_init_typs * fcomponent) (val: bool) : bool :=
   (* This helper function verifies for all ground elements of component id, which is of type and kind def,
      whether cm satisfies the specification given by expandBranch_one_var_sem.
      cm should contain the connects for the ground elements produced by
      (ExpandBranch_fun ss ... default). *)
   val && match def with
          | (Aggr_typ t, Wire) =>    expandBranch_one_component_sem_conform (Eid id) t ss cm default
                                  && expandBranch_one_component_sem_conform_flipped (Eid id) t ss cm default
          | (Aggr_typ t, Instanceof)
          | (Aggr_typ t, In_port) => expandBranch_one_component_sem_conform_flipped (Eid id) t ss cm default
          | (Aggr_typ t, Out_port) => expandBranch_one_component_sem_conform (Eid id) t ss cm default
          | (Reg_typ r, Register) => expandBranch_one_component_sem_conform (Eid id) (type r) ss cm default
          | (Mem_typ m, Memory) => match type_of_mem m with Err e => false | OK tm
                                   => expandBranch_one_component_sem_conform_flipped (Eid id) tm ss cm default end
          | _ => false (* error *)
          end.

   Fixpoint expandWhen_precondition_ss (ss : hfstmt_seq) (ce_modules : CE.env) : bool :=
   (* Precondition of expandWhen: there are no partial connects, all instance statements refer to defined modules.
      Also: all references are to declared variables.
      * ss = statement sequence that is tested whether it satisfies the precondition
      * ce_modules = component environment containing (at least) type descriptions of all instantiated modules
      Result: true iff the precondition is satisfied. *)
   match ss with
   | Qnil => true
   | Qcons s tl => match s with
                   | Sreg _ reg => is_passive (type reg) && expandWhen_precondition_ss tl ce_modules
                   | Smem _ mem => is_passive (data_type mem) && expandWhen_precondition_ss tl ce_modules
                   | Spcnct _ _ => false
                   | Sinst id def => if CE.find def ce_modules is Some (Aggr_typ _, Fmodule) then expandWhen_precondition_ss tl ce_modules else false
                   | Swhen _ sst ssf =>    expandWhen_precondition_ss sst ce_modules
                                        && expandWhen_precondition_ss ssf ce_modules
                                        && expandWhen_precondition_ss tl ce_modules
                   | _ => expandWhen_precondition_ss tl ce_modules
                   end
   end.

   Fixpoint expandWhen_ce (ss : hfstmt_seq) (ce_modules default : CE.env) : @error_type CE.env :=
   (* The result contains exactly the component types as defined by ss, in addition to default.
      The parameter ce_modules contains the port declarations of other modules. *)
   match ss with
   | Qnil => OK default
   | Qcons s ss_tail => match s with
                        | Swire id t => if CE.find id default is Some _ then Err Ealready_declared
                                        else expandWhen_ce ss_tail ce_modules (CE.add id (aggr_typ t, Wire) default)
                        | Sreg id reg => if CE.find id default is Some _ then Err Ealready_declared
                                         else expandWhen_ce ss_tail ce_modules (CE.add id (Reg_typ reg, Register) default)
                        | Smem id mem => if CE.find id default is Some _ then Err Ealready_declared
                                         else expandWhen_ce ss_tail ce_modules (CE.add id (Mem_typ mem, Memory) default)
                        | Sinst id typ => if CE.find id default is Some _ then Err Ealready_declared
                                          else match CE.find typ ce_modules with
                                               | Some (Aggr_typ type, Fmodule) => expandWhen_ce ss_tail ce_modules (CE.add id (aggr_typ type, Instanceof) default)
                                               | Some _ => Err Etype
                                               | None => Err Eundeclared
                                               end
                        | Sskip
                        | Snode _ _ (* can be ignored *)
                        | Sfcnct _ _
                        | Sinvalid _ => expandWhen_ce ss_tail ce_modules default
                        | Swhen _ ss_true ss_false => match expandWhen_ce ss_true ce_modules default with Err e => Err e | OK default_true
                                                      => match expandWhen_ce ss_false ce_modules default_true with Err e => Err e | OK default_false
                                                         => expandWhen_ce ss_tail ce_modules default_false end end
                        (* | Sstop _ _ _ => expandWhen_ce ss_tail default *)
                        | Spcnct _ _ => Err Einternal
                        end
   end.

   Fixpoint is_declared (ss : hfstmt_seq) (id : VarOrder.T) : Prop :=
      (* is True if ss contains at least one declaration of a component with identifier id. *)
      match ss with
      | Qnil => False
      | Qcons s ss_tail => match s with
                           | Swire id' _
                           | Sreg id' _
                           | Smem id' _
                           | Sinst id' _ => if id == id' then True else is_declared ss_tail id
                           | Swhen _ ss_true ss_false =>    is_declared ss_true id
                                                         \/ is_declared ss_false id
                                                         \/ is_declared ss_tail id
                           | _ => is_declared ss_tail id
                           end
      end.

   Fixpoint is_repeatedly_declared (ss : hfstmt_seq) (id : VarOrder.T) : Prop :=
      (* is True if ss contains at least two declarations of components with identifier id. *)
      match ss with
      | Qnil => False
      | Qcons s ss_tail => match s with
                           | Swire id' _
                           | Sreg id' _
                           | Smem id' _
                           | Sinst id' _ => if id == id' then is_declared ss_tail id
                                            else is_repeatedly_declared ss_tail id
                           | Swhen _ ss_true ss_false =>
                                is_repeatedly_declared ss_true id
                             \/ is_declared ss_true id /\ (is_declared ss_false id \/ is_declared ss_tail id)
                             \/ is_repeatedly_declared ss_false id
                             \/ is_declared ss_false id /\ is_declared ss_tail id
                             \/ is_repeatedly_declared ss_tail id
                           | _ => is_repeatedly_declared ss_tail id
                           end
      end.

   Definition expandWhen_ce_OK_hfstmt_seq (ss : hfstmt_seq) : Prop :=
         (forall id : VarOrder.T, is_repeatedly_declared ss id ->
             forall (ce_modules default : CE.env),
                exists e : error_info, expandWhen_ce ss ce_modules default = Err e)
      /\ (forall id : VarOrder.T, is_declared ss id ->
             forall (ce_modules default : CE.env),
                if CE.find id default is None
                then (if expandWhen_ce ss ce_modules default is OK ce_initialized
                      then CE.find id ce_initialized <> None
                      else True)
                else exists e : error_info, expandWhen_ce ss ce_modules default = Err e)
      /\ (forall (id : VarOrder.T) (ce_modules default : CE.env),
             if CE.find id default is Some (c, v)
             then (if expandWhen_ce ss ce_modules default is OK ce_initialized
                   then CE.find id ce_initialized = Some (c, v)
                   else True)
             else True).

   Definition expandWhen_ce_OK_hfstmt (s : hfstmt) : Prop :=
      if s is Swhen c sst ssf then    expandWhen_ce_OK_hfstmt_seq sst
                                   /\ expandWhen_ce_OK_hfstmt_seq ssf
                              else True.

   Lemma expandWhen_ce_OK :
      forall (ss : hfstmt_seq), expandWhen_ce_OK_hfstmt_seq ss.
   Proof.
   apply hfstmt_seq_hfstmt_ind with (P := expandWhen_ce_OK_hfstmt_seq)
                                    (P0 := expandWhen_ce_OK_hfstmt) ;
         try (unfold expandWhen_ce_OK_hfstmt_seq, is_repeatedly_declared ;
              split ; try done ;
              split ; try done ;
              unfold expandWhen_ce ; intros ;
              destruct (CE.find id default) ; try (destruct p ; reflexivity) ; done).
   induction h ;
         try (intros ; unfold expandWhen_ce_OK_hfstmt_seq, is_repeatedly_declared, expandWhen_ce ;
              exact H0).
   * (* Swire *)
     (* This is similar to Sreg below *)
     admit.
   * (* Sreg *)
     unfold expandWhen_ce_OK_hfstmt_seq.
     intros.
     destruct H0.
     destruct H1.
     split.
     + unfold is_repeatedly_declared ; fold is_repeatedly_declared.
       intros.
       unfold expandWhen_ce ; fold expandWhen_ce.
       destruct (CE.find s default) eqn: Hfs ;
             try (exists Ealready_declared ; reflexivity).
       destruct (id == s) eqn: Hid_s ;
             try (apply H0 with (id := id) ; exact H3).
       move /eqP : Hid_s => Hid_s.
       specialize H1 with (id := id) (default := (CE.add s (Reg_typ h, Register) default)).
       rewrite CELemmas.find_add_eq in H1 ; try (unfold CE.SE.eq ; rewrite Hid_s ; apply eq_refl).
       apply H1.
       exact H3.
     split.
     + unfold is_declared ; fold is_declared.
       intros.
       unfold expandWhen_ce ; fold expandWhen_ce.
       destruct (CE.find id default) eqn: Hfid.
       - destruct (CE.find s default) eqn: Hfs ;
               try (exists Ealready_declared ; reflexivity).
         destruct (id == s) eqn: Hid_s ;
               try (move /eqP : Hid_s => Hid_s ;
                    rewrite Hid_s Hfs in Hfid ;
                    done).
         specialize H1 with (id := id) (default := (CE.add s (Reg_typ h, Register) default)).
         rewrite CELemmas.find_add_neq in H1 ;
               try (unfold CE.SE.eq ; rewrite Hid_s ; done).
         rewrite Hfid in H1.
         apply H1.
         exact H3.
       - destruct (CE.find s default) eqn: Hfs ;
               try done.
         destruct (id == s) eqn: Hid_s.
         * move /eqP : Hid_s => Hid_s.
           rewrite <- Hid_s.
           specialize H2 with (id := id) (ce_modules := ce_modules) (default := (CE.add id (Reg_typ h, Register) default)).
           rewrite CELemmas.find_add_eq in H2 ;
                 try (unfold CE.SE.eq ; rewrite Hid_s ; apply eq_refl).
           destruct (expandWhen_ce h0 ce_modules (CE.add id (Reg_typ h, Register) default)) ;
                 try trivial.
           rewrite H2 ; discriminate.
         * specialize H1 with (id := id) (default := (CE.add s (Reg_typ h, Register) default)).
           rewrite CELemmas.find_add_neq in H1 ;
                 try (unfold CE.SE.eq ; rewrite Hid_s ; done).
           rewrite Hfid in H1.
           apply H1.
           exact H3.
     + intros.
       destruct (CE.find id default) eqn: Hfid ; try trivial.
       destruct p.
       unfold expandWhen_ce ; fold expandWhen_ce.
       destruct (CE.find s default) eqn: Hfs ; try trivial.
       specialize H2 with (id := id) (default := CE.add s (Reg_typ h, Register) default).
       destruct (id == s) eqn: Hid_s ;
             try (move /eqP : Hid_s => Hid_s ;
                  rewrite Hid_s Hfs in Hfid ;
                  done).
       rewrite CELemmas.find_add_neq in H2 ; try (unfold CE.SE.eq ; rewrite Hid_s ; done).
       rewrite Hfid in H2.
       apply H2.
   * (* Smem *)
     (* This is similar to Sreg above *)
     admit.
   * (* Sinst *)
     (* This is similar to Sreg above *)
     admit.
   * (* Spcnct *)
     intros.
     unfold expandWhen_ce_OK_hfstmt_seq, expandWhen_ce.
     split.
     + intros ; exists Einternal ; reflexivity.
     split.
     + intros.
       destruct (CE.find id default) ; try trivial.
       exists Einternal ; reflexivity.
     + intros ; destruct (CE.find id default) ; try trivial.
       destruct p ; trivial.
   * (* Swhen *)
     unfold expandWhen_ce_OK_hfstmt, expandWhen_ce_OK_hfstmt_seq.
     intros.
     destruct H, H, H0, H1, H2, H3, H4.
     split.
     + unfold is_repeatedly_declared ; fold is_repeatedly_declared.
       intros.
       unfold expandWhen_ce ; fold expandWhen_ce.
       destruct H8.
       - assert (exists e : error_info, expandWhen_ce h0 ce_modules default = Err e)
               by (apply H with (id := id) ; exact H8).
         destruct H9.
         rewrite H9.
         exists x.
         reflexivity.
       destruct (expandWhen_ce h0 ce_modules default) as [default_true|] eqn: Hew_h0 ;
             try (exists e ; reflexivity).
       destruct (expandWhen_ce h1 ce_modules default_true) as [default_false|] eqn: Hew_h1 ;
             try (exists e ; reflexivity).
       destruct H8.
       - destruct H8.
         specialize H2 with (id := id) (ce_modules := ce_modules) (default := default).
         rewrite Hew_h0 in H2.
         destruct H9.
         * absurd (CE.find id default_true = None).
           + enough (match CE.find id default with
                     | Some _ => exists e : error_info, OK default_true = Err e
                     | None => CE.find id default_true <> None
                     end).
             destruct (CE.find id default) ; try (destruct H10 ; discriminate).
             exact H10.
             apply H2 ; exact H8.
           + specialize H4 with (id := id) (ce_modules := ce_modules) (default := default_true).
             rewrite Hew_h1 in H4.
             destruct (CE.find id default_true) ; try reflexivity.
             destruct H4.
             - exact H9.
             - discriminate.
         * destruct (expandWhen_ce h2 ce_modules default_false) eqn: Hew_h2 ;
                 try (exists e ; reflexivity).
           specialize H3 with (id := id) (ce_modules := ce_modules) (default := default_false).
           rewrite Hew_h2 in H3.
           destruct (CE.find id default_false) eqn: Hfif ; try (apply H3 ; exact H9).
           absurd (CE.find id default_false = None) ; try (exact Hfif).
           specialize H7 with (id := id) (ce_modules := ce_modules) (default := default_true).
           rewrite Hew_h1 in H7.
           destruct (CE.find id default_true) eqn: Hfit ;
                 try (destruct p ; rewrite H7 ; discriminate).
           destruct (CE.find id default).
           + destruct H2 ; try (exact H8) ; discriminate.
           + destruct H2 ; try (exact H8) ; reflexivity.
       destruct H8.
       - specialize H1 with (id := id) (ce_modules := ce_modules) (default := default_true).
         rewrite Hew_h1 in H1.
         destruct H1 ; try (exact H8).
         discriminate.
       destruct H8.
       - specialize H3 with (id := id) (ce_modules := ce_modules) (default := default_false).
         destruct (CE.find id default_false) eqn: Hfif ; try (apply H3, H8).
         absurd (CE.find id default_false = None) ; try (exact Hfif).
         specialize H4 with (id := id) (ce_modules := ce_modules) (default := default_true).
         rewrite Hew_h1 in H4.
         destruct (CE.find id default_true) ; try (apply H4, H8).
         destruct H4 ; try (apply H8).
         discriminate.
       - specialize H0 with (id := id) (ce_modules := ce_modules) (default := default_false).
         apply H0.
         exact H8.
     split.
     + unfold is_declared ; fold is_declared.
       intros.
       unfold expandWhen_ce ; fold expandWhen_ce.
       destruct H8.
       - specialize H2 with (id := id) (ce_modules := ce_modules) (default := default).
         destruct (CE.find id default) eqn: Hfi.
         + destruct H2 ; try (exact H8).
           rewrite H2.
           exists x ; reflexivity.
         + destruct (expandWhen_ce h0 ce_modules default) as [default_true|] eqn: Hew_h0 ; try trivial.
           specialize H7 with (id := id) (ce_modules := ce_modules) (default := default_true).
           destruct (expandWhen_ce h1 ce_modules default_true) as [default_false|] eqn: Hew_h1 ; try trivial.
           specialize H6 with (id := id) (ce_modules := ce_modules) (default := default_false).
           destruct (expandWhen_ce h2 ce_modules default_false) as [default_end|] eqn: Hew_h2 ; try trivial.
           destruct (CE.find id default_false) eqn: Hfif ; try (destruct p ; rewrite H6 ; discriminate).
           contradict Hfif.
           destruct (CE.find id default_true) eqn: Hfit ; try (destruct p; rewrite H7 ; discriminate).
           destruct H2 ; try (exact H8).
           reflexivity.
       specialize H5 with (id := id) (ce_modules := ce_modules) (default := default).
       destruct H8.
       - destruct (CE.find id default) eqn: Hfi.
         * destruct (expandWhen_ce h0 ce_modules default) as [default_true|] eqn: Hew_h0 ; try (exists e ; reflexivity).
           destruct p.
           specialize H4 with (id := id) (ce_modules := ce_modules) (default := default_true).
           rewrite H5 in H4.
           destruct H4 ; try (exact H8).
           rewrite H4.
           exists x ; reflexivity.
         * destruct (expandWhen_ce h0 ce_modules default) as [default_true|] eqn: Hew_h0 ; try trivial.
           specialize H4 with (id := id) (ce_modules := ce_modules) (default := default_true).
           destruct (expandWhen_ce h1 ce_modules default_true) as [default_false|] eqn: Hew_h1 ; try trivial.
           specialize H6 with (id := id) (ce_modules := ce_modules) (default := default_false).
           destruct (expandWhen_ce h2 ce_modules default_false) as [default_end|] eqn: Hew_h2 ; try trivial.
           destruct (CE.find id default_false) eqn: Hfif ; try (destruct p ; rewrite H6 ; discriminate).
           destruct (CE.find id default_true) eqn: Hfit ; try (destruct H4 ; try (exact H8) ; discriminate).
           destruct H4 ; try (exact H8) ; reflexivity.
       - destruct (CE.find id default) eqn: Hfi.
         * destruct (expandWhen_ce h0 ce_modules default) as [default_true|] eqn: Hew_h0 ; try (exists e ; reflexivity).
           destruct p.
           specialize H7 with (id := id) (ce_modules := ce_modules) (default := default_true).
           rewrite H5 in H7.
           destruct (expandWhen_ce h1 ce_modules default_true) as [default_false|] eqn: Hew_h1 ; try (exists e ; reflexivity).
           specialize H3 with (id := id) (ce_modules := ce_modules) (default := default_false).
           rewrite H7 in H3.
           apply H3.
           exact H8.
         * destruct (expandWhen_ce h0 ce_modules default) as [default_true|] eqn: Hew_h0 ; try trivial.
           specialize H7 with (id := id) (ce_modules := ce_modules) (default := default_true).
           destruct (expandWhen_ce h1 ce_modules default_true) as [default_false|] eqn: Hew_h1 ; try trivial.
           specialize H3 with (id := id) (ce_modules := ce_modules) (default := default_false).
           destruct (expandWhen_ce h2 ce_modules default_false) as [default_end|] eqn: Hew_h2 ; try trivial.
           destruct (CE.find id default_false) eqn: Hfif ; try (apply H3 ; exact H8).
           destruct H3 ; try (apply H8).
           discriminate.
     + intros.
       unfold expandWhen_ce ; fold expandWhen_ce.
       specialize H5 with (id := id) (ce_modules := ce_modules) (default := default).
       destruct (CE.find id default) eqn: Hfi ; try trivial.
       destruct p.
       destruct (expandWhen_ce h0 ce_modules default) as [default_true|] eqn: Hew_h0 ; try trivial.
       specialize H7 with (id := id) (ce_modules := ce_modules) (default := default_true).
       rewrite H5 in H7.
       destruct (expandWhen_ce h1 ce_modules default_true) as [default_false|] eqn: Hew_h1 ; try trivial.
       specialize H6 with (id := id) (ce_modules := ce_modules) (default := default_false).
       rewrite H7 in H6.
       exact H6.
   Admitted.

   Definition is_declared_OK_hfstmt_seq (ss : hfstmt_seq) : Prop :=
      forall (ce_modules default : CE.env),
         if expandWhen_ce ss ce_modules default is OK ce_initialized
         then (forall (id : VarOrder.T),
                  if CE.find id ce_initialized is Some (c, v)
                  then is_declared ss id \/ CE.find id default = Some (c, v)
                  else True)
         else True.

   Definition is_declared_OK_hfstmt (s : hfstmt) : Prop :=
      if s is Swhen _ sst ssf
      then is_declared_OK_hfstmt_seq sst /\ is_declared_OK_hfstmt_seq ssf
      else True.

   Lemma is_declared_OK :
       forall (ss : hfstmt_seq), is_declared_OK_hfstmt_seq ss.
   Proof.
   apply hfstmt_seq_hfstmt_ind with (P := is_declared_OK_hfstmt_seq)
                                    (P0 := is_declared_OK_hfstmt) ;
         try (unfold is_declared_OK_hfstmt ; trivial).
   * (* Qnil *)
     unfold is_declared_OK_hfstmt_seq, expandWhen_ce, is_declared.
     intros.
     destruct (CE.find id default) ; try trivial.
     destruct p ; right ; reflexivity.
   * (* Qcons *)
     induction h ;
           try (intros ;
                unfold is_declared_OK_hfstmt_seq, is_declared, expandWhen_ce ;
                fold expandWhen_ce ;
                fold is_declared ;
                exact H0).
     + (* Swire *)
       (* This is similar to Sreg below *)
       admit.
     + (* Sreg *)
       unfold is_declared_OK_hfstmt_seq, is_declared, expandWhen_ce ;
       fold expandWhen_ce ;
       fold is_declared.
       intros.
       destruct (CE.find s default) eqn: Hfis ; try trivial.
       specialize H0 with (ce_modules := ce_modules) (default := CE.add s (Reg_typ h, Register) default).
       destruct (expandWhen_ce h0 ce_modules (CE.add s (Reg_typ h, Register) default)) eqn: He_h0 ; try trivial.
       intro.
       specialize H0 with (id := id).
       destruct (CE.find id e) eqn: Hfid ; try trivial.
       destruct p.
       destruct (id == s) eqn: Hid_s ; try auto.
       rewrite CELemmas.find_add_neq in H0 ; try (unfold CE.SE.eq ; rewrite Hid_s ; done).
       exact H0.
     + (* Smem *)
       (* This is similar to Sreg above *)
       admit.
     + (* Sinst *)
       (* This is similar to Sreg above *)
       admit.
     + (* Spcnct *)
       unfold is_declared_OK_hfstmt_seq, expandWhen_ce.
       trivial.
     + (* Swhen *)
       unfold is_declared_OK_hfstmt_seq, is_declared, expandWhen_ce ;
       fold expandWhen_ce ;
       fold is_declared.
       intros.
       destruct H.
       specialize H with (ce_modules := ce_modules) (default := default).
       destruct (expandWhen_ce h0 ce_modules default) as [default_true|] eqn: Hew_h0 ; try trivial.
       specialize H1 with (ce_modules := ce_modules) (default := default_true).
       destruct (expandWhen_ce h1 ce_modules default_true) as [default_false|] eqn: Hew_h1 ; try trivial.
       specialize H0 with (ce_modules := ce_modules) (default := default_false).
       destruct (expandWhen_ce h2 ce_modules default_false) as [default_end|] eqn: Hew_h2 ; try trivial.
       intro.
       specialize H0 with (id := id).
       destruct (CE.find id default_end) eqn: Hfie ; try trivial.
       destruct p.
       destruct H0.
       + left ; right ; right ; exact H0.
       + specialize H1 with (id := id).
         rewrite H0 in H1.
         destruct H1.
         - left ; right ; left ; exact H1.
         - specialize H with (id := id).
           rewrite H1 in H.
           destruct H.
           * left ; left ; exact H.
           * right ; exact H.
   * (* subgoal related to Swhen *)
     intros ; split.
     exact H.
     exact H0.
   Admitted.

   Definition no_repeated_declarations (ss : hfstmt_seq) (default : CE.env) : Prop :=
      forall (id : VarOrder.T), if CE.find id default is Some _ then ~is_declared ss id
                                else ~is_repeatedly_declared ss id.

(* Axiom cenv_elt_eq_dec : forall {x y : option (cmpnt_init_typs * fcomponent)}, {x = y} + {x <> y}.
   Parameter cenv_elt_eqn: forall (x y : option (cmpnt_init_typs * fcomponent)), bool.
   Axiom cenv_elt_eqP : Equality.axiom cenv_elt_eqn.
   Canonical cenv_elt_eqMixin := EqMixin cenv_elt_eqP. *)

   (* If a (hfstmt_seq * CE.env) satisfies the precondition,
      then expandWhen_ce does not produce an error.
      We need to prove this by a mutual induction over htstmt and hfstmt_seq. *)
   Definition precond_impl_ce_OK_hfstmt_seq (ce_modules : CE.env) (ss : hfstmt_seq) : Prop :=
      forall (default : CE.env),
         expandWhen_precondition_ss ss ce_modules ->
         no_repeated_declarations ss default ->
            forall e : error_info, expandWhen_ce ss ce_modules default <> Err e.

   Definition precond_impl_ce_OK_hfstmt (ce_modules : CE.env) (s : hfstmt) : Prop :=
      if s is Swhen c sst ssf then    precond_impl_ce_OK_hfstmt_seq ce_modules sst
                                   /\ precond_impl_ce_OK_hfstmt_seq ce_modules ssf
                              else True.

   Lemma precond_impl_ce_OK :
      forall (ce_modules : CE.env) (ss : hfstmt_seq),
         precond_impl_ce_OK_hfstmt_seq ce_modules ss.
   Proof.
   intro.
   apply hfstmt_seq_hfstmt_ind with (P := precond_impl_ce_OK_hfstmt_seq ce_modules)
                                    (P0 := precond_impl_ce_OK_hfstmt ce_modules) ;
         try (unfold precond_impl_ce_OK_hfstmt ; trivial) ;
         try (unfold precond_impl_ce_OK_hfstmt_seq, expandWhen_precondition_ss, expandWhen_ce ;
              discriminate) ;
         try (intros ; split ; try (exact H) ; exact H0).
   unfold precond_impl_ce_OK_hfstmt_seq.
   induction h ;
         try (unfold expandWhen_precondition_ss ; fold expandWhen_precondition_ss ;
              intros ;
              unfold expandWhen_ce ; fold expandWhen_ce ;
              apply H0 ; try (exact H1) ;
              unfold no_repeated_declarations, is_declared, is_repeatedly_declared in H2 ;
              exact H2).
   * (* Swire *)
     (* This case is similar to Sreg below. So we skip it. *)
     admit.
   * (* Sreg *)
     intros.
     unfold expandWhen_precondition_ss in H1 ; fold expandWhen_precondition_ss in H1.
     unfold expandWhen_ce ; fold expandWhen_ce.
     unfold no_repeated_declarations in H2.
     destruct (CE.find s default) eqn: Hsdef.
     + specialize H2 with (id := s).
       rewrite Hsdef in H2.
       unfold is_declared in H2.
       rewrite eq_refl in H2.
       contradiction.
     + apply H0.
       move /andP : H1 => H1.
       apply H1.
       unfold no_repeated_declarations.
       intro.
       specialize H2 with (id := id).
       destruct (id == s) eqn: Hid_s.
       - move/eqP : Hid_s => Hid_s.
         rewrite Hid_s.
         replace (CE.find s (CE.add s (Reg_typ h, Register) default)) with (Some (Reg_typ h, Register))
                by (symmetry ; apply CELemmas.find_add_eq, eq_refl).
         unfold is_repeatedly_declared in H2.
         rewrite Hid_s Hsdef eq_refl in H2.
         exact H2.
       - replace (CE.find id (CE.add s (Reg_typ h, Register) default)) with (CE.find id default)
                by (symmetry ; apply CELemmas.find_add_neq ;
                    unfold CE.SE.eq ;
                    rewrite Hid_s ; done).
         destruct (CE.find id default) eqn: Hfind.
         * unfold is_declared in H2.
           rewrite Hid_s in H2.
           exact H2.
         * unfold is_repeatedly_declared in H2.
           rewrite Hid_s in H2.
           exact H2.
   * (* Smem *)
     (* This case is similar to Sreg above. So we skip it. *)
     admit.
   * (* Sinst *)
     (* This case is similar to Sreg above. So we skip it. *)
     admit.
   * (* Spcnct *)
     done.
   * (* Swhen *)
     intro ; intro ; intro.
     unfold expandWhen_precondition_ss ; fold expandWhen_precondition_ss.
     intros.
     move /andP : H1 => H1.
     destruct H1.
     move /andP : H1 => H1.
     unfold expandWhen_ce ; fold expandWhen_ce.
     destruct H.
     specialize H with (default := default).
     assert (is_declared_OK_hfstmt_seq h0) by (apply is_declared_OK).
     unfold is_declared_OK_hfstmt_seq in H5.
     specialize H5 with (ce_modules := ce_modules) (default := default).
     destruct (expandWhen_ce h0 ce_modules default) as [default_true|] eqn: He_h0.
     + specialize H4 with (default := default_true).
       assert (is_declared_OK_hfstmt_seq h1) by (apply is_declared_OK).
       unfold is_declared_OK_hfstmt_seq in H6.
       specialize H6 with (ce_modules := ce_modules) (default := default_true).
       destruct (expandWhen_ce h1 ce_modules default_true) as [default_false|] eqn: He_h1.
       - apply H0.
         exact H3.
         unfold no_repeated_declarations.
         unfold no_repeated_declarations, is_declared, is_repeatedly_declared in H2.
         fold is_repeatedly_declared in H2.
         fold is_declared in H2.
         intro.
         specialize H2 with (id := id).
         destruct (CE.find id default) eqn: Hf_def.
         * assert (forall (ss : hfstmt_seq) (id : VarOrder.T) (ce_modules default : CE.env),
                      if CE.find id default is Some (c, v)
                      then (if expandWhen_ce ss ce_modules default is OK ce_initialized
                            then CE.find id ce_initialized = Some (c, v)
                            else True)
                      else True)
                 by (apply expandWhen_ce_OK).
           assert (CE.find id default_true = Some p).
             specialize H7 with (ss := h0) (id := id) (ce_modules := ce_modules) (default := default).
             destruct p.
             rewrite Hf_def He_h0 in H7.
             exact H7.
           assert (CE.find id default_false = Some p).
             specialize H7 with (ss := h1) (id := id) (ce_modules := ce_modules) (default := default_true).
             destruct p.
             rewrite H8 He_h1 in H7.
             exact H7.
           rewrite H9.
           contradict H2.
           right ; right ; exact H2.
         * specialize H6 with (id := id).
           destruct (CE.find id default_false) eqn: Hfif.
           + destruct p.
             destruct H6.
             - contradict H2.
               right ; right ; right ; left.
               split.
               * exact H6.
               * exact H2.
             - specialize H5 with (id := id).
               destruct (CE.find id default_true) eqn: Hfit ; try discriminate.
               destruct p.
               destruct H5 ; try (rewrite Hf_def in H5 ; discriminate).
               contradict H2.
               right ; left ; split.
               - exact H5.
               - right ; exact H2.
           + contradict H2.
             right ; right ; right ; right.
             exact H2.
       - apply H4.
         apply H1.
         unfold no_repeated_declarations.
         unfold no_repeated_declarations in H2.
         intro.
         specialize H2 with (id := id).
         specialize H5 with (id := id).
         destruct (CE.find id default_true) eqn: Hfit.
         * destruct p.
           destruct H5.
           + destruct (CE.find id default) eqn: Hfi.
             - unfold is_declared in H2 ; fold is_declared in H2.
               contradict H2.
               left ; exact H5.
             - unfold is_repeatedly_declared in H2 ; fold is_repeatedly_declared in H2.
               contradict H2.
               right ; left ; split.
               * exact H5.
               * left ; exact H2.
           + rewrite H5 in H2.
             unfold is_declared in H2 ; fold is_declared in H2.
             contradict H2.
             right ; left ; exact H2.
         * destruct (CE.find id default) eqn: Hfi.
           + absurd (CE.find id default_true = None) ; try (exact Hfit).
             assert (if CE.find id default is Some (c, v)
                     then (if expandWhen_ce h0 ce_modules default is OK ce_initialized
                           then CE.find id ce_initialized = Some (c, v)
                           else True)
                     else True) by (apply expandWhen_ce_OK).
             rewrite Hfi in H7.
             destruct p.
             rewrite He_h0 in H7.
             rewrite H7.
             discriminate.
           + unfold is_repeatedly_declared in H2 ; fold is_repeatedly_declared in H2.
             contradict H2.
             right ; right ; left ; exact H2.
     + apply H.
       apply H1.
        (* The rest of this branch is almost the same as the previous branch. *)
       admit.
   Admitted.

   Definition type_and_dir_of_ref (ref : href) (ce : CE.env) : @error_type (ftype * forient) :=
      (* calculates the type and flow direction of ref.
         * ref = some href that does not contain subaccesses
         * ce = component environment that contains (at least) the declaration of
           the base of ref.
         Result: (type of ref, orientation of ref)

         Example: Let a have type { b : Atyp (FUint 4) 5, c : Clock },
         that is Fflips "b" Nflip (Atyp (Gtyp (FUint 4)) 5) (Fflips "c" Nflip (Gtyp Clock) Fnil).
         Then a.b[2] is (Esubindex (Esubfield (Eid "a") "b") 2) in the abstract syntax,
         and it is calculated as follows:
         a has type { b : Atyp (FUint 4) 5, c : Clock }, so a.b has type Atyp (Gtyp (FUint 4)) 5.
         From this, a.b[2] has type Gtyp (FUint 4). *)
      match CE.find (base_ref ref) ce with
      | Some (Aggr_typ t, Wire) => type_and_dir_of_ref' ref t Duplex
      | Some (Aggr_typ t, Instanceof)
      | Some (Aggr_typ t, In_port) => type_and_dir_of_ref' ref t Source
      | Some (Aggr_typ t, Out_port) => type_and_dir_of_ref' ref t Sink
      | Some (Reg_typ r, Register) => type_and_dir_of_ref' ref (type r) Passive
      | Some (Mem_typ m, Memory) => match type_of_mem m with Err e => Err e | OK tm
                                    => type_and_dir_of_ref' ref tm Source end
      | _ => Err Etype
      end.

   Lemma type_and_dir_of_ref_OK :
      forall (ref : href) (ce : CE.env),
         (forall e : error_info, type_and_dir_of_ref ref ce <> Err e) ->
            href_without_subaccess ref.
   Proof.
   induction ref.
   * done.
   * intros.
     unfold href_without_subaccess ; fold href_without_subaccess.
     apply IHref with (ce := ce).
     unfold type_and_dir_of_ref.
     unfold type_and_dir_of_ref in H.
     unfold base_ref in H ; fold base_ref in H.
     destruct (CE.find (base_ref ref) ce) ; try exact H.
     destruct p.
     destruct c.
     + destruct f ; try exact H ;
             try (intro ; contradict H ;
                  unfold type_and_dir_of_ref' ; fold type_and_dir_of_ref' ;
                  replace (type_and_dir_of_ref' ref f0 Source) with (@Err (ftype * forient) e) ;
                  intro ; specialize H0 with (e0 := e) ; done).
       - intro ; contradict H.
         unfold type_and_dir_of_ref' ; fold type_and_dir_of_ref'.
         replace (type_and_dir_of_ref' ref f0 Sink) with (@Err (ftype * forient) e).
         intro ; specialize H0 with (e0 := e) ; done.
       - intro ; contradict H.
         unfold type_and_dir_of_ref' ; fold type_and_dir_of_ref'.
         replace (type_and_dir_of_ref' ref f0 Duplex) with (@Err (ftype * forient) e).
         intro ; specialize H0 with (e0 := e) ; done.
     + destruct f ; try exact H.
       intro ; contradict H.
       unfold type_and_dir_of_ref' ; fold type_and_dir_of_ref'.
       replace (type_and_dir_of_ref' ref (type h) Passive) with (@Err (ftype * forient) e).
       intro ; specialize H0 with (e0 := e) ; done.
     + destruct f ; try exact H.
       destruct (type_of_mem h) ; try exact H.
       intro ; contradict H.
       unfold type_and_dir_of_ref' ; fold type_and_dir_of_ref'.
       replace (type_and_dir_of_ref' ref f Source) with (@Err (ftype * forient) e).
       intro ; specialize H0 with (e0 := e) ; done.
     + exact H.
   * intros.
     unfold href_without_subaccess ; fold href_without_subaccess.
     apply IHref with (ce := ce).
     unfold type_and_dir_of_ref.
     unfold type_and_dir_of_ref in H.
     unfold base_ref in H ; fold base_ref in H.
     destruct (CE.find (base_ref ref) ce) ; try exact H.
     destruct p.
     destruct c.
     + destruct f ; try exact H ;
             try (intro ; contradict H ;
                  unfold type_and_dir_of_ref' ; fold type_and_dir_of_ref' ;
                  replace (type_and_dir_of_ref' ref f0 Source) with (@Err (ftype * forient) e) ;
                  intro ; specialize H0 with (e0 := e) ; done).
       - intro ; contradict H.
         unfold type_and_dir_of_ref' ; fold type_and_dir_of_ref'.
         replace (type_and_dir_of_ref' ref f0 Sink) with (@Err (ftype * forient) e).
         intro ; specialize H0 with (e0 := e) ; done.
       - intro ; contradict H.
         unfold type_and_dir_of_ref' ; fold type_and_dir_of_ref'.
         replace (type_and_dir_of_ref' ref f0 Duplex) with (@Err (ftype * forient) e).
         intro ; specialize H0 with (e0 := e) ; done.
     + destruct f ; try exact H.
       intro ; contradict H.
       unfold type_and_dir_of_ref' ; fold type_and_dir_of_ref'.
       replace (type_and_dir_of_ref' ref (type h) Passive) with (@Err (ftype * forient) e).
       intro ; specialize H0 with (e0 := e) ; done.
     + destruct f ; try exact H.
       destruct (type_of_mem h) ; try exact H.
       intro ; contradict H.
       unfold type_and_dir_of_ref' ; fold type_and_dir_of_ref'.
       replace (type_and_dir_of_ref' ref f Source) with (@Err (ftype * forient) e).
       intro ; specialize H0 with (e0 := e) ; done.
     + exact H.
   * intros ; contradict H.
     unfold type_and_dir_of_ref, type_and_dir_of_ref'.
     destruct (CE.find (base_ref (Esubaccess ref h)) ce) ;
           try (intro ;
                specialize H with (e := Etype) ;
                done).
     destruct p.
     destruct c.
     + destruct f ;
             try (intro ;
                  specialize H with (e := Einternal) ;
                  done) ;
             try (intro ;
                  specialize H with (e := Etype) ;
                  done).
     + destruct f ;
             try (intro ;
                  specialize H with (e := Etype) ;
                  done) ;
             try (intro ;
                  specialize H with (e := Einternal) ;
                  done).
     + destruct f ;
             try (intro ;
                  specialize H with (e := Etype) ;
                  done).
       destruct (type_of_mem h0) ;
             try (intro ;
                  specialize H with (e := Einternal) ;
                  done).
       intro ; specialize H with (e0 := e) ; done.
     + intro ; specialize H with (e := Etype) ; done.
   Qed.

   Definition is_ground_sink (ref : href) (ce : CE.env) : bool :=
      (* returns true if ref is a reference of ground type with sink, duplex or passive flow direction.
         (Only registers are passive, and they have duplex flow). *)
      match type_and_dir_of_ref ref ce with
      | OK (Gtyp _, Sink)
      | OK (Gtyp _, Duplex)
      | OK (Gtyp _, Passive) => true
      | _ => false
      end.

   Lemma expandWhen_one_var_sem_conform (ref : href) :
      (* The variable ref, which has ground type and has sink (or duplex) flow,
         is assigned the correct value.
         ce = contains definitions of other modules.
         (Probably needs additional precondition that ref is a correct reference.) *)
      href_without_subaccess ref ->
      forall (mdl : hfmodule) (ce_modules : CE.env),
         match mdl with
         | FInmod _ ports ss => forall (initial_cm : cmap) (initial_ce : CE.env),
                                match init_ports ports initial_cm initial_ce with Err e => false | OK (ports_cmap, ports_ce)
                                => expandWhen_precondition_ss ss ce_modules ->
                                   match expandWhen_ce ss ce_modules ports_ce with Err e => false | OK ce_initialized
                                   => is_ground_sink ref ce_initialized ->
                                      match expandBranch_fun ss ce_initialized ports_cmap with Err e => false | OK (_, cm_result)
                                      => match type_and_dir_of_ref ref ce_initialized with
                                         | OK (Gtyp t, Sink) | OK (Gtyp t, Duplex) | OK (Gtyp t, Passive) =>
                                              expandBranch_one_component_sem_conform ref (Gtyp t) ss cm_result ports_cmap
                                         | _ => true end end end end
         | FExmod _ _ _ => true (* cannot be checked *)
         end.
   Proof.
   destruct mdl as [_ ports ss|] ; try done.
   intros.
   destruct (init_ports ports initial_cm initial_ce) eqn: Hipo ;
         try (contradict Hipo ; apply init_ports_OK).
   destruct p as [ports_cmap ports_ce].
   destruct (expandWhen_ce ss ce_modules ports_ce) as [ce_initialized|] eqn : HeWce ;
         try (intros ; contradict HeWce ; apply precond_impl_ce_OK ; exact H0).
   move : initial_cm initial_ce ports_cmap ports_ce Hipo ce_initialized HeWce.
   induction ss as [|s].
   * intros.
     unfold expandBranch_fun.
     destruct (type_and_dir_of_ref ref ce_initialized) eqn: Htdr ; try done.
     destruct p as [type_of_ref dir_of_ref].
     destruct type_of_ref ; try done.
     unfold expandBranch_one_component_sem_conform.
     destruct (ref2var ref) eqn: Hr2v.
     + destruct (CE.find s ports_cmap).
       - destruct d ; unfold expandBranch_one_var_sem, expr_tree_to_def_expr ; destruct dir_of_ref ; done.
       - unfold expr_tree_to_def_expr ; destruct dir_of_ref ; done.
     + contradict Hr2v.
       apply ref2var_OK.
       apply type_and_dir_of_ref_OK with (ce := ce_initialized).
       rewrite Htdr.
       discriminate.
   * destruct s as [|id type|id reg|id mem| | | | | |].
     + (* Sskip *)
       unfold expandWhen_ce ; fold expandWhen_ce.
       unfold expandWhen_precondition_ss ; fold expandWhen_precondition_ss.
       unfold expandBranch_fun ; fold expandBranch_fun.
       apply IHss.
     + (* Swire -- this case is similar to Sreg *)
       admit.
     + (* Sreg *)
       unfold expandWhen_ce ; fold expandWhen_ce.
       unfold expandWhen_precondition_ss ; fold expandWhen_precondition_ss.
       intros.
       move /andP : H0 => H0.
       unfold expandBranch_fun ; fold expandBranch_fun.
       destruct (init_register id (type reg) ports_cmap) as [cm_reg|] eqn: Hiw ;
             try (contradict Hiw ;
                  apply init_register_OK, H0).
       specialize IHss with (initial_ce := initial_ce)
                            (ports_cmap := cm_reg)
                            (ports_ce := CE.add id (aggr_typ (type reg), Register) ports_ce)
                            (ce_initialized := ce_initialized).
       (* destruct (init_register id (type reg) initial_cm) eqn: Hiw_i ;
             try (contradict Hiw_i ;
                  apply init_register_OK, H0). *)
       destruct (expandBranch_fun ss ce_initialized cm_reg) eqn: Hebf.
       - destruct p as [ce_result cm_result].
         unfold snd.
         unfold is_ground_sink in H1.
         destruct (type_and_dir_of_ref ref ce_initialized) eqn: Htdf ; try done.
         destruct p as [type_of_ref dir_of_ref].
         destruct type_of_ref  ; try done.
         (*destruct dir_of_ref ; try done.*)
         unfold expandBranch_one_component_sem_conform.
         unfold expandBranch_one_component_sem_conform in IHss.
         unfold expandBranch_one_var_sem ; fold expandBranch_one_var_sem.
         destruct (base_ref ref == id) eqn: Href_id.
         destruct (ref2var ref) eqn: Hr2v.
         assert (CE.find s cm_reg <> None) by (admit) (* based on init_register_OK *).
   Admitted.

   Definition expandBranch_sem_conform (mdl : hfmodule) (ce_modules : CE.env) : Prop :=
   (* Checks for all components declared in module mdl
      whether expandBranch_fun satisfies the specification.
      * mdl = module to be checked
      * ce_modules = component environment containing all port declarations of other modules *)
   match mdl with
   | FInmod _ ports ss => expandWhen_precondition_ss ss ce_modules ->
                          match init_ports ports empty_cmap (CE.empty (cmpnt_init_typs * fcomponent)) with Err e => false | OK (ports_cmap, ports_ce)
                          => match expandWhen_ce ss ce_modules ports_ce with Err e => false | OK ce_initialized
                             => match expandBranch_fun ss ce_modules ports_cmap with Err e => false | OK result
                                => CE.fold (expandBranch_sem_conform_helper ss (snd result) ports_cmap) ce_initialized
                                            true end end end
   | FExmod _ _ _ => True (* cannot be checked *)
   end.

   Lemma expandBranch_sem_conform_OK:
      forall (mdl : hfmodule) (ce_modules : CE.env),
         expandBranch_sem_conform mdl ce_modules.

(* OLDER MATERIAL -- NOT USED CURRENTLY

What follows is a much simpler version of the proof of correctness, without much error handling,
and without looking into expression trees.

   Definition expandBranch_hfstmt_seq_sem_conform (ss : hfstmt_seq) : Prop :=
   (* The statements in ss are being translated by expandBranch_fun to correct definitions in a cmap. *)
      expandWhen_precondition_ss ss ->
      forall ce : CE.env, ce = expandWhen_ce ss (CE.empty (cmpnt_init_typs * fcomponent)) ->
                        forall default : cmap, expandBranch_vars_sem ss ce (snd (expandBranch_fun ss ce default None)) default.

   Definition expandBranch_hfstmt_sem_conform (s : hfstmt) : Prop :=
   (* The statement sequences that are part of s are being translated correctly. *)
   match s with @Swhen _ c sst ssf => expandBranch_hfstmt_seq_sem_conform sst /\ expandBranch_hfstmt_seq_sem_conform ssf
              | _ => True end.

   Lemma expandBranch_sem_conform : forall ss : hfstmt_seq, expandBranch_hfstmt_seq_sem_conform ss.
   Proof.
   intro.
   apply hfstmt_seq_hfstmt_ind with (P := expandBranch_hfstmt_seq_sem_conform) (P0 := expandBranch_hfstmt_sem_conform).
   (* case Qnil / empty program *)
   unfold expandBranch_hfstmt_seq_sem_conform.
   intros.
   unfold expandBranch_fun, snd.
   unfold expandBranch_vars_sem, expandBranch_one_var_sem.
   intros.
   destruct (CE.find id default).
   induction d ; try (unfold expr_tree_to_def_expr ; apply eq_refl).
   unfold expr_tree_to_def_expr ; apply eq_refl.
   (* case Qcons / concatenation of statements *)
   intros.
   unfold expandBranch_hfstmt_seq_sem_conform.
   intros.
   (* now we need to distinguish cases: if h is Sfcnct or Swhen,
      need to do some work; otherwise, the resulting function does not change,
      and we can apply the induction hypothesis. *)
   induction h.
   (* subcase Qcons Sskip _ *)
   unfold expandBranch_vars_sem, expandBranch_fun.
   fold expandBranch_fun.
   unfold expandBranch_one_var_sem.
   fold expandBranch_one_var_sem.
   unfold expandBranch_hfstmt_seq_sem_conform, expandBranch_vars_sem in H0.
   apply H0.
   unfold expandWhen_precondition_ss in H1.
   fold expandWhen_precondition_ss in H1.
   exact H1.
   (* subcase Qcons (Swire _ _) _ *)
   unfold expandBranch_vars_sem, expandBranch_fun.
   unfold snd at 1.
   fold expandBranch_fun.
   unfold expandBranch_one_var_sem.
   fold expandBranch_one_var_sem.
   intro.
   unfold expandWhen_precondition_ss in H1.
   fold expandWhen_precondition_ss in H1.
   induction f.
   unfold expandBranch_hfstmt_seq_sem_conform, expandBranch_vars_sem in H0.
   (* case distinction on whether id == s or not *)
   case Eq : (eid id == eid s).
   replace id with s.
   replace (Some r_default) with (SV.find s (SV.upd s r_default default)).
   apply H0.
   exact H1.
   exact H2.
   apply SV.find_upd_eq.
   apply eq_refl.
   symmetry.
   move/eqP : Eq => Eq.
   injection Eq ; done.
   replace (SV.find id default) with (SV.find id (SV.upd s r_default default)).
   apply H0.
   exact H1.
   exact H2.
   apply SV.find_upd_neq.
   move /negbT: Eq.
   apply contra_neq.
   intro.
   replace id with s.
   reflexivity.
   contradiction H1.
   contradiction H1.
   (* subcase Qcons (Sreg _ _) _ *)
   unfold expandBranch_vars_sem, expandBranch_fun.
   unfold snd at 1.
   fold expandBranch_fun.
   unfold expandBranch_one_var_sem.
   fold expandBranch_one_var_sem.
   unfold expandBranch_hfstmt_seq_sem_conform, expandBranch_vars_sem in H0.
   intro.
   unfold expandWhen_precondition_ss in H1.
   fold expandWhen_precondition_ss in H1.
   induction (type h).
   case Eq : (eid id == eid s).
   replace id with s.
   replace (Some (r_fexpr (Eref (eid s)))) with (SV.find s (SV.upd s (r_fexpr (Eref (eid s))) default)).
   apply H0.
   exact H1.
   exact H2.
   apply SV.find_upd_eq.
   apply eq_refl.
   symmetry.
   move/eqP : Eq => Eq.
   injection Eq ; done.
   replace (SV.find id default) with (SV.find id (SV.upd s (r_fexpr (Eref (eid s))) default)).
   apply H0.
   exact H1.
   exact H2.
   apply SV.find_upd_neq.
   move /negbT: Eq.
   apply contra_neq.
   intro.
   replace id with s.
   reflexivity.
   contradiction H1.
   contradiction H1.
   (* subcase Qcons (Smem _ _) _ *)
   unfold expandBranch_vars_sem, expandBranch_fun.
   unfold snd at 1.
   fold expandBranch_fun.
   unfold expandBranch_one_var_sem.
   fold expandBranch_one_var_sem.
   unfold expandBranch_vars_sem in H0.
   apply H0.
   unfold expandWhen_precondition_ss in H1.
   fold expandWhen_precondition_ss in H1.
   induction (data_type h).
   exact H1.
   contradiction H1.
   contradiction H1.
   exact H2.
   (* subcase Qcons (Sinst _ _) _ *)
   unfold expandBranch_vars_sem, expandBranch_fun.
   fold expandBranch_fun.
   unfold expandBranch_one_var_sem.
   fold expandBranch_one_var_sem.
   unfold expandBranch_vars_sem in H0.
   apply H0.
   unfold expandWhen_precondition_ss in H1.
   fold expandWhen_precondition_ss in H1.
   exact H1.
   exact H2.
   (* subcase Qcons (Snode _ _) _ *)
   unfold expandBranch_vars_sem, expandBranch_fun.
   fold expandBranch_fun.
   unfold expandBranch_one_var_sem.
   fold expandBranch_one_var_sem.
   unfold expandBranch_vars_sem in H0.
   apply H0.
   unfold expandWhen_precondition_ss in H1.
   fold expandWhen_precondition_ss in H1.
   exact H1.
   exact H2.
   (* subcase Qcons (Sfcnct _ _) _ *)
   unfold expandBranch_vars_sem, expandBranch_fun.
   fold expandBranch_fun.
   unfold expandBranch_one_var_sem.
   fold expandBranch_one_var_sem.
   unfold expandBranch_hfstmt_seq_sem_conform, expandBranch_vars_sem in H0.
   intro.
   unfold expandWhen_precondition_ss in H1.
   fold expandWhen_precondition_ss in H1.
   unfold eid.
   induction h.
   case Eq : (Eid id == Eid s).
   replace (Some (r_fexpr h1)) with (SV.find id (SV.upd (expand_eref (Eid s) ce) (r_fexpr h1) default)).
   apply H0.
   exact H1.
   exact H2.
   replace (Eid s) with (Eid id).
   unfold expand_eref.
   apply SV.find_upd_eq.
   apply eq_refl.
   move/eqP : Eq => Eq.
   exact Eq.
   replace (SV.find id default) with (SV.find id (SV.upd (expand_eref (Eid s) ce) (r_fexpr h1) default)).
   apply H0.
   exact H1.
   exact H2.
   unfold expand_eref.
   apply SV.find_upd_neq.
   move /negbT: Eq.
   apply contra_neq.
   intro.
   replace id with s.
   reflexivity.
   contradiction H1.
   contradiction H1.
   contradiction H1.
   (* subcase Qcons (Spcnct _ _) _ *)
   contradiction H1.
   (* subcase Qcond (Sinvalid _) _ *)
   unfold expandBranch_vars_sem, expandBranch_fun.
   fold expandBranch_fun.
   unfold expandBranch_one_var_sem.
   fold expandBranch_one_var_sem.
   unfold expandBranch_vars_sem in H0.
   apply H0.
   unfold expandWhen_precondition_ss in H1.
   fold expandWhen_precondition_ss in H1.
   exact H1.
   exact H2.
   (* subcase Qcons (Swhen _ _ _) _ *)
   unfold expandBranch_vars_sem, expandBranch_fun.
   unfold snd at 1.
   fold expandBranch_fun.
   intro.
   unfold expandBranch_one_var_sem.
   fold expandBranch_one_var_sem.
   unfold expandWhen_precondition_ss in H1.
   fold expandWhen_precondition_ss in H1.
   transitivity (expandBranch_one_var_sem h0 (eid id) (SV.find id (snd (combine_branches h (expandBranch_fun h1 ce default)
        (expandBranch_fun h2 ce default))))).
   unfold expandBranch_hfstmt_seq_sem_conform, expandBranch_vars_sem in H0.
   apply H0.
   apply H1.
   apply H2.
   unfold expandBranch_hfstmt_sem_conform, expandBranch_hfstmt_seq_sem_conform, expandBranch_vars_sem in H.
   (* Now comes a case distinction over expandBranch_one_var_sem h1 ...
      and over expandBranch_one_var_sem h2 ... *)
   unfold combine_branches.
   unfold snd at 1.
   replace (SV.find id (SV.map2 (map2_helper_cs_tf h) (expandBranch_fun h1 ce default).2
                                                      (expandBranch_fun h2 ce default).2)) with
     (map2_helper_cs_tf h (SV.find id (snd (expandBranch_fun h1 ce default)))
                          (SV.find id (snd (expandBranch_fun h2 ce default)))).
   unfold map2_helper_cs_tf.
   replace (expandBranch_one_var_sem h1 (eid id) (SV.find id default)) with (SV.find id (snd (expandBranch_fun h1 ce default))).
   replace (expandBranch_one_var_sem h2 (eid id) (SV.find id default)) with (SV.find id (snd (expandBranch_fun h2 ce default))).
   induction (SV.find id (snd (expandBranch_fun h1 ce default))) eqn : Hh1.
   induction (SV.find id (snd (expandBranch_fun h2 ce default))) eqn : Hh2.
   induction a.
   induction a0.
   reflexivity.
   reflexivity.
   induction a0.
   reflexivity.
   reflexivity.
   induction a.
   reflexivity.
   reflexivity.
   induction (SV.find id (snd (expandBranch_fun h2 ce default))) eqn : Hh2.
   reflexivity.
   reflexivity.
   apply H.
   apply H1.
   exact H2.
   apply H.
   apply H1.
   exact H2.
   symmetry.
   apply SV.map2_eq.
   unfold map2_helper_cs_tf.
   apply eq_refl.
   (* subcase Qcons (Sstop _ _ _) _ *)
   (* unfold expandBranch_vars_sem, expandBranch_fun. *)
   (* fold expandBranch_fun. *)
   (* unfold expandBranch_one_var_sem. *)
   (* fold expandBranch_one_var_sem. *)
   (* unfold expandBranch_vars_sem in H0. *)
   (* apply H0. *)
   (* unfold expandWhen_precondition_ss in H1. *)
   (* fold expandWhen_precondition_ss in H1. *)
   (* exact H1. *)
   (* exact H2. *)
   (* case Sskip *)
   move => //.
   (* case Swire _ _ *)
   move => //.
   (* case Sreg _ _ *)
   move => //.
   (* case Smem _ _ *)
   move => //.
   (* case Sinst _ _ *)
   move => //.
   (* case Snode _ _ *)
   move => //.
   (* case Sfcnct _ _ *)
   move => //.
   (* case Spcnct _ _ *)
   move => //.
   (* case Sinvalid _ _ *)
   move => //.
   (* case Swhen _ _ _ *)
   move => //.
   (* case Sstop _ _ _ *)
   (* move => //. *)
   Qed.
END OF OLDER MATERIAL -- NOT USED CURRENTLY *)

(* VERY OLD MATERIAL -- I, David, do not understand what this is meant.
  (** Semantics of declaim ports *)
  Inductive eval_port : hfport -> CE.env -> cstate -> CE.env -> cstate -> Prop :=
  (* in, ground type *)
  | Eval_inport_gt v t ce cs ce' cs':
      CELemmas.P.Add v (aggr_typ (Gtyp t), In_port) ce ce' ->
      (* SV.Upd v (r_ftype (Gtyp t)) cs cs' -> *)
      SV.Upd v (r_default) cs cs' ->
      eval_port (Finput v (Gtyp t)) ce cs ce' cs'
  (* in, vector type *)
  | Eval_inport_at v t n ce cs ce' cs' ce'' cs'':
      0 < n ->
      eval_port (Finput (new_var v (N.of_nat n)) t) ce cs ce'' cs'' ->
      eval_port (Finput v (Atyp t n.-1)) ce' cs' ce'' cs'' ->
      eval_port (Finput v (Atyp t n)) ce cs ce'' cs''
  (* in, bundle type non flip *)
  | Eval_inport_bt_nf v vt t fs n ce cs ce' cs' ce'' cs'':
      0 < n ->
      eval_port (Finput (new_var v vt) t) ce cs ce'' cs'' ->
      eval_port (Finput v (Btyp fs)) ce' cs' ce'' cs'' ->
      eval_port (Finput v (Btyp (Fflips vt Nflip t fs))) ce cs ce'' cs''
  (* in, bundle type flip *)
  | Eval_inport_bt_f v vt t fs n ce cs ce' cs' ce'' cs'':
      0 < n ->
      eval_port (Foutput (new_var v vt) t) ce cs ce'' cs'' ->
      eval_port (Finput v (Btyp fs)) ce' cs' ce'' cs'' ->
      eval_port (Finput v (Btyp (Fflips vt Flipped t fs))) ce cs ce'' cs''
  (* out, ground type *)
  | Eval_outport_gt v t ce cs ce' cs':
      CELemmas.P.Add v (aggr_typ (Gtyp t), In_port) ce ce' ->
      (* SV.Upd v (r_ftype (Gtyp t)) cs cs' -> *)
      SV.Upd v r_default cs cs' ->
      eval_port (Foutput v (Gtyp t)) ce cs ce' cs'
  (* out, vector type *)
  | Eval_outport_at v t n ce cs ce' cs' ce'' cs'':
      0 < n ->
      eval_port (Foutput (new_var v (N.of_nat n)) t) ce cs ce'' cs'' ->
      eval_port (Foutput v (Atyp t n.-1)) ce' cs' ce'' cs'' ->
      eval_port (Foutput v (Atyp t n)) ce cs ce'' cs''
  (* out, bundle type *)
  | Eval_outport_bt_nf v vt t fs n ce cs ce' cs' ce'' cs'':
      0 < n ->
      eval_port (Foutput (new_var v vt) t) ce cs ce'' cs'' ->
      eval_port (Foutput v (Btyp fs)) ce' cs' ce'' cs'' ->
      eval_port (Foutput v (Btyp (Fflips vt Nflip t fs))) ce cs ce'' cs''
  (* out, bundle type flip *)
  | Eval_outport_bt_f v vt t fs n ce cs ce' cs' ce'' cs'':
      0 < n ->
      eval_port (Finput (new_var v vt) t) ce cs ce'' cs'' ->
      eval_port (Foutput v (Btyp fs)) ce' cs' ce'' cs'' ->
      eval_port (Foutput v (Btyp (Fflips vt Flipped t fs))) ce cs ce'' cs''
  .

  Inductive eval_ports : seq hfport -> CE.env -> cstate -> CE.env -> cstate -> Prop :=
  | Eval_ports_nil ce cs : eval_ports [::] ce cs ce cs
  | Eval_ports_cons p ps ce cs ce' cs' ce'' cs'':
      eval_port p ce cs ce' cs' ->
      eval_ports ps ce' cs' ce'' cs'' ->
      eval_ports (p :: ps) ce cs ce'' cs''
  .

  (** Semantics of single statement, update CE.env (var -> fgtyp * fcomponent) and cstate (var -> rhs_expr) *)

  Inductive eval_fstmt_single : hfstmt -> CE.env -> cstate -> CE.env -> cstate -> Prop :=
  | Eval_sskip : forall ce cs, eval_fstmt_single sskip ce cs ce cs
  (* declare wire with ground type *)
  | Eval_swire_gt v t ce cs ce' cs':
      CELemmas.P.Add v (aggr_typ t, Wire) ce ce' ->
      (* SV.Upd v (r_ftype t) cs cs' -> *)
      SV.Upd v r_default cs cs' ->
      eval_fstmt_single (swire v t) ce cs ce' cs'
  (* declare node with expr, valid rhs *)
  | Eval_snode v e ce cs ce' cs':
      valid_rhs_fexpr e ce' ->
      CELemmas.P.Add v (aggr_typ (type_of_hfexpr e ce), Node) ce ce' ->
      SV.Upd v (r_fexpr e) cs cs' ->
      eval_fstmt_single (snode v e) ce cs ce' cs'
  (* define full connection *)
  (* valid flow orient, type eq between dst and src*)
  | Eval_sfcnct v e ce ce' cs cs':
      valid_lhs_orient (orient_of_comp (snd (CE.vtyp (base_ref v) ce))) ->
      valid_rhs_fexpr e ce ->
      ~~ is_deftyp (type_of_ref v ce) ->
      ftype_equiv (type_of_ref v ce) (type_of_hfexpr e ce) ->
      typeConstraintsGe (type_of_ref v ce) (type_of_hfexpr e ce) ->
      CELemmas.P.Add (base_ref v) (CE.vtyp (base_ref v) ce) ce ce' ->
      SV.Upd (new_var (base_ref v) (v2var (get_field_name v))) (r_fexpr e) cs cs' ->
      eval_fstmt_single (sfcnct v e) ce cs ce' cs'
  (* declare reg, reset expr type equiv with reg type*)
  | Eval_sreg_r r t c rc rs ce cs ce' cs' :
      valid_rhs_fexpr rs ce ->
      ftype_equiv (type_of_hfexpr rs ce) t ->
      CELemmas.P.Add r (reg_typ (mk_hfreg t c (rrst rc rs)), Register) ce ce' ->
      (* SV.Upd r (r_fstmt (sreg r (mk_hfreg t c (rrst rc rs)))) cs cs' -> *)
      SV.Upd r r_default cs cs' ->
      eval_fstmt_single (sreg r (mk_hfreg t c (rrst rc rs))) ce cs ce' cs'
  (* declare reg, non reset *)
  | Eval_sreg_nr r t c ce cs ce' cs' :
      CELemmas.P.Add r (reg_typ (mk_hfreg t c nrst) , Register) ce ce' ->
      (* SV.Upd r (r_fstmt (sreg r (mk_hfreg t c nrst))) cs cs' -> *)
      SV.Upd r r_default cs cs' ->
      eval_fstmt_single (sreg r (mk_hfreg t c nrst)) ce cs ce' cs'
  (* declare mem *)
  | Eval_smem m t dp r w rl wl rw ce cs ce' cs' :
      is_passive t ->
      CELemmas.P.Add m (mem_typ (mk_hfmem t dp r w rl wl rw), Memory) ce ce' ->
      (* SV.Upd m (r_fstmt (smem m (mk_hfmem t dp r w rl wl rw))) cs cs' -> *)
      SV.Upd m r_default cs cs' ->
      eval_fstmt_single (smem m (mk_hfmem t dp r w rl wl rw)) ce cs ce' cs'
  .

    Definition merge_branch_cs_t c re re_t : option rhs_expr :=
    match re, re_t with
    | None, None => None
    | Some (R_fexpr e), Some (R_fexpr e_t) => Some (r_fexpr (emux c e_t e))
    | Some R_default, Some (R_fexpr e_t) => Some (R_fexpr e_t)
    | Some er1, None => Some er1
    | None, Some er2 => Some er2
    | _, _ => None
    end.

  Definition merge_branch_cs_e c re re_e : option rhs_expr :=
    match re, re_e with
    | None, None => None
    | Some (R_fexpr e), Some (R_fexpr e_e) => Some (r_fexpr (emux c e e_e))
    | Some R_default, Some (R_fexpr e_e) => Some (R_fexpr e_e)
    | Some er1, None => Some er1
    | None, Some er2 => Some er2
    | _, _ => None
    end.

  Definition merge_branch_ce ce ce_t : option (cmpnt_init_typs * fcomponent) :=
    match ce, ce_t with
    | None, None => None
    | Some (Aggr_typ t1, cp1), Some (Aggr_typ t2, cp2) => Some (aggr_typ (max_width t1 t2), cp1)
    | Some (Reg_typ t1, cp1), Some (Aggr_typ t2, cp2) => Some (Reg_typ t1, cp1)
    | Some er1, None => Some er1
    | None, Some er2 => Some er2
    | _, _ => None
    end.

   (* Fixpoint try_expandBranch_fun (s :  hfstmt) (ce : CE.env) (cs : cstate) {struct s}: (cstate):= *)
   (*        let fix aux (ss : seq hfstmt) (ce : CE.env) (cs : cstate) {struct ss}: (cstate) := *)

   (*            match ss with *)
   (*            | [::] => (cs) *)
   (*            | s :: sss =>  aux sss ce (try_expandBranch_fun s ce cs) *)
   (*            end in *)
   (*        match s with *)
   (*               | Sinst _ _ (* ignore for now -- TBD *) *)
   (*               | Spcnct _ _ (* should not appear -- ignore *) *)
   (*               | Sskip *)
   (*               | Sinvalid _ *)
   (*               | Sstop _ _ _ => cs (* no translation needed *) *)
   (*               | Snode v e => (SV.upd v (R_fexpr e) cs) *)
   (*               | Sreg v r => SV.upd v (R_fexpr (Eref (Eid v))) cs *)
   (*                                                                (* registers keep their old value by default. *)
   (*                                                                   The above code works for registers of basic type. *) *)
   (*               | Smem v m =>  cs (* but should assign R_default to all *)
   (*                                                                      input signals of ports *) *)
   (*               | Swire v t => SV.upd v (R_default VarOrder.T) cs *)
   (*               | Sfcnct v e => SV.upd (expand_eref v ce) (R_fexpr e) cs *)
   (*               | Swhen c sst ssf => let combined_branches := SV.map2 (merge_branch_cs_t c) (aux sst ce cs) (aux ssf ce cs) in *)
   (*                                    (* let result := try_expandBranch_fun s ce (snd combined_branches) in *) *)
   (*                 (* ((fst combined_branches) ++ (fst result), snd result) *) *)
   (*                 (cs) *)
   (*               end. *)

  (** Semantics of statement group, last cnct considered *)
  Inductive eval_fstmts_group : hfstmt_seq -> CE.env -> cstate -> CE.env -> cstate -> Prop :=
  | Gnil ce cs: eval_fstmts_group qnil ce cs ce cs
  (** other than when *)
  | Gfstmts_default st hst_tl ce ce' cs cs' cs'' :
      eval_fstmt_single st ce cs ce cs' ->
      eval_fstmts_group hst_tl ce cs' ce' cs'' ->
      eval_fstmts_group (Qcons st hst_tl) ce cs ce' cs''
  (* (**  claim a sreg *) *)
  (* | Gfstmts_reg_init r rt hst_tl ce ce' ce'' cs cs' cs'' : *)
  (*     eval_fstmt_single (sreg r rt) ce cs ce' cs' -> *)
  (*     eval_fstmts_group  hst_tl ce' cs' ce'' cs'' -> *)
  (*     eval_fstmts_group (Qcons (sreg r rt) hst_tl) ce cs ce'' cs''. *)
  (* (** claim a node *) *)
  (* | Gfstmts_node v e hst_tl ce ce' ce'' cs cs' cs'' : *)
  (*     eval_fstmt_single (snode v e) ce cs ce' cs' -> *)
  (*     eval_fstmts_group hst_tl ce' cs' ce'' cs'' -> *)
  (*     eval_fstmts_group (Qcons (snode v e) hst_tl) ce cs ce'' cs'' *)
  (* (** skip *) *)
  (* | Gskip_fstmts hst_tl ce ce' cs cs' : *)
  (*     eval_fstmts_group hst_tl ce cs ce' cs' -> *)
  (*     eval_fstmts_group (Qcons sskip hst_tl) ce cs ce' cs' *)
  (** condition when *)
  | Gwhen_fstmts c hstg1 hstg2 hst_tl ce ce' ce'' cs cs' cs'' :
      eval_fstmts_group_branch c hstg1 hstg2 ce cs ce' cs' ->
      eval_fstmts_group hst_tl ce' cs' ce'' cs'' ->
      eval_fstmts_group (Qcons (swhen c hstg1 hstg2) hst_tl) ce cs ce'' cs''
  (** https://github.com/llvm/circt/blob/main/lib/Dialect/FIRRTL/Transforms/ExpandWhens.cpp *)
  with eval_fstmts_group_branch :
         hfexpr -> hfstmt_seq -> hfstmt_seq -> CE.env -> cstate -> CE.env -> cstate -> Prop :=
  (** nil *)
  | Gthen_else_def c ce cs :
      eval_fstmts_group_branch c qnil qnil ce cs ce cs
  | Gthen_else c tb eb ce0 cs0 ce1 cs1 ce2 cs2 :
      eval_fstmts_group tb ce0 cs0 ce1 cs1 ->
      eval_fstmts_group eb ce0 cs0 ce2 cs2 ->
      eval_fstmts_group_branch c tb eb ce0 cs0 (CE.map2 merge_branch_ce (CE.map2 merge_branch_ce ce0 ce1) ce2)
                               (SV.map2 (merge_branch_cs_e c) (SV.map2 (merge_branch_cs_t c) cs0 cs1) cs2).

  (* (** connect to dst in then branch which has "not" been connected previously, add then branch *) *)
  (* | Gthen_cnct_0 c v e hstg1 hstg2 ce ce' ce'' cs cs' cs'' : *)
  (*     SV.acc (base_ref v) cs == r_default -> *)
  (*     eval_fstmt_single (sfcnct v e) ce cs ce' cs' -> *)
  (*     eval_fstmts_group_branch c hstg1 hstg2 ce' cs' ce'' cs'' -> *)
  (*     eval_fstmts_group_branch c (Qcons (sfcnct v e) hstg1) hstg2 ce cs ce'' cs'' *)
  (* (** connect to dst in else branch which has "not" been connected previously, add else branch *) *)
  (* | Gelse_cnct_0 c v e hstg2 ce ce' ce'' cs cs' cs'' : *)
  (*     CE.find v ce == None -> *)
  (*     eval_fstmt_single (sfcnct (eref v) e) ce cs ce' cs' -> *)
  (*     eval_fstmts_group_branch c Qnil hstg2 ce' cs' ce'' cs'' -> *)
  (*     eval_fstmts_group_branch c Qnil (Qcons (sfcnct (eref v) e) hstg2) ce cs ce'' cs'' *)
  (* (** connect to dst in then branch which has been connected previously, add mux(p, then, prev) *) *)
  (* | Gthen_cnct c v e re hstg1 hstg2 ce ce' cs cs' cs'' : *)
  (*     SV.acc v cs == r_fexpr re -> *)
  (*     (* CELemmas.P.Add vn Node ce ce' -> *) *)
  (*     (* SV.Upd vn (r_fexpr (emux c e re)) cs cs' -> *) *)
  (*     SV.Upd v (r_fexpr (emux c e re)) cs cs' -> *)
  (*     eval_fstmts_group_branch c hstg1 hstg2 ce cs' ce' cs'' -> *)
  (*     eval_fstmts_group_branch c (Qcons (sfcnct (eref v) e) hstg1) hstg2 ce cs ce' cs'' *)
  (* (** connect to dst in else branch which has been connected previously, add mux(p, prev, else) *) *)
  (* | Gelse_cnct c v e re hstg2 ce ce' cs cs' cs'' : *)
  (*     SV.acc v cs == r_fexpr re -> *)
  (*     SV.Upd v (r_fexpr (emux c re e)) cs cs' -> *)
  (*     eval_fstmts_group_branch c Qnil hstg2 ce cs' ce' cs'' -> *)
  (*     eval_fstmts_group_branch c Qnil (Qcons (sfcnct (eref v) e) hstg2) ce cs ce' cs'' *)
  (* (** claim a sreg in then branch *) *)
  (* | Gthen_reg c r hstg1 hstg2 ce ce' ce'' cs cs' cs'' : *)
  (*     eval_fstmt_single (sreg r) ce cs ce' cs' -> *)
  (*     eval_fstmts_group_branch c hstg1 hstg2 ce' cs' ce'' cs'' -> *)
  (*     eval_fstmts_group_branch c (Qcons (sreg r) hstg1) hstg2 ce cs ce'' cs'' *)
  (* (** claim a sreg in else branch *) *)
  (* | Gelse_reg c r hstg2 ce ce' ce'' cs cs' cs'' : *)
  (*     eval_fstmt_single (sreg r) ce cs ce' cs' -> *)
  (*     eval_fstmts_group_branch c Qnil hstg2 ce' cs' ce'' cs'' -> *)
  (*     eval_fstmts_group_branch c Qnil (Qcons (sreg r) hstg2) ce cs ce'' cs'' *)
  (* (** claim a node in then branch *) *)
  (* | Gthen_node c v e hstg1 hstg2 ce ce' ce'' cs cs' cs'' : *)
  (*     eval_fstmt_single (snode v e) ce cs ce' cs' -> *)
  (*     eval_fstmts_group_branch c hstg1 hstg2 ce' cs' ce'' cs'' -> *)
  (*     eval_fstmts_group_branch c (Qcons (snode v e) hstg1) hstg2 ce cs ce'' cs'' *)
  (* (** claim a node in else branch *) *)
  (* | Gelse_node c v e hstg2 ce ce' ce'' cs cs' cs'' : *)
  (*     eval_fstmt_single (snode v e) ce cs ce' cs' -> *)
  (*     eval_fstmts_group_branch c Qnil hstg2 ce' cs' ce'' cs'' -> *)
  (*     eval_fstmts_group_branch c Qnil (Qcons (snode v e) hstg2) ce cs ce'' cs''. *)

  (* Lemma valid_conncection v e2 sts ce cs ce' cs' : *)
  (*   eval_fstmts_group (Qcons (sfcnct (eref v) e2) sts) ce cs ce' cs' -> *)
  (*   valid_rhs (SV.acc v cs') ce'. *)
END OF VERY OLD MATERIAL *)
