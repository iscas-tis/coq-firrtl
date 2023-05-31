From Coq Require Import BinNat ZArith.
From mathcomp Require Import ssreflect ssrbool eqtype seq fintype ssrnat div ssrfun.
From simplssrlib Require Import SsrOrder Var FMaps.
From firrtl Require Import Env Firrtl HiEnv HiFirrtl_r.

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
   (x + y) * (x + y + 1) / 2 + x.

Definition proj1 (p : nat) : nat :=
   let x_plus_y := (Nat.sqrt (8 * p + 1) - 1) / 2 (* rounded down *) in
   p - (x_plus_y * (x_plus_y + 1) / 2).

Definition proj2 (p : nat) : nat :=
   let x_plus_y := (Nat.sqrt (8 * p + 1) - 1) / 2 (* rounded down *) in
   (* x_plus_y - (proj1 p), which simplifies to: *)
   x_plus_y * (x_plus_y + 3) / 2 - p.

(* pair and (proj1, proj2) are each other's inverse functions.
uses lemma sqrt_square : Nat.sqrt (n * n) = n. *)

Lemma proj1_pair : forall (x y : nat), proj1 (pair x y) = x.
Admitted.

Lemma proj2_pair : forall (x y : nat), proj2 (pair x y) = y.
Admitted.

Lemma pair_proj : forall p : nat, pair (proj1 p) (proj2 p) = p.
Admitted.

Definition nat_to_var (n : nat) : VarOrder.T := bin_of_nat n.

Definition var_to_nat (id: VarOrder.T) : nat := (* nat_of_bin *) id.

(* The above two are each other's inverse.
This is proven by lemmas bin_of_natK and nat_of_binK. *)

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
   forall ref1 : href,
      href_without_subaccess ref1 ->
      forall ref2 : href, ref2var ref1 = ref2var ref2 -> ref1 = ref2.
Proof.
assert (Hmod: forall (a b c d : nat), OK (nat_to_var (a * 3 + b)) = OK (nat_to_var (c * 3 + d)) -> b == d %[mod 3]).
      intros.
      injection H ; clear ; unfold nat_to_var ; intro.
      rewrite -(modnMDl a b) -(modnMDl c d) -(bin_of_natK (a * 3 + b)) H bin_of_natK //.
assert (Hdiv : forall (a d : VarOrder.T) (b c e : nat),
                  OK (nat_to_var (pair (var_to_nat a) b * 3 + c)) =
                  OK (nat_to_var (pair (var_to_nat d) e * 3 + c)) ->
                     a = d /\ b = e).
      unfold nat_to_var, var_to_nat.
      intros.
      injection H ; clear ; intro.
      assert (pair a b == pair d e)
            by (rewrite -(@eqn_pmul2r 3) // -(eqn_add2r c)
                        -(bin_of_natK (pair a b * 3 + c))
                        H bin_of_natK //).
      move /eqP : H0 => H0.
      rewrite -(proj2_pair a b) H0 proj2_pair.
      rewrite -(nat_of_binK a) -(proj1_pair a b) H0 proj1_pair nat_of_binK.
      split ; reflexivity.
induction ref1 ; simpl href_without_subaccess ; try done.
* (* Eid s == ... *)
  intros _.
  destruct ref2 ;
        try (simpl ref2var ;
             destruct (ref2var ref2) ; try done ;
             intro ; apply Hmod in H ; done).
  simpl ref2var.
  intro ; injection H ; clear H ; unfold nat_to_var ; intro.
  assert (s * 3 + 1 == s0 * 3 + 1)
        by (rewrite -(bin_of_natK (s * 3 + 1)) H bin_of_natK eq_refl //) ;
  clear H.
  rewrite addn1 addn1 eqSS eqn_pmul2r // in H0.
  move /eqP : H0 => H0.
  rewrite -(nat_of_binK s) H0 nat_of_binK ; reflexivity.
* (* Esubfield ref1 s == ... *)
  intro.
  destruct ref2.
  + simpl ref2var.
    destruct (ref2var ref1) ; try done.
    intro ; apply Hmod in H0 ; done.
  + simpl ref2var.
    specialize IHref1 with (ref2 := ref2).
    destruct (ref2var ref1) eqn: Hr2v1 ; try (apply ref2var_OK with (e := e) in H ; done).
    destruct (ref2var ref2) eqn: Hr2v2 ; try done.
    intro.
    apply Hdiv in H0 ; destruct H0.
    rewrite IHref1 // ; try rewrite H0 //.
    rewrite -(nat_of_binK s) H1 (nat_of_binK) //.
  + simpl ref2var.
    destruct (ref2var ref1) eqn: Hr2v1 ; try (apply ref2var_OK with (e := e) in H ; done).
    destruct (ref2var ref2) ; try done.
    intro ; apply Hmod in H0 ; done.
  + simpl ref2var.
    destruct (ref2var ref1) eqn: Hr2v1 ; try done.
    apply ref2var_OK with (e := e) in H ; done.
* (* Esubindex ref1 n == ... *)
  intro.
  destruct ref2.
  + simpl ref2var.
    destruct (ref2var ref1) ; try done.
    intro ; apply Hmod in H0 ; done.
  + simpl ref2var.
    destruct (ref2var ref1) eqn: Hr2v1 ; try (apply ref2var_OK with (e := e) in H ; done).
    destruct (ref2var ref2) ; try done.
    intro ; apply Hmod in H0 ; done.
  + simpl ref2var.
    specialize IHref1 with (ref2 := ref2).
    destruct (ref2var ref1) eqn: Hr2v1 ; try (apply ref2var_OK with (e := e) in H ; done).
    destruct (ref2var ref2) eqn: Hr2v2 ; try done.
    intro.
    apply Hdiv in H0 ; destruct H0.
    rewrite IHref1 // ; try rewrite H0 //.
    rewrite H1 //.
  + simpl ref2var.
    destruct (ref2var ref1) eqn: Hr2v1 ; try done.
    apply ref2var_OK with (e := e) in H ; done.
Qed.

(* mapping from an index in CE.env to a href. *)

Fixpoint var2ref' (depth n : nat) : @error_type href :=
   match depth, n with
   | 0, _ | _, 0 => Err Einternal
   | S d', _ => if n %% 3 == 1
                then OK (Eid (nat_to_var ((n - 1) %/ 3)))
                else if n %%3 == 2
                     then let p := (n - 2) %/ 3 in
                          match var2ref' d' (proj1 p) with Err e => Err e
                          | OK ref => OK (Esubfield ref (nat_to_var (proj2 p))) end
                     else let p := (n - 3) %/ 3 in
                          match var2ref' d' (proj1 p) with Err e => Err e
                          | OK ref => OK (Esubindex ref (proj2 p)) end
   end.

Definition var2ref (id : VarOrder.T) : @error_type href := var2ref' (var_to_nat id) (var_to_nat id).

Lemma var2ref_ref2var :
   forall (id : VarOrder.T), if var2ref id is OK ref
                  then ref2var ref = OK id
                  else forall ref: href, ref2var ref <> OK id.
Proof.
enough (   (forall (d id : VarOrder.T) (ref : href),
               d >= id -> var2ref' d id = OK ref -> ref2var ref = OK id)
        /\ (forall (id d : VarOrder.T) (e : error_info),
               d >= id -> var2ref' d id = Err e -> forall ref: href, ref2var ref <> OK id)).
      intro.
      destruct H.
      unfold var2ref, var_to_nat.
      destruct (var2ref' id id) eqn: Hv2r.
      * specialize (H id id h).
        apply H ; done.
      * specialize (H0 id id e).
        apply H0 ; done.
split.
* intro.
  rewrite -(bin_of_natK d).
  induction (nat_of_bin d).
  + rewrite bin_of_natK.
    simpl var2ref'.
    done.
  + rewrite bin_of_natK.
    rewrite bin_of_natK in IHn.
    intros.
    simpl var2ref' in H0.
    destruct (nat_of_bin id) as [|idminus1] eqn: Hid ; try done.
    rewrite -Hid in H0 H.
    destruct (id %% 3 == 1) eqn: H1.
    - injection H0 ; clear H0 ; intro ; rewrite -H0.
      rewrite /ref2var /nat_to_var bin_of_natK Hid -addn1 addnK.
      enough (idminus1 %/3 * 3 + 1 = id) by (rewrite H2 nat_of_binK //).
      rewrite Hid addn1 divnK // /dvdn.
      replace 1 with ((0 + 1) %% 3) in H1 at 2 by (apply modn_small ; done).
      rewrite Hid -addn1 eqn_modDr in H1.
      rewrite H1 ; done.
    destruct (id %% 3 == 2) eqn: H2.
    - destruct (var2ref' n (proj1 ((id - 2) %/ 3))) eqn: Hv2r ; try done.
      injection H0 ; clear H0 ; intro ; rewrite -H0.
      simpl ref2var.
      specialize (IHn (bin_of_nat (proj1 ((id - 2) %/ 3))) h).
      rewrite bin_of_natK in IHn.
      rewrite /nat_to_var /var_to_nat bin_of_natK.
      replace (ref2var h) with (OK (bin_of_nat (proj1 ((id - 2) %/ 3))))
            by (symmetry ; apply IHn ; try exact Hv2r ; admit).
      rewrite bin_of_natK pair_proj.
      enough ((id - 2) %/3 * 3 + 2 = id) by (rewrite H3 nat_of_binK //).
      (* the rest is similar to the above *)
      rewrite divnK.
      * admit (* This can be proven because id >= 2, because of H2 *).
      * unfold dvdn.
        admit (* This can again be proven because of H2 *).
    - destruct (var2ref' n (proj1 ((id - 3) %/ 3))) eqn: Hv2r ; try done.
      injection H0 ; clear H0 ; intro ; rewrite -H0.
      simpl ref2var.
      specialize (IHn (bin_of_nat (proj1 ((id - 3) %/ 3))) h).
      rewrite bin_of_natK in IHn.
      rewrite /nat_to_var /var_to_nat.
      replace (ref2var h) with (OK (bin_of_nat (proj1 ((id - 3) %/ 3))))
            by (symmetry ; apply IHn ; try exact Hv2r ; admit).
      rewrite bin_of_natK pair_proj.
      enough ((id - 3) %/3 * 3 + 3 = id) by (rewrite H3 nat_of_binK //).
      (* the rest is similar to the above *)
      rewrite divnK.
      * admit (* This can be proven because id >= 3, because of Hid, H1, and H2. *).
      * unfold dvdn.
        admit (* This can again be proven because of H1 and H2 *).
* intros.
  contradict H0.
  move : id d H H0 e.
  induction ref.
  + intros.
    unfold ref2var, nat_to_var in H0.
    injection H0 ; clear H0 ; intro.
    rewrite -H0.
    rewrite bin_of_natK.
    replace (nat_of_bin d) with ((nat_of_bin d).-1.+1)
          by (rewrite addn1 in H0 ; apply prednK ;
              apply leq_trans with (n := id) ; try done ;
              rewrite -H0 bin_of_natK ; apply ltn0Sn).
    rewrite (addn1 (s * 3)).
    simpl var2ref'.
    rewrite -{1}(addn1 (s * 3)) modnMDl.
    replace (1 %% 3) with 1 by (rewrite modn_small ; reflexivity).
    discriminate.
  + intros.
    simpl ref2var in H0.
    destruct (ref2var ref) ; try done.
    specialize (IHref s0 (bin_of_nat d.-1)).
    injection H0 ; clear H0 ; intro.
    rewrite -H0.
    unfold var2ref, var_to_nat, nat_to_var.
    rewrite bin_of_natK addnS.
    replace (nat_of_bin d) with ((nat_of_bin d).-1.+1)
          by (rewrite addnS in H0 ; apply prednK ;
              apply leq_trans with (n := id) ; try done ;
              rewrite -H0 bin_of_natK ; apply ltn0Sn).
    unfold var2ref' ; fold var2ref'.
    rewrite -addnS modnMDl.
    replace (2 %% 3) with 2 by (rewrite modn_small //).
    rewrite (addnK 2).
    rewrite (mulnK (pair s0 s)) // proj1_pair proj2_pair.
    rewrite bin_of_natK in IHref.
    destruct (var2ref' d.-1 s0).
    - discriminate.
    - apply IHref ; try done.
      admit (* follows from H and H0 *).
  + (* The case Esubindex is similar to the above. *)
    admit.
  + unfold ref2var.
    done.
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
      After that we call the constructed function for every element of the array.

      However, this makes the proofs too complex.
      Therefore, we simplify as follows:
      we assume that there are no array types in a type definition.
      Then, init_ref etc. can be defined directly as resursive functions
      (that produce an error if there is an array type anyway). *)

   Fixpoint init_ref (id : href) (type : ftype) (orient : forient) (cm : cmap) : @error_type cmap :=
   (* sets all ground-type elements of id to D_undefined.
      It can be used to initialize memory write ports (data and mask fields) and wires.
      Memory ports have to be passive, but wires allow flipped fields,
      so it does not check whether the type is passive.
      Input:  * id = href of the variable that needs to be initialized
              * type = type of id
              * orient = orientation of id (Sink, Duplex or Source)
                If the orientation of id is Source, only flipped fields will be initialized.
                If the orientation of id is Sink, only non-flipped fields will be initialized.
              * cm = cmap that is being modified
      Output: * cmap with additional initializations (or an error) *)
   match type with
   | Gtyp _ => match orient with
               | Sink | Duplex => match ref2var id with Err e => Err e | OK ref
                                  => OK (CE.add ref D_undefined cm) end
               | Source => OK cm
               | _ => Err Einternal
               end
   | Atyp _ _ => Err Etype
   | Btyp ff => init_ref_bundle id ff orient cm
   end
   with init_ref_bundle (id : href) (ff : ffield) (orient : forient) (cm : cmap) : @error_type cmap :=
   match ff with
   | Fnil => OK cm
   | Fflips field_name fl field_type ff_tail =>
        match init_ref_bundle id ff_tail orient cm with Err e => Err e | OK cm_tail =>
        let field_orient := match fl, orient with Flipped, Sink => Source
                                                | Flipped, Source => Sink
                                                | _, _ => orient end
        in init_ref (Esubfield id field_name) field_type field_orient cm_tail end
   end.

   Fixpoint init_register (id : href) (type : ftype) (cm : cmap) : @error_type cmap :=
   (* Initializes the register id, which is of type type.
      Input:  * id = href of the variable that needs to be initialized
              * type = type of id
              * cm = cmap that is being modified
      Output: * cmap with additional initializations (or an error) *)
   match type with
   | Gtyp _ => match ref2var id with Err e => Err e | OK var =>
               OK (CE.add var (D_fexpr (Eref id)) cm) end
   | Atyp _ _ => Err Etype
   | Btyp ff => init_register_bundle id ff cm
   end
   with init_register_bundle (id : href) (ff : ffield) (cm : cmap) : @error_type cmap :=
   match ff with
   | Fnil => OK cm
   | Fflips field_name Nflip field_type ff_tail =>
        match init_register_bundle id ff_tail cm with Err e => Err e | OK cm_tail =>
        init_register (Esubfield id field_name) field_type cm_tail end
   | Fflips _ Flipped _ _ => Err Etype (* registers must be passive *)
   end.

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

   Definition init_instance (id: VarOrder.T) (mdl: VarOrder.T) (ce_other_modules : CE.env) (cm : cmap) : @error_type cmap :=
   (* This function should initialize the ports that connect the current module with module mdl under the name id,
      which is instantiated here.
      It is assumed that the type of the module is stored in ce_other_modules already.
      (Input ports are flipped.) *)
   match CE.find mdl ce_other_modules with
   | Some (Aggr_typ type, Fmodule) => init_ref (Eid id) type Sink cm
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
             | @Swire _ id type => match init_ref (Eid id) type Duplex cm_result with Err e => Err e | OK cm_wire
                                   => OK (Qrcons ss_result last, cm_wire) end
             | @Sreg _ id reg => match init_register (Eid id) (type reg) cm_result with Err e => Err e | OK cm_reg
                                 => OK (Qrcons ss_result last, cm_reg) end
             | @Smem _ id mem => match type_of_mem mem with Err e => Err e | OK mem_type
                                 => match init_ref (Eid id) mem_type Source cm_result with Err e => Err e | OK cm_mem
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

   (* conditions on ce_other_modules:
      a module type is a bundle containing in-ports (flipped) and out-ports (not flipped).
      The ports themselves are of ground types (to simplify the recursions). *)

   Fixpoint expandBranch_precondition_ce_module_fields (ff : ffield) : bool :=
   (* all fields in ff are of a ground type *)
   match ff with
   | Fnil => true
   | Fflips _ _ (Gtyp _) ff' => expandBranch_precondition_ce_module_fields ff'
   | _ => false
   end.

   Definition expandBranch_precondition_ce (ce_other_modules : CE.env) : Prop :=
   (* in/out ports of other modules are ground types:
      all entries in ce_other_modules are input or output ports,
      and they have ground types. *)
   forall (id : VarOrder.T),
      match CE.find id ce_other_modules with
      | None
      | Some (Aggr_typ (Gtyp _), In_port)
      | Some (Aggr_typ (Gtyp _), Out_port) => true
      | Some (Aggr_typ (Btyp ff), Fmodule) => expandBranch_precondition_ce_module_fields ff
      | Some _ => false
      end.

   Definition combine_branches_ce_map2_helper (true_entry false_entry : option (cmpnt_init_typs * fcomponent)) : option (cmpnt_init_typs * fcomponent) :=
   match true_entry with
   | Some _ => true_entry
   | None => false_entry
   end.

   Definition combine_branches_ce (ce_true ce_false : CE.env) : @error_type CE.env :=
   (* combines component declarations in the two branches. *)
      OK (CE.map2 combine_branches_ce_map2_helper ce_true ce_false).

Definition ce_map_difference_helper (minuend_entry subtrahend_entry : option (cmpnt_init_typs * fcomponent)) : option (cmpnt_init_typs * fcomponent) :=
match subtrahend_entry with
| Some _ => None
| None => minuend_entry
end.

Definition ce_map_intersection_helper (entry1 entry2 : option (cmpnt_init_typs * fcomponent)) : option (cmpnt_init_typs * fcomponent) :=
match entry1, entry2 with
| Some _, Some _ => entry1
| _, _ => None
end.

Definition ce_has_no_double_declarations (ce_butlast ce_true ce_false : CE.env) : bool :=
   (* checks whether there are double declarations in the component environments *)
   CE.is_empty (CE.map2 ce_map_intersection_helper (CE.map2 ce_map_difference_helper ce_true ce_butlast)
                                                   (CE.map2 ce_map_difference_helper ce_false ce_butlast)).

   Fixpoint expandBranch_precondition_declarations (ss : hfstmt_seq) (ce_other_modules : CE.env) (ce_previous : CE.env) : @error_type CE.env :=
   (* If all declarations are ground types, there are no partial connects in ss,
      and all full connects concern ground types,
      then the result is a CE.env containing types for all declared components.
      (ce_previous is the map containing types for the code before ss,
       or possibly CE.empty (cmpnt_init_typs * fcomponent).)
      Otherwise the result is an error message. *)
   match ss with
   | Qnil => OK ce_previous
   | Qrcons ss_butlast last =>
       match expandBranch_precondition_declarations ss_butlast ce_other_modules ce_previous with Err e => Err e | OK ce_butlast_result
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
          | @Sinst _ id mdl => if CE.find mdl ce_other_modules is Some (Aggr_typ mdl_type, Fmodule)
                               then match ref2var (Eid id) with Err e => Err e | OK var
                                    => if CE.find var ce_butlast_result is Some _
                                       then Err Ealready_declared
                                       else OK (CE.add var (aggr_typ mdl_type, Instanceof) ce_butlast_result)
                                    end
                               else Err Etype
          | @Sfcnct _ ref _ => if ref2var ref is OK id
                               then if CE.find id ce_butlast_result is Some (Aggr_typ (Gtyp _), fcomp)
                                    then if orient_of_comp fcomp == Source
                                         then Err Eflow_direction
                                         else OK ce_butlast_result
                                    else Err Etype
                               else Err Eundeclared
          | @Spcnct _ _ _ => Err Einternal
          | @Sinvalid _ ref => if ref2var ref is OK id
                               then if CE.find id ce_butlast_result is Some (Aggr_typ (Gtyp _), fcomp)
                                    then if orient_of_comp fcomp == Source
                                         then Err Eflow_direction
                                         else OK ce_butlast_result
                                    else Err Etype
                               else Err Eundeclared
          | @Swhen _ _ ss_true ss_false =>
               match expandBranch_precondition_declarations ss_true  ce_other_modules ce_butlast_result,
                     expandBranch_precondition_declarations ss_false ce_other_modules ce_butlast_result with
               | Err e, _ | _, Err e => Err e
               | OK ce_true_result, OK ce_false_result =>
                    if ce_has_no_double_declarations ce_butlast_result ce_true_result ce_false_result
                    then combine_branches_ce ce_true_result ce_false_result
                    else Err Ealready_declared
               end
          | _ => OK ce_butlast_result
                 (* for Sinst, one has to check ce_other_modules as well.
                    This is done in expandBranch_precondition_ce. *)
          end
      end
   end.

   Lemma expandBranch_precondition_declarations_does_not_contain_modules :
      forall (ss : hfstmt_seq) (ce_other_modules ce_previous : CE.env),
         if expandBranch_precondition_declarations ss ce_other_modules ce_previous is OK ce_declarations
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

Definition expandBranch_precondition_declarations_does_not_redefine_hfstmt_seq
      (var : VarOrder.T) (p : cmpnt_init_typs * fcomponent) (ce_other_modules : CE.env) (ss : hfstmt_seq) : Prop :=
   forall ce_previous : CE.env,
      CE.find var ce_previous = Some p ->
         forall ce_declarations : CE.env,
            expandBranch_precondition_declarations ss ce_other_modules ce_previous = OK ce_declarations ->
               CE.find var ce_declarations = Some p.

Lemma expandBranch_precondition_declarations_does_not_redefine :
   forall (var : VarOrder.T) (p : cmpnt_init_typs * fcomponent) (ce_other_modules : CE.env),
      forall ss : hfstmt_seq,
         expandBranch_precondition_declarations_does_not_redefine_hfstmt_seq var p ce_other_modules ss
with expandBranch_precondition_declaration_does_not_redefine_Swhen :
   forall (var : VarOrder.T) (p : cmpnt_init_typs * fcomponent) (ce_other_modules : CE.env),
      forall s : hfstmt,
         if s is Swhen _ ss_true ss_false
         then    expandBranch_precondition_declarations_does_not_redefine_hfstmt_seq var p ce_other_modules ss_true
              /\ expandBranch_precondition_declarations_does_not_redefine_hfstmt_seq var p ce_other_modules ss_false
         else True.
Proof.
* clear expandBranch_precondition_declarations_does_not_redefine.
  induction ss.
  + unfold expandBranch_precondition_declarations_does_not_redefine_hfstmt_seq,
           expandBranch_precondition_declarations.
    intros.
    injection H0 ; clear H0 ; intro.
    rewrite -H0 ; exact H.
  + intros.
    rename h into s.
    unfold expandBranch_precondition_declarations_does_not_redefine_hfstmt_seq ;
    unfold expandBranch_precondition_declarations_does_not_redefine_hfstmt_seq in IHss.
    intros.
    specialize IHss with (ce_previous := ce_previous).
    specialize expandBranch_precondition_declaration_does_not_redefine_Swhen
    with (var := var) (p := p) (ce_other_modules := ce_other_modules) (s := s).
    destruct s.
    - (* Sskip *)
      specialize IHss with (ce_declarations := ce_declarations).
      apply IHss in H ; try done ; clear IHss ; rename H into IHss.
      simpl expandBranch_precondition_declarations in H0.
      destruct (expandBranch_precondition_declarations ss ce_other_modules ce_previous) ;
            done.
    - (* Swire *)
      simpl expandBranch_precondition_declarations in H0.
      destruct (expandBranch_precondition_declarations ss ce_other_modules ce_previous) ;
            try done.
      specialize IHss with (ce_declarations := e).
      apply IHss in H ; try done ; clear IHss ; rename H into IHss.
      destruct f ; try done.
      destruct (eqVneq var (nat_to_var (s * 3 + 1))).
      * rewrite -e0 IHss in H0 ; done.
      * destruct (CE.find (nat_to_var (s * 3 + 1)) e) ; try done.
        injection H0 ; clear H0 ; intro.
        apply negbTE in i.
        rewrite -H CELemmas.find_add_neq // /CE.SE.eq i //.
    - (* Sreg *)
      simpl expandBranch_precondition_declarations in H0.
      destruct (expandBranch_precondition_declarations ss ce_other_modules ce_previous) ;
            try done.
      specialize IHss with (ce_declarations := e).
      apply IHss in H ; try done ; clear IHss ; rename H into IHss.
      destruct (type h) ; try done.
      destruct (eqVneq var (nat_to_var (s * 3 + 1))).
      * rewrite -e0 IHss in H0 ; done.
      * destruct (CE.find (nat_to_var (s * 3 + 1)) e) ; try done.
        injection H0 ; clear H0 ; intro.
        apply negbTE in i.
        rewrite -H CELemmas.find_add_neq // /CE.SE.eq i //.
    - (* Smem *)
      simpl expandBranch_precondition_declarations in H0.
      destruct (expandBranch_precondition_declarations ss ce_other_modules ce_previous) ;
            try done.
      specialize IHss with (ce_declarations := e).
      apply IHss in H ; try done ; clear IHss ; rename H into IHss.
      destruct (data_type h) ; try done.
      destruct (eqVneq var (nat_to_var (s * 3 + 1))).
      * rewrite -e0 IHss in H0 ; done.
      * destruct (CE.find (nat_to_var (s * 3 + 1)) e) ; try done.
        injection H0 ; clear H0 ; intro.
        apply negbTE in i.
        rewrite -H CELemmas.find_add_neq // /CE.SE.eq i //.
    - (* Sinst *)
      simpl expandBranch_precondition_declarations in H0.
      destruct (expandBranch_precondition_declarations ss ce_other_modules ce_previous) ;
            try done.
      specialize IHss with (ce_declarations := e).
      apply IHss in H ; try done ; clear IHss ; rename H into IHss.
      destruct (eqVneq var (nat_to_var (s * 3 + 1))).
      * rewrite -e0 IHss in H0.
        destruct (CE.find s0 ce_other_modules) ; try done.
        destruct p0, c ; try done.
        destruct f ; done.
      * destruct (CE.find s0 ce_other_modules) ; try done.
        destruct p0, c ; try done.
        destruct f ; try done.
        destruct (CE.find (nat_to_var (s * 3 + 1)) e) ; try done.
        injection H0 ; clear H0 ; intro.
        apply negbTE in i.
        rewrite -H CELemmas.find_add_neq // /CE.SE.eq i //.
    - (* Snode *)
       specialize IHss with (ce_declarations := ce_declarations).
      apply IHss in H ; try done ; clear IHss ; rename H into IHss.
      simpl expandBranch_precondition_declarations in H0.
      destruct (expandBranch_precondition_declarations ss ce_other_modules ce_previous) ;
            done.
    - (* Sfcnct *)
      simpl expandBranch_precondition_declarations in H0.
      destruct (expandBranch_precondition_declarations ss ce_other_modules ce_previous) ;
            try done.
      specialize IHss with (ce_declarations := e).
      apply IHss in H ; try done ; clear IHss ; rename H into IHss.
      destruct (ref2var h) ; try done.
      destruct (CE.find s e) ; try done.
      destruct p0, c ; try done.
      destruct f0 ; try done.
      destruct (orient_of_comp f == Source) ; try done.
      injection H0 ; clear H0 ; intros.
      rewrite -H //.
    - (* Spcnct *)
      simpl expandBranch_precondition_declarations in H0.
      destruct (expandBranch_precondition_declarations ss ce_other_modules ce_previous) ;
            done.
    - (* Sinvalid *)
      simpl expandBranch_precondition_declarations in H0.
      destruct (expandBranch_precondition_declarations ss ce_other_modules ce_previous) ;
            try done.
      specialize IHss with (ce_declarations := e).
      apply IHss in H ; try done ; clear IHss ; rename H into IHss.
      destruct (ref2var h) ; try done.
      destruct (CE.find s e) ; try done.
      destruct p0, c ; try done.
      destruct f0 ; try done.
      destruct (orient_of_comp f == Source) ; try done.
      injection H0 ; clear H0 ; intros.
      rewrite -H //.
    - (* Swhen *)
      rename h into cond, h0 into ss_true, h1 into ss_false.
      unfold expandBranch_precondition_declarations_does_not_redefine_hfstmt_seq
      in expandBranch_precondition_declaration_does_not_redefine_Swhen.
      destruct expandBranch_precondition_declaration_does_not_redefine_Swhen as [IHss_true IHss_false].
      simpl expandBranch_precondition_declarations in H0.
      destruct (expandBranch_precondition_declarations ss ce_other_modules ce_previous) ;
            try done.
      apply IHss with (ce_declarations := e) in H ; try done ; clear IHss ; rename H into IHss.
      specialize IHss_true with (ce_previous := e).
      specialize IHss_false with (ce_previous := e).
      destruct (expandBranch_precondition_declarations ss_true ce_other_modules e) as [e_true|] ;
            try done.
      destruct (expandBranch_precondition_declarations ss_false ce_other_modules e) as [e_false|] ;
            try done.
      specialize IHss_true with (ce_declarations := e_true).
      destruct (ce_has_no_double_declarations e e_true e_false) ; try done.
      unfold combine_branches_ce in H0.
      injection H0 ; clear H0 ; intro.
      rewrite -H CE.map2_1.
      * rewrite IHss_true //.
      * left.
        unfold CE.In.
        exists p.
        apply CE.find_2, IHss_true ; done.
* clear expandBranch_precondition_declaration_does_not_redefine_Swhen.
  destruct s ; done.
Qed.

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
   match expandBranch_precondition_declarations ss ce_other_modules ce_previous_declarations with Err e => true | OK ce_declarations =>
   match expandBranch_fun ss ce_other_modules cm_previous with Err e => true | OK (ss_result, cm_result)
   => forall id : VarOrder.T,
      if ref2var (Eid id) is OK var
      then match CE.find var ce_declarations with
           | Some (Aggr_typ t, fcomp) => if orient_of_comp fcomp == Source
                                         then expandBranch_one_component_sem_conform_flipped (Eid id) t ss cm_result cm_previous
                                         else expandBranch_one_component_sem_conform (Eid id) t ss cm_result cm_previous
           | Some (Reg_typ reg,_) => expandBranch_one_component_sem_conform (Eid id) (type reg) ss cm_result cm_previous
           | Some (Mem_typ mem, _) => if type_of_mem mem is OK tom
                                      then expandBranch_one_component_sem_conform_flipped (Eid id) tom ss cm_result cm_previous
                                      else false
           | _ => true
           end
      else true
   end end.

Definition expandBranch_fun_declarations_correspondence (ce_declarations : CE.env) (cm : cmap) : Prop :=
(*
   forall (var : VarOrder.T) (cmpnt_typ : cmpnt_init_typs) (fcomp : fcomponent),
      (CE.find var ce_declarations <> Some (cmpnt_typ, fcomp) \/ fcomp = Source)
      <-> CE.find var cm = None.
*)
   forall var : VarOrder.T,
      if CE.find var ce_declarations is Some (_, fcomp)
      then orient_of_comp fcomp == Source <-> CE.find var cm == None
      else CE.find var cm == None.

Definition expandBranch_fun_declarations_preserve_correspondence_hfstmt_seq (ss : hfstmt_seq) : Prop :=
   forall (ce_previous : CE.env) (cm_previous : cmap),
      expandBranch_fun_declarations_correspondence ce_previous cm_previous ->
         forall (ce_result : CE.env) (cm_result : cmap) (ce_other_modules : CE.env) (ss_result : hfstmt_seq),
            expandBranch_precondition_declarations ss ce_other_modules ce_previous = OK ce_result ->
            expandBranch_fun ss ce_other_modules cm_previous = OK (ss_result, cm_result) ->
               expandBranch_fun_declarations_correspondence ce_result cm_result.

Lemma expandBranch_fun_declarations_preserve_correspondence :
   forall (ss : hfstmt_seq), expandBranch_fun_declarations_preserve_correspondence_hfstmt_seq ss
with expandBranch_fun_declarations_preserve_correspondence_Swhen :
   forall (s : hfstmt),
      if s is Swhen _ ss_true ss_false
      then    expandBranch_fun_declarations_preserve_correspondence_hfstmt_seq ss_true
           /\ expandBranch_fun_declarations_preserve_correspondence_hfstmt_seq ss_false
      else True.
Proof.
* clear expandBranch_fun_declarations_preserve_correspondence.
  induction ss.
  + unfold expandBranch_fun_declarations_preserve_correspondence_hfstmt_seq,
           expandBranch_precondition_declarations,
           expandBranch_fun.
    intros.
    injection H0 ; injection H1 ; clear H0 H1 ; intros H0 _ H1.
    rewrite -H0 -H1 //.
  + intros.
    destruct h.
    - (* Sskip *)
      unfold expandBranch_fun_declarations_preserve_correspondence_hfstmt_seq ;
      unfold expandBranch_fun_declarations_preserve_correspondence_hfstmt_seq in IHss.
      simpl expandBranch_precondition_declarations.
      simpl expandBranch_fun.
      intros.
      specialize IHss with (ce_previous := ce_previous) (cm_previous := cm_previous)
            (ce_result := ce_result) (cm_result := cm_result)
            (ce_other_modules := ce_other_modules) (ss_result := ss_result).
      destruct (expandBranch_precondition_declarations ss ce_other_modules ce_previous) ; try done.
      destruct (expandBranch_fun ss ce_other_modules cm_previous) ; try done.
      destruct p as [ss_result0 cm_result0].
      apply IHss ; done.
    - (* Swire *)
      unfold expandBranch_fun_declarations_preserve_correspondence_hfstmt_seq ;
      unfold expandBranch_fun_declarations_preserve_correspondence_hfstmt_seq in IHss.
      simpl expandBranch_precondition_declarations.
      simpl expandBranch_fun.
      intros.
      specialize IHss with (ce_previous := ce_previous) (cm_previous := cm_previous)
            (ce_other_modules := ce_other_modules).
      destruct (expandBranch_precondition_declarations ss ce_other_modules ce_previous) ; try done.
      destruct (expandBranch_fun ss ce_other_modules cm_previous) ; try done.
      destruct p as [ss_result0 cm_result0].
      specialize IHss with (ce_result := e) (cm_result := cm_result0) (ss_result := ss_result0).
      apply IHss in H ; try done ; clear IHss ; rename H into IHss.
      destruct f ; try done.
      unfold init_ref, ref2var in H1.
      destruct (CE.find (nat_to_var (s * 3 + 1)) e) ; try done.
      injection H0 ; injection H1 ; clear H0 H1 ; intros H0 _ H1.
      rewrite -H0 -H1.
      unfold expandBranch_fun_declarations_correspondence ;
      unfold expandBranch_fun_declarations_correspondence in IHss.
      intro ; specialize IHss with (var := var).
      destruct (eqVneq var (nat_to_var (s * 3 + 1))).
      * rewrite CELemmas.find_add_eq ; try (rewrite /CE.SE.eq e0 eq_refl //).
        rewrite CELemmas.find_add_eq // ; try (rewrite /CE.SE.eq e0 eq_refl //).
      * rewrite CELemmas.find_add_neq ; try (apply negbTE in i ; rewrite /CE.SE.eq i //).
        rewrite CELemmas.find_add_neq // ; try (apply negbTE in i ; rewrite /CE.SE.eq i //).
    - (* Sreg *)
      unfold expandBranch_fun_declarations_preserve_correspondence_hfstmt_seq ;
      unfold expandBranch_fun_declarations_preserve_correspondence_hfstmt_seq in IHss.
      simpl expandBranch_precondition_declarations.
      simpl expandBranch_fun.
      intros.
      specialize IHss with (ce_previous := ce_previous) (cm_previous := cm_previous)
            (ce_other_modules := ce_other_modules).
      destruct (expandBranch_precondition_declarations ss ce_other_modules ce_previous) ; try done.
      destruct (expandBranch_fun ss ce_other_modules cm_previous) ; try done.
      destruct p as [ss_result0 cm_result0].
      specialize IHss with (ce_result := e) (cm_result := cm_result0) (ss_result := ss_result0).
      apply IHss in H ; try done ; clear IHss ; rename H into IHss.
      destruct (type h) ; try done.
      unfold init_register, ref2var in H1.
      destruct (CE.find (nat_to_var (s * 3 + 1)) e) ; try done.
      injection H0 ; injection H1 ; clear H0 H1 ; intros H0 _ H1.
      rewrite -H0 -H1.
      unfold expandBranch_fun_declarations_correspondence ;
      unfold expandBranch_fun_declarations_correspondence in IHss.
      intro ; specialize IHss with (var := var).
      destruct (eqVneq var (nat_to_var (s * 3 + 1))).
      * rewrite CELemmas.find_add_eq ; try (rewrite /CE.SE.eq e0 eq_refl //).
        rewrite CELemmas.find_add_eq // ; try (rewrite /CE.SE.eq e0 eq_refl //).
      * rewrite CELemmas.find_add_neq ; try (apply negbTE in i ; rewrite /CE.SE.eq i //).
        rewrite CELemmas.find_add_neq // ; try (apply negbTE in i ; rewrite /CE.SE.eq i //).
    - (* Smem is similar to Sreg (but more complex, because type_of_mem is composite). *)
      admit.
    - (* Sinst is similar to Smem *)
      admit.
    - (* Snode is similar to Sskip *)
      unfold expandBranch_fun_declarations_preserve_correspondence_hfstmt_seq ;
      unfold expandBranch_fun_declarations_preserve_correspondence_hfstmt_seq in IHss.
      simpl expandBranch_precondition_declarations.
      simpl expandBranch_fun.
      intros.
      specialize IHss with (ce_previous := ce_previous) (cm_previous := cm_previous)
            (ce_result := ce_result) (cm_result := cm_result)
            (ce_other_modules := ce_other_modules).
      destruct (expandBranch_precondition_declarations ss ce_other_modules ce_previous) ; try done.
      destruct (expandBranch_fun ss ce_other_modules cm_previous) ; try done.
      destruct p as [ss_result0 cm_result0].
      apply IHss with (ss_result := ss_result0) ; try done.
      injection H1 ; clear H1 ; intros H1 _.
      rewrite H1 ; reflexivity.
    - (* Sfcnct *)
      unfold expandBranch_fun_declarations_preserve_correspondence_hfstmt_seq ;
      unfold expandBranch_fun_declarations_preserve_correspondence_hfstmt_seq in IHss.
      simpl expandBranch_precondition_declarations.
      simpl expandBranch_fun.
      intros.
      specialize IHss with (ce_previous := ce_previous) (cm_previous := cm_previous)
            (ce_other_modules := ce_other_modules).
      destruct (expandBranch_precondition_declarations ss ce_other_modules ce_previous) ; try done.
      destruct (expandBranch_fun ss ce_other_modules cm_previous) ; try done.
      destruct p as [ss_result0 cm_result0].
      specialize IHss with (ce_result := e) (cm_result := cm_result0) (ss_result := ss_result0).
      apply IHss in H ; try done ; clear IHss ; rename H into IHss.
      destruct (ref2var h) ; try done.
      unfold expandBranch_fun_declarations_correspondence ;
      unfold expandBranch_fun_declarations_correspondence in IHss.
      intro ; specialize IHss with (var := var).
      destruct (CE.find s e) eqn: Hfind ; try done.
      destruct p as [comp_typ fcomp].
      destruct comp_typ ; try done.
      destruct f ; try done.
      destruct (orient_of_comp fcomp == Source) eqn: Horient ; try done.
      injection H0 ; injection H1 ; clear H0 H1 ; intros H0 _ H1.
      rewrite -H0 -H1.
      destruct (eqVneq var s).
      * rewrite e0 Hfind Horient CELemmas.find_add_eq ; try (rewrite /CE.SE.eq eq_refl //).
        done.
      * apply negbTE in i.
        rewrite CELemmas.find_add_neq // /CE.SE.eq i //.
    - (* Spcnct *)
      unfold expandBranch_fun_declarations_preserve_correspondence_hfstmt_seq.
      simpl expandBranch_precondition_declarations.
      intros.
      destruct (expandBranch_precondition_declarations ss ce_other_modules ce_previous) ;
           done.
    - (* Sinvalid *)
      unfold expandBranch_fun_declarations_preserve_correspondence_hfstmt_seq ;
      unfold expandBranch_fun_declarations_preserve_correspondence_hfstmt_seq in IHss.
      simpl expandBranch_precondition_declarations.
      simpl expandBranch_fun.
      intros.
      specialize IHss with (ce_previous := ce_previous) (cm_previous := cm_previous)
            (ce_other_modules := ce_other_modules).
      destruct (expandBranch_precondition_declarations ss ce_other_modules ce_previous) ; try done.
      destruct (expandBranch_fun ss ce_other_modules cm_previous) ; try done.
      destruct p as [ss_result0 cm_result0].
      specialize IHss with (ce_result := e) (cm_result := cm_result0) (ss_result := ss_result0).
      apply IHss in H ; try done ; clear IHss ; rename H into IHss.
      unfold invalidate_cmpnt in H1.
      destruct (ref2var h) ; try done.
      unfold expandBranch_fun_declarations_correspondence ;
      unfold expandBranch_fun_declarations_correspondence in IHss.
      intro ; specialize IHss with (var := var).
      destruct (CE.find s e) eqn: Hfind ; try done.
      destruct p as [comp_typ fcomp].
      destruct comp_typ ; try done.
      destruct f ; try done.
      destruct (orient_of_comp fcomp == Source) eqn: Horient ; try done.
      injection H0 ; injection H1 ; clear H0 H1 ; intros H0 _ H1.
      rewrite -H0 -H1.
      destruct (eqVneq var s).
      * rewrite e0 Hfind Horient CELemmas.find_add_eq ; try (rewrite /CE.SE.eq eq_refl //).
        done.
      * apply negbTE in i.
        rewrite CELemmas.find_add_neq // /CE.SE.eq i //.
    - (* Swhen *)
      rename h into cond, h0 into ss_true, h1 into ss_false.
      unfold expandBranch_fun_declarations_preserve_correspondence_hfstmt_seq ;
      unfold expandBranch_fun_declarations_preserve_correspondence_hfstmt_seq in IHss.
      simpl expandBranch_precondition_declarations.
      simpl expandBranch_fun.
      intros.
      specialize IHss with (ce_previous := ce_previous) (cm_previous := cm_previous)
            (ce_other_modules := ce_other_modules).
      specialize expandBranch_fun_declarations_preserve_correspondence_Swhen
      with (s := Swhen cond ss_true ss_false).
      unfold expandBranch_fun_declarations_preserve_correspondence_hfstmt_seq in expandBranch_fun_declarations_preserve_correspondence_Swhen.
      destruct expandBranch_fun_declarations_preserve_correspondence_Swhen as [IHss_true IHss_false].
      destruct (expandBranch_precondition_declarations ss ce_other_modules ce_previous) as [ce_before|] ; try done.
      destruct (expandBranch_fun ss ce_other_modules cm_previous) as [p_before|] ; try done.
      destruct p_before as [ss_result_before cm_result_before].
      specialize IHss with (ce_result := ce_before) (cm_result := cm_result_before) (ss_result := ss_result_before).
      assert (IHss' : expandBranch_fun_declarations_correspondence ce_before cm_result_before)
            by (apply IHss ; done) ; clear IHss.
      specialize IHss_true with (ce_previous := ce_before) (cm_previous := cm_result_before)
            (ce_other_modules := ce_other_modules).
      specialize IHss_false with (ce_previous := ce_before) (cm_previous := cm_result_before)
            (ce_other_modules := ce_other_modules).
      destruct (expandBranch_precondition_declarations ss_true ce_other_modules ce_before) as [ce_true|] eqn: Hce_true ; try done.
      destruct (expandBranch_precondition_declarations ss_false ce_other_modules ce_before) as [ce_false|] eqn: Hce_false ; try done.
      destruct (expandBranch_fun ss_true ce_other_modules cm_result_before) as [p_true|] ; try done.
      destruct (expandBranch_fun ss_false ce_other_modules cm_result_before) as [p_false|] ; try done.
      destruct p_true as [ss_result_true cm_result_true].
      destruct p_false as [ss_result_false cm_result_false].
      specialize IHss_true with (ce_result := ce_true) (cm_result := cm_result_true) (ss_result := ss_result_true).
      specialize IHss_false with (ce_result := ce_false) (cm_result := cm_result_false) (ss_result := ss_result_false).
      assert (IHss_true' : expandBranch_fun_declarations_correspondence ce_true cm_result_true)
            by (apply IHss_true ; done) ; clear IHss_true.
      assert (IHss_false' : expandBranch_fun_declarations_correspondence ce_false cm_result_false)
            by (apply IHss_false ; done) ; clear IHss_false.
      unfold expandBranch_fun_declarations_correspondence ;
      unfold expandBranch_fun_declarations_correspondence in IHss', IHss_true', IHss_false'.
      intro.
      specialize IHss' with (var := var) ;
      specialize IHss_true' with (var := var) ;
      specialize IHss_false' with (var := var).
      destruct (ce_has_no_double_declarations ce_before ce_true ce_false) eqn: Hno_double_declarations ; try done.
      unfold combine_branches_ce in H0.
      unfold combine_branches in H1.
      injection H0 ; injection H1 ; clear H0 H1 ; intros H1 _ H0.
      destruct (CE.find var ce_before) as [p_before|] eqn: Hfind_before.
      * (* the component was declared before the Swhen statement. *)
        (* We can use expandBranch_precondition_declarations_does_not_redefine
           to prove that CE.find var ce_true and CE.find var ce_false are the same. *)
        assert (CE.find var ce_true = Some p_before)
        by (apply expandBranch_precondition_declarations_does_not_redefine
            with (ce_other_modules := ce_other_modules) (ss := ss_true) (ce_previous := ce_before) ;
            done).
        assert (CE.find var ce_false = Some p_before)
        by (apply expandBranch_precondition_declarations_does_not_redefine
            with (ce_other_modules := ce_other_modules) (ss := ss_false) (ce_previous := ce_before) ;
            done).
        rewrite H2 in IHss_true'.
        rewrite H3 in IHss_false'.
        destruct p_before as [comp_typ_before fcomp_before].
        rewrite -H0 CE.map2_1 ;
              try (left ;
                   unfold CE.In ;
                   exists (comp_typ_before, fcomp_before) ;
                   apply CE.find_2, H2).
        rewrite /combine_branches_ce_map2_helper H2 -H1.
        destruct (orient_of_comp fcomp_before == Source) eqn: Horient.
        + (* the component has source orientation, so it should not appear anywhere.
             This can be proven based on the fact that its orientation will not change. *)
          split; try done ; intro.
          assert (IHss_true'' : CE.find var cm_result_true = None)
                by (apply rwP with (CE.find var cm_result_true == None) ; try apply eqP ;
                    apply IHss_true' ; done) ;
                clear IHss_true'.
          assert (IHss_false'' : CE.find var cm_result_false = None)
                by (apply rwP with (CE.find var cm_result_false == None) ; try apply eqP ;
                    apply IHss_false' ; done) ;
                clear IHss_false'.
          destruct (CE.find var (CE.map2 (map2_helper_cs_tf cond) cm_result_true cm_result_false)) eqn: Hfind_after ;
                try done.
          assert (CE.In var cm_result_true \/ CE.In var cm_result_false)
                by (apply CE.map2_2 with (f := map2_helper_cs_tf cond) ;
                    exists d ;
                    apply CE.find_2, Hfind_after).
          destruct H5.
          - destruct H5.
            apply CE.find_1 in H5.
            rewrite H5 in IHss_true''.
            discriminate.
          - destruct H5.
            apply CE.find_1 in H5.
            rewrite H5 in IHss_false''.
            discriminate.
        + (* the component was defined before according to IHss',
             so it is also afterwards. *)
          split ; try done.
          assert (CE.find var cm_result_true <> None).
                (* Probably there exists a more elegant proof than the following... *)
                move /eqP => H5.
                apply IHss_true' in H5 ; done.
          rewrite CE.map2_1.
          - unfold map2_helper_cs_tf.
            destruct (CE.find var cm_result_true) ; try done.
            destruct d ; try done ;
            destruct (CE.find var cm_result_false) ; try done ;
            destruct d ; try done.
            destruct (h == h0) ; done.
          - left.
            unfold CE.In.
            destruct (CE.find var cm_result_true) eqn: Hfind_true ; try done.
            exists d.
            apply CE.find_2, Hfind_true.
      destruct (CE.find var ce_true) eqn: Hfind_true.
      * (* the component was declared in the true branch. *)
        rewrite -H0 CE.map2_1 ;
              try (left ;
                   unfold CE.In ;
                   exists p ;
                   apply CE.find_2, Hfind_true).
        rewrite /combine_branches_ce_map2_helper Hfind_true -H1.
        destruct p as [comp_typ_true fcomp_true].
        assert (CE.find var ce_false = None).
              (* should follow from type correctness of declarations:
                 a component cannot be declared in both branches of a Swhen statement *)
              apply CE.is_empty_2 in Hno_double_declarations.
              unfold CE.Empty in Hno_double_declarations.
              destruct (CE.find var ce_false) eqn: Hfind_false ; try done.
              destruct p as [comp_typ_false fcomp_false].
              specialize Hno_double_declarations with (a := var) (e := (comp_typ_true, fcomp_true)).
              contradict Hno_double_declarations.
              apply CE.find_2.
              rewrite CE.map2_1.
              + rewrite CE.map2_1 ;
                      try (left ; exists (comp_typ_true, fcomp_true) ;
                           apply CE.find_2, Hfind_true).
                rewrite CE.map2_1 ;
                      try (left ; exists (comp_typ_false, fcomp_false) ;
                           apply CE.find_2, Hfind_false).
                rewrite Hfind_true Hfind_false Hfind_before
                        /ce_map_difference_helper
                        /ce_map_intersection_helper //.
              + left.
                exists (comp_typ_true, fcomp_true).
                apply CE.find_2.
                rewrite CE.map2_1 ;
                      try (left ; exists (comp_typ_true, fcomp_true) ;
                           apply CE.find_2, Hfind_true).
                rewrite /ce_map_difference_helper Hfind_before Hfind_true //.
        rewrite H2 in IHss_false'.
        destruct (orient_of_comp fcomp_true == Source).
        + (* the component has source orientation, so it should not appear anywhere.
             This can be proven based on the fact that its orientation will not change. *)
          split; try done ; intro.
          assert (IHss_true'' : CE.find var cm_result_true = None)
                by (apply rwP with (CE.find var cm_result_true == None) ; try apply eqP ;
                    apply IHss_true' ; done) ;
                clear IHss_true'.
          move /eqP : IHss_false' => IHss_false''.
          destruct (CE.find var (CE.map2 (map2_helper_cs_tf cond) cm_result_true cm_result_false)) eqn: Hfind_after ;
                try done.
          assert (CE.In var cm_result_true \/ CE.In var cm_result_false)
                by (apply CE.map2_2 with (f := map2_helper_cs_tf cond) ;
                    exists d ;
                    apply CE.find_2, Hfind_after).
          destruct H4.
          - destruct H4.
            apply CE.find_1 in H4.
            rewrite H4 in IHss_true''.
            discriminate.
          - destruct H4.
            apply CE.find_1 in H4.
            rewrite H4 in IHss_false''.
            discriminate.
        + (* the component was defined in ss_true according to IHss_true',
             so it is also afterwards. *)
          split ; try done.
          assert (CE.find var cm_result_true <> None).
                (* Probably there exists a more elegant proof than the following... *)
                move /eqP => H4.
                apply IHss_true' in H4 ; done.
          rewrite CE.map2_1.
          - unfold map2_helper_cs_tf.
            destruct (CE.find var cm_result_true) ; try done.
            destruct d ; try done ;
            destruct (CE.find var cm_result_false) ; done.
          - left.
            unfold CE.In.
            destruct (CE.find var cm_result_true) eqn: Hfind_cm_true ; try done.
            exists d.
            apply CE.find_2, Hfind_cm_true.
      destruct (CE.find var ce_false) eqn: Hfind_false.
      * (* the component was declared in the false branch. *)
        rewrite -H0 CE.map2_1 ;
              try (right ;
                   unfold CE.In ;
                   exists p ;
                   apply CE.find_2, Hfind_false).
        rewrite /combine_branches_ce_map2_helper Hfind_true Hfind_false -H1.
        destruct p as [comp_typ_false fcomp_false].
        destruct (orient_of_comp fcomp_false == Source).
        + (* the component has source orientation, so it should not appear anywhere.
             This can be proven based on the fact that its orientation will not change. *)
          split; try done ; intro.
          move /eqP : IHss_true' => IHss_true''.
          assert (IHss_false'' : CE.find var cm_result_false = None)
                by (apply rwP with (CE.find var cm_result_false == None) ; try apply eqP ;
                    apply IHss_false' ; done) ;
                clear IHss_false'.
          destruct (CE.find var (CE.map2 (map2_helper_cs_tf cond) cm_result_true cm_result_false)) eqn: Hfind_after ;
                try done.
          assert (CE.In var cm_result_true \/ CE.In var cm_result_false)
                by (apply CE.map2_2 with (f := map2_helper_cs_tf cond) ;
                    exists d ;
                    apply CE.find_2, Hfind_after).
          destruct H3.
          - destruct H3.
            apply CE.find_1 in H3.
            rewrite H3 in IHss_true''.
            discriminate.
          - destruct H3.
            apply CE.find_1 in H3.
            rewrite H3 in IHss_false''.
            discriminate.
        + (* the component was defined in ss_false according to IHss_false',
             so it is also afterwards. *)
          split ; try done.
          assert (CE.find var cm_result_false <> None).
                move /eqP => H4.
                apply IHss_false' in H4 ; done.
          rewrite CE.map2_1.
          - unfold map2_helper_cs_tf.
            destruct (CE.find var cm_result_true) ; try done.
            apply IHss_false'.
          - right.
            unfold CE.In.
            destruct (CE.find var cm_result_false) eqn: Hfind_cm_false ; try done.
            exists d.
            apply CE.find_2, Hfind_cm_false.
      * (* the component was not declared anywhere. *)
        rewrite -H0 -H1.
        destruct (CE.find var (CE.map2 combine_branches_ce_map2_helper ce_true ce_false)) eqn: Hfind_after.
        + assert (CE.In var ce_true \/ CE.In var ce_false)
                by (apply CE.map2_2 with (f := combine_branches_ce_map2_helper) ;
                    exists p ;
                    apply CE.find_2, Hfind_after).
          destruct H2.
          - destruct H2.
            apply CE.find_1 in H2.
            rewrite H2 in Hfind_true.
            discriminate.
          - destruct H2.
            apply CE.find_1 in H2.
            rewrite H2 in Hfind_false.
            discriminate.
        + rewrite Hfind_after.
          destruct (CE.find var (CE.map2 (map2_helper_cs_tf cond) cm_result_true cm_result_false)) eqn: Hfind_cm_after ; try done.
          assert (CE.In var cm_result_true \/ CE.In var cm_result_false)
                by (apply CE.map2_2 with (f := map2_helper_cs_tf cond) ;
                    exists d ;
                    apply CE.find_2, Hfind_cm_after).
          destruct H2.
          - destruct H2.
            apply CE.find_1 in H2.
            rewrite H2 in IHss_true'.
            done.
          - destruct H2.
            apply CE.find_1 in H2.
            rewrite H2 in IHss_false'.
            done.
* clear expandBranch_fun_declarations_preserve_correspondence_Swhen.
  destruct s ; try trivial.
  split ; apply expandBranch_fun_declarations_preserve_correspondence.
Admitted.

(* Correctness theorem:
   If ...
   then expandBranch_sem_conform is true. *)

Definition expandBranch_correct_hfstmt_seq (ce_other_modules : CE.env) (ss : hfstmt_seq) : Prop :=
   forall (ce_previous_declarations : CE.env) (cm_previous : cmap),
      expandBranch_fun_declarations_correspondence ce_previous_declarations cm_previous ->
         expandBranch_sem_conform ss ce_other_modules ce_previous_declarations cm_previous.

Theorem expandBranch_correct :
   forall (ce_other_modules : CE.env) (ss : hfstmt_seq), expandBranch_correct_hfstmt_seq ce_other_modules ss
(* Programs that cannot be handled by expandBranch_fun and generate an error message
   are always regarded as correct.
   Perhaps this will need to be refined later. *)
with expandBranch_correct_Swhen :
   forall (ce_other_modules : CE.env) (s : hfstmt),
      if s is Swhen _ ss_true ss_false
      then    expandBranch_correct_hfstmt_seq ce_other_modules ss_true
           /\ expandBranch_correct_hfstmt_seq ce_other_modules ss_false
      else True.
Proof.
* clear expandBranch_correct.
  induction ss ;
  unfold expandBranch_correct_hfstmt_seq, expandBranch_sem_conform ;
  intros.
  + unfold expandBranch_precondition_declarations, expandBranch_fun, ref2var.
    intro.
    destruct (CE.find (nat_to_var (id * 3 + 1)) ce_previous_declarations) eqn: Hfind ; try done.
    destruct p as [comp_typ f].
    destruct comp_typ as [ft|reg|mem|]; try done.
    - assert (exists t : fgtyp, ft = Gtyp t) by admit.
      destruct H1 as [t].
      rewrite H1.
      destruct (orient_of_comp f == Source) ; try done.
      simpl expandBranch_one_component_sem_conform.
      destruct (CE.find (nat_to_var (id * 3 + 1)) cm_previous) ; try done.
      destruct d ; done.
    - (* register is similar to variable *)
      admit.
    - (* memory is similar to variable *)
      admit.
  + unfold expandBranch_correct_hfstmt_seq in IHss.
    assert (IHss' : match expandBranch_precondition_declarations ss ce_other_modules ce_previous_declarations with
                    | OK ce_declarations =>
                        match expandBranch_fun ss ce_other_modules cm_previous with
                        | OK (_, cm_result) =>
                            forall id : VarOrder.T,
                            match ref2var (Eid id) with
                            | OK var =>
                                match CE.find var ce_declarations with
                                | Some (@Aggr_typ _ t, fcomp) =>
                                    if orient_of_comp fcomp == Source
                                    then expandBranch_one_component_sem_conform_flipped (Eid id) t ss cm_result cm_previous
                                    else expandBranch_one_component_sem_conform (Eid id) t ss cm_result cm_previous
                                | Some (Reg_typ reg, _) =>
                                    expandBranch_one_component_sem_conform (Eid id) (type reg) ss cm_result cm_previous
                                | Some (Mem_typ mem, _) =>
                                    match type_of_mem mem with
                                    | OK tom =>
                                        expandBranch_one_component_sem_conform_flipped (Eid id) tom ss cm_result cm_previous
                                    | Err _ => false
                                    end
                                | _ => true
                                end
                            | Err _ => true
                            end
                        | Err _ => true
                        end
                    | Err _ => true
                    end)
          by (apply IHss ; done).
    clear IHss.
    simpl expandBranch_precondition_declarations.
    destruct (expandBranch_precondition_declarations ss ce_other_modules ce_previous_declarations) as [ce_declarations|] eqn: Hdeclarations ; try done.
    destruct h eqn: Hstmt ; try done.
    - (* Skip *)
      simpl expandBranch_fun.
      destruct (expandBranch_fun ss ce_other_modules cm_previous) ; try done.
      destruct p as [_ cm_result].
      intro.
      specialize IHss' with (id := id).
      unfold ref2var ; unfold ref2var in IHss'.
      destruct (CE.find (nat_to_var (id * 3 + 1)) ce_declarations) eqn: Hfind ; try done.
      destruct p as [comp_typ fcomp].
      destruct comp_typ as [ft|reg|mem|] ; try done.
      - assert (exists t : fgtyp, ft = Gtyp t) by admit.
        destruct H1.
        rewrite H1 ; rewrite H1 in IHss'.
        exact IHss'.
      - (* register is similar to variable *)
        admit.
      - (* memory is similar to variable *)
        admit.
    + (* Swire *)
      assert (exists t : fgtyp, f = Gtyp t) by admit.
      destruct H1.
      rewrite H1.
      destruct (CE.find (nat_to_var (s * 3 + 1)) ce_declarations) eqn: Halready_declared ; try done.
      simpl expandBranch_fun.
      destruct (expandBranch_fun ss ce_other_modules cm_previous) ; try done.
      destruct p as [_ cm_result].
      intro.
      specialize IHss' with (id := id).
      unfold ref2var ; unfold ref2var in IHss'.
      destruct (eqVneq s id).
      - rewrite e.
        rewrite CELemmas.find_add_eq ; try rewrite /CE.SE.eq eq_refl //.
        unfold aggr_typ, expandBranch_one_component_sem_conform, ref2var.
        rewrite CELemmas.find_add_eq ; try rewrite /CE.SE.eq eq_refl //.
        simpl expandBranch_one_var_sem.
        rewrite eq_refl /expr_tree_to_def_expr eq_refl //.
      - assert (~ CE.SE.eq (nat_to_var (id * 3 + 1)) (nat_to_var (s * 3 + 1))).
              unfold CE.SE.eq.
              contradict i.
              move /eqP : i => i.
              apply can_inj with (g := nat_of_bin) in i ;
                    try apply bin_of_natK.
              move /eqP : i => i.
              rewrite eqn_add2r eqn_mul2r orFb in i.
              move /eqP : i => i.
              apply can_inj with (g := bin_of_nat) in i ;
                    try apply nat_of_binK.
              rewrite i eq_refl //.
        rewrite CELemmas.find_add_neq ; try exact H2.
        destruct (CE.find (nat_to_var (id * 3 + 1)) ce_declarations) ; try done.
        destruct p as [comp_typ fcomp].
        destruct comp_typ as [ft|reg|mem|] ; try done.
        * assert (exists t : fgtyp, ft = Gtyp t) by admit.
          destruct H3.
          rewrite H3 ; rewrite H3 in IHss'.
          destruct (orient_of_comp fcomp == Source) ; try done.
          unfold expandBranch_one_component_sem_conform, ref2var ;
          unfold expandBranch_one_component_sem_conform, ref2var in IHss'.
          simpl expandBranch_one_var_sem.
          rewrite CELemmas.find_add_neq ; try exact H2.
          apply negbTE in i.
          rewrite (eq_sym id) i.
          exact IHss'.
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
    + (* Sinst s s0, i.e. s = identifier and s0 = type of the module. *)
      rename s0 into mdl.
      simpl expandBranch_fun.
      destruct (expandBranch_fun ss ce_other_modules cm_previous) eqn: Hebf ;
            try (destruct (CE.find mdl ce_other_modules) ;
                 try done ;
                 destruct p, c, f, (CE.find (nat_to_var (s * 3 + 1)) ce_declarations) ;
                 done).
      destruct p as [ss_result cm_result].
      destruct (CE.find mdl ce_other_modules) eqn: Hmdl ; try done.
      destruct p as [ss_result_mdl cm_result_mdl].
      destruct ss_result_mdl ; try done.
      destruct cm_result_mdl ; try done.
      destruct (CE.find (nat_to_var (s * 3 + 1)) ce_declarations) eqn: Hs ; try done.
      destruct (init_instance s mdl ce_other_modules cm_result) eqn: Hinit_instance ; try done.
      intro.
      specialize IHss' with (id := id).
      unfold ref2var ; unfold ref2var in IHss'.
      destruct (eqVneq s id).
      - (* id now does not have a ground type but is part of the instance.
           That means, it has type (Btyp ...) where each field has a ground type. *)
        rewrite !e CELemmas.find_add_eq ; try rewrite /CE.SE.eq eq_refl //.
        rewrite e in Hinit_instance.
        unfold aggr_typ.
        (* Now we should argue as follows:
           1. (to simplify) the type f is some (Btyp f0),
              where f0 is a list of ground type entries.
              (This should be based on H1 and Hs0.)
           2. induction over f0. *)
        unfold expandBranch_precondition_ce in H0.
        specialize H0 with (id := mdl).
        unfold init_instance in Hinit_instance.
        destruct (CE.find mdl ce_other_modules) ; try done.
        destruct p.
        destruct c0, f0 ; try discriminate.
        destruct f1 ; try done.
        injection Hmdl ; intro Hf0 ; clear Hmdl.
        rewrite -Hf0 ; clear Hf0 f.
        simpl expandBranch_one_component_sem_conform_flipped.
        move : H0 c Hinit_instance.
        simpl init_ref.
        induction f0 ; try done.
        simpl expandBranch_precondition_ce_module_fields ; intros.
        destruct f0 ; try done.
        simpl expandBranch_one_component_sem_conform_flipped_fields ;
        simpl expandBranch_one_component_sem_conform_flipped_fields in IHf0.
        simpl init_ref_bundle in Hinit_instance.
        destruct f.
        + rewrite eq_refl /expr_tree_to_def_expr /var_to_nat bin_of_natK.
          (* Actually I am not sure whether “Sink” is the correct
             orientation in Hinit_instance. *)
          (*rewrite /var_to_nat bin_of_natK in Hinit_instance.*)
          destruct (init_ref_bundle (Eid id) f1 Sink
                     cm_result) eqn: Hirb ; try done.
          injection Hinit_instance ; clear Hinit_instance ; intro Hinit_instance.
          (* I don't know how to continue here... *)
          admit.
        + apply IHf0 ; try done.
          destruct (init_ref_bundle (Eid id) f1 Sink cm_result) ; try done.
          (* Here it again looks like the orientation in Hinit_instance should be different. *)
          admit.
      - rewrite CELemmas.find_add_neq.
        * (* This can be proven using IHss' and Hinit_instance.
             Similar to the above, we use that s != id and therefore
             the relevant parts of cm_result and c are equal. *)
          admit.
        * unfold CE.SE.eq.
          contradict i.
          move /eqP : i => i.
          apply can_inj with (g := nat_of_bin) in i ;
                try apply bin_of_natK.
          move /eqP : i => i.
          rewrite eqn_add2r eqn_mul2r orFb in i.
          move /eqP : i => i.
          apply can_inj with (g := bin_of_nat) in i ;
                try apply nat_of_binK.
          rewrite i eq_refl //.
    + (* Snode s h0 *)
      simpl expandBranch_fun.
      destruct (expandBranch_fun ss ce_other_modules cm_previous) ; try done.
      destruct p as [ss_result cm_result].
      (* expandBranch_one_component_sem_conform ignores the Snode statement,
         so it should be possible to prove this based on IHss'. *)
      admit.
    + (* Sfcnct h1 h2 *)
      simpl expandBranch_fun.
      destruct (ref2var h0) eqn: Hh0 ; try done.
      destruct (CE.find s ce_declarations) eqn: Hfinds ; try done.
      destruct p as [comp_typ_s fcomp_s].
      destruct comp_typ_s ; try done.
      destruct f ; try done.
      destruct (expandBranch_fun ss ce_other_modules cm_previous) ;
      destruct (orient_of_comp fcomp_s == Source) eqn: Horient ; try done.
      destruct p as [ss_result cm_result].
      intro.
      specialize IHss' with (id := id).
      destruct (eqVneq (Eid id) h0).
      - rewrite e Hh0 ; rewrite e Hh0 in IHss'.
        destruct (CE.find s ce_declarations) ; try done.
        destruct p as [comp_typ fcomp].
        injection Hfinds ; clear Hfinds ; intros.
        rewrite H2 H1 Horient ; rewrite H2 H1 Horient in IHss'.
        simpl expandBranch_one_component_sem_conform.
        rewrite Hh0 CELemmas.find_add_eq ; try (unfold CE.SE.eq ; done).
        rewrite eq_refl /expr_tree_to_def_expr eq_refl //.
      - unfold ref2var ; unfold ref2var in IHss'.
        destruct (CE.find (nat_to_var (id * 3 + 1)) ce_declarations) eqn: Hfind ; try done.
        destruct p as [comp_typ fcomp].
        destruct comp_typ as [ft|reg|mem|] ; try done.
        * assert (exists t : fgtyp, ft = Gtyp t) by admit.
          destruct H1 as [t].
          rewrite H1 ; rewrite H1 in IHss'.
          destruct (orient_of_comp fcomp == Source) ; try done.
          unfold expandBranch_one_component_sem_conform, ref2var ;
          unfold expandBranch_one_component_sem_conform, ref2var in IHss'.
          rewrite CELemmas.find_add_neq.
          + simpl expandBranch_one_var_sem.
            apply negbTE in i ; rewrite i.
            exact IHss'.
          + unfold CE.SE.eq.
            move /eqP : i => i ; contradict i ; move /eqP : i => i.
            rewrite -i in Hh0.
            destruct h0.
            - unfold ref2var in Hh0.
              injection Hh0 ; clear Hh0 ; unfold nat_to_var ; intro Hh1.
              assert (s0 * 3 + 1 == id * 3 + 1) by (rewrite -(bin_of_natK (s0 * 3 + 1)) Hh1 bin_of_natK eq_refl //).
              rewrite addn1 addn1 eqSS eqn_pmul2r // in H2.
              move /eqP : H2 => H2.
              rewrite -(nat_of_binK s0) H2 nat_of_binK ; reflexivity.
            - contradict Hh0.
              clear.
              simpl ref2var.
              destruct (ref2var h0) ; try done.
              injection ; unfold nat_to_var ; intro Hh1.
              enough (2 == 1) by done.
              replace 1 with ((id * 3 + 1) %% 3) at 2 by (rewrite modnD // modnMl //).
              replace 2 with ((pair (var_to_nat s) s0 * 3 + 2) %% 3) at 1 by (rewrite modnD // modnMl //).
              rewrite -(bin_of_natK (pair (var_to_nat s) s0 * 3 + 2)) Hh1 bin_of_natK eq_refl //.
            - contradict Hh0.
              clear.
              simpl ref2var.
              destruct (ref2var h0) ; try done.
              injection ; unfold nat_to_var ; intro Hh1.
              enough (0 == 1) by done.
              replace 1 with ((id * 3 + 1) %% 3) by (rewrite modnD // modnMl //).
              replace 0 with ((pair (var_to_nat s) n * 3 + 3) %% 3) at 1 by (rewrite modnD // modnMl //).
              rewrite -(bin_of_natK (pair (var_to_nat s) n * 3 + 3)) Hh1 bin_of_natK eq_refl //.
            - contradict Hh0.
              simpl ref2var.
              discriminate.
        * (* register is similar to variable *)
          admit.
        * (* memory is similar to variable *)
          admit.
    + (* Sinvalid h0. This is similar to Sfcnct, so we can skip this case. *)
      admit.
    + rename h into stmt, h0 into cond, h1 into ss_true, h2 into ss_false.
      (* Swhen cond ss_true ss_false *)
      specialize expandBranch_correct_Swhen with (ce_other_modules := ce_other_modules) (s := Swhen cond ss_true ss_false).
      unfold expandBranch_correct_hfstmt_seq, expandBranch_sem_conform in expandBranch_correct_Swhen.
      destruct expandBranch_correct_Swhen as [IHss_true IHss_false].
      specialize IHss_true with (ce_previous_declarations := ce_declarations).
      specialize IHss_false with (ce_previous_declarations := ce_declarations).
      destruct (expandBranch_precondition_declarations ss_true ce_other_modules
        ce_declarations) as [ce_true_result|] eqn: Htrue_declarations ; try done.
      destruct (expandBranch_precondition_declarations ss_false ce_other_modules
        ce_declarations) as [ce_false_result|] eqn: Hfalse_declarations ; try done.
      destruct (ce_has_no_double_declarations ce_declarations ce_true_result ce_false_result) eqn: Hno_double_declarations ; try done.
      unfold combine_branches_ce.
      simpl expandBranch_fun.
      destruct (expandBranch_fun ss ce_other_modules cm_previous) eqn: Hebf_before ; try done.
      destruct p as [ss_result cm_result].
      specialize IHss_true with (cm_previous := cm_result).
      specialize IHss_false with (cm_previous := cm_result).
      destruct (expandBranch_fun ss_true ce_other_modules cm_result) eqn: Htrue_branch ; try done.
      destruct p as [ss_true_result cm_true_result].
      destruct (expandBranch_fun ss_false ce_other_modules cm_result) eqn: Hfalse_branch ; try done.
      destruct p as [ss_false_result cm_false_result].
      unfold combine_branches.
      simpl snd.
      intro.
      specialize IHss' with (id := id).
      assert (expandBranch_fun_declarations_correspondence ce_declarations cm_result)
            by (apply (expandBranch_fun_declarations_preserve_correspondence ss ce_previous_declarations cm_previous)
                with (ce_other_modules := ce_other_modules) (ss_result := ss_result) ; done).
      assert (IHss_true' : match ref2var (Eid id) with
                           | OK var =>
                               match CE.find var ce_true_result with
                               | Some (@Aggr_typ _ t, fcomp) =>
                                   if orient_of_comp fcomp == Source
                                   then expandBranch_one_component_sem_conform_flipped
                                     (Eid id) t ss_true cm_true_result cm_result
                                   else expandBranch_one_component_sem_conform
                                     (Eid id) t ss_true cm_true_result cm_result
                               | Some (Reg_typ reg, _) =>
                                   expandBranch_one_component_sem_conform
                                     (Eid id) (type reg) ss_true cm_true_result cm_result
                               | Some (Mem_typ mem, _) =>
                                   match type_of_mem mem with
                                   | OK tom =>
                                       expandBranch_one_component_sem_conform_flipped
                                         (Eid id) tom ss_true cm_true_result cm_result
                                   | Err _ => false
                                   end
                               | _ => true
                               end
                           | Err _ => true
                           end)
            by (apply IHss_true ; done).
      clear IHss_true.
      assert (IHss_false' : match ref2var (Eid id) with
                            | OK var =>
                                match CE.find var ce_false_result with
                                | Some (@Aggr_typ _ t, fcomp) =>
                                    if orient_of_comp fcomp == Source
                                    then expandBranch_one_component_sem_conform_flipped
                                      (Eid id) t ss_false cm_false_result cm_result
                                    else expandBranch_one_component_sem_conform
                                      (Eid id) t ss_false cm_false_result cm_result
                                | Some (Reg_typ reg, _) =>
                                    expandBranch_one_component_sem_conform
                                      (Eid id) (type reg) ss_false cm_false_result cm_result
                                | Some (Mem_typ mem, _) =>
                                    match type_of_mem mem with
                                    | OK tom =>
                                        expandBranch_one_component_sem_conform_flipped
                                          (Eid id) tom ss_false cm_false_result cm_result
                                    | Err _ => false
                                    end
                                | _ => true
                                end
                            | Err _ => true
                            end)
            by (apply IHss_false ; done).
      clear IHss_false.
      unfold ref2var ; unfold ref2var in IHss' ;
      unfold ref2var in IHss_true' ; unfold ref2var in IHss_false'.
      (* In the following cases, we actually need something like:
             ce_declarations contains an entry for (nat_to_var (id * 3 + 1))
         iff cm_result       contains an entry for (nat_to_var (id * 3 + 1)). *)
      assert (expandBranch_fun_declarations_correspondence ce_true_result cm_true_result)
            by (apply (expandBranch_fun_declarations_preserve_correspondence ss_true ce_declarations cm_result)
                with (ce_other_modules := ce_other_modules) (ss_result := ss_true_result) ; done).
      assert (expandBranch_fun_declarations_correspondence ce_false_result cm_false_result)
            by (apply (expandBranch_fun_declarations_preserve_correspondence ss_false ce_declarations cm_result)
                with (ce_other_modules := ce_other_modules) (ss_result := ss_false_result) ; done).
      unfold expandBranch_fun_declarations_correspondence in H1.
      specialize H1 with (var := nat_to_var (id * 3 + 1)).
      unfold expandBranch_fun_declarations_correspondence in H2.
      specialize H2 with (var := nat_to_var (id * 3 + 1)).
      unfold expandBranch_fun_declarations_correspondence in H3.
      specialize H3 with (var := nat_to_var (id * 3 + 1)).
      destruct (CE.find (nat_to_var (id * 3 + 1)) ce_declarations) eqn: Hfind_ce_before.
      - (* id was declared before the Swhen statement. *)
        assert (Hfind_ce_true : CE.find (nat_to_var (id * 3 + 1)) ce_true_result = Some p).
              apply expandBranch_precondition_declarations_does_not_redefine
                    with (ce_other_modules := ce_other_modules) (ss := ss_true)
                         (ce_previous := ce_declarations) ; done.
        rewrite Hfind_ce_true in IHss_true'.
        rewrite Hfind_ce_true in H2.
        assert (Hfind_ce_false : CE.find (nat_to_var (id * 3 + 1)) ce_false_result = Some p).
              apply expandBranch_precondition_declarations_does_not_redefine
                    with (ce_other_modules := ce_other_modules) (ss := ss_false)
                         (ce_previous := ce_declarations) ; done.
        rewrite Hfind_ce_false in IHss_false'.
        rewrite Hfind_ce_false in H3.
        rewrite CE.map2_1 ;
              try (left ; exists p ; apply CE.find_2 ; exact Hfind_ce_true).
        unfold combine_branches_ce_map2_helper.
        rewrite Hfind_ce_true.
        destruct p as [comp_typ fcomp].
        destruct (orient_of_comp fcomp == Source) eqn: Horient.
        * (* the orientation is Source, so it is in none of the cmaps. *)
          destruct comp_typ as [ft|reg|mem|] ; try done.
          + assert (exists t : fgtyp, ft = Gtyp t) by admit.
            destruct H4 as [t] ; rewrite H4.
            done.
          + (* register is similar to variable *)
            admit.
          + (* memory is similar to variable *)
            admit.
        * (* the orientation is <> Source *)
          destruct comp_typ as [ft|reg|mem|] ; try done.
          + assert (exists t : fgtyp, ft = Gtyp t) by admit.
            destruct H4 as [t] ; rewrite H4 ; rewrite H4 in IHss' ;
            rewrite H4 in IHss_true' ; rewrite H4 in IHss_false'.
            unfold expandBranch_one_component_sem_conform, ref2var ;
            unfold expandBranch_one_component_sem_conform, ref2var in IHss' ;
            unfold expandBranch_one_component_sem_conform, ref2var in IHss_true' ;
            unfold expandBranch_one_component_sem_conform, ref2var in IHss_false'.
            assert (exists d : def_expr, CE.find (nat_to_var (id * 3 + 1)) cm_result = Some d).
                  destruct (CE.find (nat_to_var (id * 3 + 1)) cm_result) eqn: Hfind_cm_before.
                  - exists d ; reflexivity.
                  - rewrite eq_refl in H1 ; assert false by (apply H1 ; done) ; done.
            destruct H5 as [de_before].
            assert (exists d : def_expr, CE.find (nat_to_var (id * 3 + 1)) cm_true_result = Some d).
                  destruct (CE.find (nat_to_var (id * 3 + 1)) cm_true_result) eqn: Hfind_cm_true.
                  - exists d ; reflexivity.
                  - rewrite eq_refl in H2 ; assert false by (apply H2 ; done) ; done.
            destruct H6 as [de_true].
            assert (exists d : def_expr, CE.find (nat_to_var (id * 3 + 1)) cm_false_result = Some d).
                  destruct (CE.find (nat_to_var (id * 3 + 1)) cm_false_result) eqn: Hfind_cm_false.
                  - exists d ; reflexivity.
                  - rewrite eq_refl in H3 ; assert false by (apply H3 ; done) ; done.
            destruct H7 as [de_false].
            clear H1 H2 H3.
            rewrite CE.map2_1.
            - rewrite H6 H7.
              unfold map2_helper_cs_tf.
              simpl expandBranch_one_var_sem.
              (* Here we need to run an induction over the structure of the expr_tree
                 on the right-hand side of the equation.
                 (“destruct” is not sufficient because T_choice contains trees again.)
                 It should all be possible but it is long to write out the many cases... *)
              admit.
            - left.
              destruct (CE.find (nat_to_var (id * 3 + 1)) cm_true_result) eqn: Hfind_cm_true ; try done.
              exists d.
              apply CE.find_2 ; exact Hfind_cm_true.
          + (* register is similar to variable *)
            admit.
          + (* memory is similar to variable *)
            admit.
      destruct (CE.find (nat_to_var (id * 3 + 1)) ce_true_result) eqn: Hfind_ce_true.
      - (* id was declared in the true branch.
           We know that it was not declared in the false branch. *)
        rewrite CE.map2_1 ;
              try (left ;
                   unfold CE.In ;
                   exists p ;
                   apply CE.find_2, Hfind_ce_true).
        rewrite /combine_branches_ce_map2_helper Hfind_ce_true.
        destruct p as [comp_typ_true fcomp_true].
        assert (Hfind_ce_false : CE.find (nat_to_var (id * 3 + 1)) ce_false_result = None).
              (* should follow from type correctness of declarations:
                 a component cannot be declared in both branches of a Swhen statement *)
              apply CE.is_empty_2 in Hno_double_declarations.
              unfold CE.Empty in Hno_double_declarations.
              destruct (CE.find (nat_to_var (id * 3 + 1)) ce_false_result) eqn: Hfind_ce_false ; try done.
              destruct p as [comp_typ_false fcomp_false].
              specialize Hno_double_declarations with (a := (nat_to_var (id * 3 + 1))) (e := (comp_typ_true, fcomp_true)).
              contradict Hno_double_declarations.
              apply CE.find_2.
              rewrite CE.map2_1.
              + rewrite CE.map2_1 ;
                      try (left ; exists (comp_typ_true, fcomp_true) ;
                           apply CE.find_2, Hfind_ce_true).
                rewrite CE.map2_1 ;
                      try (left ; exists (comp_typ_false, fcomp_false) ;
                           apply CE.find_2, Hfind_ce_false).
                rewrite Hfind_ce_true Hfind_ce_false Hfind_ce_before
                        /ce_map_difference_helper
                        /ce_map_intersection_helper //.
              + left.
                exists (comp_typ_true, fcomp_true).
                apply CE.find_2.
                rewrite CE.map2_1 ;
                      try (left ; exists (comp_typ_true, fcomp_true) ;
                           apply CE.find_2, Hfind_ce_true).
                rewrite /ce_map_difference_helper Hfind_ce_before Hfind_ce_true //.
        rewrite Hfind_ce_false in H3.
        destruct (orient_of_comp fcomp_true == Source) eqn: Horient.
        * (* the orientation is Source, so it is in none of the cmaps. *)
          destruct comp_typ_true as [ft|reg|mem|] ; try done.
          + assert (exists t : fgtyp, ft = Gtyp t) by admit.
            destruct H4 as [t] ; rewrite H4.
            done.
          + (* register is similar to variable *)
            admit.
          + (* memory is similar to variable *)
            admit.
        * (* the orientation is <> Source *)
          destruct comp_typ_true as [ft|reg|mem|] ; try done.
          + assert (exists t : fgtyp, ft = Gtyp t) by admit.
            destruct H4 as [t] ; rewrite H4 ; rewrite H4 in IHss_true'.
            unfold expandBranch_one_component_sem_conform, ref2var ;
            unfold expandBranch_one_component_sem_conform, ref2var in IHss_true'.
            move /eqP : H1 => H1.
            assert (CE.find (nat_to_var (id * 3 + 1)) cm_previous = None) by admit.
                  (* This should be proven based on the preservation of correspondence and H1. *)
            assert (exists d : def_expr, CE.find (nat_to_var (id * 3 + 1)) cm_true_result = Some d).
                  destruct (CE.find (nat_to_var (id * 3 + 1)) cm_true_result) eqn: Hfind_cm_true.
                  - exists d ; reflexivity.
                  - rewrite eq_refl in H2 ; assert false by (apply H2 ; done) ; done.
            destruct H6 as [de_true].
            clear H2.
            move /eqP : H3 => H3.
            rewrite CE.map2_1.
            - rewrite H6 H3 H5.
              rewrite H1 in IHss_true'.
              unfold map2_helper_cs_tf.
              simpl expandBranch_one_var_sem.
              assert (expandBranch_one_var_sem ss (Eid id) T_undeclared = T_undeclared) by admit.
                    (* This should hold because the variable was not declared before the true branch.
                       I think that a slight change in IHss' should entail this. *)
              assert (expandBranch_one_var_sem ss_false (Eid id) T_undeclared = T_undeclared) by admit.
              rewrite H2 H7.
              rewrite H6 in IHss_true'.
              destruct de_true, (expandBranch_one_var_sem ss_true (Eid id) T_undeclared) ;
                    exact IHss_true'.
            - left.
              destruct (CE.find (nat_to_var (id * 3 + 1)) cm_true_result) eqn: Hfind_cm_true ; try done.
              exists d.
              apply CE.find_2 ; exact Hfind_cm_true.
          + (* register is similar to variable *)
            admit.
          + (* memory is similar to variable *)
            admit.
      destruct (CE.find (nat_to_var (id * 3 + 1)) ce_false_result) eqn: Hfind_ce_false.
      - (* id was declared in the false branch.
           Similar to the above (true branch). *)
        admit.
      - assert (~CE.In (nat_to_var (id * 3 + 1)) (CE.map2 combine_branches_ce_map2_helper ce_true_result
                                                  ce_false_result)).
              contradict IHss'.
              apply CE.map2_2 in IHss'.
              destruct IHss' ;
                    unfold CE.In in H4 ;
                    destruct H4 ;
                    apply CE.find_1 in H4.
              * rewrite H4 in Hfind_ce_true ; discriminate.
              * rewrite H4 in Hfind_ce_false ; discriminate.
        destruct (CE.find (nat_to_var (id * 3 + 1))
                      (CE.map2 combine_branches_ce_map2_helper ce_true_result
                       ce_false_result)) eqn: Hfind ;
              try rewrite Hfind //.
        absurd (CE.In (nat_to_var (id * 3 + 1))
              (CE.map2 combine_branches_ce_map2_helper ce_true_result
                       ce_false_result)) ; try done.
        apply CE.find_2 in Hfind.
        exists p ; exact Hfind.
* clear expandBranch_correct_Swhen.
  destruct s ; done.
Admitted.



