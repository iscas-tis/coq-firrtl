From Coq Require Import BinNat ZArith.
From mathcomp Require Import ssreflect ssrbool eqtype seq fintype.
From simplssrlib Require Import SsrOrder Var.
From firrtl Require Import Env Firrtl HiEnv HiFirrtl.

(* From Coq Require Import FunInd FMaps FMapAVL OrderedType ZArith.
From mathcomp Require Import ssrnat ssrint seq ssrfun.
From simplssrlib Require Import Types FSets FMaps Tactics Store.
From nbits Require Import NBits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits. *)

Include HiF.

(* DNJ: What follows is my proposal to create a unique lowered index from a (high-level) reference.
   I do not know whether this is compatible with ExpandConnects or LowerTypes. *)

Open Scope N_scope.

(* A bijection between pairs of natural numbers and natural numbers *)
Definition pair (x y : N) : N :=
   (x + y) * (x + y + 1) / 2 + x.

Definition proj1 (p : N) : N :=
   let x_plus_y := (N.sqrt (8 * p + 1) - 1) / 2 (* rounded down *) in
   p - (x_plus_y * (x_plus_y + 1) / 2).

Definition proj2 (p : N) : N :=
   let x_plus_y := (N.sqrt (8 * p + 1) - 1) / 2 (* rounded down *) in
   (* x_plus_y - (proj1 p), which simplifies to: *)
   x_plus_y * (x_plus_y + 3) / 2 - p.

(* pair and (proj1, proj2) are each other's inverse functions. *)
Lemma sqrt_spec : forall n: N, N.sqrt (n * n) = n.
Admitted. (* probably the proof can be based on something like
   forall p: positive, Pos.sqrtrem (p * p) = (p, IsNul). *)

Lemma proj1_pair : forall (x y : N), x = proj1 (pair x y).
Admitted.

Lemma proj2_pair : forall (y x : N), y = proj2 (pair x y).
Admitted.

Lemma pair_proj : forall p : N, p = pair (proj1 p) (proj2 p).
Admitted.

(* mapping from a href that is not a subaccess to an index in CE.env *)
Fixpoint ref2var (ref : href) : N :=
match ref with
| Eid v => v * 3 + 1
| Esubfield ref0 v => match ref2var ref0 with
                      | 0 => 0
                      | n => (pair n v) * 3 + 2
                      end
| Esubindex ref0 i => match ref2var ref0 with
                      | 0 => 0
                      | n => (pair n (N.of_nat i)) * 3 + 3
                      end
| Esubaccess _ _ => 0 (* cannot be translated actually *)
end.

(* mapping from an index in CE.env to a href. *)

Definition to_var (n : N) : VarOrder.T := n.

Fixpoint var2ref' (depth : nat) (n : N) : option href :=
   match depth, n with
   | 0%nat, _ | _, 0 => None
   | S d', _ => match n mod 3 with
                | 1 => Some (Eid (to_var ((n - 1) / 3)))
                | 2 => let p := (n - 2) / 3 in
                       match var2ref' d' (proj1 p) with
                       | None => None
                       | Some ref => Some (Esubfield ref (proj2 p))
                       end
                | _ => let p := (n - 3) / 3 in
                       match var2ref' d' (proj1 p) with
                       | None => None
                       | Some ref => Some (Esubindex ref (N.to_nat (proj2 p)))
                       end
                end
   end.

Definition var2ref (n : N) : option href := var2ref' (N.to_nat n) n.

Close Scope N_scope.

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
         (Qcat (fst true_branch) (fst false_branch),
          CE.map2 (map2_helper_cs_tf c) (snd true_branch) (snd false_branch))
   .

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

   Fixpoint init_register_vector (v : nat -> href) (array_size : nat) (type : ftype) : (nat -> cmap -> cmap) * nat :=
   (* Produces a function that initializes v to itself.
      Input:  * v = href of the variable that needs to be initialized
                    (possibly this is already an array, that's why it is a function from nat to href)
              * array_size = size of the array v (if it's not an array, array_size == 1)
              * type = type of (a single element of the array) v <number>
              * ce = component environment
      Output: * nat -> cmap -> cmap : a function that initializes one element of the array (by modifying a cmap accordingly)
              * nat : size of the array *)
   match type with
   | Gtyp _ => ((fun n : nat => CE.add (ref2var (v n)) (D_fexpr (Eref (v n)))), array_size)
   | Atyp el_type n => init_register_vector (fun m : nat => Esubindex (v (m / array_size)) (m mod array_size)) (array_size * n) el_type
   | Btyp ff => init_register_bundle v array_size ff
   end
   with init_register_bundle (v : nat -> href) (array_size : nat) (ff : ffield) : (nat -> cmap -> cmap) * nat :=
   match ff with
   | Fnil => ((fun (n : nat) (cm : cmap) => cm), 0)
   | Fflips field_name Nflip field_type ff_tail =>
        let init_field := init_register_vector (fun n : nat => Esubfield (v n) field_name) array_size field_type
        in let init_tail := init_register_bundle v array_size ff_tail
           in ((fun n : nat => if n <? snd init_field then fst init_field n
                                                      else fst init_tail (n - snd init_field)),
               snd init_field + snd init_tail)
   | Fflips _ Flipped _ _ => (* error: a register must have a passive type *) ((fun (n : nat) (cm : cmap) => empty_cmap), 0)
   end.

   Fixpoint init_apply_initializer (fn : nat -> cmap -> cmap) (array_size : nat) (cm : cmap) : cmap :=
   (* Applies initialization function fn, as produced by init_register_vector, to cm
      so as to initialize the array fn 0 ... fn (array_size - 1). *)
   match array_size with
   | 0 => cm
   | S m => init_apply_initializer fn m (fn m cm)
   end.

   Definition init_register (id : VarOrder.T) (type : ftype) (cm : cmap) : cmap :=
   (* Initializes the register id, which is of type type. *)
   let initializer := init_register_vector (fun n : nat => Eid id) 1 type
   in init_apply_initializer (fst initializer) (snd initializer) cm.

   (* Identifiers for the fields of a memory port *)
   Parameter mem_port_addr : VarOrder.T.
   Parameter mem_port_en : VarOrder.T.
   Parameter mem_port_clk : VarOrder.T.
   Parameter mem_port_data : VarOrder.T.
   Parameter mem_port_mask : VarOrder.T.

   Fixpoint init_memory_reader (id : VarOrder.T) (reader : seq VarOrder.T) (cm : cmap) : cmap :=
   (* Helper function for init_memory. It initializes the read ports that are indicated in reader. *)
   match reader with
   | [::] => cm
   | r :: rtail => init_memory_reader id rtail
                   (CE.add (ref2var (Esubfield (Esubfield (Eid id) r) mem_port_addr)) D_undefined
                      (CE.add (ref2var (Esubfield (Esubfield (Eid id) r) mem_port_en)) D_undefined
                         (CE.add (ref2var (Esubfield (Esubfield (Eid id) r) mem_port_clk)) D_undefined
                            cm
                         )
                      )
                   )
   end.

   Fixpoint init_undefined_vector (v : nat -> href) (array_size : nat) (type : ftype) (value : def_expr) : (nat -> cmap -> cmap) * nat :=
   (* Produces a function that initializes v to value (mostly D_undefined or D_invalidated).
      It can be used to initialize memory write ports (data and mask fields) and wires.
      Memory ports have to be passive, but wires allow flipped fields,
      so it does not check whether the type is passive.
      Input:  * v = href of the variable that needs to be initialized (possibly this is already an array)
              * array_size = size of the array v (if it's not an array, array_size == 1)
              * type = type of v <number>
      Output: * nat -> cmap -> cmap : a function that initializes one element of the array (by modifying a cmap accordingly)
              * nat : size of the array *)
   match type with
   | Gtyp _ => ((fun n : nat => CE.add (ref2var (v n)) value), array_size)
   | Atyp el_type n => init_undefined_vector (fun m : nat => Esubindex (v (m / array_size)) (m mod array_size)) (array_size * n) el_type value
   | Btyp ff => init_undefined_bundle v array_size ff value
   end
   with init_undefined_bundle (v : nat -> href) (array_size : nat) (ff : ffield) (value : def_expr) : (nat -> cmap -> cmap) * nat :=
   match ff with
   | Fnil => ((fun (n : nat) (cm : cmap) => cm), 0)
   | Fflips field_name fflip field_type ff_tail =>
        let init_field := match fflip with Nflip => init_undefined_vector  (fun n : nat => Esubfield (v n) field_name) array_size field_type value
                                       | Flipped => init_undefined_flipped (fun n : nat => Esubfield (v n) field_name) array_size field_type value
                          end
        in let init_tail := init_undefined_bundle v array_size ff_tail value
           in ((fun n : nat => if n <? snd init_field then fst init_field n
                                                      else fst init_tail (n - snd init_field)),
               snd init_field + snd init_tail)
   end
   with init_undefined_flipped (v : nat -> href) (array_size : nat) (type : ftype) (value : def_expr) : (nat -> cmap -> cmap) * nat :=
   match type with
   | Gtyp _ => ((fun (n : nat) (cm: cmap) => cm), 0)
   | Atyp el_type n => init_undefined_flipped (fun m : nat => Esubindex (v (m / array_size)) (m mod array_size)) (array_size * n) el_type value
   | Btyp ff => init_undefined_flipped_bundle v array_size ff value
   end
   with init_undefined_flipped_bundle (v : nat -> href) (array_size : nat) (ff : ffield) (value : def_expr) : (nat -> cmap -> cmap) * nat :=
   match ff with
   | Fnil => ((fun (n : nat) (cm : cmap) => cm), 0)
   | Fflips field_name fflip field_type ff_tail =>
        let init_field := match fflip with Nflip => init_undefined_flipped (fun n : nat => Esubfield (v n) field_name) array_size field_type value
                                       | Flipped => init_undefined_vector  (fun n : nat => Esubfield (v n) field_name) array_size field_type value
                          end
        in let init_tail := init_undefined_flipped_bundle v array_size ff_tail value
           in ((fun n : nat => if n <? snd init_field then fst init_field n
                                                      else fst init_tail (n - snd init_field)),
               snd init_field + snd init_tail)
   end.

   Fixpoint init_memory_writer (id : VarOrder.T) (data_type : ftype) (writer : seq VarOrder.T) (cm : cmap) : cmap :=
   (* Helper function for init_memory. It initializes the write ports that are indicated in writer. *)
   match writer with
   | [::] => cm
   | w :: wtail => let initializer_data := init_undefined_vector (fun n : nat => (Esubfield (Esubfield (Eid id) w) mem_port_data)) 1 data_type D_undefined
                   in let initializer_mask := init_undefined_vector (fun n : nat => (Esubfield (Esubfield (Eid id) w) mem_port_mask)) 1 data_type D_undefined
                      in init_memory_writer id data_type wtail
                         (CE.add (ref2var (Esubfield (Esubfield (Eid id) w) mem_port_addr)) D_undefined
                            (CE.add (ref2var (Esubfield (Esubfield (Eid id) w) mem_port_en)) D_undefined
                               (CE.add (ref2var (Esubfield (Esubfield (Eid id) w) mem_port_clk)) D_undefined
                                  (init_apply_initializer (fst initializer_data) (snd initializer_data)
                                     (init_apply_initializer (fst initializer_mask) (snd initializer_mask) cm)
                                  )
                               )
                            )
                         )
   end.

   Fixpoint memport_ids (m : seq mem_port) : seq VarOrder.T :=
     match m with
     | [::] => [::]
     | pid :: pids => (id pid) :: (memport_ids pids)
     end.

   Definition init_memory (id : VarOrder.T) (m : hfmem) (cm : cmap) : cmap :=
   (* This helper function initializes a memory named v with description m.
      In particular, all reader and writer ports are declared undefined. *)
   init_memory_writer id (data_type m) (memport_ids (writer m)) (init_memory_reader id (memport_ids (reader m)) cm).

   Definition init_wire (id : VarOrder.T) (type : ftype) (cm : cmap) : cmap :=
   (* Initializes a wire named id with type type. *)
   let initializer := init_undefined_vector (fun n : nat => (Eid id)) 1 type D_undefined
   in init_apply_initializer (fst initializer) (snd initializer) cm.

(* Inductive error_type (T : Type) : Type :=
   | ECorrect : T -> error_type
   | Esyntax
   | Etype
   | Euninitialized (* a component should be connected but isn't *)
   | Einternal (* e.g. if a pass receives input that should have been handled by earlier passes *)
   | E...

   Definition init_wire (id : VarOrder.T) (type : ftype) (ce : CE.env) (cm : cmap) : error_type cmap :=
   (* Initializes a wire named id with type type. May return an error message. *)
   match init_undefined_vector (fun n : nat => (Eid id)) 1 type D_undefined ce with
   Some initializer => init_apply_initializer (fst initializer) (snd initializer) cm
   error => error
   end. *)

   Definition init_instance (id: VarOrder.T) (mdl: VarOrder.T) (ce : CE.env) (cm : cmap) : cmap :=
   (* This function should initialize the ports that connect the current module with module mdl under the name id,
      which is instantiated here.
      It is assumed that the type of the module is stored in ce already. *)
   let initializer := init_undefined_flipped (fun n : nat => Eid id) 1 (type_of_cmpnttyp (fst (CE.vtyp mdl ce))) D_undefined
   in init_apply_initializer (fst initializer) (snd initializer) cm.

   Definition invalidate_cmpnt (ref : href) (cm : cmap) : cmap :=
   (* Sets the component ref to invalid, to indicate that the programmer let it unconnected on purpose. *)
      CE.add (ref2var ref) D_invalidated cm.
   (*let initializer := init_undefined_vector (fun n : nat => ref) 1 (type_of_ref ref ce) D_invalidated ce in
   init_apply_initializer (fst initializer) (snd initializer) cm.*)

   Fixpoint expandBranch_fun (ss : hfstmt_seq) (ce : CE.env) (cm : cmap) : (hfstmt_seq * cmap) :=
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
   | Qnil => (qnil, cm)
   | Qcons s ss_tail => match s with
                        | @Sskip _ => expandBranch_fun ss_tail ce cm (* no translation needed *)
                        | @Swire _ id type => let result := expandBranch_fun ss_tail ce (init_wire id type cm)
                                              in (Qcons s (fst result), snd result)
                        | @Sreg _ id reg => let result := expandBranch_fun ss_tail ce (init_register id (type reg) cm)
                                            in (Qcons s (fst result), snd result)
                        | @Smem _ id mem => let result := expandBranch_fun ss_tail ce (init_memory id mem cm)
                                            in (Qcons s (fst result), snd result)
                        | @Sinst _ id mdl => let result := expandBranch_fun ss_tail ce (init_instance id mdl ce cm)
                                             in (Qcons s (fst result), snd result)
                        | @Snode _ _ _ => let result := expandBranch_fun ss_tail ce cm
                                          in (Qcons s (fst result), snd result)
                        | @Sfcnct _ ref expr => expandBranch_fun ss_tail ce (CE.add (ref2var ref) (D_fexpr expr) cm)
                        | @Spcnct _ _ _ => (* error: should have been expanded earlier *) (qnil, empty_cmap)
                        | @Sinvalid _ ref => expandBranch_fun ss_tail ce (invalidate_cmpnt ref cm)
                        | @Swhen _ cond ss_true ss_false => let combined_branches := combine_branches cond (expandBranch_fun ss_true  ce cm)
                                                                                                           (expandBranch_fun ss_false ce cm)
                                                            in let result := expandBranch_fun ss_tail ce (snd combined_branches)
                                                               in (Qcat (fst combined_branches) (fst result), snd result)
                        (* | @Sstop _ clk cond exit => let result := expandBranch_fun ss_tail ce cm simcond *)
                        (*                             in (Qcons (Sstop clk (option_and simcond cond) exit) (fst result), snd result) *)
                        end
   end.

   Fixpoint init_ports (ports : seq hfport) (cm : cmap) : cmap :=
   (* This helper function sets the ports of a module to undefined. *)
   match ports with
   | [::] => cm
   | Finput  id type :: ports_tail => let initializer := init_undefined_flipped (fun n : nat => Eid id) 1 type D_undefined
                                      in init_ports ports_tail (init_apply_initializer (fst initializer) (snd initializer) cm)
   | Foutput id type :: ports_tail => let initializer := init_undefined_vector  (fun n : nat => Eid id) 1 type D_undefined
                                      in init_ports ports_tail (init_apply_initializer (fst initializer) (snd initializer) cm)
   end.

   Definition recode_cmap_entry (id : VarOrder.T) (dexpr : def_expr) (ss : hfstmt_seq) : hfstmt_seq :=
   (* This helper function for recode_map translates one entry of the cmap into a statement
      that is added to the statement sequence ss. *)
   match dexpr with
   | D_undefined => ss (* the user has erroneously not connected to id *)
   | D_invalidated => match var2ref id with
                      | None => (* error *) qnil
                      | Some ref => Qcons (sinvalid ref) ss (* the user has given an "is invalid" statement. Copy it. *)
                      end
   | D_fexpr expr => match var2ref id with
                     | None => (* error *) qnil
                     | Some ref => Qcons (sfcnct ref expr) ss
                     end
   end.

   Definition recode_cmap (cm : cmap) : hfstmt_seq :=
   (* Translates the entries in cm to a sequence of statements (in a random order). *)
   CE.fold recode_cmap_entry cm qnil.

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

   Definition expandWhen_fun (mdl : hfmodule) (ce : CE.env) : hfmodule :=
   (* This function provides an interface to the main function.
      Input:  * mdl = module definition
                (its statements do not contain partial or aggregate connects;
                they may contain double connects and when statements)
              * ce = component environment, containing the input/output port declarations of all other modules
                (this has been found in earlier passes and is not updated)
      Output: translated statement sequence of the module *)
   match mdl with
   | FInmod id ports ss => let result := expandBranch_fun ss ce (init_ports ports empty_cmap)
                           in FInmod id ports (Qcat (fst result) (recode_cmap (snd result)))
   | FExmod _ _ _ => (* error: external modules cannot be handled for verification *) mdl
   end.

   (* Specification of the semantics.
      The semantics of when statements and last connect is:

      +------------------------------------------------------------------------+
      | For every (ground-type) sink element, ExpandWhens produces the connect |
      | (= Sfcnct or Sinvalid) that appears last on any execution path through |
      | the module.  If there are multiple execution paths where the component |
      | containing this sink element is declared, ExpandWhens seleects between |
      | them using a multiplexer or validif expression.                        |
      | (If there is some execution path where the sink element is declared    |
      | but is neither declared invalid [Sinvalid] not connected [Sfcnct], the |
      | program is erroneous; in that case, ExpandWhens does not produce any   |
      | connect for this sink element.)                                        |
      +------------------------------------------------------------------------+

      Example of an incorrect statement sequence and its translation:
         Wire a : UInt<16>    --->   Wire a : UInt<16>
         when c : a <= b             // no connect statement for a

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
   | Gtyp _ => let default_value := match CE.find (ref2var ref) default with
                                    | None => T_undeclared
                                    | Some D_undefined => T_undefined
                                    | Some D_invalidated => T_invalidated
                                    | Some (D_fexpr e) => T_fexpr e
                                    end
               in CE.find (ref2var ref) cm == expr_tree_to_def_expr (expandBranch_one_var_sem ss ref default_value)
   | Atyp t' array_size => [forall n: ordinal array_size, expandBranch_one_component_sem_conform (Esubindex ref n) t' ss cm default]
   | Btyp ff => expandBranch_one_component_sem_conform_fields ref ff ss cm default
   end
   with expandBranch_one_component_sem_conform_fields (ref : href) (ff : ffield) (ss : hfstmt_seq) (cm : cmap) (default : cmap) : bool :=
   match ff with
   | Fnil => true
   | Fflips f Nflip t' ff_tail =>    expandBranch_one_component_sem_conform (Esubfield ref f) t' ss cm default
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
   | Fflips f Nflip t' ff_tail =>    expandBranch_one_component_sem_conform_flipped (Esubfield ref f) t' ss cm default
                                  && expandBranch_one_component_sem_conform_flipped_fields ref ff_tail ss cm default
   | Fflips f Flipped t' ff_tail =>    expandBranch_one_component_sem_conform (Esubfield ref f) t' ss cm default
                                    && expandBranch_one_component_sem_conform_flipped_fields ref ff_tail ss cm default
   end.

   Definition memory_readport_type (t : ftype) (addr_size : nat) : ftype :=
   Btyp (Fflips mem_port_addr Nflip (Gtyp (Fuint addr_size))
        (Fflips mem_port_en Nflip (Gtyp (Fuint 1))
        (Fflips mem_port_clk Nflip (Gtyp Fclock)
        (Fflips mem_port_data Flipped t Fnil)))).

   Fixpoint mask_type (t : ftype) : ftype :=
   (* the type of the mask field of a write port of a memory with type t *)
   match t with
   | Gtyp _ => Gtyp (Fuint 1)
   | Atyp t n => Atyp (mask_type t) n
   | Btyp ff => Btyp (mask_type_fields ff)
   end
   with mask_type_fields (ff : ffield) : ffield :=
   match ff with
   | Fnil => Fnil
   | Fflips fieldname Nflip t ff_tail => Fflips fieldname Nflip (mask_type t) (mask_type_fields ff_tail)
   | Fflips fieldname Flipped t ff_tail => Fnil (* error *)
   end.

   Definition memory_writeport_type (t : ftype) (addr_size : nat) : ftype :=
   Btyp (Fflips mem_port_addr Nflip (Gtyp (Fuint addr_size))
        (Fflips mem_port_en Nflip (Gtyp (Fuint 1))
        (Fflips mem_port_clk Nflip (Gtyp Fclock)
        (Fflips mem_port_data Nflip t
        (Fflips mem_port_mask Nflip (mask_type t) Fnil))))).

   Fixpoint expandBranch_readports_sem_conform (m_id : VarOrder.t) (addr_size : nat) (readports : seq mem_port) (t : ftype)
                                               (ss : hfstmt_seq) (cm : cmap) (default : cmap) : bool :=
   match readports with
   | [::] => true
   | rp :: readports_tail =>    expandBranch_one_component_sem_conform (Esubfield (Eid m_id) (id rp))
                                                  (memory_readport_type t addr_size) ss cm default
                             && expandBranch_readports_sem_conform m_id addr_size readports_tail t ss cm default
   end.

   Fixpoint expandBranch_writeports_sem_conform (m_id : VarOrder.t) (addr_size : nat) (writeports : seq mem_port) (t : ftype)
                                               (ss : hfstmt_seq) (cm : cmap) (default : cmap) : bool :=
   match writeports with
   | [::] => true
   | wp :: writeports_tail =>    expandBranch_one_component_sem_conform (Esubfield (Eid m_id) (id wp))
                                                   (memory_writeport_type t addr_size) ss cm default
                              && expandBranch_writeports_sem_conform m_id addr_size writeports_tail t ss cm default
   end.

   Definition expandBranch_memory_sem_conform (id : var) (m : hfmem) (ss : hfstmt_seq) (cm : cmap) (default : cmap) : bool :=
   (* This adapter function calls the appropriate variants of expandBranch_one_component_sem_conform
      for memory defined by id. It basically goes through all ports and checks their interfaces. *)
   let addr_size := if depth m <=? 1 then 0 else Nat.log2 (depth m - 1) + 1
   in    expandBranch_readports_sem_conform  id addr_size (reader m) (data_type m) ss cm default
      && expandBranch_writeports_sem_conform id addr_size (writer m) (data_type m) ss cm default
   .

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
          | (Mem_typ m, Memory) => expandBranch_memory_sem_conform id m ss cm default
          | _ => false (* error *)
          end.

   Fixpoint expandWhen_precondition_ss (ss : hfstmt_seq) (ce : CE.env) : bool :=
   (* Precondition of expandWhen: there are no partial connects, all instance statements refer to defined modules.
      Also: all references are to declared variables.
      * ss = statement sequence that is tested whether it satisfies the precondition
      * ce = component environment containing (at least) type descriptions of all instantiated modules
      Result: true iff the precondition is satisfied. *)
   match ss with
   | Qnil => true
   | Qcons s tl => match s with
                   | Spcnct _ _ => false
                   | Sinst id def => if CE.find def ce is Some (_, Fmodule) then expandWhen_precondition_ss tl ce else false
                   | Swhen _ sst ssf =>    expandWhen_precondition_ss sst ce
                                        && expandWhen_precondition_ss ssf ce
                                        && expandWhen_precondition_ss tl ce
                   | _ => expandWhen_precondition_ss tl ce
                   end
   end.

   Fixpoint expandWhen_ce (ss : hfstmt_seq) (ce : CE.env) (default : CE.env) : CE.env :=
   (* The result contains exactly the component types as defined by ss, in addition to default.
      The parameter ce contains the port declarations of other modules. *)
   match ss with
   | Qnil => default
   | Qcons s ss_tail => match s with
                        | Swire id t => expandWhen_ce ss_tail ce (CE.add id (@Aggr_typ VarOrder.T t, Wire) default)
                        | Sreg id reg => expandWhen_ce ss_tail ce (CE.add id (Reg_typ reg, Register) default)
                        | Smem id mem => expandWhen_ce ss_tail ce (CE.add id (Mem_typ mem, Memory) default)
                        | Sinst id typ => expandWhen_ce ss_tail ce (CE.add id (fst (CE.vtyp typ ce), Instanceof) default)
                        | Sskip
                        | Snode _ _ (* can be ignored *)
                        | Sfcnct _ _
                        | Sinvalid _ => expandWhen_ce ss_tail ce default
                        | Swhen _ ss_true ss_false => expandWhen_ce ss_tail ce (expandWhen_ce ss_false ce (expandWhen_ce ss_true ce default))
                        (* | Sstop _ _ _ => expandWhen_ce ss_tail default *)
                        | Spcnct _ _ (* error: should not appear *) => CE.empty (cmpnt_init_typs * fcomponent)
                        end
   end.

   Definition expandBranch_sem_conform (mdl : hfmodule) (ce : CE.env) : bool :=
   (* Checks for all components declared in module mdl
      whether expandBranch_fun satisfies the specification.
      * mdl = module to be checked
      * ce = component environment containing all port declarations of other modules *)
   match mdl with
   | FInmod _ ports ss => expandWhen_precondition_ss ss ce ==>
                          let ports_cmap := init_ports ports empty_cmap
                          in CE.fold (expandBranch_sem_conform_helper ss (snd (expandBranch_fun ss ce ports_cmap)) ports_cmap)
                                     (expandWhen_ce ss ce (CE.empty (cmpnt_init_typs * fcomponent))) true
   | FExmod _ _ _ => false (* error *)
   end.

(* How to prove the correctness of this semantics?
   Basically, we would like to show that for every correct (hfmodule * CE.env) pair,
   we have that expandBranch_sem_conform returns true.
   Preconditions are, in addition to expandWhen

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
