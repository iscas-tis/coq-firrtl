From Coq Require Import FunInd FMaps FMapAVL OrderedType ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat ssrint eqtype seq ssrfun.
From simplssrlib Require Import Types SsrOrder FSets FMaps Tactics Var Store.
From nbits Require Import NBits.
From firrtl Require Import Firrtl Env HiEnv.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* Delimit Scope hifirrtl with hifirrtl. *)

Section HiFirrtl.


  (****** Syntax ******)

  (****** Expressions ******)

  Variable var : eqType.

  Inductive sign := Unsigned | Signed.

  Inductive hfexpr : Type :=
  | Econst : fgtyp -> bits -> hfexpr
  | Ecast : ucast -> hfexpr -> hfexpr
  | Eprim_unop : eunop -> hfexpr -> hfexpr
  | Eprim_binop : ebinop -> hfexpr -> hfexpr -> hfexpr
  | Emux : hfexpr -> hfexpr -> hfexpr -> hfexpr
  | Evalidif : hfexpr -> hfexpr -> hfexpr
  | Eref : href -> hfexpr
  with href : Type :=
  | Eid : var -> href
  | Esubfield : href -> var -> href (* HiFirrtl *)
  | Esubindex : href -> nat -> href (* HiFirrtl *)
  | Esubaccess : href -> hfexpr -> href (* HiFirrtl *)
  .

  (** equality of hfexpr and href are decidable *)
  Axiom hfexpr_eq_dec : forall {x y : hfexpr}, {x = y} + {x <> y}.
  Parameter hfexpr_eqn : forall (x y : hfexpr), bool.
  Axiom hfexpr_eqP : Equality.axiom hfexpr_eqn.
  Canonical hfexpr_eqMixin := EqMixin hfexpr_eqP.
  Canonical hfexpr_eqType := Eval hnf in EqType hfexpr hfexpr_eqMixin.

  Axiom href_eq_dec : forall {x y : href}, {x = y} + {x <> y}.
  Parameter href_eqn : forall (x y : href), bool.
  Axiom href_eqP : Equality.axiom href_eqn.
  Canonical href_eqMixin := EqMixin href_eqP.
  Canonical href_eqType := Eval hnf in EqType href href_eqMixin.

  (****** Statements ******)

  Record mem_port : Type :=
    mk_mem_port
      {
        id : var;
        addr : var;
        en : var;
        clk : var
      }.
  
  Record hfmem : Type :=
    mk_fmem
      {
        data_type : ftype;
        depth : nat;
        reader : seq mem_port;
        writer : seq mem_port;
        read_latency : nat;
        write_latency : nat;
        read_write : ruw
      }.

  Inductive rst : Type :=
  | NRst : rst
  | Rst : hfexpr -> hfexpr -> rst.

  Record hfreg : Type :=
    mk_freg
      {
        (* rid : var; *)
        type : ftype;
        clock : hfexpr;
        reset : rst
      }.

  Inductive hfstmt : Type :=
  | Sskip
  | Swire : var -> ftype -> hfstmt
  | Sreg : var -> hfreg -> hfstmt
  | Smem : var -> hfmem -> hfstmt
  | Sinst : var -> var -> hfstmt
  | Snode : var -> hfexpr -> hfstmt
  | Sfcnct : href -> hfexpr -> hfstmt
  | Spcnct : href -> hfexpr -> hfstmt
  | Sinvalid : href -> hfstmt
  (* | Sattach : seq var -> fstmt *)
  | Swhen : hfexpr -> hfstmt_seq -> hfstmt_seq -> hfstmt
  (* | Sstop : hfexpr -> hfexpr -> nat -> hfstmt *)
  (* | Sprintf (* TBD *) *)
  (* | Sassert (* TBD *) *)
  (* | Sassume (* TBD *) *)
  (* | Sdefname : var -> fstmt *) (* TBD *)
  (* | Sparam : var -> fexpr -> fstmt *) (* TBD *)
  with hfstmt_seq : Type :=
       | Qnil
       | Qcons : hfstmt -> hfstmt_seq -> hfstmt_seq.

   Scheme hfstmt_seq_hfstmt_ind := Induction for hfstmt_seq Sort Prop
   with hfstmt_hfstmt_seq_ind := Induction for hfstmt Sort Prop.

   Fixpoint Qhead (default : hfstmt) (s : hfstmt_seq) : hfstmt :=
   match s with Qnil => default
              | Qcons h tl => h end.

   Fixpoint Qcat (s1 s2 : hfstmt_seq) : hfstmt_seq :=
   match s1 with Qnil => s2
               | Qcons h1 tl1 => Qcons h1 (Qcat tl1 s2) end.

(* Fixpoint Qcatrev (s1 s2 : hfstmt_seq) : hfstmt_seq := (* calculates the reversal of s1, followed by s2 *)
   match s1 with Qnil => s2
               | Qcons h1 tl1 => Qcatrev tl1 (Qcons h1 s2) end.

   Definition Qrev (s : hfstmt_seq) : hfstmt_seq := Qcatrev s Qnil.

   Fixpoint Qfoldl {R : Type} (f : R -> hfstmt -> R) (s : hfstmt_seq) (default : R) :=
   match s with Qnil => default
              | Qcons h tl => Qfoldl f tl (f default h) end.
   Fixpoint Qfoldr {R : Type} (f : hfstmt -> R -> R) (default : R) (s : hfstmt_seq) :=
   match s with Qnil => default
              | Qcons h tl => f h (Qfoldr f default tl) end. *)

  Inductive hfport : Type :=
  | Finput : var -> ftype -> hfport
  | Foutput : var -> ftype -> hfport
  .

  Inductive hfmodule : Type :=
  | FInmod : var -> seq hfport -> hfstmt_seq -> hfmodule
  | FExmod : var -> seq hfport -> hfstmt_seq -> hfmodule
(* DNJ: External modules do not contain statements but only an interface.
They may contain the following special statements:
one “defname = ...” (to set the Verilog name)
zero, one, or multiple “parameter <variable> = <constant> (to pass parameters to the Verilog design that implements this module)
XM : TO BE DESIGNED , how to present the parameters
Discussion result: Because we concentrate on correctness,
and external modules are black boxes whose behaviour is unknown,
it does not make sense to put effort in external modules.
*)
  .

  Inductive hfcircuit : Type := Fcircuit : var -> seq hfmodule -> hfcircuit.

End HiFirrtl.

Section Component_types.
  (* A mapping from a variable to its component type.
  This mapping is needed because a register or memory definition
  contains more information than just the data type. *)
  Variable var : eqType.

  Inductive cmpnt_init_typs : Type :=
  | Aggr_typ : ftype -> cmpnt_init_typs
  | Reg_typ : hfreg var -> cmpnt_init_typs
  | Mem_typ : hfmem var -> cmpnt_init_typs
  (* | Inst_typ : ftype -> seq var -> cmpnt_init_typs *)
  | Unknown_typ : cmpnt_init_typs.

  (* data type of component *)
  Definition type_of_cmpnttyp ct :=
    match ct with
    | Aggr_typ t => t
    | Reg_typ r => type r
    | Mem_typ m => data_type m
    | Unknown_typ => Gtyp (Fuint 0)
    end.

End Component_types.

Module Type CmpntEnv (V : SsrOrder) <: SsrFMap.
  (* a module interface to store components in the form a map from (defined) identifiers
  to their data types (e.g. ``UInt<3>'') and kind (e.g. ``node''). *)
  Include SsrFMap.

  Local Notation var := V.t.
  Local Notation cmpnttyp := (cmpnt_init_typs V.T).
  Definition env : Type := t (cmpnttyp * fcomponent).
  (* The default type of a variable not in the typing environment *)
  Parameter deftyp : cmpnttyp * fcomponent.
  (* Find the type of a variable in a typing environment.
     If a variable is not in the typing environment, return the default type. *)
  Parameter vtyp : SE.t -> env -> (cmpnttyp * fcomponent).
  Axiom find_some_vtyp :
    forall {x : SE.t} {ty :cmpnttyp * fcomponent} {e : env}, find x e = Some ty -> vtyp x e = ty.
  Axiom find_none_vtyp :
    forall {x : SE.t} {e : env}, find x e = None -> vtyp x e = deftyp.
  (* Axiom vtyp_find : *)
  (*   forall {x : SE.t} {ty : cmpnt_init_typs V.T * fcomponent} {e : env}, *)
  (*     (vtyp x e == ty) = (find x e == Some ty) || ((find x e == None) && (ty == deftyp)). *)
  Axiom vtyp_add_eq :
    forall {x y : SE.t} {ty : cmpnt_init_typs V.T * fcomponent} {e : env}, x == y -> vtyp x (add y ty e) = ty.
  Axiom vtyp_add_neq :
    forall {x y : SE.t} {ty : cmpnt_init_typs V.T * fcomponent} {e : env},
      x != y -> vtyp x (add y ty e) = vtyp x e.
  Axiom not_mem_vtyp :
    forall {v : SE.t} {e : env}, ~~ mem v e -> vtyp v e = deftyp. (* mem = member of the SsrFMap *)

  (*Parameter Add : SE.t -> (cmpnttyp * fcomponent) -> env -> env -> Prop.
  Parameter Add_add : forall v f e, Add v f e (add v f e).*)

  (* Return the env with a variable v, where the fst element of type is given *)
  Parameter add_fst : SE.t -> cmpnttyp -> env -> env.
  Parameter Add_fst : SE.t -> cmpnttyp -> env -> env -> Prop.
  Parameter Add_add_fst : forall v f e, Add_fst v f e (add_fst v f e).

  (* Return the env with a variable v, where the snd element of type is given *)
  Parameter add_snd : SE.t -> fcomponent -> env -> env.
  Parameter Add_snd : SE.t -> fcomponent -> env -> env -> Prop.

End CmpntEnv.

Module MakeCmpntEnv (V : SsrOrder) (VM : SsrFMap with Module SE := V) <:
  CmpntEnv V with Module SE := V.
  (* concretisation of the above module interface
  (in particular, defines vtyp) *)
  Include VM.
  Module Lemmas := FMapLemmas VM.
  Local Notation cmpnttyp := (cmpnt_init_typs V.T).
  (* Definition aggr_typ ty := @Aggr_typ V.T ty. *)
  (* Definition reg_typ ty := @Reg_typ V.T ty. *)
  (* Definition mem_typ ty := @Mem_typ V.T ty. *)
  Definition env : Type := t (cmpnttyp * fcomponent).

  (* The default type of a variable not in the typing environment *)
  Definition deftyp := (Unknown_typ V.T, Node).

  (* Find the type of a variable in a typing environment.
     If a variable is not in the typing environment, return the default type. *)
  Definition vtyp (v : V.t) (e : env) : cmpnttyp * fcomponent :=
    match VM.find v e with
    | None => deftyp
    | Some ty => ty
    end.

  Lemma find_some_vtyp {x ty e} : find x e = Some ty -> vtyp x e = ty.
  Proof. move=> H. rewrite /vtyp H. reflexivity. Qed.

  Lemma find_none_vtyp {x e} : find x e = None -> vtyp x e = deftyp.
  Proof. move=> H. rewrite /vtyp H. reflexivity. Qed.

  Lemma vtyp_add_eq {x y ty e} : x == y -> vtyp x (add y ty e) = ty.
  Proof. rewrite /vtyp /add => H. by rewrite (Lemmas.find_add_eq H). Qed.

  Lemma vtyp_add_neq {x y ty e} : x != y -> vtyp x (add y ty e) = vtyp x e.
  Proof.
    move/negP=> Hxy. rewrite /vtyp /add. by rewrite (Lemmas.find_add_neq Hxy).
  Qed.

  Lemma not_mem_vtyp v e : ~~ mem v e -> vtyp v e = deftyp.
  Proof. rewrite /vtyp => H. by rewrite Lemmas.not_mem_find_none. Qed.

  (*Definition Add x c e e' := forall y, vtyp y e' = vtyp y (add x c e).
  Lemma Add_add : forall v f e, Add v f e (add v f e).
  Proof. done. Qed.*)

  Definition add_fst (v : V.t) (c : cmpnttyp) (e : env) : env :=
    let (f, s) := vtyp v e in add v (c, s) e.
  Definition add_snd (v : V.t) (fc : fcomponent) (e : env) : env :=
    let (f, s) := vtyp v e in add v (f, fc) e.
  Definition Add_fst x c e e' := forall y, fst (vtyp y e') = fst (vtyp y (add_fst x c e)).
  Lemma Add_add_fst {v c e} : Add_fst v c e (add_fst v c e).
  Proof. done. Qed.
  Definition Add_snd x c e e' := forall y, snd (vtyp y e') = snd (vtyp y (add_snd x c e)).
  Lemma Add_add_snd {v c e} : Add_snd v c e (add_snd v c e).
  Proof. done. Qed.

End MakeCmpntEnv.

Module CE (*<: CmpntEnv VarOrder *) := MakeCmpntEnv VarOrder VM.

(* rhs expressions *)
Section Rhs_expr.
  Variable v : eqType.
  Inductive rhs_expr : Type :=
  | R_fexpr : hfexpr v -> rhs_expr
  | R_default
  .


  (** eq dec *)
  Lemma rhs_expr_eq_dec : forall {x y : rhs_expr}, {x = y} + {x <> y}.
  Proof. induction x, y ; try (right ; discriminate) ; try (left ; reflexivity).
  case Eq: (h == h0).
  all: move /hfexpr_eqP : Eq => Eq.
  left ; replace h0 with h ; reflexivity.
  right ; injection ; apply Eq.
  Qed.

  Definition rhs_expr_eqn (x y : rhs_expr) : bool :=
  match x, y with R_fexpr e1, R_fexpr e2 => e1 == e2 | R_default, R_default => true | _, _ => false end.

  Lemma rhs_expr_eqP : Equality.axiom rhs_expr_eqn.
  Proof. unfold Equality.axiom, rhs_expr_eqn.
  induction x, y ; try (apply ReflectF ; discriminate) ; try (apply ReflectT ; reflexivity).
  case Eq: (h == h0).
  all: move /hfexpr_eqP : Eq => Eq.
  apply ReflectT ; replace h0 with h ; reflexivity.
  apply ReflectF ; injection ; apply Eq.
  Qed.

  Canonical rhs_expr_eqMixin := EqMixin rhs_expr_eqP.
  Canonical rhs_expr_eqType := Eval hnf in EqType rhs_expr rhs_expr_eqMixin.

End Rhs_expr.

Module Type StructStore (V : SsrOrder) (CE : CmpntEnv V with Module SE := V).
  (* extension of the component environment above
  with functions (and lemmas) to define additional variables *)

  Module Lemmas := FMapLemmas CE.

  Local Notation var := V.t.
  Local Notation value := (rhs_expr V.T).

  Parameter t : Type.
  Parameter empty : t.
  Parameter find : var -> t -> option value.
  Parameter map2 : (option value -> option value -> option value) -> t -> t -> t.
  Parameter acc : var -> t -> value.
  Parameter upd : var -> value -> t -> t.
  Parameter upd2 : var -> value -> var -> value -> t -> t.
  Parameter acc_upd_eq : forall {x y v s}, x == y -> acc x (upd y v s) = v.
  Parameter find_upd_eq : forall {x y v s}, x == y -> find x (upd y v s) = Some v.
  Parameter acc_upd_neq : forall {x y v s}, x != y -> acc x (upd y v s) = acc x s.
  Parameter find_upd_neq : forall {x y v s}, x != y -> find x (upd y v s) = find x s.
  Parameter acc_upd2_eq1 :
    forall {x y1 v1 y2 v2 s},
      x == y1 -> x != y2 -> acc x (upd2 y1 v1 y2 v2 s) = v1.
  Parameter acc_upd2_eq2 :
    forall {x y1 v1 y2 v2 s},
      x == y2 -> acc x (upd2 y1 v1 y2 v2 s) = v2.
  Parameter acc_upd2_neq :
    forall {x y1 v1 y2 v2 s},
      x != y1 -> x != y2 -> acc x (upd2 y1 v1 y2 v2 s) = acc x s.
  Parameter map2_eq : forall (m m': t)
        (x:var)(f:option value->option value->option value),
        f None None == None ->
        find x (map2 f m m') = f (find x m) (find x m').
  Parameter Upd : var -> value -> t -> t -> Prop.
  Definition Upd2 x1 v1 x2 v2 (s1 s2 : t) : Prop :=
    forall y, acc y s2 = acc y (upd x2 v2 (upd x1 v1 s1)).
  Parameter Equal : t -> t -> Prop.
  Parameter Upd_upd : forall x v s, Upd x v s (upd x v s).
  Parameter Upd2_upd :
    forall x1 v1 x2 v2 s, Upd2 x1 v1 x2 v2 s (upd x2 v2 (upd x1 v1 s)).
  Parameter Upd2_upd2 : forall x1 v1 x2 v2 s, Upd2 x1 v1 x2 v2 s (upd2 x1 v1 x2 v2 s).
  Parameter acc_Upd_eq : forall x y v s1 s2, x == y -> Upd y v s1 s2 -> acc x s2 = v.
  Parameter acc_Upd_neq :
    forall x y v s1 s2, x != y -> Upd y v s1 s2 -> acc x s2 = acc x s1.
  Parameter acc_Upd2_eq1 :
    forall x y1 v1 y2 v2 s1 s2,
      x == y1 -> x != y2 -> Upd2 y1 v1 y2 v2 s1 s2 -> acc x s2 = v1.
  Parameter acc_Upd2_eq2 :
    forall x y1 v1 y2 v2 s1 s2, x == y2 -> Upd2 y1 v1 y2 v2 s1 s2 -> acc x s2 = v2.
  Parameter acc_Upd2_neq :
    forall x y1 v1 y2 v2 s1 s2,
      x != y1 -> x != y2 -> Upd2 y1 v1 y2 v2 s1 s2 -> acc x s2 = acc x s1.
  Parameter Equal_def :
    forall s1 s2,
      Equal s1 s2 <-> (forall v, acc v s1 = acc v s2).
  Parameter Equal_refl : forall s, Equal s s.
  Parameter Equal_sym : forall s1 s2, Equal s1 s2 -> Equal s2 s1.
  Parameter Equal_trans : forall s1 s2 s3, Equal s1 s2 -> Equal s2 s3 -> Equal s1 s3.
  Parameter Equal_ST : RelationClasses.Equivalence Equal.
  Parameter Equal_upd_Equal :
    forall v e s1 s2, Equal s1 s2 -> Equal (upd v e s1) (upd v e s2).
  Parameter Equal_Upd_Equal :
    forall v e s1 s2 s3 s4,
      Upd v e s1 s2 -> Upd v e s3 s4 -> Equal s1 s3 -> Equal s2 s4.
  Parameter Upd_pred_Equal :
    forall v e s1 s2 s, Upd v e s1 s2 -> Equal s1 s -> Upd v e s s2.
  Parameter Upd_succ_Equal :
    forall v e s1 s2 s, Upd v e s1 s2 -> Equal s2 s -> Upd v e s1 s.
End StructStore.

Module StructType (V:SsrOrder)<: HasDefaultTyp.
  Definition t : Type := rhs_expr V.T.
  Definition default : t := R_default V.T.

End StructType.

Module MakeStructStore (V : SsrOrder) (CE : CmpntEnv V with Module SE := V) <:
  StructStore V CE.
  Module StructTypeV := StructType V.
  Include MakeTStoreMap V StructTypeV.
  Module Lemmas := FMapLemmas CE.
  Definition map2 (f : option (rhs_expr V.T) -> option (rhs_expr V.T) -> option (rhs_expr V.T)) (s1 s2 : t) : t :=
    M.map2 f s1 s2.
  Definition find (v: V.t) (s : t) := M.find v s.
  Module Lemmas_M := FMapLemmas M.
  Lemma find_upd_eq : forall {x y v s}, x == y -> find x (upd y v s) = Some v.
  Proof.
  intros.
  unfold upd.
  apply Lemmas_M.find_add_eq.
  exact H.
  Qed.
  Lemma find_upd_neq : forall {x y v s}, x != y -> find x (upd y v s) = find x s.
  Proof.
  intros.
  unfold upd.
  apply Lemmas_M.find_add_neq.
  move/eqP.
  move/eqP: H.
  contradiction.
  Qed.
  Lemma map2_eq : forall (m m': t)
        (x:V.t)(f:option (rhs_expr V.T)->option (rhs_expr V.T)->option (rhs_expr V.T)),
        f None None == None ->
        find x (map2 f m m') = f (find x m) (find x m').
  Proof.
  intros.
  induction (find x m) eqn: Hxm.
  replace (Some a) with (find x m).
  apply M.map2_1.
  left.
  unfold M.In, M.Raw.In0.
  exists a.
  apply M.find_2.
  exact Hxm.
  induction (find x m') eqn: Hxm'.
  replace (None) with (find x m).
  replace (Some a) with (find x m').
  apply M.map2_1.
  right.
  unfold M.In, M.Raw.In0.
  exists a.
  apply M.find_2.
  exact Hxm'.
  induction (f None None) eqn: Hfnn.
  contradict H.
  move /eqP.
  discriminate.
  induction (find x (map2 f m m')) eqn: Hfm.
  assert (M.In x m \/ M.In x m').
  apply M.map2_2 with (f := f).
  unfold M.In, M.Raw.In0.
  exists a.
  apply M.find_2.
  exact Hfm.
  destruct H0.
  assert (~M.In x m).
  unfold M.In, M.Raw.In0.
  contradict Hxm.
  destruct Hxm.
  replace (find x m) with (Some x0).
  discriminate.
  symmetry.
  apply M.find_1.
  exact H1.
  contradiction.
  assert (~M.In x m').
  unfold M.In, M.Raw.In0.
  contradict Hxm'.
  destruct Hxm'.
  replace (find x m') with (Some x0).
  discriminate.
  symmetry.
  apply M.find_1.
  exact H1.
  contradiction.
  reflexivity.
  Qed.
End MakeStructStore.

Module StructState := MakeStructStore VarOrder CE.

Module MakeHiFirrtl
       (V : SsrOrder) (* identifier names *)
       (VS : SsrFSet with Module SE := V)
       (VM : SsrFMap with Module SE := V)
       (CE : CmpntEnv V with Module SE := V)
       (SV : StructStore V CE). (* map from names of defined identifiers to their type and kind *)

  (* Local Open Scope hifirrtl. *)

  Module CELemmas := FMapLemmas CE.
  Module VSLemmas := SsrFSetLemmas VS.

  Local Notation var := V.t.

  Local Notation cstate := SV.t.
  Local Notation cenv := @CE.env.

  Definition econst s c := @Econst V.T s c.
  Definition ecast u e := @Ecast V.T u e.
  Definition eprim_unop u e := @Eprim_unop V.T u e.
  Definition eprim_binop b e1 e2 := @Eprim_binop V.T b e1 e2.
  Definition emux c e1 e2 := @Emux V.T c e1 e2.
  Definition evalidif c e := @Evalidif V.T c e.
  Definition hfexpr := hfexpr V.T.
  Definition eref r := @Eref V.T r.
  Definition eid v := @Eid V.T v.
  Definition esubfield r v := @Esubfield V.T r v.
  Definition esubindex r n := @Esubindex V.T r n.
  Definition esubaccess r e := @Esubaccess V.T r e.
  Definition href := href V.T.

  Definition hfstmt := hfstmt V.T.
  Definition hfstmt_seq := hfstmt_seq V.T.
  Definition qnil := Qnil V.T.
(*Definition qcons s ss := @Qcons V.T s ss.*)
  Definition sskip := @Sskip V.T.
  Definition swire v t := @Swire V.T v t.
  Definition sreg v r := @Sreg V.T v r.
  Definition smem v m := @Smem V.T v m.
  Definition snode v e := @Snode V.T v e.
  Definition sfcnct v1 v2 := @Sfcnct V.T v1 v2.
  Definition spcnct v1 v2 := @Spcnct V.T v1 v2.
  Definition sinvalid v1 := @Sinvalid V.T v1.
  Definition swhen c s1 s2 := @Swhen V.T c s1 s2.
  (* Definition sstop e1 e2 n := @Sstop V.T e1 e2 n. *)
  Definition sinst v1 v2 := @Sinst V.T v1 v2.

  Definition hfreg := @hfreg V.T.
  Definition mk_hfreg := @mk_freg V.T.
  Definition nrst := @NRst V.T.
  Definition rrst e1 e2 := @Rst V.T e1 e2.
  Definition mk_mem_port := @mk_mem_port V.T.
  Definition mem_port := @mem_port V.T.
  Definition hfmem := @hfmem V.T.
  Definition mk_hfmem := @mk_fmem V.T.
  Definition hfport := @hfport V.T.
  Definition hinport v t := @Finput V.T v t.
  Definition houtport v t := @Foutput V.T v t.
  Definition hfmodule := @hfmodule V.T.
  Definition hfinmod v ps ss := @FInmod V.T v ps ss.
  Definition hfexmod v ps ss := @FExmod V.T v ps ss.
  Definition hfcircuit := @hfcircuit V.T.

  Definition rhs_expr := rhs_expr V.T.
  Definition r_fexpr e := @R_fexpr V.T e.
  Definition r_default := @R_default V.T.

  (****** Oriented type ******)
  Inductive forient : Type :=
  | Source | Sink | Duplex | Passive | Other.

  (** eq dec *)
  Lemma forient_eq_dec : forall {x y : forient}, {x = y} + {x <> y}.
  Proof. induction x, y ; try (right ; discriminate) ; try (left ; reflexivity). Qed.
  Definition forient_eqn (x y : forient) : bool :=
  match x, y with Source, Source | Sink, Sink | Duplex, Duplex | Passive, Passive | Other, Other => true
                | _, _ => false end.
  Lemma forient_eqP : Equality.axiom forient_eqn.
  Proof. unfold Equality.axiom, forient_eqn. induction x, y ; try (apply ReflectF ; discriminate) ; try (apply ReflectT ; reflexivity). Qed.
  Canonical forient_eqMixin := EqMixin forient_eqP.
  Canonical forient_eqType := Eval hnf in EqType forient forient_eqMixin.

  Definition orient_of_comp c :=
    match c with
    | In_port | Instanceof | Memory | Node => Source
    (* DNJ: Not sure whether a memory should be a source. It is written like that
    in the specificiation, but actually the data type of a memory port is a bundle
    defined as a sink (with some fields flipped). *)
    | Out_port => Sink
    | Register | Wire => Duplex
    | Fmodule => Other
    end.

  Definition valid_lhs_orient o :=
    match o with
    | Sink | Duplex => true
    | _ => false
    end.

  Definition valid_rhs_orient o :=
    match o with
    | Source | Duplex | Passive => true
    | _ => false
    end.

  (* rhs expr has right orient *)
  Fixpoint valid_rhs_ref (e : href) (ce : cenv) :=
    match e with
    | Eid r => let (_,c) := CE.vtyp r ce in valid_rhs_orient (orient_of_comp c)
    | Esubfield r _ => valid_rhs_ref r ce
    (* DNJ: Subfields can be flipped. So one needs to check with the data type of r *)
    | Esubindex r _ => valid_rhs_ref r ce
    | Esubaccess r _ => valid_rhs_ref r ce
    end.

  Fixpoint valid_rhs_fexpr (e : hfexpr) (ce : cenv) :=
    match e with
    | Econst _ _ => true
    | Eref r => valid_rhs_ref r ce
    | Ecast _ _ => true
    | Eprim_binop _ _ _ => true
    | Eprim_unop _ _ => true
    (* DNJ: The arguments of a multiplexer or a validif need to be passive. *)
    | Emux _ e1 e2 => valid_rhs_fexpr e1 ce && (valid_rhs_fexpr e2 ce)
    | Evalidif _ e => valid_rhs_fexpr e ce
    end.

  Definition valid_rhs (re : rhs_expr) (ce : cenv) : bool :=
    match re with
    | R_default => true
    (* | R_ftype t => is_passive t *)
    | R_fexpr e => valid_rhs_fexpr e ce
    (* | R_fstmt s => match s with *)
    (*                | Sreg _ _ | Smem _ _ => true *)
    (*                | _ => false *)
    (*                end *)
    end.

  (****** Semantics ******)

  (* ground type equivalence *)
  Definition fgtyp_equiv t1 t2 :=
    match t1, t2 with
    | Fuint _, Fuint _
    | Fsint _, Fsint _
    | Fclock, Fclock
    | Freset, Freset
    (* | Freset, Fuint 1 *)
    | Fasyncreset, Fasyncreset => true
    | _, _ => false
    end.

  (* type equivalence *)
  Fixpoint ftype_equiv t1 t2 :=
    match t1, t2 with
    | Gtyp gt1, Gtyp gt2 => fgtyp_equiv gt1 gt2
    | Atyp t1 n1, Atyp t2 n2 => (n1 == n2) && ftype_equiv t1 t2
    | Btyp bt1, Btyp bt2 => fbtyp_equiv bt1 bt2
    | _, _ => false
    end
  with fbtyp_equiv bt1 bt2 :=
         match bt1, bt2 with
         | Fnil, Fnil => true
         | Fflips v1 Flipped t1 fs1, Fflips v2 Flipped t2 fs2 =>
           (v1 == v2) && ftype_equiv t1 t2 && fbtyp_equiv fs1 fs2
         | Fflips v1 Nflip t1 fs1, Fflips v2 Nflip t2 fs2 =>
           (v1 == v2) && ftype_equiv t1 t2 && fbtyp_equiv fs1 fs2
         | _, _ => false
         end.

  (* type weak equivalence *)
  Fixpoint have_field bs f : bool :=
    match bs with
    | Fflips v fp t bs' => if v == f then true else have_field bs' f
    | Fnil => false
    end.

  Fixpoint orient_of_field bs f : option fflip :=
    match bs with
    | Fflips v fp t bs' => if v == f then Some fp else orient_of_field bs' f
    | Fnil => None
    end.

  Fixpoint type_of_field bs f : option ftype :=
    match bs with
    | Fflips v fp t bs' => if v == f then Some t else type_of_field bs' f
    | Fnil => None
    end.

  Definition same_ffilp f1 f2 : bool :=
    match f1, f2 with
    | Flipped, Flipped => true
    | Nflip, Nflip => true
    | _, _ => false
    end.

  Fixpoint fbtyp_weak_equiv b1 b2 :=
    match b1 with
    | Fflips v1 fp1 t1 fs1 =>
      match orient_of_field b1 v1, type_of_field b2 v1 with
      | Some fp2, Some t2 => (same_ffilp fp1 fp2 && (ftype_equiv t1 t2))
      | _, _ => fbtyp_weak_equiv fs1 b2
      end
    | Fnil => true
    end.

  Fixpoint ftype_weak_equiv t1 t2 :=
    match t1, t2 with
    | Gtyp gt1, Gtyp gt2 => fgtyp_equiv gt1 gt2
    | Atyp t1 n1, Atyp t2 n2 => ftype_equiv t1 t2
    | Btyp bt1, Btyp bt2 => fbtyp_weak_equiv bt1 bt2
    | _, _ => false
    end.

  Definition cmpnt_init_typs := @cmpnt_init_typs V.T.
  Definition aggr_typ t := @Aggr_typ V.T t.
  Definition reg_typ t := @Reg_typ V.T t.
  Definition mem_typ t := @Mem_typ V.T t.
  Definition unknown_typ := @Unknown_typ V.T.



  Fixpoint eref_has_v (v:var) r :=
    match r with
    | Eid v1 => v1 == v
    | Esubfield r f => eref_has_v v r
    | Esubindex r n => eref_has_v v r
    | Esubaccess r a => eref_has_v v r
    end.

  Fixpoint fexpr_has_v v e :=
    match e with
    | Econst _ _ => false
    | Ecast _ e => fexpr_has_v v e
    | Eprim_binop b e1 e2 => fexpr_has_v v e1 || fexpr_has_v v e2
    | Eprim_unop u e => fexpr_has_v v e
    | Emux c e1 e2 => fexpr_has_v v c || fexpr_has_v v e1 || fexpr_has_v v e2
    | Evalidif c e => fexpr_has_v v c || fexpr_has_v v e
    | Eref r => eref_has_v v r
    end.

  (********************************************************************************)

  (** Pass Resolvekinds *)

  (* Resolve component kind from statement, init with unknown type *)
  Inductive resolveKinds_stmt : hfstmt -> cenv -> cenv -> Prop :=
  | Resolve_wire v t (ce : cenv) (ce' : cenv) :
      CE.find v ce' = Some (unknown_typ, Wire) ->
      resolveKinds_stmt (swire v t) ce ce'
  | Resolve_reg v r ce ce' :
      CE.find v ce' = Some (unknown_typ, Register) ->
      resolveKinds_stmt (sreg v r) ce ce'
  | Resolve_inst v1 v2 ce ce' :
  (*~~ (v1 == v2) ->*)
      CE.find v1 ce' = Some (unknown_typ, Instanceof) ->
      resolveKinds_stmt (sinst v1 v2) ce ce'
  | Resolve_node v e ce ce' :
      CE.find v ce' = Some (unknown_typ, Node) ->
      resolveKinds_stmt (snode v e) ce ce'
  | Resolve_mem v m ce ce' :
      CE.find v ce' = Some (unknown_typ, Memory) ->
      resolveKinds_stmt (smem v m) ce ce'
  | Resolve_invalid v ce :
      resolveKinds_stmt (sinvalid v) ce ce
  | Resolve_skip ce :
      resolveKinds_stmt sskip ce ce
  | Resolve_fcnct r e ce :
      resolveKinds_stmt (sfcnct r e) ce ce
  | Resolve_pcnct r e ce :
      resolveKinds_stmt (spcnct r e) ce ce
  | Resolve_when e s1 s2 ce ce' ce'' :
      resolveKinds_stmts s1 ce ce' ->
      resolveKinds_stmts s2 ce' ce'' ->
      resolveKinds_stmt (swhen e s1 s2) ce ce''
  (* | Resolve_stop e1 e2 n ce : *)
  (*     resolveKinds_stmt (sstop e1 e2 n) ce ce *)


  with resolveKinds_stmts : hfstmt_seq -> cenv -> cenv -> Prop :=
  | Resolve_stmts_nil ce :
      resolveKinds_stmts qnil ce ce
  | Resolve_stmts_cons s ss ce ce' ce'' :
      resolveKinds_stmt s ce ce' ->
      resolveKinds_stmts ss ce' ce'' ->
    resolveKinds_stmts (Qcons s ss) ce ce''
  .

  Inductive resolveKinds_port : hfport -> CE.env -> CE.env -> Prop :=
  | Resolve_input v t ce ce' :
      CE.find v ce' = Some (unknown_typ, In_port) ->
      resolveKinds_port (Finput v t) ce ce'
  | Resolve_output v t ce ce' :
      CE.find v ce' = Some (unknown_typ, Out_port) ->
      resolveKinds_port (Foutput v t) ce ce'
  .

  Inductive resolveKinds_ports : seq hfport -> CE.env -> CE.env -> Prop :=
  | Resolve_ports_nil ce :
      resolveKinds_ports [::] ce ce
  | Resolve_ports_cons p ps ce ce' ce'' :
      resolveKinds_port p ce ce' ->
      resolveKinds_ports ps ce' ce'' ->
      resolveKinds_ports (p::ps) ce ce''.

  Inductive resolveKinds_module : hfmodule -> CE.env -> CE.env -> Prop :=
  | Resolves_inmod vm ps ss ce ce' :
      CE.find vm ce' = Some (unknown_typ, Fmodule) ->
      resolveKinds_module (hfinmod vm ps ss) ce ce'
  | Resolves_exmod vm ps ss ce ce' :
      CE.find vm ce' = Some (unknown_typ, Fmodule) ->
      resolveKinds_module (hfexmod vm ps ss) ce ce'
  .

  Inductive resolveKinds_modules : seq hfmodule -> CE.env -> CE.env -> Prop :=
  | Resolve_modules_nil ce :
      resolveKinds_modules [::] ce ce
  | Resolve_modules_cons p ps ce ce' ce'' :
      resolveKinds_module p ce ce' ->
      resolveKinds_modules ps ce' ce'' ->
      resolveKinds_modules (p :: ps) ce ce''.

  (* For error checking, one could replace CE.add by a function that generates an error message
     if an identifier was already declared earlier.  However, one has to be careful about namespaces. *)

  Fixpoint resolveKinds_stmt_fun (st : hfstmt) (ce : cenv) : cenv :=
    match st with
    | Sskip => ce
    | Swire v t => CE.add v (unknown_typ, Wire) ce
    | Sreg v r => CE.add v (unknown_typ, Register) ce
    | Smem v m => CE.add v (unknown_typ, Memory) ce
    | Sinst v m => CE.add v (unknown_typ, Instanceof) ce
    | Snode v e => CE.add v (unknown_typ, Node) ce
    | Sfcnct _ _
    | Spcnct _ _
    | Sinvalid _ => ce
    | Swhen _ sts_true sts_false => resolveKinds_stmts_fun sts_false (resolveKinds_stmts_fun sts_true ce)
    end

  with resolveKinds_stmts_fun (sts : hfstmt_seq) (ce : cenv) : CE.env := (*fold_right resolveKinds_stmt_fun ce sts.*)
    match sts with
    | Qnil => ce
    | Qcons s stl => resolveKinds_stmts_fun stl (resolveKinds_stmt_fun s ce)
    end.

  Definition resolveKinds_port_fun p ce :=
    match p with
    | Finput v t => CE.add v (unknown_typ, In_port) ce
    | Foutput v t => CE.add v (unknown_typ, Out_port) ce
    end.

  Fixpoint resolveKinds_ports_fun ps ce := (*fold_right resolveKinds_port_fun ce ps.*)
    match ps with
    | nil => ce
    | s :: stl => resolveKinds_ports_fun stl (resolveKinds_port_fun s ce)
    end.

  Definition resolveKinds_module_fun m ce :=
    match m with
    | FInmod v ps ss => CE.add v (unknown_typ, Fmodule) ce
    | FExmod v ps ss => CE.add v (unknown_typ, Fmodule) ce
    end.

  Fixpoint resolveKinds_modules_fun ms ce := (*fold_right resolveKinds_module_fun ce ms.*)
    match ms with
    | nil => ce
    | s :: stl => resolveKinds_modules_fun stl (resolveKinds_module_fun s ce)
    end.

  (******lemma of resolvekinds *****)
  Lemma resolveKinds_snode_sem_conform :
  forall v e ce0 ,
    resolveKinds_stmt (Snode v e) ce0 (resolveKinds_stmt_fun (Snode v e) ce0).
Proof.
  intros. apply Resolve_node.
  rewrite /resolveKinds_stmt_fun /CE.add_fst (CELemmas.add_eq_o _ _ (eq_refl v)) //.
  Qed.

Lemma resolveKinds_sreg_sem_conform :
  forall v e ce0 ,
  resolveKinds_stmt (Sreg v e) ce0 (resolveKinds_stmt_fun (Sreg v e) ce0).
Proof.
  intros. apply Resolve_reg.
  rewrite /resolveKinds_stmt_fun /CE.add_fst (CELemmas.add_eq_o _ _ (eq_refl v)) //.
  Qed.

Lemma resolveKinds_smem_sem_conform :
  forall v e ce0 ,
  resolveKinds_stmt (Smem v e) ce0 (resolveKinds_stmt_fun (Smem v e) ce0).
Proof.
  intros. apply Resolve_mem.
  rewrite /resolveKinds_stmt_fun /CE.add_fst (CELemmas.add_eq_o _ _ (eq_refl v)) //.
Qed.

Lemma resolveKinds_sinvalid_sem_conform :
  forall v ce0 ,
  resolveKinds_stmt (Sinvalid v) ce0 (resolveKinds_stmt_fun (Sinvalid v) ce0).
Proof.
  intros. apply Resolve_invalid.
Qed.

Lemma resolveKinds_sskip_sem_conform :
  forall ce0 ,
  resolveKinds_stmt sskip ce0 (resolveKinds_stmt_fun sskip ce0).
Proof.
  intros. apply Resolve_skip.
Qed.

Lemma resolveKinds_sfcnct_sem_conform :
  forall r e ce0 ,
  resolveKinds_stmt (sfcnct r e) ce0 (resolveKinds_stmt_fun (sfcnct r e) ce0).
Proof.
  intros. apply Resolve_fcnct.
Qed.

Lemma resolveKinds_spcnct_sem_conform :
forall r e ce0 ,
  resolveKinds_stmt (spcnct r e) ce0 (resolveKinds_stmt_fun (spcnct r e) ce0).
Proof.
  intros. apply Resolve_pcnct.
Qed.

Lemma resolveKinds_swhen_sem_conform :
forall (e : hfexpr) (s1 s2 : hfstmt_seq) (ce0 ce1 ce2: cenv),
  resolveKinds_stmts s1 ce0 ce1 ->
  resolveKinds_stmts s2 ce1 (resolveKinds_stmt_fun (swhen e s1 s2) ce0) ->
  resolveKinds_stmt (swhen e s1 s2) ce0 (resolveKinds_stmt_fun (swhen e s1 s2) ce0).
Proof.
  intros. apply Resolve_when with (ce' := ce1). exact H. exact H0.
Qed.

(* Lemma resolveKinds_sstop_sem_conform : *)
(* forall e1 e2 n ce0 , *)
(*   resolveKinds_stmt (sstop e1 e2 n) ce0 (resolveKinds_stmt_fun (sstop e1 e2 n) ce0). *)
(* Proof. *)
(*   intros. apply Resolve_stop. *)
(* Qed. *)

Lemma resolveKinds_swire_sem_conform :
  forall v e ce0 ,
  resolveKinds_stmt (Swire v e) ce0 (resolveKinds_stmt_fun (Swire v e) ce0).
Proof.
  intros. apply Resolve_wire.
  rewrite /resolveKinds_stmt_fun.
  rewrite (CELemmas.add_eq_o _ _ (eq_refl v)) //.
Qed.

Lemma resolveKinds_sinst_sem_conform :
  forall v1 v2 ce0 ,
  resolveKinds_stmt (Sinst v1 v2) ce0 (resolveKinds_stmt_fun (Sinst v1 v2) ce0).
Proof.
  intros. apply Resolve_inst.
  rewrite /resolveKinds_stmt_fun /CE.add_fst (CELemmas.add_eq_o _ _ (eq_refl v1)) //.
Qed.

Definition resolveKinds_stmts_sem_conform_statement (sts : hfstmt_seq) : Prop :=
forall ce0 : cenv,
  resolveKinds_stmts sts ce0 (resolveKinds_stmts_fun sts ce0).

Lemma resolveKinds_stmts_sem_conform :
  forall sts : hfstmt_seq, resolveKinds_stmts_sem_conform_statement sts.
Proof.
  apply hfstmt_seq_hfstmt_ind with (P := resolveKinds_stmts_sem_conform_statement)
                                   (P0 := fun st : hfstmt => match st with Swhen c s1 s2 => resolveKinds_stmts_sem_conform_statement s1 /\ resolveKinds_stmts_sem_conform_statement s2 | _ => True end) ; try done.
  unfold resolveKinds_stmts_sem_conform_statement. apply Resolve_stmts_nil.
  intros.
  unfold resolveKinds_stmts_sem_conform_statement.
  intros.
  apply Resolve_stmts_cons with (ce' := resolveKinds_stmt_fun h ce0).
  induction h.
  - apply resolveKinds_sskip_sem_conform.
  - apply resolveKinds_swire_sem_conform.
  - apply resolveKinds_sreg_sem_conform.
  - apply resolveKinds_smem_sem_conform.
  - apply resolveKinds_sinst_sem_conform.
  - apply resolveKinds_snode_sem_conform.
  - apply resolveKinds_sfcnct_sem_conform.
  - apply resolveKinds_spcnct_sem_conform.
  - apply resolveKinds_sinvalid_sem_conform.
  - apply resolveKinds_swhen_sem_conform with (ce1 := resolveKinds_stmts_fun h1 ce0) ; try done.
    apply H. apply H.
  rewrite /=.
  apply (H0 (resolveKinds_stmt_fun h ce0)).
  Qed.

Lemma resolveKinds_inport_sem_conform :
  forall v t ce0 ,
    resolveKinds_port (Finput v t) ce0 (resolveKinds_port_fun (Finput v t) ce0).
  Proof.
    intros.
    apply Resolve_input; try done.
    rewrite /resolveKinds_port_fun /CE.add_fst (CELemmas.add_eq_o _ _ (eq_refl v)) //.
    Qed.

Lemma resolveKinds_outport_sem_conform :
  forall v t ce0 ,
    resolveKinds_port (Foutput v t) ce0 (resolveKinds_port_fun (Foutput v t) ce0).
  Proof.
    intros.
    apply Resolve_output; try done.
    rewrite /resolveKinds_port_fun /CE.add_fst (CELemmas.add_eq_o _ _ (eq_refl v)) //.
    Qed.

Lemma resolveKinds_ports_sem_conform :
  forall ps ce0 ,
    resolveKinds_ports ps ce0 (resolveKinds_ports_fun ps ce0).
  Proof.
    elim. intros. apply Resolve_ports_nil.
    intros.
    apply Resolve_ports_cons with (resolveKinds_port_fun a ce0).
    elim a; intros;try done.
    - apply resolveKinds_inport_sem_conform.
    - apply resolveKinds_outport_sem_conform.
    rewrite /=.
    apply (H (resolveKinds_port_fun a ce0)).
  Qed.

Lemma resolveKinds_inmod_sem_conform :
forall vm ps ss ce,
  resolveKinds_module (FInmod vm ps ss) ce (resolveKinds_module_fun (FInmod vm ps ss) ce).
Proof.
  intros.
  apply Resolves_inmod.
  rewrite /resolveKinds_module_fun.
  rewrite /CE.add_fst (CELemmas.add_eq_o _ _ (eq_refl vm)) //.
Qed.

Lemma resolveKinds_exmod_sem_conform :
forall vm ps ss ce,
  resolveKinds_module (FExmod vm ps ss) ce (resolveKinds_module_fun (FExmod vm ps ss) ce).
Proof.
  intros.
  apply Resolves_exmod.
  rewrite /resolveKinds_module_fun.
  rewrite /CE.add_fst (CELemmas.add_eq_o _ _ (eq_refl vm)) //.
Qed.

Lemma resolveKinds_mods_sem_conform :
forall ms ce0 ,
  resolveKinds_modules ms ce0 (resolveKinds_modules_fun ms ce0).
Proof.
    elim. intros. apply Resolve_modules_nil.
    intros.
    apply Resolve_modules_cons with (resolveKinds_module_fun a ce0).
    elim a; intros;try done.
    - apply resolveKinds_inmod_sem_conform.
    - apply resolveKinds_exmod_sem_conform.
    rewrite /=.
    apply (H (resolveKinds_module_fun a ce0)).
    Qed.

  (** decide the type and width of hifirrtl expressions *)

  Parameter v2var : V.t -> Var.var.

  Definition def_ftype := Gtyp (Fuint 0).

  (* type of mux expression *)
  Fixpoint mux_types t1 t2 : ftype :=
      match t1, t2 with
      | Gtyp (Fuint w1), Gtyp (Fuint w2) => (Gtyp (Fuint (maxn w1 w2)))
      | Gtyp (Fsint w1), Gtyp (Fsint w2) => (Gtyp (Fsint (maxn w1 w2)))
      | Gtyp Fclock, Gtyp Fclock => (Gtyp Fclock)
      | Atyp t1 n1, Atyp t2 n2 => if n1 == n2 then (Atyp (mux_types t1 t2) n1)
                                  else def_ftype
      | Btyp bs1, Btyp bs2 => match mux_btyps bs1 bs2 with
                              | Fnil => def_ftype
                              | t => Btyp t
                              end
      | _, _ => def_ftype
      end
  with mux_btyps bs1 bs2 : ffield :=
         match bs1, bs2 with
         | Fnil, Fnil => (Fnil)
         | Fflips v1 Nflip t1 fs1, Fflips v2 Nflip t2 fs2 =>
           if v1 == v2 then
             (Fflips v1 Nflip (mux_types t1 t2) (mux_btyps fs1 fs2))
           else Fnil
         | _, _ => Fnil
    end.

  (* type of ref expressions *)
  Fixpoint type_of_ref r ce : ftype :=
    match r with
    | Eid v => type_of_cmpnttyp (fst (CE.vtyp v ce))
    | Esubfield r v => let t := type_of_ref r ce in
                       match t with
                       | Btyp fs => let fix aux fx := (
                                          match fx with
                                          | Fflips v' f t fxs =>
                                            if (v2var v == v') then t
                                            else aux fxs
                                          | Fnil => def_ftype
                                          end )
                                    in aux fs
                       | _ => def_ftype
                       end
    | Esubindex r n => let t := type_of_ref r ce in
                       match t with
                       | Atyp ty n => ty
                       | _ => def_ftype
                       end
    | Esubaccess r e => let t := type_of_ref r ce in
                        match t with
                        | Atyp ty n => ty
                        | _ => def_ftype
                        end
    end.

  Fixpoint base_ref r : V.t :=
    match r with
    | Eid v => v
    | Esubfield r v => base_ref r
    | Esubindex r n => base_ref r
    | Esubaccess r n => base_ref r
    end.

  Fixpoint base_type_of_ref r ce : ftype :=
    match r with
    | Eid v => type_of_cmpnttyp (fst (CE.vtyp v ce))
    | Esubfield r v => base_type_of_ref r ce
    | Esubindex r n => base_type_of_ref r ce
    | Esubaccess r n => base_type_of_ref r ce
    end.

  (* type of expression *)
  Fixpoint type_of_hfexpr (e : hfexpr) (ce : cenv) : ftype :=
    match e with
    | Econst t bs => Gtyp t
    | Eref r => type_of_ref r ce
    | Ecast AsUInt e1 => let t := type_of_hfexpr e1 ce in
                         match t with
                         | Gtyp (Fsint w) | Gtyp (Fuint w) => Gtyp (Fuint w)
                         | Gtyp Fclock => Gtyp (Fuint 1)
                         | Gtyp Freset => Gtyp (Fuint 1)
                         | Gtyp Fasyncreset => Gtyp (Fuint 1)
                         | _ => def_ftype
                         end
    | Ecast AsSInt e1 => let t := type_of_hfexpr e1 ce in
                         match t with
                         | Gtyp (Fsint w) | Gtyp (Fuint w) => Gtyp (Fsint w)
                         | Gtyp Fclock => Gtyp (Fsint 1)
                         | Gtyp Freset => Gtyp (Fuint 1)
                         | Gtyp Fasyncreset => Gtyp (Fuint 1)
                         | _ => def_ftype
                         end
    | Ecast AsClock e1 => let t := type_of_hfexpr e1 ce in
                          match t with
                          | Gtyp _ =>  Gtyp Fclock
                          | _ => def_ftype
                          end
    | Ecast AsReset e1 => let t := type_of_hfexpr e1 ce in
                          match t with
                          | Gtyp _ =>  Gtyp Freset
                          | _ => def_ftype
                          end
    | Ecast AsAsync e1 => let t := type_of_hfexpr e1 ce in
                          match t with
                          | Gtyp _ =>  Gtyp Fasyncreset
                          | _ => def_ftype
                          end
    | Eprim_unop (Upad n) e1 => let t := type_of_hfexpr e1 ce in
                                match t with
                                | Gtyp (Fsint w) => Gtyp (Fsint (maxn w n))
                                | Gtyp (Fuint w) => Gtyp (Fuint (maxn w n))
                                | _ => def_ftype
                                end
    | Eprim_unop (Ushl n) e1 => let t := type_of_hfexpr e1 ce in
                                match t with
                                | Gtyp (Fsint w) => Gtyp (Fsint (w + n))
                                | Gtyp (Fuint w) => Gtyp (Fuint (w + n))
                                | _ => def_ftype
                                end
    | Eprim_unop (Ushr n) e1 => let t := type_of_hfexpr e1 ce in
                                match t with
                                | Gtyp (Fsint w) => if n < w then Gtyp (Fsint (maxn (w - n) 1))
                                                    else Gtyp (Fuint 1)
                                | Gtyp (Fuint w) => if n < w then Gtyp (Fuint (maxn (w - n) 1))
                                                    else Gtyp (Fuint 1)
                                | _ => def_ftype
                                end
    | Eprim_unop Ucvt e1 => let t := type_of_hfexpr e1 ce in
                                match t with
                                | Gtyp (Fsint w) => Gtyp (Fsint w)
                                | Gtyp (Fuint w) => Gtyp (Fsint (w + 1))
                                | _ => def_ftype
                                end
    | Eprim_unop Uneg e1 => let t := type_of_hfexpr e1 ce in
                                match t with
                                | Gtyp (Fsint w) | Gtyp (Fuint w) => Gtyp (Fsint (w + 1))
                                | _ => def_ftype
                                end
    | Eprim_unop Unot e1 => let t := type_of_hfexpr e1 ce in
                                match t with
                                | Gtyp (Fsint w) | Gtyp (Fuint w) => Gtyp (Fuint w)
                                | _ => def_ftype
                                end
    | Eprim_unop (Uextr n1 n2) e1 => let t := type_of_hfexpr e1 ce in
                                     match t with
                                     | Gtyp (Fsint w) | Gtyp (Fuint w) =>
                                                        if (n2 <= n1) && (n1 < w) then Gtyp (Fuint (n1 - n2 + 1))
                                                        else def_ftype
                                     | _ => def_ftype
                                     end
    | Eprim_unop (Uhead n) e1 => let t := type_of_hfexpr e1 ce in
                                 match t with
                                 | Gtyp (Fsint w) | Gtyp (Fuint w) =>
                                                    if n <= w then Gtyp (Fuint n)
                                                    else def_ftype
                                 | _ => def_ftype
                                 end
    | Eprim_unop (Utail n) e1 => let t := type_of_hfexpr e1 ce in
                                 match t with
                                 | Gtyp (Fsint w) | Gtyp (Fuint w) =>
                                                    if n <= w then Gtyp (Fuint (w - n))
                                                    else def_ftype
                                 | _ => def_ftype
                                 end
    | Eprim_unop _ e1 => let t := type_of_hfexpr e1 ce in
                         match t with
                         | Gtyp (Fsint _) | Gtyp (Fuint _) => Gtyp (Fuint 1)
                         | _ => def_ftype
                         end
    | Eprim_binop (Bcomp _) e1 e2 => let t1 := type_of_hfexpr e1 ce in
                                     let t2 := type_of_hfexpr e2 ce in
                                     match t1, t2 with
                                     | Gtyp (Fsint _), Gtyp (Fsint _)
                                     | Gtyp (Fuint _), Gtyp (Fuint _) => Gtyp (Fuint 1)
                                     | _, _ => def_ftype
                                     end
    | Eprim_binop Badd e1 e2
    | Eprim_binop Bsub e1 e2 => let t1 := type_of_hfexpr e1 ce in
                                let t2 := type_of_hfexpr e2 ce in
                                match t1, t2 with
                                | Gtyp (Fuint w1) , Gtyp (Fuint w2) => Gtyp (Fuint (maxn w1 w2 + 1))
                                | Gtyp (Fsint w1) , Gtyp (Fsint w2) => Gtyp (Fsint (maxn w1 w2 + 1))
                                | _, _ => def_ftype
                                end
    | Eprim_binop Bmul e1 e2 => let t1 := type_of_hfexpr e1 ce in
                                let t2 := type_of_hfexpr e2 ce in
                                match t1, t2 with
                                | Gtyp (Fuint w1) , Gtyp (Fuint w2) => Gtyp (Fuint (w1 + w2))
                                | Gtyp (Fsint w1) , Gtyp (Fsint w2) => Gtyp (Fsint (w1 + w2))
                                | _, _ => def_ftype
                                end
    | Eprim_binop Bdiv e1 e2  => let t1 := type_of_hfexpr e1 ce in
                                 let t2 := type_of_hfexpr e2 ce in
                                 match t1, t2 with
                                 | Gtyp (Fuint w1), Gtyp (Fuint w2) => Gtyp (Fuint w1)
                                 | Gtyp (Fsint w1), Gtyp (Fsint w2) => Gtyp (Fsint (w1 + 1))
                                 | _, _ => def_ftype
                                 end
    | Eprim_binop Brem e1 e2 => let t1 := type_of_hfexpr e1 ce in
                                 let t2 := type_of_hfexpr e2 ce in
                                 match t1, t2 with
                                 | Gtyp (Fuint w1), Gtyp (Fuint w2) => Gtyp (Fuint (minn w1 w2))
                                 | Gtyp (Fsint w1), Gtyp (Fsint w2) => Gtyp (Fsint (minn w1 w2))
                                 | _, _ => def_ftype
                                 end
    | Eprim_binop Bdshl e1 e2 => let t1 := type_of_hfexpr e1 ce in
                                 let t2 := type_of_hfexpr e2 ce in
                                 match t1, t2 with
                                 | Gtyp (Fuint w1), Gtyp (Fuint w2) => Gtyp (Fuint (w1 + 2 ^ w2 - 1))
                                 | Gtyp (Fsint w1), Gtyp (Fuint w2) => Gtyp (Fsint (w1 + 2 ^ w2 - 1))
                                 | _, _ => def_ftype
                                 end
    | Eprim_binop Bdshr e1 e2 => let t1 := type_of_hfexpr e1 ce in
                                 let t2 := type_of_hfexpr e2 ce in
                                 match t1, t2 with
                                 | Gtyp (Fuint w1), Gtyp (Fuint w2) => Gtyp (Fuint w1)
                                 | Gtyp (Fsint w1), Gtyp (Fuint w2) => Gtyp (Fsint w1)
                                 | _, _ => def_ftype
                                 end
    | Eprim_binop Bcat e1 e2 => let t1 := type_of_hfexpr e1 ce in
                                let t2 := type_of_hfexpr e2 ce in
                                match t1, t2 with
                                | Gtyp (Fuint w1), Gtyp (Fuint w2) => Gtyp (Fuint (w1 + w2))
                                | Gtyp (Fsint w1), Gtyp (Fsint w2) => Gtyp (Fuint (w1 + w2))
                                | _, _ => def_ftype
                                end
    | Eprim_binop Band e1 e2
    | Eprim_binop Bor e1 e2
    | Eprim_binop Bxor e1 e2 => let t1 := type_of_hfexpr e1 ce in
                                let t2 := type_of_hfexpr e2 ce in
                                match t1, t2 with
                                | Gtyp (Fuint w1), Gtyp (Fuint w2) => Gtyp (Fuint (maxn w1 w2))
                                | Gtyp (Fsint w1), Gtyp (Fsint w2) => Gtyp (Fuint (maxn w1 w2))
                                | _, _ => def_ftype
                                end
    | Emux c e1 e2 => let t1 := type_of_hfexpr e1 ce in
                      let t2 := type_of_hfexpr e2 ce in
                      mux_types t1 t2
    | Evalidif c e1 => type_of_hfexpr e1 ce
    end.


  (********************************************************************************)

  Definition is_init (s : hfstmt) : bool :=
     match s with
     | Spcnct _ _ | Sfcnct _ _ | Sinvalid _ | Swhen _ _ _
     (* | Sstop _ _ _  *)| Sskip => false
     | _ => true
     end.
  
   Fixpoint is_init_all_t s : bool :=
     match (s) with
     | nil => true
     | cons h t => if (is_init h) then is_init_all_t t else false
     end.

   Fixpoint not_init_all s : bool :=
     match s with
     | nil => true
     | cons h t => if (is_init h) then false else not_init_all t
     end.

   Parameter new_comp_name : var -> Prop.

   Parameter new_v_cefind_none:
     forall v,
     new_comp_name v ->
     forall ce: cenv, CE.find v ce = None.



  (********************************************************************************)



  Definition upd_regtyp t r :=
    mk_hfreg t (clock r) (reset r).

  Definition upd_memtyp t m :=
    mk_hfmem t (depth m) (reader m) (writer m) (read_latency m) (write_latency m) (read_write m).

  Definition is_bundle t :=
    match t with Btyp _ => true | _ => false end.

  Definition is_vector t :=
    match t with Atyp _ _ => true | _ => false end.

  Fixpoint is_deftyp t :=
    match t with
    | Gtyp (Fsint 0)
    | Gtyp (Fuint 0) => true
    | Atyp tn _ => is_deftyp tn
    | Btyp Fnil => true
    | Btyp bt => is_deftyp_f bt
    | _ => false
    end
  with is_deftyp_f bt :=
         match bt with
         | Fnil => false
         | Fflips v f tv fs => is_deftyp tv || (is_deftyp_f fs)
         end.

  (* given 2 equivalent types, return the one with larger width *)
  Fixpoint max_width t1 t2 :=
    match t1, t2 with
    | Gtyp (Fsint w1), Gtyp (Fsint w2) => Gtyp (Fsint (maxn w1 w2))
    | Gtyp (Fuint w1), Gtyp (Fuint w2) => Gtyp (Fuint (maxn w1 w2))
    | Atyp tn1 n1, Atyp tn2 n2 => if n2 == n1 then Atyp (max_width tn1 tn2) n1
                                  else t1
    | Btyp bt1, Btyp bt2 => Btyp (max_width_f bt1 bt2)
    | _, _ => t1
    end
  with max_width_f bt1 bt2 :=
         match bt1, bt2 with
         | Fflips v1 ft1 t1 fs1, Fflips v2 ft2 t2 fs2 =>
           Fflips v1 ft1 (max_width t1 t2) (max_width_f fs1 fs2)
         | _, _ => bt1
         end.

  Lemma max_width_ftype_equiv :
    forall t1 t2,
      ftype_equiv t1 t2 ->
      ftype_equiv t1 (max_width t1 t2)
  with max_width_ffield_equiv :
         forall f1 f2,
           fbtyp_equiv f1 f2 ->
           fbtyp_equiv f1 (max_width_f f1 f2).
  Proof.
    elim.
    - move => f . elim; try discriminate.
      elim f;
       try (intro; elim; try done).
    - move => t1 Hm n.
      elim; try done. move => t2 Hn n2.
      move => Heqt; rewrite /= in Heqt.
      move : Heqt =>/andP[Hteq Heq12].
      rewrite (eqP Hteq) /= !eq_refl andTb.
      by apply Hm.
    - move => f1. elim; try discriminate.
      move => f2. apply max_width_ffield_equiv.
    elim.
    - elim; try done.
    - move => v1 fp1 t1 ff1 Hm.
      elim. case fp1 => //.
      move => v2 fp2 t2 ff2 Hn.
      case fp1; case fp2; try discriminate.
      + move =>/= /andP[/andP [Heq1 Heq2] Heq3].
        rewrite eq_refl andTb.
        apply /andP; split.
        * apply max_width_ftype_equiv; done.
        * apply Hm; done.
      + move =>/= /andP[/andP [Heq1 Heq2] Heq3].
        rewrite eq_refl andTb.
        apply /andP; split.
        * apply max_width_ftype_equiv; done.
        * apply Hm; done.
  Qed.

  (* directly upd a field of a ftype with name 'v' with given type t, the field width upd to larger one *)
  (* if it has no such field, return itself *)
  Fixpoint upd_name_ftype ft v t : ftype :=
    match ft with
    | Gtyp gt => t
    | Atyp tn n => Atyp (upd_name_ftype tn v t) n
    | Btyp bt => Btyp (upd_name_ffield bt v t)
    end
  with upd_name_ffield bt v t : ffield :=
         match bt with
         | Fnil => Fnil
         | Fflips v1 fp t1 fs => if v1 == v then Fflips v1 fp (max_width t1 t) fs
                                 else Fflips v1 fp (upd_name_ftype t1 v t)
                                             (upd_name_ffield fs v t)
         end.

  Lemma upd_type_equiv :
    forall t r v ce, ~~ is_deftyp (type_of_hfexpr (eref (esubfield r v)) ce) ->
                     ftype_equiv (type_of_hfexpr (eref (esubfield r v)) ce) t ->
                     ftype_equiv (base_type_of_ref r ce)
                                 (upd_name_ftype (base_type_of_ref r ce) (v2var v) t).
  Proof.
  Admitted.

  Fixpoint upd_vectyp vt t : ftype :=
    match vt with
    | Gtyp gt => t
    | Atyp tn n => Atyp (upd_vectyp tn t) n
    | Btyp bt => Btyp bt
    end.

  Lemma upd_vectyp_equiv :
    forall t r n ce, ftype_equiv (type_of_hfexpr (eref (esubaccess r n)) ce) t ->
                     ftype_equiv (base_type_of_ref r ce)
                                 (upd_vectyp (base_type_of_ref r ce) t).
  Proof.
  Admitted.

  Fixpoint typeConstraints (f1 f2 : nat -> nat -> bool) (t1 t2 : ftype) : bool :=
    match t1, t2 with
    | Gtyp (Fuint w1), Gtyp (Fuint w2)
    | Gtyp (Fsint w1), Gtyp (Fsint w2) => f1 w1 w2
    | Gtyp Fclock, Gtyp Fclock => true
    | Atyp t1 n1, Atyp t2 n2 => (n1 == n2) && typeConstraints f1 f2 t1 t2
    | Btyp b1, Btyp b2 => typeConstraints_f f1 f2 b1 b2
    | _, _ => false
    end
  with typeConstraints_f f1 f2 b1 b2 :=
         match b1, b2 with
         | Fnil, Fnil => true
         | Fflips v1 Flipped t1 fs1, Fflips v2 Flipped t2 fs2 =>
           (v1 == v2) && (typeConstraints f2 f1 t1 t2) && typeConstraints_f f1 f2 fs1 fs2
         | Fflips v1 Nflip t1 fs1, Fflips v2 Nflip t2 fs2 =>
           (v1 == v2) && typeConstraints f1 f2 t1 t2 && typeConstraints_f f1 f2 fs1 fs2
         | _, _ => false
         end.



  (* type constraint : dst type ge than src *)
  Definition typeConstraintsGe t1 t2 := typeConstraints geq ltn t1 t2.

  (* type constraint exclude default type *)
  Definition typeConstraintsGe_exdef t1 t2 :=
    if is_deftyp t1 then true
    else typeConstraintsGe t1 t2.

  (********************************************************************************)

  (** Pass ResolveFlow *)
  (* rhs passive type ? TBD. *)

  (* Fixpoint resolveFlow_fun st te : bool := *)
  (*   match st with *)
  (*   | Sfcnct r e => *)
  (*     ftype_equiv (type_of_ref r te) (type_of_hfexpr e te) && valid_rhs_fexpr e te *)
  (*     && (valid_lhs_orient (orient_of_comp (snd (CE.vtyp (base_ref r) te)))) *)
  (*   | Spcnct r e => *)
  (*     ftype_weak_equiv (type_of_ref r te) (type_of_hfexpr e te) && valid_rhs_fexpr e te *)
  (*     && (valid_lhs_orient (orient_of_comp (snd (CE.vtyp (base_ref r) te)))) *)
  (*   | Sinvalid e => valid_rhs_ref e te *)
  (*   | Sreg r rt => match (reset rt) with *)
  (*                  | NRst => true *)
  (*                  | Rst r1 r2 => valid_rhs_fexpr r2 te *)
  (*                  end *)
  (*   | _ => true *)
  (*   end. *)

  (********************************************************************************)

   (** Pass ExpandWhens *)
(* COMMENT OUT START HERE *)
(*
  
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

   Definition option_and (simcond : option hfexpr) (cond : hfexpr) : hfexpr :=
   (* calculates the conjunction between two conditions if present *)
   match simcond with
   | None => cond
   | Some s => eprim_binop Band s cond
   end.

   (* Because nat and ftype are not mutually recursive types we cannot define a mutually recursive
      initialization function for registers including array types.
      Therefore we construct, in a mutual recursion, a function that initializes one element of the array.
      After that we call the constructed function for every element of the array. *)

   Fixpoint init_register_vector (v : nat -> href) (array_size : nat) (type : ftype) (ce : cenv) : (nat -> cmap -> cmap) * nat :=
   (* Produces a function that initializes v to itself.
      Input:  * v = href of the variable that needs to be initialized (possibly this is already an array)
              * array_size = size of the array v (if it's not an array, array_size == 1)
              * type = type of (a single element of the array) v <number>
              * ce = component environment
      Output: * nat -> cmap -> cmap : a function that initializes one element of the array (by modifying a cmap accordingly)
              * nat : size of the array *)
   match type with
   | Gtyp _ => ((fun n : nat => CE.add (expand_eref (v n) ce) (D_fexpr (Eref (v n)))), array_size)
   | Atyp el_type n => init_register_vector (fun m : nat => Esubindex (v (m / array_size)) (m mod array_size)) (array_size * n) el_type ce
   | Btyp ff => init_register_bundle v array_size ff ce
   end
   with init_register_bundle (v : nat -> href) (array_size : nat) (ff : ffield) (ce : cenv) : (nat -> cmap -> cmap) * nat :=
   match ff with
   | Fnil => ((fun (n : nat) (cm : cmap) => cm), 0)
   | Fflips field_name Nflip field_type ff_tail =>
        let init_field := init_register_vector (fun n : nat => Esubfield (v n) (var2v field_name)) array_size field_type ce in
        let init_tail := init_register_bundle v array_size ff_tail ce in
        ((fun n : nat => if n < snd init_field then fst init_field n
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

   Definition init_register (id : V.T) (type : ftype) (ce : cenv) (cm : cmap) : cmap :=
   (* Initializes the register id, which is of type type. *)
   let initializer := init_register_vector (fun n : nat => Eid id) 1 type ce in
   init_apply_initializer (fst initializer) (snd initializer) cm.

   (* Identifiers for the fields of a memory port *)
   Parameter mem_port_addr : V.T.
   Parameter mem_port_en : V.T.
   Parameter mem_port_clk : V.T.
   Parameter mem_port_data : V.T.
   Parameter mem_port_mask : V.T.

   Fixpoint init_memory_reader (id : V.T) (reader : seq V.T) (ce : cenv) (cm : cmap) : cmap :=
   (* Helper function for init_memory. It initializes the read ports that are indicated in reader. *)
   match reader with
   | [::] => cm
   | r :: rtail => init_memory_reader id rtail ce
                   (CE.add (expand_eref (Esubfield (Esubfield (Eid id) r) mem_port_addr) ce) D_undefined
                      (CE.add (expand_eref (Esubfield (Esubfield (Eid id) r) mem_port_en) ce) D_undefined
                         (CE.add (expand_eref (Esubfield (Esubfield (Eid id) r) mem_port_clk) ce) D_undefined
                            cm
                         )
                      )
                   )
   end.

   Fixpoint init_undefined_vector (v : nat -> href) (array_size : nat) (type : ftype) (value : def_expr) (ce : cenv) : (nat -> cmap -> cmap) * nat :=
   (* Produces a function that initializes v to value (mostly D_undefined or D_invalidated).
      It can be used to initialize memory write ports (data and mask fields) and wires.
      Memory ports have to be passive, but wires allow flipped fields,
      so it does not check whether the type is passive.
      Input:  * v = href of the variable that needs to be initialized (possibly this is already an array)
              * array_size = size of the array v (if it's not an array, array_size == 1)
              * type = type of v <number>
              * ce = component environment
      Output: * nat -> cmap -> cmap : a function that initializes one element of the array (by modifying a cmap accordingly)
              * nat : size of the array *)
   match type with
   | Gtyp _ => ((fun n : nat => CE.add (expand_eref (v n) ce) value), array_size)
   | Atyp el_type n => init_undefined_vector (fun m : nat => Esubindex (v (m / array_size)) (m mod array_size)) (array_size * n) el_type value ce
   | Btyp ff => init_undefined_bundle v array_size ff value ce
   end
   with init_undefined_bundle (v : nat -> href) (array_size : nat) (ff : ffield) (value : def_expr) (ce : cenv) : (nat -> cmap -> cmap) * nat :=
   match ff with
   | Fnil => ((fun (n : nat) (cm : cmap) => cm), 0)
   | Fflips field_name fflip field_type ff_tail =>
        let init_field := match fflip with Nflip => init_undefined_vector  (fun n : nat => Esubfield (v n) (var2v field_name)) array_size field_type value ce
                                       | Flipped => init_undefined_flipped (fun n : nat => Esubfield (v n) (var2v field_name)) array_size field_type value ce
                          end in
        let init_tail := init_undefined_bundle v array_size ff_tail value ce in
        ((fun n : nat => if n < snd init_field then fst init_field n
                                               else fst init_tail (n - snd init_field)),
         snd init_field + snd init_tail)
   end
   with init_undefined_flipped (v : nat -> href) (array_size : nat) (type : ftype) (value : def_expr) (ce : cenv) : (nat -> cmap -> cmap) * nat :=
   match type with
   | Gtyp _ => ((fun (n : nat) (cm: cmap) => cm), 0)
   | Atyp el_type n => init_undefined_flipped (fun m : nat => Esubindex (v (m / array_size)) (m mod array_size)) (array_size * n) el_type value ce
   | Btyp ff => init_undefined_flipped_bundle v array_size ff value ce
   end
   with init_undefined_flipped_bundle (v : nat -> href) (array_size : nat) (ff : ffield) (value : def_expr) (ce : cenv) : (nat -> cmap -> cmap) * nat :=
   match ff with
   | Fnil => ((fun (n : nat) (cm : cmap) => cm), 0)
   | Fflips field_name fflip field_type ff_tail =>
        let init_field := match fflip with Nflip => init_undefined_flipped (fun n : nat => Esubfield (v n) (var2v field_name)) array_size field_type value ce
                                       | Flipped => init_undefined_vector  (fun n : nat => Esubfield (v n) (var2v field_name)) array_size field_type value ce
                          end in
        let init_tail := init_undefined_flipped_bundle v array_size ff_tail value ce in
        ((fun n : nat => if n < snd init_field then fst init_field n
                                               else fst init_tail (n - snd init_field)),
         snd init_field + snd init_tail)
   end.

   Fixpoint init_memory_writer (id : V.T) (data_type : ftype) (writer : seq V.T) (ce : cenv) (cm : cmap) : cmap :=
   (* Helper function for init_memory. It initializes the write ports that are indicated in writer. *)
   match writer with
   | [::] => cm
   | w :: wtail => let initializer_data := init_undefined_vector (fun n : nat => (Esubfield (Esubfield (Eid id) w) mem_port_data)) 1 data_type D_undefined ce in
                   let initializer_mask := init_undefined_vector (fun n : nat => (Esubfield (Esubfield (Eid id) w) mem_port_mask)) 1 data_type D_undefined ce in
                   init_memory_writer id data_type wtail ce
                   (CE.add (expand_eref (Esubfield (Esubfield (Eid id) w) mem_port_addr) ce) D_undefined
                      (CE.add (expand_eref (Esubfield (Esubfield (Eid id) w) mem_port_en) ce) D_undefined
                         (CE.add (expand_eref (Esubfield (Esubfield (Eid id) w) mem_port_clk) ce) D_undefined
                            (init_apply_initializer (fst initializer_data) (snd initializer_data)
                               (init_apply_initializer (fst initializer_mask) (snd initializer_mask) cm)
                            )
                         )
                      )
                   )
   end.

   Fixpoint memport_ids (m : seq mem_port) : seq V.T :=
     match m with
     | nil => nil
     | cons pid pids => cons (id pid) (memport_ids pids)
     end.
   
   Definition init_memory (id : V.T) (m : hfmem) (ce : cenv) (cm : cmap) : cmap :=
   (* This helper function initializes a memory named v with description m.
      In particular, all reader and writer ports are declared undefined. *)
   init_memory_writer id (data_type m) (memport_ids (writer m)) ce (init_memory_reader id (memport_ids (reader m)) ce cm).

   Definition init_wire (id : V.T) (type : ftype) (ce : cenv) (cm : cmap) : cmap :=
   (* Initializes a wire named id with type type. *)
   let initializer := init_undefined_vector (fun n : nat => (Eid id)) 1 type D_undefined ce in
   init_apply_initializer (fst initializer) (snd initializer) cm.

(* Inductive error_type (T : Type) : Type :=
   | ECorrect : T -> error_type
   | Esyntax
   | Etype
   | Euninitialized (* a component should be connected but isn't *)
   | Einternal (* e.g. if a pass receives input that should have been handled by earlier passes *)
   | E...

   Definition init_wire (id : V.T) (type : ftype) (ce : cenv) (cm : cmap) : error_type cmap :=
   (* Initializes a wire named id with type type. May return an error message. *)
   match init_undefined_vector (fun n : nat => (Eid id)) 1 type D_undefined ce with
   Some initializer => init_apply_initializer (fst initializer) (snd initializer) cm
   error => error
   end. *)

   Definition init_instance (id: V.T) (mdl: V.T) (ce : cenv) (cm : cmap) : cmap :=
   (* This function should initialize the ports that connect the current module with module mdl under the name id,
      which is instantiated here.
      It is assumed that the type of the module is stored in ce already. *)
   let initializer := init_undefined_flipped (fun n : nat => (Eid id)) 1 (type_of_cmpnttyp (fst (CE.vtyp mdl ce))) D_undefined ce in
   init_apply_initializer (fst initializer) (snd initializer) cm.

   Definition invalidate_cmpnt (ref : href) (ce : cenv) (cm : cmap) : cmap :=
   (* Sets the component ref to invalid, to indicate that the programmer let it unconnected on purpose. *)
   (* If "is invalid" statements are expanded by ExpandConnects, then it would suffice to return
      CE.add (expand_eref ref ce) D_invalidated cm. *)
   let initializer := init_undefined_vector (fun n : nat => ref) 1 (type_of_ref ref ce) D_invalidated ce in
   init_apply_initializer (fst initializer) (snd initializer) cm.

   Fixpoint expandBranch_fun (ss : hfstmt_seq) (ce : cenv) (cm : cmap) (simcond : option hfexpr) : (hfstmt_seq * cmap) :=
   (* This is the main function of ExpandWhens. It replaces when statements by expressions containing
      multiplexers/validifs where necessary.  It has the following interface:
      Input:  * ss = sequence of statements that are a final fragment of a module definition
                or a final fragment of a branch
                (not containing partial or aggregate connects or aggregate "is invalid" statements;
                possibly containing repeated connects and when statements)
              * ce = component environment, containing the type declarations
                of the module (this has been found in earlier passes and is not updated)
              * cm = map of connections that have been defined in the previous statements of the module definition
                (including, when applicable, in the previous statements of the branch).
                This map is used in case a when statement only replaces a connect in one branch;
                in that case, the other branch has to copy the connect from this map.
              * simcond = condition of the outer when statement;
                this is used to constrain simulation statement Sstop
                in case it appears within a when statement.
      Output: a pair consisting of
              * sequence of statements, mainly containing declarations of registers and wires,
                that should become part of the resulting code (because registers and wires etc.
                declared in one branch should be included always in the translated code)
              * cmap : map of connects that have been defined before or in the branch
                (i.e. this map extends parameter cm by the connects in ss). *)
   match ss with
   | Qnil => (qnil, cm)
   | Qcons s ss_tail => match s with
                 | @Sskip _ => expandBranch_fun ss_tail ce cm simcond (* no translation needed *)
                 | @Swire _ id type => let result := expandBranch_fun ss_tail ce (init_wire id type ce cm) simcond in
                                       (Qcons s (fst result), snd result)
                 | @Sreg _ id reg => let result := expandBranch_fun ss_tail ce (init_register id (type reg) ce cm) simcond in
                                     (Qcons s (fst result), snd result)
                 | @Smem _ id mem => let result := expandBranch_fun ss_tail ce (init_memory id mem ce cm) simcond in
                                     (Qcons s (fst result), snd result)
                 | @Sinst _ id mdl => let result := expandBranch_fun ss_tail ce (init_instance id mdl ce cm) simcond in
                                   (Qcons s (fst result), snd result)
                 | @Snode _ _ _ => let result := expandBranch_fun ss_tail ce cm simcond in
                                   (Qcons s (fst result), snd result)
                 | @Sfcnct _ ref expr => expandBranch_fun ss_tail ce (CE.add (expand_eref ref ce) (D_fexpr expr) cm) simcond
                 | @Spcnct _ _ _ => (* error: should have been expanded earlier *) (qnil, empty_cmap)
                 | @Sinvalid _ ref => expandBranch_fun ss_tail ce (invalidate_cmpnt ref ce cm) simcond
                 | @Swhen _ cond ss_true ss_false => let combined_branches := combine_branches cond (expandBranch_fun ss_true  ce cm (Some (option_and simcond cond)))
                                                                                                    (expandBranch_fun ss_false ce cm (Some (option_and simcond (eprim_unop Unot cond)))) in
                                         let result := expandBranch_fun ss_tail ce (snd combined_branches) simcond in
                                         (Qcat (fst combined_branches) (fst result), snd result)
                 (* | @Sstop _ clk cond exit => let result := expandBranch_fun ss_tail ce cm simcond in *)
                 (*                             (Qcons (Sstop clk (option_and simcond cond) exit) (fst result), snd result) *)
                 end
   end.

   Fixpoint init_ports (ports : seq hfport) (ce : cenv) (cm : cmap) : cmap :=
   (* This helper function sets the ports of a module to undefined. *)
   match ports with
   | [::] => cm
   | Finput  id type :: ports_tail => let initializer := init_undefined_flipped (fun n : nat => Eid id) 1 type D_undefined ce in
                                      init_ports ports_tail ce (init_apply_initializer (fst initializer) (snd initializer) cm)
   | Foutput id type :: ports_tail => let initializer := init_undefined_vector  (fun n : nat => Eid id) 1 type D_undefined ce in
                                      init_ports ports_tail ce (init_apply_initializer (fst initializer) (snd initializer) cm)
   end.

   Definition recode_cmap_entry (id : V.T) (dexpr : def_expr) (ss : hfstmt_seq) : hfstmt_seq :=
   (* This helper function for recode_map translates one entry of the cmap into a statement
      that is added to the statement sequence ss. *)
   match dexpr with
   | D_undefined => ss (* the user has erroneously not connected to id *)
   | D_invalidated => Qcons (sinvalid (Eid id)) ss (* the user has given an "is invalid" statement. Copy it. *)
   | D_fexpr expr => Qcons (sfcnct (Eid id) expr) ss
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

   Fixpoint dependencies_present (expr : hfexpr) (ce : cenv) (cm : cmap) : bool :=
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
   with dependencies_present_ref (ref : href) (ce : cenv) (cm : cmap) : bool :=
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

   Definition recode_cmap_sorted_entry (ce : cenv) (id : V.T) (dexpr : def_expr) (ss_cm : hfstmt_seq * cmap) : hfstmt_seq * cmap :=
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

   Function recode_cmap_sorted (ce : cenv) (cm : cmap) (ss : hfstmt_seq)
   (cm_is_well_founded : forall cm' : cmap, (forall (id : V.T) (dexpr : def_expr), CE.MapsTo id dexpr cm' -> CE.MapsTo id dexpr cm) ->
                                exists (id : V.T) (dexpr : def_expr),
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
   else let result := CE.fold (recode_cmap_sorted_entry ce) cm (ss, FSet.empty) in
        recode_cmap_sorted (snd result) (fst result) cm_is_well_founded. *)

   (* Perhaps a better way is to construct a dag.  The dag implicitly contains the proof
      that there are no cycles.  That reminds me: there are already some graph functions
      in some Coq library; in particular, the function to calculate sccs can be used for
      this end. *)

   Definition expandWhen_fun (mdl : hfmodule) (ce : cenv) : hfmodule :=
   (* This function provides an interface to the main function.
      Input:  * mdl = module definition
                (its statements do not contain partial or aggregate connects;
                they may contain double connects and when statements)
              * ce = component environment, containing the type declarations
                of the module and the interface declarations of all other modules
                (this has been found in earlier passes and is not updated)
      Output: translated statement sequence of the module *)
   match mdl with
   | FInmod id ports ss => let result := expandBranch_fun ss ce (init_ports ports ce empty_cmap) None in
                           FInmod id ports (Qcat (fst result) (recode_cmap (snd result)))
   | FExmod _ _ ss => (* error: external modules cannot be handled for verification *) mdl
   end.

   (* This data type is meant to describe the resulting value of a component depending on the execution path.
      Whenever there is a when statement (and the component has been declared before,
      so it is available in both execution paths), a T_choice node is inserted. *)
   Inductive expr_tree : Type :=
   | T_undeclared (* in this execution path, the component is not declared *)
   | T_undefined (* the component is erroneously not connected *)
   | T_invalidated (* the component is not connected but the programmer has indicated with an "is invalid" statement that this is ok *)
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
                   | @Sreg _ id _ => expandBranch_one_var_sem tl ref (if base_ref ref == id then T_fexpr (Eref ref) else default)
                   | @Swire _ id _
                   (* In the two lines below we disregard that some subfields of an instance may be flipped
                      and therefore have source flow direction; similarly, <memory id>.<read port id>.data
                      has source flow direction.  That is why we have the precondition
                      that ref must have sink (or duplex) flow direction. *)
                   | @Smem _ id _
                   | @Sinst _ id _ => expandBranch_one_var_sem tl ref (if base_ref ref == id then T_undefined else default)
                   (* In the two lines below we assume that ref0 is a ground type, as ExpandConnects has already been applied. *)
                   | @Sfcnct _ ref0 expr => expandBranch_one_var_sem tl ref (if ref == ref0 then T_fexpr expr else default)
                   | @Sinvalid _ ref0 => expandBranch_one_var_sem tl ref (if ref == ref0 then T_invalidated else default)
                   | @Swhen _ cond ss_true ss_false => let true_result  := expandBranch_one_var_sem ss_true  ref default in
                                                       let false_result := expandBranch_one_var_sem ss_false ref default in
                                                       match true_result, false_result with
                                                       (* ignore execution paths where ref is not declared *)
                                                       | T_undeclared, _ => expandBranch_one_var_sem tl ref false_result
                                                       | _, T_undeclared => expandBranch_one_var_sem tl ref true_result
                                                       | _, _ => expandBranch_one_var_sem tl ref
                                                                 (if true_result == false_result then true_result
                                                                  else T_choice cond true_result false_result)
                                                       end
                   | _ => expandBranch_one_var_sem tl ref default
                   end
   end.

   Parameter expandBranch_vars_sem : forall (ss : hfstmt_seq) (ce : cmap) (cs : cstate) (default : cstate), Prop.
(* TBD :=
   (* Specification: cs contains the connects defined by ss.
      If there is no connect, then the value of cs is copied from default. *)
   forall id : V.T, match SV.find id cs, expandBranch_one_var_sem ss (eid id) (SV.find id default) with
                    | None, D_undeclared => True
                    | Some
*)
   Fixpoint expandWhen_precondition_ss (ss : hfstmt_seq) : Prop :=
   (* Precondition of expandWhen: there are no aggregate types and no partial connects *)
   match ss with
   | Qnil => True
   | Qcons s tl => match s with
                  | @Spcnct _ _ _ => False
                  | @Swire _ _ t => match t          with Gtyp _ => expandWhen_precondition_ss tl
                                                        | _ => False end
                  | @Sreg _ _ r => match type r      with Gtyp _ => expandWhen_precondition_ss tl
                                                        | _ => False end
                  | @Smem _ _ m => match data_type m with Gtyp _ => expandWhen_precondition_ss tl
                                                        | _ => False end
                  | @Sfcnct _ v _ => match v with Eid _ => expandWhen_precondition_ss tl
                                                | _ => False end
                  | @Swhen _ _ sst ssf =>    expandWhen_precondition_ss sst
                                          /\ expandWhen_precondition_ss ssf
                                          /\ expandWhen_precondition_ss tl
                  | _ => expandWhen_precondition_ss tl
                  end
   end.

   Definition expandWhen_precondition_ce (ce : cenv) : Prop :=
   (* Precondition of expandWhen: all declared components have ground types *)
   forall v : V.T, match CE.find v ce with
                   | None => True (* no constraints on types of undeclared components *)
                   | Some (t, _) => match type_of_cmpnttyp t with Gtyp _ => True (* declared components have ground types *)
                                                                | _ => False end
                   end.

   Definition expandBranch_hfstmt_seq_sem_conform (ss : hfstmt_seq) : Prop :=
   (* The statements in ss are being translated by expandBranch_fun to correct definitions in a StructStore (cstate). *)
      expandWhen_precondition_ss ss ->
      forall ce : cenv, expandWhen_precondition_ce ce ->
                        forall default : cstate, expandBranch_vars_sem ss (snd (expandBranch_fun ss ce default)) default.


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
   unfold expandBranch_vars_sem, expandBranch_fun, snd.
   unfold expandBranch_one_var_sem.
   reflexivity.
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
   exact H2.
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

   (* Fixpoint try_expandBranch_fun (s :  hfstmt) (ce : cenv) (cs : cstate) {struct s}: (cstate):= *)
   (*        let fix aux (ss : seq hfstmt) (ce : cenv) (cs : cstate) {struct ss}: (cstate) := *)

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
   (*               | Swire v t => SV.upd v (R_default V.T) cs *)
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

(* COMMENT OUT END HERE *)
*)



   (********************************************************************************)


End MakeHiFirrtl.


Module HiF := MakeHiFirrtl VarOrder VS VM CE StructState.

Section Preprocess.

  Definition initial_index : N := 0.

  Definition first_assigned_index : N := 1.

  Definition 
  
End Preprocess.
