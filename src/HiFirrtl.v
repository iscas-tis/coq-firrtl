From Coq Require Import FunInd FMaps FMapAVL OrderedType ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat ssrint eqtype seq.
From simplssrlib Require Import Types SsrOrder FSets FMaps Tactics Var Store.
From nbits Require Import NBits.
From firrtl Require Import Firrtl Env HiEnv.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


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

  (****** Statements ******)

  Record hfmem : Type :=
    mk_fmem
      {
        (* mid : var; *)
        data_type : ftype;
        depth : nat;
        reader : seq var;
        writer : seq var;
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
  | Swhen : hfexpr -> seq hfstmt -> seq hfstmt -> hfstmt
  | Sstop : hfexpr -> hfexpr -> nat -> hfstmt
  (* | Sprintf (* TBD *) *)
  (* | Sassert (* TBD *) *)
  (* | Sassume (* TBD *) *)
  (* | Sdefname : var -> fstmt *) (* TBD *)
  (* | Sparam : var -> fexpr -> fstmt *) (* TBD *)
  .

  Inductive hfport : Type :=
  | Finput : var -> ftype -> hfport
  | Foutput : var -> ftype -> hfport
  .

  Inductive hfmodule : Type :=
  | FInmod : var -> seq hfport -> seq hfstmt -> hfmodule
  | FExmod : var -> seq hfport -> seq hfstmt -> hfmodule
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
  Variable tmp : eqType.
  Inductive rhs_expr : Type :=
  | R_fexpr : hfexpr tmp -> rhs_expr
  (*| R_ftype : ftype -> rhs_expr*)
  (*| R_fstmt : hfstmt tmp -> rhs_expr*)
  | R_default
  .

  
  (** eq dec *)
  Axiom rhs_expr_eq_dec : forall {x y : rhs_expr}, {x = y} + {x <> y}.
  Parameter rhs_expr_eqn : forall (x y : rhs_expr), bool.
  Axiom rhs_expr_eqP : Equality.axiom rhs_expr_eqn. 
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
  Parameter map2 : (option value -> option value -> option value) -> t -> t -> t.
  Parameter acc : var -> t -> value.
  Parameter upd : var -> value -> t -> t.
  Parameter upd2 : var -> value -> var -> value -> t -> t.
  Parameter acc_upd_eq : forall {x y v s}, x == y -> acc x (upd y v s) = v.
  Parameter acc_upd_neq : forall {x y v s}, x != y -> acc x (upd y v s) = acc x s.
  Parameter acc_upd2_eq1 :
    forall {x y1 v1 y2 v2 s},
      x == y1 -> x != y2 -> acc x (upd2 y1 v1 y2 v2 s) = v1.
  Parameter acc_upd2_eq2 :
    forall {x y1 v1 y2 v2 s},
      x == y2 -> acc x (upd2 y1 v1 y2 v2 s) = v2.
  Parameter acc_upd2_neq :
    forall {x y1 v1 y2 v2 s},
      x != y1 -> x != y2 -> acc x (upd2 y1 v1 y2 v2 s) = acc x s.
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
  Definition sskip := @Sskip V.T.
  Definition swire v t := @Swire V.T v t.
  Definition sreg v r := @Sreg V.T v r.
  Definition smem v m := @Smem V.T v m.
  Definition snode v e := @Snode V.T v e.
  Definition sfcnct v1 v2 := @Sfcnct V.T v1 v2.
  Definition spcnct v1 v2 := @Spcnct V.T v1 v2.
  Definition sinvalid v1 := @Sinvalid V.T v1.
  Definition swhen c s1 s2 := @Swhen V.T c s1 s2.
  Definition sstop e1 e2 n := @Sstop V.T e1 e2 n.
  Definition sinst v1 v2 := @Sinst V.T v1 v2.

  Definition hfreg := @hfreg V.T.
  Definition mk_hfreg := @mk_freg V.T.
  Definition nrst := @NRst V.T.
  Definition rrst e1 e2 := @Rst V.T e1 e2.
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
  (* Definition r_ftype t := @R_ftype V.T t. *)
  (* Definition r_fstmt s := @R_fstmt V.T s. *)
  Definition r_default := @R_default V.T.

  (****** Oriented type ******)
  Inductive forient : Type :=
  | Source | Sink | Duplex | Passive | Other.

  (** eq dec *)
  Axiom forient_eq_dec : forall {x y : forient}, {x = y} + {x <> y}.
  Parameter forient_eqn : forall (x y : forient), bool.
  Axiom forient_eqP : Equality.axiom forient_eqn. 
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
    (* DNJ: The arguments of a multiplexer or a validif need to be passive.
    I am not sure whether something similar holds for primitive expression arguments;
    I guess they should be valid_rhs_fexpr themselves. *)
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
      CELemmas.P.Add v (unknown_typ, Wire) ce ce' ->
      resolveKinds_stmt (swire v t) ce ce'
  | Resolve_reg v r ce ce' :
      CELemmas.P.Add v (unknown_typ, Register) ce ce' ->
      resolveKinds_stmt (sreg v r) ce ce'
  | Resolve_inst v1 v2 ce ce' :
      CELemmas.P.Add v1 (unknown_typ, Instanceof) ce ce' ->
      resolveKinds_stmt (sinst v1 v2) ce ce'
  | Resolve_node v e ce ce' :
      CELemmas.P.Add v (unknown_typ, Node) ce ce' ->
      resolveKinds_stmt (snode v e) ce ce'
  | Resolve_mem v m ce ce' :
      CELemmas.P.Add v (unknown_typ, Memory) ce ce' ->
      resolveKinds_stmt (smem v m) ce ce'
  | Resolve_invalid v ce :
      resolveKinds_stmt (sinvalid v) ce ce
  .

  Inductive resolveKinds_stmts : seq hfstmt -> cenv -> cenv -> Prop :=
  | Resolve_stmts_nil ce :
      resolveKinds_stmts [::] ce ce
  | Resolve_stmts_cons s ss ce ce' ce'' :
      resolveKinds_stmt s ce ce' ->
      resolveKinds_stmts ss ce' ce'' ->
      resolveKinds_stmts (s::ss) ce ce''.

  Inductive resolveKinds_port : hfport -> CE.env -> CE.env -> Prop :=
  | Resolve_input v t ce ce' :
      CELemmas.P.Add v (unknown_typ, In_port) ce ce' ->
      resolveKinds_port (hinport v t) ce ce'
  | Resolve_output v t ce ce' :
      CELemmas.P.Add v (unknown_typ, Out_port) ce ce' ->
      resolveKinds_port (houtport v t) ce ce'
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
      CELemmas.P.Add vm (unknown_typ, Fmodule) ce ce' ->
      resolveKinds_module (hfinmod vm ps ss) ce ce
  | Resolves_exmod vm ps ss ce ce' :
      CELemmas.P.Add vm (unknown_typ, Fmodule) ce ce' ->
      resolveKinds_module (hfexmod vm ps ss) ce ce
  .

  Inductive resolveKinds_modules : seq hfmodule -> CE.env -> CE.env -> Prop :=
  | Resolve_modules_nil ce :
      resolveKinds_modules [::] ce ce
  | Resolve_modules_cons p ps ce ce' ce'' :
      resolveKinds_module p ce ce' ->
      resolveKinds_modules ps ce' ce'' ->
      resolveKinds_modules (p::ps) ce ce''.

  Definition resolveKinds_stmt_fun st ce :=
    match st with
    | Swire v t => CE.add v (unknown_typ, Wire) ce
    | Sreg v r => CE.add v (unknown_typ, Register) ce
    | Smem v m => CE.add v (unknown_typ, Memory) ce
    | Snode v e => CE.add v (unknown_typ, Node) ce
    | Sinst v m => CE.add v (unknown_typ, Instanceof) ce
    | Sinvalid v => ce
    | Skip => ce
    end.

  Fixpoint resolveKinds_stmts_fun sts ce : CE.env := fold_right resolveKinds_stmt_fun sts ce.

  Definition resolveKinds_port_fun p ce :=
    match p with
    | Finput v t => CE.add v (aggr_typ t, In_port) ce
    | Foutput v t => CE.add v (aggr_typ t, Out_port) ce
    end.

  Fixpoint resolveKinds_ports_fun ps ce := fold_right resolveKinds_port_fun ps ce.

  Definition resolveKinds_module_fun m ce :=
    match m with
    | FInmod v ps ss => CE.add v (unknown_typ, Fmodule) ce
    | FExmod v ps ss => CE.add v (unknown_typ, Fmodule) ce
    end.

  Fixpoint resolveKinds_modules_fun ms ce := fold_right resolveKinds_module_fun ms ce.

  (******lemma of resolvekinds *****)
  Lemma resolveKinds_snode_sem_conform :
  forall v e ce0 ,
    resolveKinds_stmt (Snode v e) ce0 (resolveKinds_stmt_fun (Snode v e) ce0).
Proof.
  intros. apply Resolve_node.
  rewrite /resolveKinds_stmt_fun.
  done.
Qed.

Lemma resolveKinds_sreg_sem_conform :
  forall v e ce0 ,
  resolveKinds_stmt (Sreg v e) ce0 (resolveKinds_stmt_fun (Sreg v e) ce0).
Proof.
  intros. apply Resolve_reg.
  rewrite /resolveKinds_stmt_fun.
  done.
Qed.

Lemma resolveKinds_smem_sem_conform :
  forall v e ce0 ,
  resolveKinds_stmt (Smem v e) ce0 (resolveKinds_stmt_fun (Smem v e) ce0).
Proof.
  intros. apply Resolve_mem.
  rewrite /resolveKinds_stmt_fun.
  done.
Qed.

Lemma resolveKinds_sinvalid_sem_conform :
forall v ce0 ,
  resolveKinds_stmt (Sinvalid v) ce0 (resolveKinds_stmt_fun (Sinvalid v) ce0).
Proof.
  intros. apply Resolve_invalid.
Qed.
(*
Lemma resolveKinds_swire_sem_conform :
  forall v r ce0 ,
    new_comp_name v ->
    inferType_stmt (Swire v r) ce0 (inferType_stmt_fun (Swire v r) ce0).
Proof.
  intros. apply Infertype_wire. try done.
  rewrite /inferType_stmt_fun.
  rewrite (CELemmas.add_eq_o _ _ (eq_refl v)) //.
Qed.
  
Lemma resolveKinds_sinst_sem_conform :
  forall v1 v2  ce0 ,
    new_comp_name v1 ->
    v1 != v2 ->
    inferType_stmt (Sinst v1 v2) ce0 (inferType_stmt_fun (Sinst v1 v2) ce0).
Proof.
  intros. apply Infertype_inst. try done. try done.
  rewrite /inferType_stmt_fun.
  rewrite (CELemmas.add_eq_o _ _ (eq_refl v1)). try done.
Qed.
*)

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
                                | Gtyp (Fsint w) | Gtyp (Fuint w) => Gtyp (Fsint w)
                                | _ => def_ftype
                                end
    | Eprim_unop Unot e1 => let t := type_of_hfexpr e1 ce in
                                match t with
                                | Gtyp (Fsint w) | Gtyp (Fuint w) => Gtyp (Fuint w)
                                | _ => def_ftype
                                end
    | Eprim_unop (Uextr n1 n2) e1 => let t := type_of_hfexpr e1 ce in
                                     match t with
                                     | Gtyp (Fsint _) | Gtyp (Fuint _) => Gtyp (Fuint (n1 - n2 + 1))
                                     | _ => def_ftype
                                     end
    | Eprim_unop (Uhead n) e1 => let t := type_of_hfexpr e1 ce in
                                 match t with
                                 | Gtyp (Fsint _) | Gtyp (Fuint _) => Gtyp (Fuint n)
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
    | Eprim_binop Bdiv e1 e2
    (* | Eprim_binop Bsdiv e1 e2 *) => let t1 := type_of_hfexpr e1 ce in
                                 let t2 := type_of_hfexpr e2 ce in
                                 match t1, t2 with
                                 | Gtyp (Fuint w1), Gtyp (Fuint w2) => Gtyp (Fuint w1)
                                 | Gtyp (Fsint w1), Gtyp (Fsint w2) => Gtyp (Fsint (w1 + 1))
                                 | _, _ => def_ftype
                                 end
    | Eprim_binop Brem e1 e2
    (* | Eprim_binop Bsrem e1 e2 *) => let t1 := type_of_hfexpr e1 ce in
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
                                | Gtyp (Fsint w1), Gtyp (Fuint w2) => Gtyp (Fuint (w1 + w2))
                                | _, _ => def_ftype
                                end
    | Eprim_binop Band e1 e2
    | Eprim_binop Bor e1 e2
    | Eprim_binop Bxor e1 e2 => let t1 := type_of_hfexpr e1 ce in 
                                let t2 := type_of_hfexpr e2 ce in
                                match t1, t2 with
                                | Gtyp (Fuint w1), Gtyp (Fuint w2) => Gtyp (Fuint (maxn w1 w2))
                                | Gtyp (Fsint w1), Gtyp (Fuint w2) => Gtyp (Fuint (maxn w1 w2))
                                | _, _ => def_ftype
                                end
    | Emux c e1 e2 => let t1 := type_of_hfexpr e1 ce in
                      let t2 := type_of_hfexpr e2 ce in
                      mux_types t1 t2 
    | Evalidif c e1 => type_of_hfexpr e1 ce
    end.


  (********************************************************************************)


   Parameter new_comp_name : var -> Prop.
   
   Parameter new_v_cefind_none:
     forall v,
     new_comp_name v ->
     forall ce: cenv, CE.find v ce = None.
  
  (** Pass InferType *)
  (* infer type according to a statement *) 
  Inductive inferType_stmt : hfstmt -> cenv -> cenv -> Prop :=
  | Infertype_wire v t ce ce' :
      new_comp_name v ->
      (* CE.find v ce = None -> *)
      CE.find v ce' = Some (aggr_typ t, Wire) ->
      inferType_stmt (swire v t) ce ce'
  | Infertype_reg v r ce ce' :
      new_comp_name v ->
      (* CE.find v ce = None -> *)
      CE.find v ce' = Some (reg_typ r, Register) ->
      inferType_stmt (sreg v r) ce ce'
  | Infertype_inst v1 v2 ce ce' :
      new_comp_name v1 ->
      (* CE.find v1 ce = None -> *)
      ~~ (v1 == v2) ->
      CE.find v1 ce' = Some (fst (CE.vtyp v2 ce), Instanceof) ->
      inferType_stmt (sinst v1 v2) ce ce'
  | Infertype_node v e ce ce' :
      new_comp_name v ->
      (* CE.find v ce = None -> *)
      (* ~~ fexpr_has_v v e -> *)
      type_of_hfexpr e ce = type_of_hfexpr e ce' ->
      CE.find v ce' = Some (aggr_typ (type_of_hfexpr e ce), Node) ->
      inferType_stmt (snode v e) ce ce'
  | Infertype_mem v m ce ce' :
      new_comp_name v ->
      (* CE.find v ce = None -> *)
      CE.find v ce' = Some (mem_typ m, Memory) ->
      inferType_stmt (smem v m) ce ce'
  | Infertype_invalid v ce :
      inferType_stmt (sinvalid v) ce ce
  | Infertype_sfcnct r e ce :
      forall t t' c,
      CE.find (base_ref r) ce = Some (t, c) /\
      type_of_hfexpr e ce = t' /\
      ftype_equiv (type_of_cmpnttyp t) t' ->
      inferType_stmt (sfcnct r e) ce ce
  | Infertype_spcnct r e ce :
      forall t t' c,
      CE.find (base_ref r) ce = Some (t, c) /\
      type_of_hfexpr e ce = t' /\
      ftype_weak_equiv (type_of_cmpnttyp t) t' ->
      inferType_stmt (spcnct r e) ce ce

  | Infertype_sskip ce :
      inferType_stmt (sskip) ce ce
  | Infertype_swhen e s1 s2 ce :
      inferType_stmt (swhen e s1 s2) ce ce
  | Infertype_sstop e1 e2 n ce :
      inferType_stmt (sstop e1 e2 n) ce ce
  .

   Definition find_unknown r (ce : cenv) :=
     match (CE.find r ce) with
     | Some (unknown_typ, _) => true
     | _ => false
     end.

  Inductive inferType_stmts : seq hfstmt -> cenv -> cenv -> Prop :=
  | Infertype_stmts_nil ce : 
      inferType_stmts [::] ce ce 
  | Infertype_stmts_con s ss ce ce' ce'' : 
      inferType_stmt s ce ce' -> 
      inferType_stmts ss ce' ce'' -> 
      inferType_stmts (s::ss) ce ce''.

  (*Inductive inferType_stmts : seq hfstmt -> cenv -> cenv -> Prop :=
  | Infertype_stmts_know ss ce ce' :
      (exists v, 
                 ~~ find_unknown v ce') ->
      inferType_stmts (ss) ce ce'.*)
  
  (* infer type according to ports declaration *)
  Inductive inferType_port : hfport -> cenv -> cenv -> Prop :=
  | Infertype_inport v t ce ce' :
      CE.find v ce = None ->
      ce' = CE.add v (aggr_typ t, In_port) ce ->
      inferType_port (hinport v t) ce ce'
  | Infertype_outport v t ce ce' :
      CE.find v ce = None ->
      ce' = CE.add v (aggr_typ t, Out_port) ce ->
      inferType_port (hinport v t) ce ce'.

  Inductive inferType_ports : seq hfport -> cenv -> cenv -> Prop :=
  | infertype_ports_nil ce :
      inferType_ports [::] ce ce
  | infertype_ports_con s ss ce ce' ce'' :
      inferType_port s ce ce' ->
      inferType_ports ss ce' ce'' ->
      inferType_ports (s::ss) ce ce''.

  Fixpoint inst_type_of_ports (ps : seq hfport) :=
    match ps with
    | nil => Fnil
    | p :: ps => match p with
                   | Finput v t => Fflips (v2var v) Flipped t (inst_type_of_ports ps)
                   | Foutput v t => Fflips (v2var v) Nflip t (inst_type_of_ports ps)
                   end
    end.

  Definition inst_type_of_ports' ps :=
    let pt := inst_type_of_ports ps in
    match pt with
    | Fnil => def_ftype
    | ps => Btyp ps
    end.

  (* infer type of module according to ports declaration *)
  Inductive inferType_module : hfmodule -> cenv -> cenv -> Prop :=
  | infertype_inmod vm ps ss ce ce' :
      CE.find vm ce' = Some (aggr_typ (inst_type_of_ports' ps), Fmodule) ->
      inferType_module (hfinmod vm ps ss) ce ce'
  | infertype_exmod vm ps ss ce ce' :
      CE.find vm ce' = Some (aggr_typ (inst_type_of_ports' ps), Fmodule) ->
      inferType_module (hfexmod vm ps ss) ce ce'.

  Definition inferType_stmt_fun st (ce : cenv) : cenv :=
    match st with
    | Snode v e => CE.add v (aggr_typ (type_of_hfexpr e ce), Node) ce
    | Sinst v1 v2 => CE.add v1 (fst (CE.vtyp v2 ce), Instanceof) ce
    | Sreg v r => CE.add v (reg_typ r, Register) ce
    | Smem v m => CE.add v (mem_typ m, Memory) ce
    | Swire v t => CE.add v (aggr_typ t, Wire) ce
    | Swhen _ _ _ (* DNJ: but when has substatements that may influence the type *) (* XM : only intuitive cases considered in this pass (according to scala implementation) *)
    | Sfcnct _ _
    | Spcnct _ _
    | Sinvalid _
    | Sstop _ _ _
    | Sskip => ce
    end.

  Fixpoint inferType_stmts_fun (sts : seq hfstmt) ce : cenv := fold_right inferType_stmt_fun ce sts.

  Definition inferType_module_fun m ce :=
    match m with
    | FInmod v ps ss => inferType_stmts_fun ss (CE.add_fst v (aggr_typ (inst_type_of_ports' ps)) ce)
    | FExmod v ps ss => CE.add_fst v (aggr_typ (inst_type_of_ports' ps)) ce
    end.

  Fixpoint inferType_modules_fun ms ce := fold_right inferType_module_fun ms ce.

  Lemma ftype_equiv_ident :
    forall t , ftype_equiv t t
  with ffield_equiv_ident :
      forall(f:ffield),
      fbtyp_equiv f f.
  Proof.
    elim; rewrite /=; intros. elim f; done. 
      rewrite eq_refl H//. 
      rewrite ffield_equiv_ident//. 
    
      elim; intros. rewrite /= ; done. 
      rewrite /= eq_refl H ftype_equiv_ident. 
      case f; rewrite /=//. 
     Qed. 


(*
    elim.
    rewrite /ftype_equiv.
    intros.
    case f; try done.

    intros.
    rewrite eq_refl H//.

    move => t.
    rewrite /ftype_equiv.
    induction t.
    rewrite /fgtyp_equiv.
    case f; try done.
    rewrite eq_refl.
    try done.

    case f;try done.

    induction f.
    try done.
    try done.
    try done.
    try done.
    admit.
    try done.
    move => f.
    rewrite /fbtyp_equiv.
    induction f.
    try done.

    Admitted.
*)


    Lemma ftype_weak_equiv_ident :
  forall t ,
      ftype_weak_equiv t t.
  Proof.
    move => t.
    rewrite /ftype_weak_equiv.
    induction t.
    rewrite /fgtyp_equiv.
    case f;try done.

    rewrite /ftype_equiv.
    induction t.
    apply IHt.
    rewrite eq_refl.
    try done.
    admit.

    rewrite /fbtyp_weak_equiv.
    case f;try done.
    intros.
    case f2.


    Admitted.

  (****** TODO. For KY ******)
  (** Begin **)

  Lemma inferType_snode_sem_conform :
    forall v e ce0 ,
      new_comp_name v ->
      type_of_hfexpr e ce0 = type_of_hfexpr e (inferType_stmt_fun (Snode v e) ce0) ->
      inferType_stmt (Snode v e) ce0 (inferType_stmt_fun (Snode v e) ce0).
  Proof.
    intros. apply Infertype_node; try done.
    rewrite /inferType_stmt_fun (CELemmas.add_eq_o _ _ (eq_refl v)) //.
  Qed.
  
  Lemma inferType_sreg_sem_conform :
    forall v r ce0 ,
      new_comp_name v ->
      inferType_stmt (Sreg v r) ce0 (inferType_stmt_fun (Sreg v r) ce0).
  Proof.
    intros. apply Infertype_reg. try done.
    rewrite /inferType_stmt_fun /CE.add_fst (CELemmas.add_eq_o _ _ (eq_refl v)) //.
  Qed.

  Lemma inferType_smem_sem_conform :
    forall v r ce0 ,
      new_comp_name v ->
      inferType_stmt (Smem v r) ce0 (inferType_stmt_fun (Smem v r) ce0).
  Proof.
    intros. apply Infertype_mem. try done.
    rewrite /inferType_stmt_fun /CE.add_fst (CELemmas.add_eq_o _ _ (eq_refl v)) //.
  Qed.

  Lemma inferType_sinvalid_sem_conform :
  forall v ce0 ,
      inferType_stmt (Sinvalid v) ce0 (inferType_stmt_fun (Sinvalid v) ce0).
  Proof.
    intros. apply Infertype_invalid.
  Qed.

  Lemma inferType_swire_sem_conform :
    forall v r ce0 ,
      new_comp_name v ->
      inferType_stmt (Swire v r) ce0 (inferType_stmt_fun (Swire v r) ce0).
  Proof.
    intros. apply Infertype_wire. try done.
    rewrite /inferType_stmt_fun.
    rewrite (CELemmas.add_eq_o _ _ (eq_refl v)) //.
  Qed.
    
  Lemma inferType_sinst_sem_conform :
    forall v1 v2  ce0 ,
      new_comp_name v1 ->
      v1 != v2 ->
      inferType_stmt (Sinst v1 v2) ce0 (inferType_stmt_fun (Sinst v1 v2) ce0).
  Proof.
    intros. apply Infertype_inst. try done. try done.
    rewrite /inferType_stmt_fun.
    rewrite (CELemmas.add_eq_o _ _ (eq_refl v1)). try done.
  Qed.

  Lemma inferType_sfcnct_sem_conform :
    forall v1 t c e ce0 ,
      CE.find (base_ref v1) ce0 = Some (t, c) ->
      type_of_cmpnttyp t = type_of_hfexpr e ce0 ->
      inferType_stmt (Sfcnct v1 e) ce0 (inferType_stmt_fun (Sfcnct v1 e) ce0).
  Proof.
    intros. 
    rewrite /inferType_stmt_fun.
    apply Infertype_sfcnct with t (type_of_cmpnttyp t) c.
    split.
    apply H.
    split.
    rewrite H0.
    reflexivity.
    apply ftype_equiv_ident.
  Qed.

  Lemma inferType_spcnct_sem_conform :
    forall v1 t c e ce0 ,
      CE.find (base_ref v1) ce0 = Some (t, c) ->
      type_of_cmpnttyp t = type_of_hfexpr e ce0 ->
      inferType_stmt (Spcnct v1 e) ce0 (inferType_stmt_fun (Spcnct v1 e) ce0).
  Proof.
    intros.
    rewrite /inferType_stmt_fun.
    apply Infertype_spcnct with t (type_of_cmpnttyp t) c.
    split.
    apply H.
    split.
    rewrite H0.
    reflexivity.
    apply ftype_weak_equiv_ident.
  Qed.

  Lemma inferType_swhen_sem_conform :
  forall ce0 e s1 s2 ,
      inferType_stmt (Swhen e s1 s2) ce0 (inferType_stmt_fun (Swhen e s1 s2) ce0).
  Proof.
    intros. apply Infertype_swhen.
  Qed.

  Lemma inferType_sstop_sem_conform :
  forall ce0 e1 e2 n,
      inferType_stmt (Sstop e1 e2 n) ce0 (inferType_stmt_fun (Sstop e1 e2 n) ce0).
  Proof.
    intros. apply Infertype_sstop.
  Qed.
    
  Lemma inferType_sskip_sem_conform :
  forall ce0 ,
      inferType_stmt sskip ce0 (inferType_stmt_fun sskip ce0).
  Proof.
    intros. apply Infertype_sskip.
  Qed.

  Lemma inferType_stmts_sem_conform :
  forall ss ce0,
    inferType_stmts ss ce0 (inferType_stmts_fun ss ce0).
  Proof.
    intros.
    destruct ss eqn:Es.
    simpl.
    apply Infertype_stmts_nil.

    rewrite /inferType_stmts_fun.
    simpl.
    case h.
    Admitted.

  (*Lemma inferType_inport_sem_conform :
  forall v t ce0 ,
      inferType_inport (hinport v t) ce0 (inferType_stmt_fun sskip ce0?).
  Proof.
    intros. apply Infertype_sskip.
  Qed.  *)

  Lemma inferType_inmod_sem_conform :
  forall vm ps ss ce,
    inferType_module (hfinmod vm ps ss) ce (inferType_module_fun (hfinmod vm ps ss) ce).
  Proof.
    intros.
    apply infertype_inmod; try done.

  Admitted.

  Lemma inferType_exmod_sem_conform :
  forall vm ps ss ce,
  inferType_module (hfexmod vm ps ss) ce (inferType_module_fun (hfexmod vm ps ss) ce).
  Proof.
  Admitted.

  (*
  Lemma inferType_mods_sem_conform :
  forall vm ps ss ce,
  inferType_module (hfinmod vm ps ss) ce (inferType_module_fun (hfinmod vm ps ss) ce).

  Proof.
  Admitted.*)
    
  (** End **)
  
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

  Fixpoint resolveFlow_fun st te : bool :=
    match st with
    | Sfcnct r e => 
      ftype_equiv (type_of_ref r te) (type_of_hfexpr e te) && valid_rhs_fexpr e te
      && (valid_lhs_orient (orient_of_comp (snd (CE.vtyp (base_ref r) te))))
    | Spcnct r e =>
      ftype_weak_equiv (type_of_ref r te) (type_of_hfexpr e te) && valid_rhs_fexpr e te
      && (valid_lhs_orient (orient_of_comp (snd (CE.vtyp (base_ref r) te))))
    | Sinvalid e => valid_rhs_ref e te
    | Sreg r rt => match (reset rt) with
                   | NRst => true
                   | Rst r1 r2 => valid_rhs_fexpr r2 te
                   end
    | _ => true
    end.

  
  (********************************************************************************)

  (** Pass InferWidth *)

  (* Infer unknown width
     Infers the smallest width that is larger than or equal to all assigned widths to a signal
   * Note that this means that dummy assignments that are overwritten by last-connect-semantics
   * can still influence width inference *)


   (* A map to store candidate types *)
   Definition wmap := CE.t (seq ftype).
   Definition empty_wmap : wmap := CE.empty (seq ftype).
   Definition finds (v:var) (w:wmap) := match CE.find v w with Some t => t | None => [::] end.

   Definition wmap0 := CE.t (ftype).
   Definition empty_wmap0 : wmap0 := CE.empty (ftype).
   Definition finds0 (v:var) (w:wmap0) := match CE.find v w with Some t => t | None => def_ftype end.

   Fixpoint get_field_name r : V.t :=
     match r with
     | Eid v => v
     | Esubfield r v =>  v
     | Esubindex r n => get_field_name r
     | Esubaccess r n => get_field_name r
     end.

   (* store the larger width *)
   Fixpoint add_ref_wmap0 r t ce (w:wmap0) : wmap0 :=
     match r with
     | Eid v =>
       match CE.find v w with
       | Some t1 => CE.add v (max_width t t1) w
       | None => CE.add v t w
       end
     | Esubfield r f =>
       let br := base_ref r in
       CE.add br (upd_name_ftype (base_type_of_ref r ce) (v2var f) t) w
     | Esubindex rs n =>
       let br := base_ref rs in
       let vt := type_of_cmpnttyp (fst (CE.vtyp br ce)) in
       match vt with
       | Gtyp gt => w
       | Atyp ta na => CE.add br (upd_vectyp vt t) w
       | Btyp _ => CE.add br (upd_name_ftype vt (v2var (get_field_name rs)) t) w
       end
     | Esubaccess rs n => 
       let br := base_ref rs in
       let vt := type_of_cmpnttyp (fst (CE.vtyp br ce)) in
       match vt with
       | Gtyp gt => w
       | Atyp ta na => CE.add br (upd_vectyp vt t) w
       | Btyp Fnil => w
       | Btyp (Fflips v _ tf fs) =>
         CE.add br (upd_name_ftype vt (v2var (get_field_name rs)) t) w
       end
     end.

   
   (* Require Import FunInd. *)
   
   Fixpoint inferWidth_wmap0 (s : hfstmt) (ce : cenv) (w : wmap0): wmap0 :=
     match s with
     | Snode v e => if is_deftyp (type_of_hfexpr e ce)
                      then add_ref_wmap0 (Eid v) (type_of_hfexpr e ce) ce w else w
     | Swire v t => if is_deftyp t then add_ref_wmap0 (Eid v) t ce w else w
     | Sreg v r => if is_deftyp (type r) then add_ref_wmap0 (Eid v) (type r) ce w else w
     (* | Sreg v (mk_freg t cl (Rst (Eref rs) e)) => *)
     (*   let w1 w := add_ref_wmap0 (Eid v) (type_of_hfexpr e ce) ce w in *)
     (*   let w2 w:= add_ref_wmap0 rs (Gtyp (Fuint 1)) ce w in  *)
     (*   if (is_deftyp t) && (is_deftyp (type_of_ref rs ce)) then (w2 (w1 w)) *)
     (*   else if (is_deftyp t) then (w1 w) *)
     (*        else if (is_deftyp (type_of_ref rs ce)) then (w2 w) else w *)
     | Sfcnct r1 (Eref r2) =>
       let w1 w := add_ref_wmap0 r1 (type_of_ref r2 ce) ce w in
       let w2 w := add_ref_wmap0 r2 (type_of_ref r1 ce) ce w in
       if is_deftyp (type_of_ref r1 ce) (*&& (is_deftyp (type_of_ref r2 ce))*) then ((w1 w))
       (*else if ~~ is_deftyp (type_of_ref r1 ce) then w1 w*) else w
     | Sfcnct r e => 
       let w1 := add_ref_wmap0 r (type_of_hfexpr e ce) ce w in
       if is_deftyp (type_of_ref r ce) then w1 else w
     | Spcnct r1 (Eref r2) =>
       let add1 wx := add_ref_wmap0 r1 (type_of_ref r2 ce) ce wx in
       let add2 wx := add_ref_wmap0 r2 (type_of_ref r2 ce) ce wx in
       if is_deftyp (type_of_ref r1 ce) (*&& (is_deftyp (type_of_ref r2 ce))*) then ((add1 w))
       (*else if is_deftyp (type_of_ref r1 ce) then add1 w*)
            (*else if is_deftyp (type_of_ref r2 ce) then w2 w*) else w
     | Spcnct r e =>
       let w1 := add_ref_wmap0 r (type_of_hfexpr e ce) ce w in
       if is_deftyp (type_of_ref r ce) then w1 else w
     (* | Swhen (Eref rs) s1 s2 => *)
     (*   let w1 w := add_ref_wmap0 rs (Gtyp (Fuint 1)) ce w in *)
     (*   let fix aux ss ce w := *)
     (*       match ss with *)
     (*       | nil => w *)
     (*       | s :: ss => aux ss ce (inferWidth_wmap0 s ce w) *)
     (*       end *)
     (*   in *)
     (*   if (is_deftyp (type_of_ref rs ce)) *)
     (*   then aux s2 ce (aux s1 ce (w1 w)) *)
     (*   else aux s2 ce (aux s1 ce w) *)
     | _ => w 
     end
   .

   (* store a list of types, and compare width later *)
   (* Fixpoint add_ref_wmap r t ce w : wmap := *)
   (*   match r with *)
   (*   | Eid v => CE.add v (cons t (finds v w)) w *)
   (*   | Esubfield r f => *)
   (*     let br := base_ref r in *)
   (*     CE.add br (cons (upd_name_ftype (base_type_of_ref r ce) (v2var f) t) (finds br w)) w *)
   (*   | Esubindex rs n => *)
   (*     let br := base_ref rs in *)
   (*     let vt := type_of_cmpnttyp (fst (CE.vtyp br ce)) in *)
   (*     match vt with *)
   (*     | Gtyp gt => w *)
   (*     | Atyp ta na => CE.add br (cons (upd_vectyp vt t) (finds br w)) w *)
   (*     | Btyp _ => CE.add br (cons (upd_name_ftype vt (v2var (get_field_name rs)) t) (finds br w)) w *)
   (*     end *)
   (*   | Esubaccess rs n =>  *)
   (*     let br := base_ref rs in *)
   (*     let vt := type_of_cmpnttyp (fst (CE.vtyp br ce)) in *)
   (*     match vt with *)
   (*     | Gtyp gt => w *)
   (*     | Atyp ta na => CE.add br (cons (upd_vectyp vt t) (finds br w)) w *)
   (*     | Btyp Fnil => w *)
   (*     | Btyp (Fflips v _ tf fs) => *)
   (*       CE.add br (cons (upd_name_ftype vt (v2var (get_field_name rs)) t) (finds br w)) w *)
   (*     end *)
   (*   end. *)

   (* Fixpoint inferWidth_wmap (s : hfstmt) (ce : cenv) (w : wmap) : wmap := *)
   (*   match s with *)
   (*   | Snode v e => w *)
   (*   | Swire v t => if is_deftyp t then add_ref_wmap (Eid v) t ce w else w *)
   (*   | Sreg v (mk_freg t cl (Rst (Eref rs) e)) => *)
   (*     let w1 w := add_ref_wmap (Eid v) (type_of_hfexpr e ce) ce w in *)
   (*     let w2 w:= add_ref_wmap rs (Gtyp (Fuint 1)) ce w in  *)
   (*     if (is_deftyp t) && (is_deftyp (type_of_ref rs ce)) then (w2 (w1 w)) *)
   (*     else if (is_deftyp t) then (w1 w) *)
   (*          else if (is_deftyp (type_of_ref rs ce)) then (w2 w) else w *)
   (*   | Sfcnct r e => *)
   (*     let w1 := add_ref_wmap r (type_of_hfexpr e ce) ce w in *)
   (*     if is_deftyp (type_of_ref r ce) then w1 else w *)
   (*   | Spcnct r e =>  *)
   (*     let w1 := add_ref_wmap r (type_of_hfexpr e ce) ce w in *)
   (*     if is_deftyp (type_of_ref r ce) then w1 else w *)
   (*   | Swhen (Eref rs) s1 s2 => *)
   (*     let w1 w := add_ref_wmap rs (Gtyp (Fuint 1)) ce w in *)
   (*     if (is_deftyp (type_of_ref rs ce)) *)
   (*     then inferWidth_wmap s2 ce (inferWidth_wmap s1 ce (w1 w)) *)
   (*     else w *)
   (*   | _ => w  *)
   (*   end *)
   (* . *)

   (* Fixpoint inferWidth_stmts_wmap ss ce w: wmap := *)
   (*   match ss with *)
   (*   | nil => w *)
   (*   | s :: sts => inferWidth_stmts_wmap sts ce (inferWidth_wmap s ce w) *)
   (*   end. *)

   (* Definition max_width_of_wmap ts : ftype := *)
   (*   List.fold_left max_width ts (Gtyp (Fuint 0)). *)

   (* Definition map_max_width_wmap (w : wmap) : wmap0 := *)
   (*   CE.map max_width_of_wmap w . *)

   (* Lemma inferWidth_deftyp : *)
   (*   forall s ce w w', *)
   (*     inferWidth_wmap0 s ce w = w' -> *)
   (*     forall v, ~~ is_deftyp (finds0 v w). *)
   (* Proof. *)
   (* Admitted. *)

   Fixpoint inferWidth_stmts_wmap0 ss ce w: wmap0 :=
     match ss with
     | nil => w
     | s :: sts => inferWidth_stmts_wmap0 sts ce (inferWidth_wmap0 s ce w)
     end.

   Definition add_width_2_cenv (w : option ftype) (t : option (cmpnt_init_typs * fcomponent)) :=
     match w, t with
     | Some w, Some (Aggr_typ ta, c) => if is_deftyp ta then Some (aggr_typ w, c) else t
     | Some w, Some (Reg_typ r, c) =>
       if is_deftyp (type r) then Some (reg_typ (mk_freg (w) (clock r) (reset r)), c) else t
     | Some w, Some (Mem_typ m, c) =>
       if is_deftyp (data_type m) then Some (mem_typ (mk_fmem w (depth m) (reader m) (writer m) (read_latency m) (write_latency m) (read_write m)), c)
       else t
     | _, t => t
     end.

   (* overwrite type widths in ce by wmap with the same index *)

   Definition wmap_map2_cenv w (ce:cenv) : cenv :=
     CE.map2 add_width_2_cenv w ce.

   Definition inferWidth_fun ss ce : cenv :=
     wmap_map2_cenv (inferWidth_stmts_wmap0 ss ce empty_wmap0) ce.

   (**** infer width semantics in pred **)

   Parameter new_v_wmap_none:
     forall v,
     new_comp_name v ->
     forall w: wmap0, CE.find v w = None.
     
   Inductive inferWidth_sstmt_sem : hfstmt -> wmap0 -> wmap0 -> cenv -> cenv -> Prop :=
   | inferWidth_sskip wm1 wm2 ce1 ce2 :
       (forall v t c, 
       CE.find v ce1 = Some (t, c) ->
       CE.find v wm1 = Some (type_of_cmpnttyp t) ->
       CE.find v wm1 = CE.find v wm2 /\
       CE.find v ce1 = CE.find v ce2) ->
       inferWidth_sstmt_sem (sskip) wm1 wm2 ce1 ce2
   | inferWidth_sstop wm1 wm2 ce1 ce2 ss1 ss2 n :
       (forall v t c , 
       CE.find v ce1 = Some (t, c) ->
       CE.find v wm1 = Some (type_of_cmpnttyp t) ->
       CE.find v wm1 = CE.find v wm2 /\
       CE.find v ce1 = CE.find v ce2) ->
       inferWidth_sstmt_sem (sstop ss1 ss2 n) wm1 wm2 ce1 ce2
   | inferWidth_sinvalid wm1 wm2 ce1 ce2 :
       forall v, (forall t c,
         CE.find (base_ref v) ce1 = Some (t, c) ->
         CE.find (base_ref v) wm1 = Some (type_of_cmpnttyp t) ->
         CE.find (base_ref v) wm1 = CE.find (base_ref v) wm2 /\
         CE.find (base_ref v) ce1 = CE.find (base_ref v) ce2) ->
         inferWidth_sstmt_sem (sinvalid v) wm1 wm2 ce1 ce2
   | inferWidth_swhen wm1 wm2 ce1 ce2 c ss1 ss2:
       (forall v t c , 
         CE.find (v) ce1 = Some (t, c) ->
         CE.find (v) wm1 = Some (type_of_cmpnttyp t) ->
         CE.find (v) wm1 = CE.find (v) wm2 /\
         CE.find (v) ce1 = CE.find (v) ce2) ->
         inferWidth_sstmt_sem (swhen c ss1 ss2) wm1 wm2 ce1 ce2
   | inferWidth_smem v m wm1 wm2 ce1 ce2 :
       (forall t ,
           CE.find (v) ce1 = Some (t, Memory) ->
           (* CE.find v wm1 = None -> *)
           new_comp_name v ->
           CE.find v wm1 = CE.find v wm2 /\
           CE.find v ce1 = CE.find v ce2) ->
       inferWidth_sstmt_sem (smem v m) wm1 wm2 ce1 ce2
   | inferWidth_smem_repeatv v m wm1 ce1 :
       (forall t ,
           CE.find v wm1 = Some t) ->
       inferWidth_sstmt_sem (smem v m) wm1 wm1 ce1 ce1
   | inferWidth_sinst v m wm1 wm2 ce1 ce2 :
       (forall t c,
           CE.find (v) ce1 = Some (t, c) ->
           (* CE.find v wm1 = None -> *)
           new_comp_name v ->
           CE.find v wm1 = CE.find v wm2 /\
           CE.find v ce1 = CE.find v ce2) ->
       inferWidth_sstmt_sem (sinst v m) wm1 wm2 ce1 ce2
   | inferWidth_snode_exp v e ce0 ce1 (wm : wmap0) :
       CE.find (v) ce0 = Some (aggr_typ (type_of_hfexpr e ce0), Node) ->
       ~~ is_deftyp (type_of_hfexpr e ce0) ->
       (* CE.find v wm = None -> *)
       new_comp_name v ->
       CE.find v ce0 = CE.find v ce1 ->
       inferWidth_sstmt_sem (Snode v e) wm wm ce0 ce1
   | inferWidth_snode_imp v e ce0 ce1 (wm0 wm1 : wmap0) :
       is_deftyp ((type_of_hfexpr e ce0)) ->
       CE.find (v) ce0 = Some (aggr_typ (type_of_hfexpr e ce0), Node) ->
       (* CE.find v wm0 = None -> *)
       new_comp_name v ->
       CE.find v wm1 = Some (type_of_hfexpr e ce0) ->
       CE.find v ce0 = CE.find v ce1 ->
       inferWidth_sstmt_sem (Snode v e) wm0 wm1 ce0 ce1
   | inferWidth_swire_exp v t ce0 ce1 wm :
       ~~ is_deftyp (t) ->
       CE.find (v) ce0 = Some (aggr_typ t, Wire) ->
       (* CE.find v wm = None -> *)
       new_comp_name v ->
       CE.find v ce0 = CE.find v ce1 ->
       inferWidth_sstmt_sem (Swire v t) wm wm ce0 ce1
   | inferWidth_swire_imp v t ce0 ce1 wm0 wm1 :
       is_deftyp t ->
       CE.find (v) ce0 = Some (aggr_typ t, Wire) ->
       (* CE.find v wm0 = None -> *)
       new_comp_name v ->
       CE.find v wm1 = Some t ->
       CE.find v ce0 = CE.find v ce1 ->
       inferWidth_sstmt_sem (Swire v t) wm0 wm1 ce0 ce1
   | inferWidth_sreg_exp v r ce0 ce1 wm :
       ~~ is_deftyp (type r) ->
       CE.find (v) ce0 = Some (reg_typ r, Register) ->
       (* CE.find v wm = None -> *)
       new_comp_name v ->
       CE.find v ce0 = CE.find v ce1 ->
       inferWidth_sstmt_sem (Sreg v r) wm wm ce0 ce1
   | inferWidth_sreg_imp v r ce0 ce1 wm0 wm1 :
       is_deftyp (type r) ->
       CE.find (v) ce0 = Some (reg_typ r, Register) ->
       (* CE.find v wm0 = None -> *)
       new_comp_name v ->
       CE.find v wm1 = Some (type r) ->
       CE.find v ce0 = CE.find v ce1 ->
       inferWidth_sstmt_sem (Sreg v r) wm0 wm1 ce0 ce1
   | inferWidth_sfcnct_gtyp_gt v e c t0 t1 t2 ce0 ce1 wm0 wm1 :
       CE.find v wm0 = Some (Gtyp t1) ->
       CE.find v wm1 = Some (Gtyp t2) ->
       type_of_hfexpr e ce0 = Gtyp t2 ->
       CE.find v ce0 = Some (aggr_typ (Gtyp t0), c) ->
       is_deftyp (Gtyp t0) ->
       CE.find v ce1 = Some (aggr_typ (Gtyp t2), c) ->
       sizeof_fgtyp t1 < sizeof_fgtyp t2 ->
       inferWidth_sstmt_sem (Sfcnct ((eid v)) e) wm0 wm1 ce0 ce1
   | inferWidth_sfcnct_gtyp_le v e c t0 t1 t2 ce0 ce1 wm0 wm1 :
       CE.find v wm0 = Some (Gtyp t1) ->
       CE.find v wm1 = Some (Gtyp t1) ->
       type_of_hfexpr e ce0 = Gtyp t2 ->
       CE.find v ce0 = Some (aggr_typ (Gtyp t0), c) ->
       is_deftyp (Gtyp t0)->
       CE.find v ce1 = Some (aggr_typ (Gtyp t1), c) ->
       sizeof_fgtyp t2 <= sizeof_fgtyp t1 ->
       inferWidth_sstmt_sem (Sfcnct ((eid v)) e) wm0 wm1 ce0 ce1
   | inferWidth_sfcnct_ftype_gt r e t0 t1 t3 c ce0 ce1 wm0 wm1 :
       CE.find (base_ref r) wm0 = Some t1 ->
       CE.find (base_ref r) wm1 = Some (type_of_cmpnttyp t3) ->
       type_of_hfexpr e ce0 = type_of_cmpnttyp t3 ->
       CE.vtyp (base_ref r) ce0 = (t0, c) ->
       is_deftyp (type_of_cmpnttyp t0) ->
       CE.vtyp (base_ref r) ce1 = (t3, c) ->
       ~~ typeConstraintsGe t1 (type_of_cmpnttyp t3) ->
       inferWidth_sstmt_sem (Sfcnct r e) wm0 wm1 ce0 ce1
   | inferWidth_sfcnct_ftype_le r e t0 t1 t3 c ce0 ce1 wm0 wm1 :
       CE.find (base_ref r) wm0 = Some (type_of_cmpnttyp t1) ->
       CE.find (base_ref r) wm1 = Some (type_of_cmpnttyp t1) ->
       type_of_hfexpr e ce0 = t3 ->
       CE.vtyp (base_ref r) ce0 = (t0, c) ->
       is_deftyp (type_of_cmpnttyp t0) ->
       CE.vtyp (base_ref r) ce1 = (t1, c) ->
       typeConstraintsGe (type_of_cmpnttyp t1) (t3) ->
       inferWidth_sstmt_sem (Sfcnct r e) wm0 wm1 ce0 ce1
   | inferWidth_spcnct_ftype_gt r e t0 t1 t3 c ce0 ce1 wm0 wm1 :
       CE.find (base_ref r) wm0 = Some t1 ->
       CE.find (base_ref r) wm1 = Some (type_of_cmpnttyp t3) ->
       type_of_hfexpr e ce0 = type_of_cmpnttyp t3 ->
       CE.vtyp (base_ref r) ce0 = (t0, c) ->
       is_deftyp (type_of_cmpnttyp t0) ->
       CE.vtyp (base_ref r) ce1 = (t3, c) ->
       ~~ typeConstraintsGe t1 (type_of_cmpnttyp t3) ->
       inferWidth_sstmt_sem (Spcnct r e) wm0 wm1 ce0 ce1
   | inferWidth_spcnct_ftype_le r e t0 t1 t3 c ce0 ce1 wm0 wm1 :
       CE.find (base_ref r) wm0 = Some (type_of_cmpnttyp t1) ->
       CE.find (base_ref r) wm1 = Some (type_of_cmpnttyp t1) ->
       type_of_hfexpr e ce0 = t3 ->
       CE.vtyp (base_ref r) ce0 = (t0, c) ->
       is_deftyp (type_of_cmpnttyp t0) ->
       CE.vtyp (base_ref r) ce1 = (t1, c) ->
       typeConstraintsGe (type_of_cmpnttyp t1) (t3) ->
       inferWidth_sstmt_sem (Spcnct r e) wm0 wm1 ce0 ce1
   | inferWidth_sfcnct_tmp r e t0 wm0 wm1 ce0 ce1 :
       type_of_ref r ce0 = t0 ->
       wm0 = wm1 -> ce0 = ce1 ->
       ~~ is_deftyp t0 ->
       inferWidth_sstmt_sem (Sfcnct r e) wm0 wm1 ce0 ce1
   .

   Lemma inferWidth_snode_sem_conform :
     forall v e wm0 ce0 wm1 ce1 ce2,
       inferType_stmt (Snode v e) ce0 ce1 ->
       (* CE.find v wm0 = None -> *)
       new_comp_name v ->
       wm1 = inferWidth_wmap0 (Snode v e) ce1 wm0 ->
       ce2 = wmap_map2_cenv wm1 ce1 ->
       inferWidth_sstmt_sem (Snode v e) wm0 wm1 ce1 ce2.
   Proof.
     intros. rewrite H2/= H1.
     move : H1.
     move : (new_v_wmap_none H0 wm0) => Hn.
     rewrite /= Hn => Heqw01.
     have Hnone : (add_width_2_cenv None None = None) by done.
     move : (CELemmas.map2_1bis wm1 ce1 v Hnone).
     rewrite Heqw01 /=.
     move : Heqw01; case Hdf : (is_deftyp (type_of_hfexpr e ce1)).
     - move => Hwm1.
       move : (CELemmas.add_eq_o wm0 (type_of_hfexpr e ce1) (eq_refl v)) => Hwm01.
       rewrite Hwm01 -Hwm1 -/(wmap_map2_cenv wm1 ce1) -H2.
       inversion H. 
       move => Ht01. 
       apply inferWidth_snode_imp; try done.
       rewrite -H5//.
       rewrite Hwm1 (CELemmas.add_eq_o _ _ (eq_refl v))//.
       rewrite Ht01 H8 /add_width_2_cenv/= H5 Hdf//.
     - move => Hwm01.
       rewrite Hn -/(wmap_map2_cenv wm0 ce1) -Hwm01 -H2/= => Hce01.
       apply inferWidth_snode_exp; [ | rewrite(negbT Hdf)//|done | done ].
       rewrite -Hce01 H2 /wmap_map2_cenv (CELemmas.map2_1bis _ _ _ Hnone).
       rewrite Hwm01 Hn/=.
       inversion H. rewrite -H5 //.
   Qed.

   Lemma inferWidth_swire_exp_sem_conform :
     forall v t wm1 ce1 wm2 ce2 ce3,
       ~~ is_deftyp t ->
       inferType_stmt (Swire v t) ce1 ce2 ->
       (* CE.find v wm0 = None -> *)
       new_comp_name v ->
       wm2 = inferWidth_wmap0 (Swire v t) ce1 wm1 ->
       ce3 = wmap_map2_cenv wm2 ce2 ->
       inferWidth_sstmt_sem (Swire v t) wm1 wm2 ce2 ce3.
   Proof.
     intros. rewrite H2/=.
     move : (new_v_wmap_none H1 wm1) => Hn.
     move : H2. rewrite /= (negbTE H) => Heqw12.
     have Hnone : (add_width_2_cenv None None = None) by done.
     move : (CELemmas.map2_1bis wm1 ce2 v Hnone).
     rewrite Hn /=. rewrite -/(wmap_map2_cenv wm1 ce2) -Heqw12 -H3.
     move => Hfeq. symmetry in Hfeq.
     apply inferWidth_swire_exp; [ done | | done |done].
     inversion H0; subst. done.
   Qed.

   Lemma inferWidth_swire_imp_sem_conform :
     forall v t wm1 ce1 wm2 ce2 ce3,
       is_deftyp t ->
       inferType_stmt (Swire v t) ce1 ce2 ->
       (* CE.find v wm0 = None -> *)
       new_comp_name v ->
       wm2 = inferWidth_wmap0 (Swire v t) ce1 wm1 ->
       ce3 = wmap_map2_cenv wm2 ce2 ->
       inferWidth_sstmt_sem (Swire v t) wm1 wm2 ce2 ce3.
   Proof.
     intros.
     move : (new_v_wmap_none H1 wm1) => Hn.
     rewrite H2 /= H Hn.
     move : H2. rewrite /= H Hn => Hw2.
     inversion H0; subst.
     apply inferWidth_swire_imp; [done| done|done | |].
     - exact : (CELemmas.add_eq_o _ _ (eq_refl v)).
     -
       rewrite /wmap_map2_cenv.
       have Hnone : (add_width_2_cenv None None = None) by done.
       rewrite (CELemmas.map2_1bis _ _ _ Hnone) .
       rewrite (CELemmas.add_eq_o _ _ (eq_refl v)) H8.
       inversion H0; subst. rewrite /add_width_2_cenv/=.
       case (is_deftyp t); done.
   Qed.

   Lemma inferWidth_swire_sem_conform :
     forall v t wm1 ce1 wm2 ce2 ce3,
       inferType_stmt (Swire v t) ce1 ce2 ->
       (* CE.find v wm0 = None -> *)
       new_comp_name v ->
       wm2 = inferWidth_wmap0 (Swire v t) ce1 wm1 ->
       ce3 = wmap_map2_cenv wm2 ce2 ->
       inferWidth_sstmt_sem (Swire v t) wm1 wm2 ce2 ce3.
   Proof.
     intros.
     case Hdf : (is_deftyp t).
     apply inferWidth_swire_imp_sem_conform with ce1; try done.
     apply inferWidth_swire_exp_sem_conform with ce1; try done.
     rewrite Hdf//.
   Qed.

   Lemma inferWidth_sreg_exp_sem_conform :
     forall v r wm1 ce1 wm2 ce2 ce3,
       ~~ is_deftyp (type r) ->
       inferType_stmt (Sreg v r) ce1 ce2 ->
       (* CE.find v wm0 = None -> *)
       new_comp_name v ->
       wm2 = inferWidth_wmap0 (Sreg v r) ce1 wm1 ->
       ce3 = wmap_map2_cenv wm2 ce2 ->
       inferWidth_sstmt_sem (Sreg v r) wm1 wm2 ce2 ce3.
   Proof.
     intros. rewrite H2. 
     move : H2.
     move : (new_v_wmap_none H1 wm1) => Hn.
     rewrite/= Hn (negbTE H) => Heqw12.
     have Hnone : (add_width_2_cenv None None = None) by done.
     move : (CELemmas.map2_1bis wm1 ce2 v Hnone).
     rewrite Hn /=. rewrite -/(wmap_map2_cenv wm1 ce2) -Heqw12 -H3.
     move => Hfeq. symmetry in Hfeq.
     apply inferWidth_sreg_exp; [ done | | done |done].
     inversion H0; subst.
     done.
   Qed.

   Lemma inferWidth_sreg_imp_sem_conform :
     forall v r wm1 ce1 wm2 ce2 ce3,
       is_deftyp (type r) ->
       inferType_stmt (Sreg v r) ce1 ce2 ->
       (* CE.find v wm1 = None -> *)
       new_comp_name v ->
       wm2 = inferWidth_wmap0 (Sreg v r) ce1 wm1 ->
       ce3 = wmap_map2_cenv wm2 ce2 ->
       inferWidth_sstmt_sem (Sreg v r) wm1 wm2 ce2 ce3.
   Proof.
     intros.
     move : (new_v_wmap_none H1 wm1) => Hn.
     rewrite H2 /= H Hn.
     move : H2. rewrite /= H Hn => Hw2.
     inversion H0; subst.
     apply inferWidth_sreg_imp; [ done| done| done| |].
     - exact : (CELemmas.add_eq_o _ _ (eq_refl v)).
     - rewrite  /wmap_map2_cenv.
       have Hnone : (add_width_2_cenv None None = None) by done.
       rewrite (CELemmas.map2_1bis _ _ _ Hnone) .
       rewrite (CELemmas.add_eq_o _ _ (eq_refl v)) H8.
       rewrite /add_width_2_cenv/=.
       case (is_deftyp (type r)). case r; done.
       done.
   Qed.

   Lemma inferWidth_sreg_sem_conform :
     forall v t wm1 ce1 wm2 ce2 ce3,
       inferType_stmt (Sreg v t) ce1 ce2 ->
       (* CE.find v wm1 = None -> *)
       new_comp_name v ->
       wm2 = inferWidth_wmap0 (Sreg v t) ce1 wm1 ->
       ce3 = wmap_map2_cenv wm2 ce2 ->
       inferWidth_sstmt_sem (Sreg v t) wm1 wm2 ce2 ce3.
   Proof.
     intros.
     case Hdf : (is_deftyp (type t)).
     apply inferWidth_sreg_imp_sem_conform with ce1; try done.
     apply inferWidth_sreg_exp_sem_conform with ce1; try done.
     rewrite Hdf//.
   Qed.

   Lemma inferWidth_smem_sem_conform :
     forall v m wm1 ce1 wm2 ce2 ce3,
       inferType_stmt (Smem v m) ce1 ce2 ->
       (* CE.find v wm1 = None -> *)
       new_comp_name v ->
       wm2 = inferWidth_wmap0 (Smem v m) ce1 wm1 ->
       ce3 = wmap_map2_cenv wm2 ce2 ->
       inferWidth_sstmt_sem (Smem v m) wm1 wm2 ce2 ce3.
   Proof.
     intros.
     rewrite H2 H1/=.
     apply inferWidth_smem; try done.
     intros.
     rewrite /wmap_map2_cenv.
     have Hnone : (add_width_2_cenv None None = None) by done.
     rewrite (CELemmas.map2_1bis _ _ _ Hnone) (new_v_wmap_none H0 wm1)/=.
     done.
   Qed.

   Lemma inferWidth_sinst_sem_conform :
     forall v m wm1 ce1 wm2 ce2 ce3,
       inferType_stmt (Sinst v m) ce1 ce2 ->
       (* CE.find v wm1 = None -> *)
       new_comp_name v ->
       wm2 = inferWidth_wmap0 (Sinst v m) ce1 wm1 ->
       ce3 = wmap_map2_cenv wm2 ce2 ->
       inferWidth_sstmt_sem (Sinst v m) wm1 wm2 ce2 ce3.
   Proof.
     intros.
     rewrite H2 H1/=.
     apply inferWidth_sinst; try done.
     intros.
     rewrite /wmap_map2_cenv.
     have Hnone : (add_width_2_cenv None None = None) by done.
     rewrite (CELemmas.map2_1bis _ _ _ Hnone) (new_v_wmap_none H0 wm1)/=.
     done. 
   Qed.
   
   Lemma sizeof_fgtyp_lt_max_width t1 t2 :
     ftype_equiv (Gtyp t1) (Gtyp t2) ->
     sizeof_fgtyp t1 <= sizeof_fgtyp t2 ->
     max_width (Gtyp t1) (Gtyp t2) = Gtyp t2.
   Proof.
     elim t1; elim t2; rewrite /=; intros;
       try (rewrite (maxn_idPr H0)//|| discriminate|| done).
   Qed.

   Lemma typeConstraints_max_width t1 t2 :
     ftype_equiv t1 t2 ->
     typeConstraintsGe t1 t2 ->
     max_width t1 t2 = t1.
   Proof.
     elim t1; elim t2; rewrite /=; intros; try discriminate.
     - move : H H0. rewrite/typeConstraintsGe/=.
       elim f ; elim f0; try (intros; rewrite (maxn_idPr H0)//||discriminate||done).
   Admitted.

   Lemma max_width_typeConstraints t1 t2 : 
     ftype_equiv t1 t2 ->
     max_width t1 t2 = t1 ->
     typeConstraintsGe t1 t2.
   Proof. Admitted.
     
   Lemma neg_typeConstraints_max_width t1 t2 :
     ftype_equiv t1 t2 ->
     ~~ (typeConstraintsGe t1 t2) ->
     max_width t1 t2 = t2.
   Proof.
   Admitted.
     
   Lemma ftype_equiv_symmetry t1 t2 :
     ftype_equiv (t1) (t2) -> ftype_equiv (t2) (t1)
   with ffield_equiv_symmetry f1 f2 :
          fbtyp_equiv f1 f2 -> fbtyp_equiv f2 f1.
   Proof.
     elim: t1 t2 => [f1| f1 H1 n1| n1 ]  [f2| f2 n2| n2 ]//.
     - elim: f1 f2; try done.
     - rewrite /= => /andP [Heq Hfeq]. rewrite (eqP Heq)/= eq_refl andTb.
         by apply H1.
     - rewrite /=. apply ffield_equiv_symmetry.
     elim: f1 f2 => [|v1 flp1 f1 fs1 IH1 ] [|v2 flp2 f2 fs2 ] .
     - done.
     - rewrite /=//.
     - rewrite /=; case flp1; done.
     - elim: flp1 flp2 => [|] [|] /=//.
       + move => /andP [/andP [Heq Heqf] Heqb].
         rewrite (eqP Heq) eq_refl andTb.
         apply /andP. split.
         by apply ftype_equiv_symmetry.
         exact : (IH1 fs2 Heqb).
       + move => /andP [/andP [Heq Heqf] Heqb].
         rewrite (eqP Heq) eq_refl andTb.
         apply /andP. split.
         by apply ftype_equiv_symmetry.
         exact : (IH1 fs2 Heqb).
   Qed.

   Lemma max_width_symmetry t1 t2 :
     max_width (t1) (t2) = max_width (t2) (t1).
   Proof.
   Admitted.

   Lemma add_ref_wmap0_max_width r t1 t2 ce wm :
     CE.find (base_ref r) wm = Some t1 ->
     CE.find (base_ref r) (add_ref_wmap0 r t2 ce wm) = Some (max_width t1 t2).
   Proof. Admitted.
   
   Lemma inferWidth_sfcnct_ftype_sem_conform :
     forall r e c1 t0 t1 t2 wm1 ce1 wm2 ce2 ,
       ftype_equiv t1 t2 ->
       CE.find (base_ref r) ce1 =  Some (t0, c1) ->
       type_of_ref r ce1 = type_of_cmpnttyp t0 ->
       is_deftyp (type_of_cmpnttyp t0) ->
       type_of_hfexpr e ce1 = t2 ->
       CE.find (base_ref r) wm1 = Some t1 ->
       wm2 = inferWidth_wmap0 (Sfcnct r e) ce1 wm1 ->
       ce2 = wmap_map2_cenv wm2 ce1 ->
       ~~ find_unknown (base_ref r) ce1  ->
       inferWidth_sstmt_sem (Sfcnct r e) wm1 wm2 ce1 ce2.
   Proof.
     intros. rewrite H6 H5 /= H1 H3 H2.
     have Hnone : (add_width_2_cenv None None = None) by done.
     move : (CE.find_some_vtyp H0) => Hv.
     move : H0 H1 H2 Hv.
     case : t0; rewrite /= ; intros.
     - case Hmax : (typeConstraintsGe t1 t2).
       + move : (typeConstraints_max_width H Hmax) => Hmw.
         move : H3 H5.
         case e; intros;
           try (apply inferWidth_sfcnct_ftype_le with (aggr_typ f) (aggr_typ t1) t2 c1;
                [ done
                | rewrite -Hmw (add_ref_wmap0_max_width _ _ H4) /=Hmw//
                | done| done| done
                | apply (CE.find_some_vtyp);
                  rewrite /wmap_map2_cenv/= (CELemmas.map2_1bis _ _ _ Hnone);
                  rewrite (add_ref_wmap0_max_width _ _ H4) H0/= H2 Hmw//
                | done]).
         rewrite /= in H3; rewrite H3.
         apply inferWidth_sfcnct_ftype_le with (aggr_typ f) (aggr_typ t1) t2 c1; try done.
         rewrite (add_ref_wmap0_max_width _ _ H4)/= Hmw//.
         apply CE.find_some_vtyp.
         rewrite /wmap_map2_cenv /=(CELemmas.map2_1bis _ _ _ Hnone) (add_ref_wmap0_max_width _ _ H4).
         rewrite Hmw H0/= H2//.
       + move : (neg_typeConstraints_max_width H (negbT Hmax)) => Hmw.
         move : H3 H5.
         case e; intros; 
         try (apply inferWidth_sfcnct_ftype_gt with (aggr_typ f) t1 (aggr_typ t2) c1;
              [ done
              | rewrite (add_ref_wmap0_max_width _ _ H4) Hmw//
              | done| done | done
              | apply CE.find_some_vtyp; rewrite /wmap_map2_cenv(CELemmas.map2_1bis _ _ _ Hnone);
                  rewrite (add_ref_wmap0_max_width _ _ H4) H0/= H2 Hmw//
              | rewrite Hmax//]).
         rewrite /= in H3; rewrite H3.
         apply inferWidth_sfcnct_ftype_gt with (aggr_typ f) t1 (aggr_typ t2) c1; try done.
         rewrite (add_ref_wmap0_max_width _ _ H4)/= Hmw//.
         apply CE.find_some_vtyp. rewrite /wmap_map2_cenv (CELemmas.map2_1bis _ _ _ Hnone).
         rewrite (add_ref_wmap0_max_width _ _ H4) H0/= H2 Hmw//.
         rewrite /= Hmax//.
     - case Hmax : (typeConstraintsGe t1 t2).
       + move : (typeConstraints_max_width H Hmax) => Hmw.
         move : H3 H5.
         case e; intros;
            try (apply inferWidth_sfcnct_ftype_le with (reg_typ h) (reg_typ (mk_freg t1 (clock h) (reset h))) t2 c1;
                [ done
                | rewrite -Hmw (add_ref_wmap0_max_width _ _ H4) /=Hmw//
                | done| done| done
                | apply (CE.find_some_vtyp);
                  rewrite /wmap_map2_cenv/= (CELemmas.map2_1bis _ _ _ Hnone);
                  rewrite (add_ref_wmap0_max_width _ _ H4) H0/= H2 Hmw//
                | done]).
         rewrite /= in H3; rewrite H3.
         apply inferWidth_sfcnct_ftype_le with (reg_typ h) (reg_typ (mk_freg t1 (clock h) (reset h))) t2 c1; try done.
         rewrite (add_ref_wmap0_max_width _ _ H4)/= Hmw//.
         apply CE.find_some_vtyp.
         rewrite /wmap_map2_cenv /=(CELemmas.map2_1bis _ _ _ Hnone) (add_ref_wmap0_max_width _ _ H4).
         rewrite Hmw H0/= H2//.
       + move : (neg_typeConstraints_max_width H (negbT Hmax)) => Hmw.
         move : H3 H5.
         case e; intros; 
           try (apply inferWidth_sfcnct_ftype_gt with (reg_typ h) t1 (reg_typ (mk_freg t2 (clock h) (reset h))) c1;
                [ done
                | rewrite (add_ref_wmap0_max_width _ _ H4) Hmw//
                | done| done | done
                | apply CE.find_some_vtyp; rewrite /wmap_map2_cenv(CELemmas.map2_1bis _ _ _ Hnone);
                  rewrite (add_ref_wmap0_max_width _ _ H4) H0/= H2 Hmw//
                | rewrite Hmax//]).
         rewrite /= in H3; rewrite H3.
         apply inferWidth_sfcnct_ftype_gt with (reg_typ h) t1 (reg_typ (mk_freg t2 (clock h) (reset h))) c1; try done.
         rewrite (add_ref_wmap0_max_width _ _ H4)/= Hmw//.
         apply CE.find_some_vtyp. rewrite /wmap_map2_cenv (CELemmas.map2_1bis _ _ _ Hnone).
         rewrite (add_ref_wmap0_max_width _ _ H4) H0/= H2 Hmw//.
         rewrite /= Hmax//.
     - case Hmax : (typeConstraintsGe t1 t2).
       + move : (typeConstraints_max_width H Hmax) => Hmw.
         move : H3 H5.
         case e; intros; 
         try (apply inferWidth_sfcnct_ftype_le with
             (mem_typ h) (mem_typ (mk_fmem t1 (depth h) (reader h) (writer h) (read_latency h) (write_latency h) (read_write h))) t2 c1; 
                [ done
                | rewrite -Hmw (add_ref_wmap0_max_width _ _ H4) /=Hmw//
                | done| done| done
                | apply (CE.find_some_vtyp);
                  rewrite /wmap_map2_cenv (CELemmas.map2_1bis _ _ _ Hnone);
                  rewrite (add_ref_wmap0_max_width _ _ H4) H0/= H2 Hmw//
                | done]).
         rewrite /= in H3; rewrite H3.
         apply inferWidth_sfcnct_ftype_le with (mem_typ h) (mem_typ (mk_fmem t1 (depth h) (reader h) (writer h) (read_latency h) (write_latency h) (read_write h))) t2 c1; try done.
         rewrite (add_ref_wmap0_max_width _ _ H4)/= Hmw//.
         apply CE.find_some_vtyp. rewrite /wmap_map2_cenv (CELemmas.map2_1bis _ _ _ Hnone).
         rewrite (add_ref_wmap0_max_width _ _ H4) H0/= H2 Hmw//.
       + move : (neg_typeConstraints_max_width H (negbT Hmax)) => Hmw.
         move : H3 H5.
         case e; intros; 
           try (apply inferWidth_sfcnct_ftype_gt with (mem_typ h) t1 (mem_typ (mk_fmem t2 (depth h) (reader h) (writer h) (read_latency h) (write_latency h) (read_write h))) c1;
                [ done
                | rewrite (add_ref_wmap0_max_width _ _ H4) Hmw//
                | done| done | done
                | apply CE.find_some_vtyp; rewrite /wmap_map2_cenv(CELemmas.map2_1bis _ _ _ Hnone);
                  rewrite (add_ref_wmap0_max_width _ _ H4) H0/= H2 Hmw//
                | rewrite Hmax//]).
         rewrite /= in H3; rewrite H3.
         apply inferWidth_sfcnct_ftype_gt with (mem_typ h) t1 (mem_typ (mk_fmem t2 (depth h) (reader h) (writer h) (read_latency h) (write_latency h) (read_write h))) c1; try done.
         rewrite (add_ref_wmap0_max_width _ _ H4)/= Hmw//.
         apply CE.find_some_vtyp. rewrite /wmap_map2_cenv (CELemmas.map2_1bis _ _ _ Hnone).
         rewrite (add_ref_wmap0_max_width _ _ H4) H0/= H2 Hmw//.
         rewrite /= Hmax//.
     - rewrite /find_unknown H0 in H7.  discriminate.
   Qed.

   Lemma inferWidth_spcnct_ftype_sem_conform :
     forall r e c1 t0 t1 t2 wm1 ce1 wm2 ce2 ,
       ftype_weak_equiv t1 t2 ->
       CE.find (base_ref r) ce1 =  Some (t0, c1) ->
       type_of_ref r ce1 = type_of_cmpnttyp t0 ->
       is_deftyp (type_of_cmpnttyp t0) ->
       type_of_hfexpr e ce1 = t2 ->
       CE.find (base_ref r) wm1 = Some t1 ->
       wm2 = inferWidth_wmap0 (Spcnct r e) ce1 wm1 ->
       ce2 = wmap_map2_cenv wm2 ce1 ->
       ~~ find_unknown (base_ref r) ce1 ->
       inferWidth_sstmt_sem (Spcnct r e) wm1 wm2 ce1 ce2.
   Proof.
     intros. rewrite H6 H5 /= H1 H3 H2.
     have Hnone : (add_width_2_cenv None None = None) by done.
     move : (CE.find_some_vtyp H0) => Hv.
     move : H0 H1 H2 Hv.
     case : t0; rewrite /= ; intros.
     - case Hmax : (typeConstraintsGe t1 t2).
       + move : (typeConstraints_max_width H Hmax) => Hmw.
         move : H3 H5.
         case e; intros;
           try (apply inferWidth_spcnct_ftype_le with (aggr_typ f) (aggr_typ t1) t2 c1;
                [ done
                | rewrite -Hmw (add_ref_wmap0_max_width _ _ H4) /=Hmw//
                | done| done| done
                | apply (CE.find_some_vtyp);
                  rewrite /wmap_map2_cenv/= (CELemmas.map2_1bis _ _ _ Hnone);
                  rewrite (add_ref_wmap0_max_width _ _ H4) H0/= H2 Hmw//
                | done]).
         rewrite /= in H3; rewrite H3.
         apply inferWidth_spcnct_ftype_le with (aggr_typ f) (aggr_typ t1) t2 c1; try done.
         rewrite (add_ref_wmap0_max_width _ _ H4)/= Hmw//.
         apply CE.find_some_vtyp.
         rewrite /wmap_map2_cenv /=(CELemmas.map2_1bis _ _ _ Hnone) (add_ref_wmap0_max_width _ _ H4).
         rewrite Hmw H0/= H2//.
       + move : (neg_typeConstraints_max_width H (negbT Hmax)) => Hmw.
         move : H3 H5.
         case e; intros; 
         try (apply inferWidth_spcnct_ftype_gt with (aggr_typ f) t1 (aggr_typ t2) c1;
              [ done
              | rewrite (add_ref_wmap0_max_width _ _ H4) Hmw//
              | done| done | done
              | apply CE.find_some_vtyp; rewrite /wmap_map2_cenv(CELemmas.map2_1bis _ _ _ Hnone);
                  rewrite (add_ref_wmap0_max_width _ _ H4) H0/= H2 Hmw//
              | rewrite Hmax//]).
         rewrite /= in H3; rewrite H3.
         apply inferWidth_spcnct_ftype_gt with (aggr_typ f) t1 (aggr_typ t2) c1; try done.
         rewrite (add_ref_wmap0_max_width _ _ H4)/= Hmw//.
         apply CE.find_some_vtyp. rewrite /wmap_map2_cenv (CELemmas.map2_1bis _ _ _ Hnone).
         rewrite (add_ref_wmap0_max_width _ _ H4) H0/= H2 Hmw//.
         rewrite /= Hmax//.
     - case Hmax : (typeConstraintsGe t1 t2).
       + move : (typeConstraints_max_width H Hmax) => Hmw.
         move : H3 H5.
         case e; intros;
            try (apply inferWidth_spcnct_ftype_le with (reg_typ h) (reg_typ (mk_freg t1 (clock h) (reset h))) t2 c1;
                [ done
                | rewrite -Hmw (add_ref_wmap0_max_width _ _ H4) /=Hmw//
                | done| done| done
                | apply (CE.find_some_vtyp);
                  rewrite /wmap_map2_cenv/= (CELemmas.map2_1bis _ _ _ Hnone);
                  rewrite (add_ref_wmap0_max_width _ _ H4) H0/= H2 Hmw//
                | done]).
         rewrite /= in H3; rewrite H3.
         apply inferWidth_spcnct_ftype_le with (reg_typ h) (reg_typ (mk_freg t1 (clock h) (reset h))) t2 c1; try done.
         rewrite (add_ref_wmap0_max_width _ _ H4)/= Hmw//.
         apply CE.find_some_vtyp.
         rewrite /wmap_map2_cenv /=(CELemmas.map2_1bis _ _ _ Hnone) (add_ref_wmap0_max_width _ _ H4).
         rewrite Hmw H0/= H2//.
       + move : (neg_typeConstraints_max_width H (negbT Hmax)) => Hmw.
         move : H3 H5.
         case e; intros; 
           try (apply inferWidth_spcnct_ftype_gt with (reg_typ h) t1 (reg_typ (mk_freg t2 (clock h) (reset h))) c1;
                [ done
                | rewrite (add_ref_wmap0_max_width _ _ H4) Hmw//
                | done| done | done
                | apply CE.find_some_vtyp; rewrite /wmap_map2_cenv(CELemmas.map2_1bis _ _ _ Hnone);
                  rewrite (add_ref_wmap0_max_width _ _ H4) H0/= H2 Hmw//
                | rewrite Hmax//]).
         rewrite /= in H3; rewrite H3.
         apply inferWidth_spcnct_ftype_gt with (reg_typ h) t1 (reg_typ (mk_freg t2 (clock h) (reset h))) c1; try done.
         rewrite (add_ref_wmap0_max_width _ _ H4)/= Hmw//.
         apply CE.find_some_vtyp. rewrite /wmap_map2_cenv (CELemmas.map2_1bis _ _ _ Hnone).
         rewrite (add_ref_wmap0_max_width _ _ H4) H0/= H2 Hmw//.
         rewrite /= Hmax//.
     - case Hmax : (typeConstraintsGe t1 t2).
       + move : (typeConstraints_max_width H Hmax) => Hmw.
         move : H3 H5.
         case e; intros; 
         try (apply inferWidth_spcnct_ftype_le with
             (mem_typ h) (mem_typ (mk_fmem t1 (depth h) (reader h) (writer h) (read_latency h) (write_latency h) (read_write h))) t2 c1; 
                [ done
                | rewrite -Hmw (add_ref_wmap0_max_width _ _ H4) /=Hmw//
                | done| done| done
                | apply (CE.find_some_vtyp);
                  rewrite /wmap_map2_cenv (CELemmas.map2_1bis _ _ _ Hnone);
                  rewrite (add_ref_wmap0_max_width _ _ H4) H0/= H2 Hmw//
                | done]).
         rewrite /= in H3; rewrite H3.
         apply inferWidth_spcnct_ftype_le with (mem_typ h) (mem_typ (mk_fmem t1 (depth h) (reader h) (writer h) (read_latency h) (write_latency h) (read_write h))) t2 c1; try done.
         rewrite (add_ref_wmap0_max_width _ _ H4)/= Hmw//.
         apply CE.find_some_vtyp. rewrite /wmap_map2_cenv (CELemmas.map2_1bis _ _ _ Hnone).
         rewrite (add_ref_wmap0_max_width _ _ H4) H0/= H2 Hmw//.
       + move : (neg_typeConstraints_max_width H (negbT Hmax)) => Hmw.
         move : H3 H5.
         case e; intros; 
           try (apply inferWidth_spcnct_ftype_gt with (mem_typ h) t1 (mem_typ (mk_fmem t2 (depth h) (reader h) (writer h) (read_latency h) (write_latency h) (read_write h))) c1;
                [ done
                | rewrite (add_ref_wmap0_max_width _ _ H4) Hmw//
                | done| done | done
                | apply CE.find_some_vtyp; rewrite /wmap_map2_cenv(CELemmas.map2_1bis _ _ _ Hnone);
                  rewrite (add_ref_wmap0_max_width _ _ H4) H0/= H2 Hmw//
                | rewrite Hmax//]).
         rewrite /= in H3; rewrite H3.
         apply inferWidth_spcnct_ftype_gt with (mem_typ h) t1 (mem_typ (mk_fmem t2 (depth h) (reader h) (writer h) (read_latency h) (write_latency h) (read_write h))) c1; try done.
         rewrite (add_ref_wmap0_max_width _ _ H4)/= Hmw//.
         apply CE.find_some_vtyp. rewrite /wmap_map2_cenv (CELemmas.map2_1bis _ _ _ Hnone).
         rewrite (add_ref_wmap0_max_width _ _ H4) H0/= H2 Hmw//.
         rewrite /= Hmax//.
     - rewrite /find_unknown H0 in H7. discriminate.
   Qed.

   
   Lemma inferWidth_sfcnct_sem_conform :
     forall v1 e c1 t0 t1 t2 wm1 ce1 wm2 ce2 ,
       ftype_equiv (Gtyp t1) (Gtyp t2) ->
       CE.find v1 ce1 = Some (aggr_typ (Gtyp t0), c1) ->
       is_deftyp (Gtyp t0) ->
       type_of_hfexpr e ce1 = (Gtyp t2) ->
       CE.find v1 wm1 = Some (Gtyp t1) ->
       wm2 = inferWidth_wmap0 (Sfcnct (eid v1) e) ce1 wm1 ->
       ce2 = wmap_map2_cenv wm2 ce1 ->
       inferWidth_sstmt_sem (Sfcnct (eid v1) e) wm1 wm2 ce1 ce2.
   Proof.
     intros. rewrite H4 /= (CE.find_some_vtyp H0) H1 H3.
     have Hnone : (add_width_2_cenv None None = None) by done.
     case Hmax : (sizeof_fgtyp t2 <= sizeof_fgtyp t1).
     - move : (sizeof_fgtyp_lt_max_width (ftype_equiv_symmetry H) (Hmax)) => Hmw .
       move : H2 H4.
       case He : e => [ct c| c e1 | u e1 | op e1 e2 | c e1 e2 | c e1 | r2 ] H2 H4;
                        try (apply inferWidth_sfcnct_gtyp_le with c1 t0 t1 t2;
                           [done
                           | rewrite H2 Hmw (CELemmas.add_eq_o wm1 _ (eq_refl v1))//
                           | done| done| done
                           | rewrite H5 H4 /wmap_map2_cenv /inferWidth_wmap0 H2;
                             rewrite (lock add_ref_wmap0)/= (CE.find_some_vtyp H0) (lock is_deftyp)/= -!lock H1;
                             rewrite (CELemmas.map2_1bis (add_ref_wmap0 (eid v1) (Gtyp t2) ce1 wm1) ce1 v1 Hnone);
                             rewrite /add_ref_wmap0 (lock max_width) /= -lock H3 Hmw;
                             rewrite (CELemmas.add_eq_o wm1 (Gtyp t1) (eq_refl v1)) H0;
                             rewrite /add_width_2_cenv (lock is_deftyp)/= -lock H1//
                           | done]).
       + rewrite /type_of_hfexpr in H2. rewrite H2.
         apply inferWidth_sfcnct_gtyp_le with c1 t0 t1 t2; try done.
         rewrite Hmw (CELemmas.add_eq_o wm1 (Gtyp t1) (eq_refl v1))//.
         rewrite H5 H4/wmap_map2_cenv /inferWidth_wmap0 H2. 
         rewrite (lock add_ref_wmap0)/= (CE.find_some_vtyp H0) (lock is_deftyp)/= -lock H1/=-lock.
         rewrite /add_ref_wmap0 (lock max_width)/= H3 -lock Hmw.
         rewrite (CELemmas.map2_1bis (CE.add v1 (Gtyp t1) wm1) ce1 v1 Hnone) H0.
         rewrite (CELemmas.add_eq_o wm1 (Gtyp t1) (eq_refl v1)) /add_width_2_cenv (lock is_deftyp)/=.
         rewrite -lock H1//.
     - move : (negbT Hmax). rewrite -ltnNge => Hlt.
       move : (sizeof_fgtyp_lt_max_width H (ltnW Hlt)) => Hmw.
       move : H2 H4.
       case He : e => [ct c| c e1 | u e1 | op e1 e2 | c e1 e2 | c e1 | r2 ] H2 H4;
                        try (apply inferWidth_sfcnct_gtyp_gt with c1 t0 t1 t2;
                           [ done
                           | rewrite H2 max_width_symmetry Hmw (CELemmas.add_eq_o wm1 (Gtyp t2) (eq_refl v1))//
                           | done| done| done
                           | rewrite H5 H4 /wmap_map2_cenv /inferWidth_wmap0 H2;
                             rewrite (lock add_ref_wmap0)/= (CE.find_some_vtyp H0) (lock is_deftyp)/= -!lock H1;
                             rewrite (CELemmas.map2_1bis (add_ref_wmap0 (eid v1) (Gtyp t2) ce1 wm1) ce1 v1 Hnone);
                             rewrite /add_ref_wmap0 (lock max_width) /= -lock H3 max_width_symmetry Hmw;
                             rewrite (CELemmas.add_eq_o wm1 (Gtyp t2) (eq_refl v1)) H0;
                             rewrite /add_width_2_cenv (lock is_deftyp)/= -lock H1//
                           | done]).
       + rewrite /= in H2; rewrite H2.
         apply inferWidth_sfcnct_gtyp_gt with c1 t0 t1 t2; try done.
         rewrite max_width_symmetry Hmw (CELemmas.add_eq_o wm1 (Gtyp t2) (eq_refl v1))//.
         rewrite H5 H4/wmap_map2_cenv /inferWidth_wmap0 H2.
         rewrite (lock add_ref_wmap0)/= (CE.find_some_vtyp H0) (lock is_deftyp)/= -lock H1/=-lock.
         rewrite /add_ref_wmap0 (lock max_width)/= H3 -lock max_width_symmetry Hmw.
         rewrite (CELemmas.map2_1bis (CE.add v1 (Gtyp t2) wm1) ce1 v1 Hnone) H0.
         rewrite (CELemmas.add_eq_o wm1 (Gtyp t2) (eq_refl v1)) /add_width_2_cenv (lock is_deftyp)/=.
         rewrite -lock H1//.
   Qed.

   Lemma inferWidth_sskip_sem_conform :
     forall wm1 wm2 ce1 ce2,
       wm2 = inferWidth_wmap0 sskip ce1 wm1 ->
       ce2 = wmap_map2_cenv wm2 ce1 ->
       inferWidth_sstmt_sem (sskip) wm1 wm2 ce1 ce2.
   Proof.
     move => wm1 wm2 ce1 ce2 H H1. rewrite /= in H.
     apply inferWidth_sskip. intros.
     rewrite H1 H.
     have Hnone : (add_width_2_cenv None None = None) by done.
     rewrite /wmap_map2_cenv (CELemmas.map2_1bis _ _ _ Hnone).
     rewrite H0 H2.
     split. done.
     case t; rewrite /=; intros; try done.
     case (is_deftyp f); done.
     case (is_deftyp (type h)); try done.
     case h; intros; rewrite /=//.
     case (is_deftyp (data_type h)); try done.
     case h; intros; rewrite //.
   Qed.

   Lemma inferWidth_sstop_sem_conform :
     forall wm1 wm2 ce1 ce2 ss1 ss2 n,
       wm2 = inferWidth_wmap0 (sstop ss1 ss2 n) ce1 wm1 ->
       ce2 = wmap_map2_cenv wm2 ce1 ->
       inferWidth_sstmt_sem (sstop ss1 ss2 n) wm1 wm2 ce1 ce2.
   Proof.
     move => wm1 wm2 ce1 ce2 ss1 ss2 n H H1. rewrite /= in H.
     apply inferWidth_sstop. intros.
     rewrite H1 H.
     have Hnone : (add_width_2_cenv None None = None) by done.
     rewrite /wmap_map2_cenv (CELemmas.map2_1bis _ _ _ Hnone).
     rewrite H0 H2.
     split. done.
     case t; rewrite /=; intros; try done.
     case (is_deftyp f); done.
     case (is_deftyp (type h)); try done.
     case h; intros; rewrite /=//.
     case (is_deftyp (data_type h)); try done.
     case h; intros; rewrite //.
   Qed.

   Lemma inferWidth_sinvalid_sem_conform :
     forall wm1 wm2 ce1 ce2 v,
       wm2 = inferWidth_wmap0 (sinvalid v) ce1 wm1 ->
       ce2 = wmap_map2_cenv wm2 ce1 ->
       inferWidth_sstmt_sem (sinvalid v) wm1 wm2 ce1 ce2.
   Proof.
     move => wm1 wm2 ce1 ce2 v H H1. rewrite /= in H.
     apply inferWidth_sinvalid. intros.
     rewrite H1 H.
     have Hnone : (add_width_2_cenv None None = None) by done.
     rewrite /wmap_map2_cenv (CELemmas.map2_1bis _ _ _ Hnone).
     rewrite H0 H2.
     split. done.
     case t; rewrite /=; intros; try done.
     case (is_deftyp f); done.
     case (is_deftyp (type h)); try done.
     case h; intros; rewrite /=//.
     case (is_deftyp (data_type h)); try done.
     case h; intros; rewrite //.
   Qed.

   Lemma inferWidth_swhen_sem_conform_tmp :
     forall wm1 wm2 ce1 ce2 ss1 ss2 n,
       wm2 = inferWidth_wmap0 (swhen ss1 ss2 n) ce1 wm1 ->
       ce2 = wmap_map2_cenv wm2 ce1 ->
       inferWidth_sstmt_sem (swhen ss1 ss2 n) wm1 wm2 ce1 ce2.
   Proof.
     move => wm1 wm2 ce1 ce2 ss1 ss2 n H H1. rewrite /= in H.
     apply inferWidth_swhen. intros.
     rewrite H1 H.
     have Hnone : (add_width_2_cenv None None = None) by done.
     rewrite /wmap_map2_cenv (CELemmas.map2_1bis _ _ _ Hnone).
     rewrite H0 H2.
     split. done.
     case t; rewrite /=; intros; try done.
     case (is_deftyp f); done.
     case (is_deftyp (type h)); try done.
     case h; intros; rewrite /=//.
     case (is_deftyp (data_type h)); try done.
     case h; intros; rewrite //.
   Qed.
   
   Lemma cefind_eq_eq_width :
     forall v (ce1 ce2 : cenv) t1 t2 c,
       CE.find v ce1 = Some (t1, c) ->
       CE.find v ce2 = Some (t2, c) ->
       CE.find v ce1 = CE.find v ce2 ->
       typeConstraintsGe (type_of_cmpnttyp t2) (type_of_cmpnttyp t1).
   Proof.
   Admitted.
     
   Lemma inferWidth_sstmt_sem_conform :
     forall st wm1 wm2 ce1 ce2 
       t1 t2,
           (* CE.find (base_ref r) ce1 = Some (t1, c) -> *)
           (* is_deftyp (type_of_cmpnttyp t1) -> *)
           (* CE.find (base_ref r) ce2 = Some (t2, c) -> *)
       wm2 = inferWidth_wmap0 st ce1 wm1 ->
       ce2 = wmap_map2_cenv wm2 ce1 ->
       inferWidth_sstmt_sem st wm1 wm2 ce1 ce2 ->
       (forall r c,
           ftype_equiv (type_of_cmpnttyp t1) (type_of_cmpnttyp t2) /\
           CE.find (base_ref r) ce1 = Some (t1, c) /\
           CE.find (base_ref r) ce2 = Some (t2, c)) ->
       typeConstraintsGe (type_of_cmpnttyp t2) (type_of_cmpnttyp t1).
   Proof.
   Admitted.

   
   Inductive inferWidth_stmts_sem : seq hfstmt -> cenv -> cenv -> Prop :=
   | inferWidth_stmts_nil ce1 ce2 :
       (forall v,
         CE.find v ce1 = CE.find v ce2) ->
         inferWidth_stmts_sem nil ce1 ce2
   | inferWidth_stmts_imp st sts (ce1 ce2 ce3 : cenv) :
       (forall r  t1 c,
           new_comp_name (base_ref r) /\
           CE.find (base_ref r) ce1 = Some (t1, c) /\
           (* is_deftyp (type_of_cmpnttyp t1) -> *)
           ~~ is_deftyp (type_of_cmpnttyp (fst (CE.vtyp (base_ref r) ce3))) ->
           exists (wm1 wm2 : wmap0),
             inferWidth_sstmt_sem st wm1 wm2 ce1 ce2) ->
       inferWidth_stmts_sem sts ce2 ce3 ->
       inferWidth_stmts_sem (st :: sts) ce1 ce3.

   Lemma infer_stmt_lst st ss ce1 :
     forall wm0 wm1 ,
       wm1 = inferWidth_wmap0 st ce1 wm0 ->
       inferWidth_fun (st :: ss) ce1 = inferWidth_fun ss (wmap_map2_cenv wm1 ce1).
   Proof. Admitted.

   Lemma inferType_stmts_hd ss sts ce0 ce1 :
     inferType_stmts (ss :: sts) ce0 ce1 -> 
     inferType_stmt ss ce0 ce1.
   Proof.
   Admitted.

   Lemma type_of_hexpr_cefind r ce t :
     CE.find (base_ref r) ce = Some t ->
     type_of_ref (r) ce = type_of_cmpnttyp (fst t).
   Proof. Admitted.

   Definition is_inital (s : hfstmt) : bool :=
     match s with
     | Spcnct _ _ | Sfcnct _ _ | Sinvalid _ | Swhen _ _ _
     | Sstop _ _ _ | Sskip => false
     | _ => true
     end.

   Fixpoint is_inital_all_t s : bool :=
     match (s) with
     | nil => true
     | cons h t => if (is_inital h) then is_inital_all_t t else false
     end.

   Fixpoint not_inital_all s : bool :=
     match s with
     | nil => true
     | cons h t => if (is_inital h) then false else not_inital_all t
     end.

   Lemma inferWidth_stmts_inital_sem_conform :
     forall sts ce0 ce1 (v:var),
       (
         exists wm0 wm1,
           forall r t ,
             new_comp_name (base_ref r) /\
             is_inital_all_t sts /\
              inferWidth_wmap0 (hd sskip sts) ce1 wm0 = wm1 /\
           CE.find (base_ref r) ce0 = Some t /\
           is_deftyp (type_of_cmpnttyp (fst t)) /\
           ~~ find_unknown (base_ref r) ce1 /\
           ~~ is_deftyp (type_of_cmpnttyp (fst (CE.vtyp (base_ref r) (inferWidth_fun sts ce1)))) 
           )->
           (* ~~ is_deftyp (type_of_cmpnttyp (fst (CE.vtyp v (inferWidth_fun sts ce1)))) /\ *)
           (*ce2 = wmap_map2_cenv wm1 ce1 /\*)
           inferType_stmts sts ce0 ce1 ->
       inferWidth_stmts_sem sts ce1 (inferWidth_fun sts ce1).
   Proof.
     have Hnone : (add_width_2_cenv None None = None) by done.
     elim => [ce0 ce1  v He Hiw | st ss Hm ce0 ce1 v He Hiw].
     - 
       apply inferWidth_stmts_nil. rewrite /inferWidth_fun/wmap_map2_cenv/=. intro.
       rewrite (CELemmas.map2_1bis _ _ _ Hnone). rewrite CELemmas.empty_o//. 
     -
       case He => [wm0 [wm1 Hec]].
       apply inferWidth_stmts_imp with (wmap_map2_cenv wm1 ce1). 
       move : Hec Hiw.
       elim st.
       + (*skip*)
         intros.
         move : (Hec (r) (aggr_typ def_ftype, Node) (* sskip *)) => [Hbrs1 [Hbrt [Hi[Hdt [Hndt [Hun Hit]]]]]].
         (* move : Hbrt => [ [Hinit Hi]].  *) rewrite /= in Hbrt.
         rewrite //. 
         (* exists wm0; exists wm1. *)
         (* apply inferWidth_sskip_sem_conform; try done. *)
         (* move : (Hec (r) (aggr_typ def_ftype, Node) ) => [Hbrs1 [Hbrt [Hdt [Hndt [Hun Hit]]]]]. *)
         (* rewrite //. *)
       + (*swire*)
         intros.
         exists wm0; exists wm1.
         move : (Hec (Eid s) (aggr_typ f, Wire) (* (Swire s f) *)) => [Hbrs1 [Hbrt [Hi [Hdt [Hndt [Hun Hit]]]]]].
         move : (new_v_wmap_none Hbrs1 wm0) => Hnv.
         apply inferWidth_swire_sem_conform with ce0; try done.
         exact : (inferType_stmts_hd Hiw).
       + (*reg*)
         intros.
         exists wm0; exists wm1.
         move : (Hec (Eid s) (reg_typ h, Register) (* (Sreg s h) *)) => [Hbrs1 [Hbrt [Hi[Hdt [Hndt [Hun Hit]]]]]].
         apply inferWidth_sreg_sem_conform with ce0; try done.
         exact : (inferType_stmts_hd Hiw).
       + (*mem*)
         intros.
         exists wm0; exists wm1.
         move : (Hec (Eid s) (CE.vtyp s ce0) (* (Smem s h) *)) => [Hbrs1 [Hbrt [Hi[Hdt [Hndt [Hun Hit]]]]]].
         apply inferWidth_smem_sem_conform with ce0; try done.
         exact : (inferType_stmts_hd Hiw).
       + (*inst*)
         intros.
         move : (Hec (Eid s) (CE.vtyp s0 ce0) (* (Sinst s s0) *)) => [Hbrs1 [Hbrt [Hi[Hdt [Hndt [Hun Hit]]]]]].
         exists wm0; exists wm1.
         apply inferWidth_sinst_sem_conform with ce0; try done.
         exact : (inferType_stmts_hd Hiw).
       + (*node*)
         intros.
         exists wm0; exists wm1.
         move : (Hec (Eid s) (CE.vtyp s ce0) (* (Snode s h) *)) => [Hbrs1 [Hbrt [Hi [Hdt [Hndt [Hun Hit]]]]]].
         apply inferWidth_snode_sem_conform with ce0; try done.
         exact : (inferType_stmts_hd Hiw).
       + (*fcnct*)
         intros.
         move : (Hec h (CE.vtyp (base_ref h) ce0) (* (Sfcnct h h0) *)) => [Hbrs1 [Hbrt [Hi[Hdt [Hndt [Hun Hit]]]]]].
         rewrite //.
         (* exists wm0; exists wm1. *)
         (* move : (inferType_stmts_hd Hiw) => Hitc. *)
         (* inversion Hitc; subst.  *)
         (* apply inferWidth_sfcnct_ftype_sem_conform with (snd (CE.vtyp (base_ref h) ce1)) ( (fst (CE.vtyp (base_ref h) ce1))) (type_of_cmpnttyp (fst (CE.vtyp (base_ref h) ce1))) (type_of_cmpnttyp (fst (CE.vtyp (base_ref h) (wmap_map2_cenv wm0 ce1)))); try done. *)
         (* move : (H3 ((fst (CE.vtyp (base_ref h) ce1))) *)
         (*            (type_of_cmpnttyp (fst (CE.vtyp (base_ref h) (wmap_map2_cenv wm0 ce1)))) *)
         (*            (snd (CE.vtyp (base_ref h) ce1))) => [Hit1 [Hit2 Hit3]]. *)
         (* rewrite //. *)
         (* move : (CE.find_some_vtyp Hbrt) => Hv. rewrite -surjective_pairing -Hbrt//. *)
         (* exact : (type_of_hexpr_cefind Hbrt). *)
         (* move : (H3 ((fst (CE.vtyp (base_ref h) ce1))) *)
         (*            (type_of_cmpnttyp (fst (CE.vtyp (base_ref h) (wmap_map2_cenv wm0 ce1)))) *)
         (*            (snd (CE.vtyp (base_ref h) ce1))) => [Hit1 [Hit2 Hit3]]. *)
         (* done. *)
       + (*pcnct*)
         intros. 
         move : (Hec h (CE.vtyp (base_ref h) ce0) (* (Spcnct h h0) *)) => [Hbrs1 [Hbrt [Hi[Hdt [Hndt [Hun Hit]]]]]].
         rewrite //.
       (* exists wm0; exists wm1. *)
       (* move : (inferType_stmts_hd Hiw) => Hitc. *)
       (* inversion Hitc; subst.  *)
       (* apply inferWidth_spcnct_ftype_sem_conform with (snd (CE.vtyp (base_ref h) ce1)) ( (fst (CE.vtyp (base_ref h) ce1))) (type_of_cmpnttyp (fst (CE.vtyp (base_ref h) ce1))) (type_of_cmpnttyp (fst (CE.vtyp (base_ref h) (wmap_map2_cenv wm0 ce1)))); try done. *)
       (* move : (H3 ((fst (CE.vtyp (base_ref h) ce1))) *)
       (*            (type_of_cmpnttyp (fst (CE.vtyp (base_ref h) (wmap_map2_cenv wm0 ce1)))) *)
       (*            (snd (CE.vtyp (base_ref h) ce1))) => [Hit1 [Hit2 Hit3]]. *)
       (* rewrite //. *)
       (* move : (CE.find_some_vtyp Hbrt) => Hv. rewrite -surjective_pairing -Hbrt//. *)
       (* exact : (type_of_hexpr_cefind Hbrt). *)
       (* move : (H3 ((fst (CE.vtyp (base_ref h) ce1))) *)
       (*            (type_of_cmpnttyp (fst (CE.vtyp (base_ref h) (wmap_map2_cenv wm0 ce1)))) *)
       (*            (snd (CE.vtyp (base_ref h) ce1))) => [Hit1 [Hit2 Hit3]]. *)
       (* done. *)
       + (*invalid*)
         intros.
         move : (Hec (h) (aggr_typ def_ftype, Node) (* (Sinvalid h) *)) => [Hbrs1 [Hbrt [Hi[Hdt [Hndt [Hun Hit]]]]]].
         rewrite //.
       (* exists wm0; exists wm1. *)
       (* rewrite /= in Hdt. rewrite /= in Hbrt; rewrite /= in Hbrs1. *)
       (* apply inferWidth_sinvalid; try rewrite //. *)
       (* rewrite Hiw//. *)
       (* rewrite /wmap_map2_cenv (CELemmas.map2_1bis _ _ _ Hnone) Hbrs1. *)
       (* move : (inferType_stmts_hd Hit) => Hits. *)
       (* inversion Hits; subst. rewrite Hbrt//. *)
       + (*when*)
         intros.
         move : (Hec (r) (aggr_typ def_ftype, Node) (* (Swhen h l l0) *)) => [Hbrs1 [Hbrt [Hi[Hdt [Hndt [Hun Hit]]]]]].
         rewrite //.
       (* rewrite /= in Hiw; rewrite /= in Hbrs; rewrite /= in Hbrt. *)
       (* apply inferWidth_swhen with (Eid v); try rewrite //. *)
       (* rewrite Hiw//. *)
       (* rewrite /wmap_map2_cenv (CELemmas.map2_1bis _ _ _ Hnone) Hbrs1. *)
       (* move : (inferType_stmts_hd Hit) => Hits. *)
       (* inversion Hits; subst.  *)
       + (*stop*)
         intros.
         move : (Hec (r) (aggr_typ def_ftype, Node) (* (Sstop h h0 n) *)) => [Hbrs1 [Hbrt [Hi[Hdt [Hndt [Hun Hit]]]]]].
         rewrite //.
         (* rewrite /= in Hiw; rewrite /= in Hbrs; rewrite /= in Hbrt. *)
         (* apply inferWidth_sstop with v; try rewrite //. *)
         (* rewrite Hiw//. *)
         (* rewrite /wmap_map2_cenv (CELemmas.map2_1bis _ _ _ Hnone) Hbrs1. *)
         (* move : (inferType_stmts_hd Hit) => Hits. *)
         (* inversion Hits; subst.  *)
       +
         move : (Hec (Eid v) (aggr_typ def_ftype, Node)) => [Hbrs1 [Hbrt [Hi[Hdt [Hndt [Hun Hit]]]]]].
         symmetry in Hi.
         rewrite (infer_stmt_lst _ Hi).
         apply Hm with ce0 (*wmap_map2_cenv wm1 ce1*) ; try done.
         exists wm1; exists (inferWidth_wmap0 (hd sskip ss) (wmap_map2_cenv wm1 ce1) wm1).
         intros.
         move : (Hec r t) => [Hbrs10 [Hbrt0 [Hin0 [Hdt0 [Hndt0 [Hun0 Hit0]]]]]].
         repeat (split; try done).
         rewrite /= in Hbrt0. move : Hbrt0. case (is_inital st); try done.
         rewrite /wmap_map2_cenv/find_unknown (CELemmas.map2_1bis _ _ _ Hnone).
         rewrite (new_v_wmap_none Hbrs10 wm1)/=.
         rewrite /find_unknown/= in Hun0. done.
         move : Hit0. rewrite (infer_stmt_lst ss Hi)//.
         apply Infertype_stmts_know.
         exists (base_ref (Eid v)).
         rewrite /find_unknown/wmap_map2_cenv (CELemmas.map2_1bis _ _ _ Hnone).
         rewrite (new_v_wmap_none Hbrs1 wm1)/=.
         rewrite /find_unknown/= in Hun. done.
   Qed.

   (* Lemma ftype_equiv_ident : *)
   (*   forall t, ftype_equiv t t *)
   (* with ffield_equiv_ident : *)
   (*        forall(f: ffield), *)
   (*          fbtyp_equiv f f. *)
   (* Proof. *)
   (*   elim; rewrite /=; intros. elim f; done. *)
   (*   rewrite eq_refl H//. *)
   (*   rewrite ffield_equiv_ident//. *)
   (*   elim; intros. rewrite /= ; done. *)
   (*   rewrite /= eq_refl H ftype_equiv_ident. *)
   (*   case f; rewrite /=//. *)
   (* Qed. *)

   Lemma inferWidth_stmts_sem_conform :
     forall sts ce0 ce1 (v:var),
       (
         exists wm0 wm1,
           forall r t ,
             new_comp_name (base_ref r) /\
             inferWidth_wmap0 (hd sskip sts) ce1 wm0 = wm1 /\
             CE.find (base_ref r) ce0 = Some t /\
             CE.find (base_ref r) wm0 = Some (type_of_cmpnttyp (fst t)) /\
           is_deftyp (type_of_cmpnttyp (fst t)) /\
           ~~ find_unknown (base_ref r) ce1 /\
           ~~ is_deftyp (type_of_cmpnttyp (fst (CE.vtyp (base_ref r) (inferWidth_fun sts ce1)))) 
           )->
           (* ~~ is_deftyp (type_of_cmpnttyp (fst (CE.vtyp v (inferWidth_fun sts ce1)))) /\ *)
           (*ce2 = wmap_map2_cenv wm1 ce1 /\*)
           inferType_stmts sts ce0 ce1 ->
       inferWidth_stmts_sem sts ce1 (inferWidth_fun sts ce1).
   Proof.
     have Hnone : (add_width_2_cenv None None = None) by done.
     elim => [ce0 ce1  v He Hiw | st ss Hm ce0 ce1 v He Hiw].
     - 
       apply inferWidth_stmts_nil. rewrite /inferWidth_fun/wmap_map2_cenv/=. intro.
       rewrite (CELemmas.map2_1bis _ _ _ Hnone). rewrite CELemmas.empty_o//. 
     -
       case He => [wm0 [wm1 Hec]].
       apply inferWidth_stmts_imp with (wmap_map2_cenv wm1 ce1). 
       move : Hec Hiw.
       elim st.
       + (*skip*)
         intros.
         move : (Hec (r) (aggr_typ def_ftype, Node) (* sskip *)) => [Hbrs1 [Hbrt [[Hdt [Hndt [Hun Hit]]]]]].
         (* move : Hbrt => [ [Hinit Hi]].  *) rewrite /= in Hbrt.
         exists wm0; exists wm1.
         apply inferWidth_sskip_sem_conform; try done.
       + (*swire*)
         intros.
         exists wm0; exists wm1.
         move : (Hec (Eid s) (aggr_typ f, Wire) (* (Swire s f) *)) => [Hbrs1 [Hbrt [[Hdt [Hndt [Hun Hit]]]]]].
         rewrite /= in Hbrt. 
         move : (new_v_wmap_none Hbrs1 wm0) => Hnv.
         apply inferWidth_swire_sem_conform with ce0; try done.
         exact : (inferType_stmts_hd Hiw).
       + (*reg*)
         intros.
         exists wm0; exists wm1.
         move : (Hec (Eid s) (reg_typ h, Register) (* (Sreg s h) *)) => [Hbrs1 [Hbrt [[Hdt [Hndt [Hun Hit]]]]]].
         apply inferWidth_sreg_sem_conform with ce0; try done.
         exact : (inferType_stmts_hd Hiw).
       + (*mem*)
         intros.
         exists wm0; exists wm1.
         move : (Hec (Eid s) (CE.vtyp s ce0) (* (Smem s h) *)) => [Hbrs1 [Hbrt [[Hdt [Hndt [Hun Hit]]]]]].
         apply inferWidth_smem_sem_conform with ce0; try done.
         exact : (inferType_stmts_hd Hiw).
       + (*inst*)
         intros.
         move : (Hec (Eid s) (CE.vtyp s0 ce0) (* (Sinst s s0) *)) => [Hbrs1 [Hbrt [[Hdt [Hndt [Hun Hit]]]]]].
         exists wm0; exists wm1.
         apply inferWidth_sinst_sem_conform with ce0; try done.
         exact : (inferType_stmts_hd Hiw).
       + (*node*)
         intros.
         exists wm0; exists wm1.
         move : (Hec (Eid s) (CE.vtyp s ce0) (* (Snode s h) *)) => [Hbrs1 [Hbrt [[Hdt [Hndt [Hun Hit]]]]]].
         apply inferWidth_snode_sem_conform with ce0; try done.
         exact : (inferType_stmts_hd Hiw).
       + (*fcnct*)
         intros.
         move : (Hec h (CE.vtyp (base_ref h) ce0) (* (Sfcnct h h0) *)) => [Hbrs1 [Hbrt [[Hdt [Hndt [Hun [Hfu Hit]]]]]]].
         rewrite //.
         exists wm0; exists wm1.
         move : (inferType_stmts_hd Hiw) => Hitc.
         inversion Hitc; subst.
         move : H4 => [Hit1 [Hit2 Hit3]].
         apply inferWidth_sfcnct_ftype_sem_conform with c0 t (type_of_cmpnttyp t) t'; try done.
         rewrite (type_of_hexpr_cefind Hit1) /=//.
         rewrite (CE.find_some_vtyp Hit1) /= in Hun. done.
         rewrite Hndt (CE.find_some_vtyp Hit1)/=//.
       + (*pcnct*)
         intros.
         move : (Hec h (CE.vtyp (base_ref h) ce0) (* (Sfcnct h h0) *)) => [Hbrs1 [Hbrt [[Hdt [Hndt [Hun [Hfu Hit]]]]]]].
         rewrite //.
         exists wm0; exists wm1.
         move : (inferType_stmts_hd Hiw) => Hitc.
         inversion Hitc; subst.
         move : H4 => [Hit1 [Hit2 Hit3]].
         apply inferWidth_spcnct_ftype_sem_conform with c0 t (type_of_cmpnttyp t) t'; try done.
         
         admit.
       + (*invalid*)
         intros.
         move : (Hec (h) (aggr_typ def_ftype, Node) (* (Sinvalid h) *)) => [Hbrs1 [Hbrt [Hi[Hdt [Hndt [Hun Hit]]]]]].
         exists wm0; exists wm1.
         rewrite /= in Hdt. rewrite /= in Hbrt; rewrite /= in Hbrs1.
         apply inferWidth_sinvalid; try rewrite //.
   Admitted.
         
   (********************************************************************************)

   
   (** Pass InferResets **)

   (* A map to store candidate reset signals *)
   (* Definition rmap := CE.t (ftype). *)
   (* Definition empty_rmap : rmap := CE.empty (ftype). *)
   (* Definition finds_r (v:var) (r:rmap) := match CE.find v r with Some t => t | None => def_ftype end. *)

   Definition rmap := CE.t (seq ftype).
   Definition empty_rmap : rmap := CE.empty (seq ftype).
   Definition findr (v:var) (r:rmap) := match CE.find v r with Some t => t | None => [::] end.

   (* store a list of abstract reset types, and check async/sync later *)
   Fixpoint add_ref_rmap r t ce m : rmap :=
     match r with
     | Eid v => CE.add v (cons t (findr v m)) m
     | Esubfield r f =>
       let br := base_ref r in
       CE.add br (cons (upd_name_ftype (base_type_of_ref r ce) (v2var f) t) (finds br m)) m
     | Esubindex rs n =>
       let br := base_ref rs in
       let vt := type_of_cmpnttyp (fst (CE.vtyp br ce)) in
       match vt with
       | Gtyp gt => m
       | Atyp ta na => CE.add br (cons (upd_vectyp vt t) (finds br m)) m
       | Btyp _ => CE.add br (cons (upd_name_ftype vt (v2var (get_field_name rs)) t) (finds br m)) m
       end
     | Esubaccess rs n =>
       let br := base_ref rs in
       let vt := type_of_cmpnttyp (fst (CE.vtyp br ce)) in
       match vt with
       | Gtyp gt => m
       | Atyp ta na => CE.add br (cons (upd_vectyp vt t) (finds br m)) m
       | Btyp Fnil => m
       | Btyp (Fflips v _ tf fs) =>
         CE.add br (cons (upd_name_ftype vt (v2var (get_field_name rs)) t) (finds br m)) m
       end
     end.

   Fixpoint inferReset_rmap ce (m : rmap) (s : hfstmt) : rmap :=
     match s with
     | Snode v e => CE.add v [::type_of_hfexpr e ce] m
     | Swire v t => if is_deftyp t then CE.add v [::t] m else m
     | Sreg v _ => m
     | Smem v _ => m
     | Sinst v1 v2 => CE.add v1 [::type_of_ref (Eid v2) ce] m
     | Sinvalid v => m
     | Sfcnct r e => let te := type_of_hfexpr e ce in
                     add_ref_rmap r te ce m
     | Spcnct r e => let te := type_of_hfexpr e ce in
                     add_ref_rmap r te ce m
     | Sskip
     | Sstop _ _ _ => m
     | Swhen c s1 s2 => List.fold_left (inferReset_rmap ce) s2 (List.fold_left (inferReset_rmap ce) s1 m)
     end.

   Definition is_uninfered_reset rs := is_deftyp (hd def_ftype rs).

   Fixpoint has_async rs :=
     match rs with
     | [::] => false
     | Gtyp Fasyncreset :: rt => true
     | _ :: rt => has_async rt
     end.

   Fixpoint has_sync rs {struct rs} :=
     match rs with
     | [::] => false
     | Gtyp (Fuint 1) :: rt => true
     | _ :: rt => has_sync rt
     end.

   Definition add_reset2cenv (m : option (list ftype)) (t : option (cmpnt_init_typs * fcomponent)) :=
     match t, m with
     | Some (Aggr_typ (Gtyp Freset), c), Some rs => 
       if (has_async rs && (negb (has_sync rs))) then Some (aggr_typ (Gtyp (Fuint 1)), c)
           else if has_sync rs && has_async rs then Some (aggr_typ def_ftype, c)
                else Some (aggr_typ (Gtyp (Fuint 1)), c)
     | _, _ => t
     end.

   Definition rmap_map2_cenv (r:rmap) ce : CE.env :=
     CE.map2 add_reset2cenv r ce.

   Definition inferReset_fun ss ce : CE.env :=
     rmap_map2_cenv (List.fold_left (inferReset_rmap ce) ss empty_rmap) ce.


   (********************************************************************************)

   
   (** Pass ExpandConnect *)

   Fixpoint size_of_ftype ft :=
     match ft with
     | Gtyp t => 1
     | Atyp t n => (size_of_ftype t) * n
     | Btyp b => size_of_fields b
     end
   with size_of_fields b :=
          match b with
          | Fnil => 0
          | Fflips v fl t fs => (size_of_ftype t) + size_of_fields fs
          end.

   Fixpoint offset_of_subfield_b ft fid n :=
     match ft with
     | Fnil => n
     | Fflips v fl t fs => if fid == v then n else offset_of_subfield_b fs fid (n + size_of_ftype t)
     end.

   Definition offset_of_subfield ft fid n :=
     match ft with
     | Gtyp t => 0
     | Atyp t n => 0
     | Btyp b => offset_of_subfield_b b fid n
     end.

   (** TBD *)  
   Parameter new_var : var -> Var.var -> var.
   Parameter new_subvar : var -> nat -> var.
   Parameter new_subvar_i : var -> nat -> var.
   Parameter new_subvar_t : var -> var -> var.
   Parameter var2v : Var.var -> V.t.
   Parameter vtmp : var.

      
   Fixpoint list_repeat_fn f n (l : list ftype) :=
     match n with
     | 0 => l
     | S m => list_repeat_fn f m (f l)
     end.
   
   Fixpoint ftype_list (ft : ftype) l :=
     match ft with
     | Gtyp t => Gtyp t :: l
     | Atyp t n => list_repeat_fn (ftype_list t) n l
     | Btyp b => ftype_list_btyp b l
     end

   with ftype_list_btyp b l :=
     match b with
     | Fnil => l
     | Fflips v fl t fs => ftype_list_btyp fs (ftype_list t l)
     end.
   
   Fixpoint vlist_repeat_fn f v i n (l : list (var * ftype)) {struct n}:=
     match n with
     | 0 => l
     | S m => vlist_repeat_fn f (new_subvar v i) i m (f l)
     end.
   
   Fixpoint ftype_vlist v (ft : ftype) l :=
     match ft with
     | Gtyp t => (v, Gtyp t) :: l
     | Atyp t n => vlist_repeat_fn (ftype_vlist v t) v (size_of_ftype t) n l
     | Btyp b => ftype_vlist_btyp v b l
     end

   with ftype_vlist_btyp r b l :=
     match b with
     | Fnil => l
     | Fflips v fl t fs => ftype_vlist_btyp r fs (ftype_vlist (new_subvar r (offset_of_subfield_b b v 0)) t l)
     end.

   (* A map to store types destruct *)
   Definition dmap := CE.t (fgtyp * fcomponent).
   Definition empty_dmap : dmap := CE.empty (fgtyp * fcomponent). 
   Definition findsd (v:var) (d:dmap) :=
     match CE.find v d with Some t => t | None => (Fuint 0, Node)  end.

   Fixpoint expand_eref er ce : var :=
     match er with
     | Eid v => v
     | Esubfield r v => new_subvar (expand_eref r ce) (offset_of_subfield (type_of_ref r ce) (v2var v) 0)
     | Esubindex r n => new_subvar (expand_eref r ce) n
     | Esubaccess r e => new_subvar (expand_eref r ce) 0 (* TBD *)
     end.
   
   (*
   Fixpoint expand_index r t n l : list (var * ftype) :=
     match n with
     | 0 => l
     | S m => expand_index r t m ((expand_eref (Esubindex r n), t) :: l)
     end.

   Fixpoint expand_fields_fun r bs l : list (var * ftype) :=
     match bs with
     | Fnil => l
     | Fflips v fl t fs => expand_fields_fun r fs ((expand_eref (Esubfield r (var2v v)), t) :: l )
     end.
*)
   
   Fixpoint fcnct_list (l1 :list (var * ftype)) (l2:list (var * ftype)) cs :=
     match l1, l2 with
     | nil, nil => cs
     | (v1, t1) :: tl1, (v2, t2):: tl2 => fcnct_list tl1 tl2 (SV.upd v1 (r_fexpr (Eref (Eid v2))) cs)
     | _, _ => cs
     end.

   (* premise : passive type, weak type equiv *)

   Fixpoint pcnct_pair_b v1 v2 (t1 : ffield) (t2: ffield) cs :=
     match t1 with
     | Fnil => cs
     | Fflips vt1 fp1 tf1 fs1 =>
       match t2 with
       | Fnil => cs
       | Fflips vt2 fp2 tf2 fs2 =>
         if vt1 == vt2
         then SV.upd (new_subvar v1 (offset_of_subfield (Btyp t1) vt1 0))
                     (r_fexpr (Eref (Eid (new_subvar v2 (offset_of_subfield (Btyp t2) vt2 0))))) cs
         else pcnct_pair_b v1 v2 t1 fs2 cs
       end
     end.
   
   Fixpoint pcnct_pair (t1 : (var * ftype)) (t2: (var * ftype)) cs :=
     match t1, t2 with
     | (v1, Gtyp t1) , (v2, Gtyp t2) => SV.upd v1 (r_fexpr (Eref (Eid v2))) cs
     | (v1, Atyp t1 n1) , (v2, Atyp t2 n2) =>
       let n := minn n1 n2 in let t := Atyp t1 n in
                              fcnct_list (ftype_vlist v1 t nil) (ftype_vlist v2 t nil) cs
     | (v1, Btyp b1), (v2, Btyp b2) => pcnct_pair_b v1 v2 b1 b2 cs
     | _, _ => cs
     end.
   
   (* premise : passive type, weak type equiv *)
   
   Parameter store_spcnct : href -> href -> ftype -> cstate -> cstate.

   Definition store_rhsexpr (s : hfstmt) (cs : cstate) ce : cstate :=
     match s with
     | Swire v t => SV.upd v r_default cs
     | Snode v e => SV.upd v (r_fexpr e) cs
     | Sreg v r => SV.upd v r_default cs
     | Smem v m => SV.upd v r_default cs
     | Sfcnct r1 (Eref r2) =>
       let t1 := type_of_ref r1 ce in
       let t2 := type_of_ref r2 ce in
       fcnct_list (ftype_vlist (expand_eref r1 ce) t1 nil) (ftype_vlist (expand_eref r2 ce) t2 nil) cs 
     | Spcnct r1 (Eref r2) => 
       let t1 := type_of_ref r1 ce in
       let t2 := type_of_ref r2 ce in
       pcnct_pair (expand_eref r1 ce, t1) (expand_eref r2 ce, t2) cs
     | Sinvalid r1 => SV.upd (expand_eref r1 ce) r_default cs
     | _ => cs
     end.     

     
   (*
   (* premise : passive type, type equiv *)
   Fixpoint expand_connect_subindex r1 r2 n : seq hfstmt :=
     match n with
     | 0 => [::]
     | S m => Sfcnct (Esubindex r1 n) (Eref (Esubindex r2 n)) :: (expand_connect_subindex r1 r2 m)
     end.

   (* premise : passive type, type equiv *)
   Fixpoint expand_fullconnect_subfield r1 r2 bs :=
     match bs with
     | Fnil => [::]
     | Fflips v Nflip t bs' => Sfcnct (Esubfield r1 (var2v v)) (Eref (Esubfield r2 (var2v v)))
                                      :: (expand_fullconnect_subfield r1 r2 bs')
     | _ => [::]
     end.

   (* premise : type weak equiv *)
   Fixpoint expand_partconnect_subfield r1 r2 bs1 bs2 {struct bs1} :=
     match bs1 with
     | Fflips v1 Nflip t1 bs1' =>
       if have_field bs2 v1 then
         Sfcnct (Esubfield r1 (var2v v1)) (Eref (Esubfield r2 (var2v v1)))
                :: (expand_partconnect_subfield r1 r2 bs1' bs2)
       else expand_partconnect_subfield r1 r2 bs1' bs2
     | Fflips v1 Flipped t1 bs1' =>
       if have_field bs2 v1 then
         Sfcnct (Esubfield r2 (var2v v1)) (Eref (Esubfield r1 (var2v v1)))
                :: (expand_partconnect_subfield r1 r2 bs1' bs2)
       else expand_partconnect_subfield r1 r2 bs1' bs2
     | Fnil => [::]
     end.

   (* premise: valid lhs rhs (resolve flow), type equiv/weak_equiv (type infer, width infer) *)
   (* since types are lowered in Pass LoweringType, ExpandConnect is only in transform pass, not in semantics representation ce cs *)
   Fixpoint expandConnect_fun st ce : seq hfstmt :=
     match st with
     | Sfcnct r1 (Eref r2) =>
       let tr1 := type_of_ref r1 ce in
       let tr2 := type_of_ref r2 ce in
       match tr1, tr2 with
       | Gtyp t1, Gtyp t2 => [::Sfcnct r1 (Eref r2)]
       | Atyp t1 n1, Atyp t2 n2 => expand_connect_subindex r1 r2 n1
       | Btyp bs1, Btyp bs2 => expand_fullconnect_subfield r1 r2 bs1
       | _, _ => [::]
       end
     | Spcnct r1 (Eref r2) =>
       let tr1 := type_of_ref r1 ce in
       let tr2 := type_of_ref r2 ce in
       match tr1, tr2 with
       | Gtyp t1, Gtyp t2 => [:: Sfcnct r1 (Eref r2)]
       | Atyp t1 n1, Atyp t2 n2 => if n1 < n2 then expand_connect_subindex r1 r2 n1
                                   else expand_connect_subindex r1 r2 n2
       | Btyp bs1, Btyp bs2 => expand_partconnect_subfield r1 r2 bs1 bs2
       | _, _ => [::]
       end
     | st => [::st]
     end.

   Inductive expand_fields : var -> var -> ffield -> CE.env -> cstate -> CE.env -> cstate -> Prop :=
   | Expand_fnil r1 r2 ce cs ce' cs' : expand_fields r1 r2 (Fnil) ce cs ce' cs'
   | Expand_fields r1 r2 v t f ffs ce0 cs0 ce1 ce2 cs1 ce' cs':
       CE.Add (new_var r1 v) (aggr_typ t, Wire) ce0 ce1 ->
       CE.Add (new_var r2 v) (aggr_typ t, Wire) ce1 ce2 ->
       SV.Upd (new_var r1 v) (R_fexpr (Eref (Eid (new_var r2 v)))) cs0 cs1 ->
       expand_fields r1 r2 ffs ce2 cs1 ce' cs' ->
       expand_fields r1 r2 (Fflips (v) f t ffs) ce0 cs0 ce' cs'.
  *)
   
   (*
   Inductive expandConnect : hfstmt -> CE.env -> cstate -> CE.env -> cstate -> Prop :=
   | Expand_fcnnct :
       forall r f bs r2 ce0 cs0 ce cs ,
         base_type_of_ref r ce0 == Btyp bs ->
         have_field bs (v2var f) ->
         ftype_equiv (type_of_ref r ce0) (type_of_ref r2 ce0) ->
         expand_fields (base_ref r) (base_ref r2) bs ce0 cs0 ce cs ->
         expandConnect (Sfcnct r (Eref r2)) ce0 cs0 ce cs
   | Expand_pcnnct r r2 ce0 cs0 ce cs:
       expandConnect (Spcnct r (Eref r2)) ce0 cs0 ce cs.
    *)



   (********************************************************************************)


   (** Pass ExpandWhens *)

   (* Definition expandWhens_fun s ce cs : hfstmt := *)
   (*   match s with *)
   (*   | Swhen c (Sfcnct r e) s2 =>  *)



  (** Semantics of declaim  ports*)
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


  Parameter map2 : (option rhs_expr -> option rhs_expr -> option rhs_expr) -> cstate -> cstate -> cstate.

  (** Semantics of statement group, last cnct considered *)
  Inductive eval_fstmts_group : seq hfstmt -> CE.env -> cstate -> CE.env -> cstate -> Prop :=
  | Gnil ce cs: eval_fstmts_group [::] ce cs ce cs
  (** other than when *)
  | Gfstmts_default st hst_tl ce ce' cs cs' cs'' :
      eval_fstmt_single st ce cs ce cs' ->
      eval_fstmts_group hst_tl ce cs' ce' cs'' ->
      eval_fstmts_group (st :: hst_tl) ce cs ce' cs''
  (* (**  claim a sreg *) *)
  (* | Gfstmts_reg_init r rt hst_tl ce ce' ce'' cs cs' cs'' : *)
  (*     eval_fstmt_single (sreg r rt) ce cs ce' cs' -> *)
  (*     eval_fstmts_group  hst_tl ce' cs' ce'' cs'' -> *)
  (*     eval_fstmts_group (sreg r rt :: hst_tl) ce cs ce'' cs''. *)
  (* (** claim a node *) *)
  (* | Gfstmts_node v e hst_tl ce ce' ce'' cs cs' cs'' : *)
  (*     eval_fstmt_single (snode v e) ce cs ce' cs' -> *)
  (*     eval_fstmts_group hst_tl ce' cs' ce'' cs'' -> *)
  (*     eval_fstmts_group (snode v e :: hst_tl) ce cs ce'' cs'' *)
  (* (** skip *) *)
  (* | Gskip_fstmts hst_tl ce ce' cs cs' : *)
  (*     eval_fstmts_group hst_tl ce cs ce' cs' -> *)
  (*     eval_fstmts_group (sskip :: hst_tl) ce cs ce' cs' *)
  (** condition when *)
  | Gwhen_fstmts c hstg1 hstg2 hst_tl ce ce' ce'' cs cs' cs'' :
      eval_fstmts_group_branch c hstg1 hstg2 ce cs ce' cs' ->
      eval_fstmts_group hst_tl ce' cs' ce'' cs'' ->
      eval_fstmts_group (swhen c hstg1 hstg2 :: hst_tl) ce cs ce'' cs''
  (** https://github.com/llvm/circt/blob/main/lib/Dialect/FIRRTL/Transforms/ExpandWhens.cpp *)
  with eval_fstmts_group_branch :
         hfexpr -> seq hfstmt -> seq hfstmt -> CE.env -> cstate -> CE.env -> cstate -> Prop :=
  (** nil *)
  | Gthen_else_def c ce cs :
      eval_fstmts_group_branch c [::] [::] ce cs ce cs
  | Gthen_else c tb eb ce0 cs0 ce1 cs1 ce2 cs2 :
      eval_fstmts_group tb ce0 cs0 ce1 cs1 ->
      eval_fstmts_group eb ce0 cs0 ce2 cs2 ->
      eval_fstmts_group_branch c tb eb ce0 cs0 (CE.map2 merge_branch_ce (CE.map2 merge_branch_ce ce0 ce1) ce2)
                               (map2 (merge_branch_cs_e c) (map2 (merge_branch_cs_t c) cs0 cs1) cs2).

  (* (** connect to dst in then branch which has "not" been connected previously, add then branch *) *)
  (* | Gthen_cnct_0 c v e hstg1 hstg2 ce ce' ce'' cs cs' cs'' : *)
  (*     SV.acc (base_ref v) cs == r_default -> *)
  (*     eval_fstmt_single (sfcnct v e) ce cs ce' cs' -> *)
  (*     eval_fstmts_group_branch c hstg1 hstg2 ce' cs' ce'' cs'' -> *)
  (*     eval_fstmts_group_branch c (sfcnct v e :: hstg1) hstg2 ce cs ce'' cs'' *)
  (* (** connect to dst in else branch which has "not" been connected previously, add else branch *) *)
  (* | Gelse_cnct_0 c v e hstg2 ce ce' ce'' cs cs' cs'' : *)
  (*     CE.find v ce == None -> *)
  (*     eval_fstmt_single (sfcnct (eref v) e) ce cs ce' cs' -> *)
  (*     eval_fstmts_group_branch c [::] hstg2 ce' cs' ce'' cs'' -> *)
  (*     eval_fstmts_group_branch c [::] (sfcnct (eref v) e :: hstg2) ce cs ce'' cs'' *)
  (* (** connect to dst in then branch which has been connected previously, add mux(p, then, prev) *) *)
  (* | Gthen_cnct c v e re hstg1 hstg2 ce ce' cs cs' cs'' : *)
  (*     SV.acc v cs == r_fexpr re -> *)
  (*     (* CELemmas.P.Add vn Node ce ce' -> *) *)
  (*     (* SV.Upd vn (r_fexpr (emux c e re)) cs cs' -> *) *)
  (*     SV.Upd v (r_fexpr (emux c e re)) cs cs' -> *)
  (*     eval_fstmts_group_branch c hstg1 hstg2 ce cs' ce' cs'' -> *)
  (*     eval_fstmts_group_branch c (sfcnct (eref v) e :: hstg1) hstg2 ce cs ce' cs'' *)
  (* (** connect to dst in else branch which has been connected previously, add mux(p, prev, else) *) *)
  (* | Gelse_cnct c v e re hstg2 ce ce' cs cs' cs'' : *)
  (*     SV.acc v cs == r_fexpr re -> *)
  (*     SV.Upd v (r_fexpr (emux c re e)) cs cs' -> *)
  (*     eval_fstmts_group_branch c [::] hstg2 ce cs' ce' cs'' -> *)
  (*     eval_fstmts_group_branch c [::] (sfcnct (eref v) e :: hstg2) ce cs ce' cs'' *)
  (* (** claim a sreg in then branch *) *)
  (* | Gthen_reg c r hstg1 hstg2 ce ce' ce'' cs cs' cs'' : *)
  (*     eval_fstmt_single (sreg r) ce cs ce' cs' -> *)
  (*     eval_fstmts_group_branch c hstg1 hstg2 ce' cs' ce'' cs'' -> *)
  (*     eval_fstmts_group_branch c (sreg r :: hstg1) hstg2 ce cs ce'' cs'' *)
  (* (** claim a sreg in else branch *) *)
  (* | Gelse_reg c r hstg2 ce ce' ce'' cs cs' cs'' : *)
  (*     eval_fstmt_single (sreg r) ce cs ce' cs' -> *)
  (*     eval_fstmts_group_branch c [::] hstg2 ce' cs' ce'' cs'' -> *)
  (*     eval_fstmts_group_branch c [::] (sreg r :: hstg2) ce cs ce'' cs'' *)
  (* (** claim a node in then branch *) *)
  (* | Gthen_node c v e hstg1 hstg2 ce ce' ce'' cs cs' cs'' : *)
  (*     eval_fstmt_single (snode v e) ce cs ce' cs' -> *)
  (*     eval_fstmts_group_branch c hstg1 hstg2 ce' cs' ce'' cs'' -> *)
  (*     eval_fstmts_group_branch c (snode v e :: hstg1) hstg2 ce cs ce'' cs'' *)
  (* (** claim a node in else branch *) *)
  (* | Gelse_node c v e hstg2 ce ce' ce'' cs cs' cs'' : *)
  (*     eval_fstmt_single (snode v e) ce cs ce' cs' -> *)
  (*     eval_fstmts_group_branch c [::] hstg2 ce' cs' ce'' cs'' -> *)
  (*     eval_fstmts_group_branch c [::] (snode v e :: hstg2) ce cs ce'' cs''. *)

  (* Lemma valid_conncection v e2 sts ce cs ce' cs' : *)
  (*   eval_fstmts_group (sfcnct (eref v) e2 :: sts) ce cs ce' cs' -> *)
  (*   valid_rhs (SV.acc v cs') ce'. *)
    
       
   (********************************************************************************)
            

   (** Pass LowerTypes *)
   (* lower ports 
    * We lower ports in a separate pass in order to ensure that statements inside the module do not influence port names.*)
    (* Dependency(RemoveAccesses), // we require all SubAccess nodes to have been removed *)
    (* Dependency(CheckTypes), // we require all types to be correct *)
    (* Dependency(InferTypes), // we require instance types to be resolved (i.e., DefInstance.tpe != UnknownType) *)
    (* Dependency(ExpandConnects) // we require all PartialConnect nodes to have been expanded *)

   (* Parameter destructType_fun : var -> cenv -> dmap. *)

   Fixpoint len_of_ftype t :=
     match t with
     | Gtyp t => 1
     | Atyp t n => len_of_ftype t + n
     | Btyp bs => len_of_ffield bs
     end
   with len_of_ffield f :=
     match f with
     | Fnil => 0
     | Fflips v f t ff => len_of_ftype t + (len_of_ffield ff)
     end.

   (* Fixpoint new_vars_atyp r n t te : CE.env := *)
   (*   match n with *)
   (*   | 0 => te *)
   (*   | S m => new_vars_atyp r m t (CE.add (new_var r (N.of_nat n)) t te) *)
   (*   end. *)

   Fixpoint io_conv c :=
     match c with
     | In_port => Out_port
     | Out_port => In_port
     | c => c
     end.

   Fixpoint destructTypes_fun_aux r t c l {struct t} : list (var * fgtyp * fcomponent) :=
     match t with
     | Gtyp t => (r, t, c) :: l
     | Atyp t n =>
       match n with
       | 0 => l
       | S n => destructTypes_fun_aux (new_var r (N.of_nat n)) t c l
       end
     | Btyp bs => destructField_fun_aux r bs c l 
     end
     with destructField_fun_aux r bs c l :=
            match bs with
            | Fnil => l
            | Fflips v f t ff =>
              match f with
              | Nflip => 
                destructTypes_fun_aux (new_var r v) t c l ++ destructField_fun_aux r ff c l
              | Flipped =>
                destructTypes_fun_aux (new_var r v) t (io_conv c) l ++ destructField_fun_aux r ff c l
              end
            end.

   Fixpoint destructTypes_fun (l : list (var * fgtyp * fcomponent)) d : dmap :=
     match l with
     | nil => d
     | (r, t, c) :: tl => destructTypes_fun tl (CE.add r (t, c) d)
     end.

   Definition lowerTypes_fport (p : hfport) dm : dmap :=
     match p with
     | Finput v t => destructTypes_fun (destructTypes_fun_aux v t In_port [::]) dm
     | Foutput v t => destructTypes_fun (destructTypes_fun_aux v t Out_port [::]) dm
     end.

   Definition lowerTypes_init_fstmt dm (s : hfstmt) : dmap :=
     match s with
     | Swire v t => destructTypes_fun (destructTypes_fun_aux v t Wire [::]) dm
     | Sreg v r => destructTypes_fun (destructTypes_fun_aux v (type r) Register [::]) dm
     | Smem v m => destructTypes_fun (destructTypes_fun_aux v (data_type m) Memory [::]) dm
     | _ => dm
     end.

   Definition lowerTypes_init_fstmts ss dm := fold_left lowerTypes_init_fstmt ss dm.

   Definition add_lowtype_2_cenv (lt : option (fgtyp * fcomponent)) (t : option (cmpnt_init_typs * fcomponent)) :=
     match lt, t with
     | None, t => t
     | Some (lt, c), None => Some (aggr_typ (Gtyp lt), c)
     | Some (lt, c), Some t => Some t
     end.

   Definition dmap_2_cenv lt ce : CE.env :=
     CE.map2 add_lowtype_2_cenv lt ce.

   Definition lowerTypes_fun ss ce : CE.env :=
     dmap_2_cenv (lowerTypes_init_fstmts ss empty_dmap) ce.

   
   (********************************************************************************)

   (** Pass RemoveReset *)
   Definition is_async er ce :=
     let rt := type_of_hfexpr er ce in
     match rt with | Gtyp Fasyncreset => true | _ => false end.

   Parameter invalid_value : ftype.
   
   Definition RemoveReset_fun (st : hfstmt) ce ss :=
     match st with
     | Sreg v r => match (reset r) with
                   | Rst er (Eref (Eid ei)) => 
                     match (SV.acc ei ss) with
                     | R_default =>
                       (CE.add_fst v 
                                   (Reg_typ (mk_freg (type r) (clock r) (Rst (econst (Fuint 1) [::b0]) (eref (eid v))))) ce, ss)
                     | _ => (ce, ss)
                     end
                   | Rst (Econst t [::b0]) ei =>
                     (CE.add_fst v 
                            (Reg_typ (mk_freg (type r) (clock r) (Rst (econst (Fuint 1) [::b0]) (eref (eid v))))) ce, ss)
                   | Rst e1 ei => if is_async e1 ce then (ce, ss)
                                  else (CE.add_fst v (Reg_typ (mk_freg (type r) (clock r) (Rst (econst (Fuint 1) [::b0]) (eref (eid v))))) ce, ss)
                   | _ => (ce, ss)
                   end
     | Sfcnct (Eid rg) e =>
       let tr := fst (CE.vtyp rg ce) in
       match tr with
       | Reg_typ r => match (reset r) with
                      | Rst c ei => match type_of_hfexpr c ce with
                                    | Gtyp Freset => (ce, SV.upd rg (r_fexpr (emux c ei e)) ss)
                                    | Gtyp Fasyncreset => (ce, ss) (* TODO: check the scala code again *)
                                    | _ => (ce, ss)
                                    end
                      | _ => (ce, ss)
                      end
       | _ => (ce, ss)
       end
     | Sinvalid (Eid rg) =>
       let tr := fst (CE.vtyp rg ce) in
       match tr with
       | Reg_typ r => let ce_addnode := CE.add vtmp (aggr_typ (type r), Node) ce in
                      let sv_addinv := SV.upd vtmp (r_default) ss in
                      match (reset r) with
                      | Rst c ei => match type_of_hfexpr c ce with
                                    | Gtyp Freset => (ce_addnode, SV.upd rg (r_fexpr (emux c ei (eref (eid vtmp)))) sv_addinv)
                                    | _ => (ce, ss)
                                    end
                      | _ => (ce, ss)
                      end
       | _ => (ce, ss)
       end
     | _ => (ce, ss)
     end.
   
  
End MakeHiFirrtl.


Module HiFirrtl := MakeHiFirrtl VarOrder VS VM CE StructState.
