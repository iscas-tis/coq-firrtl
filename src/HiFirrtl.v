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
  .

  Inductive hfcircuit : Type := Fcircuit : var -> seq hfmodule -> hfcircuit.

End HiFirrtl.


(* A mapping from a variable to its component type *)

Section Component_types.

  Variable var : eqType.
  
  Inductive cmpnt_init_typs : Type :=
  | Aggr_typ : ftype -> cmpnt_init_typs
  | Reg_typ : hfreg var -> cmpnt_init_typs
  | Mem_typ : hfmem var -> cmpnt_init_typs
  | Unknown_typ : cmpnt_init_typs.
  
  (* type of component type *)
  Definition type_of_cmpnttyp ct :=
    match ct with
    | Aggr_typ t => t
    | Reg_typ r => type r
    | Mem_typ m => data_type m
    | Unknown_typ => Gtyp (Fuint 0)
    end.
  
End Component_types.

Module Type CmpntEnv (V : SsrOrder) <: SsrFMap.
  Include SsrFMap.

  Local Notation var := V.t.
  Local Notation cmpnttyp := (cmpnt_init_typs V.T).
  Definition env : Type := t (cmpnttyp * fcomponent).
  (* The default type of a variable not in the typing environment *)
  Parameter deftyp : cmpnttyp * fcomponent.
  (* Find the type of a variable in a typing environment.
     If a variable is not in the typing environment, return the default type. *)
  Parameter vtyp : SE.t -> env -> (cmpnttyp * fcomponent).
  (* Return the size of a variable in a typing environment.
     If a variable is not in the typing environment, return the size of the
     default type. *)
  (* Parameter vsize : SE.t -> env -> nat. *)
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
  (* Axiom vsize_add_eq : *)
  (*   forall {x y : SE.t} {ty : fgtyp} {e : env}, *)
  (*     x == y -> vsize x (add y ty e) = sizeof_fgtyp ty. *)
  (* Axiom vsize_add_neq : *)
  (*   forall {x y : SE.t} {ty : fgtyp} {e : env}, *)
  (*     x != y -> vsize x (add y ty e) = vsize x e. *)
  Axiom not_mem_vtyp :
    forall {v : SE.t} {e : env}, ~~ mem v e -> vtyp v e = deftyp.
  (* Axiom vtyp_vsize : *)
  (*   forall {x : SE.t} {e : env} {ty : fgtyp}, *)
  (*     vtyp x e = ty -> vsize x e = sizeof_fgtyp ty. *)

  Parameter Add : SE.t -> (cmpnttyp * fcomponent) -> env -> env -> Prop.
  Parameter Add_add : forall v f e, Add v f e (add v f e).

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

  Definition Add x c e e' := forall y, vtyp y e' = vtyp y (add x c e).
  Lemma Add_add : forall v f e, Add v f e (add v f e).
  Proof. done. Qed.

  Definition add_fst (v : V.t) (c : cmpnttyp) (e : env) : env :=
    let (f, s) := vtyp v e in add v (c, s) e.
  Definition add_snd (v : V.t) (fc : fcomponent) (e : env) : env :=
    let (f, s) := vtyp v e in add v (f, fc) e. About Lemmas.find_add_eq.
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
  Module Lemmas := FMapLemmas CE.

  Local Notation var := V.t.
  Local Notation value := (rhs_expr V.T).

  Parameter t : Type.
  (* Parameter map2 : (value -> value -> value) -> t -> t ->t. *)
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
End MakeStructStore.

Module StructState := MakeStructStore VarOrder CE.

Module MakeHiFirrtl
       (V : SsrOrder)
       (VS : SsrFSet with Module SE := V)
       (VM : SsrFMap with Module SE := V)
       (CE : CmpntEnv V with Module SE := V)
       (SV : StructStore V CE).
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
    | Fclock, Fclock => true
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
      match orient_of_field b2 v1, type_of_field b2 v1 with
      | Some fp2, Some t2 => (same_ffilp fp1 fp2 && (ftype_equiv t1 t2))
      | None, None => true
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
  
  (** Pass Resolvekinds *)
  
  (* Resolve compnent kind from statement, init with unknown type *)
  Inductive resolveKinds_stmt : hfstmt -> cenv -> cenv -> Prop :=
  | Resolve_wire v t (ce : cenv) (ce' : cenv) :
      CE.Add v (unknown_typ, Wire) ce ce' ->
      resolveKinds_stmt (swire v t) ce ce'
  | Resolve_reg v r ce ce' :
      CE.Add v (unknown_typ, Register) ce ce' ->
      resolveKinds_stmt (sreg v r) ce ce'
  | Resolve_inst v1 v2 ce ce' :
      CE.Add v1 (unknown_typ, Instanceof) ce ce' ->
      resolveKinds_stmt (sinst v1 v2) ce ce'
  | Resolve_node v e ce ce' :
      CE.Add v CE.deftyp ce ce' ->
      resolveKinds_stmt (snode v e) ce ce'
  | Resolve_mem v m ce ce' :
      CE.Add v (unknown_typ, Memory) ce ce' ->
      resolveKinds_stmt (smem v m) ce ce'
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
      CE.Add v (unknown_typ, In_port) ce ce' ->
      resolveKinds_port (hinport v t) ce ce'
  | Resolve_output v t ce ce' :
      CE.Add v (unknown_typ, Out_port) ce ce' ->
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
      CE.Add vm (unknown_typ, Fmodule) ce ce' ->
      resolveKinds_module (hfinmod vm ps ss) ce ce
  | Resolves_exmod vm ps ss ce ce' :
      CE.Add vm (unknown_typ, Fmodule) ce ce' ->
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
    | Swire v t => CE.add v (aggr_typ t, Wire) ce
    | Sreg v r => CE.add v (reg_typ r, Register) ce
    | Smem v m => CE.add v (mem_typ m, Memory) ce
    | Snode v e => CE.add v (unknown_typ, Node) ce
    | Sinst v m => CE.add v (unknown_typ, Instanceof) ce
    | Skip => ce
    end.

  Fixpoint resolveKinds_stmts_fun sts ce : CE.env := fold_right resolveKinds_stmt_fun sts ce.

  Definition resolveKinds_port_fun p ce :=
    match p with
    | Finput v t => CE.add v (t, In_port) ce
    | Foutput v t => CE.add v (t, Out_port) ce
    end.

  Fixpoint resolveKinds_ports_fun ps ce := fold_right resolveKinds_port_fun ps ce.
    
  
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
         | Fflips v1 Flipped t1 fs1, Fflips v2 Flipped t2 fs2 =>
           if v1 == v2 then
             (Fflips v1 Flipped (mux_types t1 t2) (mux_btyps fs1 fs2))
           else Fnil
         (* | Fflips v1 Nflip t1 fs1, Fflips v2 Nflip t2 fs2 => *)
         (*   if v1 == v2 then *)
         (*     (Fflips v1 Flipped (mux_types t1 t2) (mux_btyps fs1 fs2)) *)
         (*   else Fnil *)
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
                         | _ => def_ftype
                         end
    | Ecast AsSInt e1 => let t := type_of_hfexpr e1 ce in
                         match t with
                         | Gtyp (Fsint w) | Gtyp (Fuint w) => Gtyp (Fsint w)
                         | Gtyp Fclock => Gtyp (Fsint 1)
                         | _ => def_ftype
                         end
    | Ecast AsClock e1 => let t := type_of_hfexpr e1 ce in
                          match t with
                          | Gtyp _ =>  Gtyp Fclock
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
    | Eprim_binop Bsdiv e1 e2 => let t1 := type_of_hfexpr e1 ce in
                                 let t2 := type_of_hfexpr e2 ce in
                                 match t1, t2 with
                                 | Gtyp (Fuint w1), Gtyp (Fuint w2) => Gtyp (Fuint w1)
                                 | Gtyp (Fsint w1), Gtyp (Fsint w2) => Gtyp (Fsint (w1 + 1))
                                 | _, _ => def_ftype
                                 end
    | Eprim_binop Brem e1 e2
    | Eprim_binop Bsrem e1 e2 => let t1 := type_of_hfexpr e1 ce in
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


  (** Pass InferType *)
  (* infer type according to a statement *)
  Inductive inferType_stmt : hfstmt -> cenv -> cenv -> Prop :=
  | Infertype_wire v t ce ce' :
      CE.Add_fst v (aggr_typ t) ce ce' ->
      inferType_stmt (swire v t) ce ce'
  | Infertype_reg v r ce ce' :
      CE.Add_fst v (reg_typ r) ce ce' ->
      inferType_stmt (sreg v r) ce ce'
  | Infertype_inst v1 v2 ce ce' :
      CE.Add_fst v1 (fst (CE.vtyp v2 ce)) ce ce' ->
      inferType_stmt (sinst v1 v2) ce ce'
  | Infertype_node v e ce ce' :
      CE.Add_fst v (aggr_typ (type_of_hfexpr e ce)) ce ce' ->
      inferType_stmt (snode v e) ce ce'
  | Infertype_mem v m ce ce' :
      CE.Add_fst v (mem_typ m) ce ce' ->
      inferType_stmt (smem v m) ce ce'.

  Inductive inferType_stmts : seq hfstmt -> cenv -> cenv -> Prop :=
  | Infertype_stmts_nil ce :
      inferType_stmts [::] ce ce
  | Infertype_stmts_con s ss ce ce' ce'' :
      inferType_stmt s ce ce' ->
      inferType_stmts ss ce' ce'' ->
      inferType_stmts (s::ss) ce ce''.

  (* infer type according to ports declaration *)
  Inductive inferType_port : hfport -> cenv -> cenv -> Prop :=
  | Infertype_inport v t ce ce' :
      CE.Add_fst v (aggr_typ t) ce ce' ->
      inferType_port (hinport v t) ce ce'
  | Infertype_outport v t ce ce' :
      CE.Add_fst v (aggr_typ t) ce ce' ->
      inferType_port (hinport v t) ce ce'.

  Inductive inferType_ports : seq hfport -> cenv -> cenv -> Prop :=
  | infertype_ports_nil ce :
      inferType_ports [::] ce ce
  | infertype_ports_con s ss ce ce' ce'' :
      inferType_port s ce ce' ->
      inferType_ports ss ce' ce'' ->
      inferType_ports (s::ss) ce ce''.

  Fixpoint inst_type_of_ports ps :=
    match ps with
    | nil => Fnil
    | cons p ps => match p with
                   | Finput v t => Fflips (v2var v) Flipped t (inst_type_of_ports ps)
                   | Foutput v t => Fflips (v2var v) Nflip t (inst_type_of_ports ps)
                   end
    end.

  Definition inst_type_of_ports' ps :=
    match ps with
    | Btyp Fnil => def_ftype
    | ps => ps
    end.

  (* infer type of module according to ports declaration *)
  Inductive inferType_module : hfmodule -> cenv -> cenv -> Prop :=
  | infertype_inmod vm ps ss ce ce' :
      CE.Add_fst vm (aggr_typ (Btyp (inst_type_of_ports ps))) ce ce' ->
      inferType_module (hfinmod vm ps ss) ce ce'
  | infertype_exmod vm ps ss ce ce' :
      CE.Add_fst vm (aggr_typ (Btyp (inst_type_of_ports ps))) ce ce' ->
      inferType_module (hfexmod vm ps ss) ce ce'.
  
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
         | Fflips v f tv fs => is_deftyp tv && (is_deftyp_f fs)
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
         | Fnil, Fnil => bt1
         | Fflips v1 ft1 t1 fs1, Fflips v2 ft2 t2 fs2 =>
           Fflips v1 ft1 (max_width t1 t2) (max_width_f fs1 fs2)
         | Fnil, _ => bt1
         | f, Fnil => f
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
   
  (** Pass InferWidth *)
  
  (* Infer unknown width
     Infers the smallest width is larger than all assigned widths to a signal
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
     | Eid v => CE.add v t w
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

   Fixpoint inferWidth_wmap0 (s : hfstmt) (ce : cenv) (w : wmap0) {struct s}: wmap0 :=
       match s with
     | Snode v e => w
     | Swire v t => if is_deftyp t then add_ref_wmap0 (Eid v) t ce w else w
     | Sreg v (mk_freg t cl (Rst (Eref rs) e)) =>
       let w1 w := add_ref_wmap0 (Eid v) (type_of_hfexpr e ce) ce w in
       let w2 w:= add_ref_wmap0 rs (Gtyp (Fuint 1)) ce w in 
       if (is_deftyp t) && (is_deftyp (type_of_ref rs ce)) then (w2 (w1 w))
       else if (is_deftyp t) then (w1 w)
            else if (is_deftyp (type_of_ref rs ce)) then (w2 w) else w
     | Sfcnct r1 (Eref r2) =>
       let w1 w := add_ref_wmap0 r1 (type_of_ref r2 ce) ce w in
       let w2 w := add_ref_wmap0 r2 (type_of_ref r1 ce) ce w in
       if is_deftyp (type_of_ref r1 ce) && (is_deftyp (type_of_ref r2 ce)) then (w2 (w1 w))
       else if is_deftyp (type_of_ref r1 ce) then w1 w
            else if is_deftyp (type_of_ref r2 ce) then w2 w else w
     | Sfcnct r e =>
       let w1 := add_ref_wmap0 r (type_of_hfexpr e ce) ce w in
       if is_deftyp (type_of_ref r ce) then w1 else w
     | Spcnct r1 (Eref r2) =>
       let w1 w := add_ref_wmap0 r1 (type_of_ref r2 ce) ce w in
       let w2 w := add_ref_wmap0 r2 (type_of_ref r1 ce) ce w in
       if is_deftyp (type_of_ref r1 ce) && (is_deftyp (type_of_ref r2 ce)) then (w2 (w1 w))
       else if is_deftyp (type_of_ref r1 ce) then w1 w
            else if is_deftyp (type_of_ref r2 ce) then w2 w else w
     | Spcnct r e =>
       let w1 := add_ref_wmap0 r (type_of_hfexpr e ce) ce w in
       if is_deftyp (type_of_ref r ce) then w1 else w
     | Swhen (Eref rs) s1 s2 =>
       let w1 w := add_ref_wmap0 rs (Gtyp (Fuint 1)) ce w in
       let fix aux ss ce w :=
           match ss with
           | nil => w
           | s :: ss => aux ss ce (inferWidth_wmap0 s ce w)
           end
       in
       if (is_deftyp (type_of_ref rs ce))
       then aux s2 ce (aux s1 ce (w1 w))
       else aux s2 ce (aux s1 ce w)
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

   Lemma inferWidth_deftyp :
     forall s ce w w',
       inferWidth_wmap0 s ce w = w' ->
       forall v, ~~ is_deftyp (finds0 v w).
   Proof.
   Admitted.

   Fixpoint inferWidth_stmts_wmap0 ss ce w: wmap0 :=
     match ss with
     | nil => w
     | s :: sts => inferWidth_stmts_wmap0 sts ce (inferWidth_wmap0 s ce w)
     end.

   Definition add_width_2_cenv (w : option ftype) (t : option (cmpnt_init_typs * fcomponent)) :=
     match t, w with
     | Some (Aggr_typ (Gtyp (Fuint 0)), c), Some w => Some (aggr_typ w, c)
     | Some (Reg_typ (mk_freg (Gtyp (Fuint 0)) _ _), c), Some w => Some (aggr_typ w, c)
     | t , _ => t
     end.
   
   (* overwirte types width in ce by wmap with the same index *)

   Definition wmap_map2_cenv w ce : CE.env :=
     CE.map2 add_width_2_cenv w ce.

   Definition inferWidth_fun ss ce : CE.env :=
    wmap_map2_cenv (inferWidth_stmts_wmap0 ss ce empty_wmap0) ce.


   (** Pass ExpandConnect *)

   (** TBD *)  
   Parameter new_vecvar : var -> nat -> var.

   Fixpoint new_vars_atyp r n t te : CE.env :=
     match n with
     | 0 => te
     | S m => new_vars_atyp r m t (CE.add (new_vecvar r n) t te)
     end.
   
   Parameter new_bdvar : var -> Var.var -> var.
   Parameter var2v : Var.var -> V.T.
   
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
      eval_port (Finput (new_vecvar v n) t) ce cs ce'' cs'' ->
      eval_port (Finput v (Atyp t n.-1)) ce' cs' ce'' cs'' ->
      eval_port (Finput v (Atyp t n)) ce cs ce'' cs''
  (* in, bundle type non flip *)
  | Eval_inport_bt_nf v vt t fs n ce cs ce' cs' ce'' cs'':
      0 < n ->
      eval_port (Finput (new_bdvar v vt) t) ce cs ce'' cs'' ->
      eval_port (Finput v (Btyp fs)) ce' cs' ce'' cs'' ->
      eval_port (Finput v (Btyp (Fflips vt Nflip t fs))) ce cs ce'' cs''
  (* in, bundle type flip *)
  | Eval_inport_bt_f v vt t fs n ce cs ce' cs' ce'' cs'':
      0 < n ->
      eval_port (Foutput (new_bdvar v vt) t) ce cs ce'' cs'' ->
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
      eval_port (Foutput (new_vecvar v n) t) ce cs ce'' cs'' ->
      eval_port (Foutput v (Atyp t n.-1)) ce' cs' ce'' cs'' ->
      eval_port (Foutput v (Atyp t n)) ce cs ce'' cs''
  (* out, bundle type *)
  | Eval_outport_bt_nf v vt t fs n ce cs ce' cs' ce'' cs'':
      0 < n ->
      eval_port (Foutput (new_bdvar v vt) t) ce cs ce'' cs'' ->
      eval_port (Foutput v (Btyp fs)) ce' cs' ce'' cs'' ->
      eval_port (Foutput v (Btyp (Fflips vt Nflip t fs))) ce cs ce'' cs''
  (* out, bundle type flip *)
  | Eval_outport_bt_f v vt t fs n ce cs ce' cs' ce'' cs'':
      0 < n ->
      eval_port (Finput (new_bdvar v vt) t) ce cs ce'' cs'' ->
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
      CE.Add v (aggr_typ t, Wire) ce ce' ->
      (* SV.Upd v (r_ftype t) cs cs' -> *)
      SV.Upd v r_default cs cs' ->
      eval_fstmt_single (swire v t) ce cs ce' cs'
  (* declare node with expr, valid rhs *)
  | Eval_snode v e ce cs ce' cs':
      valid_rhs_fexpr e ce' ->
      CE.Add v (aggr_typ (type_of_hfexpr e ce), Node) ce ce' ->
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
      CE.Add (base_ref v) (CE.vtyp (base_ref v) ce) ce ce' ->
      SV.Upd (new_bdvar (base_ref v) (v2var (get_field_name v))) (r_fexpr e) cs cs' ->
      eval_fstmt_single (sfcnct v e) ce cs ce' cs'
  (* declare reg, reset expr type equiv with reg type*)
  | Eval_sreg_r r t c rc rs ce cs ce' cs' :
      valid_rhs_fexpr rs ce ->
      ftype_equiv (type_of_hfexpr rs ce) t ->
      CE.Add r (reg_typ (mk_hfreg t c (rrst rc rs)), Register) ce ce' ->
      (* SV.Upd r (r_fstmt (sreg r (mk_hfreg t c (rrst rc rs)))) cs cs' -> *)
      SV.Upd r r_default cs cs' ->
      eval_fstmt_single (sreg r (mk_hfreg t c (rrst rc rs))) ce cs ce' cs'
  (* declare reg, non reset *)
  | Eval_sreg_nr r t c ce cs ce' cs' :
      CE.Add r (reg_typ (mk_hfreg t c nrst) , Register) ce ce' ->
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
    
  
   
  
End MakeHiFirrtl.


Module HiFirrtl := MakeHiFirrtl VarOrder VS VM CE StructState.
