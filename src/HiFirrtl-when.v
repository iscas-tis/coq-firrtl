From Coq Require Import FunInd FMaps FMapAVL OrderedType ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat ssrint eqtype seq.
From simplssrlib Require Import Types SsrOrder FSets FMaps Tactics Var Store.
From nbits Require Import NBits.
From firrtl Require Import Firrtl Env HiEnv.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


(*Import LoFirrtl.*)

Section HiFirrtl.


  (****** Syntax ******)

  (****** Expressions ******)

  Variable var : eqType.
  
  Inductive hfexpr : Type :=
  | Econst : bits -> hfexpr
  | Eref : var -> hfexpr
  | Ecast : ucast -> hfexpr -> hfexpr
  | Eprim_unop : eunop -> hfexpr -> hfexpr
  | Eprim_binop : ebinop -> hfexpr -> hfexpr -> hfexpr
  | Emux : hfexpr -> hfexpr -> hfexpr -> hfexpr
  | Evalidif : hfexpr -> hfexpr -> hfexpr
  | Esubfield : hfexpr -> hfexpr -> hfexpr (* HiFirrtl *)
  | Eaccess : hfexpr -> hfexpr -> hfexpr (* HiFirrtl *)
  .

  (****** Statements ******)

  Record hfmem : Type :=
    mk_fmem
      {
        mid : var;
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
        rid : var;
        type : ftype;
        clock : hfexpr;
        reset : rst
      }.
  
  Inductive hfstmt : Type :=
  | Sskip
  | Swire : var -> ftype -> hfstmt
  | Sreg : hfreg -> hfstmt
  | Smem : hfmem -> hfstmt
  | Sinst : var -> var -> hfstmt
  | Snode : var -> hfexpr -> hfstmt
  | Sfcnct : hfexpr -> hfexpr -> hfstmt
  | Spcnct : hfexpr -> hfexpr -> hfstmt
  | Sinvalid : var -> hfstmt
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


Section Rhs_expr.
  Variable tmp : eqType.
  Inductive rhs_expr : Type :=
  | R_fexpr : hfexpr tmp -> rhs_expr
  | R_ftype : ftype -> rhs_expr
  | R_fstmt : hfstmt tmp -> rhs_expr
  | R_default
  .

  (** eq dec *)
  Axiom rhs_expr_eq_dec : forall {x y : rhs_expr}, {x = y} + {x <> y}.
  Parameter rhs_expr_eqn : forall (x y : rhs_expr), bool.
  Axiom rhs_expr_eqP : Equality.axiom rhs_expr_eqn. 
  Canonical rhs_expr_eqMixin := EqMixin rhs_expr_eqP.
  Canonical rhs_expr_eqType := Eval hnf in EqType rhs_expr rhs_expr_eqMixin.
  
End Rhs_expr.

Module Type StructStore (V : SsrOrder) (CE : CmpntEnv with Module SE := V).
  Module Lemmas := FMapLemmas CE.

  Local Notation var := V.t.
  Local Notation value := (@rhs_expr V.T).

  Parameter t : Type.
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

Module MakeStructStore (V : SsrOrder) (CE : CmpntEnv with Module SE := V) <:
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
       (CE : CmpntEnv with Module SE := V)
       (SV : StructStore V CE).
  (* Local Open Scope hifirrtl. *)
  
  Module CELemmas := FMapLemmas CE.
  Module VSLemmas := SsrFSetLemmas VS.

  Local Notation var := V.t.
  
  Local Notation cstate := SV.t.


  (* Definition fexpr := fexpr V.T. *)
  (* Definition lofexpr e := @Lfexpr V.T e. *)
  Definition econst c := @Econst V.T c.
  Definition eref v := @Eref V.T v.
  Definition ecast u e := @Ecast V.T u e.
  Definition eprim_unop u e := @Eprim_unop V.T u e.
  Definition eprim_binop b e1 e2 := @Eprim_binop V.T b e1 e2.
  Definition emux c e1 e2 := @Emux V.T c e1 e2.
  Definition evalidif c e := @Evalidif V.T c e.
  Definition hfexpr := hfexpr V.T.
  Definition esubfield e1 e2 := @Esubfield V.T e1 e2.
  Definition eaccess e1 e2 := @Eaccess V.T e1 e2.

  Definition hfstmt := hfstmt V.T.
  Definition sskip := @Sskip V.T.
  Definition swire v t := @Swire V.T v t.
  Definition sreg r := @Sreg V.T r.
  Definition smem m := @Smem V.T m.
  Definition snode v e := @Snode V.T v e.
  Definition sfcnct v1 v2 := @Sfcnct V.T v1 v2.
  Definition spcnct v1 v2 := @Spcnct V.T v1 v2.
  Definition sinvalid v1 := @Sinvalid V.T v1.
  Definition swhen c s1 s2 := @Swhen V.T c s1 s2.
  Definition sstop e1 e2 n := @Sstop V.T e1 e2 n.

  Definition hfreg := @hfreg V.T.
  Definition mk_hfreg := @mk_freg V.T.
  Definition nrst := @NRst V.T.
  Definition rrst e1 e2 := @Rst V.T e1 e2.
  Definition hfmem := @hfmem V.T.
  Definition mk_hfmem := @mk_fmem V.T.
  Definition hfport := @hfport V.T.
  Definition hfmodule := @hfmodule V.T.
  Definition hfcircuit := @hfcircuit V.T.
  
  Definition rhs_expr := rhs_expr V.T.
  Definition r_fexpr e := @R_fexpr V.T e.
  Definition r_ftype t := @R_ftype V.T t.
  Definition r_fstmt s := @R_fstmt V.T s.
  Definition r_default := @R_default V.T.

  (****** Oriented type ******)
  Inductive forient : Type :=
  | Source | Sink | Duplex | Passive.

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

  Fixpoint valid_rhs_fexpr (e : hfexpr) (ce : CE.env) :=
    match e with
    | Econst _ => true
    | Eref v => valid_rhs_orient (orient_of_comp (CE.vtyp v ce))
    | Ecast _ _ => true
    | Eprim_binop _ _ _ => true
    | Eprim_unop _ _ => true
    | Emux _ e1 e2 => valid_rhs_fexpr e1 ce && (valid_rhs_fexpr e2 ce)
    | Evalidif _ e => valid_rhs_fexpr e ce
    | Esubfield e _ => valid_rhs_fexpr e ce
    | Eaccess _ _ => true                                       
    end.

  Definition valid_rhs (re : rhs_expr) (ce : CE.env) : bool :=
    match re with
    | R_default => true
    | R_ftype t => is_passive t
    | R_fexpr e => valid_rhs_fexpr e ce
    | R_fstmt s => match s with
                   | Sreg _ | Smem _ => true
                   | _ => false
                   end
    end.
  
  (****** Semantics ******)
  
  (** evaluation of single statement, update CE.env (var -> fcomponent) and cstate (var -> rhs_expr) *)

  Inductive eval_fstmt_single : hfstmt -> CE.env -> cstate -> CE.env -> cstate -> Prop :=
  | Eval_sskip : forall ce cs, eval_fstmt_single sskip ce cs ce cs
  | Eval_swire v t ce cs ce' cs':
      CELemmas.P.Add v Wire ce ce' ->
      is_passive t ->
      SV.Upd v (r_ftype t) cs cs' ->
      eval_fstmt_single (swire v t) ce cs ce' cs'
  | Eval_snode v e ce cs ce' cs':
      CELemmas.P.Add v Node ce ce' ->
      SV.Upd v (r_fexpr e) cs cs' ->
      valid_rhs_fexpr e ce' ->
      eval_fstmt_single (snode v e) ce cs ce' cs'
  | Eval_sfcnct v e ce cs cs':
      SV.Upd v (r_fexpr e) cs cs' ->
      valid_lhs_orient (orient_of_comp (CE.vtyp v ce)) ->
      valid_rhs_fexpr e ce ->
      eval_fstmt_single (sfcnct (Eref v) e) ce cs ce cs'
  | Eval_sreg r ce cs ce' cs' :
      CELemmas.P.Add (rid r) Register ce ce' ->
      SV.Upd (rid r) (r_fstmt (sreg r)) cs cs' ->
      eval_fstmt_single (sreg r) ce cs ce' cs'
  | Eval_smem m ce cs ce' cs' :
      CELemmas.P.Add (mid m) Memory ce ce' ->
      SV.Upd (mid m) (r_fstmt (smem m)) cs cs' ->
      eval_fstmt_single (smem m) ce cs ce' cs'
  .

  (** evaluation of statement group, last cnct considered *)
  Inductive eval_fstmts_group : seq hfstmt -> CE.env -> cstate -> CE.env -> cstate -> Prop :=
  | Gnil ce cs: eval_fstmts_group [::] ce cs ce cs
  (** connect to a dst *)
  | Gfstmts_last_cncts v e hst_tl ce ce' cs cs' cs'' :
      eval_fstmt_single (sfcnct (Eref v) e) ce cs ce' cs' ->
      eval_fstmts_group hst_tl ce' cs' ce'' cs'' ->
      eval_fstmts_group (sfcnct (Eref v) e :: hst_tl) ce cs ce'' cs''
  (**  claim a sreg *)
  | Gfstmts_reg_init (r: hfreg) hst_tl ce ce' ce'' cs cs' cs'' :
      eval_fstmt_single (sreg r) ce cs ce' cs' ->
      eval_fstmts_group  hst_tl ce' cs' ce'' cs'' ->
      eval_fstmts_group (sreg r :: hst_tl) ce cs ce'' cs''
  (** claim a node *)
  | Gfstmts_node v e hst_tl ce ce' ce'' cs cs' cs'' :
      eval_fstmt_single (snode v e) ce cs ce' cs' ->
      eval_fstmts_group hst_tl ce' cs' ce'' cs'' ->
      eval_fstmts_group (snode v e :: hst_tl) ce cs ce'' cs''
  (** skip *)
  | Gskip_fstmts hst_tl ce ce' cs cs' :
      eval_fstmts_group hst_tl ce cs ce' cs' ->
      eval_fstmts_group (sskip :: hst_tl) ce cs ce' cs'
  (** condition when *)
  | Gwhen_fstmts c hstg1 hstg2 hst_tl ce ce_true ce_false ce_final cs cs_true cs_false cs_final :
      eval_fstmts_group hstg1 ce cs ce_true cs_true ->
      eval_ftsmts_group hstg2 ce cs ce_false cs_false ->
      ((* components that are not defined in ce are only defined in one branch *)
       forall c: CE.t, CE.vtyp c ce = CE.deftyp -> (CE.vtyp c ce_true = CE.deftyp \/ CE.vtyp c ce_false = CE.deftyp)) ->
      eval_fstmts_group hst_tl (map2 union_env ce_true ce_false) (map2 (union_states c) cs_true cs_false) ce_final cs_final ->
      eval_fstmts_group (swhen c hstg1 hstg2 :: hst_tl) ce cs ce_final cs_final

  with union_env : (c_true : option fcomponent) (c_false : option fcomponent) : option fcomponent :=
    match c_true with
    | Some _ => c_true (* <-- if both are defined, we already know that c' and c'' are equal, so it's ok to just use c' *)
    | None => c_false
    end

  (** https://github.com/llvm/circt/blob/main/lib/Dialect/FIRRTL/Transforms/ExpandWhens.cpp *)
  with union_states (c : fexpr) (s_true : option rhs_expr) (s_false : option rhs_expr) : option rhs_expr :=
    match s_true with
    | Some t_true => match s_false with
                     | Some t_true | None => s_true (* <-- expressions identical, or s_false undefined *)
                     | Some t_false => Some (r_fexpr (emux c t_true t_false))
                     end
    | None => s_false
    end
  .

(* or perhaps even simpler, as follows. However, this makes registers defined in when branches have a strange scope.

  (** condition when *)
  | Gwhen_fstmts c hstg1 hstg2 hst_tl ce ce' ce'' cs cs_true cs_false cs_final :
      eval_fstmts_group hstg1 ce cs ce' cs_true ->
      eval_ftsmts_group hstg2 ce' cs ce'' cs_false ->
      eval_fstmts_group hst_tl ce' (map2 (union_states c) cs_true cs_false) ce'' cs_final ->
      eval_fstmts_group (swhen c hstg1 hstg2 :: hst_tl) ce cs ce'' cs_final

  (** https://github.com/llvm/circt/blob/main/lib/Dialect/FIRRTL/Transforms/ExpandWhens.cpp *)
  with union_states (c : fexpr) (s_true : option rhs_expr) (s_false : option rhs_expr) : option rhs_expr :=
    match s_true with
    | Some t_true => match s_false with
                     | Some t_true | None => s_true (* <-- expressions identical, or s_false undefined *)
                     | Some t_false => Some (r_fexpr (emux c t_true t_false))
                     end
    | None => s_false
    end
  .
*)
  
End MakeHiFirrtl.


Module HiFirrtl := MakeHiFirrtl VarOrder VS VM CE StructState.
