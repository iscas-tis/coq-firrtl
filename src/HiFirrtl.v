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

  Inductive sign := Unsigned | Signed.
  
  Inductive hfexpr : Type :=
  | Econst : sign -> bits -> hfexpr
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

(* rhs *)
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
  Local Notation value := (rhs_expr V.T).

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
  Definition econst s c := @Econst V.T s c.
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
  Definition hinport v t := @Finput V.T v t.
  Definition houtport v t := @Foutput V.T v t.
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

  (* rhs expr has right orient *)
  Fixpoint valid_rhs_fexpr (e : hfexpr) (ce : CE.env) :=
    match e with
    | Econst _ _ => true
    | Eref v => let (_,c) := CE.vtyp v ce in valid_rhs_orient (orient_of_comp c)
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

  (** TBD. Flatten. upd ce and cs by flattened atoms in ports *)


  Fixpoint type_of_hfexpr (e : hfexpr) (ce : CE.env) : fgtyp :=
    match e with
    | Econst Signed bs => Fsint (size bs)
    | Econst Unsigned bs => Fuint (size bs)
    | Eref v => fst (CE.vtyp v ce)
    | Ecast AsUInt e1 => Fuint (sizeof_fgtyp (type_of_hfexpr e1 ce))
    | Ecast AsSInt e1 => Fsint (sizeof_fgtyp (type_of_hfexpr e1 ce))
    | Ecast AsClock e1 => Fclock
    | Eprim_unop (Upad n) e1 => let t := type_of_hfexpr e1 ce in
                                match t with
                                | Fsint w => Fsint (maxn w n)
                                | Fuint w => Fuint (maxn w n)
                                | Fclock => Fuint 0
                                end
    | Eprim_unop (Ushl n) e1 => let t := type_of_hfexpr e1 ce in
                                match t with
                                | Fsint w => Fsint (w + n)
                                | Fuint w => Fuint (w + n)
                                | Fclock => Fuint 0
                                end
    | Eprim_unop (Ushr n) e1 => let t := type_of_hfexpr e1 ce in
                                match t with
                                | Fsint w => Fsint (maxn (w - n) 1)
                                | Fuint w => Fuint (maxn (w - n) 1)
                                | Fclock => Fuint 0
                                end
    | Eprim_unop Ucvt e1 => let t := type_of_hfexpr e1 ce in
                                match t with
                                | Fsint w => Fsint w
                                | Fuint w => Fsint (w + 1) 
                                | Fclock => Fuint 0
                                end
    | Eprim_unop Uneg e1 => Fsint (sizeof_fgtyp (type_of_hfexpr e1 ce))
    | Eprim_unop Unot e1 => Fuint (sizeof_fgtyp (type_of_hfexpr e1 ce))
    | Eprim_unop (Uextr n1 n2) e1 => Fuint (n1 - n2 + 1)
    | Eprim_unop (Uhead n) e1 => Fuint n
    | Eprim_unop (Utail n) e1 => Fuint (sizeof_fgtyp (type_of_hfexpr e1 ce) - n)
    | Eprim_unop _ e1 => Fuint 1
    | Eprim_binop (Bcomp _) e1 e2 => Fuint 1
    | Eprim_binop Badd e1 e2
    | Eprim_binop Bsub e1 e2 => let t1 := type_of_hfexpr e1 ce in
                                let t2 := type_of_hfexpr e2 ce in
                                match t1, t2 with
                                | Fuint w1 , Fuint w2 => Fuint (maxn w1 w2 + 1)
                                | Fsint w1 , Fsint w2 => Fsint (maxn w1 w2 + 1)
                                | _, _ => Fuint 0
                                end
    | Eprim_binop Bmul e1 e2 => let t1 := type_of_hfexpr e1 ce in
                                let t2 := type_of_hfexpr e2 ce in
                                match t1, t2 with
                                | Fuint w1 , Fuint w2 => Fuint (w1 + w2)
                                | Fsint w1 , Fsint w2 => Fsint (w1 + w2)
                                | _, _ => Fuint 0
                                end
    | Eprim_binop Bdiv e1 e2
    | Eprim_binop Bsdiv e1 e2 => let t1 := type_of_hfexpr e1 ce in
                                 let t2 := type_of_hfexpr e2 ce in
                                 match t1, t2 with
                                 | Fuint w1 , Fuint w2 => Fuint w1
                                 | Fsint w1 , Fsint w2 => Fsint (w1 + 1)
                                 | _, _ => Fuint 0
                                 end
    | Eprim_binop Brem e1 e2
    | Eprim_binop Bsrem e1 e2 => let t1 := type_of_hfexpr e1 ce in
                                 let t2 := type_of_hfexpr e2 ce in
                                 match t1, t2 with
                                 | Fuint w1 , Fuint w2 => Fuint (minn w1 w2)
                                 | Fsint w1 , Fsint w2 => Fsint (minn w1 w2)
                                 | _, _ => Fuint 0
                                 end
    | Eprim_binop Bdshl e1 e2 => let t1 := type_of_hfexpr e1 ce in
                                 let t2 := type_of_hfexpr e2 ce in
                                 match t1, t2 with
                                 | Fuint w1 , Fuint w2 => Fuint (w1 + 2 ^ w2 - 1)
                                 | Fsint w1 , Fuint w2 => Fsint (w1 + 2 ^ w2 - 1)
                                 | _, _ => Fuint 0
                                 end
    | Eprim_binop Bdshr e1 e2 => let t1 := type_of_hfexpr e1 ce in
                                 let t2 := type_of_hfexpr e2 ce in
                                 match t1, t2 with
                                 | Fuint w1 , Fuint w2 => Fuint w1
                                 | Fsint w1 , Fuint w2 => Fsint w1
                                 | _, _ => Fuint 0
                                 end
    | Eprim_binop _ e1 e2 => let t1 := type_of_hfexpr e1 ce in
                             let t2 := type_of_hfexpr e2 ce in
                             Fuint (maxn (sizeof_fgtyp t1) (sizeof_fgtyp t2))
    | Emux c e1 e2 => let t1 := type_of_hfexpr e1 ce in
                      let t2 := type_of_hfexpr e2 ce in
                      Fuint (maxn (sizeof_fgtyp t1) (sizeof_fgtyp t2))
    | Evalidif c e1 => type_of_hfexpr e1 ce
    | Esubfield _ _ | Eaccess _ _ => Fuint 0
    end.

  (* ground type equivalence *)
  Definition fgtyp_equiv t1 t2 :=
    match t1, t2 with
    | Fuint _, Fuint _ 
    | Fsint _, Fsint _ 
    | Fclock, Fclock => true
    | _, _ => false
    end.

  Definition change_width t s:=
    match t with
    | Fuint _ => Fuint s
    | Fsint _ => Fsint s
    | Clock => Clock
    end.


  (* TBD *)
  Parameter new_vecvar : var -> nat -> var.
  Parameter new_bdvar : var -> Var.var -> var.

  
  (** semantics of declaim  ports *)
  Inductive eval_port : hfport -> CE.env -> cstate -> CE.env -> cstate -> Prop :=
  (* in, ground type *)
  | Eval_inport_gt v t ce cs ce' cs': 
      CELemmas.P.Add v (t, In_port) ce ce' ->
      SV.Upd v (r_ftype (Gtyp t)) cs cs' ->
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
      CELemmas.P.Add v (t, In_port) ce ce' ->
      SV.Upd v (r_ftype (Gtyp t)) cs cs' ->
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
  
  (** semantics of single statement, update CE.env (var -> fgtyp * fcomponent) and cstate (var -> rhs_expr) *)

  
  Inductive eval_fstmt_single : hfstmt -> CE.env -> cstate -> CE.env -> cstate -> Prop :=
  | Eval_sskip : forall ce cs, eval_fstmt_single sskip ce cs ce cs
  (* declare wire with ground type *)
  | Eval_swire_gt v t ce cs ce' cs':
      CELemmas.P.Add v (t, Wire) ce ce' ->
      SV.Upd v (r_ftype (Gtyp t)) cs cs' ->
      eval_fstmt_single (swire v (Gtyp t)) ce cs ce' cs'
  (* declare wire with vector type *)
  | Eval_swire_agt v t n ce cs ce' cs' ce'' cs'':
      0 < n ->
      eval_fstmt_single (swire (new_vecvar v n) t) ce cs ce' cs' ->
      eval_fstmt_single (swire v (Atyp t n.-1)) ce' cs' ce'' cs'' ->
      eval_fstmt_single (swire v (Atyp t n)) ce cs ce'' cs''
  (* TBD. declare wire with bundle type *)
  (*| Eval_swire_bt *)
  (* declare node with expr, valid rhs *)
  | Eval_snode v e ce cs ce' cs':
      valid_rhs_fexpr e ce' ->
      CELemmas.P.Add v ((type_of_hfexpr e ce), Node) ce ce' ->
      SV.Upd v (r_fexpr e) cs cs' ->
      eval_fstmt_single (snode v e) ce cs ce' cs'
  (* define full connection *)
  (* valid flow orient, type eq between dst and src, dst width upd to max (current size, src) *)
  | Eval_sfcnct v e ce ce' cs cs':
      valid_lhs_orient (orient_of_comp (snd (CE.vtyp v ce))) ->
      valid_rhs_fexpr e ce ->
      fgtyp_equiv (fst (CE.vtyp v ce)) (type_of_hfexpr e ce) ->
      CELemmas.P.Add v (change_width (fst (CE.vtyp v ce)) (maxn (sizeof_fgtyp (fst (CE.vtyp v ce))) (sizeof_fgtyp (type_of_hfexpr e ce))), snd (CE.vtyp v ce)) ce ce' ->
      SV.Upd v (r_fexpr e) cs cs' ->
      eval_fstmt_single (sfcnct (Eref v) e) ce cs ce' cs'
  (* declare reg with ground type , reset expr type equiv with reg type*)
  | Eval_sreg_r_gt r t c rc rs ce cs ce' cs' :
      fgtyp_equiv (type_of_hfexpr rs ce) t ->
      CELemmas.P.Add r (t , Register) ce ce' ->
      SV.Upd r (r_fstmt (sreg (mk_hfreg r (Gtyp t) c (rrst rc rs)))) cs cs' ->
      eval_fstmt_single (sreg (mk_hfreg r (Gtyp t) c (rrst rc rs))) ce cs ce' cs'
  (* declare reg with ground type, non reset *)
  | Eval_sreg_nr_gt r t c ce cs ce' cs' :
      CELemmas.P.Add r (t , Register) ce ce' ->
      SV.Upd r (r_fstmt (sreg (mk_hfreg r (Gtyp t) c nrst))) cs cs' ->
      eval_fstmt_single (sreg (mk_hfreg r (Gtyp t) c nrst)) ce cs ce' cs'
  (* declare reg with vector ground type *)
  | Eval_sreg_agt r t n c rs ce cs ce' cs' ce'' cs'' :
      0 < n ->
      eval_fstmt_single (sreg (mk_hfreg r t c rs)) ce cs ce' cs' ->
      eval_fstmt_single (sreg (mk_hfreg r (Atyp t n.-1) c rs)) ce' cs' ce'' cs'' ->
      eval_fstmt_single (sreg (mk_hfreg r (Atyp t n) c rs)) ce cs ce'' cs''
  (* declare mem with ground type *)
  | Eval_smem_gt m t dp r w rl wl rw ce cs ce' cs' :
      is_passive (Gtyp t) ->
      CELemmas.P.Add m (t, Memory) ce ce' ->
      SV.Upd m (r_fstmt (smem (mk_hfmem m (Gtyp t) dp r w rl wl rw))) cs cs' ->
      eval_fstmt_single (smem (mk_hfmem m (Gtyp t) dp r w rl wl rw)) ce cs ce' cs'
  (* declare mem with vector ground type *)
  | Eval_smem_agt m t n dp r w rl wl rw ce cs ce' cs' ce'' cs'':
      0 < n ->
      is_passive (Atyp (Gtyp t) n) ->
      CELemmas.P.Add m (t, Memory) ce ce' ->
      SV.Upd (new_vecvar m n) (r_fstmt (smem (mk_hfmem m (Gtyp t) dp r w rl wl rw))) cs cs' ->
      eval_fstmt_single (smem (mk_hfmem m (Atyp (Gtyp t) n.-1) dp r w rl wl rw)) ce' cs' ce'' cs'' ->
      eval_fstmt_single (smem (mk_hfmem m (Atyp (Gtyp t) n) dp r w rl wl rw)) ce cs ce'' cs''
  .

  (** semantics of statement group, last cnct considered *)
  Inductive eval_fstmts_group : seq hfstmt -> CE.env -> cstate -> CE.env -> cstate -> Prop :=
  | Gnil ce cs: eval_fstmts_group [::] ce cs ce cs
  (** connect to a dst *)
  | Gfstmts_last_cncts v e hst_tl ce ce' cs cs' cs'' :
      eval_fstmt_single (sfcnct (Eref v) e) ce cs ce cs' ->
      eval_fstmts_group hst_tl ce cs' ce' cs'' ->
      eval_fstmts_group (sfcnct (Eref v) e :: hst_tl) ce cs ce' cs''
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
  (** connect to dst in then branch which has "not" been connected previously, add then branch *)
  | Gthen_cnct_0 c v e hstg1 hstg2 ce ce' ce'' cs cs' cs'' :
      CE.find v ce == None ->
      eval_fstmt_single (sfcnct (eref v) e) ce cs ce' cs' ->
      eval_fstmts_group_branch c hstg1 hstg2 ce' cs' ce'' cs'' ->
      eval_fstmts_group_branch c (sfcnct (eref v) e :: hstg1) hstg2 ce cs ce'' cs''
  (** connect to dst in else branch which has "not" been connected previously, add else branch *)
  | Gelse_cnct_0 c v e hstg2 ce ce' ce'' cs cs' cs'' :
      CE.find v ce == None ->
      eval_fstmt_single (sfcnct (eref v) e) ce cs ce' cs' ->
      eval_fstmts_group_branch c [::] hstg2 ce' cs' ce'' cs'' ->
      eval_fstmts_group_branch c [::] (sfcnct (eref v) e :: hstg2) ce cs ce'' cs''
  (** connect to dst in then branch which has been connected previously, add mux(p, then, prev) *)
  | Gthen_cnct c v e re hstg1 hstg2 ce ce' cs cs' cs'' :
      SV.acc v cs == r_fexpr re ->
      (* CELemmas.P.Add vn Node ce ce' -> *)
      (* SV.Upd vn (r_fexpr (emux c e re)) cs cs' -> *)
      SV.Upd v (r_fexpr (emux c e re)) cs cs' ->
      eval_fstmts_group_branch c hstg1 hstg2 ce cs' ce' cs'' ->
      eval_fstmts_group_branch c (sfcnct (eref v) e :: hstg1) hstg2 ce cs ce' cs''
  (** connect to dst in else branch which has been connected previously, add mux(p, prev, else) *)
  | Gelse_cnct c v e re hstg2 ce ce' cs cs' cs'' :
      SV.acc v cs == r_fexpr re ->
      SV.Upd v (r_fexpr (emux c re e)) cs cs' ->
      eval_fstmts_group_branch c [::] hstg2 ce cs' ce' cs'' ->
      eval_fstmts_group_branch c [::] (sfcnct (eref v) e :: hstg2) ce cs ce' cs''
  (** claim a sreg in then branch *)
  | Gthen_reg c r hstg1 hstg2 ce ce' ce'' cs cs' cs'' :
      eval_fstmt_single (sreg r) ce cs ce' cs' ->
      eval_fstmts_group_branch c hstg1 hstg2 ce' cs' ce'' cs'' ->
      eval_fstmts_group_branch c (sreg r :: hstg1) hstg2 ce cs ce'' cs''
  (** claim a sreg in else branch *)
  | Gelse_reg c r hstg2 ce ce' ce'' cs cs' cs'' :
      eval_fstmt_single (sreg r) ce cs ce' cs' ->
      eval_fstmts_group_branch c [::] hstg2 ce' cs' ce'' cs'' ->
      eval_fstmts_group_branch c [::] (sreg r :: hstg2) ce cs ce'' cs''
  (** claim a node in then branch *)
  | Gthen_node c v e hstg1 hstg2 ce ce' ce'' cs cs' cs'' :
      eval_fstmt_single (snode v e) ce cs ce' cs' ->
      eval_fstmts_group_branch c hstg1 hstg2 ce' cs' ce'' cs'' ->
      eval_fstmts_group_branch c (snode v e :: hstg1) hstg2 ce cs ce'' cs''
  (** claim a node in else branch *)
  | Gelse_node c v e hstg2 ce ce' ce'' cs cs' cs'' :
      eval_fstmt_single (snode v e) ce cs ce' cs' ->
      eval_fstmts_group_branch c [::] hstg2 ce' cs' ce'' cs'' ->
      eval_fstmts_group_branch c [::] (snode v e :: hstg2) ce cs ce'' cs''
  .

  (* Lemma valid_conncection v e2 sts ce cs ce' cs' : *)
  (*   eval_fstmts_group (sfcnct (eref v) e2 :: sts) ce cs ce' cs' -> *)
  (*   valid_rhs (SV.acc v cs') ce'. *)
    
    
End MakeHiFirrtl.


Module HiFirrtl := MakeHiFirrtl VarOrder VS VM CE StructState.
