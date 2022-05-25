From Coq Require Import FunInd FMaps FMapAVL OrderedType ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat ssrint eqtype seq.
From simplssrlib Require Import Types SsrOrder FSets FMaps Tactics Var Store.
From nbits Require Import NBits.
From firrtl Require Import Firrtl Env.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


Import LoFirrtl.

Section HiFirrtl.

  (****** Oriented type ******)
  Inductive forient : Type :=
  | Source | Sink | Duplex.

  Inductive fcomponent : Type :=
  | In_port : var -> fcomponent
  | Instanceof : var -> fcomponent
  | Memory : var -> fcomponent
  | Node : var -> fcomponent
  | Out_port : var -> fcomponent
  | Register : var -> fcomponent
  | Wire : var -> fcomponent
  .

  (* TBD *)
  (* Definition orient_of_type *)

  
  (****** Bundle type ******)
  Inductive fflip : Type := Flipped | Nflip.

  Inductive ftype : Type :=
  | Btyp : ffields -> ftype
  | Gtyp : fgtyp -> ftype
  | Atyp : fgtyp -> nat -> ftype
  
  with ffields : Type :=
  | Fflips : var -> fflip -> ftype -> ffields -> ffields
  | Fnil : ffields
  .


  
  (****** Syntax ******)

  (****** Expressions ******)

  Inductive hfexpr : Type :=
  | Lfexpr : fexpr -> hfexpr
  | Esubfield : fexpr -> fexpr -> hfexpr (* HiFirrtl *)
  | Eaccess : fexpr -> fexpr -> hfexpr (* HiFirrtl *)
  .

  (****** Statements ******)

  Inductive hfstmt : Type :=
  | Lfstmt : fstmt -> hfstmt
  | Spcnct : hfexpr -> hfexpr -> hfstmt
  | Sinvalid : var -> hfstmt
  (* | Sattach : seq var -> fstmt *)
  | Swhen : fexpr -> seq hfstmt -> seq hfstmt -> hfstmt
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


  (** repr for a hifirrtl semantics  *)
  Inductive assgn : Type :=
  | Reg_init : var -> freg -> assgn
  | Wire_init : var -> fgtyp -> assgn
  | Mem_init : var -> fmem -> assgn
  | Node_as : var -> fexpr -> assgn
  | Cnct_as : var -> fexpr -> assgn
  | NAssign : assgn.

  (** eq dec *)
  Axiom assgn_eq_dec : forall {x y : assgn}, {x = y} + {x <> y}.
  Parameter assgn_eqn : forall (x y : assgn), bool.
  Axiom assgn_eqP : Equality.axiom assgn_eqn. 
  Canonical assgn_eqMixin := EqMixin assgn_eqP.
  Canonical assgn_eqType := Eval hnf in EqType assgn assgn_eqMixin.


  (** using assgn to explain hifirrtl statement semantics, with conditional stmt *)
  Inductive eval_fstmt_group : hfstmt -> assgn -> Type :=
  | Gsskip : eval_fstmt_group (Lfstmt sskip) NAssign
  | Gswire v t : eval_fstmt_group (Lfstmt (swire v t)) (Wire_init v t)
  | Gsnode v e : eval_fstmt_group (Lfstmt (snode v e)) (Node_as v e)
  | Gsfcnct v e : eval_fstmt_group (Lfstmt (sfcnct (Eref v) e)) (Cnct_as v e)
  | Gsreg (r:freg) : eval_fstmt_group (Lfstmt (sreg r)) (Reg_init (rid r) r)
  | Gsmem m : eval_fstmt_group (Lfstmt (smem m)) (Mem_init (mid m) m)
  .

  Parameter new_var : var -> Prop.
  
  (** using assgn to explain statement group semantics, including last cnct *)
  Inductive eval_fstmts_group : seq hfstmt -> seq assgn -> Type :=
  | Gnil : eval_fstmts_group [::] [::]
  (** connect to a dst which has been connected to *)
  | Gfstmts_last_cncts v e hst_tl asgn_ls :
      forall e1, (In (Cnct_as v e1) asgn_ls) -> 
                 eval_fstmts_group hst_tl (rem (Cnct_as v e1) asgn_ls) ->
                 eval_fstmts_group ((Lfstmt (sfcnct (eref v) e)) :: hst_tl)
                                   ((Cnct_as v e) :: (rem (Cnct_as v e1) asgn_ls))
  (** connect to a dst which has been initialized as sreg *)
  | Gfstmts_reg_last_cnct v e hst_tl asgn_ls :
      forall e1, (In (Reg_init v e1) asgn_ls) -> 
                 eval_fstmts_group hst_tl asgn_ls ->
                 eval_fstmts_group ((Lfstmt (sfcnct (eref v) e)) :: hst_tl)
                                   ((Cnct_as v e) :: asgn_ls)
  (** connect to a dst which has "not" been connect to *)
  | Gfstmts_cnct_0 v e hst_tl asgn_ls :
      forall e1, ~ In (Cnct_as v e1) asgn_ls ->
                 eval_fstmts_group hst_tl asgn_ls ->
                 eval_fstmts_group ((Lfstmt (sfcnct (eref v) e)) :: hst_tl)
                                   ((Cnct_as v e) :: asgn_ls)
  (**  claim a sreg *)
  | Gfstmts_init_0 (r: freg) hst_tl asgn_ls: 
       eval_fstmts_group hst_tl asgn_ls ->
       eval_fstmts_group (Lfstmt (sreg r) :: hst_tl)
                         ((Reg_init (rid r) r) :: asgn_ls)
  (** claim a node *)
  | Gnode_fstmts v e hst_tl asgn_ls :
      eval_fstmts_group hst_tl asgn_ls ->
      eval_fstmts_group (Lfstmt (snode v e) :: hst_tl) ((Node_as v e)::asgn_ls)
  (** skip *)
  | Gskip_fstmts hst_tl asgn_ls :
      eval_fstmts_group hst_tl asgn_ls ->
      eval_fstmts_group (Lfstmt sskip :: hst_tl) asgn_ls
  (** condition when *)
  | Gwhen_fstmts c hstg1 hstg2 hst_tl asgn_ls :
      eval_fstmts_group_branch c hstg1 hstg2 hst_tl asgn_ls ->
      eval_fstmts_group ((Swhen c hstg1 hstg2) :: hst_tl) asgn_ls
                        
  (** https://github.com/llvm/circt/blob/main/lib/Dialect/FIRRTL/Transforms/ExpandWhens.cpp *)
  with eval_fstmts_group_branch :
         fexpr -> seq hfstmt -> seq hfstmt -> seq hfstmt -> seq assgn -> Type :=
  (** nil *)
  | Gthen_else_def c hstg_tl asgn_ls:
      eval_fstmts_group hstg_tl asgn_ls ->
      eval_fstmts_group_branch c [::] [::] hstg_tl asgn_ls

  (** connect to dst in then branch which has "not" been connected previously *)
  | Gthen_cnct_0 c v e hstg1 hstg2 hstg_tl asgn_ls :
      forall e1, ~ In (Cnct_as v e1) asgn_ls ->
                 eval_fstmts_group_branch c hstg1 hstg2 hstg_tl asgn_ls ->
                 eval_fstmts_group_branch c ((Lfstmt (sfcnct (eref v) e)) :: hstg1) hstg2 hstg_tl
                                          ((Cnct_as v e1) :: asgn_ls)
  (** connect to dst in else branch which has "not" been connected previously *)
  | Gelse_cnct_0 c v e hstg2 hstg_tl asgn_ls :
      forall e1, ~ In (Cnct_as v e1) asgn_ls ->
                 eval_fstmts_group_branch c [::] hstg2 hstg_tl asgn_ls ->
                 eval_fstmts_group_branch c [::] ((Lfstmt (sfcnct (eref v) e)) :: hstg2) hstg_tl
                                          ((Cnct_as v e1) :: asgn_ls)
  (** connect to dst in then branch which has been connected previously *)
  | Gthen_cnct c v vn e hstg1 hstg2 hstg_tl asgn_ls :
      forall e1, In (Cnct_as v e1) asgn_ls ->
                 eval_fstmts_group_branch c hstg1 hstg2 hstg_tl (rem (Cnct_as v e1) asgn_ls) ->
                 new_var vn ->
                 eval_fstmts_group_branch c ((Lfstmt (sfcnct (eref v) e)) :: hstg1) hstg2 hstg_tl
                                          ([::(Node_as vn (emux c e e1)); (Cnct_as v (eref vn))]++(rem (Cnct_as v e1) asgn_ls))
  (** connect to dst in else branch which has been connected previously *)
  | Gelse_cnct c v vn e hstg1 hstg2 hstg_tl asgn_ls :
      forall e1, In (Cnct_as v e1) asgn_ls ->
                 eval_fstmts_group_branch c hstg1 hstg2 hstg_tl (rem (Cnct_as v e1) asgn_ls) ->
                 new_var vn ->
                 eval_fstmts_group_branch c [::] ((Lfstmt (sfcnct (eref v) e)) :: hstg2) hstg_tl
                                          ([::(Node_as vn (emux c e1 e)); (Cnct_as v (eref vn))]++(rem (Cnct_as v e1) asgn_ls))
  (** claim a sreg in then branch *)
  | Gthen_reg c r hstg1 hstg2 hstg_tl asgn_ls :
      eval_fstmts_group_branch c hstg1 hstg2 hstg_tl asgn_ls ->
      eval_fstmts_group_branch c (Lfstmt (sreg r) :: hstg1) hstg2 hstg_tl
                               (Reg_init (rid r) r :: asgn_ls)
  (** claim a sreg in else branch *)
  | Gelse_reg c r hstg2 hstg_tl asgn_ls :
      eval_fstmts_group_branch c [::] hstg2 hstg_tl asgn_ls ->
      eval_fstmts_group_branch c [::] (Lfstmt (sreg r) :: hstg2) hstg_tl
                               (Reg_init (rid r) r :: asgn_ls)
  (** claim a node in then branch *)
  | Gthen_node c v e hstg1 hstg2 hstg_tl asgn_ls :
      eval_fstmts_group_branch c hstg1 hstg2 hstg_tl asgn_ls ->
      eval_fstmts_group_branch c (Lfstmt (snode v e) :: hstg1) hstg2 hstg_tl
                               (Node_as v e :: asgn_ls)
  (** claim a node in else branch *)
  | Gelse_node c v e hstg2 hstg_tl asgn_ls :
      eval_fstmts_group_branch c [::] hstg2 hstg_tl asgn_ls ->
      eval_fstmts_group_branch c [::] (Lfstmt (snode v e) :: hstg2) hstg_tl
                               (Node_as v e :: asgn_ls)
  .


  (** translate from assgn to lofirrtl *)
  (* Definition hi2lo_trans (h : assgn) : fstmt := *)
  (*   match h with *)
  (*   | NAssign => sskip *)
  (*   | Wire_as (v, t) => swire v t *)
  (*   | Node_as (v, e) => snode v e *)
  (*   | Cnct_as (v, e) => sfcnct (Eref v) e *)
  (*   | Reg_as (v, s) => sreg s *)
  (*   end. *)
   

