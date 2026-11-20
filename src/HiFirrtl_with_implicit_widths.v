From Coq Require Import FunInd FMaps FMapAVL OrderedType ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat ssrint eqtype seq ssrfun.
From simplssrlib Require Import Types SsrOrder FSets FMaps Tactics Var Store.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths.

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
  (* | Evalidif : hfexpr -> hfexpr -> hfexpr *)
  | Eref : href -> hfexpr
  with href : Type :=
  | Eid : var -> href
  | Esubfield : href -> var -> href (* HiFirrtl *)
  | Esubindex : href -> nat -> href (* HiFirrtl *)
  | Esubaccess : href -> hfexpr -> href (* HiFirrtl *)
  .

  (** equality of hfexpr and href are decidable *)
  Lemma hfexpr_eq_dec : forall {x y : hfexpr}, {x = y} + {x <> y}
  with href_eq_dec : forall {x y : href}, {x = y} + {x <> y}.
  (** clear hfexpr_eq_dec.
    destruct x, y ; decide equality ; try (apply fgtyp_eq_dec) ; try (apply ucast_eq_dec) ;
    try (apply eunop_eq_dec) ; try (apply ebinop_eq_dec).
    + destruct (b1 == b2) eqn: H ; move /eqP : H => H ;
      first (by left  ; exact H) ;
      last  (by right ; exact H).
    1-7, 14, 21, 28, 35, 42: destruct (b0 == b1) eqn: H ; move /eqP : H => H ;
      first (by left  ; exact H) ;
      last  (by right ; exact H).
    1-36: destruct (b == b0) eqn: H ; move /eqP : H => H ;
      first (by left  ; exact H) ;
      last  (by right ; exact H).
  * clear href_eq_dec.
    destruct x, y ; decide equality ; try apply Nat.eq_dec.
    + destruct (s1 == s2) eqn: H ; move /eqP : H => H ;
      first (by left  ; exact H) ;
      last  (by right ; exact H).
    1,5,7,17,21,23,25,29,31: destruct (v == v0) eqn: H ; move /eqP : H => H ;
      first (by left  ; exact H) ;
      last  (by right ; exact H).
    1,3-5,13,18: destruct (s0 == s1) eqn: H ; move /eqP : H => H ;
      first (by left  ; exact H) ;
      last  (by right ; exact H).
    1,2,6,8,10,14: destruct (v0 == v1) eqn: H ; move /eqP : H => H ;
      first (by left  ; exact H) ;
      last  (by right ; exact H).
    1,3-10: destruct (s == s0) eqn: H ; move /eqP : H => H ;
      first (by left  ; exact H) ;
      last  (by right ; exact H).
    + destruct (v1 == v2) eqn: H ; move /eqP : H => H ;
      first (by left  ; exact H) ;
      last  (by right ; exact H).
  Qed.*) Admitted.
  Fixpoint hfexpr_eqn (x y : hfexpr) : bool :=
  match x, y with
  | Econst tx bx, Econst ty by_ => (tx == ty) && (bx == by_)
  | Ecast ux ex, Ecast uy ey => (ux == uy) && hfexpr_eqn ex ey
  | Eprim_unop ux ex, Eprim_unop uy ey => (ux == uy) && hfexpr_eqn ex ey
  | Eprim_binop bx ex fx, Eprim_binop by_ ey fy => (bx == by_) && hfexpr_eqn ex ey && hfexpr_eqn fx fy
  | Emux ex fx gx, Emux ey fy gy => hfexpr_eqn ex ey && hfexpr_eqn fx fy && hfexpr_eqn gx gy
  | Eref rx, Eref ry => href_eqn rx ry
  | _, _ => false
  end
  with href_eqn (x y : href) : bool :=
  match x, y with
  | Eid vx, Eid vy => vx == vy
  | Esubfield rx vx, Esubfield ry vy => href_eqn rx ry && (vx == vy)
  | Esubindex rx nx, Esubindex ry ny => href_eqn rx ry && (nx == ny)
  | Esubaccess rx ex, Esubaccess ry ey => href_eqn rx ry && hfexpr_eqn ex ey
  | _, _ => false
  end.
  Lemma hfexpr_eqP : (*Equality.axiom hfexpr_eqn*)
        forall x y : hfexpr, reflect (x = y) (hfexpr_eqn x y)
  with href_eqP : (*Equality.axiom href_eqn*)
        forall x y : href, reflect (x = y) (href_eqn x y).
  Proof.
  clear hfexpr_eqP.
    induction x, y ; simpl ;
          try (apply ReflectF ; discriminate).
    + destruct (f == f0) eqn: Hf ; move /eqP : Hf => Hf ;
            last by (apply ReflectF ; injection ; done).
      rewrite Hf andTb.
      destruct (b == b0) eqn: Hb ; move /eqP : Hb => Hb ;
            last by (apply ReflectF ; injection ; done).
      rewrite Hb.
      apply ReflectT ; reflexivity.
    + destruct (u == u0) eqn: Hu ; move /eqP : Hu => Hu ;
            last by (apply ReflectF ; injection ; done).
      rewrite Hu andTb.
      specialize (IHx y) ; apply reflect_iff in IHx.
      destruct (hfexpr_eqn x y) ;
            last by (apply ReflectF ; injection ; intro ;
                     destruct IHx as [IHx _] ; apply IHx in H0 ; done).
      destruct IHx as [_ IHx] ; rewrite IHx //.
      apply ReflectT ; reflexivity.
    + destruct (e == e0) eqn: He ; move /eqP : He => He ;
            last by (apply ReflectF ; injection ; done).
      rewrite He andTb.
      specialize (IHx y) ; apply reflect_iff in IHx.
      destruct (hfexpr_eqn x y) ;
            last by (apply ReflectF ; injection ; intro ;
                     destruct IHx as [IHx _] ; apply IHx in H0 ; done).
      destruct IHx as [_ IHx] ; rewrite IHx //.
      apply ReflectT ; reflexivity.
    + destruct (e == e0) eqn: He ; move /eqP : He => He ;
            last by (apply ReflectF ; injection ; done).
      rewrite He andTb.
      specialize (IHx1 y1) ; apply reflect_iff in IHx1.
      destruct (hfexpr_eqn x1 y1) ;
            last by (apply ReflectF ; injection ; intros _ H0 ;
                     destruct IHx1 as [IHx1 _] ; apply IHx1 in H0 ; done).
      destruct IHx1 as [_ IHx1] ; rewrite IHx1 //.
      specialize (IHx2 y2) ; apply reflect_iff in IHx2.
      destruct (hfexpr_eqn x2 y2) ;
            last by (apply ReflectF ; injection ; intros H0 ;
                     destruct IHx2 as [IHx2 _] ; apply IHx2 in H0 ; done).
      destruct IHx2 as [_ IHx2] ; rewrite IHx2 //.
      apply ReflectT ; reflexivity.
    + specialize (IHx1 y1) ; apply reflect_iff in IHx1.
      destruct (hfexpr_eqn x1 y1) ;
            last by (apply ReflectF ; injection ; intros _ _ H0 ;
                     destruct IHx1 as [IHx1 _] ; apply IHx1 in H0 ; done).
      destruct IHx1 as [_ IHx1] ; rewrite IHx1 //.
      specialize (IHx2 y2) ; apply reflect_iff in IHx2.
      destruct (hfexpr_eqn x2 y2) ;
            last by (apply ReflectF ; injection ; intros _ H0 ;
                     destruct IHx2 as [IHx2 _] ; apply IHx2 in H0 ; done).
      destruct IHx2 as [_ IHx2] ; rewrite IHx2 //.
      specialize (IHx3 y3) ; apply reflect_iff in IHx3.
      destruct (hfexpr_eqn x3 y3) ;
            last by (apply ReflectF ; injection ; intros H0 ;
                     destruct IHx3 as [IHx3 _] ; apply IHx3 in H0 ; done).
      destruct IHx3 as [_ IHx3] ; rewrite IHx3 //.
      apply ReflectT ; reflexivity.
    + specialize (href_eqP h h0) ; apply reflect_iff in href_eqP.
      destruct (href_eqn h h0) ;
            last by (apply ReflectF ; injection ; intros H0 ;
                     destruct href_eqP as [href_eqP _] ; apply href_eqP in H0 ; done).
      destruct href_eqP as [_ href_eqP] ; rewrite href_eqP //.
      apply ReflectT ; reflexivity.
  * clear href_eqP.
    induction x, y ; simpl ;
          try (apply ReflectF ; discriminate).
    + destruct (s == s0) eqn: Hs ; move /eqP : Hs => Hs ;
            last by (apply ReflectF ; injection ; done).
      rewrite Hs.
      apply ReflectT ; reflexivity.
    + specialize (IHx y) ; apply reflect_iff in IHx.
      destruct (href_eqn x y) ;
            last by (apply ReflectF ; injection ; intros _ H0 ;
                     destruct IHx as [IHx _] ; apply IHx in H0 ; done).
      destruct IHx as [_ IHx] ; rewrite IHx //.
      destruct (s == s0) eqn: Hv ; move /eqP : Hv => Hv ;
            last by (apply ReflectF ; injection ; done).
      rewrite Hv.
      apply ReflectT ; reflexivity.
    + specialize (IHx y) ; apply reflect_iff in IHx.
      destruct (href_eqn x y) ;
            last by (apply ReflectF ; injection ; intros _ H0 ;
                     destruct IHx as [IHx _] ; apply IHx in H0 ; done).
      destruct IHx as [_ IHx] ; rewrite IHx //.
      destruct (n == n0) eqn: Hn ; move /eqP : Hn => Hn ;
            last by (apply ReflectF ; injection ; done).
      rewrite Hn.
      apply ReflectT ; reflexivity.
    + specialize (IHx y) ; apply reflect_iff in IHx.
      destruct (href_eqn x y) ;
            last by (apply ReflectF ; injection ; intros _ H0 ;
                     destruct IHx as [IHx _] ; apply IHx in H0 ; done).
      destruct IHx as [_ IHx] ; rewrite IHx //.
      specialize (hfexpr_eqP h h0) ; apply reflect_iff in hfexpr_eqP.
      destruct (hfexpr_eqn h h0) ;
            last by (apply ReflectF ; injection ; intros H0 ;
                     destruct hfexpr_eqP as [hfexpr_eqP _] ; apply hfexpr_eqP in H0 ; done).
      destruct hfexpr_eqP as [_ hfexpr_eqP] ; rewrite hfexpr_eqP //.
      apply ReflectT ; reflexivity.
  Qed.
  Canonical hfexpr_eqMixin := EqMixin hfexpr_eqP.
  Canonical href_eqMixin := EqMixin href_eqP.
  Canonical hfexpr_eqType := Eval hnf in EqType hfexpr hfexpr_eqMixin.
  Canonical href_eqType := Eval hnf in EqType href href_eqMixin.

  (****** Statements ******)

  Record mem_port : Type :=
    mk_mem_port
      {
        id : var;
        addr : var;
        en : var;
        clk : var;
        mask : var
      }.

  Axiom mem_port_eq_dec : forall {x y : mem_port}, {x = y} + {x <> y}.
  Parameter mem_port_eqn : forall (x y : mem_port), bool.
  Axiom mem_port_eqP : Equality.axiom mem_port_eqn.
  Canonical mem_port_eqMixin := EqMixin mem_port_eqP.
  Canonical mem_port_eqType := Eval hnf in EqType mem_port mem_port_eqMixin.

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

  Lemma hfmem_eq_dec : forall {x y : hfmem}, {x = y} + {x <> y}.
  Proof.  decide equality ; try decide equality ;
          try apply mem_port_eq_dec ;
          try apply fgtyp_eq_dec ; try apply Nat.eq_dec ; try apply ffield_eq_dec.
  Qed.
  Definition hfmem_eqn (x y : hfmem) : bool :=
  (data_type x == data_type y) && (depth x == depth y) &&
  (reader x == reader y) && (writer x == writer y) &&
  (read_latency x == read_latency y) && (write_latency x == write_latency y) &&
  (read_write x == read_write y).
  Lemma hfmem_eqP : Equality.axiom hfmem_eqn.
  Proof.
  unfold Equality.axiom, hfmem_eqn.
  destruct x, y ; simpl.
  destruct (data_type0 == data_type1) eqn: Hdt ; move /eqP : Hdt => Hdt ;
        last by (apply ReflectF ; contradict Hdt ; injection Hdt ; done).
  rewrite Hdt andTb.
  destruct (depth0 == depth1) eqn: Hdp ; move /eqP : Hdp => Hdp ;
        last by (apply ReflectF ; contradict Hdp ; injection Hdp ; done).
  rewrite Hdp andTb.
  destruct (reader0 == reader1) eqn: Hrd ; move /eqP : Hrd => Hrd ;
        last by (apply ReflectF ; contradict Hrd ; injection Hrd ; done).
  rewrite Hrd andTb.
  destruct (writer0 == writer1) eqn: Hwr ; move /eqP : Hwr => Hwr ;
        last by (apply ReflectF ; contradict Hwr ; injection Hwr ; done).
  rewrite Hwr andTb.
  destruct (read_latency0 == read_latency1) eqn: Hrl ; move /eqP : Hrl => Hrl ;
        last by (apply ReflectF ; contradict Hrl ; injection Hrl ; done).
  rewrite Hrl andTb.
  destruct (write_latency0 == write_latency1) eqn: Hwl ; move /eqP : Hwl => Hwl ;
        last by (apply ReflectF ; contradict Hwl ; injection Hwl ; done).
  rewrite Hwl andTb.
  destruct (read_write0 == read_write1) eqn: Hrw ; move /eqP : Hrw => Hrw ;
        last by (apply ReflectF ; contradict Hrw ; injection Hrw ; done).
  rewrite Hrw.
  apply ReflectT ; reflexivity.
  Qed.
  Canonical hfmem_eqMixin := EqMixin hfmem_eqP.
  Canonical hfmem_eqType := Eval hnf in EqType hfmem hfmem_eqMixin.

  Inductive rst : Type :=
  | NRst : rst
  | Rst : hfexpr (* reset trigger signal *) -> hfexpr (* reset value *) -> rst.

  Lemma rst_eq_dec : forall {x y : rst}, {x = y} + {x <> y}.
  Proof.  decide equality ; apply hfexpr_eq_dec.  Qed.
  Definition rst_eqn (x y : rst) : bool :=
  match x, y with
  | NRst, NRst => true
  | Rst t1 r1, Rst t2 r2 => (t1 == t2) && (r1 == r2)
  | _, _ => false
  end.
  Lemma rst_eqP : Equality.axiom rst_eqn.
  Proof.
  unfold Equality.axiom, rst_eqn ; intros.
  destruct x, y ; try (apply ReflectF ; discriminate) ; try (apply ReflectT ; reflexivity).
  destruct (h == h1) eqn: H1 ; move /eqP : H1 => H1.
  * rewrite andTb ; destruct (h0 == h2) eqn: H2 ; move /eqP : H2 => H2.
    + apply ReflectT ; rewrite H1 H2 ; reflexivity.
    + apply ReflectF ; contradict H2 ; injection H2 ; done.
  * rewrite andFb ; apply ReflectF.
    contradict H1 ; injection H1 ; done.
  Qed.
  Canonical rst_eqMixin := EqMixin rst_eqP.
  Canonical rst_eqType := Eval hnf in EqType rst rst_eqMixin.

  Record hfreg : Type :=
    mk_freg
      {
        (* rid : var; *)
        type : ftype;
        clock : hfexpr;
        reset : rst
      }.

  Lemma hfreg_eq_dec : forall {x y : hfreg}, {x = y} + {x <> y}.
  Proof.  decide equality.  apply rst_eq_dec.  apply hfexpr_eq_dec.  apply ftype_eq_dec.  Qed.
  Definition hfreg_eqn (x y : hfreg) : bool :=
  (type x == type y) && (clock x == clock y) && (reset x == reset y).
  Lemma hfreg_eqP : Equality.axiom hfreg_eqn.
  Proof.
  unfold Equality.axiom, hfreg_eqn.
  destruct x, y ; simpl.
  destruct (type0 == type1) eqn: Ht ; move /eqP : Ht => Ht ;
        last by (apply ReflectF ; contradict Ht ; injection Ht ; done).
  rewrite Ht andTb.
  destruct (clock0 == clock1) eqn: Hc ; move /eqP : Hc => Hc ;
        last by (apply ReflectF ; contradict Hc ; injection Hc ; done).
  rewrite Hc andTb.
  destruct (reset0 == reset1) eqn: Hr ; move /eqP : Hr => Hr ;
        last by (apply ReflectF ; contradict Hr ; injection Hr ; done).
  rewrite Hr.
  apply ReflectT ; reflexivity.
  Qed.
  Canonical hfreg_eqMixin := EqMixin hfreg_eqP.
  Canonical hfreg_eqType := Eval hnf in EqType hfreg hfreg_eqMixin.

  Definition inst_ports : Type := seq var.

  Inductive hfstmt : Type :=
  | Sskip
  | Swire : var -> ftype -> hfstmt
  | Sreg : var -> hfreg -> hfstmt
  | Smem : var -> hfmem -> hfstmt
  | Sinst : var -> var -> hfstmt
  | Snode : var -> hfexpr -> hfstmt
  | Sfcnct : href -> hfexpr -> hfstmt
  (* | Spcnct : href -> hfexpr -> hfstmt *)
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

   (** equality of hfstmt and hfstmt_seq are decidable *)
  Lemma hfstmt_eq_dec : forall {x y : hfstmt}, {x = y} + {x <> y}
  with hfstmt_seq_eq_dec : forall {x y : hfstmt_seq}, {x = y} + {x <> y}.
  Proof.
  * clear hfstmt_eq_dec.
    decide equality ; try (apply ftype_eq_dec) ; try (apply hfreg_eq_dec) ;
    try (apply hfmem_eq_dec) ; try (apply hfexpr_eq_dec) ; try (apply href_eq_dec).
    1,2,3,6: destruct (s == s0) eqn: Hss0 ; move /eqP : Hss0 => Hss0 ;
         first (by left  ; exact Hss0) ;
         last  (by right ; exact Hss0).
    destruct (s0 == s2) eqn: Hss0 ; move /eqP : Hss0 => Hss0 ;
         first (by left  ; exact Hss0) ;
         last  (by right ; exact Hss0).
    destruct (s == s1) eqn: Hss0 ; move /eqP : Hss0 => Hss0 ;
         first (by left  ; exact Hss0) ;
         last  (by right ; exact Hss0).
  * clear hfstmt_seq_eq_dec.
    decide equality.
  Qed.
  Fixpoint hfstmt_eqn (x y : hfstmt) : bool :=
  match x, y with
  | Sskip, Sskip => true
  | Swire vx tx, Swire vy ty => (vx == vy) && (tx == ty)
  | Sreg vx rx, Sreg vy ry => (vx == vy) && (rx == ry)
  | Smem vx mx, Smem vy my => (vx == vy) && (mx == my)
  | Sinst vx wx, Sinst vy wy => (vx == vy) && (wx == wy)
  | Snode vx ex, Snode vy ey => (vx == vy) && (ex == ey)
  | Sfcnct rx ex, Sfcnct ry ey => (rx == ry) && (ex == ey)
  (* | Spcnct : href -> hfexpr -> hfstmt *)
  | Sinvalid rx, Sinvalid ry => rx == ry
  (* | Sattach : seq var -> fstmt *)
  | Swhen ex tx fx, Swhen ey ty fy => (ex == ey) && hfstmt_seq_eqn tx ty && hfstmt_seq_eqn fx fy
  (* | Sstop : hfexpr -> hfexpr -> nat -> hfstmt *)
  (* | Sprintf (* TBD *) *)
  (* | Sassert (* TBD *) *)
  (* | Sassume (* TBD *) *)
  (* | Sdefname : var -> fstmt *) (* TBD *)
  (* | Sparam : var -> fexpr -> fstmt *) (* TBD *)
  | _, _ => false
  end
  with hfstmt_seq_eqn (x y : hfstmt_seq) : bool :=
  match x, y with
  | Qnil, Qnil => true
  | Qcons sx qx, Qcons sy qy => hfstmt_eqn sx sy && hfstmt_seq_eqn qx qy
  | _, _ => false
  end.
  Lemma hfstmt_eqP : (*Equality.axiom hfstmt_eqn*)
              forall x y : hfstmt, reflect (x = y) (hfstmt_eqn x y)
  with hfstmt_seq_eqP : (*Equality.axiom hfstmt_seq_eqn*)
              forall x y : hfstmt_seq, reflect (x = y) (hfstmt_seq_eqn x y).
  Proof.
  * clear hfstmt_eqP.
    induction x, y ; simpl ; try (apply ReflectF ; discriminate).
    + apply ReflectT ; reflexivity.
    1-3,5: destruct (s == s0) eqn: Hs ; move /eqP : Hs => Hs ;
               last (by apply ReflectF ; injection ; done) ;
         rewrite Hs andTb.
    + destruct (f == f0) eqn: Hf ; move /eqP : Hf => Hf ;
            last by (apply ReflectF ; injection ; done).
      rewrite Hf.
      apply ReflectT ; reflexivity.
    1-3,6: destruct (h == h0) eqn: Hh ; move /eqP : Hh => Hh ;
               last (by apply ReflectF ; injection ; done) ;
         rewrite Hh ;
         apply ReflectT ; reflexivity.
    + destruct (s == s1) eqn: Hs ; move /eqP : Hs => Hs ;
               last (by apply ReflectF ; injection ; done) ;
            rewrite Hs andTb.
      destruct (s0 == s2) eqn: Hs0 ; move /eqP : Hs0 => Hs0 ;
               last (by apply ReflectF ; injection ; done) ;
            rewrite Hs0.
      apply ReflectT ; reflexivity.
    + destruct (h == h1) eqn: Hh ; move /eqP : Hh => Hh ;
               last (by apply ReflectF ; injection ; done) ;
            rewrite Hh andTb.
      destruct (h0 == h2) eqn: Hh0 ; move /eqP : Hh0 => Hh0 ;
               last (by apply ReflectF ; injection ; done) ;
            rewrite Hh0.
      apply ReflectT ; reflexivity.
    + destruct (h == h2) eqn: Hh ; move /eqP : Hh => Hh ;
               last (by apply ReflectF ; injection ; done) ;
            rewrite Hh andTb.
      generalize (hfstmt_seq_eqP h0 h3) ; intro.
      apply reflect_iff in H.
      destruct (hfstmt_seq_eqn h0 h3) ;
            last by (apply ReflectF ; injection ; intros _ H1 ;
                     apply H in H1 ; done).
      destruct H as [_ H] ; rewrite H // andTb.
      specialize (hfstmt_seq_eqP h1 h4).
      apply reflect_iff in hfstmt_seq_eqP.
      destruct (hfstmt_seq_eqn h1 h4) ;
            last by (apply ReflectF ; injection ; intros H1 ;
                     apply hfstmt_seq_eqP in H1 ; done).
      destruct hfstmt_seq_eqP as [_ hfstmt_seq_eqP] ; rewrite hfstmt_seq_eqP //.
      apply ReflectT ; reflexivity.
  * clear hfstmt_seq_eqP.
    induction x, y ; simpl ; try (apply ReflectF ; discriminate).
    + apply ReflectT ; reflexivity.
    + specialize (hfstmt_eqP h h0) ; apply reflect_iff in hfstmt_eqP.
      destruct (hfstmt_eqn h h0) ;
            last by (apply ReflectF ; injection ; intros _ H0 ;
                     apply hfstmt_eqP in H0 ; done).
      destruct hfstmt_eqP as [_ hfstmt_eqP] ; rewrite hfstmt_eqP //.
      specialize (IHx y) ; apply reflect_iff in IHx.
      destruct (hfstmt_seq_eqn x y) ;
            last by (apply ReflectF ; injection ; intros H0 ;
                     apply IHx in H0 ; done).
      destruct IHx as [_ IHx] ; rewrite IHx //.
      apply ReflectT ; reflexivity.
  Qed.
  Canonical hfstmt_eqMixin := EqMixin hfstmt_eqP.
  Canonical hfstmt_seq_eqMixin := EqMixin hfstmt_seq_eqP.
  Canonical hfstmt_eqType := Eval hnf in EqType hfstmt hfstmt_eqMixin.
  Canonical hfstmt_seq_eqType := Eval hnf in EqType hfstmt_seq hfstmt_seq_eqMixin.

   (** hfstmt_seq is an equivalence relation *)
(*
Lemma hfstmt_eqn_refl (x : hfstmt) : x == x
with hfstmt_seq_eqn_refl (fx : hfstmt_seq) : fx == fx.
Proof.  all: rewrite eq_refl //.  Qed.

(*Lemma hfstmt_eqn_eq (x y : hfstmt) : x == y <-> x = y
with hfstmt_seq_eqn_eq (fx fy : hfstmt_seq) : fx == fy <-> fx = fy.
Proof.
Admitted.*)

Lemma hfstmt_eqn_sym (x y : hfstmt) : x == y -> y == x
with hfstmt_seq_eqn_sym (fx fy : hfstmt_seq) : fx == fy -> fy == fx.
Proof.  all: intro ; rewrite eq_sym //.  Qed.

Lemma hfstmt_eqn_trans (x y z : hfstmt) : x == y -> y == z -> x == z
with hfstmt_seq_eqn_trans (x y z : hfstmt_seq) : x == y -> y == z -> x == z.
Proof.  all: intro ; move /eqP : H => H ; rewrite H ; done.  Qed.

Instance hfstmt_seq_eqn_Reflexive : Reflexive (@hfstmt_seq_eqn) := @hfstmt_seq_eqn_refl.
Instance hfstmt_seq_eqn_Symmetric : Symmetric (@hfstmt_seq_eqn) := @hfstmt_seq_eqn_sym.
Instance hfstmt_seq_eqn_Transitive : Transitive (@hfstmt_seq_eqn) := @hfstmt_seq_eqn_trans.
Instance hfstmt_seq_eqn_Equivalence : Equivalence (@hfstmt_seq_eqn) :=
    { Equivalence_Reflexive := hfstmt_seq_eqn_Reflexive;
      Equivalence_Symmetric := hfstmt_seq_eqn_Symmetric;
      Equivalence_Transitive := hfstmt_seq_eqn_Transitive }.
*)
   Definition Qhead (default : hfstmt) (s : hfstmt_seq) : hfstmt :=
   match s with Qnil => default
              | Qcons h tl => h end.

   Fixpoint Qcat (s1 s2 : hfstmt_seq) : hfstmt_seq :=
   match s1 with Qnil => s2
               | Qcons h1 tl1 => Qcons h1 (Qcat tl1 s2) end.

   Lemma Qcats0 : forall (ss : hfstmt_seq),
      Qcat ss Qnil = ss.
   Proof.
   induction ss.
   * by unfold Qcat ; reflexivity.
   * by simpl Qcat ; rewrite IHss ; reflexivity.
   Qed.

   Lemma Qcat_nil : forall (ss1 ss2 : hfstmt_seq),
       Qcat ss1 ss2 = Qnil -> ss1 = Qnil /\ ss2 = Qnil.
   Proof.
   induction ss1.
   * induction ss2 ; first by intros ; split ; reflexivity.
     simpl Qcat ; discriminate.
   * intro ; simpl Qcat ; discriminate.
   Qed.

   Lemma Qcat_assoc : forall (ss1 ss2 ss3 : hfstmt_seq),
      Qcat (Qcat ss1 ss2) ss3 = Qcat ss1 (Qcat ss2 ss3).
   Proof.
   induction ss1.
   * simpl Qcat ; by reflexivity.
   * intros ; simpl Qcat ; rewrite IHss1 ; reflexivity.
   Qed.

   Fixpoint Qcatrev (s1 s2 : hfstmt_seq) : hfstmt_seq := (* calculates the reversal of s1, followed by s2 *)
   match s1 with Qnil => s2
               | Qcons h1 tl1 => Qcatrev tl1 (Qcons h1 s2) end.

   Definition Qrev (s : hfstmt_seq) : hfstmt_seq := Qcatrev s Qnil.

   Fixpoint Qin (s : hfstmt) (ss : hfstmt_seq) : bool :=
    match ss with Qnil => false
                | Qcons h tl => (hfstmt_eqn h s) || (Qin s tl)
    end.

  Fixpoint Qin_when (s : hfstmt) (ss : hfstmt_seq) : bool :=
  match ss with 
  | Qnil => false
  | Qcons (Swhen c s1 s2) tl => (Qin_when s s1) || (Qin_when s s2) || (Qin_when s tl)
  | Qcons h tl => (hfstmt_eqn h s) || (Qin_when s tl)
  end.

  Fixpoint Qremove (s : hfstmt) (ss : hfstmt_seq) : hfstmt_seq :=
      match ss with
      | Qnil => Qnil
      | Qcons h tl =>
          if hfstmt_eqn h s
          then tl
          else Qcons h (Qremove s tl)
      end.

  Fixpoint Qremove_when (s : hfstmt) (ss : hfstmt_seq) : hfstmt_seq :=
      match ss with
      | Qnil => Qnil
      | Qcons (Swhen c s1 s2) tl => 
        if (Qin_when s s1) then Qcons (Swhen c (Qremove_when s s1) s2) tl
        else if (Qin_when s s2) then Qcons (Swhen c s1 (Qremove_when s s2)) tl
        else Qcons (Swhen c s1 s2) (Qremove_when s tl)
      | Qcons h tl =>
          if hfstmt_eqn h s
          then tl
          else Qcons h (Qremove_when s tl)
      end.

  Lemma Qremove_when_Qin_when s s0 ss : Qin_when s0 (Qremove_when s ss) -> Qin_when s0 ss.
  Proof.
    induction ss as [|hd tl IH]. simpl; done. destruct (hfstmt_eqn hd s) eqn : Heq. 
  Admitted.

  Lemma Qin_when_Qcons s0 ss s : Qin_when s0 ss -> Qin_when s0 (Qcons s ss).
  Proof.
  Admitted.

  Lemma Qin_Qcat s ss0 ss1 : Qin s ss0 \/ Qin s ss1 <-> Qin s (Qcat ss0 ss1).
  Proof.
  Admitted.
  
   Fixpoint Qrcons (ss : hfstmt_seq) (s : hfstmt) : hfstmt_seq :=
   match ss with
   | Qnil => Qcons s Qnil
   | Qcons h tl => Qcons h (Qrcons tl s)
   end.

  Lemma in_qremove (s s0 : hfstmt) ss : Qin s (Qremove s0 ss) -> Qin s ss.
  Proof.
  induction ss as [|h tl IH]; simpl.
  - intros H. discriminate H.
  - destruct (hfstmt_eqn h s0) eqn:Heq.
    + simpl. intros H. 
      apply orb_true_iff. right. assumption. 
    + simpl. intros H.
      apply orb_true_iff in H. 
      apply orb_true_iff.
      destruct H as [H|H].
      * left. assumption.
      * right. apply IH. assumption.
  Qed.

   Lemma Qcat_rcons : forall (ss1 : hfstmt_seq) (s : hfstmt) (ss2 : hfstmt_seq),
      Qcat (Qrcons ss1 s) ss2 = Qcat ss1 (Qcons s ss2).
   Proof.
   induction ss1.
   * unfold Qrcons ; simpl Qcat ; reflexivity.
   * simpl Qrcons ; simpl Qcat.
     intros.
     rewrite IHss1 ; reflexivity.
   Qed.

   Lemma Qcats1 : forall (ss : hfstmt_seq) (s : hfstmt),
       Qcat ss (Qcons s Qnil) = Qrcons ss s.
   Proof.
   induction ss.
   * simpl ; reflexivity.
   * simpl.
     intro ; rewrite -IHss //.
   Qed.

Fixpoint Qcatrev_rec (ss1 ss2 : hfstmt_seq) : hfstmt_seq :=
(* calculates the recursive reversal of ss1, followed by ss2 *)
  match ss1 with
    Qnil => ss2
  | Qcons h1 tl1 =>
      Qcatrev_rec tl1 (Qcons (Qrev_rec h1) ss2) end
with Qrev_rec (s : hfstmt) : hfstmt :=
       match s with
         Swhen c sst ssf =>
           Swhen c (Qcatrev_rec sst Qnil) (Qcatrev_rec ssf Qnil)
       | s => s end.
   
Lemma qcatrev_rec0s s : Qcatrev_rec Qnil s = s.
Proof. by []. Qed.

Lemma qcat0s s : Qcat Qnil s = s.
Proof. by []. Qed.

Lemma qcats0 s : Qcat s Qnil = s.
Proof.
  elim : s => // h h0 /= ->//. 
Qed.

Lemma Qrcons_ind' :
   forall (P : hfstmt_seq -> Prop) (P0 : hfstmt -> Prop),
       P Qnil ->
       (forall h : hfstmt, P0 h -> forall h0 : hfstmt_seq, P h0 -> P (Qrcons h0 h)) ->
       P0 Sskip ->
       (forall (s : var) (f2 : ftype), P0 (Swire s f2)) ->
       (forall (s : var) (h : hfreg), P0 (Sreg s h)) ->
       (forall (s : var) (h : hfmem), P0 (Smem s h)) ->
       (forall s s0 : var, P0 (Sinst s s0)) ->
       (forall (s : var) (h : hfexpr), P0 (Snode s h)) ->
       (forall (h : href) (h0 : hfexpr), P0 (Sfcnct h h0)) ->
       (forall h : href, P0 (Sinvalid h)) ->
       (forall (h : hfexpr) (h0 : hfstmt_seq),
        P h0 -> forall h1 : hfstmt_seq, P h1 -> P0 (Swhen h h0 h1)) ->
       forall h : hfstmt, P0 h

with Qrcons_seq_ind' :
forall (P : hfstmt_seq -> Prop) (P0 : hfstmt -> Prop),
       P Qnil ->
       (forall h : hfstmt, P0 h -> forall h0 : hfstmt_seq, P h0 -> P (Qrcons h0 h)) ->
       P0 Sskip ->
       (forall (s : var) (f2 : ftype), P0 (Swire s f2)) ->
       (forall (s : var) (h : hfreg), P0 (Sreg s h)) ->
       (forall (s : var) (h : hfmem), P0 (Smem s h)) ->
       (forall s s0 : var, P0 (Sinst s s0)) ->
       (forall (s : var) (h : hfexpr), P0 (Snode s h)) ->
       (forall (h : href) (h0 : hfexpr), P0 (Sfcnct h h0)) ->
       (forall h : href, P0 (Sinvalid h)) ->
       (forall (h : hfexpr) (h0 : hfstmt_seq),
        P h0 -> forall h1 : hfstmt_seq, P h1 -> P0 (Swhen h h0 h1)) ->
       forall h : hfstmt_seq, P h.
Proof.
  intros. move : h.
  elim; try done. 
  intros. apply H9;
    by apply (Qrcons_seq_ind' P P0).

  intros. rewrite-(qcat0s h). generalize H. move => Hnil.
  elim : h Qnil H => [|x s2 IHs] s1 Hs1.
  by rewrite qcats0.
  rewrite -Qcat_rcons. apply IHs. apply H0; last done.
  apply (Qrcons_ind' P); try done. 
Qed.
  
Lemma Qrcons_ind :
forall (Ps : hfstmt -> Prop) (Pss : hfstmt_seq -> Prop),
(Ps Sskip) ->
(forall (v : var) (ft : ftype), Ps (Swire v ft)) ->
(forall (v : var) (r : hfreg),  Ps (Sreg v r)) ->
(forall (v : var) (m : hfmem),  Ps (Smem v m)) ->
(forall (v1 v2 : var),          Ps (Sinst v1 v2)) ->
(forall (v : var) (e : hfexpr), Ps (Snode v e)) ->
(forall (r : href) (e : hfexpr), Ps (Sfcnct r e)) ->
(forall (f : href),             Ps (Sinvalid f)) ->
(forall (cond : hfexpr) (sst : hfstmt_seq), Pss sst -> forall (ssf : hfstmt_seq), Pss ssf -> Ps (Swhen cond sst ssf)) ->
(Pss Qnil) ->
(forall (s : hfstmt), Ps s -> forall (ss : hfstmt_seq), Pss ss -> Pss (Qrcons ss s)) ->
(forall s : hfstmt, Ps s) /\ (forall ss : hfstmt_seq, Pss ss).
Proof.
  intros. split.
  apply Qrcons_ind' with Pss; try done.
  apply Qrcons_seq_ind' with Ps; try done.
Qed.

   Lemma Qeqseq_cons : forall (s : hfstmt) (ss1 ss2 : hfstmt_seq), (Qcons s ss1 == Qcons s ss2) = (ss1 == ss2).
   Proof.
   intros.
   destruct (ss1 == ss2) eqn: H ; move /eqP : H => H ;
         first by rewrite -H eq_refl //.
   apply negbTE.
   apply rwP with (P := ~ (Qcons s ss1 == Qcons s ss2)) ; first by apply negP.
   contradict H.
   move /eqP : H => H ; injection H ; done.
   Qed.

   Lemma Qeqseqr_cat : forall (ss1 ss2 ss3 : hfstmt_seq), (Qcat ss1 ss2 == Qcat ss1 ss3) = (ss2 == ss3).
   Proof.
   induction ss1.
   * simpl Qcat ; reflexivity.
   * simpl Qcat ; intros.
     rewrite Qeqseq_cons IHss1 //.
   Qed.

  (* Fixpoint Qfoldl {R : Type} (f : R -> hfstmt -> R) (s : hfstmt_seq) (default : R) :=
   match s with Qnil => default
              | Qcons h tl => Qfoldl f tl (f default h) end.
   Fixpoint Qfoldr {R : Type} (f : hfstmt -> R -> R) (default : R) (s : hfstmt_seq) :=
   match s with Qnil => default
              | Qcons h tl => f h (Qfoldr f default tl) end. *)

  Inductive hfport : Type :=
  | Finput : var -> ftype -> hfport
  | Foutput : var -> ftype -> hfport
  .

  Lemma hfport_eq_dec : forall {x y : hfport}, {x = y} + {x <> y}.
  Proof.  decide equality ; try apply ftype_eq_dec.
  1,2: destruct (s == s0) eqn: Hs.
  2,4: move /eqP : Hs => Hs ; right ; exact Hs.
  1,2: move /eqP : Hs => Hs ; left ; exact Hs.
  Qed.
  Definition hfport_eqn (x y : hfport) : bool :=
  match x, y with
  | Finput vx fx, Finput vy fy
  | Foutput vx fx, Foutput vy fy => (vx == vy) && (fx == fy)
  | _, _ => false
  end.
  Lemma hfport_eqP : Equality.axiom hfport_eqn.
  Proof.
  rewrite /Equality.axiom /hfport_eqn.
  intros.
  destruct x, y ; try (apply ReflectF ; discriminate).
  1,2: destruct (s == s0) eqn: Hs.
  2,4: move /eqP : Hs => Hs ; apply ReflectF ; injection ; done.
  1,2: move /eqP : Hs => Hs ; rewrite -Hs andTb ; clear Hs s0 ;
       destruct (f == f0) eqn: Hf.
  2,4: move /eqP : Hf => Hf ; apply ReflectF ; injection ; done.
  1,2: move /eqP : Hf => Hf ; rewrite -Hf ; clear Hf f0 ;
       apply ReflectT ; reflexivity.
  Qed.
  Canonical hfport_eqMixin := EqMixin hfport_eqP.
  Canonical hfport_eqType := Eval hnf in EqType hfport hfport_eqMixin.

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

  Lemma hfmodule_eq_dec : forall {x y : hfmodule}, {x = y} + {x <> y}.
  Proof.  decide equality ; try apply hfstmt_seq_eq_dec.
  1,3: destruct (l == l0) eqn: Hl ; move /eqP : Hl => Hl ;
        first (by left  ; exact Hl) ;
        last  (by right ; exact Hl).
  all: destruct (s == s0) eqn: Hs ; move /eqP : Hs => Hs ;
        first (by left  ; exact Hs) ;
        last  (by right ; exact Hs).
  Qed.
  Definition hfmodule_eqn (x y : hfmodule) : bool :=
  match x, y with
  | FInmod mix pplx sslx, FInmod miy pply ssly
  | FExmod mix pplx sslx, FExmod miy pply ssly => (mix==miy) && (pplx==pply) && (sslx==ssly)
  | _, _ => false
  end.
  Lemma hfmodule_eqP : Equality.axiom hfmodule_eqn.
  Proof.
  rewrite /Equality.axiom /hfmodule_eqn.
  intros.
  destruct x, y ; try (apply ReflectF ; discriminate).
  1,2: destruct (s == s0) eqn: Hs ; move /eqP : Hs => Hs.
  2,4: apply ReflectF ; injection ; done.
  1,2: rewrite -Hs andTb ; clear Hs s0 ;
       destruct (l == l0) eqn: Hl ; move /eqP : Hl => Hl.
  2,4: apply ReflectF ; injection ; done.
  1,2: rewrite -Hl andTb ; clear Hl l0 ;
       destruct (h == h0) eqn: Hh ; move /eqP : Hh => Hh.
  2,4: apply ReflectF ; injection ; done.
  1,2: rewrite -Hh ; clear Hh h0 ;
       apply ReflectT ; reflexivity.
  Qed.
  Canonical hfmodule_eqMixin := EqMixin hfmodule_eqP.
  Canonical hfmodule_eqType := Eval hnf in EqType hfmodule hfmodule_eqMixin.

  Inductive hfcircuit : Type := Fcircuit : var -> seq hfmodule -> hfcircuit.

  Inductive forient : Type :=
  | Source | Sink | Duplex | Passive | Other.

  Lemma forient_eq_dec : forall { x y : forient }, { x=y } + { x <> y }.
  Proof.  intros ; decide equality.  Qed.

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

End HiFirrtl.

(********************************************************************************)

(** Component Environment *)

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

  (* equality of cmpnt_init_typs is decidable *)
   Axiom cmpnt_init_typs_eq_dec : forall {x y : cmpnt_init_typs}, {x = y} + {x <> y}.
   Parameter cmpnt_init_typs_eqn: forall (x y : cmpnt_init_typs), bool.
   Axiom cmpnt_init_typs_eqP : Equality.axiom cmpnt_init_typs_eqn.
   Canonical cmpnt_init_typs_eqMixin := EqMixin cmpnt_init_typs_eqP.
   Canonical cmpnt_init_typs_eqType := Eval hnf in EqType cmpnt_init_typs cmpnt_init_typs_eqMixin.

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


(********************************************************************************)

(** Single var, Component Environment *)
Module CE (*<: CmpntEnv VarOrder *) := MakeCmpntEnv VarOrder VM.
(*
(** Paired var, Component Environment *)
Module CEP  := MakeCmpntEnv ProdVarOrder PVM.
*)
(********************************************************************************)

(** Component Connections *)

(* rhs expressions *)
Section Rhs_expr.
  Variable v : eqType.

  Inductive rhs_expr : Type :=
  | R_fexpr : hfexpr v -> rhs_expr
  | R_default
  .
  
  Inductive rhs_expr' : Type :=
  | R_cnct : hfexpr v -> rhs_expr'
  (* | R_pcnct : hfexpr v -> rhs_expr *)
  | R_invalid : hfexpr v -> rhs_expr'
  | R_default'
  .

  (** eq dec *)
  Lemma rhs_expr_eq_dec : forall {x y : rhs_expr}, {x = y} + {x <> y}.
  Proof.
    decide equality.
    apply hfexpr_eq_dec.
  Qed.

  Lemma rhs_expr_eq_dec' : forall {x y : rhs_expr'}, {x = y} + {x <> y}.
  Proof.
    decide equality.
    all: apply hfexpr_eq_dec.
  Qed.

  Definition rhs_expr_eqn (x y : rhs_expr) : bool :=
    match x, y with R_fexpr e1, R_fexpr e2 => e1 == e2 | R_default, R_default => true | _, _ => false end.

  Definition rhs_expr_eqn' (x y : rhs_expr') : bool :=
  match x, y with R_cnct e1, R_cnct e2 => e1 == e2 | R_invalid e1, R_invalid e2 => e1 == e2 | R_default', R_default' => true | _, _ => false end.

  Lemma rhs_expr_eqP : Equality.axiom rhs_expr_eqn.
  Proof. unfold Equality.axiom, rhs_expr_eqn.
  induction x, y ; try (apply ReflectF ; discriminate) ; try (apply ReflectT ; reflexivity).
  case Eq: (h == h0).
  all: move /hfexpr_eqP : Eq => Eq.
  apply ReflectT ; replace h0 with h ; reflexivity.
  apply ReflectF ; injection ; apply Eq.
  Qed.

  Lemma rhs_expr_eqP' : Equality.axiom rhs_expr_eqn'.
  Proof. unfold Equality.axiom, rhs_expr_eqn'.
  induction x, y ; try (apply ReflectF ; discriminate) ; try (apply ReflectT ; reflexivity);
  case Eq: (h == h0);
  move /eqP : Eq => Eq.
  all : try (apply ReflectT ; replace h0 with h ; reflexivity).
  all : apply ReflectF ; injection ; auto.
  Qed.

  Canonical rhs_expr_eqMixin := EqMixin rhs_expr_eqP.
  Canonical rhs_expr_eqType := Eval hnf in EqType rhs_expr rhs_expr_eqMixin.

  
  Canonical rhs_expr_eqMixin' := EqMixin rhs_expr_eqP'.
  Canonical rhs_expr_eqType' := Eval hnf in EqType rhs_expr' rhs_expr_eqMixin'.

End Rhs_expr.

(********************************************************************************)

Module Type StructStore (V : SsrOrder) (CE : CmpntEnv V with Module SE := V).
  (* extension of the component environment above
  with functions (and lemmas) to define additional variables *)

  Module Lemmas := FMapLemmas CE.

  Local Notation var := V.t.
  Local Notation value := (rhs_expr' V.T).

  Parameter t : Type.
  Parameter empty : t.
  Parameter find : var -> t -> option value.
  Parameter map2 : (option value -> option value -> option value) -> t -> t -> t.
  Parameter elements : t -> list (var * value).
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
  Definition t : Type := rhs_expr' V.T.
  Definition default : t := R_default' V.T.

End StructType.

Module MakeStructStore (V : SsrOrder) (CE : CmpntEnv V with Module SE := V) <:
  StructStore V CE.
  Module StructTypeV := StructType V.
  Include MakeTStoreMap V StructTypeV.
  Module Lemmas := FMapLemmas CE.
  Definition map2 (f : option (rhs_expr' V.T) -> option (rhs_expr' V.T) -> option (rhs_expr' V.T)) (s1 s2 : t) : t :=
    M.map2 f s1 s2.
  Definition elements (s : t) := M.elements s.
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
        (x:V.t)(f:option (rhs_expr' V.T)->option (rhs_expr' V.T)->option (rhs_expr' V.T)),
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

(********************************************************************************)

(** Single var, Component Connections *)
Module StructState := MakeStructStore VarOrder CE.
(*
(** Paired var, Component Connections *)
Module StructStateP := MakeStructStore ProdVarOrder CEP.
*)

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
  (* Definition evalidif c e := @Evalidif V.T c e. *)
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
  Definition sinvalid v1 := @Sinvalid V.T v1.
  Definition swhen c s1 s2 := @Swhen V.T c s1 s2.
  (* Definition sstop e1 e2 n := @Sstop V.T e1 e2 n. *)
  Definition sinst v1 v2 := @Sinst V.T v1 v2.

  Definition hfreg := @hfreg V.T.
  Definition mk_hfreg := @mk_freg V.T.
  Definition rst := @rst V.T.
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
  Proof. decide equality. Qed.
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

  (********************************************************************************)

  Fixpoint base_ref r : V.t :=
    match r with
    | Eid v => v
    | Esubfield r v => base_ref r
    | Esubindex r n => base_ref r
    | Esubaccess r n => base_ref r
    end.

End MakeHiFirrtl.

(********************************************************************************)

(* HiFirrtl module with variables of type N *)
Module HiF := MakeHiFirrtl VarOrder (* ProdVarOrder PVS *) VS VM CE StructState (* CEP StructStateP *).
