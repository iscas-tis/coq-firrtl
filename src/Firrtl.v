From Coq Require Import FunInd FMaps FMapAVL OrderedType ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat ssrint eqtype seq fintype fingraph.
From simplssrlib Require Import Types SsrOrder FSets FMaps Tactics Var Store.
From nbits Require Import NBits.
From firrtl Require Import Env.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Delimit Scope firrtl with firrtl.

Section LoFirrtl.

  (****** Syntax ******)

  (****** Expressions ******)

  Inductive ucast : Set :=
  | AsUInt | AsSInt (*| AsFixed*) | AsClock | AsReset | AsAsync .

  Inductive eunop : Set :=
  | Upad : nat -> eunop
  | Ushl : nat -> eunop
  | Ushr : nat -> eunop
  | Ucvt
  | Uneg
  | Unot
  | Uandr
  | Uorr
  | Uxorr
  | Uextr : nat -> nat -> eunop
  | Uhead : nat -> eunop
  | Utail : nat -> eunop.

  Inductive bcmp : Set :=
  | Blt | Bleq | Bgt | Bgeq | Beq | Bneq.

  Inductive ebinop : Set :=
  | Badd
  | Bsub
  | Bmul
  | Bdiv
  | Brem
  (* | Bsdiv *)
  (* | Bsrem *)
  | Bcomp: bcmp -> ebinop
  | Bdshl
  | Bdshr
  | Band
  | Bor
  | Bxor
  | Bcat .

  Variable var : eqType.

  (* mux, valid, sub-xxx, TBD *)
  Inductive fexpr : Type :=
  | Econst : fgtyp -> bits -> fexpr
  (* | Edeclare : var -> fgtyp -> fexpr *)
  | Ecast : ucast -> fexpr -> fexpr
  | Eprim_unop : eunop -> fexpr -> fexpr
  | Eprim_binop : ebinop -> fexpr -> fexpr -> fexpr
  | Emux : fexpr -> fexpr -> fexpr -> fexpr
  | Evalidif : fexpr -> fexpr -> fexpr
  | Eref : var -> fexpr
  .

  (****** Statements ******)
  Inductive ruw : Set :=
  | old | new | undefined.

  Record freader_port : Type :=
    mk_freader_port
      {
        addr : var;
        data : var;
        en : var;
        clk : var;
        flag : var
      }.

Record fwriter_port : Type :=
    mk_fwriter_port
      {
        addr0 : var;
        data0 : var;
        en0 : var;
        clk0 : var;
        mask : var
      }.

  Record fmem : Type :=
    mk_fmem
      {
        mid : var;
        data_type : fgtyp;
        depth : nat;
        reader : seq freader_port;
        writer : seq fwriter_port;
        read_latency : nat;
        write_latency : nat;
        read_write : ruw
      }.

  Inductive rst : Type :=
  | NRst : rst
  | Rst : fexpr -> fexpr -> rst.
  
  Record freg : Type :=
    mk_freg
      {
        rid : var;
        type : fgtyp;
        clock : var;
        reset : rst
      }.

  Inductive fport : Type :=
  | Finput : var -> fgtyp -> fport
  | Foutput : var -> fgtyp -> fport
  .

  Record finst : Type :=
    mk_finst
      {
        iid : var;
        imid : var;
        iports : seq fport
      }.

  Inductive fstmt : Type :=
  | Sskip
  | Swire : var -> fgtyp -> fstmt
  | Sreg : freg -> fstmt
  | Smem : fmem -> fstmt
  | Sinst : finst -> fstmt
  | Snode : var -> fexpr -> fstmt
  | Sfcnct : fexpr -> fexpr -> fstmt
  (*| Spcnct : fexpr -> fexpr -> fstmt*)
  | Sinvalid : var -> fstmt
  (* | Sattach : seq var -> fstmt *)
  | Swhen : fexpr -> fstmt -> fstmt -> fstmt
  | Sstop : fexpr -> fexpr -> nat -> fstmt
  (* | Sprintf (* TBD *) *)
  (* | Sassert (* TBD *) *)
  (* | Sassume (* TBD *) *)
  (* | Sdefname : var -> fstmt *) (* TBD *)
  (* | Sparam : var -> fexpr -> fstmt *) (* TBD *)
  .

  (* TBD *)
  Inductive fmodule : Type :=
  | FInmod : var -> seq fport -> seq fstmt -> fmodule
  | FExmod : var -> seq fport -> seq fstmt -> fmodule
  .

  Inductive fcircuit : Type := Fcircuit : var -> seq fmodule -> fcircuit.

End LoFirrtl.



(************************************************************)
(* Parallel semantics model *)


Module Type ExprStore (V : SsrOrder) (TE : TypEnv with Module SE := V).
  Module Lemmas := FMapLemmas TE.

  Local Notation var := V.t.
  Local Notation value := (option (fexpr V.T)).

  Parameter t : Type.
  Parameter empty : t.
  Parameter acc : var -> t -> value.
  Parameter upd : var -> value -> t -> t.

End ExprStore.

Module ExprType (V:SsrOrder)<: HasDefaultTyp.
  Definition t : Type := option (fexpr V.T).
  Definition default : t := None. (* Econst V.T (Fuint 0) [::]. *)
End ExprType.

Module MakeExprStore (V : SsrOrder) (TE : TypEnv with Module SE := V) <:
  ExprStore V TE.
  Module ExprTypeV := ExprType V.
  Include MakeTStoreMap V ExprTypeV.
  Module Lemmas := FMapLemmas TE.
End MakeExprStore.

Module EStore := MakeExprStore VarOrder TE.

Module MakeFirrtl
       (V : SsrOrder)
       (* (VS : SsrFSet with Module SE := V)
       (VM : SsrFMap with Module SE := V) *)
       (TE : TypEnv with Module SE := V)
       (SV : ValStore V TE).
       (* (EV : ExprStore V TE). *)
  Local Open Scope firrtl.
  Local Open Scope bits.
  
  Module VSLemmas := SsrFSetLemmas VS.

  Local Notation var := V.t.

  Local Notation vstate := SV.t.

  (* Definition EStore := Store.M.t (fexpr V.T). *)

  (* Local Notation estate := EV.t. *)
  

(****** Semantics ******)

  (* Small-step *) 

  Definition fexpr := fexpr V.T.
  Definition econst c := @Econst V.T c.
  Definition eref v := @Eref V.T v.
  Definition ecast u e := @Ecast V.T u e.
  Definition eprim_unop u e := @Eprim_unop V.T u e.
  Definition eprim_binop b e1 e2 := @Eprim_binop V.T b e1 e2.
  Definition emux c e1 e2 := @Emux V.T c e1 e2.
  Definition evalidif c e := @Evalidif V.T c e.

  Definition fstmt := fstmt V.T.
  Definition sskip := @Sskip V.T.
  Definition swire v t := @Swire V.T v t.  
  Definition sreg r := @Sreg V.T r.
  Definition smem m := @Smem V.T m.
  Definition snode v e := @Snode V.T v e.
  Definition sfcnct v1 v2 := @Sfcnct V.T v1 v2.

  Definition freg := @freg V.T.
  Definition mk_freg := @mk_freg V.T.
  Definition nrst := @NRst V.T.
  Definition rrst e1 e2 := @Rst V.T e1 e2.
  Definition fmem := @fmem V.T.
  Definition mk_fmem := @mk_fmem V.T.
  Definition mk_fwriter_port := @mk_fwriter_port V.T.
  Definition mk_freader_port := @mk_freader_port V.T.
  Definition fwriter_port := @fwriter_port V.T.
  Definition freader_port := @freader_port V.T.
  Definition fport := @fport V.T.
  Definition mk_finst := @mk_finst V.T.
  Definition fmodule := @fmodule V.T.
  Definition fcircuit := @fcircuit V.T.

  Definition memory_map := bits -> bits.
  Definition memfind (key : bits) (map : memory_map) : bits := map key.
  Definition memupd (key : bits) (v : bits) (memmap : memory_map) : memory_map :=
    fun (y : bits) => if y == key then v else memfind y memmap.
  Definition memempty : memory_map := (fun _ => [::]).

  Definition mapls := TE.t (seq var).
  Definition mapioin := TE.t (seq bits).
  Definition mapdata2etc := TE.t (var * var * var * var * var).
  Definition map2etc := TE.t (mapdata2etc).

  Definition mapmem := TE.t memory_map. 

  Fixpoint mylListIn (a:var) (l:list var) : bool :=
      match l with
        | nil => b0
        | b :: m => if b == a then b1 else (mylListIn a m)
      end.

  Definition maptuple := TE.t (var * var).
  Definition mmaptuple := TE.t maptuple.
  Definition mapfstmt := TE.t (seq fstmt).
  Definition mapterss := TE.t (TE.env * vstate * vstate * mapmem).
  Definition mapvar := TE.t var.
  Definition mvar := TE.t mapvar.
  Definition mmapvar := TE.t (mvar * mapvar).
  Definition mmvar := TE.t (mapvar * mapvar).

  Fixpoint bitsIn (a: bits) (l:list bits) : bool :=
      match l with
        | nil => b0
        | b :: m => if ((to_nat b) == (to_nat a)) then b1 else (bitsIn a m)
      end.
  Fixpoint varIn (a: var) (l:seq var) : bool :=
      match l with
        | nil => b0
        | b :: m => if (b == a) then b1 else (varIn a m)
      end.

  Definition g := var -> seq var.
  Definition mapg := TE.t g.
  Definition emptyg : g := (fun _ => [::]).
  Definition findg (key : var) (map : g) : seq var := map key.
  Definition updg (key : var) (v : seq var) (map : g) : g :=
    fun (y : var) => if y == key then v else findg y map.

  Definition var2stmtmap := TE.t fstmt.
  Definition allvar2stmtmap := TE.t var2stmtmap.
  Definition fmap := TE.t nat.
  Definition boolmap := TE.t bool.
  Definition allboolmap := TE.t boolmap.

  Fixpoint upd_inner s s0 (a2 : seq var) (finstinmap : mapvar) : vstate :=
      match a2 with
      | [:: ] => s0
      | h::t => let s1 := match TE.find h finstinmap with
                            | None => s0
                            | Some a => SV.upd h (SV.acc a s) s0
                            end in
      upd_inner s s1 t finstinmap
      end.
  
  (* From Coq Require Import ZArith. *)
  
  Definition ftcast (bs : bits) (fty : fgtyp) (tty : fgtyp) : bits :=
    match fty with
    | Fuint w => ucastB bs (sizeof_fgtyp tty)
    | Fsint w => scastB bs (sizeof_fgtyp tty)
    | _ => ucastB bs 1
    end.
  
  Definition to_Clock bs := Z.b2z (lsb bs).
  Definition to_Reset bs := Z.b2z (lsb bs).

  (* Casting operations *)
  Definition eunop_ucast (o : ucast) : bits -> Z :=
    match o with
    | AsUInt => to_Zpos
    | AsSInt => to_Z
    | AsClock => to_Clock
    | AsReset | AsAsync => to_Reset
    end.

  (* Unary operations *)
  Definition eunop_op (o : eunop) (t : fgtyp) : bits -> bits :=
    match o with
    | Upad n => fun b =>
                 (match t with
                  | Fuint w => zext (n - w) b
                  | Fsint w => sext (n - w) b
                  | _ => b
                  end)
    | Ushl n => fun b => cat (zeros n) b
    | Ushr n => fun b => if (n < size b) then high (size b - n) b else [::msb b]
    | Ucvt =>  fun b =>
                 (match t with
                  | Fuint w => sext 1 b
                  | _ => b
                  end)
    | Uneg => negB
    | Unot => invB
    | Uandr => fun b => [::foldr andb b1 b]
    | Uorr => fun b => [::foldr orb b0 b]
    | Uxorr => fun b => [::foldr xorb b0 b]
    | Uextr n1 n2 => extract n1 n2
    | Uhead n => high n
    | Utail n => fun b => low (size b - n) b
    end.  

  Compute (eunop_op (Uextr 5 1) (Fuint 6) [:: true; false; true; true; true; true]).

  (* Comparison operations *)
  Definition binop_bcmp (o : bcmp) : bits -> bits -> bits :=
    match o with
    | Blt => fun b1 b2 => let bs1 := zext ((maxn (size b1) (size b2)) - (size b1)) b1 in
                          let bs2 := zext ((maxn (size b1) (size b2)) - (size b2)) b2 in
                          [::ltB bs1 bs2]
    | Bleq => fun b1 b2 => let bs1 := zext ((maxn (size b1) (size b2)) - (size b1)) b1 in
                          let bs2 := zext ((maxn (size b1) (size b2)) - (size b2)) b2 in
                          [::leB bs1 bs2]
    | Bgt => fun b1 b2 => let bs1 := zext ((maxn (size b1) (size b2)) - (size b1)) b1 in
                          let bs2 := zext ((maxn (size b1) (size b2)) - (size b2)) b2 in
                          [::gtB bs1 bs2]
    | Bgeq => fun b1 b2 => let bs1 := zext ((maxn (size b1) (size b2)) - (size b1)) b1 in
                          let bs2 := zext ((maxn (size b1) (size b2)) - (size b2)) b2 in
                          [::geB bs1 bs2]
    | Beq => fun b1 b2 => let bs1 := zext ((maxn (size b1) (size b2)) - (size b1)) b1 in
                          let bs2 := zext ((maxn (size b1) (size b2)) - (size b2)) b2 in
                          [::bs1 == bs2]
    | Bneq => fun b1 b2 => let bs1 := zext ((maxn (size b1) (size b2)) - (size b1)) b1 in
                           let bs2 := zext ((maxn (size b1) (size b2)) - (size b2)) b2 in
                          [::(~~ (bs1 == bs2))]
    end.
    (*Compute (binop_bcmp Bgeq [::true;false;true] [::true;false;true]).
    Compute (binop_bcmp Bgeq [::true;false;true] [::true;false;true;false]).*)

  Definition binop_sbcmp (o : bcmp) : bits -> bits -> bits :=
    match o with
    | Blt => fun b1 b2 => let bs1 := sext ((maxn (size b1) (size b2)) - (size b1)) b1 in
                          let bs2 := sext ((maxn (size b1) (size b2)) - (size b2)) b2 in
                          [::sltB bs1 bs2]
    | Bleq => fun b1 b2 => let bs1 := sext ((maxn (size b1) (size b2)) - (size b1)) b1 in
                          let bs2 := sext ((maxn (size b1) (size b2)) - (size b2)) b2 in
                          [::sleB bs1 bs2]
    | Bgt => fun b1 b2 => let bs1 := sext ((maxn (size b1) (size b2)) - (size b1)) b1 in
                          let bs2 := sext ((maxn (size b1) (size b2)) - (size b2)) b2 in
                          [::sgtB bs1 bs2]
    | Bgeq => fun b1 b2 => let bs1 := sext ((maxn (size b1) (size b2)) - (size b1)) b1 in
                          let bs2 := sext ((maxn (size b1) (size b2)) - (size b2)) b2 in
                          [::sgeB bs1 bs2]
    | Beq => fun b1 b2 => let bs1 := sext ((maxn (size b1) (size b2)) - (size b1)) b1 in
                          let bs2 := sext ((maxn (size b1) (size b2)) - (size b2)) b2 in
                          [::bs1 == bs2]
    | Bneq => fun b1 b2 => let bs1 := sext ((maxn (size b1) (size b2)) - (size b1)) b1 in
                           let bs2 := sext ((maxn (size b1) (size b2)) - (size b2)) b2 in
                           [::(~~ (bs1 == bs2))]
    end.

  (* Binary operations *)

  (* addition with zero extended bits *)
  Definition full_adder_ext c bs1 bs2 : bool * bits := full_adder_zip c (extzip0 bs1 bs2).
  Definition adcB_ext c bs1 bs2 := full_adder_ext c bs1 bs2.
  Definition addB_ext bs1 bs2 : bits := let (c, r) := (adcB_ext false bs1 bs2) in rcons r c.

  (*Compute (extzip0 [::false;false;false] [::true;true;true;true]).*)

  Lemma size_full_adder_ext c bs1 bs2 : size (snd (full_adder_ext c bs1 bs2)) = maxn (size bs1) (size bs2).
  Proof.
    rewrite /full_adder_ext.
    dcase (extzip0 bs1 bs2) => [zp Hzp].
    rewrite -(size_extzip b0 b0 bs1 bs2) -/extzip0 Hzp.
    elim : zp bs1 bs2 Hzp c => [|zh zt IH] bs1 bs2 Hzp c. rewrite //.
    dcase zh => [[hd1 hd2] Hz]. rewrite Hz in Hzp => {Hz zh}.
    dcase (bool_adder c hd1 hd2) => [[c0 hd] Hadder].
    dcase (full_adder_zip c0 zt) => [[c1 tl] Hfull].
    move: Hzp.
    case: bs1; case: bs2 => //.
    - move=> b bs Hzs. case: Hzs => H1 H2.
      have ->: zip (copy (size bs) b0) bs = extzip0 [::] bs by rewrite /extzip0/=; elim bs =>//.
      move => H3.
      move: (IH _ _ H3 c0). rewrite /=Hadder Hfull/=; by move=> ->.
    - move => b bs Hzs. case : Hzs => H1 H2.
      have ->: zip bs (copy (size bs) b0) = extzip0 bs [::] by rewrite /extzip0/=; elim bs =>//.
      move => H3.
      move: (IH _ _ H3 c0). rewrite /=Hadder Hfull/=; by move=> ->.
    - move => b11 bs1 b21 bs2 Hzs. case: Hzs => H1 H2 H3.
      move : (IH _ _ H3 c0). rewrite /=Hadder Hfull/=; by move => ->.
  Qed.
      
  Lemma size_adcB_ext bs1 bs2: size (snd (adcB_ext false bs1 bs2)) = maxn (size bs1) (size bs2).
  Proof.
    rewrite /adcB_ext size_full_adder_ext //.
  Qed.

  Lemma size_addB_ext bs1 bs2 : size (addB_ext bs1 bs2) = (maxn (size bs1) (size bs2)).+1.
  Proof.
    rewrite /addB_ext. case Hadc : (adcB_ext false bs1 bs2) => [c r].
    rewrite /=-size_adcB_ext Hadc size_rcons //.
  Qed.

  Search to_Zpos.

  Lemma extzip0_zext bs1 bs2 :
    extzip0 bs1 bs2 = zip (zext (size bs2 - size bs1) bs1) (zext ((size bs1) - size bs2) bs2) .
  Proof.
    rewrite /extzip0. rewrite /zext /zeros extzip_zip//.
  Qed.
  
  Lemma to_Zpos_addB_ext bs1 bs2 :
    to_Zpos (addB_ext bs1 bs2) = Z.add (to_Zpos bs1) (to_Zpos bs2).
  Proof.
    rewrite /addB_ext /adcB_ext /full_adder_ext.

    rewrite extzip0_zext.
    case Hadc : (full_adder_zip false (zip (zext (size bs2 - size bs1) bs1) (zext (size bs1 - size bs2) bs2))) => [c r].
    have ->: r = snd (full_adder_zip false (zip (zext (size bs2 - size bs1) bs1) (zext (size bs1 - size bs2) bs2))) by rewrite Hadc//.
    have ->: c = fst (full_adder_zip false (zip (zext (size bs2 - size bs1) bs1) (zext (size bs1 - size bs2) bs2))) by rewrite Hadc//.
    rewrite -/(full_adder false (zext (size bs2 - size bs1) bs1) (zext (size bs1 - size bs2) bs2)).
    rewrite -/(adcB false (zext (size bs2 - size bs1) bs1) (zext (size bs1 - size bs2) bs2)).
    rewrite -/(addB (zext (size bs2 - size bs1) bs1) (zext (size bs1 - size bs2) bs2)).
    rewrite -/(carry_addB (zext (size bs2 - size bs1) bs1) (zext (size bs1 - size bs2) bs2)).
    rewrite to_Zpos_rcons. rewrite size_addB 2!size_zext. rewrite -2!maxnE maxnC minnn maxnC maxnE.
    have ->: ((size bs1 + (size bs2 - size bs1)) = size (zext (size bs2 - size bs1) bs1)).
    rewrite size_zext//.
    rewrite to_Zpos_addB. rewrite 2!to_Zpos_zext//.
    rewrite 2!size_zext. rewrite -2!maxnE maxnC//.
  Qed.
    
    
  (*   dcase (extzip0 bs1 bs2) => [zp Hzp]. *)
  (*   case Hadc : (full_adder_zip false zp) => [c r]. *)
  (*   move: Hadc. *)
  (*   elim : zp bs1 bs2 Hzp c => [|zh zt IH] bs1 bs2 Hzp c. *)
  (*   rewrite /full_adder_zip. *)
  (*   move => Hadc. *)
  (*   rewrite to_Zpos_rcons. *)
  (*   inversion Hadc. *)
  (*   simpl. *)
  (*   assert (Hzp0: size (extzip0 bs1 bs2) = 0). *)
  (*   rewrite Hzp //. *)
  (*   rewrite (size_extzip b0 b0 bs1 bs2) in Hzp0. *)
  (*   symmetry. *)
  (*   rewrite /maxn in Hzp0. *)
  (*   case Hlt: (size bs1 < size bs2). *)
  (*   rewrite Hlt in Hzp0. *)
  (*   rewrite Hzp0 in Hlt. *)
  (*   discriminate. *)
  (*   rewrite Hlt in Hzp0. *)
  (*   rewrite Hzp0 in Hlt. *)
  (*   move /negbT : Hlt. *)
  (*   rewrite <- (eqn0Ngt (size bs2)). *)
  (*   intro. *)
  (*   move /eqP : Hlt => Hlt. *)
  (*   apply size0nil in Hzp0. *)
  (*   apply size0nil in Hlt. *)
  (*   rewrite Hzp0 Hlt. *)
  (*   simpl. *)
  (*   reflexivity. *)


  (*   move: Hzp. *)
  (*   dcase zh => [[hd1 hd2] Hz]. *)
  (*   dcase (bool_adder c hd1 hd2) => [[c0 hd] Hadder]. *)
  (*   dcase (full_adder_zip c0 zt) => [[c1 tl] Hfull].   *)

  (*   case hd1; case hd2 => /=//. *)
    

  (*   case: bs1; case: bs2 => //. *)
  (* - move => b bs Hzs. case: Hzs => H1 H2. *)
  (*   have ->: zip (copy (size bs) b0) bs = extzip0 [::] bs by rewrite /extzip0/=; elim bs =>//. *)
  (*   move => H3. *)
  (*   move: (IH _ _ H3 c0). rewrite H2. *)
    (*
    to_Z_rcons:
  forall (bs : seq bool) (b : bool),
  to_Z (rcons bs b) = (if b then (- Z.succ (to_Zneg bs))%Z else to_Zpos bs)

  to_Zpos_negB:
  forall bs : bits,
  to_Zpos (-# bs) = (- to_Zpos bs mod 2 ^ Z.of_nat (size bs))%Z

      *)  
    
  Admitted.

  (* subtraction with extended bits *)
  Definition sbbB_ext b bs1 bs2 : bool * bits := adcB_ext (~~ b) bs1 (~~# bs2).
  Definition subB_ext bs1 bs2 := let (b, r) := (sbbB_ext false bs1 bs2) in rcons r b.
  Definition wky_subB_ext bs1 bs2 := let newl := (maxn (size bs1) (size bs2))+1 in
                                     let nbs1 := zext (newl-(size bs1)) bs1 in
                                     let nbs2 := zext (newl-(size bs2)) bs2 in
    let (b, r) := (sbbB_ext false nbs1 nbs2) in r.
  Compute (sbbB_ext false [::false;false] [::false;false]).
  Compute (subB_ext [::false;false] [::false;false]).
  Compute (wky_subB_ext [::false;false] [::false;true]).

  Lemma size_subB_ext bs1 bs2 : size bs1 = size bs2 -> size (wky_subB_ext bs1 bs2) = (maxn (size bs1) (size bs2))+1.
  Proof. 
    rewrite /wky_subB_ext.
    move=> Heql.
    rewrite /maxn Heql ltnn addn1 subSnn.
    rewrite /sbbB_ext /adcB_ext.
    rewrite size_full_adder_ext.
    fold (@cat bool bs1 (zeros 1)).
    rewrite size_invB size_zext addn1 size_cat size_zeros Heql addn1.
    rewrite /maxn ltnn.
    reflexivity.
  Qed.

  (*Lemma to_Zpos_subB_ext bs1 bs2 : size bs1 = size bs2 -> Z.geq (to_Zpos bs1) (to_Zpos bs2) -> to_Zpos (wky_subB_ext bs1 bs2) = Z.sub (to_Zpos bs1) (to_Zpos bs2).
  Proof.
    
  Qed.
  *)

  Fixpoint Sfull_mul (bs1 bs2 : bits) : bits :=
    match bs1 with
    | [::] => from_nat (size bs1 + size bs2) 0
    | hd::tl =>
    if tl == nil then (
      if hd then addB (invB (sext (size bs1) bs2)) (zext (size bs2) [::b1])
        else addB (invB (sext (size bs1) (zeros (size bs2)))) (zext (size bs2) [::b1])
      )
      else (
      if hd then addB (joinlsb false (Sfull_mul tl bs2)) (sext (size bs1) bs2)
        else joinlsb false (Sfull_mul tl bs2))
    end.

  Lemma size_Sfull_mul bs1 bs2: size (Sfull_mul bs1 bs2) = (size bs1) + (size bs2).
  Proof.
    elim: bs1 => [| b bs1 IH] /=.
    - by rewrite /full_mul add0n size_from_nat.
    - case Hbs1 : (bs1 == [::]).
      + case b.
      move /eqP : Hbs1 => Hbs1.
      rewrite Hbs1 size_addB size_invB size_sext size_zext.
      simpl.
      rewrite addn1 add1n /minn ltnn //.
      move /eqP : Hbs1 => Hbs1.
      rewrite Hbs1 size_addB size_invB size_sext size_zext size_zeros.
      simpl.
      rewrite addn1 add1n /minn ltnn //.
      + case b.
      rewrite size_addB size_sext size_joinlsb IH.
      rewrite addnACl add1n /minn ltnn addnC.
      reflexivity.
      by rewrite size_joinlsb IH addSn addn1.
  Qed.

  Lemma to_Zpos_Sfull_mul bs1 bs2: to_Zpos (Sfull_mul bs1 bs2) = Z.mul (to_Zpos bs1) (to_Zpos bs2).
  Proof.
    move : bs2. elim bs1 => [|hd1 tl1 IH] bs2 /=.
     first by rewrite!from_natn0 size_zeros!add0n. 
    move : (to_nat_bounded ptl1) => Hbd1; move : (to_nat_bounded p2) => Hbd2.
    move : (ltn_mul Hbd1 Hbd2); rewrite -expnD; move => Hbd. generalize Hbd.
    rewrite -(ltn_pmul2l (ltn0Sn 1)) -expnS mulnC in Hbd. move => Hbd'.
    case phd1. 
    - rewrite/= to_nat_addB size_addB size_joinlsb to_nat_joinlsb (IH p2)
             size_full_mul size_zext to_nat_zext addn1
      -addSn addnC minnn addn0 !to_nat_from_nat -!muln2 muln_modl.
      rewrite addnS expnS.
      have-> :(2 * 2 ^ (size p2 + size ptl1) = (2 ^ (size ptl1 + size p2) * 2)) by rewrite mulnC addnC. rewrite div.modnDml.
      have->:(((1 + to_nat ptl1 * 2) * to_nat p2) = to_nat ptl1 * to_nat p2 * 2 + to_nat p2) by rewrite mulnDl mul1n; ring. done.
    - rewrite size_joinlsb to_nat_joinlsb (IH p2) size_full_mul addn0 add0n-!muln2!to_nat_from_nat_bounded; first ring; try exact. by rewrite addn1 mulnAC.

    (*
    Lemma to_Zpos_full_mul bs1 bs2 :
    to_Zpos (full_mul bs1 bs2) = (to_Zpos bs1 * to_Zpos bs2)%Z.
  Proof.
    move: (to_nat_full_mul' bs1 bs2) => Hnat.
    apply (f_equal Z.of_nat) in Hnat. rewrite Nat2Z.inj_mul -!to_Zpos_nat in Hnat.
    exact: Hnat.
  Qed.
  *)
  Admitted.

  (*Compute (sext 2 [::b1;b0]).
  Compute (joinlsb false(addB (zeros ((size [::b1;b0])+1)) (addB (invB (sext (size [::b1]) [::b1;b0])) (zext (size [::b1;b0]) [::b1])))).
  Compute (Sfull_mul [::b1;b1] [::b0;b1]).
  Compute (cat [::b1;b1] [::b0;b1]).*)
  
  Definition ebinop_op (o : ebinop) (t1 t2 : fgtyp) : bits -> bits -> bits :=
    match t1, t2 with
    | Fuint w1, Fuint w2 =>
      fun a b =>
        let w := max w1 w2 in
        let ea := zext (w-w1) a in
        let eb := zext (w-w2) b in
      match o with
      | Badd => addB_ext a b
      | Bsub => wky_subB_ext a b
      | Bdiv => udivB' a b
      | Brem => low (minn w1 w2) (uremB a b)
      (* | Bsdiv => sdivB *)
      (* | Bsrem => sremB *)
      | Bmul => full_mul a b
      | Bcomp c => binop_bcmp c a b
      | Band => andB ea eb
      | Bor => orB ea eb
      | Bxor => xorB ea eb
      | Bcat => cat (*(zext (w2 - size b) b) (zext (w1 - size a) a)*) b a
      | Bdshl => cat (zeros (to_nat b)) a
      | Bdshr => (shrB (to_nat b) a)
      end
    | Fsint w1, Fsint w2 =>
      fun a b =>
        let w := max w1 w2 in
        let ea := sext (w-w1) a in
        let eb := sext (w-w2) b in
      match o with
      | Badd => let (c, r) := adcB false ea eb in 
      (if (msb ea) == (msb eb) then (rcons r c) else (rcons r (~~c)))
      | Bsub => let (b, r) := sbbB false ea eb in 
      (if (msb ea) == (msb eb) then (rcons r b) else (rcons r (~~b)))
      | Bdiv => sext 1 (sdivB a b)
      | Brem => low (minn w1 w2) (sremB a b)
      | Bmul => Sfull_mul a b
      | Bcomp c => binop_sbcmp c ea eb
      | Band => andB ea eb
      | Bor => orB ea eb
      | Bxor => xorB ea eb
      | Bcat => cat (*sext (w2 - size b) b) (sext (w1 - size a) a*) b a
      | _ => a
      end
    | Fsint _, Fuint _ =>
      fun a b =>
      match o with
      | Bdshl => cat (zeros (to_nat b)) a
      | Bdshr => (sarB (to_nat b) a)
      | _ => a
      end
    | _, _ => fun a b => a
    end.
    
  Fixpoint type_of_fexpr (e : fexpr) (te : TE.env) : fgtyp :=
    match e with
    | Econst t c => t
    | Eref v => TE.vtyp v te
    | Ecast AsUInt e => Fuint (sizeof_fgtyp (type_of_fexpr e te))
    | Ecast AsSInt e => Fsint (sizeof_fgtyp (type_of_fexpr e te))
    | Ecast AsClock e => Fuint 1
    | Ecast AsReset e => Fuint 1
    | Ecast AsAsync e => Fuint 1
    | Eprim_unop u e => match u with
                        | Upad n => match (type_of_fexpr e te) with
                                    | Fuint _ => Fuint n
                                    | Fsint _ => Fsint n
                                    | _ => TE.deftyp
                                    end
                        | Uandr | Uorr | Uxorr => Fuint 1
                        | Uextr n1 n2 => Fuint (n2 - n1 + 1)
                        | Uhead n => Fuint n
                        | Utail n => Fuint ((sizeof_fgtyp (type_of_fexpr e te)) - n)
                        | Ushl n => match (type_of_fexpr e te) with
                                    | Fuint w => Fuint (w + n)
                                    | Fsint w => Fsint (w + n)
                                    | _ => TE.deftyp
                                    end
                        | Ushr n => match (type_of_fexpr e te) with
                                    | Fuint w => if n < w then Fuint (w - n) else Fuint 1
                                    | Fsint w => if n < w then Fsint (w - n) else Fsint 1
                                    | _ => TE.deftyp
                                    end
                        | Ucvt => match (type_of_fexpr e te) with
                                  | Fuint w => Fsint (w + 1)
                                  | Fsint w => Fsint w
                                  | _ => TE.deftyp
                                  end
                        | Uneg => match (type_of_fexpr e te) with
                                  | Fuint w => Fsint (w + 1)
                                  | Fsint w => Fsint (w + 1)
                                  | _ => TE.deftyp
                                  end
                        | Unot => match (type_of_fexpr e te) with
                                  | Fuint w => Fuint w
                                  | Fsint w => Fuint w
                                  | _ => TE.deftyp
                                  end
                        end
    | Eprim_binop b e1 e2 => match b with
                             | Bdshl => match (type_of_fexpr e1 te) with
                                                | Fuint n => Fuint (n + (Nat.pow 2 (sizeof_fgtyp (type_of_fexpr e2 te))) - 1)
                                                | Fsint n => Fsint (n + (Nat.pow 2 (sizeof_fgtyp (type_of_fexpr e2 te))) - 1)
                                                | _ => TE.deftyp
                                                end
                             | Bdshr => match (type_of_fexpr e1 te) with
                                                | Fuint n => Fuint n
                                                | Fsint n => Fsint n
                                                | _ => TE.deftyp
                                                end
                             | Badd | Bsub => match type_of_fexpr e1 te, type_of_fexpr e2 te with
                                              | Fuint s1, Fuint s2 => Fuint ((maxn s1 s2)+1)
                                              | Fsint s1, Fsint s2 => Fsint ((maxn s1 s2)+1)
                                              | _, _ => TE.deftyp
                                              end
                             | Bmul => match type_of_fexpr e1 te, type_of_fexpr e2 te with
                                              | Fuint s1, Fuint s2 => Fuint (s1 + s2)
                                              | Fsint s1, Fsint s2 => Fsint (s1 + s2)
                                              | _, _ => TE.deftyp
                                       end
                             | Bcomp c => Fuint 1
                             | Band | Bor | Bxor => match type_of_fexpr e1 te, type_of_fexpr e2 te with
                                                    | Fuint s1, Fuint s2 => Fuint (maxn s1 s2)
                                                    | Fsint s1, Fsint s2 => Fsint (maxn s1 s2)
                                                    | _, _ => TE.deftyp
                                                    end
                             | Bdiv => match type_of_fexpr e1 te with
                                       | Fuint n => Fuint n
                                       | Fsint n => Fsint (n+1)
                                       | _ => TE.deftyp
                                       end
                             | Brem => match type_of_fexpr e1 te, type_of_fexpr e2 te with
                                       | Fuint s1, Fuint s2 => Fuint (minn s1 s2)
                                       | Fsint s1, Fsint s2 => Fsint (minn s1 s2)
                                       | _, _ => TE.deftyp
                                       end
                             | Bcat => match type_of_fexpr e1 te, type_of_fexpr e2 te with
                                      | Fuint s1, Fuint s2 => Fuint (s1 + s2)
                                      | Fsint s1, Fsint s2 => Fuint (s1 + s2)
                                      | _, _ => TE.deftyp
                                      end
                             end
    | Emux c e1 e2 => let t1 := (type_of_fexpr e1 te) in
                      let t2 := (type_of_fexpr e2 te) in
                      match t1, t2 with
                      | Fuint w1, Fuint w2 => Fuint (max w1 w2)
                      | Fsint w1, Fsint w2 => Fsint (max w1 w2)
                      | _, _ => TE.deftyp
                      end
    | Evalidif c e => (* if (Z.ltb 0 (to_Z (eval_fexpr c s))) then *)
                      (type_of_fexpr e te)
    end.

  (* Expression evaluation, type env *)
  (*Definition upd_typenv_fexpr (e : fexpr) (te : TE.env) : TE.env :=
    match e with
    (* | Edeclare v t => TE.add v t te *)
    | Ecast AsUInt (Eref v) => TE.add v (Fuint (sizeof_fgtyp (TE.vtyp v te))) te
    | Ecast AsSInt (Eref v) => TE.add v (Fsint (sizeof_fgtyp (TE.vtyp v te))) te
    | Ecast AsClock (Eref v) => TE.add v (Fuint 1) te
    | Ecast AsReset (Eref v) => TE.add v (Fuint 1) te
    | Ecast AsAsync (Eref v) => TE.add v (Fuint 1) te
    | _ => te
    end.
  Compute (List.In b1 [::b0;b1]).*)

  (* Expression evaluation, value *)
  Fixpoint eval_fexpr (e : fexpr) (rs : vstate) (s : vstate) (te : TE.env) (readerls : seq var) (writerls : seq var) (data2etc : mapdata2etc) (memmap : mapmem) (read_la : boolmap) : vstate * bits :=
    match e with
    | Econst t c => let val := match t with
                    | Fuint w1 => zext (w1 - size c) c
                    | Fsint w2 => sext (w2 - size c) c
                    | _ => c
                    end in (rs, val)
    | Eref v => (* SV.acc v s*)
    if mylListIn v readerls (* reader ports *)
    then match TE.find v data2etc with
        | None => (rs, [::b0])
        | Some a => 
          let '(addrvar, envar, midvar, flagvar, clkvar) := a in 
          match TE.find midvar read_la with(* 没有找到m是同步或异步 *)
          | None => (rs, [::b0])
          | Some thisread_la =>
          let addrval := SV.acc addrvar s in
          let enval := SV.acc envar s in
          let clk0val := SV.acc clkvar s in
          let clkval := SV.acc clkvar rs in
          let flagval := SV.acc flagvar s in
          let readv := 
          (if enval == [:: b0]
            then [::b0]
          else 
          (match TE.find midvar memmap with
          | None => [::b0]
          | Some b => memfind addrval b
          end)) in 
          if thisread_la == false
          then (*if (((clk0val == [:: b0]) && (clkval == [:: b1])) || (flagval == [::b1]))
              then*) (rs, readv)
              (*else (rs, [:: b0])*)
          else if (((clk0val == [:: b0]) && (clkval == [:: b1])) || (flagval == [::b1]))
              then (*(SV.upd v readv rs, SV.acc v s)*)(rs, readv)
              else ((*SV.upd v readv *)rs, [::b0])
          end
        end
    else (rs, SV.acc v s) (* inst ports & others *)
    | Eprim_binop b e1 e2 =>
      let (rs0, ve1) := (eval_fexpr e1 rs s te readerls writerls data2etc memmap read_la) in
      let (rs1, ve2) := (eval_fexpr e2 rs0 s te readerls writerls data2etc memmap read_la) in
      let te1 := type_of_fexpr e1 te in
      let te2 := type_of_fexpr e2 te in
      let val := (ebinop_op b te1 te2) ve1 ve2 in
      (rs1, val)
    | Eprim_unop u e =>
      let t := type_of_fexpr e te in
      let (rs0, val1) := (eval_fexpr e rs s te readerls writerls data2etc memmap read_la) in
      let val := (eunop_op u t) val1 in
      (rs0, val)
    | Emux c e1 e2 =>
      let t1 := (type_of_fexpr e1 te) in
      let t2 := (type_of_fexpr e2 te) in
      let (rs0, valc) := (eval_fexpr c rs s te readerls writerls data2etc memmap read_la) in
      let (rs1, val1) := (eval_fexpr e1 rs0 s te readerls writerls data2etc memmap read_la) in
      let (rs2, val2) := (eval_fexpr e2 rs1 s te readerls writerls data2etc memmap read_la) in
      let val := match t1, t2 with
      | Fuint w1, Fuint w2 => if ~~ (is_zero valc) 
      then (zext ((max w1 w2) - w1) val1) 
      else (zext ((max w1 w2) - w2) val2)
      | Fsint w1, Fsint w2 => if ~~ (is_zero valc) 
      then (sext ((max w1 w2) - w1) val1)
      else (sext ((max w1 w2) - w2) val2)
      | _, _ => [::]
      end in (rs2, val)
    | Evalidif c e => 
      let (rs0, valc) := (eval_fexpr c rs s te readerls writerls data2etc memmap read_la) in
      let (rs1, val1) := (eval_fexpr e rs0 s te readerls writerls data2etc memmap read_la) in
      let val := if ~~ (is_zero valc) then val1 else [::] in
      (rs1, val)
    (* | Edeclare v t => zeros (sizeof_fgtyp t) *)
    | Ecast AsUInt e => 
      let (rs0, val) := (eval_fexpr e rs s te readerls writerls data2etc memmap read_la) in (rs0, val)
    | Ecast AsSInt e => let (rs0, val) := eval_fexpr e rs s te readerls writerls data2etc memmap read_la in (rs0, val)
    | Ecast AsClock e => let (rs0, val1) := (eval_fexpr e rs s te readerls writerls data2etc memmap read_la) in
                         let val := [::lsb val1] in (rs0, val)
    | Ecast AsReset e => let (rs0, val1) := (eval_fexpr e rs s te readerls writerls data2etc memmap read_la) in
                         let val := [::lsb val1] in (rs0, val)
    | Ecast AsAsync e => let (rs0, val1) := (eval_fexpr e rs s te readerls writerls data2etc memmap read_la) in
                         let val := [::lsb val1] in (rs0, val)
    end.
  
  (*Compute (ebinop_op Bcat (Fuint 4) (Fuint 4) [::true; true;true; true] [:: true]).
  Compute (ebinop_op Bsub (Fuint 16) (Fuint 16) [:: false] [:: false]).*)

  Definition upd_typenv_fport (p : fport) (te : TE.env) : TE.env :=
    match p with
    | Finput v t => TE.add v t te
    | Foutput v t => TE.add v t te
    end.

  Fixpoint upd_typenv_fports (ps : seq fport) (te : TE.env) : TE.env :=
    match ps with
    | [::] => te
    | h :: tl => upd_typenv_fports tl (upd_typenv_fport h te)
    end.

  (* Expression statement, type env *)
  Definition upd_typenv_fstmt (s : fstmt) (te : TE.env) (st : vstate) : TE.env :=
    match s with
    | Swire v t  => TE.add v t te
    | Sreg r => TE.add (rid r) (type r) te
    | Snode v e => TE.add v (type_of_fexpr e te) te
    | Smem m => let te1 := List.fold_left (fun tt tr => let tt0 := TE.add (addr tr) (Fuint ((Nat.log2 (depth m)) )) tt in
                                             let tt1 := TE.add (data tr) (data_type m) tt0 in
                                             let tt2 := TE.add (en tr) (Fuint 1) tt1 in
                                             TE.add (clk tr) Fclock tt2 
                               ) (reader m) te in
                            List.fold_left (fun tt tr => let tt0 := TE.add (addr0 tr) (Fuint ((Nat.log2 (depth m)) )) tt in
                               let tt1 := TE.add (data0 tr) (data_type m) tt0 in
                               let tt2 := TE.add (en0 tr) (Fuint 1) tt1 in
                               let tt3 := TE.add (clk0 tr) Fclock tt2 in
                               TE.add (mask tr) (Fuint 1) tt3
                               ) (writer m) (TE.add (mid m) Fclock te1) (* mid不代表任何值 *)
    | Sinst inst => upd_typenv_fports (iports inst) te
    | Sfcnct (Eref v) e2 => TE.add v (type_of_fexpr e2 te) te
    | _ => te
    end.

  Fixpoint upd_typenv_fstmts (ss : seq fstmt) (te : TE.env) (s : vstate) : TE.env :=
    match ss with
    | [::] => te
    | h :: tl => upd_typenv_fstmts tl (upd_typenv_fstmt h te s) s
    end.

  Definition eval_noninst_fstmt (st : fstmt) (rs : vstate) (s : vstate) (te : TE.env) (readerls : seq var) (writerls : seq var) (data2etc : mapdata2etc) (memmap : mapmem) (read_la : boolmap)
 : vstate * vstate * mapmem :=
    match st with
        | Sskip => (rs, s, memmap)
        | Swire v t => (rs, SV.upd v (zeros (sizeof_fgtyp t)) s, memmap)
        | Sreg r =>
          let (rs0, s0) := if SV.acc (rid r) rs == [::]
                          then (SV.upd (rid r) (zeros (sizeof_fgtyp (type r))) rs,
                                SV.upd (rid r) (zeros (sizeof_fgtyp (type r))) s)
                          else (rs, SV.upd (rid r) (SV.acc (rid r) rs) s) in
                    match reset r with
                    | NRst => (rs0, s0, memmap)
                    | Rst e1 e2 =>
                        let te1 := type_of_fexpr e1 te in
                        let (_, ve1) := eval_fexpr e1 rs s0 te readerls writerls data2etc memmap read_la in
                        let (_, ve2) := eval_fexpr e2 rs s0 te readerls writerls data2etc memmap read_la in
                        if (is_zero ve1) then (rs0, s0, memmap)
                        else
                          match te1 with
                          | Fuint 1 => (SV.upd (rid r) ve2 rs0, s0, memmap)
                          | Fasyncreset => (SV.upd (rid r) ve2 rs0, SV.upd (rid r) ve2 s0, memmap)
                          | _ => (rs0, s0, memmap)
                          end
                    end
        | Smem m => (* mem.clk 放入rs *)
          let (rs1, s1) := List.fold_left (fun '(trs, ts) tr => if SV.acc (clk tr) trs == [::]
                                                then (SV.upd (clk tr) [:: b0] trs, SV.upd (flag tr) [:: b0] (SV.upd (clk tr) [:: b1] ts))
                                                else if (SV.acc (flag tr) ts == [::b1])
                                                  then (trs,ts)
                                                  else if ((SV.acc (clk tr) trs == [::b1]) && (SV.acc (clk tr) ts == [::b0]) && (SV.acc (flag tr) ts == [::b0]))
                                                  then (trs, SV.upd (flag tr) [::b1] ts)
                                                  else (trs, SV.upd (clk tr) (SV.acc (clk tr) trs) ts)
          ) (reader m) (rs, s) in
          let (rs2, s2) := List.fold_left (fun '(trs, ts) tr => if SV.acc (clk0 tr) trs == [::]
                                                then (SV.upd (clk0 tr) [:: b0] trs, SV.upd (clk0 tr) [:: b1] ts)
                                                else (trs, SV.upd (clk0 tr) (SV.acc (clk0 tr) trs) ts)
          ) (writer m) (rs1, s1) in
          (* write延迟 *)
          let (rs3, s3) := List.fold_left (fun '(trs, ts) tr => let '(trs0, ts0) := if SV.acc (data0 tr) trs == [::]
                                                                then (SV.upd (data0 tr) (zeros (sizeof_fgtyp (data_type m))) trs,
                                                                      SV.upd (data0 tr) (zeros (sizeof_fgtyp (data_type m))) ts)
                                                                else (trs, SV.upd (data0 tr) (SV.acc (data0 tr) trs) ts) in
                                                                let '(trs1, ts1) := if SV.acc (addr0 tr) trs == [::]
                                                                then (SV.upd (addr0 tr) (zeros (Nat.log2 (depth m))) trs0,
                                                                      SV.upd (addr0 tr) (zeros (Nat.log2 (depth m))) ts0)
                                                                else (trs0, SV.upd (addr0 tr) (SV.acc (addr0 tr) trs0) ts0) in
                                                                let '(trs2, ts2) := if SV.acc (en0 tr) trs == [::]
                                                                then (SV.upd (en0 tr) [::b0] trs1,
                                                                      SV.upd (en0 tr) [::b0] ts1)
                                                                else (trs1, SV.upd (en0 tr) (SV.acc (en0 tr) trs1) ts1) in
                                                                if SV.acc (mask tr) trs == [::]
                                                                then (SV.upd (mask tr) [::b0] trs2,
                                                                      SV.upd (mask tr) [::b0] ts2)
                                                                else (trs2, SV.upd (mask tr) (SV.acc (mask tr) trs2) ts2)
          ) (writer m) (rs2, s2) in (rs3, s3, memmap)
          (*
        match TE.find (mid m) read_la with (* read延迟 *)
                  | None => (rs3, s3, memmap)
                  | Some thisread_la =>
                    if thisread_la == false 
                    then (rs3, s3, memmap)
                    else let (rs0, s0) := List.fold_left (fun '(trs, ts) tr => if SV.acc (data tr) trs == [::]
                                                                    then (SV.upd (data tr) (zeros (sizeof_fgtyp (data_type m))) trs,
                                                                          SV.upd (data tr) (zeros (sizeof_fgtyp (data_type m))) ts)
                                                                    else (trs, SV.upd (data tr) (SV.acc (data tr) trs) ts)
                    ) (reader m) (rs3, s3)
                    in (rs0, s0, memmap)
                  end*)
        | Sinst inst => (rs, s, memmap) (* 在拓扑排序时始终放在每个mod的最后，用来对所有的inst更新rs/s/memory *)
        | Snode v e => let (rs0, ve) := eval_fexpr e rs s te readerls writerls data2etc memmap read_la in
                      (rs0, SV.upd v ve s, memmap)
        | Sfcnct (Eref v) e2 => let (rs0, newv) := eval_fexpr e2 rs s te readerls writerls data2etc memmap read_la in 
                                let memmap0 := 
                                (if mylListIn v writerls (* writer ports *)
                                then match TE.find v data2etc with
                                      | None => memmap
                                      | Some a => (let '(addrvar,envar, midvar, maskvar, clkvar) := a in 
                                        match TE.find midvar memmap with
                                        | None => memmap (* parse ast时已生成所有mem的map TE.add midvar (memupd (from_nat 4 10) (from_nat 4 11) memempty) memmap*)
                                        | Some b => let maskval := SV.acc maskvar s in
                                                    let addrval := SV.acc addrvar s in 
                                                    let enval := SV.acc envar s in
                                                    let clkval := SV.acc clkvar rs in
                                                    let clk0val := SV.acc clkvar s in 
                                                    if ((enval == [:: b1]) && (clk0val == [:: b0]) && (clkval == [:: b1]))
                                                      then (if maskval == [:: b1]
                                                        then TE.add midvar (memupd addrval (SV.acc v s) b) memmap
                                                        else TE.add midvar (memupd addrval [:: b0] b) memmap
                                                      )
                                                      else
                                                      memmap
                                                    end
                                )
                                end
                                else memmap)
                                in
                                if SV.acc v rs0 == [::]
                                  then (rs0, SV.upd v newv s, memmap0)
                                else (SV.upd v newv rs0, s, memmap0) (* regs *)
        | Sinvalid v =>
          let tv := TE.vtyp v te in
          (rs, SV.upd v (zeros (sizeof_fgtyp tv)) s, memmap)
        | _ => (rs, s, memmap)
        end.

  Fixpoint eval_fstmt (st : fstmt) (rs : vstate) (s : vstate) (te : TE.env) (readerls : seq var) (writerls : seq var) (data2etc : mapdata2etc) (memmap : mapmem) (read_la : boolmap)
  (finstoutl : seq var) (finstoutm : maptuple) (ffmodsmap : mapfstmt) (fterss : mapterss) (fread_la : allboolmap) (finstin : mapls) (finstinmap : mvar) (finstoutmap : mapvar) 
  (rl : mapls) (wl : mapls) (alldata2etc : map2etc) (allfinstoutl : mapls) (allfinstoutm : mmaptuple) (allfinstportmap : mmapvar) iternum : vstate * vstate * mapmem * mapterss :=
  let te1 := upd_typenv_fstmt st te s in 
  match iternum with
  | 0 => let '(rs0,s0,memmap0) := eval_noninst_fstmt st rs s te1 readerls writerls data2etc memmap read_la in (rs0,s0,memmap0,fterss)
  | S iternum0 =>
    (match st with
        | Sfcnct (Eref v) e2 => let (newrs, newv) := (match e2 with 
                            | Eref v1 => if mylListIn v1 finstoutl
                                        then let v0 := (match TE.find v1 finstoutm with (* outport -> (mod name a4, inst name a0) *)
                                        | None => [::b1] (* 不知道inst.output对应的fmodule*)
                                        | Some (a4,a0) => (match TE.find a4 ffmodsmap with (* mod name -> fstmt seq mst *) 
                                                    | None => [::b1;b1]
                                                    | Some mst => (match TE.find a0 fterss with
                                                                | None => [::b1;b1;b1]
                                                                | Some aa => let '(te0,rs0,s0,mem0) := aa in (match TE.find a4 finstin with (* mod name -> inport name list *)
                                                                                                        | None => [::b1;b1;b1;b1]
                                                                                                        | Some a2 => (match TE.find a0 finstinmap with
                                                                                                                    | None => [::b1;b1;b1;b1]
                                                                                                                    | Some a5 => (let updfinstin := a5 in
                                                                                                        (let s1 := upd_inner s s0 a2 updfinstin in 
                                                                                                          (* evaluate inner module *)
                                                                                                          let s2 := (let readerls0 := (match TE.find a4 rl with
                                                                                                                              | None =>  nil
                                                                                                                              | Some a => a 
                                                                                                                              end) in
                                                                                                                              let writerls0 := (match TE.find a4 wl with
                                                                                                                              | None =>  nil
                                                                                                                              | Some a => a 
                                                                                                                              end) in
                                                                                                                              let finstoutl0 := (match TE.find a4 allfinstoutl with
                                                                                                                              | None =>  nil
                                                                                                                              | Some a => a 
                                                                                                                              end) in
                                                                                                                              match TE.find a4 alldata2etc with
                                                                                                                              | None => s
                                                                                                                              | Some a => let data2etc0 := a in 
                                                                                                                              match TE.find a4 fread_la with
                                                                                                                              | None => s
                                                                                                                              | Some a => let read_la0 := a in
                                                                                                                                match TE.find a4 allfinstoutm with
                                                                                                                                | None =>  s
                                                                                                                                | Some a => let finstoutm0 := a in
                                                                                                                                  match TE.find a4 allfinstportmap with
                                                                                                                                  | None =>  s
                                                                                                                                  | Some a => let (finstinmap0,finstoutmap0) := a in
                                                                                                                                      let '(_, s2, _, _) := 
                                                                                                                                      List.fold_left (fun '(trs, ts, tmemmap, tfterss) tempst => eval_fstmt tempst trs ts te0 readerls0 writerls0 data2etc0 mem0 read_la0 finstoutl0 finstoutm0 ffmodsmap tfterss fread_la finstin finstinmap0 finstoutmap0 rl wl alldata2etc allfinstoutl allfinstoutm allfinstportmap iternum0) (rev mst) (rs0, s1, mem0, fterss) in
                                                                                                                                      s2   
                                                                                                                                  end
                                                                                                                                end
                                                                                                                                end
                                                                                                                              end) in
                                                                                                          (match TE.find v1 finstoutmap with
                                                                                                          | None => [::b1;b1;b1;b1;b1]
                                                                                                          | Some a3 => (*[::b1;b1;b1;b1;b1;b1]*)SV.acc a3 s2
                                                                                                          end)))
                                                                                                          end)
                                                                                                        end)
                                                                end)
                                                    end)
                                        end) in (rs, v0)                                 
                                        else (eval_fexpr e2 rs s te1 readerls writerls data2etc memmap read_la)
                            | _ => (eval_fexpr e2 rs s te1 readerls writerls data2etc memmap read_la)
                            end) in 
                            let memmap0 := 
                            (if mylListIn v writerls (* writer ports *)
                            then match TE.find v data2etc with
                                  | None => memmap
                                  | Some a => (let '(addrvar,envar, midvar, maskvar, clkvar) := a in 
                                    match TE.find midvar memmap with
                                    | None => memmap (* parse ast时已生成所有mem的map TE.add midvar (memupd (from_nat 4 10) (from_nat 4 11) memempty) memmap*)
                                    | Some b => let maskval := SV.acc maskvar s in
                                                let addrval := SV.acc addrvar s in 
                                                let clkval := SV.acc clkvar rs in
                                                let clk0val := SV.acc clkvar s in 
                                                let enval := SV.acc envar s in
                                                if ((enval == [:: b1]) && (clk0val == [:: b0]) && (clkval == [:: b1]))
                                                  then (if maskval == [:: b1]
                                                    then TE.add midvar (memupd addrval (SV.acc v s) b) memmap(*TE.add midvar (memupd (from_nat 2 3) (from_nat 4 13) b) memmap*)
                                                    else TE.add midvar (memupd addrval [:: b0] b) memmap(*TE.add midvar (memupd (from_nat 2 3) (from_nat 4 12) b) memmap*)
                                                  )
                                                  else
                                                  (*TE.add midvar (memupd (from_nat 2 3) (from_nat 4 10) b) *)memmap
                                                end
                            )
                            end
                            else memmap)in
                            if SV.acc v newrs == [::]
                              then (newrs, SV.upd v newv s, memmap0, fterss)
                            else (SV.upd v newv newrs, s, memmap0, fterss) (* regs *)
    | Sinst inst => let v := iid inst in
                  match TE.find (imid inst) ffmodsmap with (* mod name -> fstmt seq mst *) 
                  | None => (SV.upd v [:: b1] rs,s,memmap,fterss)
                  | Some mst => (match TE.find (iid inst) fterss with
                              | None => (SV.upd v [:: b1;b1] rs,s,memmap,fterss)
                              | Some aa => let '(te0,rs0,s0,mem0) := aa in (match TE.find (imid inst) finstin with (* mod name -> inport name list *)
                                                                          | None => (SV.upd v [:: b1;b1;b1] rs,s,memmap,fterss)
                                                                          | Some a2 => (match TE.find v finstinmap with
                                                                                      | None => (rs,s,memmap,fterss)
                                                                                      | Some a3 => (let updfinstin := a3 in
                                                                          (let s1 := upd_inner s s0 a2 updfinstin in
                                                                           (* evaluate inner module *)
                                                                           let readerls0 := (match TE.find (imid inst) rl with
                                                                                  | None =>  nil
                                                                                  | Some a => a 
                                                                                  end) in
                                                                                  let writerls0 := (match TE.find (imid inst) wl with
                                                                                  | None =>  nil
                                                                                  | Some a => a 
                                                                                  end) in
                                                                                  let finstoutl0 := (match TE.find (imid inst) allfinstoutl with
                                                                                  | None =>  nil
                                                                                  | Some a => a 
                                                                                  end) in
                                                                                  match TE.find (imid inst) alldata2etc with
                                                                                  | None => (SV.upd v [:: b1;b1;b1] rs,s,memmap,fterss)
                                                                                  | Some a => let data2etc0 := a in 
                                                                                    match TE.find (imid inst) allfinstoutm with
                                                                                    | None =>  (SV.upd v [:: b1;b1;b1;b1] rs,s,memmap,fterss)
                                                                                    | Some a => let finstoutm0 := a in
                                                                                      match TE.find (imid inst) allfinstportmap with
                                                                                      | None =>  (SV.upd v [:: b1;b1;b1;b1;b1] rs,s,memmap,fterss)
                                                                                      | Some a => let (finstinmap0,finstoutmap0) := a in
                                                                                        match TE.find (imid inst) fread_la with
                                                                                        | None => (SV.upd v [:: b1;b1;b1;b1;b1] rs,s,memmap,fterss)
                                                                                        | Some a => let read_la0 := a in
                                                                                          let '(rs2, s2, memmap2, fterss2) := 
                                                                                          List.fold_left (fun '(trs, ts, tmemmap, tfterss) tempst => eval_fstmt tempst trs ts te0 readerls0 writerls0 data2etc0 mem0 read_la0 finstoutl0 finstoutm0 ffmodsmap tfterss fread_la finstin finstinmap0 finstoutmap0 rl wl alldata2etc allfinstoutl allfinstoutm allfinstportmap iternum0) (rev mst) (rs0, s1, mem0, fterss) in
                                                                                          (rs, s, memmap, TE.add v (te0,rs2,s2,memmap2) fterss2)
                                                                                      end
                                                                                    end
                                                                                    end
                                                                                  end))
                                                                                  end)
                                                                          end)
                              end)
                  end
    | _ => let '(rs0,s0,memmap0) := eval_noninst_fstmt st rs s te1 readerls writerls data2etc memmap read_la in (rs0,s0,memmap0,fterss)
    end)
    end.  

  Fixpoint eval_fstmts st rs s te (readerls : seq var) (writerls : seq var) (data2etc : mapdata2etc) (memmap : mapmem) (read_la : boolmap)
  (finstoutl : seq var) (finstoutm : maptuple) (ffmodsmap : mapfstmt) (fterss : mapterss) (fread_la : allboolmap) (finstin : mapls) (finstinmap : mvar) (finstoutmap : mapvar) 
  (rl : mapls) (wl : mapls) (alldata2etc : map2etc) (allfinstoutl : mapls) (allfinstoutm : mmaptuple) (allfinstportmap : mmapvar) iternum : vstate * vstate * mapmem * mapterss :=
    match st with
    | [::] => (rs, s, memmap, fterss) (* 对所有inst更新 terss、memory *)
    | h :: tl => let te1 := upd_typenv_fstmt h te s in 
      let '(rs1, s1, memmap0, fterss0) := eval_fstmt h rs s te1 readerls writerls data2etc memmap read_la finstoutl finstoutm ffmodsmap fterss fread_la finstin finstinmap finstoutmap rl wl alldata2etc allfinstoutl allfinstoutm allfinstportmap iternum in
      eval_fstmts tl rs1 s1 te1 readerls writerls data2etc memmap0 read_la finstoutl finstoutm ffmodsmap fterss0 fread_la finstin finstinmap finstoutmap rl wl alldata2etc allfinstoutl allfinstoutm allfinstportmap iternum
    end.

  Fixpoint upd_argulist s (io_in : mapioin) name ind : vstate :=
    match name with
     | [:: ] => s
     | h::t => let tin := match TE.find h io_in with
                          | None => nil
                          | Some a => a
                          end in
     upd_argulist (SV.upd h (List.nth ind tin [::b0]) s) io_in t ind
    end.

  Definition myupdateo s2 omap l := 
  let newv := SV.acc l s2 in
  let newl := match (TE.find l omap) with
  | Some a => (List.rev (List.cons newv (List.rev a)))
  | None => [:: [::b1]]
  end in
  TE.add l newl omap.

  Definition eval_module (v : var) rs s (te : TE.env) (io_in : mapioin) ols (readerls : mapls) (writerls : mapls) (data2etc : map2etc) (memmap : mapmem)
  (finstoutl : mapls) (finstoutm : mmaptuple) (ffmodsmap : mapfstmt) (fterss : mapterss) (fread_la : allboolmap) (finstin : mapls) (finstportmap : mmapvar) (iternum : nat) : vstate * vstate * mapmem * mapterss * mapioin :=
    match (TE.find v ffmodsmap) with
    | Some st => (*let te0 := upd_typenv_fports ps (TE.empty) in 在ocaml赋初值，因为要run多个周期，需放在clk_step外*)
                        let readerls0 := (match TE.find v readerls with
                        | None =>  nil
                        | Some a => a 
                        end) in
                        let writerls0 := (match TE.find v writerls with
                        | None =>  nil
                        | Some a => a 
                        end) in
                        let finstoutl0 := (match TE.find v finstoutl with
                        | None =>  nil
                        | Some a => a 
                        end) in
                        match TE.find v data2etc with
                        | None => (rs,s, memmap, fterss, io_in)
                        | Some a => let data2etc0 := a in 
                        match TE.find v fread_la with
                        | None => (rs,s, memmap, fterss, io_in)
                        | Some read_la =>
                          match TE.find v finstoutm with
                          | None =>  (rs,s, memmap, fterss, io_in)
                          | Some a => let finstoutm0 := a in
                            match TE.find v finstportmap with
                            | None =>  (rs,s, memmap, fterss, io_in)
                            | Some a => let (finstinmap0,finstoutmap0) := a in
                            let '(rs2,s2, memmap2, fterss2) := eval_fstmts (rev st) rs s te readerls0 writerls0 data2etc0 memmap read_la finstoutl0 finstoutm0 ffmodsmap fterss fread_la finstin finstinmap0 finstoutmap0 readerls writerls data2etc finstoutl finstoutm finstportmap iternum in
                            let io_in2 := List.fold_left (myupdateo s2) ols io_in in
                            (rs2,s2, memmap2, fterss2, io_in2)
                            end
                            end
                          end
                        end
    | None => (rs,s, memmap, fterss, io_in)
    end.

Fixpoint run_module0 (mainmod : var) rs s te (io_in : mapioin) name ols readerls writerls data2etc memmap clk_num len 
  (finstoutl : mapls) (finstoutm : mmaptuple) (ffmodsmap : mapfstmt) (fterss : mapterss) (fread_la : allboolmap) (finstin : mapls) (finstportmap : mmapvar) iternum : vstate * vstate * mapmem * mapterss * mapioin :=
  match clk_num with
    | 0 => (rs,s,memmap,fterss,io_in)
    | S m => let n := len - S m in
             let s1 := upd_argulist s io_in name n in
             (*let te1 := upd_typenv_fstmts st te s1 in*) (* 放在和upd fports同时？ *)
             let '(rs2, s2, memmap0, fterss0, io_in0) := eval_module mainmod rs s1 te io_in ols readerls writerls data2etc memmap finstoutl finstoutm ffmodsmap fterss fread_la finstin finstportmap iternum in (* 每个clk后 fterss 需要更新*)
             run_module0 mainmod rs2 s2 te io_in0 name ols readerls writerls data2etc memmap0 m len finstoutl finstoutm ffmodsmap fterss0 fread_la finstin finstportmap iternum
    end.
    

Fixpoint expr2varlist (expr : fexpr) (ls : seq var) : seq var := 
  match expr with
  | Econst _ _ => ls
  | Eref v => List.cons v ls
  | Eprim_unop _ e1 => expr2varlist e1 ls
  | Eprim_binop _ e1 e2 => expr2varlist e2 (expr2varlist e1 ls)
  | Emux e1 e2 e3 => expr2varlist e3 (expr2varlist e2 (expr2varlist e1 ls))
  | Evalidif e1 e2 => expr2varlist e2 (expr2varlist e1 ls)
  | Ecast _ e => expr2varlist e ls
  end.

Definition findreg (ls roots : seq var) (st : fstmt) : seq var * seq var :=
  match st with
  | Sreg r => (List.cons (rid r) ls, List.cons (rid r) roots)
  | Snode v e => if (expr2varlist e [::] == [::]) then (ls, List.cons v roots)
                  else (ls, roots)
  | Sfcnct e1 e2 => (match e1 with
                    | Eref v1 => if (expr2varlist e2 [::] == [::]) then (ls, List.cons v1 roots)
                                else (ls, roots)
                    | _ => (ls, roots)
                    end)
  | Sinvalid v => (ls, List.cons v roots)
  | _ => (ls, roots)
  end.

  Definition findallvar (ls : seq var) (st : fstmt) : seq var :=
  match st with
  | Sreg r => List.cons (rid r) ls
  | Snode v _ => List.cons v ls
  | Swire v _ => List.cons v ls
  | Smem m => let ls0 := List.fold_left (fun tl tr => List.cons (addr tr) ls) (reader m) ls in
              List.fold_left (fun tl tr => List.cons (addr0 tr) ls) (writer m) ls0
  | Sinst inst => List.fold_left (fun tl tp => match tp with
                                  | Finput v _ => List.cons v tl
                                  | Foutput v _ => List.cons v tl
                                  end) (iports inst) ls
  | Sinvalid v => List.cons v ls
  | _ => ls
  end.

Definition def_known_reg_order (regls : seq var) (defls : seq fstmt) (knownls : seq fstmt) (regstmtls : seq fstmt) (st : fstmt) : seq fstmt * seq fstmt * seq fstmt :=
  match st with
  | Sskip => (defls, cons st knownls, regstmtls)
  | Swire _ _ => (cons st defls, knownls, regstmtls)
  | Sreg _ => (cons st defls, knownls, regstmtls)
  | Smem m => (cons st defls, knownls, regstmtls) 
  | Sinst _ => (defls, knownls, cons st regstmtls) (*TBD*)
  | Snode v e => if (expr2varlist e [::] == [::]) then (defls, cons st knownls, regstmtls)
                else (defls, knownls, regstmtls)
  | Sfcnct e1 e2 => (match e1 with
                    | Eref v1 => if (expr2varlist e2 [::] == [::]) then (defls, cons st knownls, regstmtls)
                                 else (if (varIn v1 regls) then (defls, knownls, cons st regstmtls)
                                                          else (defls, knownls, regstmtls))
                    | _ => (defls, knownls, regstmtls)
                    end)
  | Sinvalid _ => (defls, cons st knownls, regstmtls)
  | _ => (defls, knownls, regstmtls) (*Swhen\Sstop*)
  end.

Definition known_reg_orders (oldstmts : seq fstmt) : seq fstmt * seq fstmt * seq fstmt := 
  let (regls, _) := List.fold_left (fun '(ls1, ls2) tst => findreg ls1 ls2 tst) oldstmts ([::], [::]) in
  let '(revdefls, revknownls, revregstmtls) := List.fold_left (fun '(templ1, templ2, templ3) st => def_known_reg_order regls templ1 templ2 templ3 st) oldstmts ([::],[::],[::]) in
  let knownls := List.rev revknownls in 
  let regstmtls := List.rev revregstmtls in
  let defls := List.rev revdefls in
  (defls, knownls, regstmtls).

Definition addreader2g (tempg : g) (tempr : freader_port) : g :=
  let g0 := updg (addr tempr) (cons (data tempr) (findg (addr tempr) tempg)) tempg in
  let g1 := updg (en tempr) (cons (data tempr) (findg (en tempr) g0)) g0 in
  updg (clk tempr) (cons (data tempr) (findg (clk tempr) g1)) g1.

Definition addwriter2g (tempg : g) (tempw : fwriter_port) : g :=
  let g0 := updg (addr0 tempw) (cons (data0 tempw) (findg (addr0 tempw) tempg)) tempg in
  let g1 := updg (en0 tempw) (cons (data0 tempw) (findg (en0 tempw) g0)) g0 in
  let g2 := updg (clk0 tempw) (cons (data0 tempw) (findg (clk0 tempw) g1)) g1 in
  updg (mask tempw) (cons (data0 tempw) (findg (mask tempw) g2)) g2.

Definition addnewruw2g0 (temprl : seq freader_port) (tempg : g) (tempw : fwriter_port) : g :=
  List.fold_left (fun tg tempr => updg (data0 tempw) (cons (data tempr) (findg (data0 tempw) tg)) tg) temprl tempg.

Definition addnewruw2g1 (temprl : seq freader_port) (tempg : g) (tempw : fwriter_port) : g :=
  List.fold_left (fun tg tempr => updg (data tempr) (cons (data0 tempw) (findg (data tempr) tg)) tg) temprl tempg.

Definition inst_inoutlist (pl : seq fport) : seq var * seq var :=
  List.fold_left (fun '(il, ol) tempp => match tempp with
                                        | Finput v _ => (List.cons v il, ol)
                                        | Foutput v _ => (il, List.cons v ol)
                                        end) pl ([::],[::]).

Fixpoint dfs (fing : g) (n : nat) (v : seq var) (x : var) : seq var :=
  if (varIn x v) then v else (
    match n with 
    | S n' => foldl (dfs fing n') (x :: v) (fing x)
    | 0 => v
    end).

(* y是否依赖于x *)
Definition dfs_path (fing : g) (n : nat) (x : var) (y : var) : bool :=
  let xchildren := dfs fing n [::] x in
  varIn y xchildren.

Definition add_regedge (regls : seq var) (fing : g) (st : fstmt) 
  : g :=
  match st with
  | Sfcnct e1 e2 => (match e1 with
                    | Eref v1 => (match e2 with
                                | Econst _ _ => fing
                                | _ => (if (varIn v1 regls) then (let preset := expr2varlist e2 [::] in
                                              List.fold_left (fun tempg tempv => updg tempv (cons v1 (findg tempv tempg)) tempg) preset fing) else fing)
                                end)
                    | _ => fing
                    end)
  | _ => fing
  end.

Definition buildg (regls : seq var) (flagmap : fmap) (inportsmap : mapvar) (outportsmap : mapvar) (knowng : mapg) (fing : g) (var2stmt : var2stmtmap) (st : fstmt) 
  : g * var2stmtmap :=
  match st with
  | Sskip => (fing, var2stmt)
  | Swire _ _ => (fing, var2stmt)
  | Sreg _ => (fing, var2stmt)
  | Smem m => let readerls := reader m in
              let newg0 := List.fold_left addreader2g readerls fing in
              let writerls := writer m in
              let newg1 := List.fold_left addwriter2g writerls newg0 in
              let newg := (match (read_write m) with
              | old => List.fold_left (addnewruw2g1 readerls) writerls newg1  (* reader的后继是writer *)
              | new => List.fold_left (addnewruw2g0 readerls) writerls newg1  (* writer后继是reader *)
              | undefined => newg1
              end) in
              (newg, var2stmt) 
  | Sinst inst => let instmod := imid inst in
                  let instg := (match (TE.find instmod knowng) with
                              | None => emptyg
                              | Some tempg => tempg
                              end) in
                  let (inports, outports) := inst_inoutlist (iports inst) in
                  let instlen := (match (TE.find instmod flagmap) with
                              | None => 0
                              | Some tempg => tempg
                              end) in
                  let newg := List.fold_left (fun tempg inp => (match (TE.find inp inportsmap) with
                                                              | Some ininp => List.fold_left (fun tempg0 outp => (match (TE.find outp outportsmap) with
                                                                                                                | Some inoutp => (if (dfs_path instg instlen ininp inoutp) 
                                                                                                                  then (updg inp (cons outp (findg inp tempg0)) tempg0) else tempg0)
                                                                                                                | None => tempg0
                                                                                                                end)) outports tempg
                                                              | None => tempg
                                                              end)) inports fing in
                    (newg, var2stmt) (*TBD*)
  | Snode v e =>let preset := expr2varlist e [::] in
                if (preset == [::]) then (fing, var2stmt)
                else let newg := List.fold_left (fun tempg tempv => updg tempv (cons v (findg tempv tempg)) tempg) preset fing in
                              (newg, TE.add v st var2stmt)
  | Sfcnct e1 e2 => (match e1 with
                    | Eref v1 => let preset := expr2varlist e2 [::] in
                                if (preset == [::]) then (fing, var2stmt)
                                else (if (varIn v1 regls) then (fing, var2stmt) 
                                        else (let newg := List.fold_left (fun tempg tempv => updg tempv (cons v1 (findg tempv tempg)) tempg) preset fing in
                                              (newg, TE.add v1 st var2stmt)))
                    | _ => (fing, var2stmt)
                    end)
  | Sinvalid _ => (fing, var2stmt)
  | _ => (fing, var2stmt) (*Swhen\Sstop*)
  end.

Definition findkinstps (kpsmap : mapls) (finsti2e_outmap : mvar) (ls : seq var) (st : fstmt) : seq var :=
match st with
| Sinst inst => let mv := imid inst in
                let iv := iid inst in
                match (TE.find mv kpsmap) with
                | None => ls
                | Some kps => 
                match (TE.find iv finsti2e_outmap) with
                              | None => ls
                              | Some outmap =>
                              (let exkps := List.fold_left (fun tls p => match (TE.find p outmap) with
                                                                        | None => tls
                                                                        | Some exp => (exp :: tls)
                                                                        end) kps [::] in
                              ls ++ exkps)
                              end
                end
| _ => ls
end.
(*
Inductive result_type : Type :=
   | Some : seq var -> result_type
   | Cycle : seq var -> result_type
   | N_too_small : result_type.

Fixpoint topo_tree (vertices : seq var) (fing : g) (n : nat) (gray_nodes : seq var)
                   (root : var) (maybe_already_found: result_type) : result_type :=
match maybe_already_found with
| Cycle _ | N_too_small => maybe_already_found (* propagate earlier error *)
| Some already_found =>
if root \in gray_nodes then Cycle (root :: gray_nodes) (* error: there is a cycle *)
else if root \in already_found then maybe_already_found
else match n with
     | 0 => N_too_small (* error: n was too small *)
     | S n' => match foldr (topo_tree vertices fing n' (root :: gray_nodes)) maybe_already_found (fing root) with
               | Some result => Some (root :: result)
               | e => e (* propagate resursive error *)
               end
     end
end.

Definition topo_sort (vertices : seq var) (fing : g) : result_type :=
   foldr (topo_tree vertices fing (size vertices) [::]) (Some [::]) vertices.
*)

Fixpoint topo_tree (fing : g) (n : nat) (gray_nodes : seq var) (already_found : option (seq var)) (root : var) : option (seq var) :=
match already_found, n with
| None, _ => already_found (* propagate earlier error *)
| _, 0 => None 
| Some already_found', S n' => 
(if (root \in gray_nodes) then (Some (root :: gray_nodes)) (*None cycle *)
else if (root \in already_found') then already_found
else match (foldl (topo_tree fing n' (root :: gray_nodes)) already_found (fing root)) with
  | Some result => Some (root :: result)
  | None => None
  end)
end.

Definition topo_sort (fing : g) (n : nat) (vertices : seq var) : option (seq var) :=
foldl (topo_tree fing n [::]) (Some [::]) vertices.


(* 有module依赖关系的list: [C,B,C] C->B->A, A中有B的inst, B中有C的inst. mapg为mod name->mod graph *)

Fixpoint modname2g (modorder : seq var) (flagmap : fmap) (oldstmtsmap : mapfstmt) (instportsmap : mmvar) (finsti2e_outmap : mvar) (inpsmap : mapls) (outpsmap : mapls) (instoutl : mapls) (fingmap : mapg) (newstmtsmap : mapfstmt) (newvarmap : mapls) (kpsmap : mapls) : mapg * mapfstmt * mapls * mapls :=
  match modorder with
  | [::] => (fingmap, newstmtsmap, newvarmap, kpsmap)
  | h :: t => let tempstmts := (match (TE.find h oldstmtsmap) with
                                | Some tstmts => tstmts 
                                | None => [::]
                                end) in 
              let '(inportsmap, outportsmap) := (match (TE.find h instportsmap) with
                                | Some tempm => tempm 
                                | None => (TE.empty var, TE.empty var)
                                end) in 
              let inps := (match (TE.find h inpsmap) with
                                | Some tstmts => tstmts 
                                | None => [::]
                                end) in 
              let outps := (match (TE.find h outpsmap) with
                                | Some tstmts => tstmts 
                                | None => [::]
                                end) in 
              let instoutps := (match (TE.find h instoutl) with
                                | Some tstmts => tstmts 
                                | None => [::]
                                end) in 
              let len := (match (TE.find h flagmap) with
                                | Some n => n 
                                | None => 0
                                end) in 

              let '(regls, roots) := List.fold_left (fun '(ls1, ls2) tst => findreg ls1 ls2 tst) tempstmts ([::], [::]) in
              let kinstps := List.fold_left (fun ls tst => findkinstps kpsmap finsti2e_outmap ls tst) tempstmts [::] in
              
              let '(newg, var2stmt) := List.fold_left (fun '(tempg, tempm) tempst => buildg regls flagmap inportsmap outportsmap fingmap tempg tempm tempst) tempstmts (emptyg, TE.empty fstmt) in
              let kps := (match (topo_sort newg len roots) with
              | None => [::]
              | Some tseq => List.fold_left (fun ls op => if (varIn op tseq) then (op :: ls) else ls) outps [::]
              end) in
              
              let allvar := List.fold_left (fun ls tst => findallvar ls tst) tempstmts [::] in
              (* 起点 : fcnct到常数、reg、node到常数、所有input、invalid 、inst中的reg、const*)
              match (topo_sort newg len (inps ++ roots ++ kinstps)(*allvar*)) with
              | None => (TE.add h newg fingmap, TE.add h [::] newstmtsmap, TE.add h [::] newvarmap, TE.add h [::] kpsmap)
              | Some tseq => let newvarorder := tseq in
              
(*match (topo_sort allvar newg) with
| Cycle cycleseq => (TE.add h newg fingmap, TE.add h [::] newstmtsmap, TE.add h cycleseq newvarmap, TE.add h kps kpsmap)
| N_too_small => (TE.add h newg fingmap, TE.add h [::] newstmtsmap, TE.add h [::] newvarmap, TE.add h [::] kpsmap)
| Some tseq => let newvarorder := tseq in*)

              let newstorder := List.map (fun tv => match (TE.find tv var2stmt) with 
                                                    | None => if varIn tv instoutps then Sfcnct (Eref tv) (Eref tv)
                                                    else sskip
                                                    | Some tempst => tempst
                                                    end) newvarorder in
              (*let newg0 := List.fold_left (fun tempg tempst => add_regedge regls tempg tempst) tempstmts newg in*)
              
              let '(fingmap0, newstmtsmap0, newvarmap0, kpsmap0) := (TE.add h newg fingmap, TE.add h newstorder newstmtsmap, TE.add h newvarorder newvarmap, TE.add h kps kpsmap) in
              modname2g t flagmap oldstmtsmap instportsmap finsti2e_outmap inpsmap outpsmap instoutl fingmap0 newstmtsmap0 newvarmap0 kpsmap0 
              end
  end.

Definition reorder (modorder : seq var) (flagmap : fmap) (oldstmtsmap : mapfstmt) (instportsmap : mmvar) (finsti2e_outmap : mvar) (inpsmap : mapls) (outpsmap : mapls) (instoutl : mapls) : mapfstmt * mapls :=
  let '(defmap, knownmap, regstmtmap) := List.fold_left (fun '(tempm0, tempm1, tempm2) modname => let tempstmts := (match (TE.find modname oldstmtsmap) with
                                                        | None => [::]
                                                        | Some tstmts => tstmts 
                                                        end) in 
                                                        let '(newdefls, newknown, newreg) := known_reg_orders tempstmts in
                                                        (TE.add modname newdefls tempm0, TE.add modname newknown tempm1, TE.add modname newreg tempm2)) modorder (TE.empty (seq fstmt),TE.empty (seq fstmt), TE.empty (seq fstmt)) in
  let '(a, orderedmap, varmap, b) := modname2g modorder flagmap oldstmtsmap instportsmap finsti2e_outmap inpsmap outpsmap instoutl (TE.empty g) (TE.empty (seq fstmt)) (TE.empty (seq var)) (TE.empty (seq var)) in
  let newstmtsmap := List.fold_left (fun tmap modname => match (TE.find modname defmap) with
                                                        | None => tmap 
                                                        | Some tdefs => match (TE.find modname regstmtmap) with
                                                        | None => tmap 
                                                        | Some tregs => match (TE.find modname orderedmap) with
                                                                        | None => tmap
                                                                        | Some tordered => match (TE.find modname knownmap) with
                                                                                          | None => tmap
                                                                                          | Some tknown => let allordered := tdefs ++ (tknown ++ (tordered ++ tregs)) in TE.add modname (rev allordered) tmap
                                                                                          end
                                                                        end
                                                        end
                                                        end) modorder (TE.empty (seq fstmt)) in
  (newstmtsmap, varmap)
  .

Definition run_module (modorder : seq var) (flagmap : fmap) (newinstportsmap : mmvar) (finsti2e_outmap : mvar) (mainmod : var) rs s te (io_in : mapioin) name ols readerls writerls data2etc memmap clk_num len 
  (finstoutl : mapls) (finstoutm : mmaptuple) (ffmodsmap : mapfstmt) (fterss : mapterss) (fread_la : allboolmap) (finstin : mapls) (finstout : mapls) (finstportmap : mmapvar) iternum : vstate * vstate * mapmem * mapterss * mapioin :=
  let '(newffmodsmap, varmap) := reorder modorder flagmap ffmodsmap newinstportsmap finsti2e_outmap finstin finstout finstoutl in
  run_module0 mainmod rs s te io_in name ols readerls writerls data2etc memmap clk_num len finstoutl finstoutm newffmodsmap fterss fread_la finstin finstportmap iternum.
    
(*
    Import Natlist0.
    Local Open Scope natlist0.
  
    (*
  Fixpoint clk_steps st rs s te io_in name clk_num : vstate :=
    match clk_num with
    | 0 => snd (eval_fstmts st rs s te)
    | S m => snd (eval_fstmts st rs (upd_argulist (clk_steps st rs s te io_in name m) io_in name m) te)
    end.
    *)
  
  (* XM : tail recursive version *)
  Fixpoint clk_steps_tail_rec_aux st rs s te io_in name clk_num len:=
    match clk_num with
    | 0 => s(*let s1 := upd_argulist s io_in name len in
           let te1 := upd_typenv_fstmts st te s1 in
           let (rs2, s2) := eval_fstmts st rs s1 te in s2*)
    | S m => let n := len - S m in
             let s1 := upd_argulist s io_in name n in
             (*let te1 := upd_typenv_fstmts st te s1 in*)
             let (rs2, s2) := eval_fstmts st rs s1 te in
             clk_steps_tail_rec_aux st rs2 s2 te io_in name m len
    end.
  
  Definition clk_steps_tail_rec st rs s te ios nms nclk := clk_steps_tail_rec_aux st rs s te ios nms nclk nclk.
  
  Definition run_tail_rec mainmod s rs te io_in name clk_num len readerls writerls data2etc memmap :=
    match clk_num with
    | 0 => SV.empty
    | S m => let n := len - S m in
             let (rs1, s1) := eval_module mainmod s rs te (*modsmap*) io_in n name readerls writerls data2etc memmap in
             run_tail_rec mainmod s1 rs1 te io_in name clk_num len readerls writerls data2etc memmap
    end.

  (********************************************************************************)

  (* Parallel evaluation *)

  (* Expression evaluation, fexpr -> fexpr *)
  (* Fixpoint eval_fexpr' (e : fexpr) (s : estate) : fexpr := *)
  (*   match e with *)
  (*   | Econst t c => econst t c *)
  (*   | Eref v => (ES.acc v s) (*TODO*) *)
  (*   | Eprim_binop b e1 e2 => *)
  (*     let ve1 := (eval_fexpr' e1 s) in *)
  (*     let ve2 := (eval_fexpr' e2 s) in *)
  (*     Eprim_binop b ve1 ve2 *)
  (*   | Eprim_unop u e => *)
  (*     Eprim_unop u (eval_fexpr' e s) *)
  (*   | _ => e (*TODO*) *)
  (*   end.· *)


(*     Definition store_fstmt (st : fstmt) (s : estate) (te : TE.env) : estate := *)
(*       match st with *)
(*       | Sskip => s *)
(*       | Swire v t => s *)
(*       | Sreg r => EV.upd (rid r) (Eref (rid r)) s *)
(*       | Smem m => s *)
(*       | Sinst v1 v2 => EV.upd v1 (Eref v2) s *)
(*       | Snode v e => EV.upd v e s *)
(*       | Sfcnct (Eref v) e2 => EV.upd v e2 s *)
(*       | Sinvalid v => s *)
(*       | _ => s *)
(*       end. *)

(*   Fixpoint store_fstmts st e te : estate := *)
(*     match st with *)
(*     | [::] => e *)
(*     | h :: tl => *)
(*       (*let te1 := upd_typenv_fstmt h te s in 更新type怎么做？*) *)
(*       let e1 := store_fstmt h e te in *)
(*       store_fstmts tl e1 te *)
(*     end. *)

(*   (* vstate * vstate -> estate -> vstate * vstate *) *)
(*   (* e = store_fstmts st e0 te *) *)
(*   Fixpoint eval_store rs s e te : vstate * vstate := *)
(*     (*遍历estate s 来evaluate，存入两个vstate*) *)
(* . *)

  (* Definition eval_fport (p : fport) (s : vstate) : vstate := *)
  (*   match p with *)
  (*   | Finput v t => SV.upd v [::] s *)
  (*   | Foutput v t => SV.upd v [::] s *)
  (*   end.   *)
  (* Fixpoint eval_fports (ps : seq fport) (s : vstate) : vstate := *)
  (*   match ps with *)
  (*   | [::] => s *)
  (*   | h :: tl => eval_fports tl (eval_fport h s) *)
  (*   end. *)

  
  Definition eval_fport_init (p : fport) (s : vstate) : vstate :=
    match p with
    | Finput v t => if SV.acc v s == [::] then SV.upd v (from_Z (sizeof_fgtyp t) 0) s else s
    | Foutput v t => if SV.acc v s == [::] then SV.upd v (from_Z (sizeof_fgtyp t) 0) s else s
    end.

  Fixpoint eval_fports_init (ps : seq fport) (s : vstate) : vstate :=
    match ps with
    | [::] => s
    | h :: tl => eval_fports_init tl (eval_fport_init h s)
    end.

  Fixpoint eval_fmodule (m : fmodule) (s : vstate) (te : TE.env) : vstate :=
    match m with
    | FInmod v ps st => let (_, s) := eval_fstmts st (SV.empty) ((eval_fports_init ps s)) te in s
    | _ => s
    end.

  Definition upd_typenv_fmodule (m : fmodule) (te : TE.env) (s : vstate) : TE.env :=
    match m with
    | FInmod v ps ss => upd_typenv_fstmts ss (upd_typenv_fports ps te) s
    | _ => te
    end.
  
  (* fexpr eqn , TBD *)

  (* Well-typed *)

  (* well typed expr *)
  
  Fixpoint well_typed_fexpr (e : fexpr) (te : TE.env) : bool :=
    match e with
    | Econst t c => (sizeof_fgtyp t) == (size c)
    | Eref v => 0 < sizeof_fgtyp (TE.vtyp v te)
    (* | Edeclare v t => 0 < sizeof_fgtyp t *)
    | Ecast _ _ => true
    | Eprim_unop _ e1 => well_typed_fexpr e1 te
    | Eprim_binop _ e1 e2 => (well_typed_fexpr e1 te) && (well_typed_fexpr e2 te)
    | Emux c e1 e2 => (well_typed_fexpr c te) && (well_typed_fexpr e1 te) && (well_typed_fexpr e2 te)
    | Evalidif c e1 => (well_typed_fexpr c te) && (well_typed_fexpr e1 te)
    end.

  Definition well_typed_fstmt (s : fstmt) (te : TE.env) : bool :=
    match s with
    | Sskip => true
    | Swire v t => 0 < sizeof_fgtyp t
    | Sreg r => (0 < sizeof_fgtyp (type r)) &&
                (match (reset r) with
                 | NRst => true
                 | Rst e1 e2 => (well_typed_fexpr e1 te) && (well_typed_fexpr e2 te)
                 end)
    | Snode v e => well_typed_fexpr e te
    | Sfcnct (Eref v) e => (0 < sizeof_fgtyp (TE.vtyp v te)) && well_typed_fexpr e te
    | _ => true
    end.

  (* Well-formness, is defined && well-typed *)
  
  (* Use TE.mem v te to determine if v is defined *)
  Definition is_defined (v : var) (te : TE.env) : bool :=
    TE.mem v te.

  Fixpoint is_defined_fexpr (e : fexpr) (te : TE.env) : bool :=
    match e with
    | Econst _ _ => true
    | Eref v => is_defined v te
    (* | Edeclare v t => true *)
    | Ecast _ e1 => is_defined_fexpr e1 te
    | Eprim_unop _ e1 => is_defined_fexpr e1 te
    | Eprim_binop _ e1 e2 => (is_defined_fexpr e1 te) && (is_defined_fexpr e2 te)
    | Emux c e1 e2 => (is_defined_fexpr c te) && (is_defined_fexpr e1 te) && (is_defined_fexpr e2 te)
    | Evalidif c e1 => (is_defined_fexpr c te) && (is_defined_fexpr e1 te)
    end.

  Definition is_defined_fstmt (s : fstmt) (te : TE.env) : bool :=
    match s with
    | Sskip => true
    | Swire v t => true
    | Sreg r => is_defined (rid r) te
    | Snode v e => is_defined_fexpr e te
    | Sfcnct (Eref v) e => is_defined v te && is_defined_fexpr e te
    | _ => true
    end.



  
  (************************************************************)
  
  
  (* well formed expression *)
  Definition well_formed_fexpr e te := well_typed_fexpr e te && is_defined_fexpr e te.
  (* well formed statement *)
  Definition well_formed_fstmt s te := well_typed_fstmt s te && is_defined_fstmt s te.

  (* conform lemmas *)
  Lemma conform_eval_swire_upd_env rs1 s1 rs2 s2 te v t :
    SV.conform s1 te ->
    well_formed_fstmt (Swire v t) te ->
    eval_fstmt (Swire v t) rs1 s1 te = (rs2, s2) ->
    SV.conform s2 (upd_typenv_fstmt (Swire v t) te s1).
  Proof.
    rewrite /= => Hcf1 Hwf.
    case => [Hrs Hs]. rewrite <- Hs.
    apply SV.conform_Upd with (zeros (sizeof_fgtyp t)) s1.
    rewrite size_zeros//.
    apply SV.Upd_upd.
    done.
  Qed.

  Lemma conform_eval_node_upd_env rs1 s1 rs2 s2 te v e :
    SV.conform s1 te ->
    well_formed_fstmt (Snode v e) te ->
    eval_fstmt (Snode v e) rs1 s1 te = (rs2, s2) ->
    SV.conform s2 (upd_typenv_fstmt (Snode v e) te s1).
  Proof.
    rewrite /= => Hcf Hwf.
    case => [Hrs Hs]. rewrite <- Hs.
    apply SV.conform_Upd with (eval_fexpr e s1 te) s1;
    [ |apply SV.Upd_upd | ].
    move : Hwf.
    case e; try by done.
    - (* case const *)
      move => v1.
      rewrite /well_formed_fstmt/= /is_defined.
      move => b /andP[/eqP H _]; done.
    - (* case ref *)
      move => v1.
      rewrite /well_formed_fstmt/= /is_defined.
      move/andP => [Hszv1 Hmv1].
      rewrite -(SV.conform_mem Hcf)//.
      rewrite (TE.vtyp_vsize (eqP(eqxx (TE.vtyp v1 te))))//.
    (* - (* case edeclare *) *)
    (*   move => v1 t1. *)
    (*   rewrite /well_formed_fstmt/= andbT size_zeros//. *)
    - (* case ecast *)
      move => u e1.
      rewrite /well_formed_fstmt.
      case u. admit. admit. admit.
    - (* case eunop *)  
      admit.
    - (* case ecast *)
      admit.
    - (* case emux *)
      admit.
    - (* case evalidif *)
      admit.
      (* upd env expr e *)
      admit.
  Admitted.
  *)
End MakeFirrtl.
 
Module LoFirrtl := MakeFirrtl VarOrder (*VS VM*) TE Store (*EStore*).

(*
Definition init_vm := VM.empty.
Definition init_vs := VS.empty.
Definition init_env : TE.env := TE.empty fgtyp.
Definition init_store := Store.empty.

Section clksExamples.
  
  Import LoFirrtl.
  Import Natlist0.
  Local Open Scope natlist0.

  (*Eval compute in (from_nat 1 1).
Eval compute in (from_nat 1 0).
Eval compute in (from_nat 2 3).

  (*clk rst in*)
  Definition l_in := [:: (cons (from_nat 1 0) (cons (from_nat 1 0)(cons (from_nat 1 0) nil))); (cons (from_nat 1 0) (cons (from_nat 1 0)(cons (from_nat 1 0) nil)))].
  (*Definition l_in  := [:: [:: (from_nat 1 0)(from_nat 1 0)(from_nat 1 1)]; [:: (from_nat 1 0)(from_nat 1 0)(from_nat 1 0)]; [:: (from_nat 1 0)(from_nat 1 0)(from_nat 1 1)]; [:: (from_nat 1 0)(from_nat 1 0)(from_nat 1 1)]].*)
  Eval compute in l_in.
  Eval compute in (lastd l_in).

  Eval compute in (cons (from_nat 1 0) (cons (from_nat 1 0)(cons (from_nat 1 0) nil))).
  Eval compute in lastd (cons (from_nat 1 0) (cons (from_nat 1 0)(cons (from_nat 1 0) nil))).

  Require Export Coq.Strings.String.
Definition total_map (A : Type) := string -> A.
Definition eqb_string (x y : string) : bool :=
  if string_dec x y then true else false.
Definition t_update {A : Type} (m : total_map A) (x : string) (v : A) :=
  fun x' => if eqb_string x x' then v else m x'.
Definition t_empty {A : Type} (v : A) : total_map A :=
  (fun _ => v).

Notation "'_' '!->' v" := (t_empty v)
  (at level 100, right associativity).
Notation "x '!->' v ';' m" := (t_update m x v)
                              (at level 100, v at next level, right associativity).

Definition examplemap' :=
  ( "bar" !-> true;
    "foo" !-> true;
    _ !-> false
  ).
   Eval compute in (examplemap' "bar").
   *)

  Definition st0 := Store.empty.
  Definition rs0 := Store.empty.
  Definition te0 := TE.empty fgtyp. 
  Definition Accumulator := VarOrder.default. 
  Definition accumulator := VarOrder.succ Accumulator.
  Definition io_out := VarOrder.succ accumulator.
  Definition io_in0 := VarOrder.succ io_out.
  Definition _T_11 := VarOrder.succ io_in0.
  Definition _T_12 := VarOrder.succ _T_11.
  Definition clk := VarOrder.succ _T_12.
  Definition rst1 := VarOrder.succ clk.

   
  Definition fpts_64 := [::(Finput clk Fclock);
                     (Finput rst1 (Fuint 1));
                     (Finput io_in0 (Fsint 64));
                     (Foutput io_out (Fuint 64))].
  Definition te1_64 := upd_typenv_fports fpts_64 te0. 
  Definition st1_64 := Store.upd clk [::b0] (Store.upd rst1 [::b0] (Store.upd io_in0 (from_Z 64 0) (Store.upd io_out (from_nat 64 0) st0))).
  Definition rs1_64 := (Store.upd accumulator (from_nat 9 0) rs0).
  Compute (st1_64).
  Definition fst1_64 := sreg (mk_freg accumulator (Fuint 8) (eref clk)
                                   (rrst (econst (Fuint 1) [::b0]) (eref accumulator))).
  Definition te2_64 := upd_typenv_fstmt fst1_64 te1_64 st1_64.
  Definition st2_64 := eval_fstmt fst1_64 rs0 st1_64 te0.
  Compute (Store.acc accumulator (fst st2_64)).
  
  Definition fpts := [::(Finput clk Fclock);
                     (Finput rst1 (Fuint 1));
                     (Finput io_in0 (Fsint 2));
                     (Foutput io_out (Fsint 8))].
  Definition te1 := upd_typenv_fports fpts te0. 
  Definition st1 := Store.upd clk [::b0] (Store.upd rst1 [::b0] (Store.upd io_in0 (from_Z 2 (-1)) (Store.upd io_out (from_nat 8 0) st0))).
  Definition rs1 := (Store.upd accumulator (from_nat 9 0) rs0).
  Definition fst1 := sreg (mk_freg accumulator (Fsint 8) (eref clk)
                                   (rrst (econst (Fuint 1) [::b0]) (eref accumulator))).
  Definition te2 := upd_typenv_fstmt fst1 te1 st1.
  Definition st2 := eval_fstmt fst1 rs0 st1 te0.

  Definition fst2 := (snode _T_11 (eprim_binop Badd (eref accumulator) (eref io_in0))).
  Definition te3 := let (rs2, sst2) := st2 in upd_typenv_fstmt fst2 te2 sst2.
  Definition st3 := let (rs2, sst2) := st2 in eval_fstmt fst2 rs2 sst2 te3.

  Definition fst3 := (Snode _T_12 (Ecast AsSInt (Eprim_unop (Utail 1) (Eref _T_11)))).
  Definition te4 := let (rs3, sst3) := st3 in upd_typenv_fstmt fst3 te3 sst3.
  Definition st4 := let (rs3, sst3) := st3 in eval_fstmt fst3 rs3 sst3 te4.

  Definition fst4 := (sfcnct (Eref io_out ) (Eref accumulator)).
  Definition te5 := let (rs4, sst4) := st4 in upd_typenv_fstmt fst4 te4 sst4.
  Definition st5 := let (rs4, sst4) := st4 in eval_fstmt fst4 rs4 sst4 te5.

  Definition fst5 := (Sfcnct (Eref accumulator) (Emux (Eref rst1) (econst (Fuint 8) (from_nat 8 0)) (Eref _T_12))).
  Definition te6 := let (rs5, sst5) := st5 in upd_typenv_fstmt fst5 te5 sst5.
  Definition st6 := let (rs5, sst5) := st5 in eval_fstmt fst5 rs5 sst5 te6.

  Definition fst6 := sskip.
  Definition te7 := let (rs6, sst6) := st6 in upd_typenv_fstmt fst6 te6 sst6.
  Definition st7 := let (rs6, sst6) := st6 in eval_fstmt fst6 rs6 sst6 te7.
  
Definition exampleinp :=
  ( rst1 !-> [1;1;1;0;0;1;0];
    io_in0 !-> [1;1;1;1;1;1;1];
    _ !-> nil
  ).

  Eval compute in exampleinp rst1.
  Eval compute in nth_bad (exampleinp rst1) 2.

Compute (Store.acc accumulator (clk_steps_tail_rec [::fst1;fst2;fst3;fst4;fst5;fst6] rs1 st0 te1 exampleinp [:: rst1; io_in0] 5)).
Compute (Store.acc accumulator (fst (eval_fstmts [::fst1;fst2;fst3;fst4;fst5;fst6] rs0 st1 te1))).
 
End clksExamples.


Section Examples.
  Import LoFirrtl.
  
  (* Variable Accumulator : var. *)
  (* Variable accumulator : var. *)
  (* Variable io_out : var. *)
  (* Variable io_in : var. *)
  (* Variable _T_11 : var. *)
  (* Variable _T_12 : var. *)
  (* Variable clk : var. *)
  (* Variable rst1 : var. *)
  Definition st0 := Store.empty.
  Definition te0 := TE.empty fgtyp. 
  Definition Accumulator := VarOrder.default. 
  Definition accumulator := VarOrder.succ Accumulator.
  Definition io_out := VarOrder.succ accumulator.
  Definition io_in := VarOrder.succ io_out.
  Definition _T_11 := VarOrder.succ io_in.
  Definition _T_12 := VarOrder.succ _T_11.
  Definition clk := VarOrder.succ _T_12.
  Definition rst1 := VarOrder.succ clk.
  
  Definition fpts := [::(Finput clk Fclock);
                     (Finput rst1 (Fuint 1));
                     (Finput io_in (Fuint 1));
                     (Foutput io_out (Fuint 8))].
  Definition te1 := upd_typenv_fports fpts te0. 
  Definition st1 := Store.upd clk [::b0] (Store.upd rst1 [::b1] (Store.upd io_in [::b1] (Store.upd io_out (from_nat 8 0) st0))).
  Definition fst1 := sreg (mk_freg accumulator (Fuint 8) (eref clk)
                                   (rrst (econst (Fuint 1) [::b0]) (eref accumulator))).
  Definition te2 := upd_typenv_fstmt fst1 te1 st1.
  Definition st2 := eval_fstmt fst1 st1 te2.
  Eval compute in (Store.acc accumulator st2).
  Eval compute in (TE.vtyp accumulator te2).
  Definition fst2 := (snode _T_11 (eprim_binop Badd (eref accumulator) (eref io_in))).
  Definition te3 := upd_typenv_fstmt fst2 te2 st2.
  Definition st3 := eval_fstmt fst2 st2 te3.
  Eval compute in (Store.acc _T_11 st3).
  Eval compute in (TE.vtyp _T_11 te3).
  Definition fst3 := (Snode _T_12 (Eprim_unop (Utail 1) (Eref _T_11))).
  Definition te4 := upd_typenv_fstmt fst3 te3 st3.
  Definition st4 := eval_fstmt fst3 st3 te4.
  Eval compute in (Store.acc _T_12 st4).
  Eval compute in (TE.vtyp _T_12 te4).
  Definition fst4 := (Sfcnct (Eref io_out ) (Eref accumulator)).
  Definition te5 := upd_typenv_fstmt fst4 te4 st4.
  Definition st5 := eval_fstmt fst4 st4 te5.
  Eval compute in (Store.acc io_out st5).
  Eval compute in (TE.vtyp io_out te5).
  Definition fst5 := (Sfcnct (Eref accumulator) (Emux (Eref rst1) (Econst _ (Fuint 1) [::b0]) (Eref _T_12))).
  Definition te6 := upd_typenv_fstmt fst5 te5 st5.
  Definition st6 := eval_fstmt fst5 st5 te6.
  Eval compute in (Store.acc accumulator st6).
  Eval compute in (TE.vtyp accumulator te6).
  Definition fst6 := sskip.
  Definition te7 := upd_typenv_fstmt fst6 te6 st6.
  Definition st7 := eval_fstmt fst6 st6 te7.
  Eval compute in (Store.acc accumulator st7).

  Definition fm1 :=(FInmod Accumulator
                      [::(Finput clk Fclock);
                      (Finput rst1 (Fuint 1));
                      (Finput io_in (Fuint 1));
                      (Foutput io_out (Fuint 8))]
                      [::sreg (mk_freg accumulator (Fuint 8) (eref clk)
                                                 (rrst (econst (Fuint 1) [::b0]) (eref accumulator)));
                      (snode _T_11 (eprim_binop Badd (eref accumulator) (eref io_in)));
                      (snode _T_12 (eprim_unop (Utail 1) (eref _T_11)));
                      (sfcnct (eref io_out ) (eref accumulator));
                      (sfcnct (eref accumulator) (emux (eref rst1) (econst (Fuint 1) [::b0]) (eref _T_12)));
                      sskip
                      ]
              
                   ).
  Definition eval_fm1 := Store.acc accumulator (run_fmodule fm1 st1 te1 10).
  Compute (Store.acc accumulator (run_fstmts [::fst1;fst2;fst3;fst4;fst5;fst6] st1 te1 10)).
  Compute (Store.acc accumulator (run_fmodule fm1 st1 te1 10)).


End Examples.
*)
