From Coq Require Import FunInd FMaps FMapAVL OrderedType ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat ssrint eqtype seq.
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
        clk : var
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

Module Natlist0. 
Delimit Scope natlist_scope with natlist0.

Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..) (x at level 10, right associativity) : natlist0.
Fixpoint nth_bad (l:natlist) (n:nat) : nat :=
  match l with
  | nil => 42
  | cons a l' => match n with
               | 0 => a
               | S n' => nth_bad l' n'
               end
  end.

Local Open Scope natlist0.

Eval compute in nth_bad [1;2;3] 2.

Definition in_map := N -> natlist.

Definition eqb_N (x y : N) : bool :=
  if x==y then true else false.
Definition t_update (m : in_map) (x : N) (v : natlist) :=
  fun x' => if eqb_N x x' then v else m x'.
Definition t_empty (v : natlist) : in_map :=
  (fun _ => v).

Notation "'_' '!->' v" := (t_empty v)
  (at level 100, right associativity) : natlist0.
Notation "x '!->' v ';' m" := (t_update m x v)
                              (at level 100, v at next level, right associativity) : natlist0.

End Natlist0.

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
  (* Definition edeclare v t := @Edeclare V.T v t. *)
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
  Definition fport := @fport V.T.
  Definition mk_finst := @mk_finst V.T.
  Definition fmodule := @fmodule V.T.
  Definition fcircuit := @fcircuit V.T.
  
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
    | Blt => fun b1 b2 => [::ltB b1 b2]
    | Bleq => fun b1 b2 => [::leB b1 b2]
    | Bgt => fun b1 b2 => [::gtB b1 b2]
    | Bgeq => fun b1 b2 => [::geB b1 b2]
    | Beq => fun b1 b2 => let bs1 := zext ((maxn (size b1) (size b2)) - (size b1)) b1 in
                          let bs2 := zext ((maxn (size b1) (size b2)) - (size b2)) b2 in
    [::bs1 == bs2]
    | Bneq => fun b1 b2 => let bs1 := zext ((maxn (size b1) (size b2)) - (size b1)) b1 in
                           let bs2 := zext ((maxn (size b1) (size b2)) - (size b2)) b2 in
    [::(~~ (bs1 == bs2))]
    end.
  
  Definition binop_sbcmp (o : bcmp) : bits -> bits -> bits :=
    match o with
    | Blt => fun b1 b2 => [::sltB b1 b2]
    | Bleq => fun b1 b2 => [::sleB b1 b2]
    | Bgt => fun b1 b2 => [::sgtB b1 b2]
    | Bgeq => fun b1 b2 => [::sgeB b1 b2]
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

  Compute (low (size ([::b1;b1;b1;b1]) -1) [::b1;b1;b1;b1]).

  Lemma size_full_adder_ext c bs1 bs2 : size (snd (full_adder_ext c bs1 bs2)) = maxn (size bs1) (size bs2).
  Proof.
    rewrite /full_adder_ext.
    dcase (extzip0 bs1 bs2) => [zp Hzp].
    rewrite -(size_extzip b0 b0 bs1 bs2) -/extzip0 Hzp.
    elim : zp bs1 bs2 Hzp c => [|zh zt IH] bs1 bs2 Hzp c //.
    dcase zh => [[hd1 hd2] Hz]. rewrite Hz in Hzp => {Hz zh}.
    dcase (bool_adder c hd1 hd2) => [[c0 hd] Hadder].
    dcase (full_adder_zip c0 zt) => [[c1 tl] Hfull]. move: Hzp.
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
    rewrite /adcB_ext size_full_adder_ext//.
  Qed.

  Lemma size_addB_ext bs1 bs2 : size (addB_ext bs1 bs2) = (maxn (size bs1) (size bs2)).+1.
  Proof.
    rewrite /addB_ext. case Hadc : (adcB_ext false bs1 bs2) => [c r].
    rewrite /=-size_adcB_ext Hadc size_rcons//.
  Qed.

  Lemma to_Zpos_addB_ext bs1 bs2 :
    to_Zpos (addB_ext bs1 bs2) = Z.add (to_Zpos bs1) (to_Zpos bs2).
  Proof.
  Admitted.
    
  (* subtraction with extended bits *)
  Definition sbbB_ext b bs1 bs2 : bool * bits := adcB_ext (~~ b) bs1 (~~# bs2).
  Definition subB_ext bs1 bs2 := let (b, r) := (sbbB_ext false bs1 bs2) in rcons r b.

  Lemma size_subB_ext bs1 bs2 : size (subB_ext bs1 bs2) = (maxn (size bs1) (size bs2))+1.
  Proof. Admitted.

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

  (*Compute (sext 2 [::b1;b0]).
  Compute (joinlsb false(addB (zeros ((size [::b1;b0])+1)) (addB (invB (sext (size [::b1]) [::b1;b0])) (zext (size [::b1;b0]) [::b1])))).*)
  Compute (Sfull_mul [::b1;b1] [::b0;b1]).
  
  Definition ebinop_op (o : ebinop) (t1 t2 : fgtyp) : bits -> bits -> bits :=
    match t1, t2 with
    | Fuint w1, Fuint w2 =>
      fun a b =>
        let w := max w1 w2 in
        let ea := zext (w-w1) a in
        let eb := zext (w-w2) b in
      match o with
      | Badd => addB_ext a b
      | Bsub => subB_ext a b
      | Bdiv => udivB' a b
      | Brem => low (minn w1 w2) (uremB a b)
      (* | Bsdiv => sdivB *)
      (* | Bsrem => sremB *)
      | Bmul => full_mul a b
      | Bcomp c => binop_bcmp c a b
      | Band => andB ea eb
      | Bor => orB ea eb
      | Bxor => xorB ea eb
      | Bcat => cat b a
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
      | Bcat => cat b a
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
    (* | Edeclare v t => t *)
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
                             | _ => type_of_fexpr e1 te
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
    end.*)
  Compute (List.In b1 [::b0;b1]).
  (* Expression evaluation, value *)

Definition memory_map := bits -> bits.
Definition memfind (key : bits) (map : memory_map) : bits := map key.
Definition memupd (key : bits) (v : bits) (memmap : memory_map) : memory_map :=
  fun (y : bits) => if y == key then v else memfind y memmap.
Definition memempty : memory_map := (fun _ => [::b0]).

Definition mapls := TE.t (seq var).
Definition mapioin := TE.t (seq bits).
Definition mapdata2etc := TE.t (var * var * var * var).
Definition map2etc := TE.t (mapdata2etc).
Definition mapmem := TE.t memory_map. 
Definition mapmodsmem := TE.t mapmem.
Fixpoint mylListIn (a:var) (l:list var) : bool :=
    match l with
      | nil => b0
      | b :: m => if b == a then b1 else (mylListIn a m)
    end.

Definition maptuple := TE.t (var * var).
Definition mmaptuple := TE.t maptuple.
Definition mapfmod := TE.t fmodule.
Definition mapterss := TE.t (TE.env * vstate * vstate).
Definition mapvar := TE.t var.
Definition mmapvar := TE.t mapvar.

Fixpoint bitsIn (a: bits) (l:list bits) : bool :=
    match l with
      | nil => b0
      | b :: m => if ((to_nat b) == (to_nat a)) then b1 else (bitsIn a m)
    end.

Fixpoint upd_inner s s0 (a2 : seq var) (finstinmap : mapvar) : vstate :=
    match a2 with
     | [:: ] => s0
     | h::t => let s1 := match TE.find h finstinmap with
                          | None => s0
                          | Some a => SV.upd h (SV.acc a s) s0
                          end in
     upd_inner s s1 t finstinmap
    end.

  Fixpoint eval_fexpr (e : fexpr) (s : vstate) (te : TE.env) (readerls : seq var) (writerls : seq var) (data2etc : mapdata2etc) (memmap : mapmem) : bits :=
    match e with
    | Econst t c => c
    | Eref v => (* SV.acc v s
    have map data2addr、data2en、data2mask、data2mid
    have list reader.data、writer.data
    have memmap mid->emptymap(addr value -> data value)*)
    if mylListIn v readerls (* reader ports *)
    then (match TE.find v data2etc with
        | None => [::b0]
        | Some a => (let '(addrvar, envar, midvar, ruw) := a in 
          let addrval := SV.acc addrvar s in
          let enval := SV.acc envar s in
          if enval == [:: b0]
            then [::b1]
          else
          (let writeraddr := List.fold_left (fun l w => List.cons (
                            match TE.find w data2etc with
                            | None => [::b0]
                            | Some a0 => let '(addrvar0, _, _, _) := a0 in SV.acc addrvar0 s
                            end
          ) l) writerls nil in
          (*if bitsIn addrval writeraddr
          then [::b1]
          else*)
          (match TE.find midvar memmap with
          | None => [::b0]
          | Some b => memfind addrval b
          end))
    ) end)
    else SV.acc v s (* inst ports & others *)
    | Eprim_binop b e1 e2 =>
      let ve1 := (eval_fexpr e1 s te readerls writerls data2etc memmap) in
      let ve2 := (eval_fexpr e2 s te readerls writerls data2etc memmap) in
      let te1 := type_of_fexpr e1 te in
      let te2 := type_of_fexpr e2 te in
      (ebinop_op b te1 te2) ve1 ve2
    | Eprim_unop u e =>
      let t := type_of_fexpr e te in
      (eunop_op u t) (eval_fexpr e s te readerls writerls data2etc memmap)
    | Emux c e1 e2 =>
      let t1 := (type_of_fexpr e1 te) in
      let t2 := (type_of_fexpr e2 te) in
      match t1, t2 with
      | Fuint w1, Fuint w2 => if ~~ (is_zero (eval_fexpr c s te readerls writerls data2etc memmap)) 
      then (zext ((max w1 w2) - w1) (eval_fexpr e1 s te readerls writerls data2etc memmap)) else(zext ((max w1 w2) - w2) (eval_fexpr e2 s te readerls writerls data2etc memmap))
      | Fsint w1, Fsint w2 => if ~~ (is_zero (eval_fexpr c s te readerls writerls data2etc memmap)) 
      then (sext ((max w1 w2) - w1) (eval_fexpr e1 s te readerls writerls data2etc memmap)) else(sext ((max w1 w2) - w2) (eval_fexpr e2 s te readerls writerls data2etc memmap))
      | _, _ => [::]
      end       
    | Evalidif c e => if ~~ (is_zero (eval_fexpr c s te readerls writerls data2etc memmap)) then (eval_fexpr e s te readerls writerls data2etc memmap) else [::]
    (* | Edeclare v t => zeros (sizeof_fgtyp t) *)
    | Ecast AsUInt e => eval_fexpr e s te readerls writerls data2etc memmap
    | Ecast AsSInt e => eval_fexpr e s te readerls writerls data2etc memmap
    | Ecast AsClock e => [::lsb (eval_fexpr e s te readerls writerls data2etc memmap)]
    | Ecast AsReset e => [::lsb (eval_fexpr e s te readerls writerls data2etc memmap)]
    | Ecast AsAsync e => [::lsb (eval_fexpr e s te readerls writerls data2etc memmap)]
    end.
  


  (*Compute (from_Z 6 (-3)). (*[:: true; false; true; true; true; true] *)
  Compute (from_Z 11 (-56)). (*[:: false; false; false; true; false; false; true; true; true; true; true]*)
  Compute (ebinop_op Badd (Fsint 6) (Fsint 11) [:: true; false; true; true; true; true] [:: false; false; false; true; false; false; true; true; true; true; true]).
  Compute (ebinop_op Badd (Fsint 4) (Fsint 4) [:: true;true;true;true] [:: false; true; true; false]).
  Compute (eunop_op (Ucvt) (Fuint 6) [:: true; false; true; true; true; true]).*)
  
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
    (* | Snode v e => TE.add v (type_of_fexpr e (upd_typenv_fexpr e te)) (upd_typenv_fexpr e te) *)
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
    | _ => te

    end.

  Fixpoint upd_typenv_fstmts (ss : seq fstmt) (te : TE.env) (s : vstate) : TE.env :=
    match ss with
    | [::] => te
    | h :: tl => upd_typenv_fstmts tl (upd_typenv_fstmt h te s) s
    end.

    (*
  Definition expend_mem (m : fmem) (g : graph) (mm : map) (data2addr : map) (data2en : map) (data2mask : map) (data2mid : map) (readerls : seq var) (writerls : seq var) (te : TE.env) :
  graph * map * map * map * map * map * seq var * seq var * TE.env :=
    let te1 = List.fold_right (fun x (temp : TE.env) => let te3 = TE.add (addr x) (Fuint ?(depth m)) temp in
                                          let te4 = TE.add (data x) (data_type m) te3 in
                                          let te5 = TE.add (en x) (Fuint 1) te4 in
                                          TE.add (clk x) (Fclock) te5) 
                                          te (reader m) 
                                          in
    let te2 = List.fold_right (fun x temp => let te6 = TE.add (addr x) (Fuint ?(depth m)) temp in
                                          let te7 = TE.add (data x) (data_type m) te6 in
                                          let te8 = TE.add (en x) (Fuint 1) te7 in
                                          TE.add (clk x) (Fclock) te8) 
                                          te1 (writer m) 
                                          in
    let mm0 = Map.add (mid m) emptymap mm in
    let data2addr0 = List.fold_right (fun x temp => Map.add (data x) (addr x) temp) data2addr (reader m) in 
    let data2en0 = List.fold_right (fun x temp => Map.add (data x) (en x) temp) data2addr (reader m) in 
    let data2addr1 = List.fold_right (fun x temp => Map.add (data x) (addr x) temp) data2addr (writer m) in 
    let data2en1 = List.fold_right (fun x temp => Map.add (data x) (en x) temp) data2addr (writer m) in 
    let data2mask0 = List.fold_right (fun x temp => Map.add (data x) (mask x) temp) data2addr (writer m) in 
    let data2mid0 = List.fold_right (fun x temp => Map.add (data x) (mid m) temp) data2addr (reader m) in 
    let data2mid1 = List.fold_right (fun x temp => Map.add (data x) (mid m) temp) data2addr (writer m) in 
    let readerls0 = List.fold_right (fun x temp => List.append (data x) temp) readerls (reader m) in
    let writerls0 = List.fold_right (fun x temp => List.append (data x) temp) readerls (writer m) in
    let g0 = ? in
    (g0, mm0, data2addr1, data2en1, data2mask0, data2mid1, readerls0, writerls0, te2)
    (*建立data和addr的联系*)

  Definition expend_inst (mv : var) (pl : seq fport) (g : graph) (invarmap : map) (outvarmap : map) (te : TE.env) :
  graph * map * map * TE.env :=
  (* 在graph中，使mod.input->instof->mod.output *)
    let te0 = List.fold_right (fun x temp => let (tv, tt) = name2type_fport x in
                                             TE.add tv tt temp) te pl in
    let invarmap0 = 
    let outvarmap0 = 
    let g0 = 

  Definition expr2varlist (expr : fexpr) (ls : seq var) : seq var := 
  match expr with
  | Econst _ _ -> ls
  | Eref v -> List.cons v ls
  | Eprim_unop _ e1 -> expr2varlist e1 ls
  | Eprim_binop _ e1 e2 -> expr2varlist e2 (expr2varlist e1 ls)
  | Emux e1 e2 e3 -> expr2varlist e3 (expr2varlist e2 (expr2varlist e1 ls))
  | Evalidif e1 e2 -> expr2varlist e2 (expr2varlist e1 ls)
  | Ecast _ e -> expr2varlist e ls
  end.

  Definition cons_end a ls := List.rev (List.cons a (List.rev ls))
  
  Fixpoint expend_stmts (st : seq fstmt) (g : graph) (mm : map) (data2addr) (data2en) (data2mask) (data2mid) (readerls) (writerls) (invarmap) (outvarmap) (te : TE.env) (kl : seq fstmt) (sm : map):
  (* mm: mid -> (addr -> data); invarmap、outvarmap: the var map of same port in main mod and sub mod; kl: stmts not in graph, like const、definition、invalid; sm: nodes(left hand) in graph mapping to their stmt *) 
    graph * map * map * map * map * map * seq var * seq var * map * map * TE.env * seq fstmt * map :=
    match st with
    | [::] => ([], g, mm, ... , te)
    | h :: tl =>
      match h with
      | Smem m => let (g0, mm0, data2addr0, data2en0, data2mask0, data2mid0, readerls0, writerls0, te0) := expend_mem m g mm data2addr data2en data2mask data2mid readerls writerls te in
        expend_stmts tl g0 mm0 data2addr0 data2en0 data2mask0 data2mid0 readerls0 writerls0 invarmap outvarmap te0 (cons_end h kl) sm
      | Sinst v m => 
        match m with 
        | FInmod mv pl _ => let (g0, invarmap0, outvarmap0, te0) := expend_inst mv pl g readerls writerls invarmap outvarmap te in
          expend_stmts tl g0 mm data2addr data2en data2mask data2mid readerls writerls invarmap0 outvarmap0 te0 kl (Map.add v h sm)
        | FExmod _ _ _ => ([], g, mm, ... , te, cons_end h kl, sm)
        end
      | (* other stmts add edges to graph *)
      | Sskip => ([], g, mm, ... , te, cons_end h kl, sm)
      | Swire v t => ([], g, mm, ... , te, cons_end h kl, sm)
      | Sreg r => ([], g, mm, ... , te, cons_end h kl, sm)
      | Snode v e => let func v1 v2 ggg = G.add_edge? ggg v2 v1 in (* connect in graph *)
                     let g0 = List.fold_right (func v) (expr2varlist e []) g in
                     expend_stmts tl g0 mm data2addr data2en data2mask data2mid readerls writerls invarmap outvarmap te kl (Map.add v h sm)
      | Sinvalid _ -> ([], g, mm, ... , te, cons_end h kl, sm)
      | Sfcnct (Eref v) e2 => match e2 with 
                             | Econst _ _ -> ([], g, mm, ... , te, cons_end h kl, sm)
                             | _ -> let func v1 v2 ggg = G.add_edge? ggg v2 v1 in
                                    let g0 = List.fold_right (func v) (expr2varlist e []) g in
                                    expend_stmts tl g0 mm data2addr data2en data2mask data2mid readerls writerls invarmap outvarmap te kl (Map.add v h sm)
      | _ => expend_stmts tl g mm data2addr data2en data2mask data2mid readerls writerls invarmap outvarmap te
        (* 参考ocaml的ssa排序 *)
      end
    end.

  (* 根据expend预处理画出的依赖图，对stmt排序*)
  *)
  Definition eval_fstmt (st : fstmt) (rs : vstate) (s : vstate) (te : TE.env) (readerls : seq var) (writerls : seq var) (data2etc : mapdata2etc) (memmap : mapmem) 
  (finstoutl : seq var) (finstoutm : maptuple) (ffmodsmap : mapfmod) (fterss : mapterss) (finstin : mapls) (finstinmap : mapvar) (finstoutmap : mapvar) (rl : mapls) (wl : mapls) (alldata2etc : map2etc) (allmemmap : mapmodsmem) : vstate * vstate * mapmem :=
    (* 处理mem需要增加参数 readerls data2etc memmap *)
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
                    let ve1 := eval_fexpr e1 s0 te readerls writerls data2etc memmap in
                    let ve2 := eval_fexpr e2 s0 te readerls writerls data2etc memmap in
                    if (is_zero ve1) then (rs0, s0, memmap)
                    else
                      match te1 with
                      | Fuint 1 => (SV.upd (rid r) ve2 rs0, s0, memmap)
                      | Fasyncreset => (SV.upd (rid r) ve2 rs0, SV.upd (rid r) ve2 s0, memmap)
                      | _ => (rs0, s0, memmap)
                      end
                end
    | Smem m => (rs, s, memmap)
    | Sinst inst => (rs, s, memmap) 
(*
                      have instportmap mv -> (invarmap inmod->outmod map、outvarmap outmod->inmod map)
                      
                      let m := SsrFMap.find v2 modsmap in(
                      match m with 
                      | FInmod mv pl sl => let invarm := SsrFMap.find mv inin2exin in 
                                           let outvarm := SsrFMap.find mv exout2inout in
                                           let (st0, rs0, te0) := SsrFMap.find v1 instenv4mods in

                                           let tf0 tk tv ts := SV.upd tk (SV.acc tv s) ts in(* 从主mod找到子mod input端口的值*)
                                           let s1 := Map.fold tf0 invarm st0 in 
                                           let (rs1, s2) := eval_module m sl rs0 s1 te0 readerls writerls data2etc memmap instenv4mods in (* ? *)
                                           let tf1 tk tv ts := SV.upd tk (SV.acc tv s2) ts in
                                           let s3 := Map.fold tf1 outvarm s in 
                                            (rs,s3)
                      | FExmod _ _ _ => (rs,s)
                      end)*)
    | Snode v e => (rs, SV.upd v (eval_fexpr e s te readerls writerls data2etc memmap) s, memmap)
    | Sfcnct (Eref v) e2 => let newv := (match e2 with 
                            | Eref v1 => if mylListIn v finstoutl
                                        then (match TE.find v finstoutm with (* outport -> (mod name a, inst name a0) *)
                                        | None => [::b0] (* 不知道inst.output对应的fmodule*)
                                        | Some (a,a0) => (match TE.find a ffmodsmap with (* mod name -> fmodule a1 *) 
                                                    | None => [::b0]
                                                    | Some a1 => (match TE.find a0 fterss with
                                                                | None => [::b0]
                                                                | Some aa => let '(te0,rs0,s0) := aa in (match TE.find a finstin with (* mod name -> inport name list *)
                                                                                                        | None => [::b0]
                                                                                                        | Some a2 => (let s1 := upd_inner s s0 a2 finstinmap in (* finstinmap 是参数直接传过来 *)
                                                                                                        
                                                                                                          (*let s2 := eval_innerm a1 rs0 s1 te0 allrl allwl alldata2etc allmemmap in*)
                                                                                                          (match TE.find v finstoutmap with
                                                                                                          | None => [::b0]
                                                                                                          | Some a3 => [::b1](*SV.acc a3 s2*)
                                                                                                          end))
                                                                                                        end)
                                  
                                                                end)
                                                    end)
                                        end)                                  
                                        else eval_fexpr e2 s te readerls writerls data2etc memmap
                            | _ => eval_fexpr e2 s te readerls writerls data2etc memmap
                            end) in 
                            let memmap0 := 
                            (if mylListIn v writerls (* writer ports *)
                            then match TE.find v data2etc with
                                  | None => memmap
                                  | Some a => (let '(addrvar,envar, midvar, maskvar) := a in 
                                    match TE.find midvar memmap with
                                    | None => memmap (* parse ast时已生成所有mem的map TE.add midvar (memupd (from_nat 4 10) (from_nat 4 11) memempty) memmap*)
                                    | Some b => let maskval := SV.acc maskvar s in
                                                let addrval := SV.acc addrvar s in 
                                                let enval := SV.acc envar s in
                                                if enval == [:: b1] (* en = low *)
                                                  then (if maskval == [:: b1]
                                                    then TE.add midvar (memupd addrval newv b) memmap(*TE.add midvar (memupd (from_nat 2 3) (from_nat 4 13) b) memmap*)
                                                    else TE.add midvar (memupd addrval [:: b0] b) memmap(*TE.add midvar (memupd (from_nat 2 3) (from_nat 4 12) b) memmap*)
                                                  )
                                                  else
                                                  (*TE.add midvar (memupd (from_nat 2 3) (from_nat 4 10) b) *)memmap
                                                end
                            )
                            end
                            else memmap)in
                            if SV.acc v rs == [::]
                              then (rs, SV.upd v newv s, memmap0)
                            else (SV.upd v newv rs, s, memmap0) (* regs *)
    | Sinvalid v =>
      let tv := TE.vtyp v te in
      (rs, SV.upd v (zeros (sizeof_fgtyp tv)) s, memmap)
    | _ => (rs, s, memmap)
    end.  
  
  Fixpoint eval_fstmts st rs s te (readerls : seq var) (writerls : seq var) (data2etc : mapdata2etc) (memmap : mapmem)
  (finstoutl : seq var) (finstoutm : maptuple) (ffmodsmap : mapfmod) (fterss : mapterss) (finstin : mapls) (finstinmap : mapvar) (finstoutmap : mapvar) (rl : mapls) (wl : mapls) (alldata2etc : map2etc) (allmemmap : mapmodsmem) : vstate * vstate * mapmem :=
    match st with
    | [::] => (rs, s, memmap)
    | h :: tl => (*let te1 := upd_typenv_fstmt h te s in *)
      let '(rs1, s1, memmap0) := eval_fstmt h rs s te readerls writerls data2etc memmap finstoutl finstoutm ffmodsmap fterss finstin finstinmap finstoutmap rl wl alldata2etc allmemmap in
      eval_fstmts tl rs1 s1 te readerls writerls data2etc memmap0 finstoutl finstoutm ffmodsmap fterss finstin finstinmap finstoutmap rl wl alldata2etc allmemmap
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

    (*
    (* 对每个module中，声明的每个instance，新建一个store一个te，用instance的名字为索引，建立map *)
    (* 对某module，inst var -> (store,rs,te) *)
  Definition bfr_eval_circuit_formod (m : fmodule) modsmap :=
    match m with
    | FInmod v ps st => List.fold_left (fun a x => match x with
                                                  | Sinst v1 v2 => match SsrFMap.find v2 modsmap with
                                                                  | FInmod _ tps tst => (*let s1 := eval_fports_init tps (SV.empty) in*)
                                                                                         let te0 := upd_typenv_fports tps (TE.empty) in
                                                                                         let te1 := upd_typenv_fstmts sts te0 (SV.empty) in
                                                                                         SsrFMap.add v1 (SV.empty, SV.empty, te1) a(* 利用v2的module对te做初始化*)
                                                                  | _ => a
                                                                  end      
                                                  | _ => a
                                                  end) SsrFMap.empty st
    | _ => SsrFMap.empty
    end.

  (* module var -> map(instance var -> store\reg store\te)*)
  Definition bfr_eval_circuit (modsmap (*: var -> fmodule *)) :=
    SsrFMap.fold (fun key value a => SsrFMap.add key (bfr_eval_circuit_formod value) a) modsmap SsrFMap.empty

  Definition eval_submod (m : fmodule) s rs te readerls writerls data2etc memmap instenv4mods : vstate * vstate * SsrFMap (* 需要更新instance的st、te*):=
    match m with
    | FInmod v ps st => let := eval_fstmts st s rs te readerls writerls data2etc memmap instenv4mods in 
                        (s0,rs0, ? )
    | _ => (s,rs,instenv4mods)
    end.
  *)
  Definition eval_module mainmod rs s te (readerls : mapls) (writerls : mapls) (data2etc : map2etc) (memmap : mapmodsmem)
  (finstoutl : mapls) (finstoutm : mmaptuple) (ffmodsmap : mapfmod) (fterss : mapterss) (finstin : mapls) (finstinmap : mmapvar) (finstoutmap : mmapvar) : vstate * vstate * mapmodsmem :=
    match mainmod with
    | FInmod v ps st => (*let te0 := upd_typenv_fports ps (TE.empty) in 在ocaml赋初值，因为要run多个周期，需放在clk_step外*)
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
                        | None => (rs,s, memmap)
                        | Some a => let data2etc0 := a in 
                          match TE.find v finstoutm with
                          | None =>  (rs,s, memmap)
                          | Some a => let finstoutm0 := a in
                            match TE.find v finstinmap with
                            | None =>  (rs,s, memmap)
                            | Some a => let finstinmap0 := a in
                              match TE.find v finstoutmap with
                              | None =>  (rs,s, memmap)
                              | Some a => let finstoutmap0 := a in
                                match TE.find v memmap with
                                | None =>  (rs,s, memmap)
                                | Some a => let memmap0 := a in
                          let '(rs1, s1, memmap1) := eval_fstmts (rev st) rs s te readerls0 writerls0 data2etc0 memmap0 finstoutl0 finstoutm0 ffmodsmap fterss finstin finstinmap0 finstoutmap0 readerls writerls data2etc memmap in
                          (rs1, s1, TE.add v memmap1 memmap)
                                end
                              end
                            end
                          end
                        end
                        
    | _ => (rs,s, memmap)
    end.

  Definition eval_innerm mainmod rs s te (readerls : mapls) (writerls : mapls) (data2etc : map2etc) (memmap : mapmodsmem) 
  (finstoutl : mapls) (finstoutm : mmaptuple) (ffmodsmap : mapfmod) (fterss : mapterss) (finstin : mapls) (finstinmap : mmapvar) (finstoutmap : mmapvar) : vstate :=
    match mainmod with
    | FInmod v ps st => (*let te0 := upd_typenv_fports ps (TE.empty) in 在ocaml赋初值，因为要run多个周期，需放在clk_step外*)
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
                        | None => s
                        | Some a => let data2etc0 := a in 
                          match TE.find v finstoutm with
                          | None =>  s
                          | Some a => let finstoutm0 := a in
                            match TE.find v finstinmap with
                            | None =>  s
                            | Some a => let finstinmap0 := a in
                              match TE.find v finstoutmap with
                              | None =>  s
                              | Some a => let finstoutmap0 := a in
                                match TE.find v memmap with
                                | None =>  s
                                | Some a => let memmap0 := a in
                                let '(_, s2, _) := 
                                List.fold_left (fun '(rs1, s1, memmap0) tempst => eval_fstmt tempst rs s te readerls0 writerls0 data2etc0 memmap0 finstoutl0 finstoutm0 ffmodsmap fterss finstin finstinmap0 finstoutmap0 readerls writerls data2etc memmap) (rev st) (rs, s, memmap0) in
                                s2      
                                end
                              end
                            end
                          end
                        end
                        
    | _ => s
    end.

  Fixpoint run_module mainmod rs s te (io_in : mapioin) name readerls writerls data2etc memmap clk_num len 
  (finstoutl : mapls) (finstoutm : mmaptuple) (ffmodsmap : mapfmod) (fterss : mapterss) (finstin : mapls) (finstinmap : mmapvar) (finstoutmap : mmapvar) : vstate * vstate * mapmodsmem :=
  match clk_num with
    | 0 => (rs,s,memmap)
    | S m => let n := len - S m in
             let s1 := upd_argulist s io_in name n in
             (*let te1 := upd_typenv_fstmts st te s1 in*) (* 放在和upd fports同时？ *)
             let '(rs2, s2, memmap0) := eval_module mainmod rs s1 te readerls writerls data2etc memmap finstoutl finstoutm ffmodsmap fterss finstin finstinmap finstoutmap in (* 每个clk后 fterss 需要更新*)
             run_module mainmod rs2 s2 te io_in name readerls writerls data2etc memmap0 m len finstoutl finstoutm ffmodsmap fterss finstin finstinmap finstoutmap
    end.
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
