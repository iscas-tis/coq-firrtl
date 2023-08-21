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
  | Eref : var -> fexpr
  (* | Edeclare : var -> fgtyp -> fexpr *)
  (* | Efield : fexpr -> fexpr -> fexpr *) (* HiFirrtl *)
  (* | Esubfield : var -> nat -> fexpr *) (* HiFirrtl *)
  | Ecast : ucast -> fexpr -> fexpr
  | Eprim_unop : eunop -> fexpr -> fexpr
  | Eprim_binop : ebinop -> fexpr -> fexpr -> fexpr
  | Emux : fexpr -> fexpr -> fexpr -> fexpr
  | Evalidif : fexpr -> fexpr -> fexpr
  .

  (****** Statements ******)
  Inductive ruw : Set :=
  | old | new | undefined.

  Record fmem : Type :=
    mk_fmem
      {
        mid : var;
        data_type : fgtyp;
        depth : nat;
        reader : seq var;
        writer : seq var;                    
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
        clock : fexpr;
        reset : rst
      }.

  Inductive fstmt : Type :=
  | Sskip
  | Swire : var -> fgtyp -> fstmt
  | Sreg : freg -> fstmt
  | Smem : fmem -> fstmt
  | Sinst : var -> var -> fstmt
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

  Inductive fport : Type :=
  | Finput : var -> fgtyp -> fport
  | Foutput : var -> fgtyp -> fport
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
       (VS : SsrFSet with Module SE := V)
       (VM : SsrFMap with Module SE := V)
       (TE : TypEnv with Module SE := V)
       (SV : ValStore V TE)
       (EV : ExprStore V TE).
  Local Open Scope firrtl.
  Local Open Scope bits.
  
  Module VSLemmas := SsrFSetLemmas VS.

  Local Notation var := V.t.

  Local Notation vstate := SV.t.

  (* Definition EStore := Store.M.t (fexpr V.T). *)

  Local Notation estate := EV.t.
  

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
  (* Definition sinst v1 v2 := @Sinst V.T v1 v2. *)
  Definition snode v e := @Snode V.T v e.
  Definition sfcnct v1 v2 := @Sfcnct V.T v1 v2.

  Definition freg := @freg V.T.
  Definition mk_freg := @mk_freg V.T.
  Definition nrst := @NRst V.T.
  Definition rrst e1 e2 := @Rst V.T e1 e2.
  Definition fmem := @fmem V.T.
  Definition mk_fmem := @mk_fmem V.T.
  Definition fport := @fport V.T.
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
  
  (* Expression evaluation, value *)
  Fixpoint eval_fexpr (e : fexpr) (s : vstate) (te : TE.env) : bits :=
    match e with
    | Econst t c => c
    | Eref v => SV.acc v s
    (* | Efield *)
    (* | Esubfield  *)
    | Eprim_binop b e1 e2 =>
      let ve1 := (eval_fexpr e1 s te) in
      let ve2 := (eval_fexpr e2 s te) in
      let te1 := type_of_fexpr e1 te in
      let te2 := type_of_fexpr e2 te in
      (ebinop_op b te1 te2) ve1 ve2
    | Eprim_unop u e =>
      let t := type_of_fexpr e te in
      (eunop_op u t) (eval_fexpr e s te)
    | Emux c e1 e2 =>
      let t1 := (type_of_fexpr e1 te) in
      let t2 := (type_of_fexpr e2 te) in
      match t1, t2 with
      | Fuint w1, Fuint w2 => if ~~ (is_zero (eval_fexpr c s te)) 
      then (zext ((max w1 w2) - w1) (eval_fexpr e1 s te)) else(zext ((max w1 w2) - w2) (eval_fexpr e2 s te))
      | Fsint w1, Fsint w2 => if ~~ (is_zero (eval_fexpr c s te)) 
      then (sext ((max w1 w2) - w1) (eval_fexpr e1 s te)) else(sext ((max w1 w2) - w2) (eval_fexpr e2 s te))
      | _, _ => [::]
      end       
    | Evalidif c e => if ~~ (is_zero (eval_fexpr c s te)) then (eval_fexpr e s te) else [::]
    (* | Edeclare v t => zeros (sizeof_fgtyp t) *)
    | Ecast AsUInt e => eval_fexpr e s te
    | Ecast AsSInt e => eval_fexpr e s te
    | Ecast AsClock e => [::lsb (eval_fexpr e s te)]
    | Ecast AsReset e => [::lsb (eval_fexpr e s te)]
    | Ecast AsAsync e => [::lsb (eval_fexpr e s te)]
    end.
  


  (*Compute (from_Z 6 (-3)). (*[:: true; false; true; true; true; true] *)
  Compute (from_Z 11 (-56)). (*[:: false; false; false; true; false; false; true; true; true; true; true]*)
  Compute (ebinop_op Badd (Fsint 6) (Fsint 11) [:: true; false; true; true; true; true] [:: false; false; false; true; false; false; true; true; true; true; true]).
  *)Compute (ebinop_op Badd (Fsint 4) (Fsint 4) [:: true;true;true;true] [:: false; true; true; false]).
  Compute (eunop_op (Ucvt) (Fuint 6) [:: true; false; true; true; true; true]).
  
  (* Expression statement, type env *)
  Definition upd_typenv_fstmt (s : fstmt) (te : TE.env) (st : vstate) : TE.env :=
    match s with
    | Swire v t  => TE.add v t te
    | Sreg r => TE.add (rid r) (type r) te
    (* | Snode v e => TE.add v (type_of_fexpr e (upd_typenv_fexpr e te)) (upd_typenv_fexpr e te) *)
    | Snode v e => TE.add v (type_of_fexpr e te) te
    | _ => te
    end.

  Fixpoint upd_typenv_fstmts (ss : seq fstmt) (te : TE.env) (s : vstate) : TE.env :=
    match ss with
    | [::] => te
    | h :: tl => upd_typenv_fstmts tl (upd_typenv_fstmt h te s) s
    end.
  
  Definition eval_fstmt (st : fstmt) (rs : vstate) (s : vstate) (te : TE.env) : vstate * vstate :=
    match st with
    | Sskip => (rs, s)
    | Swire v t => (rs, SV.upd v (zeros (sizeof_fgtyp t)) s)
    | Sreg r =>
      let (rs0, s0) := if SV.acc (rid r) rs == [::]
                       then (SV.upd (rid r) (zeros (sizeof_fgtyp (type r))) rs,
                             SV.upd (rid r) (zeros (sizeof_fgtyp (type r))) s)
                       else (rs, SV.upd (rid r) (SV.acc (rid r) rs) s) in
                match reset r with
                | NRst => (rs0, s0)
                | Rst e1 e2 =>
                    let te1 := type_of_fexpr e1 te in
                    let ve1 := eval_fexpr e1 s0 te in
                    let ve2 := eval_fexpr e2 s0 te in
                    if (is_zero ve1) then (rs0, s0)
                    else
                      match te1 with
                      | Fuint 1 => (SV.upd (rid r) ve2 rs0, s0)
                      | Fasyncreset => (SV.upd (rid r) ve2 rs0, SV.upd (rid r) ve2 s0)
                      | _ => (rs0, s0)
                      end
                end
    | Smem m => (rs, s) (* TBD *)
    | Sinst v1 v2 => (rs, SV.upd v1 (SV.acc v1 s) s) 
    | Snode v e => (rs, SV.upd v (eval_fexpr e s te) s)
    | Sfcnct (Eref v) e2 => if SV.acc v rs == [::]
                            then (rs, SV.upd v (eval_fexpr e2 s te) s)
                            else (SV.upd v (eval_fexpr e2 s te) rs, s)
    | Sinvalid v =>
      let tv := TE.vtyp v te in
      (rs, SV.upd v (zeros (sizeof_fgtyp tv)) s)
    | _ => (rs, s)
    end.  
  
  Fixpoint eval_fstmts st rs s te : vstate * vstate :=
    match st with
    | [::] => (rs, s)
    | h :: tl =>
      let te1 := upd_typenv_fstmt h te s in
      let (rs1, s1) := eval_fstmt h rs s te1 in
      eval_fstmts tl rs1 s1 te1
    end.

    Import Natlist0.
    Local Open Scope natlist0.
  
  Fixpoint upd_argulist s io_in name ind : vstate :=
    match name with
     | [:: ] => s
     | h::t => upd_argulist (SV.upd h (from_nat 1 (nth_bad (io_in h) ind)) s) io_in t ind
    end.
  
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
  
End MakeFirrtl.

 
Module LoFirrtl := MakeFirrtl VarOrder VS VM TE Store EStore.
(*   
(*Definition subB_ext bs1 bs2 := let (b, r) := (sbbB_ext false bs1 bs2) in rcons r b.
  Definition wky_subB_ext bs1 bs2 := let newl := (maxn (size bs1) (size bs2))+1 in
                                     let nbs1 := zext (newl-(size bs1)) bs1 in
                                     let nbs2 := zext (newl-(size bs2)) bs2 in
    let (b, r) := (sbbB_ext false nbs1 nbs2) in r.*)

Lemma size_subB_ext bs1 bs2 : size (wky_subB_ext bs1 bs2) = (maxn (size bs1) (size bs2))+1.
  Proof. 
    rewrite /wky_subB_ext.
    rewrite /sbbB_ext /adcB_ext.
    rewrite size_full_adder_ext.
    fold (@cat bool bs1 (zeros (maxn (size bs1) (size bs2) + 1 - size bs1))).
    rewrite size_cat size_invB size_zext size_zeros addn1 subnKC maxnC.
    rewrite subnKC.
    unfold maxn at 1.
    rewrite ltnn //.
    move : (leq_maxl (size bs2) (size bs1)) => Hbd2.
    rewrite maxnC in Hbd2.
    move : (leqnSn (maxn (size bs1) (size bs2))) => Hmax1.
    rewrite (leq_trans Hbd2 Hmax1) //.
    move : (leq_maxl (size bs1) (size bs2)) => Hbd1.
    rewrite maxnC in Hbd1.
    move : (leqnSn (maxn (size bs2) (size bs1))) => Hmax1.
    rewrite (leq_trans Hbd1 Hmax1) //.
  Qed.


    (*assert (Hbs1 : bs1 = -# (rcons (dropmsb (-# bs1)) (msb (-# bs1)))).
    rewrite -rconsmsb.
    rewrite negB_involutive //.
    rewrite size_negB.
    move /eqP : Hlen1 => Hlen1.
    apply not_eq_sym in Hlen1.
    apply neq_0_lt in Hlen1.
    move /ltP : Hlen1 => Hlen1.
    exact Hlen1.
    assert (Hbs2 : bs2 = -# (rcons (dropmsb (-# bs2)) (msb (-# bs2)))).
    rewrite -rconsmsb.
    rewrite negB_involutive //.
    rewrite size_negB.
    move /eqP : Hlen2 => Hlen2.
    apply not_eq_sym in Hlen2.
    apply neq_0_lt in Hlen2.
    move /ltP : Hlen2 => Hlen2.
    exact Hlen2.
    rewrite {2}Hbs1 {2}Hbs2.

    
    rewrite msb0_to_Z_negB.
    rewrite msb0_to_Z_negB.
    rewrite 2!to_Zpos_rcons.
    rewrite -msb_negB.
    rewrite -msb_negB.
    rewrite H11 H21.
    simpl.
    rewrite 2!Z.add_0_r Z.mul_opp_opp to_Zpos_full_mul //.
    apply Hdrop2.
    apply Hdrop1.
    rewrite msb_rcons -msb_negB.
    rewrite H21 //.
    apply Hdrop2.
    rewrite msb_rcons -msb_negB.
    rewrite H11 //.
    apply Hdrop1.
    trivial.
*)


    (*
        have -> : (zext (size (-# bs2)) bs1) = (zext (size (-# bs2) - 1) bs1)).
    rewrite dropmsb_rcons H10 zext_rcons0 {2}/zext rcons_cat zeros_rcons -addn1 subnK /zext //.
    move /eqP : Hlen2 =>Hlen2.
    apply not_eq_sym in Hlen2.
    apply neq_0_lt in Hlen2.
    move /ltP : Hlen2 => Hlen2.
    rewrite size_negB.
    apply Hlen2.

    rewrite Ht1 Ht2.

    assert (Hsext : to_Z (sext (size (-# bs2) -1) bs1 *# sext (size (dropmsb bs1)) (-# bs2)) =
            to_Z (sext (size (-# bs2)) bs1 *# sext (size bs1) (-# bs2))).
    rewrite splitmsb_mulB_sext1.
    have -> : (sext 1 ((sext (size (-# bs2) - 1) bs1))) = (sext (size (-# bs2)) bs1).
    admit.
    have -> : (sext 1 (sext (size (dropmsb bs1)) (-# bs2))) = sext (size bs1) (-# bs2).
    admit.
        rewrite size_negB size_dropmsb addnABC //.
    move /eqP : Hlen2 =>Hlen2.
    apply not_eq_sym in Hlen2.
    apply neq_0_lt in Hlen2.
    move /ltP : Hlen2 => Hlen2.
    apply Hlen2.
    move /eqP : Hlen1 =>Hlen1.
    apply not_eq_sym in Hlen1.
    apply neq_0_lt in Hlen1.
    move /ltP : Hlen1 => Hlen1.
    apply Hlen1.
*)

(*
    assert (Hbs2 : sext 1 bs2 = -# (rcons (dropmsb (-# (sext 1 bs2))) (msb (-# (sext 1 bs2))))).
    rewrite -rconsmsb.
    rewrite negB_involutive //.
    rewrite size_negB size_sext addn1 ltn0Sn //.
    have -> : (to_Z bs2) = (to_Z (sext 1 bs2)) by rewrite to_Z_sext //.

    rewrite {2}Hbs2.
    rewrite msb0_to_Z_negB.
    rewrite to_Zpos_rcons.
    rewrite -msb_negB.
    rewrite msb_sext.
    move /eqP : H21 => H21.
    rewrite H21.
    simpl.
    rewrite Z.add_0_r Z.mul_opp_r.

    rewrite (to_Z_to_Zpos bs1).
    move /eqP : H10 => H10.
    rewrite H10 Z.mul_0_l Z.sub_0_r.
    rewrite -to_Zpos_full_mul.
        Z_mul_to_Z_msb_same:
  forall [bs1 bs2 : bits], msb bs1 == msb bs2 -> (0 <= to_Z bs1 * to_Z bs2)%Z
  Z_mul_to_Z_msb_diff:
  forall [bs1 bs2 : bits], msb bs1 != msb bs2 -> (to_Z bs1 * to_Z bs2 <= 0)%Z
  msb1_to_Z_lt0':
  forall [bs : seq bool], 0 < size bs -> msb bs -> (to_Z bs < 0)%Z
  high1_0_to_Z_negB:
  forall [bs : bits], high 1 bs = [:: b0] -> to_Z (-# bs) = (- to_Zpos bs)%Z*)
(*
    rewrite full_mul_mulB_zext. 
    case Hdrop1 : (dropmsb bs1 == zeros (size bs1 - 1)).
    move /eqP : Hdrop1 => Hdrop1.
    admit.

    have -> : (zext (size (-# bs1)) (dropmsb bs2) = (zext (size (-# bs1) - 1) bs2)).
    have -> : (bs2 = rcons (dropmsb bs2) (msb bs2)).
    apply rconsmsb.
    move /eqP : Hlen2 =>Hlen2.
    apply not_eq_sym in Hlen2.
    apply neq_0_lt in Hlen2.
    move /ltP : Hlen2 => Hlen2.
    apply Hlen2.
    assert (Ht2 : zext (size (-# bs1) -1) (bs2) = sext (size (-# bs1) -1) (bs2)).
    rewrite /zext /sext.
    rewrite H20 //.
    rewrite dropmsb_rcons H20.

    assert (Ht1 : zext (size (dropmsb bs2)) (-# bs1) = sext (size (dropmsb bs2)) (-# bs1)).
    rewrite /zext /sext.
    rewrite -msb_negB.
    rewrite H11 //.
    apply contraFneq with (b:=(dropmsb bs1 == zeros (size bs1 - 1))).
    intro.
    move /eqP : H =>H.
    apply H.
    exact Hdrop1.
    
    rewrite Ht1 Ht2.
    rewrite bv2z_mul_signed.
    rewrite 2!to_Z_sext.
    rewrite NBitsOp.to_Z_negB.
    rewrite Z.mul_opp_l Z.opp_involutive //.
    rewrite H11 andb_true_l.
    apply contraFneq with (b:=(dropmsb bs1 == zeros (size bs1 - 1))).
    intro.
    move /eqP : H =>H.
    apply H.
    exact Hdrop1.
    rewrite size_sext size_negB.
    move /eqP : Hlen1 =>Hlen1.
    apply not_eq_sym in Hlen1.
    apply neq_0_lt in Hlen1.
    move /ltP : Hlen1 => Hlen1.
    rewrite addn_gt0 Hlen1 //.
    rewrite 2!size_sext addnC //.
    rewrite size_negB size_dropmsb addnABC //.
    move /eqP : Hlen2 =>Hlen2.
    apply not_eq_sym in Hlen2.
    apply neq_0_lt in Hlen2.
    move /ltP : Hlen2 => Hlen2.
    apply Hlen2.
    move /eqP : Hlen1 =>Hlen1.
    apply not_eq_sym in Hlen1.
    apply neq_0_lt in Hlen1.
    move /ltP : Hlen1 => Hlen1.
    apply Hlen1.
    have -> : (sext (size (-# bs1) - 1) bs2 = sext (size (-# bs1)) (dropmsb bs2)).
    admit.
    apply smulo_sext.
Admitted.

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

  Lemma to_Z_from_Z bs n x : n >= (size bs) -> x = to_Z bs -> Z.opp x = to_Z (from_Z n (Z.opp x)).
  Proof.
    intros.
    rewrite /from_Z.
    case Hz: (Z.opp x)%Z.
    - rewrite to_Z_zeros //.
    - rewrite to_Z_to_Zpos to_Zpos_from_Zpos_bounded.
    Search to_Z.
    (*to_Zpos_from_Zpos_bounded:
  forall [n : nat] [z : Z],
  (0 <= z)%Z -> (z < 2 ^ Z.of_nat n)%Z -> to_Zpos (from_Zpos n z) = z*)
    Admitted.

  Lemma to_Z_Sfull_mul0 bs1 bs2: to_Z (Sfull_mul bs1 bs2) = to_Z (from_Z (size (Sfull_mul bs1 bs2)) (Z.mul (to_Z bs1) (to_Z bs2))).
  Proof.
    Search to_Z.
    case Hbs2 : (size bs2 == 0).
    - move /eqP : Hbs2 => Hbs2.
    apply size0nil in Hbs2.
    rewrite Hbs2 to_Z_nil Z.mul_0_r -zeros_from_Z to_Z_zeros.
    admit.

    - move /eqP : Hbs2 => Hbs2.
    apply not_eq_sym in Hbs2.
    apply neq_0_lt in Hbs2.
    move /ltP : Hbs2 => Hbs2.

    elim bs1 => [|hd1 tl1 IH] /=. 
    rewrite!from_natn0 size_zeros!add0n //. 
    case Hhd1 : hd1. 
    - case Htl1 : (tl1 == [::]).
      - move /eqP : Htl1 => Htl1.
      rewrite bv2z_add_signed.
      rewrite to_Z_zext.
      rewrite bv2z_not_signed.
      rewrite to_Z_sext.
      have -> : ([::b1] = ones 1) by symmetry.
      rewrite to_Zpos_ones.
      simpl.
      rewrite Z.sub_add.
      rewrite Htl1.
      have -> : ([:: true] = ones 1) by symmetry.
      rewrite to_Z_ones.
      rewrite Z.mul_comm -Z.opp_eq_mul_m1 size_addB.
      assert (Hsizeeq : (size (~~# sext (size ([::] : bits)).+1 bs2)) = (size (zext (size bs2) (ones 1)))).
      rewrite size_zext size_ones size_invB size_sext addnC.
      simpl.
      reflexivity.
      rewrite Hsizeeq /minn ltnn size_zext size_ones.
      apply to_Z_from_Z with (bs:=bs2).
      rewrite addnC addn1 leqnSn //.
      reflexivity.
      trivial.
      rewrite size_sext -(addn1 (size tl1)) -addnACl.
      trivial.
      apply Hbs2.
      have -> : ([::b1] = ones 1) by symmetry.
      rewrite Htl1 size_zext size_ones size_invB size_sext addnC.
      simpl.
      reflexivity.
      rewrite Htl1.
      simpl.

      rewrite /Saddo.
      rewrite -/(msb (~~# sext 1 bs2)) -/(msb ((zext (size bs2) [:: b1]))) -/(msb (~~# sext 1 bs2 +# zext (size bs2) [:: b1])).
      rewrite -msb_invB.
      rewrite msb_sext msb_zext.
      simpl.
      rewrite andb_false_r andb_false_l orb_false_l andb_true_r negb_andb.
      case Hmsb2 : ((msb bs2) == false).
      - move /eqP : Hmsb2 => Hmsb2.
        rewrite Hmsb2.
        simpl.
        done.
      - move /eqP : Hmsb2 => Hmsb2.
        apply Bool.not_false_is_true in Hmsb2.
        rewrite Hmsb2.
        simpl.
        rewrite /sext /zext Hmsb2.
        have -> : (copy 1 true = [::b1]) by symmetry.
        Search msb.
(*invB_cat: forall bs1 bs2 : seq bool, ~~# (bs1 ++ bs2) = ~~# bs1 ++ ~~# bs2
invB_cons: forall (b : bool) (bs : seq bool), ~~# (b :: bs) = ~~ b :: ~~# bs*)
    admit.
        apply Hbs2.
        rewrite size_sext addn1. 
        move : (Nat.lt_0_succ (size bs2)) => Ht.
        move /ltP : Ht => Ht.
        exact Ht.

      - move /eqP : Htl1 => Htl1.
      rewrite size_addB size_joinlsb size_Sfull_mul size_sext -(addn1 (size tl1)).
      rewrite (addnC (size tl1) 1) -(addnACl (size tl1) (size bs2) 1) /minn ltnn.

      Search dropmsb. (*to_Zpos_from_Zpos_bounded:
      forall [n : nat] [z : Z],
      (0 <= z)%Z -> (z < 2 ^ Z.of_nat n)%Z -> to_Zpos (from_Zpos n z) = z*)

      (*to_Z_zext:
  forall (bs : bits) [n : nat], 0 < n -> to_Z (zext n bs) = to_Zpos bs

  bv2z_mulj_signed:
  forall [bs1 bs2 : seq bool],
  0 < size bs1 ->
  size bs1 = size bs2 ->
  to_Z (sext (size bs1) bs1 *# sext (size bs1) bs2) = (to_Z bs1 * to_Z bs2)%Z

  bv2z_mull_signed:
  forall [bs1 bs2 : seq bool],
  0 < size bs1 ->
  size bs1 = size bs2 ->
  (to_Zpos (low (size bs2) (sext (size bs1) bs1 *# sext (size bs1) bs2)) +
   to_Z (high (size bs1) (sext (size bs1) bs1 *# sext (size bs1) bs2)) *
   2 ^ Z.of_nat (size bs2))%Z = (to_Z bs1 * to_Z bs2)%Z*)
   
admit.   
  Admitted.
*)

| Smem m =>
(* mem.clk 放入rs 
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
*)