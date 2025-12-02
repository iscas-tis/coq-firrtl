From Coq Require Import FunInd FMaps FMapAVL OrderedType ZArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat ssrint eqtype seq fintype fingraph.
From simplssrlib Require Import Types SsrOrder FSets FMaps Tactics Var Store.
From nbits Require Import NBits.
From firrtl Require Import Firrtl Env HiEnv HiFirrtl.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Inductive hvalue : Type :=
  | Gval : bits -> hvalue
  | Aval : array_value -> hvalue
  | Bval : bundle_value -> hvalue
with array_value : Type :=
  | Aone : hvalue -> array_value
  | Acons : hvalue -> array_value -> array_value
with bundle_value : Type :=
  | Bnil : bundle_value
  | Bflips : var -> fflip -> hvalue -> bundle_value -> bundle_value.

Lemma bitseq_eq_dec : forall (x y : bitseq), {x = y} + {x <> y}.
Proof.
  apply list_eq_dec.
  apply bool_dec.
Qed.

(* general data value equality is decidable *)
Lemma hvalue_eq_dec (x y : hvalue) : {x = y} + {x <> y}
with array_value_eq_dec (x y : array_value) : {x = y} + {x <> y}
with bundle_value_eq_dec (x y : bundle_value) : {x = y} + {x <> y}.
Proof.
  - destruct x, y; try (right; discriminate).
    + destruct (bitseq_eq_dec b b0) as [H|H]; [left; f_equal; exact H | right; injection; auto].
    + destruct (array_value_eq_dec a a0) as [H|H]; [left; f_equal; exact H | right; injection; auto].
    + destruct (bundle_value_eq_dec b b0) as [H|H]; [left; f_equal; exact H | right; injection; auto].
  - destruct x, y; try (right; discriminate).
    + destruct (hvalue_eq_dec h h0) as [H|H]; [left; f_equal; exact H | right; injection; auto].
    + destruct (hvalue_eq_dec h h0) as [H1|H1];
      [destruct (array_value_eq_dec x y) as [H2|H2]; [left; f_equal; assumption | right; injection; auto] 
      | right; injection; auto].
  - destruct x, y; try (right; discriminate); [left; reflexivity |].
    destruct (N.eq_dec v v0) as [Hv|Hv];
      [destruct (fflip_eq_dec f f0) as [Hf|Hf];
        [destruct (hvalue_eq_dec h h0) as [Hh|Hh];
          [destruct (bundle_value_eq_dec x y) as [Ht|Ht]; 
          [left; do 4 f_equal; assumption | right; injection; auto]
        | right; injection; auto]
      | right; injection; auto]
    | right; injection; auto].
Qed.

(* Boolean equality for general data values *)
Fixpoint hvalue_eqn (x y : hvalue) : bool :=
  match x, y with
  | Gval val1, Gval val2 => val1 == val2
  | Aval val1, Aval val2 => array_value_eqn val1 val2
  | Bval val1, Bval val2 => bundle_value_eqn val1 val2
  | _, _ => false
  end
with array_value_eqn (x y : array_value) : bool :=
  match x, y with
  | Aone val1, Aone val2 => hvalue_eqn val1 val2
  | Acons val1 tl1, Acons val2 tl2 => (hvalue_eqn val1 val2) && (array_value_eqn tl1 tl2)
  | _, _ => false
  end
with bundle_value_eqn (x y : bundle_value) : bool :=
  match x, y with
  | Bnil, Bnil => true
  | Bflips v1 Nflip val1 ff1, Bflips v2 Nflip val2 ff2 => (v1 == v2) && (hvalue_eqn val1 val2) && (bundle_value_eqn ff1 ff2)
  | Bflips v1 Flipped val1 ff1, Bflips v2 Flipped val2 ff2 => (v1 == v2) && (hvalue_eqn val1 val2) && (bundle_value_eqn ff1 ff2)
  | _, _ => false
  end.

Lemma bits_eqP : forall (x y : bits), reflect (x = y) (x == y).
Proof. intros. exact: eqP. Qed.

Lemma N_eqP : forall (x y : N), reflect (x = y) (x == y).
Proof. intros. exact: eqP. Qed.

(* reflection predicate for general data values *)
Lemma hvalue_eqP : forall (x y : hvalue), reflect (x = y) (hvalue_eqn x y)
with array_value_eqP : forall (x y : array_value), reflect (x = y) (array_value_eqn x y)
with bundle_value_eqP : forall (x y : bundle_value), reflect (x = y) (bundle_value_eqn x y).
Proof.
  (* 证明hvalue_eqP *)
  - intros x y.
    destruct x as [n|a|b], y as [m|a'|b']; simpl; try (right; congruence).
    + destruct (bits_eqP n m) as [H|H].
        * left. f_equal; assumption.
        * right; congruence. 
    + destruct (array_value_eqP a a') as [H|H].
        * left; f_equal; assumption.
        * right; congruence.
    + destruct (bundle_value_eqP b b') as [H|H].
        * left; f_equal; assumption.
        * right; congruence.
  
  (* 证明array_value_eqP *)
  - intros x y.
    destruct x as [h1|h1 t1], y as [h2|h2 t2]; simpl; try (right; congruence).
    + destruct (hvalue_eqP h1 h2) as [H|H].
        * left; f_equal; assumption.
        * right; congruence.
    + destruct (hvalue_eqP h1 h2) as [H1|H1]; try (right; congruence).
        destruct (array_value_eqP t1 t2) as [H2|H2].
          * left; f_equal; assumption.
          * right; congruence.
  
  (* 证明bundle_value_eqP *)
  - intros x y.
    destruct x as [|v1 flip1 h1 t1], y as [|v2 flip2 h2 t2]; simpl; try (right; congruence).
    left; done. destruct flip1; right; done.
    destruct flip1, flip2; simpl; try (right; congruence).
    + destruct (N_eqP v1 v2) as [Hv|Hv]; try (right; congruence).
      destruct (hvalue_eqP h1 h2) as [Hh|Hh]; try (right; congruence).
      destruct (bundle_value_eqP t1 t2) as [Ht|Ht]; try (right; congruence). 
      left; do 4 f_equal; assumption.
    + destruct (N_eqP v1 v2) as [Hv|Hv]; try (right; congruence).
      destruct (hvalue_eqP h1 h2) as [Hh|Hh]; try (right; congruence).
      destruct (bundle_value_eqP t1 t2) as [Ht|Ht]; try (right; congruence). 
      left; do 4 f_equal; assumption.
Qed.

(*Compute (to_Z [::false;true]).
Compute (to_Zpos [::false;true]).
Compute (to_Z [::true;false]).
Compute (to_Zpos [::true;false]). 后为高位
若使用Z来表示value
| Fsint _ => to_Z c
| Fuint _ => to_Zpos c *)

(* type of ref expressions *)
Fixpoint type_of_ref (r : HiF.href) (tmap : VM.t (ftype * forient)) : option ftype :=
  match r with
  | Eid v => match VM.find v tmap with
            | Some (ft, _) => Some ft
            | None => None
            end
  | Esubfield r v => match type_of_ref r tmap with
              | Some (Btyp fs) => let fix aux fx := (
                                          match fx with
                                          | Fflips v' f t fxs =>
                                            if (v == v') then Some t
                                            else aux fxs
                                          | Fnil => None
                                          end )
                                  in aux fs
              | _ => None
              end
  | Esubindex r n => match type_of_ref r tmap with
              | Some (Atyp ty _) => Some ty
              | _ => None
              end
  | Esubaccess r e => None
  end.

Fixpoint type_of_hfexpr (e : HiF.hfexpr) (tmap: VM.t (ftype * forient)) : option ftype :=
  match e with
  | Econst t bs => Some (Gtyp t)
  | Eref r => type_of_ref r tmap 
  | Ecast AsUInt e1 
  | Ecast AsSInt e1 => match type_of_hfexpr e1 tmap with
                        | Some (Gtyp (Fsint w))
                        | Some (Gtyp (Fuint w)) => Some (Gtyp (Fsint w))
                        | Some (Gtyp Fclock) 
                        | Some (Gtyp Freset)
                        | Some (Gtyp Fasyncreset) => Some (Gtyp (Fsint 1))
                        | _ => None
                        end
  | Ecast AsClock e1 => match type_of_hfexpr e1 tmap with
                        | Some (Gtyp _) => Some (Gtyp Fclock)
                        | _ => None
                        end
  | Ecast AsAsync e1 => match type_of_hfexpr e1 tmap with
                        | Some (Gtyp _) => Some (Gtyp Fasyncreset)
                        | _ => None
                        end
  | _ => None
  end.
  
  
  (*TBD
  | Eprim_unop (Upad n) e1 => match type_of_hfexpr e1 tmap with
                              | Some (exist (Gtyp (Fsint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint (maxn w n))) I)
                              | Some (exist (Gtyp (Fuint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint (maxn w n))) I)
                              | _ => None
                              end
  | Eprim_unop (Ushl n) e1 => match type_of_hfexpr e1 tmap with
                              | Some (exist (Gtyp (Fsint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint (w + n))) I)
                              | Some (exist (Gtyp (Fuint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint (w + n))) I)
                              | _ => None
                              end
  | Eprim_unop (Ushr n) e1 => match type_of_hfexpr e1 tmap with
                              | Some (exist (Gtyp (Fsint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint (maxn (w - n) 1))) I)
                              | Some (exist (Gtyp (Fuint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint (maxn (w - n) 0))) I)
                              | _ => None
                              end
  | Eprim_unop Ucvt e1 => match type_of_hfexpr e1 tmap with
                          | Some (exist (Gtyp (Fsint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint w)) I)
                          | Some (exist (Gtyp (Fuint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint (w + 1))) I)
                          | _ => None
                          end
  | Eprim_unop Uneg e1 => match type_of_hfexpr e1 tmap with
                          | Some (exist (Gtyp (Fsint w)) _)
                          | Some (exist (Gtyp (Fuint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint (w + 1))) I)
                          | _ => None
                          end
  | Eprim_unop Unot e1 => match type_of_hfexpr e1 tmap with
                          | Some (exist (Gtyp (Fsint w)) _)
                          | Some (exist (Gtyp (Fuint w)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint w)) I)
                          | _ => None
                          end
  | Eprim_unop (Uextr n1 n2) e1 => match type_of_hfexpr e1 tmap with
                                    | Some (exist (Gtyp (Fsint w)) _)
                                    | Some (exist (Gtyp (Fuint w)) _) =>
                                        (*if (n2 <= n1) && (n1 < w) then*) Some (exist ftype_not_implicit_width (Gtyp (Fuint (n1 - n2 + 1))) I)
                                                                  (*else None*)
                                    | _ => None
                                    end
  | Eprim_unop (Uhead n) e1 => match type_of_hfexpr e1 tmap with
                                | Some (exist (Gtyp (Fsint w)) _)
                                | Some (exist (Gtyp (Fuint w)) _) =>
                                    (*if n <= w then*) Some (exist ftype_not_implicit_width (Gtyp (Fuint n)) I)
                                              (*else None*)
                                | _ => None
                                end
  | Eprim_unop (Utail n) e1 => match type_of_hfexpr e1 tmap with
                                | Some (exist (Gtyp (Fsint w)) _)
                                | Some (exist (Gtyp (Fuint w)) _) =>
                                    (*if n <= w then*) Some (exist ftype_not_implicit_width (Gtyp (Fuint (w - n))) I)
                                              (*else None*)
                                | _ => None
                                end
  | Eprim_unop _ e1 => match type_of_hfexpr e1 tmap with
                        | Some (exist (Gtyp (Fsint _)) _)
                        | Some (exist (Gtyp (Fuint _)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint 1)) I)
                        | _ => None
                        end
  | Eprim_binop (Bcomp _) e1 e2 => match type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap with
                                    | Some (exist (Gtyp (Fsint _)) _), Some (exist (Gtyp (Fsint _)) _)
                                    | Some (exist (Gtyp (Fuint _)) _), Some (exist (Gtyp (Fuint _)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint 1)) I)
                                    | _, _ => None
                                    end
  | Eprim_binop Badd e1 e2
  | Eprim_binop Bsub e1 e2 => match type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap with
                              | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint (maxn w1 w2 + 1))) I)
                              | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fsint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint (maxn w1 w2 + 1))) I)
                              | _, _ => None
                              end
  | Eprim_binop Bmul e1 e2 => match type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap with
                              | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint (w1 + w2))) I)
                              | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fsint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint (w1 + w2))) I)
                              | _, _ => None
                              end
  | Eprim_binop Bdiv e1 e2  => match type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap with
                                | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint w1)) I)
                                | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fsint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint (w1 + 1))) I)
                                | _, _ => None
                                end
  | Eprim_binop Brem e1 e2 => match type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap with
                                | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint (minn w1 w2))) I)
                                | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fsint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint (minn w1 w2))) I)
                                | _, _ => None
                                end
  | Eprim_binop Bdshl e1 e2 => match type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap with
                                | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint (2 ^ w2 + w1 - 1))) I)
                                | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fuint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint (2 ^ w2 + w1 - 1))) I)
                                | _, _ => None
                                end
  | Eprim_binop Bdshr e1 e2 => match type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap with
                                | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint w1)) I)
                                | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fuint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fsint w1)) I)
                                | _, _ => None
                                end
  | Eprim_binop Bcat e1 e2 => match type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap with
                              | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _)
                              | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fsint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint (w1 + w2))) I)
                              | _, _ => None
                              end
  | Eprim_binop Band e1 e2
  | Eprim_binop Bor e1 e2
  | Eprim_binop Bxor e1 e2 => match type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap with
                              | Some (exist (Gtyp (Fuint w1)) _), Some (exist (Gtyp (Fuint w2)) _)
                              | Some (exist (Gtyp (Fsint w1)) _), Some (exist (Gtyp (Fsint w2)) _) => Some (exist ftype_not_implicit_width (Gtyp (Fuint (maxn w1 w2))) I)
                              | _, _ => None
                              end
  | Emux c e1 e2 => match type_of_hfexpr c tmap, type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap with
                    | Some (exist (Gtyp (Fuint _)) _), Some t1, Some t2 => ftype_mux t1 t2
                    | _, _, _ => None
                    end
  (*| Evalidif c e1 => match type_of_hfexpr c tmap with
                    | Some (exist (Gtyp (Fuint 1)) _) => type_of_hfexpr e1 tmap
                    | _ => None
                    end*)
  end.*)

(* Expression evaluation, value *)
Fixpoint eval_hfexpr (e : HiF.hfexpr) (rs : VM.t hvalue) (s : VM.t hvalue) (tmap: VM.t (ftype * forient)) : option hvalue :=
  match e with
  | Econst t c => let val := match t with
                  | Fuint w1 => zext (w1 - size c) c
                  | Fsint w2 => sext (w2 - size c) c
                  | _ => c
                  end in Some (Gval val)
  | Ecast AsUInt e 
  | Ecast AsSInt e => eval_hfexpr e rs s tmap
  | Ecast AsClock e  
  | Ecast AsReset e  
  | Ecast AsAsync e => match eval_hfexpr e rs s tmap with Some (Gval val) => Some (Gval [::lsb val]) | _ => None end
  | Eprim_binop b e1 e2 =>
      match eval_hfexpr e1 rs s tmap, eval_hfexpr e2 rs s tmap, type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap with
      | Some (Gval val1), Some (Gval val2), Some (Gtyp gt1), Some (Gtyp gt2) => 
          let val := LoFirrtl.ebinop_op b gt1 gt2 val1 val2 in Some (Gval val)
      | _, _, _, _ => None
      end
  | _ => None
  end.

  (*TBD
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
          else if (((clk0val == [:: b0]) && (clkval == [:: b1])) )
              then (*(SV.upd v readv rs, SV.acc v s)*)(rs, readv)
              else ((*SV.upd v readv *)rs, [::b0])
          end
        end
    else (rs, SV.acc v s) (* inst ports & others *)
    
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
    
    end.*)

Definition eval_hfstmt (st : HiF.hfstmt) (rs : VM.t hvalue) (s : VM.t hvalue) (tmap: VM.t (ftype * forient)) : (VM.t hvalue) * (VM.t hvalue) * (VM.t (ftype * forient)) :=
  match st with
  | Sskip => (rs,s,tmap)
  | _ => (rs,s,tmap)
  end.
        (* TBD
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
        | Smem m => (rs, s, memmap)
        | Sinst inst => (rs, s, memmap) (* 在拓扑排序时始终放在每个mod的最后，用来对所有的inst更新rs/s/memory *)
        | Snode v e => let (rs0, ve) := eval_fexpr e rs s te readerls writerls data2etc memmap read_la in
                      (rs0, SV.upd v ve s, memmap)
        | Sfcnct v e2 => let (rs0, newv) := eval_fexpr e2 rs s te readerls writerls data2etc memmap read_la in 
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
        end.*)

Fixpoint eval_hfstmts (sts : HiF.hfstmt_seq) (rs : VM.t hvalue) (s : VM.t hvalue) (tmap: VM.t (ftype * forient)) : (VM.t hvalue) * (VM.t hvalue) * (VM.t (ftype * forient)) :=
  match sts with
  | Qnil => (rs, s, tmap)
  | Qcons st tl => let '(rs0, s0, tmap0) := eval_hfstmt st rs s tmap in
                eval_hfstmts tl rs0 s0 tmap0
  end.

(* TBD
Fixpoint iterate (n : nat) (inputs : VM.t hvalue) (rs : VM.t hvalue) (s : VM.t hvalue) (tmap: VM.t (ftype * forient)) : (VM.t hvalue) * (VM.t hvalue) :=
  match n with
  | 0 => (rs, s)
  | n'.+1 => let (rs0, s0) := *)