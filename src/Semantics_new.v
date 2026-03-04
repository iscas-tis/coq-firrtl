From Coq Require Import FunInd FMaps FMapAVL OrderedType ZArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat ssrint eqtype seq fintype fingraph.
From simplssrlib Require Import Types SsrOrder FSets FMaps Tactics Var Store.
From nbits Require Import NBits.
From firrtl Require Import Firrtl Env HiEnv HiFirrtl.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(*Definition indeterminate_val := from_nat 8 42. (* UInt<8>(0h42) as invalid value *)
Compute (indeterminate_val).
Compute (take 3 indeterminate_val).*)
Parameter indeterminate_val : bits.

Inductive hvalue : Type :=
  | Gval : bits -> hvalue
  | Aval : array_value -> hvalue
  | Bval : (*forall bu :*) bundle_value (*, not_Bnil bu*) -> hvalue
with array_value : Type :=
  | Anil : array_value
  | Acons : hvalue -> array_value -> array_value
with bundle_value : Type :=
  | Bnil : bundle_value
  | Bflips : var -> fflip -> hvalue -> bundle_value -> bundle_value
(*with not_Bnil (bu : bundle_value) : bool :=
  match bu with
  | Bnil => false
  | _ => true
  end*).

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
  - destruct x, y; try (right; discriminate); [left; reflexivity |].
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
  | Anil, Anil => true
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
    destruct x as [|h1 t1], y as [|h2 t2]; simpl; try (right; congruence).
    + left; done. 
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

(* makes val to be of type ft *)
Fixpoint ftext (ft : ftype) (val : hvalue) : option hvalue :=
  match ft, val with
  | Gtyp (Fuint w), Gval c => if (length c > w) then Some (Gval (take w c))
                              else Some (Gval (zext (w - size c) c))
  | Gtyp (Fsint w), Gval c => if (length c > w) then Some (Gval (take w c))
                              else Some (Gval (sext (w - size c) c))
  | Gtyp _, Gval c => if (length c > 1) then Some (Gval (take 1 c))
                              else Some (Gval (zext (1 - size c) c))
  | Atyp atyp n, Aval aval => match atypext atyp aval with
                            | Some aval' => Some (Aval aval')
                            | _ => None
                            end
  | Btyp btyp, Bval bval => match btypext btyp bval with
                            | Some bval' => Some (Bval bval')
                            | _ => None
                            end
  | _, _ => None
  end
with atypext (ft : ftype)(* element type *) (aval : array_value) : option array_value := 
  match aval with
  | Anil => Some Anil
  | Acons val tl => match ftext ft val, atypext ft tl with
                            | Some val', Some tl' => Some (Acons val' tl')
                            | _, _ => None
                            end
  end
with btypext (btyp : ffield) (bval : bundle_value) : option bundle_value :=
  match btyp, bval with
  | Fnil, Bnil => Some Bnil
  | Fflips _ _ ft ff, Bflips v f val tl => match ftext ft val, btypext ff tl with
                | Some val', Some tl' => Some (Bflips v f val' tl')
                | _, _ => None
                end
  | _, _ => None
  end.

Fixpoint ftext0 (ft : ftype) : hvalue :=
  match ft with
  | Gtyp (Fuint w) 
  | Gtyp (Fsint w) => Gval (zeros w)
  | Gtyp _ => Gval [::b0]
  | Atyp atyp n => 
      let fix atypext0 (n : nat) : array_value :=
        match n with
        | 0 => Anil
        | n'.+1 => Acons (ftext0 atyp) (atypext0 n')
        end
      in Aval (atypext0 n)
  | Btyp btyp => 
      let fix btypext0 (btyp : ffield) : bundle_value :=
        match btyp with
        | Fnil => Bnil
        | Fflips v f ft ff => Bflips v f (ftext0 ft) (btypext0 ff)
        end
      in Bval (btypext0 btyp)
  end.

Module Sem_HiF.

(* type of ref expressions *)
Fixpoint type_of_ref (r : HiF.href) (tmap : VM.t (ftype * fcomponent)) : option ftype :=
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
  | Esubaccess r _
  | Esubindex r _ => match type_of_ref r tmap with
              | Some (Atyp ty _) => Some ty
              | _ => None
              end
  end.

(* copied from ModuleGraph *)
Definition fgtyp_mux (x y : fgtyp) : option fgtyp :=
    match x, y with
    | Fuint wx, Fuint wy => Some (Fuint (Nat.max wx wy))
    | Fsint wx, Fsint wy => Some (Fsint (Nat.max wx wy))
    | Fclock, Fclock => Some Fclock
    | Freset, Freset => Some Freset
    | Fasyncreset, Fasyncreset => Some Fasyncreset
    | _, _ => None
    end.

Fixpoint ftype_mux (x y : ftype) : option ftype :=
  match x, y with
  | Gtyp tx, Gtyp ty => match fgtyp_mux tx ty with
                        | Some fgt => Some (Gtyp fgt)
                        | None => None
                        end
  | Atyp tx nx, Atyp ty ny => if (nx == ny)
                              then match ftype_mux tx ty with
                              | Some fat => Some (Atyp fat nx)
                              | None => None
                              end
                              else None
  | Btyp fx, Btyp fy => ffield_mux fx fy
  | _, _ => None
  end
with ffield_mux (f1 f2 : ffield) : option ftype :=
       match f1, f2 with
       | Fnil, Fnil => Some (Btyp Fnil)
       | Fflips v1 Nflip t1 fs1, Fflips v2 Nflip t2 fs2
         => if v1 == v2 then
               match ffield_mux fs1 fs2 with
               | Some (Btyp bf) => match ftype_mux t1 t2 with
                           | Some ft => Some (Btyp (Fflips v1 Nflip ft bf))
                           | _ => None
                           end
               | _ => None
               end
            else None
       | Fflips _ Flipped _ _, Fflips _ Flipped _ _
         => None
       | _, _ => None
       end.

Fixpoint type_of_hfexpr (e : HiF.hfexpr) (tmap: VM.t (ftype * fcomponent)) : option ftype :=
  match e with
  | Econst t bs => Some (Gtyp t)
  | Eref r => type_of_ref r tmap 
  | Ecast AsUInt e1 => match type_of_hfexpr e1 tmap with
                        | Some (Gtyp (Fsint w))
                        | Some (Gtyp (Fuint w)) => Some (Gtyp (Fuint w))
                        | Some (Gtyp Fclock) 
                        | Some (Gtyp Freset)
                        | Some (Gtyp Fasyncreset) => Some (Gtyp (Fuint 1))
                        | _ => None
                        end
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
  | Eprim_unop (Upad n) e1 => match type_of_hfexpr e1 tmap with
                              | Some (Gtyp (Fsint w)) => Some (Gtyp (Fsint (maxn w n)))
                              | Some (Gtyp (Fuint w)) => Some (Gtyp (Fuint (maxn w n)))
                              | _ => None
                              end
  | Eprim_unop (Ushl n) e1 => match type_of_hfexpr e1 tmap with
                              | Some (Gtyp (Fsint w)) => Some (Gtyp (Fsint (w + n)))
                              | Some (Gtyp (Fuint w)) => Some (Gtyp (Fuint (w + n)))
                              | _ => None
                              end
  | Eprim_unop (Ushr n) e1 => match type_of_hfexpr e1 tmap with
                              | Some (Gtyp (Fsint w)) => Some (Gtyp (Fsint (maxn (w - n) 1)))
                              | Some (Gtyp (Fuint w)) => Some (Gtyp (Fuint (maxn (w - n) 0)))
                              | _ => None
                              end
  | Eprim_unop Ucvt e1 => match type_of_hfexpr e1 tmap with
                          | Some (Gtyp (Fsint w)) => Some (Gtyp (Fsint w))
                          | Some (Gtyp (Fuint w)) => Some (Gtyp (Fsint (w + 1)))
                          | _ => None
                          end
  | Eprim_unop Uneg e1 => match type_of_hfexpr e1 tmap with
                          | Some (Gtyp (Fsint w))
                          | Some (Gtyp (Fuint w)) => Some (Gtyp (Fsint (w + 1)))
                          | _ => None
                          end
  | Eprim_unop Unot e1 => match type_of_hfexpr e1 tmap with
                          | Some (Gtyp (Fsint w))
                          | Some (Gtyp (Fuint w)) => Some (Gtyp (Fuint w))
                          | _ => None
                          end
  | Eprim_unop (Uextr n1 n2) e1 => match type_of_hfexpr e1 tmap with
                                    | Some (Gtyp (Fsint w))
                                    | Some (Gtyp (Fuint w)) =>
                                        if (n2 <= n1) && (n1 < w) then Some (Gtyp (Fuint (n1 - n2 + 1)))
                                                                  else None
                                    | _ => None
                                    end
  | Eprim_unop (Uhead n) e1 => match type_of_hfexpr e1 tmap with
                                | Some (Gtyp (Fsint w))
                                | Some (Gtyp (Fuint w)) =>
                                    if n <= w then Some (Gtyp (Fuint n))
                                              else None
                                | _ => None
                                end
  | Eprim_unop (Utail n) e1 => match type_of_hfexpr e1 tmap with
                                | Some (Gtyp (Fsint w))
                                | Some (Gtyp (Fuint w)) =>
                                    if n <= w then Some (Gtyp (Fuint (w - n)))
                                              else None
                                | _ => None
                                end
  | Eprim_unop _ e1 => match type_of_hfexpr e1 tmap with
                        | Some (Gtyp (Fsint _))
                        | Some (Gtyp (Fuint _)) => Some (Gtyp (Fuint 1))
                        | _ => None
                        end
  | Eprim_binop (Bcomp _) e1 e2 => match type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap with
                                    | Some (Gtyp (Fsint _)), Some (Gtyp (Fsint _))
                                    | Some (Gtyp (Fuint _)), Some (Gtyp (Fuint _)) => Some (Gtyp (Fuint 1))
                                    | _, _ => None
                                    end
  | Eprim_binop Badd e1 e2
  | Eprim_binop Bsub e1 e2 => match type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap with
                              | Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint w2)) => Some (Gtyp (Fuint (maxn w1 w2 + 1)))
                              | Some (Gtyp (Fsint w1)), Some (Gtyp (Fsint w2)) => Some (Gtyp (Fsint (maxn w1 w2 + 1)))
                              | _, _ => None
                              end
  | Eprim_binop Bmul e1 e2 => match type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap with
                              | Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint w2)) => Some (Gtyp (Fuint (w1 + w2)))
                              | Some (Gtyp (Fsint w1)), Some (Gtyp (Fsint w2)) => Some (Gtyp (Fsint (w1 + w2)))
                              | _, _ => None
                              end
  | Eprim_binop Bdiv e1 e2  => match type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap with
                                | Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint w2)) => Some (Gtyp (Fuint w1))
                                | Some (Gtyp (Fsint w1)), Some (Gtyp (Fsint w2)) => Some (Gtyp (Fsint (w1 + 1)))
                                | _, _ => None
                                end
  | Eprim_binop Brem e1 e2 => match type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap with
                                | Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint w2)) => Some (Gtyp (Fuint (minn w1 w2)))
                                | Some (Gtyp (Fsint w1)), Some (Gtyp (Fsint w2)) => Some (Gtyp (Fsint (minn w1 w2)))
                                | _, _ => None
                                end
  | Eprim_binop Bdshl e1 e2 => match type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap with
                                | Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint w2)) => Some (Gtyp (Fuint (2 ^ w2 + w1 - 1)))
                                | Some (Gtyp (Fsint w1)), Some (Gtyp (Fuint w2)) => Some (Gtyp (Fsint (2 ^ w2 + w1 - 1)))
                                | _, _ => None
                                end
  | Eprim_binop Bdshr e1 e2 => match type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap with
                                | Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint w2)) => Some (Gtyp (Fuint w1))
                                | Some (Gtyp (Fsint w1)), Some (Gtyp (Fuint w2)) => Some (Gtyp (Fsint w1))
                                | _, _ => None
                                end
  | Eprim_binop Bcat e1 e2 => match type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap with
                              | Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint w2))
                              | Some (Gtyp (Fsint w1)), Some (Gtyp (Fsint w2)) => Some (Gtyp (Fuint (w1 + w2)))
                              | _, _ => None
                              end
  | Eprim_binop Band e1 e2
  | Eprim_binop Bor e1 e2
  | Eprim_binop Bxor e1 e2 => match type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap with
                              | Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint w2))
                              | Some (Gtyp (Fsint w1)), Some (Gtyp (Fsint w2)) => Some (Gtyp (Fuint (maxn w1 w2)))
                              | _, _ => None
                              end
  | Emux c e1 e2 => match type_of_hfexpr c tmap, type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap with
                    | Some (Gtyp (Fuint _)), Some t1, Some t2 => ftype_mux t1 t2
                    | _, _, _ => None
                    end
  (*| Evalidif _ _ => None*)
  end.

(* value of ref expressions *)
Fixpoint hvalue_of_ref (r : HiF.href) (s : VM.t hvalue) (tmap: VM.t (ftype * fcomponent)) : option hvalue :=
  match r with
  | Eid v => VM.find v s
  | Esubfield r v => match hvalue_of_ref r s tmap with
              | Some (Bval fv) => let fix aux fx := (
                                          match fx with
                                          | Bflips v' f t fxs =>
                                            if (v == v') then Some t
                                            else aux fxs
                                          | Bnil => None
                                          end )
                                  in aux fv
              | _ => None
              end
  | Esubindex r n => match hvalue_of_ref r s tmap with
              | Some (Aval fv) => let fix aux fx m := (
                                          match fx, m with
                                          | Acons t fxs, m'.+1 => aux fxs m'
                                          | Acons t _, 0 => Some t 
                                          | _, _ => None
                                          end )
                                  in aux fv n
              | _ => None
              end
  | Esubaccess r e => match eval_hfexpr e s tmap, hvalue_of_ref r s tmap with 
              | Some (Gval val), Some (Aval fv) => let n := to_nat val in
                                  let fix aux fx m := (
                                          match fx, m with
                                          | Acons t fxs, m'.+1 => aux fxs m'
                                          | Acons t _, 0 => Some t 
                                          | _, _ => None
                                          end )
                                  in aux fv n
              | _, _ => None
              end
  end
(* Expression evaluation, value *)
with eval_hfexpr (exp : HiF.hfexpr) (s : VM.t hvalue) (tmap: VM.t (ftype * fcomponent)) : option hvalue :=
  match exp with
  | Econst t c => match t with
                  | Fuint w1 => if (size c) > w1 then None else Some (Gval (zext (w1 - size c) c))
                  | Fsint w2 => if (size c) > w2 then None else Some (Gval (sext (w2 - size c) c))
                  | _ => None
                  end
  | Eref r => hvalue_of_ref r s tmap
  | Ecast AsUInt e 
  | Ecast AsSInt e => eval_hfexpr e s tmap
  | Ecast AsClock e  
  | Ecast AsAsync e => match eval_hfexpr e s tmap with Some (Gval val) => Some (Gval [::lsb val]) | _ => None end
  | Eprim_binop b e1 e2 =>
      match eval_hfexpr e1 s tmap, eval_hfexpr e2 s tmap, type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap with
      | Some (Gval val1), Some (Gval val2), Some (Gtyp gt1), Some (Gtyp gt2) => 
          let val := LoFirrtl.ebinop_op b gt1 gt2 val1 val2 in Some (Gval val)
      | _, _, _, _ => None
      end
  | Eprim_unop u e =>
      match eval_hfexpr e s tmap, type_of_hfexpr e tmap with
      | Some (Gval val1), Some (Gtyp gt1) =>
          let val := LoFirrtl.eunop_op u gt1 val1 in Some (Gval val)
      | _, _ => None
      end
  | Emux c e1 e2 => 
      match eval_hfexpr c s tmap, type_of_hfexpr exp tmap, eval_hfexpr e1 s tmap, eval_hfexpr e2 s tmap with
      | Some (Gval valc), Some ft, Some val1, Some val2 => if ~~ (is_zero valc) then ftext ft val1
                                                                                else ftext ft val2
      | _, _, _, _ => None
      end
  end.

Fixpoint elements_of_ftype ft :=
  match ft with
  | Gtyp t => 1
  | Atyp t n => (elements_of_ftype t) * n + 1
  | Btyp b => elements_of_fields b + 1
  end
with elements_of_fields b :=
       match b with
       | Fnil => 0
       | Fflips v fl t fs => (elements_of_ftype t) + elements_of_fields fs
       end.

(* 内部aggr也有offset的版本 *)
Fixpoint offset_ref (r : HiF.href) (tmap: VM.t (ftype * fcomponent)) (n : nat) : option nat :=
  match r with
  | Eid v => Some n
  | Esubindex v i => match offset_ref v tmap n with
                    | Some os =>  match type_of_ref v tmap with
                                | Some (Atyp ty _) => Some (os + i * elements_of_ftype ty + 1)
                                | _ => None
                                end
                    | _ => None
                    end
  | Esubfield v f =>  match offset_ref v tmap n with
                    | Some os => match type_of_ref v tmap with
                        | Some (Btyp fs) => let fix aux fx acc :=
                            match fx with
                            | Fflips v' _ ty fxs =>
                                if (v' == f) then Some (acc + 1)
                                else aux fxs (acc + elements_of_ftype ty)
                            | Fnil => None
                            end in aux fs os
                        | _ => None
                        end
                    | None => None
                    end
  | Esubaccess r e => None
  end.

  Definition g_typ := Gtyp (Fuint 8).
  Definition a_typ := Atyp g_typ 3.
  Definition aa_typ := Atyp a_typ 3.
  Definition b_typ := Btyp (Fflips 2%num Nflip g_typ (Fflips 3%num Nflip aa_typ (Fflips 4%num Nflip g_typ Fnil))).
  Definition bb_typ := Btyp (Fflips 2%num Nflip g_typ (Fflips 3%num Nflip b_typ (Fflips 4%num Nflip g_typ Fnil))).
  Definition cenv0 := VM.empty (ftype * fcomponent).
  Definition cenv1 := CE.add 1%num (bb_typ, Node) cenv0.
  Definition eid1 := (HiF.eid 1%num).
  Definition esf12 := (HiF.esubfield eid1 2%num).
  Definition esf13 := (HiF.esubfield eid1 3%num).
  Definition esf14 := (HiF.esubfield eid1 4%num).
  Definition esf132 := (HiF.esubfield esf13 2%num).
  Definition esf133 := (HiF.esubfield esf13 3%num).
  Definition esf134 := (HiF.esubfield esf13 4%num).
  Definition esf1330 := HiF.esubindex esf133 0.
  Definition esf13300 := HiF.esubindex esf1330 0.
  Definition esf13301 := HiF.esubindex esf1330 1.
  Definition esf13302 := HiF.esubindex esf1330 2.
  Definition esf1331 := HiF.esubindex esf133 1.
  Definition esf1332 := HiF.esubindex esf133 2.
  Compute (offset_ref eid1 cenv1 0).
  Compute (offset_ref esf12 cenv1 0).
  Compute (offset_ref esf13 cenv1 0).
  Compute (offset_ref esf132 cenv1 0).
  Compute (offset_ref esf133 cenv1 0).
  Compute (offset_ref esf1330 cenv1 0).
  Compute (offset_ref esf13300 cenv1 0).
  Compute (offset_ref esf13301 cenv1 0).
  Compute (offset_ref esf13302 cenv1 0).
  Compute (offset_ref esf1331 cenv1 0).
  Compute (offset_ref esf1332 cenv1 0).
  Compute (offset_ref esf134 cenv1 0).

Fixpoint elements_of_hvalue val :=
  match val with
  | Gval _ => 1
  | Aval aval => elements_of_array_value aval + 1
  | Bval bval => elements_of_bundle_value bval + 1
  end
with elements_of_array_value aval :=
  match aval with
  | Anil => 0
  | Acons val tl => elements_of_hvalue val + elements_of_array_value tl
  end
with elements_of_bundle_value bval :=
  match bval with
  | Bnil => 0
  | Bflips _ _ t fs => elements_of_hvalue t + elements_of_bundle_value fs
  end.

(* 通过offset来找到hvalue中对应值 *)
Fixpoint find_hvalue_by_offset (val : hvalue) (offset : nat) : option bits :=
  match val, offset with
  | Gval bv, 0 => Some bv
  | Aval aval, os.+1 => find_array_value_by_offset aval os
  | Bval bval, os.+1 => find_bundle_value_by_offset bval os
  | _, _ => None
  end 
with find_array_value_by_offset (aval : array_value) (offset : nat) : option bits :=
  match aval with
  | Acons val tl => let element_size := elements_of_hvalue val in if offset >= element_size then
                    find_array_value_by_offset tl (offset - element_size)
                else find_hvalue_by_offset val offset
  | _ => None
  end
with find_bundle_value_by_offset (bval : bundle_value) (offset : nat) : option bits := 
  match bval with
  | Bflips _ _ val tl => let element_size := elements_of_hvalue val in if offset >= element_size then
                    find_bundle_value_by_offset tl (offset - element_size)
                else find_hvalue_by_offset val offset
  | _ => None
  end.

(* 通过offset来修改hvalue中的对应值 *)
Fixpoint update_hvalue_by_offset (val : hvalue) (offset : nat) (new_val : hvalue) : option hvalue :=
  match val, offset with
  | _, 0 => Some new_val
  | Gval _, _ => None
  | Aval aval, os.+1 => 
                match update_array_value_by_offset aval os new_val with
                | Some aval' => Some (Aval aval')
                | _ => None
                end
  | Bval bval, os.+1 => 
                match update_bundle_value_by_offset bval os new_val with
                | Some bval' => Some (Bval bval')
                | _ => None
                end
  end 
with update_array_value_by_offset (aval : array_value) (offset : nat) (new_val : hvalue) : option array_value :=
  match aval with
  | Acons val tl => let element_size := elements_of_hvalue val in if offset >= element_size then
                    match update_array_value_by_offset tl (offset - element_size) new_val with
                    | Some tl' => Some (Acons val tl')
                    | _ => None
                    end 
                else match update_hvalue_by_offset val offset new_val with
                    | Some val' => Some (Acons val' tl)
                    | _ => None
                    end
  | _ => None
  end
with update_bundle_value_by_offset (bval : bundle_value) (offset : nat) (new_val : hvalue) : option bundle_value := 
  match bval with
  | Bflips v f val tl => let element_size := elements_of_hvalue val in if offset >= element_size then
                    match update_bundle_value_by_offset tl (offset - element_size) new_val with
                    | Some tl' => Some (Bflips v f val tl')
                    | _ => None
                    end 
                else match update_hvalue_by_offset val offset new_val with
                    | Some val' => Some (Bflips v f val' tl)
                    | _ => None
                    end
  | _ => None
  end.

  Definition g_val0 := Gval [::false; false].
  Definition g_val1 := Gval [::true; false].
  Definition g_val2 := Gval [::false; true].
  Definition g_val3 := Gval [::true; true].
  Definition a_val0 := Aval (Acons g_val0 (Acons g_val1 Anil)).
  Definition a_val1 := Aval (Acons g_val2 (Acons g_val3 Anil)).
  Definition aa_val := Aval (Acons a_val0 (Acons a_val1 Anil)).
  Definition b_val := Bval (Bflips 2%num Nflip g_val0 (Bflips 3%num Nflip a_val0 (Bflips 4%num Nflip g_val1 Bnil))).
  Definition bb_val := Bval (Bflips 2%num Nflip g_val2 (Bflips 3%num Nflip b_val (Bflips 4%num Nflip g_val3 Bnil))).
  Compute (find_hvalue_by_offset bb_val 8).
  Compute (update_hvalue_by_offset g_val0 0 g_val1).
  Compute (update_hvalue_by_offset a_val0 1 g_val3).
  Compute (update_hvalue_by_offset aa_val 3 g_val3).
  Compute (update_hvalue_by_offset aa_val 4 a_val0).
  Compute (update_hvalue_by_offset b_val 2 a_val1).
  Compute (update_hvalue_by_offset bb_val 4 a_val1).

Fixpoint eval_ref_connection (ft : ftype) (val_l val_r : hvalue) (offset_l offset_r : nat) : option (hvalue * hvalue) :=
  (* bidirectional connect between different components *)
  match ft with
  | Gtyp gt => match find_hvalue_by_offset val_r offset_r with
              | Some bv => match update_hvalue_by_offset val_l offset_l (Gval bv) with
                          | Some val_l' => Some (val_l', val_r)
                          | _ => None
                          end
              | _ => None
              end
  | Atyp atyp n => let element_size := elements_of_ftype atyp in
                   let fix aux m temp_l temp_r os_l os_r := (
                          match m with
                          | m'.+1 => match eval_ref_connection atyp temp_l temp_r os_l os_r with
                                    | Some (temp_l', temp_r') => aux m' temp_l' temp_r' (os_l + element_size) (os_r + element_size)
                                    | _ => None
                                    end
                          | _ => Some (temp_l, temp_r)
                          end) in aux n val_l val_r (offset_l + 1) (offset_r + 1)
  | Btyp ff => eval_bundle_connection ff val_l val_r (offset_l + 1) (offset_r + 1) 
  end
with eval_bundle_connection (ff : ffield) (val_l val_r : hvalue) (offset_l offset_r : nat) : option (hvalue * hvalue) :=
  match ff with
  | Fnil => Some (val_l, val_r)
  | Fflips _ Nflip ft tl => match eval_ref_connection ft val_l val_r offset_l offset_r with
                          | Some (val_l', val_r') => let element_size := elements_of_ftype ft in
                            eval_bundle_connection tl val_l' val_r' (offset_l + element_size) (offset_r + element_size)
                          | _ => None
                          end
  | Fflips _ Flipped ft tl => match eval_ref_connection ft val_r val_l offset_r offset_l with
                          | Some (val_r', val_l') => let element_size := elements_of_ftype ft in
                            eval_bundle_connection tl val_l' val_r' (offset_l + element_size) (offset_r + element_size)
                          | _ => None
                          end
  end.

Fixpoint eval_ref_connection1 (ft : ftype) (val : hvalue) (offset_l offset_r : nat) : option hvalue :=
  (* bidirectional connect between different sub-component inside the same component.
     It is assumed that offset_l indicates the sub-component to be written and offset_r the one to be read,
     even when they are flipped. *)
  match ft with
  | Gtyp gt => match find_hvalue_by_offset val offset_r with
              | Some bv => match update_hvalue_by_offset val offset_l (Gval bv) with
                          | Some val' => Some val'
                          | _ => None
                          end
              | _ => None
              end
  | Atyp atyp n => let element_size := elements_of_ftype atyp in
                   let fix aux m temp os_l os_r := (
                          match m with
                          | m'.+1 => match eval_ref_connection1 atyp temp os_l os_r with
                                    | Some temp' => aux m' temp' (os_l + element_size) (os_r + element_size)
                                    | _ => None
                                    end
                          | _ => Some temp
                          end) in aux n val (offset_l + 1) (offset_r + 1)
  | Btyp ff => eval_bundle_connection1 ff val (offset_l + 1) (offset_r + 1) 
  end
with eval_bundle_connection1 (ff : ffield) (val : hvalue) (offset_l offset_r : nat) : option hvalue :=
  match ff with
  | Fnil => Some val
  | Fflips _ Nflip ft tl => match eval_ref_connection1 ft val offset_l offset_r with
                          | Some val' => let element_size := elements_of_ftype ft in
                            eval_bundle_connection1 tl val' (offset_l + element_size) (offset_r + element_size)
                          | _ => None
                          end
  | Fflips _ Flipped ft tl => match eval_ref_connection1 ft val offset_r offset_l with
                          | Some val' => let element_size := elements_of_ftype ft in
                            eval_bundle_connection1 tl val' (offset_l + element_size) (offset_r + element_size)
                          | _ => None
                          end
  end.

Compute (eval_ref_connection (Gtyp (Fuint 2)) aa_val a_val1 2 2).
Compute (eval_ref_connection (Atyp (Gtyp (Fuint 2)) 2) aa_val a_val0 4 0).
Compute (eval_ref_connection (Gtyp (Fuint 2)) bb_val b_val 6 3).
Compute (eval_ref_connection (Atyp (Gtyp (Fuint 2)) 2) bb_val aa_val 4 4).
Definition bb_val0 := Bval (Bflips 2%num Nflip g_val2 (Bflips 3%num Flipped g_val1 Bnil)).
Definition bb_val1 := Bval (Bflips 2%num Nflip g_val3 (Bflips 3%num Flipped g_val0 Bnil)).
Definition bb_val2 := Bval (Bflips 2%num Nflip g_val1 (Bflips 3%num Flipped bb_val0 Bnil)).
Definition btype := Btyp (Fflips 2%num Nflip (Gtyp (Fuint 2)) (Fflips 3%num Flipped (Gtyp (Fuint 2)) Fnil)).
Compute (eval_ref_connection btype bb_val0 bb_val1 0 0).
Compute (eval_ref_connection btype bb_val2 bb_val1 2 0).
Compute (eval_ref_connection (Gtyp (Fuint 2)) b_val b_val 4 1). (* 不正确,如果同一个value内互相更新？ *)
Compute (eval_ref_connection1 (Gtyp (Fuint 2)) b_val 4 1).

Fixpoint invalidate_ft (ft : ftype) : hvalue :=
  match ft with
  | Gtyp gt => 
      let w := sizeof_fgtyp gt in 
      let w_inde := length indeterminate_val in
      if (w_inde > w) then Gval (take w indeterminate_val)
                  else Gval (zext (w - w_inde) indeterminate_val)
  | Atyp atyp n => 
      let fix invalidate_atyp (n : nat) : array_value :=
        match n with
        | 0 => Anil
        | n'.+1 => Acons (invalidate_ft atyp) (invalidate_atyp n')
        end
      in Aval (invalidate_atyp n)
  | Btyp btyp => 
      let fix invalidate_btyp (btyp : ffield) : bundle_value :=
        match btyp with
        | Fnil => Bnil
        | Fflips v f ft ff => Bflips v f (invalidate_ft ft) (invalidate_btyp ff)
        end
      in Bval (invalidate_btyp btyp)
  end.

Fixpoint eval_hfstmt (st : HiF.hfstmt) (rs ns : VM.t hvalue) (s : VM.t hvalue) (tmap: VM.t (ftype * fcomponent)) : option ((VM.t hvalue) * (VM.t hvalue)) :=
  match st with
  | Snode v e => match eval_hfexpr e s tmap with
                | Some val => Some (rs, VM.add v val ns)
                | _ => None
                end
  | Sfcnct r (Eref ref) => (* 考虑flip和aggr *) 
            match offset_ref r tmap 0, offset_ref ref tmap 0, type_of_ref r tmap with
            | Some offset_r, Some offset_ref, Some ft => 
                let base_r := HiF.base_ref r in let base_ref := HiF.base_ref ref in 
                (* 需要单独讨论连接发生在1个aggr内部 *)
                if base_r == base_ref then match VM.find base_r s with
                | Some val_base_r => match eval_ref_connection1 ft val_base_r offset_r offset_ref with
                    | Some val_base_r' => 
                        (* 讨论是否对应reg *)
                        match VM.find base_r tmap with
                        | Some (_, Register) => (* 更新rs *) Some (VM.add base_r val_base_r' rs, ns)
                        | Some _ => (* 更新s *) Some (rs, VM.add base_r val_base_r' ns)
                        | _ => None
                        end
                    | _ => None
                    end
                | _ => None
                end else
                match VM.find base_r s, VM.find base_ref s with
                | Some val_base_r, Some val_base_ref =>
                    match eval_ref_connection ft val_base_r val_base_ref offset_r offset_ref with
                    | Some (val_base_r', val_base_ref') => 
                        (* 分情况讨论r和ref是否对应reg *)
                        match VM.find base_r tmap, VM.find base_ref tmap with
                        | Some (_, Register), Some (_, Register) => (* 均更新rs *) 
                            Some (VM.add base_ref val_base_ref' (VM.add base_r val_base_r' rs), ns)
                        | Some (_, Register), Some _ => (* lhs更新rs, rhs更新s *) 
                            Some (VM.add base_r val_base_r' rs, VM.add base_ref val_base_ref' ns)
                        | Some _, Some (_, Register) => (* lhs更新s, rhs更新rs *) 
                            Some (VM.add base_ref val_base_ref' rs, VM.add base_r val_base_r' ns)
                        | Some _, Some _ => (* 均更新s *) 
                            Some (rs, VM.add base_ref val_base_ref' (VM.add base_r val_base_r' ns))
                        | _,_ => None
                        end
                    | _ => None
                    end
                | _, _ => None
                end
            | _, _, _ => None
            end
  | Sfcnct r e => (* 不考虑flip,考虑aggr,不区分mux和其他expr *)
                  match offset_ref r tmap 0, eval_hfexpr e s tmap with
                  | Some offset, Some new_val => let base_r := HiF.base_ref r in
                      match  VM.find base_r tmap with
                      | Some (ft, Register) => (* 更新rs *) 
                          match VM.find base_r s with
                          | Some val => match update_hvalue_by_offset val offset new_val with
                                      | Some val' => Some (VM.add base_r val' rs, ns)
                                      | _ => None
                                      end
                          | _ => None
                          end
                      | Some (ft, _) => (* 更新s *)
                          match VM.find base_r s with
                          | Some val => match update_hvalue_by_offset val offset new_val with
                                      | Some val' => Some (rs, VM.add base_r val' ns)
                                      | _ => None
                                      end
                          | _ => None
                          end
                      | _ => None
                      end
                  | _, _ => None
                  end 
  | Sinvalid r => (* 不考虑flip,考虑aggr *)
                  match offset_ref r tmap 0, type_of_ref r tmap with
                  | Some offset, Some ft => let new_val := invalidate_ft ft in
                      let base_r := HiF.base_ref r in
                      match VM.find base_r tmap with
                      | Some (ft, Register) => (* 更新rs *) 
                          match VM.find base_r s with
                          | Some val => match update_hvalue_by_offset val offset new_val with
                                      | Some val' => Some (VM.add base_r val' rs, ns)
                                      | _ => None
                                      end
                          | _ => None
                          end
                      | Some (ft, _) => (* 更新s *)
                          match VM.find base_r s with
                          | Some val => match update_hvalue_by_offset val offset new_val with
                                      | Some val' => Some (rs, VM.add base_r val' ns)
                                      | _ => None
                                      end
                          | _ => None
                          end
                      | _ => None
                      end
                  | _, _ => None
                  end 
  | Swhen cond ss_true ss_false => match eval_hfexpr cond s tmap with
                  | Some (Gval valc) => if ~~ (is_zero valc) then eval_hfstmts ss_true rs ns s tmap else eval_hfstmts ss_false rs ns s tmap
                  | _ => None
                  end
  | _ => Some (rs,ns)
  end
with eval_hfstmts (sts : HiF.hfstmt_seq) (rs ns : VM.t hvalue) (s : VM.t hvalue) (tmap: VM.t (ftype * fcomponent)) : option ((VM.t hvalue) * (VM.t hvalue)) :=
  match sts with
  | Qnil => Some (rs, ns)
  | Qcons st tl => match eval_hfstmt st rs ns s tmap with
                | Some (rs0, ns0) => eval_hfstmts tl rs0 ns0 s tmap
                | _ => None
                end
  end.

(* functions used to record ftype and component type *)
Fixpoint stmts_tmap' (tmap : VM.t (ftype * fcomponent)) (ss : HiF.hfstmt_seq): option (VM.t (ftype * fcomponent)) :=
  match ss with
  | Qnil => Some tmap
  | Qcons s ss' => match stmt_tmap' tmap s with
      | Some tmap' => stmts_tmap' tmap' ss'
      | None => None
      end
  end
with stmt_tmap' (tmap : VM.t (ftype * fcomponent)) (s : HiF.hfstmt) : option (VM.t (ftype * fcomponent)) :=
  match s with
  | Sskip => Some tmap
  | Sfcnct _ _ => Some tmap
  | Sinvalid _ => Some tmap
  | Swire v t => match VM.find v tmap with
      | None => Some (VM.add v (t, Wire) tmap)
      | _ => None
      end
  | Sreg v reg => match VM.find v tmap, type_of_hfexpr (clock reg) tmap with
      | None, Some _ => Some (VM.add v ((type reg), Register) tmap)
      | _, _ => None
      end
  | Snode v expr => match VM.find v tmap, type_of_hfexpr expr tmap with
                  | None, Some ft => Some (VM.add v (ft, Node) tmap)
                  | _, _ => None
                  end
  | Smem _ _ => None (* Memory not considered*)
  | Sinst _ _ => None
  | Swhen cond ss_true ss_false =>
      match type_of_hfexpr cond tmap, stmts_tmap' tmap ss_true with
      | Some (Gtyp _), Some tmap_true => stmts_tmap' tmap_true ss_false 
      | _, _ => None
      end
  end.
  
Fixpoint ports_tmap' (tmap : VM.t (ftype * fcomponent)) (pp : seq HiF.hfport) : option (VM.t (ftype * fcomponent)) :=
  match pp with
  | [::] => Some tmap
  | Finput v t :: pp' => match VM.find v tmap with
          | Some _ => None
          | None => ports_tmap' (VM.add v (t, In_port) tmap) pp'
          end
  | Foutput v t :: pp' => match VM.find v tmap with
          | Some _ => None
          | None => ports_tmap' (VM.add v (t, Out_port) tmap) pp'
          end
  end.    

Definition module_tmap (tmap : VM.t (ftype * fcomponent)) (m : HiF.hfmodule) : option (VM.t (ftype * fcomponent)) :=
  match m with
  | FInmod _ ps ss => match ports_tmap' tmap ps with
              | Some pmap => stmts_tmap' pmap ss
              | None => None
              end
  | _ => None
  end.

Fixpoint modules_tmap (tmap : VM.t (ftype * fcomponent)) (ml : seq HiF.hfmodule) : option (VM.t (ftype * fcomponent)) :=
  match ml with
  | nil => Some tmap
  | hd :: tl => match module_tmap tmap hd with
              | Some tmap' => modules_tmap tmap' tl
              | _ => None
              end
  end.

Definition circuit_tmap (c : HiF.hfcircuit) : option (VM.t (ftype * fcomponent)) :=
  match c with
  | Fcircuit v ml => modules_tmap (VM.empty (ftype * fcomponent)) ml
  end.

Fixpoint init_dclrs (ss : HiF.hfstmt_seq) (valmap : VM.t hvalue) (tmap: VM.t (ftype * fcomponent)) : VM.t hvalue := 
  match ss with
  | Qnil => valmap
  | Qcons s ss' => init_dclrs ss' (init_dclr s valmap tmap) tmap
  end
with init_dclr (s : HiF.hfstmt) (valmap : VM.t hvalue) (tmap: VM.t (ftype * fcomponent)) : VM.t hvalue := 
  match s with
  | Swire v t => VM.add v (ftext0 t) valmap
  | Snode v e => match eval_hfexpr e valmap tmap with(* e中被用到的变量应该已被赋初值0,则一定有值 *)
                | Some val => VM.add v val valmap
                | _ => valmap
                end
  | Swhen cond ss_true ss_false => init_dclrs ss_false (init_dclrs ss_true valmap tmap) tmap
  | _ => valmap
  end.

(*Fixpoint init_registers (ss : HiF.hfstmt_seq) (valmap rs : VM.t hvalue) (tmap: VM.t (ftype * fcomponent)) : VM.t hvalue := 
  match ss with
  | Qnil => rs
  | Qcons s ss' => init_registers ss' valmap (init_register s valmap rs tmap) tmap
  end
with init_register (s : HiF.hfstmt) (valmap rs : VM.t hvalue) (tmap: VM.t (ftype * fcomponent)) : VM.t hvalue := 
  match s with
  | Sreg v reg => match reset reg with
      | NRst => rs
      | Rst rst_sig rst_val => (* asyncreset only const reset value *)
          match eval_hfexpr rst_val valmap tmap with 
          | Some val => VM.add v val rs
          | _ => rs
          end
      end
  | Swhen cond ss_true ss_false =>
      match eval_hfexpr cond valmap tmap with
      | Some (Gval valc) => if ~~ (is_zero valc) then init_registers ss_true valmap rs tmap else init_registers ss_false valmap rs tmap
      | _ => rs
      end 
  | _ => rs
  end.*)

Definition update_values (rs : VM.t hvalue) (s : VM.t hvalue) : VM.t hvalue := 
  VM.fold (fun key value temps => VM.add key value temps) rs s.

Fixpoint iterate (n : nat) (func : VM.t hvalue -> VM.t hvalue -> VM.t hvalue -> VM.t (ftype * fcomponent) -> option (VM.t hvalue * VM.t hvalue))
  (s : VM.t hvalue) (tmap: VM.t (ftype * fcomponent)) : option (VM.t hvalue) :=
  match n with
  | 0 => Some s
  | n'.+1 => match func (VM.empty hvalue) (VM.empty hvalue) s tmap with
            | Some (_, ns) => (* everytime we start with an empty map to record the values to be updated in the next iteration *) 
              let s_upd := update_values ns s in
              if VM.equal (fun val1 val2 => hvalue_eqn val1 val2) s_upd s (* LFP *) then Some s_upd else iterate n' func s_upd tmap
            | _ => None
            end
  end.

Parameter n : nat. 
Definition compute_Sem (c : HiF.hfcircuit) (inputs : VM.t hvalue) (reg_init : VM.t hvalue) : option (VM.t hvalue * VM.t hvalue) :=
  (* inputs signal and register should update during a rising edge and keep during the iteration *)
  (* compute the value connected to registers according to the stable state, return it as a new reg_init for the next clock cycle *)
  (* the return value is 1) the table state of all components, 2) the to-be-updated values of all registers *)
  match circuit_tmap c, c with
  | Some tmap, Fcircuit _ [::(FInmod _ ps ss)] => 
        let s := update_values reg_init inputs in (* value of inputs and registers should keep during the iteration, wait until the next rising edge comes. *)
        let init_s := init_dclrs ss s tmap in (* only combinational components are initialized *)
        match iterate n (eval_hfstmts ss) init_s tmap with (* only combinational components are iterately computed *)
        | Some s0 => match eval_hfstmts ss (VM.empty hvalue) (VM.empty hvalue) s0 tmap with
            (* compute the registers' new value according to the stable state *)
            | Some (rs, _) => Some (s0, rs) 
            | _ => None
            end
        | _ => None
        end
  | _, _ => None
  end.
  
End Sem_HiF.

Module Sem_HiFP.

Fixpoint type_of_hfexpr (e : HiFP.hfexpr) (tmap: PVM.t (fgtyp * fcomponent)) : option fgtyp :=
  match e with
  | Econst t c => Some t
  | Eref (Eid v) => match PVM.find v tmap with
                    | Some (gt, _) => Some gt
                    | _ => None
                    end
  | Eref _ => None
  | Ecast AsUInt e1 
  | Ecast AsSInt e1 => match type_of_hfexpr e1 tmap with
                        | Some (Fsint w)
                        | Some (Fuint w) => Some (Fsint w)
                        | Some Fclock
                        | Some Freset
                        | Some Fasyncreset => Some (Fsint 1)
                        | _ => None
                        end
  | Ecast AsClock e1 => match type_of_hfexpr e1 tmap with
                        | Some _ => Some Fclock
                        | _ => None
                        end
  | Ecast AsAsync e1 => match type_of_hfexpr e1 tmap with
                        | Some _ => Some Fasyncreset
                        | _ => None
                        end
  | Eprim_unop (Upad n) e1 => match type_of_hfexpr e1 tmap with
                              | Some (Fsint w) => Some (Fsint (maxn w n))
                              | Some (Fuint w) => Some (Fuint (maxn w n))
                              | _ => None
                              end
  | Eprim_unop (Ushl n) e1 => match type_of_hfexpr e1 tmap with
                              | Some (Fsint w) => Some (Fsint (w + n))
                              | Some (Fuint w) => Some (Fuint (w + n))
                              | _ => None
                              end
  | Eprim_unop (Ushr n) e1 => match type_of_hfexpr e1 tmap with
                              | Some (Fsint w) => Some (Fsint (maxn (w - n) 1))
                              | Some (Fuint w) => Some (Fuint (maxn (w - n) 0))
                              | _ => None
                              end
  | Eprim_unop Ucvt e1 => match type_of_hfexpr e1 tmap with
                          | Some (Fsint w) => Some (Fsint w)
                          | Some (Fuint w) => Some (Fsint (w + 1))
                          | _ => None
                          end
  | Eprim_unop Uneg e1 => match type_of_hfexpr e1 tmap with
                          | Some (Fsint w)
                          | Some (Fuint w) => Some (Fsint (w + 1))
                          | _ => None
                          end
  | Eprim_unop Unot e1 => match type_of_hfexpr e1 tmap with
                          | Some (Fsint w)
                          | Some (Fuint w) => Some (Fuint w)
                          | _ => None
                          end
  | Eprim_unop (Uextr n1 n2) e1 => match type_of_hfexpr e1 tmap with
                                    | Some (Fsint w)
                                    | Some (Fuint w) =>
                                        if (n2 <= n1) && (n1 < w) then Some (Fuint (n1 - n2 + 1))
                                                                  else None
                                    | _ => None
                                    end
  | Eprim_unop (Uhead n) e1 => match type_of_hfexpr e1 tmap with
                                | Some (Fsint w)
                                | Some (Fuint w) =>
                                    if n <= w then Some (Fuint n)
                                              else None
                                | _ => None
                                end
  | Eprim_unop (Utail n) e1 => match type_of_hfexpr e1 tmap with
                                | Some (Fsint w)
                                | Some (Fuint w) =>
                                    if n <= w then Some (Fuint (w - n))
                                              else None
                                | _ => None
                                end
  | Eprim_unop _ e1 => match type_of_hfexpr e1 tmap with
                        | Some (Fsint _)
                        | Some (Fuint _) => Some (Fuint 1)
                        | _ => None
                        end
  | Eprim_binop (Bcomp _) e1 e2 => match type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap with
                                    | Some (Fsint _), Some (Fsint _)
                                    | Some (Fuint _), Some (Fuint _) => Some (Fuint 1)
                                    | _, _ => None
                                    end
  | Eprim_binop Badd e1 e2
  | Eprim_binop Bsub e1 e2 => match type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap with
                              | Some (Fuint w1), Some (Fuint w2) => Some (Fuint (maxn w1 w2 + 1))
                              | Some (Fsint w1), Some (Fsint w2) => Some (Fsint (maxn w1 w2 + 1))
                              | _, _ => None
                              end
  | Eprim_binop Bmul e1 e2 => match type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap with
                              | Some (Fuint w1), Some (Fuint w2) => Some (Fuint (w1 + w2))
                              | Some (Fsint w1), Some (Fsint w2) => Some (Fsint (w1 + w2))
                              | _, _ => None
                              end
  | Eprim_binop Bdiv e1 e2  => match type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap with
                                | Some (Fuint w1), Some (Fuint w2) => Some (Fuint w1)
                                | Some (Fsint w1), Some (Fsint w2) => Some (Fsint (w1 + 1))
                                | _, _ => None
                                end
  | Eprim_binop Brem e1 e2 => match type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap with
                                | Some (Fuint w1), Some (Fuint w2) => Some (Fuint (minn w1 w2))
                                | Some (Fsint w1), Some (Fsint w2) => Some (Fsint (minn w1 w2))
                                | _, _ => None
                                end
  | Eprim_binop Bdshl e1 e2 => match type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap with
                                | Some (Fuint w1), Some (Fuint w2) => Some (Fuint (2 ^ w2 + w1 - 1))
                                | Some (Fsint w1), Some (Fuint w2) => Some (Fsint (2 ^ w2 + w1 - 1))
                                | _, _ => None
                                end
  | Eprim_binop Bdshr e1 e2 => match type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap with
                                | Some (Fuint w1), Some (Fuint w2) => Some (Fuint w1)
                                | Some (Fsint w1), Some (Fuint w2) => Some (Fsint w1)
                                | _, _ => None
                                end
  | Eprim_binop Bcat e1 e2 => match type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap with
                              | Some (Fuint w1), Some (Fuint w2)
                              | Some (Fsint w1), Some (Fsint w2) => Some (Fuint (w1 + w2))
                              | _, _ => None
                              end
  | Eprim_binop Band e1 e2
  | Eprim_binop Bor e1 e2
  | Eprim_binop Bxor e1 e2 => match type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap with
                              | Some (Fuint w1), Some (Fuint w2)
                              | Some (Fsint w1), Some (Fsint w2) => Some (Fuint (maxn w1 w2))
                              | _, _ => None
                              end
  | Emux c e1 e2 => match type_of_hfexpr c tmap, type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap with
                    | Some (Fuint _), Some (Fuint w1), Some (Fuint w2) => Some (Fuint (maxn w1 w2))
                    | Some (Fuint _), Some (Fsint w1), Some (Fsint w2) => Some (Fsint (maxn w1 w2))
                    | _, _, _ => None
                    end
  end.

(* Expression evaluation, value *)
Fixpoint eval_hfexpr (exp : HiFP.hfexpr) (s : PVM.t bits) (tmap: PVM.t (fgtyp * fcomponent)) : option bits :=
  match exp with
  | Econst t c => match t with
                  | Fuint w1 => if (size c) > w1 then None else Some (zext (w1 - size c) c)
                  | Fsint w2 => if (size c) > w2 then None else Some (sext (w2 - size c) c)
                  | _ => None
                  end
  | Eref (Eid v) => PVM.find v s
  | Eref _ => None
  | Ecast AsUInt e 
  | Ecast AsSInt e => eval_hfexpr e s tmap
  | Ecast AsClock e  
  | Ecast AsAsync e => match eval_hfexpr e s tmap with Some val => Some [::lsb val] | _ => None end
  | Eprim_binop b e1 e2 =>
      match eval_hfexpr e1 s tmap, eval_hfexpr e2 s tmap, type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap with
      | Some val1, Some val2, Some gt1, Some gt2 => 
          let val := LoFirrtl.ebinop_op b gt1 gt2 val1 val2 in Some val
      | _, _, _, _ => None
      end
  | Eprim_unop u e =>
      match eval_hfexpr e s tmap, type_of_hfexpr e tmap with
      | Some val1, Some gt1 =>
          let val := LoFirrtl.eunop_op u gt1 val1 in Some val
      | _, _ => None
      end
  | Emux c e1 e2 => 
      match eval_hfexpr c s tmap, type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap, eval_hfexpr e1 s tmap, eval_hfexpr e2 s tmap with
      | Some valc, Some (Fuint w1), Some (Fuint w2), Some val1, Some val2 => if ~~ (is_zero valc) then Some (zext ((max w1 w2) - w1) val1)
                                                                             else Some (zext ((max w1 w2) - w2) val2)
      | Some valc, Some (Fsint w1), Some (Fsint w2), Some val1, Some val2 => if ~~ (is_zero valc) then Some (sext ((max w1 w2) - w1) val1)
                                                                             else Some (sext ((max w1 w2) - w2) val2)
      | _, _, _, _, _ => None
      end
  end.

Fixpoint eval_hfstmt (st : HiFP.hfstmt) (rs ns : PVM.t bits) (s : PVM.t bits) (tmap: PVM.t (fgtyp * fcomponent)) : option ((PVM.t bits) * (PVM.t bits)) :=
  match st with
  | Snode v e => match eval_hfexpr e s tmap with
                | Some val => Some (rs, PVM.add v val ns)
                | _ => None
                end
  | Sreg v _ => match PVM.find v s with
                | Some val => Some (PVM.add v val rs, ns)
                | _ => None
                end
  | Sfcnct (Eid r) e => match PVM.find r tmap, eval_hfexpr e s tmap with
                        | Some (_, Register), Some val => (* 更新rs *) Some (PVM.add r val rs, ns)
                        | Some _, Some val => (* 更新s *) Some (rs, PVM.add r val ns)
                        | _, _ => None
                        end
  | Sinvalid (Eid r) => let w_inde := length indeterminate_val in
                        match PVM.find r tmap with
                        | Some (gt, Register) => (* 更新rs *) 
                            let w := sizeof_fgtyp gt in 
                            if (w_inde > w) then Some (PVM.add r (take w indeterminate_val) rs, ns)
                            else Some (PVM.add r (zext (w - w_inde) indeterminate_val) rs, ns)
                        | Some (gt, _) => 
                            let w := sizeof_fgtyp gt in 
                            if (w_inde > w) then Some (rs, PVM.add r (take w indeterminate_val) ns)
                            else Some (rs, PVM.add r (zext (w - w_inde) indeterminate_val) ns)
                        | _ => None
                        end
  | Swhen cond ss_true ss_false => match eval_hfexpr cond s tmap with
                  | Some valc => if ~~ (is_zero valc) then eval_hfstmts ss_true rs ns s tmap else eval_hfstmts ss_false rs ns s tmap
                  | _ => None
                  end
  | _ => Some (rs,ns)
  end
with eval_hfstmts (sts : HiFP.hfstmt_seq) (rs ns : PVM.t bits) (s : PVM.t bits) (tmap: PVM.t (fgtyp * fcomponent)) : option ((PVM.t bits) * (PVM.t bits)) :=
  match sts with
  | Qnil => Some (rs, ns)
  | Qcons st tl => match eval_hfstmt st rs ns s tmap with
                | Some (rs0, ns0) => eval_hfstmts tl rs0 ns0 s tmap
                | _ => None
                end
  end.
  
(* functions used to record ftype and component type *)
Fixpoint stmts_tmap' (tmap : PVM.t (fgtyp * fcomponent)) (ss : HiFP.hfstmt_seq): option (PVM.t (fgtyp * fcomponent)) :=
  match ss with
  | Qnil => Some tmap
  | Qcons s ss' => match stmt_tmap' tmap s with
      | Some tmap' => stmts_tmap' tmap' ss'
      | None => None
      end
  end
with stmt_tmap' (tmap : PVM.t (fgtyp * fcomponent)) (s : HiFP.hfstmt) : option (PVM.t (fgtyp * fcomponent)) :=
  match s with
  | Sskip => Some tmap
  | Sfcnct _ _ => Some tmap
  | Sinvalid _ => Some tmap
  | Swire v (Gtyp t) => match PVM.find v tmap with
      | None => Some (PVM.add v (t, Wire) tmap)
      | _ => None
      end
  | Swire v _ => None
  | Sreg v reg => match PVM.find v tmap, type_of_hfexpr (clock reg) tmap, type reg with
      | None, Some _, Gtyp gt => Some (PVM.add v (gt, Register) tmap)
      | _, _, _ => None
      end
  | Snode v expr => match PVM.find v tmap, type_of_hfexpr expr tmap with
                  | None, Some ft => Some (PVM.add v (ft, Node) tmap)
                  | _, _ => None
                  end
  | Smem _ _ => None (* Memory not considered*)
  | Sinst _ _ => None
  | Swhen _ ss_true ss_false =>
      match stmts_tmap' tmap ss_true with
      | Some tmap_true => stmts_tmap' tmap_true ss_false 
      | _ => None
      end
  end.

Fixpoint ports_tmap' (tmap : PVM.t (fgtyp * fcomponent)) (pp : seq HiFP.hfport) : option (PVM.t (fgtyp * fcomponent)) :=
  match pp with
  | [::] => Some tmap
  | Finput v (Gtyp t) :: pp' => match PVM.find v tmap with
          | Some _ => None
          | None => ports_tmap' (PVM.add v (t, In_port) tmap) pp'
          end
  | Foutput v (Gtyp t) :: pp' => match PVM.find v tmap with
          | Some _ => None
          | None => ports_tmap' (PVM.add v (t, Out_port) tmap) pp'
          end
  | _ => None
  end.    

Definition module_tmap (tmap : PVM.t (fgtyp * fcomponent)) (m : HiFP.hfmodule) : option (PVM.t (fgtyp * fcomponent)) :=
  match m with
  | FInmod _ ps ss => match ports_tmap' tmap ps with
              | Some pmap => stmts_tmap' pmap ss
              | None => None
              end
  | _ => None
  end.

Fixpoint modules_tmap (tmap : PVM.t (fgtyp * fcomponent)) (ml : seq HiFP.hfmodule) : option (PVM.t (fgtyp * fcomponent)) :=
  match ml with
  | nil => Some tmap
  | hd :: tl => match module_tmap tmap hd with
              | Some tmap' => modules_tmap tmap' tl
              | _ => None
              end
  end.

Definition circuit_tmap (c : HiFP.hfcircuit) : option (PVM.t (fgtyp * fcomponent)) :=
  match c with
  | Fcircuit v ml => modules_tmap (PVM.empty (fgtyp * fcomponent)) ml
  end.

Fixpoint init_dclrs (ss : HiFP.hfstmt_seq) (valmap : PVM.t bits) (tmap: PVM.t (fgtyp * fcomponent)) : option (PVM.t bits) := 
  match ss with
  | Qnil => Some valmap
  | Qcons s ss' => match init_dclr s valmap tmap with
                  | Some valmap' => init_dclrs ss' valmap' tmap
                  | _ => None
                  end
  end
with init_dclr (s : HiFP.hfstmt) (valmap : PVM.t bits) (tmap: PVM.t (fgtyp * fcomponent)) : option (PVM.t bits) := 
  match s with
  | Swire v (Gtyp gt) => let w := sizeof_fgtyp gt in Some (PVM.add v (zeros w) valmap)
  | Swire v _ => None
  | Snode v e => match eval_hfexpr e valmap tmap with(* e中被用到的变量应该已被赋初值0,则一定有值 *)
                | Some val => Some (PVM.add v val valmap)
                | _ => None
                end
  | Swhen cond ss_true ss_false => match init_dclrs ss_true valmap tmap with
                | Some valmap' => init_dclrs ss_false valmap' tmap
                | _ => None
                end
  | _ => Some valmap
  end.

(*Fixpoint init_registers (ss : HiFP.hfstmt_seq) (valmap rs : PVM.t bits) (tmap: PVM.t (fgtyp * fcomponent)) : PVM.t bits := 
  match ss with
  | Qnil => rs
  | Qcons s ss' => init_registers ss' valmap (init_register s valmap rs tmap) tmap
  end
with init_register (s : HiFP.hfstmt) (valmap rs : PVM.t bits) (tmap: PVM.t (fgtyp * fcomponent)) : PVM.t bits := 
  match s with
  | Sreg v reg => match reset reg with
      | NRst => rs
      | Rst rst_sig rst_val => (* 本质这里需要区分同步/异步rst *)
          match eval_hfexpr rst_val valmap tmap with 
          | Some val => PVM.add v val rs
          | _ => rs
          end
      end
  | Swhen cond ss_true ss_false =>
      match eval_hfexpr cond valmap tmap with
      | Some valc => if ~~ (is_zero valc) then init_registers ss_true valmap rs tmap else init_registers ss_false valmap rs tmap
      | _ => rs
      end 
  | _ => rs
  end.*)

Definition update_values (rs s: PVM.t bits) : PVM.t bits := 
  PVM.fold (fun key value temps => PVM.add key value temps) rs s.

Fixpoint iterate (n : nat) (func : PVM.t bits -> PVM.t bits -> PVM.t bits -> PVM.t (fgtyp * fcomponent) -> option (PVM.t bits * PVM.t bits))
  (s : PVM.t bits) (tmap: PVM.t (fgtyp * fcomponent)) : option (PVM.t bits) :=
  match n with
  | 0 => Some s
  | n'.+1 => match func (PVM.empty bits) (PVM.empty bits) s tmap with
            | Some (_, ns) => (* everytime we start with an empty map to record the values to be updated in the next iteration *) 
              let s_upd := update_values ns s in
              (*if PVM.equal (fun val1 val2 => val1 == val2) s_upd s (* LFP *) then Some s_upd else*) iterate n' func s_upd tmap
            | _ => None
            end
  end.

Parameter n : nat. 
Definition compute_Sem (c : HiFP.hfcircuit) (inputs reg_init : PVM.t bits) : option (PVM.t bits * PVM.t bits) :=
  match circuit_tmap c, c with
  | Some tmap, Fcircuit _ [::(FInmod _ ps ss)] => 
        let s := update_values reg_init inputs in (* value of inputs and registers should keep during the iteration, wait until the next rising edge comes. *)
        match init_dclrs ss s tmap with (* only combinational components are initialized *)
        | Some init_s => match iterate n (eval_hfstmts ss) init_s tmap with
            (* only combinational components are iterately computed *)
            | Some s0 => match eval_hfstmts ss (PVM.empty bits) (PVM.empty bits) s0 tmap with
                (* compute the registers' new value according to the stable state *)
                | Some (rs, _) => Some (s0, rs) 
                | _ => None
                end
            | _ => None
            end
        | _ => None
        end
  | _, _ => None
  end.

Lemma iterate_n_is_LFP n ss init_s tmap s : iterate n (eval_hfstmts ss) init_s tmap = Some s -> 
  forall rs ns, eval_hfstmts ss (PVM.empty bits) (PVM.empty bits) s tmap = Some (rs, ns) -> 
  PVM.equal (fun val1 val2 => val1 == val2) (update_values ns s) s.
Proof.
(* TBD *)
Admitted.

Definition indeterminate_cst (gt : fgtyp) : HiFP.hfexpr := 
  let w := sizeof_fgtyp gt in 
  let w_inde := length indeterminate_val in
  if (w_inde > w) then HiFP.econst gt (take w indeterminate_val)
                  else HiFP.econst gt (zext (w - w_inde) indeterminate_val).

End Sem_HiFP.

Parameter flat_valmap : (VM.t hvalue) -> (VM.t (ftype * fcomponent)) -> PVM.t bits.

Parameter expandConnects : HiF.hfcircuit -> option HiFP.hfcircuit.

Theorem Sem_preservation_expandConnects : 
(* Proves pass expandConnects preserves the semantics *)
  forall (c : HiF.hfcircuit) (inputs reg_init : VM.t hvalue),
  match Sem_HiF.compute_Sem c inputs reg_init, Sem_HiF.circuit_tmap c with
  | Some (sem, regval), Some tmap =>
      forall (newc : HiFP.hfcircuit),
      expandConnects c = Some newc ->
      let flatten_inputs := flat_valmap inputs tmap in
      let flatten_reg_init := flat_valmap reg_init tmap in
      let flatten_sem := flat_valmap sem tmap in
      let flatten_regval := flat_valmap regval tmap in
      match Sem_HiFP.compute_Sem newc flatten_inputs flatten_reg_init with
      | Some (sem_new, regval_new) => PVM.equal (fun val1 val2 => val1 == val2) flatten_sem sem_new /\ 
                                      PVM.equal (fun val1 val2 => val1 == val2) flatten_regval regval_new
                                      (* we need to proof that 1) the stable state is equivalence,
                                                               2) the new values that registers will be updated to is equivalence. *)
      | _ => true
      end
  | _, _ => true
  end.
Proof.
Admitted.

Section ExpandWhens.

(* a type to indicate connects *)
Inductive def_expr : Type :=
| D_invalidated : fgtyp -> def_expr (* a "is invalid" statement *)
| D_fexpr : HiFP.hfexpr -> def_expr (* connected *)
.

(* equality of def_expr is decidable [because equality of hfexpr is decidable] *)
Lemma def_expr_eq_dec : forall {x y : def_expr}, {x = y} + {x <> y}.
Proof.
  decide equality.
  apply fgtyp_eq_dec.
  apply hfexpr_eq_dec.
Qed.

Definition def_expr_eqn (x y : def_expr) : bool :=
match x, y with
| D_invalidated gt1, D_invalidated gt2 => gt1 == gt2
| D_fexpr expr1, D_fexpr expr2 => expr1 == expr2
| _, _ => false
end.

Lemma def_expr_eqP : Equality.axiom def_expr_eqn.
Proof.
unfold Equality.axiom, def_expr_eqn.
intros ; induction x, y ; try (apply ReflectF ; discriminate) ; try (apply ReflectT ; reflexivity).
case Eq: (f == f0).
1-2: move /fgtyp_eqP : Eq => Eq.
apply ReflectT ; replace f0 with f ; reflexivity.
apply ReflectF ; injection ; apply Eq.
case Eq: (h == h0).
all: move /hfexpr_eqP : Eq => Eq.
apply ReflectT ; replace h0 with h ; reflexivity.
apply ReflectF ; injection ; apply Eq.
Qed.

Canonical def_expr_eqMixin := EqMixin def_expr_eqP.
Canonical def_expr_eqType := Eval hnf in EqType def_expr def_expr_eqMixin.

Definition combine_when_connections
    (* a helper function that takes two connection maps, generated
       by the two branches of a when statement, and combines them
       into one connection map containing suitable multiplexers *)
    (cond           : HiFP.hfexpr)    (* condition under which to decide whether to take the value from true_conn_map *)
    (true_conn_map  : PVM.t def_expr) (* connections made before or in the true branch *)
    (false_conn_map : PVM.t def_expr) (* connections made before or in the false branch *)
:   PVM.t def_expr
:=  PVM.map2 (fun true_expr false_expr : option def_expr =>
                      match true_expr, false_expr with
                      | Some (D_fexpr te), Some (D_fexpr fe) =>
                          if te == fe then true_expr
                          else Some (D_fexpr (Emux cond te fe))
                      | None, _ => false_expr 
                      | _, None => true_expr
                      | Some (D_invalidated gt), Some (D_fexpr fe) => Some (D_fexpr (Emux cond (Sem_HiFP.indeterminate_cst gt) fe)) 
                      | Some (D_fexpr te), Some (D_invalidated gt) => Some (D_fexpr (Emux cond te (Sem_HiFP.indeterminate_cst gt))) 
                      | Some (D_invalidated gt0), Some (D_invalidated gt1) => 
                          Some (D_fexpr (Emux cond (Sem_HiFP.indeterminate_cst gt0) (Sem_HiFP.indeterminate_cst gt1)))
                      end)
             true_conn_map false_conn_map.
(*
Definition combine_when_connections
    (* a helper function that takes two connection maps, generated
       by the two branches of a when statement, and combines them
       into one connection map containing suitable multiplexers *)
    (cond           : HiFP.hfexpr)    (* condition under which to decide whether to take the value from true_conn_map *)
    (true_conn_map  : PVM.t def_expr) (* connections made before or in the true branch *)
    (false_conn_map : PVM.t def_expr) (* connections made before or in the false branch *)
:   PVM.t def_expr
:=  PVM.map2 (fun true_expr false_expr : option def_expr =>
                      match true_expr, false_expr with
                      | Some (D_fexpr te), Some (D_fexpr fe) =>
                          if te == fe then true_expr
                          else Some (D_fexpr (Emux cond te fe))
                      | None, _ => false_expr 
                      | _, None => true_expr
                      | Some (D_invalidated gt), Some (D_fexpr fe) => match gt with
                          | Fuint _ 
                          | Fsint _ => Some (D_fexpr (Emux cond (Sem_HiFP.indeterminate_cst gt) fe)) 
                          | _ => None
                          end
                      | Some (D_fexpr te), Some (D_invalidated gt) => match gt with
                          | Fuint _ 
                          | Fsint _ => Some (D_fexpr (Emux cond te (Sem_HiFP.indeterminate_cst gt))) 
                          | _ => None
                          end
                      | Some (D_invalidated gt0), Some (D_invalidated gt1) => match gt0, gt1 with
                          | Fuint _, Fuint _  
                          | Fuint _, Fsint _  
                          | Fsint _, Fuint _  
                          | Fsint _, Fsint _ => 
                          Some (D_fexpr (Emux cond (Sem_HiFP.indeterminate_cst gt0) (Sem_HiFP.indeterminate_cst gt1)))
                          | _, _ => None
                          end
                      end)
             true_conn_map false_conn_map.
*)
Fixpoint ExpandBranches_funs
(* split a statement sequence (possibly containing when
   statements) into a connection map.  The output does not contain when statements. *)
(ss           : HiFP.hfstmt_seq)   (* sequence of statements being translated *)
(old_conn_map : PVM.t def_expr)    (* connections made by earlier statements in the sequence (used for recursion) *)
(tmap : PVM.t (fgtyp * fcomponent))
:   option (PVM.t def_expr)
(* old_conn_map, extended with the connection statements in ss *)
:=  match ss with
| Qnil => Some old_conn_map
| Qcons s ss =>
    match ExpandBranch_fun s old_conn_map tmap with
    | Some temp_conn_map =>
        ExpandBranches_funs ss temp_conn_map tmap
    | None => None
    end
end
with ExpandBranch_fun
(* split a single statement (possibly consisting of a when
   statement) into a connection map.  The output does not contain when statements. *)
(s            : HiFP.hfstmt)       (* a single statement being translated *)
(old_conn_map : PVM.t def_expr)    (* connections made by earlier statements in the sequence (used for recursion) *)
(tmap : PVM.t (fgtyp * fcomponent))
:   option (PVM.t def_expr)
(* old_conn_map, extended with the connection statements in s *)
:=  match s with
| Sskip => Some old_conn_map
| Sreg var reg =>
    match type reg with
    | Gtyp gt => Some (PVM.add var (D_fexpr (Eref (Eid var))) old_conn_map)
    | _ => None
    end
| Sfcnct (Eid var) expr => Some (PVM.add var (D_fexpr expr) old_conn_map)
| Sfcnct _ expr => None
| Sinvalid (Eid var) => match PVM.find var tmap with
  | Some (gt, _) => Some (PVM.add var (D_invalidated gt) old_conn_map)
  | _ => None
  end
| Sinvalid _ => None
| Swhen cond ss_true ss_false =>
    match ExpandBranches_funs ss_true old_conn_map tmap with
    | Some true_conn_map =>
        match ExpandBranches_funs ss_false old_conn_map tmap with
        | Some false_conn_map =>
            Some (combine_when_connections cond true_conn_map false_conn_map)
        | _ => None
        end
    | _ => None
    end
| _ => Some old_conn_map (* wire, mem, inst, node *)
end.

Definition convert_to_connect_stmt
    (* convert one entry in a map of connections to a connect statement,
       helper function for PVM.fold *)
    (v : PVM.key) (* key of the connection *)
    (d : def_expr) (* value of the connection *)
    (old_ss : HiFP.hfstmt_seq) (* old sequence of connect statements *)
:   HiFP.hfstmt_seq (* returns old_ss, extended with assigning d to v *)
:=  match d with
    | D_invalidated _ => Qcons (Sinvalid (Eid v)) old_ss
    | D_fexpr e => Qcons (Sfcnct (Eid v) e) old_ss
    end.

Fixpoint component_stmts_of (ss : HiFP.hfstmt_seq) : HiFP.hfstmt_seq :=
(* extracts from ss the statements that define components *)
match ss with
| Qnil => ss 
| Qcons s ss' => Qcat (component_stmt_of s) (component_stmts_of ss')
end
with component_stmt_of (s : HiFP.hfstmt) : HiFP.hfstmt_seq :=
match s with
| Sskip
| Sfcnct _ _
| Sinvalid _ => Qnil ProdVarOrder.T
| Swire _ _
| Sreg _ _
| Snode _ _
| Smem _ _
| Sinst _ _ => Qcons s (Qnil ProdVarOrder.T)
| Swhen _ ss_true ss_false => Qcat (component_stmts_of ss_true) (component_stmts_of ss_false)
end.

Definition convert_to_connect_stmts
    (* converts a map of connections to connect statements *)
    (conn_map : PVM.t def_expr) (* map that needs to be converted *)
:   HiFP.hfstmt_seq
:=  PVM.fold convert_to_connect_stmt conn_map (Qnil ProdVarOrder.T).

Definition ExpandWhens_fun
    (* Expand When statements in a module *)
    (m : HiFP.hfmodule) (* module that needs to be handled *)
    (tmap : PVM.t (fgtyp * fcomponent))
:   option HiFP.hfmodule (* result is either a semantically equivalent module without when statements,
                            or nothing if there was some error *)
:=  match m with
    | FInmod v pp ss =>
        match ExpandBranches_funs ss (PVM.empty def_expr) tmap with
            | Some conn_map =>
                Some (FInmod v pp (Qcat (component_stmts_of ss) (convert_to_connect_stmts conn_map)))
            | None => None
            end
    | FExmod _ _ _ => None
    end.

Definition expandWhens (c : HiFP.hfcircuit) : option HiFP.hfcircuit :=
  match c, Sem_HiFP.circuit_tmap c with
  | Fcircuit v [:: m], Some tmap => match ExpandWhens_fun m tmap with
    | Some fm => Some (Fcircuit v [:: fm])
    | _ => None
    end
  | _, _ => None
  end.

End ExpandWhens.

Definition is_connection (s : HiFP.hfstmt) := match s with
  | Sinvalid _
  | Sfcnct _ _=> true
  | _ => false
  end.

Definition is_declaration (s : HiFP.hfstmt) := match s with
  | Swire _ _
  | Sreg _ _
  | Snode _ _
  | Smem _ _
  | Sinst _ _ => true
  | _ => false
  end.

Lemma convert_to_connect_stmts_is_connection conn_map : forall s, Qin s (convert_to_connect_stmts conn_map) -> is_connection s.
Proof.
  intro. unfold convert_to_connect_stmts. 
  apply HiFP.PCELemmas.P.fold_rec ; simpl; intros.
  - done.
  - unfold convert_to_connect_stmt in *.
    destruct e; auto.
    + (* D_invalidated：添加 Sinvalid *)
      simpl in H3.
      case /orP : H3 => H3.
      * destruct s; try done.
      * apply H2; done.
    + (* D_fexpr：添加 Sfcnct *)
      simpl in H3.
      case /orP : H3 => H3.
      * destruct s; try done.
      * by apply H2.
Qed.

Lemma component_stmts_of_is_declaration ss : forall s, Qin s (component_stmts_of ss) -> is_declaration s.
Proof.
  (*induction ss as [|s ss IH]. simpl; done.
  simpl; intros. destruct s as [|v0 t|v0 r|v0 m|v0 v1|v0 e0|v0 e0|v0|c s1 s2] eqn : Hstmt; subst s; simpl in *.
  1,7,8 : apply IH; done.
  1,2,3,4,5 : case /orP : H => H; destruct s0 eqn : Hs0; try done; apply IH; done.
  admit. when *)
Admitted.

Lemma stmts_tmap_qcat pmap s1 s2 : match Sem_HiFP.stmts_tmap' pmap s1 with
  | Some tmap_true => Sem_HiFP.stmts_tmap' tmap_true s2 
  | _ => None
  end = Sem_HiFP.stmts_tmap' pmap (Qcat s1 s2).
Proof. 
  move : s1 pmap s2. elim; simpl in *; try done.
  intros hd tl IH pmap s2. destruct (Sem_HiFP.stmt_tmap' pmap hd) as [tmap'|]; try done.
Qed.

Lemma stmts_tmap_component_stmts_of_eq ss pmap : Sem_HiFP.stmts_tmap' pmap ss = Sem_HiFP.stmts_tmap' pmap (component_stmts_of ss)
with stmt_tmap_component_stmts_of_eq s pmap : Sem_HiFP.stmt_tmap' pmap s = Sem_HiFP.stmts_tmap' pmap (component_stmt_of s).
Proof.
  move : ss pmap; elim. simpl; done.
  intros hd tl IH pmap. simpl. destruct hd as [|v0 t|v0 r|v0 m|v0 v1|v0 e0|v0 e0|v0|c s1 s2] eqn : Hstmt; subst hd; simpl in *; try done.
  destruct t; try done; destruct (PVM.find v0 pmap); try done.
  destruct (PVM.find v0 pmap); try done; destruct (Sem_HiFP.type_of_hfexpr (clock r) pmap); try done; destruct r; try done; 
    destruct (HiFirrtl.type {| type := type; clock := clock; reset := reset |}); try done.
  destruct (PVM.find v0 pmap); try done; destruct (Sem_HiFP.type_of_hfexpr e0 pmap); try done.
  rewrite (stmts_tmap_component_stmts_of_eq s1). rewrite -stmts_tmap_qcat. rewrite -stmts_tmap_qcat.
  destruct (Sem_HiFP.stmts_tmap' pmap (component_stmts_of s1)) as [tmap_true|]; try done.
  rewrite (stmts_tmap_component_stmts_of_eq s2). destruct (Sem_HiFP.stmts_tmap' tmap_true (component_stmts_of s2)) as [tmap_false|]; try done.

  clear stmt_tmap_component_stmts_of_eq. destruct s as [|v0 t|v0 r|v0 m|v0 v1|v0 e0|v0 e0|v0|c s1 s2] eqn : Hstmt; subst s; simpl in *; try done.
  (* wire *)
  destruct t as [gt|a b|a b]; try done. destruct (PVM.find v0 pmap); try done.
  (* reg *)
  destruct (PVM.find v0 pmap); try done. destruct (Sem_HiFP.type_of_hfexpr (clock r) pmap); try done. destruct (type r); try done.
  (* node *)
  destruct (PVM.find v0 pmap); destruct (Sem_HiFP.type_of_hfexpr e0 pmap); try done.
  (* when *)
  rewrite stmts_tmap_component_stmts_of_eq. rewrite -stmts_tmap_qcat. destruct (Sem_HiFP.stmts_tmap' pmap (component_stmts_of s1)); try done.
Qed.

Lemma stmts_tmap_qcat_convert_to_connect_stmts_eq ss cncts pmap : (forall s, Qin s cncts -> is_connection s) ->
  Sem_HiFP.stmts_tmap' pmap (Qcat ss cncts) = Sem_HiFP.stmts_tmap' pmap ss.
Proof.
  intro. move : ss pmap. elim. simpl. intro; move : cncts H. elim. simpl; done.
  simpl; intros. assert (is_connection h). apply H0. simpl. specialize (hfstmt_eqn_refl h) as Heq. move/eqP : Heq => Heq. 
    specialize (hfstmt_eqP h h) as Heq'. apply reflect_iff in Heq'. apply Heq' in Heq. rewrite Heq orb_true_l //.
    destruct h; try done. simpl; apply H. intros; apply H0. rewrite H2 orb_true_r //.
    simpl; apply H. intros; apply H0. rewrite H2 orb_true_r //.
  simpl; intros. destruct (Sem_HiFP.stmt_tmap' pmap h); try done.
Qed.

Lemma ExpandWhens_fun_tmap_eq m tmap : Sem_HiFP.module_tmap (PVM.empty (fgtyp * fcomponent)) m = Some tmap -> 
  forall fm, ExpandWhens_fun m tmap = Some fm -> Sem_HiFP.module_tmap (PVM.empty (fgtyp * fcomponent)) fm = Some tmap.
Proof.
  intros Htmap fm Hexpand. destruct m as [mv ps ss|]; try discriminate. simpl in *.
  destruct (ExpandBranches_funs ss (PVM.empty def_expr) tmap) as [conn_map|] eqn : Hexpand_branches; try discriminate.
  inversion Hexpand; subst fm; clear Hexpand. simpl.
  destruct (Sem_HiFP.ports_tmap' (PVM.empty (fgtyp * fcomponent)) ps) as [pmap|]; try discriminate.
  rewrite stmts_tmap_component_stmts_of_eq in Htmap. rewrite stmts_tmap_qcat_convert_to_connect_stmts_eq //.
  apply convert_to_connect_stmts_is_connection.
Qed.

Lemma init_dclrs_qcat valmap tmap s1 s2 : match Sem_HiFP.init_dclrs s1 valmap tmap with
  | Some valmap' => Sem_HiFP.init_dclrs s2 valmap' tmap 
  | _ => None
  end = Sem_HiFP.init_dclrs (Qcat s1 s2) valmap tmap.
Proof. 
  move : s1 tmap valmap s2. elim; simpl in *; try done.
  intros hd tl IH tmap valmap s2. destruct (Sem_HiFP.init_dclr hd valmap tmap) as [valmap'|]; try done.
Qed.

Lemma init_dclrs_component_stmts_of_eq ss valmap tmap : Sem_HiFP.init_dclrs ss valmap tmap = Sem_HiFP.init_dclrs (component_stmts_of ss) valmap tmap
with init_dclr_component_stmt_of_eq s valmap tmap : Sem_HiFP.init_dclr s valmap tmap = Sem_HiFP.init_dclrs (component_stmt_of s) valmap tmap.
Proof.
  move : ss valmap; elim. simpl; done.
  intros hd tl IH valmap. simpl. rewrite (init_dclr_component_stmt_of_eq hd). rewrite -init_dclrs_qcat.
  destruct (Sem_HiFP.init_dclrs (component_stmt_of hd) valmap tmap); try done.
  
  clear init_dclr_component_stmt_of_eq.
  destruct s as [|v0 t|v0 r|v0 m|v0 v1|v0 e0|v0 e0|v0|c s1 s2] eqn : Hstmt; subst s; simpl in *; try done.
  destruct t; try done.
  destruct (Sem_HiFP.eval_hfexpr e0 valmap tmap); try done.
  rewrite (init_dclrs_component_stmts_of_eq s1). rewrite -init_dclrs_qcat. destruct (Sem_HiFP.init_dclrs (component_stmts_of s1) valmap tmap); try done.
Qed.

Lemma init_dclrs_convert_to_connect_stmts_eq ss cncts valmap tmap : (forall s, Qin s cncts -> is_connection s) ->
  Sem_HiFP.init_dclrs (Qcat ss cncts) valmap tmap = Sem_HiFP.init_dclrs ss valmap tmap.
Proof.
  intro. move : ss valmap. elim. simpl. intro; move : cncts H. elim. simpl; done.
  simpl; intros. assert (is_connection h). apply H0. simpl. specialize (hfstmt_eqn_refl h) as Heq. move/eqP : Heq => Heq. 
    specialize (hfstmt_eqP h h) as Heq'. apply reflect_iff in Heq'. apply Heq' in Heq. rewrite Heq orb_true_l //.
    destruct h; try done. simpl; apply H. intros; apply H0. rewrite H2 orb_true_r //.
    simpl; apply H. intros; apply H0. rewrite H2 orb_true_r //.
  simpl; intros. destruct (Sem_HiFP.init_dclr h valmap tmap); try done.
Qed.

Lemma component_stmts_of_init_dclrs_eq ss valmap tmap : 
  forall conn_map, Sem_HiFP.init_dclrs (Qcat (component_stmts_of ss) (convert_to_connect_stmts conn_map)) valmap tmap = Sem_HiFP.init_dclrs ss valmap tmap.
Proof.
  intros. specialize convert_to_connect_stmts_is_connection as Hcncts. specialize (Hcncts conn_map).
  rewrite init_dclrs_convert_to_connect_stmts_eq; try done. rewrite -init_dclrs_component_stmts_of_eq //.
Qed.

(*Lemma PVM_equal_iff_find_eq (m1 m2 : PVM.t bits) : PVM.equal (fun val1 val2 : bitseq => val1 == val2) m1 m2 <-> (forall v, PVM.find v m1 = PVM.find v m2).
Proof.
Admitted.

Lemma PVM_equal_refl [A : Type] (m : PVM.t A) func: PVM.equal func m m.
Proof.
Admitted.

Lemma PVM_equal_trans (m1 m2 m3: PVM.t bits) func : PVM.equal func m1 m2 -> PVM.equal func m2 m3 -> PVM.equal func m1 m3.
Proof.
Admitted.

Lemma PVM_non_equal_trans (m1 m2 m3: PVM.t bits) func : ~ PVM.equal func m1 m2 -> PVM.equal func m2 m3 -> ~ PVM.equal func m1 m3.
Proof.
Admitted.

Lemma PVM_equal_comm (m1 m2 : PVM.t bits) func : PVM.equal func m1 m2 <-> PVM.equal func m2 m1.
Proof.
Admitted.

Lemma update_values_equal : forall ns1 ns2 s,
  PVM.equal (fun v1 v2 : bitseq => v1 == v2) ns1 ns2 ->
  PVM.equal (fun v1 v2 : bitseq => v1 == v2) (Sem_HiFP.update_values ns1 s) (Sem_HiFP.update_values ns2 s).
Proof.
Admitted.*)

Definition pvm_included (m1 m2 : PVM.t bits) : Prop :=
  forall k v1, 
    PVM.find k m1 = Some v1 -> 
    PVM.find k m2 = Some v1.

Lemma included_update_values_included : forall s1 s2 ns1 ns2,
  (*forall v, PVM.mem v s1 -> ~ PVM.mem v ns1 -> ~ PVM.mem v ns2) ->*)
  pvm_included s1 s2 -> pvm_included ns1 ns2 ->
  pvm_included (Sem_HiFP.update_values ns1 s1) (Sem_HiFP.update_values ns2 s2).
Proof. (* TBD *)
  unfold pvm_included, Sem_HiFP.update_values in *; intros s1 s2 ns1 ns2 (*Hypo*) Hinclude_s Hinclude_ns v bs Hfind. 
  assert (Hfind' : PVM.find v ns1 = Some bs \/ (PVM.find v ns1 = None /\ PVM.find v s1 = Some bs)). admit.
  destruct Hfind' as [Hfind'|Hfind'].
  - (* in ns *)
    apply Hinclude_ns in Hfind'. admit.
  - (* not in ns *)
    (* 不在ns1,但在s1的，是input或未被连接的reg，那么ns2也没有 *)
Admitted.

Definition func_type : Type := PVM.t bits -> PVM.t bits -> PVM.t bits -> PVM.t (fgtyp * fcomponent) -> option (PVM.t bits * PVM.t bits).
Definition func_type_included (fun1 fun2 : func_type) (tmap : PVM.t (fgtyp * fcomponent)) : Prop := forall (init_s1 init_s2 : PVM.t bits) (s1 s2 rs1 rs2 : PVM.t bits),
  pvm_included init_s1 init_s2 -> fun1 (PVM.empty bits) (PVM.empty bits) init_s1 tmap = Some (rs1, s1) -> fun2 (PVM.empty bits) (PVM.empty bits) init_s2 tmap = Some (rs2, s2) -> 
  (pvm_included s1 s2) /\ (pvm_included rs1 rs2).

Lemma iterate_func_included n fun1 fun2 init_s1 init_s2 tmap sem sem_new : 
  func_type_included fun1 fun2 tmap -> pvm_included init_s1 init_s2 -> Sem_HiFP.iterate n fun1 init_s1 tmap = Some sem -> Sem_HiFP.iterate n fun2 init_s2 tmap = Some sem_new -> 
  pvm_included sem sem_new.
Proof.
  intros Hfun_included. move : init_s1 init_s2 sem sem_new. 
  induction n as [|n IH]; intros init_s1 init_s2 sem sem_new Hinit_eq Hiter1 Hiter2.
  - (* Case n = 0 *)
    simpl in Hiter1, Hiter2.
    inversion Hiter1; inversion Hiter2. subst sem sem_new; done.
  - (* Case n = S n' *)
    simpl in Hiter1, Hiter2.
    destruct (fun1 (PVM.empty bits) (PVM.empty bits) init_s1 tmap) as [[rs1 ns1]|] eqn:Hcall1;
      [|discriminate].
    destruct (fun2 (PVM.empty bits) (PVM.empty bits) init_s2 tmap) as [[rs2 ns2]|] eqn:Hcall2;
      [|discriminate].
    unfold func_type_included in Hfun_included. specialize (Hfun_included init_s1 init_s2 ns1 ns2 rs1 rs2).
    specialize (Hfun_included Hinit_eq Hcall1 Hcall2). move : Hfun_included => [Hfun_included _]. 
    move : Hiter1 Hiter2; apply IH.
    move : Hinit_eq Hfun_included; apply included_update_values_included.
Qed.

Definition unique_node_dclr (ss : HiFP.hfstmt_seq) : Prop :=
  forall v e, Qin (Snode v e) ss -> (forall v' e', Qin (Snode v' e') (Qremove (Snode v e) ss) -> v <> v') /\ (forall e', ~ Qin (Sfcnct (Eid v) e') ss) /\ (forall v', Qin (Sinvalid (Eid v')) ss -> v <> v').

Definition unique_node_dclr_when (ss : HiFP.hfstmt_seq) : Prop :=
  forall v e, Qin_when (Snode v e) ss -> 
  (forall v' e', Qin_when (Snode v' e') (Qremove_when (Snode v e) ss) -> v <> v') /\ (forall e', ~ Qin_when (Sfcnct (Eid v) e') ss) /\ (forall v', Qin_when (Sinvalid (Eid v')) ss -> v <> v').

Fixpoint Qin_with_cond (s : HiFP.hfstmt) (ss : HiFP.hfstmt_seq) init_s tmap : bool :=
match ss with 
| Qnil => false
| Qcons (Swhen c s1 s2) tl => match Sem_HiFP.eval_hfexpr c init_s tmap with
    | Some valc => if (~~ is_zero valc) then (Qin_with_cond s s1 init_s tmap) || (Qin_with_cond s tl init_s tmap)
                   else (Qin_with_cond s s2 init_s tmap) || (Qin_with_cond s tl init_s tmap)
    | _ => false
    end
| Qcons h tl => (hfstmt_eqn h s) || (Qin_with_cond s tl init_s tmap)
end.

Lemma eval_hfstmts_unique_ss_find_eq ss rs0 ns0 init_s tmap rs s v : 
  (forall v' e', Qin (Snode v' e') ss -> v <> v') -> (forall e', ~ Qin (Sfcnct (Eid v) e') ss) -> (forall v', Qin (Sinvalid (Eid v')) ss -> v <> v') ->
  (forall c ss1 ss2, ~ Qin (Swhen c ss1 ss2) ss) ->
  Sem_HiFP.eval_hfstmts ss rs0 ns0 init_s tmap = Some (rs, s) -> PVM.find v s = PVM.find v ns0
with eval_hfstmt_unique_ss_find_eq st rs0 ns0 init_s tmap rs s v : match st with
  | Snode v' _ => v <> v'
  | Sfcnct (Eid v') _ => v <> v'
  | Sinvalid (Eid v') => v <> v'
  | Swhen _ _ _ => false
  | _ => True
  end ->
  Sem_HiFP.eval_hfstmt st rs0 ns0 init_s tmap = Some (rs, s) -> PVM.find v s = PVM.find v ns0.
Proof.
  clear eval_hfstmts_unique_ss_find_eq. move : ss rs0 ns0. elim. simpl; intros. inversion H3; subst s; done.
  intros hd tl IH. simpl; intros rs0 ns0 Hnode Hcnct Hinvalid Hwhen Hevals. destruct (Sem_HiFP.eval_hfstmt hd rs0 ns0 init_s tmap) as [[rs1 ns1]|] eqn : Heval; try discriminate.
  apply IH in Hevals; clear IH. rewrite Hevals. move : Heval; apply eval_hfstmt_unique_ss_find_eq.
  case Hst : hd => [||var reg|||var node_e|ref e|ref|cond ss_true ss_false]; subst hd; try done.
  - (* node *) move : Hnode; clear. intro. apply (Hnode _ node_e). simpl. rewrite eq_refl. rewrite eq_refl //.
  - (* cnct *) move : Hcnct; clear. intros. specialize (Hcnct e). destruct ref; try done. move : Hcnct; apply contra_not. intro; subst v. 
    simpl. rewrite eq_refl. rewrite eq_refl //.
  - (* invalid *) move : Hinvalid; clear. intro. destruct ref; try done. apply Hinvalid. simpl. rewrite eq_refl orb_true_l //.
  - (* when *) specialize (Hwhen cond ss_true ss_false); simpl in Hwhen. rewrite eq_refl in Hwhen; simpl in Hwhen. 
    specialize (hfstmt_seq_eqn_refl ss_true) as Heq. move/eqP : Heq => Heq. specialize (hfstmt_seq_eqP ss_true ss_true) as Heq'. apply reflect_iff in Heq'.
    apply Heq' in Heq. rewrite Heq in Hwhen; simpl in Hwhen. clear Heq Heq'.
    specialize (hfstmt_seq_eqn_refl ss_false) as Heq. move/eqP : Heq => Heq. specialize (hfstmt_seq_eqP ss_false ss_false) as Heq'. apply reflect_iff in Heq'.
    apply Heq' in Heq. rewrite Heq in Hwhen; simpl in Hwhen. done.
  - (* node *) move : Hnode; clear. intros. apply (Hnode _ e'). rewrite H orb_true_r //.
  - (* cnct *) move : Hcnct; clear. intros. specialize (Hcnct e'). move : Hcnct; apply contra_not. intro. rewrite H orb_true_r //. 
  - (* invalid *) move : Hinvalid; clear. intros. apply Hinvalid. rewrite H orb_true_r //.
  - (* when *) intros. specialize (Hwhen c ss1 ss2). move : Hwhen; apply contra_not; intro. rewrite H orb_true_r //.

  clear eval_hfstmt_unique_ss_find_eq. case Hst : st => [||var reg|||var node_e|ref e|ref|cond ss_true ss_false]; subst st. 
  (* skip, wire *) 
  1,2,4,5 : simpl; intros _ Heval; inversion Heval; subst rs s; done.
  (* reg *)
  simpl; intros _ Heval. destruct (PVM.find var init_s); try discriminate. inversion Heval; subst rs s; done.
  (* node *)
  simpl; intros Hneq Heval. destruct (Sem_HiFP.eval_hfexpr node_e init_s tmap); try discriminate. inversion Heval; subst rs s.
  rewrite PVM.Lemmas.find_add_neq //. unfold PVM.M.SE.eq. move : Hneq; apply contra_not. intro. move /eqP : H => H. done.
  (* cnct *)
  simpl; intros Hneq Heval. destruct ref; try (inversion Heval; subst rs s; done).
  destruct (PVM.find s0 tmap) as [[gt cmpnt]|]; try discriminate. 
  destruct cmpnt; destruct (Sem_HiFP.eval_hfexpr e init_s tmap); try discriminate; try (inversion Heval; subst rs s; try done).
  1-7 : rewrite PVM.Lemmas.find_add_neq //. 1-7 : unfold PVM.M.SE.eq; move : Hneq; apply contra_not; intro; move /eqP : H => H; done.
  (* invalid *)
  simpl; intros Hneq Heval. destruct ref; try (inversion Heval; subst rs s; done).
  destruct (PVM.find s0 tmap) as [[gt cmpnt]|]; try discriminate. 
  destruct cmpnt; destruct (sizeof_fgtyp gt < length indeterminate_val); try (inversion Heval; subst rs s; try done).
  1-14 : rewrite PVM.Lemmas.find_add_neq //. 1-14 : unfold PVM.M.SE.eq; move : Hneq; apply contra_not; intro; move /eqP : H => H; done.
  (* when *) intro; done.
Qed.

Lemma eval_hfstmts_for_unique_node' ss v e : 
  Qin (Snode v e) ss -> unique_node_dclr ss -> (forall c ss1 ss2, ~ Qin (Swhen c ss1 ss2) ss) ->
  forall init_s tmap rs s, Sem_HiFP.eval_hfstmts ss (PVM.empty bits) (PVM.empty bits) init_s tmap = Some (rs, s) -> PVM.find v s = Sem_HiFP.eval_hfexpr e init_s tmap.
Proof.
  intros Hin Hunique Hwhen init_s tmap.
  assert (Hhelper : forall rs0 ns0, PVM.find v ns0 = None -> forall rs s : PVM.t bits,
    Sem_HiFP.eval_hfstmts ss rs0 ns0 init_s tmap = Some (rs, s) ->
    PVM.find v s = Sem_HiFP.eval_hfexpr e init_s tmap). {
    induction ss as [|s ss IH].
    - (* nil *)
      simpl in Hin. done.
    - simpl; intros rs0 ns0 Hnone rs s0 Heval. simpl in Hin. destruct (hfstmt_eqn s (Snode v e)) eqn : Hs.
      + clear Hin. clear IH. destruct (Sem_HiFP.eval_hfstmt s rs0 ns0 init_s tmap) as [[rs1 ns1]|] eqn : Heval_node; try discriminate.
        case Hst : s => [||var reg|||var node_e||ref|cond ss_true ss_false]; subst s; simpl in Hs; try done. simpl in Heval_node.
        destruct (Sem_HiFP.eval_hfexpr node_e init_s tmap) as [val|] eqn : Hnode_e; try discriminate. inversion Heval_node; subst rs1 ns1. clear Heval_node.
        move /andP : Hs => [Hv He]. move /eqP : Hv => Hv. move /eqP : He => He. subst var node_e. rewrite Hnode_e; clear Hnode_e.
        unfold unique_node_dclr in Hunique. assert (Hin : Qin (Snode v e) (Qcons (Snode v e) ss)) by (simpl; rewrite eq_refl; rewrite eq_refl //).
        apply Hunique in Hin; clear Hunique. move : Hin => [Hnode [Hcnct Hinvalid]]. 
        apply eval_hfstmts_unique_ss_find_eq with (v := v) in Heval. rewrite PVM.Lemmas.find_add_eq in Heval. done. apply PVM.M.SE.eq_refl.
        (* node *) simpl in Hnode. intros; apply (Hnode _ e'). rewrite eq_refl; simpl. rewrite eq_refl; simpl; done.
        (* cnct *) intro. specialize (Hcnct e'). move : Hcnct; apply contra_not. intro. simpl; rewrite H //.
        (* invalid *) intros; apply Hinvalid. simpl. done.
        (* when *) intros. specialize (Hwhen c ss1 ss2). move : Hwhen; apply contra_not; intro. simpl; done.
      + rewrite orb_false_l in Hin. 
        destruct (Sem_HiFP.eval_hfstmt s rs0 ns0 init_s tmap) as [[rs1 ns1]|] eqn : Hevals; try discriminate.
        move : Heval. apply (IH Hin). 
        move : Hunique Hs; clear.
        { unfold unique_node_dclr in *; intros.
          assert (Qin (Snode v0 e0) (Qcons s ss)). simpl. rewrite H orb_true_r //.
          specialize (Hunique _ _ H0). move : Hunique => [Hunique0 [Hunique1 Hunique2]]. split.
          intros. apply (Hunique0 _ e'). simpl. destruct (hfstmt_eqn s (Snode v0 e0)). move : H1; apply in_qremove. simpl; rewrite H1 orb_true_r //. split.
          intros. specialize (Hunique1 e'). move : Hunique1; apply contra_not.
          simpl; intros. rewrite H1 orb_true_r //.
          intros. apply Hunique2. simpl. rewrite H1 orb_true_r //. }
        { intros. specialize (Hwhen c ss1 ss2). move : Hwhen; apply contra_not; intro. simpl. rewrite H orb_true_r //. }
        { unfold unique_node_dclr in Hunique. 
          assert (Qin (Snode v e) (Qcons s ss)). simpl. rewrite Hin orb_true_r //.
          specialize (Hunique v e H).
          assert (Hwhen' : forall c ss1 ss2, ~ hfstmt_eqn s (Swhen c ss1 ss2)).
          intros. specialize (Hwhen c ss1 ss2). move : Hwhen; apply contra_not; intro. simpl. rewrite H0 orb_true_l //.
          move : Hevals Hnone Hs Hunique Hwhen'; clear; intros. destruct s as [|v0 t|v0 r|v0 m|v0 v1|v0 e0|v0 e0|v0|c ss1 ss2] eqn : Hstmt; subst s; simpl in Hevals.
          * (* skip, wire, mem, inst *)
            1,2,4,5 : inversion Hevals; subst rs1 ns1; done.
          * (* reg *)
            destruct (PVM.find v0 init_s); try discriminate.
            inversion Hevals; subst rs1 ns1; done.
          * (* node *)
            move : Hunique => [Hunique _].
            destruct (Sem_HiFP.eval_hfexpr e0 init_s tmap); try discriminate.
            inversion Hevals; subst rs1 ns1; rewrite PVM.Lemmas.find_add_neq //.
            assert (Qin (Snode v0 e0) (Qremove (Snode v e) (Qcons (Snode v0 e0) ss))). simpl; simpl in Hs; rewrite Hs. simpl. rewrite eq_refl. rewrite eq_refl. simpl; done.
            specialize (Hunique _ _ H).
            unfold PVM.M.SE.eq. move : Hunique; apply contra_not. intro. move /eqP : H0 => H0; done.
          * (* cnct *)
            move : Hunique => [_ [Hunique _]].
            destruct v0 as [ref|a|a|a] eqn : Href; try (inversion Hevals; subst rs1 ns1; done).
            destruct (PVM.find ref tmap) as [[gt cmpnt]|] eqn : Hfind; try discriminate.
            specialize (Hunique e0). assert (Hnoteq : ~ hfstmt_eqn (Sfcnct (Eid ref) e0) (Sfcnct (Eid v) e0)). 
              move : Hunique; apply contra_not. simpl; intro. rewrite H orb_true_l //.
            assert (Hneq : ~ PVM.M.SE.eq v ref). simpl in Hnoteq. rewrite eq_refl andb_true_r in Hnoteq.
              move : Hnoteq; apply contra_not. intro. unfold PVM.M.SE.eq in H. move /eqP : H => H; subst v; done.
            destruct cmpnt; destruct (Sem_HiFP.eval_hfexpr e0 init_s tmap); try discriminate.
            1-5,7-8 : inversion Hevals; subst rs1 ns1; rewrite PVM.Lemmas.find_add_neq //.
            inversion Hevals; subst rs1 ns1; done.
          * (* invalid *)
            move : Hunique => [_ [_ Hunique]].
            destruct v0 as [ref|a|a|a] eqn : Href; try (inversion Hevals; subst rs1 ns1; done).
            destruct (PVM.find ref tmap) as [[gt cmpnt]|] eqn : Hfind; try discriminate. subst v0. clear Hs.
            assert (Hnoteq : v <> ref). apply Hunique. simpl. rewrite eq_refl orb_true_l //.
            destruct cmpnt; destruct (sizeof_fgtyp gt < length indeterminate_val); inversion Hevals; subst rs1 ns1; try done.
            1-14 : rewrite PVM.Lemmas.find_add_neq //. 1-14 : unfold PVM.M.SE.eq; move : Hnoteq; apply contra_not; intro; move /eqP : H => H; done.
          * (* when *) specialize (Hwhen' c ss1 ss2); simpl in Hwhen'. rewrite eq_refl in Hwhen'; simpl in Hwhen'. 
            specialize (hfstmt_seq_eqn_refl ss1) as Heq. move/eqP : Heq => Heq. specialize (hfstmt_seq_eqP ss1 ss1) as Heq'. apply reflect_iff in Heq'.
            apply Heq' in Heq. rewrite Heq in Hwhen'; simpl in Hwhen'. clear Heq Heq'.
            specialize (hfstmt_seq_eqn_refl ss2) as Heq. move/eqP : Heq => Heq. specialize (hfstmt_seq_eqP ss2 ss2) as Heq'. apply reflect_iff in Heq'.
            apply Heq' in Heq. rewrite Heq in Hwhen'; simpl in Hwhen'. done. }
  }
  apply Hhelper. done.
Qed.

Lemma eval_hfstmts_unique_when_ss_find_eq ss rs0 ns0 init_s tmap rs s v : 
  (forall v' e', Qin_when (Snode v' e') ss -> v <> v') -> (forall e', ~ Qin_when (Sfcnct (Eid v) e') ss) -> (forall v', Qin_when (Sinvalid (Eid v')) ss -> v <> v') ->
  Sem_HiFP.eval_hfstmts ss rs0 ns0 init_s tmap = Some (rs, s) -> PVM.find v s = PVM.find v ns0
with eval_hfstmt_unique_when_ss_find_eq st rs0 ns0 init_s tmap rs s v : match st with
  | Snode v' _ => v <> v'
  | Sfcnct (Eid v') _ => v <> v'
  | Sinvalid (Eid v') => v <> v'
  | Swhen _ ss1 ss2 => 
    (forall v' e', Qin_when (Snode v' e') ss1 -> v <> v') /\ (forall e', ~ Qin_when (Sfcnct (Eid v) e') ss1) /\ (forall v', Qin_when (Sinvalid (Eid v')) ss1 -> v <> v') /\
    (forall v' e', Qin_when (Snode v' e') ss2 -> v <> v') /\ (forall e', ~ Qin_when (Sfcnct (Eid v) e') ss2) /\ (forall v', Qin_when (Sinvalid (Eid v')) ss2 -> v <> v') 
  | _ => True
  end ->
  Sem_HiFP.eval_hfstmt st rs0 ns0 init_s tmap = Some (rs, s) -> PVM.find v s = PVM.find v ns0.
Proof.
  clear eval_hfstmts_unique_when_ss_find_eq. move : ss rs0 ns0. elim. simpl; intros. inversion H2; subst s; done.
  intros hd tl IH. simpl; intros rs0 ns0 Hnode Hcnct Hinvalid Hevals. destruct (Sem_HiFP.eval_hfstmt hd rs0 ns0 init_s tmap) as [[rs1 ns1]|] eqn : Heval; try discriminate.
  apply IH in Hevals; clear IH. rewrite Hevals. move : Heval; apply eval_hfstmt_unique_when_ss_find_eq.
  case Hst : hd => [||var reg|||var node_e|ref e|ref|cond ss_true ss_false]; subst hd; try done.
  - (* node *) move : Hnode; clear. intro. apply (Hnode _ node_e). simpl. rewrite eq_refl. rewrite eq_refl //.
  - (* cnct *) move : Hcnct; clear. intros. specialize (Hcnct e). destruct ref; try done. move : Hcnct; apply contra_not. intro; subst v. 
    simpl. rewrite eq_refl. rewrite eq_refl //.
  - (* invalid *) move : Hinvalid; clear. intro. destruct ref; try done. apply Hinvalid. simpl. rewrite eq_refl orb_true_l //.
  - (* when *) split. intros; apply (Hnode _ e'). rewrite H //. split.
    intro. specialize (Hcnct e'). move : Hcnct; apply contra_not; intro. rewrite H //. split.
    intros; apply Hinvalid. rewrite H //. split.
    intros; apply (Hnode v' e'). rewrite H orb_true_r orb_true_l //. split.
    intro. specialize (Hcnct e'). move : Hcnct; apply contra_not; intro. rewrite H orb_true_r orb_true_l //.
    intros; apply Hinvalid. rewrite H orb_true_r orb_true_l //. 
    intros. apply (Hnode v' e'). rewrite H; destruct hd; try (rewrite orb_true_r; done); try (rewrite orb_true_r orb_true_l; done).
    intros. specialize (Hcnct e'). move : Hcnct; apply contra_not; intro. 
      rewrite H; destruct hd; try (rewrite orb_true_r; done); try (rewrite orb_true_r orb_true_l; done).
    intros; apply Hinvalid. rewrite H; destruct hd; try (rewrite orb_true_r; done); try (rewrite orb_true_r orb_true_l; done).

  clear eval_hfstmt_unique_when_ss_find_eq. case Hst : st => [||var reg|||var node_e|ref e|ref|cond ss_true ss_false]; subst st. 
  (* skip, wire *) 
  1,2,4,5 : simpl; intros _ Heval; inversion Heval; subst rs s; done.
  (* reg *)
  simpl; intros _ Heval. destruct (PVM.find var init_s); try discriminate. inversion Heval; subst rs s; done.
  (* node *)
  simpl; intros Hneq Heval. destruct (Sem_HiFP.eval_hfexpr node_e init_s tmap); try discriminate. inversion Heval; subst rs s.
  rewrite PVM.Lemmas.find_add_neq //. unfold PVM.M.SE.eq. move : Hneq; apply contra_not. intro. move /eqP : H => H. done.
  (* cnct *)
  simpl; intros Hneq Heval. destruct ref; try (inversion Heval; subst rs s; done).
  destruct (PVM.find s0 tmap) as [[gt cmpnt]|]; try discriminate. 
  destruct cmpnt; destruct (Sem_HiFP.eval_hfexpr e init_s tmap); try discriminate; try (inversion Heval; subst rs s; try done).
  1-7 : rewrite PVM.Lemmas.find_add_neq //. 1-7 : unfold PVM.M.SE.eq; move : Hneq; apply contra_not; intro; move /eqP : H => H; done.
  (* invalid *)
  simpl; intros Hneq Heval. destruct ref; try (inversion Heval; subst rs s; done).
  destruct (PVM.find s0 tmap) as [[gt cmpnt]|]; try discriminate. 
  destruct cmpnt; destruct (sizeof_fgtyp gt < length indeterminate_val); try (inversion Heval; subst rs s; try done).
  1-14 : rewrite PVM.Lemmas.find_add_neq //. 1-14 : unfold PVM.M.SE.eq; move : Hneq; apply contra_not; intro; move /eqP : H => H; done.
  (* when *) intros [Hnode_true [Hcnct_true [Hinvalid_true [Hnode_false [Hcnct_false Hinvalid_false]]]]] Heval. simpl in Heval.
  destruct (Sem_HiFP.eval_hfexpr cond init_s tmap) as [valc|]; try discriminate. destruct (~~ is_zero valc).
  1,2 :move : Heval; apply eval_hfstmts_unique_when_ss_find_eq; try done.
Qed.

Lemma unique_node_dclr_when_subseq s ss : unique_node_dclr_when (Qcons s ss) -> unique_node_dclr_when ss.
Proof.
  unfold unique_node_dclr_when; intros. assert (Hin : Qin_when (Snode v e) (Qcons s ss)). simpl. rewrite H0.
  destruct s; try (rewrite orb_true_r; done); try (rewrite orb_true_r orb_true_l; done).
  apply H in Hin. move : Hin => [Hnode [Hcnct Hinvalid]]. split.
  intros; apply (Hnode v' e'). simpl. destruct s; simpl; try done. destruct ((s == v) && (h == e)); try done.
  move : H1; apply Qremove_when_Qin_when. simpl; rewrite H1 orb_true_r //.
  destruct (Qin_when (Snode v e) h0). apply Qremove_when_Qin_when in H1. move : H1; apply Qin_when_Qcons.
  destruct (Qin_when (Snode v e) h1). apply Qremove_when_Qin_when in H1. move : H1; apply Qin_when_Qcons.
  move : H1; apply Qin_when_Qcons.
  split. intros. specialize (Hcnct e'). move : Hcnct; apply contra_not; intro; simpl. rewrite H1.
  destruct s; try (rewrite orb_true_r; done); try (rewrite orb_true_r orb_true_l; done).
  intros. apply Hinvalid. simpl. rewrite H1.
  destruct s; try (rewrite orb_true_r; done); try (rewrite orb_true_r orb_true_l; done).
Qed.

Lemma unique_node_dclr_when_branches c ss1 ss2 ss : unique_node_dclr_when (Qcons (Swhen c ss1 ss2) ss) -> unique_node_dclr_when ss1 /\ unique_node_dclr_when ss2.
Proof. 
  unfold unique_node_dclr_when; intros. split.
  intros. assert (Hin : Qin_when (Snode v e) (Qcons (Swhen c ss1 ss2) ss)). simpl. rewrite H0 //.
  apply H in Hin; clear H. move : Hin => [Hnode [Hcnct Hinvalid]]. split.
  intros; apply (Hnode v' e'). simpl.
  destruct (Qin_when (Snode v e) ss1). simpl. rewrite H //.
  destruct (Qin_when (Snode v e) ss2). simpl. apply Qremove_when_Qin_when in H. rewrite H //.
  simpl. apply Qremove_when_Qin_when in H. rewrite H //. split.
  intros. specialize (Hcnct e'). move : Hcnct; apply contra_not; intro; simpl. rewrite H //.
  intros. apply Hinvalid. simpl. rewrite H //.

  intros. assert (Hin : Qin_when (Snode v e) (Qcons (Swhen c ss1 ss2) ss)). simpl. rewrite H0 orb_true_r //.
  apply H in Hin; clear H. move : Hin => [Hnode [Hcnct Hinvalid]]. split.
  intros; apply (Hnode v' e'). simpl.
  destruct (Qin_when (Snode v e) ss1). simpl. apply Qremove_when_Qin_when in H. rewrite H orb_true_r //.
  destruct (Qin_when (Snode v e) ss2). simpl. rewrite H orb_true_r //.
  simpl. apply Qremove_when_Qin_when in H. rewrite H orb_true_r //. split.
  intros. specialize (Hcnct e'). move : Hcnct; apply contra_not; intro; simpl. rewrite H orb_true_r //.
  intros. apply Hinvalid. simpl. rewrite H orb_true_r //.
Qed.

Lemma Qin_with_cond2Qin_when s ss init_s tmap : Qin_with_cond s ss init_s tmap -> Qin_when s ss.
Proof.
  move : ss; elim. simpl; done.
  intros hd tl IH Hin. unfold Qin_with_cond in Hin. unfold Qin_when. 
  case Hhd : hd => [||var reg|||var node_e|ref e|ref|cond ss_true ss_false]; try rewrite -Hhd.
  1-8 : destruct (hfstmt_eqn hd s) eqn : Heq; try (rewrite orb_true_l; done). 
  1-8 : rewrite orb_false_l; subst hd; rewrite orb_false_l in Hin.
Admitted.

Lemma Qin_when_uniqie_False v e ss e' cond ss_true ss_false : (forall (v' : ProdVarOrder.T) (e' : hfexpr ProdVarOrder.T),
  Qin_when (Snode v' e')
    (Qremove_when (Snode v e) (Qcons (Swhen cond ss_true ss_false) ss)) ->
  v <> v') -> Qin_when (Snode v e) ss -> Qin_when (Snode v e') ss_true \/ Qin_when (Snode v e') ss_false -> False.
Proof.
Admitted.

Lemma eval_hfstmts_for_unique_node_helper ss v e init_s tmap : 
  Qin_with_cond (Snode v e) ss init_s tmap -> unique_node_dclr_when ss -> 
  forall rs0 ns0, PVM.find v ns0 = None -> forall rs s,
  Sem_HiFP.eval_hfstmts ss rs0 ns0 init_s tmap = Some (rs, s) ->
  PVM.find v s = Sem_HiFP.eval_hfexpr e init_s tmap
with eval_hfstmt_for_unique_node s v e init_s tmap : 
  forall rs0 ns0, PVM.find v ns0 = None -> forall rs ns,
  Sem_HiFP.eval_hfstmt s rs0 ns0 init_s tmap = Some (rs, ns) ->
  match s with
  | Swhen c ss1 ss2 => forall valc, Sem_HiFP.eval_hfexpr c init_s tmap = Some valc -> unique_node_dclr_when ss1 -> unique_node_dclr_when ss2 -> 
    if (~~ is_zero valc) then Qin_with_cond (Snode v e) ss1 init_s tmap -> PVM.find v ns = Sem_HiFP.eval_hfexpr e init_s tmap
    else Qin_with_cond (Snode v e) ss2 init_s tmap -> PVM.find v ns = Sem_HiFP.eval_hfexpr e init_s tmap
  | _ => True
  end.
Proof.
  clear eval_hfstmts_for_unique_node_helper. move : ss; elim. simpl; intros; done.
  intros s ss IH Hin Hunique rs0 ns0 Hfind rs ns Hevals.
  simpl in Hevals. destruct (Sem_HiFP.eval_hfstmt s rs0 ns0 init_s tmap) as [[rs1 ns1]|] eqn : Heval; try discriminate. simpl in Hin.
  case Hst : s => [||var reg|||var node_e|var cnct_e|var|cond ss_true ss_false]; subst s.
  + (* skip *) simpl in Heval; inversion Heval; subst rs0 ns0. move : Hevals; apply (IH Hin); try (move : Hunique; apply unique_node_dclr_when_subseq); try done.
  + (* wire *) simpl in Heval; inversion Heval; subst rs0 ns0. move : Hevals; apply (IH Hin); try (move : Hunique; apply unique_node_dclr_when_subseq); try done.
  + (* reg *) simpl in Heval. destruct (PVM.find var init_s); try discriminate.
    inversion Heval; subst rs1 ns1. move : Hevals; apply (IH Hin); try (move : Hunique; apply unique_node_dclr_when_subseq); try done.
  + (* mem *) simpl in Heval; inversion Heval; subst rs0 ns0. move : Hevals; apply (IH Hin); try (move : Hunique; apply unique_node_dclr_when_subseq); try done.
  + (* inst *) simpl in Heval; inversion Heval; subst rs0 ns0. move : Hevals; apply (IH Hin); try (move : Hunique; apply unique_node_dclr_when_subseq); try done.
  + (* node *) destruct (hfstmt_eqn (Snode var node_e) (Snode v e)) eqn : Hs. 
    - (* s is node *) clear Hin IH eval_hfstmt_for_unique_node. simpl in Hs. 
      move /andP : Hs => [Hvar Hnode_e]; move /eqP : Hvar => Hvar; move /eqP : Hnode_e => Hnode_e. subst var node_e.
      unfold unique_node_dclr_when in Hunique. assert (Hin : Qin_when (Snode v e) (Qcons (Snode v e) ss)) by (simpl; rewrite eq_refl; rewrite eq_refl //).
      apply Hunique in Hin; clear Hunique. move : Hin => [Hnode [Hcnct Hinvalid]]. 
      simpl in Hcnct. simpl in Hinvalid. simpl in Hnode; rewrite eq_refl in Hnode; simpl in Hnode. rewrite eq_refl in Hnode; simpl in Hnode.
      apply (eval_hfstmts_unique_when_ss_find_eq Hnode Hcnct Hinvalid) in Hevals.
      rewrite Hevals. simpl in Heval. destruct (Sem_HiFP.eval_hfexpr e init_s tmap); try discriminate.
      inversion Heval; subst rs1 ns1. apply PVM.Lemmas.find_add_eq; apply PVM.M.SE.eq_refl.
    - (* s is in ss *) rewrite orb_false_l in Hin.
      move : Hevals. apply (IH Hin); try (move : Hunique; apply unique_node_dclr_when_subseq). move : Hunique Hs Hin Heval Hfind; clear; intros.
      unfold unique_node_dclr_when in Hunique. apply Qin_with_cond2Qin_when in Hin. assert (Qin_when (Snode v e) (Qcons (Snode var node_e) ss)) by (simpl; rewrite Hin orb_true_r //).
      specialize (Hunique v e H).
      move : Hunique => [Hunique _]. specialize (Hunique var node_e). simpl in Heval.
      destruct (Sem_HiFP.eval_hfexpr node_e init_s tmap); try discriminate.
      inversion Heval; subst rs1 ns1; rewrite PVM.Lemmas.find_add_neq //.
      simpl in Hunique; simpl in Hs; rewrite Hs in Hunique. simpl in Hunique. 
      rewrite eq_refl in Hunique; simpl in Hunique. rewrite eq_refl in Hunique; simpl in Hunique.
      assert (true) by done. apply Hunique in H0.
      unfold PVM.M.SE.eq. move : H0; apply contra_not. intro. move /eqP : H0 => H0; done.
  + (* cnct *) simpl in Hin.
      move : Hevals. apply (IH Hin); try (move : Hunique; apply unique_node_dclr_when_subseq). 
      move : Hunique Hin Heval Hfind; clear; intros.
      unfold unique_node_dclr_when in Hunique. apply Qin_with_cond2Qin_when in Hin. assert (Qin_when (Snode v e) (Qcons (Sfcnct var cnct_e) ss)) by (simpl; done).
      specialize (Hunique v e H). simpl in Heval. destruct var as [ref|a|a|a] eqn : Href; try (inversion Heval; subst rs1 ns1; done).
      destruct (PVM.find ref tmap) as [[gt cmpnt]|] eqn : Hgt; try discriminate.
      move : Hunique => [_ [Hunique _]]. specialize (Hunique cnct_e). simpl in Hunique. rewrite eq_refl in Hunique; simpl in Hunique.
      destruct cmpnt; destruct (Sem_HiFP.eval_hfexpr cnct_e init_s tmap); try discriminate; 
      inversion Heval; subst rs1 ns1; try done. 1-7 : rewrite PVM.Lemmas.find_add_neq //.
      1-7 : unfold PVM.M.SE.eq; move : Hunique; apply contra_not; intro; move /eqP : H0 => H0; subst v; rewrite eq_refl; simpl; done.
  + (* invalid *) simpl in Hin.
      move : Hevals. apply (IH Hin); try (move : Hunique; apply unique_node_dclr_when_subseq). 
      move : Hunique Hin Heval Hfind; clear; intros.
      unfold unique_node_dclr_when in Hunique. apply Qin_with_cond2Qin_when in Hin. assert (Qin_when (Snode v e) (Qcons (Sinvalid var) ss)) by (simpl; done).
      specialize (Hunique v e H). simpl in Heval. destruct var as [ref|a|a|a] eqn : Href; try (inversion Heval; subst rs1 ns1; done).
      destruct (PVM.find ref tmap) as [[gt cmpnt]|] eqn : Hgt; try discriminate.
      move : Hunique => [_ [_ Hunique]]. specialize (Hunique ref). simpl in Hunique. rewrite eq_refl in Hunique; simpl in Hunique.
      destruct cmpnt; destruct (sizeof_fgtyp gt < length indeterminate_val); 
      try (inversion Heval; subst rs1 ns1; try done). 1-14 : rewrite PVM.Lemmas.find_add_neq //. 
      1-14 : assert (true) by done; apply Hunique in H0.
      1-14 : unfold PVM.M.SE.eq; move : H0; apply contra_not; intro; move /eqP : H0 => H0; subst v; done.
  + (* when *) specialize (eval_hfstmt_for_unique_node _ _ e _ _ _ _ Hfind _ _ Heval); simpl in eval_hfstmt_for_unique_node.
    simpl in Heval; destruct (Sem_HiFP.eval_hfexpr cond init_s tmap) as [valc|] eqn : Hc; try discriminate. specialize (eval_hfstmt_for_unique_node valc).
    destruct (~~ is_zero valc). 
    - (* go to true *)
      destruct (Qin_with_cond (Snode v e) ss_true init_s tmap) eqn : Hin_true.
      * (* node in true, not in ss *)
        clear IH Hin. rewrite -eval_hfstmt_for_unique_node; try done.
        unfold unique_node_dclr_when in Hunique. assert (Qin_when (Snode v e) (Qcons (Swhen cond ss_true ss_false) ss)). 
        apply Qin_with_cond2Qin_when in Hin_true. simpl; rewrite Hin_true orb_true_l //. apply Hunique in H. move : H => [Hnode [Hcnct Hinvalid]].
        move : Hevals; apply eval_hfstmts_unique_when_ss_find_eq.
        move : Hnode Hin_true; clear; intros. apply (Hnode v' e'). simpl. apply Qin_with_cond2Qin_when in Hin_true. rewrite Hin_true. apply Qin_when_Qcons; done.
        intros. move : (Hcnct e'); clear. apply contra_not. apply Qin_when_Qcons; done.
        intros. apply (Hinvalid v'). move : H; apply Qin_when_Qcons; done.
        1,2 : apply unique_node_dclr_when_branches in Hunique; move : Hunique => [Hunique1 Hunique2]; done.
      * (* in ss *) rewrite orb_false_l in Hin. move : Hevals; apply (IH Hin).
        move : Hunique; apply unique_node_dclr_when_subseq.
        unfold unique_node_dclr_when in Hunique. assert (Qin_when (Snode v e) (Qcons (Swhen cond ss_true ss_false) ss)). 
        apply Qin_with_cond2Qin_when in Hin. apply Qin_when_Qcons; done. apply Hunique in H. move : H => [Hnode [Hcnct Hinvalid]].
        rewrite -Hfind. move : Heval; apply eval_hfstmts_unique_when_ss_find_eq.
        move : Hnode Hin; clear; intros. intro; subst v'. apply Qin_with_cond2Qin_when in Hin. 
        assert (Qin_when (Snode v e') ss_true \/ Qin_when (Snode v e') ss_false) by (left; done).
        apply (Qin_when_uniqie_False Hnode Hin H0).
        intros. move : (Hcnct e'); clear. apply contra_not. intro; simpl. rewrite H //.
        intros. apply (Hinvalid v'). simpl. rewrite H //.
    - (* go to false *)
      destruct (Qin_with_cond (Snode v e) ss_false init_s tmap) eqn : Hin_false.
      * (* node in false, not in ss *)
        clear IH Hin. rewrite -eval_hfstmt_for_unique_node; try done.
        unfold unique_node_dclr_when in Hunique. assert (Qin_when (Snode v e) (Qcons (Swhen cond ss_true ss_false) ss)). 
        apply Qin_with_cond2Qin_when in Hin_false. simpl; rewrite Hin_false orb_true_r //. apply Hunique in H. move : H => [Hnode [Hcnct Hinvalid]].
        move : Hevals; apply eval_hfstmts_unique_when_ss_find_eq.
        move : Hnode Hin_false; clear; intros. apply (Hnode v' e'). simpl. apply Qin_with_cond2Qin_when in Hin_false. rewrite Hin_false. 
        destruct (Qin_when (Snode v e) ss_true); apply Qin_when_Qcons; done.
        intros. move : (Hcnct e'); clear. apply contra_not. apply Qin_when_Qcons; done.
        intros. apply (Hinvalid v'). move : H; apply Qin_when_Qcons; done.
        1,2 : apply unique_node_dclr_when_branches in Hunique; move : Hunique => [Hunique1 Hunique2]; done.
      * (* in ss *) rewrite orb_false_l in Hin. move : Hevals; apply (IH Hin).
        move : Hunique; apply unique_node_dclr_when_subseq.
        unfold unique_node_dclr_when in Hunique. assert (Qin_when (Snode v e) (Qcons (Swhen cond ss_true ss_false) ss)). 
        apply Qin_with_cond2Qin_when in Hin. apply Qin_when_Qcons; done. apply Hunique in H. move : H => [Hnode [Hcnct Hinvalid]].
        rewrite -Hfind. move : Heval; apply eval_hfstmts_unique_when_ss_find_eq.
        move : Hnode Hin; clear; intros. intro; subst v'. apply Qin_with_cond2Qin_when in Hin. 
        assert (Qin_when (Snode v e') ss_true \/ Qin_when (Snode v e') ss_false) by (right; done).
        apply (Qin_when_uniqie_False Hnode Hin H0).
        intros. move : (Hcnct e'); clear. apply contra_not. intro; simpl. rewrite H orb_true_r //.
        intros. apply (Hinvalid v'). simpl. rewrite H orb_true_r //.

  intros rs0 ns0 Hfind rs ns Heval. case Hst : s => [||var reg|||var node_e||ref|cond ss_true ss_false]; try done; subst s.
  simpl in Heval. intros. rewrite H in Heval. destruct (~~ is_zero valc). 
  1, 2 : intro; move : Heval; apply (eval_hfstmts_for_unique_node_helper _ _ _ _ _ H2); try done.
Admitted.

Lemma eval_hfstmts_for_unique_node ss v e init_s tmap : Qin_with_cond (Snode v e) ss init_s tmap -> unique_node_dclr_when ss -> 
  forall rs s, Sem_HiFP.eval_hfstmts ss (PVM.empty bits) (PVM.empty bits) init_s tmap = Some (rs, s) ->
  PVM.find v s = Sem_HiFP.eval_hfexpr e init_s tmap.
Proof.
  intro. intro. apply eval_hfstmts_for_unique_node_helper; try done.
Qed.

Lemma eval_hfstmt_find_eq2find_eq temp_rs temp_s temp_rs' temp_s' init_s tmap rs' s' rs s stmt v : 
  Sem_HiFP.eval_hfstmt stmt temp_rs temp_s init_s tmap = Some (rs, s) ->
  Sem_HiFP.eval_hfstmt stmt temp_rs' temp_s' init_s tmap = Some (rs', s') ->
  (PVM.find v temp_rs' = PVM.find v temp_rs -> PVM.find v rs' = PVM.find v rs) /\
  (PVM.find v temp_s' = PVM.find v temp_s -> PVM.find v s' = PVM.find v s)
with eval_hfstmts_find_eq2find_eq temp_rs temp_s temp_rs' temp_s' init_s tmap rs' s' rs s connect_stmts v : 
  Sem_HiFP.eval_hfstmts connect_stmts temp_rs temp_s init_s tmap = Some (rs, s) ->
  Sem_HiFP.eval_hfstmts connect_stmts temp_rs' temp_s' init_s tmap = Some (rs', s') ->
  (PVM.find v temp_rs' = PVM.find v temp_rs -> PVM.find v rs' = PVM.find v rs) /\
  (PVM.find v temp_s' = PVM.find v temp_s -> PVM.find v s' = PVM.find v s).
Proof.
  clear eval_hfstmt_find_eq2find_eq.
  destruct stmt as [|v0 t|v0 r|v0 m|v0 v1|v0 e0|v0 e0|v0|c s1 s2] eqn : Hstmt.
  - (* skip, wire, mem, inst *)
    1,2,4,5 : simpl; intros; inversion H; inversion H0; subst rs s rs' s'; split; try done.
  - (* reg *)
    simpl; intros. destruct (PVM.find v0 init_s) as [val|]; try discriminate.
    inversion H; inversion H0; subst rs s rs' s'. split; try done. destruct (v == v0) eqn : Heq.
    move /eqP : Heq => Heq; subst v. rewrite PVM.Lemmas.find_add_eq. rewrite PVM.Lemmas.find_add_eq //. 1,2 : apply PVM.M.SE.eq_refl.
    rewrite PVM.Lemmas.find_add_neq. rewrite PVM.Lemmas.find_add_neq. try done. 
    1,2 : unfold PVM.M.SE.eq; rewrite Heq //. 
  - (* node *)
    simpl; intros. destruct (Sem_HiFP.eval_hfexpr e0 init_s tmap) as [val|]; try discriminate.
    inversion H; inversion H0; subst rs s rs' s'. split; try done. destruct (v == v0) eqn : Heq.
    move /eqP : Heq => Heq; subst v. rewrite PVM.Lemmas.find_add_eq. rewrite PVM.Lemmas.find_add_eq //. 1,2 : apply PVM.M.SE.eq_refl.
    rewrite PVM.Lemmas.find_add_neq. rewrite PVM.Lemmas.find_add_neq. try done. 
    1,2 : unfold PVM.M.SE.eq; rewrite Heq //. 
  - (* cnct *)
    simpl; intros. destruct v0; try (inversion H; inversion H0; subst rs s rs' s'; split; try done).
    destruct (PVM.find s0 tmap) as [[gt cmpnt]|]; try discriminate. destruct cmpnt; destruct (Sem_HiFP.eval_hfexpr e0 init_s tmap); try discriminate;
    inversion H; inversion H0; subst rs s rs' s'; clear H H0; try (split; try done).
    1-8 : destruct (v == s0) eqn : Heq.
    1,3,5,7,9,11,13,15 : move /eqP : Heq => Heq; subst v; rewrite PVM.Lemmas.find_add_eq; try apply PVM.M.SE.eq_refl; rewrite PVM.Lemmas.find_add_eq //; try apply PVM.M.SE.eq_refl.
    1-8 : rewrite PVM.Lemmas.find_add_neq; unfold PVM.M.SE.eq; try rewrite Heq; try done; rewrite PVM.Lemmas.find_add_neq; unfold PVM.M.SE.eq; try rewrite Heq; try done.
  - (* invalid *)
    simpl; intros. destruct v0; try (inversion H; inversion H0; subst rs s rs' s'; split; try done).
    destruct (PVM.find s0 tmap) as [[gt cmpnt]|]; try discriminate. destruct cmpnt; destruct (sizeof_fgtyp gt < length indeterminate_val);
    inversion H; inversion H0; subst rs s rs' s'; clear H H0; try (split; try done).
    1-16 : destruct (v == s0) eqn : Heq.
    1,3,5,7,9,11,13,15,17,19,21,23,25,27,29,31 : move /eqP : Heq => Heq; subst v; rewrite PVM.Lemmas.find_add_eq; try apply PVM.M.SE.eq_refl; rewrite PVM.Lemmas.find_add_eq //; try apply PVM.M.SE.eq_refl.
    1-16 : rewrite PVM.Lemmas.find_add_neq; unfold PVM.M.SE.eq; try rewrite Heq; try done; rewrite PVM.Lemmas.find_add_neq; unfold PVM.M.SE.eq; try rewrite Heq; try done.
  - (* when *)
    simpl; intros. destruct (Sem_HiFP.eval_hfexpr c init_s tmap); try discriminate. destruct (~~ is_zero b).
    1,2 : move : H H0; apply eval_hfstmts_find_eq2find_eq.

  clear eval_hfstmts_find_eq2find_eq.
  move : connect_stmts temp_rs temp_s temp_rs' temp_s'. elim. simpl. intros. inversion H; inversion H0. subst rs s rs' s'. split; try done.
  intros hd tl IH. simpl; intros temp_rs temp_s temp_rs' temp_s' Hevals Hevals'.
  destruct (Sem_HiFP.eval_hfstmt hd temp_rs temp_s init_s tmap) as [[rs0 ns0]|] eqn : Heval; try discriminate.
  destruct (Sem_HiFP.eval_hfstmt hd temp_rs' temp_s' init_s tmap) as [[rs'0 ns'0]|] eqn : Heval'; try discriminate.
  apply (IH _ _ _ _ Hevals) in Hevals'. move : Hevals' => [Hrs Hns]. clear IH Hevals. 
  specialize (eval_hfstmt_find_eq2find_eq _ _ _ _ _ _ _ _ _ _ _ v Heval Heval') as Hhelper. move : Hhelper => [Hhelper1 Hhelper2].
  split.
  intros; apply Hrs. apply Hhelper1; done.
  intros; apply Hns. apply Hhelper2; done.
Qed.

Lemma eval_hfstmts_for_comb_only_cnct init_s tmap v component_stmts connect_stmts:
  (forall s, Qin s component_stmts -> is_declaration s) ->
  match PVM.find v tmap with
  | Some (gt, Out_port) => (forall v' e', Qin (Snode v' e') component_stmts -> v <> v') -> 
      (forall c ss1 ss2, ~ Qin (Swhen c ss1 ss2) (Qcat component_stmts connect_stmts)) ->
      forall rs s, Sem_HiFP.eval_hfstmts (Qcat component_stmts connect_stmts) (PVM.empty bits) (PVM.empty bits) init_s tmap = Some (rs, s) ->
      forall rs' s', Sem_HiFP.eval_hfstmts connect_stmts (PVM.empty bits) (PVM.empty bits) init_s tmap = Some (rs', s') -> PVM.find v s' = PVM.find v s
  | Some (gt, Wire) => (forall v' e', Qin (Snode v' e') component_stmts -> v <> v') -> 
      (forall c ss1 ss2, ~ Qin (Swhen c ss1 ss2) (Qcat component_stmts connect_stmts)) ->
      forall rs s, Sem_HiFP.eval_hfstmts (Qcat component_stmts connect_stmts) (PVM.empty bits) (PVM.empty bits) init_s tmap = Some (rs, s) ->
      forall rs' s', Sem_HiFP.eval_hfstmts connect_stmts (PVM.empty bits) (PVM.empty bits) init_s tmap = Some (rs', s') -> PVM.find v s' = PVM.find v s
  | _ => True
  end.
Proof.
  intro Hdclr. destruct (PVM.find v tmap) as [[gt cmpnt]|] eqn : Hcmpnt; try done. destruct cmpnt; try done.
  (* outport *) 
  assert (Hhelper : forall temp_rs temp_s rs s : PVM.t bits,
    (forall v' e', Qin (Snode v' e') component_stmts -> v <> v') ->
    (forall c ss1 ss2, ~ Qin (Swhen c ss1 ss2) (Qcat component_stmts connect_stmts)) ->
    Sem_HiFP.eval_hfstmts (Qcat component_stmts connect_stmts)
    temp_rs temp_s init_s tmap = 
    Some (rs, s) ->
    forall temp_rs' temp_s' rs' s' : PVM.t bits,
    PVM.find v temp_s' = PVM.find v temp_s ->
    Sem_HiFP.eval_hfstmts connect_stmts temp_rs' temp_s' init_s tmap = Some (rs', s') ->
    PVM.find v s' = PVM.find v s). {
    move : component_stmts Hdclr. elim.
    intros Hdclr temp_rs temp_s rs s Hneq Hwhen Heval temp_rs' temp_s' rs' s' Htemp Heval'. simpl in Heval. apply (eval_hfstmts_find_eq2find_eq v Heval) in Heval'.
      move : Heval' => [_ Heval']. apply Heval'; done.
    intros st ss IH Hdclr temp_rs temp_s rs s Hneq Hwhen Heval temp_rs' temp_s' rs' s' Htemp Heval'. simpl in Heval.
    case Hst : st => [||var reg|||var node_e|ref e|ref|cond ss_true ss_false]; subst st; simpl in Heval.
    1,2,4,5 : move : Heval temp_rs' temp_s' rs' s' Htemp Heval'; apply IH. 
    1,4,7,10 : intros; apply Hdclr; simpl; rewrite H orb_true_r //.
    1,3,5,7 : intros; apply (Hneq v' e'); simpl; done.
    1-4 : intros; specialize (Hwhen c ss1 ss2); move : Hwhen; apply contra_not; intro; try done.
    (* reg *)
    destruct (PVM.find var init_s); try discriminate.
    move : Heval temp_rs' temp_s' rs' s' Htemp Heval'; apply IH. intros; apply Hdclr; simpl; rewrite H orb_true_r //.
    intros; apply (Hneq v' e'); simpl; done.
    intros; specialize (Hwhen c ss1 ss2); move : Hwhen; apply contra_not; intro; try done.
    (* node *)
    destruct (Sem_HiFP.eval_hfexpr node_e init_s tmap); try discriminate.
    move : Heval'; apply IH with (temp_rs := temp_rs) (temp_s := PVM.add var b temp_s) (rs := rs); try done. intros; apply Hdclr; simpl; rewrite H orb_true_r //.
    intros; apply (Hneq v' e'); simpl; rewrite H orb_true_r; done.
    rewrite Htemp HiFP.PCELemmas.find_add_neq //. assert (v <> var). specialize (Hneq var node_e). apply Hneq. simpl. rewrite eq_refl. rewrite eq_refl. simpl; done.
    unfold PVM.M.SE.eq. move : H; apply contra_not. intro. move /eqP : H => H. done.
    (* cnct *)
    assert (Qin (Sfcnct ref e) (Qcons (Sfcnct ref e) ss)). simpl. rewrite eq_refl. rewrite eq_refl //. apply Hdclr in H. simpl in H. done.
    (* invalid *)
    assert (Qin (Sinvalid ref) (Qcons (Sinvalid ref) ss)). simpl. rewrite eq_refl //. apply Hdclr in H. simpl in H. done.
    (* when *)
    specialize (Hwhen cond ss_true ss_false). simpl in Hwhen. rewrite eq_refl in Hwhen; simpl in Hwhen. 
    specialize (hfstmt_seq_eqn_refl ss_true) as Heq. move/eqP : Heq => Heq. specialize (hfstmt_seq_eqP ss_true ss_true) as Heq'. apply reflect_iff in Heq'.
    apply Heq' in Heq. rewrite Heq in Hwhen; simpl in Hwhen. clear Heq Heq'.
    specialize (hfstmt_seq_eqn_refl ss_false) as Heq. move/eqP : Heq => Heq. specialize (hfstmt_seq_eqP ss_false ss_false) as Heq'. apply reflect_iff in Heq'.
    apply Heq' in Heq. rewrite Heq in Hwhen; simpl in Hwhen. done.
    }
  intros. move : H2. apply (Hhelper _ _ _ _ H H0 H1). done.
  (* wire *)
  assert (Hhelper : forall temp_rs temp_s rs s : PVM.t bits,
    (forall v' e', Qin (Snode v' e') component_stmts -> v <> v') ->
    (forall c ss1 ss2, ~ Qin (Swhen c ss1 ss2) (Qcat component_stmts connect_stmts)) ->
    Sem_HiFP.eval_hfstmts (Qcat component_stmts connect_stmts)
    temp_rs temp_s init_s tmap = 
    Some (rs, s) ->
    forall temp_rs' temp_s' rs' s' : PVM.t bits,
    PVM.find v temp_s' = PVM.find v temp_s ->
    Sem_HiFP.eval_hfstmts connect_stmts temp_rs' temp_s' init_s tmap = Some (rs', s') ->
    PVM.find v s' = PVM.find v s). {
    move : component_stmts Hdclr. elim.
    intros Hdclr temp_rs temp_s rs s Hneq Hwhen Heval temp_rs' temp_s' rs' s' Htemp Heval'. simpl in Heval. apply (eval_hfstmts_find_eq2find_eq v Heval) in Heval'.
      move : Heval' => [_ Heval']. apply Heval'; done.
    intros st ss IH Hdclr temp_rs temp_s rs s Hneq Hwhen Heval temp_rs' temp_s' rs' s' Htemp Heval'. simpl in Heval.
    case Hst : st => [||var reg|||var node_e|ref e|ref|cond ss_true ss_false]; subst st; simpl in Heval.
    1,2,4,5 : move : Heval temp_rs' temp_s' rs' s' Htemp Heval'; apply IH. 
    1,4,7,10 : intros; apply Hdclr; simpl; rewrite H orb_true_r //.
    1,3,5,7 : intros; apply (Hneq v' e'); simpl; done.
    1-4 : intros; specialize (Hwhen c ss1 ss2); move : Hwhen; apply contra_not; intro; try done.
    (* reg *)
    destruct (PVM.find var init_s); try discriminate.
    move : Heval temp_rs' temp_s' rs' s' Htemp Heval'; apply IH. intros; apply Hdclr; simpl; rewrite H orb_true_r //.
    intros; apply (Hneq v' e'); simpl; done.
    intros; specialize (Hwhen c ss1 ss2); move : Hwhen; apply contra_not; intro; try done.
    (* node *)
    destruct (Sem_HiFP.eval_hfexpr node_e init_s tmap); try discriminate.
    move : Heval'; apply IH with (temp_rs := temp_rs) (temp_s := PVM.add var b temp_s) (rs := rs); try done. intros; apply Hdclr; simpl; rewrite H orb_true_r //.
    intros; apply (Hneq v' e'); simpl; rewrite H orb_true_r; done.
    rewrite Htemp HiFP.PCELemmas.find_add_neq //. assert (v <> var). specialize (Hneq var node_e). apply Hneq. simpl. rewrite eq_refl. rewrite eq_refl. simpl; done.
    unfold PVM.M.SE.eq. move : H; apply contra_not. intro. move /eqP : H => H. done.
    (* cnct *)
    assert (Qin (Sfcnct ref e) (Qcons (Sfcnct ref e) ss)). simpl. rewrite eq_refl. rewrite eq_refl //. apply Hdclr in H. simpl in H. done.
    (* invalid *)
    assert (Qin (Sinvalid ref) (Qcons (Sinvalid ref) ss)). simpl. rewrite eq_refl //. apply Hdclr in H. simpl in H. done.
    (* when *)
    specialize (Hwhen cond ss_true ss_false). simpl in Hwhen. rewrite eq_refl in Hwhen; simpl in Hwhen. 
    specialize (hfstmt_seq_eqn_refl ss_true) as Heq. move/eqP : Heq => Heq. specialize (hfstmt_seq_eqP ss_true ss_true) as Heq'. apply reflect_iff in Heq'.
    apply Heq' in Heq. rewrite Heq in Hwhen; simpl in Hwhen. clear Heq Heq'.
    specialize (hfstmt_seq_eqn_refl ss_false) as Heq. move/eqP : Heq => Heq. specialize (hfstmt_seq_eqP ss_false ss_false) as Heq'. apply reflect_iff in Heq'.
    apply Heq' in Heq. rewrite Heq in Hwhen; simpl in Hwhen. done.
    }
  intros. move : H2. apply (Hhelper _ _ _ _ H H0 H1). done.
Qed.

Lemma eval_hfstmts_Qcat_exists s0 rs0 init_s tmap rs s l1 l2 : Sem_HiFP.eval_hfstmts (Qcat l1 l2) rs0 s0 init_s tmap = Some (rs, s)
  -> exists temp_s temp_rs, Sem_HiFP.eval_hfstmts l1 rs0 s0 init_s tmap = Some (temp_rs, temp_s) /\  Sem_HiFP.eval_hfstmts l2 temp_rs temp_s init_s tmap = Some (rs, s).
Proof.
  move : l1 s0 rs0. elim. simpl. intros. exists s0; exists rs0. split; simpl; try done.
  intros hd tl IH s0 rs0 Heval; simpl. simpl in Heval. destruct (Sem_HiFP.eval_hfstmt hd rs0 s0 init_s tmap) as [[rs1 s1]|]; try discriminate.
  apply IH in Heval. done.
Qed.

Lemma eval_hfstmt_exists s rs0 ns0 init_s tmap rs ns : Sem_HiFP.eval_hfstmt s rs0 ns0 init_s tmap = Some (rs, ns) ->
  forall rs1 ns1, exists rs' ns', Sem_HiFP.eval_hfstmt s rs1 ns1 init_s tmap = Some (rs', ns')
with eval_hfstmts_exists ss rs0 ns0 init_s tmap rs ns : Sem_HiFP.eval_hfstmts ss rs0 ns0 init_s tmap = Some (rs, ns) ->
  forall rs1 ns1, exists rs' ns', Sem_HiFP.eval_hfstmts ss rs1 ns1 init_s tmap = Some (rs', ns').
Proof.
  clear eval_hfstmt_exists.
  destruct s as [|v0 t|v0 r|v0 m|v0 v1|v0 e0|v0 e0|v0|c s1 s2] eqn : Hstmt; subst s; simpl; intros Heval rs1 ns1.
  1,2,4,5 : exists rs1; exists ns1; done.
  (* reg *)
  destruct (PVM.find v0 init_s); try discriminate.
  exists (PVM.add v0 b rs1); exists ns1; done.
  (* node *)
  destruct (Sem_HiFP.eval_hfexpr e0 init_s tmap); try discriminate.
  exists rs1; exists (PVM.add v0 b ns1); done.
  (* cnct *)
  destruct v0; try (exists rs1; exists ns1; done).
  destruct (PVM.find s tmap) as [[gt cmpnt]|]; try discriminate.
  destruct cmpnt; destruct (Sem_HiFP.eval_hfexpr e0 init_s tmap); try discriminate.
  6 : exists (PVM.add s b rs1); exists ns1; done.
  1-7 : exists rs1; exists (PVM.add s b ns1); done.
  (* invalid *)
  destruct v0; try (exists rs1; exists ns1; done).
  destruct (PVM.find s tmap) as [[gt cmpnt]|]; try discriminate.
  destruct cmpnt; destruct (sizeof_fgtyp gt < length indeterminate_val).
  1,3,5,7,9,13,15 : exists rs1; exists (PVM.add s (take (sizeof_fgtyp gt) indeterminate_val) ns1); try done.
  6 : exists (PVM.add s (take (sizeof_fgtyp gt) indeterminate_val) rs1); exists ns1; done.
  6 : exists (PVM.add s (zext (sizeof_fgtyp gt - length indeterminate_val) indeterminate_val) rs1); exists ns1; done.
  1-7 : exists rs1; exists (PVM.add s (zext (sizeof_fgtyp gt - length indeterminate_val) indeterminate_val) ns1); done.
  (* when *)
  destruct (Sem_HiFP.eval_hfexpr c init_s tmap); try discriminate.
  destruct ( ~~ is_zero b). move : Heval rs1 ns1; apply eval_hfstmts_exists.
  move : Heval rs1 ns1; apply eval_hfstmts_exists.

  clear eval_hfstmts_exists. move : ss rs0 ns0. elim.
  simpl; intros. exists rs1; exists ns1; done.
  simpl; intros hd tl IH rs0 ns0 Hevals; intros. destruct (Sem_HiFP.eval_hfstmt hd rs0 ns0 init_s tmap) as [[rs0' ns0']|] eqn : Heval; try discriminate.
  specialize (eval_hfstmt_exists _ _ _ _ _ _ _ Heval rs1 ns1). destruct eval_hfstmt_exists as [rs' [ns' Hexists]].
  rewrite Hexists. apply (IH _ _ Hevals).
Qed.

Lemma eval_hfstmt_cnct_no_order s1 s2 rs0 ns0 rs1 ns1 rs2 ns2 init_s tmap rs ns rs' ns' : 
  match s1, s2 with
  | Sinvalid v1, Sinvalid v2 
  | Sinvalid v1, Sfcnct v2 _
  | Sfcnct v1 _, Sinvalid v2
  | Sfcnct v1 _, Sfcnct v2 _ => v1 <> v2
  | _, _ => False
  end ->
  Sem_HiFP.eval_hfstmt s1 rs0 ns0 init_s tmap = Some (rs1, ns1) -> Sem_HiFP.eval_hfstmt s2 rs1 ns1 init_s tmap = Some (rs, ns) -> 
  Sem_HiFP.eval_hfstmt s2 rs0 ns0 init_s tmap = Some (rs2, ns2) -> Sem_HiFP.eval_hfstmt s1 rs2 ns2 init_s tmap = Some (rs', ns') -> 
  forall v : PVM.key, PVM.find v rs' = PVM.find v rs /\ PVM.find v ns' = PVM.find v ns.
Proof.
  intros Hneq. 
  case Hs1 : s1 => [||||||v1 e1|v1|c1 true_ss1 false_ss1]; subst s1; try done;
  case Hs2 : s2 => [||||||v2 e2|v2|c2 true_ss2 false_ss2]; subst s2; try done; simpl in *; intros Heval11 Heval12 Heval21 Heval22 v.
  destruct v1; destruct v2; try (inversion Heval11; inversion Heval12; inversion Heval21; inversion Heval22; subst rs1 ns1 rs ns rs2 ns2 rs' ns'; try done).
  assert (Hneq' : ~ PVM.SE.eq s s0) by (move : Hneq; apply contra_not; intro; unfold PVM.SE.eq in H; move /eqP : H => H; subst s; done).
  - destruct (PVM.find s tmap) as [[gt0 cmpnt0]|]; try discriminate; destruct (PVM.find s0 tmap) as [[gt1 cmpnt1]|]; try discriminate.
    destruct cmpnt0; destruct cmpnt1; destruct (Sem_HiFP.eval_hfexpr e1 init_s tmap); destruct (Sem_HiFP.eval_hfexpr e2 init_s tmap); 
    try discriminate; try (inversion Heval11; inversion Heval12; inversion Heval21; inversion Heval22; subst rs1 ns1 rs ns rs2 ns2 rs' ns'; try done; try (split; try done)).
    36 : specialize (CEP.Lemmas.add_comm b b0 rs0 Hneq') as Hcomm; specialize (PVM.M.SE.eq_refl v) as Heq; apply (PVM.Lemmas.OP.P.F.find_m Heq Hcomm).
    1-49 : specialize (CEP.Lemmas.add_comm b b0 ns0 Hneq') as Hcomm; specialize (PVM.M.SE.eq_refl v) as Heq; apply (PVM.Lemmas.OP.P.F.find_m Heq Hcomm).
  - destruct (PVM.find s tmap) as [[gt0 cmpnt0]|]; try discriminate.
    destruct cmpnt0;destruct (Sem_HiFP.eval_hfexpr e1 init_s tmap); 
    try discriminate; try (inversion Heval11; inversion Heval12; inversion Heval21; inversion Heval22; subst rs1 ns1 rs ns rs2 ns2 rs' ns'; try done; try (split; try done)).
  - destruct (PVM.find s tmap) as [[gt0 cmpnt0]|]; try discriminate.
    destruct cmpnt0; destruct (Sem_HiFP.eval_hfexpr e1 init_s tmap); 
    try discriminate; try (inversion Heval11; inversion Heval12; inversion Heval21; inversion Heval22; subst rs1 ns1 rs ns rs2 ns2 rs' ns'; try done; try (split; try done)).
  - destruct (PVM.find s tmap) as [[gt0 cmpnt0]|]; try discriminate.
    destruct cmpnt0; destruct (Sem_HiFP.eval_hfexpr e1 init_s tmap); 
    try discriminate; try (inversion Heval11; inversion Heval12; inversion Heval21; inversion Heval22; subst rs1 ns1 rs ns rs2 ns2 rs' ns'; try done; try (split; try done)).
  - destruct (PVM.find s0 tmap) as [[gt0 cmpnt0]|]; try discriminate.
    destruct cmpnt0; destruct (Sem_HiFP.eval_hfexpr e2 init_s tmap); 
    try discriminate; try (inversion Heval11; inversion Heval12; inversion Heval21; inversion Heval22; subst rs1 ns1 rs ns rs2 ns2 rs' ns'; try done; try (split; try done)).
  - destruct (PVM.find s tmap) as [[gt0 cmpnt0]|]; try discriminate.
    destruct cmpnt0; destruct (Sem_HiFP.eval_hfexpr e2 init_s tmap); 
    try discriminate; try (inversion Heval11; inversion Heval12; inversion Heval21; inversion Heval22; subst rs1 ns1 rs ns rs2 ns2 rs' ns'; try done; try (split; try done)).
  - destruct (PVM.find s tmap) as [[gt0 cmpnt0]|]; try discriminate.
    destruct cmpnt0; destruct (Sem_HiFP.eval_hfexpr e2 init_s tmap); 
    try discriminate; try (inversion Heval11; inversion Heval12; inversion Heval21; inversion Heval22; subst rs1 ns1 rs ns rs2 ns2 rs' ns'; try done; try (split; try done)).
  
  destruct v1; destruct v2; try (inversion Heval11; inversion Heval12; inversion Heval21; inversion Heval22; subst rs1 ns1 rs ns rs2 ns2 rs' ns'; try done).
  assert (Hneq' : ~ PVM.SE.eq s s0) by (move : Hneq; apply contra_not; intro; unfold PVM.SE.eq in H; move /eqP : H => H; subst s; done).
  - destruct (PVM.find s tmap) as [[gt0 cmpnt0]|]; try discriminate; destruct (PVM.find s0 tmap) as [[gt1 cmpnt1]|]; try discriminate.
    destruct cmpnt0; destruct cmpnt1; destruct (Sem_HiFP.eval_hfexpr e1 init_s tmap); destruct (sizeof_fgtyp gt1 < length indeterminate_val); 
    try discriminate; try (inversion Heval11; inversion Heval12; inversion Heval21; inversion Heval22; subst rs1 ns1 rs ns rs2 ns2 rs' ns'; try done; try (split; try done));
    try (specialize (CEP.Lemmas.add_comm b (take (sizeof_fgtyp gt1) indeterminate_val) ns0 Hneq') as Hcomm; specialize (PVM.M.SE.eq_refl v) as Heq; apply (PVM.Lemmas.OP.P.F.find_m Heq Hcomm));
    try (specialize (CEP.Lemmas.add_comm b (zext (sizeof_fgtyp gt1 - length indeterminate_val) indeterminate_val) ns0 Hneq') as Hcomm; specialize (PVM.M.SE.eq_refl v) as Heq; apply (PVM.Lemmas.OP.P.F.find_m Heq Hcomm)).
    specialize (CEP.Lemmas.add_comm b (take (sizeof_fgtyp gt1) indeterminate_val) rs0 Hneq') as Hcomm; specialize (PVM.M.SE.eq_refl v) as Heq; apply (PVM.Lemmas.OP.P.F.find_m Heq Hcomm).
    specialize (CEP.Lemmas.add_comm b (zext (sizeof_fgtyp gt1 - length indeterminate_val) indeterminate_val) rs0 Hneq') as Hcomm; specialize (PVM.M.SE.eq_refl v) as Heq; apply (PVM.Lemmas.OP.P.F.find_m Heq Hcomm).
  - destruct (PVM.find s tmap) as [[gt0 cmpnt0]|]; try discriminate.
    destruct cmpnt0;destruct (Sem_HiFP.eval_hfexpr e1 init_s tmap); 
    try discriminate; try (inversion Heval11; inversion Heval12; inversion Heval21; inversion Heval22; subst rs1 ns1 rs ns rs2 ns2 rs' ns'; try done; try (split; try done)).
  - destruct (PVM.find s tmap) as [[gt0 cmpnt0]|]; try discriminate.
    destruct cmpnt0; destruct (Sem_HiFP.eval_hfexpr e1 init_s tmap); 
    try discriminate; try (inversion Heval11; inversion Heval12; inversion Heval21; inversion Heval22; subst rs1 ns1 rs ns rs2 ns2 rs' ns'; try done; try (split; try done)).
  - destruct (PVM.find s tmap) as [[gt0 cmpnt0]|]; try discriminate.
    destruct cmpnt0; destruct (Sem_HiFP.eval_hfexpr e1 init_s tmap); 
    try discriminate; try (inversion Heval11; inversion Heval12; inversion Heval21; inversion Heval22; subst rs1 ns1 rs ns rs2 ns2 rs' ns'; try done; try (split; try done)).
  - destruct (PVM.find s0 tmap) as [[gt0 cmpnt0]|]; try discriminate.
    destruct cmpnt0; destruct (sizeof_fgtyp gt0 < length indeterminate_val); 
    try discriminate; try (inversion Heval11; inversion Heval12; inversion Heval21; inversion Heval22; subst rs1 ns1 rs ns rs2 ns2 rs' ns'; try done; try (split; try done)).
  - destruct (PVM.find s tmap) as [[gt0 cmpnt0]|]; try discriminate.
    destruct cmpnt0; destruct (sizeof_fgtyp gt0 < length indeterminate_val); 
    try discriminate; try (inversion Heval11; inversion Heval12; inversion Heval21; inversion Heval22; subst rs1 ns1 rs ns rs2 ns2 rs' ns'; try done; try (split; try done)).
  - destruct (PVM.find s tmap) as [[gt0 cmpnt0]|]; try discriminate.
    destruct cmpnt0; destruct (sizeof_fgtyp gt0 < length indeterminate_val); 
    try discriminate; try (inversion Heval11; inversion Heval12; inversion Heval21; inversion Heval22; subst rs1 ns1 rs ns rs2 ns2 rs' ns'; try done; try (split; try done)).
  
  destruct v1; destruct v2; try (inversion Heval11; inversion Heval12; inversion Heval21; inversion Heval22; subst rs1 ns1 rs ns rs2 ns2 rs' ns'; try done).
  assert (Hneq' : ~ PVM.SE.eq s s0) by (move : Hneq; apply contra_not; intro; unfold PVM.SE.eq in H; move /eqP : H => H; subst s; done).
  - destruct (PVM.find s tmap) as [[gt0 cmpnt0]|]; try discriminate; destruct (PVM.find s0 tmap) as [[gt1 cmpnt1]|]; try discriminate.
    destruct cmpnt0; destruct cmpnt1; destruct (Sem_HiFP.eval_hfexpr e2 init_s tmap); destruct (sizeof_fgtyp gt0 < length indeterminate_val); 
    try discriminate; try (inversion Heval11; inversion Heval12; inversion Heval21; inversion Heval22; subst rs1 ns1 rs ns rs2 ns2 rs' ns'; try done; try (split; try done));
    try (specialize (CEP.Lemmas.add_comm (take (sizeof_fgtyp gt0) indeterminate_val) b ns0 Hneq') as Hcomm; specialize (PVM.M.SE.eq_refl v) as Heq; apply (PVM.Lemmas.OP.P.F.find_m Heq Hcomm));
    try (specialize (CEP.Lemmas.add_comm (zext (sizeof_fgtyp gt0 - length indeterminate_val) indeterminate_val) b ns0 Hneq') as Hcomm; specialize (PVM.M.SE.eq_refl v) as Heq; apply (PVM.Lemmas.OP.P.F.find_m Heq Hcomm)).
    specialize (CEP.Lemmas.add_comm (take (sizeof_fgtyp gt0) indeterminate_val) b rs0 Hneq') as Hcomm; specialize (PVM.M.SE.eq_refl v) as Heq; apply (PVM.Lemmas.OP.P.F.find_m Heq Hcomm).
    specialize (CEP.Lemmas.add_comm (zext (sizeof_fgtyp gt0 - length indeterminate_val) indeterminate_val) b rs0 Hneq') as Hcomm; specialize (PVM.M.SE.eq_refl v) as Heq; apply (PVM.Lemmas.OP.P.F.find_m Heq Hcomm).
  - destruct (PVM.find s tmap) as [[gt0 cmpnt0]|]; try discriminate.
    destruct cmpnt0; destruct (sizeof_fgtyp gt0 < length indeterminate_val); 
    try discriminate; try (inversion Heval11; inversion Heval12; inversion Heval21; inversion Heval22; subst rs1 ns1 rs ns rs2 ns2 rs' ns'; try done; try (split; try done)).
  - destruct (PVM.find s tmap) as [[gt0 cmpnt0]|]; try discriminate.
    destruct cmpnt0; destruct (sizeof_fgtyp gt0 < length indeterminate_val); 
    try discriminate; try (inversion Heval11; inversion Heval12; inversion Heval21; inversion Heval22; subst rs1 ns1 rs ns rs2 ns2 rs' ns'; try done; try (split; try done)).
  - destruct (PVM.find s tmap) as [[gt0 cmpnt0]|]; try discriminate.
    destruct cmpnt0; destruct (sizeof_fgtyp gt0 < length indeterminate_val); 
    try discriminate; try (inversion Heval11; inversion Heval12; inversion Heval21; inversion Heval22; subst rs1 ns1 rs ns rs2 ns2 rs' ns'; try done; try (split; try done)).
  - destruct (PVM.find s0 tmap) as [[gt0 cmpnt0]|]; try discriminate.
    destruct cmpnt0;destruct (Sem_HiFP.eval_hfexpr e2 init_s tmap); 
    try discriminate; try (inversion Heval11; inversion Heval12; inversion Heval21; inversion Heval22; subst rs1 ns1 rs ns rs2 ns2 rs' ns'; try done; try (split; try done)).
  - destruct (PVM.find s tmap) as [[gt0 cmpnt0]|]; try discriminate.
    destruct cmpnt0; destruct (Sem_HiFP.eval_hfexpr e2 init_s tmap); 
    try discriminate; try (inversion Heval11; inversion Heval12; inversion Heval21; inversion Heval22; subst rs1 ns1 rs ns rs2 ns2 rs' ns'; try done; try (split; try done)).
  - destruct (PVM.find s tmap) as [[gt0 cmpnt0]|]; try discriminate.
    destruct cmpnt0; destruct (Sem_HiFP.eval_hfexpr e2 init_s tmap); 
    try discriminate; try (inversion Heval11; inversion Heval12; inversion Heval21; inversion Heval22; subst rs1 ns1 rs ns rs2 ns2 rs' ns'; try done; try (split; try done)).
  
  destruct v1; destruct v2; try (inversion Heval11; inversion Heval12; inversion Heval21; inversion Heval22; subst rs1 ns1 rs ns rs2 ns2 rs' ns'; try done).
  assert (Hneq' : ~ PVM.SE.eq s s0) by (move : Hneq; apply contra_not; intro; unfold PVM.SE.eq in H; move /eqP : H => H; subst s; done).
  - destruct (PVM.find s tmap) as [[gt0 cmpnt0]|]; try discriminate; destruct (PVM.find s0 tmap) as [[gt1 cmpnt1]|]; try discriminate.
    destruct cmpnt0; destruct cmpnt1; destruct (sizeof_fgtyp gt1 < length indeterminate_val); destruct (sizeof_fgtyp gt0 < length indeterminate_val); 
    try discriminate; try (inversion Heval11; inversion Heval12; inversion Heval21; inversion Heval22; subst rs1 ns1 rs ns rs2 ns2 rs' ns'; try done; try (split; try done));
    try (specialize (CEP.Lemmas.add_comm (take (sizeof_fgtyp gt0) indeterminate_val) (take (sizeof_fgtyp gt1) indeterminate_val) ns0 Hneq') as Hcomm; specialize (PVM.M.SE.eq_refl v) as Heq; apply (PVM.Lemmas.OP.P.F.find_m Heq Hcomm));
    try (specialize (CEP.Lemmas.add_comm (zext (sizeof_fgtyp gt0 - length indeterminate_val) indeterminate_val) (take (sizeof_fgtyp gt1) indeterminate_val) ns0 Hneq') as Hcomm; specialize (PVM.M.SE.eq_refl v) as Heq; apply (PVM.Lemmas.OP.P.F.find_m Heq Hcomm));
    try (specialize (CEP.Lemmas.add_comm (take (sizeof_fgtyp gt0) indeterminate_val) (zext (sizeof_fgtyp gt1 - length indeterminate_val) indeterminate_val) ns0 Hneq') as Hcomm; specialize (PVM.M.SE.eq_refl v) as Heq; apply (PVM.Lemmas.OP.P.F.find_m Heq Hcomm));
    try (specialize (CEP.Lemmas.add_comm (zext (sizeof_fgtyp gt0 - length indeterminate_val) indeterminate_val) (zext (sizeof_fgtyp gt1 - length indeterminate_val) indeterminate_val) ns0 Hneq') as Hcomm; specialize (PVM.M.SE.eq_refl v) as Heq; apply (PVM.Lemmas.OP.P.F.find_m Heq Hcomm)).
    specialize (CEP.Lemmas.add_comm (take (sizeof_fgtyp gt0) indeterminate_val) (take (sizeof_fgtyp gt1) indeterminate_val) rs0 Hneq') as Hcomm; specialize (PVM.M.SE.eq_refl v) as Heq; apply (PVM.Lemmas.OP.P.F.find_m Heq Hcomm).
    specialize (CEP.Lemmas.add_comm (zext (sizeof_fgtyp gt0 - length indeterminate_val) indeterminate_val) (take (sizeof_fgtyp gt1) indeterminate_val) rs0 Hneq') as Hcomm; specialize (PVM.M.SE.eq_refl v) as Heq; apply (PVM.Lemmas.OP.P.F.find_m Heq Hcomm).
    specialize (CEP.Lemmas.add_comm (take (sizeof_fgtyp gt0) indeterminate_val) (zext (sizeof_fgtyp gt1 - length indeterminate_val) indeterminate_val) rs0 Hneq') as Hcomm; specialize (PVM.M.SE.eq_refl v) as Heq; apply (PVM.Lemmas.OP.P.F.find_m Heq Hcomm).
    specialize (CEP.Lemmas.add_comm (zext (sizeof_fgtyp gt0 - length indeterminate_val) indeterminate_val) (zext (sizeof_fgtyp gt1 - length indeterminate_val) indeterminate_val) rs0 Hneq') as Hcomm; specialize (PVM.M.SE.eq_refl v) as Heq; apply (PVM.Lemmas.OP.P.F.find_m Heq Hcomm).
  - destruct (PVM.find s tmap) as [[gt0 cmpnt0]|]; try discriminate.
    destruct cmpnt0; destruct (sizeof_fgtyp gt0 < length indeterminate_val); 
    try discriminate; try (inversion Heval11; inversion Heval12; inversion Heval21; inversion Heval22; subst rs1 ns1 rs ns rs2 ns2 rs' ns'; try done; try (split; try done)).
  - destruct (PVM.find s tmap) as [[gt0 cmpnt0]|]; try discriminate.
    destruct cmpnt0; destruct (sizeof_fgtyp gt0 < length indeterminate_val); 
    try discriminate; try (inversion Heval11; inversion Heval12; inversion Heval21; inversion Heval22; subst rs1 ns1 rs ns rs2 ns2 rs' ns'; try done; try (split; try done)).
  - destruct (PVM.find s tmap) as [[gt0 cmpnt0]|]; try discriminate.
    destruct cmpnt0; destruct (sizeof_fgtyp gt0 < length indeterminate_val); 
    try discriminate; try (inversion Heval11; inversion Heval12; inversion Heval21; inversion Heval22; subst rs1 ns1 rs ns rs2 ns2 rs' ns'; try done; try (split; try done)).
  - destruct (PVM.find s0 tmap) as [[gt0 cmpnt0]|]; try discriminate.
    destruct cmpnt0;destruct (sizeof_fgtyp gt0 < length indeterminate_val); 
    try discriminate; try (inversion Heval11; inversion Heval12; inversion Heval21; inversion Heval22; subst rs1 ns1 rs ns rs2 ns2 rs' ns'; try done; try (split; try done)).
  - destruct (PVM.find s tmap) as [[gt0 cmpnt0]|]; try discriminate.
    destruct cmpnt0; destruct (sizeof_fgtyp gt0 < length indeterminate_val); 
    try discriminate; try (inversion Heval11; inversion Heval12; inversion Heval21; inversion Heval22; subst rs1 ns1 rs ns rs2 ns2 rs' ns'; try done; try (split; try done)).
  - destruct (PVM.find s tmap) as [[gt0 cmpnt0]|]; try discriminate.
    destruct cmpnt0; destruct (sizeof_fgtyp gt0 < length indeterminate_val); 
    try discriminate; try (inversion Heval11; inversion Heval12; inversion Heval21; inversion Heval22; subst rs1 ns1 rs ns rs2 ns2 rs' ns'; try done; try (split; try done)).
Qed.

Definition unique_connect_stmts (ss : HiFP.hfstmt_seq) : Prop :=
  (forall v e, Qin (Sfcnct v e) ss -> (forall e', ~ Qin (Sfcnct v e') (Qremove (Sfcnct v e) ss)) /\ (~ Qin (Sinvalid v) (Qremove (Sfcnct v e) ss))) /\
  (forall v, Qin (Sinvalid v) ss -> (forall e', ~ Qin (Sfcnct v e') (Qremove (Sinvalid v) ss)) /\ (~ Qin (Sinvalid v) (Qremove (Sinvalid v) ss))).

Lemma eval_hfstmts_cnct_no_order connect_stmts rs0 ns0 init_s tmap rs ns : 
  Sem_HiFP.eval_hfstmts connect_stmts rs0 ns0 init_s tmap = Some (rs, ns) ->
  (forall s, Qin s connect_stmts -> is_connection s) ->
  unique_connect_stmts connect_stmts ->
  forall s, Qin s connect_stmts -> 
  exists rs' ns', Sem_HiFP.eval_hfstmts (Qcons s (Qremove s connect_stmts)) rs0 ns0 init_s tmap = Some (rs', ns') /\
  forall v, PVM.find v rs' = PVM.find v rs /\ PVM.find v ns' = PVM.find v ns.
Proof.
  move : connect_stmts rs0 ns0. elim. 
  simpl; intros; done.
  intros hd tl IH. simpl; intros rs0 ns0 Hevals His Hunique s Hin.
  destruct (Sem_HiFP.eval_hfstmt hd rs0 ns0 init_s tmap) as [[rs1 ns1]|] eqn : Heval; try discriminate. destruct (hfstmt_eqn hd s) eqn : Heqs.
  - (* eq s *)
    clear Hin IH. assert (hd = s).  specialize (hfstmt_eqP hd s) as Heq'. apply reflect_iff in Heq'. apply Heq' in Heqs. done.
    subst hd. clear Heqs. rewrite Heval. exists rs; exists ns. rewrite Hevals. split; try done.
  - (* in *)
    rewrite orb_false_l in Hin. 
    assert (His_hd : is_connection hd). apply His. specialize (hfstmt_eqn_refl hd) as Heq. move/eqP : Heq => Heq. 
      specialize (hfstmt_eqP hd hd) as Heq'. apply reflect_iff in Heq'. apply Heq' in Heq. rewrite Heq orb_true_l //.
    assert (His_s : is_connection s). apply His. rewrite Hin orb_true_r //. generalize Hin; intro Heq.
    apply (IH _ _ Hevals) in Heq. clear IH. destruct Heq as [rs' [ns' [Hevals' Heq]]]. simpl in Hevals'.
    destruct (Sem_HiFP.eval_hfstmt s rs1 ns1 init_s tmap) as [[rs2 ns2]|] eqn : Heval_s; try discriminate.
    specialize (eval_hfstmt_exists Heval_s rs0 ns0) as Heval3. destruct Heval3 as [rs3 [ns3 Heval3]]. rewrite Heval3. simpl.
    specialize (eval_hfstmt_exists Heval rs3 ns3) as Heval4. destruct Heval4 as [rs4 [ns4 Heval4]]. rewrite Heval4. 
    specialize (eval_hfstmts_exists Hevals' rs4 ns4) as Hexists. destruct Hexists as [rs'0 [ns'0 Hevals'0]]. 
    rewrite Hevals'0; exists rs'0; exists ns'0. split; try done. intro. specialize (Heq v). destruct Heq as [Heq0 Heq1].
    rewrite -Heq0 -Heq1; clear Heq0 Heq1 Hevals rs ns. 
    specialize (eval_hfstmts_find_eq2find_eq v Hevals' Hevals'0) as Hfindeq. move : Hfindeq => [Hfindeq0 Hfindeq1].
    assert (Hhelper : match hd, s with
      | Sinvalid v1, Sinvalid v2 
      | Sinvalid v1, Sfcnct v2 _
      | Sfcnct v1 _, Sinvalid v2
      | Sfcnct v1 _, Sfcnct v2 _ => v1 <> v2
      | _, _ => False
      end). {
      move : His_hd His_s Hunique Hin; clear; unfold unique_connect_stmts; intros. destruct hd eqn : Hhd; destruct s eqn : Hs; simpl in *; try done.
      - (* cnct cnct *)
        move : Hunique => [Hunique _]. assert ((h == h) && (h0 == h0) || Qin (Sfcnct h h0) tl). rewrite eq_refl; rewrite eq_refl; simpl; done.
        apply Hunique in H; clear Hunique. move : H => [H _]. rewrite eq_refl in H; rewrite eq_refl in H; simpl in H. move : (H h2); apply contra_not.
        intro; subst h; done.
      - (* cnct invalid *)
        move : Hunique => [Hunique _]. assert ((h == h) && (h0 == h0) || Qin (Sfcnct h h0) tl). rewrite eq_refl; rewrite eq_refl; simpl; done.
        apply Hunique in H; clear Hunique. move : H => [_ H]. rewrite eq_refl in H; rewrite eq_refl in H; simpl in H. move : H; apply contra_not.
        intro; subst h; done.
      - (* invalid cnct *)
        move : Hunique => [_ Hunique]. assert ((h == h) || Qin (Sinvalid h) tl). rewrite eq_refl; simpl; done.
        apply Hunique in H; clear Hunique. move : H => [H _]. rewrite eq_refl in H; simpl in H. move : (H h1); apply contra_not.
        intro; subst h; done.
      - (* invalid invalid *)
        move : Hunique => [_ Hunique]. assert ((h == h) || Qin (Sinvalid h) tl). rewrite eq_refl; simpl; done.
        apply Hunique in H; clear Hunique. move : H => [_ H]. rewrite eq_refl in H; simpl in H. move : H; apply contra_not.
        intro; subst h; done.
      }
    specialize (eval_hfstmt_cnct_no_order Hhelper Heval Heval_s Heval3 Heval4 v) as Hfindeq. move : Hfindeq => [Hfindeq Hfindeq'].
    split; try (apply Hfindeq0; done); try (apply Hfindeq1; done).
    intros; apply His. rewrite H orb_true_r //.
    move : Hunique; clear; unfold unique_connect_stmts; intros. move : Hunique => [Hunique0 Hunique1]. split; intros.
    - (* no cnct *) 
      assert (Qin (Sfcnct v e) (Qcons hd tl)). simpl. rewrite H orb_true_r //. apply Hunique0 in H0. move : H0 => [H0 H1].
      split. intros. move : (H0 e'). apply contra_not. clear; simpl; intros. 
      destruct (hfstmt_eqn hd (Sfcnct v e)). move : H; apply in_qremove. simpl; rewrite H orb_true_r //.
      move : H1; apply contra_not. clear; simpl; intros. 
      destruct (hfstmt_eqn hd (Sfcnct v e)). move : H; apply in_qremove. simpl; rewrite H orb_true_r //.
    - (* no invalid *)
      assert (Qin (Sinvalid v) (Qcons hd tl)). simpl. rewrite H orb_true_r //. apply Hunique1 in H0. move : H0 => [H0 H1].
      split. intros. move : (H0 e'). apply contra_not. clear; simpl; intros. 
      destruct (hfstmt_eqn hd (Sinvalid v)). move : H; apply in_qremove. simpl; rewrite H orb_true_r //.
      move : H1; apply contra_not. clear; simpl; intros. 
      destruct (hfstmt_eqn hd (Sinvalid v)). move : H; apply in_qremove. simpl; rewrite H orb_true_r //.
Qed.

Lemma unique_connect_stmts_convert_to_connect_stmt ss (v : ProdVarOrder.t) d_expr: 
  (~ Qin (Sinvalid (Eid v)) ss /\ forall e, ~ Qin (Sfcnct (Eid v) e) ss) ->
  unique_connect_stmts ss -> unique_connect_stmts (convert_to_connect_stmt v d_expr ss).
Proof.
  intros [Hnot_invalid Hnot_cnct] Hss; unfold unique_connect_stmts in *. move : Hss => [Hcnct Hinvalid]. split.
  - (* cnct in *)
    intros v0 e0 Hin. destruct d_expr as [gt|de]; simpl in *. 
    * specialize (Hnot_cnct e0). destruct (Eid v == v0) eqn : Hneq. move /eqP : Hneq => Hneq; subst v0; done.
      apply Hcnct in Hin as Hcnct'; clear Hcnct. move : Hcnct' => [Hcnct' Hinvalid']; split; try done.
    * destruct (Eid v == v0) eqn : Hneq. move /eqP : Hneq => Hneq; subst v0. simpl in *. destruct (de == e0) eqn : Heqe.
      + (* eq v, eq e *)
        move /eqP : Heqe => Heqe; subst de; clear Hin. split; try done.
      + (* eq v, neq e *)
        rewrite orb_false_l in Hin. specialize (Hnot_cnct e0); done.
      + (* neqv *)
        simpl in *. rewrite Hneq. simpl. apply Hcnct; done.
  - (* invalid in *) 
    intros v0 Hin. destruct d_expr as [gt|de]; simpl in *. 
    * destruct (Eid v == v0) eqn : Hneq. move /eqP : Hneq => Hneq; subst v0; done.
      rewrite orb_false_l in Hin. simpl. rewrite Hneq; simpl.
      apply Hinvalid in Hin as Hinvalid'; clear Hinvalid. move : Hinvalid' => [Hcnct' Hinvalid']; split; try done.
    * destruct (Eid v == v0) eqn : Hneq. move /eqP : Hneq => Hneq; subst v0; done. simpl in *.
      apply Hinvalid; done.
Qed.

Lemma qin_convert_to_connect_stmt_invalid v0 ss v d_expr : v <> v0 -> Qin (Sinvalid (Eid v0)) (convert_to_connect_stmt v d_expr ss) -> Qin (Sinvalid (Eid v0)) ss.
Proof.
  destruct d_expr; simpl; try done.
  intros. destruct (Eid v == Eid v0) eqn : Heq. move /eqP : Heq => Heq. inversion Heq; subst v; done.
  rewrite orb_false_l in H0; done. 
Qed.

Lemma qin_convert_to_connect_stmt_cnct v0 e0 ss v d_expr : v <> v0 -> Qin (Sfcnct (Eid v0) e0) (convert_to_connect_stmt v d_expr ss) -> Qin (Sfcnct (Eid v0) e0) ss.
Proof.
  destruct d_expr; simpl; try done.
  intros. destruct (Eid v == Eid v0) eqn : Heq. move /eqP : Heq => Heq. inversion Heq; subst v; done.
  rewrite orb_false_l in H0; done. 
Qed.

Lemma NoDupA_notin : forall (l1 l2 : list (PVM.key * def_expr)) v e,
  NoDupA (PVM.eq_key (elt:=def_expr)) (l1 ++ (v, e) :: l2) ->
  ~ In v (fst (List.split l1)) /\ ~ In v (fst (List.split l2)).
Proof.
Admitted.

Lemma convert_to_connect_stmts_unique_connect_stmts conn_map : unique_connect_stmts (convert_to_connect_stmts conn_map).
Proof.
  unfold convert_to_connect_stmts.
  rewrite PVM.M.fold_1.
  specialize (PVM.elements_3w conn_map) as Hnodup.
  remember (PVM.M.elements conn_map) as elements. 
  assert (Hhelper : forall res, unique_connect_stmts res -> 
    (forall p, In p elements -> ~ Qin (Sinvalid (Eid (fst p))) res /\ forall e, ~ Qin (Sfcnct (Eid (fst p)) e) res) ->
    unique_connect_stmts (fold_left
    (fun (a : HiFP.hfstmt_seq) (p : PVM.M.key * def_expr) =>
    convert_to_connect_stmt (fst p) (snd p) a) elements 
    res)). { clear Heqelements; move : elements Hnodup.
    elim. simpl; done. 
    simpl; intros hd tl IH Hnodup res Hres Hnotin. apply IH; clear IH. 
    assert (hd :: tl = nil ++ (hd :: tl)) by (simpl; done). rewrite H in Hnodup. apply NoDupA_split in Hnodup. simpl in Hnodup; done.
    apply unique_connect_stmts_convert_to_connect_stmt; try done.
    apply Hnotin. left; done.
    (* hypo *)
    intros. assert (hd = p \/ In p tl) by (right; done). specialize (Hnotin _ H0). clear H0.
    move : Hnotin => [Hnot_invalid Hnot_cnct]; split.
    move : Hnot_invalid; apply contra_not. apply qin_convert_to_connect_stmt_invalid. destruct hd as [hd_v hd_e]; simpl.
      assert ((hd_v, hd_e) :: tl = nil ++ (hd_v, hd_e) :: tl) by (simpl; done). rewrite H0 in Hnodup; clear H0. 
      specialize (NoDupA_notin Hnodup) as [_ Hnotin]. move : Hnotin; apply contra_not. intro; subst hd_v.
      apply in_split_l; done.
    intro. move : (Hnot_cnct e); apply contra_not. apply qin_convert_to_connect_stmt_cnct. destruct hd as [hd_v hd_e]; simpl.
      assert ((hd_v, hd_e) :: tl = nil ++ (hd_v, hd_e) :: tl) by (simpl; done). rewrite H0 in Hnodup; clear H0. 
      specialize (NoDupA_notin Hnodup) as [_ Hnotin]. move : Hnotin; apply contra_not. intro; subst hd_v.
      apply in_split_l; done.
  }
  apply Hhelper. unfold unique_connect_stmts.
  split; simpl; try done. intros; split; try done.
Qed.

Lemma eval_hfstmts_for_sequ_only_cnct v tmap ss init_s conn_map : 
  (forall s, Qin s (component_stmts_of ss) -> is_declaration s) ->
  match PVM.find v tmap with
  | Some (gt, Register) => ExpandBranches_funs ss (PVM.empty def_expr) tmap = Some conn_map -> 
      Qin (Sfcnct (Eid v) (Eref (Eid v))) (convert_to_connect_stmts conn_map) \/
        (exists e : hfexpr ProdVarOrder.T, Qin (Sfcnct (Eid v) e) (convert_to_connect_stmts conn_map)) ->
      forall rs s, Sem_HiFP.eval_hfstmts (Qcat (component_stmts_of ss) (convert_to_connect_stmts conn_map)) (PVM.empty bits) (PVM.empty bits) init_s tmap = Some (rs, s) ->
      forall rs' s', Sem_HiFP.eval_hfstmts (convert_to_connect_stmts conn_map) (PVM.empty bits) (PVM.empty bits) init_s tmap = Some (rs', s') -> PVM.find v rs' = PVM.find v rs
  | _ => True
  end.
Proof.
  intro Hdclr. destruct (PVM.find v tmap) as [[gt cmpnt]|] eqn : Hcmpnt; try done. destruct cmpnt; try done.
  assert (Hhelper : forall connect_stmts component_stmts, 
    (forall s, Qin s component_stmts -> is_declaration s) ->
    (forall s, Qin s connect_stmts -> is_connection s) -> 
    (Qin (Sfcnct (Eid v) (Eref (Eid v))) connect_stmts \/ exists e, Qin (Sfcnct (Eid v) e) connect_stmts) -> 
    unique_connect_stmts connect_stmts ->
    forall temp_rs temp_s rs s : PVM.t bits,
    Sem_HiFP.eval_hfstmts (Qcat component_stmts connect_stmts)
    temp_rs temp_s init_s tmap = Some (rs, s) ->
    forall temp_rs' temp_s' rs' s' : PVM.t bits,
    PVM.find v temp_rs' = PVM.find v temp_rs ->
    Sem_HiFP.eval_hfstmts connect_stmts temp_rs' temp_s' init_s tmap = Some (rs', s') ->
    PVM.find v rs' = PVM.find v rs). { move : Hcmpnt; clear. intro; intro; elim.
  - intros Hdclr _ _ _ temp_rs temp_s rs s Heval temp_rs' temp_s' rs' s' Htemp Heval'. simpl in Heval. 
    apply (eval_hfstmts_find_eq2find_eq v Heval) in Heval'. move : Heval' => [Heval' _]. apply Heval'; done.
  - intros st ss IH Hdclr Hhelper1 Hexpand_branches Hhelper2 temp_rs temp_s rs s Heval temp_rs' temp_s' rs' s' Htemp Heval'. simpl in Heval.
    case Hst : st => [||var reg|||var node_e|ref e|ref|cond ss_true ss_false]; subst st; simpl in Heval.
    1,2,4,5 : move : temp_rs temp_s rs s Heval temp_rs' temp_s' rs' s' Htemp Heval'; apply IH; try done; intros; apply Hdclr; simpl; rewrite H orb_true_r //.
    (* reg *)
    destruct (PVM.find var init_s) as [val|] eqn : Hfind; try discriminate.
    destruct (var == v) eqn : Heq. 
    - (* eq *)
      move /eqP : Heq => Heq; subst var. clear IH. apply eval_hfstmts_Qcat_exists in Heval. destruct Heval as [ss_s [ss_rs [Hss Heval]]].
      (*assert (Hexpand_branches : Qin (Sfcnct (Eid v) (Eref (Eid v))) connect_stmts \/ exists e, Qin (Sfcnct (Eid v) e) connect_stmts). admit. 
      assert (Hhelper1 : forall s, Qin s connect_stmts -> is_connection s). admit. 
      assert (Hhelper2 : unique_connect_stmts connect_stmts). admit. *)
      destruct Hexpand_branches as [Hcase1|Hcase2].
      - (* reg <= reg *)
        specialize (eval_hfstmts_cnct_no_order Heval' Hhelper1 Hhelper2 Hcase1) as Heval'_order. destruct Heval'_order as [rs'0 [ns'0 [Heval'_order Hfind'_order]]].
        specialize (eval_hfstmts_cnct_no_order Heval Hhelper1 Hhelper2 Hcase1) as Heval_order. destruct Heval_order as [rs0 [ns0 [Heval_order Hfind_order]]].
        clear Heval' Heval. clear Hhelper1 Hhelper2. 
        specialize (Hfind'_order v); move : Hfind'_order => [Hfind'_order _].
        specialize (Hfind_order v); move : Hfind_order => [Hfind_order _]. 
        rewrite -Hfind_order -Hfind'_order; clear Hfind_order Hfind'_order.
        simpl in Heval'_order; simpl in Heval_order. rewrite Hcmpnt Hfind in Heval_order Heval'_order.
        apply (eval_hfstmts_find_eq2find_eq v Heval_order) in Heval'_order. move : Heval'_order => [Hfind' _].
        apply Hfind'. rewrite PVM.Lemmas.find_add_eq. rewrite PVM.Lemmas.find_add_eq //. 1,2 : apply PVM.M.SE.eq_refl.
      - (* reg <= e *)
        destruct Hcase2 as [e Hcase1].
        specialize (eval_hfstmts_cnct_no_order Heval' Hhelper1 Hhelper2 Hcase1) as Heval'_order. destruct Heval'_order as [rs'0 [ns'0 [Heval'_order Hfind'_order]]].
        specialize (eval_hfstmts_cnct_no_order Heval Hhelper1 Hhelper2 Hcase1) as Heval_order. destruct Heval_order as [rs0 [ns0 [Heval_order Hfind_order]]].
        clear Heval' Heval. clear Hhelper1 Hhelper2. 
        specialize (Hfind'_order v); move : Hfind'_order => [Hfind'_order _].
        specialize (Hfind_order v); move : Hfind_order => [Hfind_order _]. 
        rewrite -Hfind_order -Hfind'_order; clear Hfind_order Hfind'_order.
        simpl in Heval'_order; simpl in Heval_order. rewrite Hcmpnt in Heval_order Heval'_order.
        destruct (Sem_HiFP.eval_hfexpr e init_s tmap) as [val_e|]; try discriminate.
        apply (eval_hfstmts_find_eq2find_eq v Heval_order) in Heval'_order. move : Heval'_order => [Hfind' _].
        apply Hfind'. rewrite PVM.Lemmas.find_add_eq. rewrite PVM.Lemmas.find_add_eq //. 1,2 : apply PVM.M.SE.eq_refl.
    - (* neq *)
      assert (Htemp' : PVM.find v temp_rs' = PVM.find v (PVM.add var val temp_rs)). rewrite PVM.Lemmas.find_add_neq //. move /eqP : Heq => Heq. move : Heq; apply contra_not.
        intro. rewrite /PVM.M.SE.eq in H. move /eqP : H => H; subst v; done.
      move : Htemp' Heval'. apply IH with (temp_s := temp_s) (s := s); try done. intros. apply Hdclr. simpl; rewrite H orb_true_r //.
    (* node *)
    destruct (Sem_HiFP.eval_hfexpr node_e init_s tmap); try discriminate.
    move : Heval'; apply IH with (temp_rs := temp_rs) (temp_s := PVM.add var b temp_s) (s := s); try done. intros; apply Hdclr; simpl; rewrite H orb_true_r //.
    (* cnct *)
    assert (Qin (Sfcnct ref e) (Qcons (Sfcnct ref e) ss)). simpl. rewrite eq_refl; rewrite eq_refl; simpl; done. apply Hdclr in H. simpl in H. done.
    (* invalid *)
    assert (Qin (Sinvalid ref) (Qcons (Sinvalid ref) ss)). simpl. rewrite eq_refl; simpl; done. apply Hdclr in H. simpl in H. done.
    (* when *)
    assert (Qin (Swhen cond ss_true ss_false) (Qcons (Swhen cond ss_true ss_false) ss)). simpl. rewrite eq_refl; simpl.
    specialize (hfstmt_seq_eqn_refl ss_true) as Heq. move/eqP : Heq => Heq. specialize (hfstmt_seq_eqP ss_true ss_true) as Heq'. apply reflect_iff in Heq'.
    apply Heq' in Heq. rewrite Heq; simpl. clear Heq Heq'.
    specialize (hfstmt_seq_eqn_refl ss_false) as Heq. move/eqP : Heq => Heq. specialize (hfstmt_seq_eqP ss_false ss_false) as Heq'. apply reflect_iff in Heq'.
    apply Heq' in Heq. rewrite Heq //.
    apply Hdclr in H. simpl in H. done.
    }
  intros H Hr_cnct rs s H0 rs' s' H1. move : H1; apply (Hhelper _ _ Hdclr) with (temp_rs := PVM.empty bits) (temp_s := PVM.empty bits) (s := s); try done.
  apply convert_to_connect_stmts_is_connection. 
  apply convert_to_connect_stmts_unique_connect_stmts.
Qed.

Lemma eval_hfstmts_Qcat_some' s1 s2 rs0 ns0 rs1 ns1 s tmap res : Sem_HiFP.eval_hfstmts (Qcat s1 s2) rs0 ns0 s tmap = Some res ->
  exists res', Sem_HiFP.eval_hfstmts s2 rs1 ns1 s tmap = Some res'.
Proof.
  move : s1 rs0 ns0 rs1 ns1. elim; simpl; intros.
  - (* s1 = Qnil *) destruct res as [rs ns].
    apply eval_hfstmts_exists with (rs1 := rs1) (ns1 := ns1) in H. destruct H as [rs' [ns' H]].
    exists (rs', ns'); done.
  - (* s1 = Qcons st sts *)
    destruct (Sem_HiFP.eval_hfstmt h rs0 ns0 s tmap) as [[rs2 ns2]|] eqn:E; try discriminate.
    apply (H rs2 ns2); done.
Qed.

Lemma convert_to_connect_stmt_qrcons k d acc hd : 
  convert_to_connect_stmt k d (Qrcons acc hd) = Qrcons (convert_to_connect_stmt k d acc) hd.
Proof.
  destruct d; simpl; try done.
Qed.

Lemma fold_left_qrcons l new acc : fold_left (fun (a : HiFP.hfstmt_seq) (p : PVM.key * def_expr) =>
  convert_to_connect_stmt (fst p) (snd p) a) l (Qrcons acc new) = Qrcons (fold_left (fun (a : HiFP.hfstmt_seq)
  (p : PVM.key * def_expr) => convert_to_connect_stmt (fst p) (snd p) a) l acc) new.
Proof.
  move : l acc. elim; simpl. done.
  intros hd tl IH acc. rewrite convert_to_connect_stmt_qrcons IH //.
Qed.

Lemma fold_left_qcat res l acc : fold_left (fun (a : HiFP.hfstmt_seq) (p : PVM.key * def_expr) =>
  convert_to_connect_stmt (fst p) (snd p) a) l (Qcat acc res) = Qcat (fold_left (fun (a : HiFP.hfstmt_seq)
  (p : PVM.key * def_expr) => convert_to_connect_stmt (fst p) (snd p) a) l acc) res.
Proof.
  move : res acc. elim; simpl.
  - intro; rewrite Qcats0. rewrite Qcats0 //.
  - intros hd tl IH acc. simpl. rewrite -Qcat_rcons. rewrite IH; clear IH.
    rewrite -Qcat_rcons. rewrite fold_left_qrcons //.
Qed.

Lemma eval_hfstmts_notin_none v ns0 rs0 init_s tmap : 
  forall l ss rs s,
  Sem_HiFP.eval_hfstmts ss rs0 ns0 init_s tmap = Some (rs, s) -> 
  (~ In v (fst (List.split l))) -> forall temp_rs temp_s, 
  Sem_HiFP.eval_hfstmts
  (fold_left
    (fun (a : HiFP.hfstmt_seq) (p : PVM.key * def_expr) =>
      convert_to_connect_stmt (fst p) (snd p) a) l ss)
  rs0 ns0 init_s tmap = Some (temp_rs, temp_s) -> 
  (PVM.find v s = None -> PVM.find v temp_s = None) /\ (PVM.find v rs = None -> PVM.find v temp_rs = None).
Proof.
  elim; simpl. intros. rewrite H in H1. inversion H1; subst temp_s temp_rs; done.
  intros [v_hd de_hd] tl IH ss rs s Hss Hnotin temp_rs temp_s Heval. destruct (List.split tl) as [tl_left tl_right] eqn : Hsplit; simpl in *.
  apply Decidable.not_or in Hnotin; move : Hnotin => [Hneq Hnotin].
  assert (convert_to_connect_stmt v_hd de_hd ss = Qcat (Qnil ProdVarOrder.T) (convert_to_connect_stmt v_hd de_hd ss)). simpl; done. 
  generalize Heval; intro Heval'. rewrite H in Heval; clear H. rewrite fold_left_qcat in Heval. specialize (eval_hfstmts_Qcat_exists Heval) as Hexists.
  destruct Hexists as [s_hd [rs_hd [_ Heval_hd]]]. apply eval_hfstmts_exists with (rs1 := rs0) (ns1 := ns0) in Heval_hd.
  destruct Heval_hd as [rs' [ns' Heval_hd]]. 
  specialize (IH _ _ _ Heval_hd Hnotin temp_rs temp_s Heval') as [IH0 IH1]. split.
  (* comb *) intro Hnone.
  assert (Hnone_hd : PVM.find v ns' = None). {
    move : Hneq Hss Hnone Heval_hd; clear.
    destruct de_hd; simpl in *; intros.
    - (* invalid *)
    destruct (PVM.find v_hd tmap) as [[gt cmpnt]|]; try discriminate. rewrite -Hnone.
    destruct cmpnt; destruct (sizeof_fgtyp gt < length indeterminate_val). 
    11-12 : specialize (eval_hfstmts_find_eq2find_eq v Hss Heval_hd) as [Hfind0 Hfind1]; apply Hfind1; done.
    1-14 : specialize (eval_hfstmts_find_eq2find_eq v Hss Heval_hd) as [Hfind0 Hfind1]; apply Hfind1; rewrite PVM.Lemmas.find_add_neq //;
    unfold PVM.M.SE.eq; intro; move /eqP : H => H; subst v; done.
    - (* cnct *)
    destruct (PVM.find v_hd tmap) as [[gt cmpnt]|]; try discriminate. rewrite -Hnone.
    destruct cmpnt; destruct (Sem_HiFP.eval_hfexpr h init_s tmap); try discriminate. 
    6 : specialize (eval_hfstmts_find_eq2find_eq v Hss Heval_hd) as [Hfind0 Hfind1]; apply Hfind1; done.
    1-7 : specialize (eval_hfstmts_find_eq2find_eq v Hss Heval_hd) as [Hfind0 Hfind1]; apply Hfind1; rewrite PVM.Lemmas.find_add_neq //;
    unfold PVM.M.SE.eq; intro; move /eqP : H => H; subst v; done.
  } apply IH0; done.
  (* sequ *) intro Hnone.
  assert (Hnone_hd : PVM.find v rs' = None). {
    move : Hneq Hss Hnone Heval_hd; clear.
    destruct de_hd; simpl in *; intros. 
    - (* invalid *)
    destruct (PVM.find v_hd tmap) as [[gt cmpnt]|]; try discriminate. rewrite -Hnone.
    destruct cmpnt; destruct (sizeof_fgtyp gt < length indeterminate_val). 
    1-10,13-16 : specialize (eval_hfstmts_find_eq2find_eq v Hss Heval_hd) as [Hfind0 Hfind1]; apply Hfind0; done.
    1-2 : specialize (eval_hfstmts_find_eq2find_eq v Hss Heval_hd) as [Hfind0 Hfind1]; apply Hfind0; rewrite PVM.Lemmas.find_add_neq //;
    unfold PVM.M.SE.eq; intro; move /eqP : H => H; subst v; done.
    - (* cnct *)
    destruct (PVM.find v_hd tmap) as [[gt cmpnt]|]; try discriminate. rewrite -Hnone.
    destruct cmpnt; destruct (Sem_HiFP.eval_hfexpr h init_s tmap); try discriminate. 
    1-5,7,8 : specialize (eval_hfstmts_find_eq2find_eq v Hss Heval_hd) as [Hfind0 Hfind1]; apply Hfind0; done.
    specialize (eval_hfstmts_find_eq2find_eq v Hss Heval_hd) as [Hfind0 Hfind1]; apply Hfind0; rewrite PVM.Lemmas.find_add_neq //;
    unfold PVM.M.SE.eq; intro; move /eqP : H => H; subst v; done.
  } apply IH1; done.
Qed.

Lemma eval_hfstmts_notinss_findeq tmap init_s ss temp_rs temp_s rs s v : (forall st, Qin st ss ->
  match st with 
  | Snode _ _ 
  | Sreg _ _ 
  | Swhen _ _ _ => False
  | Sfcnct v0 _ 
  | Sinvalid v0 => v0 <> Eid v
  | _ => True
  end) ->
  Sem_HiFP.eval_hfstmts ss temp_rs temp_s init_s tmap = Some (rs, s) ->
  PVM.find v s = PVM.find v temp_s /\ PVM.find v rs = PVM.find v temp_rs
with eval_hfstmt_notinss_findeq tmap init_s st temp_rs temp_s rs s v : 
  match st with 
  | Snode _ _ 
  | Sreg _ _ 
  | Swhen _ _ _ => False
  | Sfcnct v0 _ 
  | Sinvalid v0 => v0 <> Eid v
  | _ => True
  end ->
  Sem_HiFP.eval_hfstmt st temp_rs temp_s init_s tmap = Some (rs, s) ->
  PVM.find v s = PVM.find v temp_s /\ PVM.find v rs = PVM.find v temp_rs.
Proof.
  clear eval_hfstmts_notinss_findeq. move : ss temp_rs temp_s rs s. elim; simpl. intros temp_rs temp_s rs s Hnotin Hevals. inversion Hevals; subst s; done.
  intros hd tl IH temp_rs temp_s rs s Hnotin Hevals. destruct (Sem_HiFP.eval_hfstmt hd temp_rs temp_s init_s tmap) as [[rs0 ns0]|] eqn : Heval; try discriminate.
  assert (forall st : hfstmt ProdVarOrder.T,
    Qin st tl ->
    match st with
    | Snode _ _ 
    | Sreg _ _ 
    | Swhen _ _ _ => False
    | Sfcnct v0 _ | Sinvalid v0 => v0 <> Eid v
    | _ => True
    end). intros; apply Hnotin. rewrite H orb_true_r //.
  apply (IH _ _ _ _ H) in Hevals as [Hevals0 Hevals1]. rewrite Hevals0 Hevals1. clear H. 
  assert (match hd with
  | Snode _ _
  | Sreg _ _ 
  | Swhen _ _ _ => False
  | Sfcnct v0 _ | Sinvalid v0 => v0 <> Eid v
  | _ => True
  end). apply Hnotin. specialize (hfstmt_eqn_refl hd) as Heq. move/eqP : Heq => Heq. 
  specialize (hfstmt_eqP hd hd) as Heq'. apply reflect_iff in Heq'. apply Heq' in Heq. rewrite Heq orb_true_l //.
  move : H Heval; apply eval_hfstmt_notinss_findeq.

  clear eval_hfstmt_notinss_findeq. intros Hneq Heval. destruct st as [|v0 t|v0 r|v0 m|v0 v1|v0 e0|v0 e0|v0|c s1 s2] eqn : Hstmt; subst st; simpl in *; try done.
  1-4 : inversion Heval; subst s; done.
  (* cnct *) destruct v0; try (inversion Heval; subst s; done). destruct (PVM.find s0 tmap) as [[gt cmpnt]|]; try discriminate.
  destruct cmpnt; destruct (Sem_HiFP.eval_hfexpr e0 init_s tmap); try discriminate; try (inversion Heval; subst rs s; split); try done.
  1-8 : rewrite PVM.Lemmas.find_add_neq //. 1-8 : unfold PVM.M.SE.eq; intro; move /eqP : H => H; subst v; done.
  (* invalid *) destruct v0; try (inversion Heval; subst s rs; done). destruct (PVM.find s0 tmap) as [[gt cmpnt]|]; try discriminate.
  destruct cmpnt; destruct (sizeof_fgtyp gt < length indeterminate_val); try (inversion Heval; subst s rs; split); try done.
  1-16 : rewrite PVM.Lemmas.find_add_neq //. 1-16 : unfold PVM.M.SE.eq; intro; move /eqP : H => H; subst v; done.
Qed.

Lemma convert_to_connect_stmt_qcat k d l tl : convert_to_connect_stmt k d (Qcat l tl) =
  Qcat (convert_to_connect_stmt k d l) tl.
Proof. 
  destruct d; simpl; done.
Qed.

Lemma eval_hfstmts_convert_to_connect_stmts_for_comb_helper v l1: 
  (~ In v (fst (List.split l1))) -> forall ss, (forall st : hfstmt ProdVarOrder.T,
      Qin st ss ->
      match st with
      | Snode _ _ 
      | Sreg _ _ 
      | Swhen _ _ _ => False
      | Sfcnct v0 _ | Sinvalid v0 => v0 <> Eid v
      | _ => True
      end) ->
      forall st : hfstmt ProdVarOrder.T,
        Qin st
          (fold_left
            (fun (a : HiFP.hfstmt_seq) (p : PVM.key * def_expr) =>
              convert_to_connect_stmt (fst p) (snd p) a) l1 
            ss) ->
        match st with
        | Snode _ _ 
        | Sreg _ _ 
        | Swhen _ _ _ => False
        | Sfcnct v0 _ | Sinvalid v0 => v0 <> Eid v
        | _ => True
        end.
Proof.
  move : l1. elim; simpl. intros _ ss Hss st Hin. apply Hss; done.
  intros [hd_key hd_de] tl IH Hnotin ss Hss st. apply IH. move : Hnotin; apply contra_not; clear; intro.
    destruct (List.split tl) as [left right]; simpl in *. right; done.
  simpl; clear IH. rewrite -(qcat0s ss).
  rewrite convert_to_connect_stmt_qcat. destruct hd_de; simpl; try done.
  (* invalid *)
  intros. destruct (Qin st0 ss) eqn : Hin. apply Hss; done. clear Hin. rewrite orb_false_r in H.
  destruct st0; try done. move : Hnotin; apply contra_not; intro. subst h. move /eqP : H => H; inversion H; subst v.
  destruct (List.split tl); simpl. left; done.
  (* cnct *)
  intros. destruct (Qin st0 ss) eqn : Hin. apply Hss; done. clear Hin. rewrite orb_false_r in H.
  destruct st0; try done. move : Hnotin; apply contra_not; intro. subst h0. move /andP : H => [H _]. 
  move /eqP : H => H; inversion H; subst v. destruct (List.split tl); simpl. left; done.
Qed.

Lemma eval_hfstmts_convert_to_connect_stmts_for_comb conn_map init_s tmap rs s v : 
  match PVM.find v tmap with
  | Some (gt, Out_port) 
  | Some (gt, Wire) => Sem_HiFP.eval_hfstmts (convert_to_connect_stmts conn_map) (PVM.empty bits) (PVM.empty bits) init_s tmap = Some (rs, s) -> 
      match PVM.find v conn_map with
      | Some (D_fexpr e) => Sem_HiFP.eval_hfexpr e init_s tmap = PVM.find v s
      | Some (D_invalidated _) => 
          if (length indeterminate_val > sizeof_fgtyp gt) then Some (take (sizeof_fgtyp gt) indeterminate_val) = PVM.find v s
          else Some (zext ((sizeof_fgtyp gt) - (length indeterminate_val)) indeterminate_val) = PVM.find v s
      | _ => True
      end
  | _ => True
  end.
Proof. 
  case Hcmpnt : (PVM.find v tmap) => [[gt cmpnt]|]; try done. destruct cmpnt; try done.
  - (* outport *)
    intros Heval. destruct (PVM.find v conn_map) as [de|] eqn : Hcm; try done. destruct de as [gt_e|e].
    + (* invalid *) 
    remember (convert_to_connect_stmts conn_map) as cmlist.
    rewrite /convert_to_connect_stmts PVM.fold_1 in Heqcmlist. 
    apply CEP.Lemmas.find_some_mapsto in Hcm. apply CEP.Lemmas.F.elements_mapsto_iff in Hcm.
    remember (PVM.elements conn_map) as elements. apply InA_alt in Hcm. destruct Hcm as [[v' e'] [Heq Hin]].
    destruct Heq as [Heq0 Heq1]. simpl in Heq0; simpl in Heq1. move /eqP : Heq0 => Heq0; subst v' e'.
    destruct (in_split _ _ Hin) as [l1 [l2 Helements]]. subst elements.
    rewrite Helements in Heqcmlist. rewrite fold_left_app in Heqcmlist. simpl in Heqcmlist.
    remember (fold_left (fun (a : HiFP.hfstmt_seq) (p : PVM.key * def_expr) => convert_to_connect_stmt (fst p) (snd p) a) l1 (Qnil _)) as ss_prefix.
    remember (fold_left (fun (a : HiFP.hfstmt_seq) (p : PVM.key * def_expr) => convert_to_connect_stmt (fst p) (snd p) a) l2 (Qcons (Sinvalid (Eid v)) ss_prefix)) as ss_suffix.
    subst cmlist.
    assert (Heqss_suffix' : ss_suffix = Qcat (fold_left
                 (fun (a : HiFP.hfstmt_seq) (p : PVM.key * def_expr) =>
                  convert_to_connect_stmt (fst p) (snd p) a) l2 (Qnil ProdVarOrder.T)) (Qcons (Sinvalid (Eid v)) ss_prefix)). {
      move : Heqss_suffix; clear; intro. remember (Qcons (Sinvalid (Eid v)) ss_prefix) as res. clear Heqres. subst ss_suffix; clear.
      rewrite -fold_left_qcat. simpl. done. }
    clear Heqss_suffix.
    rewrite Heqss_suffix' in Heval. apply eval_hfstmts_Qcat_exists in Heval. destruct Heval as [temp_s [temp_rs [Heval2 Heval1]]].
    assert (Htemp : PVM.find v temp_s = None). { 
      assert (Hnodup : ~ In v (fst (List.split l2))). {
        specialize (PVM.elements_3w conn_map) as Hnodup. rewrite Helements in Hnodup. move : Hnodup; clear; intro.
        specialize (NoDupA_notin Hnodup) as [_ Hnotin]; done. }
      clear Heval1. assert (Sem_HiFP.eval_hfstmts (Qnil ProdVarOrder.T) (PVM.empty bits) (PVM.empty bits) init_s tmap = Some (PVM.empty bits, PVM.empty bits)) by (simpl; done).
      specialize (eval_hfstmts_notin_none H Hnodup Heval2) as [Hhelper _]. apply Hhelper; done.
    }
    clear Heval2 Heqss_suffix'. simpl in Heval1. rewrite Hcmpnt in Heval1. destruct (sizeof_fgtyp gt < length indeterminate_val).
    (* take *)
    remember (take (sizeof_fgtyp gt) indeterminate_val) as val; clear Heqval.
    assert (Hprefix : PVM.find v s = PVM.find v (PVM.add v val temp_s)).
      assert (Hnotin : ~ In v (fst (List.split l1))). 
      { specialize (PVM.elements_3w conn_map) as Hnodup. rewrite Helements in Hnodup. move : Hnodup; clear; intro. specialize (NoDupA_notin Hnodup) as [Hnotin _]; done. }
      assert (Hhypo : forall st, Qin st ss_prefix ->
      match st with 
      | Snode _ _ 
      | Sreg _ _
      | Swhen _ _ _ => False
      | Sfcnct v0 _ 
      | Sinvalid v0 => v0 <> Eid v
      | _ => True
      end).
      rewrite Heqss_prefix; move : Hnotin Hin; clear.
    intros Hnotin Hin. apply eval_hfstmts_convert_to_connect_stmts_for_comb_helper; intros; try done.
    specialize (eval_hfstmts_notinss_findeq Hhypo Heval1) as [Hhelper _]; done.
    rewrite Hprefix HiFP.PCELemmas.find_add_eq //. apply CEP.SE.eq_refl.
    (* ext *)
    remember (zext (sizeof_fgtyp gt - length indeterminate_val) indeterminate_val) as val; clear Heqval.
    assert (Hprefix : PVM.find v s = PVM.find v (PVM.add v val temp_s)).
      assert (Hnotin : ~ In v (fst (List.split l1))). 
      { specialize (PVM.elements_3w conn_map) as Hnodup. rewrite Helements in Hnodup. move : Hnodup; clear; intro. specialize (NoDupA_notin Hnodup) as [Hnotin _]; done. }
      assert (Hhypo : forall st, Qin st ss_prefix ->
      match st with 
      | Snode _ _ 
      | Sreg _ _
      | Swhen _ _ _ => False
      | Sfcnct v0 _ 
      | Sinvalid v0 => v0 <> Eid v
      | _ => True
      end).
      rewrite Heqss_prefix; move : Hnotin Hin; clear.
    intros Hnotin Hin. apply eval_hfstmts_convert_to_connect_stmts_for_comb_helper; intros; try done.
    specialize (eval_hfstmts_notinss_findeq Hhypo Heval1) as [Hhelper _]; done.
    rewrite Hprefix HiFP.PCELemmas.find_add_eq //. apply CEP.SE.eq_refl.
    + (* cnct *)
    remember (convert_to_connect_stmts conn_map) as cmlist.
    rewrite /convert_to_connect_stmts PVM.fold_1 in Heqcmlist. 
    apply CEP.Lemmas.find_some_mapsto in Hcm. apply CEP.Lemmas.F.elements_mapsto_iff in Hcm.
    remember (PVM.elements conn_map) as elements. apply InA_alt in Hcm. destruct Hcm as [[v' e'] [Heq Hin]].
    destruct Heq as [Heq0 Heq1]. simpl in Heq0; simpl in Heq1. move /eqP : Heq0 => Heq0; subst v' e'.
    destruct (in_split _ _ Hin) as [l1 [l2 Helements]]. subst elements.
    rewrite Helements in Heqcmlist. rewrite fold_left_app in Heqcmlist. simpl in Heqcmlist.
    remember (fold_left (fun (a : HiFP.hfstmt_seq) (p : PVM.key * def_expr) => convert_to_connect_stmt (fst p) (snd p) a) l1 (Qnil _)) as ss_prefix.
    remember (fold_left (fun (a : HiFP.hfstmt_seq) (p : PVM.key * def_expr) => convert_to_connect_stmt (fst p) (snd p) a) l2 (Qcons (Sfcnct (Eid v) e) ss_prefix)) as ss_suffix.
    subst cmlist.
    assert (Heqss_suffix' : ss_suffix = Qcat (fold_left
                 (fun (a : HiFP.hfstmt_seq) (p : PVM.key * def_expr) =>
                  convert_to_connect_stmt (fst p) (snd p) a) l2 (Qnil ProdVarOrder.T)) (Qcons (Sfcnct (Eid v) e) ss_prefix)). {
      move : Heqss_suffix; clear; intro. remember (Qcons (Sfcnct (Eid v) e) ss_prefix) as res. clear Heqres. subst ss_suffix; clear.
      rewrite -fold_left_qcat. simpl. done. }
    clear Heqss_suffix.
    rewrite Heqss_suffix' in Heval. apply eval_hfstmts_Qcat_exists in Heval. destruct Heval as [temp_s [temp_rs [Heval2 Heval1]]].
    assert (Htemp : PVM.find v temp_s = None). { 
      assert (Hnodup : ~ In v (fst (List.split l2))). {
        specialize (PVM.elements_3w conn_map) as Hnodup. rewrite Helements in Hnodup. move : Hnodup; clear; intro.
        specialize (NoDupA_notin Hnodup) as [_ Hnotin]; done. }
      clear Heval1. assert (Sem_HiFP.eval_hfstmts (Qnil ProdVarOrder.T) (PVM.empty bits) (PVM.empty bits) init_s tmap = Some (PVM.empty bits, PVM.empty bits)) by (simpl; done).
      specialize (eval_hfstmts_notin_none H Hnodup Heval2) as [Hhelper _]. apply Hhelper; done.
    }
    clear Heval2 Heqss_suffix'. simpl in Heval1. rewrite Hcmpnt in Heval1. destruct (Sem_HiFP.eval_hfexpr e init_s tmap) as [val|]; try discriminate.
    assert (Hprefix : PVM.find v s = PVM.find v (PVM.add v val temp_s)).
      assert (Hnotin : ~ In v (fst (List.split l1))). 
      { specialize (PVM.elements_3w conn_map) as Hnodup. rewrite Helements in Hnodup. move : Hnodup; clear; intro. specialize (NoDupA_notin Hnodup) as [Hnotin _]; done. }
      assert (Hhypo : forall st, Qin st ss_prefix ->
      match st with 
      | Snode _ _ 
      | Sreg _ _
      | Swhen _ _ _ => False
      | Sfcnct v0 _ 
      | Sinvalid v0 => v0 <> Eid v
      | _ => True
      end).
      rewrite Heqss_prefix; move : Hnotin Hin; clear.
    intros Hnotin Hin. apply eval_hfstmts_convert_to_connect_stmts_for_comb_helper; intros; try done.
    specialize (eval_hfstmts_notinss_findeq Hhypo Heval1) as [Hhelper _]; done.
    rewrite Hprefix HiFP.PCELemmas.find_add_eq //. apply CEP.SE.eq_refl.
  - (* wire 同上 *)
    intros Heval. destruct (PVM.find v conn_map) as [de|] eqn : Hcm; try done. destruct de as [gt_e|e].
    + (* invalid *) 
    remember (convert_to_connect_stmts conn_map) as cmlist.
    rewrite /convert_to_connect_stmts PVM.fold_1 in Heqcmlist. 
    apply CEP.Lemmas.find_some_mapsto in Hcm. apply CEP.Lemmas.F.elements_mapsto_iff in Hcm.
    remember (PVM.elements conn_map) as elements. apply InA_alt in Hcm. destruct Hcm as [[v' e'] [Heq Hin]].
    destruct Heq as [Heq0 Heq1]. simpl in Heq0; simpl in Heq1. move /eqP : Heq0 => Heq0; subst v' e'.
    destruct (in_split _ _ Hin) as [l1 [l2 Helements]]. subst elements.
    rewrite Helements in Heqcmlist. rewrite fold_left_app in Heqcmlist. simpl in Heqcmlist.
    remember (fold_left (fun (a : HiFP.hfstmt_seq) (p : PVM.key * def_expr) => convert_to_connect_stmt (fst p) (snd p) a) l1 (Qnil _)) as ss_prefix.
    remember (fold_left (fun (a : HiFP.hfstmt_seq) (p : PVM.key * def_expr) => convert_to_connect_stmt (fst p) (snd p) a) l2 (Qcons (Sinvalid (Eid v)) ss_prefix)) as ss_suffix.
    subst cmlist.
    assert (Heqss_suffix' : ss_suffix = Qcat (fold_left
                 (fun (a : HiFP.hfstmt_seq) (p : PVM.key * def_expr) =>
                  convert_to_connect_stmt (fst p) (snd p) a) l2 (Qnil ProdVarOrder.T)) (Qcons (Sinvalid (Eid v)) ss_prefix)). {
      move : Heqss_suffix; clear; intro. remember (Qcons (Sinvalid (Eid v)) ss_prefix) as res. clear Heqres. subst ss_suffix; clear.
      rewrite -fold_left_qcat. simpl. done. }
    clear Heqss_suffix.
    rewrite Heqss_suffix' in Heval. apply eval_hfstmts_Qcat_exists in Heval. destruct Heval as [temp_s [temp_rs [Heval2 Heval1]]].
    assert (Htemp : PVM.find v temp_s = None). { 
      assert (Hnodup : ~ In v (fst (List.split l2))). {
        specialize (PVM.elements_3w conn_map) as Hnodup. rewrite Helements in Hnodup. move : Hnodup; clear; intro.
        specialize (NoDupA_notin Hnodup) as [_ Hnotin]; done. }
      clear Heval1. assert (Sem_HiFP.eval_hfstmts (Qnil ProdVarOrder.T) (PVM.empty bits) (PVM.empty bits) init_s tmap = Some (PVM.empty bits, PVM.empty bits)) by (simpl; done).
      specialize (eval_hfstmts_notin_none H Hnodup Heval2) as [Hhelper _]. apply Hhelper; done.
    }
    clear Heval2 Heqss_suffix'. simpl in Heval1. rewrite Hcmpnt in Heval1. destruct (sizeof_fgtyp gt < length indeterminate_val).
    (* take *)
    remember (take (sizeof_fgtyp gt) indeterminate_val) as val; clear Heqval.
    assert (Hprefix : PVM.find v s = PVM.find v (PVM.add v val temp_s)).
      assert (Hnotin : ~ In v (fst (List.split l1))). 
      { specialize (PVM.elements_3w conn_map) as Hnodup. rewrite Helements in Hnodup. move : Hnodup; clear; intro. specialize (NoDupA_notin Hnodup) as [Hnotin _]; done. }
      assert (Hhypo : forall st, Qin st ss_prefix ->
      match st with 
      | Snode _ _ 
      | Sreg _ _
      | Swhen _ _ _ => False
      | Sfcnct v0 _ 
      | Sinvalid v0 => v0 <> Eid v
      | _ => True
      end).
      rewrite Heqss_prefix; move : Hnotin Hin; clear.
    intros Hnotin Hin. apply eval_hfstmts_convert_to_connect_stmts_for_comb_helper; intros; try done.
    specialize (eval_hfstmts_notinss_findeq Hhypo Heval1) as [Hhelper _]; done.
    rewrite Hprefix HiFP.PCELemmas.find_add_eq //. apply CEP.SE.eq_refl.
    (* ext *)
    remember (zext (sizeof_fgtyp gt - length indeterminate_val) indeterminate_val) as val; clear Heqval.
    assert (Hprefix : PVM.find v s = PVM.find v (PVM.add v val temp_s)).
      assert (Hnotin : ~ In v (fst (List.split l1))). 
      { specialize (PVM.elements_3w conn_map) as Hnodup. rewrite Helements in Hnodup. move : Hnodup; clear; intro. specialize (NoDupA_notin Hnodup) as [Hnotin _]; done. }
      assert (Hhypo : forall st, Qin st ss_prefix ->
      match st with 
      | Snode _ _ 
      | Sreg _ _
      | Swhen _ _ _ => False
      | Sfcnct v0 _ 
      | Sinvalid v0 => v0 <> Eid v
      | _ => True
      end).
      rewrite Heqss_prefix; move : Hnotin Hin; clear.
    intros Hnotin Hin. apply eval_hfstmts_convert_to_connect_stmts_for_comb_helper; intros; try done.
    specialize (eval_hfstmts_notinss_findeq Hhypo Heval1) as [Hhelper _]; done.
    rewrite Hprefix HiFP.PCELemmas.find_add_eq //. apply CEP.SE.eq_refl.
    + (* cnct *)
    remember (convert_to_connect_stmts conn_map) as cmlist.
    rewrite /convert_to_connect_stmts PVM.fold_1 in Heqcmlist. 
    apply CEP.Lemmas.find_some_mapsto in Hcm. apply CEP.Lemmas.F.elements_mapsto_iff in Hcm.
    remember (PVM.elements conn_map) as elements. apply InA_alt in Hcm. destruct Hcm as [[v' e'] [Heq Hin]].
    destruct Heq as [Heq0 Heq1]. simpl in Heq0; simpl in Heq1. move /eqP : Heq0 => Heq0; subst v' e'.
    destruct (in_split _ _ Hin) as [l1 [l2 Helements]]. subst elements.
    rewrite Helements in Heqcmlist. rewrite fold_left_app in Heqcmlist. simpl in Heqcmlist.
    remember (fold_left (fun (a : HiFP.hfstmt_seq) (p : PVM.key * def_expr) => convert_to_connect_stmt (fst p) (snd p) a) l1 (Qnil _)) as ss_prefix.
    remember (fold_left (fun (a : HiFP.hfstmt_seq) (p : PVM.key * def_expr) => convert_to_connect_stmt (fst p) (snd p) a) l2 (Qcons (Sfcnct (Eid v) e) ss_prefix)) as ss_suffix.
    subst cmlist.
    assert (Heqss_suffix' : ss_suffix = Qcat (fold_left
                 (fun (a : HiFP.hfstmt_seq) (p : PVM.key * def_expr) =>
                  convert_to_connect_stmt (fst p) (snd p) a) l2 (Qnil ProdVarOrder.T)) (Qcons (Sfcnct (Eid v) e) ss_prefix)). {
      move : Heqss_suffix; clear; intro. remember (Qcons (Sfcnct (Eid v) e) ss_prefix) as res. clear Heqres. subst ss_suffix; clear.
      rewrite -fold_left_qcat. simpl. done. }
    clear Heqss_suffix.
    rewrite Heqss_suffix' in Heval. apply eval_hfstmts_Qcat_exists in Heval. destruct Heval as [temp_s [temp_rs [Heval2 Heval1]]].
    assert (Htemp : PVM.find v temp_s = None). { 
      assert (Hnodup : ~ In v (fst (List.split l2))). {
        specialize (PVM.elements_3w conn_map) as Hnodup. rewrite Helements in Hnodup. move : Hnodup; clear; intro.
        specialize (NoDupA_notin Hnodup) as [_ Hnotin]; done. }
      clear Heval1. assert (Sem_HiFP.eval_hfstmts (Qnil ProdVarOrder.T) (PVM.empty bits) (PVM.empty bits) init_s tmap = Some (PVM.empty bits, PVM.empty bits)) by (simpl; done).
      specialize (eval_hfstmts_notin_none H Hnodup Heval2) as [Hhelper _]. apply Hhelper; done.
    }
    clear Heval2 Heqss_suffix'. simpl in Heval1. rewrite Hcmpnt in Heval1. destruct (Sem_HiFP.eval_hfexpr e init_s tmap) as [val|]; try discriminate.
    assert (Hprefix : PVM.find v s = PVM.find v (PVM.add v val temp_s)).
      assert (Hnotin : ~ In v (fst (List.split l1))). 
      { specialize (PVM.elements_3w conn_map) as Hnodup. rewrite Helements in Hnodup. move : Hnodup; clear; intro. specialize (NoDupA_notin Hnodup) as [Hnotin _]; done. }
      assert (Hhypo : forall st, Qin st ss_prefix ->
      match st with 
      | Snode _ _ 
      | Sreg _ _
      | Swhen _ _ _ => False
      | Sfcnct v0 _ 
      | Sinvalid v0 => v0 <> Eid v
      | _ => True
      end).
      rewrite Heqss_prefix; move : Hnotin Hin; clear.
    intros Hnotin Hin. apply eval_hfstmts_convert_to_connect_stmts_for_comb_helper; intros; try done.
    specialize (eval_hfstmts_notinss_findeq Hhypo Heval1) as [Hhelper _]; done.
    rewrite Hprefix HiFP.PCELemmas.find_add_eq //. apply CEP.SE.eq_refl.
Qed. 

Lemma eval_hfstmts_convert_to_connect_stmts_for_sequ conn_map init_s tmap rs s v : 
  match PVM.find v tmap with
  | Some (gt, Register) => Sem_HiFP.eval_hfstmts (convert_to_connect_stmts conn_map) (PVM.empty bits) (PVM.empty bits) init_s tmap = Some (rs, s) -> 
      match PVM.find v conn_map with
      | Some (D_fexpr e) => Sem_HiFP.eval_hfexpr e init_s tmap = PVM.find v rs
      | Some (D_invalidated _) => 
          if (length indeterminate_val > sizeof_fgtyp gt) then Some (take (sizeof_fgtyp gt) indeterminate_val) = PVM.find v rs
          else Some (zext ((sizeof_fgtyp gt) - (length indeterminate_val)) indeterminate_val) = PVM.find v rs
      | _ => True
      end
  | _ => True
  end.
Proof. 
  destruct (PVM.find v tmap) as [[gt cmpnt]|] eqn : Hcmpnt; try done. destruct cmpnt; try done.
  intros Heval. destruct (PVM.find v conn_map) as [de|] eqn : Hcm; try done. destruct de as [gt_e|e].
  + (* invalid *) 
  remember (convert_to_connect_stmts conn_map) as cmlist.
  rewrite /convert_to_connect_stmts PVM.fold_1 in Heqcmlist. 
  apply CEP.Lemmas.find_some_mapsto in Hcm. apply CEP.Lemmas.F.elements_mapsto_iff in Hcm.
  remember (PVM.elements conn_map) as elements. apply InA_alt in Hcm. destruct Hcm as [[v' e'] [Heq Hin]].
  destruct Heq as [Heq0 Heq1]. simpl in Heq0; simpl in Heq1. move /eqP : Heq0 => Heq0; subst v' e'.
  destruct (in_split _ _ Hin) as [l1 [l2 Helements]]. subst elements.
  rewrite Helements in Heqcmlist. rewrite fold_left_app in Heqcmlist. simpl in Heqcmlist.
  remember (fold_left (fun (a : HiFP.hfstmt_seq) (p : PVM.key * def_expr) => convert_to_connect_stmt (fst p) (snd p) a) l1 (Qnil _)) as ss_prefix.
  remember (fold_left (fun (a : HiFP.hfstmt_seq) (p : PVM.key * def_expr) => convert_to_connect_stmt (fst p) (snd p) a) l2 (Qcons (Sinvalid (Eid v)) ss_prefix)) as ss_suffix.
  subst cmlist.
  assert (Heqss_suffix' : ss_suffix = Qcat (fold_left
                 (fun (a : HiFP.hfstmt_seq) (p : PVM.key * def_expr) =>
                  convert_to_connect_stmt (fst p) (snd p) a) l2 (Qnil ProdVarOrder.T)) (Qcons (Sinvalid (Eid v)) ss_prefix)). rewrite -fold_left_qcat qcat0s //. clear Heqss_suffix.
  rewrite Heqss_suffix' in Heval. apply eval_hfstmts_Qcat_exists in Heval. destruct Heval as [temp_s [temp_rs [Heval2 Heval1]]].
  assert (Htemp : PVM.find v temp_rs = None). { 
    assert (Hnodup : ~ In v (fst (List.split l2))). {
      specialize (PVM.elements_3w conn_map) as Hnodup. rewrite Helements in Hnodup. move : Hnodup; clear; intro.
      specialize (NoDupA_notin Hnodup) as [_ Hnotin]; done. }
    clear Heval1. assert (Sem_HiFP.eval_hfstmts (Qnil ProdVarOrder.T) (PVM.empty bits) (PVM.empty bits) init_s tmap = Some (PVM.empty bits, PVM.empty bits)) by (simpl; done).
    specialize (eval_hfstmts_notin_none H Hnodup Heval2) as [_ Hhelper]. apply Hhelper; done.
  }
  clear Heval2 Heqss_suffix'. simpl in Heval1. rewrite Hcmpnt in Heval1. destruct (sizeof_fgtyp gt < length indeterminate_val).
  (* take *)
  remember (take (sizeof_fgtyp gt) indeterminate_val) as val; clear Heqval.
  assert (Hprefix : PVM.find v rs = PVM.find v (PVM.add v val temp_rs)). 
    assert (Hnotin : ~ In v (fst (List.split l1))). 
      { specialize (PVM.elements_3w conn_map) as Hnodup. rewrite Helements in Hnodup. move : Hnodup; clear; intro. specialize (NoDupA_notin Hnodup) as [Hnotin _]; done. }
      assert (Hhypo : forall st, Qin st ss_prefix ->
      match st with 
      | Snode _ _ 
      | Sreg _ _ 
      | Swhen _ _ _ => False
      | Sfcnct v0 _ 
      | Sinvalid v0 => v0 <> Eid v
      | _ => True
      end). 
      rewrite Heqss_prefix; move : Hnotin Hin; clear.
    intros Hnotin Hin. apply eval_hfstmts_convert_to_connect_stmts_for_comb_helper; intros; try done.
    specialize (eval_hfstmts_notinss_findeq Hhypo Heval1) as [_ Hhelper]; done.
  rewrite Hprefix HiFP.PCELemmas.find_add_eq //. apply CEP.SE.eq_refl.
  (* ext *)
  remember (zext (sizeof_fgtyp gt - length indeterminate_val) indeterminate_val) as val; clear Heqval.
  assert (Hprefix : PVM.find v rs = PVM.find v (PVM.add v val temp_rs)). 
    assert (Hnotin : ~ In v (fst (List.split l1))). 
      { specialize (PVM.elements_3w conn_map) as Hnodup. rewrite Helements in Hnodup. move : Hnodup; clear; intro. specialize (NoDupA_notin Hnodup) as [Hnotin _]; done. }
      assert (Hhypo : forall st, Qin st ss_prefix ->
      match st with 
      | Snode _ _ 
      | Sreg _ _ 
      | Swhen _ _ _ => False
      | Sfcnct v0 _ 
      | Sinvalid v0 => v0 <> Eid v
      | _ => True
      end). 
      rewrite Heqss_prefix; move : Hnotin Hin; clear.
    intros Hnotin Hin. apply eval_hfstmts_convert_to_connect_stmts_for_comb_helper; intros; try done.
    specialize (eval_hfstmts_notinss_findeq Hhypo Heval1) as [_ Hhelper]; done.
  rewrite Hprefix HiFP.PCELemmas.find_add_eq //. apply CEP.SE.eq_refl.
  + (* cnct *) 
  remember (convert_to_connect_stmts conn_map) as cmlist.
  rewrite /convert_to_connect_stmts PVM.fold_1 in Heqcmlist. 
  apply CEP.Lemmas.find_some_mapsto in Hcm. apply CEP.Lemmas.F.elements_mapsto_iff in Hcm.
  remember (PVM.elements conn_map) as elements. apply InA_alt in Hcm. destruct Hcm as [[v' e'] [Heq Hin]].
  destruct Heq as [Heq0 Heq1]. simpl in Heq0; simpl in Heq1. move /eqP : Heq0 => Heq0; subst v' e'.
  destruct (in_split _ _ Hin) as [l1 [l2 Helements]]. subst elements.
  rewrite Helements in Heqcmlist. rewrite fold_left_app in Heqcmlist. simpl in Heqcmlist.
  remember (fold_left (fun (a : HiFP.hfstmt_seq) (p : PVM.key * def_expr) => convert_to_connect_stmt (fst p) (snd p) a) l1 (Qnil _)) as ss_prefix.
  remember (fold_left (fun (a : HiFP.hfstmt_seq) (p : PVM.key * def_expr) => convert_to_connect_stmt (fst p) (snd p) a) l2 (Qcons (Sfcnct (Eid v) e) ss_prefix)) as ss_suffix.
  subst cmlist.
  assert (Heqss_suffix' : ss_suffix = Qcat (fold_left
                 (fun (a : HiFP.hfstmt_seq) (p : PVM.key * def_expr) =>
                  convert_to_connect_stmt (fst p) (snd p) a) l2 (Qnil ProdVarOrder.T)) (Qcons (Sfcnct (Eid v) e) ss_prefix)). rewrite -fold_left_qcat qcat0s //. clear Heqss_suffix.
  rewrite Heqss_suffix' in Heval. apply eval_hfstmts_Qcat_exists in Heval. destruct Heval as [temp_s [temp_rs [Heval2 Heval1]]].
  assert (Htemp : PVM.find v temp_rs = None). { 
    assert (Hnodup : ~ In v (fst (List.split l2))). {
      specialize (PVM.elements_3w conn_map) as Hnodup. rewrite Helements in Hnodup. move : Hnodup; clear; intro.
      specialize (NoDupA_notin Hnodup) as [_ Hnotin]; done. }
    clear Heval1. assert (Sem_HiFP.eval_hfstmts (Qnil ProdVarOrder.T) (PVM.empty bits) (PVM.empty bits) init_s tmap = Some (PVM.empty bits, PVM.empty bits)) by (simpl; done).
    specialize (eval_hfstmts_notin_none H Hnodup Heval2) as [_ Hhelper]. apply Hhelper; done.
  }
  clear Heval2 Heqss_suffix'. simpl in Heval1. rewrite Hcmpnt in Heval1. destruct (Sem_HiFP.eval_hfexpr e init_s tmap) as [val|]; try discriminate.
  assert (Hprefix : PVM.find v rs = PVM.find v (PVM.add v val temp_rs)). 
    assert (Hnotin : ~ In v (fst (List.split l1))). 
      { specialize (PVM.elements_3w conn_map) as Hnodup. rewrite Helements in Hnodup. move : Hnodup; clear; intro. specialize (NoDupA_notin Hnodup) as [Hnotin _]; done. }
      assert (Hhypo : forall st, Qin st ss_prefix ->
      match st with 
      | Snode _ _ 
      | Sreg _ _ 
      | Swhen _ _ _ => False
      | Sfcnct v0 _ 
      | Sinvalid v0 => v0 <> Eid v
      | _ => True
      end). 
      rewrite Heqss_prefix; move : Hnotin Hin; clear.
    intros Hnotin Hin. apply eval_hfstmts_convert_to_connect_stmts_for_comb_helper; intros; try done.
    specialize (eval_hfstmts_notinss_findeq Hhypo Heval1) as [_ Hhelper]; done.
  rewrite Hprefix HiFP.PCELemmas.find_add_eq //. apply CEP.SE.eq_refl.
Qed.

Lemma eval_fexpr_PVM_included_eq e init_s1 init_s2 tmap bs : pvm_included init_s1 init_s2 -> Sem_HiFP.eval_hfexpr e init_s1 tmap = Some bs ->
  Sem_HiFP.eval_hfexpr e init_s2 tmap = Some bs.
Proof. 
  unfold pvm_included. intro Heq. move : e bs; elim.
  simpl; done.
  (* cast *)
  simpl; intros. destruct u; try (apply H; done). 
  1,2 : destruct (Sem_HiFP.eval_hfexpr h init_s1 tmap); try discriminate; inversion H0; subst bs; rewrite (H b) //.
  (* unop *)
  simpl; intros. destruct (Sem_HiFP.eval_hfexpr h init_s1 tmap); try discriminate.
  destruct (Sem_HiFP.type_of_hfexpr h tmap); try discriminate. rewrite (H b) //.
  (* binop *)
  simpl; intros. destruct (Sem_HiFP.eval_hfexpr h init_s1 tmap); try discriminate.
  destruct (Sem_HiFP.eval_hfexpr h0 init_s1 tmap); try discriminate.
  destruct (Sem_HiFP.type_of_hfexpr h tmap); try discriminate. 
  destruct (Sem_HiFP.type_of_hfexpr h0 tmap); try discriminate. rewrite (H b). rewrite (H0 b0) //. done.
  (* mux *)
  simpl; intros. destruct (Sem_HiFP.eval_hfexpr h init_s1 tmap); try discriminate.
  destruct (Sem_HiFP.type_of_hfexpr h0 tmap); try discriminate. destruct f; try discriminate. 
    destruct (Sem_HiFP.type_of_hfexpr h1 tmap); try discriminate. destruct f; try discriminate. 
    destruct (Sem_HiFP.eval_hfexpr h0 init_s1 tmap); try discriminate.
    destruct (Sem_HiFP.eval_hfexpr h1 init_s1 tmap); try discriminate.
    rewrite (H b); try done. rewrite (H0 b0); try done. rewrite (H1 b1); try done.
    (* same *)
    destruct (Sem_HiFP.type_of_hfexpr h1 tmap); try discriminate. destruct f; try discriminate. 
    destruct (Sem_HiFP.eval_hfexpr h0 init_s1 tmap); try discriminate.
    destruct (Sem_HiFP.eval_hfexpr h1 init_s1 tmap); try discriminate.
    rewrite (H b); try done. rewrite (H0 b0); try done. rewrite (H1 b1); try done.
  (* ref *)
  simpl; intros. destruct h; try discriminate. move : H; apply Heq.
Qed.

Lemma eval_hfexpr_Emux_eq_true_false cond init_s tmap: match Sem_HiFP.eval_hfexpr cond init_s tmap with
  | Some valc => forall e1 e2, if (~~ is_zero valc) then Sem_HiFP.eval_hfexpr (Emux cond e1 e2) = Sem_HiFP.eval_hfexpr e1
                 else Sem_HiFP.eval_hfexpr (Emux cond e1 e2) = Sem_HiFP.eval_hfexpr e2 
  | _ => True
  end.
Proof. (* mux对长度有要求，但一般情况并不检查 *)
  destruct (Sem_HiFP.eval_hfexpr cond init_s tmap) as [valc|] eqn : Hcond; try done. 
Admitted.

Lemma eval_hfstmts_ExpandBranches_funs_find_for_comb_helper v gt init_s tmap :
  PVM.find v tmap = Some (gt, Out_port) \/ PVM.find v tmap = Some (gt, Wire) ->
  forall (ss : HiFP.hfstmt_seq) (rs s rs0 s0 : PVM.t bits),
    (~ exists r, Qin (Sreg v r) ss) /\ (~ exists e, Qin (Snode v e) ss) -> 
    Sem_HiFP.eval_hfstmts ss rs0 s0 init_s tmap = Some (rs, s) ->
    forall val, PVM.find v s = Some val ->
    forall (old_conn_map : PVM.t def_expr), (forall val0, PVM.find v s0 = Some val0 ->
    match PVM.find v old_conn_map with
    | Some (D_fexpr e') => Sem_HiFP.eval_hfexpr e' init_s tmap = Some val0
    | Some (D_invalidated _) => 
          if (length indeterminate_val > sizeof_fgtyp gt) then take (sizeof_fgtyp gt) indeterminate_val = val0
          else zext ((sizeof_fgtyp gt) - (length indeterminate_val)) indeterminate_val = val0
    | _ => False
    end) ->
    forall conn_map : PVM.t def_expr,
    ExpandBranches_funs ss old_conn_map tmap = Some conn_map ->
    match PVM.find v conn_map with
    | Some (D_fexpr e) => Sem_HiFP.eval_hfexpr e init_s tmap = Some val 
    | Some (D_invalidated _) => 
          if (length indeterminate_val > sizeof_fgtyp gt) then take (sizeof_fgtyp gt) indeterminate_val = val
          else zext ((sizeof_fgtyp gt) - (length indeterminate_val)) indeterminate_val = val
    | _ => False
    end
with eval_hfstmt_ExpandBranches_funs_find_for_comb_helper st v gt init_s tmap :
  PVM.find v tmap = Some (gt, Out_port) \/ PVM.find v tmap = Some (gt, Wire) ->
  forall (rs_temp s_temp rs0 s0 : PVM.t bits),
  Sem_HiFP.eval_hfstmt st rs0 s0 init_s tmap = Some (rs_temp, s_temp) ->
  forall (old_conn_map : PVM.t def_expr), (forall val0, PVM.find v s0 = Some val0 ->
    match PVM.find v old_conn_map with
    | Some (D_fexpr e') => Sem_HiFP.eval_hfexpr e' init_s tmap = Some val0
    | Some (D_invalidated _) => 
          if (length indeterminate_val > sizeof_fgtyp gt) then take (sizeof_fgtyp gt) indeterminate_val = val0
          else zext ((sizeof_fgtyp gt) - (length indeterminate_val)) indeterminate_val = val0
    | _ => False
    end) ->
    match st with
    | Swhen cond ss_true ss_false => forall true_conn_map false_conn_map,
                        ExpandBranches_funs ss_true old_conn_map tmap = Some true_conn_map -> 
                        ExpandBranches_funs ss_false old_conn_map tmap = Some false_conn_map ->
                        forall val, PVM.find v s_temp = Some val ->
                        match PVM.find v (combine_when_connections cond true_conn_map false_conn_map) with
                        | Some (D_invalidated _) =>
                                if sizeof_fgtyp gt < length indeterminate_val
                                then take (sizeof_fgtyp gt) indeterminate_val = val
                                else
                                zext (sizeof_fgtyp gt - length indeterminate_val) indeterminate_val = val
                        | Some (D_fexpr e') => Sem_HiFP.eval_hfexpr e' init_s tmap = Some val
                        | None => False
                        end
    | _ => True
    end. 
Proof. clear eval_hfstmts_ExpandBranches_funs_find_for_comb_helper. intro Hcmpnt.
  elim. 
  - simpl; intros rs s rs0 s0 Hnotin Heval val Hval old_conn_map Hinit conn_map Hexpand_branches.
    inversion Heval; subst rs s; clear Heval. inversion Hexpand_branches; subst conn_map; clear Hexpand_branches. apply Hinit; done.
  - intros st sts IH rs s rs0 s0 Hnotin Heval val Hval old_conn_map Hinit conn_map Hexpand_branches.
    simpl in Heval. destruct (Sem_HiFP.eval_hfstmt st rs0 s0 init_s tmap) as [[rs_temp s_temp]|] eqn : Heval_temp; try discriminate.
    simpl in Hexpand_branches. destruct (ExpandBranch_fun st old_conn_map) as [temp_conn_map|] eqn : Hexpand_branches_temp; try discriminate.
    move : conn_map Hexpand_branches. apply IH with (rs := rs) (s := s) (rs0 := rs_temp) (s0 := s_temp); try done. split; move : Hnotin => [Hnotin0 Hnotin1].
    (* not in *)
    move : Hnotin0; apply contra_not; intro. destruct H as [r H]; exists r; simpl. rewrite H orb_true_r //.
    move : Hnotin1; apply contra_not; intro. destruct H as [e H]; exists e; simpl. rewrite H orb_true_r //.
    (* find temp *)
    assert ((~ exists r, hfstmt_eqn st (Sreg v r)) /\ (~ exists e, hfstmt_eqn st (Snode v e))). {
      split; move : Hnotin => [Hnotin0 Hnotin1].
      move : Hnotin0; apply contra_not; intro. destruct H as [r H]; exists r; simpl. rewrite H orb_true_l //.
      move : Hnotin1; apply contra_not; intro. destruct H as [e H]; exists e; simpl. rewrite H orb_true_l //. }
    move : H; clear IH Hnotin Heval sts rs. intros Hnotin val_temp Hval_temp.
    case Hst : st => [||var reg|||var node_e|ref e|ref|cond ss_true ss_false]; subst st.
    + (* skip, wire *)
      1,2,4,5 : simpl in Hexpand_branches_temp; inversion Hexpand_branches_temp; subst old_conn_map; clear Hexpand_branches_temp;
      simpl in Heval_temp; inversion Heval_temp; subst rs0 s0; clear Heval_temp; apply Hinit in Hval_temp; done.
    + (* reg *) 
      simpl in Hexpand_branches_temp. destruct (type reg); try discriminate. inversion Hexpand_branches_temp; subst temp_conn_map; clear Hexpand_branches_temp.
      rewrite HiFP.PCELemmas.find_add_neq.
      simpl in Heval_temp. destruct (PVM.find var init_s); try discriminate. inversion Heval_temp; subst rs_temp s_temp; clear Heval_temp. apply Hinit in Hval_temp; done.
      move : Hnotin => [Hnotin _]. move : Hnotin; apply contra_not; intro. exists reg; simpl. move /eqP : H => H; subst v. rewrite eq_refl; rewrite eq_refl; simpl; done.
    + (* node *) 
      simpl in Hexpand_branches_temp. inversion Hexpand_branches_temp; subst temp_conn_map; clear Hexpand_branches_temp.
      simpl in Heval_temp. destruct (Sem_HiFP.eval_hfexpr node_e init_s tmap); try discriminate. inversion Heval_temp; subst rs_temp s_temp; clear Heval_temp. 
      rewrite HiFP.PCELemmas.find_add_neq in Hval_temp. apply Hinit in Hval_temp; done.
      move : Hnotin => [_ Hnotin]. move : Hnotin; apply contra_not; intro. exists node_e; simpl. move /eqP : H => H; subst v. rewrite eq_refl; rewrite eq_refl; simpl; done.
    + (* fcnct *) 
      simpl in Hexpand_branches_temp. case Href : ref => [var|||]; subst ref; try discriminate. inversion Hexpand_branches_temp; subst temp_conn_map; clear Hexpand_branches_temp.
      destruct (v == var) eqn : Heq.
      * move /eqP : Heq => Heq; subst var. rewrite HiFP.PCELemmas.find_add_eq; try apply CEP.SE.eq_refl.
        simpl in Heval_temp. destruct Hcmpnt as [Hcmpnt|Hcmpnt].
        (* outport *)
        rewrite Hcmpnt in Heval_temp. destruct (Sem_HiFP.eval_hfexpr e init_s tmap) as [val_e|]; try discriminate.
        inversion Heval_temp; subst rs_temp s_temp; clear Heval_temp. rewrite HiFP.PCELemmas.find_add_eq in Hval_temp. done.
        apply CEP.SE.eq_refl.
        (* wire *)
        rewrite Hcmpnt in Heval_temp. destruct (Sem_HiFP.eval_hfexpr e init_s tmap) as [val_e|]; try discriminate.
        inversion Heval_temp; subst rs_temp s_temp; clear Heval_temp. rewrite HiFP.PCELemmas.find_add_eq in Hval_temp. done.
        apply CEP.SE.eq_refl.
      * rewrite HiFP.PCELemmas.find_add_neq. 
        simpl in Heval_temp. destruct (PVM.find var tmap) as [[gt_var cmpnt_var]|]; try discriminate.
        destruct cmpnt_var; destruct (Sem_HiFP.eval_hfexpr e init_s tmap) as [val_e|]; try discriminate; inversion Heval_temp; subst rs_temp s_temp; clear Heval_temp;
        try rewrite HiFP.PCELemmas.find_add_neq in Hval_temp; try (apply Hinit; done). 1-8 : move /eqP : Heq => Heq; move : Heq; apply contra_not; intro; unfold CEP.SE.eq in H; move /eqP : H => H; subst v; done.
    + (* invalid *) 
      simpl in Hexpand_branches_temp. case Href : ref => [var|||]; subst ref; try discriminate. destruct (PVM.find var tmap) as [[gt' cmpnt]|]; try discriminate.
      inversion Hexpand_branches_temp; subst temp_conn_map; clear Hexpand_branches_temp Hnotin. 
      destruct (v == var) eqn : Heq.
      * move /eqP : Heq => Heq; subst var. rewrite HiFP.PCELemmas.find_add_eq; try apply CEP.SE.eq_refl.
        simpl in Heval_temp. destruct Hcmpnt as [Hcmpnt|Hcmpnt].
        (* outport *)
        rewrite Hcmpnt in Heval_temp. destruct (sizeof_fgtyp gt < length indeterminate_val).
        - (* take *)
          inversion Heval_temp; subst rs_temp s_temp; clear Heval_temp; rewrite HiFP.PCELemmas.find_add_eq in Hval_temp.
          inversion Hval_temp; done. apply CEP.SE.eq_refl.
        - (* ext *)
          inversion Heval_temp; subst rs_temp s_temp; clear Heval_temp. rewrite HiFP.PCELemmas.find_add_eq in Hval_temp.
          inversion Hval_temp; done. apply CEP.SE.eq_refl.
        (* wire *)
        rewrite Hcmpnt in Heval_temp. destruct (sizeof_fgtyp gt < length indeterminate_val).
        - (* take *)
          inversion Heval_temp; subst rs_temp s_temp; clear Heval_temp; rewrite HiFP.PCELemmas.find_add_eq in Hval_temp.
          inversion Hval_temp; done. apply CEP.SE.eq_refl.
        - (* ext *)
          inversion Heval_temp; subst rs_temp s_temp; clear Heval_temp. rewrite HiFP.PCELemmas.find_add_eq in Hval_temp.
          inversion Hval_temp; done. apply CEP.SE.eq_refl.
      * rewrite HiFP.PCELemmas.find_add_neq. 
        simpl in Heval_temp. destruct (PVM.find var tmap) as [[gt_var cmpnt_var]|]; try discriminate.
        destruct cmpnt_var; destruct (sizeof_fgtyp gt_var < length indeterminate_val); inversion Heval_temp; subst rs_temp s_temp; clear Heval_temp;
        try rewrite HiFP.PCELemmas.find_add_neq in Hval_temp; try (apply Hinit; done). 1-15 : move /eqP : Heq => Heq; move : Heq; apply contra_not; intro; unfold CEP.SE.eq in H; move /eqP : H => H; subst v; done. 
    + (* when *)
      simpl in Hexpand_branches_temp. destruct (ExpandBranches_funs ss_true old_conn_map tmap) as [true_conn_map|] eqn : Hexpand_true; try discriminate.
      destruct (ExpandBranches_funs ss_false old_conn_map tmap) as [false_conn_map|] eqn : Hexpand_false; try discriminate. 
      inversion Hexpand_branches_temp; subst temp_conn_map; clear Hexpand_branches_temp.
      specialize (eval_hfstmt_ExpandBranches_funs_find_for_comb_helper _ _ _ _ _ Hcmpnt _ _ _ _ Heval_temp _ Hinit) as Hwhen; simpl in Hwhen;
        clear eval_hfstmt_ExpandBranches_funs_find_for_comb_helper. specialize (Hwhen _ _ Hexpand_true Hexpand_false _ Hval_temp). done.

  clear eval_hfstmt_ExpandBranches_funs_find_for_comb_helper.
  intros Hcmpnt rs_temp s_temp rs0 s0 Heval old_conn_map Hinit.
  case Hst : st => [||var reg|||var node_e|ref e|ref|cond ss_true ss_false]; subst st; try done. intros true_conn_map false_conn_map Hexpand_true Hexpand_false val Hval.
  simpl in Heval. destruct (Sem_HiFP.eval_hfexpr cond init_s tmap) as [valc|] eqn : Hvalc; try discriminate. destruct (~~ is_zero valc) eqn : Hcond.
  - (* when go to true *)
    clear Hexpand_false. 
    assert ((~ exists r, Qin (Sreg v r) ss_true) /\ (~ exists e, Qin (Snode v e) ss_true)) by admit.
    specialize (eval_hfstmts_ExpandBranches_funs_find_for_comb_helper _ _ _ _ Hcmpnt _ _ _ _ _ H Heval _ Hval _ Hinit _ Hexpand_true) as Htrue; 
      clear eval_hfstmts_ExpandBranches_funs_find_for_comb_helper. unfold combine_when_connections. rewrite PVM.Lemmas.F.map2_1bis; try done.
    destruct (PVM.find v true_conn_map) as [de_true|] eqn : Hde_true; try done. destruct de_true as [gt_e_true|e_true].
    + (* true is invlid *) 
      destruct (PVM.M.find v false_conn_map) as [de_false|]; try done. destruct de_false.
      * (* false is invalid *) 
        specialize (eval_hfexpr_Emux_eq_true_false cond init_s tmap) as Hmux. rewrite Hvalc Hcond in Hmux. rewrite Hmux.
        unfold Sem_HiFP.indeterminate_cst. admit. (* eval_hfexpr const 稍微与invalid有些冲突*)
      * (* false is cnct *) 
        specialize (eval_hfexpr_Emux_eq_true_false cond init_s tmap) as Hmux. rewrite Hvalc Hcond in Hmux. rewrite Hmux.
        unfold Sem_HiFP.indeterminate_cst. admit. (* eval_hfexpr const 稍微与invalid有些冲突*)
    + (* true is cnct *) 
      destruct (PVM.M.find v false_conn_map) as [de_false|]; try done. destruct de_false as [gt_e_false|e_false].
      * (* false is invalid *) 
        specialize (eval_hfexpr_Emux_eq_true_false cond init_s tmap) as Hmux. rewrite Hvalc Hcond in Hmux. rewrite Hmux //.
      * (* false is cnct *) destruct (e_true == e_false) eqn : Heq; try done.
        specialize (eval_hfexpr_Emux_eq_true_false cond init_s tmap) as Hmux. rewrite Hvalc Hcond in Hmux. rewrite Hmux //.
  - (* when go to false *)
    clear Hexpand_true. 
    assert ((~ exists r, Qin (Sreg v r) ss_false) /\ (~ exists e, Qin (Snode v e) ss_false)) by admit.
    specialize (eval_hfstmts_ExpandBranches_funs_find_for_comb_helper _ _ _ _ Hcmpnt _ _ _ _ _ H Heval _ Hval _ Hinit _ Hexpand_false) as Hfalse; 
      clear eval_hfstmts_ExpandBranches_funs_find_for_comb_helper. unfold combine_when_connections. rewrite PVM.Lemmas.F.map2_1bis; try done.
    destruct (PVM.find v true_conn_map) as [de_true|] eqn : Hde_true; try done. destruct de_true as [gt_e_true|e_true].
    + (* true is invlid *) 
      destruct (PVM.M.find v false_conn_map) as [de_false|]; try done. destruct de_false.
      * (* false is invalid *) 
        specialize (eval_hfexpr_Emux_eq_true_false cond init_s tmap) as Hmux. rewrite Hvalc Hcond in Hmux. rewrite Hmux.
        unfold Sem_HiFP.indeterminate_cst. admit. (* eval_hfexpr const 稍微与invalid有些冲突*)
      * (* false is cnct *) 
        specialize (eval_hfexpr_Emux_eq_true_false cond init_s tmap) as Hmux. rewrite Hvalc Hcond in Hmux. rewrite Hmux //.
    + (* true is cnct *) 
      destruct (PVM.M.find v false_conn_map) as [de_false|]; try done. destruct de_false as [gt_e_false|e_false].
      * (* false is invalid *) 
        specialize (eval_hfexpr_Emux_eq_true_false cond init_s tmap) as Hmux. rewrite Hvalc Hcond in Hmux. rewrite Hmux.
        unfold Sem_HiFP.indeterminate_cst. admit. (* eval_hfexpr const 稍微与invalid有些冲突*)
      * (* false is cnct *) destruct (e_true == e_false) eqn : Heq. move /eqP : Heq => Heq; subst e_true. done.
        specialize (eval_hfexpr_Emux_eq_true_false cond init_s tmap) as Hmux. rewrite Hvalc Hcond in Hmux. rewrite Hmux //.
Admitted.

Lemma eval_hfstmts_ExpandBranches_funs_find_for_comb ss init_s tmap rs s v : 
  match PVM.find v tmap with
  | Some (gt, Out_port) 
  | Some (gt, Wire) => (~ exists r, Qin (Sreg v r) ss) /\ (~ exists e, Qin (Snode v e) ss) ->
  Sem_HiFP.eval_hfstmts ss (PVM.empty bits) (PVM.empty bits) init_s tmap = Some (rs, s) ->
  forall val, PVM.find v s = Some val ->
  forall conn_map, ExpandBranches_funs ss (PVM.empty def_expr) tmap = Some conn_map -> 
      match PVM.find v conn_map with
      | Some (D_fexpr e) => Sem_HiFP.eval_hfexpr e init_s tmap = Some val
      | Some (D_invalidated _) => 
          if (length indeterminate_val > sizeof_fgtyp gt) then take (sizeof_fgtyp gt) indeterminate_val = val
          else zext ((sizeof_fgtyp gt) - (length indeterminate_val)) indeterminate_val = val
      | _ => False
      end
  | _ => True
  end.
Proof. 
  destruct (PVM.find v tmap) as [[gt cmpnt]|] eqn : Hcmpnt; try done. destruct cmpnt; try done.
  assert (Hcmpnt' : PVM.find v tmap = Some (gt, Out_port) \/ PVM.find v tmap = Some (gt, Wire)) by (left; done).
  intros; move : conn_map H2. apply (eval_hfstmts_ExpandBranches_funs_find_for_comb_helper Hcmpnt' H H0 H1); try done.
  assert (Hcmpnt' : PVM.find v tmap = Some (gt, Out_port) \/ PVM.find v tmap = Some (gt, Wire)) by (right; done).
  intros; move : conn_map H2. apply (eval_hfstmts_ExpandBranches_funs_find_for_comb_helper Hcmpnt' H H0 H1); try done.
Qed. 

Lemma ExpandBranch_fun_none st old_conn_map tmap temp_conn_map v : ExpandBranch_fun st old_conn_map tmap = Some temp_conn_map -> PVM.find v temp_conn_map = None
  -> PVM.find v old_conn_map = None
with ExpandBranches_fun_none ss old_conn_map tmap temp_conn_map v : ExpandBranches_funs ss old_conn_map tmap = Some temp_conn_map -> PVM.find v temp_conn_map = None
  -> PVM.find v old_conn_map = None.
Proof. 
  destruct st; simpl.
  1,2,4,5,6 : intros; inversion H; subst old_conn_map; done.
  (* reg *)
  intros. destruct (type h); try discriminate. inversion H; subst temp_conn_map; clear H.
  apply CEP.Lemmas.not_in_find_none. apply CEP.Lemmas.find_none_not_in in H0. move : H0; apply contra_not.
  intro. apply CEP.Lemmas.F.add_in_iff; right; done.
  (* cnct *)
  intros. destruct h; try discriminate. inversion H; subst temp_conn_map; clear H.
  apply CEP.Lemmas.not_in_find_none. apply CEP.Lemmas.find_none_not_in in H0. move : H0; apply contra_not.
  intro. apply CEP.Lemmas.F.add_in_iff; right; done.
  (* invalid *)
  intros. destruct h; try discriminate. destruct (PVM.find s tmap) as [[gt cmpnt]|]; try discriminate.
  inversion H; subst temp_conn_map; clear H.
  apply CEP.Lemmas.not_in_find_none. apply CEP.Lemmas.find_none_not_in in H0. move : H0; apply contra_not.
  intro. apply CEP.Lemmas.F.add_in_iff; right; done.
  (* when *)
  intros. destruct (ExpandBranches_funs h0 old_conn_map tmap) as [true_conn_map|] eqn : Htrue; try discriminate.
  destruct (ExpandBranches_funs h1 old_conn_map tmap) as [false_conn_map|] eqn : Hfalse; try discriminate.
  inversion H; subst temp_conn_map; clear H. unfold combine_when_connections in H0. 
  rewrite CEP.Lemmas.map2_1bis in H0; try done. destruct (PVM.find v true_conn_map) as [de_true|] eqn : Hfind_true.
  destruct de_true; destruct (PVM.find v false_conn_map) as [de_false|]; try destruct de_false; try destruct (h2 == h3); try discriminate.
  move : Hfalse H0; apply ExpandBranches_fun_none.

  clear ExpandBranches_fun_none. move : ss old_conn_map temp_conn_map. elim. 
  simpl; intros. inversion H; subst temp_conn_map; done.
  simpl; intros hd tl IH; intros. destruct (ExpandBranch_fun hd old_conn_map tmap) eqn : Hexpand; try discriminate.
  apply (IH _ _ H) in H0; clear IH. move : Hexpand H0; apply ExpandBranch_fun_none.
Qed.

Lemma eval_hfstmts_ExpandBranches_funs_find_for_sequ_helper v gt init_s tmap :
  PVM.find v tmap = Some (gt, Register) -> 
  forall (ss : HiFP.hfstmt_seq) (rs s rs0 s0 : PVM.t bits),
    Sem_HiFP.eval_hfstmts ss rs0 s0 init_s tmap = Some (rs, s) ->
    forall val, PVM.find v rs = Some val ->
    forall (old_conn_map : PVM.t def_expr), (forall val0, PVM.find v rs0 = Some val0 ->
    match PVM.find v old_conn_map with
      | Some (D_fexpr e') => Sem_HiFP.eval_hfexpr e' init_s tmap = Some val0
      | Some (D_invalidated _) => 
            if (length indeterminate_val > sizeof_fgtyp gt) then take (sizeof_fgtyp gt) indeterminate_val = val0
            else zext ((sizeof_fgtyp gt) - (length indeterminate_val)) indeterminate_val = val0
      | _ => False
      end) ->
    forall conn_map : PVM.t def_expr,
    ExpandBranches_funs ss old_conn_map tmap = Some conn_map ->
      match PVM.find v conn_map with
      | Some (D_fexpr e) => Sem_HiFP.eval_hfexpr e init_s tmap = Some val 
      | Some (D_invalidated _) => 
            if (length indeterminate_val > sizeof_fgtyp gt) then take (sizeof_fgtyp gt) indeterminate_val = val
            else zext ((sizeof_fgtyp gt) - (length indeterminate_val)) indeterminate_val = val
      | _ => False
      end
with eval_hfstmt_ExpandBranches_funs_find_for_sequ_helper st v gt init_s tmap :
  PVM.find v tmap = Some (gt, Register) -> 
  forall (rs_temp s_temp rs0 s0 : PVM.t bits),
  Sem_HiFP.eval_hfstmt st rs0 s0 init_s tmap = Some (rs_temp, s_temp) ->
  forall (old_conn_map : PVM.t def_expr), (forall val0, PVM.find v rs0 = Some val0 ->
  match PVM.find v old_conn_map with
    | Some (D_fexpr e') => Sem_HiFP.eval_hfexpr e' init_s tmap = Some val0
    | Some (D_invalidated _) => 
          if (length indeterminate_val > sizeof_fgtyp gt) then take (sizeof_fgtyp gt) indeterminate_val = val0
          else zext ((sizeof_fgtyp gt) - (length indeterminate_val)) indeterminate_val = val0
    | _ => False
    end) ->
    match st with
    | Swhen cond ss_true ss_false => forall true_conn_map false_conn_map,
                        ExpandBranches_funs ss_true old_conn_map tmap = Some true_conn_map -> 
                        ExpandBranches_funs ss_false old_conn_map tmap = Some false_conn_map ->
                        forall val, PVM.find v rs_temp = Some val ->
                        match PVM.find v (combine_when_connections cond true_conn_map false_conn_map) with
                          | Some (D_invalidated _) =>
                                  if sizeof_fgtyp gt < length indeterminate_val
                                  then take (sizeof_fgtyp gt) indeterminate_val = val
                                  else
                                  zext (sizeof_fgtyp gt - length indeterminate_val) indeterminate_val = val
                          | Some (D_fexpr e') => Sem_HiFP.eval_hfexpr e' init_s tmap = Some val
                          | None => False
                          end
    | _ => True
    end. 
Proof. intro Hcmpnt.
  elim. clear eval_hfstmts_ExpandBranches_funs_find_for_sequ_helper.
  - simpl; intros rs s rs0 s0 Heval val Hval old_conn_map Hinit conn_map Hexpand_branches.
    inversion Heval; subst rs s; clear Heval. inversion Hexpand_branches; subst conn_map; clear Hexpand_branches. apply Hinit; done.
  - intros st sts IH rs s rs0 s0 Heval val Hval old_conn_map Hinit conn_map Hexpand_branches.
    simpl in Heval. destruct (Sem_HiFP.eval_hfstmt st rs0 s0 init_s tmap) as [[rs_temp s_temp]|] eqn : Heval_temp; try discriminate.
    simpl in Hexpand_branches. destruct (ExpandBranch_fun st old_conn_map) as [temp_conn_map|] eqn : Hexpand_branches_temp; try discriminate.
    move : Hexpand_branches; apply IH with (rs := rs) (s := s) (rs0 := rs_temp) (s0 := s_temp); try done.
    (* find temp *)
    clear IH Heval conn_map sts s. 
    case Hst : st => [||var reg|||var node_e|ref e|ref|cond ss_true ss_false]; subst st.
    + (* skip, wire *) 1,2,4,5 : 
      simpl in Hexpand_branches_temp; inversion Hexpand_branches_temp; subst old_conn_map; clear Hexpand_branches_temp;
      simpl in Heval_temp; inversion Heval_temp; subst rs0 s0; clear Heval_temp; apply Hinit; done.
    + (* reg *) 
      simpl in Hexpand_branches_temp. destruct (type reg); try discriminate. inversion Hexpand_branches_temp; subst temp_conn_map; clear Hexpand_branches_temp.
      simpl in Heval_temp. destruct (PVM.find var init_s) as [val_temp|] eqn : Hval_temp; try discriminate. inversion Heval_temp; subst rs_temp s_temp; clear Heval_temp. intros bs Hfind.
      destruct (v == var) eqn : Heq.
      move /eqP : Heq => Heq; subst v. rewrite PVM.Lemmas.find_add_eq. rewrite PVM.Lemmas.find_add_eq in Hfind. inversion Hfind; subst bs. simpl; done. 1,2 : apply PVM.M.SE.eq_refl.
      rewrite PVM.Lemmas.find_add_neq. rewrite PVM.Lemmas.find_add_neq in Hfind. apply Hinit; done.
      1,2 : move /eqP : Heq => Heq; move : Heq; apply contra_not; intro; unfold CEP.SE.eq in H; move /eqP : H => H; done.
    + (* node *) 
      simpl in Hexpand_branches_temp. inversion Hexpand_branches_temp; subst temp_conn_map; clear Hexpand_branches_temp.
      simpl in Heval_temp. destruct (Sem_HiFP.eval_hfexpr node_e init_s tmap); try discriminate. inversion Heval_temp; subst rs_temp s_temp; clear Heval_temp. done. 
    + (* fcnct *) 
      simpl in Hexpand_branches_temp. case Href : ref => [var|||]; subst ref; try discriminate. inversion Hexpand_branches_temp; subst temp_conn_map; clear Hexpand_branches_temp.
      destruct (v == var) eqn : Heq.
      * move /eqP : Heq => Heq; subst var. rewrite HiFP.PCELemmas.find_add_eq.
        simpl in Heval_temp. rewrite Hcmpnt in Heval_temp. destruct (Sem_HiFP.eval_hfexpr e init_s tmap) as [val_e|]; try discriminate.
        inversion Heval_temp; subst rs_temp s_temp; clear Heval_temp. rewrite HiFP.PCELemmas.find_add_eq //.
        1,2 : apply CEP.SE.eq_refl.
      * rewrite HiFP.PCELemmas.find_add_neq. 
        simpl in Heval_temp. destruct (PVM.find var tmap) as [[gt_var cmpnt_var]|]; try discriminate.
        destruct cmpnt_var; destruct (Sem_HiFP.eval_hfexpr e init_s tmap) as [val_e|]; try discriminate; inversion Heval_temp; subst rs_temp s_temp; clear Heval_temp;
        try rewrite HiFP.PCELemmas.find_add_neq; try done. 1-2 : move /eqP : Heq => Heq; move : Heq; apply contra_not; intro; unfold CEP.SE.eq in H; move /eqP : H => H; subst v; done.
    + (* invalid *) 
      simpl in Hexpand_branches_temp. case Href : ref => [var|||]; subst ref; try discriminate. destruct (PVM.find var tmap) as [[gt' cmpnt]|]; try discriminate.
      inversion Hexpand_branches_temp; subst temp_conn_map; clear Hexpand_branches_temp. 
      destruct (v == var) eqn : Heq.
      * move /eqP : Heq => Heq; subst var. rewrite HiFP.PCELemmas.find_add_eq; try apply CEP.SE.eq_refl.
        simpl in Heval_temp. rewrite Hcmpnt in Heval_temp. destruct (sizeof_fgtyp gt < length indeterminate_val).
        - (* take *)
          inversion Heval_temp; subst rs_temp s_temp; clear Heval_temp. rewrite HiFP.PCELemmas.find_add_eq.
          intros. inversion H; done. apply CEP.SE.eq_refl.
        - (* ext *)
          inversion Heval_temp; subst rs_temp s_temp; clear Heval_temp. rewrite HiFP.PCELemmas.find_add_eq.
          intros. inversion H; done. apply CEP.SE.eq_refl.
      * rewrite HiFP.PCELemmas.find_add_neq. 
        simpl in Heval_temp. destruct (PVM.find var tmap) as [[gt_var cmpnt_var]|]; try discriminate.
        destruct cmpnt_var; destruct (sizeof_fgtyp gt_var < length indeterminate_val); inversion Heval_temp; subst rs_temp s_temp; clear Heval_temp; try done.
        1,2 : rewrite HiFP.PCELemmas.find_add_neq; try done.
        1-3 : move /eqP : Heq => Heq; move : Heq; apply contra_not; intro; unfold CEP.SE.eq in H; move /eqP : H => H; subst v; done. 
    + (* when *)
      simpl in Hexpand_branches_temp. destruct (ExpandBranches_funs ss_true old_conn_map tmap) as [true_conn_map|] eqn : Hexpand_true; try discriminate.
      destruct (ExpandBranches_funs ss_false old_conn_map tmap) as [false_conn_map|] eqn : Hexpand_false; try discriminate. 
      inversion Hexpand_branches_temp; subst temp_conn_map; clear Hexpand_branches_temp. 
      specialize (eval_hfstmt_ExpandBranches_funs_find_for_sequ_helper _ _ _ _ _ Hcmpnt _ _ _ _ Heval_temp _ Hinit) as Hwhen; simpl in Hwhen;
        clear eval_hfstmt_ExpandBranches_funs_find_for_sequ_helper. specialize (Hwhen _ _ Hexpand_true Hexpand_false). done.

  clear eval_hfstmt_ExpandBranches_funs_find_for_sequ_helper. intro Hcmpnt.
  intros rs_temp s_temp rs0 s0 Heval old_conn_map Hinit.
  case Hst : st => [||var reg|||var node_e|ref e|ref|cond ss_true ss_false]; subst st; try done. intros true_conn_map false_conn_map Hexpand_true Hexpand_false val Hval.
  simpl in Heval. destruct (Sem_HiFP.eval_hfexpr cond init_s tmap) as [valc|] eqn : Hvalc; try discriminate. destruct (~~ is_zero valc) eqn : Hcond.
  - (* when go to true *)
    clear Hexpand_false. 
    specialize (eval_hfstmts_ExpandBranches_funs_find_for_sequ_helper _ _ _ _ Hcmpnt _ _ _ _ _ Heval _ Hval _ Hinit _ Hexpand_true) as Htrue; 
      clear eval_hfstmts_ExpandBranches_funs_find_for_sequ_helper. unfold combine_when_connections. rewrite PVM.Lemmas.F.map2_1bis; try done.
    destruct (PVM.find v true_conn_map) as [de_true|] eqn : Hde_true; try done. destruct de_true as [gt_e_true|e_true].
    + (* true is invlid *) 
      destruct (PVM.M.find v false_conn_map) as [de_false|]; try done. destruct de_false.
      * (* false is invalid *) 
        specialize (eval_hfexpr_Emux_eq_true_false cond init_s tmap) as Hmux. rewrite Hvalc Hcond in Hmux. rewrite Hmux.
        unfold Sem_HiFP.indeterminate_cst. admit. (* eval_hfexpr const 稍微与invalid有些冲突*)
      * (* false is cnct *) 
        specialize (eval_hfexpr_Emux_eq_true_false cond init_s tmap) as Hmux. rewrite Hvalc Hcond in Hmux. rewrite Hmux.
        unfold Sem_HiFP.indeterminate_cst. admit. (* eval_hfexpr const 稍微与invalid有些冲突*)
    + (* true is cnct *) 
      destruct (PVM.M.find v false_conn_map) as [de_false|]; try done. destruct de_false as [gt_e_false|e_false].
      * (* false is invalid *) 
        specialize (eval_hfexpr_Emux_eq_true_false cond init_s tmap) as Hmux. rewrite Hvalc Hcond in Hmux. rewrite Hmux //.
      * (* false is cnct *) destruct (e_true == e_false) eqn : Heq; try done.
        specialize (eval_hfexpr_Emux_eq_true_false cond init_s tmap) as Hmux. rewrite Hvalc Hcond in Hmux. rewrite Hmux //.
  - (* when go to false *)
    clear Hexpand_true. 
    specialize (eval_hfstmts_ExpandBranches_funs_find_for_sequ_helper _ _ _ _ Hcmpnt _ _ _ _ _ Heval _ Hval _ Hinit _ Hexpand_false) as Hfalse; 
      clear eval_hfstmts_ExpandBranches_funs_find_for_sequ_helper. unfold combine_when_connections. rewrite PVM.Lemmas.F.map2_1bis; try done.
    destruct (PVM.find v true_conn_map) as [de_true|] eqn : Hde_true; try done. destruct de_true as [gt_e_true|e_true].
    + (* true is invlid *) 
      destruct (PVM.M.find v false_conn_map) as [de_false|]; try done. destruct de_false.
      * (* false is invalid *) 
        specialize (eval_hfexpr_Emux_eq_true_false cond init_s tmap) as Hmux. rewrite Hvalc Hcond in Hmux. rewrite Hmux.
        unfold Sem_HiFP.indeterminate_cst. admit. (* eval_hfexpr const 稍微与invalid有些冲突*)
      * (* false is cnct *) 
        specialize (eval_hfexpr_Emux_eq_true_false cond init_s tmap) as Hmux. rewrite Hvalc Hcond in Hmux. rewrite Hmux //.
    + (* true is cnct *) 
      destruct (PVM.M.find v false_conn_map) as [de_false|]; try done. destruct de_false as [gt_e_false|e_false].
      * (* false is invalid *) 
        specialize (eval_hfexpr_Emux_eq_true_false cond init_s tmap) as Hmux. rewrite Hvalc Hcond in Hmux. rewrite Hmux.
        unfold Sem_HiFP.indeterminate_cst. admit. (* eval_hfexpr const 稍微与invalid有些冲突*)
      * (* false is cnct *) destruct (e_true == e_false) eqn : Heq. move /eqP : Heq => Heq; subst e_true. done.
        specialize (eval_hfexpr_Emux_eq_true_false cond init_s tmap) as Hmux. rewrite Hvalc Hcond in Hmux. rewrite Hmux //.
Admitted.

Lemma eval_hfstmts_ExpandBranches_funs_find_for_sequ ss init_s tmap rs s v : 
  match PVM.find v tmap with
  | Some (gt, Register) => 
  Sem_HiFP.eval_hfstmts ss (PVM.empty bits) (PVM.empty bits) init_s tmap = Some (rs, s) ->
  forall val, PVM.find v rs = Some val ->
  forall conn_map, ExpandBranches_funs ss (PVM.empty def_expr) tmap = Some conn_map -> 
      match PVM.find v conn_map with
      | Some (D_fexpr e) => Sem_HiFP.eval_hfexpr e init_s tmap = Some val
      | Some (D_invalidated _) => 
          if (length indeterminate_val > sizeof_fgtyp gt) then take (sizeof_fgtyp gt) indeterminate_val = val
          else zext ((sizeof_fgtyp gt) - (length indeterminate_val)) indeterminate_val = val
      | _ => False
      end
  | _ => True
  end.
Proof.
  destruct (PVM.find v tmap) as [[gt cmpnt]|] eqn : Hcmpnt; try done. destruct cmpnt; try done.
  intros. move : conn_map H1; apply (eval_hfstmts_ExpandBranches_funs_find_for_sequ_helper Hcmpnt H H0).
  try done.
Qed. 

Lemma eval_hfstmts_find_none_cases_helper ss init_s tmap rs s temp_rs temp_ns : 
  (forall v, match PVM.find v tmap with
  | Some (_, Register) => True
  | _ => PVM.find v temp_rs = None
  end) ->
  Sem_HiFP.eval_hfstmts ss temp_rs temp_ns init_s tmap = Some (rs, s) ->
  forall v, match PVM.find v tmap with
  | Some (_, Register) => True
  | _ => PVM.find v rs = None
  end
with eval_hfstmt_find_rs_helper st init_s tmap rs s temp_rs temp_ns : 
  (forall v, match PVM.find v tmap with
  | Some (_, Register) => True
  | _ => PVM.find v temp_rs = None
  end) ->
  Sem_HiFP.eval_hfstmt st temp_rs temp_ns init_s tmap = Some (rs, s) ->
  forall v, match PVM.find v tmap with
  | Some (_, Register) => True
  | _ => PVM.find v rs = None
  end.
Proof. (*td*)
  move : ss temp_rs temp_ns rs s. elim. 
  simpl; intros. inversion H0; subst rs s. apply H. 
  simpl; intros hd tl IH; intros. 
  destruct (Sem_HiFP.eval_hfstmt hd temp_rs temp_ns init_s tmap) as [[rs0 ns0]|] eqn : Heval; try discriminate.
  move : H0 v; apply IH; clear IH.
Admitted.

Lemma eval_hfstmts_find_none_cases ss init_s tmap rs s : Sem_HiFP.eval_hfstmts ss (PVM.empty bits) (PVM.empty bits) init_s tmap = Some (rs, s) ->
  forall v, match PVM.find v tmap with
  | Some (_, In_port) => PVM.find v s = None /\ PVM.find v rs = None
  | Some (_, Instanceof) => PVM.find v s = None /\ PVM.find v rs = None
  | Some (_, Memory) => PVM.find v s = None /\ PVM.find v rs = None
  | Some (_, Fmodule) => PVM.find v s = None /\ PVM.find v rs = None
  | Some (_, Register) => PVM.find v s = None
  | None => PVM.find v s = None /\ PVM.find v rs = None
  | _ => PVM.find v rs = None
  end.
Proof. 
  (*apply eval_hfstmts_find_none_cases_helper. intros; destruct (PVM.find v tmap) as [[gt cmpnt]|]; try done. destruct cmpnt; try done.
Qed.*)
Admitted.

Lemma find_node_qin_with_cond mv pp ss tmap: Sem_HiFP.module_tmap (PVM.empty (fgtyp * fcomponent)) (FInmod mv pp ss) = Some tmap ->
  forall v gt, PVM.find v tmap = Some (gt, Node) -> 
  forall init_s rs1 s1 bs, Sem_HiFP.eval_hfstmts ss (PVM.empty bits) (PVM.empty bits) init_s tmap = Some (rs1, s1) ->
  PVM.find v s1 = Some bs ->
  exists e, Qin_with_cond (Snode v e) ss init_s tmap.
Proof.
  simpl; intros. destruct (Sem_HiFP.ports_tmap' (PVM.empty (fgtyp * fcomponent)) pp) as[pmap|]; try discriminate.
  (* td *)
Admitted.

Lemma qin_with_cond_node_qin_cmpnt v e ss init_s tmap: 
  Qin_with_cond (Snode v e) ss init_s tmap -> 
  Qin (Snode v e) (component_stmts_of ss).
Proof.
  (* td *)
Admitted.

Lemma pvm_included_refl valmap : pvm_included valmap valmap.
Proof. 
  unfold pvm_included. intros; done.
Qed.

Lemma func_type_included_eval_hfstmts ss conn_map tmap : ExpandBranches_funs ss (PVM.empty def_expr) tmap = Some conn_map ->
  func_type_included (Sem_HiFP.eval_hfstmts ss) (Sem_HiFP.eval_hfstmts (Qcat (component_stmts_of ss) (convert_to_connect_stmts conn_map))) tmap.
Proof.
Admitted.

Theorem Sem_preservation_expandWhens : 
(* Proves pass expandWhens preserves the semantics *)
  forall (c : HiFP.hfcircuit) (inputs reg_init : PVM.t bits),
  match Sem_HiFP.compute_Sem c inputs reg_init with
  | Some (sem, regval) =>
      forall (newc : HiFP.hfcircuit),
      expandWhens c = Some newc ->
      match Sem_HiFP.compute_Sem newc inputs reg_init with
      | Some (sem_new, regval_new) => pvm_included sem sem_new /\
                                      pvm_included regval regval_new
      | _ => true
      end
  | _ => true
  end.
Proof.
  intros. destruct (Sem_HiFP.compute_Sem c inputs) as [[sem regval]|] eqn : Hsem; try done.
  intros. destruct (Sem_HiFP.compute_Sem newc inputs) as [[sem_new regval_new]|] eqn : Hsem_new; try done.
  unfold Sem_HiFP.compute_Sem in *. unfold expandWhens in *. unfold Sem_HiFP.circuit_tmap in *.
  destruct c as [cv ml] eqn : Hcir; subst c.
  destruct ml as [|m ml0]; try discriminate. destruct ml0; try discriminate. simpl in *.
  destruct (Sem_HiFP.module_tmap (PVM.empty (fgtyp * fcomponent)) m) as [tmap|] eqn : Htmap; try discriminate.
  destruct (ExpandWhens_fun m) as [fm|] eqn: Hpass; try discriminate. inversion H; subst newc. clear H.
  rewrite /Sem_HiFP.modules_tmap in Hsem_new.
  specialize (ExpandWhens_fun_tmap_eq Htmap) as Htmap_new. rewrite (Htmap_new _ Hpass) in Hsem_new. clear Htmap_new.
  unfold ExpandWhens_fun in *. destruct m as [mv pp ss|] eqn : Hm; try discriminate.
  destruct (ExpandBranches_funs ss (PVM.empty def_expr)) as [conn_map|] eqn : Hexpand_branches; try discriminate.
  inversion Hpass; subst fm. clear Hpass.
  rewrite component_stmts_of_init_dclrs_eq in Hsem_new.
  destruct (Sem_HiFP.init_dclrs ss (Sem_HiFP.update_values reg_init inputs) tmap) as [init_s|] eqn : Hinit_s; try discriminate.
  destruct (Sem_HiFP.iterate Sem_HiFP.n (Sem_HiFP.eval_hfstmts ss) init_s tmap) as [s0|] eqn : Hiter; try discriminate.
  destruct (Sem_HiFP.eval_hfstmts ss (PVM.empty bits) (PVM.empty bits) s0 tmap) as [[rs ns]|] eqn : Hregval; try discriminate. inversion Hsem; subst s0 rs; clear Hsem.
  destruct (Sem_HiFP.iterate Sem_HiFP.n
               (Sem_HiFP.eval_hfstmts (Qcat (component_stmts_of ss) (convert_to_connect_stmts conn_map)))
               init_s tmap) as [s0|] eqn : Hiter_new; try discriminate.
  destruct (Sem_HiFP.eval_hfstmts (Qcat (component_stmts_of ss) (convert_to_connect_stmts conn_map))
               (PVM.empty bits) (PVM.empty bits) s0 tmap) as [[rs ns_new]|] eqn : Hregval_new; try discriminate. inversion Hsem_new; subst s0 rs; clear Hsem_new.

  assert (Hfst_do_this : pvm_included sem sem_new). { 
    move : Hiter Hiter_new; apply iterate_func_included.
    (*apply func_type_included_eval_hfstmts; try done. apply pvm_included_refl. } *)

  unfold func_type_included. intros init_s1 init_s2 s1 s2 rs1 rs2 Hinit_eq Hevalss1 Hevalss2. split.
  - (* combinational part *)
    move : Hevalss1 Hevalss2 Hexpand_branches Htmap Hinit_eq; clear. intros Hevalss1 Hevalss2 Hexpand_branches Htmap Hinit_eq v.
    destruct (PVM.find v tmap) as [[gt cmpnt]|] eqn : Hcmpnt. destruct cmpnt.
    * (* inport *) 
      specialize (eval_hfstmts_find_none_cases Hevalss1 v) as Hfind1; rewrite Hcmpnt in Hfind1; move : Hfind1 => [Hfind1 _].
      intros; rewrite Hfind1 in H; discriminate.
    * (* instance of *) 
      specialize (eval_hfstmts_find_none_cases Hevalss1 v) as Hfind1; rewrite Hcmpnt in Hfind1; move : Hfind1 => [Hfind1 _].
      intros; rewrite Hfind1 in H; discriminate.
    * (* memory *) 
      specialize (eval_hfstmts_find_none_cases Hevalss1 v) as Hfind1; rewrite Hcmpnt in Hfind1; move : Hfind1 => [Hfind1 _].
      intros; rewrite Hfind1 in H; discriminate.
    * (* node : v的值在 component_stmts_of 中 *) intros bs Hfind1.
      specialize (find_node_qin_with_cond Htmap Hcmpnt Hevalss1 Hfind1) as He. destruct He as [e He].
      assert (Hunique : unique_node_dclr_when ss). admit.
      assert (He' : Qin (Snode v e) (Qcat (component_stmts_of ss) (convert_to_connect_stmts conn_map))). 
      specialize (qin_with_cond_node_qin_cmpnt He) as Hin. apply Qin_Qcat; left; done.
      assert (Hunique' : unique_node_dclr (Qcat (component_stmts_of ss) (convert_to_connect_stmts conn_map))). admit.
      rewrite (eval_hfstmts_for_unique_node He Hunique Hevalss1) in Hfind1.
      assert (Hwhen : forall c ss1 ss2, ~ Qin (Swhen c ss1 ss2) (Qcat (component_stmts_of ss) (convert_to_connect_stmts conn_map))).
        intros. intro. apply Qin_Qcat in H. destruct H. specialize (component_stmts_of_is_declaration H); simpl; done.
        specialize (convert_to_connect_stmts_is_connection H); simpl; done.
      rewrite (eval_hfstmts_for_unique_node' He' Hunique' Hwhen Hevalss2).
      move : Hinit_eq Hfind1; apply eval_fexpr_PVM_included_eq.
    * (* outport *) 
      specialize (eval_hfstmts_Qcat_some' (PVM.empty bits) (PVM.empty bits) Hevalss2) as Hexists. destruct Hexists as [[rs s] Hexists].
      specialize eval_hfstmts_for_comb_only_cnct with (v := v) (tmap := tmap) as Hcnct. rewrite Hcmpnt in Hcnct.
      assert (Hin : forall s, Qin s (component_stmts_of ss) -> is_declaration s) by (apply component_stmts_of_is_declaration).
      assert (Hneq : forall v' e', Qin (Snode v' e') (component_stmts_of ss) -> v <> v'). admit. (* TBD *)
      assert (Hwhen : forall c ss1 ss2, ~ Qin (Swhen c ss1 ss2) (Qcat (component_stmts_of ss) (convert_to_connect_stmts conn_map))). 
        intros. intro. apply Qin_Qcat in H. destruct H. specialize (component_stmts_of_is_declaration H); simpl; done.
        specialize (convert_to_connect_stmts_is_connection H); simpl; done.
      specialize (Hcnct _ _ _ Hin Hneq Hwhen _ _ Hevalss2 _ _ Hexists). rewrite -Hcnct; clear Hcnct Hevalss2.
      specialize eval_hfstmts_convert_to_connect_stmts_for_comb with (v := v) (tmap := tmap) as Hconvert. rewrite Hcmpnt in Hconvert.
      specialize (Hconvert _ _ _ _ Hexists). clear Hexists.
      specialize eval_hfstmts_ExpandBranches_funs_find_for_comb with (v := v) (tmap := tmap) as Hhelper.
      rewrite Hcmpnt in Hhelper. 
      assert (Hnotin : ~ (exists r : hfreg ProdVarOrder.T, Qin (Sreg v r) ss) /\ ~ (exists e : hfexpr ProdVarOrder.T, Qin (Snode v e) ss)). admit.
      intros val Hval; specialize (Hhelper _ _ _ _ Hnotin Hevalss1 _ Hval _ Hexpand_branches). 
      destruct (PVM.find v conn_map) as [dexpr|] eqn : Hcm; try done. destruct dexpr as [gt_e|e] eqn : Hde; subst dexpr.
      (* invalid *)
      destruct (sizeof_fgtyp gt < length indeterminate_val).
      1,2 : rewrite -Hconvert Hhelper //.
      (* cnct *)
      rewrite -Hconvert. move : Hhelper; apply eval_fexpr_PVM_included_eq; done.
    * (* register *) 
      specialize (eval_hfstmts_find_none_cases Hevalss1 v) as Hfind1; rewrite Hcmpnt in Hfind1.
      intros; rewrite Hfind1 in H; discriminate.
    * (* wire : 同 outport *) 
      specialize (eval_hfstmts_Qcat_some' (PVM.empty bits) (PVM.empty bits) Hevalss2) as Hexists. destruct Hexists as [[rs s] Hexists].
      specialize eval_hfstmts_for_comb_only_cnct with (v := v) (tmap := tmap) as Hcnct. rewrite Hcmpnt in Hcnct.
      assert (Hin : forall s, Qin s (component_stmts_of ss) -> is_declaration s) by (apply component_stmts_of_is_declaration).
      assert (Hneq : forall v' e', Qin (Snode v' e') (component_stmts_of ss) -> v <> v'). admit. (* TBD *)
      assert (Hwhen : forall c ss1 ss2, ~ Qin (Swhen c ss1 ss2) (Qcat (component_stmts_of ss) (convert_to_connect_stmts conn_map))). 
        intros. intro. apply Qin_Qcat in H. destruct H. specialize (component_stmts_of_is_declaration H); simpl; done.
        specialize (convert_to_connect_stmts_is_connection H); simpl; done.
      specialize (Hcnct _ _ _ Hin Hneq Hwhen _ _ Hevalss2 _ _ Hexists). rewrite -Hcnct; clear Hcnct Hevalss2.
      specialize eval_hfstmts_convert_to_connect_stmts_for_comb with (v := v) (tmap := tmap) as Hconvert. rewrite Hcmpnt in Hconvert.
      specialize (Hconvert _ _ _ _ Hexists). clear Hexists.
      specialize eval_hfstmts_ExpandBranches_funs_find_for_comb with (v := v) (tmap := tmap) as Hhelper.
      rewrite Hcmpnt in Hhelper. 
      assert (Hnotin : ~ (exists r : hfreg ProdVarOrder.T, Qin (Sreg v r) ss) /\ ~ (exists e : hfexpr ProdVarOrder.T, Qin (Snode v e) ss)). admit.
      intros val Hval; specialize (Hhelper _ _ _ _ Hnotin Hevalss1 _ Hval _ Hexpand_branches). 
      destruct (PVM.find v conn_map) as [dexpr|] eqn : Hcm; try done. destruct dexpr as [gt_e|e] eqn : Hde; subst dexpr.
      (* invalid *)
      destruct (sizeof_fgtyp gt < length indeterminate_val).
      1,2 : rewrite -Hconvert Hhelper //.
      (* cnct *)
      rewrite -Hconvert. move : Hhelper; apply eval_fexpr_PVM_included_eq; done.
    * (* module *) 
      specialize (eval_hfstmts_find_none_cases Hevalss1 v) as Hfind1; rewrite Hcmpnt in Hfind1; move : Hfind1 => [Hfind1 _].
      intros; rewrite Hfind1 in H; discriminate.
    * (* None *) 
      specialize (eval_hfstmts_find_none_cases Hevalss1 v) as Hfind1; rewrite Hcmpnt in Hfind1; move : Hfind1 => [Hfind1 _].
      intros; rewrite Hfind1 in H; discriminate.

  - (* sequential part *)
    move : Hevalss1 Hevalss2 Hexpand_branches Htmap Hinit_eq; clear. intros Hevalss1 Hevalss2 Hexpand_branches Htmap Hinit_eq v.
    destruct (PVM.find v tmap) as [[gt cmpnt]|] eqn : Hcmpnt. destruct cmpnt.
    * (* inport, instance of, memory, node, output, wire, module, none *) 
      1,2,3,8,9 : 
      specialize (eval_hfstmts_find_none_cases Hevalss1 v) as Hfind1; rewrite Hcmpnt in Hfind1; move : Hfind1 => [_ Hfind1];
      intros; rewrite Hfind1 in H; discriminate.
      1,2,4 : specialize (eval_hfstmts_find_none_cases Hevalss1 v) as Hfind1; rewrite Hcmpnt in Hfind1;
      intros; rewrite Hfind1 in H; discriminate.
    * (* register *) 
      specialize (eval_hfstmts_Qcat_some' (PVM.empty bits) (PVM.empty bits) Hevalss2) as Hexists. destruct Hexists as [[rs s] Hexists].
      specialize eval_hfstmts_for_sequ_only_cnct with (v := v) (tmap := tmap) as Hcnct. rewrite Hcmpnt in Hcnct.
      assert (Hdclr : forall s, Qin s (component_stmts_of ss) -> is_declaration s) by (apply component_stmts_of_is_declaration).
      assert (Hin : Qin (Sfcnct (Eid v) (Eref (Eid v))) (convert_to_connect_stmts conn_map) \/
        (exists e : hfexpr ProdVarOrder.T, Qin (Sfcnct (Eid v) e) (convert_to_connect_stmts conn_map))). admit. (* TBD *)
      specialize (Hcnct _ _ _ Hdclr Hexpand_branches Hin _ _ Hevalss2 _ _ Hexists). rewrite -Hcnct; clear Hcnct Hevalss2.
      specialize eval_hfstmts_convert_to_connect_stmts_for_sequ with (v := v) (tmap := tmap) as Hconvert. rewrite Hcmpnt in Hconvert.
      specialize (Hconvert _ _ _ _ Hexists). clear Hexists.
      specialize eval_hfstmts_ExpandBranches_funs_find_for_sequ with (v := v) (tmap := tmap) as Hhelper.
      rewrite Hcmpnt in Hhelper. 
      intros val Hval; specialize (Hhelper _ _ _ _ Hevalss1 _ Hval _ Hexpand_branches). 
      destruct (PVM.find v conn_map) as [dexpr|] eqn : Hcm; try done. destruct dexpr as [gt_e|e] eqn : Hde; subst dexpr.
      (* invalid *)
      destruct (sizeof_fgtyp gt < length indeterminate_val).
      1,2 : rewrite -Hconvert Hhelper //.
      (* cnct *)
      rewrite -Hconvert. move : Hhelper; apply eval_fexpr_PVM_included_eq; done.
    apply pvm_included_refl.
  }
  (* proof the equivalence of registers' next state values *)
  split; try done.
  specialize func_type_included_eval_hfstmts as Hhelper. apply Hhelper with (tmap := tmap) in Hexpand_branches. clear Hhelper.
  unfold func_type_included in Hexpand_branches. apply (Hexpand_branches _ _ _ _ _ _ Hfst_do_this Hregval) in Hregval_new.
  move : Hregval_new => [_ Hregval_new]. done.
Admitted.