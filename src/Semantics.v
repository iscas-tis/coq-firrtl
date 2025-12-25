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
  | Gtyp (Fuint w), Gval c => Some (Gval (zext (w - size c) c))
  | Gtyp (Fsint w), Gval c => Some (Gval (sext (w - size c) c))
  | Gtyp _, Gval c => Some (Gval (zext (1 - size c) c))
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

Parameter n : nat. (* TBD *)
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
  | Sfcnct (Eid r) e => match PVM.find r tmap, eval_hfexpr e s tmap with
                        | Some (_, Register), Some val => (* 更新rs *) Some (PVM.add r val rs, ns)
                        | Some _, Some val => (* 更新s *) Some (rs, PVM.add r val ns)
                        | _, _ => None
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
  | Swhen cond ss_true ss_false =>
      match type_of_hfexpr cond tmap, stmts_tmap' tmap ss_true with
      | Some _, Some tmap_true => stmts_tmap' tmap_true ss_false 
      | _, _ => None
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
              if PVM.equal (fun val1 val2 => val1 == val2) s_upd s (* LFP *) then Some s_upd else iterate n' func s_upd tmap
            | _ => None
            end
  end.

Parameter n : nat. (* TBD *)
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

End Sem_HiFP.

Parameter flat_valmap : (VM.t hvalue) -> (VM.t (ftype * fcomponent)) -> PVM.t bits.
(* TBD *)

Parameter expandConnects : HiF.hfcircuit -> option HiFP.hfcircuit.

Theorem Sem_preservation_expandConnects : 
(* Proves pass expandConnects preserves the semantics *)
  forall (c : HiF.hfcircuit) (inputs reg_init : VM.t hvalue),
  match Sem_HiF.compute_Sem c inputs reg_init, Sem_HiF.circuit_tmap c with
  | Some (sem, _), Some tmap =>
      forall (newc : HiFP.hfcircuit),
      expandConnects c = Some newc ->
      let flatten_inputs := flat_valmap inputs tmap in
      let flatten_reg_init := flat_valmap reg_init tmap in
      let flatten_sem := flat_valmap sem tmap in
      match Sem_HiFP.compute_Sem newc flatten_inputs flatten_reg_init with
      | Some (new_sem, _) => PVM.equal (fun val1 val2 => val1 == val2) flatten_sem new_sem
      | _ => true
      end
  | _, _ => true
  end.
Proof.
Admitted.

Section ExpandWhens.

(* a type to indicate connects *)
Inductive def_expr : Type :=
| D_undefined (* declared but not connected, no "is invalid" statement *)
| D_invalidated (* declared but not connected, there is a "is invalid" statement *)
| D_fexpr : HiFP.hfexpr -> def_expr (* declared and connected *)
.

(* equality of def_expr is decidable [because equality of hfexpr is decidable] *)
Lemma def_expr_eq_dec : forall {x y : def_expr}, {x = y} + {x <> y}.
Proof.
  decide equality.
  apply hfexpr_eq_dec.
Qed.

Definition def_expr_eqn (x y : def_expr) : bool :=
match x, y with
| D_undefined, D_undefined => true
| D_invalidated, D_invalidated => true
| D_fexpr expr1, D_fexpr expr2 => expr1 == expr2
| _, _ => false
end.

Lemma def_expr_eqP : Equality.axiom def_expr_eqn.
Proof.
unfold Equality.axiom, def_expr_eqn.
intros ; induction x, y ; try (apply ReflectF ; discriminate) ; try (apply ReflectT ; reflexivity).
case Eq: (h == h0).
all: move /hfexpr_eqP : Eq => Eq.
apply ReflectT ; replace h0 with h ; reflexivity.
apply ReflectF ; injection ; apply Eq.
Qed.

Canonical def_expr_eqMixin := EqMixin def_expr_eqP.
Canonical def_expr_eqType := Eval hnf in EqType def_expr def_expr_eqMixin.

Fixpoint ExpandPorts_fun
    (* create a module graph for the port sequence pp.
       Out ports need to be assigned value “undefined”;
       in ports do not need to be assigned any value.
       Because types have been lowered already, we can assume
       that all ports have ground types. *)
    (pp : seq HiFP.hfport) (* the sequence of ports of the module *)
:   option (PVM.t def_expr * PVM.t (fgtyp * fcomponent)) (* result: a connection map and a scope map for the ports *)
:=  match pp with
    | [::] => Some (PVM.empty def_expr, PVM.empty (fgtyp * fcomponent))
    | Finput p (Gtyp gt) :: pp' =>
        match ExpandPorts_fun pp' with
        | Some (temp_ct, temp_scope) =>
            Some (temp_ct, PVM.add p (gt, In_port) temp_scope)
        | None => None
        end
    | Foutput p (Gtyp gt) :: pp' =>
        match ExpandPorts_fun pp' with
        | Some (temp_ct, temp_scope) =>
            Some (PVM.add p D_undefined temp_ct, PVM.add p (gt, In_port) temp_scope)
        | None => None
        end
    | _ => None
    end.

Definition connect_type_compatible (gt_tgt gt_src : fgtyp) : bool :=
(* Returns true if a connection from ft_src to ft_tgt is allowed.
   flipped == true indicates that the connection should be the other way actually.
   If can_flip == false, no flipped fields are allowed in bundle types. *)
match gt_tgt, gt_src with
| Fuint w1, Fuint w2
| Fsint w1, Fsint w2 => w1 == w2
| Fclock, Fclock
| Fasyncreset, Fasyncreset => true 
| _, _ => false
end.

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
                      | Some D_undefined, _
                      | _, Some D_undefined => Some D_undefined
                      | None, _ => false_expr
                      | _, None => true_expr
                      | Some D_invalidated, _ => false_expr
                      | _, Some D_invalidated => true_expr
                      end)
             true_conn_map false_conn_map.

Fixpoint ExpandBranches_funs
(* split a statement sequence (possibly containing when
   statements) into a sequence that defines components and a
   connection map.  The output does not contain when statements. *)
(ss           : HiFP.hfstmt_seq)   (* sequence of statements being translated *)
(old_conn_map : PVM.t def_expr)    (* connections made by earlier statements in the sequence (used for recursion) *)
(old_scope    : PVM.t (fgtyp * fcomponent)) (* part of module graph vertices that is currently in scope *)
:   option (PVM.t def_expr * PVM.t (fgtyp * fcomponent))
(* old_conn_map, extended with the connection statements in ss,
   and old_scope, extended with the component statements in ss that remain in scope *)
:=  match ss with
| Qnil => Some (old_conn_map, old_scope)
| Qcons s ss =>
    match ExpandBranch_fun s old_conn_map old_scope with
    | Some (temp_conn_map, temp_scope) =>
        ExpandBranches_funs ss temp_conn_map temp_scope
    | None => None
    end
end
with ExpandBranch_fun
(* split a single statement (possibly consisting of a when
   statement) into a sequence that defines components and a
   connection map.  The output does not contain when statements. *)
(s            : HiFP.hfstmt)       (* a single statement being translated *)
(old_conn_map : PVM.t def_expr)    (* connections made by earlier statements in the sequence (used for recursion) *)
(old_scope    : PVM.t (fgtyp * fcomponent)) (* part of module graph vertices that is currently in scope *)
:   option (PVM.t def_expr * PVM.t (fgtyp * fcomponent))
(* old_comp_ss, extended with the component statements in s,
   old_conn_map, extended with the connection statements in s,
   and old_scope, extended with the component statements in s that remain in scope *)
:=  match s with
| Sskip => Some (old_conn_map, old_scope)
| Swire var (Gtyp gt) =>
    match PVM.find var old_scope with
    | None => Some (PVM.add var D_undefined old_conn_map, PVM.add var (gt, Wire) old_scope)
    | Some _ => None
    end
| Sreg var reg =>
    match PVM.find var old_scope, Sem_HiFP.type_of_hfexpr (clock reg) old_scope, type reg with
    | None, Some _, Gtyp gt =>
        match reset reg with
        | NRst => Some (PVM.add var (D_fexpr (Eref (Eid var))) old_conn_map, PVM.add var (gt, Register) old_scope)
        | Rst rst_sig rst_val =>
            match Sem_HiFP.type_of_hfexpr rst_sig old_scope with
            | Some (Fuint 1) =>
                match Sem_HiFP.type_of_hfexpr rst_val (PVM.add var (gt, Register) old_scope) with
                | Some _ => Some (PVM.add var (D_fexpr (Eref (Eid var))) old_conn_map, PVM.add var (gt, Register) old_scope)
                | None => None
                end
            | Some Fasyncreset =>
                match Sem_HiFP.type_of_hfexpr rst_val old_scope with
                | Some _ => Some (PVM.add var (D_fexpr (Eref (Eid var))) old_conn_map, PVM.add var (gt, Register) old_scope)
                | None => None
                end
            | _ => None
            end
        end
    | _, _, _ => None
    end
| Smem var mem => None
| Sinst var1 var2 => None
| Snode var expr =>
    match PVM.find var old_scope, Sem_HiFP.type_of_hfexpr expr old_scope with
    | None, Some ft =>
        Some (old_conn_map, PVM.add var (ft, Node) old_scope)
    | _, _ => None
    end
| Sfcnct (Eid var) expr =>
    (* The following code needs to be moved to a helper function
       because ref can be more complex than just (Eid var). *)
    match PVM.find var old_scope with
    | Some (gt_ref, _) =>
        match Sem_HiFP.type_of_hfexpr expr old_scope with
        | Some gt_expr =>
            if connect_type_compatible gt_ref gt_expr
            then Some (PVM.add var (D_fexpr expr) old_conn_map, old_scope)
            else None
        | _ => None
        end
    | _ => None
    end
| Sinvalid (Eid var) =>
    match PVM.find var old_scope with
    | Some _ =>
        Some (PVM.add var D_invalidated old_conn_map, old_scope)
    | _ => None
    end
| Swhen cond ss_true ss_false =>
    match Sem_HiFP.type_of_hfexpr cond old_scope, ExpandBranches_funs ss_true old_conn_map old_scope with
    | Some (Fuint 1), Some (true_conn_map, _) =>
        match ExpandBranches_funs ss_false old_conn_map old_scope with
        | Some (false_conn_map, _) =>
            Some (combine_when_connections cond true_conn_map false_conn_map, old_scope)
        | _ => None
        end
    | _, _ => None
    end
| _ => None
end.

Definition convert_to_connect_stmt
    (* convert one entry in a map of connections to a connect statement,
       helper function for PVM.fold *)
    (v : PVM.key) (* key of the connection *)
    (d : def_expr) (* value of the connection *)
    (old_ss : HiFP.hfstmt_seq) (* old sequence of connect statements *)
:   HiFP.hfstmt_seq (* returns old_ss, extended with assigning d to v *)
:=  match d with
    | D_undefined => old_ss
    | D_invalidated => Qcons (Sinvalid (Eid v)) old_ss
    | D_fexpr e => Qcons (Sfcnct (Eid v) e) old_ss
    end.

Definition convert_to_connect_stmts
    (* converts a map of connections to connect statements *)
    (conn_map : PVM.t def_expr) (* map that needs to be converted *)
:   HiFP.hfstmt_seq
:=  PVM.fold convert_to_connect_stmt conn_map (Qnil ProdVarOrder.T).

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

Definition ExpandWhens_fun
    (* Expand When statements in a module *)
    (m : HiFP.hfmodule) (* module that needs to be handled *)
:   option HiFP.hfmodule (* result is either a semantically equivalent module without when statements,
                            or nothing if there was some error *)
:=  match m with
    | FInmod v pp ss =>
        match ExpandPorts_fun pp with
        | Some (port_ct, port_scope) =>
            match ExpandBranches_funs ss port_ct port_scope with
            | Some (conn_map, _) =>
                Some (FInmod v pp (Qcat (component_stmts_of ss) (convert_to_connect_stmts conn_map)))
            | None => None
            end
        | None => None
        end
    | FExmod _ _ _ => None
    end.

Definition expandWhens (c : HiFP.hfcircuit) : option HiFP.hfcircuit :=
  match c with
  | Fcircuit v [:: m] => match ExpandWhens_fun m with
    | Some fm => Some (Fcircuit v [:: fm])
    | _ => None
    end
  | _ => None
  end.

End ExpandWhens.

Lemma ExpandWhens_fun_tmap_eq m tmap : Sem_HiFP.module_tmap (PVM.empty (fgtyp * fcomponent)) m = Some tmap -> 
  forall fm, ExpandWhens_fun m = Some fm -> Sem_HiFP.module_tmap (PVM.empty (fgtyp * fcomponent)) fm = Some tmap.
Proof.
Admitted.

Lemma component_stmts_of_init_dclrs_eq ss valmap tmap init_s : Sem_HiFP.init_dclrs ss valmap tmap = Some init_s ->
  forall conn_map, Sem_HiFP.init_dclrs (Qcat (component_stmts_of ss) (convert_to_connect_stmts conn_map)) valmap tmap = Some init_s.
Proof.
Admitted.

Lemma PVM_equal_iff_find_eq (m1 m2 : PVM.t bits) : PVM.equal (fun val1 val2 : bitseq => val1 == val2) m1 m2 <-> (forall v, PVM.find v m1 = PVM.find v m2).
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
Admitted.

Lemma update_values_equal' : forall ns s1 s2,
  PVM.equal (fun v1 v2 : bitseq => v1 == v2) s1 s2 ->
  PVM.equal (fun v1 v2 : bitseq => v1 == v2) (Sem_HiFP.update_values ns s1) (Sem_HiFP.update_values ns s2).
Proof.
Admitted.

Definition func_type : Type := PVM.t bits -> PVM.t bits -> PVM.t bits -> PVM.t (fgtyp * fcomponent) -> option (PVM.t bits * PVM.t bits).
Definition func_type_eq (fun1 fun2 : func_type) (tmap : PVM.t (fgtyp * fcomponent)) : Prop := forall (init_s1 init_s2 : PVM.t bits) (s1 s2 : PVM.t bits * PVM.t bits),
PVM.equal (fun val1 val2 : bitseq => val1 == val2) init_s1 init_s2 -> fun1 (PVM.empty bits) (PVM.empty bits) init_s1 tmap = Some s1 -> fun2 (PVM.empty bits) (PVM.empty bits) init_s2 tmap = Some s2 -> (forall v, PVM.find v (snd s1) = PVM.find v (snd s2)).

Lemma iterate_func_eq n fun1 fun2 init_s1 init_s2 tmap sem sem_new : 
  func_type_eq fun1 fun2 tmap -> PVM.equal (fun val1 val2 : bitseq => val1 == val2) init_s1 init_s2 -> Sem_HiFP.iterate n fun1 init_s1 tmap = Some sem -> Sem_HiFP.iterate n fun2 init_s2 tmap = Some sem_new -> 
  (forall v, PVM.find v sem = PVM.find v sem_new).
Proof.
  intros Hfun_eq. revert init_s1 init_s2 sem sem_new. 
  induction n as [|n IH]; intros init_s1 init_s2 sem sem_new Hinit_eq Hiter1 Hiter2.
  - (* Case n = 0 *)
    simpl in Hiter1, Hiter2.
    inversion Hiter1; inversion Hiter2. subst sem sem_new. apply PVM_equal_iff_find_eq. done.
  - (* Case n = S n' *)
    simpl in Hiter1, Hiter2.
    destruct (fun1 (PVM.empty bits) (PVM.empty bits) init_s1 tmap) as [[rs1 ns1]|] eqn:Hcall1;
      [|discriminate].
    destruct (fun2 (PVM.empty bits) (PVM.empty bits) init_s2 tmap) as [[rs2 ns2]|] eqn:Hcall2;
      [|discriminate].
    specialize (Hfun_eq init_s1 init_s2 (rs1, ns1) (rs2, ns2)).
    specialize (Hfun_eq Hinit_eq Hcall1 Hcall2). 
    simpl in Hfun_eq. 
    apply PVM_equal_iff_find_eq in Hfun_eq. generalize Hfun_eq; intro Hns_eq. apply update_values_equal with (s := init_s1) in Hfun_eq.
    destruct (PVM.equal (fun val1 val2 : bitseq => val1 == val2)
             (Sem_HiFP.update_values ns1 init_s1) init_s1) eqn:Hfp1.
    + (* 达到不动点 *)
      apply PVM_equal_iff_find_eq. inversion Hiter1; subst sem; clear Hiter1.
      specialize (update_values_equal' ns2 Hinit_eq) as Hhelper. apply (PVM_equal_trans Hfun_eq) in Hhelper.
      apply PVM_equal_comm in Hfp1. apply (PVM_equal_trans Hfp1) in Hhelper. apply PVM_equal_comm in Hhelper. 
      apply (PVM_equal_trans Hhelper) in Hinit_eq. rewrite Hinit_eq in Hiter2. inversion Hiter2; subst sem_new; clear Hiter2.
      apply PVM_equal_comm. apply (PVM_equal_trans Hhelper Hfp1).
    + (* 未达到不动点 *)
      assert (Hfalse : ~ PVM.equal (fun val1 val2 : bitseq => val1 == val2) (Sem_HiFP.update_values ns2 init_s2) init_s2).
        intro Hneg. specialize (update_values_equal' ns2 Hinit_eq) as Hhelper. apply (PVM_equal_trans Hfun_eq) in Hhelper.
        apply (PVM_equal_trans Hhelper) in Hneg. apply not_true_iff_false in Hfp1. apply (PVM_non_equal_trans Hfp1) in Hinit_eq. 
        done.
      apply not_true_iff_false in Hfalse. rewrite Hfalse in Hiter2.
      move : Hiter1 Hiter2; apply IH.
      specialize (update_values_equal' ns2 Hinit_eq) as Hhelper. apply (PVM_equal_trans Hfun_eq) in Hhelper. 
      done.
Qed.

Lemma find_eq_iff_mem_eq_and_1d :
  forall (m1 m2 : PVM.t bits),
    (forall v, PVM.find v m1 = PVM.find v m2) <->
    (forall v, PVM.mem v m1 <-> PVM.mem v m2) /\
    (forall v val, PVM.find v m1 = Some val -> PVM.find v m2 = Some val).
Proof.
  split.
  - (* 方向 1: equal 蕴含合取 *)
    intros Hequal.
    split.
    + (* 证明 mem 等价 *)
Admitted.

Fixpoint eval_hfstmt_for_v (st : HiFP.hfstmt) (s : PVM.t bits) (tmap: PVM.t (fgtyp * fcomponent)) (v : PVM.key) (current_val : option bits) : option bits :=
  match st with
  | Snode v e => Sem_HiFP.eval_hfexpr e s tmap 
  | Sfcnct (Eid v) e => match PVM.find v tmap with
                        | Some (_, Register) => None
                        | Some _ => Sem_HiFP.eval_hfexpr e s tmap
                        | _ => None
                        end
  | Swhen cond ss_true ss_false => match Sem_HiFP.eval_hfexpr cond s tmap with
                  | Some valc => if ~~ (is_zero valc) then eval_hfstmts_for_v ss_true s tmap v current_val else eval_hfstmts_for_v ss_false s tmap v current_val
                  | _ => None
                  end
  | _ => current_val
  end
with eval_hfstmts_for_v (sts : HiFP.hfstmt_seq) (s : PVM.t bits) (tmap: PVM.t (fgtyp * fcomponent)) (v : PVM.key) (current_val : option bits) : option bits :=
  match sts with
  | Qnil => current_val
  | Qcons st tl => eval_hfstmts_for_v tl s tmap v (eval_hfstmt_for_v st s tmap v current_val)
  end.

Lemma eval_hfstmts_for_v_init_eq ss init_s1 init_s2 tmap v : PVM.equal (fun val1 val2 : bitseq => val1 == val2) init_s1 init_s2 ->
  eval_hfstmts_for_v ss init_s1 tmap v None = eval_hfstmts_for_v ss init_s2 tmap v None.
Proof.
Admitted.

Theorem Sem_preservation_expandWhens : 
(* Proves pass expandWhens preserves the semantics *)
  forall (c : HiFP.hfcircuit) (inputs reg_init : PVM.t bits),
  match Sem_HiFP.compute_Sem c inputs reg_init with
  | Some (sem, _) =>
      forall (newc : HiFP.hfcircuit),
      expandWhens c = Some newc ->
      match Sem_HiFP.compute_Sem newc inputs reg_init with
      | Some (sem_new, _) => PVM.equal (fun val1 val2 => val1 == val2) sem sem_new
      | _ => true
      end
  | _ => true
  end.
Proof.
  intros. destruct (Sem_HiFP.compute_Sem c inputs) as [[sem regval]|] eqn : Hsem; try done.
  intros. destruct (Sem_HiFP.compute_Sem newc inputs) as [[sem_new regval_new]|] eqn : Hsem_new; try done.
  unfold Sem_HiFP.compute_Sem in *. unfold expandWhens in *.
  destruct c as [cv ml] eqn : Hcir; subst c.
  destruct ml as [|m ml0]; try discriminate. destruct ml0; try discriminate. destruct (ExpandWhens_fun m) as [fm|] eqn: Hpass; try discriminate.
  inversion H; subst newc. clear H. unfold Sem_HiFP.circuit_tmap in *; unfold Sem_HiFP.modules_tmap in *. 
  destruct (Sem_HiFP.module_tmap (PVM.empty (fgtyp * fcomponent)) m) as [tmap|] eqn : Htmap; try discriminate.
  specialize (ExpandWhens_fun_tmap_eq Htmap) as Htmap_new. rewrite (Htmap_new _ Hpass) in Hsem_new. clear Htmap_new.
  unfold ExpandWhens_fun in *. destruct m as [v pp ss|] eqn : Hm; try discriminate.
  destruct (ExpandPorts_fun pp) as [[port_ct port_scope]|] eqn : Hexpand_ports; try discriminate. 
  destruct (ExpandBranches_funs ss port_ct port_scope) as [[conn_map conn_map']|] eqn : Hexpand_branches; try discriminate.
  inversion Hpass; subst fm. clear Hpass.
  destruct (Sem_HiFP.init_dclrs ss (Sem_HiFP.update_values reg_init inputs) tmap) as [init_s|] eqn : Hinit_s; try discriminate.
  specialize (component_stmts_of_init_dclrs_eq Hinit_s) as Hinit_s_new. rewrite Hinit_s_new in Hsem_new; clear Hinit_s_new.
  destruct (Sem_HiFP.iterate Sem_HiFP.n (Sem_HiFP.eval_hfstmts ss) init_s tmap) as [s0|] eqn : Hiter; try discriminate.
  destruct (Sem_HiFP.eval_hfstmts ss (PVM.empty bits) (PVM.empty bits) s0 tmap) as [[rs ns]|]; try discriminate. inversion Hsem; subst s0 regval; clear Hsem rs ns.
  destruct (Sem_HiFP.iterate Sem_HiFP.n
               (Sem_HiFP.eval_hfstmts (Qcat (component_stmts_of ss) (convert_to_connect_stmts conn_map)))
               init_s tmap) as [s0|] eqn : Hiter_new; try discriminate.
  destruct (Sem_HiFP.eval_hfstmts (Qcat (component_stmts_of ss) (convert_to_connect_stmts conn_map))
               (PVM.empty bits) (PVM.empty bits) s0 tmap) as [[rs ns]|]; try discriminate. inversion Hsem_new; subst s0 regval_new; clear Hsem_new rs ns.
  apply PVM_equal_iff_find_eq. move : Hiter Hiter_new; apply iterate_func_eq.  

  unfold func_type_eq. intros init_s1 init_s2 [rs1 s1] [rs2 s2] Hinit_eq Hevalss1 Hevalss2; simpl. apply find_eq_iff_mem_eq_and_1d. split.
  + (* mem eq *) admit. (* 这里比较好说明的角度应该是: 说明 s1的定义域等于init_s1 和 s2的定义域等于init_s2 *)
  + (* find some value eq *) 
    assert (Hbefore : forall v val, PVM.find v s1 = Some val -> eval_hfstmts_for_v ss init_s1 tmap v None = Some val). admit.
    assert (Hafter : forall v val, eval_hfstmts_for_v ss init_s2 tmap v None = Some val -> PVM.find v s2 = Some val). {
      destruct (PVM.find v tmap) as [[gt cmpnt]|] eqn : Hcmpnt. destruct cmpnt.
      * (* inport *) admit. (* 此时 eval_hfstmts_for_v = None, inport 不出现在连接 lhs *)
      * (* instance of *) admit. (* 暂不考虑 *)
      * (* memory *) admit. (* 暂不考虑 *)
      * (* node TBD : v的值在 component_stmts_of 中 *) admit.
      * (* outport TBD : PVM.find v conn_map = Some e -> eval_hfstmts_for_v ss init_s2 tmap v None = eval_expr e*) admit.
      * (* register *) admit. (* 此时 eval_hfstmts_for_v = None, iteration中不考虑reg*)
      * (* wire TBD : 同 outport *) admit.
      * (* module *) admit. (* tmap 中不含 *)
      * (* None *) admit. (* 此时 eval_hfstmts_for_v = None *)
    }
    move : Hinit_eq Hbefore Hafter; clear; intros.
    apply Hbefore in H. rewrite (eval_hfstmts_for_v_init_eq _ _ _ Hinit_eq) in H. apply Hafter in H; done.

  apply PVM_equal_refl.
Admitted.

Lemma eval_hfstmts_for_node_no_cnct component_stmts connect_stmts init_s tmap v val: (* 这里需要一些语义前提，即node不再次被连接，不出现在cnct stmt中 *) 
  (exists gt, PVM.find v tmap = Some (gt, Node)) -> forall rs s rs' s', Sem_HiFP.eval_hfstmts (Qcat component_stmts connect_stmts) (PVM.empty bits) (PVM.empty bits) init_s tmap = Some (rs, s) ->
  Sem_HiFP.eval_hfstmts component_stmts (PVM.empty bits) (PVM.empty bits) init_s tmap = Some (rs', s') -> PVM.find v s' = Some val -> PVM.find v s = Some val.
Proof.
Admitted.

Lemma eval_hfstmts_for_node_dclr1 ss init_s tmap v val : (* 在ss induction即可？ *)
  (exists gt, PVM.find v tmap = Some (gt, Node)) -> forall rs s, eval_hfstmts_for_v ss init_s tmap v None = Some val -> 
  Sem_HiFP.eval_hfstmts (component_stmts_of ss) (PVM.empty bits) (PVM.empty bits) init_s tmap = Some (rs, s) -> PVM.find v s = Some val.
Proof.
Admitted.

(*Lemma eval_hfstmts_for_others ss init_s tmap v : 
  exists gt, match PVM.find v tmap with
  | Some (gt, Out_port) 
  | Some (gt, Wire) => PVM.find v conn_map = Some e -> eval_hfstmts_for_v ss init_s tmap v None = Sem_HiFP.eval_hfexpr e init_s tmap
  | Some (gt, Register) => eval_hfstmts_for_v ss init_s2 tmap v0 None = None
  | _ => true
  end.
Proof.
  
Qed.*)
