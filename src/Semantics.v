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
  | Esubindex r n => match type_of_ref r tmap with
              | Some (Atyp ty _) => Some ty
              | _ => None
              end
  | Esubaccess r e => None
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
  | Ecast AsReset _ => None
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
  end.

(* value of ref expressions *)
Fixpoint hvalue_of_ref (r : HiF.href) (s : VM.t hvalue) : option hvalue :=
  match r with
  | Eid v => VM.find v s
  | Esubfield r v => match hvalue_of_ref r s with
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
  | Esubindex r n => match hvalue_of_ref r s with
              | Some (Aval fv) => let fix aux fx m := (
                                          match fx, m with
                                          | Acons t fxs, m'.+1 => aux fxs m'
                                          | Aone t, 0 => Some t 
                                          | _, _ => None
                                          end )
                                  in aux fv n
              | _ => None
              end
  | Esubaccess r e => None
  end.

(* makes val to be of type ft *)
Fixpoint ftext (ft : ftype) (val : hvalue) : option hvalue :=
  match ft, val with
  | Gtyp (Fuint w), Gval c => Some (Gval (zext (w - size c) c))
  | Gtyp (Fsint w), Gval c => Some (Gval (sext (w - size c) c))
  | Gtyp _, Gval c => Some (Gval (zext (1 - size c) c))
  | Atyp atyp n, Aval aval => match atypext atyp n aval with
                            | Some aval' => Some (Aval aval')
                            | _ => None
                            end
  | Btyp btyp, Bval bval => match btypext btyp bval with
                            | Some bval' => Some (Bval bval')
                            | _ => None
                            end
  | _, _ => None
  end
with atypext (ft : ftype)(* element type *) (n : nat)(* element amount *) (aval : array_value) : option array_value := 
  match n, aval with
  | 1, Aone val => match ftext ft val with
                  | Some val' => Some (Aone val')
                  | _ => None
                  end
  | n'.+1, Acons val tl => match ftext ft val, atypext ft n' tl with
                            | Some val', Some tl' => Some (Acons val' tl')
                            | _, _ => None
                            end
  | _, _ => None
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
        | 0 => Aone (Gval nil)
        | 1 => Aone (ftext0 atyp)
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

(* Expression evaluation, value *)
Fixpoint eval_hfexpr (exp : HiF.hfexpr) (s : VM.t hvalue) (tmap: VM.t (ftype * fcomponent)) : option hvalue :=
  match exp with
  | Econst t c => let val := match t with
                  | Fuint w1 => zext (w1 - size c) c
                  | Fsint w2 => sext (w2 - size c) c
                  | _ => c
                  end in Some (Gval val)
  | Eref r => hvalue_of_ref r s
  | Ecast AsUInt e 
  | Ecast AsSInt e => eval_hfexpr e s tmap
  | Ecast AsClock e  
  | Ecast AsReset e  
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

(* 内部aggr也有offset的版本 *)
Fixpoint offset_ref (r : HiF.href) (tmap: VM.t (ftype * fcomponent)) (n : nat) : option nat :=
  match r with
  | Eid v => Some n
  | Esubindex v i => match offset_ref v tmap n with
                    | Some os => Some (os + S i)
                    | _ => None
                    end
  | Esubfield v f => match type_of_ref v tmap with
                    | Some (Btyp fs) => let fix aux fx n := 
                        (match fx with
                        | Fflips v' fp t fxs =>
                            if ~~(v' == f) then aux fxs (n + size_of_ftype t)
                            else Some (n + 1)
                        | Fnil => None
                        end ) in aux fs n
                    | _ => None
                    end
  | Esubaccess r e => None
  end.

(* 通过offset来数hvalue中改变的地方 *)
Fixpoint update_hvalue_by_offset (val : hvalue) (checkt : ftype) (offset : nat) (new_val : hvalue) : option hvalue :=
  match checkt, val with
  | Gtyp _, Gval _ => if offset == 0 then Some new_val else None
  | Atyp atyp _, Aval aval => if offset == 0 then Some new_val else 
                              match update_array_value_by_offset atyp aval (offset - 1) new_val with
                              | Some aval' => Some (Aval aval')
                              | _ => None
                              end
  | Btyp ff, Bval bval => if offset == 0 then Some new_val else 
                              match update_bundle_value_by_offset ff bval (offset - 1) new_val with
                              | Some bval' => Some (Bval bval')
                              | _ => None
                              end
  | _, _ => None
  end 
with update_array_value_by_offset (atyp : ftype) (aval : array_value) (offset : nat) (new_val : hvalue) : option array_value :=
  match aval with
  | Aone val => let element_size := size_of_ftype atyp + 1 in if offset > element_size then None
                else match update_hvalue_by_offset val atyp offset new_val with
                    | Some val' => Some (Aone val')
                    | _ => None
                    end
  | Acons val tl => let element_size := size_of_ftype atyp + 1 in if offset > element_size then
                    match update_array_value_by_offset atyp tl (offset - element_size) new_val with
                    | Some tl' => Some (Acons val tl')
                    | _ => None
                    end 
                else match update_hvalue_by_offset val atyp offset new_val with
                    | Some val' => Some (Acons val' tl)
                    | _ => None
                    end
  end
with update_bundle_value_by_offset (btyp : ffield) (bval : bundle_value) (offset : nat) (new_val : hvalue) : option bundle_value := 
  match btyp, bval with
  | Fflips _ _ ft ff', Bflips v f val tl => let element_size := size_of_ftype ft + 1 in if offset > element_size then
                    match update_bundle_value_by_offset ff' tl (offset - element_size) new_val with
                    | Some tl' => Some (Bflips v f val tl')
                    | _ => None
                    end 
                else match update_hvalue_by_offset val ft offset new_val with
                    | Some val' => Some (Bflips v f val' tl)
                    | _ => None
                    end
  | _, _ => None
  end.

Definition eval_hfstmt (st : HiF.hfstmt) (rs : VM.t hvalue) (s : VM.t hvalue) (tmap: VM.t (ftype * fcomponent)) : (VM.t hvalue) * (VM.t hvalue) :=
  match st with
  | Snode v e => match eval_hfexpr e s tmap with
                | Some val => (rs, VM.add v val s)
                | _ => (rs, s)
                end
  (*| Sfcnct r (Eref ref) => (* 考虑flip和aggr *) 
            match hvalue_of_ref r s, hvalue_of_ref ref s with
            | Some val_r, Some val_ref => let base_r := HiF.base_ref r in let base_ref := HiF.base_ref ref in
                match VM.find base_r tmap, VM.find base_ref tmap with
                | Some (ft_r, Register), Some (ft_ref, Register) => (* 均更新rs *)
                | Some (ft_r, Register), Some (ft_ref, _) => (* nflip更新rs, flip更新s *)
                | Some (ft_r, _), Some (ft_ref, _) => (* 均更新s *)
                | _,_ => (rs,s)
                end
            | _, _ => (rs,s)
            end
                
  | Sfcnct r (Emux c e1 e2) => (* 不考虑flip,考虑aggr *)
  | Sfcnct r e => (* 不考虑flip,不考虑aggr *)
                  match eval_hfexpr e s tmap with
                  | Some val_e => let base_r := HiF.base_ref r in
                      match  VM.find base_r tmap with
                      | Some (ft_r, Register) => (* 更新rs *) match VM.find base_r s with
                      | Some (ft_r, _) => (* 更新s *)
                      | _, _ => (rs,s)
                      end
                  | _ => (rs,s)
                  end
  考虑是否为reg，更新rs/s *)
  (* TBD *)

  | _ => (rs,s) (* not sure其他情况：wire、reg、isinvalid 是否要给变量赋0？是否有意义/必要？ *)
  end.

Fixpoint eval_hfstmts (sts : HiF.hfstmt_seq) (rs : VM.t hvalue) (s : VM.t hvalue) (tmap: VM.t (ftype * fcomponent)) : (VM.t hvalue) * (VM.t hvalue) :=
  match sts with
  | Qnil => (rs, s)
  | Qcons st tl => let '(rs0, s0) := eval_hfstmt st rs s tmap in
                eval_hfstmts tl rs0 s0 tmap
  end.

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
  | Smem _ _ => None (* Memory *)
  | Sinst _ _ => None
  | Swhen cond ss_true ss_false =>
      match type_of_hfexpr cond tmap, stmts_tmap' tmap ss_true with
      | Some (Gtyp _), Some tmap_true => stmts_tmap' tmap_true ss_false 
      | _, _ => None
      end
  end.
  
Fixpoint ports_tmap' (tmap : VM.t (ftype * fcomponent)) (pp : seq HiF.hfport) : option (VM.t (ftype * fcomponent)) :=
(* creates a tmap that contains exactly the types of the ports in pp. *)
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
  | Snode v e => match eval_hfexpr e valmap tmap with
                | Some val => VM.add v val valmap
                | _ => valmap
                end
  | Sreg v reg => VM.add v (ftext0 (type reg)) valmap
  | Swhen cond ss_true ss_false => init_dclrs ss_false (init_dclrs ss_true valmap tmap) tmap
  | _ => valmap
  end.

Fixpoint init_registers (ss : HiF.hfstmt_seq) (valmap : VM.t hvalue) : VM.t hvalue := 
  match ss with
  | Qnil => valmap
  | Qcons s ss' => init_registers ss' (init_register s valmap)
  end
with init_register (s : HiF.hfstmt) (valmap : VM.t hvalue) : VM.t hvalue := 
  match s with
  | Sreg v reg => match reset reg with
      | NRst => valmap
      | Rst rst_sig rst_val => (* 本质这里需要区分同步/异步rst *)
          match eval_hfexpr rst_val (VM.empty hvalue) (VM.empty (ftype * fcomponent)) with (* 初始化电路中变量不存在value，只有const将初始化 *)
          | Some val => VM.add v val valmap
          | _ => valmap
          end
      end
  | Swhen cond ss_true ss_false =>
      match eval_hfexpr cond (VM.empty hvalue) (VM.empty (ftype * fcomponent)) with
      | Some (Gval valc) => if ~~ (is_zero valc) then init_registers ss_true valmap else init_registers ss_false valmap
      | _ => valmap
      end 
  | _ => valmap
  end.

Definition update_registers (rs : VM.t hvalue) (s : VM.t hvalue) : VM.t hvalue := 
  VM.fold (fun key value temps => VM.add key value temps) rs s.

Fixpoint iterate (n : nat) (func : HiF.hfstmt_seq -> VM.t hvalue -> VM.t hvalue -> VM.t (ftype * fcomponent) -> VM.t hvalue * VM.t hvalue)
  (ss : HiF.hfstmt_seq) (rs : VM.t hvalue) (s : VM.t hvalue) (tmap: VM.t (ftype * fcomponent)) : (VM.t hvalue) * (VM.t hvalue) :=
  match n with
  | 0 => (rs, s)
  | n'.+1 => let s_regupd := update_registers rs s in
             let (rs0, s0) := func ss (VM.empty hvalue)(* everytime we start with an empty map to record the value of registers in the next iteration *) s_regupd tmap in
             if VM.equal (fun val1 val2 => hvalue_eqn val1 val2) s0 s (* LFP *) then (rs0, s0) else iterate n' func ss rs0 s0 tmap
  end.

Definition n := 10.
Definition compute_Sem (c : HiF.hfcircuit) (inputs : VM.t hvalue) : option (VM.t hvalue) :=
  match circuit_tmap c, c with
  | Some tmap, Fcircuit _ [::(FInmod _ ps ss)] => 
        let s := init_dclrs ss inputs tmap in 
        let rs := init_registers ss (VM.empty hvalue) in
        let (rs0,s0) := iterate n eval_hfstmts ss rs s tmap in Some s0
  | _, _ => None
  end.

Definition flat_valmap (valmap : VM.t hvalue) (tmap: VM.t (ftype * fcomponent)) : PVM.t hvalue (*:= valmap ?? *).
(* TBD *)

(*Theorem Sem_preservation : 
(* Proves pass func preserves the semantics *)
  forall (c : HiF.hfcircuit) (inputs : VM.t hvalue),
  match compute_Sem c inputs, circuit_tmap c with
  | Some sem, Some tmap =>
      forall (newc : HiFP.hfcircuit),
      expandConnects c = Some newc ->
      let flatten_inputs := flat_valmap inputs tmap in
      let flatten_sem := flat_valmap sem tmap in
      match compute_SemP newc flatten_inputs with
      | Some new_sem => PVM.equal (fun val1 val2 => hvalue_eqn val1 val2) flatten_sem new_sem
      | _ => true
      end
  | _, _ => true
  end.
Proof.
Admitted.*)
