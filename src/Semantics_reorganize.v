From Coq Require Import FunInd FMaps FMapAVL OrderedType ZArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat ssrint eqtype seq fintype fingraph.
From simplssrlib Require Import Types SsrOrder FSets FMaps Tactics Var Store.
From nbits Require Import NBits.
From firrtl Require Import Firrtl Env HiEnv HiFirrtl.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section Value.

  Variable var : eqType.

  Inductive ftype : Type :=
  | Gtyp : fgtyp -> ftype
  | Atyp : ftype -> nat -> ftype
  | Btyp : ffield -> ftype

  with ffield : Type :=
  | Fnil : ffield
  | Fflips : var -> fflip -> ftype -> ffield -> ffield
  .

  Definition econst s c := @Econst var s c.
  Definition ecast u e := @Ecast var u e.
  Definition eprim_unop u e := @Eprim_unop var u e.
  Definition eprim_binop b e1 e2 := @Eprim_binop var b e1 e2.
  Definition emux c e1 e2 := @Emux var c e1 e2.
  (* Definition evalidif c e := @Evalidif V.T c e. *)
  Definition hfexpr := hfexpr var.
  Definition eref r := @Eref var r.
  Definition eid v := @Eid var v.
  Definition esubfield r v := @Esubfield var r v.
  Definition esubindex r n := @Esubindex var r n.
  Definition esubaccess r e := @Esubaccess var r e.
  Definition href := href var.

  Inductive rst : Type :=
  | NRst : rst
  | Rst : hfexpr -> hfexpr -> rst.

  Record hfreg : Type :=
    mk_freg
      {
        type : ftype;
        clock : hfexpr;
        reset : rst
      }.

  Record mem_port : Type :=
    mk_mem_port
      {
        id : var;
        addr : var;
        en : var;
        clk : var;
        mask : var
      }.

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

  Inductive hfport : Type :=
  | Finput : var -> ftype -> hfport
  | Foutput : var -> ftype -> hfport
  .

  Inductive hfmodule : Type :=
  | FInmod : var -> seq hfport -> hfstmt_seq -> hfmodule
  | FExmod : var -> seq hfport -> hfstmt_seq -> hfmodule.

  Inductive hfcircuit : Type := Fcircuit : var -> seq hfmodule -> hfcircuit.


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

  (* general data value equality is decidable *)
  Axiom hvalue_eq_dec : forall {x y : hvalue}, {x = y} + {x <> y}.
  Axiom array_value_eq_dec : forall {x y : array_value}, {x = y} + {x <> y}.
  Axiom bundle_value_eq_dec : forall {x y : bundle_value}, {x = y} + {x <> y}.

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

  Axiom hvalue_eqP : Equality.axiom hvalue_eqn.
  Axiom array_value_eqP : Equality.axiom array_value_eqn.
  Axiom bundle_value_eqP : Equality.axiom bundle_value_eqn.

  Canonical hvalue_eqMixin := EqMixin hvalue_eqP.
  Canonical hvalue_eqType := Eval hnf in EqType hvalue hvalue_eqMixin.

End Value.

Module MakeSemantics
  (V : SsrOrder) (* identifier names *)
  (VM : SsrFMap with Module SE := V).

  Local Notation var := V.t.

  Definition gtyp gt := @Gtyp V.T gt.
  Definition atyp ft n := @Atyp V.T ft n.
  Definition btyp bt := @Btyp V.T bt.
  Definition ftype := ftype V.T.
  Definition fnil := @Fnil V.T.
  Definition fflips v f ft tl:= @Fflips V.T v f ft tl.
  Definition ffield := ffield V.T.

  Definition gval val := @Gval V.T val.
  Definition aval val := @Aval V.T val.
  Definition bval val := @Bval V.T val.
  Definition hvalue := hvalue V.T.
  Definition aone val := @Aone V.T val.
  Definition acons hd tl := @Acons V.T hd tl.
  Definition array_value := array_value V.T.
  Definition bnil := @Bnil V.T.
  Definition bflips v f val tl := @Bflips V.T v f val tl.
  Definition bundle_value := bundle_value V.T.

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
  Definition qcons s ss := @Qcons V.T s ss.
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
  Definition type ft := @type V.T ft.
  Definition clock e := @clock V.T e.
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

(* type of ref expressions *)
Fixpoint type_of_ref (r : href) (tmap : VM.t (ftype * fcomponent)) : option ftype :=
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
                        | Some fgt => Some (gtyp fgt)
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
       | Fnil, Fnil => Some (Btyp fnil)
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

Fixpoint type_of_hfexpr (e : hfexpr) (tmap: VM.t (ftype * fcomponent)) : option ftype :=
  match e with
  | Econst t bs => Some (gtyp t)
  | Eref r => type_of_ref r tmap 
  | Ecast AsUInt e1 
  | Ecast AsSInt e1 => match type_of_hfexpr e1 tmap with
                        | Some (Gtyp (Fsint w))
                        | Some (Gtyp (Fuint w)) => Some (gtyp (Fsint w))
                        | Some (Gtyp Fclock) 
                        | Some (Gtyp Freset)
                        | Some (Gtyp Fasyncreset) => Some (gtyp (Fsint 1))
                        | _ => None
                        end
  | Ecast AsClock e1 => match type_of_hfexpr e1 tmap with
                        | Some (Gtyp _) => Some (gtyp Fclock)
                        | _ => None
                        end
  | Ecast AsAsync e1 => match type_of_hfexpr e1 tmap with
                        | Some (Gtyp _) => Some (gtyp Fasyncreset)
                        | _ => None
                        end
  | Ecast AsReset _ => None
  | Eprim_unop (Upad n) e1 => match type_of_hfexpr e1 tmap with
                              | Some (Gtyp (Fsint w)) => Some (gtyp (Fsint (maxn w n)))
                              | Some (Gtyp (Fuint w)) => Some (gtyp (Fuint (maxn w n)))
                              | _ => None
                              end
  | Eprim_unop (Ushl n) e1 => match type_of_hfexpr e1 tmap with
                              | Some (Gtyp (Fsint w)) => Some (gtyp (Fsint (w + n)))
                              | Some (Gtyp (Fuint w)) => Some (gtyp (Fuint (w + n)))
                              | _ => None
                              end
  | Eprim_unop (Ushr n) e1 => match type_of_hfexpr e1 tmap with
                              | Some (Gtyp (Fsint w)) => Some (gtyp (Fsint (maxn (w - n) 1)))
                              | Some (Gtyp (Fuint w)) => Some (gtyp (Fuint (maxn (w - n) 0)))
                              | _ => None
                              end
  | Eprim_unop Ucvt e1 => match type_of_hfexpr e1 tmap with
                          | Some (Gtyp (Fsint w)) => Some (gtyp (Fsint w))
                          | Some (Gtyp (Fuint w)) => Some (gtyp (Fsint (w + 1)))
                          | _ => None
                          end
  | Eprim_unop Uneg e1 => match type_of_hfexpr e1 tmap with
                          | Some (Gtyp (Fsint w))
                          | Some (Gtyp (Fuint w)) => Some (gtyp (Fsint (w + 1)))
                          | _ => None
                          end
  | Eprim_unop Unot e1 => match type_of_hfexpr e1 tmap with
                          | Some (Gtyp (Fsint w))
                          | Some (Gtyp (Fuint w)) => Some (gtyp (Fuint w))
                          | _ => None
                          end
  | Eprim_unop (Uextr n1 n2) e1 => match type_of_hfexpr e1 tmap with
                                    | Some (Gtyp (Fsint w))
                                    | Some (Gtyp (Fuint w)) =>
                                        if (n2 <= n1) && (n1 < w) then Some (gtyp (Fuint (n1 - n2 + 1)))
                                                                  else None
                                    | _ => None
                                    end
  | Eprim_unop (Uhead n) e1 => match type_of_hfexpr e1 tmap with
                                | Some (Gtyp (Fsint w))
                                | Some (Gtyp (Fuint w)) =>
                                    if n <= w then Some (gtyp (Fuint n))
                                              else None
                                | _ => None
                                end
  | Eprim_unop (Utail n) e1 => match type_of_hfexpr e1 tmap with
                                | Some (Gtyp (Fsint w))
                                | Some (Gtyp (Fuint w)) =>
                                    if n <= w then Some (gtyp (Fuint (w - n)))
                                              else None
                                | _ => None
                                end
  | Eprim_unop _ e1 => match type_of_hfexpr e1 tmap with
                        | Some (Gtyp (Fsint _))
                        | Some (Gtyp (Fuint _)) => Some (gtyp (Fuint 1))
                        | _ => None
                        end
  | Eprim_binop (Bcomp _) e1 e2 => match type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap with
                                    | Some (Gtyp (Fsint _)), Some (Gtyp (Fsint _))
                                    | Some (Gtyp (Fuint _)), Some (Gtyp (Fuint _)) => Some (gtyp (Fuint 1))
                                    | _, _ => None
                                    end
  | Eprim_binop Badd e1 e2
  | Eprim_binop Bsub e1 e2 => match type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap with
                              | Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint w2)) => Some (gtyp (Fuint (maxn w1 w2 + 1)))
                              | Some (Gtyp (Fsint w1)), Some (Gtyp (Fsint w2)) => Some (gtyp (Fsint (maxn w1 w2 + 1)))
                              | _, _ => None
                              end
  | Eprim_binop Bmul e1 e2 => match type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap with
                              | Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint w2)) => Some (gtyp (Fuint (w1 + w2)))
                              | Some (Gtyp (Fsint w1)), Some (Gtyp (Fsint w2)) => Some (gtyp (Fsint (w1 + w2)))
                              | _, _ => None
                              end
  | Eprim_binop Bdiv e1 e2  => match type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap with
                                | Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint w2)) => Some (gtyp (Fuint w1))
                                | Some (Gtyp (Fsint w1)), Some (Gtyp (Fsint w2)) => Some (gtyp (Fsint (w1 + 1)))
                                | _, _ => None
                                end
  | Eprim_binop Brem e1 e2 => match type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap with
                                | Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint w2)) => Some (gtyp (Fuint (minn w1 w2)))
                                | Some (Gtyp (Fsint w1)), Some (Gtyp (Fsint w2)) => Some (gtyp (Fsint (minn w1 w2)))
                                | _, _ => None
                                end
  | Eprim_binop Bdshl e1 e2 => match type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap with
                                | Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint w2)) => Some (gtyp (Fuint (2 ^ w2 + w1 - 1)))
                                | Some (Gtyp (Fsint w1)), Some (Gtyp (Fuint w2)) => Some (gtyp (Fsint (2 ^ w2 + w1 - 1)))
                                | _, _ => None
                                end
  | Eprim_binop Bdshr e1 e2 => match type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap with
                                | Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint w2)) => Some (gtyp (Fuint w1))
                                | Some (Gtyp (Fsint w1)), Some (Gtyp (Fuint w2)) => Some (gtyp (Fsint w1))
                                | _, _ => None
                                end
  | Eprim_binop Bcat e1 e2 => match type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap with
                              | Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint w2))
                              | Some (Gtyp (Fsint w1)), Some (Gtyp (Fsint w2)) => Some (gtyp (Fuint (w1 + w2)))
                              | _, _ => None
                              end
  | Eprim_binop Band e1 e2
  | Eprim_binop Bor e1 e2
  | Eprim_binop Bxor e1 e2 => match type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap with
                              | Some (Gtyp (Fuint w1)), Some (Gtyp (Fuint w2))
                              | Some (Gtyp (Fsint w1)), Some (Gtyp (Fsint w2)) => Some (gtyp (Fuint (maxn w1 w2)))
                              | _, _ => None
                              end
  | Emux c e1 e2 => match type_of_hfexpr c tmap, type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap with
                    | Some (Gtyp (Fuint _)), Some t1, Some t2 => ftype_mux t1 t2
                    | _, _, _ => None
                    end
  end.

(* functions used to record ftype and component type *)
Fixpoint stmts_tmap' (tmap : VM.t (ftype * fcomponent)) (ss : hfstmt_seq): option (VM.t (ftype * fcomponent)) :=
    match ss with
    | Qnil => Some tmap
    | Qcons s ss' => match stmt_tmap' tmap s with
        | Some tmap' => stmts_tmap' tmap' ss'
        | None => None
        end
    end
with stmt_tmap' (tmap : VM.t (ftype * fcomponent)) (s : hfstmt) : option (VM.t (ftype * fcomponent)) :=
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
    | Smem _ _ => None
    | Sinst _ _ => None
    | Swhen cond ss_true ss_false =>
        match type_of_hfexpr cond tmap, stmts_tmap' tmap ss_true with
        | Some (Gtyp _), Some tmap_true => stmts_tmap' tmap_true ss_false 
        | _, _ => None
        end
    end.
    
Fixpoint ports_tmap' (tmap : VM.t (ftype * fcomponent)) (pp : seq hfport) : option (VM.t (ftype * fcomponent)) :=
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
  
Definition module_tmap (tmap : VM.t (ftype * fcomponent)) (m : hfmodule) : option (VM.t (ftype * fcomponent)) :=
    match m with
    | FInmod _ ps ss => match ports_tmap' tmap ps with
                | Some pmap => stmts_tmap' pmap ss
                | None => None
                end
    | _ => None
    end.
  
Fixpoint modules_tmap (tmap : VM.t (ftype * fcomponent)) (ml : seq hfmodule) : option (VM.t (ftype * fcomponent)) :=
    match ml with
    | nil => Some tmap
    | hd :: tl => match module_tmap tmap hd with
                | Some tmap' => modules_tmap tmap' tl
                | _ => None
                end
    end.
  
Definition circuit_tmap (c : hfcircuit) : option (VM.t (ftype * fcomponent)) :=
    match c with
    | Fcircuit v ml => modules_tmap (VM.empty (ftype * fcomponent)) ml
    end.

Fixpoint ftext0 (ft : ftype) : hvalue :=
  match ft with
  | Gtyp (Fuint w) 
  | Gtyp (Fsint w) => gval (zeros w)
  | Gtyp _ => gval [::b0]
  | Atyp atyp n => 
      let fix atypext0 (n : nat) : array_value :=
        match n with
        | 0 => Aone (gval nil)
        | 1 => Aone (ftext0 atyp)
        | n'.+1 => Acons (ftext0 atyp) (atypext0 n')
        end
      in Aval (atypext0 n)
  | Btyp btyp => 
      let fix btypext0 (btyp : ffield) : bundle_value :=
        match btyp with
        | Fnil => bnil
        | Fflips v f ft ff => Bflips v f (ftext0 ft) (btypext0 ff)
        end
      in Bval (btypext0 btyp)
  end.

(* makes val to be of type ft *)
Fixpoint ftext (ft : ftype) (val : hvalue) : option hvalue :=
  match ft, val with
  | Gtyp (Fuint w), Gval c => Some (gval (zext (w - size c) c))
  | Gtyp (Fsint w), Gval c => Some (gval (sext (w - size c) c))
  | Gtyp _, Gval c => Some (gval (zext (1 - size c) c))
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
                  | Some val' => Some (aone val')
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
  | Fnil, Bnil => Some bnil
  | Fflips _ _ ft ff, Bflips v f val tl => match ftext ft val, btypext ff tl with
                | Some val', Some tl' => Some (Bflips v f val' tl')
                | _, _ => None
                end
  | _, _ => None
  end.

(* value of ref expressions *)
Fixpoint hvalue_of_ref (r : href) (s : VM.t hvalue) (tmap: VM.t (ftype * fcomponent)) : option hvalue :=
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
                                          | Aone t, 0 => Some t 
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
                                          | Aone t, 0 => Some t 
                                          | _, _ => None
                                          end )
                                  in aux fv n
              | _, _ => None
              end
  end
(* Expression evaluation, value *)
with eval_hfexpr (exp : hfexpr) (s : VM.t hvalue) (tmap: VM.t (ftype * fcomponent)) : option hvalue :=
  match exp with
  | Econst t c => match t with
                  | Fuint w1 => Some (gval (zext (w1 - size c) c))
                  | Fsint w2 => Some (gval (sext (w2 - size c) c))
                  | _ => None
                  end
  | Eref r => hvalue_of_ref r s tmap
  | Ecast AsUInt e 
  | Ecast AsSInt e => eval_hfexpr e s tmap
  | Ecast AsClock e  
  | Ecast AsReset e  
  | Ecast AsAsync e => match eval_hfexpr e s tmap with Some (Gval val) => Some (gval [::lsb val]) | _ => None end
  | Eprim_binop b e1 e2 =>
      match eval_hfexpr e1 s tmap, eval_hfexpr e2 s tmap, type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap with
      | Some (Gval val1), Some (Gval val2), Some (Gtyp gt1), Some (Gtyp gt2) => 
          let val := LoFirrtl.ebinop_op b gt1 gt2 val1 val2 in Some (gval val)
      | _, _, _, _ => None
      end
  | Eprim_unop u e =>
      match eval_hfexpr e s tmap, type_of_hfexpr e tmap with
      | Some (Gval val1), Some (Gtyp gt1) =>
          let val := LoFirrtl.eunop_op u gt1 val1 in Some (gval val)
      | _, _ => None
      end
  | Emux c e1 e2 => 
      match eval_hfexpr c s tmap, type_of_hfexpr exp tmap, eval_hfexpr e1 s tmap, eval_hfexpr e2 s tmap with
      | Some (Gval valc), Some ft, Some val1, Some val2 => if ~~ (is_zero valc) then ftext ft val1
                                                                                else ftext ft val2
      | _, _, _, _ => None
      end
  end.

Fixpoint init_dclrs (ss : hfstmt_seq) (valmap : VM.t hvalue) (tmap: VM.t (ftype * fcomponent)) : VM.t hvalue := 
  match ss with
  | Qnil => valmap
  | Qcons s ss' => init_dclrs ss' (init_dclr s valmap tmap) tmap
  end
with init_dclr (s : hfstmt) (valmap : VM.t hvalue) (tmap: VM.t (ftype * fcomponent)) : VM.t hvalue := 
  match s with
  | Swire v t => VM.add v (ftext0 t) valmap
  | Snode v e => match eval_hfexpr e valmap tmap with(* e中被用到的变量应该已被赋初值0,则一定有值 *)
                | Some val => VM.add v val valmap
                | _ => valmap
                end
  | Sreg v reg => VM.add v (ftext0 (type reg)) valmap
  | Swhen cond ss_true ss_false => init_dclrs ss_false (init_dclrs ss_true valmap tmap) tmap
  | _ => valmap
  end.

Fixpoint init_registers (ss : hfstmt_seq) (valmap rs : VM.t hvalue) (tmap: VM.t (ftype * fcomponent)) : VM.t hvalue := 
  match ss with
  | Qnil => rs
  | Qcons s ss' => init_registers ss' valmap (init_register s valmap rs tmap) tmap
  end
with init_register (s : hfstmt) (valmap rs : VM.t hvalue) (tmap: VM.t (ftype * fcomponent)) : VM.t hvalue := 
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
  end.

  Fixpoint base_ref (r : href) : V.t :=
    match r with
    | Eid v => v
    | Esubfield r v => base_ref r
    | Esubindex r n => base_ref r
    | Esubaccess r n => base_ref r
    end.

Fixpoint elements_of_ftype (ft : ftype) :=
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

Fixpoint elements_of_hvalue (val : hvalue) : nat :=
  match val with
  | Gval _ => 1
  | Aval aval => elements_of_array_value aval + 1
  | Bval bval => elements_of_bundle_value bval + 1
  end
with elements_of_array_value aval :=
  match aval with
  | Aone val => elements_of_hvalue val
  | Acons val tl => elements_of_hvalue val + elements_of_array_value tl
  end
with elements_of_bundle_value bval :=
  match bval with
  | Bnil => 0
  | Bflips _ _ t fs => elements_of_hvalue t + elements_of_bundle_value fs
  end.

(* 内部aggr也有offset的版本 *)
Fixpoint offset_ref (r : href) (tmap: VM.t (ftype * fcomponent)) (n : nat) : option nat :=
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
  | Esubaccess r e => None(*TBD*)
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
  | Aone val => find_hvalue_by_offset val offset
  | Acons val tl => let element_size := elements_of_hvalue val in if offset >= element_size then
                    find_array_value_by_offset tl (offset - element_size)
                else find_hvalue_by_offset val offset
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
  | Aone val => let element_size := elements_of_hvalue val in if offset >= element_size then None
                else match update_hvalue_by_offset val offset new_val with
                    | Some val' => Some (Aone val')
                    | _ => None
                    end
  | Acons val tl => let element_size := elements_of_hvalue val in if offset >= element_size then
                    match update_array_value_by_offset tl (offset - element_size) new_val with
                    | Some tl' => Some (Acons val tl')
                    | _ => None
                    end 
                else match update_hvalue_by_offset val offset new_val with
                    | Some val' => Some (Acons val' tl)
                    | _ => None
                    end
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

Fixpoint eval_ref_connection (ft : ftype) (val_l val_r : hvalue) (offset_l offset_r : nat) : option (hvalue * hvalue) :=
  match ft with
  | Gtyp gt => match find_hvalue_by_offset val_r offset_r with
              | Some bv => match update_hvalue_by_offset val_l offset_l (gval bv) with
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
  (* bidirction between different sub-component inside the same component *)
  match ft with
  | Gtyp gt => match find_hvalue_by_offset val offset_r with
              | Some bv => match update_hvalue_by_offset val offset_l (gval bv) with
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

Fixpoint eval_hfstmt (st : hfstmt) (rs : VM.t hvalue) (s : VM.t hvalue) (tmap: VM.t (ftype * fcomponent)) : (VM.t hvalue) * (VM.t hvalue) :=
  match st with
  | Snode v e => match eval_hfexpr e s tmap with
                | Some val => (rs, VM.add v val s)
                | _ => (rs, s)
                end
  | Sfcnct r (Eref ref) => (* 考虑flip和aggr *) 
            match offset_ref r tmap 0, offset_ref ref tmap 0, type_of_ref r tmap with
            | Some offset_r, Some offset_ref, Some ft => 
                let base_r := base_ref r in let base_ref := base_ref ref in 
                (* 需要单独讨论连接发生在1个aggr内部 *)
                if base_r == base_ref then match VM.find base_r s with
                | Some val_base_r => match eval_ref_connection1 ft val_base_r offset_r offset_ref with
                    | Some val_base_r' => 
                        (* 讨论是否对应reg *)
                        match VM.find base_r tmap with
                        | Some (_, Register) => (* 更新rs *) (s, VM.add base_r val_base_r' rs)
                        | Some _ => (* 更新s *) (VM.add base_r val_base_r' s, rs)
                        | _ => (rs,s)
                        end
                    | _ => (rs,s)
                    end
                | _ => (rs,s)
                end else
                match VM.find base_r s, VM.find base_ref s with
                | Some val_base_r, Some val_base_ref => 
                    match eval_ref_connection ft val_base_r val_base_ref offset_r offset_ref with
                    | Some (val_base_r', val_base_ref') => 
                        (* 分情况讨论r和ref是否对应reg *)
                        match VM.find base_r tmap, VM.find base_ref tmap with
                        | Some (_, Register), Some (_, Register) => (* 均更新rs *) (s, VM.add base_ref val_base_ref' (VM.add base_r val_base_r' rs))
                        | Some (_, Register), Some _ => (* lhs更新rs, rhs更新s *) (VM.add base_ref val_base_ref' s, VM.add base_r val_base_r' rs)
                        | Some _, Some (_, Register) => (* lhs更新s, rhs更新rs *) (VM.add base_r val_base_r' s, VM.add base_ref val_base_ref' rs)
                        | Some _, Some _ => (* 均更新s *) (VM.add base_ref val_base_ref' (VM.add base_r val_base_r' s), rs)
                        | _,_ => (rs,s)
                        end
                    | _ => (rs,s)
                    end
                | _, _ => (rs,s)
                end
            | _, _, _ => (rs,s)
            end
  | Sfcnct r e => (* 不考虑flip,考虑aggr,不区分mux和其他expr *)
                  match offset_ref r tmap 0, eval_hfexpr e s tmap with
                  | Some offset, Some new_val => let base_r := base_ref r in
                      match  VM.find base_r tmap with
                      | Some (ft, Register) => (* 更新rs *) 
                          match VM.find base_r s with
                          | Some val => match update_hvalue_by_offset val offset new_val with
                                      | Some val' => (VM.add base_r val' rs, s)
                                      | _ => (rs,s)
                                      end
                          | _ => (rs,s)
                          end
                      | Some (ft, _) => (* 更新s *)
                          match VM.find base_r s with
                          | Some val => match update_hvalue_by_offset val offset new_val with
                                      | Some val' => (rs, VM.add base_r val' s)
                                      | _ => (rs,s)
                                      end
                          | _ => (rs,s)
                          end
                      | _ => (rs,s)
                      end
                  | _, _ => (rs,s)
                  end 
  | Swhen cond ss_true ss_false => match eval_hfexpr cond s tmap with
                  | Some (Gval valc) => if ~~ (is_zero valc) then eval_hfstmts ss_true rs s tmap else eval_hfstmts ss_false rs s tmap
                  | _ => (rs, s)
                  end
  | _ => (rs,s)
  end
with eval_hfstmts (sts : hfstmt_seq) (rs : VM.t hvalue) (s : VM.t hvalue) (tmap: VM.t (ftype * fcomponent)) : (VM.t hvalue) * (VM.t hvalue) :=
  match sts with
  | Qnil => (rs, s)
  | Qcons st tl => let '(rs0, s0) := eval_hfstmt st rs s tmap in
                eval_hfstmts tl rs0 s0 tmap
  end.

Definition update_registers (rs : VM.t hvalue) (s : VM.t hvalue) : VM.t hvalue := 
  VM.fold (fun key value temps => VM.add key value temps) rs s.

Fixpoint iterate (n : nat) (func : VM.t hvalue -> VM.t hvalue -> VM.t (ftype * fcomponent) -> VM.t hvalue * VM.t hvalue)
  (rs : VM.t hvalue) (s : VM.t hvalue) (tmap: VM.t (ftype * fcomponent)) : (VM.t hvalue) * (VM.t hvalue) :=
  match n with
  | 0 => (rs, s)
  | n'.+1 => let s_regupd := update_registers rs s in
             let (rs0, s0) := func (VM.empty hvalue)(* everytime we start with an empty map to record the value of registers in the next iteration *) s_regupd tmap in
             if VM.equal (fun val1 val2 => hvalue_eqn val1 val2) s0 s (* LFP *) then (rs0, s0) else iterate n' func rs0 s0 tmap
  end.

Definition n := 10. (* TBD *)

Definition compute_Sem (c : hfcircuit) (inputs : VM.t hvalue) : option (VM.t hvalue) :=
  match circuit_tmap c, c with
  | Some tmap, Fcircuit _ [::(FInmod _ ps ss)] => 
        let s := init_dclrs ss inputs tmap in 
        let rs := init_registers ss s (VM.empty hvalue) tmap in (* assume the circuit starts after a reset signal *)
        let (rs0,s0) := iterate n (eval_hfstmts ss) rs s tmap in Some s0
  | _, _ => None
  end.

End MakeSemantics.

(* HiFirrtl Semantics with variables of eqType *)
Module HiF_sem := MakeSemantics VarOrder VM.
