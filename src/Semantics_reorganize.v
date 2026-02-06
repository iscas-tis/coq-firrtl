From Coq Require Import FunInd FMaps FMapAVL OrderedType ZArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat ssrint eqtype seq fintype fingraph.
From simplssrlib Require Import Types SsrOrder FSets FMaps Tactics Var Store.
From nbits Require Import NBits.
From firrtl Require Import Firrtl Env HiEnv HiFirrtl.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section Value.

  Variable var_mod : eqType.
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
  | Sinst : var (* instance name *) -> var_mod (* module type *) -> hfstmt
  | Snode : var -> hfexpr -> hfstmt
  | Sfcnct : href -> hfexpr -> hfstmt
  | Sinvalid : href -> hfstmt
  | Swhen : hfexpr -> hfstmt_seq -> hfstmt_seq -> hfstmt
  with hfstmt_seq : Type :=
       | Qnil
       | Qcons : hfstmt -> hfstmt_seq -> hfstmt_seq.

  Inductive hfport : Type :=
  | Finput : var -> ftype -> hfport
  | Foutput : var -> ftype -> hfport
  .

  Inductive hfmodule : Type :=
  | FInmod : var_mod -> seq hfport -> hfstmt_seq -> hfmodule
  | FExmod : var_mod -> seq hfport -> hfstmt_seq -> hfmodule.

  (* Circuit, i.e. a list of modules with an indication which one is the main module *)
  Inductive hfcircuit : Type := Fcircuit : var_mod -> seq hfmodule -> hfcircuit.

  (* General data value of an expression (which may have an aggregate type *)
  Inductive hvalue : Type :=
  | Gval : bits -> hvalue
  | Aval : array_value -> hvalue
  | Bval : bundle_value -> hvalue
  with array_value : Type :=
  | Anil : array_value
  | Acons : hvalue -> array_value -> array_value
  with bundle_value : Type :=
  | Bnil : bundle_value
  | Bflips : var -> fflip -> hvalue -> bundle_value -> bundle_value.

  (* general data value equality is decidable *)
  Lemma hvalue_eq_dec : forall {x y : hvalue}, {x = y} + {x <> y}
  with array_value_eq_dec : forall {x y : array_value}, {x = y} + {x <> y}
  with bundle_value_eq_dec : forall {x y : bundle_value}, {x = y} + {x <> y}.
  Proof.
  * clear hvalue_eq_dec.  by decide equality ; decide equality ; decide equality.
  * clear array_value_eq_dec.  by decide equality.
  * clear bundle_value_eq_dec.  decide equality ; first by decide equality.
    by apply (eq_comparable).
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

  Axiom hvalue_eqP : Equality.axiom hvalue_eqn.
  Axiom array_value_eqP : Equality.axiom array_value_eqn.
  Axiom bundle_value_eqP : Equality.axiom bundle_value_eqn.

  Canonical hvalue_eqMixin := EqMixin hvalue_eqP.
  Canonical hvalue_eqType := Eval hnf in EqType hvalue hvalue_eqMixin.

End Value.

Module MakeSemantics
  (V_mod : SsrOrder) (* module names *)
  (V : SsrOrder) (* identifier names *)
  (VM_mod : SsrFMap with Module SE := V_mod)
  (VM : SsrFMap with Module SE := V).

  Local Notation var_mod := V_mod.t.
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
  Definition anil := @Anil V.T.
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

  Definition hfstmt := hfstmt V_mod.T V.T.
  Definition hfstmt_seq := hfstmt_seq V_mod.T V.T.
  Definition qnil := Qnil V_mod.T V.T.
  Definition qcons s ss := @Qcons V_mod.T V.T s ss.
  Definition sskip := @Sskip V_mod.T V.T.
  Definition swire v t := @Swire V_mod.T V.T v t.
  Definition sreg v r := @Sreg V_mod.T V.T v r.
  Definition smem v m := @Smem V_mod.T V.T v m.
  Definition snode v e := @Snode V_mod.T V.T v e.
  Definition sfcnct v1 v2 := @Sfcnct V_mod.T V.T v1 v2.
  Definition sinvalid v1 := @Sinvalid V_mod.T V.T v1.
  Definition swhen c s1 s2 := @Swhen V_mod.T V.T c s1 s2.
  (* Definition sstop e1 e2 n := @Sstop V.T e1 e2 n. *)
  Definition sinst v1 v2 := @Sinst V_mod.T V.T v1 v2.

  Definition hfreg := @hfreg V.T.
  Definition mk_hfreg := @mk_freg V.T.
  Definition rst := @rst V.T.
  Definition nrst := @NRst V.T.
  Definition rrst (e1 e2 : hfexpr) := @Rst V.T e1 e2.
  Definition type (r : hfreg) := @type V.T r.
  Definition clock (r : hfreg) := @clock V.T r.
  Definition mk_mem_port := @mk_mem_port V.T.
  Definition mem_port := @mem_port V.T.
  Definition hfmem := @hfmem V.T.
  Definition mk_hfmem := @mk_fmem V.T.
  Definition hfport := @hfport V.T.
  Definition hinport (v : var) (t : ftype) := @Finput V.T v t.
  Definition houtport (v : var) (t : ftype) := @Foutput V.T v t.
  Definition hfmodule := @hfmodule V_mod.T V.T.
  Definition hfinmod (v : var_mod) (ps : seq hfport) (ss : hfstmt_seq) := @FInmod V_mod.T V.T v ps ss.
  Definition hfexmod (v : var_mod) (ps : seq hfport) (ss : hfstmt_seq) := @FExmod V_mod.T V.T v ps ss.

  Definition hfcircuit := @hfcircuit V_mod.T V.T.

(* type of reference r, according to the type map tmap *)
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
(* type of a Emux expression for ground types *)
Definition fgtyp_mux (x y : fgtyp) : option fgtyp :=
    match x, y with
    | Fuint wx, Fuint wy => Some (Fuint (Nat.max wx wy))
    | Fsint wx, Fsint wy => Some (Fsint (Nat.max wx wy))
    | Fclock, Fclock => Some Fclock
    | Freset, Freset => Some Freset
    | Fasyncreset, Fasyncreset => Some Fasyncreset
    | _, _ => None
    end.

(* type of a Emux expression for general types *)
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
(* type of a Emux expression for bundle types *)
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

(* type of expression e, given that references have types as in tmap *)
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

(* Find the interface type of the list of ports ps.
   Because the result is always a bundle type, we return the ffields *)
Fixpoint port_interface_ffield (ps : seq hfport) : ffield :=
   match ps with
   | nil => fnil
   | Finput  v t :: ps' => fflips v Nflip   t (port_interface_ffield ps')
   | Foutput v t :: ps' => fflips v Flipped t (port_interface_ffield ps')
   end.

(* Find the interface types of all modules in ml
   and return them as one tmap *)
Fixpoint ports_interface_tmap (ml : seq hfmodule) : option (VM_mod.t ffield) :=
   match ml with
   | nil => Some (VM_mod.empty ffield)
   | (FInmod m ps _) :: tl => match ports_interface_tmap tl with
                              | Some im => Some (VM_mod.add m (port_interface_ffield ps) im)
                              | _ => None
                              end
   | _ => None
   end.

(* Extend tmap with the component definitions in statement sequence ss,
   including those that fall out of scope because they were defined within Swhen.
   modmap contains the types of modules (for Sinst statements).
   Also ensure that a component is not defined twice. *)
Fixpoint stmts_tmap (tmap : VM.t (ftype * fcomponent)) (modmap : VM_mod.t ffield) (ss : hfstmt_seq): option (VM.t (ftype * fcomponent)) :=
    match ss with
    | Qnil => Some tmap
    | Qcons s ss' => match stmt_tmap tmap modmap s with
        | Some tmap' => stmts_tmap tmap' modmap ss'
        | None => None
        end
    end
(* Extend tmap with the component declaration in statement s,
   including those that fall out of scope because they were defined within Swhen.
   modmap contains the types of modules (for Sinst statements).
   Also ensure that a component is not defined twice. *)
with stmt_tmap (tmap : VM.t (ftype * fcomponent)) (modmap : VM_mod.t ffield) (s : hfstmt) : option (VM.t (ftype * fcomponent)) :=
    match s with
    | Sskip
    | Sfcnct _ _
    | Sinvalid _ => Some tmap
    | Swire v t => if VM.mem v tmap then None
                   else Some (VM.add v (t, Wire) tmap)
    | Sreg v reg => if VM.mem v tmap then None
                    else match type_of_hfexpr (clock reg) tmap with
                         | Some (Gtyp Fclock) => Some (VM.add v ((type reg), Register) tmap)
                         | _ => None
                         end
    | Snode v expr => if VM.mem v tmap then None
                      else match type_of_hfexpr expr tmap with
                           | Some ft => Some (VM.add v (ft, Node) tmap)
                           | _ => None
                           end
    | Smem _ _ => None
    | Sinst id mo => match VM_mod.find mo modmap with
                     | Some ff => Some (VM.add id (Btyp ff, Instanceof) tmap)
                     | _ => None
                     end
    | Swhen cond ss_true ss_false =>
        match type_of_hfexpr cond tmap, stmts_tmap tmap modmap ss_true with
        | Some (Gtyp (Fuint _)), Some tmap_true => stmts_tmap tmap_true modmap ss_false
        | _, _ => None
        end
    end.

(* Extend tmap with the component definitions in ports sequence pp.
   Also ensure that no port is defined twice.
   (While one could define a function without input parameter tmap,
   the current one is more efficient because it uses tail recursion) *)
Fixpoint ports_tmap (tmap : VM.t (ftype * fcomponent)) (pp : seq hfport) : option (VM.t (ftype * fcomponent)) :=
    match pp with
    | [::] => Some tmap
    | Finput  v t :: pp' => if VM.mem v tmap then None
                            else ports_tmap (VM.add v (t, In_port) tmap) pp'
    | Foutput v t :: pp' => if VM.mem v tmap then None
                            else ports_tmap (VM.add v (t, Out_port) tmap) pp'
    end.

(* Find the type map with the component definitions in the ports and statements
   of module m. The module has to be internal.
   modmap contains the types of modules (for Sinst statements). *)
Definition module_tmap (modmap : VM_mod.t ffield) (m : hfmodule) : option (VM.t (ftype * fcomponent)) :=
    match m with
    | FInmod _ ps ss => match ports_tmap (VM.empty (ftype * fcomponent)) ps with
                        | Some pmap => stmts_tmap pmap modmap ss
                        | None => None
                        end
    | _ => None
    end.

(* Find the type map of a list of modules;
   we already know that modmap contains the interfaces of the modules
   (used to find the type of Sinst statements).
   All modules must be internal. *)
Fixpoint modules_tmaps (modmap : VM_mod.t ffield) (ml : seq hfmodule) : option (VM_mod.t (VM.t (ftype * fcomponent))) :=
   match ml with
   | nil => Some (VM_mod.empty (VM.t (ftype * fcomponent))) (* empty map *)
   | FInmod v _ _ as mo :: ml'
   | FExmod v _ _ as mo :: ml' => match module_tmap modmap mo, modules_tmaps modmap ml' with
                                  | Some mp, Some mps => Some (VM_mod.add v mp mps)
                                  | _, _ => None
                                  end
   end.

(* Find the type map of a circuit.
   (It first finds the interface map of all the modules
   and then uses this to find the detailed type map of every module,
   including the Sinst statements in them. Possibly the interface map
   should also be returned?) *)
Definition circuit_tmaps (c : hfcircuit) : option (VM_mod.t (VM.t (ftype * fcomponent))) :=
    match c with
    | Fcircuit v ml => match ports_interface_tmap ml with
                       | Some modmap => modules_tmaps modmap ml
                       | None => None
                       end
    end.

(* Calculate a "constant zero" value *)
Fixpoint ftext0 (ft : ftype) : hvalue :=
  match ft with
  | Gtyp (Fuint w) 
  | Gtyp (Fsint w) => gval (zeros w)
  | Gtyp _ => gval [::b0]
  | Atyp atyp n => 
      let fix atypext0 (n : nat) : array_value :=
        match n with
        | 0 => anil
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

(* makes the constant val to be of type ft.
   In particular, extends bit patterns to the correct width. *)
Fixpoint ftext (ft : ftype) (val : hvalue) : option hvalue :=
  match ft, val with
  | Gtyp (Fuint w), Gval c => Some (gval (zext (w - size c) c))
  | Gtyp (Fsint w), Gval c => Some (gval (sext (w - size c) c))
  | Gtyp _, Gval c => Some (gval (zext (1 - size c) c))
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
  | Anil => Some anil
  | Acons val tl => match ftext ft val, atypext ft tl with
                            | Some val', Some tl' => Some (Acons val' tl')
                            | _, _ => None
                            end
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

(* How should components in a circuit be referred to?
   Through an access path: a sequence of instance names, and finally a component name.
   Instance names are V (not V_mod).
   Actually instance names might by V_mod but that would complicate matters;
   then they cannot be part of the module’s type map but require a separate map.
   (They might require it anyway because instances remain instances even after LowerTypes.)

   A related question is how to link inputs/outputs of an instance with
   the corresponding fields in the outer module.

   I think it is easier to store the port values in the instance variable of the outer module.
   Inputs and outputs of a module are accessed by looking at the outer module,
   i.e. the last element of the access path becomes the component name in that module.
   (The other way around, one would have to combine all inputs and outputs of the inner module
   into one bundle every time the outer module accesses an instance.)

   So, the value of a circuit is a PMap where
   - keys are access sequences (a list of instance names + a component name)
   - inputs and outputs are stored with key the list of instance names, without component name;
     the name of the input/output is used as the name of a field in the bundle that is stored under this key

Example:

Top module input/output access sequence: [::]
Top module register r: [:: r]
Instance i in top module = port interface of instance i: [:: i]
Input of instance i: [:: i]
Wire w in instance i : [:: i, w]

r, i, w are all of type V (not V_mod).


 *)

Module MakeSeqOrderMinimal (O : SsrOrder) <: SsrOrderMinimal with Definition t := seq_eqType O.T.

  Definition t : eqType := seq_eqType O.T.

  Definition eqn (x y : t) : bool := x == y.

  Fixpoint ltn (x y : t) : bool :=
    match x, y with
    | [::], [::] => false
    | [::], _ => true
    | _, [::] => false
    | xh :: xt, yh :: yt => (O.ltn xh yh) || ((xh == yh) && ltn xt yt)
    end.

  Lemma ltn_trans (x y z : t) : ltn x y -> ltn y z -> ltn x z.
  Proof.
    revert y z ; induction x as [|xh xt] ; intros.
    * (* x == [::] *)
      destruct y as [|yh yt] ; first by done.
      destruct z as [|zh zt] ; by done.
    * destruct y as [|yh yt] ; first by done.
      destruct z as [|zh zt] ; first by done.
      simpl ; simpl in H, H0.
      move /orP : H => [H|/andP H] ; move /orP : H0 => [H0|/andP H0].
      + by rewrite (O.ltn_trans H H0) orTb //.
      + move : H0 => [/eqP H0 _] ; subst yh.
        by rewrite H orTb //.
      + move : H => [/eqP H _] ; subst yh.
        by rewrite H0 orTb //.
      + move : H => [/eqP H1 H2] ; move : H0 => [/eqP H3 H4] ; subst yh zh.
        by rewrite eq_refl andTb (IHxt yt zt H2 H4) orbT //.
  Qed.

  Lemma ltn_not_eqn (x y : t) : ltn x y -> x != y.
  Proof.
    revert y ; induction x as [|xh xt] ; intros.
    * destruct y as [|yh yt] ; by done.
    * destruct y as [|yh yt] ; first by done.
      rewrite eqseq_cons ; simpl in H.
      move /orP : H => [H|/andP [_ H]].
      + by rewrite (O.ltn_eqF H) andFb //.
      + by rewrite (negbTE (IHxt yt H)) andbF //.
  Qed.

  Definition compare (x y : t) : Compare ltn eqn x y.
  Proof.
    revert y ; induction x as [|xh xt] ; intros.
    * destruct y as [|yh yt].
      + apply EQ ; done.
      + apply LT ; done.
    * destruct y as [|yh yt].
      + apply GT ; done.
      + destruct (O.compare xh yh).
        - apply LT ; simpl ; rewrite l orTb //.
        - unfold O.eq in e.
          specialize (IHxt yt) ; destruct IHxt.
          * apply LT ; simpl.
            by rewrite e andTb i orbT //.
          * apply EQ ; unfold eqn in i.
            by rewrite /eqn eqseq_cons e i //.
          * apply GT ; simpl.
            by rewrite eq_sym e andTb i orbT //.
        - apply GT ; simpl ; rewrite l orTb //.
  Defined.

End MakeSeqOrderMinimal.

Module MakeSeqOrder (O : SsrOrder) <: SsrOrder
    with Definition T := seq_eqType O.T.
  Module M := MakeSeqOrderMinimal O.
  Module P := MakeSsrOrder M.
  Include P.
End MakeSeqOrder.

Module SeqVarOrder := MakeSeqOrder V.
Module SVS <: SsrFSet := FSets.MakeTreeSet SeqVarOrder.
Module SVM <: SsrFMap := FMaps.MakeTreeMap SeqVarOrder.

(* select a field in a Bvalue *)
Fixpoint select_field (bu : bundle_value) (v : var) : option (hvalue (* * fflip*) ) :=
   match bu with
   | Bnil => None
   | Bflips v' fl hv bu' => if v == v' then Some (hv (*, fl *) ) else select_field bu' v
   end.

(* value of reference r in instance inst. s is the value map of the circuit. tmap is the type map of the current module. *)
Fixpoint hvalue_of_ref (inst : SVM.key) (r : href) (s : SVM.t hvalue) (tmap: VM.t (ftype * fcomponent)) : option hvalue :=
  match r with
  | Eid v => match VM.find v tmap with
             | Some (_, In_port)
             | Some (_, Out_port) => match SVM.find inst s with
                                     | Some (Bval bu) => select_field bu v
                                     | _ => None
                                     end
             | _ => SVM.find (rcons inst v) s
             end
  | Esubfield r v => match hvalue_of_ref inst r s tmap with
              | Some (Bval fv) => select_field fv v
              | _ => None
              end
  | Esubindex r n => match hvalue_of_ref inst r s tmap with
              | Some (Aval fv) => let fix aux fx m := (
                                          match fx, m with
                                          | Acons t fxs, m'.+1 => aux fxs m'
                                          | Acons t _, 0 => Some t 
                                          | _, _ => None
                                          end )
                                  in aux fv n
              | _ => None
              end
  | Esubaccess r e => match eval_hfexpr inst e s tmap, hvalue_of_ref inst r s tmap with 
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
with eval_hfexpr (inst : SVM.key) (exp : hfexpr) (s : SVM.t hvalue) (tmap: VM.t (ftype * fcomponent)) : option hvalue :=
  match exp with
  | Econst t c => match t with
                  | Fuint w1 => if (size c) > w1 then None else Some (gval (zext (w1 - size c) c))
                  | Fsint w2 => if (size c) > w2 then None else Some (gval (sext (w2 - size c) c))
                  | _ => None
                  end
  | Eref r => hvalue_of_ref inst r s tmap
  | Ecast AsUInt e 
  | Ecast AsSInt e => eval_hfexpr inst e s tmap
  | Ecast AsClock e  
  | Ecast AsAsync e => match eval_hfexpr inst e s tmap with Some (Gval val) => Some (gval [::lsb val]) | _ => None end
  | Eprim_binop b e1 e2 =>
      match eval_hfexpr inst e1 s tmap, eval_hfexpr inst e2 s tmap, type_of_hfexpr e1 tmap, type_of_hfexpr e2 tmap with
      | Some (Gval val1), Some (Gval val2), Some (Gtyp gt1), Some (Gtyp gt2) => 
          let val := LoFirrtl.ebinop_op b gt1 gt2 val1 val2 in Some (gval val)
      | _, _, _, _ => None
      end
  | Eprim_unop u e =>
      match eval_hfexpr inst e s tmap, type_of_hfexpr e tmap with
      | Some (Gval val1), Some (Gtyp gt1) =>
          let val := LoFirrtl.eunop_op u gt1 val1 in Some (gval val)
      | _, _ => None
      end
  | Emux c e1 e2 => 
      match eval_hfexpr inst c s tmap, type_of_hfexpr exp tmap, eval_hfexpr inst e1 s tmap, eval_hfexpr inst e2 s tmap with
      | Some (Gval valc), Some ft, Some val1, Some val2 => if ~~ (is_zero valc) then ftext ft val1
                                                                                else ftext ft val2
      | _, _, _, _ => None
      end
  end.

Fixpoint init_dclrs (inst : SVM.key) (ss : hfstmt_seq) (valmap : SVM.t hvalue) (tmap: VM.t (ftype * fcomponent)) : SVM.t hvalue := 
  match ss with
  | Qnil => valmap
  | Qcons s ss' => init_dclrs inst ss' (init_dclr inst s valmap tmap) tmap
  end
with init_dclr (inst : SVM.key) (s : hfstmt) (valmap : SVM.t hvalue) (tmap: VM.t (ftype * fcomponent)) : SVM.t hvalue := 
  match s with
  | Swire v t => SVM.add (rcons inst v) (ftext0 t) valmap
  | Snode v e => match eval_hfexpr inst e valmap tmap with(* e中被用到的变量应该已被赋初值0,则一定有值 *)
                | Some val => SVM.add (rcons inst v) val valmap
                | _ => valmap
                end
  (*| Sreg v reg => SVM.add (rcons inst v) (ftext0 (type reg)) valmap*)
  | Swhen cond ss_true ss_false => init_dclrs inst ss_false (init_dclrs inst ss_true valmap tmap) tmap
  | _ => valmap
  end.

(*Fixpoint init_registers (ss : hfstmt_seq) (valmap rs : VM.t hvalue) (tmap: VM.t (ftype * fcomponent)) : VM.t hvalue := 
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
  end.*)

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
  | Anil => 0
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

(* connects reference ref (which cannot be an input or output port) to expression val *)
Definition connect_passive (inst : SVM.key) (ref : href) (val : hvalue) (ns : SVM.t hvalue) (tmap : VM.t (ftype * fcomponent)) : option (SVM.t hvalue) :=
   match SVM.find (rcons inst (base_ref ref)) ns, offset_ref ref tmap 0 with
   | Some rval, Some offs => match update_hvalue_by_offset rval offs val with
                             | Some new_rval => Some (SVM.add (rcons inst (base_ref ref)) new_rval ns)
                             | None => None
                             end
   | _, _ => None
   end.

(* calculates the offset of the port named p, based on the interface value val *)
Fixpoint offset_of_port (p : V.t) (val : bundle_value) : option nat :=
   match val with
   | Bnil => None
   | Bflips p' _ vp' val' => if (p == p') then Some 1
                             else match offset_of_port p val' with
                                  | Some offs => Some (elements_of_hvalue vp' + offs)
                                  | None => None
                                  end
   end.

(* connects reference ref (which is a ground-type [output or flipped input] port) to expression val *)
Definition connect_passive_port (inst : SVM.key) (ref : href) (val : hvalue) (ns : SVM.t hvalue) (tmap : VM.t (ftype * fcomponent)) : option (SVM.t hvalue) :=
   match SVM.find inst ns with
   | Some (Bval rval) => match offset_of_port (base_ref ref) rval with
                         | Some port_offs => match offset_ref ref tmap port_offs with
                                             | Some offs => match update_hvalue_by_offset (Bval rval) offs val with
                                                            | Some new_rval => Some (SVM.add inst new_rval ns)
                                                            | None => None
                                                            end
                                             | None => None
                                             end
                         | None => None
                         end
   | _ => None
   end.

Fixpoint is_passive (ft : ftype) : bool :=
    match ft with
    | Gtyp _ => false
    | Atyp ft' _ => is_passive ft'
    | Btyp ff => is_passive_fields ff
    end
with is_passive_fields (ff : ffield) : bool :=
    match ff with
    | Fnil => true
    | Fflips _ Nflip ft' ff' => is_passive ft' && is_passive_fields ff'
    | Fflips _ Flipped _ _ => false
    end.

(* changes ns for a bidirectional connect statement "connect left, right". ft is the (common) type of the references.
   rs = values to be read; ns = new values to be written; tmap = type map of the current module. *)
Fixpoint bidirectional_connect (ft : ftype) (inst : SVM.key) (left right : href) (rs ns : SVM.t hvalue) (tmap : VM.t (ftype * fcomponent)) : option (SVM.t hvalue) :=
   if is_passive ft then match hvalue_of_ref inst right rs tmap, VM.find (base_ref left) tmap with
                         | Some val, Some (_, In_port) (* can still happen if the port has a flipped field *)
                         | Some val, Some (_, Out_port) => connect_passive_port inst left val ns tmap
                         | Some val, Some (_, _       ) => connect_passive      inst left val ns tmap
                         | _, _ => None
                         end
                    else let fix bidirectional_connect_non_passive (ft : ftype) (left right : href) (ns : SVM.t hvalue) : option (SVM.t hvalue) :=
                             match ft with
                             | Gtyp _ => None (* this cannot happen, as ft must be a non-passive type *)
                             | Atyp ft' m => let fix bidirectional_array_connect (i : nat) (ns : SVM.t hvalue) : option (SVM.t hvalue) :=
                                                 match i with
                                                 | 0 => Some ns
                                                 | i'.+1 => match bidirectional_array_connect i' ns with
                                                            | Some ns' => bidirectional_connect_non_passive ft' (Esubindex left i) (Esubindex right i) ns'
                                                            | None => None
                                                            end
                                                 end
                                             in bidirectional_array_connect m ns
                             | Btyp ff => bidirectional_bundle_connect ff inst left right rs ns tmap
                             end
                         in bidirectional_connect_non_passive ft left right ns
with bidirectional_bundle_connect (ff : ffield) (inst : SVM.key) (left right : href) (rs ns : SVM.t hvalue) (tmap : VM.t (ftype * fcomponent)) : option (SVM.t hvalue) :=
   match ff with
   | Fnil => Some ns
   | Fflips v Nflip   ft' ff' => match bidirectional_connect ft' inst (Esubfield left v) (Esubfield right v) rs ns tmap with
                                 | Some ns' => bidirectional_bundle_connect ff' inst left right rs ns' tmap
                                 | None => None
                                 end
   | Fflips v Flipped ft' ff' => match bidirectional_connect ft' inst (Esubfield right v) (Esubfield left v) rs ns tmap with
                                 | Some ns' => bidirectional_bundle_connect ff' inst left right rs ns' tmap
                                 | None => None
                                 end
   end.

(* evaluate the statement st, which is part of the code in instance inst.
   rs contains the old values that are read; ns contains the new values that have been updated until now;
   the return value is ns, changed by the effect of st.
   tmap is the type map of the current module. *)
Fixpoint eval_hfstmt (inst : SVM.key) (st : hfstmt) (rs ns : SVM.t hvalue) (tmap: VM.t (ftype * fcomponent)) : option (SVM.t hvalue) :=
  match st with
  | Snode v e => match eval_hfexpr inst e rs tmap with
                | Some val => Some (SVM.add (rcons inst v) val ns)
                | _ => None
                end
  | Sfcnct r_left (Eref r_right) => (* 考虑flip和aggr *)
            match type_of_ref r_left tmap with
            | Some ft => bidirectional_connect ft inst r_left r_right rs ns tmap
            | None => None
            end
  | Sfcnct r e => (* 不考虑flip,考虑aggr,不区分mux和其他expr *)
            match eval_hfexpr inst e rs tmap, VM.find (base_ref r) tmap with
            | Some val, Some (_, In_port)
            | Some val, Some (_, Out_port) => connect_passive_port inst r val ns tmap
            | Some val, Some (_, _       ) => connect_passive      inst r val ns tmap
            | _, _ => None
            end
  | Swhen cond ss_true ss_false => match eval_hfexpr inst cond rs tmap with
                  | Some (Gval valc) => if ~~ (is_zero valc) then eval_hfstmts inst ss_true rs ns tmap else eval_hfstmts inst ss_false rs ns tmap
                  | _ => None
                  end
  | _ => Some ns
  end
with eval_hfstmts (inst : SVM.key) (sts : hfstmt_seq) (rs ns : SVM.t hvalue) (tmap: VM.t (ftype * fcomponent)) : option (SVM.t hvalue) :=
  match sts with
  | Qnil => Some ns
  | Qcons st tl => match eval_hfstmt inst st rs ns tmap with
                | Some ns0 => eval_hfstmts inst tl rs ns0 tmap
                | None => None
                end
  end.

(* Find the module named m in module sequence ms *)
Fixpoint find_module (m : var_mod) (ms : seq hfmodule) : option hfmodule :=
    match ms with
    | [::] => None
    | (FInmod mn _ _) as m' :: ms'
    | (FExmod mn _ _) as m' :: ms' => if m == mn then Some m'
                                                 else find_module m ms'
    end.

(* The instance inst is of type m.
   Add this information, and all instances that are sub-instances of inst, to inst_map, up to n sub-instances deep.
   ms is the sequence of all modules in the current circuit. *)
Fixpoint find_module_instances (n : nat) (inst : SVM.key) (m : var_mod) (ms : seq hfmodule) (inst_map : SVM.t var_mod) : option (SVM.t var_mod) :=
    match find_module m ms with
    | Some (FInmod _ _ ss) => match n with
                              | 0 => Some (SVM.add inst m inst_map)
                              | n'.+1 => let fix find_stmts_instances (ss : hfstmt_seq) (inst_map : SVM.t var_mod) : option (SVM.t var_mod) :=
                                             match ss with
                                             | Qnil => Some inst_map
                                             | Qcons (Sinst i m') ss' => match find_module_instances n' (rcons inst i) m' ms inst_map with
                                                                         | Some inst_map' => find_stmts_instances ss' inst_map'
                                                                         | None => None
                                                                         end
                                             | Qcons _ ss' => find_stmts_instances ss' inst_map
                                             end
                                         in find_stmts_instances ss (SVM.add inst m inst_map)
                              end
    | _ => None
    end.

Local Definition find_circuit_instances_nat (c : hfcircuit) (n : nat) : option (SVM.t var_mod) :=
    match c with
    | Fcircuit top ms => find_module_instances n [::] top ms (SVM.empty var_mod)
    end.

Local Definition var_mod_eq (x y : var_mod) : bool := x == y.

Lemma find_circuit_instances_nat_fixed_point :
    forall (c : hfcircuit) (n : nat),
        match find_circuit_instances_nat c n, find_circuit_instances_nat c n.+1 with
        | Some insts_n, Some insts_nplus1 =>
                SVM.equal var_mod_eq insts_n insts_nplus1
            ->
                match c with
                | Fcircuit _ ms => match find_circuit_instances_nat c (size ms) with
                                   | Some insts_size_ms => SVM.equal var_mod_eq insts_n insts_size_ms
                                   | None => false
                                   end
                end
        | _, _ => true
        end.
Proof.
intros.
unfold find_circuit_instances_nat.
destruct c as [top ms].
(* How could this be proven? What inductive strengthening might work?
   find_module_instances i sq ... ms insts
   where i + size sq == n
   and uniq (map of sq to their module types)
   and some condition on insts?

        ->
            find_circuit_instances_nat c n = find_circuit_instances_nat c (size ms) *)
Abort.

(* Find all instances of the circuit c.
   The result is a map with domain all instances, and for every instance its type is indicated. *)
Definition find_circuit_instances (c : hfcircuit) : option (SVM.t var_mod) :=
    match c with
    | Fcircuit _ ms => find_circuit_instances_nat c (size ms)
    end.

(* We now would like a lemma like the following:
   If circuit c does not contain circular instance statements,
   and all its modules are internal,
   then find_circuit_instances c will find all instances
   (in particular, a larger value of n would not change the result).

   Perhaps it could be formulated like this:
   If circuit c does not contain circular instance statements,
   then forall n : nat, n >= size ms -> find_circuit_instances c = find_module_instances n' [::] top ms (SVM.empty var_mod).

   Or so:
   Given fun (n : nat) => find_module_instances n [::] top ms (SVM.empty var_mod).
   Note that this function is monotonous.
   if this function in n has a (least) fixed point, it is reached with an n <= size ms.
*)

(* Evaluate the (connect) statements in all instances indicated by insts.
   Update ns accordingly.
   ms is the sequence of all modules in the current circuit.
   tmaps indicates for every module the type map. *)
Local Definition eval_instances (insts : SVM.t var_mod) (ms : seq hfmodule) (rs ns : SVM.t hvalue) (tmaps : VM_mod.t (VM.t (ftype * fcomponent))) : option (SVM.t hvalue) :=
    SVM.fold (fun (inst : SVM.key) (m : var_mod) (opt_ns : option (SVM.t hvalue))
               => match opt_ns, find_module m ms, VM_mod.find m tmaps with
                  | Some ns, Some (FInmod _ _ ss), Some tmap => eval_hfstmts inst ss rs ns tmap
                  | _, _, _ => None
                  end)
             insts (Some ns).

(* Evaluate the (connect) statements etc. in circuit c *)
Definition eval_circuit (c : hfcircuit) (rs : SVM.t hvalue) : option (SVM.t hvalue) :=
    match circuit_tmaps c, find_circuit_instances c, c with
    | Some tmaps, Some insts, Fcircuit top ms => eval_instances insts ms rs rs tmaps
    | _, _, _ => None
    end.

(* Generate an initial value map for the instances insts.
   In this map, all components in all instances are initialized to zero
   (should be: initialized to "uninitialized") *)
Local Definition init_instances_dclrs (insts : SVM.t var_mod) (ms : seq hfmodule) (tmaps : VM_mod.t (VM.t (ftype * fcomponent))) : option (SVM.t hvalue) :=
    SVM.fold (fun (inst : SVM.key) (m : var_mod) (opt_valmap : option (SVM.t hvalue))
               => match opt_valmap, find_module m ms, VM_mod.find m tmaps with
                  | Some valmap, Some (FInmod _ _ ss), Some tmap => Some (init_dclrs inst ss valmap tmap)
                  | _, _, _ => None
                  end)
             insts (Some (SVM.empty hvalue)).

(* Generate an initial value map for circuit c.
   In this map, all components in all instances are initialized to zero
   (should be: initialized to "uninitialized". It should also initialize registers!) *)
Definition init_circuit_dclrs (c : hfcircuit) : option (SVM.t hvalue) :=
    match circuit_tmaps c, find_circuit_instances c, c with
    | Some tmaps, Some insts, Fcircuit _ ms => init_instances_dclrs insts ms tmaps
    | _, _, _ => None
    end.

(*
The next step is to define an iteration that looks approximately like this:
1. Call init_circuit_dclrs to calculate an initial value map rs.
   Additionally, copy register values and external inputs from their sources into rs.
2. Repeat until stabilization:
   - Set ns := rs
   - Call eval_circuit to update ns
   - If ns == rs (for all components except registers) then stabilization has been achieved, leave this loop.
   - Update the wires, nodes, all outputs, and internal inputs in rs to their values in ns.
     (Registers and external inputs should not be changed).
   (If stabilization is not achieved within # of ground-type components iterations,
   then there must be a combinational loop in the circuit.)
3. Now the ns value map contains the stabilized values;
   in this value map, the registers have reached their new values.
*)

(* finds the instance and component type of component “key” in the circuit described by tmaps and insts. *)
Definition find_instance_and_type (tmaps : VM_mod.t (VM.t (ftype * fcomponent))) (insts : SVM.t var_mod) (key : SVM.key) : option (SVM.key * fcomponent) :=
    match SVM.find key insts with
    | Some _ => (* _ is the module type of key. key is a module. *)
                Some (key, Fmodule)
    | None => match key with
              | key1 :: keyt => match SVM.find (belast key1 keyt) insts with
                                | Some vm => (* vm is the module type of key ... key is a component within this module *)
                                             match VM_mod.find vm tmaps with
                                             | Some tmap => match VM.find (last key1 keyt) tmap with
                                                            | Some (_, fc) => Some (belast key1 keyt, fc)
                                                            | None => None
                                                            end
                                             | None => None
                                             end
                                | None => None
                                end
              | [::] => None
              end
    end.

(* helper function for copy_ns_to_rs_helper:
   copy the fl-ed parts of newval to oldval
   (flipped parts are outputs or flipped inputs) *)
Fixpoint copy_flipped_parts_fields (oldval newval : bundle_value) (fl : fflip) : option bundle_value :=
    match oldval, newval with
    | Bnil, Bnil => Some bnil
    | Bflips vo fo valo oldval', Bflips vn fn valn newval' => if (vo == vn) && (fo == fn)
                                                              then match copy_flipped_parts valo valn (if fl == fo then Nflip else Flipped), copy_flipped_parts_fields oldval' newval' fl with
                                                                   | Some val, Some tail => Some (Bflips vo fo val tail)
                                                                   | _, _ => None
                                                                   end
                                                              else None
    | _, _ => None
    end
(* copy the fl-ed parts of newval to oldval *)
with copy_flipped_parts (oldval newval : hvalue) (fl : fflip) : option hvalue :=
    match oldval, newval with
    | Gval bo, Gval bn => Some (gval (if fl == Nflip then bn else bo))
    | Aval ao, Aval an => match copy_flipped_parts_array ao an fl with
                          | Some av => Some (Aval av)
                          | None => None
                          end
    | Bval bo, Bval bn => match copy_flipped_parts_fields bo bn fl with
                          | Some bv => Some (Bval bv)
                          | None => None
                          end
    | _, _ => None
    end
with copy_flipped_parts_array (oldval newval : array_value) (fl : fflip) : option array_value :=
    match oldval, newval with
    | Anil, Anil => Some anil
    | Acons vo oldval', Acons vn newval' => match copy_flipped_parts vo vn fl, copy_flipped_parts_array oldval' newval' fl with
                                            | Some v, Some val => Some (Acons v val)
                                            | _, _ => None
                                            end
    | _, _ => None
    end.

(* helper function for copy_ns_to_rs:
   copy the new value val of component key to rs, unless the component is a register. *)
Definition copy_ns_to_rs_helper (tmaps : VM_mod.t (VM.t (ftype * fcomponent))) (insts : SVM.t var_mod) (key : SVM.key) (val : hvalue) (opt_rs : option (SVM.t hvalue)) : option (SVM.t hvalue) :=
    match opt_rs, find_instance_and_type tmaps insts key with
    | Some rs, Some ([::], Fmodule) => (* top-level module: only copy flipped parts, i.e. outputs.
                                          Keep the original value of top-level/external inputs. *)
                                       match SVM.find [::] rs, val with
                                       | Some (Bval br), Bval bn => match copy_flipped_parts_fields br bn Flipped with
                                                                    | Some b => Some (SVM.add key (Bval b) rs)
                                                                    | None => None
                                                                    end
                                       | _, _ => None
                                       end
    | Some rs, Some (_, Register) => Some rs (* register values are not updated, but we always read the old value *)
    | Some rs, Some (_, In_port)
    | Some rs, Some (_, Out_port) => None (* this should not happen, as in- and out-ports are stored with the module they belong to *)
    | Some rs, Some (_, _) => (* other components:
                                 all values from ns should be copied to rs *)
                              Some (SVM.add key val rs)
    | _, _ => None
    end.

(* copy the new values of all components except registers in ns to rs *)
Definition copy_ns_to_rs (c : hfcircuit) (rs ns : SVM.t hvalue) : option (SVM.t hvalue) :=
    match circuit_tmaps c, find_circuit_instances c with
    | Some tmaps, Some insts => SVM.fold (copy_ns_to_rs_helper tmaps insts) ns (Some rs)
    | _, _ => None
    end.

(* iterate n times the evaluation of circuit c.
   old_rs and old_ns should be initialized to the old values of the circuit components
   (typically an "uninitialized" value, except for registers and external inputs). *)
Fixpoint iterate (n : nat) (c : hfcircuit) (old_rs old_ns : SVM.t hvalue) : option (SVM.t hvalue) :=
    match n with
    | 0 => Some old_ns
    | n'.+1 => match eval_circuit c old_rs with
               | Some ns => match copy_ns_to_rs c old_rs ns with
                            | Some rs => iterate n' c rs ns
                            | None => None
                            end
               | None => None
               end
    end.

(* Edited until here by David.
   The next steps would be to define a function that initializes rs for all components in all instances
   (using insts and tmaps in a similar way as in eval_circuit),
   and then to iterate over eval_circuit, together with a function like update_values below,
   that copies mutable values from ns back to rs. *)

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

Definition n := 10. (* TBD *)
Definition compute_Sem (c : hfcircuit) (inputs : VM.t hvalue) (reg_init : VM.t hvalue) : option (VM.t hvalue * VM.t hvalue) :=
  (* inputs signal and register should update during a rising edge and keep during the iteration *)
  (* compute the value connected to registers according to the stable state, return it as a new reg_init for the next clock cycle *)
  (* the return value is 1) the table state of all components, 2) the to-be-updated values of all registers *)
  match circuit_tmaps c, c with
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

End MakeSemantics.

(* HiFirrtl Semantics with variables of eqType *)
Module HiF_sem := MakeSemantics VarOrder VM.
