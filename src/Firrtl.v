From Coq Require Import ZArith Arith RelationClasses OrderedType.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.

(****** Types ******)

(****** Ground Types ******)

Inductive fgtyp : Set :=
  Fuint : nat -> fgtyp
| Fsint : nat -> fgtyp
| Fanalog : nat -> fgtyp
| Fclock
| Ffixed : nat -> Z -> fgtyp
| Fvector : fgtyp -> fgtyp -> fgtyp.


(* Integer, bitvector or ssrint, TBD *)
Definition fbits := Type.

Inductive fint : Type :=
| UInt : fbits -> fint
| SInt : fbits -> fint.

(* Fix-point, TBD *)

(* Analog, TBD *)

(* Vector, TBD *)

(*
(****** Type Equivalence ******)

(* TBD *)
Parameter fint_to_Z : fbits -> Z.

(* Integer type eq *)

Definition fint_eq fi1 fi2 :=
  match fi1, fi2 with
  | UInt bs1, UInt bs2 => Zeq_bool (fint_to_Z bs1) (fint_to_Z bs2)
  | SInt bs1, SInt bs2 => Zeq_bool (fint_to_Z bs1) (fint_to_Z bs2)
  | UInt _, SInt _ => false
  | SInt _, UInt _ => false
  end.
*)
                        
(****** Syntax ******)

(****** Expressions ******)

(* Import ssrlib, TBD *)
Variable var : eqType.

Inductive ucast : Set :=
| AsUInt | AsSInt | AsFixed | AsClock.

Inductive eunop : Set :=
| Upadding : nat -> eunop
| Ucast : ucast -> eunop
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
| Utail : nat -> eunop
| Uincp
| Udecp
| Usetp .

Inductive bcmp : Set :=
| Blt | Bleq | Bgt | Bgeq | eq | neq.

Inductive ebinop : Set :=
| Badd
| Bsub
| Bmul
| Bdiv
| Brem
| Bcomp: bcmp -> ebinop
| Bdshl
| Bdshr
| Band
| Bor
| Bxor
| Bcat .

(* mux, valid, sub-xxx, TBD *)
Inductive fexpr : Type :=
| Econst : fint -> fexpr
| Eref : var -> fgtyp -> fexpr
| Efield : var -> fexpr -> fexpr
| Esubacc : var -> nat -> fexpr
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
      data_type : fexpr;
      depth : nat;
      reader : seq var;
      writer : seq var;                    
      read_latency : nat;
      write_latency : nat;
      read_under_write : ruw
    }.

Record freg : Type :=
  mk_freg
    {
      rid : var;
      type : fexpr;
      reset : seq fexpr
    }.

Inductive fstmt : Type :=
| Sskip
| Swire : var -> fgtyp -> fstmt
| Sreg : freg -> fstmt
| Smem : fmem -> fstmt
| Sinst : var -> var -> fstmt
| Snode : var -> fexpr -> fstmt
| Sfcnct : fexpr -> fexpr -> fstmt
| Spcnct : fexpr -> fexpr -> fstmt
| Sinvalid : var -> fstmt
| Sattach : seq var -> fstmt
| Swhen : fexpr -> fstmt -> fstmt -> fstmt
| Sstop : fexpr -> fexpr -> nat -> fstmt
| Sprintf (* TBD *)
| Sassert (* TBD *)
| Sassume (* TBD *)
| Sdefname : var -> fstmt (* TBD *)
| Sparam : var -> fexpr -> fstmt (* TBD *)
.

Inductive fport : Type :=
| Finput : fexpr -> fport
| Foutput : fexpr -> fport
.

(* TBD *)
Inductive fmodule : Type :=
| FInmod : var -> seq fport -> seq fstmt -> fmodule
| FExmod : var -> seq fport -> seq fstmt -> fmodule
.

Definition fcircuit := var -> seq fmodule.



(****** Semantics ******)


Record fstate : Type :=
  mk_state
    {
      fregs : seq freg;
      fmems : seq fmem
    }.

(* TBD *)
Parameter eval_fexpr : fstate -> fexpr -> fstate.

(* TBD *)
Parameter eval_fstmt : fstate -> fstmt -> fstate.
