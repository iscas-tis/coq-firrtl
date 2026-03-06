open BinNat
open ZAriths
open Eqtype

type var = int

module VarOrder :
 sig
  val coq_T : Equality.coq_type

  type t = Equality.sort

  val ltn : t -> t -> bool

  val compare : t -> t -> t OrderedType.coq_Compare

  val eq_dec : t -> t -> bool

  val succ : t -> t

  val default : t
 end
