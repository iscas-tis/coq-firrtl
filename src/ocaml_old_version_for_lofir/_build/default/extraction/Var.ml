open BinNat
open ZAriths
open Eqtype

type var = int

module VarOrder =
 struct
  (** val coq_T : Equality.coq_type **)

  let coq_T =
    NOrderMinimal.t

  type t = Equality.sort

  (** val ltn : t -> t -> bool **)

  let ltn =
    NOrderMinimal.ltn

  (** val compare : t -> t -> t OrderedType.coq_Compare **)

  let compare =
    NOrderMinimal.compare

  (** val eq_dec : t -> t -> bool **)

  let eq_dec =
    NOrder.eq_dec

  (** val succ : t -> t **)

  let succ =
    Obj.magic N.succ

  (** val default : t **)

  let default =
    Obj.magic 0
 end
