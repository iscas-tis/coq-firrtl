open Eqtype

let __ = let rec f _ = Obj.repr f in Obj.repr f

module type SsrOrderMinimal =
 sig
  val t : Equality.coq_type

  val eqn : Equality.sort -> Equality.sort -> bool

  val ltn : Equality.sort -> Equality.sort -> bool

  val compare :
    Equality.sort -> Equality.sort -> Equality.sort OrderedType.coq_Compare
 end

module type SsrOrder =
 sig
  val coq_T : Equality.coq_type

  type t = Equality.sort

  val ltn : t -> t -> bool

  val compare : t -> t -> t OrderedType.coq_Compare

  val eq_dec : t -> t -> bool
 end

module MakeSsrOrder =
 functor (M:SsrOrderMinimal) ->
 struct
  (** val coq_T : Equality.coq_type **)

  let coq_T =
    M.t

  type t = Equality.sort

  (** val ltn : t -> t -> bool **)

  let ltn =
    M.ltn

  (** val compare : t -> t -> t OrderedType.coq_Compare **)

  let compare =
    M.compare

  (** val eq_dec : t -> t -> bool **)

  let eq_dec x y =
    let _evar_0_ = fun _ -> true in
    let _evar_0_0 = fun _ -> false in
    if eq_op coq_T x y then _evar_0_ __ else _evar_0_0 __
 end

module type SsrOrderWithDefaultSucc =
 sig
  val coq_T : Equality.coq_type

  type t = Equality.sort

  val ltn : t -> t -> bool

  val compare : t -> t -> t OrderedType.coq_Compare

  val eq_dec : t -> t -> bool

  val default : Equality.sort

  val succ : t -> t
 end
