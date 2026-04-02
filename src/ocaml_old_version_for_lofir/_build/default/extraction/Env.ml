open Bool
open Eqtype
open Ssrnat

let __ = let rec f _ = Obj.repr f in Obj.repr f

type fgtyp =
| Fuint of int
| Fsint of int
| Fclock
| Freset
| Fasyncreset

(** val sizeof_fgtyp : fgtyp -> int **)

let sizeof_fgtyp = function
| Fuint w -> w
| Fsint w -> w
| _ -> Stdlib.Int.succ 0

(** val fgtyp_eqn : fgtyp -> fgtyp -> bool **)

let fgtyp_eqn x y =
  match x with
  | Fuint wx ->
    (match y with
     | Fuint wy -> eq_op nat_eqType (Obj.magic wx) (Obj.magic wy)
     | _ -> false)
  | Fsint wx ->
    (match y with
     | Fsint wy -> eq_op nat_eqType (Obj.magic wx) (Obj.magic wy)
     | _ -> false)
  | Fclock -> (match y with
               | Fclock -> true
               | _ -> false)
  | Freset -> (match y with
               | Freset -> true
               | _ -> false)
  | Fasyncreset -> (match y with
                    | Fasyncreset -> true
                    | _ -> false)

(** val fgtyp_eqP : fgtyp -> fgtyp -> reflect **)

let fgtyp_eqP x y =
  let _evar_0_ = fun _ -> ReflectT in
  let _evar_0_0 = fun _ -> ReflectF in
  if fgtyp_eqn x y then _evar_0_ __ else _evar_0_0 __

(** val fgtyp_eqMixin : fgtyp Equality.mixin_of **)

let fgtyp_eqMixin =
  { Equality.op = fgtyp_eqn; Equality.mixin_of__1 = fgtyp_eqP }

(** val fgtyp_eqType : Equality.coq_type **)

let fgtyp_eqType =
  Obj.magic fgtyp_eqMixin
