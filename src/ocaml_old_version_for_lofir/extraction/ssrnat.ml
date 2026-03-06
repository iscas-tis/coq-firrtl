open BinNat
open Datatypes
open Nat0
open Eqtype
open Ssrbool

(** val eqn : int -> int -> bool **)

let rec eqn m n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> true)
      (fun _ -> false)
      n)
    (fun m' ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> false)
      (fun n' -> eqn m' n')
      n)
    m

(** val eqnP : int Equality.axiom **)

let eqnP n m =
  iffP (eqn n m) (idP (eqn n m))

(** val nat_eqMixin : int Equality.mixin_of **)

let nat_eqMixin =
  { Equality.op = eqn; Equality.mixin_of__1 = eqnP }

(** val nat_eqType : Equality.coq_type **)

let nat_eqType =
  Obj.magic nat_eqMixin

(** val addn_rec : int -> int -> int **)

let addn_rec =
  add

(** val addn : int -> int -> int **)

let addn =
  addn_rec

(** val subn_rec : int -> int -> int **)

let subn_rec =
  sub

(** val subn : int -> int -> int **)

let subn =
  subn_rec

(** val leq : int -> int -> bool **)

let leq m n =
  eq_op nat_eqType (Obj.magic subn m n) (Obj.magic 0)

(** val maxn : int -> int -> int **)

let maxn m n =
  if leq (Stdlib.Int.succ m) n then n else m

(** val minn : int -> int -> int **)

let minn m n =
  if leq (Stdlib.Int.succ m) n then m else n

(** val iter : int -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)

let rec iter n f x =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> x)
    (fun i -> f (iter i f x))
    n

(** val iteri : int -> (int -> 'a1 -> 'a1) -> 'a1 -> 'a1 **)

let rec iteri n f x =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> x)
    (fun i -> f i (iteri i f x))
    n

(** val iterop : int -> ('a1 -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 **)

let iterop n op0 x =
  let f = fun i y ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> x)
      (fun _ -> op0 x y)
      i
  in
  iteri n f

(** val muln_rec : int -> int -> int **)

let muln_rec =
  mul

(** val muln : int -> int -> int **)

let muln =
  muln_rec

(** val expn_rec : int -> int -> int **)

let expn_rec m n =
  iterop n muln m (Stdlib.Int.succ 0)

(** val expn : int -> int -> int **)

let expn =
  expn_rec

(** val nat_of_bool : bool -> int **)

let nat_of_bool = function
| true -> Stdlib.Int.succ 0
| false -> 0

(** val odd : int -> bool **)

let rec odd n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> false)
    (fun n' -> negb (odd n'))
    n

(** val double_rec : int -> int **)

let rec double_rec n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> 0)
    (fun n' -> Stdlib.Int.succ (Stdlib.Int.succ (double_rec n')))
    n

(** val double : int -> int **)

let double =
  double_rec

(** val half : int -> int **)

let rec half n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> n)
    (fun n' -> uphalf n')
    n

(** val uphalf : int -> int **)

and uphalf n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> n)
    (fun n' -> Stdlib.Int.succ (half n'))
    n

(** val eq_binP : int Equality.axiom **)

let eq_binP p q =
  iffP (N.eqb p q) (idP (N.eqb p q))

(** val bin_nat_eqMixin : int Equality.mixin_of **)

let bin_nat_eqMixin =
  { Equality.op = N.eqb; Equality.mixin_of__1 = eq_binP }

(** val bin_nat_eqType : Equality.coq_type **)

let bin_nat_eqType =
  Obj.magic bin_nat_eqMixin
