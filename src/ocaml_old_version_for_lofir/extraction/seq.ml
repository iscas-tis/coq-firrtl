open Bool
open Eqtype
open Ssrbool
open Ssrnat

let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val ncons : int -> 'a1 -> 'a1 list -> 'a1 list **)

let ncons n x =
  iter n (fun x0 -> x :: x0)

(** val nseq : int -> 'a1 -> 'a1 list **)

let nseq n x =
  ncons n x []

(** val cat : 'a1 list -> 'a1 list -> 'a1 list **)

let rec cat s1 s2 =
  match s1 with
  | [] -> s2
  | x :: s1' -> x :: (cat s1' s2)

(** val rcons : 'a1 list -> 'a1 -> 'a1 list **)

let rec rcons s z =
  match s with
  | [] -> z :: []
  | x :: s' -> x :: (rcons s' z)

(** val take : int -> 'a1 list -> 'a1 list **)

let rec take n = function
| [] -> []
| x :: s' ->
  ((fun fO fS n -> if n=0 then fO () else fS (n-1))
     (fun _ -> [])
     (fun n' -> x :: (take n' s'))
     n)

(** val catrev : 'a1 list -> 'a1 list -> 'a1 list **)

let rec catrev s1 s2 =
  match s1 with
  | [] -> s2
  | x :: s1' -> catrev s1' (x :: s2)

(** val eqseq :
    Equality.coq_type -> Equality.sort list -> Equality.sort list -> bool **)

let rec eqseq t s1 s2 =
  match s1 with
  | [] -> (match s2 with
           | [] -> true
           | _ :: _ -> false)
  | x1 :: s1' ->
    (match s2 with
     | [] -> false
     | x2 :: s2' -> (&&) (eq_op t x1 x2) (eqseq t s1' s2'))

(** val eqseqP : Equality.coq_type -> Equality.sort list Equality.axiom **)

let eqseqP t _top_assumption_ =
  let _evar_0_ = fun __top_assumption_ ->
    let _evar_0_ = ReflectT in
    let _evar_0_0 = fun _ _ -> ReflectF in
    (match __top_assumption_ with
     | [] -> _evar_0_
     | a :: l -> _evar_0_0 a l)
  in
  let _evar_0_0 = fun x1 s1 iHs __top_assumption_ ->
    let _evar_0_0 = ReflectF in
    let _evar_0_1 = fun x2 s2 ->
      let __top_assumption_0 = eqP t x1 x2 in
      let _evar_0_1 = fun _ -> iffP (eqseq t s1 s2) (iHs s2) in
      let _evar_0_2 = fun _ -> ReflectF in
      (match __top_assumption_0 with
       | ReflectT -> _evar_0_1 __
       | ReflectF -> _evar_0_2 __)
    in
    (match __top_assumption_ with
     | [] -> _evar_0_0
     | a :: l -> _evar_0_1 a l)
  in
  let rec f = function
  | [] -> _evar_0_
  | y :: l0 -> _evar_0_0 y l0 (f l0)
  in f _top_assumption_

(** val seq_eqMixin :
    Equality.coq_type -> Equality.sort list Equality.mixin_of **)

let seq_eqMixin t =
  { Equality.op = (eqseq t); Equality.mixin_of__1 = (eqseqP t) }

type bitseq = bool list

(** val bitseq_eqType : Equality.coq_type **)

let bitseq_eqType =
  Obj.magic seq_eqMixin bool_eqType

(** val foldr : ('a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 list -> 'a2 **)

let rec foldr f z0 = function
| [] -> z0
| x :: s' -> f x (foldr f z0 s')
