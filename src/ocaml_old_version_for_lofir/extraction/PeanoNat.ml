
module Nat =
 struct
  (** val pred : int -> int **)

  let pred n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> n)
      (fun u -> u)
      n

  (** val add : int -> int -> int **)

  let rec add n m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> m)
      (fun p -> Stdlib.Int.succ (add p m))
      n

  (** val mul : int -> int -> int **)

  let rec mul n m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> 0)
      (fun p -> add m (mul p m))
      n

  (** val pow : int -> int -> int **)

  let rec pow n m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> Stdlib.Int.succ 0)
      (fun m0 -> mul n (pow n m0))
      m

  (** val log2_iter : int -> int -> int -> int -> int **)

  let rec log2_iter k p q r =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> p)
      (fun k' ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ ->
        log2_iter k' (Stdlib.Int.succ p) (Stdlib.Int.succ q) q)
        (fun r' -> log2_iter k' p (Stdlib.Int.succ q) r')
        r)
      k

  (** val log2 : int -> int **)

  let log2 n =
    log2_iter (pred n) 0 (Stdlib.Int.succ 0) 0
 end
