open Datatypes
open NBitsDef
open Eqtype
open Seq
open Ssrnat

(** val extzip : 'a1 -> 'a2 -> 'a1 list -> 'a2 list -> ('a1 * 'a2) list **)

let rec extzip sd td ss ts =
  match ss with
  | [] ->
    (match ts with
     | [] -> zip ss (nseq (size ss) td)
     | _ :: _ -> zip (nseq (size ts) sd) ts)
  | s :: ss0 ->
    (match ts with
     | [] -> zip ss (nseq (size ss) td)
     | t :: ts0 -> (s, t) :: (extzip sd td ss0 ts0))

(** val lift :
    'a1 -> ('a1 -> 'a1 -> 'a1) -> 'a1 list -> 'a1 list -> 'a1 list **)

let lift d op ss ts =
  map (fun e -> op (fst e) (snd e)) (extzip d d ss ts)

(** val lift0 :
    (bool -> bool -> bool) -> bool list -> bool list -> bool list **)

let lift0 =
  lift b0

(** val extzip0 : bool list -> bool list -> (bool * bool) list **)

let extzip0 =
  extzip b0 b0

(** val succB : bits -> bits **)

let rec succB = function
| [] -> []
| hd :: tl -> if hd then b0 :: (succB tl) else b1 :: tl

(** val andB : bits -> bits -> bits **)

let andB bs1 bs2 =
  lift0 (&&) bs1 bs2

(** val orB : bits -> bits -> bits **)

let orB bs1 bs2 =
  lift0 (||) bs1 bs2

(** val xorB : bits -> bits -> bits **)

let xorB bs1 bs2 =
  lift0 xorb bs1 bs2

(** val negB : bits -> bits **)

let negB bs =
  succB (invB bs)

(** val bool_adder : bool -> bool -> bool -> bool * bool **)

let bool_adder c b2 b3 =
  if c
  then if b2
       then if b3 then (true, true) else (true, false)
       else if b3 then (true, false) else (false, true)
  else if b2
       then if b3 then (true, false) else (false, true)
       else if b3 then (false, true) else (false, false)

(** val full_adder_zip : bool -> (bool * bool) list -> bool * bits **)

let rec full_adder_zip c = function
| [] -> (c, [])
| p :: tl ->
  let (hd1, hd2) = p in
  let (c0, hd) = bool_adder c hd1 hd2 in
  let (c1, tl0) = full_adder_zip c0 tl in (c1, (hd :: tl0))

(** val full_adder : bool -> bits -> bits -> bool * bits **)

let full_adder c bs1 bs2 =
  full_adder_zip c (zip bs1 bs2)

(** val adcB : bool -> bits -> bits -> bool * bits **)

let adcB =
  full_adder

(** val addB : bits -> bits -> bits **)

let addB bs1 bs2 =
  snd (adcB false bs1 bs2)

(** val sbbB : bool -> bits -> bits -> bool * bits **)

let sbbB b bs1 bs2 =
  let (c, res) = adcB (negb b) bs1 (invB bs2) in ((negb c), res)

(** val subB : bits -> bits -> bits **)

let subB bs1 bs2 =
  snd (sbbB false bs1 bs2)

(** val full_mul : bits -> bits -> bits **)

let rec full_mul bs1 bs2 =
  match bs1 with
  | [] -> from_nat (addn (size bs1) (size bs2)) 0
  | hd :: tl ->
    if hd
    then addB (joinlsb false (full_mul tl bs2)) (zext (size bs1) bs2)
    else joinlsb false (full_mul tl bs2)

(** val ltB_lsb_zip : (bool * bool) list -> bool **)

let rec ltB_lsb_zip = function
| [] -> false
| p :: tl ->
  let (hd1, hd2) = p in
  (||)
    ((&&)
      ((&&)
        (eq_op (seq_eqType bool_eqType) (Obj.magic unzip1 tl)
          (Obj.magic unzip2 tl)) (negb hd1)) hd2) (ltB_lsb_zip tl)

(** val ltB_lsb : bits -> bits -> bool **)

let ltB_lsb bs1 bs2 =
  ltB_lsb_zip (extzip0 bs1 bs2)

(** val leB : bits -> bits -> bool **)

let leB bs1 bs2 =
  (||) (eq_op bitseq_eqType (Obj.magic bs1) (Obj.magic bs2)) (ltB_lsb bs1 bs2)

(** val gtB : bits -> bits -> bool **)

let gtB bs1 bs2 =
  ltB_lsb bs2 bs1

(** val geB : bits -> bits -> bool **)

let geB bs1 bs2 =
  leB bs2 bs1

(** val sltB : bits -> bits -> bool **)

let sltB bs1 bs2 =
  let tbs1 = fst (splitmsb bs1) in
  let sign1 = snd (splitmsb bs1) in
  let tbs2 = fst (splitmsb bs2) in
  let sign2 = snd (splitmsb bs2) in
  let ult_tl = ltB_lsb tbs1 tbs2 in
  (||) ((&&) (eq_op bool_eqType (Obj.magic sign1) (Obj.magic sign2)) ult_tl)
    ((&&) sign1 (negb sign2))

(** val sleB : bits -> bits -> bool **)

let sleB bs1 bs2 =
  (||) (eq_op bitseq_eqType (Obj.magic bs1) (Obj.magic bs2)) (sltB bs1 bs2)

(** val sgtB : bits -> bits -> bool **)

let sgtB bs1 bs2 =
  sltB bs2 bs1

(** val sgeB : bits -> bits -> bool **)

let sgeB bs1 bs2 =
  sleB bs2 bs1

(** val shrB1 : bits -> bits **)

let shrB1 bs =
  droplsb (joinmsb bs b0)

(** val shrB : int -> bits -> bits **)

let shrB n bs =
  iter n shrB1 bs

(** val sarB1 : bits -> bits **)

let sarB1 bs =
  droplsb (joinmsb bs (msb bs))

(** val sarB : int -> bits -> bits **)

let sarB n bs =
  iter n sarB1 bs

(** val ucastB : bits -> int -> bits **)

let ucastB bs n =
  if eq_op nat_eqType (Obj.magic n) (Obj.magic size bs)
  then bs
  else if leq (Pervasives.succ n) (size bs)
       then low n bs
       else zext (subn n (size bs)) bs

(** val scastB : bits -> int -> bits **)

let scastB bs n =
  if eq_op nat_eqType (Obj.magic n) (Obj.magic size bs)
  then bs
  else if leq (Pervasives.succ n) (size bs)
       then low n bs
       else sext (subn n (size bs)) bs

(** val udivB_rec : bits -> bits -> bits -> bits -> bits * bits **)

let rec udivB_rec n m q r =
  match n with
  | [] -> (q, r)
  | nhd :: ntl ->
    let di = dropmsb (joinlsb nhd r) in
    let bi = leB m di in
    let ri = if bi then subB di m else di in
    let qi = dropmsb (joinlsb bi q) in udivB_rec ntl m qi ri

(** val udivB : bits -> bits -> bits * bits **)

let udivB n' m =
  let n = rev n' in
  if eq_op bitseq_eqType (Obj.magic from_Zpos (size n) (to_Zpos m))
       (Obj.magic zeros (size n))
  then ((ones (size n)), n')
  else udivB_rec n (from_Zpos (size n) (to_Zpos m)) (zeros (size n))
         (zeros (size n))

(** val udivB' : bits -> bits -> bits **)

let udivB' n m =
  fst (udivB n m)

(** val uremB : bits -> bits -> bits **)

let uremB bs1 bs2 =
  snd (udivB bs1 bs2)

(** val absB : bits -> bits **)

let absB bs =
  if msb bs then negB bs else bs

(** val sdivB : bits -> bits -> bits **)

let sdivB bs1' bs2' =
  let bs1 = absB bs1' in
  let bs2 = absB bs2' in
  if eq_op bool_eqType (Obj.magic msb bs1') (Obj.magic msb bs2')
  then fst (udivB bs1 bs2)
  else negB (fst (udivB bs1 bs2))

(** val sremB : bits -> bits -> bits **)

let sremB bs1' bs2' =
  let bs1 = absB bs1' in
  let bs2 = absB bs2' in
  if msb bs1' then negB (snd (udivB bs1 bs2)) else snd (udivB bs1 bs2)
