open Ascii
open BinInt
open String0
open Seq
open Ssrbool
open Ssrnat

type bits = bitseq

(** val b0 : bool **)

let b0 =
  false

(** val zeros : int -> bits **)

let zeros n =
  nseq n b0

(** val joinlsb : 'a1 -> 'a1 list -> 'a1 list **)

let joinlsb x x0 =
  x :: x0

(** val joinmsb : 'a1 list -> 'a1 -> 'a1 list **)

let joinmsb =
  rcons

(** val zext : int -> bits -> bits **)

let zext n bs =
  cat bs (zeros n)

(** val to_nat : bits -> int **)

let to_nat bs =
  foldr (fun b res -> addn (nat_of_bool b) (double res)) 0 bs

(** val from_nat : int -> int -> bits **)

let rec from_nat n x =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> [])
    (fun m -> joinlsb (odd x) (from_nat m (half x)))
    n

(** val from_Zpos : int -> int -> bits **)

let rec from_Zpos n x =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> [])
    (fun m -> joinlsb (Z.odd x) (from_Zpos m (Z.div2 x)))
    n

(** val from_Zneg : int -> int -> bits **)

let rec from_Zneg n x =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> [])
    (fun m -> joinlsb (Z.even x) (from_Zneg m (Z.div2 x)))
    n

(** val from_Z : int -> int -> bits **)

let from_Z n x =
  (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
    (fun _ -> zeros n)
    (fun _ -> from_Zpos n x)
    (fun _ -> from_Zneg n (Z.pred (Z.opp x)))
    x

(** val char_to_nibble : char -> bits **)

let char_to_nibble c =
  from_nat (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))
    (findex 0 (c::[])
      ('0'::('1'::('2'::('3'::('4'::('5'::('6'::('7'::('8'::('9'::('A'::('B'::('C'::('D'::('E'::('F'::('0'::('1'::('2'::('3'::('4'::('5'::('6'::('7'::('8'::('9'::('a'::('b'::('c'::('d'::('e'::('f'::[])))))))))))))))))))))))))))))))))

(** val char_to_bit : char -> bool **)

let char_to_bit c =
  is_left ((=) c '1')

(** val from_bin : char list -> bits **)

let rec from_bin = function
| [] -> []
| c::s0 -> joinmsb (from_bin s0) (char_to_bit c)

(** val from_hex : char list -> bits **)

let rec from_hex = function
| [] -> []
| c::s0 -> cat (from_hex s0) (char_to_nibble c)

(** val coq_Zpos_of_num_string_rec : int -> char list -> int **)

let rec coq_Zpos_of_num_string_rec res = function
| [] -> res
| c::s0 ->
  coq_Zpos_of_num_string_rec
    (Z.add (Z.mul res ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1))))
      (Z.of_nat (subn (nat_of_ascii c) (nat_of_ascii '0')))) s0

(** val coq_Zpos_of_num_string : char list -> int **)

let coq_Zpos_of_num_string s =
  coq_Zpos_of_num_string_rec 0 s

(** val from_string : char list -> bits **)

let from_string s =
  let n = coq_Zpos_of_num_string s in
  from_Z (addn (Z.to_nat (Z.log2 n)) (Stdlib.Int.succ 0)) n

(** val nibble_to_char : bits -> char **)

let nibble_to_char n =
  match get (to_nat n)
          ('0'::('1'::('2'::('3'::('4'::('5'::('6'::('7'::('8'::('9'::('A'::('B'::('C'::('D'::('E'::('F'::[])))))))))))))))) with
  | Some c -> c
  | None -> ' '

(** val append_nibble_on_string : bits -> char list -> char list **)

let append_nibble_on_string n s =
  append s ((nibble_to_char n)::[])

(** val to_hex : bits -> char list **)

let rec to_hex bs = match bs with
| [] -> []
| b1 :: l ->
  (match l with
   | [] ->
     append_nibble_on_string
       (cat bs
         (zeros (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))) []
   | b2 :: l0 ->
     (match l0 with
      | [] ->
        append_nibble_on_string
          (cat bs (zeros (Stdlib.Int.succ (Stdlib.Int.succ 0)))) []
      | b3 :: l1 ->
        (match l1 with
         | [] ->
           append_nibble_on_string (cat bs (zeros (Stdlib.Int.succ 0))) []
         | b4 :: tl ->
           append_nibble_on_string (b1 :: (b2 :: (b3 :: (b4 :: []))))
             (to_hex tl))))

(** val to_bin : bits -> char list **)

let rec to_bin = function
| [] -> []
| b :: bs0 -> append (to_bin bs0) (if b then '1'::[] else '0'::[])
