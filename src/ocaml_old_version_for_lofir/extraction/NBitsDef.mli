open Ascii
open BinInt
open String0
open Seq
open Ssrbool
open Ssrnat

type bits = bitseq

val b0 : bool

val zeros : int -> bits

val joinlsb : 'a1 -> 'a1 list -> 'a1 list

val joinmsb : 'a1 list -> 'a1 -> 'a1 list

val zext : int -> bits -> bits

val to_nat : bits -> int

val from_nat : int -> int -> bits

val from_Zpos : int -> int -> bits

val from_Zneg : int -> int -> bits

val from_Z : int -> int -> bits

val char_to_nibble : char -> bits

val char_to_bit : char -> bool

val from_bin : char list -> bits

val from_hex : char list -> bits

val coq_Zpos_of_num_string_rec : int -> char list -> int

val coq_Zpos_of_num_string : char list -> int

val from_string : char list -> bits

val nibble_to_char : bits -> char

val append_nibble_on_string : bits -> char list -> char list

val to_hex : bits -> char list

val to_bin : bits -> char list
