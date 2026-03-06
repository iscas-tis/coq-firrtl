open Datatypes
open NBitsDef
open Eqtype
open Seq
open Ssrnat

val extzip : 'a1 -> 'a2 -> 'a1 list -> 'a2 list -> ('a1 * 'a2) list

val lift : 'a1 -> ('a1 -> 'a1 -> 'a1) -> 'a1 list -> 'a1 list -> 'a1 list

val lift0 : (bool -> bool -> bool) -> bool list -> bool list -> bool list

val extzip0 : bool list -> bool list -> (bool * bool) list

val succB : bits -> bits

val andB : bits -> bits -> bits

val orB : bits -> bits -> bits

val xorB : bits -> bits -> bits

val negB : bits -> bits

val bool_adder : bool -> bool -> bool -> bool * bool

val full_adder_zip : bool -> (bool * bool) list -> bool * bits

val full_adder : bool -> bits -> bits -> bool * bits

val adcB : bool -> bits -> bits -> bool * bits

val addB : bits -> bits -> bits

val sbbB : bool -> bits -> bits -> bool * bits

val subB : bits -> bits -> bits

val full_mul : bits -> bits -> bits

val ltB_lsb_zip : (bool * bool) list -> bool

val ltB_lsb : bits -> bits -> bool

val leB : bits -> bits -> bool

val gtB : bits -> bits -> bool

val geB : bits -> bits -> bool

val sltB : bits -> bits -> bool

val sleB : bits -> bits -> bool

val sgtB : bits -> bits -> bool

val sgeB : bits -> bits -> bool

val shrB1 : bits -> bits

val shrB : int -> bits -> bits

val sarB1 : bits -> bits

val sarB : int -> bits -> bits

val ucastB : bits -> int -> bits

val scastB : bits -> int -> bits

val udivB_rec : bits -> bits -> bits -> bits -> bits * bits

val udivB : bits -> bits -> bits * bits

val udivB' : bits -> bits -> bits

val uremB : bits -> bits -> bits

val absB : bits -> bits

val sdivB : bits -> bits -> bits

val sremB : bits -> bits -> bits
