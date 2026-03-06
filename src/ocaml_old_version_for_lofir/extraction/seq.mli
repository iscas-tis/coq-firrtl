open Bool
open Eqtype
open Ssrbool
open Ssrnat

val ncons : int -> 'a1 -> 'a1 list -> 'a1 list

val nseq : int -> 'a1 -> 'a1 list

val cat : 'a1 list -> 'a1 list -> 'a1 list

val rcons : 'a1 list -> 'a1 -> 'a1 list

val take : int -> 'a1 list -> 'a1 list

val catrev : 'a1 list -> 'a1 list -> 'a1 list

val eqseq :
  Equality.coq_type -> Equality.sort list -> Equality.sort list -> bool

val eqseqP : Equality.coq_type -> Equality.sort list Equality.axiom

val seq_eqMixin : Equality.coq_type -> Equality.sort list Equality.mixin_of

type bitseq = bool list

val bitseq_eqType : Equality.coq_type

val foldr : ('a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 list -> 'a2
