open Bool
open Eqtype
open Ssrnat

type fgtyp =
| Fuint of int
| Fsint of int
| Fclock
| Freset
| Fasyncreset

val sizeof_fgtyp : fgtyp -> int

val fgtyp_eqn : fgtyp -> fgtyp -> bool

val fgtyp_eqP : fgtyp -> fgtyp -> reflect

val fgtyp_eqMixin : fgtyp Equality.mixin_of

val fgtyp_eqType : Equality.coq_type
