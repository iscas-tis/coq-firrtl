open Bool
open Eqtype
open Ssrnat

type ucast =
| AsUInt
| AsSInt
| AsClock
| AsAsync

val ucast_eqn : ucast -> ucast -> bool

val ucast_eqP : ucast Equality.axiom

val ucast_eqMixin : ucast Equality.mixin_of

val ucast_eqType : Equality.coq_type

type eunop =
| Upad of int
| Ushl of int
| Ushr of int
| Ucvt
| Uneg
| Unot
| Uandr
| Uorr
| Uxorr
| Uextr of int * int
| Uhead of int
| Utail of int

val eunop_eqn : eunop -> eunop -> bool

val eunop_eqP : eunop Equality.axiom

val eunop_eqMixin : eunop Equality.mixin_of

val eunop_eqType : Equality.coq_type

type bcmp =
| Blt
| Bleq
| Bgt
| Bgeq
| Beq
| Bneq

val bcmp_eqn : bcmp -> bcmp -> bool

val bcmp_eqP : bcmp Equality.axiom

val bcmp_eqMixin : bcmp Equality.mixin_of

val bcmp_eqType : Equality.coq_type

type ebinop =
| Badd
| Bsub
| Bmul
| Bdiv
| Brem
| Bcomp of bcmp
| Bdshl
| Bdshr
| Band
| Bor
| Bxor
| Bcat

val ebinop_eqn : ebinop -> ebinop -> bool

val ebinop_eqP : ebinop Equality.axiom

val ebinop_eqMixin : ebinop Equality.mixin_of

val ebinop_eqType : Equality.coq_type

type ruw =
| Coq_old
| Coq_new
| Coq_undefined
