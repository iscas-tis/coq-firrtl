open Bool
open Eqtype
open Ssrnat

type ucast =
| AsUInt
| AsSInt
| AsClock
| AsAsync

(** val ucast_eqn : ucast -> ucast -> bool **)

let ucast_eqn x y =
  match x with
  | AsUInt -> (match y with
               | AsUInt -> true
               | _ -> false)
  | AsSInt -> (match y with
               | AsSInt -> true
               | _ -> false)
  | AsClock -> (match y with
                | AsClock -> true
                | _ -> false)
  | AsAsync -> (match y with
                | AsAsync -> true
                | _ -> false)

(** val ucast_eqP : ucast Equality.axiom **)

let ucast_eqP x y =
  match x with
  | AsUInt -> (match y with
               | AsUInt -> ReflectT
               | _ -> ReflectF)
  | AsSInt -> (match y with
               | AsSInt -> ReflectT
               | _ -> ReflectF)
  | AsClock -> (match y with
                | AsClock -> ReflectT
                | _ -> ReflectF)
  | AsAsync -> (match y with
                | AsAsync -> ReflectT
                | _ -> ReflectF)

(** val ucast_eqMixin : ucast Equality.mixin_of **)

let ucast_eqMixin =
  { Equality.op = ucast_eqn; Equality.mixin_of__1 = ucast_eqP }

(** val ucast_eqType : Equality.coq_type **)

let ucast_eqType =
  Obj.magic ucast_eqMixin

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

(** val eunop_eqn : eunop -> eunop -> bool **)

let eunop_eqn x y =
  match x with
  | Upad n ->
    (match y with
     | Upad m -> eq_op nat_eqType (Obj.magic n) (Obj.magic m)
     | _ -> false)
  | Ushl n ->
    (match y with
     | Ushl m -> eq_op nat_eqType (Obj.magic n) (Obj.magic m)
     | _ -> false)
  | Ushr n ->
    (match y with
     | Ushr m -> eq_op nat_eqType (Obj.magic n) (Obj.magic m)
     | _ -> false)
  | Ucvt -> (match y with
             | Ucvt -> true
             | _ -> false)
  | Uneg -> (match y with
             | Uneg -> true
             | _ -> false)
  | Unot -> (match y with
             | Unot -> true
             | _ -> false)
  | Uandr -> (match y with
              | Uandr -> true
              | _ -> false)
  | Uorr -> (match y with
             | Uorr -> true
             | _ -> false)
  | Uxorr -> (match y with
              | Uxorr -> true
              | _ -> false)
  | Uextr (n, n0) ->
    (match y with
     | Uextr (m, m0) ->
       (&&) (eq_op nat_eqType (Obj.magic n) (Obj.magic m))
         (eq_op nat_eqType (Obj.magic n0) (Obj.magic m0))
     | _ -> false)
  | Uhead n ->
    (match y with
     | Uhead m -> eq_op nat_eqType (Obj.magic n) (Obj.magic m)
     | _ -> false)
  | Utail n ->
    (match y with
     | Utail m -> eq_op nat_eqType (Obj.magic n) (Obj.magic m)
     | _ -> false)

(** val eunop_eqP : eunop Equality.axiom **)

let eunop_eqP x y =
  match x with
  | Upad n ->
    (match y with
     | Upad n0 ->
       let b = eq_op nat_eqType (Obj.magic n) (Obj.magic n0) in
       if b then ReflectT else ReflectF
     | _ -> ReflectF)
  | Ushl n ->
    (match y with
     | Ushl n0 ->
       let b = eq_op nat_eqType (Obj.magic n) (Obj.magic n0) in
       if b then ReflectT else ReflectF
     | _ -> ReflectF)
  | Ushr n ->
    (match y with
     | Ushr n0 ->
       let b = eq_op nat_eqType (Obj.magic n) (Obj.magic n0) in
       if b then ReflectT else ReflectF
     | _ -> ReflectF)
  | Ucvt -> (match y with
             | Ucvt -> ReflectT
             | _ -> ReflectF)
  | Uneg -> (match y with
             | Uneg -> ReflectT
             | _ -> ReflectF)
  | Unot -> (match y with
             | Unot -> ReflectT
             | _ -> ReflectF)
  | Uandr -> (match y with
              | Uandr -> ReflectT
              | _ -> ReflectF)
  | Uorr -> (match y with
             | Uorr -> ReflectT
             | _ -> ReflectF)
  | Uxorr -> (match y with
              | Uxorr -> ReflectT
              | _ -> ReflectF)
  | Uextr (n, n0) ->
    (match y with
     | Uextr (n1, n2) ->
       let b = eq_op nat_eqType (Obj.magic n) (Obj.magic n1) in
       if b
       then let b0 = eq_op nat_eqType (Obj.magic n0) (Obj.magic n2) in
            if b0 then ReflectT else ReflectF
       else ReflectF
     | _ -> ReflectF)
  | Uhead n ->
    (match y with
     | Uhead n0 ->
       let b = eq_op nat_eqType (Obj.magic n) (Obj.magic n0) in
       if b then ReflectT else ReflectF
     | _ -> ReflectF)
  | Utail n ->
    (match y with
     | Utail n0 ->
       let b = eq_op nat_eqType (Obj.magic n) (Obj.magic n0) in
       if b then ReflectT else ReflectF
     | _ -> ReflectF)

(** val eunop_eqMixin : eunop Equality.mixin_of **)

let eunop_eqMixin =
  { Equality.op = eunop_eqn; Equality.mixin_of__1 = eunop_eqP }

(** val eunop_eqType : Equality.coq_type **)

let eunop_eqType =
  Obj.magic eunop_eqMixin

type bcmp =
| Blt
| Bleq
| Bgt
| Bgeq
| Beq
| Bneq

(** val bcmp_eqn : bcmp -> bcmp -> bool **)

let bcmp_eqn x y =
  match x with
  | Blt -> (match y with
            | Blt -> true
            | _ -> false)
  | Bleq -> (match y with
             | Bleq -> true
             | _ -> false)
  | Bgt -> (match y with
            | Bgt -> true
            | _ -> false)
  | Bgeq -> (match y with
             | Bgeq -> true
             | _ -> false)
  | Beq -> (match y with
            | Beq -> true
            | _ -> false)
  | Bneq -> (match y with
             | Bneq -> true
             | _ -> false)

(** val bcmp_eqP : bcmp Equality.axiom **)

let bcmp_eqP x y =
  match x with
  | Blt -> (match y with
            | Blt -> ReflectT
            | _ -> ReflectF)
  | Bleq -> (match y with
             | Bleq -> ReflectT
             | _ -> ReflectF)
  | Bgt -> (match y with
            | Bgt -> ReflectT
            | _ -> ReflectF)
  | Bgeq -> (match y with
             | Bgeq -> ReflectT
             | _ -> ReflectF)
  | Beq -> (match y with
            | Beq -> ReflectT
            | _ -> ReflectF)
  | Bneq -> (match y with
             | Bneq -> ReflectT
             | _ -> ReflectF)

(** val bcmp_eqMixin : bcmp Equality.mixin_of **)

let bcmp_eqMixin =
  { Equality.op = bcmp_eqn; Equality.mixin_of__1 = bcmp_eqP }

(** val bcmp_eqType : Equality.coq_type **)

let bcmp_eqType =
  Obj.magic bcmp_eqMixin

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

(** val ebinop_eqn : ebinop -> ebinop -> bool **)

let ebinop_eqn x y =
  match x with
  | Badd -> (match y with
             | Badd -> true
             | _ -> false)
  | Bsub -> (match y with
             | Bsub -> true
             | _ -> false)
  | Bmul -> (match y with
             | Bmul -> true
             | _ -> false)
  | Bdiv -> (match y with
             | Bdiv -> true
             | _ -> false)
  | Brem -> (match y with
             | Brem -> true
             | _ -> false)
  | Bcomp b ->
    (match y with
     | Bcomp c -> eq_op bcmp_eqType (Obj.magic b) (Obj.magic c)
     | _ -> false)
  | Bdshl -> (match y with
              | Bdshl -> true
              | _ -> false)
  | Bdshr -> (match y with
              | Bdshr -> true
              | _ -> false)
  | Band -> (match y with
             | Band -> true
             | _ -> false)
  | Bor -> (match y with
            | Bor -> true
            | _ -> false)
  | Bxor -> (match y with
             | Bxor -> true
             | _ -> false)
  | Bcat -> (match y with
             | Bcat -> true
             | _ -> false)

(** val ebinop_eqP : ebinop Equality.axiom **)

let ebinop_eqP x y =
  match x with
  | Badd -> (match y with
             | Badd -> ReflectT
             | _ -> ReflectF)
  | Bsub -> (match y with
             | Bsub -> ReflectT
             | _ -> ReflectF)
  | Bmul -> (match y with
             | Bmul -> ReflectT
             | _ -> ReflectF)
  | Bdiv -> (match y with
             | Bdiv -> ReflectT
             | _ -> ReflectF)
  | Brem -> (match y with
             | Brem -> ReflectT
             | _ -> ReflectF)
  | Bcomp b ->
    (match y with
     | Bcomp b0 ->
       let b1 = eq_op bcmp_eqType (Obj.magic b) (Obj.magic b0) in
       if b1 then ReflectT else ReflectF
     | _ -> ReflectF)
  | Bdshl -> (match y with
              | Bdshl -> ReflectT
              | _ -> ReflectF)
  | Bdshr -> (match y with
              | Bdshr -> ReflectT
              | _ -> ReflectF)
  | Band -> (match y with
             | Band -> ReflectT
             | _ -> ReflectF)
  | Bor -> (match y with
            | Bor -> ReflectT
            | _ -> ReflectF)
  | Bxor -> (match y with
             | Bxor -> ReflectT
             | _ -> ReflectF)
  | Bcat -> (match y with
             | Bcat -> ReflectT
             | _ -> ReflectF)

(** val ebinop_eqMixin : ebinop Equality.mixin_of **)

let ebinop_eqMixin =
  { Equality.op = ebinop_eqn; Equality.mixin_of__1 = ebinop_eqP }

(** val ebinop_eqType : Equality.coq_type **)

let ebinop_eqType =
  Obj.magic ebinop_eqMixin

type ruw =
| Coq_old
| Coq_new
| Coq_undefined
