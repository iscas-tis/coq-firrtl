open BinInt
open Bool
open Datatypes
open Env
open FSets
open List0
open NBitsDef
open NBitsOp
open PeanoNat
open Var
open Eqtype
open Seq
open Ssrbool
open Ssrnat

type __ = Obj.t

type ucast =
| AsUInt
| AsSInt
| AsClock
| AsReset
| AsAsync

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

type bcmp =
| Blt
| Bleq
| Bgt
| Bgeq
| Beq
| Bneq

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

module Coq__1 : sig
 type fexpr =
 | Econst of fgtyp * bits
 | Ecast of ucast * fexpr
 | Eprim_unop of eunop * fexpr
 | Eprim_binop of ebinop * fexpr * fexpr
 | Emux of fexpr * fexpr * fexpr
 | Evalidif of fexpr * fexpr
 | Eref of Equality.sort
end
include module type of struct include Coq__1 end

type ruw =
| Coq_old
| Coq_new
| Coq_undefined

module Coq__6 : sig
 type freader_port = { addr : Equality.sort; data : Equality.sort;
                       en : Equality.sort; clk : Equality.sort }
end
include module type of struct include Coq__6 end

module Coq__5 : sig
 type fwriter_port = { addr0 : Equality.sort; data0 : Equality.sort;
                       en0 : Equality.sort; clk0 : Equality.sort;
                       mask : Equality.sort }
end
include module type of struct include Coq__5 end

module Coq__4 : sig
 type fmem = { mid : Equality.sort; data_type : fgtyp; depth : int;
               reader : freader_port list; writer : fwriter_port list;
               read_latency : int; write_latency : int; read_write : 
               ruw }
end
include module type of struct include Coq__4 end

type rst =
| NRst
| Rst of fexpr * fexpr

module Coq__3 : sig
 type freg = { rid : Equality.sort; coq_type : fgtyp; clock : Equality.sort;
               reset : rst }
end
include module type of struct include Coq__3 end

module Coq__7 : sig
 type fport =
 | Finput of Equality.sort * fgtyp
 | Foutput of Equality.sort * fgtyp
end
include module type of struct include Coq__7 end

type finst = { iid : Equality.sort; imid : Equality.sort; iports : fport list }

module Coq__2 : sig
 type fstmt =
 | Sskip
 | Swire of Equality.sort * fgtyp
 | Sreg of freg
 | Smem of fmem
 | Sinst of finst
 | Snode of Equality.sort * fexpr
 | Sfcnct of Equality.sort * fexpr
 | Sinvalid of Equality.sort
 | Swhen of fexpr * fstmt * fstmt
 | Sstop of fexpr * fexpr * int
end
include module type of struct include Coq__2 end

module Coq__8 : sig
 type fmodule =
 | FInmod of Equality.sort * fport list * fstmt list
 | FExmod of Equality.sort * fport list * fstmt list
end
include module type of struct include Coq__8 end

module Coq__9 : sig
 type fcircuit =
 | Fcircuit of Equality.sort * fmodule list
end
include module type of struct include Coq__9 end

module MakeFirrtl :
 functor (V:SsrOrder.SsrOrder) ->
 functor (TE:TypEnv with module SE = V) ->
 functor (SV:sig
  module Lemmas :
   sig
    module F :
     sig
      val eqb : TE.SE.t -> TE.SE.t -> bool

      val coq_In_dec : 'a1 TE.t -> TE.key -> bool
     end

    module OP :
     sig
      module ME :
       sig
        module TO :
         sig
          type t = TE.SE.t
         end

        module IsTO :
         sig
         end

        module OrderTac :
         sig
         end

        val eq_dec : TE.SE.t -> TE.SE.t -> bool

        val lt_dec : TE.SE.t -> TE.SE.t -> bool

        val eqb : TE.SE.t -> TE.SE.t -> bool
       end

      module O :
       sig
        module MO :
         sig
          module TO :
           sig
            type t = TE.SE.t
           end

          module IsTO :
           sig
           end

          module OrderTac :
           sig
           end

          val eq_dec : TE.SE.t -> TE.SE.t -> bool

          val lt_dec : TE.SE.t -> TE.SE.t -> bool

          val eqb : TE.SE.t -> TE.SE.t -> bool
         end
       end

      module P :
       sig
        module F :
         sig
          val eqb : TE.SE.t -> TE.SE.t -> bool

          val coq_In_dec : 'a1 TE.t -> TE.key -> bool
         end

        val uncurry : ('a1 -> 'a2 -> 'a3) -> ('a1 * 'a2) -> 'a3

        val of_list : (TE.key * 'a1) list -> 'a1 TE.t

        val to_list : 'a1 TE.t -> (TE.key * 'a1) list

        val fold_rec :
          (TE.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 TE.t -> ('a1 TE.t -> __
          -> 'a3) -> (TE.key -> 'a1 -> 'a2 -> 'a1 TE.t -> 'a1 TE.t -> __ ->
          __ -> __ -> 'a3 -> 'a3) -> 'a3

        val fold_rec_bis :
          (TE.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 TE.t -> ('a1 TE.t ->
          'a1 TE.t -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3 -> (TE.key -> 'a1 ->
          'a2 -> 'a1 TE.t -> __ -> __ -> 'a3 -> 'a3) -> 'a3

        val fold_rec_nodep :
          (TE.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 TE.t -> 'a3 -> (TE.key
          -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

        val fold_rec_weak :
          (TE.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> ('a1 TE.t -> 'a1 TE.t ->
          'a2 -> __ -> 'a3 -> 'a3) -> 'a3 -> (TE.key -> 'a1 -> 'a2 -> 'a1
          TE.t -> __ -> 'a3 -> 'a3) -> 'a1 TE.t -> 'a3

        val fold_rel :
          (TE.key -> 'a1 -> 'a2 -> 'a2) -> (TE.key -> 'a1 -> 'a3 -> 'a3) ->
          'a2 -> 'a3 -> 'a1 TE.t -> 'a4 -> (TE.key -> 'a1 -> 'a2 -> 'a3 -> __
          -> 'a4 -> 'a4) -> 'a4

        val map_induction :
          ('a1 TE.t -> __ -> 'a2) -> ('a1 TE.t -> 'a1 TE.t -> 'a2 -> TE.key
          -> 'a1 -> __ -> __ -> 'a2) -> 'a1 TE.t -> 'a2

        val map_induction_bis :
          ('a1 TE.t -> 'a1 TE.t -> __ -> 'a2 -> 'a2) -> 'a2 -> (TE.key -> 'a1
          -> 'a1 TE.t -> __ -> 'a2 -> 'a2) -> 'a1 TE.t -> 'a2

        val cardinal_inv_2 : 'a1 TE.t -> int -> (TE.key * 'a1)

        val cardinal_inv_2b : 'a1 TE.t -> (TE.key * 'a1)

        val filter : (TE.key -> 'a1 -> bool) -> 'a1 TE.t -> 'a1 TE.t

        val for_all : (TE.key -> 'a1 -> bool) -> 'a1 TE.t -> bool

        val exists_ : (TE.key -> 'a1 -> bool) -> 'a1 TE.t -> bool

        val partition :
          (TE.key -> 'a1 -> bool) -> 'a1 TE.t -> 'a1 TE.t * 'a1 TE.t

        val update : 'a1 TE.t -> 'a1 TE.t -> 'a1 TE.t

        val restrict : 'a1 TE.t -> 'a1 TE.t -> 'a1 TE.t

        val diff : 'a1 TE.t -> 'a1 TE.t -> 'a1 TE.t

        val coq_Partition_In :
          'a1 TE.t -> 'a1 TE.t -> 'a1 TE.t -> TE.key -> bool

        val update_dec : 'a1 TE.t -> 'a1 TE.t -> TE.key -> 'a1 -> bool

        val filter_dom : (TE.key -> bool) -> 'a1 TE.t -> 'a1 TE.t

        val filter_range : ('a1 -> bool) -> 'a1 TE.t -> 'a1 TE.t

        val for_all_dom : (TE.key -> bool) -> 'a1 TE.t -> bool

        val for_all_range : ('a1 -> bool) -> 'a1 TE.t -> bool

        val exists_dom : (TE.key -> bool) -> 'a1 TE.t -> bool

        val exists_range : ('a1 -> bool) -> 'a1 TE.t -> bool

        val partition_dom :
          (TE.key -> bool) -> 'a1 TE.t -> 'a1 TE.t * 'a1 TE.t

        val partition_range : ('a1 -> bool) -> 'a1 TE.t -> 'a1 TE.t * 'a1 TE.t
       end

      val gtb : (TE.key * 'a1) -> (TE.key * 'a1) -> bool

      val leb : (TE.key * 'a1) -> (TE.key * 'a1) -> bool

      val elements_lt : (TE.key * 'a1) -> 'a1 TE.t -> (TE.key * 'a1) list

      val elements_ge : (TE.key * 'a1) -> 'a1 TE.t -> (TE.key * 'a1) list

      val max_elt_aux : (TE.key * 'a1) list -> (TE.key * 'a1) option

      val max_elt : 'a1 TE.t -> (TE.key * 'a1) option

      val min_elt : 'a1 TE.t -> (TE.key * 'a1) option

      val map_induction_max :
        ('a1 TE.t -> __ -> 'a2) -> ('a1 TE.t -> 'a1 TE.t -> 'a2 -> TE.SE.t ->
        'a1 -> __ -> __ -> 'a2) -> 'a1 TE.t -> 'a2

      val map_induction_min :
        ('a1 TE.t -> __ -> 'a2) -> ('a1 TE.t -> 'a1 TE.t -> 'a2 -> TE.SE.t ->
        'a1 -> __ -> __ -> 'a2) -> 'a1 TE.t -> 'a2
     end

    val eqb : TE.SE.t -> TE.SE.t -> bool

    val coq_In_dec : 'a1 TE.t -> TE.key -> bool

    module ME :
     sig
      module TO :
       sig
        type t = TE.SE.t
       end

      module IsTO :
       sig
       end

      module OrderTac :
       sig
       end

      val eq_dec : TE.SE.t -> TE.SE.t -> bool

      val lt_dec : TE.SE.t -> TE.SE.t -> bool

      val eqb : TE.SE.t -> TE.SE.t -> bool
     end

    module O :
     sig
      module MO :
       sig
        module TO :
         sig
          type t = TE.SE.t
         end

        module IsTO :
         sig
         end

        module OrderTac :
         sig
         end

        val eq_dec : TE.SE.t -> TE.SE.t -> bool

        val lt_dec : TE.SE.t -> TE.SE.t -> bool

        val eqb : TE.SE.t -> TE.SE.t -> bool
       end
     end

    module P :
     sig
      module F :
       sig
        val eqb : TE.SE.t -> TE.SE.t -> bool

        val coq_In_dec : 'a1 TE.t -> TE.key -> bool
       end

      val uncurry : ('a1 -> 'a2 -> 'a3) -> ('a1 * 'a2) -> 'a3

      val of_list : (TE.key * 'a1) list -> 'a1 TE.t

      val to_list : 'a1 TE.t -> (TE.key * 'a1) list

      val fold_rec :
        (TE.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 TE.t -> ('a1 TE.t -> __
        -> 'a3) -> (TE.key -> 'a1 -> 'a2 -> 'a1 TE.t -> 'a1 TE.t -> __ -> __
        -> __ -> 'a3 -> 'a3) -> 'a3

      val fold_rec_bis :
        (TE.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 TE.t -> ('a1 TE.t -> 'a1
        TE.t -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3 -> (TE.key -> 'a1 -> 'a2 ->
        'a1 TE.t -> __ -> __ -> 'a3 -> 'a3) -> 'a3

      val fold_rec_nodep :
        (TE.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 TE.t -> 'a3 -> (TE.key ->
        'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

      val fold_rec_weak :
        (TE.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> ('a1 TE.t -> 'a1 TE.t -> 'a2
        -> __ -> 'a3 -> 'a3) -> 'a3 -> (TE.key -> 'a1 -> 'a2 -> 'a1 TE.t ->
        __ -> 'a3 -> 'a3) -> 'a1 TE.t -> 'a3

      val fold_rel :
        (TE.key -> 'a1 -> 'a2 -> 'a2) -> (TE.key -> 'a1 -> 'a3 -> 'a3) -> 'a2
        -> 'a3 -> 'a1 TE.t -> 'a4 -> (TE.key -> 'a1 -> 'a2 -> 'a3 -> __ ->
        'a4 -> 'a4) -> 'a4

      val map_induction :
        ('a1 TE.t -> __ -> 'a2) -> ('a1 TE.t -> 'a1 TE.t -> 'a2 -> TE.key ->
        'a1 -> __ -> __ -> 'a2) -> 'a1 TE.t -> 'a2

      val map_induction_bis :
        ('a1 TE.t -> 'a1 TE.t -> __ -> 'a2 -> 'a2) -> 'a2 -> (TE.key -> 'a1
        -> 'a1 TE.t -> __ -> 'a2 -> 'a2) -> 'a1 TE.t -> 'a2

      val cardinal_inv_2 : 'a1 TE.t -> int -> (TE.key * 'a1)

      val cardinal_inv_2b : 'a1 TE.t -> (TE.key * 'a1)

      val filter : (TE.key -> 'a1 -> bool) -> 'a1 TE.t -> 'a1 TE.t

      val for_all : (TE.key -> 'a1 -> bool) -> 'a1 TE.t -> bool

      val exists_ : (TE.key -> 'a1 -> bool) -> 'a1 TE.t -> bool

      val partition :
        (TE.key -> 'a1 -> bool) -> 'a1 TE.t -> 'a1 TE.t * 'a1 TE.t

      val update : 'a1 TE.t -> 'a1 TE.t -> 'a1 TE.t

      val restrict : 'a1 TE.t -> 'a1 TE.t -> 'a1 TE.t

      val diff : 'a1 TE.t -> 'a1 TE.t -> 'a1 TE.t

      val coq_Partition_In :
        'a1 TE.t -> 'a1 TE.t -> 'a1 TE.t -> TE.key -> bool

      val update_dec : 'a1 TE.t -> 'a1 TE.t -> TE.key -> 'a1 -> bool

      val filter_dom : (TE.key -> bool) -> 'a1 TE.t -> 'a1 TE.t

      val filter_range : ('a1 -> bool) -> 'a1 TE.t -> 'a1 TE.t

      val for_all_dom : (TE.key -> bool) -> 'a1 TE.t -> bool

      val for_all_range : ('a1 -> bool) -> 'a1 TE.t -> bool

      val exists_dom : (TE.key -> bool) -> 'a1 TE.t -> bool

      val exists_range : ('a1 -> bool) -> 'a1 TE.t -> bool

      val partition_dom : (TE.key -> bool) -> 'a1 TE.t -> 'a1 TE.t * 'a1 TE.t

      val partition_range : ('a1 -> bool) -> 'a1 TE.t -> 'a1 TE.t * 'a1 TE.t
     end

    val gtb : (TE.key * 'a1) -> (TE.key * 'a1) -> bool

    val leb : (TE.key * 'a1) -> (TE.key * 'a1) -> bool

    val elements_lt : (TE.key * 'a1) -> 'a1 TE.t -> (TE.key * 'a1) list

    val elements_ge : (TE.key * 'a1) -> 'a1 TE.t -> (TE.key * 'a1) list

    val max_elt_aux : (TE.key * 'a1) list -> (TE.key * 'a1) option

    val max_elt : 'a1 TE.t -> (TE.key * 'a1) option

    val min_elt : 'a1 TE.t -> (TE.key * 'a1) option

    val map_induction_max :
      ('a1 TE.t -> __ -> 'a2) -> ('a1 TE.t -> 'a1 TE.t -> 'a2 -> TE.SE.t ->
      'a1 -> __ -> __ -> 'a2) -> 'a1 TE.t -> 'a2

    val map_induction_min :
      ('a1 TE.t -> __ -> 'a2) -> ('a1 TE.t -> 'a1 TE.t -> 'a2 -> TE.SE.t ->
      'a1 -> __ -> __ -> 'a2) -> 'a1 TE.t -> 'a2

    val memP : TE.key -> 'a1 TE.t -> reflect

    val split : ('a1 * 'a2) TE.t -> 'a1 TE.t * 'a2 TE.t

    module EFacts :
     sig
      module TO :
       sig
        type t = TE.SE.t
       end

      module IsTO :
       sig
       end

      module OrderTac :
       sig
       end

      val eq_dec : TE.SE.t -> TE.SE.t -> bool

      val lt_dec : TE.SE.t -> TE.SE.t -> bool

      val eqb : TE.SE.t -> TE.SE.t -> bool
     end

    val max_opt : TE.key -> TE.key option -> TE.key

    val max_key_elements : (TE.key * 'a1) list -> TE.key option

    val max_key : 'a1 TE.t -> TE.key option

    val min_opt : TE.key -> TE.key option -> TE.key

    val min_key_elements : (TE.key * 'a1) list -> TE.key option

    val min_key : 'a1 TE.t -> TE.key option
   end

  type t

  val empty : t

  val acc : V.t -> t -> bits

  val upd : V.t -> bits -> t -> t

  val upd2 : V.t -> bits -> V.t -> bits -> t -> t

  val map2 : (bits option -> bits option -> bits option) -> t -> t -> t
 end) ->
 sig
  module VSLemmas :
   sig
    module F :
     sig
      val eqb : VS.SE.t -> VS.SE.t -> bool
     end

    module OP :
     sig
      module ME :
       sig
        module TO :
         sig
          type t = VS.SE.t
         end

        module IsTO :
         sig
         end

        module OrderTac :
         sig
         end

        val eq_dec : VS.SE.t -> VS.SE.t -> bool

        val lt_dec : VS.SE.t -> VS.SE.t -> bool

        val eqb : VS.SE.t -> VS.SE.t -> bool
       end

      module P :
       sig
        module Dec :
         sig
          module F :
           sig
            val eqb : VS.SE.t -> VS.SE.t -> bool
           end

          module FSetLogicalFacts :
           sig
           end

          module FSetDecideAuxiliary :
           sig
           end

          module FSetDecideTestCases :
           sig
           end
         end

        module FM :
         sig
          val eqb : VS.SE.t -> VS.SE.t -> bool
         end

        val coq_In_dec : VS.elt -> VS.t -> bool

        val of_list : VS.elt list -> VS.t

        val to_list : VS.t -> VS.elt list

        val fold_rec :
          (VS.elt -> 'a1 -> 'a1) -> 'a1 -> VS.t -> (VS.t -> __ -> 'a2) ->
          (VS.elt -> 'a1 -> VS.t -> VS.t -> __ -> __ -> __ -> 'a2 -> 'a2) ->
          'a2

        val fold_rec_bis :
          (VS.elt -> 'a1 -> 'a1) -> 'a1 -> VS.t -> (VS.t -> VS.t -> 'a1 -> __
          -> 'a2 -> 'a2) -> 'a2 -> (VS.elt -> 'a1 -> VS.t -> __ -> __ -> 'a2
          -> 'a2) -> 'a2

        val fold_rec_nodep :
          (VS.elt -> 'a1 -> 'a1) -> 'a1 -> VS.t -> 'a2 -> (VS.elt -> 'a1 ->
          __ -> 'a2 -> 'a2) -> 'a2

        val fold_rec_weak :
          (VS.elt -> 'a1 -> 'a1) -> 'a1 -> (VS.t -> VS.t -> 'a1 -> __ -> 'a2
          -> 'a2) -> 'a2 -> (VS.elt -> 'a1 -> VS.t -> __ -> 'a2 -> 'a2) ->
          VS.t -> 'a2

        val fold_rel :
          (VS.elt -> 'a1 -> 'a1) -> (VS.elt -> 'a2 -> 'a2) -> 'a1 -> 'a2 ->
          VS.t -> 'a3 -> (VS.elt -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

        val set_induction :
          (VS.t -> __ -> 'a1) -> (VS.t -> VS.t -> 'a1 -> VS.elt -> __ -> __
          -> 'a1) -> VS.t -> 'a1

        val set_induction_bis :
          (VS.t -> VS.t -> __ -> 'a1 -> 'a1) -> 'a1 -> (VS.elt -> VS.t -> __
          -> 'a1 -> 'a1) -> VS.t -> 'a1

        val cardinal_inv_2 : VS.t -> int -> VS.elt

        val cardinal_inv_2b : VS.t -> VS.elt
       end

      val gtb : VS.SE.t -> VS.SE.t -> bool

      val leb : VS.SE.t -> VS.SE.t -> bool

      val elements_lt : VS.SE.t -> VS.t -> VS.SE.t list

      val elements_ge : VS.SE.t -> VS.t -> VS.SE.t list

      val set_induction_max :
        (VS.t -> __ -> 'a1) -> (VS.t -> VS.t -> 'a1 -> VS.SE.t -> __ -> __ ->
        'a1) -> VS.t -> 'a1

      val set_induction_min :
        (VS.t -> __ -> 'a1) -> (VS.t -> VS.t -> 'a1 -> VS.SE.t -> __ -> __ ->
        'a1) -> VS.t -> 'a1
     end

    val eqb : VS.SE.t -> VS.SE.t -> bool

    module ME :
     sig
      module TO :
       sig
        type t = VS.SE.t
       end

      module IsTO :
       sig
       end

      module OrderTac :
       sig
       end

      val eq_dec : VS.SE.t -> VS.SE.t -> bool

      val lt_dec : VS.SE.t -> VS.SE.t -> bool

      val eqb : VS.SE.t -> VS.SE.t -> bool
     end

    module P :
     sig
      module Dec :
       sig
        module F :
         sig
          val eqb : VS.SE.t -> VS.SE.t -> bool
         end

        module FSetLogicalFacts :
         sig
         end

        module FSetDecideAuxiliary :
         sig
         end

        module FSetDecideTestCases :
         sig
         end
       end

      module FM :
       sig
        val eqb : VS.SE.t -> VS.SE.t -> bool
       end

      val coq_In_dec : VS.elt -> VS.t -> bool

      val of_list : VS.elt list -> VS.t

      val to_list : VS.t -> VS.elt list

      val fold_rec :
        (VS.elt -> 'a1 -> 'a1) -> 'a1 -> VS.t -> (VS.t -> __ -> 'a2) ->
        (VS.elt -> 'a1 -> VS.t -> VS.t -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a2

      val fold_rec_bis :
        (VS.elt -> 'a1 -> 'a1) -> 'a1 -> VS.t -> (VS.t -> VS.t -> 'a1 -> __
        -> 'a2 -> 'a2) -> 'a2 -> (VS.elt -> 'a1 -> VS.t -> __ -> __ -> 'a2 ->
        'a2) -> 'a2

      val fold_rec_nodep :
        (VS.elt -> 'a1 -> 'a1) -> 'a1 -> VS.t -> 'a2 -> (VS.elt -> 'a1 -> __
        -> 'a2 -> 'a2) -> 'a2

      val fold_rec_weak :
        (VS.elt -> 'a1 -> 'a1) -> 'a1 -> (VS.t -> VS.t -> 'a1 -> __ -> 'a2 ->
        'a2) -> 'a2 -> (VS.elt -> 'a1 -> VS.t -> __ -> 'a2 -> 'a2) -> VS.t ->
        'a2

      val fold_rel :
        (VS.elt -> 'a1 -> 'a1) -> (VS.elt -> 'a2 -> 'a2) -> 'a1 -> 'a2 ->
        VS.t -> 'a3 -> (VS.elt -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

      val set_induction :
        (VS.t -> __ -> 'a1) -> (VS.t -> VS.t -> 'a1 -> VS.elt -> __ -> __ ->
        'a1) -> VS.t -> 'a1

      val set_induction_bis :
        (VS.t -> VS.t -> __ -> 'a1 -> 'a1) -> 'a1 -> (VS.elt -> VS.t -> __ ->
        'a1 -> 'a1) -> VS.t -> 'a1

      val cardinal_inv_2 : VS.t -> int -> VS.elt

      val cardinal_inv_2b : VS.t -> VS.elt
     end

    val gtb : VS.SE.t -> VS.SE.t -> bool

    val leb : VS.SE.t -> VS.SE.t -> bool

    val elements_lt : VS.SE.t -> VS.t -> VS.SE.t list

    val elements_ge : VS.SE.t -> VS.t -> VS.SE.t list

    val set_induction_max :
      (VS.t -> __ -> 'a1) -> (VS.t -> VS.t -> 'a1 -> VS.SE.t -> __ -> __ ->
      'a1) -> VS.t -> 'a1

    val set_induction_min :
      (VS.t -> __ -> 'a1) -> (VS.t -> VS.t -> 'a1 -> VS.SE.t -> __ -> __ ->
      'a1) -> VS.t -> 'a1

    val memP : VS.elt -> VS.t -> reflect

    val disjoint : VS.t -> VS.t -> bool
   end

  type fexpr = Coq__1.fexpr

  val econst : fgtyp -> bits -> Coq__1.fexpr

  val eref : Equality.sort -> Coq__1.fexpr

  val ecast : ucast -> Coq__1.fexpr -> Coq__1.fexpr

  val eprim_unop : eunop -> Coq__1.fexpr -> Coq__1.fexpr

  val eprim_binop : ebinop -> Coq__1.fexpr -> Coq__1.fexpr -> Coq__1.fexpr

  val emux : Coq__1.fexpr -> Coq__1.fexpr -> Coq__1.fexpr -> Coq__1.fexpr

  val evalidif : Coq__1.fexpr -> Coq__1.fexpr -> Coq__1.fexpr

  type fstmt = Coq__2.fstmt

  val sskip : Coq__2.fstmt

  val swire : Equality.sort -> fgtyp -> Coq__2.fstmt

  val sreg : freg -> Coq__2.fstmt

  val smem : fmem -> Coq__2.fstmt

  val snode : Equality.sort -> Coq__1.fexpr -> Coq__2.fstmt

  val sfcnct : Equality.sort -> Coq__1.fexpr -> Coq__2.fstmt

  type freg = Coq__3.freg

  val mk_freg : Equality.sort -> fgtyp -> Equality.sort -> rst -> Coq__3.freg

  val nrst : rst

  val rrst : Coq__1.fexpr -> Coq__1.fexpr -> rst

  type fmem = Coq__4.fmem

  val mk_fmem :
    Equality.sort -> fgtyp -> int -> freader_port list -> fwriter_port list
    -> int -> int -> ruw -> Coq__4.fmem

  val mk_fwriter_port :
    Equality.sort -> Equality.sort -> Equality.sort -> Equality.sort ->
    Equality.sort -> fwriter_port

  val mk_freader_port :
    Equality.sort -> Equality.sort -> Equality.sort -> Equality.sort ->
    freader_port

  type fwriter_port = Coq__5.fwriter_port

  type freader_port = Coq__6.freader_port

  type fport = Coq__7.fport

  val mk_finst : Equality.sort -> Equality.sort -> Coq__7.fport list -> finst

  type fmodule = Coq__8.fmodule

  type fcircuit = Coq__9.fcircuit

  type memory_map = bits -> bits

  val memfind : bits -> memory_map -> bits

  val memupd : bits -> bits -> memory_map -> memory_map

  val memempty : memory_map

  type mapls = V.t list TE.t

  type mapioin = bits list TE.t

  type mapdata2etc = ((((V.t * V.t) * V.t) * V.t) * V.t) TE.t

  type map2etc = mapdata2etc TE.t

  type mapmem = memory_map TE.t

  val mylListIn : V.t -> V.t list -> bool

  type maptuple = (V.t * V.t) TE.t

  type mmaptuple = maptuple TE.t

  type mapfstmt = fstmt list TE.t

  type mapterss = (((TE.env * SV.t) * SV.t) * mapmem) TE.t

  type mapvar = V.t TE.t

  type mvar = mapvar TE.t

  type mmapvar = (mvar * mapvar) TE.t

  type mmvar = (mapvar * mapvar) TE.t

  val bitsIn : bits -> bits list -> bool

  val varIn : V.t -> V.t list -> bool

  type g = V.t -> V.t list

  type mapg = g TE.t

  val emptyg : g

  val findg : V.t -> g -> V.t list

  val updg : V.t -> V.t list -> g -> g

  type var2stmtmap = fstmt TE.t

  type allvar2stmtmap = var2stmtmap TE.t

  type fmap = int TE.t

  type boolmap = bool TE.t

  type allboolmap = boolmap TE.t

  val upd_inner : SV.t -> SV.t -> V.t list -> mapvar -> SV.t

  val ftcast : bits -> fgtyp -> fgtyp -> bits

  val to_Clock : bits -> int

  val to_Reset : bits -> int

  val eunop_ucast : ucast -> bits -> int

  val eunop_op : eunop -> fgtyp -> bits -> bits

  val binop_bcmp : bcmp -> bits -> bits -> bits

  val binop_sbcmp : bcmp -> bits -> bits -> bits

  val full_adder_ext : bool -> bool list -> bool list -> bool * bits

  val adcB_ext : bool -> bool list -> bool list -> bool * bits

  val addB_ext : bool list -> bool list -> bits

  val sbbB_ext : bool -> bool list -> bits -> bool * bits

  val subB_ext : bool list -> bool list -> bits

  val coq_SadcB_ext : bits -> bits -> bool list

  val coq_SsbbB_ext : bits -> bits -> bool list

  val coq_Sfull_mul : bits -> bits -> bits

  val ebinop_op : ebinop -> fgtyp -> fgtyp -> bits -> bits -> bits

  val type_of_fexpr : fexpr -> TE.env -> fgtyp

  val eval_fexpr :
    fexpr -> SV.t -> SV.t -> TE.env -> V.t list -> V.t list -> mapdata2etc ->
    mapmem -> boolmap -> SV.t * bits

  val upd_typenv_fport : fport -> TE.env -> TE.env

  val upd_typenv_fports : fport list -> TE.env -> TE.env

  val upd_typenv_fstmt : fstmt -> TE.env -> SV.t -> TE.env

  val upd_typenv_fstmts : fstmt list -> TE.env -> SV.t -> TE.env

  val eval_noninst_fstmt :
    fstmt -> SV.t -> SV.t -> TE.env -> V.t list -> V.t list -> mapdata2etc ->
    mapmem -> boolmap -> (SV.t * SV.t) * mapmem

  val eval_fstmt :
    fstmt -> SV.t -> SV.t -> TE.env -> V.t list -> V.t list -> mapdata2etc ->
    mapmem -> boolmap -> V.t list -> maptuple -> mapfstmt -> mapterss ->
    allboolmap -> mapls -> mvar -> mapvar -> mapls -> mapls -> map2etc ->
    mapls -> mmaptuple -> mmapvar -> int ->
    ((SV.t * SV.t) * mapmem) * mapterss

  val eval_fstmts :
    fstmt list -> SV.t -> SV.t -> TE.env -> V.t list -> V.t list ->
    mapdata2etc -> mapmem -> boolmap -> V.t list -> maptuple -> mapfstmt ->
    mapterss -> allboolmap -> mapls -> mvar -> mapvar -> mapls -> mapls ->
    map2etc -> mapls -> mmaptuple -> mmapvar -> int ->
    ((SV.t * SV.t) * mapmem) * mapterss

  val upd_argulist : SV.t -> mapioin -> TE.key list -> int -> SV.t

  val myupdateo : SV.t -> bits list TE.t -> V.t -> bits list TE.t

  val eval_module :
    V.t -> SV.t -> SV.t -> TE.env -> mapioin -> V.t list -> mapls -> mapls ->
    map2etc -> mapmem -> mapls -> mmaptuple -> mapfstmt -> mapterss ->
    allboolmap -> mapls -> mmapvar -> int ->
    (((SV.t * SV.t) * mapmem) * mapterss) * mapioin

  val run_module0 :
    V.t -> SV.t -> SV.t -> TE.env -> mapioin -> TE.key list -> V.t list ->
    mapls -> mapls -> map2etc -> mapmem -> int -> int -> mapls -> mmaptuple
    -> mapfstmt -> mapterss -> allboolmap -> mapls -> mmapvar -> int ->
    (((SV.t * SV.t) * mapmem) * mapterss) * mapioin

  val expr2varlist : fexpr -> V.t list -> V.t list

  val findreg : V.t list -> V.t list -> fstmt -> V.t list * V.t list

  val findallvar : V.t list -> fstmt -> V.t list

  val def_known_reg_order :
    V.t list -> fstmt list -> fstmt list -> fstmt list -> fstmt -> (fstmt
    list * fstmt list) * fstmt list

  val known_reg_orders : fstmt list -> (fstmt list * fstmt list) * fstmt list

  val addreader2g : g -> freader_port -> g

  val addwriter2g : g -> fwriter_port -> g

  val addnewruw2g0 : freader_port list -> g -> fwriter_port -> g

  val addnewruw2g1 : freader_port list -> g -> fwriter_port -> g

  val inst_inoutlist : fport list -> V.t list * V.t list

  val dfs : g -> int -> V.t list -> V.t -> V.t list

  val dfs_path : g -> int -> V.t -> V.t -> bool

  val add_regedge : V.t list -> g -> fstmt -> g

  val buildg :
    V.t list -> fmap -> mapvar -> mapvar -> mapg -> g -> var2stmtmap -> fstmt
    -> g * var2stmtmap

  val findkinstps : mapls -> mvar -> V.t list -> fstmt -> V.t list

  val topo_tree :
    g -> int -> V.t list -> V.t list option -> V.t -> V.t list option

  val topo_sort : g -> int -> V.t list -> V.t list option

  val modname2g :
    V.t list -> fmap -> mapfstmt -> mmvar -> mvar -> mapls -> mapls -> mapls
    -> mapg -> mapfstmt -> mapls -> mapls ->
    ((mapg * mapfstmt) * mapls) * mapls

  val reorder :
    V.t list -> fmap -> mapfstmt -> mmvar -> mvar -> mapls -> mapls -> mapls
    -> mapfstmt * mapls

  val run_module :
    V.t list -> fmap -> mmvar -> mvar -> V.t -> SV.t -> SV.t -> TE.env ->
    mapioin -> TE.key list -> V.t list -> mapls -> mapls -> map2etc -> mapmem
    -> int -> int -> mapls -> mmaptuple -> mapfstmt -> mapterss -> allboolmap
    -> mapls -> mapls -> mmapvar -> int ->
    (((SV.t * SV.t) * mapmem) * mapterss) * mapioin

  val eval_fport_init : fport -> SV.t -> SV.t

  val eval_fports_init : fport list -> SV.t -> SV.t

  val upd_typenv_fmodule : fmodule -> TE.env -> SV.t -> TE.env

  val well_typed_fexpr : fexpr -> TE.env -> bool

  val no_mem_eval_fexpr : fexpr -> SV.t -> TE.env -> bits

  val no_mem_eval_noninst_fstmt :
    fstmt -> SV.t -> SV.t -> TE.env -> SV.t * SV.t

  val no_mem_upd_typenv_fstmt : fstmt -> TE.env -> TE.env

  val no_mem_upd_typenv_fstmts : fstmt list -> TE.env -> TE.env

  val no_mem_eval_fstmt :
    fstmt -> SV.t -> SV.t -> TE.env -> V.t list -> maptuple -> mapfstmt ->
    mapterss -> mapls -> mvar -> mapvar -> mapls -> mmaptuple -> mmapvar ->
    int -> (SV.t * SV.t) * mapterss

  val no_mem_eval_fstmts :
    fstmt list -> SV.t -> SV.t -> TE.env -> V.t list -> maptuple -> mapfstmt
    -> mapterss -> mapls -> mvar -> mapvar -> mapls -> mmaptuple -> mmapvar
    -> int -> (SV.t * SV.t) * mapterss

  val no_mem_eval_module :
    V.t -> SV.t -> SV.t -> TE.env -> mapioin -> V.t list -> mapls ->
    mmaptuple -> mapfstmt -> mapterss -> mapls -> mmapvar -> int ->
    ((SV.t * SV.t) * mapterss) * mapioin

  val no_mem_run_module0 :
    V.t -> SV.t -> SV.t -> TE.env -> mapioin -> TE.key list -> V.t list ->
    int -> int -> mapls -> mmaptuple -> mapfstmt -> mapterss -> mapls ->
    mmapvar -> int -> ((SV.t * SV.t) * mapterss) * mapioin

  val no_mem_run_module :
    V.t list -> fmap -> mmvar -> mvar -> V.t -> SV.t -> SV.t -> TE.env ->
    mapioin -> TE.key list -> V.t list -> int -> int -> mapls -> mmaptuple ->
    mapfstmt -> mapterss -> mapls -> mapls -> mmapvar -> int ->
    ((SV.t * SV.t) * mapterss) * mapioin

  val no_mem_eval_fstmts_inline :
    fstmt list -> SV.t -> SV.t -> TE.env -> SV.t * SV.t

  val no_mem_eval_module_inline :
    fstmt list -> SV.t -> SV.t -> TE.env -> mapioin -> V.t list ->
    (SV.t * SV.t) * mapioin

  val no_mem_run_module0_inline :
    fstmt list -> SV.t -> SV.t -> TE.env -> mapioin -> TE.key list -> V.t
    list -> int -> int -> (SV.t * SV.t) * mapioin

  val reorder_inline : Coq__8.fmodule -> fstmt list * g

  val no_mem_run_module_inline :
    Coq__8.fmodule -> SV.t -> SV.t -> TE.env -> mapioin -> TE.key list -> V.t
    list -> int -> int -> (SV.t * SV.t) * mapioin

  val is_defined : V.t -> TE.env -> bool

  val is_defined_fexpr : fexpr -> TE.env -> bool

  val is_defined_fstmt : fstmt -> TE.env -> bool

  val well_formed_fexpr : fexpr -> TE.env -> bool

  val well_typed_fstmt_inline : fstmt -> TE.env -> SV.t -> SV.t -> bool

  val well_formed_fstmt_inline : fstmt -> TE.env -> SV.t -> SV.t -> bool

  val well_formed_fstmts_inline : fstmt list -> TE.env -> SV.t -> SV.t -> bool
 end

module LoFirrtl :
 sig
  module VSLemmas :
   sig
    module F :
     sig
      val eqb : VS.SE.t -> VS.SE.t -> bool
     end

    module OP :
     sig
      module ME :
       sig
        module TO :
         sig
          type t = VS.SE.t
         end

        module IsTO :
         sig
         end

        module OrderTac :
         sig
         end

        val eq_dec : VS.SE.t -> VS.SE.t -> bool

        val lt_dec : VS.SE.t -> VS.SE.t -> bool

        val eqb : VS.SE.t -> VS.SE.t -> bool
       end

      module P :
       sig
        module Dec :
         sig
          module F :
           sig
            val eqb : VS.SE.t -> VS.SE.t -> bool
           end

          module FSetLogicalFacts :
           sig
           end

          module FSetDecideAuxiliary :
           sig
           end

          module FSetDecideTestCases :
           sig
           end
         end

        module FM :
         sig
          val eqb : VS.SE.t -> VS.SE.t -> bool
         end

        val coq_In_dec : VS.elt -> VS.t -> bool

        val of_list : VS.elt list -> VS.t

        val to_list : VS.t -> VS.elt list

        val fold_rec :
          (VS.elt -> 'a1 -> 'a1) -> 'a1 -> VS.t -> (VS.t -> __ -> 'a2) ->
          (VS.elt -> 'a1 -> VS.t -> VS.t -> __ -> __ -> __ -> 'a2 -> 'a2) ->
          'a2

        val fold_rec_bis :
          (VS.elt -> 'a1 -> 'a1) -> 'a1 -> VS.t -> (VS.t -> VS.t -> 'a1 -> __
          -> 'a2 -> 'a2) -> 'a2 -> (VS.elt -> 'a1 -> VS.t -> __ -> __ -> 'a2
          -> 'a2) -> 'a2

        val fold_rec_nodep :
          (VS.elt -> 'a1 -> 'a1) -> 'a1 -> VS.t -> 'a2 -> (VS.elt -> 'a1 ->
          __ -> 'a2 -> 'a2) -> 'a2

        val fold_rec_weak :
          (VS.elt -> 'a1 -> 'a1) -> 'a1 -> (VS.t -> VS.t -> 'a1 -> __ -> 'a2
          -> 'a2) -> 'a2 -> (VS.elt -> 'a1 -> VS.t -> __ -> 'a2 -> 'a2) ->
          VS.t -> 'a2

        val fold_rel :
          (VS.elt -> 'a1 -> 'a1) -> (VS.elt -> 'a2 -> 'a2) -> 'a1 -> 'a2 ->
          VS.t -> 'a3 -> (VS.elt -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

        val set_induction :
          (VS.t -> __ -> 'a1) -> (VS.t -> VS.t -> 'a1 -> VS.elt -> __ -> __
          -> 'a1) -> VS.t -> 'a1

        val set_induction_bis :
          (VS.t -> VS.t -> __ -> 'a1 -> 'a1) -> 'a1 -> (VS.elt -> VS.t -> __
          -> 'a1 -> 'a1) -> VS.t -> 'a1

        val cardinal_inv_2 : VS.t -> int -> VS.elt

        val cardinal_inv_2b : VS.t -> VS.elt
       end

      val gtb : VS.SE.t -> VS.SE.t -> bool

      val leb : VS.SE.t -> VS.SE.t -> bool

      val elements_lt : VS.SE.t -> VS.t -> VS.SE.t list

      val elements_ge : VS.SE.t -> VS.t -> VS.SE.t list

      val set_induction_max :
        (VS.t -> __ -> 'a1) -> (VS.t -> VS.t -> 'a1 -> VS.SE.t -> __ -> __ ->
        'a1) -> VS.t -> 'a1

      val set_induction_min :
        (VS.t -> __ -> 'a1) -> (VS.t -> VS.t -> 'a1 -> VS.SE.t -> __ -> __ ->
        'a1) -> VS.t -> 'a1
     end

    val eqb : VS.SE.t -> VS.SE.t -> bool

    module ME :
     sig
      module TO :
       sig
        type t = VS.SE.t
       end

      module IsTO :
       sig
       end

      module OrderTac :
       sig
       end

      val eq_dec : VS.SE.t -> VS.SE.t -> bool

      val lt_dec : VS.SE.t -> VS.SE.t -> bool

      val eqb : VS.SE.t -> VS.SE.t -> bool
     end

    module P :
     sig
      module Dec :
       sig
        module F :
         sig
          val eqb : VS.SE.t -> VS.SE.t -> bool
         end

        module FSetLogicalFacts :
         sig
         end

        module FSetDecideAuxiliary :
         sig
         end

        module FSetDecideTestCases :
         sig
         end
       end

      module FM :
       sig
        val eqb : VS.SE.t -> VS.SE.t -> bool
       end

      val coq_In_dec : VS.elt -> VS.t -> bool

      val of_list : VS.elt list -> VS.t

      val to_list : VS.t -> VS.elt list

      val fold_rec :
        (VS.elt -> 'a1 -> 'a1) -> 'a1 -> VS.t -> (VS.t -> __ -> 'a2) ->
        (VS.elt -> 'a1 -> VS.t -> VS.t -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a2

      val fold_rec_bis :
        (VS.elt -> 'a1 -> 'a1) -> 'a1 -> VS.t -> (VS.t -> VS.t -> 'a1 -> __
        -> 'a2 -> 'a2) -> 'a2 -> (VS.elt -> 'a1 -> VS.t -> __ -> __ -> 'a2 ->
        'a2) -> 'a2

      val fold_rec_nodep :
        (VS.elt -> 'a1 -> 'a1) -> 'a1 -> VS.t -> 'a2 -> (VS.elt -> 'a1 -> __
        -> 'a2 -> 'a2) -> 'a2

      val fold_rec_weak :
        (VS.elt -> 'a1 -> 'a1) -> 'a1 -> (VS.t -> VS.t -> 'a1 -> __ -> 'a2 ->
        'a2) -> 'a2 -> (VS.elt -> 'a1 -> VS.t -> __ -> 'a2 -> 'a2) -> VS.t ->
        'a2

      val fold_rel :
        (VS.elt -> 'a1 -> 'a1) -> (VS.elt -> 'a2 -> 'a2) -> 'a1 -> 'a2 ->
        VS.t -> 'a3 -> (VS.elt -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

      val set_induction :
        (VS.t -> __ -> 'a1) -> (VS.t -> VS.t -> 'a1 -> VS.elt -> __ -> __ ->
        'a1) -> VS.t -> 'a1

      val set_induction_bis :
        (VS.t -> VS.t -> __ -> 'a1 -> 'a1) -> 'a1 -> (VS.elt -> VS.t -> __ ->
        'a1 -> 'a1) -> VS.t -> 'a1

      val cardinal_inv_2 : VS.t -> int -> VS.elt

      val cardinal_inv_2b : VS.t -> VS.elt
     end

    val gtb : VS.SE.t -> VS.SE.t -> bool

    val leb : VS.SE.t -> VS.SE.t -> bool

    val elements_lt : VS.SE.t -> VS.t -> VS.SE.t list

    val elements_ge : VS.SE.t -> VS.t -> VS.SE.t list

    val set_induction_max :
      (VS.t -> __ -> 'a1) -> (VS.t -> VS.t -> 'a1 -> VS.SE.t -> __ -> __ ->
      'a1) -> VS.t -> 'a1

    val set_induction_min :
      (VS.t -> __ -> 'a1) -> (VS.t -> VS.t -> 'a1 -> VS.SE.t -> __ -> __ ->
      'a1) -> VS.t -> 'a1

    val memP : VS.elt -> VS.t -> reflect

    val disjoint : VS.t -> VS.t -> bool
   end

  type fexpr = Coq__1.fexpr

  val econst : fgtyp -> bits -> Coq__1.fexpr

  val eref : Equality.sort -> Coq__1.fexpr

  val ecast : ucast -> Coq__1.fexpr -> Coq__1.fexpr

  val eprim_unop : eunop -> Coq__1.fexpr -> Coq__1.fexpr

  val eprim_binop : ebinop -> Coq__1.fexpr -> Coq__1.fexpr -> Coq__1.fexpr

  val emux : Coq__1.fexpr -> Coq__1.fexpr -> Coq__1.fexpr -> Coq__1.fexpr

  val evalidif : Coq__1.fexpr -> Coq__1.fexpr -> Coq__1.fexpr

  type fstmt = Coq__2.fstmt

  val sskip : Coq__2.fstmt

  val swire : Equality.sort -> fgtyp -> Coq__2.fstmt

  val sreg : freg -> Coq__2.fstmt

  val smem : fmem -> Coq__2.fstmt

  val snode : Equality.sort -> Coq__1.fexpr -> Coq__2.fstmt

  val sfcnct : Equality.sort -> Coq__1.fexpr -> Coq__2.fstmt

  type freg = Coq__3.freg

  val mk_freg : Equality.sort -> fgtyp -> Equality.sort -> rst -> Coq__3.freg

  val nrst : rst

  val rrst : Coq__1.fexpr -> Coq__1.fexpr -> rst

  type fmem = Coq__4.fmem

  val mk_fmem :
    Equality.sort -> fgtyp -> int -> freader_port list -> fwriter_port list
    -> int -> int -> ruw -> Coq__4.fmem

  val mk_fwriter_port :
    Equality.sort -> Equality.sort -> Equality.sort -> Equality.sort ->
    Equality.sort -> fwriter_port

  val mk_freader_port :
    Equality.sort -> Equality.sort -> Equality.sort -> Equality.sort ->
    freader_port

  type fwriter_port = Coq__5.fwriter_port

  type freader_port = Coq__6.freader_port

  type fport = Coq__7.fport

  val mk_finst : Equality.sort -> Equality.sort -> Coq__7.fport list -> finst

  type fmodule = Coq__8.fmodule

  type fcircuit = Coq__9.fcircuit

  type memory_map = bits -> bits

  val memfind : bits -> memory_map -> bits

  val memupd : bits -> bits -> memory_map -> memory_map

  val memempty : memory_map

  type mapls = VarOrder.t list TE.t

  type mapioin = bits list TE.t

  type mapdata2etc =
    ((((VarOrder.t * VarOrder.t) * VarOrder.t) * VarOrder.t) * VarOrder.t)
    TE.t

  type map2etc = mapdata2etc TE.t

  type mapmem = memory_map TE.t

  val mylListIn : VarOrder.t -> VarOrder.t list -> bool

  type maptuple = (VarOrder.t * VarOrder.t) TE.t

  type mmaptuple = maptuple TE.t

  type mapfstmt = fstmt list TE.t

  type mapterss = (((TE.env * Store.t) * Store.t) * mapmem) TE.t

  type mapvar = VarOrder.t TE.t

  type mvar = mapvar TE.t

  type mmapvar = (mvar * mapvar) TE.t

  type mmvar = (mapvar * mapvar) TE.t

  val bitsIn : bits -> bits list -> bool

  val varIn : VarOrder.t -> VarOrder.t list -> bool

  type g = VarOrder.t -> VarOrder.t list

  type mapg = g TE.t

  val emptyg : g

  val findg : VarOrder.t -> g -> VarOrder.t list

  val updg : VarOrder.t -> VarOrder.t list -> g -> g

  type var2stmtmap = fstmt TE.t

  type allvar2stmtmap = var2stmtmap TE.t

  type fmap = int TE.t

  type boolmap = bool TE.t

  type allboolmap = boolmap TE.t

  val upd_inner : Store.t -> Store.t -> VarOrder.t list -> mapvar -> Store.t

  val ftcast : bits -> fgtyp -> fgtyp -> bits

  val to_Clock : bits -> int

  val to_Reset : bits -> int

  val eunop_ucast : ucast -> bits -> int

  val eunop_op : eunop -> fgtyp -> bits -> bits

  val binop_bcmp : bcmp -> bits -> bits -> bits

  val binop_sbcmp : bcmp -> bits -> bits -> bits

  val full_adder_ext : bool -> bool list -> bool list -> bool * bits

  val adcB_ext : bool -> bool list -> bool list -> bool * bits

  val addB_ext : bool list -> bool list -> bits

  val sbbB_ext : bool -> bool list -> bits -> bool * bits

  val subB_ext : bool list -> bool list -> bits

  val coq_SadcB_ext : bits -> bits -> bool list

  val coq_SsbbB_ext : bits -> bits -> bool list

  val coq_Sfull_mul : bits -> bits -> bits

  val ebinop_op : ebinop -> fgtyp -> fgtyp -> bits -> bits -> bits

  val type_of_fexpr : fexpr -> TE.env -> fgtyp

  val eval_fexpr :
    fexpr -> Store.t -> Store.t -> TE.env -> VarOrder.t list -> VarOrder.t
    list -> mapdata2etc -> mapmem -> boolmap -> Store.t * bits

  val upd_typenv_fport : fport -> TE.env -> TE.env

  val upd_typenv_fports : fport list -> TE.env -> TE.env

  val upd_typenv_fstmt : fstmt -> TE.env -> Store.t -> TE.env

  val upd_typenv_fstmts : fstmt list -> TE.env -> Store.t -> TE.env

  val eval_noninst_fstmt :
    fstmt -> Store.t -> Store.t -> TE.env -> VarOrder.t list -> VarOrder.t
    list -> mapdata2etc -> mapmem -> boolmap -> (Store.t * Store.t) * mapmem

  val eval_fstmt :
    fstmt -> Store.t -> Store.t -> TE.env -> VarOrder.t list -> VarOrder.t
    list -> mapdata2etc -> mapmem -> boolmap -> VarOrder.t list -> maptuple
    -> mapfstmt -> mapterss -> allboolmap -> mapls -> mvar -> mapvar -> mapls
    -> mapls -> map2etc -> mapls -> mmaptuple -> mmapvar -> int ->
    ((Store.t * Store.t) * mapmem) * mapterss

  val eval_fstmts :
    fstmt list -> Store.t -> Store.t -> TE.env -> VarOrder.t list ->
    VarOrder.t list -> mapdata2etc -> mapmem -> boolmap -> VarOrder.t list ->
    maptuple -> mapfstmt -> mapterss -> allboolmap -> mapls -> mvar -> mapvar
    -> mapls -> mapls -> map2etc -> mapls -> mmaptuple -> mmapvar -> int ->
    ((Store.t * Store.t) * mapmem) * mapterss

  val upd_argulist : Store.t -> mapioin -> TE.key list -> int -> Store.t

  val myupdateo : Store.t -> bits list TE.t -> VarOrder.t -> bits list TE.t

  val eval_module :
    VarOrder.t -> Store.t -> Store.t -> TE.env -> mapioin -> VarOrder.t list
    -> mapls -> mapls -> map2etc -> mapmem -> mapls -> mmaptuple -> mapfstmt
    -> mapterss -> allboolmap -> mapls -> mmapvar -> int ->
    (((Store.t * Store.t) * mapmem) * mapterss) * mapioin

  val run_module0 :
    VarOrder.t -> Store.t -> Store.t -> TE.env -> mapioin -> TE.key list ->
    VarOrder.t list -> mapls -> mapls -> map2etc -> mapmem -> int -> int ->
    mapls -> mmaptuple -> mapfstmt -> mapterss -> allboolmap -> mapls ->
    mmapvar -> int -> (((Store.t * Store.t) * mapmem) * mapterss) * mapioin

  val expr2varlist : fexpr -> VarOrder.t list -> VarOrder.t list

  val findreg :
    VarOrder.t list -> VarOrder.t list -> fstmt -> VarOrder.t
    list * VarOrder.t list

  val findallvar : VarOrder.t list -> fstmt -> VarOrder.t list

  val def_known_reg_order :
    VarOrder.t list -> fstmt list -> fstmt list -> fstmt list -> fstmt ->
    (fstmt list * fstmt list) * fstmt list

  val known_reg_orders : fstmt list -> (fstmt list * fstmt list) * fstmt list

  val addreader2g : g -> freader_port -> g

  val addwriter2g : g -> fwriter_port -> g

  val addnewruw2g0 : freader_port list -> g -> fwriter_port -> g

  val addnewruw2g1 : freader_port list -> g -> fwriter_port -> g

  val inst_inoutlist : fport list -> VarOrder.t list * VarOrder.t list

  val dfs : g -> int -> VarOrder.t list -> VarOrder.t -> VarOrder.t list

  val dfs_path : g -> int -> VarOrder.t -> VarOrder.t -> bool

  val add_regedge : VarOrder.t list -> g -> fstmt -> g

  val buildg :
    VarOrder.t list -> fmap -> mapvar -> mapvar -> mapg -> g -> var2stmtmap
    -> fstmt -> g * var2stmtmap

  val findkinstps :
    mapls -> mvar -> VarOrder.t list -> fstmt -> VarOrder.t list

  val topo_tree :
    g -> int -> VarOrder.t list -> VarOrder.t list option -> VarOrder.t ->
    VarOrder.t list option

  val topo_sort : g -> int -> VarOrder.t list -> VarOrder.t list option

  val modname2g :
    VarOrder.t list -> fmap -> mapfstmt -> mmvar -> mvar -> mapls -> mapls ->
    mapls -> mapg -> mapfstmt -> mapls -> mapls ->
    ((mapg * mapfstmt) * mapls) * mapls

  val reorder :
    VarOrder.t list -> fmap -> mapfstmt -> mmvar -> mvar -> mapls -> mapls ->
    mapls -> mapfstmt * mapls

  val run_module :
    VarOrder.t list -> fmap -> mmvar -> mvar -> VarOrder.t -> Store.t ->
    Store.t -> TE.env -> mapioin -> TE.key list -> VarOrder.t list -> mapls
    -> mapls -> map2etc -> mapmem -> int -> int -> mapls -> mmaptuple ->
    mapfstmt -> mapterss -> allboolmap -> mapls -> mapls -> mmapvar -> int ->
    (((Store.t * Store.t) * mapmem) * mapterss) * mapioin

  val eval_fport_init : fport -> Store.t -> Store.t

  val eval_fports_init : fport list -> Store.t -> Store.t

  val upd_typenv_fmodule : fmodule -> TE.env -> Store.t -> TE.env

  val well_typed_fexpr : fexpr -> TE.env -> bool

  val no_mem_eval_fexpr : fexpr -> Store.t -> TE.env -> bits

  val no_mem_eval_noninst_fstmt :
    fstmt -> Store.t -> Store.t -> TE.env -> Store.t * Store.t

  val no_mem_upd_typenv_fstmt : fstmt -> TE.env -> TE.env

  val no_mem_upd_typenv_fstmts : fstmt list -> TE.env -> TE.env

  val no_mem_eval_fstmt :
    fstmt -> Store.t -> Store.t -> TE.env -> VarOrder.t list -> maptuple ->
    mapfstmt -> mapterss -> mapls -> mvar -> mapvar -> mapls -> mmaptuple ->
    mmapvar -> int -> (Store.t * Store.t) * mapterss

  val no_mem_eval_fstmts :
    fstmt list -> Store.t -> Store.t -> TE.env -> VarOrder.t list -> maptuple
    -> mapfstmt -> mapterss -> mapls -> mvar -> mapvar -> mapls -> mmaptuple
    -> mmapvar -> int -> (Store.t * Store.t) * mapterss

  val no_mem_eval_module :
    VarOrder.t -> Store.t -> Store.t -> TE.env -> mapioin -> VarOrder.t list
    -> mapls -> mmaptuple -> mapfstmt -> mapterss -> mapls -> mmapvar -> int
    -> ((Store.t * Store.t) * mapterss) * mapioin

  val no_mem_run_module0 :
    VarOrder.t -> Store.t -> Store.t -> TE.env -> mapioin -> TE.key list ->
    VarOrder.t list -> int -> int -> mapls -> mmaptuple -> mapfstmt ->
    mapterss -> mapls -> mmapvar -> int ->
    ((Store.t * Store.t) * mapterss) * mapioin

  val no_mem_run_module :
    VarOrder.t list -> fmap -> mmvar -> mvar -> VarOrder.t -> Store.t ->
    Store.t -> TE.env -> mapioin -> TE.key list -> VarOrder.t list -> int ->
    int -> mapls -> mmaptuple -> mapfstmt -> mapterss -> mapls -> mapls ->
    mmapvar -> int -> ((Store.t * Store.t) * mapterss) * mapioin

  val no_mem_eval_fstmts_inline :
    fstmt list -> Store.t -> Store.t -> TE.env -> Store.t * Store.t

  val no_mem_eval_module_inline :
    fstmt list -> Store.t -> Store.t -> TE.env -> mapioin -> VarOrder.t list
    -> (Store.t * Store.t) * mapioin

  val no_mem_run_module0_inline :
    fstmt list -> Store.t -> Store.t -> TE.env -> mapioin -> TE.key list ->
    VarOrder.t list -> int -> int -> (Store.t * Store.t) * mapioin

  val reorder_inline : Coq__8.fmodule -> fstmt list * g

  val no_mem_run_module_inline :
    Coq__8.fmodule -> Store.t -> Store.t -> TE.env -> mapioin -> TE.key list
    -> VarOrder.t list -> int -> int -> (Store.t * Store.t) * mapioin

  val is_defined : VarOrder.t -> TE.env -> bool

  val is_defined_fexpr : fexpr -> TE.env -> bool

  val is_defined_fstmt : fstmt -> TE.env -> bool

  val well_formed_fexpr : fexpr -> TE.env -> bool

  val well_typed_fstmt_inline : fstmt -> TE.env -> Store.t -> Store.t -> bool

  val well_formed_fstmt_inline : fstmt -> TE.env -> Store.t -> Store.t -> bool

  val well_formed_fstmts_inline :
    fstmt list -> TE.env -> Store.t -> Store.t -> bool
 end
