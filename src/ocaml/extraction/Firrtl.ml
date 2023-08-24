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

module Coq__1 = struct
 type fexpr =
 | Econst of fgtyp * bits
 | Ecast of ucast * fexpr
 | Eprim_unop of eunop * fexpr
 | Eprim_binop of ebinop * fexpr * fexpr
 | Emux of fexpr * fexpr * fexpr
 | Evalidif of fexpr * fexpr
 | Eref of Equality.sort
end
include Coq__1

type ruw =
| Coq_old
| Coq_new
| Coq_undefined

module Coq__6 = struct
 type freader_port = { addr : Equality.sort; data : Equality.sort;
                       en : Equality.sort; clk : Equality.sort }
end
include Coq__6

module Coq__5 = struct
 type fwriter_port = { addr0 : Equality.sort; data0 : Equality.sort;
                       en0 : Equality.sort; clk0 : Equality.sort;
                       mask : Equality.sort }
end
include Coq__5

module Coq__4 = struct
 type fmem = { mid : Equality.sort; data_type : fgtyp; depth : int;
               reader : freader_port list; writer : fwriter_port list;
               read_latency : int; write_latency : int; read_write : 
               ruw }
end
include Coq__4

type rst =
| NRst
| Rst of fexpr * fexpr

module Coq__3 = struct
 type freg = { rid : Equality.sort; coq_type : fgtyp; clock : Equality.sort;
               reset : rst }
end
include Coq__3

module Coq__7 = struct
 type fport =
 | Finput of Equality.sort * fgtyp
 | Foutput of Equality.sort * fgtyp
end
include Coq__7

type finst = { iid : Equality.sort; imid : Equality.sort; iports : fport list }

module Coq__2 = struct
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
include Coq__2

module Coq__8 = struct
 type fmodule =
 | FInmod of Equality.sort * fport list * fstmt list
 | FExmod of Equality.sort * fport list * fstmt list
end
include Coq__8

module Coq__9 = struct
 type fcircuit =
 | Fcircuit of Equality.sort * fmodule list
end
include Coq__9

module MakeFirrtl =
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
 struct
  module VSLemmas = SsrFSetLemmas(VS)

  type fexpr = Coq__1.fexpr

  (** val econst : fgtyp -> bits -> Coq__1.fexpr **)

  let econst c x =
    Econst (c, x)

  (** val eref : Equality.sort -> Coq__1.fexpr **)

  let eref v =
    Eref v

  (** val ecast : ucast -> Coq__1.fexpr -> Coq__1.fexpr **)

  let ecast u e =
    Ecast (u, e)

  (** val eprim_unop : eunop -> Coq__1.fexpr -> Coq__1.fexpr **)

  let eprim_unop u e =
    Eprim_unop (u, e)

  (** val eprim_binop :
      ebinop -> Coq__1.fexpr -> Coq__1.fexpr -> Coq__1.fexpr **)

  let eprim_binop b e1 e2 =
    Eprim_binop (b, e1, e2)

  (** val emux :
      Coq__1.fexpr -> Coq__1.fexpr -> Coq__1.fexpr -> Coq__1.fexpr **)

  let emux c e1 e2 =
    Emux (c, e1, e2)

  (** val evalidif : Coq__1.fexpr -> Coq__1.fexpr -> Coq__1.fexpr **)

  let evalidif c e =
    Evalidif (c, e)

  type fstmt = Coq__2.fstmt

  (** val sskip : Coq__2.fstmt **)

  let sskip =
    Sskip

  (** val swire : Equality.sort -> fgtyp -> Coq__2.fstmt **)

  let swire v t0 =
    Swire (v, t0)

  (** val sreg : freg -> Coq__2.fstmt **)

  let sreg r =
    Sreg r

  (** val smem : fmem -> Coq__2.fstmt **)

  let smem m =
    Smem m

  (** val snode : Equality.sort -> Coq__1.fexpr -> Coq__2.fstmt **)

  let snode v e =
    Snode (v, e)

  (** val sfcnct : Equality.sort -> Coq__1.fexpr -> Coq__2.fstmt **)

  let sfcnct v1 v2 =
    Sfcnct (v1, v2)

  type freg = Coq__3.freg

  (** val mk_freg :
      Equality.sort -> fgtyp -> Equality.sort -> rst -> Coq__3.freg **)

  let mk_freg x x0 x1 x2 =
    { rid = x; coq_type = x0; clock = x1; reset = x2 }

  (** val nrst : rst **)

  let nrst =
    NRst

  (** val rrst : Coq__1.fexpr -> Coq__1.fexpr -> rst **)

  let rrst e1 e2 =
    Rst (e1, e2)

  type fmem = Coq__4.fmem

  (** val mk_fmem :
      Equality.sort -> fgtyp -> int -> freader_port list -> fwriter_port list
      -> int -> int -> ruw -> Coq__4.fmem **)

  let mk_fmem x x0 x1 x2 x3 x4 x5 x6 =
    { mid = x; data_type = x0; depth = x1; reader = x2; writer = x3;
      read_latency = x4; write_latency = x5; read_write = x6 }

  (** val mk_fwriter_port :
      Equality.sort -> Equality.sort -> Equality.sort -> Equality.sort ->
      Equality.sort -> fwriter_port **)

  let mk_fwriter_port x x0 x1 x2 x3 =
    { addr0 = x; data0 = x0; en0 = x1; clk0 = x2; mask = x3 }

  (** val mk_freader_port :
      Equality.sort -> Equality.sort -> Equality.sort -> Equality.sort ->
      freader_port **)

  let mk_freader_port x x0 x1 x2 =
    { addr = x; data = x0; en = x1; clk = x2 }

  type fwriter_port = Coq__5.fwriter_port

  type freader_port = Coq__6.freader_port

  type fport = Coq__7.fport

  (** val mk_finst :
      Equality.sort -> Equality.sort -> Coq__7.fport list -> finst **)

  let mk_finst x x0 x1 =
    { iid = x; imid = x0; iports = x1 }

  type fmodule = Coq__8.fmodule

  type fcircuit = Coq__9.fcircuit

  type memory_map = bits -> bits

  (** val memfind : bits -> memory_map -> bits **)

  let memfind key0 map0 =
    map0 key0

  (** val memupd : bits -> bits -> memory_map -> memory_map **)

  let memupd key0 v memmap y =
    if eq_op bitseq_eqType (Obj.magic y) (Obj.magic key0)
    then v
    else memfind y memmap

  (** val memempty : memory_map **)

  let memempty _ =
    []

  type mapls = V.t list TE.t

  type mapioin = bits list TE.t

  type mapdata2etc = ((((V.t * V.t) * V.t) * V.t) * V.t) TE.t

  type map2etc = mapdata2etc TE.t

  type mapmem = memory_map TE.t

  (** val mylListIn : V.t -> V.t list -> bool **)

  let rec mylListIn a = function
  | [] -> b0
  | b :: m -> if eq_op V.coq_T b a then b1 else mylListIn a m

  type maptuple = (V.t * V.t) TE.t

  type mmaptuple = maptuple TE.t

  type mapfstmt = fstmt list TE.t

  type mapterss = (((TE.env * SV.t) * SV.t) * mapmem) TE.t

  type mapvar = V.t TE.t

  type mvar = mapvar TE.t

  type mmapvar = (mvar * mapvar) TE.t

  type mmvar = (mapvar * mapvar) TE.t

  (** val bitsIn : bits -> bits list -> bool **)

  let rec bitsIn a = function
  | [] -> b0
  | b :: m ->
    if eq_op nat_eqType (Obj.magic to_nat b) (Obj.magic to_nat a)
    then b1
    else bitsIn a m

  (** val varIn : V.t -> V.t list -> bool **)

  let rec varIn a = function
  | [] -> b0
  | b :: m -> if eq_op V.coq_T b a then b1 else varIn a m

  type g = V.t -> V.t list

  type mapg = g TE.t

  (** val emptyg : g **)

  let emptyg _ =
    []

  (** val findg : V.t -> g -> V.t list **)

  let findg key0 map0 =
    map0 key0

  (** val updg : V.t -> V.t list -> g -> g **)

  let updg key0 v map0 y =
    if eq_op V.coq_T y key0 then v else findg y map0

  type var2stmtmap = fstmt TE.t

  type allvar2stmtmap = var2stmtmap TE.t

  type fmap = int TE.t

  type boolmap = bool TE.t

  type allboolmap = boolmap TE.t

  (** val upd_inner : SV.t -> SV.t -> V.t list -> mapvar -> SV.t **)

  let rec upd_inner s s0 a2 finstinmap =
    match a2 with
    | [] -> s0
    | h :: t0 ->
      let s1 =
        match TE.find h finstinmap with
        | Some a -> SV.upd h (SV.acc a s) s0
        | None -> s0
      in
      upd_inner s s1 t0 finstinmap

  (** val ftcast : bits -> fgtyp -> fgtyp -> bits **)

  let ftcast bs fty tty =
    match fty with
    | Fuint _ -> ucastB bs (sizeof_fgtyp tty)
    | Fsint _ -> scastB bs (sizeof_fgtyp tty)
    | _ -> ucastB bs (Pervasives.succ 0)

  (** val to_Clock : bits -> int **)

  let to_Clock bs =
    Z.b2z (lsb bs)

  (** val to_Reset : bits -> int **)

  let to_Reset bs =
    Z.b2z (lsb bs)

  (** val eunop_ucast : ucast -> bits -> int **)

  let eunop_ucast = function
  | AsUInt -> to_Zpos
  | AsSInt -> to_Z
  | AsClock -> to_Clock
  | _ -> to_Reset

  (** val eunop_op : eunop -> fgtyp -> bits -> bits **)

  let eunop_op o t0 =
    match o with
    | Upad n ->
      (fun b ->
        if leq (Pervasives.succ n) (size b)
        then b
        else (match t0 with
              | Fuint w -> zext (subn n w) b
              | Fsint w -> sext (subn n w) b
              | _ -> b))
    | Ushl n -> (fun b -> cat (zeros n) b)
    | Ushr n ->
      (fun b ->
        if leq (Pervasives.succ n) (size b)
        then high (subn (size b) n) b
        else (msb b) :: [])
    | Ucvt ->
      (fun b -> match t0 with
                | Fuint _ -> sext (Pervasives.succ 0) b
                | _ -> b)
    | Uneg ->
      (fun b ->
        match t0 with
        | Fuint _ -> negB (zext (Pervasives.succ 0) b)
        | Fsint _ -> negB (sext (Pervasives.succ 0) b)
        | _ -> b)
    | Unot -> invB
    | Uandr -> (fun b -> (foldr (&&) b1 b) :: [])
    | Uorr -> (fun b -> (foldr (||) b0 b) :: [])
    | Uxorr -> (fun b -> (foldr xorb b0 b) :: [])
    | Uextr (n1, n2) -> extract n1 n2
    | Uhead n -> high n
    | Utail n -> (fun b -> low (subn (size b) n) b)

  (** val binop_bcmp : bcmp -> bits -> bits -> bits **)

  let binop_bcmp o b2 b3 =
    match o with
    | Blt ->
      let bs1 = zext (subn (maxn (size b2) (size b3)) (size b2)) b2 in
      let bs2 = zext (subn (maxn (size b2) (size b3)) (size b3)) b3 in
      (ltB_lsb bs1 bs2) :: []
    | Bleq ->
      let bs1 = zext (subn (maxn (size b2) (size b3)) (size b2)) b2 in
      let bs2 = zext (subn (maxn (size b2) (size b3)) (size b3)) b3 in
      (leB bs1 bs2) :: []
    | Bgt ->
      let bs1 = zext (subn (maxn (size b2) (size b3)) (size b2)) b2 in
      let bs2 = zext (subn (maxn (size b2) (size b3)) (size b3)) b3 in
      (gtB bs1 bs2) :: []
    | Bgeq ->
      let bs1 = zext (subn (maxn (size b2) (size b3)) (size b2)) b2 in
      let bs2 = zext (subn (maxn (size b2) (size b3)) (size b3)) b3 in
      (geB bs1 bs2) :: []
    | Beq ->
      let bs1 = zext (subn (maxn (size b2) (size b3)) (size b2)) b2 in
      let bs2 = zext (subn (maxn (size b2) (size b3)) (size b3)) b3 in
      (eq_op bitseq_eqType (Obj.magic bs1) (Obj.magic bs2)) :: []
    | Bneq ->
      let bs1 = zext (subn (maxn (size b2) (size b3)) (size b2)) b2 in
      let bs2 = zext (subn (maxn (size b2) (size b3)) (size b3)) b3 in
      (negb (eq_op bitseq_eqType (Obj.magic bs1) (Obj.magic bs2))) :: []

  (** val binop_sbcmp : bcmp -> bits -> bits -> bits **)

  let binop_sbcmp o b2 b3 =
    match o with
    | Blt ->
      let bs1 = sext (subn (maxn (size b2) (size b3)) (size b2)) b2 in
      let bs2 = sext (subn (maxn (size b2) (size b3)) (size b3)) b3 in
      (sltB bs1 bs2) :: []
    | Bleq ->
      let bs1 = sext (subn (maxn (size b2) (size b3)) (size b2)) b2 in
      let bs2 = sext (subn (maxn (size b2) (size b3)) (size b3)) b3 in
      (sleB bs1 bs2) :: []
    | Bgt ->
      let bs1 = sext (subn (maxn (size b2) (size b3)) (size b2)) b2 in
      let bs2 = sext (subn (maxn (size b2) (size b3)) (size b3)) b3 in
      (sgtB bs1 bs2) :: []
    | Bgeq ->
      let bs1 = sext (subn (maxn (size b2) (size b3)) (size b2)) b2 in
      let bs2 = sext (subn (maxn (size b2) (size b3)) (size b3)) b3 in
      (sgeB bs1 bs2) :: []
    | Beq ->
      let bs1 = sext (subn (maxn (size b2) (size b3)) (size b2)) b2 in
      let bs2 = sext (subn (maxn (size b2) (size b3)) (size b3)) b3 in
      (eq_op bitseq_eqType (Obj.magic bs1) (Obj.magic bs2)) :: []
    | Bneq ->
      let bs1 = sext (subn (maxn (size b2) (size b3)) (size b2)) b2 in
      let bs2 = sext (subn (maxn (size b2) (size b3)) (size b3)) b3 in
      (negb (eq_op bitseq_eqType (Obj.magic bs1) (Obj.magic bs2))) :: []

  (** val full_adder_ext : bool -> bool list -> bool list -> bool * bits **)

  let full_adder_ext c bs1 bs2 =
    full_adder_zip c (extzip0 bs1 bs2)

  (** val adcB_ext : bool -> bool list -> bool list -> bool * bits **)

  let adcB_ext =
    full_adder_ext

  (** val addB_ext : bool list -> bool list -> bits **)

  let addB_ext bs1 bs2 =
    let (c, r) = adcB_ext false bs1 bs2 in rcons r c

  (** val sbbB_ext : bool -> bool list -> bits -> bool * bits **)

  let sbbB_ext b bs1 bs2 =
    adcB_ext (negb b) bs1 (invB bs2)

  (** val subB_ext : bool list -> bool list -> bits **)

  let subB_ext bs1 bs2 =
    let newl = addn (maxn (size bs1) (size bs2)) (Pervasives.succ 0) in
    let nbs1 = zext (subn newl (size bs1)) bs1 in
    let nbs2 = zext (subn newl (size bs2)) bs2 in snd (sbbB false nbs1 nbs2)

  (** val coq_SadcB_ext : bits -> bits -> bool list **)

  let coq_SadcB_ext ea eb =
    let (c, r) = adcB false ea eb in
    if eq_op bool_eqType (Obj.magic msb ea) (Obj.magic msb eb)
    then rcons r c
    else rcons r (negb c)

  (** val coq_SsbbB_ext : bits -> bits -> bool list **)

  let coq_SsbbB_ext ea eb =
    let (b, r) = sbbB false ea eb in
    if eq_op bool_eqType (Obj.magic msb ea) (Obj.magic msb eb)
    then rcons r b
    else rcons r (negb b)

  (** val coq_Sfull_mul : bits -> bits -> bits **)

  let coq_Sfull_mul bs1 bs2 =
    if (||) (eq_op nat_eqType (Obj.magic size bs1) (Obj.magic 0))
         (eq_op nat_eqType (Obj.magic size bs2) (Obj.magic 0))
    then zeros (addn (size bs1) (size bs2))
    else if (||) (eq_op bitseq_eqType (Obj.magic bs1) (Obj.magic (b0 :: [])))
              (eq_op bitseq_eqType (Obj.magic bs2) (Obj.magic (b0 :: [])))
         then zeros (addn (size bs1) (size bs2))
         else if eq_op bitseq_eqType (Obj.magic bs1)
                   (Obj.magic rcons
                     (zeros (subn (size bs1) (Pervasives.succ 0))) b1)
              then negB
                     (sext (Pervasives.succ 0)
                       (cat (zeros (subn (size bs1) (Pervasives.succ 0))) bs2))
              else if eq_op bitseq_eqType (Obj.magic bs2)
                        (Obj.magic rcons
                          (zeros (subn (size bs2) (Pervasives.succ 0))) b1)
                   then negB
                          (sext (Pervasives.succ 0)
                            (cat
                              (zeros (subn (size bs2) (Pervasives.succ 0)))
                              bs1))
                   else let msb1 = msb bs1 in
                        let msb2 = msb bs2 in
                        if (&&)
                             (eq_op bool_eqType (Obj.magic msb1)
                               (Obj.magic b0))
                             (eq_op bool_eqType (Obj.magic msb2)
                               (Obj.magic b0))
                        then zext (Pervasives.succ (Pervasives.succ 0))
                               (full_mul (dropmsb bs1) (dropmsb bs2))
                        else if (&&)
                                  (eq_op bool_eqType (Obj.magic msb1)
                                    (Obj.magic b1))
                                  (eq_op bool_eqType (Obj.magic msb2)
                                    (Obj.magic b1))
                             then full_mul (negB bs1) (negB bs2)
                             else if (&&)
                                       (eq_op bool_eqType (Obj.magic msb1)
                                         (Obj.magic b0))
                                       (eq_op bool_eqType (Obj.magic msb2)
                                         (Obj.magic b1))
                                  then negB
                                         (sext (Pervasives.succ 0)
                                           (full_mul (dropmsb bs1) (negB bs2)))
                                  else negB
                                         (sext (Pervasives.succ 0)
                                           (full_mul (negB bs1) (dropmsb bs2)))

  (** val ebinop_op : ebinop -> fgtyp -> fgtyp -> bits -> bits -> bits **)

  let ebinop_op o t1 t2 a b =
    match t1 with
    | Fuint w1 ->
      (match t2 with
       | Fuint w2 ->
         let w = maxn w1 w2 in
         let ea = zext (subn w w1) a in
         let eb = zext (subn w w2) b in
         (match o with
          | Badd -> addB_ext a b
          | Bsub -> subB_ext a b
          | Bmul -> full_mul a b
          | Bdiv -> udivB' a b
          | Brem -> low (minn w1 w2) (uremB a b)
          | Bcomp c -> binop_bcmp c a b
          | Bdshl ->
            zext
              (subn
                (subn
                  (Nat.pow (Pervasives.succ (Pervasives.succ 0)) (size b))
                  (Pervasives.succ 0)) (to_nat b)) (cat (zeros (to_nat b)) a)
          | Bdshr -> shrB (to_nat b) a
          | Band -> andB ea eb
          | Bor -> orB ea eb
          | Bxor -> xorB ea eb
          | Bcat -> cat b a)
       | _ -> a)
    | Fsint w1 ->
      (match t2 with
       | Fuint _ ->
         (match o with
          | Bdshl ->
            sext
              (subn
                (subn
                  (Nat.pow (Pervasives.succ (Pervasives.succ 0)) (size b))
                  (Pervasives.succ 0)) (to_nat b)) (cat (zeros (to_nat b)) a)
          | Bdshr -> sarB (to_nat b) a
          | _ -> a)
       | Fsint w2 ->
         let w = maxn w1 w2 in
         let ea = sext (subn w w1) a in
         let eb = sext (subn w w2) b in
         (match o with
          | Badd -> coq_SadcB_ext ea eb
          | Bsub -> coq_SsbbB_ext ea eb
          | Bmul -> coq_Sfull_mul a b
          | Bdiv -> sext (Pervasives.succ 0) (sdivB a b)
          | Brem -> low (minn w1 w2) (sremB a b)
          | Bcomp c -> binop_sbcmp c ea eb
          | Band -> andB ea eb
          | Bor -> orB ea eb
          | Bxor -> xorB ea eb
          | Bcat -> cat b a
          | _ -> a)
       | _ -> a)
    | _ -> a

  (** val type_of_fexpr : fexpr -> TE.env -> fgtyp **)

  let rec type_of_fexpr e te =
    match e with
    | Econst (t0, _) -> t0
    | Ecast (u, e0) ->
      (match u with
       | AsUInt -> Fuint (sizeof_fgtyp (type_of_fexpr e0 te))
       | AsSInt -> Fsint (sizeof_fgtyp (type_of_fexpr e0 te))
       | _ -> Fuint (Pervasives.succ 0))
    | Eprim_unop (u, e0) ->
      (match u with
       | Upad n ->
         if leq (Pervasives.succ n) (sizeof_fgtyp (type_of_fexpr e0 te))
         then type_of_fexpr e0 te
         else (match type_of_fexpr e0 te with
               | Fuint _ -> Fuint n
               | Fsint _ -> Fsint n
               | _ -> TE.deftyp)
       | Ushl n ->
         (match type_of_fexpr e0 te with
          | Fuint w -> Fuint (addn w n)
          | Fsint w -> Fsint (addn w n)
          | _ -> TE.deftyp)
       | Ushr n ->
         (match type_of_fexpr e0 te with
          | Fuint w ->
            if leq (Pervasives.succ n) w
            then Fuint (subn w n)
            else Fuint (Pervasives.succ 0)
          | Fsint w ->
            if leq (Pervasives.succ n) w
            then Fsint (subn w n)
            else Fsint (Pervasives.succ 0)
          | _ -> TE.deftyp)
       | Ucvt ->
         (match type_of_fexpr e0 te with
          | Fuint w -> Fsint (addn w (Pervasives.succ 0))
          | Fsint w -> Fsint w
          | _ -> TE.deftyp)
       | Uneg ->
         (match type_of_fexpr e0 te with
          | Fuint w -> Fsint (addn w (Pervasives.succ 0))
          | Fsint w -> Fsint (addn w (Pervasives.succ 0))
          | _ -> TE.deftyp)
       | Unot ->
         (match type_of_fexpr e0 te with
          | Fuint w -> Fuint w
          | Fsint w -> Fuint w
          | _ -> TE.deftyp)
       | Uextr (n1, n2) -> Fuint (addn (subn n1 n2) (Pervasives.succ 0))
       | Uhead n -> Fuint n
       | Utail n -> Fuint (subn (sizeof_fgtyp (type_of_fexpr e0 te)) n)
       | _ -> Fuint (Pervasives.succ 0))
    | Eprim_binop (b, e1, e2) ->
      (match b with
       | Badd ->
         (match type_of_fexpr e1 te with
          | Fuint s1 ->
            (match type_of_fexpr e2 te with
             | Fuint s2 -> Fuint (addn (maxn s1 s2) (Pervasives.succ 0))
             | _ -> TE.deftyp)
          | Fsint s1 ->
            (match type_of_fexpr e2 te with
             | Fsint s2 -> Fsint (addn (maxn s1 s2) (Pervasives.succ 0))
             | _ -> TE.deftyp)
          | _ -> TE.deftyp)
       | Bsub ->
         (match type_of_fexpr e1 te with
          | Fuint s1 ->
            (match type_of_fexpr e2 te with
             | Fuint s2 -> Fuint (addn (maxn s1 s2) (Pervasives.succ 0))
             | _ -> TE.deftyp)
          | Fsint s1 ->
            (match type_of_fexpr e2 te with
             | Fsint s2 -> Fsint (addn (maxn s1 s2) (Pervasives.succ 0))
             | _ -> TE.deftyp)
          | _ -> TE.deftyp)
       | Bmul ->
         (match type_of_fexpr e1 te with
          | Fuint s1 ->
            (match type_of_fexpr e2 te with
             | Fuint s2 -> Fuint (addn s1 s2)
             | _ -> TE.deftyp)
          | Fsint s1 ->
            (match type_of_fexpr e2 te with
             | Fsint s2 -> Fsint (addn s1 s2)
             | _ -> TE.deftyp)
          | _ -> TE.deftyp)
       | Bdiv ->
         (match type_of_fexpr e1 te with
          | Fuint n -> Fuint n
          | Fsint n -> Fsint (addn n (Pervasives.succ 0))
          | _ -> TE.deftyp)
       | Brem ->
         (match type_of_fexpr e1 te with
          | Fuint s1 ->
            (match type_of_fexpr e2 te with
             | Fuint s2 -> Fuint (minn s1 s2)
             | _ -> TE.deftyp)
          | Fsint s1 ->
            (match type_of_fexpr e2 te with
             | Fsint s2 -> Fsint (minn s1 s2)
             | _ -> TE.deftyp)
          | _ -> TE.deftyp)
       | Bcomp _ -> Fuint (Pervasives.succ 0)
       | Bdshl ->
         (match type_of_fexpr e1 te with
          | Fuint n ->
            Fuint
              (subn
                (addn n
                  (Nat.pow (Pervasives.succ (Pervasives.succ 0))
                    (sizeof_fgtyp (type_of_fexpr e2 te)))) (Pervasives.succ
                0))
          | Fsint n ->
            Fsint
              (subn
                (addn n
                  (Nat.pow (Pervasives.succ (Pervasives.succ 0))
                    (sizeof_fgtyp (type_of_fexpr e2 te)))) (Pervasives.succ
                0))
          | _ -> TE.deftyp)
       | Bdshr ->
         (match type_of_fexpr e1 te with
          | Fuint n -> Fuint n
          | Fsint n -> Fsint n
          | _ -> TE.deftyp)
       | Bcat ->
         (match type_of_fexpr e1 te with
          | Fuint s1 ->
            (match type_of_fexpr e2 te with
             | Fuint s2 -> Fuint (addn s1 s2)
             | _ -> TE.deftyp)
          | Fsint s1 ->
            (match type_of_fexpr e2 te with
             | Fsint s2 -> Fuint (addn s1 s2)
             | _ -> TE.deftyp)
          | _ -> TE.deftyp)
       | _ ->
         (match type_of_fexpr e1 te with
          | Fuint s1 ->
            (match type_of_fexpr e2 te with
             | Fuint s2 -> Fuint (maxn s1 s2)
             | _ -> TE.deftyp)
          | Fsint s1 ->
            (match type_of_fexpr e2 te with
             | Fsint s2 -> Fsint (maxn s1 s2)
             | _ -> TE.deftyp)
          | _ -> TE.deftyp))
    | Emux (_, e1, e2) ->
      let t1 = type_of_fexpr e1 te in
      let t2 = type_of_fexpr e2 te in
      (match t1 with
       | Fuint w1 ->
         (match t2 with
          | Fuint w2 -> Fuint (maxn w1 w2)
          | _ -> TE.deftyp)
       | Fsint w1 ->
         (match t2 with
          | Fsint w2 -> Fsint (maxn w1 w2)
          | _ -> TE.deftyp)
       | _ -> TE.deftyp)
    | Evalidif (_, e0) -> type_of_fexpr e0 te
    | Eref v -> TE.vtyp v te

  (** val eval_fexpr :
      fexpr -> SV.t -> SV.t -> TE.env -> V.t list -> V.t list -> mapdata2etc
      -> mapmem -> boolmap -> SV.t * bits **)

  let rec eval_fexpr e rs s te readerls writerls data2etc memmap read_la =
    match e with
    | Econst (t0, c) ->
      let val0 =
        match t0 with
        | Fuint w1 -> zext (subn w1 (size c)) c
        | Fsint w2 -> sext (subn w2 (size c)) c
        | _ -> c
      in
      (rs, val0)
    | Ecast (u, e0) ->
      (match u with
       | AsClock ->
         let (rs0, val1) =
           eval_fexpr e0 rs s te readerls writerls data2etc memmap read_la
         in
         let val0 = (lsb val1) :: [] in (rs0, val0)
       | AsReset ->
         let (rs0, val1) =
           eval_fexpr e0 rs s te readerls writerls data2etc memmap read_la
         in
         let val0 = (lsb val1) :: [] in (rs0, val0)
       | AsAsync ->
         let (rs0, val1) =
           eval_fexpr e0 rs s te readerls writerls data2etc memmap read_la
         in
         let val0 = (lsb val1) :: [] in (rs0, val0)
       | _ -> eval_fexpr e0 rs s te readerls writerls data2etc memmap read_la)
    | Eprim_unop (u, e0) ->
      let t0 = type_of_fexpr e0 te in
      let (rs0, val1) =
        eval_fexpr e0 rs s te readerls writerls data2etc memmap read_la
      in
      let val0 = eunop_op u t0 val1 in (rs0, val0)
    | Eprim_binop (b, e1, e2) ->
      let (rs0, ve1) =
        eval_fexpr e1 rs s te readerls writerls data2etc memmap read_la
      in
      let (rs1, ve2) =
        eval_fexpr e2 rs0 s te readerls writerls data2etc memmap read_la
      in
      let te1 = type_of_fexpr e1 te in
      let te2 = type_of_fexpr e2 te in
      let val0 = ebinop_op b te1 te2 ve1 ve2 in (rs1, val0)
    | Emux (c, e1, e2) ->
      let t1 = type_of_fexpr e1 te in
      let t2 = type_of_fexpr e2 te in
      let (rs0, valc) =
        eval_fexpr c rs s te readerls writerls data2etc memmap read_la
      in
      let (rs1, val1) =
        eval_fexpr e1 rs0 s te readerls writerls data2etc memmap read_la
      in
      let (rs2, val2) =
        eval_fexpr e2 rs1 s te readerls writerls data2etc memmap read_la
      in
      let val0 =
        match t1 with
        | Fuint w1 ->
          (match t2 with
           | Fuint w2 ->
             if negb (is_zero valc)
             then zext (subn (Pervasives.max w1 w2) w1) val1
             else zext (subn (Pervasives.max w1 w2) w2) val2
           | _ -> [])
        | Fsint w1 ->
          (match t2 with
           | Fsint w2 ->
             if negb (is_zero valc)
             then sext (subn (Pervasives.max w1 w2) w1) val1
             else sext (subn (Pervasives.max w1 w2) w2) val2
           | _ -> [])
        | _ -> []
      in
      (rs2, val0)
    | Evalidif (c, e0) ->
      let (rs0, valc) =
        eval_fexpr c rs s te readerls writerls data2etc memmap read_la
      in
      let (rs1, val1) =
        eval_fexpr e0 rs0 s te readerls writerls data2etc memmap read_la
      in
      let val0 = if negb (is_zero valc) then val1 else [] in (rs1, val0)
    | Eref v ->
      if mylListIn v readerls
      then (match TE.find v data2etc with
            | Some a ->
              let (p, clkvar) = a in
              let (p0, _) = p in
              let (p1, midvar) = p0 in
              let (addrvar, envar) = p1 in
              (match TE.find midvar read_la with
               | Some thisread_la ->
                 let addrval = SV.acc addrvar s in
                 let enval = SV.acc envar s in
                 let clk0val = SV.acc clkvar s in
                 let clkval = SV.acc clkvar rs in
                 let readv =
                   if eq_op bitseq_eqType (Obj.magic enval)
                        (Obj.magic (b0 :: []))
                   then b0 :: []
                   else (match TE.find midvar memmap with
                         | Some b -> memfind addrval b
                         | None -> b0 :: [])
                 in
                 if eq_op bool_eqType (Obj.magic thisread_la)
                      (Obj.magic false)
                 then (rs, readv)
                 else if (&&)
                           (eq_op bitseq_eqType (Obj.magic clk0val)
                             (Obj.magic (b0 :: [])))
                           (eq_op bitseq_eqType (Obj.magic clkval)
                             (Obj.magic (b1 :: [])))
                      then (rs, readv)
                      else (rs, (b0 :: []))
               | None -> (rs, (b0 :: [])))
            | None -> (rs, (b0 :: [])))
      else (rs, (SV.acc v s))

  (** val upd_typenv_fport : fport -> TE.env -> TE.env **)

  let upd_typenv_fport p te =
    match p with
    | Finput (v, t0) -> TE.add v t0 te
    | Foutput (v, t0) -> TE.add v t0 te

  (** val upd_typenv_fports : fport list -> TE.env -> TE.env **)

  let rec upd_typenv_fports ps te =
    match ps with
    | [] -> te
    | h :: tl -> upd_typenv_fports tl (upd_typenv_fport h te)

  (** val upd_typenv_fstmt : fstmt -> TE.env -> SV.t -> TE.env **)

  let upd_typenv_fstmt s te _ =
    match s with
    | Swire (v, t0) -> TE.add v t0 te
    | Sreg r -> TE.add r.rid r.coq_type te
    | Smem m ->
      let te1 =
        fold_left (fun tt tr ->
          let tt0 = TE.add tr.addr (Fuint (Nat.log2 m.depth)) tt in
          let tt1 = TE.add tr.data m.data_type tt0 in
          let tt2 = TE.add tr.en (Fuint (Pervasives.succ 0)) tt1 in
          TE.add tr.clk Fclock tt2) m.reader te
      in
      fold_left (fun tt tr ->
        let tt0 = TE.add tr.addr0 (Fuint (Nat.log2 m.depth)) tt in
        let tt1 = TE.add tr.data0 m.data_type tt0 in
        let tt2 = TE.add tr.en0 (Fuint (Pervasives.succ 0)) tt1 in
        let tt3 = TE.add tr.clk0 Fclock tt2 in
        TE.add tr.mask (Fuint (Pervasives.succ 0)) tt3) m.writer
        (TE.add m.mid Fclock te1)
    | Sinst inst -> upd_typenv_fports inst.iports te
    | Snode (v, e) -> TE.add v (type_of_fexpr e te) te
    | Sfcnct (v, e2) -> TE.add v (type_of_fexpr e2 te) te
    | Sinvalid v -> TE.add v (TE.vtyp v te) te
    | _ -> te

  (** val upd_typenv_fstmts : fstmt list -> TE.env -> SV.t -> TE.env **)

  let rec upd_typenv_fstmts ss te s =
    match ss with
    | [] -> te
    | h :: tl -> upd_typenv_fstmts tl (upd_typenv_fstmt h te s) s

  (** val eval_noninst_fstmt :
      fstmt -> SV.t -> SV.t -> TE.env -> V.t list -> V.t list -> mapdata2etc
      -> mapmem -> boolmap -> (SV.t * SV.t) * mapmem **)

  let eval_noninst_fstmt st rs s te readerls writerls data2etc memmap read_la =
    match st with
    | Swire (v, t0) -> ((rs, (SV.upd v (zeros (sizeof_fgtyp t0)) s)), memmap)
    | Sreg r ->
      if eq_op bitseq_eqType (Obj.magic SV.acc r.rid rs) (Obj.magic [])
      then let rs0 = SV.upd r.rid (zeros (sizeof_fgtyp r.coq_type)) rs in
           let s0 = SV.upd r.rid (zeros (sizeof_fgtyp r.coq_type)) s in
           (match r.reset with
            | NRst -> ((rs0, s0), memmap)
            | Rst (e1, e2) ->
              let te1 = type_of_fexpr e1 te in
              let (_, ve1) =
                eval_fexpr e1 rs s0 te readerls writerls data2etc memmap
                  read_la
              in
              let (_, ve2) =
                eval_fexpr e2 rs s0 te readerls writerls data2etc memmap
                  read_la
              in
              if is_zero ve1
              then ((rs0, s0), memmap)
              else (match te1 with
                    | Fuint n ->
                      ((fun fO fS n -> if n=0 then fO () else fS (n-1))
                         (fun _ -> ((rs0, s0), memmap))
                         (fun n0 ->
                         (fun fO fS n -> if n=0 then fO () else fS (n-1))
                           (fun _ -> (((SV.upd r.rid ve2 rs0), s0),
                           memmap))
                           (fun _ -> ((rs0, s0), memmap))
                           n0)
                         n)
                    | Fasyncreset ->
                      (((SV.upd r.rid ve2 rs0), (SV.upd r.rid ve2 s0)),
                        memmap)
                    | _ -> ((rs0, s0), memmap)))
      else let s0 = SV.upd r.rid (SV.acc r.rid rs) s in
           (match r.reset with
            | NRst -> ((rs, s0), memmap)
            | Rst (e1, e2) ->
              let te1 = type_of_fexpr e1 te in
              let (_, ve1) =
                eval_fexpr e1 rs s0 te readerls writerls data2etc memmap
                  read_la
              in
              let (_, ve2) =
                eval_fexpr e2 rs s0 te readerls writerls data2etc memmap
                  read_la
              in
              if is_zero ve1
              then ((rs, s0), memmap)
              else (match te1 with
                    | Fuint n ->
                      ((fun fO fS n -> if n=0 then fO () else fS (n-1))
                         (fun _ -> ((rs, s0), memmap))
                         (fun n0 ->
                         (fun fO fS n -> if n=0 then fO () else fS (n-1))
                           (fun _ -> (((SV.upd r.rid ve2 rs), s0),
                           memmap))
                           (fun _ -> ((rs, s0), memmap))
                           n0)
                         n)
                    | Fasyncreset ->
                      (((SV.upd r.rid ve2 rs), (SV.upd r.rid ve2 s0)), memmap)
                    | _ -> ((rs, s0), memmap)))
    | Snode (v, e) ->
      let (rs0, ve) =
        eval_fexpr e rs s te readerls writerls data2etc memmap read_la
      in
      ((rs0, (SV.upd v ve s)), memmap)
    | Sfcnct (v, e2) ->
      let (rs0, newv) =
        eval_fexpr e2 rs s te readerls writerls data2etc memmap read_la
      in
      let memmap0 =
        if mylListIn v writerls
        then (match TE.find v data2etc with
              | Some a ->
                let (p, clkvar) = a in
                let (p0, maskvar) = p in
                let (p1, midvar) = p0 in
                let (addrvar, envar) = p1 in
                (match TE.find midvar memmap with
                 | Some b ->
                   let maskval = SV.acc maskvar s in
                   let addrval = SV.acc addrvar s in
                   let enval = SV.acc envar s in
                   let clkval = SV.acc clkvar rs in
                   let clk0val = SV.acc clkvar s in
                   if (&&)
                        ((&&)
                          (eq_op bitseq_eqType (Obj.magic enval)
                            (Obj.magic (b1 :: [])))
                          (eq_op bitseq_eqType (Obj.magic clk0val)
                            (Obj.magic (b0 :: []))))
                        (eq_op bitseq_eqType (Obj.magic clkval)
                          (Obj.magic (b1 :: [])))
                   then if eq_op bitseq_eqType (Obj.magic maskval)
                             (Obj.magic (b1 :: []))
                        then TE.add midvar (memupd addrval (SV.acc v s) b)
                               memmap
                        else TE.add midvar (memupd addrval (b0 :: []) b)
                               memmap
                   else memmap
                 | None -> memmap)
              | None -> memmap)
        else memmap
      in
      if eq_op bitseq_eqType (Obj.magic SV.acc v rs0) (Obj.magic [])
      then ((rs0, (SV.upd v newv s)), memmap0)
      else (((SV.upd v newv rs0), s), memmap0)
    | Sinvalid v ->
      let tv = TE.vtyp v te in
      ((rs, (SV.upd v (zeros (sizeof_fgtyp tv)) s)), memmap)
    | _ -> ((rs, s), memmap)

  (** val eval_fstmt :
      fstmt -> SV.t -> SV.t -> TE.env -> V.t list -> V.t list -> mapdata2etc
      -> mapmem -> boolmap -> V.t list -> maptuple -> mapfstmt -> mapterss ->
      allboolmap -> mapls -> mvar -> mapvar -> mapls -> mapls -> map2etc ->
      mapls -> mmaptuple -> mmapvar -> int ->
      ((SV.t * SV.t) * mapmem) * mapterss **)

  let rec eval_fstmt st rs s te readerls writerls data2etc memmap read_la finstoutl finstoutm ffmodsmap fterss fread_la finstin finstinmap finstoutmap rl wl alldata2etc allfinstoutl allfinstoutm allfinstportmap iternum =
    let te1 = upd_typenv_fstmt st te s in
    ((fun fO fS n -> if n=0 then fO () else fS (n-1))
       (fun _ ->
       ((eval_noninst_fstmt st rs s te1 readerls writerls data2etc memmap
          read_la), fterss))
       (fun iternum0 ->
       match st with
       | Sinst inst ->
         let v = inst.iid in
         (match TE.find inst.imid ffmodsmap with
          | Some mst ->
            (match TE.find inst.iid fterss with
             | Some aa ->
               let (p, mem0) = aa in
               let (p0, s0) = p in
               let (te0, rs0) = p0 in
               (match TE.find inst.imid finstin with
                | Some a2 ->
                  (match TE.find v finstinmap with
                   | Some a3 ->
                     let s1 = upd_inner s s0 a2 a3 in
                     let readerls0 =
                       match TE.find inst.imid rl with
                       | Some a -> a
                       | None -> []
                     in
                     let writerls0 =
                       match TE.find inst.imid wl with
                       | Some a -> a
                       | None -> []
                     in
                     let finstoutl0 =
                       match TE.find inst.imid allfinstoutl with
                       | Some a -> a
                       | None -> []
                     in
                     (match TE.find inst.imid alldata2etc with
                      | Some a ->
                        (match TE.find inst.imid allfinstoutm with
                         | Some a0 ->
                           (match TE.find inst.imid allfinstportmap with
                            | Some a1 ->
                              let (finstinmap0, finstoutmap0) = a1 in
                              (match TE.find inst.imid fread_la with
                               | Some a4 ->
                                 let (p1, fterss2) =
                                   fold_left (fun pat tempst ->
                                     let (y, tfterss) = pat in
                                     let (y0, _) = y in
                                     let (trs, ts) = y0 in
                                     eval_fstmt tempst trs ts te0 readerls0
                                       writerls0 a mem0 a4 finstoutl0 a0
                                       ffmodsmap tfterss fread_la finstin
                                       finstinmap0 finstoutmap0 rl wl
                                       alldata2etc allfinstoutl allfinstoutm
                                       allfinstportmap iternum0) (rev mst)
                                     (((rs0, s1), mem0), fterss)
                                 in
                                 let (p2, memmap2) = p1 in
                                 let (rs2, s2) = p2 in
                                 (((rs, s), memmap),
                                 (TE.add v (((te0, rs2), s2), memmap2)
                                   fterss2))
                               | None ->
                                 ((((SV.upd v
                                      (b1 :: (b1 :: (b1 :: (b1 :: (b1 :: [])))))
                                      rs), s), memmap), fterss))
                            | None ->
                              ((((SV.upd v
                                   (b1 :: (b1 :: (b1 :: (b1 :: (b1 :: [])))))
                                   rs), s), memmap), fterss))
                         | None ->
                           ((((SV.upd v (b1 :: (b1 :: (b1 :: (b1 :: [])))) rs),
                             s), memmap), fterss))
                      | None ->
                        ((((SV.upd v (b1 :: (b1 :: (b1 :: []))) rs), s),
                          memmap), fterss))
                   | None -> (((rs, s), memmap), fterss))
                | None ->
                  ((((SV.upd v (b1 :: (b1 :: (b1 :: []))) rs), s), memmap),
                    fterss))
             | None ->
               ((((SV.upd v (b1 :: (b1 :: [])) rs), s), memmap), fterss))
          | None -> ((((SV.upd v (b1 :: []) rs), s), memmap), fterss))
       | Sfcnct (v, e2) ->
         let (newrs, newv) =
           match e2 with
           | Eref v1 ->
             if mylListIn v1 finstoutl
             then let v0 =
                    match TE.find v1 finstoutm with
                    | Some p ->
                      let (a4, a0) = p in
                      (match TE.find a4 ffmodsmap with
                       | Some mst ->
                         (match TE.find a0 fterss with
                          | Some aa ->
                            let (p0, mem0) = aa in
                            let (p1, s0) = p0 in
                            let (te0, rs0) = p1 in
                            (match TE.find a4 finstin with
                             | Some a2 ->
                               (match TE.find a0 finstinmap with
                                | Some a5 ->
                                  let s1 = upd_inner s s0 a2 a5 in
                                  let s2 =
                                    let readerls0 =
                                      match TE.find a4 rl with
                                      | Some a -> a
                                      | None -> []
                                    in
                                    let writerls0 =
                                      match TE.find a4 wl with
                                      | Some a -> a
                                      | None -> []
                                    in
                                    let finstoutl0 =
                                      match TE.find a4 allfinstoutl with
                                      | Some a -> a
                                      | None -> []
                                    in
                                    (match TE.find a4 alldata2etc with
                                     | Some a ->
                                       (match TE.find a4 fread_la with
                                        | Some a1 ->
                                          (match TE.find a4 allfinstoutm with
                                           | Some a3 ->
                                             (match TE.find a4 allfinstportmap with
                                              | Some a6 ->
                                                let (finstinmap0, finstoutmap0) =
                                                  a6
                                                in
                                                let (p2, _) =
                                                  fold_left
                                                    (fun pat tempst ->
                                                    let (y, tfterss) = pat in
                                                    let (y0, _) = y in
                                                    let (trs, ts) = y0 in
                                                    eval_fstmt tempst trs ts
                                                      te0 readerls0 writerls0
                                                      a mem0 a1 finstoutl0 a3
                                                      ffmodsmap tfterss
                                                      fread_la finstin
                                                      finstinmap0
                                                      finstoutmap0 rl wl
                                                      alldata2etc
                                                      allfinstoutl
                                                      allfinstoutm
                                                      allfinstportmap iternum0)
                                                    (rev mst) (((rs0, s1),
                                                    mem0), fterss)
                                                in
                                                let (p3, _) = p2 in
                                                let (_, s2) = p3 in s2
                                              | None -> s)
                                           | None -> s)
                                        | None -> s)
                                     | None -> s)
                                  in
                                  (match TE.find v1 finstoutmap with
                                   | Some a3 -> SV.acc a3 s2
                                   | None -> [])
                                | None -> b1 :: (b1 :: (b1 :: (b1 :: []))))
                             | None -> b1 :: (b1 :: (b1 :: (b1 :: []))))
                          | None -> b1 :: (b1 :: (b1 :: [])))
                       | None -> b1 :: (b1 :: []))
                    | None -> b1 :: []
                  in
                  (rs, v0)
             else eval_fexpr e2 rs s te1 readerls writerls data2etc memmap
                    read_la
           | _ ->
             eval_fexpr e2 rs s te1 readerls writerls data2etc memmap read_la
         in
         let memmap0 =
           if mylListIn v writerls
           then (match TE.find v data2etc with
                 | Some a ->
                   let (p, clkvar) = a in
                   let (p0, maskvar) = p in
                   let (p1, midvar) = p0 in
                   let (addrvar, envar) = p1 in
                   (match TE.find midvar memmap with
                    | Some b ->
                      let maskval = SV.acc maskvar s in
                      let addrval = SV.acc addrvar s in
                      let clkval = SV.acc clkvar rs in
                      let clk0val = SV.acc clkvar s in
                      let enval = SV.acc envar s in
                      if (&&)
                           ((&&)
                             (eq_op bitseq_eqType (Obj.magic enval)
                               (Obj.magic (b1 :: [])))
                             (eq_op bitseq_eqType (Obj.magic clk0val)
                               (Obj.magic (b0 :: []))))
                           (eq_op bitseq_eqType (Obj.magic clkval)
                             (Obj.magic (b1 :: [])))
                      then if eq_op bitseq_eqType (Obj.magic maskval)
                                (Obj.magic (b1 :: []))
                           then TE.add midvar (memupd addrval (SV.acc v s) b)
                                  memmap
                           else TE.add midvar (memupd addrval (b0 :: []) b)
                                  memmap
                      else memmap
                    | None -> memmap)
                 | None -> memmap)
           else memmap
         in
         if eq_op bitseq_eqType (Obj.magic SV.acc v newrs) (Obj.magic [])
         then (((newrs, (SV.upd v newv s)), memmap0), fterss)
         else ((((SV.upd v newv newrs), s), memmap0), fterss)
       | _ ->
         ((eval_noninst_fstmt st rs s te1 readerls writerls data2etc memmap
            read_la), fterss))
       iternum)

  (** val eval_fstmts :
      fstmt list -> SV.t -> SV.t -> TE.env -> V.t list -> V.t list ->
      mapdata2etc -> mapmem -> boolmap -> V.t list -> maptuple -> mapfstmt ->
      mapterss -> allboolmap -> mapls -> mvar -> mapvar -> mapls -> mapls ->
      map2etc -> mapls -> mmaptuple -> mmapvar -> int ->
      ((SV.t * SV.t) * mapmem) * mapterss **)

  let rec eval_fstmts st rs s te readerls writerls data2etc memmap read_la finstoutl finstoutm ffmodsmap fterss fread_la finstin finstinmap finstoutmap rl wl alldata2etc allfinstoutl allfinstoutm allfinstportmap iternum =
    match st with
    | [] -> (((rs, s), memmap), fterss)
    | h :: tl ->
      let te1 = upd_typenv_fstmt h te s in
      let (p, fterss0) =
        eval_fstmt h rs s te1 readerls writerls data2etc memmap read_la
          finstoutl finstoutm ffmodsmap fterss fread_la finstin finstinmap
          finstoutmap rl wl alldata2etc allfinstoutl allfinstoutm
          allfinstportmap iternum
      in
      let (p0, memmap0) = p in
      let (rs1, s1) = p0 in
      eval_fstmts tl rs1 s1 te1 readerls writerls data2etc memmap0 read_la
        finstoutl finstoutm ffmodsmap fterss0 fread_la finstin finstinmap
        finstoutmap rl wl alldata2etc allfinstoutl allfinstoutm
        allfinstportmap iternum

  (** val upd_argulist : SV.t -> mapioin -> TE.key list -> int -> SV.t **)

  let rec upd_argulist s io_in name ind =
    match name with
    | [] -> s
    | h :: t0 ->
      let tin = match TE.find h io_in with
                | Some a -> a
                | None -> [] in
      upd_argulist (SV.upd h (nth ind tin (b0 :: [])) s) io_in t0 ind

  (** val myupdateo : SV.t -> bits list TE.t -> V.t -> bits list TE.t **)

  let myupdateo s2 omap l =
    let newv = SV.acc l s2 in
    let newl =
      match TE.find l omap with
      | Some a -> List0.rev (newv :: (List0.rev a))
      | None -> (b1 :: []) :: []
    in
    TE.add l newl omap

  (** val eval_module :
      V.t -> SV.t -> SV.t -> TE.env -> mapioin -> V.t list -> mapls -> mapls
      -> map2etc -> mapmem -> mapls -> mmaptuple -> mapfstmt -> mapterss ->
      allboolmap -> mapls -> mmapvar -> int ->
      (((SV.t * SV.t) * mapmem) * mapterss) * mapioin **)

  let eval_module v rs s te io_in ols readerls writerls data2etc memmap finstoutl finstoutm ffmodsmap fterss fread_la finstin finstportmap iternum =
    match TE.find v ffmodsmap with
    | Some st ->
      let readerls0 = match TE.find v readerls with
                      | Some a -> a
                      | None -> []
      in
      let writerls0 = match TE.find v writerls with
                      | Some a -> a
                      | None -> []
      in
      let finstoutl0 = match TE.find v finstoutl with
                       | Some a -> a
                       | None -> []
      in
      (match TE.find v data2etc with
       | Some a ->
         (match TE.find v fread_la with
          | Some read_la ->
            (match TE.find v finstoutm with
             | Some a0 ->
               (match TE.find v finstportmap with
                | Some a1 ->
                  let (finstinmap0, finstoutmap0) = a1 in
                  let (p, fterss2) =
                    eval_fstmts (rev st) rs s te readerls0 writerls0 a memmap
                      read_la finstoutl0 a0 ffmodsmap fterss fread_la finstin
                      finstinmap0 finstoutmap0 readerls writerls data2etc
                      finstoutl finstoutm finstportmap iternum
                  in
                  let (p0, memmap2) = p in
                  let (rs2, s2) = p0 in
                  let io_in2 = fold_left (myupdateo s2) ols io_in in
                  ((((rs2, s2), memmap2), fterss2), io_in2)
                | None -> ((((rs, s), memmap), fterss), io_in))
             | None -> ((((rs, s), memmap), fterss), io_in))
          | None -> ((((rs, s), memmap), fterss), io_in))
       | None -> ((((rs, s), memmap), fterss), io_in))
    | None -> ((((rs, s), memmap), fterss), io_in)

  (** val run_module0 :
      V.t -> SV.t -> SV.t -> TE.env -> mapioin -> TE.key list -> V.t list ->
      mapls -> mapls -> map2etc -> mapmem -> int -> int -> mapls -> mmaptuple
      -> mapfstmt -> mapterss -> allboolmap -> mapls -> mmapvar -> int ->
      (((SV.t * SV.t) * mapmem) * mapterss) * mapioin **)

  let rec run_module0 mainmod rs s te io_in name ols readerls writerls data2etc memmap clk_num len finstoutl finstoutm ffmodsmap fterss fread_la finstin finstportmap iternum =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> ((((rs, s), memmap), fterss), io_in))
      (fun m ->
      let n = subn len (Pervasives.succ m) in
      let s1 = upd_argulist s io_in name n in
      let (p, io_in0) =
        eval_module mainmod rs s1 te io_in ols readerls writerls data2etc
          memmap finstoutl finstoutm ffmodsmap fterss fread_la finstin
          finstportmap iternum
      in
      let (p0, fterss0) = p in
      let (p1, memmap0) = p0 in
      let (rs2, s2) = p1 in
      run_module0 mainmod rs2 s2 te io_in0 name ols readerls writerls
        data2etc memmap0 m len finstoutl finstoutm ffmodsmap fterss0 fread_la
        finstin finstportmap iternum)
      clk_num

  (** val expr2varlist : fexpr -> V.t list -> V.t list **)

  let rec expr2varlist expr ls =
    match expr with
    | Econst (_, _) -> ls
    | Ecast (_, e) -> expr2varlist e ls
    | Eprim_unop (_, e1) -> expr2varlist e1 ls
    | Eprim_binop (_, e1, e2) -> expr2varlist e2 (expr2varlist e1 ls)
    | Emux (e1, e2, e3) ->
      expr2varlist e3 (expr2varlist e2 (expr2varlist e1 ls))
    | Evalidif (e1, e2) -> expr2varlist e2 (expr2varlist e1 ls)
    | Eref v -> v :: ls

  (** val findreg : V.t list -> V.t list -> fstmt -> V.t list * V.t list **)

  let findreg ls roots = function
  | Sreg r -> ((r.rid :: ls), (r.rid :: roots))
  | Snode (v, e) ->
    if eq_op (seq_eqType V.coq_T) (Obj.magic expr2varlist e []) (Obj.magic [])
    then (ls, (v :: roots))
    else (ls, roots)
  | Sfcnct (v1, e2) ->
    if eq_op (seq_eqType V.coq_T) (Obj.magic expr2varlist e2 [])
         (Obj.magic [])
    then (ls, (v1 :: roots))
    else (ls, roots)
  | Sinvalid v -> (ls, (v :: roots))
  | _ -> (ls, roots)

  (** val findallvar : V.t list -> fstmt -> V.t list **)

  let findallvar ls = function
  | Swire (v, _) -> v :: ls
  | Sreg r -> r.rid :: ls
  | Smem m ->
    let ls0 = fold_left (fun _ tr -> tr.addr :: ls) m.reader ls in
    fold_left (fun _ tr -> tr.addr0 :: ls) m.writer ls0
  | Sinst inst ->
    fold_left (fun tl tp ->
      match tp with
      | Finput (v, _) -> v :: tl
      | Foutput (v, _) -> v :: tl) inst.iports ls
  | Snode (v, _) -> v :: ls
  | Sinvalid v -> v :: ls
  | _ -> ls

  (** val def_known_reg_order :
      V.t list -> fstmt list -> fstmt list -> fstmt list -> fstmt -> (fstmt
      list * fstmt list) * fstmt list **)

  let def_known_reg_order regls defls knownls regstmtls st = match st with
  | Sskip -> ((defls, (st :: knownls)), regstmtls)
  | Sinst _ -> ((defls, knownls), (st :: regstmtls))
  | Snode (_, e) ->
    if eq_op (seq_eqType V.coq_T) (Obj.magic expr2varlist e []) (Obj.magic [])
    then ((defls, (st :: knownls)), regstmtls)
    else ((defls, knownls), regstmtls)
  | Sfcnct (v1, e2) ->
    if eq_op (seq_eqType V.coq_T) (Obj.magic expr2varlist e2 [])
         (Obj.magic [])
    then ((defls, (st :: knownls)), regstmtls)
    else if varIn v1 regls
         then ((defls, knownls), (st :: regstmtls))
         else ((defls, knownls), regstmtls)
  | Sinvalid _ -> ((defls, (st :: knownls)), regstmtls)
  | Swhen (_, _, _) -> ((defls, knownls), regstmtls)
  | Sstop (_, _, _) -> ((defls, knownls), regstmtls)
  | _ -> (((st :: defls), knownls), regstmtls)

  (** val known_reg_orders :
      fstmt list -> (fstmt list * fstmt list) * fstmt list **)

  let known_reg_orders oldstmts =
    let (regls, _) =
      fold_left (fun pat tst -> let (ls1, ls2) = pat in findreg ls1 ls2 tst)
        oldstmts ([], [])
    in
    let (p, revregstmtls) =
      fold_left (fun pat st ->
        let (y, templ3) = pat in
        let (templ1, templ2) = y in
        def_known_reg_order regls templ1 templ2 templ3 st) oldstmts (([],
        []), [])
    in
    let (revdefls, revknownls) = p in
    let knownls = List0.rev revknownls in
    let regstmtls = List0.rev revregstmtls in
    let defls = List0.rev revdefls in ((defls, knownls), regstmtls)

  (** val addreader2g : g -> freader_port -> g **)

  let addreader2g tempg tempr =
    let g0 = updg tempr.addr (tempr.data :: (findg tempr.addr tempg)) tempg in
    let g1 = updg tempr.en (tempr.data :: (findg tempr.en g0)) g0 in
    updg tempr.clk (tempr.data :: (findg tempr.clk g1)) g1

  (** val addwriter2g : g -> fwriter_port -> g **)

  let addwriter2g tempg tempw =
    let g0 = updg tempw.addr0 (tempw.data0 :: (findg tempw.addr0 tempg)) tempg
    in
    let g1 = updg tempw.en0 (tempw.data0 :: (findg tempw.en0 g0)) g0 in
    let g2 = updg tempw.clk0 (tempw.data0 :: (findg tempw.clk0 g1)) g1 in
    updg tempw.mask (tempw.data0 :: (findg tempw.mask g2)) g2

  (** val addnewruw2g0 : freader_port list -> g -> fwriter_port -> g **)

  let addnewruw2g0 temprl tempg tempw =
    fold_left (fun tg tempr ->
      updg tempw.data0 (tempr.data :: (findg tempw.data0 tg)) tg) temprl tempg

  (** val addnewruw2g1 : freader_port list -> g -> fwriter_port -> g **)

  let addnewruw2g1 temprl tempg tempw =
    fold_left (fun tg tempr ->
      updg tempr.data (tempw.data0 :: (findg tempr.data tg)) tg) temprl tempg

  (** val inst_inoutlist : fport list -> V.t list * V.t list **)

  let inst_inoutlist pl =
    fold_left (fun pat tempp ->
      let (il, ol) = pat in
      (match tempp with
       | Finput (v, _) -> ((v :: il), ol)
       | Foutput (v, _) -> (il, (v :: ol)))) pl ([], [])

  (** val dfs : g -> int -> V.t list -> V.t -> V.t list **)

  let rec dfs fing n v x =
    if varIn x v
    then v
    else ((fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ -> v)
            (fun n' -> foldl (dfs fing n') (x :: v) (fing x))
            n)

  (** val dfs_path : g -> int -> V.t -> V.t -> bool **)

  let dfs_path fing n x y =
    let xchildren = dfs fing n [] x in varIn y xchildren

  (** val add_regedge : V.t list -> g -> fstmt -> g **)

  let add_regedge regls fing = function
  | Sfcnct (v1, e2) ->
    (match e2 with
     | Econst (_, _) -> fing
     | _ ->
       if varIn v1 regls
       then let preset = expr2varlist e2 [] in
            fold_left (fun tempg tempv ->
              updg tempv (v1 :: (findg tempv tempg)) tempg) preset fing
       else fing)
  | _ -> fing

  (** val buildg :
      V.t list -> fmap -> mapvar -> mapvar -> mapg -> g -> var2stmtmap ->
      fstmt -> g * var2stmtmap **)

  let buildg regls flagmap inportsmap outportsmap knowng fing var2stmt st = match st with
  | Smem m ->
    let readerls = m.reader in
    let newg0 = fold_left addreader2g readerls fing in
    let writerls = m.writer in
    let newg1 = fold_left addwriter2g writerls newg0 in
    let newg =
      match m.read_write with
      | Coq_old -> fold_left (addnewruw2g1 readerls) writerls newg1
      | Coq_new -> fold_left (addnewruw2g0 readerls) writerls newg1
      | Coq_undefined -> newg1
    in
    (newg, var2stmt)
  | Sinst inst ->
    let instmod = inst.imid in
    let instg =
      match TE.find instmod knowng with
      | Some tempg -> tempg
      | None -> emptyg
    in
    let (inports, outports) = inst_inoutlist inst.iports in
    let instlen =
      match TE.find instmod flagmap with
      | Some tempg -> tempg
      | None -> 0
    in
    let newg =
      fold_left (fun tempg inp ->
        match TE.find inp inportsmap with
        | Some ininp ->
          fold_left (fun tempg0 outp ->
            match TE.find outp outportsmap with
            | Some inoutp ->
              if dfs_path instg instlen ininp inoutp
              then updg inp (outp :: (findg inp tempg0)) tempg0
              else tempg0
            | None -> tempg0) outports tempg
        | None -> tempg) inports fing
    in
    (newg, var2stmt)
  | Snode (v, e) ->
    let preset = expr2varlist e [] in
    if eq_op (seq_eqType V.coq_T) (Obj.magic preset) (Obj.magic [])
    then (fing, var2stmt)
    else let newg =
           fold_left (fun tempg tempv ->
             updg tempv (v :: (findg tempv tempg)) tempg) preset fing
         in
         (newg, (TE.add v st var2stmt))
  | Sfcnct (v1, e2) ->
    let preset = expr2varlist e2 [] in
    if eq_op (seq_eqType V.coq_T) (Obj.magic preset) (Obj.magic [])
    then (fing, var2stmt)
    else if varIn v1 regls
         then (fing, var2stmt)
         else let newg =
                fold_left (fun tempg tempv ->
                  updg tempv (v1 :: (findg tempv tempg)) tempg) preset fing
              in
              (newg, (TE.add v1 st var2stmt))
  | _ -> (fing, var2stmt)

  (** val findkinstps : mapls -> mvar -> V.t list -> fstmt -> V.t list **)

  let findkinstps kpsmap finsti2e_outmap ls = function
  | Sinst inst ->
    let mv = inst.imid in
    let iv = inst.iid in
    (match TE.find mv kpsmap with
     | Some kps ->
       (match TE.find iv finsti2e_outmap with
        | Some outmap ->
          let exkps =
            fold_left (fun tls p ->
              match TE.find p outmap with
              | Some exp -> exp :: tls
              | None -> tls) kps []
          in
          cat ls exkps
        | None -> ls)
     | None -> ls)
  | _ -> ls

  (** val topo_tree :
      g -> int -> V.t list -> V.t list option -> V.t -> V.t list option **)

  let rec topo_tree fing n gray_nodes already_found root =
    match already_found with
    | Some already_found' ->
      ((fun fO fS n -> if n=0 then fO () else fS (n-1))
         (fun _ -> None)
         (fun n' ->
         if in_mem root (mem (seq_predType V.coq_T) (Obj.magic gray_nodes))
         then Some (root :: gray_nodes)
         else if in_mem root
                   (mem (seq_predType V.coq_T) (Obj.magic already_found'))
              then already_found
              else (match foldl (topo_tree fing n' (root :: gray_nodes))
                            already_found (fing root) with
                    | Some result -> Some (root :: result)
                    | None -> None))
         n)
    | None -> already_found

  (** val topo_sort : g -> int -> V.t list -> V.t list option **)

  let topo_sort fing n vertices =
    foldl (topo_tree fing n []) (Some []) vertices

  (** val modname2g :
      V.t list -> fmap -> mapfstmt -> mmvar -> mvar -> mapls -> mapls ->
      mapls -> mapg -> mapfstmt -> mapls -> mapls ->
      ((mapg * mapfstmt) * mapls) * mapls **)

  let rec modname2g modorder flagmap oldstmtsmap instportsmap finsti2e_outmap inpsmap outpsmap instoutl fingmap newstmtsmap newvarmap kpsmap =
    match modorder with
    | [] -> (((fingmap, newstmtsmap), newvarmap), kpsmap)
    | h :: t0 ->
      let tempstmts =
        match TE.find h oldstmtsmap with
        | Some tstmts -> tstmts
        | None -> []
      in
      let (inportsmap, outportsmap) =
        match TE.find h instportsmap with
        | Some tempm -> tempm
        | None -> (TE.empty, TE.empty)
      in
      let inps =
        match TE.find h inpsmap with
        | Some tstmts -> tstmts
        | None -> []
      in
      let outps =
        match TE.find h outpsmap with
        | Some tstmts -> tstmts
        | None -> []
      in
      let instoutps =
        match TE.find h instoutl with
        | Some tstmts -> tstmts
        | None -> []
      in
      let len = match TE.find h flagmap with
                | Some n -> n
                | None -> 0 in
      let (regls, roots) =
        fold_left (fun pat tst ->
          let (ls1, ls2) = pat in findreg ls1 ls2 tst) tempstmts ([], [])
      in
      let kinstps =
        fold_left (fun ls tst -> findkinstps kpsmap finsti2e_outmap ls tst)
          tempstmts []
      in
      let (newg, var2stmt) =
        fold_left (fun pat tempst ->
          let (tempg, tempm) = pat in
          buildg regls flagmap inportsmap outportsmap fingmap tempg tempm
            tempst) tempstmts (emptyg, TE.empty)
      in
      let kps =
        match topo_sort newg len roots with
        | Some tseq ->
          fold_left (fun ls op -> if varIn op tseq then op :: ls else ls)
            outps []
        | None -> []
      in
      (match topo_sort newg len (cat inps (cat roots kinstps)) with
       | Some tseq ->
         let newstorder =
           List0.map (fun tv ->
             match TE.find tv var2stmt with
             | Some tempst -> tempst
             | None ->
               if varIn tv instoutps then Sfcnct (tv, (Eref tv)) else sskip)
             tseq
         in
         let p = (((TE.add h newg fingmap),
           (TE.add h newstorder newstmtsmap)), (TE.add h tseq newvarmap))
         in
         let kpsmap0 = TE.add h kps kpsmap in
         let (p0, newvarmap0) = p in
         let (fingmap0, newstmtsmap0) = p0 in
         modname2g t0 flagmap oldstmtsmap instportsmap finsti2e_outmap
           inpsmap outpsmap instoutl fingmap0 newstmtsmap0 newvarmap0 kpsmap0
       | None ->
         ((((TE.add h newg fingmap), (TE.add h [] newstmtsmap)),
           (TE.add h [] newvarmap)), (TE.add h [] kpsmap)))

  (** val reorder :
      V.t list -> fmap -> mapfstmt -> mmvar -> mvar -> mapls -> mapls ->
      mapls -> mapfstmt * mapls **)

  let reorder modorder flagmap oldstmtsmap instportsmap finsti2e_outmap inpsmap outpsmap instoutl =
    let (p, regstmtmap) =
      fold_left (fun pat modname ->
        let (y, tempm2) = pat in
        let (tempm0, tempm1) = y in
        let tempstmts =
          match TE.find modname oldstmtsmap with
          | Some tstmts -> tstmts
          | None -> []
        in
        let (p, newreg) = known_reg_orders tempstmts in
        let (newdefls, newknown) = p in
        (((TE.add modname newdefls tempm0),
        (TE.add modname newknown tempm1)), (TE.add modname newreg tempm2)))
        modorder ((TE.empty, TE.empty), TE.empty)
    in
    let (defmap, knownmap) = p in
    let (p0, _) =
      modname2g modorder flagmap oldstmtsmap instportsmap finsti2e_outmap
        inpsmap outpsmap instoutl TE.empty TE.empty TE.empty TE.empty
    in
    let (p1, varmap) = p0 in
    let (_, orderedmap) = p1 in
    let newstmtsmap =
      fold_left (fun tmap modname ->
        match TE.find modname defmap with
        | Some tdefs ->
          (match TE.find modname regstmtmap with
           | Some tregs ->
             (match TE.find modname orderedmap with
              | Some tordered ->
                (match TE.find modname knownmap with
                 | Some tknown ->
                   let allordered =
                     cat tdefs (cat tknown (cat tordered tregs))
                   in
                   TE.add modname (rev allordered) tmap
                 | None -> tmap)
              | None -> tmap)
           | None -> tmap)
        | None -> tmap) modorder TE.empty
    in
    (newstmtsmap, varmap)

  (** val run_module :
      V.t list -> fmap -> mmvar -> mvar -> V.t -> SV.t -> SV.t -> TE.env ->
      mapioin -> TE.key list -> V.t list -> mapls -> mapls -> map2etc ->
      mapmem -> int -> int -> mapls -> mmaptuple -> mapfstmt -> mapterss ->
      allboolmap -> mapls -> mapls -> mmapvar -> int ->
      (((SV.t * SV.t) * mapmem) * mapterss) * mapioin **)

  let run_module modorder flagmap newinstportsmap finsti2e_outmap mainmod rs s te io_in name ols readerls writerls data2etc memmap clk_num len finstoutl finstoutm ffmodsmap fterss fread_la finstin finstout finstportmap iternum =
    let (newffmodsmap, _) =
      reorder modorder flagmap ffmodsmap newinstportsmap finsti2e_outmap
        finstin finstout finstoutl
    in
    run_module0 mainmod rs s te io_in name ols readerls writerls data2etc
      memmap clk_num len finstoutl finstoutm newffmodsmap fterss fread_la
      finstin finstportmap iternum

  (** val eval_fport_init : fport -> SV.t -> SV.t **)

  let eval_fport_init p s =
    match p with
    | Finput (v, t0) ->
      if eq_op bitseq_eqType (Obj.magic SV.acc v s) (Obj.magic [])
      then SV.upd v (from_Z (sizeof_fgtyp t0) 0) s
      else s
    | Foutput (v, t0) ->
      if eq_op bitseq_eqType (Obj.magic SV.acc v s) (Obj.magic [])
      then SV.upd v (from_Z (sizeof_fgtyp t0) 0) s
      else s

  (** val eval_fports_init : fport list -> SV.t -> SV.t **)

  let rec eval_fports_init ps s =
    match ps with
    | [] -> s
    | h :: tl -> eval_fports_init tl (eval_fport_init h s)

  (** val upd_typenv_fmodule : fmodule -> TE.env -> SV.t -> TE.env **)

  let upd_typenv_fmodule m te s =
    match m with
    | FInmod (_, ps, ss) -> upd_typenv_fstmts ss (upd_typenv_fports ps te) s
    | FExmod (_, _, _) -> te

  (** val well_typed_fexpr : fexpr -> TE.env -> bool **)

  let rec well_typed_fexpr e te =
    match e with
    | Econst (t0, c) ->
      eq_op nat_eqType (Obj.magic sizeof_fgtyp t0) (Obj.magic size c)
    | Ecast (_, e1) -> well_typed_fexpr e1 te
    | Eprim_unop (o, e1) ->
      (match o with
       | Upad _ ->
         (match type_of_fexpr e1 te with
          | Fuint _ -> well_typed_fexpr e1 te
          | Fsint _ -> well_typed_fexpr e1 te
          | _ -> false)
       | Ushl _ ->
         (match type_of_fexpr e1 te with
          | Fuint _ -> well_typed_fexpr e1 te
          | Fsint _ -> well_typed_fexpr e1 te
          | _ -> false)
       | Ushr _ ->
         (match type_of_fexpr e1 te with
          | Fuint _ -> well_typed_fexpr e1 te
          | Fsint _ -> well_typed_fexpr e1 te
          | _ -> false)
       | Ucvt ->
         (match type_of_fexpr e1 te with
          | Fuint _ -> well_typed_fexpr e1 te
          | Fsint _ -> well_typed_fexpr e1 te
          | _ -> false)
       | Uneg ->
         (match type_of_fexpr e1 te with
          | Fuint _ -> well_typed_fexpr e1 te
          | Fsint _ -> well_typed_fexpr e1 te
          | _ -> false)
       | Unot ->
         (match type_of_fexpr e1 te with
          | Fuint _ -> well_typed_fexpr e1 te
          | Fsint _ -> well_typed_fexpr e1 te
          | _ -> false)
       | _ -> well_typed_fexpr e1 te)
    | Eprim_binop (b, e1, e2) ->
      (match b with
       | Bdshl ->
         (match type_of_fexpr e1 te with
          | Fuint _ ->
            (match type_of_fexpr e2 te with
             | Fuint _ ->
               (&&) (well_typed_fexpr e1 te) (well_typed_fexpr e2 te)
             | _ -> false)
          | Fsint _ ->
            (match type_of_fexpr e2 te with
             | Fuint _ ->
               (&&) (well_typed_fexpr e1 te) (well_typed_fexpr e2 te)
             | _ -> false)
          | _ -> false)
       | Bdshr ->
         (match type_of_fexpr e1 te with
          | Fuint _ ->
            (match type_of_fexpr e2 te with
             | Fuint _ ->
               (&&) (well_typed_fexpr e1 te) (well_typed_fexpr e2 te)
             | _ -> false)
          | Fsint _ ->
            (match type_of_fexpr e2 te with
             | Fuint _ ->
               (&&) (well_typed_fexpr e1 te) (well_typed_fexpr e2 te)
             | _ -> false)
          | _ -> false)
       | _ ->
         (match type_of_fexpr e1 te with
          | Fuint _ ->
            (match type_of_fexpr e2 te with
             | Fuint _ ->
               (&&) (well_typed_fexpr e1 te) (well_typed_fexpr e2 te)
             | _ -> false)
          | Fsint _ ->
            (match type_of_fexpr e2 te with
             | Fsint _ ->
               (&&) (well_typed_fexpr e1 te) (well_typed_fexpr e2 te)
             | _ -> false)
          | _ -> false))
    | Emux (c, e1, e2) ->
      let t1 = type_of_fexpr e1 te in
      let t2 = type_of_fexpr e2 te in
      (match t1 with
       | Fuint _ ->
         (match t2 with
          | Fuint _ ->
            (&&) ((&&) (well_typed_fexpr c te) (well_typed_fexpr e1 te))
              (well_typed_fexpr e2 te)
          | _ -> false)
       | Fsint _ ->
         (match t2 with
          | Fsint _ ->
            (&&) ((&&) (well_typed_fexpr c te) (well_typed_fexpr e1 te))
              (well_typed_fexpr e2 te)
          | _ -> false)
       | _ -> false)
    | Evalidif (c, e1) ->
      (&&) (well_typed_fexpr c te) (well_typed_fexpr e1 te)
    | Eref v -> leq (Pervasives.succ 0) (sizeof_fgtyp (TE.vtyp v te))

  (** val no_mem_eval_fexpr : fexpr -> SV.t -> TE.env -> bits **)

  let rec no_mem_eval_fexpr e s te =
    match e with
    | Econst (t0, c) ->
      (match t0 with
       | Fuint _ -> zext (subn (sizeof_fgtyp t0) (size c)) c
       | Fsint _ -> sext (subn (sizeof_fgtyp t0) (size c)) c
       | _ -> c)
    | Ecast (u, e0) ->
      (match u with
       | AsUInt -> no_mem_eval_fexpr e0 s te
       | AsSInt -> no_mem_eval_fexpr e0 s te
       | _ -> (lsb (no_mem_eval_fexpr e0 s te)) :: [])
    | Eprim_unop (u, e0) ->
      let t0 = type_of_fexpr e0 te in
      eunop_op u t0 (no_mem_eval_fexpr e0 s te)
    | Eprim_binop (b, e1, e2) ->
      let ve1 = no_mem_eval_fexpr e1 s te in
      let ve2 = no_mem_eval_fexpr e2 s te in
      let te1 = type_of_fexpr e1 te in
      let te2 = type_of_fexpr e2 te in ebinop_op b te1 te2 ve1 ve2
    | Emux (c, e1, e2) ->
      let t1 = type_of_fexpr e1 te in
      let t2 = type_of_fexpr e2 te in
      (match t1 with
       | Fuint w1 ->
         (match t2 with
          | Fuint w2 ->
            if negb (is_zero (no_mem_eval_fexpr c s te))
            then zext (subn (maxn w1 w2) w1) (no_mem_eval_fexpr e1 s te)
            else zext (subn (maxn w1 w2) w2) (no_mem_eval_fexpr e2 s te)
          | _ -> [])
       | Fsint w1 ->
         (match t2 with
          | Fsint w2 ->
            if negb (is_zero (no_mem_eval_fexpr c s te))
            then sext (subn (maxn w1 w2) w1) (no_mem_eval_fexpr e1 s te)
            else sext (subn (maxn w1 w2) w2) (no_mem_eval_fexpr e2 s te)
          | _ -> [])
       | _ -> [])
    | Evalidif (_, e0) -> no_mem_eval_fexpr e0 s te
    | Eref v -> SV.acc v s

  (** val no_mem_eval_noninst_fstmt :
      fstmt -> SV.t -> SV.t -> TE.env -> SV.t * SV.t **)

  let no_mem_eval_noninst_fstmt st rs s te =
    match st with
    | Swire (v, t0) -> (rs, (SV.upd v (zeros (sizeof_fgtyp t0)) s))
    | Sreg r ->
      if eq_op bitseq_eqType (Obj.magic SV.acc r.rid rs) (Obj.magic [])
      then let rs0 = SV.upd r.rid (zeros (sizeof_fgtyp r.coq_type)) rs in
           let s0 = SV.upd r.rid (zeros (sizeof_fgtyp r.coq_type)) s in
           (match r.reset with
            | NRst -> (rs0, s0)
            | Rst (e1, e2) ->
              let te1 = type_of_fexpr e1 te in
              let ve1 = no_mem_eval_fexpr e1 s0 te in
              let ve2 = no_mem_eval_fexpr e2 s0 te in
              if is_zero ve1
              then (rs0, s0)
              else (match te1 with
                    | Fuint n ->
                      ((fun fO fS n -> if n=0 then fO () else fS (n-1))
                         (fun _ -> (rs0, s0))
                         (fun n0 ->
                         (fun fO fS n -> if n=0 then fO () else fS (n-1))
                           (fun _ -> ((SV.upd r.rid ve2 rs0), s0))
                           (fun _ -> (rs0, s0))
                           n0)
                         n)
                    | Fasyncreset ->
                      ((SV.upd r.rid ve2 rs0), (SV.upd r.rid ve2 s0))
                    | _ -> (rs0, s0)))
      else let s0 = SV.upd r.rid (SV.acc r.rid rs) s in
           (match r.reset with
            | NRst -> (rs, s0)
            | Rst (e1, e2) ->
              let te1 = type_of_fexpr e1 te in
              let ve1 = no_mem_eval_fexpr e1 s0 te in
              let ve2 = no_mem_eval_fexpr e2 s0 te in
              if is_zero ve1
              then (rs, s0)
              else (match te1 with
                    | Fuint n ->
                      ((fun fO fS n -> if n=0 then fO () else fS (n-1))
                         (fun _ -> (rs, s0))
                         (fun n0 ->
                         (fun fO fS n -> if n=0 then fO () else fS (n-1))
                           (fun _ -> ((SV.upd r.rid ve2 rs), s0))
                           (fun _ -> (rs, s0))
                           n0)
                         n)
                    | Fasyncreset ->
                      ((SV.upd r.rid ve2 rs), (SV.upd r.rid ve2 s0))
                    | _ -> (rs, s0)))
    | Snode (v, e) -> (rs, (SV.upd v (no_mem_eval_fexpr e s te) s))
    | Sfcnct (v, e2) ->
      let newv = no_mem_eval_fexpr e2 s te in
      let len0 = size newv in
      (match TE.vtyp v te with
       | Fuint w ->
         if eq_op bitseq_eqType (Obj.magic SV.acc v rs) (Obj.magic [])
         then (rs, (SV.upd v (zext (subn w len0) newv) s))
         else ((SV.upd v (zext (subn w len0) newv) rs), s)
       | Fsint w ->
         if eq_op bitseq_eqType (Obj.magic SV.acc v rs) (Obj.magic [])
         then (rs, (SV.upd v (sext (subn w len0) newv) s))
         else ((SV.upd v (sext (subn w len0) newv) rs), s)
       | _ -> (rs, s))
    | Sinvalid v ->
      let tv = TE.vtyp v te in (rs, (SV.upd v (zeros (sizeof_fgtyp tv)) s))
    | _ -> (rs, s)

  (** val no_mem_upd_typenv_fstmt : fstmt -> TE.env -> TE.env **)

  let no_mem_upd_typenv_fstmt s te =
    match s with
    | Swire (v, t0) -> TE.add v t0 te
    | Sreg r -> TE.add r.rid r.coq_type te
    | Sinst inst -> upd_typenv_fports inst.iports te
    | Snode (v, e) -> TE.add v (type_of_fexpr e te) te
    | Sinvalid v -> TE.add v (TE.vtyp v te) te
    | _ -> te

  (** val no_mem_upd_typenv_fstmts : fstmt list -> TE.env -> TE.env **)

  let rec no_mem_upd_typenv_fstmts ss te =
    match ss with
    | [] -> te
    | h :: tl -> no_mem_upd_typenv_fstmts tl (no_mem_upd_typenv_fstmt h te)

  (** val no_mem_eval_fstmt :
      fstmt -> SV.t -> SV.t -> TE.env -> V.t list -> maptuple -> mapfstmt ->
      mapterss -> mapls -> mvar -> mapvar -> mapls -> mmaptuple -> mmapvar ->
      int -> (SV.t * SV.t) * mapterss **)

  let rec no_mem_eval_fstmt st rs s te finstoutl finstoutm ffmodsmap fterss finstin finstinmap finstoutmap allfinstoutl allfinstoutm allfinstportmap iternum =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> ((no_mem_eval_noninst_fstmt st rs s te),
      fterss))
      (fun iternum0 ->
      match st with
      | Sinst inst ->
        let v = inst.iid in
        (match TE.find inst.imid ffmodsmap with
         | Some mst ->
           (match TE.find inst.iid fterss with
            | Some aa ->
              let (p, mem0) = aa in
              let (p0, s0) = p in
              let (te0, rs0) = p0 in
              (match TE.find inst.imid finstin with
               | Some a2 ->
                 (match TE.find v finstinmap with
                  | Some updfinstin ->
                    let s1 = upd_inner s s0 a2 updfinstin in
                    (match TE.find inst.imid allfinstoutl with
                     | Some finstoutl0 ->
                       (match TE.find inst.imid allfinstoutm with
                        | Some a ->
                          (match TE.find inst.imid allfinstportmap with
                           | Some a0 ->
                             let (finstinmap0, finstoutmap0) = a0 in
                             let (p1, fterss2) =
                               fold_left (fun pat tempst ->
                                 let (y, tfterss) = pat in
                                 let (trs, ts) = y in
                                 no_mem_eval_fstmt tempst trs ts te0
                                   finstoutl0 a ffmodsmap tfterss finstin
                                   finstinmap0 finstoutmap0 allfinstoutl
                                   allfinstoutm allfinstportmap iternum0)
                                 (rev mst) ((rs0, s1), fterss)
                             in
                             let (rs2, s2) = p1 in
                             ((rs, s),
                             (TE.add v (((te0, rs2), s2), mem0) fterss2))
                           | None -> ((rs, s), fterss))
                        | None -> ((rs, s), fterss))
                     | None -> ((rs, s), fterss))
                  | None -> ((rs, s), fterss))
               | None -> ((rs, s), fterss))
            | None -> ((rs, s), fterss))
         | None -> ((rs, s), fterss))
      | Sfcnct (v, e2) ->
        (match e2 with
         | Eref v1 ->
           if mylListIn v1 finstoutl
           then let newv =
                  match TE.find v1 finstoutm with
                  | Some p ->
                    let (a4, a0) = p in
                    (match TE.find a4 ffmodsmap with
                     | Some mst ->
                       (match TE.find a0 fterss with
                        | Some aa ->
                          let (p0, _) = aa in
                          let (p1, s0) = p0 in
                          let (te0, rs0) = p1 in
                          (match TE.find a4 finstin with
                           | Some a2 ->
                             (match TE.find a0 finstinmap with
                              | Some updfinstin ->
                                (match TE.find a4 allfinstoutl with
                                 | Some finstoutl0 ->
                                   let s1 = upd_inner s s0 a2 updfinstin in
                                   let s2 =
                                     match TE.find a4 allfinstoutm with
                                     | Some finstoutm0 ->
                                       (match TE.find a4 allfinstportmap with
                                        | Some p2 ->
                                          let (finstinmap0, finstoutmap0) = p2
                                          in
                                          let te1 =
                                            no_mem_upd_typenv_fstmts
                                              (rev mst) te0
                                          in
                                          snd
                                            (fst
                                              (fold_left (fun pat tempst ->
                                                let (y, tfterss) = pat in
                                                let (trs, ts) = y in
                                                no_mem_eval_fstmt tempst trs
                                                  ts te1 finstoutl0
                                                  finstoutm0 ffmodsmap
                                                  tfterss finstin finstinmap0
                                                  finstoutmap0 allfinstoutl
                                                  allfinstoutm
                                                  allfinstportmap iternum0)
                                                (rev mst) ((rs0, s1), fterss)))
                                        | None -> s)
                                     | None -> s
                                   in
                                   (match TE.find v1 finstoutmap with
                                    | Some a3 -> SV.acc a3 s2
                                    | None -> [])
                                 | None -> [])
                              | None -> [])
                           | None -> [])
                        | None -> [])
                     | None -> [])
                  | None -> []
                in
                if eq_op bitseq_eqType (Obj.magic SV.acc v rs) (Obj.magic [])
                then ((rs, (SV.upd v newv s)), fterss)
                else (((SV.upd v newv rs), s), fterss)
           else ((no_mem_eval_noninst_fstmt st rs s te), fterss)
         | _ -> ((no_mem_eval_noninst_fstmt st rs s te), fterss))
      | _ -> ((no_mem_eval_noninst_fstmt st rs s te), fterss))
      iternum

  (** val no_mem_eval_fstmts :
      fstmt list -> SV.t -> SV.t -> TE.env -> V.t list -> maptuple ->
      mapfstmt -> mapterss -> mapls -> mvar -> mapvar -> mapls -> mmaptuple
      -> mmapvar -> int -> (SV.t * SV.t) * mapterss **)

  let rec no_mem_eval_fstmts st rs s te finstoutl finstoutm ffmodsmap fterss finstin finstinmap finstoutmap allfinstoutl allfinstoutm allfinstportmap iternum =
    match st with
    | [] -> ((rs, s), fterss)
    | hd :: tl ->
      let te0 = no_mem_upd_typenv_fstmt hd te in
      let (p, _) =
        no_mem_eval_fstmt hd rs s te0 finstoutl finstoutm ffmodsmap fterss
          finstin finstinmap finstoutmap allfinstoutl allfinstoutm
          allfinstportmap iternum
      in
      let (rs0, s0) = p in
      no_mem_eval_fstmts tl rs0 s0 te0 finstoutl finstoutm ffmodsmap fterss
        finstin finstinmap finstoutmap allfinstoutl allfinstoutm
        allfinstportmap iternum

  (** val no_mem_eval_module :
      V.t -> SV.t -> SV.t -> TE.env -> mapioin -> V.t list -> mapls ->
      mmaptuple -> mapfstmt -> mapterss -> mapls -> mmapvar -> int ->
      ((SV.t * SV.t) * mapterss) * mapioin **)

  let no_mem_eval_module v rs s te io_in ols finstoutl finstoutm ffmodsmap fterss finstin finstportmap iternum =
    match TE.find v ffmodsmap with
    | Some st ->
      let finstoutl0 = match TE.find v finstoutl with
                       | Some a -> a
                       | None -> []
      in
      (match TE.find v finstoutm with
       | Some a ->
         (match TE.find v finstportmap with
          | Some a0 ->
            let (finstinmap0, finstoutmap0) = a0 in
            let (p, fterss2) =
              no_mem_eval_fstmts (rev st) rs s te finstoutl0 a ffmodsmap
                fterss finstin finstinmap0 finstoutmap0 finstoutl finstoutm
                finstportmap iternum
            in
            let (rs2, s2) = p in
            let io_in2 = fold_left (myupdateo s2) ols io_in in
            (((rs2, s2), fterss2), io_in2)
          | None -> (((rs, s), fterss), io_in))
       | None -> (((rs, s), fterss), io_in))
    | None -> (((rs, s), fterss), io_in)

  (** val no_mem_run_module0 :
      V.t -> SV.t -> SV.t -> TE.env -> mapioin -> TE.key list -> V.t list ->
      int -> int -> mapls -> mmaptuple -> mapfstmt -> mapterss -> mapls ->
      mmapvar -> int -> ((SV.t * SV.t) * mapterss) * mapioin **)

  let rec no_mem_run_module0 mainmod rs s te io_in name ols clk_num len finstoutl finstoutm ffmodsmap fterss finstin finstportmap iternum =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> (((rs, s), fterss), io_in))
      (fun m ->
      let n = subn len (Pervasives.succ m) in
      let s1 = upd_argulist s io_in name n in
      let (p, io_in0) =
        no_mem_eval_module mainmod rs s1 te io_in ols finstoutl finstoutm
          ffmodsmap fterss finstin finstportmap iternum
      in
      let (p0, fterss0) = p in
      let (rs2, s2) = p0 in
      no_mem_run_module0 mainmod rs2 s2 te io_in0 name ols m len finstoutl
        finstoutm ffmodsmap fterss0 finstin finstportmap iternum)
      clk_num

  (** val no_mem_run_module :
      V.t list -> fmap -> mmvar -> mvar -> V.t -> SV.t -> SV.t -> TE.env ->
      mapioin -> TE.key list -> V.t list -> int -> int -> mapls -> mmaptuple
      -> mapfstmt -> mapterss -> mapls -> mapls -> mmapvar -> int ->
      ((SV.t * SV.t) * mapterss) * mapioin **)

  let no_mem_run_module modorder flagmap newinstportsmap finsti2e_outmap mainmod rs s te io_in name ols clk_num len finstoutl finstoutm ffmodsmap fterss finstin finstout finstportmap iternum =
    let (newffmodsmap, _) =
      reorder modorder flagmap ffmodsmap newinstportsmap finsti2e_outmap
        finstin finstout finstoutl
    in
    no_mem_run_module0 mainmod rs s te io_in name ols clk_num len finstoutl
      finstoutm newffmodsmap fterss finstin finstportmap iternum

  (** val no_mem_eval_fstmts_inline :
      fstmt list -> SV.t -> SV.t -> TE.env -> SV.t * SV.t **)

  let rec no_mem_eval_fstmts_inline st rs s te =
    match st with
    | [] -> (rs, s)
    | hd :: tl ->
      let te0 = no_mem_upd_typenv_fstmt hd te in
      let (rs0, s0) = no_mem_eval_noninst_fstmt hd rs s te0 in
      no_mem_eval_fstmts_inline tl rs0 s0 te0

  (** val no_mem_eval_module_inline :
      fstmt list -> SV.t -> SV.t -> TE.env -> mapioin -> V.t list ->
      (SV.t * SV.t) * mapioin **)

  let no_mem_eval_module_inline sl rs s te io_in ols =
    let (rs2, s2) = no_mem_eval_fstmts_inline (rev sl) rs s te in
    let io_in2 = fold_left (myupdateo s2) ols io_in in ((rs2, s2), io_in2)

  (** val no_mem_run_module0_inline :
      fstmt list -> SV.t -> SV.t -> TE.env -> mapioin -> TE.key list -> V.t
      list -> int -> int -> (SV.t * SV.t) * mapioin **)

  let rec no_mem_run_module0_inline sl rs s te io_in name ols clk_num len =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> ((rs, s), io_in))
      (fun m ->
      let n = subn len (Pervasives.succ m) in
      let s1 = upd_argulist s io_in name n in
      let (p, io_in0) = no_mem_eval_module_inline sl rs s1 te io_in ols in
      let (rs2, s2) = p in
      no_mem_run_module0_inline sl rs2 s2 te io_in0 name ols m len)
      clk_num

  (** val reorder_inline : Coq__8.fmodule -> fstmt list * g **)

  let reorder_inline = function
  | FInmod (_, pl, sl) ->
    let (p, regstmt) = known_reg_orders sl in
    let (def, known) = p in
    let (regls, roots) =
      fold_left (fun pat tst -> let (ls1, ls2) = pat in findreg ls1 ls2 tst)
        sl ([], [])
    in
    let inps =
      fold_left (fun ls p0 ->
        match p0 with
        | Finput (v, _) -> v :: ls
        | Foutput (_, _) -> ls) pl []
    in
    let (newg, var2stmt) =
      fold_left (fun pat tempst ->
        let (tempg, tempm) = pat in
        (match tempst with
         | Snode (v, e) ->
           let preset = expr2varlist e [] in
           if eq_op (seq_eqType V.coq_T) (Obj.magic preset) (Obj.magic [])
           then (tempg, tempm)
           else let newg0 =
                  fold_left (fun tempg0 tempv ->
                    updg tempv (v :: (findg tempv tempg0)) tempg0) preset
                    tempg
                in
                (newg0, (TE.add v tempst tempm))
         | Sfcnct (v1, e2) ->
           let preset = expr2varlist e2 [] in
           if eq_op (seq_eqType V.coq_T) (Obj.magic preset) (Obj.magic [])
           then (tempg, tempm)
           else if varIn v1 regls
                then (tempg, tempm)
                else let newg0 =
                       fold_left (fun tempg0 tempv ->
                         updg tempv (v1 :: (findg tempv tempg0)) tempg0)
                         preset tempg
                     in
                     (newg0, (TE.add v1 tempst tempm))
         | Sinvalid _ -> (tempg, tempm)
         | Swhen (_, _, _) -> (tempg, tempm)
         | Sstop (_, _, _) -> (tempg, tempm)
         | _ -> (tempg, tempm))) sl (emptyg, TE.empty)
    in
    (match topo_sort newg (addn (length pl) (length sl)) (cat inps roots) with
     | Some varorder ->
       let ordered =
         List0.map (fun tv ->
           match TE.find tv var2stmt with
           | Some tempst -> tempst
           | None -> sskip) varorder
       in
       ((cat def (cat known (cat ordered regstmt))), newg)
     | None -> ([], emptyg))
  | FExmod (_, _, _) -> ([], emptyg)

  (** val no_mem_run_module_inline :
      Coq__8.fmodule -> SV.t -> SV.t -> TE.env -> mapioin -> TE.key list ->
      V.t list -> int -> int -> (SV.t * SV.t) * mapioin **)

  let no_mem_run_module_inline fmain rs s te io_in name ols clk_num len =
    let (reordersl, _) = reorder_inline fmain in
    no_mem_run_module0_inline (rev reordersl) rs s te io_in name ols clk_num
      len

  (** val is_defined : V.t -> TE.env -> bool **)

  let is_defined =
    TE.mem

  (** val is_defined_fexpr : fexpr -> TE.env -> bool **)

  let rec is_defined_fexpr e te =
    match e with
    | Econst (_, _) -> true
    | Ecast (_, e1) -> is_defined_fexpr e1 te
    | Eprim_unop (_, e1) -> is_defined_fexpr e1 te
    | Eprim_binop (_, e1, e2) ->
      (&&) (is_defined_fexpr e1 te) (is_defined_fexpr e2 te)
    | Emux (c, e1, e2) ->
      (&&) ((&&) (is_defined_fexpr c te) (is_defined_fexpr e1 te))
        (is_defined_fexpr e2 te)
    | Evalidif (c, e1) ->
      (&&) (is_defined_fexpr c te) (is_defined_fexpr e1 te)
    | Eref v -> is_defined v te

  (** val is_defined_fstmt : fstmt -> TE.env -> bool **)

  let is_defined_fstmt s te =
    match s with
    | Sreg r -> is_defined r.rid te
    | Snode (_, e) -> is_defined_fexpr e te
    | Sfcnct (v, e) -> (&&) (is_defined v te) (is_defined_fexpr e te)
    | _ -> true

  (** val well_formed_fexpr : fexpr -> TE.env -> bool **)

  let well_formed_fexpr e te =
    (&&) (well_typed_fexpr e te) (is_defined_fexpr e te)

  (** val well_typed_fstmt_inline :
      fstmt -> TE.env -> SV.t -> SV.t -> bool **)

  let well_typed_fstmt_inline s te s1 rs1 =
    match s with
    | Swire (_, t0) -> leq (Pervasives.succ 0) (sizeof_fgtyp t0)
    | Sreg r ->
      (&&)
        (eq_op fgtyp_eqType (Obj.magic TE.vtyp r.rid te)
          (Obj.magic r.coq_type))
        (match r.reset with
         | NRst -> true
         | Rst (e1, e2) ->
           (&&)
             ((&&) ((&&) (well_typed_fexpr e1 te) (well_typed_fexpr e2 te))
               (eq_op nat_eqType
                 (Obj.magic size
                   (no_mem_eval_fexpr e2
                     (SV.upd r.rid (zeros (sizeof_fgtyp r.coq_type)) s1)
                     (TE.add r.rid r.coq_type te)))
                 (Obj.magic sizeof_fgtyp r.coq_type)))
             (eq_op nat_eqType
               (Obj.magic size
                 (no_mem_eval_fexpr e2 (SV.upd r.rid (SV.acc r.rid rs1) s1)
                   (TE.add r.rid r.coq_type te)))
               (Obj.magic sizeof_fgtyp r.coq_type)))
    | Sinst _ -> false
    | Snode (_, e) -> well_typed_fexpr e te
    | Sfcnct (v, e) ->
      (match TE.vtyp v te with
       | Fuint w ->
         (&&) (well_typed_fexpr e te)
           (leq (sizeof_fgtyp (type_of_fexpr e te)) w)
       | Fsint w ->
         (&&) (well_typed_fexpr e te)
           (leq (sizeof_fgtyp (type_of_fexpr e te)) w)
       | _ -> false)
    | _ -> true

  (** val well_formed_fstmt_inline :
      fstmt -> TE.env -> SV.t -> SV.t -> bool **)

  let well_formed_fstmt_inline s te s1 rs1 =
    (&&) (well_typed_fstmt_inline s te s1 rs1) (is_defined_fstmt s te)

  (** val well_formed_fstmts_inline :
      fstmt list -> TE.env -> SV.t -> SV.t -> bool **)

  let rec well_formed_fstmts_inline sts te s rs =
    match sts with
    | [] -> true
    | hd :: tl ->
      (&&) (well_formed_fstmt_inline hd te s rs)
        (well_formed_fstmts_inline tl (no_mem_upd_typenv_fstmt hd te)
          (snd
            (no_mem_eval_noninst_fstmt hd rs s
              (no_mem_upd_typenv_fstmt hd te)))
          (fst
            (no_mem_eval_noninst_fstmt hd rs s
              (no_mem_upd_typenv_fstmt hd te))))
 end

module LoFirrtl = MakeFirrtl(VarOrder)(TE)(Store)
