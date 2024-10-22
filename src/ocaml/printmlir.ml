open Hifirrtl_lang
open Big_int_Z
(*open Transform
open ModuleGraph_simplified*)

open Printf
open Extraction
open HiFirrtl
open Transhiast_pair

let pair2nat (m, n) = (m + n) * (m + n + 1) /2 + m

let pp_fgtyp_mlir out gt =
  match gt with
  | Env.Fuint n -> fprintf out "uint<%d>" n
  | Env.Fsint n -> fprintf out "sint<%d>" n
  | Env.Fclock -> fprintf out "clock"
  | Env.Fasyncreset -> fprintf out "asyncreset"
  | Env.Fuint_implicit n -> fprintf out "uint<%d>" n
  | Env.Fsint_implicit n -> fprintf out "sint<%d>" n
  | Env.Freset -> fprintf out "reset"

let pp_ftype_mlir out ft = 
  match ft with
  | HiEnv.Gtyp gt -> pp_fgtyp_mlir out gt
  | HiEnv.Atyp _ -> fprintf out "array type\n"
  | HiEnv.Btyp _ -> fprintf out "bundle type\n"(*
  | HiEnv.Atyp (atyp, n) -> fprintf out "vector<"; pp_ftype_mlir out btyp; fprintf out ", "^(Int.to_string n)^">"
  | HiEnv.Btyp btyp -> fprintf out "bundle<"; pp_fbtyp_mlir out btyp; fprintf out ">"

and pp_fbtyp_mlir out btyp =
  match btyp with
  | HiEnv.Fnil -> fprintf out ""
  | HiEnv.Fflips (fv, HiEnv.Nflip, ft, Fnil) -> fprintf out v^": "; pp_ftype_mlir out ft
  | HiEnv.Fflips (fv, HiEnv.Flipped, ft, Fnil) -> fprintf out v^" flip: "; pp_ftype_mlir out ft
  | HiEnv.Fflips (fv, HiEnv.Nflip, ft, ff) -> fprintf out v^": "; pp_ftype_mlir out ft; fprintf out ", "; pp_fbtyp_mlir out ff
  | HiEnv.Fflips (fv, HiEnv.Flipped, ft, ff) -> fprintf out v^" flip: "; pp_ftype_mlir out ft; fprintf out ", "; pp_fbtyp_mlir out ff
*)
let pp_port_mlir out p =
  match p with 
  | HiFirrtl.Finput (v, ft) -> fprintf out "in %%%d: !firrtl." (pair2nat (Obj.magic v)); pp_ftype_mlir out ft
  | HiFirrtl.Foutput (v, ft) -> fprintf out "out %%%d: !firrtl." (pair2nat (Obj.magic v)); pp_ftype_mlir out ft

let rec pp_ports_mlir out pl =
  match pl with
  | [] -> fprintf out ""
  | p :: [] -> pp_port_mlir out p
  | p :: tl -> pp_port_mlir out p; fprintf out ", "; pp_ports_mlir out tl

let sizeof_ftype ft =
  match ft with
  | HiEnv.Gtyp gt -> Env.sizeof_fgtyp gt
  | _ -> 0

let nat_of_bits bv = 
  let rec helper i max lst res =
    if i >= max then res
    else match List.nth bv i with
    | false -> helper (succ i) max lst res
    | true -> helper (succ i) max lst (add_big_int (power_int_positive_int (2) i) res) in
  helper 0 (List.length bv) bv zero_big_int

let z_of_bits bv = 
  let (v,sign) = NBitsDef.splitmsb bv in
  if sign then (sub_big_int (nat_of_bits v) (power_int_positive_int (2) ((List.length bv)-1))) (*最高位true，负数*)
  else
    nat_of_bits v

let rec pp_expr_mlir out eflag tmap e = 
  match e with
  | HiFirrtl.Econst (gt, bs) -> (match gt with
                          | Env.Fuint _ -> fprintf out "%%e%d = firrtl.constant %s : !firrtl." eflag (string_of_big_int (nat_of_bits bs)); pp_fgtyp_mlir out gt; fprintf out "\n"; ("%e"^(Int.to_string eflag), eflag + 1)
                          | Env.Fsint _ -> fprintf out "%%e%d = firrtl.constant %s : !firrtl." eflag (string_of_big_int (z_of_bits bs)); pp_fgtyp_mlir out gt; fprintf out "\n"; ("%e"^(Int.to_string eflag), eflag + 1)
                          | _ -> printf "error const expression\n"; ("error const expression", eflag))
  | HiFirrtl.Ecast (c, e0) -> (let (eflag0, eflag1) = pp_expr_mlir out eflag tmap e0 in match c with
                          | Firrtl.AsUInt -> fprintf out "%%e%d = firrtl.asUInt %s : (!firrtl." eflag1 eflag0; (match ModuleGraph_simplified.type_of_expr e0 tmap, ModuleGraph_simplified.type_of_expr e tmap with
                                                                                                                | Some te0, Some te -> pp_ftype_mlir out te0; fprintf out ") -> !firrtl."; pp_ftype_mlir out te; ("%e"^(Int.to_string eflag1), eflag1 + 1)
                                                                                                                | _, _ -> fprintf out "wrong expression type"; ("%e"^(Int.to_string eflag1), eflag1 + 1))
                          | Firrtl.AsSInt -> fprintf out "%%e%d = firrtl.asSInt %s : (!firrtl." eflag1 eflag0; (match ModuleGraph_simplified.type_of_expr e0 tmap, ModuleGraph_simplified.type_of_expr e tmap with
                                                                                                                | Some te0, Some te -> pp_ftype_mlir out te0; fprintf out ") -> !firrtl."; pp_ftype_mlir out te; ("%e"^(Int.to_string eflag1), eflag1 + 1)
                                                                                                                | _, _ -> fprintf out "wrong expression type"; ("%e"^(Int.to_string eflag1), eflag1 + 1))
                          | Firrtl.AsClock -> fprintf out "%%e%d = firrtl.asClock %s : (!firrtl." eflag1 eflag0; (match ModuleGraph_simplified.type_of_expr e0 tmap with
                                                                                                                | Some te0 -> pp_ftype_mlir out te0; fprintf out ") -> !firrtl.clock"; ("%e"^(Int.to_string eflag1), eflag1 + 1)
                                                                                                                | _ -> fprintf out "wrong expression type"; ("%e"^(Int.to_string eflag1), eflag1 + 1))
                          | Firrtl.AsAsync -> fprintf out "%%e%d = firrtl.asAsyncReset %s : (!firrtl." eflag1 eflag0; (match ModuleGraph_simplified.type_of_expr e0 tmap with
                                                                                                                | Some te0 -> pp_ftype_mlir out te0; fprintf out ") -> !firrtl.asyncreset"; ("%e"^(Int.to_string eflag1), eflag1 + 1)
                                                                                                                | _ -> fprintf out "wrong expression type"; ("%e"^(Int.to_string eflag1), eflag1 + 1))
                          (*| Firrtl.AsReset -> fprintf out "wrong expression asreset"; ("%e"^(Int.to_string eflag1), eflag1 + 1)*))
  | HiFirrtl.Eprim_unop (op, e0) -> (let (eflag0, eflag1) = pp_expr_mlir out eflag tmap e0 in match op with
                          | Firrtl.Upad s -> fprintf out "%%e%d = firrtl.pad %s, %d : (!firrtl." eflag1 eflag0 s; (match ModuleGraph_simplified.type_of_expr e0 tmap, ModuleGraph_simplified.type_of_expr e tmap with
                                                                                                                | Some te0, Some te -> pp_ftype_mlir out te0; fprintf out ") -> !firrtl."; pp_ftype_mlir out te; ("%e"^(Int.to_string eflag1), eflag1 + 1)
                                                                                                                | _, _ -> fprintf out "wrong expression type"; ("%e"^(Int.to_string eflag1), eflag1 + 1))
                          | Firrtl.Ushl s -> fprintf out "%%e%d = firrtl.shl %s, %d : (!firrtl." eflag1 eflag0 s; (match ModuleGraph_simplified.type_of_expr e0 tmap, ModuleGraph_simplified.type_of_expr e tmap with
                                                                                                                | Some te0, Some te -> pp_ftype_mlir out te0; fprintf out ") -> !firrtl."; pp_ftype_mlir out te; ("%e"^(Int.to_string eflag1), eflag1 + 1)
                                                                                                                | _, _ -> fprintf out "wrong expression type"; ("%e"^(Int.to_string eflag1), eflag1 + 1))
                          | Firrtl.Ushr s -> fprintf out "%%e%d = firrtl.shr %s, %d : (!firrtl." eflag1 eflag0 s; (match ModuleGraph_simplified.type_of_expr e0 tmap, ModuleGraph_simplified.type_of_expr e tmap with
                                                                                                                | Some te0, Some te -> pp_ftype_mlir out te0; fprintf out ") -> !firrtl."; pp_ftype_mlir out te; ("%e"^(Int.to_string eflag1), eflag1 + 1)
                                                                                                                | _, _ -> fprintf out "wrong expression type"; ("%e"^(Int.to_string eflag1), eflag1 + 1))
                          | Firrtl.Ucvt -> fprintf out "%%e%d = firrtl.cvt %s : (!firrtl." eflag1 eflag0; (match ModuleGraph_simplified.type_of_expr e0 tmap, ModuleGraph_simplified.type_of_expr e tmap with
                                                                                                                | Some te0, Some te -> pp_ftype_mlir out te0; fprintf out ") -> !firrtl."; pp_ftype_mlir out te; ("%e"^(Int.to_string eflag1), eflag1 + 1)
                                                                                                                | _, _ -> fprintf out "wrong expression type"; ("%e"^(Int.to_string eflag1), eflag1 + 1))
                          | Firrtl.Uneg -> fprintf out "%%e%d = firrtl.cvt %s : (!firrtl." eflag1 eflag0; (match ModuleGraph_simplified.type_of_expr e0 tmap, ModuleGraph_simplified.type_of_expr e tmap with
                                                                                                                | Some te0, Some te -> pp_ftype_mlir out te0; fprintf out ") -> !firrtl."; pp_ftype_mlir out te; ("%e"^(Int.to_string eflag1), eflag1 + 1)
                                                                                                                | _, _ -> fprintf out "wrong expression type"; ("%e"^(Int.to_string eflag1), eflag1 + 1))
                          | Firrtl.Unot -> fprintf out "%%e%d = firrtl.cvt %s : (!firrtl." eflag1 eflag0; (match ModuleGraph_simplified.type_of_expr e0 tmap, ModuleGraph_simplified.type_of_expr e tmap with
                                                                                                                | Some te0, Some te -> pp_ftype_mlir out te0; fprintf out ") -> !firrtl."; pp_ftype_mlir out te; ("%e"^(Int.to_string eflag1), eflag1 + 1)
                                                                                                                | _, _ -> fprintf out "wrong expression type"; ("%e"^(Int.to_string eflag1), eflag1 + 1))
                          | Firrtl.Uandr -> fprintf out "%%e%d = firrtl.cvt %s : (!firrtl." eflag1 eflag0; (match ModuleGraph_simplified.type_of_expr e0 tmap, ModuleGraph_simplified.type_of_expr e tmap with
                                                                                                                | Some te0, Some te -> pp_ftype_mlir out te0; fprintf out ") -> !firrtl."; pp_ftype_mlir out te; ("%e"^(Int.to_string eflag1), eflag1 + 1)
                                                                                                                | _, _ -> fprintf out "wrong expression type"; ("%e"^(Int.to_string eflag1), eflag1 + 1))
                          | Firrtl.Uorr -> fprintf out "%%e%d = firrtl.cvt %s : (!firrtl." eflag1 eflag0; (match ModuleGraph_simplified.type_of_expr e0 tmap, ModuleGraph_simplified.type_of_expr e tmap with
                                                                                                                | Some te0, Some te -> pp_ftype_mlir out te0; fprintf out ") -> !firrtl."; pp_ftype_mlir out te; ("%e"^(Int.to_string eflag1), eflag1 + 1)
                                                                                                                | _, _ -> fprintf out "wrong expression type"; ("%e"^(Int.to_string eflag1), eflag1 + 1))
                          | Firrtl.Uxorr -> fprintf out "%%e%d = firrtl.cvt %s : (!firrtl." eflag1 eflag0; (match ModuleGraph_simplified.type_of_expr e0 tmap, ModuleGraph_simplified.type_of_expr e tmap with
                                                                                                                | Some te0, Some te -> pp_ftype_mlir out te0; fprintf out ") -> !firrtl."; pp_ftype_mlir out te; ("%e"^(Int.to_string eflag1), eflag1 + 1)
                                                                                                                | _, _ -> fprintf out "wrong expression type"; ("%e"^(Int.to_string eflag1), eflag1 + 1))
                          | Firrtl.Uextr (s1, s2) -> fprintf out "%%e%d = firrtl.shr %s %d to %d : (!firrtl." eflag1 eflag0 s1 s2; (match ModuleGraph_simplified.type_of_expr e0 tmap, ModuleGraph_simplified.type_of_expr e tmap with
                                                                                                                | Some te0, Some te -> pp_ftype_mlir out te0; fprintf out ") -> !firrtl."; pp_ftype_mlir out te; ("%e"^(Int.to_string eflag1), eflag1 + 1)
                                                                                                                | _, _ -> fprintf out "wrong expression type"; ("%e"^(Int.to_string eflag1), eflag1 + 1))
                          | Firrtl.Uhead s -> fprintf out "%%e%d = firrtl.head %s, %d : (!firrtl." eflag1 eflag0 s; (match ModuleGraph_simplified.type_of_expr e0 tmap, ModuleGraph_simplified.type_of_expr e tmap with
                                                                                                                | Some te0, Some te -> pp_ftype_mlir out te0; fprintf out ") -> !firrtl."; pp_ftype_mlir out te; ("%e"^(Int.to_string eflag1), eflag1 + 1)
                                                                                                                | _, _ -> fprintf out "wrong expression type"; ("%e"^(Int.to_string eflag1), eflag1 + 1))
                          | Firrtl.Utail s -> fprintf out "%%e%d = firrtl.tail %s, %d : (!firrtl." eflag1 eflag0 s; (match ModuleGraph_simplified.type_of_expr e0 tmap, ModuleGraph_simplified.type_of_expr e tmap with
                                                                                                                | Some te0, Some te -> pp_ftype_mlir out te0; fprintf out ") -> !firrtl."; pp_ftype_mlir out te; ("%e"^(Int.to_string eflag1), eflag1 + 1)
                                                                                                                | _, _ -> fprintf out "wrong expression type"; ("%e"^(Int.to_string eflag1), eflag1 + 1)))
  | HiFirrtl.Eprim_binop (op, e1, e2) -> (let (eflag0, eflag1) = pp_expr_mlir out eflag tmap e1 in
                          let (eflag2, eflag3) = pp_expr_mlir out eflag1 tmap e2 in match op with
                          | Firrtl.Badd -> fprintf out "%%e%d = firrtl.add %s, %s : (!firrtl." eflag3 eflag0 eflag2; 
                                          (match ModuleGraph_simplified.type_of_expr e1 tmap, ModuleGraph_simplified.type_of_expr e2 tmap, ModuleGraph_simplified.type_of_expr e tmap with
                                          | Some te1, Some te2, Some te -> pp_ftype_mlir out te1; fprintf out ", !firrtl."; pp_ftype_mlir out te2; fprintf out ") -> !firrtl."; pp_ftype_mlir out te; ("%e"^(Int.to_string eflag3), eflag3 + 1)
                                          | _, _, _ -> fprintf out "wrong expression type"; ("%e"^(Int.to_string eflag3), eflag3 + 1))
                          | Firrtl.Bsub -> fprintf out "%%e%d = firrtl.sub %s, %s : (!firrtl." eflag3 eflag0 eflag2;
                                          (match ModuleGraph_simplified.type_of_expr e1 tmap, ModuleGraph_simplified.type_of_expr e2 tmap, ModuleGraph_simplified.type_of_expr e tmap with
                                          | Some te1, Some te2, Some te -> pp_ftype_mlir out te1; fprintf out ", !firrtl."; pp_ftype_mlir out te2; fprintf out ") -> !firrtl."; pp_ftype_mlir out te; ("%e"^(Int.to_string eflag3), eflag3 + 1)
                                          | _, _, _ -> fprintf out "wrong expression type"; ("%e"^(Int.to_string eflag3), eflag3 + 1))
                          | Firrtl.Bmul -> fprintf out "%%e%d = firrtl.mul %s, %s : (!firrtl." eflag3 eflag0 eflag2; 
                                          (match ModuleGraph_simplified.type_of_expr e1 tmap, ModuleGraph_simplified.type_of_expr e2 tmap, ModuleGraph_simplified.type_of_expr e tmap with
                                          | Some te1, Some te2, Some te -> pp_ftype_mlir out te1; fprintf out ", !firrtl."; pp_ftype_mlir out te2; fprintf out ") -> !firrtl."; pp_ftype_mlir out te; ("%e"^(Int.to_string eflag3), eflag3 + 1)
                                          | _, _, _ -> fprintf out "wrong expression type"; ("%e"^(Int.to_string eflag3), eflag3 + 1))
                          | Firrtl.Bdiv -> fprintf out "%%e%d = firrtl.div %s, %s : (!firrtl." eflag3 eflag0 eflag2;
                                          (match ModuleGraph_simplified.type_of_expr e1 tmap, ModuleGraph_simplified.type_of_expr e2 tmap, ModuleGraph_simplified.type_of_expr e tmap with
                                          | Some te1, Some te2, Some te -> pp_ftype_mlir out te1; fprintf out ", !firrtl."; pp_ftype_mlir out te2; fprintf out ") -> !firrtl."; pp_ftype_mlir out te; ("%e"^(Int.to_string eflag3), eflag3 + 1)
                                          | _, _, _ -> fprintf out "wrong expression type"; ("%e"^(Int.to_string eflag3), eflag3 + 1))
                          | Firrtl.Brem -> fprintf out "%%e%d = firrtl.rem %s, %s : (!firrtl." eflag3 eflag0 eflag2;
                                          (match ModuleGraph_simplified.type_of_expr e1 tmap, ModuleGraph_simplified.type_of_expr e2 tmap, ModuleGraph_simplified.type_of_expr e tmap with
                                          | Some te1, Some te2, Some te -> pp_ftype_mlir out te1; fprintf out ", !firrtl."; pp_ftype_mlir out te2; fprintf out ") -> !firrtl."; pp_ftype_mlir out te; ("%e"^(Int.to_string eflag3), eflag3 + 1)
                                          | _, _, _ -> fprintf out "wrong expression type"; ("%e"^(Int.to_string eflag3), eflag3 + 1))
                          | Firrtl.Bcomp s -> (match s with
                                              | Firrtl.Blt -> fprintf out "%%e%d = firrtl.lt %s, %s : (!firrtl." eflag3 eflag0 eflag2; 
                                                              (match ModuleGraph_simplified.type_of_expr e1 tmap, ModuleGraph_simplified.type_of_expr e2 tmap, ModuleGraph_simplified.type_of_expr e tmap with
                                                              | Some te1, Some te2, Some te -> pp_ftype_mlir out te1; fprintf out ", !firrtl."; pp_ftype_mlir out te2; fprintf out ") -> !firrtl."; pp_ftype_mlir out te; ("%e"^(Int.to_string eflag3), eflag3 + 1)
                                                              | _, _, _ -> fprintf out "wrong expression type"; ("%e"^(Int.to_string eflag3), eflag3 + 1))
                                              | Firrtl.Bleq -> fprintf out "%%e%d = firrtl.leq %s, %s : (!firrtl." eflag3 eflag0 eflag2; 
                                                              (match ModuleGraph_simplified.type_of_expr e1 tmap, ModuleGraph_simplified.type_of_expr e2 tmap, ModuleGraph_simplified.type_of_expr e tmap with
                                                              | Some te1, Some te2, Some te -> pp_ftype_mlir out te1; fprintf out ", !firrtl."; pp_ftype_mlir out te2; fprintf out ") -> !firrtl."; pp_ftype_mlir out te; ("%e"^(Int.to_string eflag3), eflag3 + 1)
                                                              | _, _, _ -> fprintf out "wrong expression type"; ("%e"^(Int.to_string eflag3), eflag3 + 1))
                                              | Firrtl.Bgt -> fprintf out "%%e%d = firrtl.gt %s, %s : (!firrtl." eflag3 eflag0 eflag2; 
                                                              (match ModuleGraph_simplified.type_of_expr e1 tmap, ModuleGraph_simplified.type_of_expr e2 tmap, ModuleGraph_simplified.type_of_expr e tmap with
                                                              | Some te1, Some te2, Some te -> pp_ftype_mlir out te1; fprintf out ", !firrtl."; pp_ftype_mlir out te2; fprintf out ") -> !firrtl."; pp_ftype_mlir out te; ("%e"^(Int.to_string eflag3), eflag3 + 1)
                                                              | _, _, _ -> fprintf out "wrong expression type"; ("%e"^(Int.to_string eflag3), eflag3 + 1))
                                              | Firrtl.Bgeq -> fprintf out "%%e%d = firrtl.geq %s, %s : (!firrtl." eflag3 eflag0 eflag2; 
                                                              (match ModuleGraph_simplified.type_of_expr e1 tmap, ModuleGraph_simplified.type_of_expr e2 tmap, ModuleGraph_simplified.type_of_expr e tmap with
                                                              | Some te1, Some te2, Some te -> pp_ftype_mlir out te1; fprintf out ", !firrtl."; pp_ftype_mlir out te2; fprintf out ") -> !firrtl."; pp_ftype_mlir out te; ("%e"^(Int.to_string eflag3), eflag3 + 1)
                                                              | _, _, _ -> fprintf out "wrong expression type"; ("%e"^(Int.to_string eflag3), eflag3 + 1))
                                              | Firrtl.Beq -> fprintf out "%%e%d = firrtl.eq %s, %s : (!firrtl." eflag3 eflag0 eflag2; 
                                                              (match ModuleGraph_simplified.type_of_expr e1 tmap, ModuleGraph_simplified.type_of_expr e2 tmap, ModuleGraph_simplified.type_of_expr e tmap with
                                                              | Some te1, Some te2, Some te -> pp_ftype_mlir out te1; fprintf out ", !firrtl."; pp_ftype_mlir out te2; fprintf out ") -> !firrtl."; pp_ftype_mlir out te; ("%e"^(Int.to_string eflag3), eflag3 + 1)
                                                              | _, _, _ -> fprintf out "wrong expression type"; ("%e"^(Int.to_string eflag3), eflag3 + 1))
                                              | Firrtl.Bneq -> fprintf out "%%e%d = firrtl.neq %s, %s : (!firrtl." eflag3 eflag0 eflag2; 
                                                              (match ModuleGraph_simplified.type_of_expr e1 tmap, ModuleGraph_simplified.type_of_expr e2 tmap, ModuleGraph_simplified.type_of_expr e tmap with
                                                              | Some te1, Some te2, Some te -> pp_ftype_mlir out te1; fprintf out ", !firrtl."; pp_ftype_mlir out te2; fprintf out ") -> !firrtl."; pp_ftype_mlir out te; ("%e"^(Int.to_string eflag3), eflag3 + 1)
                                                              | _, _, _ -> fprintf out "wrong expression type"; ("%e"^(Int.to_string eflag3), eflag3 + 1)))
                          | Firrtl.Bdshl -> fprintf out "%%e%d = firrtl.dshl %s, %s : (!firrtl." eflag3 eflag0 eflag2; 
                                          (match ModuleGraph_simplified.type_of_expr e1 tmap, ModuleGraph_simplified.type_of_expr e2 tmap, ModuleGraph_simplified.type_of_expr e tmap with
                                          | Some te1, Some te2, Some te -> pp_ftype_mlir out te1; fprintf out ", !firrtl."; pp_ftype_mlir out te2; fprintf out ") -> !firrtl."; pp_ftype_mlir out te; ("%e"^(Int.to_string eflag3), eflag3 + 1)
                                          | _, _, _ -> fprintf out "wrong expression type"; ("%e"^(Int.to_string eflag3), eflag3 + 1))
                          | Firrtl.Bdshr -> fprintf out "%%e%d = firrtl.dshr %s, %s : (!firrtl." eflag3 eflag0 eflag2; 
                                          (match ModuleGraph_simplified.type_of_expr e1 tmap, ModuleGraph_simplified.type_of_expr e2 tmap, ModuleGraph_simplified.type_of_expr e tmap with
                                          | Some te1, Some te2, Some te -> pp_ftype_mlir out te1; fprintf out ", !firrtl."; pp_ftype_mlir out te2; fprintf out ") -> !firrtl."; pp_ftype_mlir out te; ("%e"^(Int.to_string eflag3), eflag3 + 1)
                                          | _, _, _ -> fprintf out "wrong expression type"; ("%e"^(Int.to_string eflag3), eflag3 + 1))
                          | Firrtl.Band -> fprintf out "%%e%d = firrtl.and %s, %s : (!firrtl." eflag3 eflag0 eflag2; 
                                          (match ModuleGraph_simplified.type_of_expr e1 tmap, ModuleGraph_simplified.type_of_expr e2 tmap, ModuleGraph_simplified.type_of_expr e tmap with
                                          | Some te1, Some te2, Some te -> pp_ftype_mlir out te1; fprintf out ", !firrtl."; pp_ftype_mlir out te2; fprintf out ") -> !firrtl."; pp_ftype_mlir out te; ("%e"^(Int.to_string eflag3), eflag3 + 1)
                                          | _, _, _ -> fprintf out "wrong expression type"; ("%e"^(Int.to_string eflag3), eflag3 + 1))
                          | Firrtl.Bor -> fprintf out "%%e%d = firrtl.or %s, %s : (!firrtl." eflag3 eflag0 eflag2; 
                                          (match ModuleGraph_simplified.type_of_expr e1 tmap, ModuleGraph_simplified.type_of_expr e2 tmap, ModuleGraph_simplified.type_of_expr e tmap with
                                          | Some te1, Some te2, Some te -> pp_ftype_mlir out te1; fprintf out ", !firrtl."; pp_ftype_mlir out te2; fprintf out ") -> !firrtl."; pp_ftype_mlir out te; ("%e"^(Int.to_string eflag3), eflag3 + 1)
                                          | _, _, _ -> fprintf out "wrong expression type"; ("%e"^(Int.to_string eflag3), eflag3 + 1))
                          | Firrtl.Bxor -> fprintf out "%%e%d = firrtl.xor %s, %s : (!firrtl." eflag3 eflag0 eflag2; 
                                          (match ModuleGraph_simplified.type_of_expr e1 tmap, ModuleGraph_simplified.type_of_expr e2 tmap, ModuleGraph_simplified.type_of_expr e tmap with
                                          | Some te1, Some te2, Some te -> pp_ftype_mlir out te1; fprintf out ", !firrtl."; pp_ftype_mlir out te2; fprintf out ") -> !firrtl."; pp_ftype_mlir out te; ("%e"^(Int.to_string eflag3), eflag3 + 1)
                                          | _, _, _ -> fprintf out "wrong expression type"; ("%e"^(Int.to_string eflag3), eflag3 + 1))
                          | Firrtl.Bcat -> fprintf out "%%e%d = firrtl.cat %s, %s : (!firrtl." eflag3 eflag0 eflag2; 
                                          (match ModuleGraph_simplified.type_of_expr e1 tmap, ModuleGraph_simplified.type_of_expr e2 tmap, ModuleGraph_simplified.type_of_expr e tmap with
                                          | Some te1, Some te2, Some te -> pp_ftype_mlir out te1; fprintf out ", !firrtl."; pp_ftype_mlir out te2; fprintf out ") -> !firrtl."; pp_ftype_mlir out te; ("%e"^(Int.to_string eflag3), eflag3 + 1)
                                          | _, _, _ -> fprintf out "wrong expression type"; ("%e"^(Int.to_string eflag3), eflag3 + 1)))
  | HiFirrtl.Emux (c, e1, e2) -> let (eflag0, eflag1) = pp_expr_mlir out eflag tmap c in
                                 let (eflag2, eflag3) = pp_expr_mlir out eflag1 tmap e1 in 
                                 let (eflag4, eflag5) = pp_expr_mlir out eflag3 tmap e2 in 
                                 fprintf out "%%e%d = firrtl.mux(%s, %s, %s) : (!firrtl." eflag3 eflag0 eflag2 eflag4;
                                 (match ModuleGraph_simplified.type_of_expr c tmap, ModuleGraph_simplified.type_of_expr e1 tmap, ModuleGraph_simplified.type_of_expr e2 tmap, ModuleGraph_simplified.type_of_expr e tmap with
                                 | Some tc, Some te1, Some te2, Some te -> pp_ftype_mlir out tc; fprintf out ", !firrtl."; pp_ftype_mlir out te1; fprintf out ", !firrtl."; pp_ftype_mlir out te2; fprintf out ") -> !firrtl."; pp_ftype_mlir out te; ("%e"^(Int.to_string eflag5), eflag5 + 1)
                                 | _, _, _, _ -> fprintf out "wrong expression type"; ("%e"^(Int.to_string eflag5), eflag5 + 1))
  | HiFirrtl.Eref ref -> (match ref with
                        | Eid var -> (*fprintf out "%%%d" (pair2nat (Obj.magic var));*) ("%"^(Int.to_string (pair2nat (Obj.magic var))), eflag)
                        | _ -> fprintf out "wrong identifier"; (Int.to_string eflag, eflag))
  | HiFirrtl.Evalidif _ -> fprintf out "wrong expression validif"; (Int.to_string eflag, eflag)

let pp_stmt_mlir out eflag tmap s =
  match s with
  | HiFirrtl.Sskip -> fprintf out "firrtl.skip"; eflag
  | HiFirrtl.Swire (v, ty) -> fprintf out "%%%d = firrtl.wire : !firrtl." (pair2nat (Obj.magic v)); pp_ftype_mlir out ty; eflag
  | HiFirrtl.Smem _ -> fprintf out "memory"; eflag
  | HiFirrtl.Sfcnct (Eid v, Eref (Eid e)) -> (match CEP.find v tmap with
                                  | Some tv -> (match CEP.find v tmap with
                                        | Some te -> (if (HiEnv.ftype_not_implicit te) then 
                                                      (if ((sizeof_ftype tv) > (sizeof_ftype te)) then
                                                        (fprintf out "%%e%d = firrtl.pad %%%d, %d : (!firrtl." eflag (pair2nat (Obj.magic e)) (sizeof_ftype tv); pp_ftype_mlir out te; fprintf out ") -> !firrtl."; pp_ftype_mlir out tv;)
                                                      else (if ((sizeof_ftype tv) < (sizeof_ftype te)) then 
                                                              (fprintf out "%%e%d = firrtl.tail %%%d, %d : (!firrtl." eflag (pair2nat (Obj.magic e)) ((sizeof_ftype te) - (sizeof_ftype tv)); pp_ftype_mlir out te; fprintf out ") -> !firrtl."; pp_ftype_mlir out tv;)
                                                            else fprintf out "";))
                                                     else
                                                      (fprintf out "%%e%d = firrtl.widthCast %%%d : (!firrtl." eflag (pair2nat (Obj.magic e)); pp_ftype_mlir out te; fprintf out ") -> !firrtl."; pp_ftype_mlir out tv;));
                                         fprintf out "firrtl.strictconnect %%%d, %%%d : !firrtl." (pair2nat (Obj.magic v)) (pair2nat (Obj.magic e)); pp_ftype_mlir out tv; eflag + 1
                                         | _ -> fprintf out "wrong variable name\n"; eflag)
                                  | _ -> fprintf out "wrong variable name\n"; eflag)
  | HiFirrtl.Sfcnct (Eid v, e) -> let (eflag0, eflag1) = pp_expr_mlir out eflag tmap e in (match CEP.find v tmap with
                                  | Some tv -> fprintf out "firrtl.strictconnect %%%d, %s : !firrtl." (pair2nat (Obj.magic v)) eflag0; pp_ftype_mlir out tv; fprintf out "\n"; eflag1
                                  | _ -> fprintf out "wrong variable name\n"; eflag1)
  | HiFirrtl.Sinvalid (Eid v) -> fprintf out "%%e%d = firrtl.invalidvalue : !firrtl." eflag; (match CEP.find v tmap with
                                  | Some tv -> pp_ftype_mlir out tv; fprintf out "\n"; 
                                               fprintf out "firrtl.strictconnect %%%d, %%e%d : !firrtl." (pair2nat (Obj.magic v)) eflag; pp_ftype_mlir out tv; fprintf out "\n"; eflag + 1
                                  | _ -> fprintf out "wrong variable name\n"; eflag + 1)
  | HiFirrtl.Snode (v, e) -> let (eflag0, eflag1) = pp_expr_mlir out eflag tmap e in (match CEP.find v tmap with
                                  | Some tv -> fprintf out "\n%%%d = firrtl.node %s : !firrtl." (pair2nat (Obj.magic v)) eflag0; pp_ftype_mlir out tv; eflag1
                                  | _ -> fprintf out "wrong variable name\n"; eflag1)
  | HiFirrtl.Sreg (v, r) ->
     (match r.reset with
     | HiFirrtl.NRst -> let (eflag0, eflag1) = pp_expr_mlir out eflag tmap r.clock in
       fprintf out "%%%d = firrtl.reg %s : !firrtl.clock, !firrtl." (pair2nat (Obj.magic v)) eflag0; pp_ftype_mlir out r.coq_type; eflag1
     | HiFirrtl.Rst (e1, e2) -> (let (eflag0, eflag1) = pp_expr_mlir out eflag tmap r.clock in
       let (eflag2, eflag3) = pp_expr_mlir out eflag1 tmap e1 in
       let (eflag4, eflag5) = pp_expr_mlir out eflag3 tmap e2 in
       match ModuleGraph_simplified.type_of_expr e1 tmap, ModuleGraph_simplified.type_of_expr e2 tmap with
       | Some te1, Some te2 -> fprintf out "%%%d = firrtl.regreset %s, %s, %s : !firrtl.clock, !firrtl." (pair2nat (Obj.magic v)) eflag0 eflag2 eflag4; 
         pp_ftype_mlir out te1; fprintf out ", !firrtl."; pp_ftype_mlir out te2; fprintf out ", !firrtl."; pp_ftype_mlir out r.coq_type; eflag5
       | _, _ -> fprintf out "wrong expression type"; eflag5))
  | HiFirrtl.Sinst _ -> fprintf out "inst"; eflag
  | HiFirrtl.Swhen _ -> fprintf out "when"; eflag
  | _ -> fprintf out "wrong id"; eflag

(*let rec pp_statement out s =
  match s with
  | Sskip -> fprintf out "sskip\n"
  | Swire (r, ty) -> fprintf out "(swire "; fprintf out " (%d, %d)" (fst (Obj.magic r)) (snd (Obj.magic r)); pp_ftype_mlir out ty; fprintf out ")\n"
  | Smem (r, _) -> fprintf out "smem ( "; fprintf out " (%d, %d)" (fst (Obj.magic r)) (snd (Obj.magic r)); (*pp_type out (m.data_type); fprintf out "Depth ";
   fprintf out (Int.to_string m.depth); fprintf out " ReadL "; fprintf out (Int.to_string m.read_latency); fprintf out " WriteL "; 
   fprintf out (Int.to_string m.write_latency); fprintf out "  Reader "; List.iter (fun c ->  fprintf out (c^" "); fprintf out "") m.reader; 
   fprintf out " Writer "; List.iter (fun c ->  fprintf out (c^" "); fprintf out "") m.writer; fprintf out " "; fprintf out " RuW "; 
   pp_ruw out (m.read_write);*) fprintf out ")\n"
  | Sfcnct (Eid r, e2) -> fprintf out "(sfcnct "; fprintf out " (%d, %d)" (fst (Obj.magic r)) (snd (Obj.magic r)); fprintf out " "; pp_expr out e2; fprintf out ")\n"
  | Sinvalid (Eid r) -> fprintf out "(sinvalid "; fprintf out " (%d, %d)" (fst (Obj.magic r)) (snd (Obj.magic r)); fprintf out ")\n"
  | Sreg (ref, r) ->
     (match r.reset with
     | NRst -> fprintf out "sreg ( "; fprintf out " (%d, %d)" (fst (Obj.magic ref)) (snd (Obj.magic ref)); pp_ftype_mlir out (r.coq_type); fprintf out " "; pp_expr out r.clock; fprintf out " NRst)\n"
     | Rst (e1, e2) ->
        fprintf out "sreg ( "; fprintf out " (%d, %d)" (fst (Obj.magic ref)) (snd (Obj.magic ref)); pp_ftype_mlir out (r.coq_type); fprintf out " "; pp_expr out r.clock; fprintf out " (rrst "; pp_expr out e1; fprintf out " "; pp_expr out e2; fprintf out "))\n")
  | Snode (r, e) -> fprintf out "(snode "; fprintf out " (%d, %d)" (fst (Obj.magic r)) (snd (Obj.magic r)); pp_expr out e; fprintf out ")\n"
  | Sinst (r, e) -> fprintf out "(sinst "; fprintf out " (%d, %d)" (fst (Obj.magic r)) (snd (Obj.magic r)); fprintf out "of "; fprintf out " (%d, %d)" (fst (Obj.magic e)) (snd (Obj.magic e)); fprintf out ")\n"
  | Swhen (c, s1, s2) -> fprintf out "(swhen "; pp_expr out c; fprintf out "\nthen [::"; pp_statements out s1; fprintf out "]\nelse \n [::"; pp_statements out s2; fprintf out "])\n"
  | _ -> fprintf out "wrong id"
and pp_statements out sl = 
  match sl with
  | Qnil -> fprintf out "";
  | Qcons (s, ss) -> pp_statement out s; fprintf out "\n"; pp_statements out ss
         
let pp_module out cn fmod = (* 只存在1个module的情况，与circuit同名 *)
  match fmod with
  | HiFirrtl.FInmod (_, pl, sl) -> fprintf out "firrtl.module @"; fprintf out "%s(" cn; 
    pp_ports_mlir out pl; fprintf out (") {\n"); let _ = pp_statements out sl in fprintf out "}\n"
  | HiFirrtl.FExmod _ -> fprintf out "extmod .. \n"
    *)
let rec pp_stmts_mlir out sl eflag tmap =
  match sl with
  | HiFirrtl.Qnil -> fprintf out ""; eflag
  | HiFirrtl.Qcons (s, ss) -> let eflag0 = pp_stmt_mlir out eflag tmap s in 
                           fprintf out "\n"; pp_stmts_mlir out ss eflag0 tmap

let pp_module_mlir out cn tmap fmod = (* 只存在1个module的情况，与circuit同名 *)
  match fmod with
  | HiFirrtl.FInmod (_, pl, sl) -> fprintf out "firrtl.circuit \""; fprintf out "%s\"{\n" cn;
                                   fprintf out "firrtl.module @"; fprintf out "%s(" cn; 
    pp_ports_mlir out pl; fprintf out (") {\n"); let _ = pp_stmts_mlir out sl 0 tmap in fprintf out "}\n"; fprintf out "}\n"
  | HiFirrtl.FExmod _ -> fprintf out "extmod .. \n"
          
let pp_modules_mlir out cn tmap fmod = (*List.iter (fun c -> pp_module_mlir out c; fprintf out "}\n") fmod*) pp_module_mlir out cn tmap (List.hd fmod)

let pp_fcircuit_mlir out cn tmap fc = 
  match fc with
  | HiFirrtl.Fcircuit (_, fmod) -> fprintf out "firrtl.circuit \""; fprintf out "%s\"{\n" cn; pp_modules_mlir out cn tmap fmod; fprintf out "}\n"

let hiparse f =
  let lexbuf = Lexing.from_channel (open_in f) in
  FirrtlParser.file FirrtlLexer.token lexbuf

let hif_ast = hiparse "./demo/hifir/circt/pretest1.fir"

let () =
  let out = open_out "./demo/output.txt" in
  match hif_ast with
  | Ast.Fcircuit (_, ml) -> let (map0, _, flag) = mapmod (initmap_s, 0) (List.hd ml) in 
    (*StringMap.iter (fun key (value1, value2) -> (printf "%s: (%d, %d)" key value1 value2); printf "\n") map0;
    StringMap.iter (fun key value -> (printf "%s: " key; Ast.pp_type stdout value); printf "\n") tmap0;*)
  (*let _ = trans_cir hif_ast map0 flag in*)
    let fmod = trans_mod (List.hd ml) map0 flag in
    let ut1 = (Unix.times()).tms_utime in

    (*match fmod with
    | FInmod (_, ps, ss) -> (match InferWidth_new.ports_tmap' ps with
      | Some pmap -> (match InferWidth_new.stmts_tmap' pmap CEP.empty ss with
        | Some (tmap, _) -> (match InferWidth_new.type_of_expr (Eref (Eid (Obj.magic (4,0)))) tmap with 
          | Some _ -> printf "1"
          | _ -> printf "5")
        | _ -> printf "4")
      | _ -> printf "3")
    | _ -> printf "2"*)

    match InferWidth_new.coq_InferWidths_m fmod with
    | Some (m, _) -> let ut2 = (Unix.times()).tms_utime in 
                        (*pp_module_mlir out "Foo" tmap0 m; 
                        pp_module_mlir out "Foo" (ExpandConnects_new.rcd_pmap_from_m m CEP.empty) (ExpandConnects_new.expandconnects_fmodule m (ExpandConnects_new.rcd_pmap_from_m m CEP.empty));*)
                        (*match CEP.find (Obj.magic (0, 3)) (ExpandConnects_new.rcd_pmap_from_m m CEP.empty) with
                        | Some t -> pp_ftype_mlir stdout t
                        | _ -> printf "12"*)
                        let m1 = (ExpandConnects_new.expandconnects_fmodule m (ExpandConnects_new.rcd_pmap_from_m m CEP.empty)) in
                        let ut3 = (Unix.times()).tms_utime in
                        (match (ExpandWhens.coq_ExpandWhens_fun m1) with
                        | Some fm -> let ut4 = (Unix.times()).tms_utime in
                        pp_module_mlir out "Foo" (*ExpandConnects_new.output_ft_pmap m tmap*)(ExpandConnects_new.rcd_pmap_from_m m CEP.empty) fm
                        ; printf "%f\n%f\n%f\n" (Float.sub ut2 ut1) (Float.sub ut3 ut2) (Float.sub ut4 ut3)
                        | _ -> printf "12")

    | _ -> printf "11"
