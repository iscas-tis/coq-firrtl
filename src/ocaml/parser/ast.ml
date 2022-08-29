
(** Types *)
open Extraction.NBitsDef

type nat = Z.t

type fgtyp =
| Fuint of nat
| Fsint of nat
| Fclock

let sizeof_fgtyp fgtyp =
  match fgtyp with
  | Fuint w -> w
  | Fsint w -> w
  | Fclock -> Z.one

type var = string
             
(** Operators *)

type ucast =
  | AsUInt | AsSInt | AsClock
              
type eunop =
  | Upad of Z.t
  | Ushl of Z.t
  | Ushr of Z.t
  | Ucvt
  | Uneg
  | Unot
  | Uandr
  | Uorr
  | Uxorr
  | Uextr of Z.t * Z.t
  | Uhead of Z.t
  | Utail of Z.t
  | Ubits of Z.t * Z.t
  (*| Uincp
  | Udecp
  | Usetp*)
              
type bcmp =
  | Blt | Bleq | Bgt | Bgeq | Beq | Bneq

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
  | Bsdiv
  | Bsrem

type fexpr =
  | Econst of fgtyp * Z.t
  | Eref of var
  (*| Edeclare of var * fgtyp
  | Efield of fexpr * fexpr
  | Esubacc of var * Z.t *)
  | Eprim_unop of eunop * fexpr
  | Eprim_binop of ebinop * fexpr * fexpr
  | Emux of fexpr * fexpr * fexpr
  | Evalidif of fexpr * fexpr
  | Ecast of ucast * fexpr
                                   
type ruw =
  | Mold | Mnew | Mundefined


type fmem =
  {
    mid : var;
    data_type : fgtyp;
    depth : Z.t;
    read_latency : Z.t;
    write_latency : Z.t;
    reader : var list;
    writer : var list; 
    read_write : ruw
  }

type rst =
  | NRst 
  | Rst of fexpr * fexpr

  
type freg =
  {
    rid : var;
    rtype : fgtyp;
    clock : fexpr;
    reset : rst
  }

let mk_freg v t c e1 e2 = { rid = v; rtype = t; clock = c; reset = Rst (e1, e2) }
let mk_fmem v e z1 z2 z3 vl1 vl2 r = { mid = v; data_type = e; depth = z1;  read_latency = z2; write_latency = z3; reader = vl1; writer = vl2; read_write = r }
let  mk_fmem_non v e z1 z2 z3 r = { mid = v; data_type = e; depth = z1;  read_latency = z2; write_latency = z3; reader = []; writer = []; read_write = r }
let mk_fmem_r v e z1 z2 z3 vl r = { mid = v; data_type = e; depth = z1;  read_latency = z2; write_latency = z3; reader = vl; writer = []; read_write = r }


type fstmt =
  | Sskip
  | Swire of var * fgtyp
  | Sreg of freg
  | Smem of fmem
  | Sinst of var * var
  | Snode of var * fexpr
  | Sfcnct of fexpr * fexpr
  | Spcnct of fexpr * fexpr
  | Sinvalid of var
  (*  | Sattach of var list *)
  | Swhen of fexpr * fstmt * fstmt
  | Sstop of fexpr * fexpr * Z.t
  | Sprintf (* TBD *)
  | Sassert (* TBD *)
  | Sassume (* TBD *)
  | Sdefname of var (* TBD *)
  | Sparam of var * fexpr (* TBD *)

type fport =
  | Finput of var * fgtyp
  | Foutput of var * fgtyp

type fmodule =
  | FInmod of var * fport list * fstmt list
  | FExmod of var * fport list * fstmt list

type fcircuit = var * fmodule list
                  
type file = fcircuit

let pp_type out ty =
 match ty with
 | Fuint s -> output_string out "(Fuint "; output_string out (Z.to_string s); output_string out ")"
 | Fsint s -> output_string out "(Fsint "; output_string out (Z.to_string s); output_string out ")"
 | Fclock -> output_string out "Fclock"

let pp_cast out cst = 
 match cst with
 | AsUInt -> output_string out "AsUInt"
 | AsSInt -> output_string out "AsSInt"
 (*| AsFixed ->  output_string out "AsFixed"*)
 | AsClock -> output_string out "AsUint "
         
let pp_unop out op =
 match op with
 | Upad s -> output_string out "(Upad "; output_string out (Z.to_string s); output_string out ")" 
 | Ushl s -> output_string out "(Ushl "; output_string out (Z.to_string s); output_string out")"
 | Ushr s -> output_string out "(Ushr "; output_string out (Z.to_string s); output_string out")"
 | Ucvt -> output_string out "Ucvt"
 | Uneg -> output_string out "Uneg"
 | Unot -> output_string out "Unot "
 | Uandr -> output_string out "Uandr"
 | Uorr -> output_string out "Uorr"
 | Uxorr -> output_string out "Uxorr"
 | Uextr (s1, s2) -> output_string out "(Uextr "; output_string out (Z.to_string s1);  output_string out " "; output_string out (Z.to_string s2); output_string out")"
 | Uhead s -> output_string out "(Uhead "; output_string out (Z.to_string s); output_string out")"
 | Utail s -> output_string out "(Utail "; output_string out (Z.to_string s); output_string out")"
 | Ubits (s1,s2)  -> output_string out "(Ubits "; output_string out (Z.to_string s1); output_string out " "; output_string out (Z.to_string s2); output_string out")"
 (*| Uincp -> output_string out "Uincp"
 | Udecp -> output_string out "Udecp"
 | Usetp -> output_string out "Usetp"
 | _ -> output_string out "" *)

let pp_comp out cmp = 
 match cmp with
 | Blt -> output_string out "Blt" 
 | Bleq -> output_string out "Bleq"
 | Bgt -> output_string out "Bgt"
 | Bgeq -> output_string out "Bgeq"
 | Beq -> output_string out "Beq"
 | Bneq -> output_string out "Bneq"
      
let pp_binop out op =
 match op with
 | Badd -> output_string out "Badd "
 | Bsub -> output_string out "Bsub "
 | Bmul -> output_string out "Bmul"
 | Bdiv -> output_string out "Bdiv"
 | Brem -> output_string out "Brem"
 | Bcomp s -> output_string out "Bcomp("; pp_comp out s; output_string out")"
 | Bdshl -> output_string out "Bdshl "
 | Bdshr -> output_string out "Bdshr "
 | Band -> output_string out "Band "
 | Bor -> output_string out "Bor "
 | Bxor -> output_string out "Bxor "
 | Bcat -> output_string out "Bcat "
 | Bsdiv -> output_string out "Bsdiv "
 | Bsrem -> output_string out "Bsrem "
 (* | _ -> output_string out "" *)
         
let rec pp_expr out e =
 match e with
 | Econst (ty, s) -> output_string out "(econst "; pp_type out ty; output_string out " [::b"; output_string out (Z.format "%b" s) ; output_string out"])"
 | Eref v -> output_string out "(eref "; output_string out (v^" "); output_string out ")"
 (*| Edeclare (v, ty) -> output_string out "(edeclare "; output_string out (v^" "); output_string out " "; pp_type out ty; output_string out ")\n"
 | Esubacc (v, s) -> output_string out "(Esubacc "; output_string out (v^" "); output_string out " "; output_string out (Z.to_string s); output_string out ")\n" *)
 | Eprim_unop (op, e1) -> output_string out "(eprim_unop "; pp_unop out op; pp_expr out e1; output_string out ")"
 | Eprim_binop (bop, e1, e2) -> output_string out "(eprim_binop "; pp_binop out bop; pp_expr out e1; output_string out " "; pp_expr out e2; output_string out ")"
 | Emux (e1,e2,e3)  -> output_string out "(emux "; pp_expr out e1; output_string out " "; pp_expr out e2; output_string out " "; pp_expr out e3; output_string out " "; output_string out ")"
 | Evalidif (e1,e2)  -> output_string out "(evalidif "; pp_expr out e1; output_string out " "; pp_expr out e2; output_string out ")"
 | Ecast (s, e) -> output_string out "(ecast "; pp_cast out s; output_string out " "; pp_expr out e; output_string out ")"
 (* | _ -> output_string out "" *)

 let pp_ruw out e = 
 match e with
 | Mold -> output_string out "old"
 | Mnew -> output_string out "new"
 | Mundefined -> output_string out "undefined"

let pp_exprs out el =  List.iter (fun c -> pp_expr out c; output_string out "") el

let rec pp_ports out pl =   output_string out "[::"; List.iter (fun c -> pp_port out c; output_string out "") pl;  output_string out "]\n";
                     
and pp_port out p =
  match p with
  | Finput (v, ty) -> output_string out "(Finput "; output_string out (v^" "); pp_type out ty; output_string out ")\n"
  | Foutput (v, ty) -> output_string out "(Foutput "; output_string out (v^" "); pp_type out ty; output_string out ")\n"                 
                 
                       
let rec pp_statements out sl =  output_string out "[::"; List.iter (fun c -> pp_statement out c; output_string out "") sl;  output_string out "]\n";
                             
and  pp_statement out s =
  match s with
  | Sskip -> output_string out "sskip"
  | Swire (v, ty) -> output_string out "(swire "; output_string out (v^" "); pp_type out ty; output_string out ")\n"
  | Smem m -> output_string out "smem ("; output_string out ((m.mid)^" "); pp_type out (m.data_type); output_string out "Depth "; output_string out (Z.to_string m.depth); output_string out " ReadL "; output_string out (Z.to_string m.read_latency); output_string out " WriteL "; output_string out (Z.to_string m.write_latency); output_string out "  Reader "; List.iter (fun c ->  output_string out (c^" "); output_string out "") m.reader; output_string out " Writer "; List.iter (fun c ->  output_string out (c^" "); output_string out "") m.writer; output_string out " "; output_string out " RuW "; pp_ruw out (m.read_write); output_string out ")\n"
  | Sinst (v1,v2) -> output_string out "(sinst "; output_string out (v1^" ");  output_string out " ";  output_string out (v2^" "); output_string out ")\n"
  | Sfcnct (e1, e2) -> output_string out "(sfcnct "; pp_expr out e1; output_string out " "; pp_expr out e2; output_string out ")\n"
  | Spcnct (e1, e2) -> output_string out "(spcnct "; pp_expr out e1; output_string out " "; pp_expr out e2; output_string out ")\n"
  | Sinvalid v -> output_string out "(sinvalid "; output_string out (v^" "); output_string out ")\n"
  | Swhen (e, s1, s2) -> output_string out "(swhen "; pp_expr out e; pp_statement out s1; pp_statement out s2; output_string out ")\n"
  | Sreg r ->
     (match r.reset with
     | NRst -> output_string out "sreg (mk_freg "; output_string out ((r.rid)^" "); pp_type out (r.rtype); output_string out " "; pp_expr out (r.clock); output_string out "NRst)\n"
     | Rst (e1, e2) ->
        output_string out "sreg (mk_freg "; output_string out ((r.rid)^" "); pp_type out (r.rtype); output_string out " "; pp_expr out (r.clock); output_string out " "; output_string out "(rrst "; pp_expr out e1; output_string out " "; pp_expr out e2; output_string out "))\n")
  | Sstop (e1,e2,s) -> output_string out "(sstop "; pp_expr out e1; pp_expr out e2; output_string out (Z.to_string s);  output_string out")\n"
  | Snode (v, e) -> output_string out "(snode "; output_string out (v^" "); pp_expr out e; output_string out ")\n"
  | _ -> output_string out ""
                 
          
let pp_module out fmod =
  match fmod with
  | FInmod (v, pl, sl) -> output_string out "(FInmod "; output_string out (v^"\n"); pp_ports out pl; pp_statements out sl; output_string out ").\n"
  | FExmod (v, pl, sl) -> output_string out "(FInmod "; output_string out (v^"\n"); pp_ports out pl; pp_statements out sl; output_string out ").\n"
  (* | _ -> output_string out "\n" *)
          
let pp_modules out fmod = List.iter (fun c -> pp_module out c; output_string out "") fmod

let pp_fcircuit out fc =
  match fc with
  | (v, fmod) -> output_string out "(FCircuit "; output_string out (v^"\n"); pp_modules out fmod; output_string out ")\n"

let pp_file out fc = pp_fcircuit out fc
