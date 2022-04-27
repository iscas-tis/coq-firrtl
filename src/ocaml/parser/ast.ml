   
(** Types *)

type size = Z.t

type fgtyp =
  Tuint of size
| Tsint of size
| Clock

let uint_t w = Tuint w
let int_t w = Tsint w

type var = string
             
(** Operators *)

type ucast =
  | AsUint | AsSInt | AsFixed | AsClock
              
type eunop =
  | Upadding of Z.t
  | Ucast of ucast
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
  | Uincp
  | Udecp
  | Usetp
              
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

type fexpr =
  | Econst of int
  | Eref of var
  | Edeclare of var * fgtyp
  (* | Efield of var * fexpr
  | Esubacc of var * Z.t *)
  | Eprim_unop of eunop * fexpr
  | Eprim_binop of ebinop * fexpr * fexpr
  | Emux of fexpr * fexpr * fexpr
  | Evalidif of fexpr
                                   
type ruw =
  | RUWold | RUWnew | RUWundefined


type fmem =
  {
    mid : var;
    data_type : fexpr;
    depth : Z.t;
    reader : var list;
    writer : var list;                    
    read_latency : Z.t;
    write_latency : Z.t;
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

let mkfreg v t c e1 e2 = { rid = v; rtype = t; clock = c; reset = Rst (e1, e2) }
  
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
  | Tuint s -> output_string out "(Tunit "; output_string out (Z.to_string s); output_string out ")"
  | Tsint s -> output_string out "(Tsnit "; output_string out (Z.to_string s); output_string out ")"
  | Clock -> output_string out "Clock"
          
let pp_unop out op =
  match op with
  | Unot -> output_string out "Unot ";
  | _ -> output_string out ""
       
let pp_binop out op =
  match op with
  | Badd -> output_string out "Badd ";
  | _ -> output_string out ""
          
let rec pp_expr out e =
  match e with
  | Eref v -> output_string out "(Eref "; output_string out (v^" "); output_string out ")"
  | Edeclare (v, ty) -> output_string out "(Edeclare "; output_string out (v^" "); output_string out " "; pp_type out ty; output_string out ")\n"
  | Eprim_unop (op, e1) -> output_string out "(Eprim_unop "; pp_unop out op; pp_expr out e1; output_string out ")"
  | Eprim_binop (bop, e1, e2) -> output_string out "(Eprim_binop "; pp_binop out bop; pp_expr out e1; output_string out " "; pp_expr out e2; output_string out ")"
  | _ -> output_string out ""

let pp_exprs out el =  List.iter (fun c -> pp_expr out c; output_string out "") el

let rec pp_ports out pl =  List.iter (fun c -> pp_port out c; output_string out "") pl
                     
and pp_port out p =
  match p with
  | Finput (v, ty) -> output_string out "(Finput "; output_string out (v^" "); pp_type out ty; output_string out ")\n"
  | Foutput (v, ty) -> output_string out "(Foutput "; output_string out (v^" "); pp_type out ty; output_string out ")\n"                 
                 
                       
let rec pp_statements out sl = List.iter (fun c -> pp_statement out c; output_string out "") sl
                             
and  pp_statement out s =
  match s with
  | Sskip -> output_string out "(Sskip)"
  | Swire (v, ty) -> output_string out "(Swire "; output_string out (v^" "); pp_type out ty; output_string out ")\n"
  | Sfcnct (e1, e2) -> output_string out "(Sfcnct "; pp_expr out e1; output_string out " "; pp_expr out e2; output_string out ")\n"
  | Spcnct (e1, e2) -> output_string out "(Spcnct "; pp_expr out e1; output_string out " "; pp_expr out e2; output_string out ")\n"
  | Swhen (e, s1, s2) -> output_string out "(Swhen "; pp_expr out e; pp_statement out s1; pp_statement out s2; output_string out ")\n"
  | Sreg r ->
     (match r.reset with
     | NRst -> output_string out "Sreg (mk_freg ("; output_string out ((r.rid)^" "); pp_type out (r.rtype); output_string out " "; pp_expr out (r.clock); output_string out "NRst)\n"
     | Rst (e1, e2) ->
        output_string out "Sreg (mk_freg ("; output_string out ((r.rid)^" "); pp_type out (r.rtype); output_string out " "; pp_expr out (r.clock); output_string out " "; output_string out "(Rst "; pp_expr out e1; output_string out " "; pp_expr out e2; output_string out ")\n")
  | Snode (v, e) -> output_string out "(Snode "; output_string out (v^" "); pp_expr out e; output_string out ")\n"
  | _ -> output_string out ""
                 
          
let pp_module out fmod =
  match fmod with
  | FInmod (v, pl, sl) -> output_string out "(FInmod "; output_string out (v^"\n"); pp_ports out pl; pp_statements out sl; output_string out ")\n"
  | _ -> output_string out "\n"
          
let pp_modules out fmod = List.iter (fun c -> pp_module out c; output_string out "") fmod

let pp_fcircuit out fc =
  match fc with
  | (v, fmod) -> output_string out "(FCircuit "; output_string out (v^"\n"); pp_modules out fmod; output_string out ")\n"

let pp_file out fc = pp_fcircuit out fc
