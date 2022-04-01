(*open Set*)

   
let fgtyp_delim = "@"
            
(** Types *)

type size = Z.t

type fgtyp =
  Tuint of size
| Tsint of size

let uint_t w = Tuint w
let int_t w = Tsint w
(*let bit_t = Tuint 1*)

(*
let z_two = Z.of_int 2

let string_of_fgtyp ty =
  match ty with
  | Tuint w -> "uint" ^ string_of_int w
  | Tsint w -> "int" ^ string_of_int w
let size_of_fgtyp ty =
  match ty with
  | Tuint w -> w
  | Tsint w -> w
let min_of_fgtyp ty =
  match ty with
  | Tuint _w -> Z.zero
  | Tsint w -> Z.neg (Z.pow z_two (w - 1))
let max_of_fgtyp ty =
  match ty with
  | Tuint w -> Z.sub (Z.pow z_two w) Z.one
  | Tsint w -> Z.sub (Z.pow z_two (w - 1)) Z.one
let fgtyp_is_signed ty =
  match ty with
  | Tsint _ -> true
  | Tuint _ -> false
let fgtyp_to_signed ty =
  match ty with
  | Tuint w -> Tsint w
  | Tsint _w -> ty
let fgtyp_to_unsigned ty =
  match ty with
  | Tuint _w -> ty
  | Tsint w -> Tuint w
 *)
            
type var = string
             
(*
(** Variables with SSA index taken into consideration *)

type var =
  {
    vname : string;     (* name of the variable *)
    vtyp : fgtyp;         (* type of the variable *)
    vsidx : int         (* SSA index of the variable *)
  }

let invalid_sidx i = i < 0
let default_non_ssa_idx = -1
(*
 * The string representation of a variable with SSA index taken into consideration
 * If the argument labeled with vtyp is true, the variable type is also output.
 *)
let string_of_var ?fgtyp:(fgtyp=false) v =
  let str =
    if invalid_sidx v.vsidx then v.vname
    else v.vname ^ "_" ^ string_of_int v.vsidx in
  if fgtyp then str ^ fgtyp_delim ^ string_of_fgtyp v.vtyp
  else str
let size_of_var v = size_of_fgtyp v.vtyp
let fgtyp_of_var v = v.vtyp
(* Two variables are equal if
 * - they have the same name and
 * - their SSA indices are equal.
 *)
let eq_var v1 v2 = v1.vname = v2.vname && v1.vsidx = v2.vsidx
let cmp_var v1 v2 =
  let c = Pervasives.compare v1.vname v2.vname in
  if c = 0 then Pervasives.compare v1.vsidx v2.vsidx
  else c
let mem_var v vs = List.exists (fun u -> eq_var u v) vs
let mkvar vn vt = { vname = vn; vtyp = vt; vsidx = default_non_ssa_idx }
let var_is_uint v =
  match v.vtyp with
  | Tuint _ -> true
  | _ -> false
let var_is_sint v =
  match v.vtyp with
  | Tsint _ -> true
  | _ -> false
let var_is_bit v = v.vtyp = bit_t
let var_is_signed v = fgtyp_is_signed v.vtyp

module VarElem : OrderedType with type t = var =
  struct
    type t = var
    let compare = cmp_var
  end
module VS = Set.Make(VarElem)
module VM = Map.Make(VarElem)


let vs_disjoint vs1 vs2 = VS.is_empty (VS.inter vs1 vs2)
let string_of_vs ?fgtyp:(fgtyp=false) vs = String.concat ", " (List.map (fun v -> string_of_var ~fgtyp:fgtyp v) (VS.elements vs))

(** Syntax *)

type numeral = Z.t

type decimal = string

(* A hexadecimal number is a string with MSB at the beginning *)
type hex = string

(* A binary number is a string of 0's and 1's with MSB at the head *)
type binary = string

type symbol = string
            
(* type spec_constant =
 *   | CNumeral of numeral
 *   | CDecimal of decimal
 *   | CHexDecimal of hex
 *   | CBinary of binary
 *   | CString of string
 * 
 * (\* A keyword always starts with a ":" *\)
 * type keyword = string
 * 
 * type attribute =
 *   | AKeyword of keyword
 *   | AConstant of keyword * spec_constant
 *   | ASymbol of keyword * symbol
 * 
 * type solver_option =
 *   | OKeyword of keyword
 *   | OConstant of keyword * spec_constant
 *   | OSymbol of keyword * symbol
 *              
 * type index =
 *   | INumeral of numeral
 *   | ISymbol of symbol
 * 
 * type identifier =
 *   | ISimple of symbol                             (\* Simple Identifier *\)
 *   | IIndexed of symbol * index list               (\* Indexed Identifier *\)
 * 
 * type sort =
 *   | SIdentifier of identifier
 *   | SApplication of identifier * sort list
 * 
 * type qual_identifier =
 *   | QIdentifier of identifier
 *   | QAnnotated of identifier * sort
 * 
 * type var_binding = symbol * term
 * 
 * and term =
 *   | TConstant of spec_constant
 *   | TVariable of qual_identifier
 *   | TApplication of qual_identifier * term list
 *   | TLet of var_binding list * term
 * 
 * type sorted_var = symbol * sort
 * 
 * type command =
 *   | CSetLogic of symbol
 *   | CSetInfo of attribute
 *   | CSetOption of solver_option
 *   | CDeclareFun of symbol * sort list * sort
 *   | CDefineFun of symbol * sorted_var list * sort * term
 *   | CAssert of term
 *   | CCheckSat
 *   | CGetModel
 *   | CExit
 *   | CComment of string *)
 *)
             
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
  | Evar of var
  | Eref of var * fgtyp
  | Efield of var * fexpr
  | Esubacc of var * Z.t
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

type freg =
  {
    rid : var;
    rtype : fexpr;
    reset : fexpr list
  }

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
  | Sattach of var list
  | Swhen of fexpr * fstmt * fstmt
  | Sstop of fexpr * fexpr * Z.t
  | Sprintf (* TBD *)
  | Sassert (* TBD *)
  | Sassume (* TBD *)
  | Sdefname of var (* TBD *)
  | Sparam of var * fexpr (* TBD *)

type fport =
  | Finput of fexpr
  | Foutput of fexpr

type fmodule =
  | FInmod of var * fport list * fstmt list
  | FExmod of var * fport list * fstmt list

type fcircuit = var * fmodule list
                  
type file = fcircuit


let pp_type out ty =
  match ty with
  | Tuint s -> output_string out "(Tunit "; output_string out (Z.to_string s); output_string out ")"
  | Tsint s -> output_string out "(Tsnit "; output_string out (Z.to_string s); output_string out ")"
          
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
  | Evar v -> output_string out "(Evar "; output_string out (v^" "); output_string out ")"
  | Eref (v, ty) -> output_string out "(Eref "; output_string out (v^" "); output_string out " "; pp_type out ty; output_string out ")\n"
  | Eprim_unop (op, e1) -> output_string out "(Eprim_unop "; pp_unop out op; pp_expr out e1; output_string out ")"
  | Eprim_binop (bop, e1, e2) -> output_string out "(Eprim_binop "; pp_binop out bop; pp_expr out e1; output_string out " "; pp_expr out e2; output_string out ")"
  | _ -> output_string out ""

let pp_exprs out el =  List.iter (fun c -> pp_expr out c; output_string out "") el

let rec pp_ports out pl =  List.iter (fun c -> pp_port out c; output_string out "") pl
                     
and pp_port out p =
  match p with
  | Finput e -> output_string out "(Finput "; pp_expr out e; output_string out ")\n"
  | Foutput e -> output_string out "(Foutput "; pp_expr out e; output_string out ")\n"                 
                 

let rec pp_statements out sl = List.iter (fun c -> pp_statement out c; output_string out "") sl
                             
and  pp_statement out s =
  match s with
  | Sskip -> output_string out "(Sskip)"
  | Swire (v, ty) -> output_string out "(Swire "; output_string out (v^" "); pp_type out ty; output_string out ")\n"
  | Sfcnct (e1, e2) -> output_string out "(Sfcnct "; pp_expr out e1; output_string out " "; pp_expr out e2; output_string out ")\n"
  | Spcnct (e1, e2) -> output_string out "(Spcnct "; pp_expr out e1; output_string out " "; pp_expr out e2; output_string out ")\n"
  | Swhen (e, s1, s2) -> output_string out "(Swhen "; pp_expr out e; pp_statement out s1; pp_statement out s2; output_string out ")\n"
  | _ -> output_string out ""
                 
          
let pp_module out fmod =
  match fmod with
  | FInmod (v, pl, sl) -> output_string out "(FInmod "; output_string out (v^" "); pp_ports out pl; pp_statements out sl; output_string out ")\n"
  | _ -> output_string out "\n"
          
let pp_modules out fmod = List.iter (fun c -> pp_module out c; output_string out "") fmod

let pp_fcircuit out fc =
  match fc with
  | (v, fmod) -> output_string out "(FCircuit "; output_string out (v^" "); pp_modules out fmod; output_string out ")"

let pp_file out fc = pp_fcircuit out fc
