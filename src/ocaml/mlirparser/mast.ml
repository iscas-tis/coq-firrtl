type var = string

type fgtyp =
| Fuint of int
| Fsint of int
| Fuint_implicit of int
| Fsint_implicit of int
| Fclock
| Freset
| Fasyncreset

type ucast =
| AsUInt
| AsSInt
| AsClock
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

type hfexpr =
| Econst of fgtyp * Z.t
| Ecast of ucast * var
| Eprim_unop of eunop * var
| Eprim_binop of ebinop * var * var
| Emux of var * var * var
| Emultimux of var list
| Eref of var

type hfstmt =
| Sskip
| Swire of var
| Sreg of var
| Smem of var 
| Sinst of var * var
| Snode of var * hfexpr
| Sfcnct of var * var
| Sinvalid of var
| Sinferport of var * var * hfexpr

type hfstmt_seq =
| Qnil
| Qcons of hfstmt * hfstmt_seq

let rec qcat s1 s2 =
  match s1 with
  | Qnil -> s2
  | Qcons (h1, tl1) -> Qcons (h1, (qcat tl1 s2))

type hfport =
| Finput of var * fgtyp
| Foutput of var * fgtyp

type hfmodule =
| FInmod of var * hfport list * hfstmt_seq
| FExmod of var * hfport list * hfstmt_seq

type hfcircuit =
| Fcircuit of var * hfmodule list

(*type file = hfcircuit*)
type file = hfmodule list

let pp_gtyp out ty =
  match ty with
  | Fuint s -> output_string out "(Fuint "; output_string out (Int.to_string s); output_string out ")"
  | Fsint s -> output_string out "(Fsint "; output_string out (Int.to_string s); output_string out ")"
  | Fuint_implicit s -> output_string out "Fuint_implicit"
  | Fsint_implicit s -> output_string out "Fsint_implicit"
  | Freset -> output_string out "Freset"
  | Fasyncreset -> output_string out "Fasyncreset"
  | Fclock -> output_string out "Fclock"
 
let pp_cast out cst = 
 match cst with
 | AsUInt -> output_string out "AsUInt"
 | AsSInt -> output_string out "AsSInt"
 | AsClock -> output_string out "AsUint "
 | AsAsync ->  output_string out "AsAsync"
 
let pp_unop out op =
 match op with
 | Upad s -> output_string out "(Upad "; output_string out (Int.to_string s); output_string out ")" 
 | Ushl s -> output_string out "(Ushl "; output_string out (Int.to_string s); output_string out")"
 | Ushr s -> output_string out "(Ushr "; output_string out (Int.to_string s); output_string out")"
 | Ucvt -> output_string out "Ucvt"
 | Uneg -> output_string out "Uneg"
 | Unot -> output_string out "Unot "
 | Uandr -> output_string out "Uandr"
 | Uorr -> output_string out "Uorr"
 | Uxorr -> output_string out "Uxorr"
 | Uextr (s1, s2) -> output_string out "(Uextr "; output_string out (Int.to_string s1);  output_string out " "; output_string out (Int.to_string s2); output_string out")"
 | Uhead s -> output_string out "(Uhead "; output_string out (Int.to_string s); output_string out")"
 | Utail s -> output_string out "(Utail "; output_string out (Int.to_string s); output_string out")"
 (*| Ubits (s1,s2)  -> output_string out "(Ubits "; output_string out (Int.to_string s1); output_string out " "; output_string out (Int.to_string s2); output_string out")"
 | Uincp -> output_string out "Uincp"
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
 (*| Bsdiv -> output_string out "Bsdiv "
 | Bsrem -> output_string out "Bsrem "
 | _ -> output_string out "" *)
         
let rec pp_expr out e =
 match e with
 | Econst (ty, s) -> output_string out "(econst "; pp_gtyp out ty; output_string out " [::b"; output_string out (Z.format "%b" s) ; output_string out"])"
 | Eref v -> output_string out ("(eref "^v^")")
 | Eprim_unop (op, v) -> output_string out "(eprim_unop "; pp_unop out op; output_string out (v^")")
 | Eprim_binop (bop, v1, v2) -> output_string out "(eprim_binop "; pp_binop out bop; output_string out (v1^", "^v2^")")
 | Emux (v1, v2, v3)  -> output_string out ("(emux "^v1^", "^v2^", "^v3^")")
 | Emultimux vl  -> output_string out "(emultimux "; List.iter (fun c -> output_string out (c^", ")) vl;  output_string out ")\n";
 | Ecast (s, v) -> output_string out "(ecast "; pp_cast out s; output_string out (" "^v^")")

let pp_exprs out el =  List.iter (fun c -> pp_expr out c; output_string out "") el

let rec pp_ports out pl = output_string out "["; List.iter (fun c -> pp_port out c; output_string out ",\n") pl;  output_string out "]\n";
                     
and pp_port out p =
  match p with
  | Finput (v, ty) -> output_string out "Finput "; output_string out (v^" : "); pp_gtyp out ty
  | Foutput (v, ty) -> output_string out "Foutput "; output_string out (v^" : "); pp_gtyp out ty               
     
let rec pp_statements out sl = 
  match sl with
  | Qnil -> output_string out "Fnil"
  | Qcons (s, ss) -> pp_statement out s; pp_statements out ss
                             
and pp_statement out s =
  match s with
  | Sskip -> output_string out "sskip\n"
  | Swire v -> output_string out ("swire "^v^"\n")
  | Smem v -> output_string out ("smem "^v^"\n")
  | Sfcnct (v1, v2) -> output_string out ("(sfcnct "^v1^" "^v2^")\n")
  | Sinvalid v -> output_string out ("(sinvalid "^v^")\n")
  | Sreg v -> output_string out "sreg "; output_string out v; output_string out "\n"
  | Snode (v, e) -> output_string out "(snode "; output_string out (v^" : "); pp_expr out e; output_string out ")\n"
  | Sinst (v, e) -> output_string out "(sinst "; output_string out (v^" "); output_string out "of "; output_string out e; output_string out ")\n"
  | Sinferport _ -> output_string out "inferport\n"
      
let pp_module out fmod =
  match fmod with
  | FInmod (v, pl, sl) -> output_string out "FInmod "; output_string out (v^" : \n"); pp_ports out pl; pp_statements out sl; output_string out "\n"
  | FExmod (v, pl, sl) -> output_string out "FExmod "; output_string out (v^" : \n"); pp_ports out pl; pp_statements out sl; output_string out "\n"
          
let pp_modules out fmod = List.iter (fun c -> pp_module out c; output_string out "") fmod

let pp_fcircuit out fc =
  match fc with
  | Fcircuit (v, fmod) -> output_string out "FCircuit "; output_string out (v^" : \n"); pp_modules out fmod; output_string out "\n"


module StringMap = Map.Make(String)
let initmap_s = StringMap.empty

(* connection map *)
(*let mapport tmap p = 
  match p with
  | Finput (v, ty) -> StringMap.add v ty tmap
  | Foutput (v, ty) -> StringMap.add v ty tmap

let rec cm_s stmt cm = 
  match stmt with
  | Sfcnct (e1, e2) ->
  | Sinvalid v -> 
  | Sreg (v, r) -> StringMap.add v r tmap
  | Snode (v, e) -> StringMap.add v e tmap
  | Sinst _ -> tmap (*tbd*)
  | Swhen (c, s1, s2) ->
  | _ -> cm

and cm_ss stmts cm = 
  match stmts with
  | Qnil -> cm
  | Qcons (s, ss) -> mapstmts (mapstmt tmap s) ss

let cm_modl ml (mod_cm, mod_ports) = 
  match ml with
  | (FInmod (mv, pl, sl)) : tl -> cm_modl tl (StringMap.add mv (cm_ss sl initmap_s) mod_cm, StringMap.add mv pl mod_ports)
  | _ -> (mod_cm, mod_ports)

let cm_cir cir = 
  match cir with
  | Fcircuit (cv, ml) -> (* 需要通过cv找到main module *) let (mod_cm, mod_ports) = cm_modl ml (initmap_s, initmap_s) in ()
*)