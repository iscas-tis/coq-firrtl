open Hifirrtl_lang
type var = string

type hfexpr =
| Econst of Ast.fgtyp * Z.t
| Ecast of Ast.ucast * var
| Eprim_unop of Ast.eunop * var
| Eprim_binop of Ast.ebinop * var * var
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
| Finput of var * Ast.fgtyp
| Foutput of var * Ast.fgtyp

type hfmodule =
| FInmod of var * hfport list * hfstmt_seq
| FExmod of var * hfport list * hfstmt_seq

type hfcircuit =
| Fcircuit of var * hfmodule list

(*type file = hfcircuit*)
type file = hfmodule list
         
let rec pp_expr out e =
 match e with
 | Econst (ty, s) -> output_string out "(econst "; Ast.pp_gtyp out ty; output_string out " [::b"; output_string out (Z.format "%b" s) ; output_string out"])"
 | Eref v -> output_string out ("(eref "^v^")")
 | Eprim_unop (op, v) -> output_string out "(eprim_unop "; Ast.pp_unop out op; output_string out (v^")")
 | Eprim_binop (bop, v1, v2) -> output_string out "(eprim_binop "; Ast.pp_binop out bop; output_string out (v1^", "^v2^")")
 | Emux (v1, v2, v3)  -> output_string out ("(emux "^v1^", "^v2^", "^v3^")")
 | Emultimux vl  -> output_string out "(emultimux "; List.iter (fun c -> output_string out (c^", ")) vl;  output_string out ")\n";
 | Ecast (s, v) -> output_string out "(ecast "; Ast.pp_cast out s; output_string out (" "^v^")")

let pp_exprs out el =  List.iter (fun c -> pp_expr out c; output_string out "") el

let rec pp_ports out pl = output_string out "["; List.iter (fun c -> pp_port out c; output_string out ",\n") pl;  output_string out "]\n";
                     
and pp_port out p =
  match p with
  | Finput (v, ty) -> output_string out "Finput "; output_string out (v^" : "); Ast.pp_gtyp out ty
  | Foutput (v, ty) -> output_string out "Foutput "; output_string out (v^" : "); Ast.pp_gtyp out ty               
     
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

let rec cm_s stmt cm = (* 只看node和fcnct *)
  match stmt with
  | Sfcnct (v1, v2) -> StringMap.add v1 (Eref v2) cm
  | Sinvalid v -> StringMap.add v (Econst (Fuint 0, Z.of_int 0)) cm
  | Sreg v -> StringMap.add v (Eref v) cm
  | Snode (v, e) -> StringMap.add v e cm
  | Sinst (v1, v2) -> StringMap.add v1 (Eref v2) cm
  | _ -> cm

and cm_ss stmts cm = 
  match stmts with
  | Qnil -> cm
  | Qcons (s, ss) -> cm_ss ss (cm_s s cm)

let rec cm_modl ml mod_cm = 
  match ml with
  | [] -> mod_cm
  | (FInmod (mv, pl, sl)) :: tl -> cm_modl tl (StringMap.add mv (cm_ss sl initmap_s) mod_cm)
  | _ -> output_string stdout "There is a extmodule\n"; mod_cm

let cm_cir cir = (* 逐module记录connection map, String(module name) -> connection tree *)
  match cir with
  | Fcircuit (cv, ml) -> (* 需要通过cv找到main module *) cm_modl ml initmap_s
