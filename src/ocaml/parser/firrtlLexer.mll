{
  open FirrtlParser

  exception Error of string
  let lnum = ref 1
  let cnum = ref 0
  let get_len lexbuf = String.length (Lexing.lexeme lexbuf)
  let upd_cnum lexbuf = cnum := !cnum + get_len lexbuf
  let reset_cnum () = cnum := 0
}

let digit = ['0'-'9']
let binary_digit = ['0' '1']
let numeral = '0' | ['1'-'9'] digit*
let letter = ['a'-'z' 'A'-'Z' '_']
let special_char = ['+' '-' '/' '*' '=' '%' '?' '!' '.' '$' '_' '~' '&' '^' '<' '>' '@' '\'']
let symbol = ('|' [^'|']+ '|') | (letter|special_char)(letter|special_char|digit)*
let escape_space = "\"\""

let letter = ['a'-'z' 'A'-'Z' '_']
let number = ['0'-'9']
let hex = ['0'-'9' 'a'-'f' 'A'-'F']
let identity = letter (letter | number)*
let comment_line = ('@'([^ '\n' ]+))|('#'([^ '\n' ]+))

rule line_comment = parse
 ("\r\n"|'\n'|'\r')                     { reset_cnum(); incr lnum; token lexbuf }
| _                                     { upd_cnum lexbuf; line_comment lexbuf }
                                   
and token = parse

| [' ' '\t']                            { upd_cnum lexbuf; token lexbuf }
| ("\r\n"|'\n'|'\r')                    { reset_cnum(); incr lnum; token lexbuf }
| '@'                                   { upd_cnum lexbuf; line_comment lexbuf }
| '('                                   { upd_cnum lexbuf; PAR_OPEN }
| ')'                                   { upd_cnum lexbuf; PAR_CLOSE }
| '<'                                   { upd_cnum lexbuf; ANG_OPEN }
| '>'                                   { upd_cnum lexbuf; ANG_CLOSE }
| '['                                   { upd_cnum lexbuf; SQR_OPEN }
| ']'                                   { upd_cnum lexbuf; SQR_CLOSE }
| '"'                                   { upd_cnum lexbuf; QUOT }
| '_'                                   { upd_cnum lexbuf; UNDERSCORE }
| "b" (binary_digit+ as str)            { upd_cnum lexbuf; BINARY str }
| "o" (numeral+ as str)                 { upd_cnum lexbuf; OCTAL str }
| ':'                                   { upd_cnum lexbuf; KEYWORD }
| ','                                   { upd_cnum lexbuf; SPRT }
| '.'                                   { upd_cnum lexbuf; SUB_FIELD }
| "h" (hex+ as str)
                                        { upd_cnum lexbuf; HEX_DECIMAL str }
| numeral '.' '0'* numeral as str       { upd_cnum lexbuf; DECIMAL str }
| numeral as str                        { upd_cnum lexbuf; NUMERAL str }
| '"' (([^'"']|escape_space)* as str) '"'
                                        { upd_cnum lexbuf; STRING str }
| "circuit"                             { upd_cnum lexbuf; CIRCUIT }
| "module"                              { upd_cnum lexbuf; STM_MODULE }
| "skip"                                { upd_cnum lexbuf; STM_SKIP }
| "input"                               { upd_cnum lexbuf; STM_INPUT }
| "output"                              { upd_cnum lexbuf; STM_OUTPUT }
| "when"                                { upd_cnum lexbuf; STM_WHEN }
| "else"                                { upd_cnum lexbuf; STM_ELSE }
| "<="                                  { upd_cnum lexbuf; STM_CONNECT }
| "<-"                                  { upd_cnum lexbuf; STM_PCONNECT}
| "add"                                 { upd_cnum lexbuf; EXPR_ADD}
| "not"                                 { upd_cnum lexbuf; EXPR_NOT}
| "wire"                                { upd_cnum lexbuf; STM_WIRE }

| "reg"                                 { upd_cnum lexbuf; STM_REG }
| "with"                                { upd_cnum lexbuf; REG_WITH }
| "reset"                               { upd_cnum lexbuf; REG_RST }
| "=>"                                  { upd_cnum lexbuf; REG_RSTARR }
| "node"                                { upd_cnum lexbuf; STM_NODE }
| "="                                   { upd_cnum lexbuf; STM_NASS }
(*
| "mem"                                 { upd_cnum lexbuf; STM_MEM }
 *)
(* Types *)
| "UInt"                                { upd_cnum lexbuf; UINT }
| "SInt"                                { upd_cnum lexbuf; SINT }
| "Int"                                 { upd_cnum lexbuf; SINT }
(*
| "Analog"                              { upd_cnum lexbuf; ANALOG } *)
| "Clock"                               { upd_cnum lexbuf; CLOCK }
(* 
| "Fixed"                               { upd_cnum lexbuf; FIXED }
 *)
| symbol as str                         { upd_cnum lexbuf; SYMBOL str }
| eof                                   { EOF }
