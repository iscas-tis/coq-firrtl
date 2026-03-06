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
let s_binary_digit = binary_digit | ('-' binary_digit)
let s_numeral = numeral | ('-' numeral)
let letter = ['a'-'z' 'A'-'Z' '_']
let special_char = ['+' '-' '/' '*' '=' '%' '?' '!' '$' '_' '~' '&' '^' '@' '\'' '.']
let symbol = ('|' [^'|']+ '|') | (letter|special_char)(letter|special_char|digit)*
let escape_space = "\"\""

let letter = ['a'-'z' 'A'-'Z' '_']
let number = ['0'-'9']
let hex = ['0'-'9' 'a'-'f' 'A'-'F']
let s_hex = hex | ('-' hex)
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
| '"'                                  { upd_cnum lexbuf; QUOT } 
| '_'                                   { upd_cnum lexbuf; UNDERSCORE }
| "b" (binary_digit+ as str)            { upd_cnum lexbuf; BINARY str }
| "o" (numeral+ as str)                 { upd_cnum lexbuf; OCTAL str }
| "h" (hex+ as str)                           { upd_cnum lexbuf; HEX_DECIMAL str }
| "b" (s_binary_digit+ as str)            { upd_cnum lexbuf; S_BINARY str }
| "o" (s_numeral+ as str)                 { upd_cnum lexbuf; S_OCTAL str }
| "h" (s_hex+ as str)                           { upd_cnum lexbuf; S_HEX_DECIMAL str }
| ':'                                   { upd_cnum lexbuf; KEYWORD }
| ','                                   { upd_cnum lexbuf; SPRT }
(*| numeral '.' '0'* numeral as str       { upd_cnum lexbuf; DECIMAL str }*)
| numeral as str                        { upd_cnum lexbuf; NUMERAL str }
| s_numeral as str                        { upd_cnum lexbuf; S_NUMERAL str }
(* | '"' (([^'"']|escape_space)* as str) '"'
 *                                         { upd_cnum lexbuf; STRING str } *)
| "circuit"                             { upd_cnum lexbuf; CIRCUIT }
| "module"                              { upd_cnum lexbuf; STM_MODULE }
| "extmodule"                   { upd_cnum lexbuf; STM_EXTMODULE }
| "defname"                   { upd_cnum lexbuf; STM_DEFNAME }
| "parameter"                  { upd_cnum lexbuf; STM_PARAM }
| "skip"                                { upd_cnum lexbuf; STM_SKIP }
| "input"                               { upd_cnum lexbuf; STM_INPUT }
| "output"                              { upd_cnum lexbuf; STM_OUTPUT }
| "when"                                { upd_cnum lexbuf; STM_WHEN }
| "else"                                { upd_cnum lexbuf; STM_ELSE }
| "<="                                  { upd_cnum lexbuf; STM_CONNECT }
| "<-"                                  { upd_cnum lexbuf; STM_PCONNECT}

| "add"                                 { upd_cnum lexbuf; EXPR_ADD}
| "sub"                                 { upd_cnum lexbuf; EXPR_SUB}
| "mul"                                 { upd_cnum lexbuf; EXPR_MUL}
| "div"                                 { upd_cnum lexbuf; EXPR_DIV}
| "rem"                                 { upd_cnum lexbuf; EXPR_REM}
| "dshl"                                 { upd_cnum lexbuf; EXPR_DSHL}
| "dshr"                                 { upd_cnum lexbuf; EXPR_DSHR}
| "and"                                 { upd_cnum lexbuf; EXPR_AND}
| "or"                                 { upd_cnum lexbuf; EXPR_OR}
| "xor"                                 { upd_cnum lexbuf; EXPR_XOR}
| "not"                                 { upd_cnum lexbuf; EXPR_NOT}
| "cvt"                                 { upd_cnum lexbuf; EXPR_CVT}
| "neg"                                 { upd_cnum lexbuf; EXPR_NEG}
| "andr"                                 { upd_cnum lexbuf; EXPR_ANDR}
| "orr"                                 { upd_cnum lexbuf; EXPR_ORR}
| "xorr"                                 { upd_cnum lexbuf; EXPR_XORR}
| "tail"                                 { upd_cnum lexbuf; EXPR_TAIL}
| "ahead"                                 { upd_cnum lexbuf; EXPR_HEAD}
| "pad"                                 { upd_cnum lexbuf; EXPR_PAD}
| "shl"                                 { upd_cnum lexbuf; EXPR_SHL}
| "shr"                                 { upd_cnum lexbuf; EXPR_SHR}
| "mux"                                 { upd_cnum lexbuf; EXPR_MUX}
| "validif"                                 { upd_cnum lexbuf; EXPR_VALIDIF}

| "cat"                                 { upd_cnum lexbuf; EXPR_CAT}
| "bits"                                { upd_cnum lexbuf; EXPR_BITS}

| "asUInt"                                       { upd_cnum lexbuf;  EXPR_ASUINT}
| "asSInt"                                       { upd_cnum lexbuf; EXPR_ASSINT }
| "asFixed"                                       { upd_cnum lexbuf; EXPR_ASFIXED }
| "asClock"                                       { upd_cnum lexbuf; EXPR_ASCLOCK }

| "wire"                                { upd_cnum lexbuf; STM_WIRE }
| "reg"                                 { upd_cnum lexbuf; STM_REG }
| "with"                                { upd_cnum lexbuf; REG_WITH }
| "reset"                               { upd_cnum lexbuf; REG_RST }
| "=>"                                  { upd_cnum lexbuf; REG_RSTARR }
| "node"                                { upd_cnum lexbuf; STM_NODE }
| "="                                   { upd_cnum lexbuf; STM_NASS }
| "inst"                                { upd_cnum lexbuf; STM_INST }
| "aof"                                   { upd_cnum lexbuf; KEYWORD_OF }
| "is invalid"                      { upd_cnum lexbuf; STM_INVALID}
| "data-type"                      { upd_cnum lexbuf; STM_DATATYPE}
| "depth"                      { upd_cnum lexbuf; STM_DEPTH}
| "read-latency"                      { upd_cnum lexbuf; STM_READ_L}
| "write-latency"                      { upd_cnum lexbuf; STM_WRITE_L}
| "reader"                      { upd_cnum lexbuf; STM_READ}
| "writer"                      { upd_cnum lexbuf; STM_WRITE}
| "read-under-write"                      { upd_cnum lexbuf; STM_READWRITE}
| "new"                      { upd_cnum lexbuf; M_NEW}
| "old"                      { upd_cnum lexbuf; M_OLD}
| "undefined"                      { upd_cnum lexbuf; M_UNDEFINED}

| "gt"                                       { upd_cnum lexbuf; EXPR_GT }
| "lt"                                       { upd_cnum lexbuf; EXPR_LT }
| "geq"                                       { upd_cnum lexbuf; EXPR_GEQ }
| "leq"                                       { upd_cnum lexbuf; EXPR_LEQ }
| "eq"                                       { upd_cnum lexbuf; EXPR_EQ }
| "neq"                                       { upd_cnum lexbuf; EXPR_NEQ }


| "mem"                                 { upd_cnum lexbuf; STM_MEM }
 
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
