{
  open MlirParser

  exception Error of string
  let lnum = ref 1
  let cnum = ref 0
  let get_len lexbuf = String.length (Lexing.lexeme lexbuf)
  let upd_cnum lexbuf = cnum := !cnum + get_len lexbuf
  let reset_cnum () = cnum := 0
}

let digit = ['0'-'9']
let numeral = '0' | ['1'-'9'] digit*
let s_numeral = '-'? numeral
let letter = ['a'-'z' 'A'-'Z' '_' '-']
let symbol = ('|' [^'|']+ '|') | (letter|'_'|digit)*
let escape_space = "\"\""

rule line_comment = parse
 ("\r\n"|'\n'|'\r')                     { reset_cnum(); incr lnum; token lexbuf }
| _                                     { upd_cnum lexbuf; line_comment lexbuf }
                                   
and token = parse

| [' ' '\t']                            { upd_cnum lexbuf; token lexbuf }
| ("\r\n"|'\n'|'\r')                    { reset_cnum(); incr lnum; token lexbuf }
| "attributes {convention = #firrtl<convention scalarized>}"
                                        { upd_cnum lexbuf; ATTRIBUTES }
| "//"                                  { upd_cnum lexbuf; line_comment lexbuf }
| "firrtl.printf"                       { upd_cnum lexbuf; line_comment lexbuf }
| '('                                   { upd_cnum lexbuf; PAR_OPEN }
| ')'                                   { upd_cnum lexbuf; PAR_CLOSE }
| '<'                                   { upd_cnum lexbuf; ANG_OPEN }
| '>'                                   { upd_cnum lexbuf; ANG_CLOSE }
| '['                                   { upd_cnum lexbuf; SQR_OPEN }
| ']'                                   { upd_cnum lexbuf; SQR_CLOSE }
| '{'                                   { upd_cnum lexbuf; BRA_OPEN }
| "name"                                { upd_cnum lexbuf; NAME_EQ }
| '}'                                   { upd_cnum lexbuf; BRA_CLOSE }
| '"'                                   { upd_cnum lexbuf; QUOT } 
| '@'                                   { upd_cnum lexbuf; AT }
| "to"                                  { upd_cnum lexbuf; TO }
| ':'                                   { upd_cnum lexbuf; KEYWORD }
| ','                                   { upd_cnum lexbuf; SPRT }
| "firrtl."                             { upd_cnum lexbuf; FIRRTLDOT }
| numeral as str                        { upd_cnum lexbuf; NUMERAL str }
| s_numeral as str                      { upd_cnum lexbuf; S_NUMERAL str }
| "circuit"                             { upd_cnum lexbuf; CIRCUIT }
| "module"                              { upd_cnum lexbuf; STM_MODULE }
| "private"                             { upd_cnum lexbuf; PRIVATE }
| "in"                                  { upd_cnum lexbuf; STM_INPUT }
| "out"                                 { upd_cnum lexbuf; STM_OUTPUT }

| "wire"                                { upd_cnum lexbuf; STM_WIRE }
| "reg"                                 { upd_cnum lexbuf; STM_REG }
| "regreset"                            { upd_cnum lexbuf; STM_REGRESET0 }
| "node"                                { upd_cnum lexbuf; STM_NODE }
| "="                                   { upd_cnum lexbuf; STM_NASS }
| "instance"                            { upd_cnum lexbuf; STM_INST }
| "connect"                             { upd_cnum lexbuf; STM_CNCT }
| "strictconnect"                       { upd_cnum lexbuf; STM_CONNECT }
| "matchingconnect"                     { upd_cnum lexbuf; STM_MCONNECT }
| "constant"                            { upd_cnum lexbuf; CONST }
| "->"                                  { upd_cnum lexbuf; RARROW }

| "and"                                 { upd_cnum lexbuf; EXPR_AND}
| "add"                                 { upd_cnum lexbuf; EXPR_ADD}
| "sub"                                 { upd_cnum lexbuf; EXPR_SUB}
| "mul"                                 { upd_cnum lexbuf; EXPR_MUL}
| "div"                                 { upd_cnum lexbuf; EXPR_DIV}
| "rem"                                 { upd_cnum lexbuf; EXPR_REM}
| "dshl"                                { upd_cnum lexbuf; EXPR_DSHL}
| "dshr"                                { upd_cnum lexbuf; EXPR_DSHR}
| "or"                                  { upd_cnum lexbuf; EXPR_OR}
| "xor"                                 { upd_cnum lexbuf; EXPR_XOR}
| "not"                                 { upd_cnum lexbuf; EXPR_NOT}
| "cvt"                                 { upd_cnum lexbuf; EXPR_CVT}
| "neg"                                 { upd_cnum lexbuf; EXPR_NEG}
| "andr"                                { upd_cnum lexbuf; EXPR_ANDR}
| "orr"                                 { upd_cnum lexbuf; EXPR_ORR}
| "xorr"                                { upd_cnum lexbuf; EXPR_XORR}
| "tail"                                { upd_cnum lexbuf; EXPR_TAIL}
| "ahead"                               { upd_cnum lexbuf; EXPR_HEAD}
| "pad"                                 { upd_cnum lexbuf; EXPR_PAD}
| "shl"                                 { upd_cnum lexbuf; EXPR_SHL}
| "shr"                                 { upd_cnum lexbuf; EXPR_SHR}
| "mux"                                 { upd_cnum lexbuf; EXPR_MUX}
| "multibit_mux"                        { upd_cnum lexbuf; EXPR_MULTIMUX}
| "cat"                                 { upd_cnum lexbuf; EXPR_CAT}
| "bits"                                { upd_cnum lexbuf; EXPR_BITS}
| "gt"                                  { upd_cnum lexbuf; EXPR_GT }
| "lt"                                  { upd_cnum lexbuf; EXPR_LT }
| "geq"                                 { upd_cnum lexbuf; EXPR_GEQ }
| "leq"                                 { upd_cnum lexbuf; EXPR_LEQ }
| "eq"                                  { upd_cnum lexbuf; EXPR_EQ }
| "neq"                                 { upd_cnum lexbuf; EXPR_NEQ }
| "asUInt"                              { upd_cnum lexbuf; EXPR_ASUINT}
| "asSInt"                              { upd_cnum lexbuf; EXPR_ASSINT }
| "asClock"                             { upd_cnum lexbuf; EXPR_ASCLOCK }
| "asAsyncReset"                        { upd_cnum lexbuf; EXPR_ASASYNC }

(*| "wire"                                { upd_cnum lexbuf; STM_WIRE }
| "reg"                                 { upd_cnum lexbuf; STM_REG }
| "regreset"                            { upd_cnum lexbuf; STM_REGRESET0 }
| "with"                                { upd_cnum lexbuf; REG_WITH }
| "reset"                               { upd_cnum lexbuf; REG_RST }
| "=>"                                  { upd_cnum lexbuf; REG_RSTARR }
| "node"                                { upd_cnum lexbuf; STM_NODE }
| "="                                   { upd_cnum lexbuf; STM_NASS }
| "inst"                                { upd_cnum lexbuf; STM_INST }
| "aof"                                 { upd_cnum lexbuf; KEYWORD_OF }
| "is invalid"                          { upd_cnum lexbuf; STM_INVALID}
| "invalidate"                          { upd_cnum lexbuf; STM_INVALID0}
(*| "data-type"                           { upd_cnum lexbuf; STM_DATATYPE}
| "depth"                               { upd_cnum lexbuf; STM_DEPTH}
| "read-latency"                        { upd_cnum lexbuf; STM_READ_L}
| "write-latency"                       { upd_cnum lexbuf; STM_WRITE_L}
| "reader"                              { upd_cnum lexbuf; STM_READ}
| "writer"                              { upd_cnum lexbuf; STM_WRITE}
| "read-under-write"                    { upd_cnum lexbuf; STM_READWRITE}
| "new"                                 { upd_cnum lexbuf; M_NEW}
| "old"                                 { upd_cnum lexbuf; M_OLD}*)
| "undefined"                           { upd_cnum lexbuf; M_UNDEFINED}

| "cmem"                                { upd_cnum lexbuf; STM_MEM }
| "smem"                                { upd_cnum lexbuf; STM_SMEM }
| "infer mport"                         { upd_cnum lexbuf; STM_MEM_INFER }
| "read mport"                          { upd_cnum lexbuf; STM_MEM_READ }
| "write mport"                         { upd_cnum lexbuf; STM_MEM_WRITE }
*)

(* Types *)
| "!firrtl.uint"                                { upd_cnum lexbuf; UINT }
| "!firrtl.sint"                                { upd_cnum lexbuf; SINT }
| "!firrtl.clock"                               { upd_cnum lexbuf; CLOCK }
| "!firrtl.asyncreset"                          { upd_cnum lexbuf; ASYNC }
| "!firrtl.reset"                               { upd_cnum lexbuf; RESET }

| symbol as str                         { upd_cnum lexbuf; SYMBOL str }
| "%" (symbol as str)                   { upd_cnum lexbuf; SYMBOL_PRCT str }
| '%' (symbol as left) '.' (symbol as right) 
                                        { upd_cnum lexbuf; SUBSYMBOL_PRCT (left^"."^right) }
| eof                                   { EOF }
