type token =
  | COMMENT of (string)
  | BINARY of (string)
  | HEX_DECIMAL of (string)
  | OCTAL of (string)
  | DECIMAL of (string)
  | NUMERAL of (string)
  | STRING of (string)
  | SYMBOL of (string)
  | S_HEX_DECIMAL of (string)
  | S_BINARY of (string)
  | S_NUMERAL of (string)
  | S_OCTAL of (string)
  | PAR_OPEN
  | PAR_CLOSE
  | ANG_OPEN
  | ANG_CLOSE
  | SQR_OPEN
  | SQR_CLOSE
  | UNDERSCORE
  | QUOT
  | SPRT
  | KEYWORD
  | CIRCUIT
  | STM_MODULE
  | STM_EXTMODULE
  | STM_SKIP
  | STM_INPUT
  | STM_OUTPUT
  | STM_WHEN
  | STM_ELSE
  | STM_CONNECT
  | STM_PCONNECT
  | STM_NODE
  | STM_NASS
  | STM_INST
  | KEYWORD_OF
  | STM_DEFNAME
  | STM_INVALID
  | STM_PARAM
  | STM_DATATYPE
  | STM_DEPTH
  | STM_READ
  | STM_READ_L
  | STM_WRITE
  | STM_WRITE_L
  | STM_READWRITE
  | STM_WIRE
  | STM_REG
  | REG_WITH
  | REG_RST
  | REG_RSTARR
  | STM_MEM
  | SUB_FIELD
  | UINT
  | SINT
  | INT
  | CLOCK
  | EXPR_VALIDIF
  | EXPR_ADD
  | EXPR_AND
  | EXPR_ANDR
  | EXPR_ASCLOCK
  | EXPR_ASFIXED
  | EXPR_ASSINT
  | EXPR_ASUINT
  | EXPR_CAT
  | EXPR_CVT
  | EXPR_DIV
  | EXPR_DSHL
  | EXPR_DSHR
  | EXPR_EQ
  | EXPR_GEQ
  | EXPR_GT
  | EXPR_HEAD
  | EXPR_LEQ
  | EXPR_LT
  | EXPR_MUL
  | EXPR_MUX
  | EXPR_NEG
  | EXPR_NEQ
  | EXPR_NOT
  | EXPR_OR
  | EXPR_ORR
  | EXPR_PAD
  | EXPR_REM
  | EXPR_SHL
  | EXPR_SHR
  | EXPR_SUB
  | EXPR_TAIL
  | EXPR_XOR
  | EXPR_XORR
  | EXPR_BITS
  | EOF
  | M_OLD
  | M_NEW
  | M_UNDEFINED

val file :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Ast.file
