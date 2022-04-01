%{
    open Ast

%}

%token<string> COMMENT
%token<string> BINARY HEX_DECIMAL OCTAL DECIMAL NUMERAL STRING SYMBOL
%token PAR_OPEN PAR_CLOSE ANG_OPEN ANG_CLOSE SQR_OPEN SQR_CLOSE UNDERSCORE QUOT SPRT KEYWORD
%token CIRCUIT STM_MODULE STM_SKIP STM_INPUT STM_OUTPUT STM_WHEN STM_ELSE  STM_CONNECT STM_PCONNECT
%token STM_WIRE STM_REG STM_MEM EXPR_ADD EXPR_NOT SUB_FIELD UINT SINT INT
%token EOF

%start file
%type <Ast.file> file

%%

file
  : circuit EOF                          { $1 }
;

circuit
  : cct fmodules                         { ($1, $2)}
  ;

cct
  : CIRCUIT symbol KEYWORD               { $2 }
  ;
    
fmodules
  :                                      { [] }
  | fmodule fmodules                     { $1::$2}
  ;
    
fmodule
  : mdl ports statements                 { FInmod ($1, $2, $3) }
  ;

mdl 
  : STM_MODULE symbol KEYWORD            { $2 }
  ;

ports
  :                                      { [] }
  | port ports                           { $1::$2 }
  ;    

port
  : STM_INPUT symbol KEYWORD typ_def
                                         { Finput (Eref ($2, $4)) }
  | STM_OUTPUT symbol KEYWORD typ_def
                                         { Foutput (Eref ($2, $4)) }
;

typ_def
  :  UINT ANG_OPEN numeral ANG_CLOSE      { Tuint $3 }
  | SINT ANG_OPEN numeral ANG_CLOSE      { Tsint $3 }
;

/* statement */

statements
  :                                      { [] }
  | statement statements                 { $1::$2 }
  ;    

statement
  : STM_SKIP
	                                    { Sskip }
  | STM_WHEN expr KEYWORD statement STM_ELSE KEYWORD statement
                                            { Swhen ($2, $4, $7) }
  | expr STM_CONNECT expr
                                            { Sfcnct ( $1, $3) }
  | expr STM_PCONNECT expr
                                            { Spcnct ( $1, $3) } 
  | STM_WIRE symbol KEYWORD typ_def 
                                            { Swire ($2, $4) } 
;
  
/* expression */
  
expr
:   symbol                                  { Evar $1 }
  | EXPR_ADD PAR_OPEN symbol SPRT symbol PAR_CLOSE
                                            { Eprim_binop (Badd, (Evar $3), (Evar $5))}
  | EXPR_NOT PAR_OPEN symbol PAR_CLOSE
                                            { Eprim_unop (Unot, (Evar $3))}
;  

/* Symbols */

symbol
  : SYMBOL                              { $1 }
;


/* spec_constant */

numeral
  : NUMERAL                             { Z.of_string $1 }
;

decimal
  : DECIMAL                             { $1 }
;

hexadecimal
  : HEX_DECIMAL                         { String.uppercase_ascii $1 }
;

binary
  : BINARY                              { $1 }
;

string
  : STRING                              { $1 }
;
