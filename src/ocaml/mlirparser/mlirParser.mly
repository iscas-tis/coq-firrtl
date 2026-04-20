%{
    open Mast

%}

%token<string> NUMERAL S_NUMERAL SYMBOL SYMBOL_PRCT SUBSYMBOL_PRCT
%token BRA_OPEN BRA_CLOSE PAR_OPEN PAR_CLOSE ANG_OPEN ANG_CLOSE SQR_OPEN SQR_CLOSE QUOT SPRT KEYWORD ATTRIBUTES AT FIRRTLDOT
%token CIRCUIT STM_MODULE PRIVATE STM_INPUT STM_OUTPUT
%token STM_NODE STM_NASS STM_INST STM_WIRE STM_REG STM_REGRESET0 UINT SINT ASYNC RESET VECTOR BUNDLE FLIP CLOCK 
%token EXPR_VALIDIF EXPR_ADD EXPR_AND EXPR_ANDR EXPR_ASCLOCK EXPR_ASFIXED EXPR_ASSINT EXPR_ASUINT EXPR_CAT EXPR_CVT EXPR_DIV EXPR_DSHL EXPR_ASASYNC
%token EXPR_DSHR EXPR_EQ EXPR_GEQ EXPR_GT EXPR_HEAD EXPR_LEQ EXPR_LT EXPR_MUL EXPR_MUX EXPR_NEG EXPR_NEQ EXPR_NOT EXPR_OR EXPR_ORR EXPR_PAD EXPR_REM EXPR_SHL EXPR_SHR EXPR_SUB EXPR_TAIL EXPR_XOR EXPR_XORR EXPR_BITS
%token EOF NAME_EQ STM_CONNECT RARROW EXPR_AND TO CONST STM_CNCT STM_MCONNECT EXPR_MULTIMUX 

%start file
%type <Mast.file> file

%%

file
  : fmodules EOF                          { $1 }
;
    
fmodules
  : fmodule                                     { [$1] }
  | fmodule fmodules                     { $1::$2}
  ;
    
fmodule
  : mdl ports PAR_CLOSE ATTRIBUTES BRA_OPEN statements BRA_CLOSE     { FInmod ($1, $2, $6) }
  | mdl ports PAR_CLOSE BRA_OPEN statements  BRA_CLOSE               { FInmod ($1, $2, $5) }
  ;

mdl 
  : FIRRTLDOT STM_MODULE PRIVATE AT symbol PAR_OPEN            { $5 }
  | FIRRTLDOT STM_MODULE AT symbol PAR_OPEN            { $4 }
  ;

ports
  :                                      { [] }
  | port                           { [$1] }
  | port SPRT ports                           { $1::$3 }
  ;    

port
  : STM_INPUT symbol_prct KEYWORD gtyp_def
                                         { Finput ($2, $4) }
  | STM_OUTPUT symbol_prct KEYWORD gtyp_def
                                         { Foutput ($2, $4) }
;

ports_inst
  :                                      { [] }
  | port_inst                           { [$1] }
  | port_inst SPRT ports_inst                           { $1::$3 }
  ;    

port_inst
  : STM_INPUT symbol KEYWORD gtyp_def
                                         { Finput ($2, $4) }
  | STM_OUTPUT symbol KEYWORD gtyp_def
                                         { Foutput ($2, $4) }
;

gtyp_def 
  : UINT ANG_OPEN numeral ANG_CLOSE      { Fuint $3 }
  | SINT ANG_OPEN numeral ANG_CLOSE      { Fsint $3 }
  | CLOCK                                { Fclock }
  | RESET                                { Freset}
  | ASYNC                                { Fasyncreset}
  | UINT                                 { Fuint_implicit 0 }
  | SINT                                 { Fsint_implicit 0 }

/* statement */

statements
  :                                      { Qnil }
  | statement statements                 { Qcons ($1, $2) }
  ;    

statement
  : symbol_prct STM_NASS FIRRTLDOT STM_WIRE KEYWORD gtyp_def
                                         { Swire $1 }
  | symbol_prct STM_NASS FIRRTLDOT STM_WIRE BRA_OPEN NAME_EQ STM_NASS QUOT symbol QUOT BRA_CLOSE
                                         KEYWORD gtyp_def
                                         { Swire $1 }
  | FIRRTLDOT STM_CONNECT symbol_prct SPRT symbol_prct KEYWORD gtyp_def
                                         { Sfcnct ($3, $5)}
  | FIRRTLDOT STM_MCONNECT symbol_prct SPRT symbol_prct KEYWORD gtyp_def
                                         { Sfcnct ($3, $5)}
  | FIRRTLDOT STM_CNCT symbol_prct SPRT symbol_prct KEYWORD gtyp_def SPRT gtyp_def
                                         { Sfcnct ($3, $5)}
  | symbol_prct STM_NASS FIRRTLDOT STM_NODE symbol_prct KEYWORD gtyp_def
                                         { Snode ($1, Eref $5) }
  | symbol_prct STM_NASS FIRRTLDOT CONST u_numeral KEYWORD gtyp_def
                                         { Snode ($1, Econst ($7, $5)) }
  | symbol_prct STM_NASS FIRRTLDOT expr KEYWORD expr_type
                                         { Snode ($1, $4) }
  | symbol_prct STM_NASS FIRRTLDOT STM_REG symbol_prct KEYWORD gtyp_def SPRT
      gtyp_def
                                         { Sreg ($1) }
  | symbol_prct STM_NASS FIRRTLDOT STM_REGRESET0 symbol_prct SPRT symbol_prct SPRT symbol_prct KEYWORD gtyp_def SPRT
      gtyp_def SPRT gtyp_def SPRT gtyp_def
                                         { Sreg ($1) }
  | symbols STM_NASS FIRRTLDOT STM_INST symbol AT symbol PAR_OPEN ports_inst PAR_CLOSE    { Sinst ($5, $7) }
;

/* expression */
expr_type
:   gtyp_def
                                          { }
    | gtyp_def SPRT gtyp_def
                                          { }
    | PAR_OPEN gtyp_def PAR_CLOSE RARROW gtyp_def
                                          { }
    | PAR_OPEN gtyp_def SPRT gtyp_def PAR_CLOSE RARROW gtyp_def
                                          { }
    | PAR_OPEN gtyp_def SPRT gtyp_def SPRT gtyp_def PAR_CLOSE RARROW gtyp_def
                                          { }
expr
:   symbol_prct                             { Eref $1 }
    | EXPR_AND symbol_prct SPRT symbol_prct
                                            { Eprim_binop (Band, $2, $4)}
    | EXPR_ADD symbol_prct SPRT symbol_prct
                                            { Eprim_binop (Badd, $2, $4)}
    | EXPR_SUB symbol_prct SPRT symbol_prct
                                            { Eprim_binop (Bsub, $2, $4)}
    | EXPR_MUL symbol_prct SPRT symbol_prct
                                            { Eprim_binop (Bmul, $2, $4)}
    | EXPR_DIV symbol_prct SPRT symbol_prct
                                            { Eprim_binop (Bdiv, $2, $4)}
    | EXPR_REM symbol_prct SPRT symbol_prct
                                            { Eprim_binop (Brem, $2, $4)}
    | EXPR_DSHL symbol_prct SPRT symbol_prct
                                            { Eprim_binop (Bdshl, $2, $4)}
    | EXPR_DSHR symbol_prct SPRT symbol_prct
                                            { Eprim_binop (Bdshr, $2, $4)}
    | EXPR_OR symbol_prct SPRT symbol_prct
                                            { Eprim_binop (Bor, $2, $4)}
    | EXPR_XOR symbol_prct SPRT symbol_prct
                                            { Eprim_binop (Bxor, $2, $4)}
    | EXPR_CAT symbol_prct SPRT symbol_prct
                                            { Eprim_binop (Bcat, $2, $4)}
    | EXPR_GT symbol_prct SPRT symbol_prct
                                            { Eprim_binop (Bcomp (Bgt), $2, $4)}
    | EXPR_LT symbol_prct SPRT symbol_prct
                                            { Eprim_binop (Bcomp (Blt), $2, $4)}
    | EXPR_LEQ symbol_prct SPRT symbol_prct
                                            { Eprim_binop (Bcomp (Bleq), $2, $4)}
    | EXPR_GEQ symbol_prct SPRT symbol_prct
                                            { Eprim_binop (Bcomp (Bgeq), $2, $4)}
    | EXPR_EQ symbol_prct SPRT symbol_prct
                                            { Eprim_binop (Bcomp (Beq), $2, $4)}
    | EXPR_NEQ symbol_prct SPRT symbol_prct
                                            { Eprim_binop (Bcomp (Bneq), $2, $4)}

    | EXPR_BITS symbol_prct numeral TO numeral   { Eprim_unop ( Uextr ($3, $5), $2)}
    | EXPR_CVT symbol_prct
                                            { Eprim_unop (Ucvt, $2)}
    | EXPR_NEG symbol_prct
                                            { Eprim_unop (Uneg, $2)}
    | EXPR_NOT symbol_prct
                                            { Eprim_unop (Unot, $2)}
    | EXPR_NOT symbol_prct
                                            { Eprim_unop (Unot, $2)}
    | EXPR_ANDR symbol_prct
                                            { Eprim_unop (Uandr, $2)}
    | EXPR_ORR symbol_prct
                                            { Eprim_unop (Uorr, $2)}
    | EXPR_XORR symbol_prct
                                            { Eprim_unop (Uxorr, $2)}
    | EXPR_ASUINT symbol_prct
                                            { Ecast (AsUInt, $2)}
    | EXPR_ASSINT symbol_prct
                                            { Ecast (AsSInt, $2)}
    | EXPR_ASCLOCK symbol_prct
                                            { Ecast (AsClock, $2)}
    | EXPR_ASASYNC symbol_prct
                                            { Ecast (AsAsync, $2)}
                                            
    | EXPR_TAIL symbol_prct SPRT numeral 
                                            { Eprim_unop (Utail $4, $2)}
    | EXPR_HEAD symbol_prct SPRT numeral 
                                            { Eprim_unop (Uhead $4, $2)}
    | EXPR_PAD symbol_prct SPRT numeral 
                                            { Eprim_unop ( Upad $4, $2)}
    | EXPR_SHL symbol_prct SPRT numeral 
                                            { Eprim_unop ( Ushl $4, $2)}
    | EXPR_SHR symbol_prct SPRT numeral 
                                            { Eprim_unop ( Ushr $4, $2)}

    | EXPR_MUX PAR_OPEN symbol_prct SPRT symbol_prct SPRT symbol_prct PAR_CLOSE
                                            { Emux ($3, $5, $7)}
    | EXPR_MULTIMUX symbols 
                                            { Emultimux ($2)}
;  

/* Symbols */

symbol
  : SYMBOL                              { $1 }
;

symbol_prct
  : SYMBOL_PRCT                         { $1 }
  | SUBSYMBOL_PRCT                      { $1 }
;

symbols
  :                                      { [] }
  | symbol_prct                               { [$1] }
  | symbol_prct SPRT symbols                       { $1::$3 }
;

/* spec_constant */

numeral
  : NUMERAL                             { Stdlib.int_of_string $1 }
;

u_numeral
  : NUMERAL                             { Z.of_string $1 }
;

s_numeral
  : S_NUMERAL                           { Z.of_string $1 }
;