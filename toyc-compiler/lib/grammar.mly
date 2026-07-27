%{
open Ast
open Frontend_support

let parse_error _ = raise_parse_error ()

let mk_ident name pos =
  { name; id = fresh_id (); loc = loc_of_pos pos }

let mk_decl is_const ident init = { is_const; ident; init }

let mk_func ret name params body = { ret; name; params; body }
%}

%token EOF
%token KW_INT KW_VOID KW_CONST KW_IF KW_ELSE KW_WHILE KW_BREAK KW_CONTINUE KW_RETURN
%token LPAR RPAR LBRACE RBRACE SEMI COMMA ASSIGN
%token PLUS MINUS STAR SLASH PERCENT BANG
%token LESS GREATER LESSEQ GREATEREQ EQEQ BANGEQ ANDAND OROR
%token <string> ID
%token <int64> NUMBER

%start program
%type <Ast.program> program
%type <Ast.top list> rev_tops
%type <Ast.top> top
%type <Ast.ident> ident param
%type <Ast.ident list> param_list_opt rev_params
%type <Ast.decl> decl
%type <Ast.stmt list> block rev_stmts
%type <Ast.stmt> stmt
%type <Ast.expr> expr
%type <Ast.expr list> arg_list_opt rev_args

%nonassoc IFX
%nonassoc KW_ELSE
%left OROR
%left ANDAND
%left LESS GREATER LESSEQ GREATEREQ EQEQ BANGEQ
%left PLUS MINUS
%left STAR SLASH PERCENT
%right UPLUS UMINUS UNOT

%%

program:
  rev_tops EOF { List.rev $1 }
;

rev_tops:
  { [] }
| rev_tops top { $2 :: $1 }
;

top:
  KW_CONST KW_INT ident ASSIGN expr SEMI
    { TopDecl (mk_decl true $3 $5) }
| KW_INT ident ASSIGN expr SEMI
    { TopDecl (mk_decl false $2 $4) }
| KW_INT ident LPAR param_list_opt RPAR block
    { FuncDef (mk_func TInt $2 $4 $6) }
| KW_VOID ident LPAR param_list_opt RPAR block
    { FuncDef (mk_func TVoid $2 $4 $6) }
;

ident:
  ID { mk_ident $1 (Parsing.rhs_start_pos 1) }
;

param:
  KW_INT ident { $2 }
;

param_list_opt:
  { [] }
| rev_params { List.rev $1 }
;

rev_params:
  param { [$1] }
| rev_params COMMA param { $3 :: $1 }
;

decl:
  KW_CONST KW_INT ident ASSIGN expr SEMI
    { mk_decl true $3 $5 }
| KW_INT ident ASSIGN expr SEMI
    { mk_decl false $2 $4 }
;

block:
  LBRACE rev_stmts RBRACE { List.rev $2 }
;

rev_stmts:
  { [] }
| rev_stmts stmt { $2 :: $1 }
;

stmt:
  block { Block $1 }
| SEMI { Empty }
| decl { Decl $1 }
| KW_IF LPAR expr RPAR stmt %prec IFX
    { If ($3, $5, None) }
| KW_IF LPAR expr RPAR stmt KW_ELSE stmt
    { If ($3, $5, Some $7) }
| KW_WHILE LPAR expr RPAR stmt
    { While ($3, $5) }
| KW_BREAK SEMI { Break }
| KW_CONTINUE SEMI { Continue }
| KW_RETURN SEMI { Return None }
| KW_RETURN expr SEMI { Return (Some $2) }
| ID ASSIGN expr SEMI { Assign ($1, $3) }
| expr SEMI { Expr $1 }
;

expr:
  NUMBER { Int $1 }
| ID { Var $1 }
| ID LPAR arg_list_opt RPAR { Call ($1, $3) }
| LPAR expr RPAR { $2 }
| expr OROR expr { Binary (LOr, $1, $3) }
| expr ANDAND expr { Binary (LAnd, $1, $3) }
| expr LESS expr { Binary (Lt, $1, $3) }
| expr GREATER expr { Binary (Gt, $1, $3) }
| expr LESSEQ expr { Binary (Le, $1, $3) }
| expr GREATEREQ expr { Binary (Ge, $1, $3) }
| expr EQEQ expr { Binary (Eq, $1, $3) }
| expr BANGEQ expr { Binary (Ne, $1, $3) }
| expr PLUS expr { Binary (Add, $1, $3) }
| expr MINUS expr { Binary (Sub, $1, $3) }
| expr STAR expr { Binary (Mul, $1, $3) }
| expr SLASH expr { Binary (Div, $1, $3) }
| expr PERCENT expr { Binary (Mod, $1, $3) }
| PLUS expr %prec UPLUS { Unary (UPlus, $2) }
| MINUS expr %prec UMINUS { Unary (UMinus, $2) }
| BANG expr %prec UNOT { Unary (UNot, $2) }
;

arg_list_opt:
  { [] }
| rev_args { List.rev $1 }
;

rev_args:
  expr { [$1] }
| rev_args COMMA expr { $3 :: $1 }
;
