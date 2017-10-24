%{

open Srk
open CcaSyntax

%}

%token <string> IDENTIFIER
%token <int> INTEGER
%token ARROW WHEN
%token EQ NEQ LEQ GEQ LT GT
%token LPAREN RPAREN
%token OR AND NOT
%token ADD SUB MUL DIV
%token COMMA
%token EOF
%token GOAL COMPLEXITY STARTTERM VAR RULES COM1 FUNCTIONSYMBOLS

%left OR
%left AND
%nonassoc NOT
%left ADD SUB
%left MUL DIV

%type <CcaSyntax.ces> program
%start program

%%

program:
 | LPAREN; GOAL; COMPLEXITY; RPAREN;
   LPAREN; STARTTERM; LPAREN; FUNCTIONSYMBOLS; start=IDENTIFIER; RPAREN; RPAREN;
   LPAREN; VAR; vars = list(IDENTIFIER); RPAREN;
   LPAREN; RULES; rules = nonempty_list(rule); RPAREN;
   EOF
   { { start; rules } }
;

rule:
  | src = IDENTIFIER; LPAREN; src_args = separated_list(COMMA,IDENTIFIER); RPAREN; ARROW;
    COM1; LPAREN; tgt = IDENTIFIER; LPAREN; tgt_args = separated_list(COMMA,term); RPAREN; RPAREN; guard = option(guard); 
    { let guard = match guard with | Some phi -> phi | None -> Ctx.mk_true in
      ((src, src_args), (tgt, tgt_args), guard)  }
;

guard:
  | WHEN; guard = formula { guard }
;

formula:
  | s = term; GEQ; t = term { Ctx.mk_leq t s }
  | s = term; LEQ; t = term { Ctx.mk_leq s t }
  | s = term; EQ; t = term { Ctx.mk_eq s t }
  | s = term; LT; t = term { Ctx.mk_lt s t }
  | s = term; GT; t = term { Ctx.mk_lt t s }
  | s = term; NEQ; t = term { Ctx.mk_not (Ctx.mk_eq t s) }
  | phi = formula; AND; psi = formula { Ctx.mk_and [phi; psi] }
  | phi = formula; OR; psi = formula { Ctx.mk_or [phi; psi] }
  | NOT; phi = formula { Ctx.mk_not (phi) }
  | LPAREN; phi = formula; RPAREN { phi }
;

term:
  | v = IDENTIFIER { Ctx.mk_const (Var.symbol_of v) }
  | s = term; ADD; t = term { Ctx.mk_add [s; t] }
  | s = term; SUB; t = term { Ctx.mk_sub s t }
  | s = term; MUL; t = term { Ctx.mk_mul [s; t] }
  | s = term; DIV; t = term { Ctx.mk_div s t }
  | n = INTEGER { Ctx.mk_real (QQ.of_int n) }
  | LPAREN; t = term; RPAREN { t }
;
%%
