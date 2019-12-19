%{

open SrkAst

let pp_pos formatter pos =
  let open Lexing in
  Format.fprintf formatter "File \"%s\", line %d, position %d"
    pos.pos_fname
    pos.pos_lnum
    (pos.pos_cnum - pos.pos_bol + 1)

let symbol_of_string =
  Memo.memo (fun name -> Ctx.mk_symbol ~name `TyReal)

%}

%token EOF
%token COMMA
%token OBJECTIVE
%token <string> ID
%token <QQ.t> REAL
%token ADD MINUS MUL
%token AND OR NOT
%token EQ LEQ LT GT
%token FORALL EXISTS
%token LPAREN RPAREN
%token LBRACKET RBRACKET
%token LBRACE RBRACE

%left ADD
%left MUL
%nonassoc UMINUS

%start math_main
%type <SrkAst.formula> math_main
%start math_opt_main
%type <SrkAst.term * SrkAst.formula> math_opt_main
%start smt2_formula
%type <SrkAst.formula> smt2_formula

%%

math_opt_main:
    | OBJECTIVE; objective = math_term; phi = math_formula; EOF { (objective, phi) }
;
math_main:
    | phi = math_formula; EOF { phi }
;

math_formula:
    | AND; LBRACKET; phi = math_formula; COMMA; psi = math_formula; RBRACKET
      { Ctx.mk_and [phi; psi] }
    | OR; LBRACKET; phi = math_formula; COMMA; psi = math_formula; RBRACKET
      { Ctx.mk_or [phi; psi] }
    | NOT; LBRACKET; phi = math_formula; RBRACKET { Ctx.mk_not phi }
    | FORALL; LBRACKET; vars = math_vars; COMMA; phi = math_formula; RBRACKET
      { mk_forall vars phi }
    | EXISTS; LBRACKET; vars = math_vars; COMMA; phi = math_formula; RBRACKET
      { mk_exists vars phi }
    | s = math_term; LEQ; t = math_term { Ctx.mk_leq s t }
    | s = math_term; LT; t = math_term { Ctx.mk_lt s t }
    | s = math_term; EQ; t = math_term { Ctx.mk_eq s t }
;

math_vars:
    | LBRACE; vars = separated_list(COMMA,ID); RBRACE { List.map symbol_of_string vars }
    | v = ID; { [symbol_of_string v] }
;

math_term:
    | LPAREN; t = math_term; RPAREN { t }
    | s = math_term; ADD; t = math_term { Ctx.mk_add [s; t] }
    | LPAREN; s = math_term; MINUS; t = math_term; RPAREN { Ctx.mk_sub s t }
    | s = math_term; MUL; t = math_term { Ctx.mk_mul [s; t] }
    | v = ID { Ctx.mk_const (symbol_of_string v) }
    | k = REAL { Ctx.mk_real k }
    | MINUS; t = math_term { Ctx.mk_neg t } %prec UMINUS
;


smt2_formula:
  | LPAREN; phi = up_smt2_formula; RPAREN { phi }
;

up_smt2_formula:
  | AND; conjuncts = list(smt2_formula) { Ctx.mk_and conjuncts }
  | OR; disjuncts = list(smt2_formula) { Ctx.mk_or disjuncts }
  | GT; s = smt2_term; t = smt2_term { Ctx.mk_lt t s }
;

smt2_term:
  | LPAREN; t = up_smt2_term; RPAREN { t }
;

up_smt2_term:
  | ADD; ts = list(smt2_term) { Ctx.mk_add ts }
  | MUL; ts = list(smt2_term) { Ctx.mk_mul ts }
  | MINUS; t = smt2_term { Ctx.mk_neg t }
  | k = REAL { Ctx.mk_real k }
;
