%{

open BatPervasives
open ArkAst

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
%token ADD MINUS MUL DIV
%token AND OR NOT
%token EQ LEQ GEQ LT GT
%token FORALL EXISTS
%token LPAREN RPAREN
%token LBRACKET RBRACKET
%token LBRACE RBRACE
%token INIT SAFE REACH VARS

%left ADD MINUS
%left MUL DIV
%nonassoc UMINUS

%start math_main
%type <ArkAst.formula> math_main
%start math_opt_main
%type <ArkAst.term * ArkAst.formula> math_opt_main
%start smt2_formula
%type <ArkAst.formula> smt2_formula
%type <Syntax.symbol list * Syntax.symbol list * ArkAst.formula * ArkAst.formula * ArkAst.formula> game
%start game

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

game_additive_term:
  | s = game_multiplicative_term; ADD; t = game_additive_term {
						  Ctx.mk_add [s; t]
						}
  | s = game_multiplicative_term; MINUS; t = game_additive_term {
						    Ctx.mk_sub s t
						  }
  | t = game_multiplicative_term { t }
;

game_multiplicative_term:
  | s = game_multiplicative_term; MUL; t = game_multiplicative_term {
						  Ctx.mk_mul [s; t]
						}
  | s = game_multiplicative_term; DIV; t = game_multiplicative_term {
						  Ctx.mk_div s t
						}
  | t = game_atomic_term { t }
;

game_atomic_term:
  | LPAREN; t = game_additive_term; RPAREN { t }
  | v = ID { Ctx.mk_const (symbol_of_string v) }
  | k = REAL { Ctx.mk_real k }
  ;

game_disj_formula:
  | disjuncts = separated_nonempty_list(OR,game_conj_formula) { Ctx.mk_or disjuncts }
  ;

game_conj_formula:
  | conjuncts = separated_nonempty_list(AND,game_atomic_formula) { Ctx.mk_and conjuncts }
  ;

game_atomic_formula:
  | s = game_additive_term; LEQ; t = game_additive_term { Ctx.mk_leq s t }
  | s = game_additive_term; GEQ; t = game_additive_term { Ctx.mk_leq t s }
  | s = game_additive_term; LT; t = game_additive_term { Ctx.mk_lt s t }
  | s = game_additive_term; GT; t = game_additive_term { Ctx.mk_lt t s }
  | s = game_additive_term; EQ; t = game_additive_term { Ctx.mk_eq s t }
  | NOT; LPAREN; phi = game_disj_formula; RPAREN { Ctx.mk_not phi }
  | LPAREN; phi = game_disj_formula; RPAREN { phi }
  ;

game:
  | VARS; vars = separated_nonempty_list(COMMA,ID);
    INIT; init = game_disj_formula;
    SAFE; safe = game_disj_formula;
    REACH; reach = game_disj_formula;
    EOF {
	let primed_vars =
	  List.map (fun v -> symbol_of_string (v ^ "'")) vars
	in
	(List.map symbol_of_string vars, primed_vars, init, safe, reach)
      }
  ;
