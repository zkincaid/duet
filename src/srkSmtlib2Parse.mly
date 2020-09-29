%{
open SrkSmtlib2Defs
%}
%token <string> SYMBOL
%token <string> KEYWORD
%token <string> STRING
%token <ZZ.t> INT
%token <QQ.t> REAL
%token EOF

%token LPAREN RPAREN
%token UNDERSCORE
%token AS
%token LET
%token FORALL EXISTS
%token MATCH
%token BANG

%token MODEL
%token DEFFUN

%start main_term
%type <SrkSmtlib2Defs.term> main_term
%start main_model
%type <SrkSmtlib2Defs.model> main_model

%%

main_model:
    | m = model; EOF { m }
;
model:
    | LPAREN; MODEL; mrl = model_response_list; RPAREN { mrl }
    | LPAREN; mrl = model_response_list; RPAREN { mrl }
;
model_response_list:
    | (* empty *) { [] }
    | mr = model_response; mrl = model_response_list { mr :: mrl }
;
model_response:
    | LPAREN; DEFFUN; fn = function_def; RPAREN { fn }
;
function_def:
    | sym = SYMBOL; LPAREN; RPAREN; s = sort; t = term { (sym, [], s, t) }
    | sym = SYMBOL; LPAREN; svl = sorted_var_list; RPAREN; s = sort; t = term { (sym, svl, s, t) }
;
main_term:
    | t = term; EOF { t }
;
term_list:
    | t = term { [t] }
    | t = term; tl = term_list { t :: tl }
;
term:
    | c = spec_constant { Const c }
    | id = qual_identifier { App (id, []) }
    | LPAREN; id = qual_identifier; tl = term_list; RPAREN { App (id, tl) }
    | LPAREN; LET; LPAREN; vbl = var_binding_list; RPAREN; t = term; RPAREN { Let (vbl, t) }
    | LPAREN; FORALL; LPAREN; svl = sorted_var_list; RPAREN; t = term; RPAREN { Forall (svl, t) }
    | LPAREN; EXISTS; LPAREN; svl = sorted_var_list; RPAREN; t = term; RPAREN { Exists (svl, t) }
    | LPAREN; MATCH; t = term; LPAREN; cases = match_case_list; RPAREN; RPAREN { Match (t, cases) }
    | LPAREN; BANG; t = term; attrs = attribute_list; RPAREN { Attribute (t, attrs) }
;
spec_constant:
    | n = INT { Int n }
    | r = REAL { Real r }
    | s = STRING { String s }
;
qual_identifier:
    | id = identifier { (id, None) }
    | LPAREN; AS; id = identifier; s = sort; RPAREN { (id, Some s) }
;
identifier:
    | sym = SYMBOL { (sym,[]) }
    | LPAREN; UNDERSCORE; sym = SYMBOL; il = index_list; RPAREN { (sym,il) }
;
index_list:
  | i = index { [i] }
  | i = index; il = index_list { i :: il }
;
index:
    | n = INT { Num n }
    | sym = SYMBOL { Sym sym }
;
sort_list:
    | s = sort { [s] }
    | s = sort; sl = sort_list { s :: sl }
sort:
    | id = identifier { Sort (id, []) }
    | LPAREN; id = identifier; sl = sort_list; RPAREN { Sort (id, sl) }
;
var_binding_list:
    | vb = var_binding { [vb] }
    | vb = var_binding; vl = var_binding_list { vb :: vl }
;
var_binding:
    | LPAREN; sym = SYMBOL; t = term; RPAREN { (sym, t) }
;
sorted_var_list:
    | sv = sorted_var { [sv] }
    | sv = sorted_var; sl = sorted_var_list { sv :: sl }
;
sorted_var:
    | LPAREN; sym = SYMBOL; s = sort; RPAREN { (sym, s) }
;
match_case_list:
    | case = match_case { [case] }
    | case = match_case; cases = match_case_list { case :: cases }
;
match_case:
    | LPAREN; p = pattern; t = term; RPAREN { (p, t) }
;
pattern:
    | sym = SYMBOL { (sym, []) }
    | LPAREN; sym = SYMBOL; syms = symbol_list; RPAREN { (sym, syms) }
;
symbol_list:
    | sym = SYMBOL { [sym] }
    | sym = SYMBOL; syms = symbol_list { sym :: syms }
;
attribute_list:
    | attr = attribute { [attr] }
    | attr = attribute; attrs = attribute_list { attr :: attrs }
;
attribute:
    | kw = KEYWORD { (kw, None) }
    | kw = KEYWORD; av = attribute_value { (kw, Some av) }
;
attribute_value:
    | c = spec_constant { VConst c }
    | sym = SYMBOL { VSym sym }
    | LPAREN; sexprs = sexpr_list; RPAREN { VSexpr sexprs }
;
sexpr_list:
    | (* empty *) { [] }
    | sexp = sexpr; sexps = sexpr_list { sexp :: sexps }
;
sexpr:
    | c = spec_constant { SConst c }
    | sym = SYMBOL { SSym sym }
    | kw = KEYWORD { SKey kw }
    | LPAREN; sexprs = sexpr_list; RPAREN { SSexpr sexprs }
;

