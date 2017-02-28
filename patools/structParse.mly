%{
open Apak
open PredicateAutomata
open BatPervasives
open Patop

let pp_pos formatter pos =
  let open Lexing in
  Format.fprintf formatter "File \"%s\", line %d, position %d"
    pos.pos_fname
    pos.pos_lnum
    (pos.pos_cnum - pos.pos_bol + 1)

%}

%token EOF
%token <string> ID
%token <int> INT
%token COMMA
%token LPAREN RPAREN LBRACE RBRACE
%start main
%type <(Patop.A.Config.t * Patop.A.Config.t) list> main
%start main_struct
%type <Patop.A.Config.t> main_struct
%type <(string * int list) list> main_props
%type <string * int list> main_prop
%type <int list> main_args
%%

main:
  | EOF { [] }
  | c = main_struct; d = main_struct; rest = main { (c, d) :: rest }
;
main_struct:
  | LBRACE ; RBRACE { Patop.A.Config.empty 0 }
  | LBRACE ; props = main_props; RBRACE
      { Patop.A.Config.make (BatRefList.enum (BatRefList.of_list props)) }
;
main_props:
  | prop = main_prop; COMMA; props = main_props { prop :: props }
  | prop = main_prop { [prop] }
;
main_prop:
  | pred = ID; LPAREN; RPAREN { (pred, []) }
  | pred = ID; LPAREN; args = main_args; RPAREN { (pred, args) }
  | pred = ID { (pred, []) }
;
main_args:
  | arg = INT; COMMA; args = main_args { arg :: args }
  | arg = INT { [arg] }
;