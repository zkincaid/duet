{
open ArkParse
open Lexing
let next_line lexbuf =
  let pos = lexbuf.lex_curr_p in
  lexbuf.lex_curr_p <-
    { pos with pos_bol = lexbuf.lex_curr_pos;
               pos_lnum = pos.pos_lnum + 1
    }
}
let newline = '\r' | '\n' | "\r\n"
let whitespace = [' ' '\t']+

rule math_token = parse
| whitespace { math_token lexbuf }
| newline  { next_line lexbuf; math_token lexbuf }
| "Objective:" { OBJECTIVE }
| "And" { AND }
| "Or" { OR }
| "ForAll" { FORALL }
| "Exists" { EXISTS }
| "Not" { NOT }
| "<=" { LEQ }
| "=" { EQ }
| "<" { LT }
| "*" { MUL }
| "+" { ADD }
| "-" { MINUS }
| "," { COMMA }
| "(" { LPAREN }
| ")" { RPAREN }
| "[" { LBRACKET }
| "]" { RBRACKET }
| "{" { LBRACE }
| "}" { RBRACE }
| ['_' 'a'-'z' 'A'-'Z' '$' '?']['_' 'a'-'z' 'A'-'Z' '0'-'9']* as lxm { ID(lxm) }
| ['-']?['0'-'9']+['/']?['0'-'9']* as lxm { REAL(QQ.of_string lxm) }
| eof { EOF }

and smt2token = parse
| whitespace { math_token lexbuf }
| newline  { next_line lexbuf; math_token lexbuf }
| "and" { AND }
| "or" { OR }
| "forall" { FORALL }
| "exists" { EXISTS }
| "<=" { LEQ }
| "=" { EQ }
| "<" { LT }
| ">" { GT }
| "*" { MUL }
| "+" { ADD }
| "-" { MINUS }
| "(" { LPAREN }
| ")" { RPAREN }
| ['_' 'a'-'z' 'A'-'Z' '$' '?']['_' 'a'-'z' 'A'-'Z' '0'-'9']* as lxm { ID(lxm) }
| ['-']?['0'-'9']+['/']?['0'-'9']* as lxm { REAL(QQ.of_string lxm) }
| eof { EOF }
