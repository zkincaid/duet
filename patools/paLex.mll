{
open PaParse
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
rule token = parse
| whitespace { token lexbuf }
| newline  { next_line lexbuf; token lexbuf }
| "/\\" { AND }
| "\\/" { OR }
| "forall" { FORALL }
| "exists" { EXISTS }
| "final" { FINAL }
| "start" { START }
| "true" { TRUE }
| "false" { FALSE }
| "if" { IF }
| "then" { THEN }
| "else" { ELSE }
| "let" { LET }
| "in" { IN }
| "." { DOT }
| "," { COMMA }
| ":" { COLON }
| "=" { EQ }
| "!=" { NEQ }
| ")->" { ARROWHEAD }
| "--(" { ARROWTAIL }
| "(" { LPAREN }
| ")" { RPAREN }
| ['_' 'a'-'z' 'A'-'Z' '$']['_' 'a'-'z' '0'-'9' '=' '-' '+']* as lxm { ID(lxm) }
| ['a'-'z']+':'['0'-'9']+ as lxm { ID(lxm) }
| ['<'][^'>']*['>'] as lxm { ID(lxm) }
| ['['][^']']*[']'] as lxm { ID(lxm) }
| ['{'][^'}']*['}'] as lxm { ID(lxm) }
| ['1'-'9']['0'-'9']* as lxm { INT(int_of_string lxm) }
| "0" { INT(0) }
| "(*" { comment 0 lexbuf }
| eof { EOF }
and comment n = parse
| newline  { next_line lexbuf; comment n lexbuf }
| "(*" { comment (n + 1) lexbuf }
| "*)" { if n > 0 then comment (n - 1) lexbuf else token lexbuf }
| eof { failwith "Comment terminated by end of file" }                   
| _  { comment n lexbuf }
