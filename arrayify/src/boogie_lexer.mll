{
open Boogie_parser  (* The parser's module *)
}

rule token = parse
  | [' ' '\t' '\r' '\n'] { token lexbuf }
  | "procedure" { PROCEDURE }
  | "returns" { RETURNS }
  | "var" { VAR }
  | "true" { TRUE }
  | "false" { FALSE }
  | "havoc" { HAVOC }
  | "assume" { ASSUME }
  | "assert" { ASSERT }
  | "if" { IF }
  | "else" { ELSE }
  | "while" { WHILE }
  | "call" { CALL }
  | "return" { RETURN }
  | '+' { PLUS }
  | '-' { MINUS }
  | '*' { STAR }
  | '/' { SLASH }
  | '%' { PERCENT }
  | "&&" { AND }
  | "||" { OR }
  | "==" { EQ }
  | "!=" { NEQ }
  | '<' { LT }
  | "<=" { LE }
  | '>' { GT }
  | ">=" { GE }
  | '!' { NOT }
  | ":=" { ASSIGN }
  | '(' { LPAR }
  | ')' { RPAR }
  | '{' { LBRACE }
  | '}' { RBRACE }
  | '[' { LBRACKET }
  | ']' { RBRACKET }
  | ',' { COMMA }
  | ';' { SEMICOLON }
  | ':' { COLON }
  | "goto" { GOTO }
  | "int" { INT_TYPE }
  | ['0'-'9']+ as i { INT(int_of_string i) }
  | ['0'-'9']+ '.' ['0'-'9']* as f { REAL(float_of_string f) }
  | ['A'-'Z' 'a'-'z' '_' ] ['A'-'Z' 'a'-'z' '0'-'9' '_' ]* as id { IDENT(id) }
  | eof { EOF }
  | _ as c { failwith (Printf.sprintf "Unexpected character: %c" c) }
