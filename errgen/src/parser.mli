type token =
  | EOF
  | REAL of (float)
  | VAR of (string)
  | PLUS
  | MINUS
  | TIMES
  | TRUE
  | FALSE
  | AND
  | OR
  | NOT
  | EQ
  | NE
  | GT
  | LT
  | LE
  | GE
  | ASSIGN
  | SEMI
  | IF
  | WHILE
  | ELSE
  | SKIP
  | PRINT
  | ASSERT
  | LPAREN
  | RPAREN
  | LBRACE
  | RBRACE

val main :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Ast.prog_type
