type token =
  | EOF
  | REAL of (Ark.ArkPervasives.QQ.t)
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
  | ASSUME
  | LPAREN
  | RPAREN
  | LBRACE
  | RBRACE

val main :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Ast.prog_type
