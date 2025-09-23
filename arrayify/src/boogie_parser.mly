%{
open Boogie_ast  
%}

%token <int> INT
%token <float> REAL
%token <string> IDENT
%token ARRAY
%token TRUE FALSE
%token PLUS MINUS STAR SLASH PERCENT
%token AND OR EQ NEQ LT LE GT GE
%token NOT
%token ASSIGN
%token HAVOC ASSUME ASSERT IF ELSE WHILE CALL RETURN
%token LPAR RPAR LBRACE RBRACE LBRACKET RBRACKET COMMA SEMICOLON
%token COLON PROCEDURE VAR RETURNS
%token GOTO
%token INT_TYPE
%token EOF


%start program
%type <Boogie_ast.program> program

%%

program:
  globals procedures EOF { { globals = $1; procedures = $2 } }

globals:
  | /* empty */ { [] }
  | globals VAR IDENT COLON typ SEMICOLON { ($3, $5) :: $1 }

procedures:
  | /* empty */ { [] }
  | procedures procedure { $2 :: $1 }

procedure:
  | PROCEDURE IDENT LPAR params RPAR returns LBRACE locals stmts RBRACE
    { { name = $2; params = $4; returns = $6; locals = $8; body = $9 } }
  | PROCEDURE IDENT LPAR params RPAR LBRACE locals stmts RBRACE
    { { name = $2; params = $4; returns = []; locals = $7; body = $8 } }

params:
  | /* empty */ { [] }
  | nonempty_params { $1 }

nonempty_params:
  param { [$1] }
  | param COMMA nonempty_params { $1 :: $3 }

param:
  IDENT COLON typ { ($1, $3) }

returns:
  | /* empty */ { [] }
  | RETURNS LPAR returns_inner RPAR { $3 }

returns_inner:
  | return { [$1] }
  | return COMMA returns_inner { $1 :: $3 }

return:
    IDENT COLON typ { ($1, $3) }

locals:
  | /* empty */ { [] }
  | locals VAR IDENT COLON typ SEMICOLON { ($3, $5) :: $1 }

typ:
  | INT_TYPE { Int }
  | LBRACKET typ RBRACKET typ { Array $4 }

stmts:
  | /* empty */ { [] }
  | stmt stmts { $1 :: $2 }

stmt:
  | IDENT ASSIGN expr SEMICOLON { Assign($1, $3) }
  | IDENT LBRACKET expr RBRACKET ASSIGN expr SEMICOLON { ArrayAssign($1, $3, $6) }
  | HAVOC IDENT SEMICOLON { Havoc($2) }
  | ASSUME expr SEMICOLON { Assume($2) }
  | ASSERT expr SEMICOLON { Assert($2) }
  | IF expr LBRACE stmts RBRACE elsepart { If($2, $4, $6)}
  | WHILE expr LBRACE stmts RBRACE { While($2, $4) }
  | CALL IDENT LPAR args RPAR SEMICOLON { Call($2, $4) }
  | IDENT COLON { Label($1) }
  | GOTO IDENT SEMICOLON { Goto $2 }
  | RETURN SEMICOLON { Return }

elsepart:
  | /* empty */ { [] }
  | ELSE LBRACE stmts RBRACE { $3 }
  | ELSE IF expr LBRACE stmts RBRACE elsepart { [If($3, $5, $7)] }

args:
  | /* empty */ { [] }
  | nonempty_args { $1 }

nonempty_args:
  expr { [$1] }
  | expr COMMA nonempty_args { $1 :: $3 }

expr:
  | INT { LiteralInt($1) }
  | REAL { LiteralReal($1) }
  | TRUE { LiteralBool(true) }
  | FALSE { LiteralBool(false) }
  | IDENT { Var($1) }
  | expr PLUS expr { BinaryOp(Add, $1, $3) }
  | expr MINUS expr { BinaryOp(Sub, $1, $3) }
  | expr STAR expr { BinaryOp(Mul, $1, $3) }
  | expr SLASH expr { BinaryOp(Div, $1, $3) }
  | expr PERCENT expr { BinaryOp(Mod, $1, $3) }
  | expr AND expr { BinaryOp(And, $1, $3) }
  | expr OR expr { BinaryOp(Or, $1, $3) }
  | expr EQ expr { BinaryOp(Eq, $1, $3) }
  | expr NEQ expr { BinaryOp(Neq, $1, $3) }
  | expr LT expr { BinaryOp(Lt, $1, $3) }
  | expr LE expr { BinaryOp(Le, $1, $3) }
  | expr GT expr { BinaryOp(Gt, $1, $3) }
  | expr GE expr { BinaryOp(Ge, $1, $3) }
  | NOT expr { UnaryOp(Not, $2) }
  | MINUS expr { UnaryOp(Neg, $2) }
  | IDENT LPAR args RPAR { FunctionCall($1, $3) }
  | LPAR expr RPAR { $2 }
  | IDENT LBRACKET expr RBRACKET { ArrayAccess($1, $3) }

