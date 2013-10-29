(* File lexer.mll *)
        {
        open Parser        (* The type token is defined in parser.mli *)
	open Ast
	open Ark
	open ArkPervasives
        }
        rule token = parse
            [' ' '\t' '\n']     { token lexbuf }     (* skip whitespace *)
	  | "while"        { WHILE }
          | "if"           { IF }
          | "else"         { ELSE }
          | "skip"         { SKIP }
          | "print"        { PRINT }
          | "assert"       { ASSERT }
          | "assume"       { ASSUME }
          | '='            { ASSIGN }
          | "true"         { TRUE }
          | "false"        { FALSE }
          | "=="           { EQ }
	  | "!="           { NE } 
          | '>'            { GT }
          | '<'            { LT }
          | "<="           { LE }
          | ">="           { GE }
          | "&&"           { AND }
          | "||"           { OR }
          | '!'            { NOT }
          | ';'            { SEMI }
(*          | ['0'-'9']+['.']?['0'-'9']* as lxm { REAL(float_of_string lxm) }*)
	  | ['0'-'9']+['/']?['0'-'9']* as lxm
	      { REAL(QQ.of_string lxm) }

	  | ['_' 'a'-'z' 'A'-'Z']['_' 'a'-'z' '0'-'9']* as lxm { VAR(lxm) }
          | '+'            { PLUS }
          | '-'            { MINUS }
          | '*'            { TIMES }
          | '('            { LPAREN }
          | ')'            { RPAREN }
          | '{'            { LBRACE }
          | '}'            { RBRACE }
          | eof            { EOF }  
