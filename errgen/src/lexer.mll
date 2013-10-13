(* File lexer.mll *)
        {
        open Parser        (* The type token is defined in parser.mli *)
	open Ast
        }
        rule token = parse
            [' ' '\t' '\n']     { token lexbuf }     (* skip whitespace *)
	  | "while"        { WHILE }
          | "if"           { IF }
          | "else"         { ELSE }
          | "skip"         { SKIP }
          | "print"        { PRINT }
          | "assert"       { ASSERT }
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
          | ['0'-'9']+['.']?['0'-'9']* as lxm { REAL(float_of_string lxm) }
          | (['_']|['a'-'z']|['A'-'Z'])+ as lxm { VAR(lxm) }
          | '+'            { PLUS }
          | '-'            { MINUS }
          | '*'            { TIMES }
          | '('            { LPAREN }
          | ')'            { RPAREN }
          | '{'            { LBRACE }
          | '}'            { RBRACE }
          | eof            { EOF }  
