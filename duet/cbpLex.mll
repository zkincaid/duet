{
  open CbpParse;;

  let create_hashtable size init =
    let tbl = Hashtbl.create size in
    List.iter (fun (key, data) -> Hashtbl.add tbl key data) init;
    tbl

  let keyword_table = 
    create_hashtable 8 [
      ("return", RETURN);
      ("goto", GOTO);
      ("skip", SKIP);
(*      ("dead", DEAD); *) (* ? *)
      ("dfs", DFS);   (* ? *)
      ("do", DO);
      ("od", OD);
      ("else", ELSE);
      ("elsif", ELSIF);
      ("if", IF);
      ("then", THEN);
      ("fi", FI);
      ("decl", DECL);
      ("while", WHILE);
      ("begin", BEGIN);
      ("end", END);
      ("bool", BOOL);
      ("void", VOID);
      ("assert", ASSERT);
      ("assume", ASSUME);
(*      ("print", PRINT); *)
      ("enforce", ENFORCE);
      ("constrain", CONSTRAIN);
      ("schoose", SCHOOSE);
      ("abortif", ABORTIF);
      ("start_thread", START_THREAD);
      ("end_thread", END_THREAD);
(*      ("sync", SYNC); *)
      ("atomic_begin", ATOMIC_BEGIN);
      ("atomic_end", ATOMIC_END);
    ]
}
let integer = '0' | (['1'-'9'] ['0'-'9']*)
let id = ['a'-'z' 'A'-'Z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_']*

rule cbp = parse
  | '*' { HAVOC }
  | '?' { TERNARY }
  | ":=" { ASSIGN }
  | '=' { EQ }
  | "!=" { NEQ }
  | "=>" { IMPL }
  | ';' { SEMI }

  | "'" { SINGLE_QUOTE }
  | ',' { COMMA }
  | ':' { COLON }
  | '(' { LPAREN }
  | ')' { RPAREN }
  | '[' { LBRACKET }
  | ']' { RBRACKET }
  | '&' { AND }
  | "&&" { AND }
  | '!' { NOT }
       (*  | '~' { TILDE }*)
  | '^' { XOR }
  | '|' { OR }
  | "||" { OR }
  | '<' { LANGLE }
  | '>' { RANGLE }

  | id as identifier
      { try Hashtbl.find keyword_table identifier
	with Not_found -> IDENTIFIER identifier }
  | integer as num { INTEGER (int_of_string num) }

  | [' ' '\t' '\n'] { cbp lexbuf }
  | "/*" { multiline_comment lexbuf }
  | "//" { line_comment lexbuf }
  | eof { EOF }

and line_comment = parse
  | '\n' { cbp lexbuf }
  | _    { line_comment lexbuf }

and multiline_comment = parse
  | "*/" { cbp lexbuf }
  | _    { multiline_comment lexbuf }

{ }
