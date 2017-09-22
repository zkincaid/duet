{
  open Printf;;
  open KoatParse;;

  let create_hashtable size init =
    let tbl = Hashtbl.create size in
    List.iter (fun (key, data) -> Hashtbl.add tbl key data) init;
    tbl

  let keyword_table = 
    create_hashtable 97 [
       ("GOAL", GOAL);
       ("COMPLEXITY", COMPLEXITY);
       ("STARTTERM", STARTTERM);
       ("VAR", VAR);
       ("RULES", RULES);
       ("FUNCTIONSYMBOLS", FUNCTIONSYMBOLS);
       ("Com_1", COM1)
    ]

  let next_line lexbuf =
    let open Lexing in
    let pos = lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <-
      { pos with pos_bol = lexbuf.lex_curr_pos;
                 pos_lnum = pos.pos_lnum + 1
      }
}

let integer = '0' | (['1'-'9'] ['0'-'9']*)
let id = ['a'-'z' 'A'-'Z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_']*

rule koat = parse
  | "->" { ARROW }
  | ":|:" { WHEN }
  | '+' { ADD }
  | '-' { SUB }
  | '*' { MUL }
  | '/' { DIV }
  | "<=" { LEQ }
  | ">=" { GEQ }
  | '=' { EQ }
  | "!=" { NEQ }
  | "<" { LT }
  | '>' { GT }
  | ',' { COMMA }
  | '(' { LPAREN }
  | ')' { RPAREN }
  | '&' { AND }
  | "&&" { AND }
  | '!' { NOT }
  | "||" { OR }

  | id as identifier
      { try Hashtbl.find keyword_table identifier
	with Not_found -> IDENTIFIER identifier }
  | integer as num { INTEGER (int_of_string num) }

  | [' ' '\t'] { koat lexbuf }
  | ['\n'] { next_line lexbuf; koat lexbuf }
  | "/*" { multiline_comment lexbuf }
  | "//" { line_comment lexbuf }
  | eof { EOF }

and line_comment = parse
  | '\n' { next_line lexbuf; koat lexbuf }
  | _    { line_comment lexbuf }

and multiline_comment = parse
  | "*/" { koat lexbuf }
  | '\n' { next_line lexbuf; multiline_comment lexbuf }
  | _    { multiline_comment lexbuf }

{ }
