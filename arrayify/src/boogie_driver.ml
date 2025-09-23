let parse (filename : string) : Boogie_ast.program =
  let chan = open_in filename in
  let lexbuf = Lexing.from_channel chan in
  try
    let ast = Boogie_parser.program Boogie_lexer.token lexbuf in
    close_in chan;
    ast
  with
  | Boogie_parser.Error ->
      let pos = lexbuf.Lexing.lex_curr_p in
      Printf.eprintf "Syntax error at line %d, column %d\n"
        pos.Lexing.pos_lnum
        (pos.Lexing.pos_cnum - pos.Lexing.pos_bol);
      close_in chan;
      exit 1
