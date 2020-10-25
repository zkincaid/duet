{
open SrkSmtlib2Parse
open Lexing
let next_line lexbuf =
  let pos = lexbuf.lex_curr_p in
  lexbuf.lex_curr_p <-
    { pos with pos_bol = lexbuf.lex_curr_pos;
               pos_lnum = pos.pos_lnum + 1
    }

let hex_to_zz hex =
  let ten = ZZ.of_int 10 in
  let rec go i v =
    if i >= String.length hex then v else
    let cv =
      let c = String.get hex i in
      match c with
      | '0' | '1' | '2' | '3' | '4'
      | '5' | '6' | '7' | '8' | '9' ->
        (int_of_char c) - (int_of_char '0')
      | 'a' | 'b' | 'c' | 'd' | 'e' | 'f' ->
        10 + (int_of_char c) - (int_of_char 'a')
      | 'A' | 'B' | 'C' | 'D' | 'E' | 'F' ->
        10 + (int_of_char c) - (int_of_char 'A')
      | _ -> invalid_arg "Input is not a hexidecimal value"
    in go (i + 1) (ZZ.add (ZZ.mul v ten) (ZZ.of_int cv))
  in go 0 ZZ.zero

let bin_to_zz bin =
  let two = ZZ.of_int 2 in
  let rec go i v =
    if i >= String.length bin then v else
    let cv =
      match String.get bin i with
      | '0' -> 0
      | '1' -> 1
      | _ -> invalid_arg "input is not a binary value"
    in go (i + 1) (ZZ.add (ZZ.mul v two) (ZZ.of_int cv))
  in go 0 ZZ.zero

let decimal_to_qq int frac =
  let int = QQ.of_string int in
  let pow = String.length frac in
  let frac = QQ.div (QQ.of_string frac) (QQ.exp (QQ.of_int 10) pow) in
  QQ.add int frac
}
let newline = '\r' | '\n' | "\r\n"
let whitespace = [' ' '\t']+
let numeral = "0" | ['1'-'9']['0'-'9']*

rule token = parse
| whitespace { token lexbuf }
| newline  { next_line lexbuf; token lexbuf }
| "_" { UNDERSCORE }
| "!" { BANG }
| "(" { LPAREN }
| ")" { RPAREN }
| "as" { AS }
| "let" { LET }
| "forall" { FORALL }
| "exists" { EXISTS }
| "model" { MODEL }
| "define-fun" { DEFFUN }
| numeral as lxm { INT (ZZ.of_string lxm) }
| "#x" (("0" | ['1'-'9' 'a'-'f' 'A'-'F']['0'-'9' 'a'-'f' 'A'-'F']*) as lxm) { INT (hex_to_zz lxm) }
| "#b" (("0" | "1"['0'-'1']*) as lxm) { INT (bin_to_zz lxm) }
| (numeral as int) '.' ('0'* numeral as frac) { REAL (decimal_to_qq int frac) }
| '"' [^ '"'] '"' as lxm { STRING (String.sub lxm 1 ((String.length lxm) - 2)) }
| ['a'-'z' 'A'-'Z' '+' '-' '/' '*' '=' '%' '?' '!' '.' '$' '_' '~' '&' '^' '<' '>' '@']['a'-'z' 'A'-'Z' '0'-'9' '+' '-' '/' '*' '=' '%' '?' '!' '.' '$' '_' '~' '&' '^' '<' '>' '@']* as lxm { SYMBOL lxm }
| '|' [^ '|' '\\']* '|' as lxm { SYMBOL lxm }
| ":"(['a'-'z' 'A'-'Z' '+' '-' '/' '*' '=' '%' '?' '!' '.' '$' '_' '~' '&' '^' '<' '>' '@']['a'-'z' 'A'-'Z' '0'-'9' '+' '-' '/' '*' '=' '%' '?' '!' '.' '$' '_' '~' '&' '^' '<' '>' '@']* as lxm) { KEYWORD lxm }
| eof { EOF }
