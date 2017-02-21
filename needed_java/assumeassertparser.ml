  open Camlp4.PreCast;;
  module Gram = MakeGram(Lexer);;

  type t = Op1 of string * t
         | Op2 of t * string * t
         | Int of int
         | Id of string;;

  let expression = Gram.Entry.mk "expression";;

  EXTEND Gram
    GLOBAL: expression;

    expression:
    [ "logicals0"
      [ e1 = SELF; "||"; e2 = SELF -> Op2(e1, "||", e2) ]
    | "logicals1"
      [ e1 = SELF; "&&"; e2 = SELF -> Op2(e1, "&&", e2) ]
    | "comparisons0" LEFTA
      [ e1 = SELF; "=="; e2 = SELF -> Op2(e1, "==", e2)
      | e1 = SELF; "!="; e2 = SELF -> Op2(e1, "!=", e2) ]
    | "comparisons1" LEFTA
      [ e1 = SELF;  "<"; e2 = SELF -> Op2(e1,  "<", e2)
      | e1 = SELF; "<="; e2 = SELF -> Op2(e1, "<=", e2)
      | e1 = SELF;  ">"; e2 = SELF -> Op2(e1,  ">", e2)
      | e1 = SELF; ">="; e2 = SELF -> Op2(e1, ">=", e2) ]
    | "additives" LEFTA
      [ e1 = SELF;  "-"; e2 = SELF -> Op2(e1,  "-", e2)
      | e1 = SELF;  "+"; e2 = SELF -> Op2(e1,  "+", e2) ]
    | "multiplicatives" LEFTA
      [ e1 = SELF;  "*"; e2 = SELF -> Op2(e1,  "*", e2)
      | e1 = SELF;  "/"; e2 = SELF -> Op2(e1,  "/", e2) ]
    | "unaryminus" RIGHTA
      [             "-"; e2 = SELF -> Op1(     "-", e2) ]
    | "logicals2" RIGHTA
      (*[             "!"; "("; e2 = SELF; ")" -> Op1("!", e2)]*)
      [             "!"; e2 = SELF -> Op1(     "!", e2) ]
    | "basecases"
      [ `INT(i, _) -> Int(i)
      | `LIDENT s -> Id(s)
      | "("; e = expression; ")" -> e ]
    ];

  END;;

  (* This function parses a string according to the above grammar: *)
  let parse_expression s = Gram.parse_string expression (Loc.mk "asserts file") s;;
  (*
   * Might throw an exception like:
       * Fatal error: exception Loc.Exc_located(_, _)
   *)

  (* This is an example of a function that walks over the parse tree: *)
  let rec toString =
    function
    | Op1(opString, e) -> "(" ^ opString ^ " " ^ (toString e) ^ ")"
    | Op2(e1, opString, e2) -> "(" ^ (toString e1) ^ " " ^ opString ^ " " ^ (toString e2) ^ ")"
    | Int(i) -> string_of_int i
    | Id(x) -> x;;

  let showParse before = Format.printf "Before: %s\tAfter:%s\n" before (toString (parse_expression before));;

  (* Some tests: *)

  (* Should fail to parse: *)
  (*
  showParse "42 * @#$@#$";; (* intentional garbage.  use this to see the exception that bad parses throw *)
  *)

  (* Should succeed in parsing: *)
  (*
  showParse "21 * 32 / 2";;
  showParse "5 * 3 + 2 - 4";;
  showParse "2 + 4 + 3 * 5 / 3 - 5";;
  showParse "42 * (21 + 21) * -33 && x <= 5";; (* was parsed wrongly at some point... but, now, I think it's okay. *)
  showParse "0 || 42 * (21 + 21) * -33 && x <= 5 || 1";;
  showParse "42 * (21 + 21) * (0 - 33) && x <= 5";;
  showParse "8 * 9 - 10 / 2 <= x && y + 5 > z * 9";;
  showParse "!( x < 5)";;
  showParse "! x + 1 < 5 / 9";;
  *)
