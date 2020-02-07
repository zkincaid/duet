open Srk
open Apak
open OUnit
open Regex

let parse str =
  let str_len = String.length str in
  let ret x pos = Some (x, pos) in
  let fail _ = None in
  let next_char pos =
    if pos < str_len then Some (String.get str pos, pos + 1)
    else None
  in
  let seq f g pos =
    match f pos with
    | (Some (x, pos)) -> g x pos
    | None            -> None
  in
  let alt f g pos =
    match f pos with
    | None -> g pos
    | x    -> x
  in
  let seq0 f g = seq f (fun _ -> g) in
  let char x =
    seq next_char (fun y -> if x = y then ret x else fail)
  in
  let rec many f =
    alt
      (seq f (fun x -> seq (many f) (fun xs -> ret (x::xs))))
      (ret [])
  in
  let many1 f =
    seq f (fun x -> seq (many f) (fun xs -> ret (x::xs)))
  in
  let sepBy sep f =
    seq f (fun x -> seq (many (seq0 (char sep) f)) (fun xs -> ret (x::xs)))
  in
  let paren f =
    seq0
      (char '(')
      (seq f (fun x -> seq0 (char ')') (ret x)))
  in
  let alpha =
    seq next_char (fun x ->
        if Char.code x >= 97 && Char.code x <= 122
        then ret (Alpha x)
        else fail)
  in
  let rec factor pos = alt (paren plus) alpha pos
  and star pos =
    alt
      (seq
         factor
         (fun x -> seq0 (char '*') (ret (Star x))))
      factor
      pos
  and cat pos =
    seq
      (many1 star)
      (fun xs -> ret (List.fold_right regex_mul xs Epsilon))
      pos
  and plus pos =
    seq
      (sepBy '+' cat)
      (fun xs -> ret (List.fold_right regex_add xs Empty))
      pos
  in
  match plus 0 with
  | Some (x, pos) ->
    if pos = str_len then Some x else None
  | None          -> None

module NR = NormalizedRegex(struct
    type t = char [@@deriving show,ord]
    let consistent = (=)
  end)

let intersects x y = NR.intersects (NR.normalize x) (NR.normalize y)

let regex_string regex =
  SrkUtil.mk_show (pp_regex Format.pp_print_char) regex

let norm_string = NR.show

let must_parse x =
  match parse x with
  | Some y -> y
  | None -> failwith ("Failed to parse " ^ x)

let test_parse () =
  let check x y =
    assert_equal ~printer:regex_string (must_parse x) (must_parse y)
  in
  check "abc" "a(bc)";
  check "a+b+c" "a+(b+c)";
  check "a(bc+d)ef*" "a(((bc)+d)(e(f*)))";
  check "ba*+(ab)*" "(b(a*))+(ab)*";
  check "(a+ab)*+b(a+ab)*" "(a+ab)*+b((a+ab)*)";
  check "(a+ab)*+(z(a+ab)*z)" "(a+(ab))*+(z((a+(ab))*z))";
  check "ab+ba+a+a*b+ba*+(ab)*" "(ab)+((ba)+(a+(((a*)b)+((b(a*))+(ab)*))))"

let parse_norm x = NR.normalize (must_parse x)

let test_norm () =
  let assert_equal = assert_equal ~cmp:NR.equal ~printer:norm_string in
  assert_equal (parse_norm "a+b+c") (parse_norm "c+b+a");
  assert_equal (parse_norm "a*+b+a*") (parse_norm "b+a*");
  assert_equal (parse_norm "(a+(a+a))*+a*") (parse_norm "a*")

let test_derivative () =
  let assert_equal = assert_equal ~cmp:NR.equal ~printer:norm_string in
  assert_equal (parse_norm "b") (NR.derivative 'a' (parse_norm "ab"));
  assert_equal (parse_norm "bb") (NR.derivative 'a' (parse_norm "abb"));
  assert_equal (NR.derivative 'a' (parse_norm "ba")) NR.zero;
  assert_equal (parse_norm "c+b") (NR.derivative 'a' (parse_norm "ab+ac"));
  assert_equal (parse_norm "b(ab)*") (NR.derivative 'a' (parse_norm "(ab)*"));
  assert_equal
    (NR.derivative 'a' (parse_norm "(a+ab)*"))
    (NR.derivative 'a' (NR.derivative 'a' (parse_norm "(a+ab)*")))

let test_intersect () =
  let parse_intersect x y = intersects (must_parse x) (must_parse y) in
  let check x y =
    assert_bool ("intersects " ^ x ^ ", " ^ y) (parse_intersect x y)
  in
  let check_not x y =
    assert_bool ("!intersects " ^ x ^ ", " ^ y) (not (parse_intersect x y))
  in
  check "a" "a";
  check_not "a" "b";
  check "ab*" "abbbb";
  check "a*" "z*";
  check_not "(aa)*" "aaaaaaa";
  check "(aa)*" "aaaaaaaa";
  check "(a+b)(c+d)*(e+f)" "(b+c)*f";
  check_not "(a+b)(c+d)*(e+f)" "(a+b+c)d*";
  check_not "a*(ab)*a*" "baa";
  check "(a*b+aa*+a*b*c)*" "(baa*)(baa*)*b"

let test_eqv () =
  let assert_equal = assert_equal ~cmp:NR.eqv ~printer:norm_string in
  let assert_nequal x y =
    assert_bool
      ("not equivalent: " ^ (norm_string x) ^ ", " ^ (norm_string y))
      (not (NR.eqv x y))
  in
  assert_equal (parse_norm "aa*") (parse_norm "a*a");
  assert_equal (parse_norm "(a*+b*)*") (parse_norm "(a+b)*");
  assert_equal (parse_norm "(a+b+c+d)*") (parse_norm "(a*b*c*d*)*");
  assert_nequal (parse_norm "(a*+b*)*") (parse_norm "(a+b)(a+b)*");
  assert_nequal (parse_norm "a*((b+c)*+d)*a") (parse_norm ("a*(b+c)*d*a"));
  assert_nequal (parse_norm "a*b*(c*d*)*") (parse_norm ("a*b*(cd)*"))

let suite = "Regex" >:::
            [
              "parse" >:: test_parse;
              "normalized" >:: test_norm;
              "derivative" >:: test_derivative;
              "intersect" >:: test_intersect;
              "equivalence" >:: test_eqv;
            ]
