open OUnit
open Apak
open Patop

module Struct = Patop.A.Config

let parse_formula string =
  let lexbuf = Lexing.from_string (string ^ "\n") in
  Formula.substitute
    (BatPervasives.undefined ~message:"Start formula should be a sentence")
    (PaParse.main_formula PaLex.token lexbuf)

let parse_pa string =
  let lexbuf = Lexing.from_string (string ^ "\n") in
  PaParse.main PaLex.token lexbuf

let models () =
  let m = Struct.make (BatList.enum [
      ("p", [1]);
      ("q", [2]);
    ])
  in
  let phi =
    parse_formula "exists i. p(i) /\\ forall j. i = j \\/ q(j)"
  in
  let msg =
    Format.asprintf "%a |= %a"
      Struct.pp m
      (Formula.pp Putil.PString.pp Putil.PInt.pp) phi
  in
  assert_bool msg (Struct.models m phi)

let min_models () =
  let phi =
    parse_formula
      "<!$>() /\\ {old>x}() /\\ (forall i. (D(i) /\\ {old'>t}(i,i)))"
  in
  let check m =
    let msg =
      Format.asprintf "%a |= %a"
        Struct.pp m
        (Formula.pp Putil.PString.pp Putil.PInt.pp) phi
    in
    assert_bool msg (Struct.models m phi)
  in
  BatEnum.iter check (Struct.min_models 2 phi)

let substitute_atom () =
    let phi = parse_formula "\
      let def(x) = p(x) \\/ q(x) in
      exists i. forall j. def(i) \\/ r(j,j)"
  in
  let psi = parse_formula "exists i. forall j. p(i) \\/ q(i) \\/ r(j,j)" in
  assert_equal ~printer:show_formula psi phi

module StructSet = BatSet.Make(Struct)
let bounded_check_post pa phi =
  let open BatPervasives in
  let size = 2 in
  BatEnum.iter (fun alpha ->
      let succs (config, i) =
        A.succs pa config (alpha, i)
      in
      let all_succs =
        (ApakEnum.cartesian_product
           (Struct.min_models size phi)
           (1 -- size))
        /@ succs
        |> BatEnum.concat |> StructSet.of_enum
      in
      let post =
        Struct.min_models size (A.post pa phi alpha)
        |> StructSet.of_enum
      in
      begin try
        let c =
          BatEnum.find
            (not % flip StructSet.mem all_succs)
            (StructSet.enum post)
        in
        Format.asprintf "Extra configuration post %s: %a"
          alpha
          Struct.pp c
        |> assert_failure
      with Not_found -> () end;
      try
        let c =
          BatEnum.find
            (not % flip StructSet.mem all_succs)
            (StructSet.enum post)
        in
        Format.asprintf "Missing configuration post %s: %a"
          alpha
          Struct.pp c
        |> assert_failure
      with Not_found -> ()
    ) (A.alphabet pa)
  

let post () =
  let pa = parse_pa "\
    start: forall i. p(i).
    final: q.
    p(i) --( a : j )-> if i = j then q(i) else p(i).
    q(i) --( a : j )-> if i = j then p(i) else q(i)."
  in
  pa

let suite = "patools" >::: [
    "models" >:: models;
    "min_models" >:: min_models;
    "substitute_atom" >:: substitute_atom;
  ]

let _ =
  Printexc.record_backtrace true;
  Printf.printf "Running patools test suite\n";
  ignore (run_test_tt_main suite)
