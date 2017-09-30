open OUnit
open ArkParse

let suite = "Main" >::: [
    Test_memo.suite;
    Test_scalar.suite;
    Test_syntax.suite;
    Test_smt.suite;
    Test_interval.suite;
    Test_linear.suite;
    Test_polynomial.suite;
    Test_apron.suite;
    Test_quantifier.suite;
    Test_game.suite;
    Test_wedge.suite;
    Test_abstract.suite;
    Test_iteration.suite;
    Test_transition.suite;
]

let _ =
  Printexc.record_backtrace true;
  Printf.printf "Running ark test suite";
  ignore (run_test_tt_main suite)
