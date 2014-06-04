open OUnit

let suite = "Main" >::: [
  Test_pervasives.suite;
  Test_formula.suite;
  Test_numdomain.suite;
  Test_transition.suite
]

let _ =
  Printexc.record_backtrace true;
  Printf.printf "Running test suite";
  ignore (run_test_tt_main suite)
