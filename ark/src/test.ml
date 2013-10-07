open OUnit

let suite = "Main" >::: [
  Test_formula.suite;
  Test_numdomain.suite;
  Test_transition.suite
]

let _ =
  Printf.printf "Running test suite";
  ignore (run_test_tt_main suite)
