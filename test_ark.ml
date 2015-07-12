open OUnit

let suite = "Main" >::: [
  Test_scalar.suite;
]

let _ =
  Printexc.record_backtrace true;
  Printf.printf "Running ark test suite";
  ignore (run_test_tt_main suite)
