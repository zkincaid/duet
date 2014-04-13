open OUnit

let suite = "Main" >:::
  [
    Test_ipa.suite;
  ]

let _ =
  Printexc.record_backtrace true;
  Printf.printf "Running test suite";
  ignore (run_test_tt_main suite)
