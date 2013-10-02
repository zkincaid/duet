open OUnit

let suite = "Main" >:::
  [
    Test_regex.suite;
    Test_kleene.suite;
    Test_memo.suite;
  ]

let _ =
  run_test_tt_main suite
