open OUnit

let suite = "Main" >::: [
    Test_memo.suite;
    Test_scalar.suite;
    Test_loop.suite;
    Test_fixpoint.suite;
    Test_syntax.suite;
    Test_smt.suite;
    Test_interval.suite;
    Test_ring.suite;
    Test_linear.suite;
    Test_polynomial.suite;
    Test_exppolynomial.suite;
    Test_apron.suite;
    Test_simplify.suite;
    Test_quantifier.suite;
    Test_wedge.suite;
    Test_abstract.suite;
    Test_lts.suite;
    Test_iteration.suite;
    Test_termination.suite;
    Test_transition.suite;
    Test_WeightedGraph.suite;
]

let _ =
  Printexc.record_backtrace true;
  Printf.printf "Running srk test suite";
  ignore (run_test_tt_main suite)
