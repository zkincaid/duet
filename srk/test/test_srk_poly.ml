open OUnit

let _ =
  ignore (run_test_tt_main Test_polyhedron.suite);
  ignore (run_test_tt_main Test_intLattice.suite);
  ignore (run_test_tt_main Test_polynomialLattice.suite);
  ignore (run_test_tt_main Test_polynomialCone.suite);
  ignore (run_test_tt_main Test_polynomialConeCpClosure.suite)
