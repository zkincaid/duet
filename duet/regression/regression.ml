let print_result f s =
  print_endline (if f s then "Passed" else "Failed")

let run_bt_arg =
  ("-run-bt",
   Arg.String (print_result BtRegression.run),
   "Run a dependence testing regression test")

let run_cfg_arg =
  ("-run-cfg",
   Arg.String (print_result CfgRegression.run),
   "Run a CFG regression test")

let baseline_bt_arg =
  ("-baseline-bt",
   Arg.String BtRegression.gen,
   "Generate a dependence testing baseline")

let baseline_cfg_arg =
  ("-baseline-cfg", Arg.String CfgRegression.gen, "Generate a CFG baseline")

let load_path_arg =
  ("-loadpath", Arg.String Cdfautil.set_load_path, " Set load path")

let spec_list =
  [
    (* run *)
    run_bt_arg;
    run_cfg_arg;

    (* baselines *)
    baseline_bt_arg;
    baseline_cfg_arg;

    (* options *)
    load_path_arg;
  ]

let usage_msg = "Regression testing interface."

let anon_fun s = raise (Arg.Bad (s ^ " is not recognized"));;

Arg.parse (Arg.align spec_list) anon_fun usage_msg
