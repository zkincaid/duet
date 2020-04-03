open OUnit
open Test_pervasives
module QQMatrix = Linear.QQMatrix

let tr_symbols = [(wsym,wsym');(xsym,xsym');(ysym,ysym');(zsym,zsym')]

module A = LinearSemiautomaton

let assert_equiv_tdlts x y =
  let show_tdlts = SrkUtil.mk_show A.pp_tdlts in
  assert_equal ~cmp:A.tdlts_equiv ~printer:show_tdlts x y

let assert_equiv_lts x y =
  let equiv_lts a b =
    A.lts_simulates a b && A.lts_simulates b a
  in
  let show_lts = SrkUtil.mk_show A.pp_lts in
  assert_equal ~cmp:equiv_lts ~printer:show_lts x y

let ls_abstract1 () =
  let phi =
    let open Infix in
    x' = x + (int 10)
    && y' = (int 0)
    && z' = x + (int 1)
  in
  let ls = A.abstract srk phi tr_symbols in
  assert_equiv_formula phi (A.to_transition_formula srk ls tr_symbols)

let ls_abstract2 () =
  let phi =
    let open Infix in
    x' = x + (int 10)
    && y = (int 0)
    && z' = x + v
  in
  let ls = A.abstract srk phi tr_symbols in
  let phi_abs =
    let open Infix in
    x' = x + (int 10)
    && z' = x + v
  in
  assert_equiv_formula phi_abs (A.to_transition_formula srk ls tr_symbols)

let ls_abstract3 () =
  let phi =
    let open Infix in
    (x' = x + (int 1)
     && (y' = y + (int 2) || y' = x))
  in
  let ls = A.abstract srk phi tr_symbols in
  assert_equiv_formula phi (A.to_transition_formula srk ls tr_symbols)

let ls_abstract4 () =
  let phi =
    let open Infix in
    (x' = x + (int 1) && y' = y + (int 2))
    || (x' = x + (int 2) && z' = z + (int 3))
  in
  let ls = A.abstract srk phi tr_symbols in
  let phi_abs =
    let open Infix in
    x' = x + (int 1) || x' = x + (int 2)
  in
  assert_equiv_formula phi_abs (A.to_transition_formula srk ls tr_symbols)

let ls_abstract5 () =
  let phi =
    let open Infix in
    x' = x + v && w' = (int 0) && y' = v && z' = (int 0)
    || (x' = x && w' + z' = w + z + (int 1) && w' + y' = x)
  in
  let ls = A.abstract srk phi tr_symbols in
  let phi_abs =
    let open Infix in
    (x' = x + v && (w' + z' = (int 0)) && (w' + y' = v)
     || (x' = x && w' + z' = w + z + (int 1) && w' + y' = x))
  in
  assert_equiv_formula phi_abs (A.to_transition_formula srk ls tr_symbols)

let ls_abstract6 () =
  let phi =
    let open Infix in
    x' = x && y' = y + x && z' = z + v
    || y' = y + w && w' = (int 0) && z' = z + v
  in
  let ls = A.abstract srk phi tr_symbols in
  let phi_abs =
    let open Infix in
    z' = z + v
  in
  assert_equiv_formula phi_abs (A.to_transition_formula srk ls tr_symbols)

let ls_abstract7 () =
  let phi = (* Eigenvalues are (1+i), (1-i), and 2 *)
    let open Infix in
    x' = x - y
    && y' = y + x
    && z' = (int 2) * z + (int 1)
  in
  let ls = A.abstract srk phi tr_symbols in
  let phi_abs =
    let open Infix in
    z' = (int 2) * z + (int 1)
  in
  assert_equiv_formula phi_abs (A.to_transition_formula srk ls tr_symbols)

let suite = "LinearSemiautomaton" >::: [
    "ls_abstract1" >:: ls_abstract1;
    "ls_abstract2" >:: ls_abstract2;
    "ls_abstract3" >:: ls_abstract3;
    "ls_abstract4" >:: ls_abstract4;
    "ls_abstract5" >:: ls_abstract5;
    "ls_abstract6" >:: ls_abstract6;
    "ls_abstract7" >:: ls_abstract7;

    "generalized_eigenspace1" >:: (fun () ->
        let mA = mk_matrix [ [ 1; 0; 0; 0 ];
                             [ 0; 1; 0; 0 ];
                             [ 0; 0; 1; 0 ];
                             [ 0; 0; 0; 1 ] ]
        in
        let mB = mk_matrix [ [ 1; 1; 0; 0 ];
                             [ 0; 1; 1; 0 ];
                             [ 0; 0; 1; 1 ];
                             [ 0; 0; 0; 1 ] ]
        in
        let lts = A.mk_lts mA mB in
        let tdlts =
          A.abstract_generalized_eigenspace lts QQ.one 3
        in
        assert_equiv_tdlts (A.mk_tdlts mA mB) tdlts
      );

    "generalized_eigenspace2" >:: (fun () ->
        let mA = mk_matrix [ [ 1 ];
                             [ 1 ] ]
        in
        let mB = mk_matrix [ [ 1 ];
                             [ 0 ] ]
        in
        let dynamics = mk_matrix [ [ 1; 0 ];
                                   [ 1; 1 ] ]
        in
        let lts = A.mk_lts mA mB in
        let tdlts =
          A.abstract_generalized_eigenspace lts QQ.one 1
        in
        assert_equiv_tdlts (A.mk_tdlts mA dynamics) tdlts
      );

    "generalized_eigenspace3" >:: (fun () ->
        let mA = mk_matrix [ [ 1; 0 ];
                             [ 1; 0 ];
                             [ 0; 1 ] ]
        in
        let mB = mk_matrix [ [ 1; 0 ];
                             [ 1; 1 ];
                             [ 1; 1 ] ]
        in
        let simulation = mk_matrix [ [ 1; 0 ];
                                     [ 0; 1 ];
                                     [ 1; 0 ] ]
        in
        let dynamics = mk_matrix [ [ 1; 0; 0 ];
                                   [ 1; 1; 0 ];
                                   [ 0; 1; 1 ] ]
        in
        let lts = A.mk_lts mA mB in
        let tdlts =
          A.abstract_generalized_eigenspace lts QQ.one 2
        in
        assert_equiv_tdlts (A.mk_tdlts simulation dynamics) tdlts
      );

    "generalized_eigenspace4" >:: (fun () ->
        let mA = mk_matrix [ [ 1; 0; 0 ];
                             [ 0; 1; 0 ];
                             [ 0; 0; 1 ] ]
        in
        let mB = mk_matrix [ [ 0; 1; 0 ];
                             [ 0; 0; 1 ];
                             [ 0; 0; 0 ] ]
        in
        let lts = A.mk_lts mA mB in
        let tdlts =
          A.abstract_generalized_eigenspace lts QQ.zero 2
        in
        assert_equiv_tdlts (A.mk_tdlts mA mB) tdlts
      );

    "generalized_eigenspace5" >:: (fun () ->
        let mA = mk_matrix [ [ 1; 0 ];
                             [ 0; 1 ];
                             [ 1; 1 ] ]
        in
        let mB = mk_matrix [ [ 2; 2 ];
                             [ 2; 2 ];
                             [ 1; 1 ] ]
        in

        let simulation = mk_matrix [ [ 1; -1 ];
                                     [ 2; -1 ];
                                     [ 1;  0 ];
                                     [ 1;  1 ] ]
        in
        let dynamics = mk_matrix [ [ 0; 0; 0; 0 ];
                                   [ 0; 0; 0; 0 ];
                                   [ -3; 2; 0; 0 ];
                                   [ -3; 2; 0; 0 ] ]
        in
        let lts = A.mk_lts mA mB in
        let tdlts =
          A.abstract_generalized_eigenspace lts QQ.zero 1
        in
        assert_equiv_tdlts (A.mk_tdlts simulation dynamics) tdlts
      )
  ]
