open Srk
open Syntax
open OUnit
open Test_pervasives


let tr_symbols = [(wsym,wsym');(xsym,xsym');(ysym,ysym');(zsym,zsym')]
let mp_exp =
  let all_sym = (List.map fst tr_symbols)@(List.map snd tr_symbols) in
  fun tr_symbols phi ->
  TerminationExp.mp
    (module Iteration.LinearRecurrenceInequation)
    srk
    (TransitionFormula.make
       ~exists:(fun sym -> List.mem sym all_sym)
       phi
       tr_symbols)

let build_tf phi =
  let all_sym = (List.map fst tr_symbols)@(List.map snd tr_symbols) in
  TransitionFormula.make
    ~exists:(fun sym -> List.mem sym all_sym)
    phi
    tr_symbols

let suite = "Termination" >::: [
      "even" >:: (fun () ->
        let tr =
          Infix.(!(x = (int 0)) && x' = x - (int 2))
        in
        assert_equiv_quantified_formula
          Infix.((x mod (int 2)) = (int 0) && (int 0) <= x)
          (mp_exp tr_symbols tr)
      );
      "disjunctive_guard" >:: (fun () ->
        let tr =
          Infix.(((int 0) < x || (int 0) < y)
                 && (x' = x - (int 1) && y' = y - (int 1)))
        in
        assert_equiv_quantified_formula
          (mk_true srk)
          (mp_exp tr_symbols tr)
      );
      "midpoint" >:: (fun () ->
        let tr =
          Infix.((!(x = y)
                  && ((x' = x + (int 1) && y' = y)
                      || (x' = x && y' = y - (int 1)))))
        in
        assert_equiv_quantified_formula
          Infix.(x <= y)
          (mp_exp tr_symbols tr)
      );
      "llrf_1D" >:: (fun () ->
        let phi =
          Infix.( ((int 0) < x) && x' = x - (int 1))
          |> build_tf
        in
        assert_bool "Has LLRF" (TerminationLLRF.has_llrf srk phi)
      );
      "llrf_2D" >:: (fun () ->
        let phi =
          Infix.( (int 0) < x &&
                    ( ((int 0) < y && (y' = y - (int 1)) && x' = x)
                      || (y <= (int 0)) && y' = (int 10) && x' = x - (int 1)))
          |> build_tf
        in
        assert_bool "Has LLRF" (TerminationLLRF.has_llrf srk phi)
      );
      "llrf_sym_const" >:: (fun () ->
        let phi =
          TransitionFormula.make
            Infix.( (int 0) < x &&
                      ( (z < y && (y' = y - x) && x' = x)
                        || (y <= z) && x' = x - (int 1)))
            [(xsym,xsym');(ysym,ysym')]
        in
        assert_bool "Has LLRF" (TerminationLLRF.has_llrf srk phi)
      );
      "no_llrf" >:: (fun () ->
        let phi =
          Infix.( (int 0) <= x &&
                    (((y' = y - (int 1)) && x' = x)
                     || x' = x - (int 1)))
          |> build_tf
        in
        assert_bool "No LLRF" (not (TerminationLLRF.has_llrf srk phi))
      );
      "no_llrf_sym_const" >:: (fun () ->
        let phi =
          TransitionFormula.make
            ~exists:(fun w -> List.mem w [xsym;xsym';ysym;ysym'])
            Infix.( (int 0) < x &&
                      ( (z < y && (y' = y - x) && x' = x)
                        || (y <= z) && x' = x - (int 1)))
            [(xsym,xsym');(ysym,ysym')]
        in
        assert_bool "No LLRF" (not (TerminationLLRF.has_llrf srk phi))
      );


    ]
