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

      "exp_seq1" >:: (fun () ->
        let seq = BatDynArray.to_list (TerminationDTA.XSeq.seq_of_exp 32 2) in
        assert_equal seq [0]
      );
      "exp_seq2" >:: (fun () ->
        let seq = BatDynArray.to_list (TerminationDTA.XSeq.seq_of_exp 6 2) in
        assert_equal seq [4; 2]
      );
      "exp_seq3" >:: (fun () ->
        let seq = BatDynArray.to_list (TerminationDTA.XSeq.seq_of_exp 5 3) in
        assert_equal seq [1; 3; 4; 2]
      )


    ]
