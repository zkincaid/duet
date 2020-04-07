(* Try to prove a loop terminate by synthesizing lexicographic ranking functions *)

type analysis_result = ProvedToTerminate | Unknown

(**   arg1: context, e.g., srk
      arg2: a way to convert formulas into transition systems: Transition.to_transition_formula
      arg3: a tuple of loop header formula, loop body formula
      return: whether this loop can be proved to terminate using lexicographic ranking function
 *)
val prove_LLRF_termination: 'a Syntax.context ->
('b ->
 'c list ->
 (Syntax.Symbol.Map.key * Syntax.Symbol.Set.elt) list * 'a Syntax.formula) ->
'd * 'b -> 
analysis_result
