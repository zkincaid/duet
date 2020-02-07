open Abstract
open Syntax
open SrkApron
open Printf
open BatEnum
open SolvablePolynomial

module Vec = Linear.QQVector
module Mat = Linear.QQMatrix
module NL = NestedLoops

include Log.Make(struct let name = "TerminationDTA" end)


let generate_terminating_conditions srk tto_transition_formula loop =
  let _, body = loop in
  let x_xp, orig_formula = tto_transition_formula body [] in
  let body_formula = Nonlinear.linearize srk orig_formula in
  match Smt.get_model srk body_formula with
  | `Sat interp -> 
    logf ~attributes:[`Bold; `Green] "\n\n\nTransition formula SAT\n\n";
    
  | `Unknown -> failwith "SMT solver should not return unknown for QRA formulas"
  | `Unsat -> (logf ~attributes:[`Bold; `Yellow] "Transition formula UNSAT, done"); ()

