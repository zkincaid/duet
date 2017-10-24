open Syntax
open BatPervasives

include Log.Make(struct let name = "srk.smt" end)
let default_solver = ref `Z3

let mk_solver srk =
  match !default_solver with
  | `Z3 -> (SrkZ3.mk_solver srk :> 'a smt_solver)
  | `Mathsat -> (SrkMathsat.mk_solver srk :> 'a smt_solver)

let get_model srk phi =
  let solver = mk_solver srk in
  solver#add [phi];
  solver#get_model ()

let is_sat srk phi =
  let solver = mk_solver srk in
  solver#add [phi];
  solver#check []

let set_default_solver s = default_solver := s
