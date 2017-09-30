open Syntax
open BatPervasives

include Log.Make(struct let name = "ark.smt" end)
let default_solver = ref `Z3

let mk_solver ark =
  match !default_solver with
  | `Z3 -> (ArkZ3.mk_solver ark :> 'a smt_solver)
  | `Mathsat -> (ArkMathsat.mk_solver ark :> 'a smt_solver)

let get_model ark phi =
  let solver = mk_solver ark in
  solver#add [phi];
  solver#get_model ()

let is_sat ark phi =
  let solver = mk_solver ark in
  solver#add [phi];
  solver#check []

let entails ark phi psi =
  let solver = mk_solver ark in
  solver#add [phi; mk_not ark psi];
  match solver#check [] with
  | `Sat -> `No
  | `Unsat -> `Yes
  | `Unknown -> `Unknown

let set_default_solver s = default_solver := s
