open Syntax
open BatPervasives

include Log.Make(struct let name = "srk.smt" end)

let mk_solver ?(theory="") srk = SrkZ3.mk_solver ~theory srk

let get_model srk phi =
  let solver = mk_solver srk in
  solver#add [phi];
  solver#get_model ()

let is_sat srk phi =
  let solver = mk_solver srk in
  solver#add [phi];
  solver#check []

let entails srk phi psi =
  match is_sat srk (mk_and srk [phi; mk_not srk psi]) with
  | `Sat -> `No
  | `Unsat -> `Yes
  | `Unknown -> `Unknown

let equiv srk phi psi =
  let equiv_formula =
    mk_or srk [mk_and srk [phi; mk_not srk psi];
               mk_and srk [mk_not srk phi; psi]]
  in
  match is_sat srk equiv_formula with
  | `Sat -> `No
  | `Unsat -> `Yes
  | `Unknown -> `Unknown
