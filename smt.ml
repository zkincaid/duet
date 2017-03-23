open Syntax
open BatPervasives

include Apak.Log.Make(struct let name = "ark.smt" end)

class type ['a] smt_model = object
  method eval_int : 'a term -> ZZ.t
  method eval_real : 'a term -> QQ.t
  method sat :  'a formula -> bool
  method to_string : unit -> string
end

class type ['a] smt_solver = object
  method add : ('a formula) list -> unit
  method push : unit -> unit
  method pop : int -> unit
  method reset : unit -> unit
  method check : ('a formula) list -> [ `Sat | `Unsat | `Unknown ]  
  method to_string : unit -> string
  method get_model : unit -> [ `Sat of 'a smt_model | `Unsat | `Unknown ]
  method get_unsat_core : ('a formula) list ->
    [ `Sat | `Unsat of ('a formula) list | `Unknown ]
end

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

let set_default_solver s = default_solver := s
