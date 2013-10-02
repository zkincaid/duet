open Core
open Apak

include Putil.Ordered with type t = def

module Set : Putil.Set.S with type elt = def
module Map : BatMap.S with type key = def
module HT : Hashtbl.S with type key = def

val get_defs : def -> AP.Set.t
val get_uses : def -> AP.Set.t
val get_accessed : def -> AP.Set.t
val free_vars : def -> Var.Set.t
val assigned_var : def -> var option

val hash : def -> int
val equal : def -> def -> bool
val initial : def

val clone : def -> def
