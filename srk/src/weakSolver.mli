open Syntax

module Model : sig
  type t
  val evaluate_formula : 'a context -> t -> 'a formula -> bool
  val nonnegative_cone : t -> PolynomialCone.t
end

module Solver : sig
  type 'a t
  val mk_solver : 'a context -> 'a t
  val add : 'a t -> 'a formula list -> unit
  val get_model : 'a t -> [ `Sat of Model.t | `Unsat | `Unknown ]
end

val get_model : 'a context -> 'a formula -> [ `Sat of Model.t | `Unsat | `Unknown ]
val is_sat : 'a context -> 'a formula -> [ `Sat | `Unsat | `Unknown ]
val find_consequences : 'a context -> 'a formula -> PolynomialCone.t
val find_linear_consequences : 'a context -> 'a formula -> BatSet.Int.t -> PolynomialCone.t
