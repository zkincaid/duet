open Syntax

module Model : sig
  type t
  val evaluate_formula : 'a context -> t -> 'a formula -> bool
  val nonnegative_cone : t -> PolynomialCone.t
  val sign : 'a context -> t -> 'a arith_term -> [ `Zero | `Pos | `Neg | `Unknown ]
end

module Solver : sig
  type 'a t
  val make : 'a context -> 'a t
  val add : 'a t -> 'a formula list -> unit
  val get_model : ?assumptions:('a formula list) -> 'a t -> [ `Sat of Model.t | `Unsat | `Unknown ]
  val push : 'a t -> unit
  val pop : 'a t -> int -> unit
end

val get_model : 'a context -> 'a formula -> [ `Sat of Model.t | `Unsat | `Unknown ]
val is_sat : 'a context -> 'a formula -> [ `Sat | `Unsat | `Unknown ]
val find_consequences : 'a context -> 'a formula -> PolynomialCone.t
val abstract : 'a context ->
  (PolynomialCone.t -> PolynomialCone.t) ->
  'a formula ->
  PolynomialCone.t
