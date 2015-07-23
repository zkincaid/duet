open Syntax

exception Nonlinear

module type AbstractionContext = sig

  include Syntax.BuilderContext

  val const_typ : const_sym -> typ
  module Term : sig
    type t = term
    val eval : ('a open_term -> 'a) -> t -> 'a
    val pp : Format.formatter -> t -> unit
  end
  module Formula : sig
    type t = formula
    val eval : (('a, term) open_formula -> 'a) -> t -> 'a    
    val pp : Format.formatter -> t -> unit
  end

  type solver
  type model

  module Solver : sig
    val mk_solver : unit -> solver
    val add : solver -> formula list -> unit
    val push : solver -> unit
    val pop : solver -> int -> unit
    val check : solver -> formula list -> [ `Sat | `Unsat | `Unknown ]
    val get_model : solver -> [ `Sat of model | `Unsat | `Unknown ]
  end

  module Model : sig
    val eval_int : model -> term -> ZZ.t
    val eval_real : model -> term -> QQ.t
    val sat : model -> formula -> bool
    val to_string : model -> string
  end
end

val affine_hull :
  (module AbstractionContext with type formula = 'a and type term = 'b) ->
  'a ->
  const_sym list ->
  'b list
