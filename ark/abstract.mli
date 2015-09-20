open Syntax

exception Nonlinear

module type AbstractionContext = sig

  include Syntax.BuilderContext
  val const_typ : const_sym -> typ
  val pp_const : Format.formatter -> const_sym -> unit
  val mk_sub : term -> term -> term
  val mk_skolem : ?name:string -> typ -> const_sym
  module Term : sig
    type t = term
    val eval : ('a open_term -> 'a) -> t -> 'a
    val pp : Format.formatter -> t -> unit
    val compare : t -> t -> int
    val equal : t -> t -> bool
    val fold_constants : (const_sym -> 'a -> 'a) -> t -> 'a -> 'a
  end
  module Formula : sig
    type t = formula
    val eval : (('a, term) open_formula -> 'a) -> t -> 'a    
    val pp : Format.formatter -> t -> unit
    val substitute_const : (const_sym -> term) -> t -> t
    val substitute : (int -> term) -> t -> t
    val destruct : t -> (t, term) open_formula
    val fold_constants : (const_sym -> 'a -> 'a) -> t -> 'a -> 'a
    val prenex : t -> t
  end

  type solver
  type model

  val get_model : formula -> [`Sat of model | `Unknown | `Unsat ]
  val interpolate_seq : formula list ->
    [ `Sat of model | `Unsat of formula list | `Unknown ]

  module Solver : sig
    val mk_solver : unit -> solver
    val add : solver -> formula list -> unit
    val push : solver -> unit
    val pop : solver -> int -> unit
    val check : solver -> formula list -> [ `Sat | `Unsat | `Unknown ]
    val get_model : solver -> [ `Sat of model | `Unsat | `Unknown ]
    val get_unsat_core : solver ->
      formula list ->
      [ `Sat | `Unsat of formula list | `Unknown ]
  end

  module Model : sig
    val eval_int : model -> term -> ZZ.t
    val eval_real : model -> term -> QQ.t
    val sat : model -> formula -> bool
    val to_string : model -> string
  end

  val optimize_box : formula -> term list -> [ `Sat of Interval.t list
					     | `Unsat
					     | `Unknown ]
end

val affine_hull :
  (module AbstractionContext with type formula = 'a and type term = 'b) ->
  'a ->
  const_sym list ->
  'b list

val boxify :
  (module AbstractionContext with type formula = 'a and type term = 'b) ->
  'a ->
  'b list ->
  'a

(** Alternating quantifier satisfiability *)
val aqsat :
  (module AbstractionContext with type formula = 'a) ->
  'a ->
  [ `Sat | `Unsat | `Unknown ]

(** Alternating quantifier optimization *)
val aqopt :
  (module AbstractionContext with type formula = 'a and type term = 'b) ->
  'a ->
  'b ->
  [ `Sat of Interval.t
  | `Unsat
  | `Unknown ]

(** Quantifier eliminiation via model-based projection *)
val qe_mbp :
  (module AbstractionContext with type formula = 'a) ->
  'a ->
  'a
