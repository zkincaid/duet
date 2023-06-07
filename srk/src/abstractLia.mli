(** Computing integer hull of quantifier-free LIA formulas using model-based projection.
    All variables have to be of integer type (for now).
 *)

(** [Standard] computes the integer hull of the implicant that the model satisfies
    and then projects it.
    [Cooper] computes the (projected) disjunct in Cooper's LIA QE that the model satisfies.
 *)
val integer_hull: 'a Syntax.context -> how:[`Standard | `Cooper | `Cone] ->
                  'a Syntax.formula ->
                  ('a Syntax.arith_term) array -> DD.closed DD.t

(** Abstract domain that supports symbolic abstraction *)
module type AbstractDomain = sig
  type t
  type context
  val context : context Syntax.context

  val bottom : t
  val join : t -> t -> t
  val concretize : t -> context Syntax.formula
  val abstract : context Syntax.formula -> context Interpretation.interpretation -> t

  val pp : Format.formatter -> t -> unit

end

module Abstract (A : AbstractDomain) : sig

  val init : A.context Syntax.formula -> A.context Smt.Solver.t * A.t

  val abstract : A.context Syntax.formula -> A.t

end
