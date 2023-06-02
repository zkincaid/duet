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
