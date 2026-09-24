(** Groebner basis computation using the msolve executable.

    The executable is selected by the [MSOLVE] environment variable and
    defaults to [msolve]. *)

val grobner_basis :
  Polynomial.Monomial.dim list ->
  Polynomial.Monomial.dim list ->
  Polynomial.QQXs.t list ->
  Polynomial.QQXs.t list

(** [eliminate eliminated retained polys] computes generators for the
    elimination ideal [<polys> intersect Q[retained]]. *)
val eliminate :
  Polynomial.Monomial.dim list ->
  Polynomial.Monomial.dim list ->
  Polynomial.QQXs.t list ->
  Polynomial.QQXs.t list

(** The two-block degree-reverse-lexicographic order used by
    {!grobner_basis}. *)
val get_mon_order :
  Polynomial.Monomial.dim list ->
  Polynomial.Monomial.dim list ->
  Polynomial.Monomial.t ->
  Polynomial.Monomial.t ->
  [ `Eq | `Lt | `Gt ]

(** [parametrization variables polys] computes a rational univariate
    parametrization of a zero-dimensional system.  It returns the linear form,
    its minimal polynomial, the common denominator, and the numerator/scale
    pair for each variable other than the parametrizing variable. *)
val parametrization :
  Polynomial.Monomial.dim list ->
  Polynomial.QQXs.t list ->
  QQ.t list * Polynomial.QQX.t * Polynomial.QQX.t *
  (Polynomial.QQX.t * QQ.t) list
