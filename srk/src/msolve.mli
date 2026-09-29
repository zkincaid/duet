(** Groebner basis computation using the msolve executable.

    The executable is selected by the [MSOLVE] environment variable and
    defaults to [msolve]. *)

(** Whether the msolve executable can be found.  Checked once, on first use. *)
val available : unit -> bool

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
    representation of the zero-dimensional system [polys]: a square-free
    polynomial [m] and, for each variable in [variables] (in order), a
    polynomial [c_i] with [deg c_i < deg m], such that the solutions of
    [polys] are exactly the points [(c_1(t), ..., c_n(t))] for [t] a root
    of [m]. *)
val parametrization :
  Polynomial.Monomial.dim list ->
  Polynomial.QQXs.t list ->
  Polynomial.QQX.t * (Polynomial.QQX.t list)
