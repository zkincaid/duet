(** Convex polyhedra. *)

open Syntax

(** Convex polyhedra. *)
type t

module V = Linear.QQVector

(** Kinds of polyhedral constraints.  Each polyhedral constraint
    constrains a vector to be either equal to zero, non-negative, or
    positive. *)
type constraint_kind = [ `Zero | `Nonneg | `Pos ]

(** Kinds of polyhedral generators.  Each generator is either a single
    point, a directed ray, or a line (equivalent to two rays in
    opposite directions). *)
type generator_kind = [ `Vertex | `Ray | `Line ]

(** Enumerate the constraints of a polyhedron. *)
val enum_constraints : t -> (constraint_kind * V.t) BatEnum.t

val pp : (Format.formatter -> int -> unit) -> Format.formatter -> t -> unit

(** Intersect two polyhedra. *)
val meet : t -> t -> t

(** Polyhedron representing the whole ambient space. *)
val top : t

(** Empty polyhedron. *)
val bottom : t

(** Convert formula that contains only conjunction and linear equalities and
    disequalities into a polyhedron. *)
val of_formula : ?admit:bool -> 'a CoordinateSystem.t -> 'a formula -> t

val of_constraints : (constraint_kind * V.t) BatEnum.t -> t

(** Inverse of [of_formula] *)
val to_formula : 'a CoordinateSystem.t -> t -> 'a formula

val to_apron : 'a CoordinateSystem.t -> 'a SrkApron.Env.t -> 'abs Apron.Manager.t -> t -> ('a,'abs) SrkApron.property

(** Test whether a point, representing as a map from symbols to rationals, is
    inside a polyhedron. *)
val mem : (int -> QQ.t) -> t -> bool

val implies : t -> (constraint_kind * V.t) -> bool

(** Convert a conjunction of atomic formulas (as returned by
    [Interpretation.select_implicant]) to a polyhedron. *)
val of_implicant : ?admit:bool -> 'a CoordinateSystem.t -> ('a formula) list -> t

(** Convert a polyhedron to a conjunction of atomic formulas (as returned by
    [Interpretation.select_implicant]). *)
val implicant_of : 'a CoordinateSystem.t -> t -> ('a formula) list

(** Model-guided projection of a polyhedron.  Given a point m within a
    polyhedron p and a set of dimension xs, compute a polyhedron q such that
    m|_xs is within q, and q is a subset of p|_xs (using |_xs to denote
    projection of dimensions xs) *)
val local_project : (int -> QQ.t) -> int list -> t -> t

(** Fourier-Motzkin elimination. *)
val project : int list -> t -> t

(** Project using the double-description method *)
val project_dd : int list -> t -> t

(** Apply Fourier-Motzkin elimination to the subset of symbols that appear
    linearly and are "easy" to eliminate.  Symbols that do not appear linearly
    are not projected.  *)
val try_fourier_motzkin : 'a CoordinateSystem.t -> (symbol -> bool) -> t -> t

(** [dual_cone n p] computes a constraint representation for the dual
    cone of the [n]-dimensional polyhedron [p]: the cone of functionals
    on QQ^[n] that are non-negative on every point in [p].  The
    supplied parameter dimension [n] must be >= the greatest dimension
    involved in a constraint in [p].*)
val dual_cone : int -> t -> t

(** [conical_hull n p] takes a natural [n] and a polyhedron [p] in
    QQ^n and computes the smallest cone that contains [p], represented
    as a polyhedron.  All half-spaces making up the conical hull are
    linear (rather than affine) halfspaces. *)
val conical_hull : t -> t

(** [integer_hull p] computes the convex hull of the integer points contained
    in p.
*)
val integer_hull : ?decompose:bool -> [`GomoryChvatal | `Normaliz] -> t -> t

(** Test whether two polyhedra are equal (as sets of points in
    QQ^omega). *)
val equal : t -> t -> bool

(** [constraint_space p] computes a basis for the vector space of
    linear functionals that are bounded (on at least one side) over the
    polyhedron.  For every halfspace [a^T x <= b] that contains [p],
    [a] belongs to this space. *)
val constraint_space : t -> Linear.QQVectorSpace.t

val dd_of : ?man:(Polka.loose Polka.t Apron.Manager.t) -> int -> t -> DD.closed DD.t
val nnc_dd_of : ?man:(Polka.strict Polka.t Apron.Manager.t) -> int -> t -> DD.nnc DD.t
val of_dd : 'a DD.t -> t
