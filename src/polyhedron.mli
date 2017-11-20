open Syntax

type t

module V = Linear.QQVector

val enum : t -> [ `EqZero of V.t | `LeqZero of V.t ] BatEnum.t
val pp : Format.formatter -> t -> unit

val conjoin : t -> t -> t
val top : t

(** Convert formula that contains only conjunction and linear equalities and
    disequalities into a polyhedron. *)
val of_formula : 'a context -> 'a formula -> t

(** Inverse of [of_formula] *)
val to_formula : 'a context -> t -> 'a formula

val to_apron : 'a SrkApron.Env.t -> 'abs Apron.Manager.t -> t -> ('a,'abs) SrkApron.property

(** Test whether a point, representing as a map from symbols to rationals, is
    inside a polyhedron. *)
val mem : (symbol -> QQ.t) -> t -> bool

(** Convert a conjunction of linear formulas (as returned by
    [Interpretation.select_implicant] on a linear formula) to a polyhedron. *)
val polyhedron_of_implicant : 'a context -> ('a formula) list -> t

(** Model-guided projection of a polyhedron.  Given a point m within a
    polyhedron p and a set of dimension xs, compute a polyhedron q such that
    m|_xs is within q, and q is a subset of p|_xs (using |_xs to denote
    projection of dimensions xs) *)
val local_project : (symbol -> QQ.t) -> Symbol.Set.t -> t -> t
