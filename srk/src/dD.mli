(** Double-description method polyhedra. *)

open Apron
module V = Linear.QQVector

type constraint_kind = [`Zero | `Nonneg | `Pos]
type generator_kind = [`Vertex | `Ray | `Line]

(** Topologically closed polyhedra *)
type closed = Polka.loose Polka.t

(** Not-necessarily closed polyhedra *)
type nnc = Polka.strict Polka.t

(** Double-description method polyhedra.  Type parameter is either [closed] or
   [nnc]. *)
type 'a t = 'a Abstract0.t

(** Pretty print *)
val pp : (Format.formatter -> int -> unit) -> Format.formatter -> 'a t -> unit


(** Compute double-description polyhedron from its generators. *)
val of_generators : ?man:(closed Apron.Manager.t) ->
  int ->
  (generator_kind * V.t) BatEnum.t ->
  closed t

(** Compute double-description polyhedron from its constraints.  Strict
   constraints are silently converted to non-strict constraints. *)
val of_constraints_closed : ?man:(closed Apron.Manager.t) ->
  int ->
  (constraint_kind * V.t) BatEnum.t ->
  closed t
val of_constraints : ?man:(nnc Apron.Manager.t) ->
  int ->
  (constraint_kind * V.t) BatEnum.t -> nnc t

(** Enumerate the generators of a polyhedron. *)
val enum_generators : 'a t -> (generator_kind * V.t) BatEnum.t

(** Enumerate the constraints of a polyhedron. *)
val enum_constraints : 'a t -> (constraint_kind * V.t) BatEnum.t

(** Enumerate the constraints of a closed polyhedron. *)
val enum_constraints_closed : closed t -> ([`Zero | `Nonneg] * V.t) BatEnum.t

(** Convex hull of the union of two polyhedra. *)
val join : 'a t -> 'a t -> 'a t

(** Intersect two polyhedra. *)
val meet : 'a t -> 'a t -> 'a t

(** Test whether two polyhedra have exactly the same points *)
val equal : 'a t -> 'a t -> bool

(** Test whether a constraint is satisfied by all points in a polyhedron. *)
val implies : 'a t -> (constraint_kind * V.t) -> bool

(** Find polyhedron consisting of all points in a polyhedron that satisfy all
   given constraints.  *)
val meet_constraints : 'a t -> (constraint_kind * V.t) list -> 'a t

(** Project the given dimensions *out* of a polyhedron; the resulting
   polyhedron has the same dimension as the original, but the dimensions that
   have been projected out are unconstrainted. *)
val project : int list -> 'a t -> 'a t

(** Convert Apron linear constraint to DD constraint *)
val constraint_of_lcons : Lincons0.t -> constraint_kind * V.t

(** Convert DD constraint to Apron  linear constraint *)
val lcons_of_constraint : constraint_kind * V.t -> Lincons0.t

(** Convert vector to Apron linear expression. *)
val vec_of_lexpr : Linexpr0.t -> V.t

(** Convert Apron linear expression to constraint *)
val lexpr_of_vec : V.t -> Linexpr0.t

(** [minimal_faces p] returns the minimal faces of [p], where each minimal
   face is given by a point that it contains and the list of constraints
   active at that point (and all points on the minimal face).  *)
val minimal_faces : 'a t -> (V.t * ((constraint_kind * V.t) list)) list
