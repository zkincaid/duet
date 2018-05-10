(** A coordinate system is a bijection between a set of coordinates and a set
    of terms.  *)

open Syntax

(** Coordinate system *)
type 'a t

(** A cs_term is a term associated with a coordinate, which is defined in
    terms of lower coordinates.  *)
type cs_term = [ `Mul of Linear.QQVector.t * Linear.QQVector.t
               | `Inv of Linear.QQVector.t
               | `Mod of Linear.QQVector.t * Linear.QQVector.t
               | `Floor of Linear.QQVector.t
               | `App of symbol * (Linear.QQVector.t list) ]

val pp : Format.formatter -> 'a t -> unit

val pp_vector : 'a t -> Format.formatter -> Linear.QQVector.t -> unit

val pp_cs_term : 'a t -> Format.formatter -> cs_term -> unit

val mk_empty : 'a context -> 'a t

val get_context : 'a t -> 'a context

val copy : 'a t -> 'a t

(** Extend a coordinate system to admit a term *)
val admit_term : 'a t -> 'a term -> unit

(** Extend a coordinate system with one additional coordinate term, if that
    coordinate does not already belong to the system. *)
val admit_cs_term : 'a t -> cs_term -> unit

(** Virtual coordinate associated with 1 *)
val const_id : int

(** Number of dimensions in the coordinate system *)
val dim : 'a t -> int

(** Number of integer dimensions in the coordinate system *)
val int_dim : 'a t -> int

(** Number of real dimensions in the coordinate system *)
val real_dim : 'a t -> int

val destruct_coordinate : 'a t -> int -> cs_term

(** Find the term associated with a coordinate *)
val term_of_coordinate : 'a t -> int -> 'a term

val term_of_vec : 'a t -> Linear.QQVector.t -> 'a term

(** Find the coordinate associated with an coordinate term.  If the coordinate
    term is does not belong to the coorindate system and [admit] is set then
    extend the coordinate system; otherwise, raise [Not_found]. *)
val cs_term_id : ?admit:bool -> 'a t -> cs_term -> int

(** Find the vector associated with an admissible term.  If the term is
    inadmissible and [admit] is set then extend the coordinate system; otherwise,
    raise [Not_found]. *)
val vec_of_term : ?admit:bool -> 'a t -> 'a term -> Linear.QQVector.t

val type_of_id : 'a t -> int -> [ `TyInt | `TyReal ]

val type_of_vec : 'a t -> Linear.QQVector.t -> [ `TyInt | `TyReal ]

val type_of_monomial : 'a t -> Polynomial.Monomial.t -> [ `TyInt | `TyReal ]

val type_of_polynomial : 'a t -> Polynomial.Mvp.t -> [ `TyInt | `TyReal ]

(** Find a polynomial associated with an admissible term over
    {i non-multiplicative} coordinates. *)
val polynomial_of_term : 'a t -> 'a term -> Polynomial.Mvp.t

(** Convert a vector to a polynomial {i without multiplicative coordinates}.
    Multiplicative coordinates are expanded into higher-degree polynomials
    over non-multiplicative coordinates. *)
val polynomial_of_vec : 'a t -> Linear.QQVector.t -> Polynomial.Mvp.t

val polynomial_of_coordinate : 'a t -> int -> Polynomial.Mvp.t

val term_of_polynomial : 'a t -> Polynomial.Mvp.t -> 'a term

(** Does a coordinate system admit the given term? *)
val admits : 'a t -> 'a term -> bool

val project_ideal : 'a t ->
  Polynomial.Mvp.t list ->
  ?subterm:(symbol -> bool) ->
  (symbol -> bool) ->
  (int * 'a term * 'a formula) list

(** Find the set of all coordinates that are associated with subterms of the
    term associated with a given coordinate. *)
val subcoordinates : 'a t -> int -> SrkUtil.Int.Set.t

(** Find the set of all coordinates that are associated with *direct* subterms
    of the term associated with a given coordinate. *)
val direct_subcoordinates : 'a t -> int -> SrkUtil.Int.Set.t
