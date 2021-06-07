open Polynomial


type t 

(* val pp :(Format.formatter -> int -> unit) -> Format.formatter -> t -> unit *)

val intersection : t -> t -> t

(* int refers to dimensions 
   already implemented polyhedron of a cone (wrt to the monomials as dimensions), 
   project out the dimensions that correspond to 
   monomials with variables we don't want, and take the generators of the 
   resulting cone is the projection.
 *)
val project : t -> (int -> bool) -> t

val get_ideal : t -> Ideal.t 

val get_cone_generators : t -> (QQXs.t BatList.t) 

val change_monomial_ordering: t -> 
  (Monomial.t -> Monomial.t -> [ `Eq | `Lt | `Gt  ]) -> t

(* Ideal contains the necessary monomial ordering *)
(* Could generalize Ideal interface, when having binary operators of ideals 
   make sure they have the same monomial operation
   Also need to be able to change monomial ordering of an ideal. 
 *)
val make : Ideal.t -> QQXs.t BatList.t -> t

val add_polynomial_to_ideal : t -> QQXs.t -> t

val add_polynomial_to_cone : t -> QQXs.t -> t

(* This does not belong here in this interface *)
(* val mk_nonnegative_cone_of_tf : ('a TransitionFormula.t -> t) *)

val mem : QQXs.t -> t -> bool

(* Does -1 belong to this cone? If yes then all polynomials belong to the cone. *)
val is_proper: t -> bool 

(* ideals must be the same, rewrite to the same monomial ordering and test 
   if cone are the same
   or use the membership testing on the generators 
 *)
val equal: t -> t -> bool

(* To get a fresh symbol for elimination https://github.com/zkincaid/duet/blob/modern/srk/src/polynomial.ml#L989 *)
(* Consider using the dual space, polyhedron.ml to do the Farkas lemma stuff *)

(* another module that takes in CoordinateSystem and compute polynomial cones for formulas *)
(* To implement the weak theory, using an SMT solver, replace mult by uninterpreted function symbol and call the solver,
   if UNSAT then done, otherwise get a model (implicant), which we use to construct a polynomial cone and check if proper. 
 *)  

