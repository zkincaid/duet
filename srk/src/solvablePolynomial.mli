(** Solvable polynomial maps.  A polynomial map [f : Q^n -> Q^n] is
   solvable if its circular dependencies are linear (e.g. [f(x,y) =
   (x+1,y+x^2)] is solvable but [f(x,y) = (y^2,x)] is not).  *)

open Syntax
open Iteration

(** Solvable polynomial maps with eigenvalue 1.  Closed forms are
   polynomial. *)
module SolvablePolynomialOne : PreDomainWedgeIter

(** Solvable polynomial maps without spectral assumptions.  Closed
   forms may use operators from Berg's operational calculus,
   represented as uninterpreted function symbols that will be
   allocated upon calling [exp]. *)
module SolvablePolynomial : PreDomainWedgeIter

(** Solvable polynomial maps with periodic rational eigenvalues.
   Closed forms are exponential polynomials. *)
module SolvablePolynomialPeriodicRational : PreDomainWedgeIter

(** Extends [SolvablePolynomialPeriodicRational] with universally
   quantified precondition expressed over terms with
   Presurger-definable dynamics. *)
module PresburgerGuard : PreDomain

(** Deterministic linear transition systems *)
type 'a dlts_abstraction =
  { dlts : Lts.PartialLinearMap.t;
    simulation : ('a arith_term) array }

(** Deterministic linear transition systems *)
module DLTS : sig
  include PreDomainIter with type 'a t = 'a dlts_abstraction

  (** Simplify the simulation function of a DLTS abstraction.  If
     [scale] is set, the resulting simulation is scaled so that the
     simulation matrix is integral.  Warning: this function performs a
     change-of-basis that is incompatible with the expectations of
     DLTS.exp.  *)
  val simplify : 'a context -> ?scale:bool -> 'a t -> 'a t
end

(** Solvable polynomial maps with periodic rational eigenvalues,
   restricted to an algebraic variety, represented as a DLTS with a
   polynomial simulation. *)
module DLTSSolvablePolynomial : PreDomainWedge with type 'a t = 'a dlts_abstraction

module DLTSPeriodicRational : sig
  include PreDomainIter with type 'a t = 'a dlts_abstraction

  (** Find best abstraction as a DLTS with rational (rather than
     periodic rational) spectrum *)
  val abstract_rational : 'a context -> 'a TransitionFormula.t -> 'a t
end

module SolvablePolynomialLIRR : 
  sig
    include PreDomain

    type pre_t

    val make_sp : TransitionIdeal.t -> TransitionIdeal.solvable_polynomial -> pre_t

    val exp_ti : pre_t -> TransitionIdeal.t
  end
