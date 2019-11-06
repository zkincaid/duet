(** Solvable polynomial maps.  A polynomial map [f : Q^n -> Q^n] is
   solvable if its circular dependencies are linear (e.g. [f(x,y) =
   (x+1,y+x^2)] is solvable but [f(x,y) = (y^2,x)] is not).  *)

open Syntax
open Iteration

(** Solvable polynomial maps with eigenvalue 1.  Closed forms are
   polynomial. *)
module SolvablePolynomialOne : PreDomainWedge

(** Solvable polynomial maps without spectral assumptions.  Closed
   forms may use operators from Berg's operational calculus,
   represented as uninterpreted function symbols that will be
   allocated upon calling [exp]. *)
module SolvablePolynomial : PreDomainWedge

(** Solvable polynomial maps with periodic rational eigenvalues.
   Closed forms are exponential polynomials. *)
module SolvablePolynomialPeriodicRational : PreDomainWedge

(** Extends [SolvablePolynomialPeriodicRational] with universally
   quantified precondition expressed over terms with
   Presurger-definable dynamics. *)
module PresburgerGuard : PreDomain

(** Deterministic linear transition systems *)
module DLTS : PreDomain
