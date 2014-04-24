(** Arithmetic terms *)

open Apak
open ArkPervasives

module type Var = sig
  include Linear.Var
  module Map : Putil.Map.S with type key = t
  val of_smt : Smt.symbol -> t
  val typ : t -> typ
  val hash : t -> int
  val equal : t -> t -> bool
end

module type S = sig
  type t
  include Putil.Hashed.S with type t := t
  include Putil.OrderedMix with type t := t

  module V : Var
  module D : NumDomain.S with type var = V.t
  module Linterm : Linear.Affine.S with type var = V.t
				   and type base = QQ.t
  module Set : Putil.Set.S with type elt = t

  (** {2 Term constructors} *)
  val var : V.t -> t
  val const : QQ.t -> t
  val int : ZZ.t -> t
  val mul : t -> t -> t
  val add : t -> t -> t
  val sub : t -> t -> t
  val div : t -> t -> t
  val neg : t -> t
  val floor : t -> t
  val zero : t
  val one : t

  val sum : t BatEnum.t -> t

  (** Multiplicative inverse *)
  val inverse : t -> t

  (** Integer division *)
  val idiv : t -> t -> t
  val qq_linterm : (t * QQ.t) BatEnum.t -> t

  (** Exponentiation by a constant *)
  val exp : t -> int -> t

  (** {2 Term deconstructors} *)
  (** [eval] is a fold for terms.  More precisely, terms are initial objects
      in the category of term-algebras, and [eval alg] gives the (unique)
      morphism from the initial algebra to [alg]. *)
  val eval : ('a,V.t) term_algebra -> t -> 'a

  (** Determine the type of a term.  This is a conservative estimate: some
      terms, for example (n+n+1)/2, only take integral values but are
      conservatively typed as real. *)
  val typ : t -> typ

  (** Determine a term equivalent to a constant (and if so, which). *)
  val to_const : t -> QQ.t option

  (** Determine a term equivalent to a variable (and if so, which). *)
  val to_var : t -> V.t option

  (** {2 Misc operations} *)
  val to_smt : t -> Smt.ast

  (** Apply a substitution *)
  val subst : (V.t -> t) -> t -> t

  (** Given an environment [env] and a term [t], evaluate [t], using [env] to
      interpret variables.   May raise [Ark.Divide_by_zero]. *)
  val evaluate : (V.t -> QQ.t) -> t -> QQ.t

  val is_linear : t -> bool
  val split_linear : t -> t * ((t * QQ.t) list)

  val of_smt : (int -> V.t) -> ?var_smt:(Smt.symbol -> t) -> Smt.ast -> t
  val to_apron : D.env -> t -> NumDomain.term
  val of_apron : D.env -> NumDomain.term -> t
  val to_linterm : t -> Linterm.t option
  val of_linterm : Linterm.t -> t

  val log_stats : unit -> unit

  module Syntax : sig
    val ( + ) : t -> t -> t
    val ( - ) : t -> t -> t
    val ( * ) : t -> t -> t
    val ( / ) : t -> t -> t
    val ( ~$ ) : V.t -> t
    val ( ~@ ) : QQ.t -> t
  end
end

module Make (V : Var) : S with module V = V
