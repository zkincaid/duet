open Apron
open Syntax

type dim = int
type texpr = Texpr0.t
type lexpr = Linexpr0.t
type tcons = Tcons0.t
type lcons = Lincons0.t
type scalar = Scalar.t
type coeff = Coeff.t

val qq_of_scalar : scalar -> QQ.t
val qq_of_coeff : coeff -> QQ.t option
val coeff_of_qq : QQ.t -> coeff

module Env : sig
  type 'a t
  val pp : Format.formatter -> 'a t -> unit
  val empty : 'a context -> 'a t
  val of_set : 'a context -> Symbol.Set.t -> 'a t
  val of_enum : 'a context -> symbol BatEnum.t -> 'a t
  val of_list : 'a context -> symbol list -> 'a t
  val vars : 'a t -> symbol BatEnum.t
  val dimensions : 'a t -> int BatEnum.t
  val mem : symbol -> 'a t -> bool
  val int_dim : 'a t -> int
  val real_dim : 'a t -> int
  val dimension : 'a t -> int
  val var_of_dim : 'a t -> int -> symbol
  val dim_of_var : 'a t -> symbol -> int
  val filter : (symbol -> bool) -> 'a t -> 'a t
end

type ('a,'abs) property
val pp : Format.formatter -> ('a,'abs) property -> unit
val show : ('a,'abs) property -> string

val get_manager : ('a, 'abs) property -> 'abs Manager.t

val is_bottom : ('a,'abs) property -> bool
val is_top : ('a,'abs) property -> bool

val top : 'abs Manager.t -> 'a Env.t -> ('a,'abs) property
val bottom : 'abs Manager.t -> 'a Env.t -> ('a,'abs) property
val meet_tcons : ('a,'abs) property -> tcons list -> ('a,'abs) property
val meet_lcons : ('a,'abs) property -> lcons list -> ('a,'abs) property

val leq : ('a,'abs) property -> ('a,'abs) property -> bool
val equal : ('a,'abs) property -> ('a,'abs) property -> bool

val join : ('a,'abs) property -> ('a,'abs) property -> ('a,'abs) property
val meet : ('a,'abs) property -> ('a,'abs) property -> ('a,'abs) property
val widen : ('a,'abs) property -> ('a,'abs) property -> ('a,'abs) property

val exists : 'abs Manager.t -> (symbol -> bool) -> ('a,'abs) property -> ('a,'abs) property
val add_vars : symbol BatEnum.t -> ('a,'abs) property -> ('a,'abs) property
val boxify : ('a,'abs) property -> ('a,'abs) property
val rename : (symbol -> symbol) -> ('a,'abs) property -> ('a,'abs) property

val lexpr_of_vec : 'a Env.t -> Linear.QQVector.t -> lexpr
val vec_of_lexpr : 'a Env.t -> lexpr -> Linear.QQVector.t
val texpr_of_term : 'a Env.t -> 'a term -> texpr
val term_of_texpr : 'a Env.t -> texpr -> 'a term

val tcons_geqz : texpr -> tcons
val tcons_eqz : texpr -> tcons
val tcons_gtz : texpr -> tcons

val lcons_geqz : lexpr -> lcons
val lcons_eqz : lexpr -> lcons
val lcons_gtz : lexpr -> lcons

val formula_of_property : ('a,'abs) property -> 'a formula

(** Evaluate an expression in the environment Top. *)
val eval_texpr : texpr -> Apron.Interval.t
