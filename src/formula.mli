open Apak
open ArkPervasives

module type Formula = sig
  type t
  include Putil.Hashed.S with type t := t
  include Putil.OrderedMix with type t := t

  module T : Term.S

  val eval : ('a, T.t atom) formula_algebra -> t -> 'a
  val view : t -> (t, T.t atom) open_formula
  val to_smt : t -> Smt.ast

  val top : t
  val bottom : t

  val conj : t -> t -> t
  val disj : t -> t -> t

  val leqz : T.t -> t
  val eqz : T.t -> t
  val ltz : T.t -> t
  val atom : T.t atom -> t
  val eq : T.t -> T.t -> t
  val leq : T.t -> T.t -> t
  val geq : T.t -> T.t -> t
  val lt : T.t -> T.t -> t
  val gt : T.t -> T.t -> t

  val log_stats : unit -> unit

  val negate : t -> t
  val exists : (T.V.t -> bool) -> t -> t
  val exists_list : T.V.t list -> t -> t 
  val of_smt : Smt.ast -> t
  val implies : t -> t -> bool
  val equiv : t -> t -> bool

  val map : (T.t atom -> t) -> t -> t
  val subst : (T.V.t -> T.t) -> t -> t

  val select_disjunct : (T.V.t -> QQ.t) -> t -> t option

  val big_conj : t BatEnum.t -> t
  val big_disj : t BatEnum.t -> t

  val of_abstract : 'a T.D.t -> t
  val abstract : ?exists:(T.V.t -> bool) option -> 'a Apron.Manager.t -> t -> 'a T.D.t
  val abstract_assign : 'a Apron.Manager.t -> 'a T.D.t -> T.V.t -> T.t -> 'a T.D.t
  val abstract_assume : 'a Apron.Manager.t -> 'a T.D.t -> t -> 'a T.D.t
  val symbolic_bounds : (T.V.t -> bool) -> t -> T.t -> (pred * T.t) list
  val linearize : (unit -> T.V.t) -> t -> t
  val symbolic_abstract : (T.t list) -> t -> (QQ.t option * QQ.t option) list
  val disj_optimize : (T.t list) -> t -> (QQ.t option * QQ.t option) list list

  module Syntax : sig
    val ( && ) : t -> t -> t
    val ( || ) : t -> t -> t
    val ( == ) : T.t -> T.t -> t
    val ( < ) : T.t -> T.t -> t
    val ( > ) : T.t -> T.t -> t
    val ( <= ) : T.t -> T.t -> t
    val ( >= ) : T.t -> T.t -> t
  end
end

module Make (T : Term.S) : Formula with module T = T
module MakeEq (F : Formula) : sig
  module AMap : BatMap.S with type key = F.T.AffineVar.t
  val extract_equalities : F.t -> F.T.V.t list -> F.T.Linterm.t list
end
