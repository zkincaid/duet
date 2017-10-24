(** Function memoization *)

(** Memoize a function using built-in polymorphic hash. *)
val memo : ?size:int -> ('a -> 'b) -> ('a -> 'b)

(** Memoize a recursive function using built-in polymorphic hash. *)
val memo_recursive : ?size:int -> (('a -> 'b) -> 'a -> 'b) -> ('a -> 'b)

(** Functorized memoization with user-defined hash function. *)
module Make (M : Hashtbl.HashedType) : sig
  val memo : ?size:int -> (M.t -> 'a) -> (M.t -> 'a)
  val memo_recursive: ?size:int -> ((M.t -> 'a) -> M.t -> 'a) -> (M.t -> 'a)
end

module Tabulate : sig

  module type Fun = sig
    type dom
    type cod

    (** Function to be tabulated *)
    val f : dom -> (cod -> unit) -> unit
    val hash : dom -> int
    val join : cod -> cod -> cod
    val bottom : cod
    val dom_equal : dom -> dom -> bool
    val cod_equal : cod -> cod -> bool
  end

  module type RecFun = sig
    type dom
    type cod

    (** Function to be tabulated *)
    val f : (dom -> (cod -> unit) -> unit) -> dom -> (cod -> unit) -> unit
    val hash : dom -> int
    val join : cod -> cod -> cod
    val bottom : cod
    val dom_equal : dom -> dom -> bool
    val cod_equal : cod -> cod -> bool
  end

  module type S = sig
    type dom
    type cod
    val update : dom -> cod -> unit
    val call : dom -> (cod -> unit) -> unit
    val call_direct : dom -> cod
  end

  module Make (F : Fun) : S with type dom = F.dom
                             and type cod = F.cod

  module MakeRec (F : RecFun) : S with type dom = F.dom
                                   and type cod = F.cod
end
