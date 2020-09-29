(** Function memoization *)

(** Memoize a function using built-in polymorphic hash. *)
val memo : ?size:int -> ('a -> 'b) -> ('a -> 'b)

(** Memoize a recursive function using built-in polymorphic hash. *)
val memo_recursive : ?size:int -> (('a -> 'b) -> 'a -> 'b) -> ('a -> 'b)

(** Memoize a function using an LRU cache with *)
val lru_memo : ?params:Cache.cache_params -> ?size:int -> ('a -> 'b) -> ('a -> 'b)

(** Memoize a recursive function using an LRU cache *)
val lru_memo_recursive : ?params:Cache.cache_params -> ?size:int -> (('a -> 'b) -> 'a -> 'b) -> ('a -> 'b)

(** Functorized memoization with user-defined hash function. *)
module Make (M : Hashtbl.HashedType) : sig
  val memo : ?size:int -> (M.t -> 'a) -> (M.t -> 'a)
  val memo_recursive: ?size:int -> ((M.t -> 'a) -> M.t -> 'a) -> (M.t -> 'a)
end

(** Functorized memoization with user-defiend hash function using weak keys.
    The weak hashtble is implemented using Emphemeron.K1
    Keys may be reclaimed by the GC when no other references to the key exists
    values are kept alive if thier key is alive (even if no other references exist

    NOTE: This module should NOT be used with non-heap allocated types
    this may lead to a memory leak as keys will not be reclaimed by GC *)
module MakeWeak(M : Hashtbl.HashedType) : sig
  val memo : ?size:int -> (M.t -> 'a) -> (M.t -> 'a)
  val memo_recursive: ?size:int -> ((M.t -> 'a) -> M.t -> 'a) -> (M.t -> 'a)
end

(** Functorized memoization using a given cache *)
module MakeCache(C : Cache.S) : sig
  val memo : ?params:Cache.cache_params -> ?size:int -> ('a -> 'b) -> ('a -> 'b)
  val memo_recursive: ?params:Cache.cache_params -> ?size:int -> (('a -> 'b) -> 'a -> 'b) -> ('a -> 'b)
end

(** Functorized memoization using a given cache with specific hash function *)
module MakeCacheHF(C : Cache.HashS) : sig
  val memo : ?params:Cache.cache_params -> ?size:int -> (C.key -> 'a) -> (C.key -> 'a)
  val memo_recursive: ?params:Cache.cache_params -> ?size:int -> ((C.key -> 'a) -> C.key -> 'a) -> (C.key -> 'a)
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
