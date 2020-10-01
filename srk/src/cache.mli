type cache_params = {
  max_size : int;
  (* used for auto resizing cache when new items are added to reduce cache misses
     The hard_limit >= max_size (or is 0 for unbounded size) limits unbounded growth of the cache
     Each time the cache would need to grow / evict, we look to see if we should resize the cache
     We compute the number of keys that are hit at least min_hits times with a specific aging factor.
     One epoch/age is the time between consecutive ages.
     num_hits = hits_age_n + hits_ane_{n-1} * aging_factor + ... + hits_age_0 * aging_factor^n *)
  hard_limit : int;
  keys_hit_rate : float;
  min_hits : float;
  aging_factor : float; (* must be between 0 and 1 *)
}

module type S = sig
  type ('a, 'b) t
  val create : ?random:bool -> ?params:cache_params -> int -> ('a, 'b) t
  val get_params : ('a, 'b) t -> cache_params
  val set_params : ('a, 'b) t -> cache_params -> unit
  val clear : ('a, 'b) t -> unit
  val reset : ('a, 'b) t -> unit
  val copy : ('a, 'b) t -> ('a, 'b) t
  val add : ('a, 'b) t -> 'a -> 'b -> unit
  val find : ('a, 'b) t -> 'a -> 'b
  val find_opt : ('a, 'b) t -> 'a -> 'b option
  val mem : ('a, 'b) t -> 'a -> bool
  val remove : ('a, 'b) t -> 'a -> unit
  val iter : ('a -> 'b -> unit) -> ('a, 'b) t -> unit
  val filter_map_inplace : ('a -> 'b -> 'b option) -> ('a, 'b) t -> unit
  val fold : ('a -> 'b -> 'c -> 'c) -> ('a, 'b) t -> 'c -> 'c
  val length : ('a, 'b) t -> int
end

module type HashS = sig
  type key
  type 'a t
  val create : ?params:cache_params -> int -> 'a t
  val get_params : 'a t -> cache_params
  val set_params : 'a t -> cache_params -> unit
  val clear : 'a t -> unit
  val reset : 'a t -> unit
  val copy : 'a t -> 'a t
  val add : 'a t -> key -> 'a -> unit
  val find : 'a t -> key -> 'a
  val find_opt : 'a t -> key -> 'a option
  val mem : 'a t -> key -> bool
  val remove : 'a t -> key -> unit
  val iter : (key -> 'a -> unit) -> 'a t -> unit
  val filter_map_inplace : (key -> 'a -> 'a option) -> 'a t -> unit
  val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
  val length : 'a t -> int
end

module LRU : sig
  include S
  module Make(K : Hashtbl.HashedType) : HashS with type key = K.t
end
