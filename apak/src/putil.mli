(** Apak pervasives *)

module type S =
sig
  type t
  val format : Format.formatter -> t -> unit
  val show : t -> string
  module Show_t : Show.Show with type a = t
end

module type SimpleFormatter = sig
  type a
  val format : Format.formatter -> a -> unit
end
module MakeFmt (S : SimpleFormatter) : sig
  val format : Format.formatter -> S.a -> unit
  val show : S.a -> string
  module Show_t : Show.Show with type a = S.a
end

module type OrderedMix =
sig
  type t
  val compare : t -> t -> int
  module Compare_t : Compare.Compare with type a = t
end

module type Ordered =
sig
  include S
  include OrderedMix with type t := t
end

module Set : sig
  module type S = sig
    include Ordered
    type elt
    val empty : t
    val is_empty : t -> bool
    val singleton : elt -> t
    val mem : elt -> t -> bool
    val add : elt -> t -> t
    val remove : elt -> t -> t
    val union : t -> t -> t
    val inter : t -> t -> t
    val diff : t -> t -> t
    val compare : t -> t -> int
    val equal : t -> t -> bool
    val subset : t -> t -> bool
    val iter : (elt -> unit) -> t -> unit
    val map : (elt -> elt) -> t -> t
    val filter : (elt -> bool) -> t -> t
    val filter_map : (elt -> elt option) -> t -> t
    val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a
    val for_all : (elt -> bool) -> t -> bool
    val exists : (elt -> bool) -> t -> bool
    val partition : (elt -> bool) -> t -> t * t
    val cardinal : t -> int
    val elements : t -> elt list
    val min_elt : t -> elt
    val max_elt : t -> elt
    val choose : t -> elt
    val pop : t -> elt * t
    val enum : t -> elt BatEnum.t
    val of_enum : elt BatEnum.t -> t
  end

  module Make (Ord : Ordered) : S with type elt = Ord.t
end

module Map : sig
  module type S = sig
    type key
    type +'a t
    val empty : 'a t
    val is_empty : 'a t -> bool
    val mem : key -> 'a t -> bool
    val add : key -> 'a -> 'a t -> 'a t
    val singleton : key -> 'a -> 'a t
    val remove : key -> 'a t -> 'a t
    val merge :
      (key -> 'a option -> 'b option -> 'c option) ->
      'a t -> 'b t -> 'c t
    val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int
    val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
    val iter : (key -> 'a -> unit) -> 'a t -> unit
    val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
    val for_all : (key -> 'a -> bool) -> 'a t -> bool
    val exists : (key -> 'a -> bool) -> 'a t -> bool
    val filter : (key -> 'a -> bool) -> 'a t -> 'a t
    val partition : (key -> 'a -> bool) -> 'a t -> 'a t * 'a t
    val cardinal : 'a t -> int
    val bindings : 'a t -> (key * 'a) list
    val min_binding : 'a t -> key * 'a
    val max_binding : 'a t -> key * 'a
    val choose : 'a t -> key * 'a
    val find : key -> 'a t -> 'a
    val map : ('a -> 'b) -> 'a t -> 'b t
    val mapi : (key -> 'a -> 'b) -> 'a t -> 'b t
    val filter_map : (key -> 'a -> 'b option) -> 'a t -> 'b t
    val keys : 'a t -> key BatEnum.t
    val values : 'a t -> 'a BatEnum.t
    val enum : 'a t -> (key * 'a) BatEnum.t
    val of_enum : (key * 'a) BatEnum.t -> 'a t
    val format :
      (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit
  end
  module Make (Key : Ordered) : S with type key = Key.t
end

(** Monomorphic maps *)
module MonoMap : sig
  module type PP = S (* save pretty printing sig *)
  module type S = sig
    include PP
    type key
    type value
    val empty : t
    val is_empty : t -> bool
    val cardinal : t -> int
    val add : key -> value -> t -> t
    val find : key -> t -> value
    val remove : key -> t -> t
    val modify : key -> (value -> value) -> t -> t
    val modify_def : value -> key -> (value -> value) -> t -> t
    val extract : key -> t -> value * t
    val pop : t -> (key * value) * t
    val mem : key -> t -> bool
    val iter : (key -> value -> unit) -> t -> unit
    val map : (value -> value) -> t -> t
    val mapi : (key -> value -> value) -> t -> t
    val fold : (key -> value -> 'a -> 'a) -> t -> 'a -> 'a
    val filterv : (value -> bool) -> t -> t
    val filter : (key -> value -> bool) -> t -> t
    val filter_map : (key -> value -> value option) -> t -> t
    val compare : (value -> value -> int) -> t -> t -> int
    val equal : (value -> value -> bool) -> t -> t -> bool
    val keys : t -> key BatEnum.t
    val values : t -> value BatEnum.t
    val min_binding : t -> key * value
    val max_binding : t -> key * value
    val choose : t -> key * value
    val split : key -> t -> t * value option * t
    val partition : (key -> value -> bool) -> t -> t * t
    val singleton : key -> value -> t
    val bindings : t -> (key * value) list
    val enum : t -> (key * value) BatEnum.t
    val backwards : t -> (key * value) BatEnum.t
    val of_enum : (key * value) BatEnum.t -> t
    val for_all : (key -> value -> bool) -> t -> bool
    val exists : (key -> value -> bool) -> t -> bool
    val merge : (key -> value option -> value option -> value option) ->
      t -> t -> t
  end

  module Make (Key : Ordered) (Val : PP) : S with
					       type key = Key.t
					     and type value = Val.t

  module Ordered : sig
    module type S = sig
      include S
      include OrderedMix with type t := t
    end
    module Make (Key : Ordered) (Val : Ordered) : S with
						      type key = Key.t
						    and type value = Val.t
  end
end

(** Total function spaces where all but finitely many elements map to the same
    "default" value. *)
module TotalFunction : sig
  module type S = sig
    include S
    type dom
    type cod
    val eval : t -> dom -> cod
    val map : (cod -> cod) -> t -> t
    val update : dom -> cod -> t -> t
    val enum : t -> (dom * cod) BatEnum.t
    val support : t -> dom BatEnum.t
    val merge : (cod -> cod -> cod) -> t -> t -> t
    val default : t -> cod
    val const : cod -> t
    val equal : t -> t -> bool
  end
  module LiftMap
    (M : Map.S)
    (Codomain : sig
      type t
      val format : Format.formatter -> t -> unit
      val equal : t -> t -> bool
    end) :
    S with type dom = M.key
      and type cod = Codomain.t

  module Ordered : sig
    module type S = sig
      include S
      include OrderedMix with type t := t
    end
    module LiftMap (M : Map.S) (Codomain : Ordered) :
      S with type dom = M.key
	and type cod = Codomain.t
  end
end

(* Hashed types ***************************************************************)
module Hashed : sig
  val list : ('a -> int) -> 'a list -> int
  module type S = sig
    include S
    val hash : t -> int
    val equal : t -> t -> bool
  end

  module type Mix = sig
    type t
    val hash : t -> int
    val equal : t -> t -> bool
  end

  module type Ordered = sig
    include Ordered
    val hash : t -> int
    val equal : t -> t -> bool
  end

  module Set : sig
    module type S = sig
      include Set.S
      val hash : t -> int
      val equal : t -> t -> bool
    end
    module Make (M : Ordered) : sig
      include Set.S with type elt = M.t
      val hash : t -> int
      val equal : t -> t -> bool
    end
  end
end

module type CoreTypeBasis = sig
  include Ordered
  val equal : t -> t -> bool
  val hash : t -> int
end
module type CoreType = sig
  include CoreTypeBasis
  module HT : BatHashtbl.S with type key = t
  module Map : Map.S with type key = t
  module Set : Hashed.Set.S with type elt = t
end
module MakeCoreType : functor (T : CoreTypeBasis) -> CoreType with type t = T.t

module PString : CoreType with type t = string
module PInt : CoreType with type t = int
module PChar : CoreType with type t = char
module PUnit : CoreType with type t = unit

val format_enum : (Format.formatter -> 'a -> unit) -> ?left:string -> ?sep:string -> ?right:string -> Format.formatter -> 'a BatEnum.t -> unit
val format_list : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a list -> unit
val pp_string : (Format.formatter -> 'a -> unit) -> 'a -> string

val set_load_path : string -> unit
val set_temp_dir : string -> unit

(** Search for a file named {!file} in all the directories in the load
    path.  Raise File_not_found if no such file exists. *)
val find_file : string -> string option
val with_temp_filename : string -> string -> (string -> 'a) -> 'a
val with_temp_file : string -> string -> (string -> out_channel -> 'a) -> 'a
val with_temp_dir : string -> (string -> 'a) -> 'a

val adjacent_pairs : 'a BatEnum.t -> ('a * 'a) BatEnum.t
val cartesian_product : 'a BatEnum.t -> 'b BatEnum.t -> ('a * 'b) BatEnum.t

val compare_tuple : int Lazy.t list -> int
