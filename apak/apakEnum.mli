val pp_print_enum : ?pp_sep:(Format.formatter -> unit -> unit) ->
  (Format.formatter -> 'a -> unit) ->
  Format.formatter ->
  'a BatEnum.t ->
  unit
val adjacent_pairs : 'a BatEnum.t -> ('a * 'a) BatEnum.t
val cartesian_product : 'a BatEnum.t -> 'b BatEnum.t -> ('a * 'b) BatEnum.t
val tuples : ('a BatEnum.t) list -> ('a list) BatEnum.t
val distinct_pairs : 'a BatEnum.t -> ('a * 'a) BatEnum.t
