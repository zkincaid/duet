(*pp deriving *)

(* Copyright Jeremy Yallop 2007.
   This file is free software, distributed under the MIT license.
   See the file COPYING for details.
*)

module type Compare =
sig
  type a
  val compare : a -> a -> int
end

module Defaults (E : Compare) = E

module Compare_immutable(S : sig type a end) :
  Compare with type a = S.a =
struct
  type a = S.a
  let compare = compare
end

module Compare_mutable(S : sig type a end) :
  Compare with type a = S.a =
struct
  type a = S.a
  let compare = compare
end

module Compare_int = Compare_immutable(struct type a = int end)
module Compare_bool = Compare_immutable(struct type a = bool end)
module Compare_float = Compare_immutable(struct type a = float end)
module Compare_unit = Compare_immutable(struct type a = unit end)
module Compare_char = Compare_immutable(struct type a = char end)

module Compare_string = Compare_mutable(struct type a = string end)
module Compare_ref (E : Compare) = Compare_mutable(struct type a = E.a ref end)
module Compare_array (E : Compare) = Compare_mutable(struct type a = E.a array end)

module Compare_option (E : Compare) 
  : Compare with type a = E.a option =
struct 
  type a = E.a option
  let compare l r = match l, r with
    | Some l, Some r -> E.compare l r
    | None, None -> 0
    | Some _, _ -> 1
    | _, Some _ -> -1
end

module Compare_map_s_t (E : Compare) (M : Map.S)
  : Compare with type a = E.a M.t =
struct
  type a = E.a M.t
  let compare = M.compare (E.compare)
end  

module Compare_list (E : Compare) :
  Compare with type a = E.a list =
struct
  type a = E.a list
  let rec compare l r = match l, r with
    | [], [] -> 0
    | (lfst::lrst), (rfst::rrst) ->
	let cmp = E.compare lfst rfst in
	  if cmp != 0 then cmp else compare lrst rrst
    | (_, []) -> 1
    | ([], _) -> -1
end

(*
module Compare_num
  : Compare with type a = Num.num =
struct
  type a = Num.num
  let eq = Num.eq_num
end
*)
