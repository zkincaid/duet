(** Round-robin worklist *)
module MakeRR (S : Set.OrderedType) : sig
  type t
  val empty : t
  val add : S.t -> t -> t
  val singleton : S.t -> t
  val pick : t -> (S.t * t) option
  val fix : (S.t -> t) -> t -> unit
  val cat : t -> t -> t
end = struct
  module Set = Set.Make(S)
  type t = { front : S.t list;
	     back  : S.t list;
	     set   : Set.t }

  let normalize s =
    match s.front with
      | [] -> { s with front = List.rev s.back; back = [] }
      | _  -> s

  let pick s =
    let n = normalize s in
      match n.front with
	| (x::xs) -> Some (x, { n with front = xs; set = Set.remove x n.set })
	| [] -> None

  let empty = { front = []; back = []; set = Set.empty }
  let singleton x = { front = [x]; back = []; set = Set.singleton x }
  let add elt wl =
    if Set.mem elt wl.set then wl
    else { wl with back = elt::wl.back; set = Set.add elt wl.set }

  let cat x y = Set.fold add y.set x

  let rec fix f wl =
    match pick wl with
      | None -> ()
      | Some (elt, wl) -> fix f (cat wl (f elt))
end
