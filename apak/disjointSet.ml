(** Implementation of disjoint set data structure *)

module Make (M : Hashtbl.HashedType) (*: sig
  type t
  type set
  val union : set -> set -> unit
  val find : t -> M.t -> set
  val create : int -> t
  val copy : t -> t
  val eq : set -> set -> bool
  val same_set : t -> M.t -> M.t -> bool
  val reverse_map : t -> 'a -> (M.t -> 'a -> 'a) -> M.t -> 'a
end*) = struct
  module HT = Hashtbl.Make(M);;

  type set = { id : int;
	       mutable parent : set option;
	       mutable rank : int }

  type t = { set_map : set HT.t;
	     mutable size : int }

  let create size = { set_map = HT.create size;
                      size = 0 }

  let copy ds = { set_map = HT.copy ds.set_map; 
                  size = ds.size}

  (* find + path compression *)
  let rec find_impl set =
    match set.parent with
      | None -> set
      | Some p ->
	  let root = find_impl p in
	    set.parent <- Some root;
	    root

  let find ds elem = 
    let set =
      try HT.find ds.set_map elem
      with Not_found -> begin
	let s = { id = ds.size; parent = None; rank = 0} in
	  (* add elem to the disjoint set data structure *)
	  HT.add ds.set_map elem s;
	  ds.size <- ds.size + 1;
	  s
      end
    in
      find_impl set

  let eq x y = x.id = y.id

  let union x y =
    let x_root = find_impl x in
    let y_root = find_impl y in
      if x_root.rank > y_root.rank then y_root.parent <- Some x_root
      else if x_root.rank < y_root.rank then x_root.parent <- Some y_root
      else if not (eq x_root y_root) then begin
	y_root.parent <- Some x_root;
	x_root.rank <- x_root.rank + 1
      end;
      find_impl x

  let same_set ds x y = eq (find ds x) (find ds y)

  module SetMap = Map.Make(struct
			     type t = set
			     let compare x y = Pervasives.compare x.id y.id
			   end)
  let reverse_map ds empty add =
    let map_add rep m map =
      let old =
	try SetMap.find rep map
	with Not_found -> empty
      in
	SetMap.add rep (add m old) map
    in
    let map =
      HT.fold (fun m set -> map_add (find_impl set) m) ds.set_map SetMap.empty
    in
      (fun m -> SetMap.find (find_impl (HT.find ds.set_map m)) map)

  let clear ds =
    HT.clear ds.set_map;
    ds.size <- 0;
end
