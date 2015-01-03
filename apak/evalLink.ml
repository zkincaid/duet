(** Implementation of Tarjan's EVAL-LINK-UPDATE data structure (from
    "Applications of Path Compression on Balanced Trees"). *)

exception Not_in_pc
module Make (Elem : Hashtbl.HashedType) (Val : Sig.Semigroup.S) : sig
  type t
  type node
  val link : t -> Elem.t -> Elem.t -> unit
  val eval : t -> Elem.t -> Val.t
  val add : t -> Elem.t -> Val.t -> unit
  val update : t -> Elem.t -> Val.t -> unit
  val create : int -> t
end = struct
  module HT = Hashtbl.Make(Elem)
  type node = { id : int;
		mutable parent : node option;
		mutable value : Val.t }

  type t = { set_map : node HT.t;
	     mutable size : int }

  let create size = { set_map = HT.create size;
		      size = 0 }

  let eq x y = x.id = y.id

  let rec compress set =
    match set.parent with
      | None -> set
      | Some p ->
	  let root = compress p in
	    if not (eq root p) then begin
	      set.parent <- Some root;
	      set.value <- Val.mul set.value p.value
	    end;
	    root

  let eval_node node =
    ignore(compress node);
    match node.parent with
      | None -> node.value
      | Some p -> Val.mul p.value node.value

  let get ds x =
    try HT.find ds.set_map x
    with Not_found -> raise Not_in_pc

  let eval ds elem = eval_node (get ds elem)

  let add ds elem value =
    HT.add ds.set_map elem { id = ds.size; parent = None; value = value };
    ds.size <- ds.size + 1

  let link ds x y = (get ds y).parent <- Some (get ds x)

  let update ds x v =
    let node = get ds x in
      node.value <- Val.mul node.value v
end
