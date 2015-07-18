(** Maintains a bidirectional mapping from an n-element list to \{1,
    ..., n\} *)

module DynArray = BatDynArray

(* From Deriving.Show.Show_array *)
let pp_dynarray pp formatter items =
  let write_items formatter items =
    let length = DynArray.length items in
    for i = 0 to length - 2 do
      Format.fprintf formatter "@[%d -> %a;@;@]"
        i
        pp (DynArray.get items i)
    done;
    if length <> 0
    then pp formatter (DynArray.get items (length - 1))
  in
  Format.fprintf formatter "@[[|%a|]@]" write_items items

exception Not_in_enumeration of int

module type S = sig
  type t
  type elt
  val from_int : t -> int -> elt
  val to_int : t -> elt -> int
  val create : elt list -> t
  val empty : unit -> t
  val pp : (Format.formatter -> elt -> unit) -> Format.formatter -> t -> unit
  val size : t -> int
  val iter : (elt -> unit) -> t -> unit
  val in_enum : t -> elt -> bool
end

module Make (HTyp : Hashtbl.HashedType) : S with type elt = HTyp.t = 
struct
  module HT = Hashtbl.Make (HTyp);;
  type t = { left  : HTyp.t DynArray.t;
             right : int HT.t }
  type elt = HTyp.t

  let pp pp_elt formatter enum = pp_dynarray pp_elt formatter enum.left

  let size enum = DynArray.length (enum.left)

  let in_enum enum elem = HT.mem enum.right elem

  (** may raise Not_in_enumeration *)
  let from_int enum elem =
    if elem >= (size enum)
    then raise (Not_in_enumeration elem)
    else DynArray.get enum.left elem

  let add enum elem =
    let len = DynArray.length enum.left in
    begin
      DynArray.add enum.left elem;
      HT.add enum.right elem len
    end

  let to_int enum elem =
    (if not (HT.mem enum.right elem) then add enum elem;
     HT.find enum.right elem)

  let create list =
    let left = DynArray.of_list list in
    let right = HT.create (DynArray.length left) in
    begin
      DynArray.iteri (fun i x -> HT.add right x i) left;
      { left = left; right = right }
    end

  let empty () = 
    { left = DynArray.create (); right = HT.create 32 }

  let iter f enum = DynArray.iter f enum.left
end

module MakeWeak (H : Hashtbl.HashedType) : S with type elt = H.t = struct
  module HT = Hashtbl.Make (H);;
  type t = { left  : H.t WeakDynArray.t;
             right : int HT.t }
  type elt = H.t

  let pp pp_elt formatter enum = WeakDynArray.pp pp_elt formatter enum.left

  let size enum = WeakDynArray.length (enum.left)

  let in_enum enum elem = HT.mem enum.right elem

  (** may raise Not_in_enumeration *)
  let from_int enum elem =
    if elem >= (size enum)
    then raise (Not_in_enumeration elem)
    else match WeakDynArray.get enum.left elem with
      | Some id -> id
      | None -> raise (Not_in_enumeration elem)

  let add enum elem =
    let len = WeakDynArray.length enum.left in
    begin
      WeakDynArray.add enum.left elem;
      HT.add enum.right elem len
    end

  let to_int enum elem =
    (if not (HT.mem enum.right elem) then add enum elem;
     HT.find enum.right elem)

  let create list =
    let left = WeakDynArray.of_list list in
    let right = HT.create (2 * (WeakDynArray.length left)) in
    begin
      WeakDynArray.iteri (fun i x -> HT.add right x i) left;
      { left = left; right = right }
    end

  let empty () = 
    { left = WeakDynArray.create (); right = HT.create 32 }

  let iter f enum = WeakDynArray.iter f enum.left
end
