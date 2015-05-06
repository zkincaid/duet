(** Maintains a bidirectional mapping from an n-element list to \{1,
    ..., n\} *)

module DynArray = BatDynArray

(* From Deriving.Show.Show_array *)
let format_dynarray pp formatter items =
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
  type e
  val from_int : t -> int -> e
  val to_int : t -> e -> int
  val create : e list -> t
  val empty : unit -> t
  val format : (Format.formatter -> e -> unit) -> Format.formatter -> t -> unit
  val size : t -> int
  val iter : (e -> unit) -> t -> unit
  val in_enum : t -> e -> bool
end
module type Enum = sig
  include S
  type k 
  val make     : t -> k -> e
  val kind_of  : e -> k
end


module Make (HTyp : Hashtbl.HashedType) : S with type e = HTyp.t = 
struct
  module HT = Hashtbl.Make (HTyp);;
  type t = { left  : HTyp.t DynArray.t;
             right : int HT.t }
  type e = HTyp.t

  let format pp formatter enum = format_dynarray pp formatter enum.left

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

module MakeEnum (M : sig type t end) : Enum with type k = M.t = 
struct
  type t = { left  : M.t DynArray.t }
  type k = M.t
  type e = int * k

  let format pp formatter enum =
    format_dynarray pp formatter (DynArray.mapi (fun i k -> (i,k)) enum.left)

  let size enum = DynArray.length (enum.left)

  let in_enum enum (i, _) = i < (size enum)

  (** may raise Not_in_enumeration *)
  let from_int enum id =
    if id >= (size enum) || id < 0
    then raise (Not_in_enumeration id)
    else (id, DynArray.get enum.left id)

  let make enum kind =
    let len = DynArray.length enum.left in
    DynArray.add enum.left kind;
    (len, kind)

  let kind_of (id, kind) = kind

  let to_int enum (id, _) = id

  let create list =
    { left = DynArray.of_list (List.map snd list) }

  let empty () = 
    { left = DynArray.create () }

  let iter f enum = DynArray.iteri (fun i x -> f (i,x)) enum.left
end
