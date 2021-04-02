open Srk
let load_path       = ref ["."]
let temp_dir        = ref (None : string option)

let set_load_path str = load_path := BatString.split_on_char ':' str
let set_temp_dir str = temp_dir := Some str

include BatEnum.Infix
include BatPervasives
module List = BatList

module type S =
sig
  type t
  val pp : Format.formatter -> t -> unit
end

module type OrderedMix =
sig
  type t
  val compare : t -> t -> int
end

module type Ordered =
sig
  type t
  val pp : Format.formatter -> t -> unit
  val compare : t -> t -> int
end

(* Sets ***********************************************************************)
module Set = struct
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

  module Make (Ord : Ordered) : S with type elt = Ord.t =
  struct
    module S = BatSet.Make(Ord)
    include S

    let pp formatter set =
      Format.fprintf formatter "{@[%a@]}"
        (SrkUtil.pp_print_enum Ord.pp) (enum set)
  end
end

(* Maps ***********************************************************************)
module Map = struct
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
    val pp :
      (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit
  end
  module Make (Key : Ordered) : S with type key = Key.t = struct
    include BatMap.Make(Key)
    let pp pp_val formatter map =
      let pp_elt formatter (key, value) =
        Format.fprintf formatter "@[%a@ => %a@]"
          Key.pp key
          pp_val value;
      in
      Format.fprintf formatter "[@[%a@]]"
        (SrkUtil.pp_print_enum pp_elt) (enum map)
  end
end

module MonoMap = struct
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

  module Make (Key : Ordered) (Val : PP) : S with type key = Key.t
                                              and type value = Val.t =
  struct
    module M = BatMap.Make(Key)
    type key = Key.t
    type value = Val.t
    type 'a u = 'a M.t
    include (M : BatMap.S with type 'a t := 'a u and type key := key)
    type t = value u
    let pp formatter map =
      let pp_elt formatter (key, value) =
        Format.fprintf formatter "@[%a@ => %a@]"
          Key.pp key
          Val.pp value;
      in
      Format.fprintf formatter "[@[%a@]]"
        (SrkUtil.pp_print_enum pp_elt) (M.enum map)
  end

  module Ordered = struct
    module type S = sig
      include S
      include OrderedMix with type t := t
    end
    module Make (Key : Ordered) (Val : Ordered) : S with
      type key = Key.t
                                                     and type value = Val.t =
    struct
      include Make(Key)(Val)
      let compare = compare Val.compare
    end
  end
end

module TotalFunction = struct
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
    val show : t -> string
    val default : t -> cod
    val const : cod -> t
    val equal : t -> t -> bool
  end
  module LiftMap
      (M : Map.S)
      (Codomain : sig
         type t
         val pp : Format.formatter -> t -> unit
         val equal : t -> t -> bool
       end) =
  struct
    type dom = M.key
    type cod = Codomain.t
    type t = 
      { map : Codomain.t M.t;
        default : Codomain.t }

    let pp format map =
      Format.fprintf format "{@[map: %a;@ default: %a@]}"
        (M.pp Codomain.pp) map.map
        Codomain.pp map.default
    let show = SrkUtil.mk_show pp

    let equal f g =
      Codomain.equal f.default g.default
      && M.equal Codomain.equal f.map g.map

    let const v = { map = M.empty; default = v }

    let update k v f =
      if Codomain.equal f.default v
      then if M.mem k f.map then { f with map = M.remove k f.map } else f
      else { f with map = M.add k v f.map }

    let eval f x =
      try M.find x f.map
      with Not_found -> f.default

    let merge m f g =
      let default = m f.default g.default in
      let return x = if Codomain.equal x default then None else Some x in
      let merge _ a b = match a,b with
        | Some a, Some b -> return (m a b)
        | Some a, _ -> return (m a g.default)
        | _, Some b -> return (m f.default b)
        | None, None -> assert false
      in
      { map = M.merge merge f.map g.map;
        default = default }

    let map f x =
      { map = M.map f x.map;
        default = f x.default }
    let enum f = M.enum f.map
    let support f = M.keys f.map
    let default f = f.default
  end

  module Ordered = struct
    module type S = sig
      include S
      include OrderedMix with type t := t
    end
    module LiftMap (M : Map.S) (Codomain : Ordered) = struct
      include LiftMap(M)(struct
          include Codomain
          let equal x y = compare x y = 0
        end)
      let compare f g =
        match Codomain.compare f.default g.default with
        | 0 -> M.compare Codomain.compare f.map g.map
        | x -> x
    end
  end
end

(* Hashed types ***************************************************************)
module Hashed = struct

  let list h xs = Hashtbl.hash (List.map h xs)
  let combine x y = Hashtbl.hash (x, y)

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

  module Set = struct
    module type S = sig
      include Set.S
      val hash : t -> int
      val equal : t -> t -> bool
    end
    module Make (M : Ordered) = struct
      include Set.Make(M)
      let hash set =
        fold (fun elt hash -> combine (M.hash elt) hash) set 0
    end
  end
end

let with_temp_filename base exn f =
  let file = Filename.temp_file base exn in
  let result = f file in
  Sys.remove file;
  result

let with_temp_file base exn f =
  let go name =
    let file = Stdlib.open_out name in
    let result = f name file in
    Stdlib.close_out file;
    result
  in
  with_temp_filename base exn go

(* not completely safe! *)
let with_temp_dir base f =
  let name = Filename.temp_file base "" in
  Unix.unlink name; (* kill regular file, make a directory *)
  Unix.mkdir name 0o770; (* ug+rwx *)
  let result = f name in
  (* cleanup *)
  begin
    let handle = Unix.opendir name in
    try while true do
        let fn = Unix.readdir handle in
        if not (fn = "." || fn = "..") then Unix.unlink (name ^ "/" ^ fn)
      done with End_of_file -> Unix.rmdir name
  end;
  result

let with_temp_dir base f =
  match !temp_dir with
  | Some x -> f x
  | None   -> with_temp_dir base f

(** Search for a file named {!file} in all the directories in the load
    path.  Raise File_not_found if no such file exists. *)
let find_file file =
  let rec go = function
    | [] -> None
    | (d::ds) ->
      let qualified = d ^ "/" ^ file in
      if Sys.file_exists qualified then Some qualified
      else go ds
  in
  go (!load_path)

module type CoreTypeBasis = sig
  include Ordered
  val hash : t -> int
end
module type CoreType = sig
  include CoreTypeBasis
  val show : t -> string
  val equal : t -> t -> bool
  module HT : BatHashtbl.S with type key = t
  module Map : Map.S with type key = t
  module Set : Hashed.Set.S with type elt = t
end

module MakeCoreType (M : CoreTypeBasis) = struct
  module AM = struct
    include M
    let equal x y = compare x y = 0
  end
  include AM
  let show = SrkUtil.mk_show pp
  module HT = BatHashtbl.Make(AM)
  module Map = Map.Make(M)
  module Set = Hashed.Set.Make(AM)
end

module PString = MakeCoreType(struct
    type t = string [@@deriving show,ord]
    let hash = Hashtbl.hash
  end)

module PInt = MakeCoreType(struct
    type t = int [@@deriving show,ord]
    let hash = Hashtbl.hash
  end)

module PUnit = MakeCoreType(struct
    type t = unit [@@deriving show,ord]
    let hash _ = 0
  end)

module PChar = MakeCoreType(struct
    type t = char [@@deriving show,ord]
    let hash = Hashtbl.hash
  end)

let rec compare_tuple = function
  | [] -> 0
  | (x::xs) ->
    let cmp = Lazy.force x in
    if cmp = 0 then compare_tuple xs else cmp
