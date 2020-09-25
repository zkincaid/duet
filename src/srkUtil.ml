(** Common utility functions *)
open BatPervasives

module A = BatDynArray

(** Search for an index in a sorted array *)
let search ?compare:(compare = Stdlib.compare) v array =
  let rec go min max =
    if max < min then raise Not_found
    else begin
      let mid = min + ((max - min) / 2) in
      let cmp = compare v (A.get array mid) in
      if cmp < 0 then go min (mid - 1)
      else if cmp > 0 then go (mid + 1) max
      else mid
    end
  in
  go 0 (A.length array - 1)

(** Merge two (sorted) arrays *)
let merge_array ?compare:(compare = Stdlib.compare) a b =
  let alen = Array.length a in
  let blen = Array.length b in
  (* count the size of the intersection of a and b *)
  let rec common i j acc =
    if i == alen || j == blen then acc else begin
      let cmp = compare a.(i) b.(j) in
      if cmp < 0 then common (i + 1) j acc
      else if cmp > 0 then common i (j + 1) acc
      else common (i + 1) (j + 1) (acc + 1)
    end
  in
  let clen = alen + blen - (common 0 0 0) in
  let c = Array.make clen (Obj.magic ()) in
  let rec go i j k =
    if k < clen then begin
      if i == alen then (c.(k) <- b.(j); go i (j + 1) (k + 1))
      else if j == blen then (c.(k) <- a.(i); go (i + 1) j (k + 1))
      else begin
        let cmp = compare a.(i) b.(j) in
        if cmp < 0 then (c.(k) <- a.(i); go (i + 1) j (k + 1))
        else if cmp > 0 then (c.(k) <- b.(j); go i (j + 1) (k + 1))
        else (c.(k) <- a.(i); go (i + 1) (j + 1) (k + 1))
      end
    end
  in
  go 0 0 0;
  c

let rec exp mul one p n =
  if n = 0 then one
  else if n = 1 then p
  else begin
    let q = exp mul one p (n / 2) in
    let q_squared = mul q q in
    if n mod 2 = 0 then q_squared
    else mul p q_squared
  end

let mk_show pp x =
  let b = Buffer.create 16 in
  let formatter = Format.formatter_of_buffer b in
  Format.fprintf formatter "@[<hov 0>%a@]@?" pp x;
  Buffer.sub b 0 (Buffer.length b)

let default_sep formatter () = Format.fprintf formatter ",@ "
let pp_print_enum_nobox ?(pp_sep=default_sep) pp_elt formatter enum =
  match BatEnum.get enum with
  | None   -> ()
  | Some x -> begin
      pp_elt formatter x;
      BatEnum.iter (fun elt ->
          pp_sep formatter ();
          pp_elt formatter elt
        ) enum;
    end
let pp_print_enum ?(indent=2) ?(pp_sep=default_sep) pp_elt formatter enum =
  Format.pp_open_hovbox formatter indent;
  pp_print_enum_nobox ~pp_sep pp_elt formatter enum;
  Format.pp_close_box formatter ()

let cartesian_product e1 e2 =
  let e2c = ref (BatEnum.clone e2) in
  let go () =
    match BatEnum.peek e1 with
    | None -> raise BatEnum.No_more_elements
    | Some x -> begin match BatEnum.get (!e2c) with
        | Some y -> (x, y)
        | None -> begin
            BatEnum.junk e1;
            e2c := BatEnum.clone e2;
            match BatEnum.peek e1, BatEnum.get (!e2c) with
            | Some x, Some y -> (x, y)
            | _, _ -> raise BatEnum.No_more_elements
          end
      end
  in
  BatEnum.from go

let rec tuples = function
  | [x] -> x /@ (fun elt -> [elt])
  | (x::xs) ->
    cartesian_product x (tuples xs) /@ (fun (x,y) -> x::y)
  | [] -> BatEnum.singleton []

let adjacent_pairs enum =
  let go () = match BatEnum.get enum, BatEnum.peek enum with
    | Some x, Some y -> (x, y)
    | _, _ -> raise BatEnum.No_more_elements
  in
  BatEnum.from go

let distinct_pairs enum =
  match BatEnum.get enum with
  | None -> BatEnum.empty ()
  | Some first ->
    let rest = ref (BatEnum.clone enum) in
    let cur = ref first in
    let rec go () =
      match BatEnum.get (!rest) with
      | None -> begin
          cur := BatEnum.get_exn enum;
          rest := BatEnum.clone enum;
          go ()
        end
      | Some elt -> (!cur, elt)
    in
    BatEnum.from go

let pp_print_list pp_elt formatter xs =
  let sep formatter () = Format.fprintf formatter ";@ " in
  Format.fprintf formatter "[%a]"
    (pp_print_enum ~pp_sep:sep pp_elt)
    (BatList.enum xs)

module Int = struct
  module I = struct
    type t = int [@@deriving show,ord]
    let hash = Hashtbl.hash
    let equal = (=)
  end
  include I
  module Set = struct
    include BatSet.Make(I)
    let pp formatter set =
      Format.fprintf formatter "{@[%a@]}"
        (pp_print_enum Format.pp_print_int) (enum set)
  end
  module Map = BatMap.Make(I)
end
