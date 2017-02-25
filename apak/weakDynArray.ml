type 'a t = {
  mutable arr : 'a Weak.t;
  mutable len : int;
}

let length d = d.len

let make len =
  { arr = Weak.create len;
    len = len }

let create () = make 32

let grow d =
  let new_length =
    let twice = if d.len > 0 then 2 * d.len else 1 in
    if twice < Sys.max_array_length && twice > d.len then
      twice
    else if d.len < Sys.max_array_length then
      Sys.max_array_length
    else
      invalid_arg "WeakDynarray.grow: Out of space"
  in      
  let new_arr = Weak.create new_length in
  Weak.blit d.arr 0 new_arr 0 d.len;
  d.arr <- new_arr

let add d v =
  if d.len = Weak.length d.arr then grow d;
  Weak.set d.arr d.len (Some v);
  d.len <- d.len + 1

let set d i v = Weak.set d.arr i v

let get d i = Weak.get d.arr i

let get_copy d i = Weak.get_copy d.arr i

let check d i = Weak.check d.arr i

let blit src srcidx dst dstidx len =
  Weak.blit src.arr srcidx dst.arr dstidx len

let iter f d =
  for i = 0 to d.len - 1 do
    match get d i with
    | Some elt -> f elt
    | None -> ()    
  done

let iteri f d =
  for i = 0 to d.len - 1 do
    match get d i with
    | Some elt -> f i elt
    | None -> ()    
  done

let of_list items =
  let len = List.length items in
  let d = make len in
  List.iteri (fun i v -> Weak.set d.arr i (Some v)) items;
  d

let pp pp_elt formatter d =
  let write_items formatter () =
    d |> iteri (fun i item ->
        Format.fprintf formatter "@[%d -> %a;@;@]" i pp_elt item)
  in
  Format.fprintf formatter "@[[|%a|]@]" write_items ()
