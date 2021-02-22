open BatPervasives

let lcm x y =
  match ZZ.to_int (ZZ.lcm (ZZ.of_int x) (ZZ.of_int y)) with
  | Some lcm -> lcm
  | None -> invalid_arg "Period length too long"

(* Find a list of the first n elements of an enumeration (and remove
   them from the enumeration). *)
let rec take_skip e n =
  if n = 0 then
    []
  else
    let hd = BatEnum.get_exn e in
    let tl = take_skip e (n-1) in
    hd::tl

(* Given a list of enums [e0, ..., ek], compute the list [f [e0 0;
   ..., ek 0], ... [f [e0 (n-1); ...; ek (n-1)]] (and remove the first
   n elements of each enum) *)
let rec take_skipn enums f n =
  if n = 0 then
    []
  else
    let hd = f (List.map BatEnum.get_exn enums) in
    let tl = take_skipn enums f (n-1) in
    hd::tl

module UltimatelyPeriodic = struct
  type 'a t = ('a list * 'a list) (* (transient, period) pair *)

  let enum =
    let count () = raise BatEnum.Infinite_enum in
    let rec next ct cp p () =
      match !ct with
      | (x::xs) ->
        ct := xs; x
      | [] -> match !cp with
        | x::xs ->
          cp := xs; x
        | [] ->
          cp := List.tl p;
          List.hd p
    and clone ct cp p () =
      let ct = ref !ct in
      let cp = ref !cp in
      BatEnum.make ~next:(next ct cp p) ~count ~clone:(clone ct cp p)
    in
    fun (t, p) ->
      let ct = ref t in
      let cp = ref p in
      BatEnum.make
        ~next:(next ct cp p)
        ~count
        ~clone:(clone ct cp p)

  let transient_len (t, _) = List.length t
  let period_len (_, p) = List.length p

  let transient (t, _) = t
  let periodic (_, p) = p

  let map f (t, p) = (List.map f t, List.map f p)

  let map2 f seq seq' =
    let transient = max (transient_len seq) (transient_len seq') in
    let period = lcm (period_len seq) (period_len seq') in
    let e =
      BatEnum.combine (enum seq) (enum seq')
      /@ (fun (x, y) -> f x y)
    in
    let t = take_skip e transient in
    let p = take_skip e period in
    (t, p)

  let mapn f seqs =
    let transient =
      List.fold_left (fun len seq -> max len (transient_len seq)) 0 seqs
    in
    let period =
      List.fold_left (fun len seq -> lcm len (period_len seq)) 1 seqs
    in
    let enums = List.map enum seqs in
    let t = take_skipn enums f transient in
    let p = take_skipn enums f period in
    (t, p)

  let equal ?(equal=(=)) seq seq' =
    let transient = max (transient_len seq) (transient_len seq') in
    let period = lcm (period_len seq) (period_len seq') in
    (BatEnum.combine (enum seq) (enum seq'))
    |> BatEnum.take (transient+period)
    |> BatEnum.for_all (fun (x,y) -> equal x y)

  let make t p = match p with
    | [] -> invalid_arg "Cannot make ultimate periodic sequence with empty period"
    | _ -> (t, p)

  let pp pp_elt formatter (t, p) =
    Format.fprintf formatter "%a(@[%a@])^omega"
      (SrkUtil.pp_print_enum_nobox pp_elt) (BatList.enum t)
      (SrkUtil.pp_print_enum_nobox pp_elt) (BatList.enum p)

  let nth (t, p) k =
    let t_len = List.length p in
    if k < t_len then
      List.nth t k
    else
      List.nth p ((k - t_len) mod (List.length p))

  let concat prefix (t, p) = (prefix @ t, p)

  let unfold ?(equal=(=)) f init =
    (* Brent's cycle detection algorithm *)
    let rec find_period tortoise hare power period_len =
      if equal tortoise hare then
        period_len
      else if power == period_len then
        find_period hare (f hare) (2 * power) 1
      else
        find_period tortoise (f hare) power (period_len + 1)
    in
    let period_len = find_period init (f init) 1 1 in
    let rec construct_seq n x seq =
      if n == 0 then (x, seq)
      else construct_seq (n - 1) (f x) (x::seq)
    in
    let rec find_repeat tortoise (hare, seq) =
      if equal tortoise hare then seq
      else find_repeat (f tortoise) (f hare, hare::seq)
    in
    let seq = find_repeat init (construct_seq period_len init []) in
    let rec split n seq period =
      if n == 0 then (List.rev seq, period)
      else match seq with
           | (x::seq) -> split (n - 1) seq (x::period)
           | [] -> assert false
    in
    split period_len seq []
end

module Periodic = struct
  type 'a t = 'a list

  let enum =
    let count () = raise BatEnum.Infinite_enum in
    let rec next cp p () =
      match !cp with
      | x::xs ->
         cp := xs; x
      | [] ->
         cp := List.tl p;
         List.hd p
    and clone cp p () =
      let cp = ref !cp in
      BatEnum.make ~next:(next cp p) ~count ~clone:(clone cp p)
    in
    fun p ->
      let cp = ref p in
      BatEnum.make
        ~next:(next cp p)
        ~count
        ~clone:(clone cp p)

  let period_len p = List.length p

  let period p = p

  let map f p = List.map f p

  let map2 f seq seq' =
    let period = lcm (period_len seq) (period_len seq') in
    let e =
      BatEnum.combine (enum seq) (enum seq')
      /@ (fun (x, y) -> f x y)
    in
    take_skip e period

  let mapn f seqs =
    let period =
      List.fold_left (fun len seq -> lcm len (period_len seq)) 1 seqs
    in
    take_skipn (List.map enum seqs) f period

  let equal ?(equal=(=)) seq seq' =
    (BatEnum.combine (enum seq) (enum seq'))
    |> BatEnum.take (lcm (period_len seq) (period_len seq'))
    |> BatEnum.for_all (fun (x,y) -> equal x y)

  let make p = match p with
    | [] -> invalid_arg "Cannot make periodic sequence with empty period"
    | _ -> p

  let pp pp_elt formatter p =
    Format.fprintf formatter "(@[%a@])^omega"
      (SrkUtil.pp_print_enum_nobox pp_elt) (BatList.enum p)

  let nth p k =
    List.nth p (k mod (List.length p))
end


let periodic_approx up =
  let transient = UltimatelyPeriodic.transient_len up in
  let period = UltimatelyPeriodic.period_len up in
  let n = (period - (transient mod period)) mod period in
  let (prefix, suffix) =
    BatList.takedrop n (UltimatelyPeriodic.periodic up)
  in
  Periodic.make (suffix @ prefix)
