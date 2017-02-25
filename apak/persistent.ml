(** Persistent, dynamic array *)
module Array = struct
  type 'a t = 'a data ref
  and 'a data =
    | Array of 'a array
    | Diff  of int * 'a * 'a t

  let make n f = ref (Array (Array.make n f))
  let init n f = ref (Array (Array.init n f))

  let rec length arr = match !arr with
    | Array a -> Array.length a
    | Diff (_, _, arr) -> length arr

  let sget arr n =
    try arr.(n) with
    | Invalid_argument _ -> 
      failwith ("Persistent: " ^ string_of_int n ^ " out of bounds")

  let rec reroot arr = match !arr with
    | Array _ -> ()
    | Diff (n, v, arr_diff) ->
      reroot arr_diff;
      begin match !arr_diff with
        | Array a ->
          let u = sget a n in
          a.(n) <- v;
          arr := Array a;
          arr_diff := Diff (n, u, arr)
        | Diff _ -> assert false
      end

  let rec resize arr newsize f = 
    reroot arr;
    match !arr with
    | Array a -> 
      let len = Array.length a in
      let g i = if i < len then a.(i)
        else f i
      in
      init newsize g
    | Diff _ -> assert false

  let get arr n = match !arr with
    | Array arr -> sget arr n
    | Diff _ ->
      reroot arr;
      begin match !arr with
        | Array arr -> sget arr n
        | Diff _ -> assert false
      end

  let set arr n v = 
    reroot arr;
    match !arr with
    | Array a ->
      let old_val = sget a n in
      a.(n) <- v;
      if old_val != v then
        let ret = ref (Array a) in
        arr := Diff (n, old_val, ret);
        ret
      else
        arr
    | Diff _ -> assert false

  let iter f arr = match !arr with
    | Array arr -> Array.iter f arr
    | Diff _ ->
      reroot arr;
      begin match !arr with
        | Array arr -> Array.iter f arr
        | Diff _ -> assert false
      end
end

(** Persistent union-find-delete *)
module DisjointSet = struct
  module Make (M : Putil.Ordered) : sig
    include Putil.S

    val create : int -> t
    val union : t -> M.t -> M.t -> t
    val union_sets : t -> int -> int -> t
    val find : t -> M.t -> int
    val eq : int -> int -> bool
    val same_set : t -> M.t -> M.t -> bool
    val delete : t -> M.t -> t
    val inter : t -> t -> t
    val equal : t -> t -> bool
    val compare : t -> t -> int

    val iter : (M.t -> unit) -> t -> unit
    val fold : (M.t -> 'a -> 'a) -> t -> 'a -> 'a
    val containing_set : t -> M.t -> M.t list

    val to_list : t -> (M.t list) list

    val join : t -> t -> t
    val widen : t -> t -> t
    val rep : (M.t -> bool) -> t -> M.t -> M.t
  end = struct
    module Map = Map.Make(M);;
    module A = Array;;

    type elt = M.t option
    type t = { mutable name : elt A.t;
               mutable rank : int A.t;
               mutable parent : int A.t;
               mutable map : int Map.t;
               mutable size : int;
               mutable max_id : int }

    let get_name arr s = match A.get arr s with
      | Some ap -> ap
      | None -> failwith "Persistent: no name set"

    let set_name arr s elem = A.set arr s (Some elem)


    (* Try to make accurate estimates for size, as a resizing will result in two
     * copies of the disjoint set in order to maintain persistency. *)
    let create size = { 
      name = A.init size (fun _ -> None);
      rank = A.init size (fun _ -> 0);
      parent = A.init size (fun i -> i);
      map = Map.empty;
      size = size;
      max_id = 0 }

    let resize ds = 
      let size = ds.size * 2 in
      ds.name <- A.resize ds.name size (fun _ -> None);
      ds.rank <- A.resize ds.rank size (fun _ -> 0);
      ds.parent <- A.resize ds.parent size (fun i -> i);
      ds.size <- size

    let get_id ds elem =
      try 
        let s = Map.find elem ds.map in
        if (M.compare (get_name ds.name s) elem) = 0 then s
        else failwith "Persistent: mappings don't agree"
      with Not_found -> begin
          let s = ds.max_id in
          ds.map <- Map.add elem s ds.map;
          ds.name <- set_name ds.name s elem;
          ds.max_id <- ds.max_id + 1;
          if ds.max_id  >= ds.size then resize ds;
          s
        end

    (* Compress path and pass the new parent array back up *)
    let rec find_aux parent x =
      let y = A.get parent x in
      if y = x then
        (parent, x)
      else
        let (y_parent, root) = find_aux parent y in
        let new_parent = A.set y_parent x root in
        (new_parent, root)

    let find ds elem =
      let x = get_id ds elem in
      let (new_parent, root) = find_aux ds.parent x in
      ds.parent <- new_parent;
      root

    let eq x y = x = y

    let union_sets ds x_root y_root =
      let rx = A.get ds.rank x_root in
      let ry = A.get ds.rank y_root in
      if rx > ry then {ds with parent = A.set ds.parent y_root x_root}
      else if rx < ry then {ds with parent = A.set ds.parent x_root y_root}
      else if not (eq x_root y_root) then
        { name = ds.name;
          rank = A.set ds.rank x_root (rx + 1);
          parent = A.set ds.parent y_root x_root;
          map = ds.map;
          size = ds.size;
          max_id = ds.max_id }
      else ds

    let union ds x y =
      union_sets ds (find ds x) (find ds y)

    let same_set ds x y = eq (find ds x) (find ds y)

    let flatten ds =
      ds.parent <- Map.fold 
          (fun _ x parent -> fst (find_aux parent x)) 
          ds.map 
          ds.parent

    let delete ds elem =
      let try_delete elem =
        let x = get_id ds elem in
        let y = A.get ds.parent x in
        if y = x then
          let f _ y (parent, z) =
            if y != x && A.get parent y = x then
              if z = -1 then
                (A.set parent y y, y)
              else
                (A.set parent y z, z)
            else
              (parent, z)
          in
          {ds with parent = fst (Map.fold f ds.map (ds.parent, -1))}
        else
          {ds with parent = A.set ds.parent x x}
      in
      flatten ds;
      try try_delete elem
      with Not_found -> ds

    let inter ds1 ds2 =
      let inter_ordered ds1 ds2 =
        let new_ds = create (ds1.size) in

        let g s (new_ds, singleton) t =
          if same_set ds2 s t then
            (union new_ds s t, false)
          else 
            (new_ds, singleton && true)
        in

        let f s _ (new_ds, wl) =
          let sprime = get_name ds1.name (find ds1 s) in
          let (new_ds, singleton) = 
            List.fold_left (g s) (new_ds, true) (sprime::wl)
          in
          if singleton then (new_ds, s::wl)
          else (new_ds, wl)
        in

        Map.fold f ds1.map (new_ds, [])
      in
      if (ds1.max_id) > (ds2.max_id) then 
        fst (inter_ordered ds2 ds1)
      else 
        fst (inter_ordered ds1 ds2)

    let equal ds1 ds2 = 
      let equal_ordered ds1 ds2 =
        let f s _ flg =
          let sprime = get_name ds1.name (get_id ds1 s) in
          flg && (same_set ds2 s sprime)
        in
        Map.fold f ds1.map true
      in
      equal_ordered ds1 ds2 && equal_ordered ds2 ds1

    module IntMap = Putil.PInt.Map
    let compute_rep p ds =
      let min x y = if M.compare x y < 0 then x else y in
      let f elt _ map =
        let root = find ds elt in
        if p elt then begin
          let rep =
            if IntMap.mem root map then min elt (IntMap.find root map)
            else elt
          in
          IntMap.add root rep map
        end else map
      in
      Map.fold f ds.map IntMap.empty

    let normalize = compute_rep (fun _ -> true)

    let compare x y =
      IntMap.compare M.compare (normalize x) (normalize y)

    let to_list_map ds =
      let f s _ map =
        let root = get_name ds.name (find ds s) in
        let v =
          try Map.find root map
          with Not_found -> []
        in 
        Map.add root (s::v) map
      in
      Map.fold f ds.map Map.empty

    let to_list ds =
      let map = to_list_map ds in
      Map.fold (fun _ x xs -> x::xs) map []

    let rep p ds =
      let map = compute_rep p ds in
      fun elt ->
        try IntMap.find (find ds elt) map
        with Not_found -> elt

    let pp formatter ds =
      let pp_elt elt =
        Format.pp_print_string formatter ([%derive.show : M.t list] elt)
      in
      Format.pp_open_box formatter 0;
      List.iter pp_elt (to_list ds);
      Format.pp_close_box formatter ()

    let show = Putil.mk_show pp

    let iter f ds = Map.iter (fun s _ -> f s) ds.map
    let fold f ds x = Map.fold (fun s _ -> f s) ds.map x

    let containing_set ds x =
      let f ap lst =
        if (same_set ds ap x) then ap::lst
        else lst
      in
      fold f ds [x]

    let join = inter
    let widen = inter
  end
end
