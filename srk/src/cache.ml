type cache_params = {
  max_size : int;
  hard_limit : int;
  keys_hit_rate : float;
  min_hits : float;
  aging_factor : float;
}

let default_params = {
    max_size = 1000;
    hard_limit = 0;
    keys_hit_rate = 0.9;
    min_hits = 0.9;
    aging_factor = 0.95;
  }

module type S = sig
  type ('a, 'b) t
  val create : ?random:bool -> ?params:cache_params -> int -> ('a, 'b) t
  val get_params : ('a, 'b) t -> cache_params
  val set_params : ('a, 'b) t -> cache_params -> unit
  val clear : ('a, 'b) t -> unit
  val reset : ('a, 'b) t -> unit
  val copy : ('a, 'b) t -> ('a, 'b) t
  val add : ('a, 'b) t -> 'a -> 'b -> unit
  val find : ('a, 'b) t -> 'a -> 'b
  val find_opt : ('a, 'b) t -> 'a -> 'b option
  val mem : ('a, 'b) t -> 'a -> bool
  val remove : ('a, 'b) t -> 'a -> unit
  val iter : ('a -> 'b -> unit) -> ('a, 'b) t -> unit
  val filter_map_inplace : ('a -> 'b -> 'b option) -> ('a, 'b) t -> unit
  val fold : ('a -> 'b -> 'c -> 'c) -> ('a, 'b) t -> 'c -> 'c
  val length : ('a, 'b) t -> int
end

module type HashS = sig
  type key
  type 'a t
  val create : ?params:cache_params -> int -> 'a t
  val get_params : 'a t -> cache_params
  val set_params : 'a t -> cache_params -> unit
  val clear : 'a t -> unit
  val reset : 'a t -> unit
  val copy : 'a t -> 'a t
  val add : 'a t -> key -> 'a -> unit
  val find : 'a t -> key -> 'a
  val find_opt : 'a t -> key -> 'a option
  val mem : 'a t -> key -> bool
  val remove : 'a t -> key -> unit
  val iter : (key -> 'a -> unit) -> 'a t -> unit
  val filter_map_inplace : (key -> 'a -> 'a option) -> 'a t -> unit
  val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
  val length : 'a t -> int
end

module DList = struct
  type 'a node = {
    data : 'a;
    mutable prev : 'a node option;
    mutable next : 'a node option;
  }

  type 'a t = {
    mutable head : 'a node option;
    mutable tail : 'a node option;
  }

  let create _ =
    { head = None; tail = None }

  let clear dl =
    dl.head <- None; dl.tail <- None

  let copy dl =
    let rec go n cprev =
      match n with
      | None -> (Some cprev)
      | Some n ->
        let cn = { data = n.data; prev = (Some cprev); next = None } in
        go n.next cn
    in
    match (dl.head, dl.tail) with
    | None, None -> { head = None; tail = None }
    | Some hd, Some _ ->
      let chd = { data = hd.data; prev = None; next = None } in
      { head = Some chd; tail = (go hd.next chd) }
    | _ -> assert false

  let move_front dl n =
    match n.prev with
    | None -> ()
    | Some prev ->
      prev.next <- n.next;
      (match n.next with
      | None -> dl.tail <- Some prev
      | Some next -> next.prev <- Some prev);
      n.prev <- None;
      n.next <- dl.head;
      dl.head <- (Some n)

  let add_front dl datum =
    let n = {data = datum; prev = None; next = None } in
    (match (dl.head, dl.tail) with
    | None, None -> dl.head <- Some n; dl.tail <- Some n
    | Some hd, Some _ -> hd.prev <- Some n; n.next <- dl.head; dl.head <- Some n
    | _ -> assert false);
    n

  let remove dl n =
    (match n.prev with
    | None -> dl.head <- n.next
    | Some prev -> prev.next <- n.next);
    (match n.next with
    | None -> dl.tail <- n.prev
    | Some next -> next.prev <- n.prev);
    n.prev <- None; n.next <- None

end

module LRU = struct

  type ('a, 'b) data = {
    key : 'a;
    mutable value : 'b;
    mutable hits : float;
  }

  let new_data k v = { key = k; value = v; hits = 0.0 }

  type ('a, 'b) node = ('a, 'b) data DList.node
  type ('a, 'b) dlist = ('a, 'b) data DList.t

  type ('a, 'b) t = {
    updates : ('a, 'b) dlist;   (* head is most recently updated, tail is least recently updated *)
    table : ('a, ('a, 'b) node) Hashtbl.t;

    mutable num_hit_rate : int; (* number of keys that surpass min_hit threshold *)
    mutable params : cache_params;
    init_params : cache_params;
  }

  let validate_params p =
    0 < p.max_size &&
    (p.hard_limit = 0 || p.max_size <= p.hard_limit) &&
    0.0 <= p.keys_hit_rate && p.keys_hit_rate <= 1.0 &&
    0.0 <= p.min_hits &&
    0.0 <= p.aging_factor && p.aging_factor <= 1.0

  let create ?(random = false) ?(params = default_params) init_sz =
  if not (validate_params params) then invalid_arg "Cache params not valid" else
    { updates = DList.create ();
      table = Hashtbl.create ~random init_sz;
      num_hit_rate = 0;
      params;
      init_params = params;
    }

  let get_params c = c.params

  let clear c =
    DList.clear c.updates;
    c.num_hit_rate <- 0;
    Hashtbl.clear c.table

  let reset c =
    DList.clear c.updates;
    c.num_hit_rate <- 0;
    Hashtbl.reset c.table;
    c.params <- c.init_params

  let copy c =
    { c with updates = DList.copy c.updates; table = Hashtbl.copy c.table }

  let remove c k =
    match Hashtbl.find_opt c.table k with
    | None -> ()
    | Some n ->
      DList.remove c.updates n; 
      Hashtbl.remove c.table k;
      if c.params.min_hits <= n.data.hits then
        c.num_hit_rate <- c.num_hit_rate - 1

  let evict c =
    let k =
      match c.updates.tail with
      | None -> assert false
      | Some tl -> tl.data.key
    in remove c k

  let resize c =
    let next_sz sz limit = min (2 * sz) limit in
    let limit = if c.params.hard_limit = 0 then Sys.max_array_length else c.params.hard_limit in
    let nsize = next_sz (Hashtbl.length c.table) limit in
    c.params <- { c.params with max_size = nsize };
    Hashtbl.iter (fun _ (n : ('a, 'b) node) ->
      n.data.hits <- c.params.aging_factor *. n.data.hits
    ) c.table

  let evict_or_resize c =
    assert (Hashtbl.length c.table = c.params.max_size);
    if (c.params.hard_limit <> 0 && c.params.max_size = c.params.hard_limit) ||
       (float c.num_hit_rate) /. (float (Hashtbl.length c.table)) < c.params.keys_hit_rate then
      evict c
    else
      resize c

  let set_params c p =
    if not (validate_params p) then invalid_arg "Cache params not valid";
    c.params <- p;
    c.num_hit_rate <- 0;
    Hashtbl.iter (fun _ (n : ('a, 'b) node) ->
      if p.min_hits <= n.data.hits then
        c.num_hit_rate <- c.num_hit_rate + 1
    ) c.table;
    while c.params.max_size < Hashtbl.length c.table do
      evict_or_resize c
    done

  let add_hit c (n : ('a, 'b) node) =
    let b4 = n.data.hits in
    n.data.hits <- n.data.hits +. 1.0;
    let after = n.data.hits in
    if b4 < c.params.min_hits && c.params.min_hits <= after then
      c.num_hit_rate <- c.num_hit_rate + 1

  let add c k v =
    match Hashtbl.find_opt c.table k with
    | Some n ->
      n.data.value <- v;
      add_hit c n;
      DList.move_front c.updates n
    | None ->
      if c.params.max_size <= Hashtbl.length c.table then (* Cache is full *)
        evict_or_resize c;
      let n = DList.add_front c.updates (new_data k v) in
      Hashtbl.add c.table k n

  let find c k =
    match Hashtbl.find_opt c.table k with
    | None -> raise Not_found
    | Some n -> add_hit c n; DList.move_front c.updates n; n.data.value

  let find_opt c k =
    match Hashtbl.find_opt c.table k with
    | None -> None
    | Some n -> add_hit c n; DList.move_front c.updates n; Some n.data.value

  let mem c k =
    match Hashtbl.find_opt c.table k with
    | None -> false
    | Some n -> add_hit c n; DList.move_front c.updates n; true

  let iter f c =
    Hashtbl.iter (fun k n ->
      add_hit c n; f k n.data.value
    ) c.table

  let filter_map_inplace f c =
    Hashtbl.filter_map_inplace (fun k (n : ('a, 'b) node) ->
      match f k n.data.value with
      | Some v -> add_hit c n; n.data.value <- v; Some n
      | None ->
      DList.remove c.updates n;
      if c.params.min_hits <= n.data.hits then
        c.num_hit_rate <- c.num_hit_rate - 1;
      None
    ) c.table

  let fold f c init =
    Hashtbl.fold (fun k n acc ->
      add_hit c n; f k n.data.value acc
    ) c.table init

  let length c = Hashtbl.length c.table

  module Make(K : Hashtbl.HashedType) = struct
    type key = K.t
    module HT = Hashtbl.Make(K)

    type 'a t = {
      updates : (key, 'a) dlist;    (* head is most recently updated, tail is least recently updated *)
      table : (key, 'a) node HT.t;

      mutable num_hit_rate : int;   (* number of keys that surpass min_hit threshold *)
      mutable params : cache_params;
      init_params : cache_params;
    }

    let create ?(params = default_params) init_sz =
      if not (validate_params params) then invalid_arg "Cache params not valid" else
      { updates = DList.create ();
        table = HT.create init_sz;
        num_hit_rate = 0;
        params;
        init_params = params;
      }

    let get_params c = c.params

    let clear c =
      DList.clear c.updates;
      c.num_hit_rate <- 0;
      HT.clear c.table

    let reset c =
      DList.clear c.updates;
      c.num_hit_rate <- 0;
      HT.reset c.table;
      c.params <- c.init_params

    let copy c =
      { c with updates = DList.copy c.updates; table = HT.copy c.table }

    let remove c k =
      match HT.find_opt c.table k with
      | None -> ()
      | Some n ->
        DList.remove c.updates n; 
        HT.remove c.table k;
        if c.params.min_hits <= n.data.hits then
          c.num_hit_rate <- c.num_hit_rate - 1

    let evict c =
      let k =
        match c.updates.tail with
        | None -> assert false
        | Some tl -> tl.data.key
      in remove c k

    let resize c =
      let next_sz sz limit = min (2 * sz) limit in
      let limit = if c.params.hard_limit = 0 then Sys.max_array_length else c.params.hard_limit in
      let nsize = next_sz (HT.length c.table) limit in
      c.params <- { c.params with max_size = nsize };
      HT.iter (fun _ (n : ('a, 'b) node) ->
        n.data.hits <- c.params.aging_factor *. n.data.hits
      ) c.table

    let evict_or_resize c =
      assert (HT.length c.table = c.params.max_size);
      if (c.params.hard_limit <> 0 && c.params.max_size = c.params.hard_limit) ||
         (float c.num_hit_rate) /. (float (HT.length c.table)) < c.params.keys_hit_rate then
        evict c
      else
        resize c

    let set_params c p =
      if not (validate_params p) then invalid_arg "Cache params not valid";
      c.params <- p;
      c.num_hit_rate <- 0;
      HT.iter (fun _ (n : ('a, 'b) node) ->
        if p.min_hits <= n.data.hits then
          c.num_hit_rate <- c.num_hit_rate + 1
      ) c.table;
      while c.params.max_size < HT.length c.table do
        evict_or_resize c
      done

    let add_hit c (n : ('a, 'b) node) =
      let b4 = n.data.hits in
      n.data.hits <- n.data.hits +. 1.0;
      let after = n.data.hits in
      if b4 < c.params.min_hits && c.params.min_hits <= after then
        c.num_hit_rate <- c.num_hit_rate + 1

    let add c k v =
      match HT.find_opt c.table k with
      | Some n ->
        n.data.value <- v;
        add_hit c n;
        DList.move_front c.updates n
      | None ->
        if c.params.max_size <= HT.length c.table then (* Cache is full *)
          evict_or_resize c;
        let n = DList.add_front c.updates (new_data k v) in
        HT.add c.table k n

    let find c k =
      match HT.find_opt c.table k with
      | None -> raise Not_found
      | Some n -> add_hit c n; DList.move_front c.updates n; n.data.value

    let find_opt c k =
      match HT.find_opt c.table k with
      | None -> None
      | Some n -> add_hit c n; DList.move_front c.updates n; Some n.data.value

    let mem c k =
      match HT.find_opt c.table k with
      | None -> false
      | Some n -> add_hit c n; DList.move_front c.updates n; true

    let iter f c =
      HT.iter (fun k n ->
        add_hit c n; f k n.data.value
      ) c.table

    let filter_map_inplace f c =
      HT.filter_map_inplace (fun k (n : ('a, 'b) node) ->
        match f k n.data.value with
        | Some v -> add_hit c n; n.data.value <- v; Some n
        | None ->
        DList.remove c.updates n;
        if c.params.min_hits <= n.data.hits then
          c.num_hit_rate <- c.num_hit_rate - 1;
        None
      ) c.table

    let fold f c init =
      HT.fold (fun k n acc ->
        add_hit c n; f k n.data.value acc
      ) c.table init

    let length c = HT.length c.table
  end
end
