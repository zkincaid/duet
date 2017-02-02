open Pervasives
open BatPervasives
open Apak

include Log.Make(struct let name = "BiGraph" end)

module type Vertex = sig
  type t
  val hash : t -> int
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val pp : Format.formatter -> t -> unit
end

module type S = sig
  type t
  type vertex

  val pp : Format.formatter -> t -> unit

  val empty : t
  val make : vertex BatEnum.t -> vertex BatEnum.t -> (vertex * vertex) BatEnum.t -> t
  val max_matching : t -> int
  val u_size : t -> int
  val v_size : t -> int
  val e_size : t -> int
end

module Make (V : Vertex) = struct
  type vertex = V.t
  type edge = V.t * V.t [@@deriving ord]

  module VertexSet = BatSet.Make(V)
  module EdgeSet = BatSet.Make(struct
      type t = edge [@@deriving ord]
    end)

  type t =
    { u : VertexSet.t;
      v : VertexSet.t;
      e : EdgeSet.t }

  let pp_edge formatter (u, v) =
    Format.fprintf formatter "(%a, %a)" V.pp u V.pp v

  let pp formatter graph =
    Format.fprintf formatter "{U: {%a}, V: {%a}, E: {%a}}"
    (ApakEnum.pp_print_enum V.pp) (VertexSet.enum graph.u)
    (ApakEnum.pp_print_enum V.pp) (VertexSet.enum graph.v)
    (ApakEnum.pp_print_enum pp_edge) (EdgeSet.enum graph.e)

  let empty = 
    { u = VertexSet.empty;
      v = VertexSet.empty;
      e = EdgeSet.empty }

  let make u v e =
    { u = VertexSet.of_enum u;
      v = VertexSet.of_enum v;
      e = EdgeSet.of_enum e}

  module VMap = BatMap.Make(V)
  module VoptMap = BatMap.Make(struct
    type t = V.t option
    let compare x y = (* None is the least element *)
      match (x, y) with
        None, None -> 0
      | None, Some _ -> -1
      | Some _, None -> 1
      | Some x', Some y' -> compare x' y'
  end)

(*  let make_adj e =
    let f (u, v) map =
      VMap.add u v map
    in
    EdgeSet.fold f e VMap.empty *)

  let make_adj e =
    let f (u, v) (uMap, vMap) =
      let g x y map =
        if (VMap.mem x map) then
          VertexSet.add y (VMap.find x map)
        else
          VertexSet.add y VertexSet.empty
      in
      ((VMap.add u (g u v uMap) uMap), (VMap.add v (g v u vMap) vMap))
    in
    EdgeSet.fold f e (VMap.empty, VMap.empty)

  let bfs u adj_u pair_u pair_v =
    let init u pair_u =
      let q = Queue.create() in
      let f u dist =
        match VMap.find u pair_u with
          None -> (Queue.add u q); VoptMap.add (Some u) 0 dist
        | Some v -> VoptMap.add (Some u) max_int dist
      in
      (VertexSet.fold f u VoptMap.empty), q
    in
    let (dist, q) = init u pair_u in
    let dist = VoptMap.add None max_int dist in
    let rec go dist =
      if (Queue.is_empty q) then dist
      else
        let u = Queue.take q in
        let du = VoptMap.find (Some u) dist in
        if du < (VoptMap.find None dist) then
          let f v dist =
            let pv = (VMap.find v pair_v) in
            if (VoptMap.find pv dist) = max_int then
              match pv with
                None -> VoptMap.add pv (du + 1) dist
              | Some u -> (Queue.add u q); VoptMap.add pv (du + 1) dist
            else dist
          in
          if (VMap.mem u adj_u) then
            go (VertexSet.fold f (VMap.find u adj_u) dist)
          else
            go dist
        else go dist
    in go dist

  let rec dfs u adj_u pair_u pair_v dist =
    match u with
      None -> pair_u, pair_v, true
    | Some u ->
      let f v (pair_u, pair_v, b) =
        if b then
          (pair_u, pair_v, b)
        else
          let pv = VMap.find v pair_v in
          if (VoptMap.find pv dist) = (VoptMap.find (Some u) dist) + 1 then
            let (pair_u, pair_v, b) = dfs pv adj_u pair_u pair_v dist in
            if b then
              (VMap.add u (Some v) pair_u), (VMap.add v (Some u) pair_v), true
            else
              (pair_u, pair_v, false)
          else
            (pair_u, pair_v, false)
      in
      if (VMap.mem u adj_u) then
        VertexSet.fold f (VMap.find u adj_u) (pair_u, pair_v, false)
      else
        (pair_u, pair_v, false)

  let max_matching graph =
    let (adj_u, adj_v) = make_adj graph.e in
    let f v map =
      VMap.add v None map
    in
    let pair_u = VertexSet.fold f graph.u (VMap.empty) in
    let pair_v = VertexSet.fold f graph.v (VMap.empty) in
    let rec go (pair_u, pair_v, matches) =
      let dist = bfs graph.u adj_u pair_u pair_v in
      if (VoptMap.find None dist) = max_int then
        matches
      else
        let f u (pair_u, pair_v, matches) =
          match VMap.find u pair_u with
            None ->
            let (pair_u, pair_v, b) = dfs (Some u) adj_u pair_u pair_v dist in
            if b then
              pair_u, pair_v, (matches + 1)
            else
              pair_u, pair_v, matches
          | Some _ -> (pair_u, pair_v, matches)
        in
        go (VertexSet.fold f graph.u (pair_u, pair_v, matches))
    in
    go (pair_u, pair_v, 0)

    let u_size g = VertexSet.cardinal g.u
    let v_size g = VertexSet.cardinal g.v
    let e_size g = EdgeSet.cardinal g.e
end
