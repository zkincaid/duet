open Pervasives
open BatPervasives
open Ark

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

  val incident_u : t -> int
  val incident_v : t -> int
end

module Make (V : Vertex) = struct
  type vertex = V.t

  module VertexSet = BatSet.Make(V)
  module VertexMap = BatMap.Make(V)

  (* Adjacency map representation for a BiPartite Graph *)
  type t =
    { u : VertexSet.t;
      v : VertexSet.t;
      adj_u : VertexSet.t VertexMap.t;  (* v in adj_u[u] -> (u, v) in E *)
      adj_v : VertexSet.t VertexMap.t } (* u in adj_v[v] -> (u, v) in E *) (* Not necessary for matching algorithm *)

  let pp formatter graph =
    Format.fprintf formatter "{U: {%a}, V: {%a}}"
    (ArkUtil.pp_print_enum V.pp) (VertexSet.enum graph.u)
    (ArkUtil.pp_print_enum V.pp) (VertexSet.enum graph.v)

  (* An empty BiPartite Graph *)
  let empty = 
    { u = VertexSet.empty;
      v = VertexSet.empty;
      adj_u = VertexMap.empty;
      adj_v = VertexMap.empty}

  (* Takes sets of vertices, U and V, and edges, E,
     and construcsts adjacency map representation
     U and V do not need to be disjoint (i.e.
     you can reuse the same name for a vertex in U
     and V)
     Example:
       U = {1}, V = {1}, E = {(1, 1)}
       U      V
       1 <--> 1'
  *)
  let make u v e =
    let f (uMap, vMap) (u, v) =
      let g x y map =
        if (VertexMap.mem x map) then
          VertexSet.add y (VertexMap.find x map)
        else
          VertexSet.add y VertexSet.empty
      in
      ((VertexMap.add u (g u v uMap) uMap), (VertexMap.add v (g v u vMap) vMap))
    in
    let uMap, vMap = BatEnum.fold f (VertexMap.empty, VertexMap.empty) e in
    { u = VertexSet.of_enum u;
      v = VertexSet.of_enum v;
      adj_u = uMap;
      adj_v = vMap}

  (* Part of the Hopcroft-Karp algorithm
     performs a breadth first search to determine
     the distance of vertices in U from a free vertex *)
  let bfs u adj_u pair_u pair_v =
    let q = Queue.create() in
    let init u dist =
      match VertexMap.find u pair_u with
        None -> (Queue.add u q); VertexMap.add u 0 dist
      | Some _ -> VertexMap.add u max_int dist
    in
    let dNone : int ref = ref max_int in
    let rec go dist =
      if (Queue.is_empty q) then (dist, !dNone)
      else
        let u = Queue.take q in
        let du = VertexMap.find u dist in
        if du < !dNone then
          let f v dist =
            match (VertexMap.find v pair_v) with
              None -> (if (!dNone) = max_int then dNone := (du + 1)); dist
            | Some u ->
               if (VertexMap.find u dist) = max_int then
                 begin (Queue.add u q); VertexMap.add u (du + 1) dist end
               else dist
          in
          if (VertexMap.mem u adj_u) then
            go (VertexSet.fold f (VertexMap.find u adj_u) dist)
          else go dist
        else go dist
    in go (VertexSet.fold init u VertexMap.empty)

  (* Performs a Depth First Search to perform the
     path alternation of the Hopcroft-Karp algorithm
     Finds the shortest one then flips path and returns
   *)
  let rec dfs u adj_u pair_u pair_v dist dNone du =
    let f v (pair_u, pair_v, b) =
      if b then (pair_u, pair_v, b)
      else
        match VertexMap.find v pair_v with
          None -> if dNone = (du + 1) then
                    (VertexMap.add u (Some v) pair_u), (VertexMap.add v (Some u) pair_v), true
                  else pair_u, pair_v, false
        | Some u ->
           if (VertexMap.find u dist) = (du + 1) then
           begin
             let pair_u, pair_v, b = dfs u adj_u pair_u pair_v dist dNone (du + 1) in
             if b then
               (VertexMap.add u (Some v) pair_u), (VertexMap.add v (Some u) pair_v), true
             else
               pair_u, pair_v, false
           end
           else pair_u, pair_v, false
    in
    if (VertexMap.mem u adj_u) then
      VertexSet.fold f (VertexMap.find u adj_u) (pair_u, pair_v, false)
    else
      pair_u, pair_v, false
             
  (* Implements the Hopcroft-Karp algorithm for finding
     a maximum cardinality bipartite graph matching
     returns the cardinality of the produced matching *)
  let max_matching graph =
    let f v map =
      VertexMap.add v None map
    in
    let pair_u = VertexSet.fold f graph.u (VertexMap.empty) in
    let pair_v = VertexSet.fold f graph.v (VertexMap.empty) in
    let rec go (pair_u, pair_v, matches) =
      let dist, dNone = bfs graph.u graph.adj_u pair_u pair_v in
      if dNone = max_int then
        matches
      else
        let f u (pair_u, pair_v, matches) =
          match VertexMap.find u pair_u with
            None ->
            let (pair_u, pair_v, b) = dfs u graph.adj_u pair_u pair_v dist dNone 0 in
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

  let incident_u g = VertexMap.cardinal g.adj_u
  let incident_v g = VertexMap.cardinal g.adj_v
end
