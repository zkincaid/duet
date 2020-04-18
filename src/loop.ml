module type G = sig
  type t
  module V : sig
    type t
    val compare : t -> t -> int
    val hash : t -> int
    val equal : t -> t -> bool
  end
  val iter_vertex : (V.t -> unit) -> t -> unit
  val iter_succ : (V.t -> unit) -> t -> V.t -> unit
end

module Make(G : G) = struct
  module VertexSet = BatSet.Make(G.V)

  module SubG = struct
    type t =
      { graph : G.t;
        vertices : VertexSet.t }

    module V = G.V

    let iter_vertex f g = VertexSet.iter f g.vertices

    let iter_succ f g v =
      let func s =
        if VertexSet.mem s g.vertices then
          f s
      in
      G.iter_succ func g.graph v

  end
  module SCC = Graph.Components.Make(SubG)

  type loop = {
      header : G.V.t;
      children : forest;
      body : VertexSet.t
    }

  and forest = [ `Vertex of G.V.t | `Loop of loop ] list

  (* Promote a graph to its (trivial) subgraph *)
  let promote g =
    let vertices = ref VertexSet.empty in
    G.iter_vertex
      (fun v -> vertices := VertexSet.add v (!vertices))
      g;
    SubG.{ vertices = !vertices;
           graph = g }

  let loop_nest g =
    let entries = ref VertexSet.empty in
    let add_entry v =
      entries := VertexSet.add v (!entries)
    in
    let rec go g =
      List.fold_left (fun loops scc ->
          match scc with
          | [v] ->
             let self_loop = ref false in
             G.iter_succ (fun s ->
                 add_entry s;
                 if G.V.equal s v then self_loop := true)
               g.SubG.graph
               v;
             if !self_loop then
               let loop =
                 { header = v;
                   children = [];
                   body = VertexSet.singleton v }
               in
               (`Loop loop)::loops
             else
               (`Vertex v)::loops
          | xs ->
             let body = VertexSet.of_list xs in
             let header =
               try
                 VertexSet.enum body
                 |> BatEnum.find (fun v -> VertexSet.mem v (!entries))
               with Not_found ->
                 VertexSet.choose body
             in
             G.iter_succ add_entry g.graph header;
             let children =
               go SubG.{ vertices = VertexSet.remove header body;
                         graph = g.graph }
             in
             (`Loop { header; children; body })::loops)
        []
        (SCC.scc_list g)
    in
    go (promote g)

    (*
  let steensgaard g =
    (* Headers are vertices that have incoming edges from outside the
       loop *)
    let select_headers body g =
      VertexSet.fold (fun v entries ->
          let is_entry = ref false in
          LoopGraph.iter_pred (fun p ->
              if not (VertexSet.mem p body) then
                is_entry := true)
            g
            v;
          if !is_entry then VertexSet.add v entries
          else entries)
        body
        VertexSet.empty
    in
    construct select_headers g

  let havlak g =
    (* Arbitrarily choose a vertex header *)
    let select_headers body g =
      try
        VertexSet.enum body
        |> BatEnum.find (fun v ->
               let is_entry = ref false in
               LoopGraph.iter_pred (fun p ->
                   if not (VertexSet.mem p body) then is_entry := true)
                 g
                 v;
               !is_entry)
        |> VertexSet.singleton
      with Not_found -> assert false
    in
    construct select_headers g
     *)

  let header loop = loop.header

  let body loop = loop.body

  let children loop = loop.children

  let rec all_loops forest =
    List.fold_left
      (fun loops elt -> all_loops_elt elt @ loops)
      []
      forest
  and all_loops_elt = function
    | `Loop loop -> loop :: (all_loops loop.children)
    | `Vertex _ -> []

  let cutpoints forest =
    List.fold_left (fun cutpoints loop ->
        VertexSet.add loop.header cutpoints)
      VertexSet.empty
      (all_loops forest)

  let pp pp_vertex formatter forest =
    let open Format in
    let pp_sep formatter () = fprintf formatter "@;" in
    let pp_enum pp_elt formatter enum =
      SrkUtil.pp_print_enum_nobox ~pp_sep pp_elt formatter enum
    in
    let rec pp_elt formatter = function
      | `Loop loop ->
         fprintf formatter "(@[<v 0>Header:@;  @[<v 0>";
         pp_vertex formatter loop.header;
         fprintf formatter "@]@;Children:@;  @[<v 0>";
         pp_enum pp_elt formatter (BatList.enum loop.children);
         fprintf formatter "@]@])";
      | `Vertex v -> pp_vertex formatter v
    in
    pp_enum pp_elt formatter (BatList.enum forest)
end
