type ('a, 'b) scc =
  { graph : 'b;
    mutable entries : 'a list;
    mutable exits : 'a list;
    mutable backedges : 'a list }

type ('a, 'b) scc_type =
  | Simple of 'a
  | Scc of ('a, 'b) scc

type ('a, 'b) scc_vertex =
  { scc_id : int;
    mutable vtype : ('a, 'b) scc_type }

module type G = sig
  type t
  module V : Graph.Sig.VERTEX
  val iter_vertex : (V.t -> unit) -> t -> unit
  val iter_succ : (V.t -> unit) -> t -> V.t -> unit
  val fold_vertex : (V.t -> 'a -> 'a) -> t -> 'a -> 'a
  val fold_edges : (V.t -> V.t -> 'a -> 'a) -> t -> 'a -> 'a
  val fold_succ : (V.t -> 'a -> 'a) -> t -> V.t -> 'a -> 'a
  val mem_vertex : t -> V.t -> bool
end

module SccGraph (G : G) =
struct
  module rec Vertex
    : (Graph.Sig.VERTEX with type t = (G.V.t, SCCG.t) scc_vertex) =
  struct
    type t = (G.V.t, SCCG.t) scc_vertex
    type label = t
    let compare x y = compare x.scc_id y.scc_id
    let hash x = x.scc_id
    let equal x y = x.scc_id = y.scc_id
    let create x = x
    let label x = x
  end
  and SCCG : Graph.Sig.P with type V.t = Vertex.t =
    Graph.Persistent.Digraph.Concrete(Vertex)

  module PG = ExtGraph.PersistentCopy.Digraph(G)

  module C = Graph.Components.Make(PG)
  include SCCG
  module Top = Graph.Topological.Make(SCCG)
  module VSet = Set.Make(G.V)
  let construct g =
    let extract_vertex g =
      match PG.fold_vertex (fun v x -> Some v) g None with
      | Some v -> v
      | None -> failwith "Loop.extract_vertex: empty graph!"
    in
    let rec go g =
      let (nb_components, component) = C.scc g in
      let component_graph = Array.make nb_components PG.empty in
      let entries = Array.make nb_components VSet.empty in
      let exits = Array.make nb_components VSet.empty in
      let edges = Array.make nb_components [] in
      let addva array index v =
        array.(index) <- VSet.add v array.(index)
      in
      let add_vertex v =
        let cv = component v in
        component_graph.(cv) <- PG.add_vertex component_graph.(cv) v
      in
      let add_edge u v =
        let cu = component u in
        let cv = component v in
        if cu = cv
        then component_graph.(cu) <- PG.add_edge component_graph.(cu) u v
        else begin
          addva exits cu u;
          addva entries cv v;
          edges.(cu) <- cv::(edges.(cu))
        end
      in
      PG.iter_vertex add_vertex g;
      PG.iter_edges add_edge g;
      let init_vertex i =
        let vtype =
          if PG.nb_edges component_graph.(i) > 0 then begin

            (* If a component has no incoming entry vertices, select an
               		 arbitrary one to be the entry. *)
            if VSet.cardinal entries.(i) = 0 then begin
              let v = extract_vertex component_graph.(i) in
              entries.(i) <- VSet.singleton v
            end;

            (* Remove edges coming into the entry vertices, so that "cut" is
               		 no longer strongly connected, then recursively decompose
               		 cut *)
            let backedges = ref VSet.empty in
            let remove_backedge v p g =
              backedges := VSet.add p (!backedges);
              PG.remove_edge g p v
            in
            let f v g = PG.fold_pred (remove_backedge v) g v g in

            let cut = VSet.fold f entries.(i) component_graph.(i) in
            Scc { graph = go cut;
                  entries = VSet.elements entries.(i);
                  exits = VSet.elements exits.(i);
                  backedges = VSet.elements (!backedges) }
          end
          else Simple (extract_vertex component_graph.(i))
        in
        { scc_id = i;
          vtype = vtype }
      in
      let vertices = Array.init nb_components init_vertex in
      let sccg = Array.fold_left SCCG.add_vertex SCCG.empty vertices in
      let fold_edges f acc =
        BatArray.fold_lefti
          (fun g i succs -> List.fold_left (fun g -> f g i) g succs)
          acc
          edges
      in
      let add_edge g i j =
        SCCG.add_edge g vertices.(i) vertices.(j)
      in
      fold_edges add_edge sccg
    in
    go (PG.copy g)

  (** Display an SCC graph with boxes around each SCC *)
  let output_scc_graph vertex_string ch g =
    let emit s = output_string ch (s ^ "\n") in
    let max_region = ref 0 in
    let vstring v = "\"" ^ (vertex_string v) ^ "\"" in
    let next_cluster () =
      let id = !max_region in
      max_region := id + 1;
      "cluster" ^ (string_of_int id)
    in
    let pick_entry v =
      match v.vtype with
      | Scc c -> List.hd c.entries
      | Simple x -> x
    in
    let pick_exit v =
      match v.vtype with
      | Scc c -> List.hd c.exits
      | Simple x -> x
    in
    let rec go g =
      let emit_vertex v =
        match v.vtype with
        | Scc c ->
          emit ("subgraph " ^ (next_cluster ()) ^ "{");
          go c.graph;
          emit "}"
        | Simple v -> emit ((vstring v) ^ ";")
      in
      let emit_edge u v =
        emit (((vstring (pick_exit u)) ^ " -> " ^ (vstring (pick_entry v))))
      in
      SCCG.iter_vertex emit_vertex g;
      SCCG.iter_edges emit_edge g
    in
    emit "digraph G {";
    emit "compound = true;";
    go g;
    emit "}";
    ()

  let display_scc g vertex_string =
    ExtGraph.display_dot (output_scc_graph vertex_string) g
  let is_header g =
    let rec get_headers g = SCCG.fold_vertex f g VSet.empty
    and f v headers =
      match v.vtype with
      | Simple x -> headers
      | Scc scc ->
        let headers = VSet.union headers (get_headers scc.graph) in
        List.fold_right VSet.add scc.entries headers
    in
    let headers = get_headers g in
    fun v -> VSet.mem v headers

  let rec enum_headers g =
    let f v rest =
      match v.vtype with
      | Simple _ -> rest
      | Scc scc ->
        BatEnum.append rest
          (BatEnum.append
             (BatList.enum scc.entries)
             (BatEnum.delay (fun () -> enum_headers scc.graph)))
    in
    SCCG.fold_vertex f g (BatEnum.empty ())

  let (fold_inside_out : (G.V.t -> 'a -> 'a) -> G.t -> 'a -> 'a) = fun f g a ->
    let sccg = construct g in
    let is_header = is_header sccg in
    let rec go_simple v a = match v.vtype with
      | Simple x -> if is_header x then a else f x a
      | Scc _ -> a
    and go_scc v a = match v.vtype with
      | Simple _ -> a
      | Scc scc ->
        let res =
          Top.fold go_simple scc.graph
            (SCCG.fold_vertex go_scc scc.graph a)
        in
        List.fold_left (fun a x -> f x a) res scc.entries
    in
    Top.fold go_simple sccg (SCCG.fold_vertex go_scc sccg a)

end

module SccInfo = struct
  module type G = sig
    type t
    module V : Graph.Sig.VERTEX

    val iter_vertex : (V.t -> unit) -> t -> unit
    val iter_succ : (V.t -> unit) -> t -> V.t -> unit
    val iter_pred : (V.t -> unit) -> t -> V.t -> unit
  end
  module Make (G : G) = struct
    open BatPervasives

    module C = Graph.Components.Make(G)
    module VSet = BatSet.Make(G.V)

    type t = int * VSet.t
    module Compare_t = struct
      type a = t
      let compare (a,_) (b,_) = Pervasives.compare a b
    end
    let compare = Compare_t.compare
    let hash = Hashtbl.hash
    let equal (a,_) (b,_) = a = b

    let mem v (_,vs) = VSet.mem v vs
    let enum (_,vs) = VSet.enum vs

    let scc g =
      let f i vs = (i, VSet.of_enum (BatList.enum vs)) in
      BatEnum.mapi f (BatList.enum (C.scc_list g))

    let scc_map g =
      let (size, map) = C.scc g in
      let m = Array.make size VSet.empty in
      let f v =
        let i = map v in
        m.(i) <- VSet.add v m.(i)
      in
      let lookup v =
        let i = map v in
        (i, m.(i))
      in
      G.iter_vertex f g;
      (size, lookup)

    let exists_succ p g v =
      let ex = ref false in
      G.iter_succ (fun u -> ex := (!ex) || p u) g v;
      !ex

    let exists_pred p g v =
      let ex = ref false in
      G.iter_pred (fun u -> ex := (!ex) || p u) g v;
      !ex

    let count_succ p g v =
      let count = ref 0 in
      G.iter_succ (fun u -> if p u then incr count) g v;
      !count

    let count_pred p g v =
      let count = ref 0 in
      G.iter_pred (fun u -> if p u then incr count) g v;
      !count

    let is_sink g (_,c) =
      not (VSet.exists (exists_succ (not % flip VSet.mem c) g) c)
    let is_source g (_,c) =
      not (VSet.exists (exists_pred (not % flip VSet.mem c) g) c)

    let in_degree g (_,c) =
      VSet.fold (fun v a -> a + (count_pred (not % flip VSet.mem c) g v)) c 0
    let out_degree g (_,c) =
      VSet.fold (fun v a -> a + (count_succ (not % flip VSet.mem c) g v)) c 0
    let degree g (_,c) =
      let outside = not % flip VSet.mem c in
      let f v a = a + (count_pred outside g v) + (count_succ outside g v)in
      VSet.fold f c 0

    let sinks g = BatEnum.filter (is_sink g) (scc g)
    let sources g = BatEnum.filter (is_source g) (scc g)

    let component_entries g (_,scc) =
      let f v vs =
        if exists_pred (not % flip VSet.mem scc) g v then v::vs else vs
      in
      VSet.fold f scc []

    let component_exits g (_,scc) =
      let f v vs =
        if exists_succ (not % flip VSet.mem scc) g v then v::vs else vs
      in
      VSet.fold f scc []

    let component_internals g (_,scc) =
      let outside = not % flip VSet.mem scc in
      let f v vs =
        if not (exists_succ outside g v || exists_pred outside g v) then v::vs
        else vs
      in
      VSet.fold f scc []

    let entries g =
      let f scc = (component_entries g scc, scc) in
      BatEnum.map f (scc g)

    let exits g =
      let f scc = (component_exits g scc, scc) in
      BatEnum.map f (scc g)
  end
end

type 'a loop_nest =
  { body : 'a;
    headers : 'a;
    children : 'a loop_nest list }

(** Weak topological order element *)
type 'a wto_elt =
  | WSimple of 'a
  | WLoop of ('a wto_elt) list

(** Weak topological order *)
type 'a wto = ('a wto_elt) list

(** Compute weak topological orders *)
module Wto (G : G) = struct
  module SCCG = SccGraph(G)
  module Top = Graph.Topological.Make(SCCG)
  let rec from_sccg g =
    let wto_elt v = match v.vtype with
      | Simple x -> WSimple x
      | Scc g -> WLoop (from_sccg g.graph)
    in
    List.rev (Top.fold (fun v wto -> (wto_elt v)::wto) g [])

  let create g = from_sccg (Log.time "WTO computation" SCCG.construct g)
  let create_widening g =
    let sccg = Log.time "WTO computation" SCCG.construct g in
    (from_sccg sccg, SCCG.is_header sccg)
end

let rec pp_wto pp_elt formatter wto =
  let rec pp_item formatter = function
    | WSimple x -> Format.fprintf formatter "%a@;" pp_elt x
    | WLoop xs  ->
      Format.fprintf formatter "[@[%a@]]" (Putil.pp_print_list pp_item) wto
  in
  Format.fprintf formatter "[@[%a@]]" (Putil.pp_print_list pp_item) wto
