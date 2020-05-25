open Pathexpr

include Log.Make(struct let name = "srk.weightedGraph" end)

module U = Graph.Persistent.Digraph.ConcreteBidirectional(SrkUtil.Int)
module L = Loop.Make(U)

module IntPair = struct
  type t = int * int [@@deriving ord, eq]
  let hash = Hashtbl.hash
end

module M = BatMap.Make(IntPair)

type 'a algebra =
  { mul : 'a -> 'a -> 'a;
    add : 'a -> 'a -> 'a;
    star : 'a -> 'a;
    zero : 'a;
    one : 'a }

type ('a,'b) omega_algebra =
  { omega : 'a -> 'b;
    omega_add : 'b -> 'b -> 'b;
    omega_mul : 'a -> 'b -> 'b }

type 'a weighted_graph =
  { graph : U.t;
    labels : 'a M.t;
    algebra : 'a algebra }

type 'a t = 'a weighted_graph

type vertex = int

(* Check invariant: 1-to-1 correspondence between labels & edges *)
let _sat_inv wg =
  (M.for_all (fun (u,v) _ -> U.mem_edge wg.graph u v) wg.labels)
  && U.fold_edges (fun u v b -> b && M.mem (u,v) wg.labels) wg.graph true

let empty algebra =
  { graph = U.empty;
    labels = M.empty;
    algebra = algebra }

let add_vertex wg vertex =
  { wg with graph = U.add_vertex wg.graph vertex }

let edge_weight_opt wg u v =
  try Some (M.find (u, v) wg.labels)
  with Not_found -> None

let edge_weight wg u v =
  try M.find (u, v) wg.labels
  with Not_found -> wg.algebra.zero

let add_edge wg u weight v =
  if M.mem (u, v) wg.labels then
    let labels' = M.modify (u, v) (wg.algebra.add weight) wg.labels in
    { wg with labels = labels' }
  else
    { wg with graph = U.add_edge wg.graph u v;
              labels = M.add (u, v) weight wg.labels }

let remove_vertex wg u =
  let labels =
    U.fold_succ
      (fun v labels -> M.remove (u, v) labels)
      wg.graph
      u
      (U.fold_pred
         (fun v labels -> M.remove (v, u) labels)
         wg.graph
         u
         wg.labels)
  in
  { wg with graph = U.remove_vertex wg.graph u;
            labels = labels }

let remove_edge wg u v =
  { wg with graph = U.remove_edge wg.graph u v;
            labels = M.remove (u, v) wg.labels }

let fold_incident_edges f graph v acc =
  U.fold_succ
    (fun u acc -> f (v, u) acc)
    graph
    v
    (U.fold_pred
       (fun u acc -> if u == v then acc else f (u, v) acc)
       graph
       v
       acc)

(* Rename vertex u to w.  If w already exists in the graph, then all
   of the incident edges of u become incident to w instead (and u is
   removed). *)
let rename_vertex wg u w =
  let g' = U.add_vertex (U.remove_vertex wg.graph u) w in
  let rename v = if v = u then w else v in
  fold_incident_edges (fun (v,v') wg ->
      let (weight, labels) = M.extract (v, v') wg.labels in
      let graph' =
        U.add_edge wg.graph (rename v) (rename v')
      in
      let labels' =
        M.add (rename v, rename v') weight labels
      in
        { wg with graph = graph'; labels = labels' })
    wg.graph
    u
    { wg with graph = g' }

let contract_vertex wg v =
  (* List of all { (s, w(v,v)*w(v,s)) : (v,s) in E } *)
  let star x = wg.algebra.star x in
  let mul x y = wg.algebra.mul x y in
  let loop_succ =
    let loop =
      try star (M.find (v, v) wg.labels)
      with Not_found -> wg.algebra.one
    in
    U.fold_succ (fun u succs ->
        if u = v then
          succs
        else
          (u, mul loop (M.find (v, u) wg.labels))::succs)
      wg.graph
      v
      []
  in
  U.fold_pred (fun pred wg' ->
      if pred = v then
        wg'
      else
        let pw = edge_weight wg pred v in
        List.fold_left (fun wg' (succ, sw) ->
            add_edge wg' pred (mul pw sw) succ)
          wg'
          loop_succ)
    wg.graph
    v
    (remove_vertex wg v)

let max_vertex wg = U.fold_vertex max wg.graph 0

let path_weight wg src tgt =
  let start = max_vertex wg + 1 in
  let final = start + 1 in
  let one = wg.algebra.one in
  let contracted_graph =
    let g = add_vertex wg start in
    let g = add_vertex g final in
    let g = add_edge g start one src in
    let g = add_edge g tgt one final in
    let rec go g elt =
      match elt with
      | `Vertex v -> contract_vertex g v
      | `Loop loop ->
        let g = List.fold_left go g (L.children loop) in
        contract_vertex g (L.header loop)
    in
    List.fold_left go g (L.loop_nest wg.graph)
  in
  match edge_weight_opt contracted_graph start final with
  | None -> wg.algebra.zero
  | Some w -> w

let msat_path_weight wg srcs =
  (* For each source vertex s, augment the graph with a fresh vertex
     s' and an edge s' -> s with weight 1.  After bypassing all
     vertices in the original graph, the edges leaving s' correspond
     to paths leaving s. *)
  let start = max_vertex wg + 1 in
  let wg' =
    List.fold_left (fun (wg, next) src ->
        let wg = add_vertex wg next in
        let wg = add_edge wg next wg.algebra.one src in
        (wg, next + 1))
      (wg, start)
      srcs
    |> fst
  in

  (* Contract the successor edges of a vertex.  In the resulting
     graph, v has no outgoing edges but all paths that don't begin at
     v are preserved. *)
  let bypass_vertex wg v =
    let mul = wg.algebra.mul in
    (* If v has a loop, remove it and shift its weight to v's
       predecessors *)
    let wg =
      if M.mem (v, v) wg.labels then begin
          let loop = wg.algebra.star (M.find (v,v) wg.labels) in
          let wg = remove_edge wg v v in
          let labels' =
            U.fold_pred (fun p labels ->
                M.modify (p, v) (fun w -> mul w loop) labels)
              wg.graph
              v
              wg.labels
          in
          { wg with labels = labels' }
        end
      else wg
    in

    (* For each successor s of v, connect s to all predecessors of v
       and remove the s->v edge *)
    let predecessors = (* Save predecessor edges to avoid repeated lookups *)
      List.map (fun p -> (p, edge_weight wg p v)) (U.pred wg.graph v)
    in

    U.fold_succ (fun s wg ->
        let v_to_s = edge_weight wg v s in
        List.fold_left (fun wg (p, p_to_v) ->
            add_edge wg p (mul p_to_v v_to_s) s)
          (remove_edge wg v s)
          predecessors)
      wg.graph
      v
      wg
  in
  let rec go wg elt =
    match elt with
    | `Vertex v -> bypass_vertex wg v
    | `Loop loop ->
       let wg = List.fold_left go wg (L.children loop) in
       bypass_vertex wg (L.header loop)
  in
  let wg' = List.fold_left go wg' (L.loop_nest wg.graph) in
  List.fold_left (fun (wg, next) src ->
      let wg = rename_vertex wg next src in
      (wg, next + 1))
    (wg', start)
    srcs
  |> fst

let omega_path_weight
      (wg : 'a t)
      (omega : ('a,'b) omega_algebra)
      (src : vertex) =
  let start = max_vertex wg + 1 in

  (* Each vertex v is associated with the sum of the weights of all
     omega paths beginning at v that *only* pass through contracted
     vertices. *)
  let omega_weights = BatHashtbl.create 991 in
  let add_omega v weight =
    if BatHashtbl.mem omega_weights v then
      BatHashtbl.modify v (omega.omega_add weight) omega_weights
    else
      BatHashtbl.add omega_weights v weight
  in
  let contract_vertex g v =
    (* If there are omega paths starting at v, when v is contracted
       those omega paths now begin at v's predecessors *)
    if M.mem (v, v) g.labels || BatHashtbl.mem omega_weights v then
      begin
        let loop =
          (* Try to avoid omega addition if possible *)
          try
            let self_loop = omega.omega (M.find (v, v) g.labels) in
            (try omega.omega_add (BatHashtbl.find omega_weights v) self_loop
             with Not_found -> self_loop)
          with Not_found ->
            BatHashtbl.find omega_weights v
        in
        U.iter_pred (fun pred ->
            if pred != v then
              let pw = edge_weight g pred v in
              add_omega pred (omega.omega_mul pw loop))
          g.graph
          v
      end;
    contract_vertex g v
  in
  let g = add_vertex wg start in
  let g = add_edge g start wg.algebra.one src in
  let rec go g elt =
    match elt with
    | `Vertex v -> contract_vertex g v
    | `Loop loop ->
       let header = L.header loop in
       let g = List.fold_left go g (L.children loop) in
       (* Contract v, then add v back the the graph along with
          predecessor edges *)
       U.fold_pred (fun pred g' ->
           add_edge g' pred (edge_weight g pred header) header)
         g.graph
         header
         (contract_vertex g header)
  in
  ignore (List.fold_left go g (L.loop_nest wg.graph));
  try
    BatHashtbl.find omega_weights start
  with Not_found -> omega.omega wg.algebra.zero

let split_vertex wg u weight v =
  U.fold_succ (fun w wg ->
      let (uw, labels) = M.extract (u, w) wg.labels in
      { wg with graph = U.add_edge (U.remove_edge wg.graph u w) v w;
                labels = M.add (v, w) uw labels })
    wg.graph
    u
    { wg with graph = U.add_edge wg.graph u v;
              labels = M.add (u, v) weight wg.labels }

let forget_weights wg = wg.graph

let map_weights f wg =
  { wg with labels = M.mapi (fun (u,v) w -> f u w v) wg.labels }

let fold_edges f wg acc =
  M.fold (fun (u,v) w acc ->
      f (u, w, v) acc)
    wg.labels
    acc

let iter_edges f wg =
  M.iter (fun (u, v) w -> f (u, w, v)) wg.labels

let fold_pred_e f wg v =
  U.fold_pred
    (fun u acc -> f (u, edge_weight wg u v, v) acc)
    wg.graph
    v

let fold_succ_e f wg u =
  U.fold_succ
    (fun v acc -> f (u, edge_weight wg u v, v) acc)
    wg.graph
    u

let iter_pred_e f wg v =
  U.iter_pred
    (fun u -> f (u, edge_weight wg u v, v))
    wg.graph
    v

let iter_succ_e f wg u =
  U.iter_succ
    (fun v -> f (u, edge_weight wg u v, v))
    wg.graph
    u

let fold_vertex f wg = U.fold_vertex f wg.graph
let iter_vertex f wg = U.iter_vertex f wg.graph
let mem_edge wg u v = M.mem (u, v) wg.labels

(* Cut graph reduces a weighted graph to only those vertices in c, while preserving all weighted paths between pairs of vertices in c *)
let cut_graph wg c =
  let module Set = SrkUtil.Int.Set in
  let cut_set = Set.of_list c in
  let pre_vertex v = v in
  let post_vertex =
     let max = Set.fold max cut_set (max_vertex wg) + 1 in
     Memo.memo (fun v -> if Set.mem v cut_set then v + max else v)
  in
  let path_graph =
    let pg = Set.fold (fun v pg -> add_vertex (add_vertex pg (pre_vertex v)) (post_vertex v)) cut_set (empty wg.algebra) in
    let pg = fold_vertex (fun v pg -> add_vertex pg v) wg pg in
    fold_edges (fun (u, w, v) pg -> add_edge pg (pre_vertex u) w (post_vertex v)) wg pg
  in
  Set.fold (fun u cg ->
    Set.fold (fun v cg ->
      add_edge (add_vertex cg v) u (path_weight path_graph (pre_vertex u) (post_vertex v)) v
    ) cut_set (add_vertex cg u)
  ) cut_set (empty wg.algebra)

(* Line graphs swaps vertices and edges *)
module LineGraph = struct
  type t = U.t
  module V = IntPair
  let iter_vertex f graph = U.iter_edges (fun x y -> f (x, y)) graph
  let iter_succ f graph (_, dst) =
    U.iter_succ
      (fun succ -> f (dst, succ))
      graph
      dst
end
module LGLoop = Loop.Make(LineGraph)

let forward_analysis wg ~entry ~update ~init =
  let data_table = Hashtbl.create 991 in
  let get_data v =
    try Hashtbl.find data_table v
    with Not_found ->
      let data = init v in
      Hashtbl.add data_table v data;
      data
  in
  let set_data v data =
    Hashtbl.replace data_table v data;
  in

  let module ESet = LGLoop.VertexSet in
  let update_edge work ((src, dst) as e) =
    if ESet.mem e work then
      let work = ESet.remove e work in
      let weight = edge_weight wg src dst in
      match update ~pre:(get_data src) weight ~post:(get_data dst) with
      | Some data ->
        set_data dst data;
        U.fold_succ_e ESet.add wg.graph dst work
      | None -> work
    else
      work
  in
  let rec solve work loop_nest =
    match loop_nest with
    | `Vertex e -> update_edge work e
    | `Loop loop ->
      let cmp_edges = LGLoop.body loop in
      let rec fix work =
        let work =
          List.fold_left
            solve
            (update_edge work (LGLoop.header loop))
            (LGLoop.children loop)
        in
        if ESet.exists (fun e -> ESet.mem e work) cmp_edges then
          fix work
        else
          work
      in
      fix work
  in

  (* Add an artificial edge to act as the entry point to the line
     graph of graph. Don't add to the initial worklist, so update will
     never be called on the artifical edge.  *)
  let init_vertex = max_vertex wg + 1 in
  let graph' = U.add_edge wg.graph init_vertex entry in

  ignore (List.fold_left
            solve
            (U.fold_succ_e ESet.add wg.graph entry ESet.empty)
            (LGLoop.loop_nest graph'));

  get_data

module RecGraph = struct
  module HT = BatHashtbl.Make(IntPair)
  module CallSet = BatSet.Make(IntPair)
  module VertexSet = SrkUtil.Int.Set
  module CallGraph = struct
    type t = CallSet.t M.t
    module V = IntPair
    let iter_vertex f callgraph =
      M.iter (fun k _ -> f k) callgraph
    let iter_succ f callgraph v =
      CallSet.iter f (M.find v callgraph)
    let add_vertex callgraph v =
      if M.mem v callgraph then
        callgraph
      else
        M.add v CallSet.empty callgraph
    let add_edge callgraph u v =
      let callgraph = add_vertex callgraph v in
      if M.mem u callgraph then
        M.add u (CallSet.add v (M.find u callgraph)) callgraph
      else
        M.add u (CallSet.singleton v) callgraph
    let empty = M.empty
  end

  type call = vertex * vertex

  type t =
    { path_graph : Pathexpr.simple Pathexpr.t weighted_graph;
      call_edges : call M.t;
      context : Pathexpr.context }

  type query =
    { recgraph : t;

      (* The intraprocedural path graph has an edge u->v for
         each entry vertex u and each vertex v reachable from u,
         weighted with a path expression for the paths from u to v. *)
      intraproc_paths : Pathexpr.simple Pathexpr.t weighted_graph;

      (* The interprocedural graph has entries as vertices, and each
         edge u->v is weighted by a path expression recognizing all
         paths from u to an call edge (v, _) *)
      interproc : Pathexpr.nested Pathexpr.t weighted_graph;

      (* The interprocedural path graph has an edge src->v for each
         entry vertex v weighted by a path expression for the paths in
         the interprocedural graph from src to v *)
      interproc_paths : Pathexpr.nested Pathexpr.t weighted_graph;

      src : vertex (* designated source vertex *) }

  (* The memo table and algebra of a weighted query should not be
     accessed directly -- the memo table becomes stale when summaries
     are updated.  Use the "prepare" function to fix the memo table
     and get an algebra that also provides an interpretation for call
     edges. *)
  type 'a weight_query =
    { query : query;
      summaries : 'a HT.t; (* Map calls to their summaries *)

      (* Memo table mapping path expressions to their weights *)
      table : 'a Pathexpr.table;

      (* Calls whose summaries have changed since they were last
         evaluated *)
      changed : CallSet.t ref;

      (* An algebra for assigning weights to non-call edges and *)
      algebra : 'a Pathexpr.nested_algebra }

  let pathexpr_algebra context =
    { mul = mk_mul context;
      add = mk_add context;
      star = mk_star context;
      zero = mk_zero context;
      one = mk_one context }

  let fold_reachable_edges f g v acc =
    let visited = ref VertexSet.empty in
    let rec go u acc =
      U.fold_succ (fun v acc ->
          let acc = f u v acc in
          if not (VertexSet.mem v !visited) then begin
              visited := VertexSet.add v (!visited);
              go v acc
            end
          else acc)
        g.graph
        u
        acc
    in
    go v acc

  let mk_query rg src =
    (* All calls that appear on a call edge *)
    let callset =
      M.fold (fun _ call callset ->
          CallSet.add call callset)
        rg.call_edges
        CallSet.empty
    in
    let sources =
      CallSet.fold (fun (src, _) -> VertexSet.add src) callset VertexSet.empty
      |> VertexSet.add src
      |> VertexSet.elements
    in
    let intraproc_paths = msat_path_weight rg.path_graph sources in
    let interproc =
      let intraproc_paths = edge_weight intraproc_paths in
      List.fold_left (fun interproc_graph src ->
          fold_reachable_edges (fun u v interproc_graph ->
              try
                let (en,_) = M.find (u,v) rg.call_edges in
                let pathexpr =
                  mk_segment rg.context (intraproc_paths src u)
                in
                add_edge interproc_graph src pathexpr en
              with Not_found -> interproc_graph)
            rg.path_graph
            src
            (add_vertex interproc_graph src))
        (empty (pathexpr_algebra rg.context))
        sources
    in
    { recgraph = rg;
      intraproc_paths = intraproc_paths;
      interproc = interproc;
      interproc_paths = msat_path_weight interproc [src];
      src = src }

  let call_pathexpr query (src, tgt) =
    (* intraproc_paths is only set when src is an entry vertex *)
    if not (U.mem_vertex query.interproc.graph src) then
      invalid_arg "call_weight: unknown call";
    edge_weight query.intraproc_paths src tgt

  let mk_callgraph query =
    (* If there is a call to (s,t) between s' and t', add a dependence
       edge from (s',t') to (s,t) *)
    let callset =
      (* All calls that appear on a call edge *)
      M.fold
        (fun _ call callset -> CallSet.add call callset)
        query.recgraph.call_edges
        CallSet.empty
    in
    (* Collect the set of calls that appear in a path expression *)
    let callset_algebra = function
      | `Edge e ->
         begin try
             CallSet.singleton (M.find e query.recgraph.call_edges)
           with Not_found -> CallSet.empty
         end
      | `Mul (x, y) | `Add (x, y) -> CallSet.union x y
      | `Star x -> x
      | `Zero | `One -> CallSet.empty
    in
    let table = mk_table () in
    CallSet.fold (fun call callgraph ->
          CallGraph.add_vertex callgraph call)
        callset
        CallGraph.empty
    |> CallSet.fold (fun (en, ex) callgraph ->
           let pathexpr = edge_weight query.intraproc_paths en ex in
           CallSet.fold (fun target callgraph ->
               CallGraph.add_edge callgraph target (en, ex))
             (eval ~table ~algebra:callset_algebra pathexpr)
             callgraph)
         callset

  let mk_omega_algebra context =
    { omega = mk_omega context;
      omega_add = mk_omega_add context;
      omega_mul = mk_omega_mul context }

  let omega_pathexpr (query : query) =
    let context = query.recgraph.context in
    let omega_algebra =mk_omega_algebra context in
    let omega_inter_algebra = mk_omega_algebra context in
    fold_vertex (fun entry w ->
        let src_entry =
          edge_weight query.interproc_paths query.src entry
        in
        let entry_omega =
          omega_path_weight query.recgraph.path_graph omega_algebra entry
          |> Pathexpr.promote_omega
        in
        let src_entry_omega =
          Pathexpr.mk_omega_mul query.recgraph.context src_entry entry_omega
        in
        Pathexpr.mk_omega_add context w src_entry_omega)
      query.interproc_paths
      (omega_path_weight query.interproc omega_inter_algebra query.src)

  let pathexpr query tgt =
    (* The interprocedural path weight to tgt is the sum over all
       entries of an interprocedural path from src to entry * an
       intraprocedural path from entry to tgt *)
    let context = query.recgraph.context in
    U.fold_pred (fun entry w ->
        if U.mem_edge query.interproc_paths.graph query.src entry then
          let src_entry_tgt =
            Pathexpr.mk_mul
              context
              (edge_weight query.interproc_paths query.src entry)
              (Pathexpr.promote (edge_weight query.intraproc_paths entry tgt))
          in
          Pathexpr.mk_add context w src_entry_tgt
        else w)
      query.intraproc_paths.graph tgt (Pathexpr.mk_zero context)

  exception No_summary of call

  (* Prepare memo table & algebra for a weight query *)
  let prepare (q : 'a weight_query) =
    let call_edges = q.query.recgraph.call_edges in
    let changed = !(q.changed) in
    let algebra = function
      | `Edge (s, t) when M.mem (s, t) call_edges ->
         let call = M.find (s, t) call_edges in
         (try HT.find q.summaries call
          with Not_found -> raise (No_summary call))
      | e -> q.algebra e
    in
    if not (CallSet.is_empty changed) then begin
        forget q.table (fun s t ->
            try not (CallSet.mem (M.find (s, t) call_edges) changed)
            with Not_found -> true);
        q.changed := CallSet.empty
      end;
    (q.table, algebra)

  let get_summary query call =
    try HT.find query.summaries call
    with Not_found -> raise (No_summary call)

  let set_summary query call weight =
    query.changed := CallSet.add call !(query.changed);
    HT.replace query.summaries call weight

  let mk_weight_query query algebra =
    { query = query;
      summaries = HT.create 991;
      changed = ref CallSet.empty;
      table = Pathexpr.mk_table ();
      algebra = algebra }

  let path_weight query tgt =
    let (table, algebra) = prepare query in
    Pathexpr.eval_nested ~table ~algebra (pathexpr query.query tgt)

  let call_weight query (src, tgt) =
    let (table, algebra) = prepare query in
    Pathexpr.eval ~table ~algebra (call_pathexpr query.query (src, tgt))

  let omega_path_weight query omega_algebra =
    let (table, algebra) = prepare query in
    let omega_table = Pathexpr.mk_omega_table table in
    let paths = omega_pathexpr query.query in
    Pathexpr.eval_omega ~table:omega_table ~algebra ~omega_algebra paths

  let empty () =
    let context = mk_context () in
    let algebra =
      { mul = mk_mul context;
        add = mk_add context;
        star = mk_star context;
        zero = mk_zero context;
        one = mk_one context }
    in
    { path_graph = empty algebra;
      call_edges = M.empty;
      context = context }

  let add_call_edge rg u call v =
    { rg with path_graph = add_edge rg.path_graph u (mk_edge rg.context u v) v;
              call_edges = M.add (u,v) call rg.call_edges }

  let add_edge rg u v =
    { rg with path_graph = add_edge rg.path_graph u (mk_edge rg.context u v) v }

  let add_vertex rg v =
    { rg with path_graph = add_vertex rg.path_graph v }
end

module SummarizeIterative (D : sig
             type weight
             type abstract_weight
             val abstract : weight -> abstract_weight
             val concretize : abstract_weight -> weight
             val equal : abstract_weight -> abstract_weight -> bool
             val widen : abstract_weight -> abstract_weight -> abstract_weight
           end) = struct

  type query = D.weight RecGraph.weight_query

  module CallGraph = RecGraph.CallGraph
  module CallGraphLoop = Loop.Make(CallGraph)
  module HT = BatHashtbl.Make(IntPair)

  let mk_query ?(delay=1) rg src algebra =
    let path_query = RecGraph.mk_query rg src in
    let weight_query = RecGraph.mk_weight_query path_query algebra in
    let callgraph = RecGraph.mk_callgraph path_query in
    let project x = algebra (`Segment x) in
    let abstract_summaries = HT.create 991 in
    (* stabilize summaries within a WTO component, and add to unstable
       all calls whose summary (may have) changed as a result. *)
    let rec fix = function
      | `Vertex call ->
         RecGraph.call_weight weight_query call
         |> project
         |> RecGraph.set_summary weight_query call

      | `Loop loop ->
         let header = CallGraphLoop.header loop in
         let rec fix_component delay =
           let old_abs_weight = HT.find abstract_summaries header in
           let (new_abs_weight, new_weight) =
             let new_weight =
               project (RecGraph.call_weight weight_query header)
             in
             let new_abs_weight = D.abstract new_weight in
             if delay > 0 then
               (new_abs_weight, new_weight)
             else
               let new_abs_weight = D.widen old_abs_weight new_abs_weight in
               let new_weight = D.concretize new_abs_weight in
               (new_abs_weight, new_weight)
           in
           HT.replace abstract_summaries header new_abs_weight;
           RecGraph.set_summary weight_query header new_weight;
           List.iter fix (CallGraphLoop.children loop);
           if not (D.equal old_abs_weight new_abs_weight)
           then fix_component (delay - 1)
         in
         fix_component delay
    in
    let zero = algebra `Zero in
    let abstract_zero = D.abstract zero in
    callgraph
    |> CallGraph.iter_vertex (fun call ->
           RecGraph.set_summary weight_query call zero;
           HT.add abstract_summaries call abstract_zero);
    List.iter fix (CallGraphLoop.loop_nest callgraph);
    weight_query
end
