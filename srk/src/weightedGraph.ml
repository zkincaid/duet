open Pathexpr

include Log.Make(struct let name = "srk.weightedGraph" end)

module U = Graph.Persistent.Digraph.ConcreteBidirectional(SrkUtil.Int)
module L = Loop.Make(U)
module D = Graph.Dominator.Make(U)
module C = Graph.Components.Make(U)

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

let omega_trivial =
  { omega = (fun _ -> ());
    omega_add = (fun _ _ -> ());
    omega_mul = (fun _ _ -> ()) }

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
let _rename_vertex wg u w =
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

(* Contract edges in the graph, preserving path weight from src to
   every other vertex.  Remaining edges start at src or are a
   self-loop. *)
let _solve_dense (wg : 'a weighted_graph) (src : vertex) =
  let mul = wg.algebra.mul in
  (* Contract the successor edges of a vertex, except self-loops. *)
  let bypass_vertex wg v =
    if v = src then
      wg
    else
      let predecessors =
        let mul_loop =
          if M.mem (v, v) wg.labels then
            let loop = wg.algebra.star (M.find (v,v) wg.labels) in
            (fun x -> mul x loop)
          else
            (fun x -> x)
        in
        BatList.filter_map (fun p ->
            if p = v then None
            else Some (p, mul_loop (edge_weight wg p v)))
          (U.pred wg.graph v)
      in
      (* For each succesor s of v, connect s to all predecessors of v
         and remove the s->v edge *)
      U.fold_succ (fun s wg ->
          if s = v then
            wg
          else
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
  List.fold_left go wg (L.loop_nest wg.graph)

(* Main logic for single-source multi-target path weights and omega
   path weights.  The algorithm is a variation of Tarjan's algorithm
   from "Fast Algorithms for Solving Path Problems", JACM '81.
   Returns a triple (omega_weight, path_weight, reachable), where
   omega_weight is the sum of weights of all omega paths starting at
   src, path_weight v is the sum of weights of all paths from src to
   v, and reachable is an enumeration of the vertices reachable from
   src.  *)
let _path_weight
      (wg : 'a t)
      (omega : ('a, 'b) omega_algebra)
      (src : vertex) =
  (* Ensure that src has no incoming edges *)
  let (wg, src) =
    let start = max_vertex wg + 1 in
    (add_edge (add_vertex wg start) start wg.algebra.one src, start)
  in

  let module F = CompressedWeightedForest in
  let mul = wg.algebra.mul in
  let one = wg.algebra.one in
  let star = wg.algebra.star in
  let forest =
    F.create ~mul:(fun x y -> mul y x) ~one
  in
  let wg_to_forest = BatHashtbl.create 97 in
  let forest_to_wg = BatHashtbl.create 97 in
  let to_forest v =
    if BatHashtbl.mem wg_to_forest v then
      BatHashtbl.find wg_to_forest v
    else begin
        let r = F.root forest in
        BatHashtbl.add wg_to_forest v r;
        BatHashtbl.add forest_to_wg r v;
        r
      end
  in
  let find v =
    BatHashtbl.find forest_to_wg (F.find forest (to_forest v))
  in
  let link u weight v =
    F.link forest ~child:(to_forest u) weight ~parent:(to_forest v)
  in
  let eval v = F.eval forest (to_forest v) in
  let idom = D.compute_idom wg.graph src in
  let children = D.idom_to_dom_tree wg.graph idom in
  let rec solve (v : vertex) =
    let children_omega = List.map solve (children v) in

    (* Graph where vertices are children of v, and there is an edge u
       -> w iff there is a path from u to w consisting only of
       vertices strictly dominated by v *)
    let sibling_graph =
      List.fold_left
        (fun sg child ->
          U.fold_pred (fun pred sg ->
              let pred = find pred in
              if pred = v then sg
              else U.add_edge sg pred child)
            wg.graph
            child
            (U.add_vertex sg child))
        U.empty
        (children v)
    in
    (* Traverse SCCs in topological order *)
    let omega_weight =
      List.fold_right
        (fun component omega_weight ->
          let component_wg =
            List.fold_left (fun component_wg v ->
                U.fold_pred (fun p component_wg ->
                    let weight = mul (eval p) (edge_weight wg p v) in
                    add_edge component_wg (find p) weight v)
                  wg.graph
                  v
                  component_wg)
              (empty wg.algebra)
              component
          in
          let reduced = _solve_dense component_wg v in
          List.fold_left (fun omega_weight c ->
              let v_to_c = edge_weight reduced v c in
              let (omega_weight, weight) =
                if U.mem_edge reduced.graph c c then
                  let c_to_c = edge_weight reduced c c in
                  let v_c_omega = omega.omega_mul v_to_c (omega.omega c_to_c) in
                  (omega.omega_add omega_weight v_c_omega,
                   mul v_to_c (star c_to_c))
                else (omega_weight, v_to_c)
              in
              link c weight v;
              omega_weight)
            omega_weight
            component)
        (C.scc_list sibling_graph)
        (omega.omega wg.algebra.zero)
    in
    BatList.fold_left2 (fun v_omega c c_omega ->
        omega.omega_add v_omega (omega.omega_mul (eval c) c_omega))
      omega_weight
      (children v)
      children_omega
  in
  let omega_weight = solve src in
  (* src is an artificial start node -- it's not reachable and its
     path weight 0 *)
  let path_weight x =
    if Hashtbl.mem wg_to_forest x && find x = src && x != src then eval x
    else wg.algebra.zero
  in
  let reachable =
    BatEnum.filter (fun x -> x != src && find x = src) (BatHashtbl.keys wg_to_forest)
  in
  (omega_weight, path_weight, reachable)

let path_weight wg src =
  let (_, path_weight, _) = (_path_weight wg omega_trivial src) in
  path_weight

let omega_path_weight wg omega src =
  let (omega_weight, _, _) = _path_weight wg omega src in
  omega_weight

let msat_path_weight wg sources =
  List.fold_left (fun g src ->
      let (_, path_weight, reachable) = _path_weight wg omega_trivial src in
      BatEnum.fold
        (fun g v -> add_edge g src (path_weight v) v)
        (add_vertex g src)
        reachable)
    (empty wg.algebra)
    sources

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

module type AbstractWeight = sig
  type weight
  type abstract_weight
  val abstract : weight -> abstract_weight
  val concretize : abstract_weight -> weight
  val equal : abstract_weight -> abstract_weight -> bool
  val widen : abstract_weight -> abstract_weight -> abstract_weight
end

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
  module CallGraphLoop = Loop.Make(CallGraph)

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

  let summarize_iterative
        (type a)
        path_query
        algebra
        ?(delay=1)
        (module A : AbstractWeight with type weight = a) =
    let weight_query = mk_weight_query path_query algebra in
    let callgraph = mk_callgraph path_query in
    let project x = algebra (`Segment x) in
    let abstract_summaries = HT.create 991 in
    (* stabilize summaries within a WTO component, and add to unstable
       all calls whose summary (may have) changed as a result. *)
    let rec fix = function
      | `Vertex call ->
         call_weight weight_query call
         |> project
         |> set_summary weight_query call

      | `Loop loop ->
         let header = CallGraphLoop.header loop in
         let rec fix_component delay =
           let old_abs_weight = HT.find abstract_summaries header in
           let (new_abs_weight, new_weight) =
             let new_weight =
               project (call_weight weight_query header)
             in
             let new_abs_weight = A.abstract new_weight in
             if delay > 0 then
               (new_abs_weight, new_weight)
             else
               let new_abs_weight = A.widen old_abs_weight new_abs_weight in
               let new_weight = A.concretize new_abs_weight in
               (new_abs_weight, new_weight)
           in
           HT.replace abstract_summaries header new_abs_weight;
           set_summary weight_query header new_weight;
           List.iter fix (CallGraphLoop.children loop);
           if not (A.equal old_abs_weight new_abs_weight)
           then fix_component (delay - 1)
         in
         fix_component delay
    in
    let zero = algebra `Zero in
    let abstract_zero = A.abstract zero in
    callgraph
    |> CallGraph.iter_vertex (fun call ->
           set_summary weight_query call zero;
           HT.add abstract_summaries call abstract_zero);
    List.iter fix (CallGraphLoop.loop_nest callgraph);
    weight_query

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
