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
    let new_weight =
      wg.algebra.add (M.find (u, v) wg.labels) weight
    in
    { wg with labels = M.add (u, v) new_weight wg.labels }
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

module type Weight = sig
  type t
  val mul : t -> t -> t
  val add : t -> t -> t
  val zero : t
  val one : t
  val star : t -> t
  val equal : t -> t -> bool
  val project : t -> t
  val widen : t -> t -> t
end

type 'a label =
  | Weight of 'a
  | Call of int * int

module MakeRecGraph (W : Weight) = struct

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

  let fold_reachable_edges f g v acc =
    let visited = ref VertexSet.empty in
    let rec go u acc =
      U.fold_succ (fun v acc ->
          let acc = f u v acc in
          if not (VertexSet.mem v !visited) then begin
            visited := VertexSet.add v (!visited);
            go v acc
          end else
            acc)
        g.graph
        u
        acc
    in
    go v acc

  type recgraph = (W.t label) weighted_graph

  type query =
    { summaries : W.t M.t; (* Map calls to weights that summarize all paths in
                              the call *)
      labels : (W.t label) M.t; (* Interpretation for all path expression edges *)
      graph : Pathexpr.t t; (* Path expression weighted graph *)
      table : W.t table; (* Path expression memo table  *)
      context : Pathexpr.context (* Path expression context *) }


  type t = recgraph

  let label_algebra =
    let add x y = match x, y with
      | Weight x, Weight y -> Weight (W.add x y)
      | _, _ -> invalid_arg "No weight operations for call edges"
    in
    let mul x y = match x, y with
      | Weight x, Weight y -> Weight (W.mul x y)
      | _, _ -> invalid_arg "No weight operations for call edges"
    in
    let star = function
      | Weight x -> Weight (W.star x)
      | _ -> invalid_arg "No weight operations for call edges"
    in
    let zero = Weight W.zero in
    let one = Weight W.one in
    { add; mul; star; zero; one }

  let empty = empty label_algebra

  let weight_algebra f = function
    | `Edge (s, t) -> f s t
    | `Mul (x, y) -> W.mul x y
    | `Add (x, y) -> W.add x y
    | `Star x -> W.star x
    | `Zero -> W.zero
    | `One -> W.one

  let pathexp_algebra context =
    { mul = mk_mul context;
      add = mk_add context;
      star = mk_star context;
      zero = mk_zero context;
      one = mk_one context }

  (* For each (s,t) call reachable from [src], add an edge from [src] to [s]
     with the path weight from [src] to the call.  *)
  let add_call_edges query src =
    let weight_algebra =
      weight_algebra (fun s t ->
          match M.find (s, t) query.labels with
          | Weight w -> w
          | Call (en, ex) -> M.find (en, ex) query.summaries)
    in
    fold_reachable_edges
      (fun u v query' ->
         match M.find (u, v) query'.labels with
         | Call (call, _) ->
           let weight =
             path_weight query.graph src u
             |> eval ~table:query.table weight_algebra
             |> W.project
           in
           if M.mem (src, call) query'.labels then
             match M.find (src, call) query'.labels with
             | Weight w ->
               let label = Weight (W.add w weight) in
               let labels' =
                 M.add (src, call) label query'.labels
               in
               { query' with labels = labels' }
             | _ -> assert false
           else
             let graph' =
               add_edge query'.graph src (mk_edge query.context src call) call
             in
             let labels' = M.add (src, call) (Weight weight) query'.labels in
             { query' with graph = graph';
                           labels = labels' }
         | _ -> query')
      query.graph
      src
      query

  let mk_query ?(delay=1) rg =
    let table = mk_table () in
    let context = mk_context () in
    let calls = (* All calls that appear on a call edge *)
      fold_edges (fun (_, label, _) callset ->
          match label with
          | Weight _ -> callset
          | Call (en, ex) -> CallSet.add (en, ex) callset)
        rg
        CallSet.empty
    in
    let path_graph =
      { graph = rg.graph;
        labels = M.mapi (fun (u,v) _ -> mk_edge context u v) rg.labels;
        algebra = pathexp_algebra context }
    in

    if CallSet.is_empty calls then
      { summaries = M.empty;
        table;
        graph = path_graph;
        context;
        labels = rg.labels }
    else begin
      let call_pathexpr =
        CallSet.fold (fun (src, tgt) pathexpr ->
            M.add (src, tgt) (path_weight path_graph src tgt) pathexpr)
          calls
          M.empty
      in
      (* Create a fresh call vertex to serve as entry.  It will have an edge
           to every other call *)
      let callgraph_entry =
        let s = fst (CallSet.min_elt calls) in
        (s-1, s-1)
      in
      (* Compute summaries *************************************************)
      let callgraph_loop_nest =
        let pe_calls = function
          | `Edge (s, t) ->
            begin match M.find (s, t) rg.labels with
              | Call (en, ex) -> CallSet.singleton (en, ex)
              | _ -> CallSet.empty
            end
          | `Mul (x, y) | `Add (x, y) -> CallSet.union x y
          | `Star x -> x
          | `Zero | `One -> CallSet.empty
        in
        let table = mk_table () in
        let initial_callgraph =
          CallSet.fold (fun call callgraph ->
              CallGraph.add_edge callgraph callgraph_entry call)
            calls
            CallGraph.empty
        in
        (* If there is a call to (s,t) between s' and t', add a dependence
           edge from (s',t') to (s,t) *)
        let callgraph =
          M.fold (fun proc pathexpr callgraph ->
              CallSet.fold (fun target callgraph ->
                  CallGraph.add_edge callgraph target proc)
                (eval ~table pe_calls pathexpr)
                callgraph)
            call_pathexpr
            initial_callgraph
        in
        CallGraphLoop.loop_nest callgraph
      in
      let summaries = ref (M.map (fun _ -> W.zero) call_pathexpr) in
      let weight =
        weight_algebra (fun s t ->
            match M.find (s, t) rg.labels with
            | Weight w -> w
            | Call (en, ex) -> M.find (en, ex) (!summaries))
      in
      let is_stable_edge unstable s t =
        match M.find (s, t) rg.labels with
        | Weight _ -> true
        | Call (s, t) -> not (CallSet.mem (s, t) unstable)
      in

      (* stabilize summaries within a WTO component, and add to unstable all
         calls whose summary (may have) changed as a result. *)
      let rec fix = function
        | `Vertex call when call = callgraph_entry -> ()
        | `Vertex call ->
           let pathexpr = M.find call call_pathexpr in
           let new_weight =
             eval ~table weight pathexpr
             |> W.project
           in
           summaries := M.add call new_weight (!summaries)
        | `Loop loop ->
           let header = CallGraphLoop.header loop in
           let pathexpr = M.find header call_pathexpr in
           let unstable = CallGraphLoop.body loop in
           let rec fix_component delay =
             let old_weight = M.find header (!summaries) in
             let new_weight =
               eval ~table weight pathexpr
               |> W.project
             in
             let new_weight =
               if delay > 0 then new_weight
               else W.widen old_weight new_weight
             in
             summaries := M.add header new_weight (!summaries);
             List.iter fix (CallGraphLoop.children loop);
             if not (W.equal old_weight new_weight) then begin
                 forget table (is_stable_edge unstable);
                 fix_component (delay - 1)
               end
           in
           fix_component delay
      in
      List.iter fix callgraph_loop_nest;
      let query =
        { summaries = !summaries;
          table;
          graph = path_graph;
          context;
          labels = rg.labels }
      in
      (* For each (s,t) call containing a call (s',t'), add an edge from s to s'
         with the path weight from s to call(s',t'). *)
      CallSet.fold
        (fun (src, _) query' -> add_call_edges query' src)
        calls
        query
    end

  let path_weight query src tgt =
    (* For each (s,t) call edge reachable from src, add corresponding edge
       from src to s with the path weight from src to s *)
    let query' = add_call_edges query src in
    let weight =
      weight_algebra (fun s t ->
          match M.find (s, t) query'.labels with
          | Weight w -> w
          | Call (en, ex) -> M.find (en, ex) query'.summaries)
    in
    path_weight query'.graph src tgt
    |> eval ~table:query.table weight

  let omega_pathexpr context =
    { omega = mk_omega context;
      omega_mul = mk_omega_mul context;
      omega_add = mk_omega_add context }

  let omega_path_weight query (omega : (W.t, 'b) omega_algebra) =
    (* Memo table is constructed for [omega_path_weight query omega],
       so the table can be re-used for multiple sources. *)
    let omega_table = mk_omega_table query.table in
    fun src -> begin
        (* For each (s,t) call edge reachable from src, add
           corresponding edge from src to s with the path weight from
           src to s *)
        let query' = add_call_edges query src in
        let weight =
          weight_algebra (fun s t ->
              match M.find (s, t) query'.labels with
              | Weight w -> w
              | Call (en, ex) -> M.find (en, ex) query'.summaries)
        in
        let omega_weight = function
          | `Omega x -> omega.omega x
          | `Mul (x, y) -> omega.omega_mul x y
          | `Add (x, y) -> omega.omega_add x y
        in
        omega_path_weight query'.graph (omega_pathexpr query.context) src
        |> eval_omega ~table:omega_table weight omega_weight
      end
end
