(*pp camlp4find deriving.syntax *)

open Sig.KA
open BatPervasives

(** Implementation of Kleene's algorithm *)
module type G = sig
  type t
  module V : Graph.Sig.VERTEX
  module E : Graph.Sig.EDGE with type vertex = V.t
  val fold_vertex : (V.t -> 'a -> 'a) -> t  -> 'a -> 'a
  val fold_edges_e : (E.t -> 'a -> 'a) -> t -> 'a -> 'a
  val fold_succ : (V.t -> 'a -> 'a) -> t -> V.t -> 'a -> 'a
  val fold_pred : (V.t -> 'a -> 'a) -> t -> V.t -> 'a -> 'a
  val nb_vertex : t -> int
end

(** Compute path expressions for all pairs of vertices on dense graphs *)
module Make(G : G)(K : Ordered.S) :
sig

  (** Get a path expression for all pairs of vertices. *)
  val all_paths : G.t -> (G.E.t -> K.t) -> (G.V.t -> G.V.t -> K.t)

  val all_paths_v : G.t -> (G.V.t -> K.t) -> (G.V.t -> G.V.t -> K.t)
end = struct
  module HT = Hashtbl.Make(G.V)

  (* Display a matrix of K-values *)
  let print_matrix m size =
    for i = 0 to size - 1 do
      for j = 0 to size - 1 do
	if not (K.equal m.(i).(j) K.zero) then begin
	  Log.debug ((string_of_int i) ^ ":" ^ (string_of_int j));
	  Log.debug_pp K.format m.(i).(j);
	end
      done
    done

  (** Given a graph [g] and a function [weight] mapping each graph edge to an
      element of the Kleene algebra {!K}... *)
  let all_paths g weight =
    let num_vertices = G.nb_vertex g in
    let m = Array.make_matrix num_vertices num_vertices K.zero in
    let n = Array.make_matrix num_vertices num_vertices K.zero in

    (* Maintain a vertex -> integer mapping *)
    let vertex_map = HT.create num_vertices in
    let id v =
      try HT.find vertex_map v
      with Not_found -> failwith "Kleene: no ID for vertex"
    in

    let init_edge e () =
      m.(id (G.E.src e)).(id (G.E.dst e)) <- weight e
    in

    (* Main loop of the algorithm.  m is a matrix such that m[j][k] contains
       the "shortest" path from j to k that doesn't pass through any vertex >=
       i.  n is just a matrix with the same dimensions as m whose entries can
       be overwritten. *)
    let rec go m n i =
      if i = num_vertices then m else begin
	let loop = K.star m.(i).(i) in
	  for j = 0 to num_vertices - 1 do
	    if not (K.equal m.(j).(i) K.zero) then begin
	      let j_to_i = K.mul m.(j).(i) loop in
		for k = 0 to num_vertices - 1 do
		  n.(j).(k) <- K.add m.(j).(k) (K.mul j_to_i m.(i).(k))
		done
	    end else begin
	      for k = 0 to num_vertices - 1 do
		n.(j).(k) <- m.(j).(k)
	      done
	    end
	  done;
	  go n m (i + 1)
      end
    in
      ignore (G.fold_vertex (fun v i -> HT.add vertex_map v i; i+1) g 0);

      (* Initialize edge weights *) 
      G.fold_edges_e init_edge g ();

      (* Add 1 to the diagonal *)
      for i = 0 to num_vertices - 1 do
	m.(i).(i) <- K.add K.one m.(i).(i)
      done;

      let m = go m n 0 in
	fun x y -> m.(id x).(id y)

  module M = Memo.Make(G.V)

  (** Run Kleene's algorithm on a graph with weighted vertices rather than
      weighted edges.  This is equivalent to running {!kleene}, where the
      weight of each edge is determined by the weight of its source, but
      {!kleene_v} memoizes the {!weight} function. *)
  let all_paths_v g weight =
    let weight = M.memo weight in
    let edge_weight e = weight (G.E.src e) in
      all_paths g edge_weight
end


module MakeElim (G : G)(K : Ordered.S) :
sig
  (** Get a path expression for a single source and single target *)
  val path_expr : G.t -> (G.E.t -> K.t) -> G.V.t -> G.V.t -> K.t

  val path_expr_v : G.t -> (G.V.t -> K.t) -> G.V.t -> G.V.t -> K.t

  (** Get a path expression for a single source and a set of targets
      (specified by a predicate) by taking the sum the path expressions to
      each individual target. *)
  val path_expr_multiple_tgt : G.t -> (G.E.t -> K.t) -> G.V.t -> (G.V.t -> bool) -> K.t
  val path_expr_multiple_tgt_v : G.t -> (G.V.t -> K.t) -> G.V.t -> (G.V.t -> bool) -> K.t

  (** Compute a path expression from a single source to every other vertex.
      This function has the same signature as [path_expr] and [allpaths], but
      is more efficient if path expressions are required for multiple
      targets, but only a single source. *)
  val single_src : G.t -> (G.E.t -> K.t) -> G.V.t -> (G.V.t -> K.t)

  (** Similar to [single_src], except path expressions are only computed for
      target vertices that satisfy the given predicate. *)
  val single_src_restrict :
    G.t -> (G.E.t -> K.t) -> G.V.t -> (G.V.t -> bool) -> (G.V.t -> K.t)

  val single_src_v : G.t -> (G.V.t -> K.t) -> G.V.t -> (G.V.t -> K.t)
  val single_src_restrict_v :
    G.t -> (G.V.t -> K.t) -> G.V.t -> (G.V.t -> bool) -> (G.V.t -> K.t)


  (** For each vertex [v], compute the sum over all [u] of [path_expr v u].
      That is, [paths_from] computes, for each vertex [v], a path expression
      that represents all paths emanating from [v].  This is equivalent to
      (but more efficent than) calling [path_expr_multiple_tgt v (fun _ ->
      true)] for every vertex v. *)
  val paths_from : G.t -> (G.E.t -> K.t) -> G.V.t -> (G.V.t -> K.t)
end = struct
  module HT = Hashtbl.Make(G.V)
  module KEdge = struct
    type t = K.t
    let default = K.zero
    let compare = K.compare
  end
  type wgv =
    | Real of G.V.t
    | Dummy of int
  module WGV = struct
    type t = wgv
    let compare x y = match x, y with
      | (Real x, Real y) -> G.V.compare x y
      | (Real _, Dummy _) -> 1
      | (Dummy _, Real _) -> -1
      | (Dummy x, Dummy y) -> Pervasives.compare x y
    let equal x y = compare x y = 0
    let hash = function
      | Real x -> 4 * (G.V.hash x)
      | Dummy x -> x
  end
  module WG = Graph.Persistent.Digraph.ConcreteLabeled(WGV)(KEdge)
  module WGTop = Graph.Topological.Make(WG)
  module WGTraverse = ExtGraph.Traverse.Make(WG)
  module WGReverseTop = Graph.Topological.Make(ExtGraph.Reverse(WG))
  module WGLoop = Loop.SccGraph(WG)
  module R = ExtGraph.Slice.Make(G)

  let add_edge g v u k =
    if WG.mem_edge g v u then begin
      let e = WG.find_edge g v u in
      let g = WG.remove_edge_e g e in
	WG.add_edge_e g (WG.E.create v (K.add (WG.E.label e) k) u)
    end else WG.add_edge_e g (WG.E.create v k u)

  let elim v g =
    let (loop, g) =
      if WG.mem_edge g v v then (K.star (WG.E.label (WG.find_edge g v v)),
				 WG.remove_edge g v v)
      else (K.one, g)
    in
    let mul_loop =
      if K.equal loop K.one then (fun x -> x)
      else K.mul loop
    in
    let f se h =
      let v_to_se = mul_loop (WG.E.label se) in
      let add pe h =
	let weight = K.mul (WG.E.label pe) v_to_se in
	add_edge h (WG.E.src pe) (WG.E.dst se) weight
      in
      WG.fold_pred_e add g v h
    in
    WG.fold_succ_e f g v (WG.remove_vertex g v)

  let elim_succ v g =
    let (loop, g) =
      if WG.mem_edge g v v then (K.star (WG.E.label (WG.find_edge g v v)),
				 WG.remove_edge g v v)
      else (K.one, g)
    in
    let mul_loop =
      if K.equal loop K.one then (fun x -> x)
      else (fun x -> K.mul x loop)
    in
    let f pe h =
      let pe_to_v = mul_loop (WG.E.label pe) in
      let add se h =
	let weight = K.mul pe_to_v (WG.E.label se) in
	  add_edge h (WG.E.src pe) (WG.E.dst se) weight
      in
	add_edge (WG.fold_succ_e add g v h) (WG.E.src pe) v pe_to_v
    in
    let h = WG.add_vertex (WG.remove_vertex g v) v in
      WG.fold_pred_e f g v h

  let elim_pred v g =
    let (loop, g) =
      if WG.mem_edge g v v then (K.star (WG.E.label (WG.find_edge g v v)),
				 WG.remove_edge g v v)
      else (K.one, g)
    in
    let mul_loop =
      if K.equal loop K.one then (fun x -> x)
      else K.mul loop
    in
    let f se h =
      let v_to_se = mul_loop (WG.E.label se) in
      let add pe h =
	let weight = K.mul (WG.E.label pe) v_to_se in
	  add_edge h (WG.E.src pe) (WG.E.dst se) weight
      in
	add_edge (WG.fold_pred_e add g v h) v (WG.E.dst se) v_to_se
    in
    let h = WG.add_vertex (WG.remove_vertex g v) v in
      WG.fold_succ_e f g v h

  module KCheck = Make(G)(K)

  let dummy_start = Dummy 0
  let dummy_end = Dummy 1

  let make_weighted_graph g weight s =
    let reach = R.forward_reachable g s in
    let wg =
      BatEnum.fold (fun wg v -> WG.add_vertex wg (Real v)) WG.empty reach
    in
    let f e wg =
      let (src, dst) = (Real (G.E.src e), Real (G.E.dst e)) in
      if WG.mem_vertex wg src && WG.mem_vertex wg dst
      then add_edge wg src dst (weight e)
      else wg
    in
    let wg = WG.add_vertex (G.fold_edges_e f g wg) dummy_start in
    WG.add_vertex (add_edge wg dummy_start (Real s) K.one) dummy_end

  let make_weighted_graph_v g weight s =
    let reach = R.forward_reachable g s in
    let wg =
      BatEnum.fold (fun wg v -> WG.add_vertex wg (Real v)) WG.empty reach
    in
    let f v wg =
      let realv = Real v in
      if WG.mem_vertex wg realv then begin
	let k = weight v in
	let add_edge u wg =
	  let realu = Real u in
	  if WG.mem_vertex wg realu then add_edge wg realv realu k else wg
	in
	G.fold_succ add_edge g v wg
      end else wg
    in
    let wg = WG.add_vertex (G.fold_vertex f g wg) dummy_start in
    WG.add_vertex (add_edge wg dummy_start (Real s) K.one) dummy_end

  let make_weighted_graph_restrict_v g weight s p =
    let final_vertices =
      G.fold_vertex (fun v vs -> if p v then v::vs else vs) g []
    in
    let wg =
      BatEnum.fold
	(fun wg v -> WG.add_vertex wg (Real v))
	WG.empty
	(R.chop_set g [s] final_vertices)
    in
    let f v wg =
      let add_succ v vs = if WG.mem_vertex wg (Real v) then v::vs else vs in
      let succs = G.fold_succ add_succ g v [] in
      if WG.mem_vertex wg (Real v) && not (BatList.is_empty succs) then begin
	let k = weight v in
	let add_edge wg u =
	  WG.add_edge_e wg (WG.E.create (Real v) k (Real u))
	in
	List.fold_left add_edge wg succs
      end
      else wg
    in
    let wg = WG.add_vertex (G.fold_vertex f g wg) dummy_start in
      WG.add_vertex (add_edge wg dummy_start (Real s) K.one) dummy_end

  let path_expr_wg wg =
    let elim v wg =
      assert (WG.mem_vertex wg v);
      if WG.V.equal v dummy_start || WG.V.equal v dummy_end then wg
      else elim v wg
    in
    let scc = WGLoop.construct wg in
    let wg = WGLoop.fold_inside_out elim wg wg in
    if WG.mem_edge wg dummy_start dummy_end
    then WG.E.label (WG.find_edge wg dummy_start dummy_end)
    else K.zero

  let single_src_wg wg =
    let elim_succ v g =
      if WG.V.equal v dummy_start then g else elim_succ v g
    in
    let scc = WGLoop.construct wg in
    let wg = WGTop.fold elim_succ wg wg in
    let path_from t =
      if WG.mem_edge wg dummy_start (Real t)
      then WG.E.label (WG.find_edge wg dummy_start (Real t))
      else K.zero
    in
      path_from

  let single_src_wg_p wg p =
    let elim_succ v g = match v with
      | Real rv -> if p rv then elim_succ v g else elim v g
      | Dummy _ -> g
    in
    let scc = WGLoop.construct wg in
    let wg = WGTop.fold elim_succ wg wg in
    let from_init t =
      if WG.mem_edge wg dummy_start (Real t)
      then WG.E.label (WG.find_edge wg dummy_start (Real t))
      else K.zero
    in
      from_init

  let paths_from_wg wg p =
    let elim_pred v g = match v with
      | Real rv -> if p rv then elim_pred v g else elim v g
      | Dummy _ -> g
    in
    let wg = WG.fold_vertex (fun v wg -> add_edge wg v dummy_end K.one) wg wg in
    let wg = WGReverseTop.fold elim_pred wg wg in
    let paths_from t =
      try WG.E.label (WG.find_edge wg (Real t) (dummy_end))
      with Not_found -> assert false (* impossible *)
    in
      paths_from

  let path_expr g weight s t =
    let wg = make_weighted_graph g weight s in
    if WG.mem_vertex wg (Real t) then begin
      let wg = add_edge wg (Real t) dummy_end K.one in
      path_expr_wg wg
    end else K.zero

  let path_expr_v g weight s t =
    let wg = make_weighted_graph_v g weight s in
    if WG.mem_vertex wg (Real t) then begin
      let wg = add_edge wg (Real t) dummy_end K.one in
      path_expr_wg wg
    end else K.zero

  let path_expr_multiple_tgt_v g weight s p =
    let f v wg =
      if p v && WG.mem_vertex wg (Real v)
      then WG.add_edge_e wg (WG.E.create (Real v) (weight v) dummy_end)
      else wg
    in
    let wg = G.fold_vertex f g (make_weighted_graph_v g weight s) in
      path_expr_wg wg

  let path_expr_multiple_tgt g weight s p =
    let f v wg =
      if p v && WG.mem_vertex wg (Real v)
      then WG.add_edge_e wg (WG.E.create (Real v) K.one dummy_end)
      else wg
    in
    let wg = G.fold_vertex f g (make_weighted_graph g weight s) in
      path_expr_wg wg

  let paths_from g weight s =
    paths_from_wg (make_weighted_graph g weight s) (fun _ -> true)

  let single_src g weight s =
    single_src_wg (make_weighted_graph g weight s)
  let single_src_restrict g weight s =
    single_src_wg_p (make_weighted_graph g weight s)
  let single_src_v g weight s = single_src_wg (make_weighted_graph_v g weight s)
  let single_src_restrict_v g weight s p =
    single_src_wg_p (make_weighted_graph_restrict_v g weight s p) p
end

open RecGraph
module MakeRG
  (R : RecGraph.S)
  (Block : BLOCK with type t = R.block)
  (K : Sig.KA.Quantified.Ordered.S) =
struct
  module CG = RecGraph.Callgraph(R)
  module HT = BatHashtbl.Make(Block)
  module Fix = Fixpoint.Wto(ExtGraph.Reverse(CG))

  module Summarize = MakeElim(R.G)(K)

  (* Summarize paths to call *)
  module P2C = struct
    include Ka.MakePath(Block)(K)
    type var = K.var
    let exists p f =
      { map = M.map (K.exists p) f.map;
	default = K.exists p f.default }
  end
  module SummarizeP2C = MakeElim(R.G)(P2C)

  module InterPE = MakeElim(CG)(K)

  type query =
    { recgraph : R.t;
      weight : R.atom -> K.t;
      local : R.block -> (K.var -> bool);
      root : R.block;
      mutable callgraph : CG.t option;
      summaries : K.t HT.t;
      to_block : K.t HT.t }

  let is_block v = match R.classify v with
    | Block _ -> true
    | Atom _  -> false

  let mk_query g weight local root =
    { recgraph = g;
      weight = weight;
      local = local;
      root = root;
      callgraph = None;
      summaries = HT.create 32;
      to_block = HT.create 32 }

  (** Construct a "call graph" for a recursive graph.  There is an edge from
      block [a] to block [b] if [b] appears inside [a].  The initially open
      graph gets the name [root]. *)
  let callgraph query =
    match query.callgraph with
    | Some cg -> cg
    | None -> begin
      let cg = CG.callgraph query.recgraph query.root in
      query.callgraph <- Some cg;
      cg
    end

  let add_callgraph_edge query b1 b2 =
    let cg' = CG.add_edge (callgraph query) b1 b2 in
    query.callgraph <- Some cg'

  let compute_summaries query =
    let cg = callgraph query in
    let weight v = match R.classify v with
      | Atom atom   -> query.weight atom
      | Block block -> try HT.find query.summaries block
	               with Not_found -> K.zero
    in

    (* Compute summaries for each block *)
    let update block =
      Log.logf Log.info "Computing summary for block %a" Block.format block;
      let body = R.block_body query.recgraph block in
      let src = R.block_entry query.recgraph block in
      let tgt = R.block_exit query.recgraph block in
      let summary =
	let s = Summarize.path_expr_v body weight src tgt in
	let local = query.local block in
	K.exists (fun x -> not (local x)) s
      in
      try
	if K.equal (HT.find query.summaries block) summary then false
	else (HT.replace query.summaries block summary; true)
      with Not_found ->
	if K.equal K.zero summary then false
	else (HT.add query.summaries block summary; true)
    in
    Log.phase "Block summarization" (Fix.fix cg update) None;
    let f k s =
      Log.logf Log.fix "  Summary for %a:@\n    @[%a@]"
	Block.format k
	K.format s
    in
    Log.log Log.fix "Summaries:";
    HT.iter f query.summaries

  let get_summaries query =
    if HT.is_empty query.summaries then compute_summaries query;
    query.summaries

  let get_summary query block =
    let summaries = get_summaries query in 
    try HT.find summaries block
    with Not_found -> K.zero

  let single_src_blocks query =
    let cg = callgraph query in

    let weight v = match R.classify v with
      | Atom atom   -> query.weight atom
      | Block block -> get_summary query block
    in

    let p2c_summaries = HT.create 32 in
    let block_succ_weights block src graph =
      let path = Summarize.single_src_restrict_v graph weight src is_block in
      let ht = HT.create 32 in
      let f u = match R.classify u with
	| Block blk ->
	  let to_blk = (* path from src to blk *)
	    let local = query.local block in
	    K.exists (fun x -> not (local x)) (path u)
	  in
	  begin
	    try HT.replace ht blk (K.add (HT.find ht blk) to_blk)
	    with Not_found -> HT.add ht blk to_blk
	  end
	| Atom _ -> ()
      in
      R.G.iter_vertex f graph;
      HT.add p2c_summaries block ht
    in
    R.bodies query.recgraph
    |> BatEnum.iter (fun (block,graph) ->
      block_succ_weights block (R.block_entry query.recgraph block) graph);

    let cg_weight e =
      try HT.find (HT.find p2c_summaries (CG.E.src e)) (CG.E.dst e)
      with Not_found -> assert false
    in
    InterPE.single_src cg cg_weight query.root

  let single_src_blocks query =
    ignore (get_summaries query);
    Log.phase "Compute path to block" single_src_blocks query


  let single_src_restrict query p go =
    let to_block = single_src_blocks query in
    let weight v = match R.classify v with
      | Atom atom   -> query.weight atom
      | Block block -> try HT.find query.summaries block
	               with Not_found -> K.zero
    in
    let f (block, body) =
      let block_path = to_block block in
      let block_entry = R.block_entry query.recgraph block in
      let from_block =
	Log.time
	  "Single source restrict"
	  (Summarize.single_src_restrict_v body weight block_entry)
	  p
      in
      let f v =
	if p v then go v (K.mul block_path (from_block v))
      in
      R.G.iter_vertex f body
    in
    BatEnum.iter f (R.bodies query.recgraph)

  let single_src query =
    let path_to_block = single_src_blocks query in
    let weight v = match R.classify v with
      | Atom atom   -> query.weight atom
      | Block block -> try HT.find query.summaries block
	               with Not_found -> K.zero
    in
    fun block -> begin
      let to_block = path_to_block block in
      let body = R.block_body query.recgraph block in
      let entry = R.block_entry query.recgraph block in
      let to_v = Summarize.single_src_v body weight entry in
      fun v -> K.mul to_block (to_v v)
    end

  let enum_single_src query =
    let pathexp = single_src query in
    let enum_block (block, body) =
      let pathexp = pathexp block in
      R.G.vertices body /@ (fun v -> (block, v, pathexp v))
    in
    BatEnum.concat (R.bodies query.recgraph /@ enum_block)
end
