(*pp camlp4find deriving.syntax *)

open Sig.KA
open BatPervasives

module L = Log.Make(struct let name = "pathexp" end)

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

  let dummy_start = Dummy 0
  let dummy_end = Dummy 1

  module LoopDom = Graph.Dominator.Make(struct
    type t = WGLoop.t ref
    module V = WGLoop.V
    let pred g v = WGLoop.pred (!g) v
    let succ g v = WGLoop.succ (!g) v
    let fold_vertex f g a = WGLoop.fold_vertex f (!g) a
    let iter_vertex f g = WGLoop.iter_vertex f (!g)
    let nb_vertex g = WGLoop.nb_vertex (!g)
    let create ?(size=0) () = ref WGLoop.empty
    let add_edge g u v = g := WGLoop.add_edge (!g) u v
  end)
  module LoopPostDom = Graph.Dominator.Make(struct
    type t = WGLoop.t ref
    module V = WGLoop.V
    let pred g v = WGLoop.succ (!g) v
    let succ g v = WGLoop.pred (!g) v
    let fold_vertex f g a = WGLoop.fold_vertex f (!g) a
    let iter_vertex f g = WGLoop.iter_vertex f (!g)
    let nb_vertex g = WGLoop.nb_vertex (!g)
    let create ?(size=0) () = ref WGLoop.empty
    let add_edge g u v = g := WGLoop.add_edge (!g) u v
  end)


  module VMemo = Memo.Make(WGV)
  let get_id =
    let id = ref (-1) in
    VMemo.memo (fun _ -> incr id; !id)

  module WGD = ExtGraph.Display.MakeSimple(WG)(struct
    type t = WG.V.t
    include Putil.MakeFmt(struct
      type a = t
      let format formatter v =
	Format.fprintf formatter "Vertex %d" (get_id v)
    end)
  end)
  let fold_dom : (WG.V.t -> 'a -> 'a) -> WG.t -> 'a -> 'a
    = fun f g acc ->
(*      Log.errorf "Using fold_dom";*)
(*      WGD.display g;*)
    let open Loop in
    let open WGLoop in
    let sccg = WGLoop.construct g in
    let rec go acc v =
      match v.vtype with
      | Simple v ->
	L.logf "Visit: %d" (get_id v);
	f v acc
      | Scc scc -> go_graph scc.entries (scc.backedges@scc.exits) scc.graph acc
    and go_graph initial exits graph acc =
      assert(initial != []);
      let is_initial v = List.exists (WG.V.equal v) initial in
      let find_roots v roots =
	match v.vtype with
	| Simple w -> if is_initial w then v::roots else roots
	| Scc _ -> roots
      in
      let roots = WGLoop.fold_vertex find_roots graph [] in
      assert (List.length roots = List.length initial);

      let exits = if exits = [] then initial else exits in
      let is_exit v = List.exists (WG.V.equal v) exits in
      let find_post_roots v roots =
	match v.vtype with
	| Simple w -> if is_exit w then v::roots else roots
	| Scc scc ->
	  if (List.exists (fun v -> List.exists (WG.V.equal v) exits) scc.entries)
	    || (List.exists (fun v -> List.exists (WG.V.equal v) exits) scc.exits)
	  then v::roots
	  else roots
      in
      let post_roots = WGLoop.fold_vertex find_post_roots graph [] in
(*      Log.errorf "%d != %d" (List.length post_roots) (List.length exits);*)
      assert (List.length post_roots != 0);
      (*assert (List.length post_roots = List.length exits);*)

      (* Connect the forest with a new root *)
      let root =
	{ scc_id = -1;
	  vtype = Simple dummy_start }
      in
      let graph =
	List.fold_left
	  (fun g v -> WGLoop.add_edge g root v)
	  graph
	  roots
      in
      let post_root =
	{ scc_id = -2;
	  vtype = Simple dummy_end }
      in
      let graph =
	List.fold_left
	  (fun g v -> WGLoop.add_edge g v post_root)
	  graph
	  post_roots
      in

      let dom_tree =
	(LoopDom.compute_all (ref graph) root).LoopDom.dom_tree
      in
      let postdom =
	(LoopPostDom.compute_all (ref graph) post_root).LoopPostDom.dom
      in
      let rec visit acc v =
	if List.length (dom_tree v) > 1
	then go (visit_children acc v) v
	else visit_children (go acc v) v

      and visit_children acc v =
	let rec go children acc = match children with
	  | [] -> acc
	  | (x::xs) ->
	    if List.exists (flip postdom x) xs then go (xs@[x]) acc
	    else go xs (visit acc x)
	in
	go (dom_tree v) acc
      in

      let visit_domtree_root acc v =
	if List.exists (fun x -> x.scc_id = v.scc_id) roots
	then visit_children acc v
	else visit acc v
      in
      let acc = List.fold_left visit_domtree_root acc (dom_tree root) in
      List.fold_left go acc roots
    in
    go_graph [dummy_start] [dummy_end] sccg acc


  module Re = Sese.Make(WG)
  module ReLoop = Loop.SccGraph(Re.G)
  module WGVMemo = Memo.Make(WGV)
  let get_id =
    let id = ref (-1) in
    WGVMemo.memo (fun _ -> incr id; !id)
  module ReGD = ExtGraph.Display.MakeSimple(Re.G)(struct
    type t = Re.G.V.t
    include Putil.MakeFmt(struct
      type a = t
      let format formatter =
	let open RecGraph in
	function
	| `Block k -> Format.fprintf formatter "Block %d" k
	| `Atom k -> Format.fprintf formatter "Atom %d" (get_id k)
    end)
  end)
  let fold_sese f wg acc =
    let open RecGraph in
    let rg = Re.construct wg dummy_start dummy_end in
    let fold_body = ReLoop.fold_inside_out in
    let rec visit v acc =
      match v with
      | `Block block ->
	L.logf "Enter block %d" block;
	let bentry = Re.block_entry rg block in
	let bexit = Re.block_exit rg block in
	let go v acc =
	  if Re.G.V.equal v bentry || Re.G.V.equal v bexit then acc
	  else visit v acc
	in
	let acc = fold_body go (Re.block_body rg block) acc in
	let res =
	if Re.G.V.equal bentry bexit then visit bentry acc
	else visit bentry (visit bexit acc)
	in
	L.logf "Exit block %d" block;
	res
      | `Atom atom ->
	L.logf "Visit: %d" (get_id atom);
	f atom acc
    in
    fold_body visit (Re.block_body rg 0) acc

  module BB = Graph.Leaderlist.Make(WG)

  (* Fold over vertices which do not start or end a basic block *)
  let fold_bb f wg acc =
    let fold_block acc xs =
      assert (xs != []);
      if List.length xs > 2
      then List.fold_right f (List.tl (List.rev (List.tl xs))) acc
      else acc
    in
    List.fold_left fold_block acc (BB.leader_lists wg dummy_start)

  let opt_elimination_strategy = ref fold_sese

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
    let wg = fold_bb elim wg wg in
    let wg = (!opt_elimination_strategy) elim wg wg in
    if WG.mem_edge wg dummy_start dummy_end
    then WG.E.label (WG.find_edge wg dummy_start dummy_end)
    else K.zero

  let single_src_wg wg =
    let elim_succ v g =
      if WG.V.equal v dummy_start then g else elim_succ v g
    in
    let wg = WGLoop.fold_inside_out elim_succ wg wg in
    (* todo: fold_sese doesn't work if there are multiple targets *)
    (* let wg = (!opt_elimination_strategy) elim_succ wg wg in*)
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
    let wg = WGLoop.fold_inside_out elim_succ wg wg in
    (* todo: fold_sese doesn't work if there are multiple targets *)
    (* let wg = (!opt_elimination_strategy) elim_succ wg wg in*)
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
module MakeParRG
  (R : RecGraph.S with type ('a,'b) typ = ('a, 'b) RecGraph.par_typ)
  (Block : BLOCK with type t = R.block)
  (K : sig 
    include Sig.KA.Quantified.Ordered.S
    val fork : t -> t
    val widen : t -> t -> t
  end) =
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
    { mutable recgraph : R.t;
      weight : R.atom -> K.t;
      local : R.block -> (K.var -> bool);
      root : R.block;
      mutable callgraph : CG.t option;
      summaries : K.t HT.t;
      to_block : K.t HT.t }

  let is_block v = match R.classify v with
    | `ParBlock _ | `Block _ -> true
    | `Atom _  -> false

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
      L.logf "Call graph vertices: %d, edges: %d"
	(CG.nb_vertex cg)
	(CG.nb_edges cg);
      query.callgraph <- Some cg;
      cg
    end

  let add_callgraph_edge query b1 b2 =
    let cg' = CG.add_edge (callgraph query) b1 b2 in
    query.callgraph <- Some cg'

  let remove_dead_code query =
    let cg = callgraph query in
    let f acc block = if not (CG.mem_vertex cg block)
                      then R.remove_block acc block
                      else acc
    in
      query.recgraph <- BatEnum.fold f query.recgraph (R.blocks query.recgraph)

  let compute_summaries query =
    let cg = callgraph query in
    let weight v = match R.classify v with
      | `Atom atom   -> query.weight atom
      | `Block block ->
	begin
	  try HT.find query.summaries block
	  with Not_found -> K.zero
	end
      | `ParBlock block ->
	begin
	  try K.fork (HT.find query.summaries block)
	  with Not_found -> K.fork K.zero
	end
    in

    (* Compute summaries for each block *)
    let update join block =
      L.logf
	~level:Log.phases
	~attributes:[Log.Cyan]
	"Computing summary for block `%a`"
	Block.format block;
      let body = R.block_body query.recgraph block in
      let src = R.block_entry query.recgraph block in
      let tgt = R.block_exit query.recgraph block in
      let summary =
	let s = Summarize.path_expr_v body weight src tgt in
	let local = query.local block in
	K.exists (fun x -> not (local x)) s
      in
      try
	let old_summary = HT.find query.summaries block in
	let new_summary = join old_summary summary in
	if K.equal old_summary new_summary then false
	else (HT.replace query.summaries block new_summary; true)
      with Not_found ->
	if K.equal K.zero summary then false
	else (HT.add query.summaries block summary; true)
    in
    Log.phase "Block summarization"
      (Fix.fix cg (update K.add))
      (Some (update K.widen));
    let f k s =
      L.logf "  Summary for %a:@\n    @[%a@]"
	Block.format k
	K.format s
    in
    L.logf "Summaries:";
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
      | `Atom atom   -> query.weight atom
      | `Block block -> get_summary query block
      | `ParBlock block -> K.fork (get_summary query block)
    in

    let p2c_summaries = HT.create 32 in
    let block_succ_weights (block, graph) =
      L.logf "Compute paths to call vertices in `%a`" Block.format block;
      let src = R.block_entry query.recgraph block in
      let path = Summarize.single_src_v graph weight src in
      let ht = HT.create 32 in
      let f u = match R.classify u with
	| `Block blk | `ParBlock blk ->
	  let to_blk = (* path from src to blk *)
	    let local = query.local block in
	    K.exists (fun x -> not (local x)) (path u)
	  in
	  begin
	    try HT.replace ht blk (K.add (HT.find ht blk) to_blk)
	    with Not_found -> HT.add ht blk to_blk
	  end
	| `Atom _ -> ()
      in
      R.G.iter_vertex f graph;
      HT.add p2c_summaries block ht
    in
    Log.phase "Compute call graph weights"
      (BatEnum.iter block_succ_weights) (R.bodies query.recgraph);

    let cg_weight e =
      try HT.find (HT.find p2c_summaries (CG.E.src e)) (CG.E.dst e)
      with Not_found -> assert false
    in
    Log.phase "Compute path to block"
      (InterPE.single_src cg cg_weight) query.root

  let single_src_blocks query =
    ignore (get_summaries query);
    single_src_blocks query

  let single_src_restrict query p go =
    let to_block = single_src_blocks query in
    let weight v = match R.classify v with
      | `Atom atom -> query.weight atom
      | `Block block ->
	begin
	  try HT.find query.summaries block
          with Not_found -> K.zero
	end
      | `ParBlock block ->
	begin
	  try HT.find query.summaries block
          with Not_found -> K.fork K.zero
	end
    in
    let f (block, body) =
      L.logf "Intraprocedural paths in `%a`" Block.format block;
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
      | `Atom atom -> query.weight atom
      | `Block block ->
	begin
	  try HT.find query.summaries block
	  with Not_found -> K.zero
	end
      | `ParBlock block ->
	begin
	  try HT.find query.summaries block
	  with Not_found -> K.fork K.zero
	end
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

module MakeSeqRG
  (R : RecGraph.S with type ('a,'b) typ = ('a, 'b) RecGraph.seq_typ)
  (Block : BLOCK with type t = R.block)
  (K : sig
    include Sig.KA.Quantified.Ordered.S
    val widen : t -> t -> t
  end) =
  MakeParRG
    (RecGraph.LiftPar(R))
    (Block)
    (struct
      include K
      let fork _ = assert false
     end)
