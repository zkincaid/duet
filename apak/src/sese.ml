(*pp camlp4find deriving.syntax *)

(** Implementation of program structure trees.  More details can be found in
    Richard Johnson, David Pearson, and Keshav Pingali, "The Program Structure
    Tree: Computing Control Regions in Linear Time". *)
open BatPervasives

module type G = sig
  type t
  module V : Graph.Sig.VERTEX
  module E : Graph.Sig.EDGE with type vertex = V.t
  val fold_vertex : (V.t -> 'a -> 'a) -> t  -> 'a -> 'a
  val fold_edges_e : (E.t -> 'a -> 'a) -> t -> 'a -> 'a
  val fold_edges : (V.t -> V.t -> 'a -> 'a) -> t -> 'a -> 'a
  val fold_succ : (V.t -> 'a -> 'a) -> t -> V.t -> 'a -> 'a
  val fold_pred : (V.t -> 'a -> 'a) -> t -> V.t -> 'a -> 'a
  val nb_vertex : t -> int
  val mem_vertex : t -> V.t -> bool
end

module Make(G : G) = struct

  open Loop
  module U = Graph.Persistent.Graph.Concrete(G.V)

  module ExtG = struct
    include G
    let iter_edges_e f g = fold_edges_e (fun e () -> f e) g ()
    let iter_edges f g =
      fold_edges_e (fun e () -> f (G.E.src e) (G.E.dst e)) g ()
    let iter_vertex f g = fold_vertex (fun v () -> f v) g ()
    let is_directed = true
    let iter_succ f g v = fold_succ (fun v () -> f v) g v ()
    let iter_pred f g v = fold_pred (fun v () -> f v) g v ()
    let find_edge g u v =
      let f e = function
	| Some e -> Some e
	| None ->
	  if G.V.equal (G.E.src e) u && G.V.equal (G.E.dst e) v then Some e
	  else None
      in
      match fold_edges_e f g None with
      | Some e -> e
      | None -> raise Not_found
    let mem_edge g u v =
      let f v0 mem = mem || G.V.equal v0 v in
      G.fold_succ f g u false
  end

  module M = Memo.Make(G.V)
  let id = ref (-1)
  let name = M.memo (fun _ -> incr id; !id)
  let pp formatter v = Format.pp_print_int formatter (name v)

  module GD = ExtGraph.Display.MakeSimple(ExtG)(struct
    type t = G.V.t
    include Putil.MakeFmt(struct
      type a = t
      let format = pp
    end)
  end)

  module GScc = Loop.SccInfo.Make(ExtG)
  module DfsTree = ExtGraph.DfsTree.Make(ExtG)

  type e = G.V.t * G.V.t

  module GE = struct
    type t = G.V.t * G.V.t
    module Compare_t = struct
      type a = t
      let compare (a,b) (c,d) =
	match G.V.compare a c with
	| 0 -> G.V.compare b d
	| x -> x
    end
    let compare = Compare_t.compare
    include Putil.MakeFmt(struct
      type a = t
      let format formatter (a, b) =
	Format.fprintf formatter "(%a,%a)"
	  pp a
	  pp b
    end)
  end
  module ESet = Putil.Set.Make(GE)

  type pst = PSTNode of (e * e * (pst list))

  (* Internal structure used for building program structure trees *)
  type pst_node = {
    pst_start : e;
    mutable pst_end : e option;
    pst_parent : pst_node option;
    mutable pst_children : pst_node list;
    pst_cls : int
  }

  (* Create a new pst node with parent node and beginning edge e.  cls must be
     the CEC of e. *)
  let pst_mk_child node cls e =
    let child_node = {
      pst_start = e;
      pst_end = None;
      pst_parent = Some node;
      pst_children = [];
      pst_cls = cls;
    } in
    node.pst_children <- child_node::node.pst_children;
    child_node
  let pst_parent node = match node.pst_parent with
    | Some p -> p
    | None   -> invalid_arg "pst_parent"

  (* Create an undirected copy of the vertices reachable from init. *)
  let undirected g init =
    let open U in
    let rec go (worklist, pg) =
      match worklist with
      | [] -> pg
      | (v::worklist) ->
	let f succ (worklist, pg) =
	  let h = add_edge pg v succ in
	  if mem_vertex pg succ then (worklist, h)
	  else (succ::worklist, h)
	in
	go (G.fold_succ f g v (worklist, pg))
    in
    add_vertex (go ([init], empty)) init

  let rec format_pst pp formatter (PSTNode (s, e, children)) =
    Format.fprintf formatter "@[{(%a->%a) ==> (%a->%a) : %a}@]"
      pp (fst s)
      pp (snd s)
      pp (fst e)
      pp (snd e)
      (Putil.format_list (format_pst pp)) children

  type cec_edge =
    { mutable recent_size : int;
      mutable recent_class : int;
      src : int;
      tgt : int }
  type child =
    { dfsnum : int;
      hi : int; (* dfsnum of the destination vertex closest to the root of
		   any edge originating from a decendent of this vertex. *)
      blist : cec_edge Dll.t }

  (* Normalize a pair of integers so that the smaller integer comes first.
     This gives a canonical name to undirected edges. *)
  let norm_pair (x, y) = if x < y then (x, y) else (y, x)
  module H = Hashtbl.Make (struct
			     type t = int * int
			     let hash x = Hashtbl.hash (norm_pair x)
			     let equal x y = (norm_pair x) = (norm_pair y)
			   end)

  let find_cls tbl edge = H.find tbl (norm_pair edge)
  let set_cls tbl edge cls = H.add tbl (norm_pair edge) cls

  module UDfsTree = ExtGraph.DfsTree.Make(U)
  module UComponents = Graph.Components.Make(U)

  (** Compute cycle equivalence classes.  The function returns a triple
      {!(vertex_class, edge_class, num_classes)}, where vertex_class maps each
      vertex to a CEC, edge_class maps each edge to a CEC, and num_classes is
      the number of CECs in the graph. *)
  let compute_cec digraph init =
    let open Dll in
    let open UDfsTree in
    let graph = undirected digraph init in

    let twocycles =
      G.fold_edges
	(fun u v set ->
	  if ExtG.mem_edge digraph v u then ESet.add (u, v) set
	  else set)
	digraph
	ESet.empty
    in

    (* We need the graph to be strongly 2-connected.  Add edges from sink SCCs
       back to init. *)
    let graph =
      let sinks = GScc.sinks digraph in
      let f graph scc =
	let v =
	  try BatEnum.find (not % ExtG.mem_edge digraph init) (GScc.enum scc)
	  with Not_found -> assert false (* this can happen *)
	in
	U.add_edge graph v init
      in
      BatEnum.fold f graph sinks
    in

    (* This fixes a bug caused by 2-cycles: these are collapsed into single
       edges when we look at the undirected version of the graph.  If we have
       u->v->u, and v has no other edges, then v isn't terminal in the
       directed graph but it is terminal in the directed graph.  *)
    let graph =
      U.fold_vertex
	(fun v g -> if U.out_degree g v == 1 then U.add_edge g v init else g)
	graph
	graph
    in

    let tree = UDfsTree.compute graph init in
    let size = UDfsTree.size tree in
    let cls = H.create (3 * size) in
    let infty = size + 1 in
    let fold_backedges f = UDfsTree.fold_backedges f graph tree in
    let iter_backedges f v = fold_backedges (fun x () -> ignore (f x)) v () in
    let vertex_cls = Array.create size (-1) in
    let max_class = ref 0 in
    let new_class () =
      let cls = !max_class in
      incr max_class;
      cls
    in
    let mk_edge u v =
      { recent_size = -1;
	recent_class = -1;
	src = u;
	tgt = v }
    in

    (* For each vertex v, maintain a list of the (capping) backedges from a
       descendent of v to v. *)
    let backedges = Array.create size [] in
    let capping_backedges = Array.create size [] in
    let push_backedge u v blist =
      let edge = mk_edge u v in
      let edge_dll_node = Dll.push edge blist in
      backedges.(v) <- edge_dll_node::(backedges.(v))
    in
    let push_capping_backedge u v blist =
      let edge = mk_edge u v in
      let edge_dll_node = Dll.push edge blist in
      capping_backedges.(v) <- edge_dll_node::(capping_backedges.(v))
    in
    (* The idea of this algorithm is that two edges are in the same cycle
       equivalence class iff they have the same set of brackets (an edge is a
       bracket of a vertex v if it is from a decendent of v to an ancestor of
       v in the DFS tree).  Most of the "work" of this function is just book
       keeping that's required to efficiently give sets of brackets canonical
       names.  *)
    let f v children =
      let fold_children f a = List.fold_left f a children in
      let dfsnum = get_dfs_num v tree in
      let hi0 = fold_backedges (fun x -> min (get_dfs_num x tree)) v infty in
      let min2 x (y, z) =
	if x <= y then (x, y)
	else if x < z then (y, x)
	else (y, z)
      in
      let (hi1, hi2) = fold_children (fun m c -> min2 c.hi m) (infty, infty) in
      let blist =
	fold_children (fun bl c -> Dll.concat bl c.blist) (Dll.create ())
      in
      (* Push backedges originating at this vertex *)
      iter_backedges
	(fun x -> push_backedge dfsnum (get_dfs_num x tree) blist)
	v;
      if hi2 < hi0 then push_capping_backedge dfsnum hi2 blist;
      begin
	let b =
	  try Dll.top blist
	  with Not_found -> failwith "ExtGraph.CEC: empty blist"
	in
	if b.recent_size != (Dll.size blist) then begin
	  b.recent_size <- Dll.size blist;
	  b.recent_class <- new_class ()
	end;
	vertex_cls.(dfsnum) <- b.recent_class;
	if b.recent_size = 1
	then set_cls cls (b.src, b.tgt) b.recent_class;
      end;

      (* Delete backedges ending at this vertex, and determine the CEC for
	 real backedges (that is, non-capping backedges) *)
      List.iter (Dll.delete blist) capping_backedges.(dfsnum);
      begin
	let f b =
	  Dll.delete blist b;
	  let edge = Dll.elt b in
	  let edge_cls =
	    try find_cls cls (edge.src, edge.tgt) with Not_found -> infty
	  in
	  if edge_cls = infty
	  then set_cls cls (edge.src, edge.tgt) (new_class ())
	in
	List.iter f backedges.(dfsnum)
      end;

      (* Determine the CEC for the edge from the parent of v to v. *)
      begin match parent v tree with
      | None -> () (* nothing to do for root *)
      | Some p ->
	let b =
	  try Dll.top blist
	  with Not_found -> failwith "ExtGraph.CEC: empty blist"
	in
	if b.recent_size != (Dll.size blist) then begin
	  b.recent_size <- Dll.size blist;
	  b.recent_class <- new_class ()
	end;
	set_cls cls (dfsnum, get_dfs_num p tree) b.recent_class;
	if b.recent_size = 1
	then set_cls cls (b.src, b.tgt) b.recent_class
      end;
      { dfsnum = dfsnum;
	hi = min hi0 hi1;
	blist = blist }
    in
    (* Another 2-cycle problem: edges which belong to a 2-cycle are not
       cycle-equivalent with anything. *)
    let bump_2cycle (u, v) =
      if get_dfs_num u tree < get_dfs_num v tree then begin
	set_cls cls (get_dfs_num u tree, get_dfs_num v tree) (new_class ());
	ignore (new_class ());
      end
    in
    ignore (UDfsTree.fold_dfs_tree f tree);
    ESet.iter bump_2cycle twocycles;
    ((fun x -> vertex_cls.(get_dfs_num x tree)),
     (fun x y ->
       let cls = find_cls cls (get_dfs_num x tree, get_dfs_num y tree) in
       if ESet.mem (x,y) twocycles && get_dfs_num x tree < get_dfs_num y tree
       then cls + 1 else cls),
     !max_class)


  (** Construct a program structure tree. *)
  let construct_pst init g =
    let (_, cls, num_cls) =
      try compute_cec g init with e -> begin
	Log.errorf "Failed to compute cycle equivalence classes";
	GD.display g;
	raise e
      end
    in
    if !Log.debug_mode then begin
      let classes = Array.create num_cls [] in
      ExtG.iter_edges (fun v u ->
	classes.(cls v u) <- (name v, name u)::classes.(cls v u)
      ) g;
      for i = 0 to num_cls - 1 do
	Log.debugf "CEC %d: %a" i Show.format<(int*int) list> classes.(i)
      done
    end;
    
    (* Within each nontrivial CEC, edges are linearly ordered, and adjacent
       edges enclose a canonical SESE region.  We maintain a mapping from CECs
       to the number of edges of that CEC that have not yet been visited, so
       that we can determine whether an edge begins a canonical SESE
       region. *)
    let cls_size = Array.create num_cls 0 in
    ExtG.iter_edges
      (fun v u ->
	try cls_size.(cls v u) <- cls_size.(cls v u) + 1
	with Not_found -> ())
      g;
    let tree = DfsTree.compute g init in
    let visit node v u =
      Log.debugf "Visiting (DFS) %d -> %d" (name v) (name u);
      let e_cls = cls v u in
      let edge = (v, u) in
      let node =
	if node.pst_cls = e_cls then begin
	  (* This edge ends the canonical SESE region. *)
	  node.pst_end <- Some edge;
	  pst_parent node
	end else node
      in
      if cls_size.(e_cls) > 1 then begin
	(* This edge begins a canonical SESE region *)
	cls_size.(e_cls) <- cls_size.(e_cls) - 1;
	pst_mk_child node e_cls edge
      end else node
    in
    let rec go node v u =
      let next_node = visit node v u in
      if  DfsTree.classify v u tree = ExtGraph.TreeEdge
      then ExtG.iter_succ (fun w -> go next_node u w) g u
    in
    (* We (arbitrarily) make the root a (nonexistent) self-loop on init *)
    let root = (init, init) in
    let root_node =
      { pst_parent = None;
	pst_start = root;
	pst_end = None;
	pst_cls = -1;	
	pst_children = [] }
    in
    ExtG.iter_succ (fun w -> go root_node init w) g init;

    let rec mk_pst node =
      let children = List.map mk_pst node.pst_children in
      match node.pst_end with
      | Some pst_end -> PSTNode (node.pst_start,  pst_end, children)
      | None -> assert false
    in
    PSTNode (root, root, (List.map mk_pst root_node.pst_children))

  let construct_pst init g =
    try
      let pst = construct_pst init g in
      Log.debugf "Pst: %a" (format_pst pp) pst;
      pst
    with e -> begin
      Log.error "Failed to construct program structure tree";
      raise e
    end

  module Vertex = struct
    type atom = G.V.t
    type block = int

    include Putil.MakeCoreType(struct
      open RecGraph
      type t = (G.V.t, int) typ
      include Putil.MakeFmt(struct
	type a = t
	let format formatter = function
	  | Atom v    -> Format.fprintf formatter "Atom %a" pp v
	  | Block blk -> Format.fprintf formatter "Block %d" blk
      end)
      module Compare_t = struct
	type a = t
	let compare u v = match u, v with
	  | Atom u,  Atom v  -> G.V.compare u v
	  | Atom _,  _       -> 1
	  | _,       Atom _  -> -1
	  | Block u, Block v -> Pervasives.compare u v
      end
      let compare = Compare_t.compare
      let equal u v = compare u v = 0
      let hash = function
	| Atom v  -> Hashtbl.hash (G.V.hash v, 0)
	| Block v -> Hashtbl.hash (v, 1)
    end)
    let classify x = x
  end
  module R = RecGraph.Make(Vertex)(Putil.PInt)
  module HT = Hashtbl.Make(G.V)

  let rec get_entry g = function
    | RecGraph.Atom atom   -> atom
    | RecGraph.Block block -> get_entry g (R.block_entry g block)

  let rec get_exit g = function
    | RecGraph.Atom atom   -> atom
    | RecGraph.Block block -> get_exit g (R.block_exit g block)

  (** Iterate over the flattened (i.e., cfg) structure of an SESE graph *)
  let iter_flattened vertex edge pre_region post_region rg block =
    let g = R.block_body rg block in
    let visit_edge u v = edge (get_exit rg u) (get_entry rg v) in
    let rec visit_vertex = function
      | RecGraph.Atom v -> vertex v
      | RecGraph.Block r -> visit_region r
    and visit_region r =
      let body = R.block_body rg r in
      pre_region r;
      R.G.iter_vertex visit_vertex body;
      R.G.iter_edges visit_edge body;
      post_region r
    in
    R.G.iter_vertex visit_vertex g;
    R.G.iter_edges visit_edge g

  (** Display a region graph with boxes around each region *)
  let output_graph ch g =
    let open Pervasives in
    let emit s = output_string ch (s ^ "\n") in
    let max_region = ref 0 in
    let vstring v = String.escaped (Putil.pp_string pp v) in
    let new_region () =
      let id = !max_region in
      max_region := id + 1;
      "cluster" ^ (string_of_int id)
    in
    let pre_region _ = emit ("subgraph " ^ (new_region ()) ^ " {") in
    let post_region _ = emit "}" in
    let display_vertex v = emit (vstring v) in
    let display_edge u v = emit ((vstring u) ^ " -> " ^ (vstring v)) in
    emit "digraph G {";
    iter_flattened display_vertex display_edge pre_region post_region g 0;
    emit "}"

  let display g = ExtGraph.display_dot output_graph g

  let enclose block s e post_e (rg, g) =
    let module G = R.G in

    assert (G.mem_vertex g s);
    assert (G.mem_vertex g e);
    assert (G.mem_edge g e post_e);

    (* Compute the subgraph of g induced by the set consisting of all those
       vertices that are reachable from s without going through post_e. *)
    let rec go v graph =
      if G.mem_vertex graph v then graph else
	let f u graph =
	  if G.V.equal u post_e then graph
	  else G.add_edge (go u graph) v u
	in
	G.fold_succ f g v (G.add_vertex graph v)
    in
    let body = go s G.empty in
    let blockv = RecGraph.Block block in
    let rg = R.add_block rg block body ~entry:s ~exit:e in

    (* for every edge u->s, add u->block; for every e->v, add block->v *)
    let g = G.add_vertex g blockv in
    let in_block = G.mem_vertex body in
    let add_pred u g = if in_block u then g else G.add_edge g u blockv in
    let add_succ u g = if in_block u then g else G.add_edge g blockv u in
    let g = G.fold_pred add_pred g s g in
    let g = G.fold_succ add_succ g e g in

    (* remove enclosed vertices *)
    (rg, G.fold_vertex (flip G.remove_vertex) body g)

  (** Construct an SESE graph from a CFG.  Essentially, this just traverses a
      PST bottom-up, collapsing canonical SESE regions into region vertices as
      it goes. *)
  let construct cfg init exit =
    let open RecGraph in
    let ht = HT.create 991 in

    (* First id is 1: 0 is reserved for the top-level block *)
    let max_block = ref 0 in
    let get_block_id () =
      incr max_block;
      !max_block
    in

    let vertex v =
      try HT.find ht v
      with Not_found -> Atom v
    in
    let enclose (s0,s1) (e0,e1) g =
      let block = get_block_id () in
      Log.debugf "Enclose(%d) (%a->%a) ==> (%a->%a)"
	block pp s0 pp s1 pp e0 pp e1;

      let g = enclose block (vertex s1) (vertex e0) (vertex e1) g in
      HT.add ht s1 (Block block);
      HT.add ht e0 (Block block);
(*      display g;*)
      g
    in
    let rec visit (rg, g) = function
      | PSTNode (_, _, []) -> (rg, g) (* leaves are trivial *)
      | PSTNode (s, e, children) ->
	enclose s e (List.fold_left visit (rg, g) children)
    in
    let g =
      G.fold_vertex (fun v g -> R.G.add_vertex g (Atom v)) cfg R.G.empty
    in
    let g =
      G.fold_edges (fun v u g -> R.G.add_edge g (Atom v) (Atom u)) cfg g
    in
    Log.debugf "Construct SESE graph from init: %d" (name init);
(*    display g;*)
    let PSTNode (_, _, children) = construct_pst init cfg in
    let (rg, g) = List.fold_left visit (R.empty, g) children in
    R.add_block rg 0 g ~entry:(Atom init) ~exit:(Atom exit)

  let construct g ~entry:init ~exit:exit =
    let open RecGraph in
    if G.nb_vertex g <= 2 then begin
      let sg =
	G.fold_vertex (fun v sg -> R.G.add_vertex sg (Atom v)) g R.G.empty
      in
      let sg =
	G.fold_edges (fun v u sg -> R.G.add_edge sg (Atom v) (Atom u)) g sg
      in
      R.add_block R.empty 0 sg ~entry:(Atom init) ~exit:(Atom exit)
    end else
      try construct g init exit
      with e -> begin
	Log.error "Failed to construct region graph";
	raise e
      end

  let construct_triv g ~entry:init ~exit:exit =
    let open RecGraph in
    let sg =
      G.fold_vertex (fun v sg -> R.G.add_vertex sg (Atom v)) g R.G.empty
    in
    let sg =
      G.fold_edges (fun v u sg -> R.G.add_edge sg (Atom v) (Atom u)) g sg
    in
    R.add_block R.empty 0 sg ~entry:(Atom init) ~exit:(Atom exit)

  module T = Graph.Topological.Make(R.G)
  let fold_sese f cfg init acc =
    let open RecGraph in
    let rg =
      (* exit doesn't matter *)
      Log.time
	"Construct SESE graph"
	(fun () -> construct cfg ~entry:init ~exit:init)
	()
    in
    let rec visit v acc = match Vertex.classify v with
      | Block block ->
	let bentry = R.block_entry rg block in
	let bexit = R.block_exit rg block in
	let go v acc =
	  if Vertex.equal v bentry || Vertex.equal v bexit then acc
	  else visit v acc
	in
	let acc = R.G.fold_vertex go (R.block_body rg block) acc in
	if Vertex.equal bentry bexit then visit bentry acc
	else visit bentry (visit bexit acc)
      | Atom atom -> f atom acc
    in
    T.fold visit (R.block_body rg 0) acc

  let block rg =
    let ht = HT.create 991 in
    let f (block, vertex) = match vertex with
      | RecGraph.Atom v  -> HT.add ht v block
      | RecGraph.Block _ -> ()
    in
    BatEnum.iter f (R.vertices rg);
    fun v ->
      let id = HT.find ht v in
      if id = 0 then None else Some id

  include R
end
