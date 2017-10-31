(** Implementation of Lengauer and Tarjan's dominance algorithm *)

open Core
open Cil
open Srk
open Apak

module Make (G : Graph.Sig.G) = struct

  (* Dominator tree *)
  module T = Graph.Imperative.Digraph.Concrete(G.V)
  module HT = Hashtbl.Make(G.V)
  module VS = Set.Make(G.V)

  (* Get a set of all vertices in a graph *)
  let get_vertices graph = G.fold_vertex VS.add graph VS.empty

  exception No_parent
  let get_predecessor tree v =
    match T.pred tree v with
    | [p] -> p
    | _ -> raise No_parent

  let rec get_dominators tree v =
    try VS.add v (get_dominators tree (get_predecessor tree v))
    with No_parent -> VS.singleton v

  (* Do not export.  Get a set of all vertices in a graph that are dominated
     by a particular vertex. *)
  let get_dominated_g graph init v =
    (* Do a depth first search, stopping whenever the vertex in question is
       reached.  Those vertices that are not visited by the dfs are dominated by
       v. *)
    let visited = ref (VS.singleton v) in
    let visit w = visited := VS.add w (!visited) in
    let was_visited w = VS.mem w (!visited) in
    let rec dfs w =
      if not (was_visited w) then begin
        visit w;
        G.iter_succ dfs graph w
      end
    in
    dfs init;
    VS.add v (VS.diff (get_vertices graph) (!visited))

  (** Find the set of descendents of v in a dominator tree *)
  let rec get_dominated dom_tree v =
    let add_child c = VS.union (get_dominated dom_tree c) in
    T.fold_succ add_child dom_tree v (VS.singleton v)

  (** Check that a dominator tree was computed correctly.  This procedure is
      inefficient, and should only be called in debug mode *)
  let sanity_check graph init dom =
    let check_node v =
      let graph_dom = get_dominated_g graph init v in
      let tree_dom = get_dominated dom v in
      if not (VS.equal graph_dom tree_dom)
      then failwith "Dominator tree sanity check failed"
    in
    T.iter_vertex check_node dom


  let compute graph init =
    let size = G.nb_vertex graph in

    (* bidirectional mapping between vertices and their dfs number *)
    let dfs_num = HT.create size in
    let vertex = Array.make size init in

    let parent = Array.make size 0 in  (* parent in dfs spanning tree *)
    let sdom = Array.init size (fun n -> n) in  (* semidominators *)

    (* During sdom computation, map each vertex w to the vertex u for which
       sdom(u) is minimal among vertices u satisfying sdom(w) ->+ u ->* w.
       During dominator tree construction, map each vertex to its immediate
       dominator. *)
    let idom = Array.make size 0 in

    let pred = Array.make size [] in (* predecessors in graph *)
    let add_pred v p = pred.(v) <- p::pred.(v) in

    (* Eval/link structure used for computing sdom and idom.  The link
       operations will build the dfs spanning tree from the bottom up, and
       eval(v) returns the vertex w such that sdom(w) is minimal and w ->* v in
       the current forest *)
    let module SemiOrder =
    struct
      type t = int
      let mul x y = if sdom.(x) < sdom.(y) then x else y
    end
    in
    let module EL = EvalLink.Make(G.V)(SemiOrder) in
    let (add_el, eval, link) =
      let el = EL.create size in
      (EL.add el, EL.eval el, EL.link el)
    in
    let iter_successors v f = G.iter_succ f graph v in

    (* Give each vertex a number indicating when it was reached in the dfs
       search.  Construct the dfs spanning tree and initialize pred.  Return
       the dfs number of the vertex dfs was called on.  *)
    let rec dfs = let next = ref 0 in fun v ->
        let n = !next in
        let get_dfs_num w =
          try HT.find dfs_num w
          with Not_found -> (* not yet visited *)
            let w_num = dfs w in
            parent.(w_num) <- n;
            w_num
        in
        next := !next + 1;

        (* Maintain bidirectional mapping between vertices and their dfs
           	   number *)
        HT.add dfs_num v n;
        vertex.(n) <- v;
        add_el v n;

        iter_successors v (fun w -> add_pred (get_dfs_num w) n);
        n
    in
    ignore(dfs init);

    (* Traverse vertices in reverse dfs order.  Invariant: eval/link is the
       forest constructed from the edges of the DFS spanning tree using only
       vertices with DFS numbers greater than w.  So for any vertex v,

         eval(v) = | v if v < w
                   | u such that u > w, u ->* v, and sdom(u) is minimal

       Bucket maps each vertex to the vertices it semidominates.  This
       is necessary for computing immediate dominators.  More
       specifically, it helps compute (for each vertex w) the vertex u
       for which sdom(u) is minimal among vertices u satisfying
         sdom(w) ->+ u ->* w.

       We can obtain u from the eval/link structure, but we have to
       wait until we have added all the proper descendents of sdom(w)
       to the eval/link forest.  We use the bucket to store those w
       that still need u to be computed until we reach sdom(w).

       Given u, we can compute immediate dominators by Corollary 1 of
       Lengauer and Tarjan:
         idom(w) = | sdom(w) if sdom(w) = sdom(u)
                   | idom(u) otherwise
    *)
    (let bucket = Array.make size [] in
     let add_to_bucket b v = bucket.(b) <- (v::bucket.(b)) in

     for w = (size - 1) downto 1 do
       let parent_w = parent.(w) in

       let set_min_sdom v =
         sdom.(w) <- (min sdom.(w) sdom.(eval vertex.(v)))
       in
       (* sdom(w) = min({sdom(w)}
                           U {sdom(u) : u>w /\ exists v. (v,w) in E and u ->* v}

          note: we're guaranteed that u > w, since we're iterating in reverse
          dfs order. *)
       List.iter set_min_sdom pred.(w);

       add_to_bucket sdom.(w) w;
       link vertex.(parent_w) vertex.(w);

       (* Set idom.(v) to be the vertex u for which sdom(u) is minimal
          		among vertices u satisfying sdom(w) ->+ u ->* v. *)
       List.iter (fun v -> idom.(v) <- eval vertex.(v)) bucket.(parent_w);
       bucket.(parent_w) <- []
     done);

    (* Construct explicit dominator tree *)
    let dom_tree = T.create ~size:size () in
    let get_dom_tree_vertex =
      let map = Array.init size (fun v -> T.V.create vertex.(v)) in
      fun v -> map.(v)
    in
    let add_edge x y =
      T.add_edge dom_tree (get_dom_tree_vertex x) (get_dom_tree_vertex y)
    in
    (* Recalling Corollary 1 and that idom(w) is currently the vertex u for
       which sdom(u) is minimal among vertices u satisfying
       	     sdom(w) ->+ u ->* v,
             idom(w) = | sdom(w) if sdom(w) = sdom(idom(w))
                       | idom(idom(w)) otherwise
    *)
    for w = 1 to (size - 1) do
      let u = idom.(w) in
      let u_sdom = sdom.(u) in
      let w_sdom = sdom.(w) in
      let w_idom = if u_sdom == w_sdom then w_sdom else idom.(u) in
      add_edge w_idom w
    done;
    if !Log.debug_mode then sanity_check graph init dom_tree;
    dom_tree

  (** Compute least common ancestor in a dominator tree *)
  let get_lca tree x y =
    let x_dom = get_dominators tree x in
    let rec find v =
      if VS.mem v x_dom then v
      else find (get_predecessor tree v)
    in
    find y

  let rec fold_to_ancestor f a tree v ancestor =
    if G.V.equal v ancestor then a
    else fold_to_ancestor f (f a v) tree (get_predecessor tree v) ancestor
end

