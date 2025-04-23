(** reachability tree module *)

open Srk
open BatPervasives
module RG = Interproc.RG
module WG = Srk.WeightedGraph
module G = RG.G
module Int = SrkUtil.Int
module TF = TransitionFormula

module TransitionSystem = Srk.TransitionSystem
module Syntax = Srk.Syntax 
module Interpretation = Srk.Interpretation 


include Log.Make (struct
  let name = "reachTree"
end)

type equery = OverApprox | UnderApprox

module ART
    (G : sig
       type t
       type vertex
       type weight
       val fold_succ :  (vertex -> 'a -> 'a) -> t -> vertex -> 'a -> 'a
       val iter_succ_e :  (vertex * weight * vertex -> unit) -> t -> vertex -> unit
       val weight : t -> vertex -> vertex -> weight
       val summary : t -> vertex -> weight
       val compare_vertex : vertex -> vertex -> int
       val pp_vertex : Format.formatter -> vertex -> unit
     end)
    (L : sig
       type t
       val top : t
       val meet : t -> t -> t
       val leq : t -> t -> bool
       val pp : Format.formatter -> t -> unit
     end)
    (T : sig
       type t
       type label
       type state
       val check : label -> t list -> label -> [ `Valid of label list
                                               | `Invalid of state
                                               | `Unknown ]
       val post_model : state -> t -> state option
       val is_deterministic : t -> bool
       val mul : t -> t -> t
       val assume : label -> t
       val guard : t -> label
     end with type t = G.weight
          and type label = L.t) =
struct
  (* type for a tree node *)
  type node = int
  type state = T.state
  type weight = T.t

  module IntMap = BatMap.Make (Int)
  module VertexMap = BatMap.Make(struct
                         type t = G.vertex
                         let compare = G.compare_vertex
                       end)
  module StringMap = BatMap.Make (String)
  module ISet = BatSet.Make (Int)
  module DQ = BatDeque
  module ARR = Batteries.DynArray

  exception Mexception of string

  let log_formulas prefix formulas =
    List.iteri
      (fun i f ->
        logf "[formula] %s(%i): %a\n" prefix i
          L.pp f)
      formulas

  type t = {
    graph : G.t;
    entry : G.vertex;
    err_loc : G.vertex;
    mutable vtxcnt : int;
    mutable cfg_vertex : G.vertex IntMap.t;
    mutable parents : int IntMap.t;
    mutable labels : L.t IntMap.t;
    mutable covers : int IntMap.t;
    mutable children : int list IntMap.t;
    (* also maintain reverse map for each y, storing (x, y) that are in cover. *)
    (* i.e. reverse_covers[y] returns all x such that (x,y) is in the cover. *)
    mutable reverse_covers : ISet.t IntMap.t;
    (* precedent_nodes[v] stores all tree nodes mapping to CFG vertex v. Used in mc_close. *)
    mutable precedent_nodes : ISet.t VertexMap.t;
    mutable leaves : ISet.t;
  }

  let root = 0

  let make (g : G.t) (entry : G.vertex) (err_loc : G.vertex) =
    ref
      {
        graph = g;
        entry;
        err_loc;
        vtxcnt = 1;
        cfg_vertex = IntMap.add 0 entry IntMap.empty;
        parents = IntMap.add 0 (-1) IntMap.empty;
        labels = IntMap.add 0 L.top IntMap.empty;
        children = IntMap.add 0 [] IntMap.empty;
        covers = IntMap.empty; (* for (u, v) in cover, u is ancestor of v and label(v) |= label(u). v is covered if (u, v) in cover. Then cover[v] = u. *)
        reverse_covers = IntMap.empty; (* for each v, store the v's that cover it: i.e. cover[v] *)
        precedent_nodes = VertexMap.empty;
        leaves = ISet.empty;
      }

  let get_err_loc (art : t ref) = !art.err_loc
  let get_entry (art: t ref) = !art.entry 

  (** [print_tree t ident v] prints an ART t with indentation `ident` rooted at node v *)
  let print_tree (art : t ref) (indent : string) (v : node) =
    let rec print_tree_ (art : t ref) indent v =
      logf "%s|" indent;
      logf "%s+-%d(%a)" indent v
        G.pp_vertex (IntMap.find v !art.cfg_vertex);
      List.iter
        (fun x -> print_tree_ art (indent ^ " ") x)
        (IntMap.find_default [] v !art.children)
    in
    logf "*";
    print_tree_ art indent v

  (*  [parent t i] gets parent of node i in tree t.  *)
  let parent (art : t ref) (i : node) : node = IntMap.find i !art.parents
    

  (*  [t %-> i]: get CFG vertex mapped by node i in tree t. *)
  let maps_to (art : t ref) (i : node) : G.vertex =
    try IntMap.find i !art.cfg_vertex
    with _ -> failwith @@ Printf.sprintf "maps_to: not found tree node %d\n" i

  let parent_weight (art : t ref) (i : node) =
    let parent = IntMap.find i !art.parents in
    if parent < 0 then
      None
    else
      Some (parent, G.weight !art.graph (maps_to art parent) (maps_to art i))

  (* [tree_path t u] returns list of tree nodes that form the corrsp. tree path from root of t to tree node u *)
  let tree_path (art : t ref) ?(src=root) (u : node) : node list =
    let rec tree_path_rev art u =
      if u = root || u = src then [ u ]
      else u :: tree_path_rev art (parent art u)
    in
    List.rev @@ tree_path_rev art u

  (* [children t v] returns children of tree node v in tree t. *)
  let children (art : t ref) (v : node) : node list =
    IntMap.find v !art.children

  (* [descendants t v] returns descendants of tree node v in tree t in DFS order. *)
  let rec descendants (art : t ref) (v : node) : node list =
    let v_children = children art v in
    v :: List.fold_left (fun l ch -> descendants art ch @ l) [] v_children

  (* return leaves of the tree. *)
  let leaves (art : t ref) : node list = 
    !art.leaves |> ISet.to_list 

  (* is a node in tree a leaf? *)
  let is_leaf (art : t ref) (v : node) : bool =
    let chs = children art v in
    List.length chs == 0

  (* [label t v] returns the node label of tree node v in tree t. *)
  let label (art : t ref) (v : node) : L.t = IntMap.find v !art.labels

  (* (replaces) sets a label at v *)
  let set_label (art : t ref) (v : node) (lbl : L.t) =
    !art.labels <- IntMap.add v lbl !art.labels

  (* [get_precedent_nodes t v] retrieves a sequence of precedent nodes of tree node vin preorder in tree t. *)
  (* the list of precedent nodes for a cfg vertex is a list of tree nodes which map to the same cfg location, ordered by < on integers. *)
  let get_precedent_nodes (art : t ref) (v : node) =
    let cfg_vertex = maps_to art v in
    let precedents_set =
      VertexMap.find_default ISet.empty cfg_vertex !art.precedent_nodes
    in
    ISet.elements precedents_set

  (** retrieves a new ART node ID, ensuring all ART nodes have distinct IDs in increasing order according to their creation *)
  let get_id (art : t ref) : node =
    let new_id = !art.vtxcnt in
    !art.vtxcnt <- !art.vtxcnt + 1;
    new_id

  (* [update_leaf art x] attempts to update leaf structure; if x is a leaf then x is marked as leaf, otherwise x is unmarked as leaf. *)
  let update_leaf (art: t ref) (x: node) = 
    if is_leaf art x then 
      !art.leaves <- ISet.add x !art.leaves 
    else 
      !art.leaves <- ISet.remove x !art.leaves 

  (* Add new tree leaf mapping to CFG vertex v and with parent tree node p. *)
  let add_tree_vertex (art : t ref) ?(label = L.top) (v : G.vertex)
      (p : node) =
    (* sequentially add v to the lists, indexed by !vtxcnt *)
    let new_vertex = get_id art in
    (* note that new_vertex refers to a new tree vertex, where as v is a corresp. cfg location. *)
    !art.cfg_vertex <- IntMap.add new_vertex v !art.cfg_vertex;
    !art.parents <- IntMap.add new_vertex p !art.parents;
    !art.labels <- IntMap.add new_vertex label !art.labels;
    !art.children <- IntMap.add new_vertex [] !art.children;
    (* set children of parent to be !vtxcnt :: children. *)
    if p >= 0 then
      !art.children <-
        IntMap.add p (new_vertex :: IntMap.find p !art.children) !art.children;
    (* Add v to precedent_nodes. *)
    let precedent_nodes =
      VertexMap.find_default ISet.empty v !art.precedent_nodes
      |> ISet.add new_vertex
    in
    !art.precedent_nodes <-
      VertexMap.add v precedent_nodes !art.precedent_nodes;
    update_leaf art p;
    update_leaf art new_vertex;
    new_vertex 

  (** expand:  
        for every out-neighbor y of v, first try deriving a post-state model of v-> y, if successful, put it
          on the concolic execution worklist. Otherwise, it is a frontier node, and put it on the 
          refinement worklist. *)


  (* New (more general) API for expansion that supports summary-guided testing 
    * and an IMPACT-style algorithm. The expansion is performed guarded by the pre-image
      of [tr], where, in GPS and SGT, [tr] is a single-target path summary, in IMPACT, [tr]
      is the identity transition. More specifically, for each out-neighbor u of G(v), we 
      first test if m /\ tr is SAT, if so, then this out-neighbor is non-frontier. Otherwise,
      this out neighbor is a frontier.  *)
  let expand (art: t ref) (v: node) (m: T.state) =
    let vg = maps_to art v in 
    let new_concolic_nodes, new_frontier_nodes = (ref [], ref []) in 
    (* visit out-neighbors of v *)
    G.iter_succ_e 
      (fun (_, weight, y) -> 
        let weight =
          if T.is_deterministic weight then weight
          else T.mul weight (T.assume @@ T.guard @@ G.summary !art.graph y)
        in 
        match T.post_model m weight with
        | Some y_model ->
           let new_vtx = add_tree_vertex art y v in
           new_concolic_nodes := (new_vtx, y_model) :: !new_concolic_nodes
        | None ->
           let new_node = add_tree_vertex art y v in
           new_frontier_nodes := new_node :: !new_frontier_nodes)
      !art.graph vg;
    (* make it FIFO *)
    (List.rev !new_concolic_nodes, List.rev !new_frontier_nodes)
    

  (** maintenance of coverings *) 

  (* for w that is an ancestor/precedent of v, *)
  (* Adds (v -> w) to covering relation if possible and returns true, false otherwise. *)
  (* note that (v, w) in covering if stateLabel(v) IMPLIES stateLabel(w) *)
  let cover (art : t ref) v w =
    let v_label = label art v in
    let w_label = label art w in
    if maps_to art v <> maps_to art w then
      failwith
      @@ Format.asprintf "error: %d->%a but %d->%a\n"
           v
           G.pp_vertex (maps_to art v)
           w
           G.pp_vertex (maps_to art w)
    else if L.leq v_label w_label then begin
        logf "   cover success (v=%d, w=%d). \n" v w;
        log_formulas "        v label " [ v_label ];
        log_formulas "        w label " [ w_label ];
        let reverse_covers_w =
          IntMap.find_default ISet.empty w !art.reverse_covers
        in
        !art.covers <- IntMap.add v w !art.covers;
        !art.reverse_covers <-
          IntMap.add w (ISet.add v reverse_covers_w) !art.reverse_covers;
        true
    end else false


  (*     it returns (`true`, wl) iff covering succeeds at v and wl is a worklist of nodes to be refined. *)

  (** [close art v] visits precedents of v in tree and attempts to derive covering relations from v. *)
  let close (art : t ref) (v : node) =
    (* A _precedent_ of v in tree is any vertex u<v such that u, v map to the same CFG locations, where < is integer less than. *)
    let precedents = get_precedent_nodes art v in
    (* Fold from first node in preorder to the right. If covering succeeds, do not continue covering. *)
    let result =
      List.fold_right
        (fun w (status, wl) ->
          if status || w == v || w > v (* preorder constraint *) then
            (status, wl)
          else
            (* try to "cover v" by deciding if v --> w. If so, no need to further explore v. *)
            (* cover v using w *)
            let cover_success = cover art v w in
            let wl' = ref wl in
            (if cover_success then
               (* remove, for each descendant of v, nodes that are sinks of covers. *)
               let v_descendants = descendants art v in
               List.iter
                 (fun y ->
                   (* Find relations (x,y) in covering relation where y is descendant of v. *)
                   if y <> v then (
                     (* xs = {x | x -> y} *)
                     let xs =
                       IntMap.find_default ISet.empty y !art.reverse_covers
                     in
                     (* Iterate through and remove pairs (x, y) from covering relation. *)
                     (* Step 1: Remove (x |-> y) from !ptt.covers. *)
                     ISet.iter
                       (fun x -> !art.covers <- IntMap.remove x !art.covers)
                       xs;
                     (* Step 2: Remove (y |-> xs) from !pthit.reverse_covers. *)
                     !art.reverse_covers <- IntMap.remove y !art.reverse_covers;
                     (* Step 3: add xs to worklist. *)
                     ISet.iter
                       (fun _x ->
                         (* add x's subtree leaves back to the worklist. *)
                         (* Zak: TODO: This adds *all* leaves back to the worklist *)
                         let x_leaves = leaves art in
                         List.iter
                           (fun x_leaf ->
                            if not (is_leaf art x_leaf) then failwith "ERR: found non-leaf among leaves set of ART";
                              logf
                               "         close: adding %d back to worklist \n"
                               x_leaf;
                             wl' := x_leaf :: !wl')
                           x_leaves)
                       xs))
                 v_descendants);
            (cover_success, !wl'))
        precedents (false, [])
    in
    result

  (* Checks if tree node v is covered. It is covered if its ancestors or it is in covering relation. *)
  let rec is_covered (art : t ref) v =
    match IntMap.find_opt v !art.covers with
    | None -> if v == 0 then false else is_covered art (parent art v)
    | Some u ->
        logf "  | covered by %d\n" u;
        true

  (* refine the label of each tree node u along path from tree root to v. *)
  let refine (art : t ref) path interpolants : node list =
    let worklist = ref [] in
    List.iter2
      (fun u interpolant ->
        let u_label = label art u in
        let u_label' = L.meet u_label interpolant in
        log_formulas
          (Format.asprintf "[relabelling %d CFG vertex %a] to label: " u
             G.pp_vertex (maps_to art u))
          [ u_label' ];
        set_label art u u_label';
        (* remove ( * -> u) in covering relation; we just refined label(u) so implications of form label(y)->label(u)
           might not hold anymore. *)
        match IntMap.find_opt u !art.reverse_covers with
        | None -> ()
        | Some l ->
            (* remove covers (List.iter (fun x -> Printf.printf " (%d->%d)" x u) l *)
            let u_coverers =
              ISet.fold
                (fun x coverers ->
                  (* test if label(x) --> new label(u)*)
                  let x_label = label art x in
                  let u_label = label art u in
                  if L.leq x_label u_label then
                    (logf
                       "    refine: cover (x %d-> u %d) still holds\n" x u;
                     log_formulas " x label: " [ x_label ];
                     log_formulas " u label: " [ u_label ];
                     ISet.add x coverers (* unchanged. *))
                  else begin
                      (* remove (x, u) from covering. *)
                      logf "   refine: removing cover (%d->%d)\n"
                        x u;
                      !art.covers <- IntMap.remove x !art.covers;
                      (* add x's subtree leaves back to the worklist. *)
                      (* Zak: TODO: This adds *all* leaves back to the worklist *)
                      let x_leaves = leaves art in
                      List.iter
                        (fun x_leaf ->
                          logf
                            "         refine: adding %d back to worklist \n"
                            x_leaf;
                            if not (is_leaf art x_leaf) then failwith "ERROR: found a non-leaf node in leaves set of ART";
                          worklist := x_leaf :: !worklist)
                        x_leaves;
                      l
                    end)
                l
                ISet.empty
            in
            !art.reverse_covers <- IntMap.add u u_coverers !art.reverse_covers)
      path
      interpolants;
    !worklist
  
  let rec glue l = 
    match l with 
    | a :: b :: t -> (a, b) :: (glue (b :: t))
    | _ -> []

  

  (* convention: w is an ancestor of v. returns true if we can add (v, w) to covers such that label(v) |= label(w) *)
  let force_cover (art : t ref) v w = (* check if v_label -> w_label where v is an ancestor at w *)
    if maps_to art v <> maps_to art w then (false, []) 
    else begin 
      logf "force_cover(%d, %d)\n" v w;
      (* let v_label = label art v in *)
      let w_label = label art w in 
      let artpath = tree_path art ~src:w v in
      let path_weights = 
        artpath 
        |> glue 
        |> List.map (fun (x, y) -> 
               G.weight !art.graph (maps_to art x) (maps_to art y))
      in
      match T.check w_label path_weights w_label with
      | `Valid itps -> 
        let new_frontiers = refine art (List.tl artpath) (List.tl itps) in
        if cover art v w then
          (true, new_frontiers)
        else
          failwith "error: force_cover is buggy!"

      | `Invalid _ -> (false, []) 
      | `Unknown -> failwith "force_cover: interpolation failed with status UNKNOWN."
    end
  

  (** a more lightweight version of close *)
  let lclose (art: t ref) v =
    let rec go u = 
      if u = -1 then (false, [])
      else begin   
        if maps_to art u <> maps_to art v then 
          try let p = parent art u in go p 
          with Not_found -> (false, []) 
         else 
          begin match force_cover art v u with 
        | (true, frontiers) -> (true, frontiers)
        | (false, _) -> 
          try 
            let p = parent art u in go p 
          with Not_found -> (false, [])
        end 
      end
    in
      let res = match v with 
      | 0 -> (false, [])
      | _ -> go (parent art v) in 
      let bb, _ = res in 
      logf " --- lclose result of %d : %b ---\n" v  bb ; res


  (** TODO: [deprecated] procedures for lightweight verification of ART invariants *)
    
  let _verify_well_labelled_tree (t : t ref) =
    let rec aux v =
      let children = children t v in
      match children with
      | [] (* leaf node *) -> (
          match IntMap.find_opt v !t.covers with
          | None ->
              logf "!!! found uncovered leaf: %d\n" v;
              G.fold_succ
                (fun y _ ->
                  logf
                    "  ERROR ERROR ERROR: mapped cfg vertex %a has \
                     out-neighbor %a\n"
                    G.pp_vertex (maps_to t v)
                    G.pp_vertex y;
                  false)
                !t.graph (maps_to t v) true
          | Some _ -> true)
      | _ -> (
          match IntMap.find_opt v !t.covers with
          | None ->
              logf "node %d uncovered\n" v;
              List.fold_left (fun acc u -> aux u && acc) true children
          | Some u ->
              logf "node %d covered by %d\n" v u;
              true)
    in
    logf "verifying well-labelledness of ART...\n";
    let r = aux 0 in
    logf "...done verifying well-labelledness of ART\n";
    r

  let _check_covering_welformedness (t : t ref) =
    logf "checking welformedness of covering relations\n";
    IntMap.iter
      (fun dst covered_from ->
        ISet.iter
          (fun src ->
            logf "checking if (%d, %d) in covering\n" src dst;
            match IntMap.find_opt src !t.covers with
            | Some dst' ->
                if dst' <> dst then
                  failwith
                  @@ Printf.sprintf "ERROR: (%d, %d) in covering\n" src dst'
            | None -> failwith "ERROR: not in covering")
          covered_from)
      !t.reverse_covers;
    logf "performing a reverse check\n";
    IntMap.iter
      (fun src dst ->
        match IntMap.find_opt dst !t.reverse_covers with
        | Some reverse_covers -> (
            match ISet.mem src reverse_covers with
            | false ->
                failwith
                @@ Printf.sprintf
                     "ERROR: (%d, %d) in t.covers but %d not in %d's \
                      reverse_covers\n"
                     src dst src dst
            | true -> ())
        | None ->
            failwith
            @@ Printf.sprintf
                 "ERROR: (%d, %d) in t.covers but no list found in \
                  reverse_covers\n"
                 src dst)
      !t.covers;
    logf "...done checking welformedness of covering relations\n"

  (** pretty-printing functionalities *)
  let tree_printer_get_name (art : t ref) i =
    match IntMap.find_opt i !art.covers with
    | None -> Format.asprintf "%d(%a)" i G.pp_vertex (maps_to art i)
    | Some j ->
        Format.asprintf "[%d(%a)]->%d" i G.pp_vertex (maps_to art i) j

  let log_art (art : t ref) =
    logf " +----------------- ART ----------------+\n";
    let string_of_art =
      Tree_printer.to_string ~line_prefix:"* "
        ~get_name:(tree_printer_get_name art)
        ~get_children:(children art) 0
    in
    logf "%s" string_of_art;
    logf " +----------------- ART ----------------+\n"

  let log_node u = 
    logf " node: visit %d\n" u 
  
  let of_node u = u

  let pp_node = Format.pp_print_int
end
