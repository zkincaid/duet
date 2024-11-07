(** reachability tree module *)

open Srk
open BatPervasives
open Syntax
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
    (Ctx : Srk.Syntax.Context)
    (K : sig
      type t
      type var

      val pp : Format.formatter -> t -> unit
      val guard : t -> Ctx.t formula
      val transform : t -> (var * Ctx.t arith_term) BatEnum.t
      val mem_transform : var -> t -> bool
      val get_transform : var -> t -> Ctx.t arith_term
      val assume : Ctx.t formula -> t
      val mul : t -> t -> t
      val conjunct : t -> t -> t
      val add : t -> t -> t
      val zero : t
      val one : t
      val star : t -> t
      val exists : (var -> bool) -> t -> t
      val contains_havoc : t -> bool
      val contextualize :  t -> t -> t  -> [ `Sat of t | `Unsat ]
      val interpolate_or_concrete_model : t list -> Ctx.t Syntax.formula 
            -> [`Valid of Ctx.t Syntax.formula list 
                 | `Invalid of Ctx.t Interpretation.interpretation | `Unknown ]

      val get_post_model :
        Ctx.t Interpretation.interpretation ->
        t ->
        Ctx.t Interpretation.interpretation option
      val is_deterministic : t -> bool
    end)
    (TS : sig
      type vertex
      type transition = K.t
      type t
      type query
      type reverse_query

      val empty : t
      val path_weight : query -> vertex -> transition
      val call_weight : query -> vertex * vertex -> transition
      val set_summary : query -> vertex * vertex -> transition -> unit
      val get_summary : query -> vertex * vertex -> transition


      val mk_reverse_query : query -> vertex -> reverse_query
      val exit_summary : reverse_query -> vertex -> vertex -> K.t
      val target_summary : reverse_query -> vertex -> K.t

      val omega_path_weight :
        query -> (transition, 'b) Srk.Pathexpr.omega_algebra -> 'b

      val forward_invariants_ivl :
        t -> vertex -> (vertex * Ctx.t Srk.Syntax.formula) list

      val forward_invariants_ivl_pa :
        Ctx.t Srk.Syntax.formula list ->
        t ->
        vertex ->
        (vertex * Ctx.t Srk.Syntax.formula) list

      val simplify : (vertex -> bool) -> t -> t

      val iter_succ_e :
        (vertex * transition TransitionSystem.label * vertex -> unit) ->
        t ->
        vertex ->
        unit

      val edge_weight : t -> vertex -> vertex -> K.t Srk.TransitionSystem.label

      val fold_succ_e :
        (vertex * K.t Srk.TransitionSystem.label * vertex -> 'b -> 'b) ->
        t ->
        vertex ->
        'b ->
        'b
    end)
    (PN : sig
      type t 

      val make : TS.vertex * TS.vertex -> t
      val string_of : t -> string
      val of_string : string -> t

      (* lexicographic comparison using Stdlib.compare *)
      val compare : t -> t -> int
    end)
    (VN : sig
      val to_vertex : int -> TS.vertex
      val of_vertex : TS.vertex -> int
    end)
    (Summarizer : sig
      type t
      val over_proc_summary : t -> PN.t -> K.t
      val under_proc_summary : t -> PN.t -> K.t
      val set_over_proc_summary : t -> PN.t -> K.t -> unit
      val set_under_proc_summary : t -> PN.t -> K.t -> unit
      val refine_over_summary : t -> PN.t -> K.t -> unit
      val refine_under_summary : t -> PN.t -> K.t -> unit
      val path_weight_intra : t -> TS.vertex -> TS.vertex -> K.t
      val path_weight_inter : t -> TS.vertex -> K.t
    end) = 
struct
  (* type for a tree node *)
  type node = int

  module ProcMap = BatMap.Make (PN)
  module IntMap = BatMap.Make (Int)
  module StringMap = BatMap.Make (String)
  module ISet = BatSet.Make (Int)
  module DQ = BatDeque
  module ARR = Batteries.DynArray

  type idq_t = int BatDeque.t
  type state_formula = Ctx.t Syntax.formula

  exception Mexception of string

  let mk_true () = Syntax.mk_true Ctx.context
  let mk_false () = Syntax.mk_false Ctx.context

  let log_formulas prefix formulas =
    List.iteri
      (fun i f ->
        logf "[formula] %s(%i): %a\n" prefix i
          (Syntax.pp_expr Ctx.context)
          f)
      formulas

  let log_weights prefix weights =
    List.iteri
      (fun i f -> logf "[weight] %s(%i): %a\n" prefix i K.pp f)
      weights

  let log_model prefix model =
    logf "[model] %s: %a\n" prefix Interpretation.pp model

  type t = {
    graph : TS.t;
    entry : TS.vertex;
    err_loc : TS.vertex;
    mutable vtxcnt : int;
    mutable cfg_vertex : TS.vertex IntMap.t;
    mutable parents : int IntMap.t;
    mutable labels : Ctx.t Syntax.formula IntMap.t;
    mutable covers : int IntMap.t;
    mutable children : int list IntMap.t;
    (* also maintain reverse map for each y, storing (x, y) that are in cover. *)
    (* i.e. reverse_covers[y] returns all x such that (x,y) is in the cover. *)
    mutable reverse_covers : ISet.t IntMap.t;
    (* precedent_nodes[v] stores all tree nodes mapping to CFG vertex v. Used in mc_close. *)
    mutable precedent_nodes : ISet.t IntMap.t;
    interproc : Summarizer.t;
    mutable leaves : ISet.t;
  }

  let root = 0

  let make (g : TS.t) (entry : TS.vertex) (err_loc : TS.vertex) (pre_state: state_formula) interproc =
    ref
      {
        graph = g;
        entry;
        err_loc;
        vtxcnt = 1;
        cfg_vertex = IntMap.add 0 entry IntMap.empty;
        parents = IntMap.add 0 (-1) IntMap.empty;
        labels = IntMap.add 0 pre_state IntMap.empty;
        children = IntMap.add 0 [] IntMap.empty;
        covers = IntMap.empty; (* for (u, v) in cover, u is ancestor of v and label(v) |= label(u). v is covered if (u, v) in cover. Then cover[v] = u. *)
        reverse_covers = IntMap.empty; (* for each v, store the v's that cover it: i.e. cover[v] *)
        precedent_nodes = IntMap.empty;
        leaves = ISet.empty;
        interproc;
      }

  let get_summarizer (art : t ref) = !art.interproc
  let get_err_loc (art : t ref) = !art.err_loc
  let get_entry (art: t ref) = !art.entry 

  (** [print_tree t ident v] prints an ART t with indentation `ident` rooted at node v *)
  let print_tree (art : t ref) (indent : string) (v : node) =
    let rec print_tree_ (art : t ref) indent v =
      logf "%s|" indent;
      logf "%s+-%d(%d)" indent v
        (IntMap.find v !art.cfg_vertex |> VN.of_vertex);
      List.iter
        (fun x -> print_tree_ art (indent ^ " ") x)
        (IntMap.find_default [] v !art.children)
    in
    logf "*";
    print_tree_ art indent v

  (*  [parent t i] gets parent of node i in tree t.  *)
  let parent (art : t ref) (i : node) : node = IntMap.find i !art.parents

  (*  [t %-> i]: get CFG vertex mapped by node i in tree t. *)
  let maps_to (art : t ref) (i : node) : TS.vertex =
    try IntMap.find i !art.cfg_vertex
    with _ -> failwith @@ Printf.sprintf "maps_to: not found tree node %d\n" i

  (* deprecated:
  (* [cfg_edge_weight t mode u v] returns the edge weight of edge (u, v) in ART t.
       If (u, v) maps to a call-edge (x, y) in the CFG, return the over-approximate summary if
      `mode` is set to `OverApprox`, and return an under-approximate summary otherwise. *)
  let edge_weight (art : t ref) (mode : equery) (u : node) (v : node) =
    let t = !art in
    match TS.edge_weight t.graph (maps_to art u) (maps_to art v) with
    | TransitionSystem.Weight w -> w
    | TransitionSystem.Call (a, b) -> (
        (* (a, b) is a pair of CFG vertices that uniquely identify a call *)
        let a, b = (VN.to_vertex a, VN.to_vertex b) in
        match mode with
        | OverApprox -> Summarizer.over_proc_summary t.interproc (PN.make (a, b))
        | UnderApprox ->
            Summarizer.under_proc_summary t.interproc (PN.make (a, b)))
  
  let edge_weight (art : t ref) (mode : equery) (u : node) (v : node) =
    let t = !art in
    match TS.edge_weight t.graph (maps_to art u) (maps_to art v) with
    | TransitionSystem.Weight w -> w
    | TransitionSystem.Call (a, b) -> (
        (* (a, b) is a pair of CFG vertices that uniquely identify a call *)
        let a, b = (VN.to_vertex a, VN.to_vertex b) in
        match mode with
        | OverApprox -> Summarizer.over_proc_summary t.interproc (PN.make (a, b))
        | UnderApprox ->
            Summarizer.under_proc_summary t.interproc (PN.make (a, b)))


            *)
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

  (* return leaves of subtree rooted at v. *)
  (* let rec leaves (art : t ref) (v : node) : node list =
    let chs = children art v in
    if List.length chs == 0 then [ v ]
    else
      List.fold_left
        (fun child_leaves ch ->  (leaves art ch) @ child_leaves)
        [] chs *)
  let leaves (art : t ref) (v : node) : node list = 
    !art.leaves |> ISet.to_list 

  (* is a node in tree a leaf? *)
  let is_leaf (art : t ref) (v : node) : bool =
    let chs = children art v in
    List.length chs == 0

  (* [label t v] returns the node label of tree node v in tree t. *)
  let label (art : t ref) (v : node) : state_formula = IntMap.find v !art.labels

  (* (replaces) sets a label at v *)
  let set_label (art : t ref) (v : node) (lbl : state_formula) =
    !art.labels <- IntMap.add v lbl !art.labels

  (* [get_precedent_nodes t v] retrieves a sequence of precedent nodes of tree node vin preorder in tree t. *)
  (* the list of precedent nodes for a cfg vertex is a list of tree nodes which map to the same cfg location, ordered by < on integers. *)
  let get_precedent_nodes (art : t ref) (v : node) =
    let cfg_vertex = maps_to art v in
    let precedents_set =
      IntMap.find_default ISet.empty (VN.of_vertex cfg_vertex)
        !art.precedent_nodes
    in
    ISet.elements precedents_set

  (* deprecated:
  (* [path_condition t mode u] returns a list of edge weights that form the path condition from root of t to tree node u.  *)
  (* if `cutoff` is specified to a non-zero value, then [path_condition] will try to stop at intermediate ancestor `cutoff`. *)
  (* Over-approximate summaries are substituted in for call-edge locations if mode = `OverApprox`, and under-approximate *)
  (* summaries are substituted in otherwise. *)
  let path_condition (art : t ref) (mode : equery) ?(cutoff = 0) (u : node) =
    if u == 0 || cutoff = u then []
    else
      let rec visit (art : t ref) (u : node) =
        let v = parent art u in
        if v = 0 then [ edge_weight art mode 0 u ]
        else if v = cutoff then
          (* v=0 case is already handled above *)
          [ edge_weight art mode cutoff u ]
        else edge_weight art mode v u :: visit art v
      in
      List.rev (visit art u)
  *)

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
  let add_tree_vertex (art : t ref) ?(label = mk_true ()) (v : TS.vertex)
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
      IntMap.find_default ISet.empty (VN.of_vertex v) !art.precedent_nodes
      |> ISet.add new_vertex
    in
    !art.precedent_nodes <-
      IntMap.add (VN.of_vertex v) precedent_nodes !art.precedent_nodes;
    update_leaf art p;
    update_leaf art new_vertex;
    new_vertex 
  
  (** expand:  
        for every out-neighbor y of v, first try deriving a post-state model of v-> y, if successful, put it
          on the concolic execution worklist. Otherwise, it is a frontier node, and put it on the 
          refinement worklist. *)

  let is_deterministic =
    let is_det tr =
      not (K.contains_havoc tr) || K.is_deterministic tr
    in
    Memo.memo is_det

  (* returns (new nodes on concolic worklist, new nodes on frontier worklist) *)
  (* a newly expanded node (leaf) is deemed a _concolic node_ if it can inherit
     a post-state model from its parent by means of symbol substitution. It is deemed
     a _frontier node_ if concrete execution cannot reach it from its parent node. A
     frontier node does not have a model associated with it and is in need of refinement. *)
  let expand recurse_level (art : t ref) (v : node) (m: Ctx.t Interpretation.interpretation)=
    let oracle s src tgt =
      if recurse_level = 0 then Summarizer.path_weight_inter s src
      else Summarizer.path_weight_intra s src tgt
    in
    let vg = maps_to art v in
    let new_concolic_nodes, new_frontier_nodes = (ref [], ref []) in
    (* visit out neighbors of v *)
    TS.iter_succ_e
      (fun (_, weight, y) ->
        let weight =
          match weight with
          | TransitionSystem.Weight w ->
            if is_deterministic w then w
            else
              K.mul w
                (K.assume
                 @@ K.guard (oracle !art.interproc y !art.err_loc))

          | TransitionSystem.Call (u, v) ->
              let proc = (VN.to_vertex u, VN.to_vertex v) |> PN.make in
              Summarizer.over_proc_summary !art.interproc proc
        in
        match K.get_post_model m weight with
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
      @@ Printf.sprintf "error: %d->%d but %d->%d\n" v
           (maps_to art v |> VN.of_vertex)
           w
           (maps_to art w |> VN.of_vertex);
    match Smt.entails Ctx.context v_label w_label with
    | `Yes ->
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
    | `No | `Unknown -> false


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
                       (fun x ->
                         (* add x's subtree leaves back to the worklist. *)
                         let x_leaves = leaves art x in
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
        let u_label' = Syntax.mk_and Ctx.context [ u_label; interpolant ] in
        log_formulas
          (Printf.sprintf "[relabelling %d CFG vertex %d] to label: " u
             (maps_to art u |> VN.of_vertex))
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
                  match Smt.entails Ctx.context x_label u_label with
                  | `No | `Unknown ->
                      (* remove (x, u) from covering. *)
                      logf "   refine: removing cover (%d->%d)\n"
                        x u;
                      !art.covers <- IntMap.remove x !art.covers;
                      (* add x's subtree leaves back to the worklist. *)
                      let x_leaves = leaves art x in
                      List.iter
                        (fun x_leaf ->
                          logf
                            "         refine: adding %d back to worklist \n"
                            x_leaf;
                            if not (is_leaf art x_leaf) then failwith "ERROR: found a non-leaf node in leaves set of ART";
                          worklist := x_leaf :: !worklist)
                        x_leaves;
                      l
                  | `Yes ->
                      logf
                        "    refine: cover (x %d-> u %d) still holds\n" x u;
                      log_formulas " x label: " [ x_label ];
                      log_formulas " u label: " [ u_label ];
                      ISet.add x coverers (* unchanged. *))
                l ISet.empty
            in
            !art.reverse_covers <- IntMap.add u u_coverers !art.reverse_covers)
      path
      interpolants;
    !worklist
  
  let rec glue l = 
    match l with 
    | a :: b :: t -> (a, b) :: (glue (b :: t))
    | _ -> []

  

  (* for w that is an ancestor of v, cover[v] stores w *)
  let remove_from_cover art v w = 
    match IntMap.find_opt v !art.covers with 
    | Some u ->
      begin if u <> w then failwith "remove_from_cover: node pair to remove not in cover"
      else 
        !art.covers <- IntMap.remove v !art.covers;
        let w_coverers = IntMap.find w !art.reverse_covers |> ISet.remove v in  
        !art.reverse_covers <- IntMap.add w w_coverers !art.reverse_covers;
      end
    | None -> failwith "remove_from_cover: node pair to remove not in cover ()"
  
  let add_to_cover art v w = 
    match IntMap.find_opt v !art.covers with 
    | Some r -> remove_from_cover art v r 
    | None -> ();
    !art.covers <- IntMap.add v w !art.covers;
    !art.reverse_covers <- 
      IntMap.add w 
        (IntMap.find_default ISet.empty w !art.reverse_covers 
          |> ISet.add v) !art.reverse_covers
    

  (* convention: w is an ancestor of v. returns true if we can add (v, w) to covers such that label(v) |= label(w) *)
  let force_cover (art : t ref) v w = (* check if v_label -> w_label where v is an ancestor at w *)
    if maps_to art v <> maps_to art w then (false, []) 
    else begin 
      (* let v_label = label art v in *)
      let w_label = label art w in 
      let artpath = tree_path art ~src:w v in 
      let path_weights = 
        artpath 
        |> glue 
        |> List.map (fun (x, y) ->
            match TS.edge_weight !art.graph (maps_to art x) (maps_to art y) with
            | TransitionSystem.Call (src, dst) ->
              Summarizer.over_proc_summary
                !art.interproc
                (PN.make (VN.to_vertex src, VN.to_vertex dst))
            | TransitionSystem.Weight wht -> wht)
      in
      let w_path_weights = (K.assume w_label) :: path_weights in
      match K.interpolate_or_concrete_model w_path_weights w_label with
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
         else match force_cover art v u with 
        | (true, frontiers) -> (true, frontiers)
        | (false, _) -> 
          try 
            let p = parent art u in go p 
          with Not_found -> (false, [])
        end 
    in
      match v with 
      | 0 -> (false, [])
      | _ -> go (parent art v)


  (** TODO: [deprecated] procedures for lightweight verification of ART invariants *)
    
  let verify_well_labelled_tree (t : t ref) =
    let rec aux v =
      let children = children t v in
      match children with
      | [] (* leaf node *) -> (
          match IntMap.find_opt v !t.covers with
          | None ->
              logf "!!! found uncovered leaf: %d\n" v;
              TS.fold_succ_e
                (fun (x, _, y) _ ->
                  logf
                    "  ERROR ERROR ERROR: mapped cfg vertex %d has \
                     out-neighbor %d\n"
                    (VN.of_vertex x) (VN.of_vertex y);
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

  let check_covering_welformedness (t : t ref) =
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
    | None -> Printf.sprintf "%d(%d)" i (maps_to art i |> VN.of_vertex)
    | Some j ->
        Printf.sprintf "[%d(%d)]->%d" i (maps_to art i |> VN.of_vertex) j

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
end
