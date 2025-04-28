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
       val negate : t -> t
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
       val pp_state : Format.formatter -> state -> unit
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

  let log_formulas prefix formulas =
    List.iteri
      (fun i f ->
        logf "[formula] %s(%i): %a\n" prefix i
          L.pp f)
      formulas

  type node_info =
    { parent : int
    ; cfg_vertex : G.vertex
    ; mutable label : L.t
    ; mutable children : int list }

  type t = {
    graph : G.t;
    err_loc : G.vertex;
    nodes : node_info ARR.t;
    precondition : L.t;
    mutable covers : int IntMap.t;
    (* also maintain reverse map for each y, storing (x, y) that are in cover. *)
    (* i.e. reverse_covers[y] returns all x such that (x,y) is in the cover. *)
    mutable reverse_covers : ISet.t IntMap.t;
    (* precedent_nodes[v] stores all tree nodes mapping to CFG vertex v. Used in mc_close. *)
    mutable precedent_nodes : ISet.t VertexMap.t;
    mutable frontier : node DQ.t;
  }

  let root = 0

  let make (g : G.t) (precondition : L.t) ~(src : G.vertex) ~(dst : G.vertex) =
    let nodes = ARR.make 65536 in
    ARR.add nodes { parent = -1
                  ; cfg_vertex = src
                  ; label = L.top
                  ; children = [] };
    { graph = g
    ; err_loc = dst
    ; nodes = nodes
    ; precondition = precondition
    ; covers = IntMap.empty (* for (u, v) in cover, u is ancestor of v and label(v) |= label(u). v is covered if (u, v) in cover. Then cover[v] = u. *)
    ; reverse_covers = IntMap.empty (* for each v, store the v's that cover it: i.e. cover[v] *)
    ; precedent_nodes = VertexMap.empty
    ; frontier = DQ.cons root DQ.empty }

  let get_err_loc (art : t) = art.err_loc
  let get_entry (art: t) = (ARR.get art.nodes 0).cfg_vertex

  (** [print_tree t ident v] prints an ART t with indentation `ident` rooted at node v *)
  let print_tree (art : t) (indent : string) (v : node) =
    let rec print_tree_ (art : t) indent v =
      logf "%s|" indent;
      logf "%s+-%d(%a)" indent v
        G.pp_vertex (ARR.get art.nodes v).cfg_vertex;
      List.iter
        (fun x -> print_tree_ art (indent ^ " ") x)
        (ARR.get art.nodes v).children
    in
    logf "*";
    print_tree_ art indent v

  (*  [parent t i] gets parent of node i in tree t.  *)
  let parent (art : t) (i : node) : node = (ARR.get art.nodes i).parent
    

  (*  [t %-> i]: get CFG vertex mapped by node i in tree t. *)
  let maps_to (art : t) (i : node) : G.vertex = (ARR.get art.nodes i).cfg_vertex

  let parent_weight (art : t) (i : node) =
    let parent = (ARR.get art.nodes i).parent in
    if parent < 0 then
      None
    else
      Some (parent, G.weight art.graph (maps_to art parent) (maps_to art i))

  (* [tree_path t u] returns list of tree nodes that form the corrsp. tree path from root of t to tree node u *)
  let tree_path (art : t) ?(src=root) (u : node) : node list =
    let rec tree_path_rev art u =
      if u = root || u = src then [ u ]
      else u :: tree_path_rev art (parent art u)
    in
    List.rev @@ tree_path_rev art u

  (* [children t v] returns children of tree node v in tree t. *)
  let children (art : t) (v : node) : node list = (ARR.get art.nodes v).children

  (* [descendants t v] returns descendants of tree node v in tree t in DFS order. *)
  let rec descendants (art : t) (v : node) : node list =
    let v_children = children art v in
    v :: List.fold_left (fun l ch -> descendants art ch @ l) [] v_children

  (* is a node in tree a leaf? *)
  let is_leaf (art : t) (v : node) : bool =
    match children art v with
    | [] -> true
    | _ -> false

  (* [label t v] returns the node label of tree node v in tree t. *)
  let label (art : t) (v : node) : L.t = (ARR.get art.nodes v).label

  (* [get_precedent_nodes t v] retrieves a sequence of precedent nodes of tree node vin preorder in tree t. *)
  (* the list of precedent nodes for a cfg vertex is a list of tree nodes which map to the same cfg location, ordered by < on integers. *)
  let get_precedent_nodes (art : t) (v : node) =
    let cfg_vertex = maps_to art v in
    let precedents_set =
      VertexMap.find_default ISet.empty cfg_vertex art.precedent_nodes
    in
    ISet.elements precedents_set

  (* Add new tree leaf mapping to CFG vertex v and with parent tree node p. *)
  let add_tree_vertex (art : t) ?(label = L.top) (v : G.vertex)
      (p : node) =
    (* note that new_vertex refers to a new tree vertex, where as v is a corresp. cfg location. *)
    let id = ARR.length art.nodes in
    ARR.add art.nodes { cfg_vertex = v
                      ; parent = p
                      ; label = label
                      ; children = [] };

    (* set children of parent to be vtxcnt :: children. *)
    begin if p >= 0 then
            let parent = ARR.get art.nodes p in
            parent.children <- id::parent.children
    end;
    (* Add v to precedent_nodes. *)
    let precedent_nodes =
      VertexMap.find_default ISet.empty v art.precedent_nodes
      |> ISet.add id
    in
    art.precedent_nodes <- VertexMap.add v precedent_nodes art.precedent_nodes;
    id

  let deque_frontier art =
    match DQ.front art.frontier with
    | None -> None
    | Some (u, frontier') ->
       art.frontier <- frontier';
       Some u

  let add_frontier art node = art.frontier <- DQ.snoc art.frontier node

  let expand (art : t) (v : node) =
    G.fold_succ (fun succ () ->
        let new_node = add_tree_vertex art succ v in
        add_frontier art new_node)
      art.graph
      (maps_to art v)
      ()

  (** maintenance of coverings *) 

  (* for w that is an ancestor/precedent of v, *)
  (* Adds (v -> w) to covering relation if possible and returns true, false otherwise. *)
  (* note that (v, w) in covering if stateLabel(v) IMPLIES stateLabel(w) *)
  let cover (art : t) v w =
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
          IntMap.find_default ISet.empty w art.reverse_covers
        in
        art.covers <- IntMap.add v w art.covers;
        art.reverse_covers <-
          IntMap.add w (ISet.add v reverse_covers_w) art.reverse_covers;
        true
    end else false


  let fold_leaves art f v acc =
    let rec go worklist acc =
      match worklist with
      | [] -> acc
      | v::worklist ->
         match children art v with
         | [] -> go worklist (f v acc)
         | children -> go (List.rev_append children worklist) acc
    in
    go [v] acc

  (** [close art v] visits precedents of v in tree and attempts to derive covering relations from v. *)
  let close (art : t) (v : node) =
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
                       IntMap.find_default ISet.empty y art.reverse_covers
                     in
                     (* Iterate through and remove pairs (x, y) from covering relation. *)
                     (* Step 1: Remove (x |-> y) from ptt.covers. *)
                     ISet.iter
                       (fun x -> art.covers <- IntMap.remove x art.covers)
                       xs;
                     (* Step 2: Remove (y |-> xs) from pthit.reverse_covers. *)
                     art.reverse_covers <- IntMap.remove y art.reverse_covers;
                     (* Step 3: add xs to worklist. *)
                     ISet.iter
                       (fun x ->
                         (* add x's subtree leaves back to the worklist. *)
                         fold_leaves
                           art
                           (fun x_leaf () ->
                             logf
                               "         close: adding %d back to worklist \n"
                               x_leaf;
                             wl' := x_leaf :: !wl')
                           x
                           ())
                       xs))
                 v_descendants);
            (cover_success, !wl'))
        precedents (false, [])
    in
    result

  (* Checks if tree node v is covered. It is covered if its ancestors or it is in covering relation. *)
  let rec is_covered (art : t) v =
    match IntMap.find_opt v art.covers with
    | None -> if v == 0 then false else is_covered art (parent art v)
    | Some u ->
        logf "  | covered by %d\n" u;
        true

  (* refine the label of each tree node u along path from tree root to v. *)
  let refine (art : t) path interpolants =
    List.iter2
      (fun u interpolant ->
        let u_info = ARR.get art.nodes u in
        let u_label' = L.meet u_info.label interpolant in
        log_formulas
          (Format.asprintf "[relabelling %d CFG vertex %a] to label: " u
             G.pp_vertex (maps_to art u))
          [ u_label' ];
        u_info.label <- u_label';
        (* remove ( * -> u) in covering relation; we justined label(u) so implications of form label(y)->label(u)
           might not hold anymore. *)
        match IntMap.find_opt u art.reverse_covers with
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
                      art.covers <- IntMap.remove x art.covers;
                      (* add x's subtree leaves back to the worklist. *)
                      fold_leaves
                        art
                        (fun x_leaf () ->
                          logf
                            "         refine: adding %d back to worklist \n"
                            x_leaf;
                          add_frontier art x_leaf)
                        x
                        ();
                      coverers
                    end)
                l
                ISet.empty
            in
            art.reverse_covers <- IntMap.add u u_coverers art.reverse_covers)
      path
      interpolants

  
  let rec glue l = 
    match l with 
    | a :: b :: t -> (a, b) :: (glue (b :: t))
    | _ -> []

  

  (* convention: w is an ancestor of v. returns true if we can add (v, w) to covers such that label(v) |= label(w) *)
  let force_cover (art : t) v w = (* check if v_label -> w_label where v is an ancestor at w *)
    if maps_to art v <> maps_to art w then false
    else begin 
      logf "force_cover(%d, %d)\n" v w;
      (* let v_label = label art v in *)
      let w_label = label art w in 
      let artpath = tree_path art ~src:w v in
      let path_weights = 
        artpath 
        |> glue 
        |> List.map (fun (x, y) -> 
               G.weight art.graph (maps_to art x) (maps_to art y))
      in
      match T.check w_label path_weights w_label with
      | `Valid itps -> 
         refine art (List.tl artpath) (List.tl itps);
         assert (cover art v w);
         true

      | `Invalid _ -> false
      | `Unknown -> failwith "force_cover: interpolation failed with status UNKNOWN."
    end
  

  (** a more lightweight version of close *)
  let lclose (art: t) v =
    let rec go u = 
      if u = -1 then false
      else begin   
          if maps_to art u <> maps_to art v then 
            try go (parent art u)
            with Not_found -> false
          else
            if force_cover art v u then true
            else
              try go (parent art u)
              with Not_found -> false
        end 
    in
    let res = match v with
      | 0 -> false
      | _ -> go (parent art v)
    in
    logf " --- lclose result of %d : %b ---\n" v  res ; res


  (** TODO: [deprecated] procedures for lightweight verification of ART invariants *)
    
  let _verify_well_labelled_tree (t : t) =
    let rec aux v =
      let children = children t v in
      match children with
      | [] (* leaf node *) -> (
          match IntMap.find_opt v t.covers with
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
                t.graph (maps_to t v) true
          | Some _ -> true)
      | _ -> (
          match IntMap.find_opt v t.covers with
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

  let _check_covering_welformedness (t : t) =
    logf "checking welformedness of covering relations\n";
    IntMap.iter
      (fun dst covered_from ->
        ISet.iter
          (fun src ->
            logf "checking if (%d, %d) in covering\n" src dst;
            match IntMap.find_opt src t.covers with
            | Some dst' ->
                if dst' <> dst then
                  failwith
                  @@ Printf.sprintf "ERROR: (%d, %d) in covering\n" src dst'
            | None -> failwith "ERROR: not in covering")
          covered_from)
      t.reverse_covers;
    logf "performing a reverse check\n";
    IntMap.iter
      (fun src dst ->
        match IntMap.find_opt dst t.reverse_covers with
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
      t.covers;
    logf "...done checking welformedness of covering relations\n"

  (** pretty-printing functionalities *)
  let tree_printer_get_name (art : t) i =
    match IntMap.find_opt i art.covers with
    | None -> Format.asprintf "%d(%a)" i G.pp_vertex (maps_to art i)
    | Some j ->
        Format.asprintf "[%d(%a)]->%d" i G.pp_vertex (maps_to art i) j

  let log_art (art : t) =
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
  
  let pp_node = Format.pp_print_int

  let of_node u = u

  let execute art node state =
    let rec loop worklist =
      match worklist with
      | [] -> `Safe
      | (u, u_model)::worklist ->
        logf " visit %d (%a)\n" u G.pp_vertex (maps_to art u);
        if (maps_to art u) = (get_err_loc art) then begin
            logf " *** found path-to-error";
            (* We're abandoning the search without exhausting worklist, so
               worklist must be added to frontier. *)
            List.iter (fun (v, _) -> art.frontier <- DQ.snoc art.frontier v) worklist;
            `Unsafe u
        end else begin
            logf "model of %d (%a): @[%a@]"
              u
              G.pp_vertex (maps_to art u)
              T.pp_state u_model;
            let u_v = maps_to art u in
            let worklist =
              G.fold_succ (fun succ worklist ->
                  let succ_node = add_tree_vertex art succ u in
                  let weight = G.weight art.graph u_v succ in
                  let weight =
                    if T.is_deterministic weight then weight
                    else
                      T.mul weight (T.assume @@ T.guard @@ G.summary art.graph succ)
                  in
                  match T.post_model u_model weight with
                  | Some model -> (succ_node,model)::worklist
                  | None -> add_frontier art succ_node; worklist)
                art.graph
                u_v
                worklist
            in
            loop worklist
        end
    in
    loop [(node, state)]

  let path_to_error art node = G.summary art.graph (maps_to art node)

  let generate_test art node =
    let post = L.negate (T.guard (path_to_error art node)) in
    let rec get_path rest node =
      match parent_weight art node with
      | Some (p, weight) -> get_path (weight::rest) p
      | None -> rest
    in
    let path = get_path [] node in
    match T.check art.precondition path post with
    | `Invalid v_model ->
       logf ~level:`trace "-> found test";
       `Test v_model
    | `Unknown -> failwith "generate_test: got UNKNOWN as a result for interpolate_or_get_model"
    | `Valid interpolants ->
       logf ~level:`trace "-> pruned";
       log_formulas "interpolants - " interpolants;
       refine art (tree_path art node) interpolants;
       `Pruned

  let gps art =
    let rec loop () =
      match deque_frontier art with
      | None -> `Safe
      | Some u ->
         (* Fetched tree node u from work list. First attempt to close it. *)
         logf ~level:`trace "At frontier node %d:" u;
         if is_covered art u then
           (logf ~level:`trace "-> covered";
            loop ())
         else begin
             if lclose art u then (* Close succeeded. No need to further explore it. *)
               (logf ~level:`trace "-> closed"; loop ())
             else begin
                 (* u is uncovered. *)
                 match generate_test art u with
                 | `Pruned -> (* refinement succeeded *)
                    (* for every node along path of refinement try close *)
                    List.iter (fun v -> ignore (close art v)) (tree_path art u);

                    loop ()
                 | `Test state ->
                    logf ~level:`trace "-> found test";
                    match execute art u state with
                    | `Safe -> loop ()
                    | `Unsafe n -> `Unsafe n
               end
           end
    in
    loop ()

end
