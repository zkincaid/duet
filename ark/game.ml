open Apak
open Syntax
open Smt
open BatPervasives

include Log.Make(struct let name = "ark.game" end)

module GameTree : sig
  type 'a t
  type 'a vertex
  val empty : 'a smt_context ->
    (symbol list * symbol list) ->
    start:('a formula) -> 
    safe:('a formula) ->
    reach:('a formula) ->
    'a t
  val well_labeled : 'a t -> bool
  val expand_vertex : 'a t -> 'a vertex -> int -> bool
  val get_open : 'a t -> ('a vertex) option
  val root : 'a t -> 'a vertex
  val pp : Format.formatter -> 'a t -> unit
end = struct
  module A = BatDynArray

  type 'a vertex_state =
    | Covered of 'a vertex
    | Expanded of (('a vertex) list)
    | Open
  and 'a vertex =
    { id : int;
      mutable annotation : 'a formula;
      mutable state : 'a vertex_state;
      mutable covers : 'a vertex list;
      parent : ('a vertex * 'a formula * (('a, typ_fo) expr list)) option }

  type 'a t =
    { ctx : 'a smt_context;
      xs : symbol list;
      ys : symbol list;
      safe : 'a formula;
      reach : 'a formula;
      start : 'a formula;
      root : 'a vertex;
      var_to_level : (symbol * int, symbol) Hashtbl.t;
      level_to_var : (symbol, symbol) Hashtbl.t;
      mutable max_vertex : int }

  let root game_tree = game_tree.root

  let empty ctx (xs,ys) ~start ~safe ~reach =
    assert (List.length xs == List.length ys);
    let root =
      { id = 0;
        annotation = mk_true ctx#ark;
        state = Open;
        covers = [];
        parent = None }
    in
    { ctx = ctx;
      xs = xs;
      ys = ys;
      safe = safe;
      reach = reach;
      start = start;
      root = root;
      max_vertex = 0;
      var_to_level = Hashtbl.create 991;
      level_to_var = Hashtbl.create 991 }

  let var_to_level game_tree level sym =
    let ark = game_tree.ctx#ark in
    try Hashtbl.find game_tree.var_to_level (sym, level)
    with Not_found ->
      begin
        let sym_level =
          mk_symbol
            ark
            ~name:((show_symbol ark sym) ^ "$" ^ (string_of_int level))
            (typ_symbol ark sym)
        in
        Hashtbl.add game_tree.var_to_level (sym, level) sym_level;
        Hashtbl.add game_tree.level_to_var sym_level sym;
        sym_level
      end
    
  let substitute_var_to_level game_tree level =
    let ark = game_tree.ctx#ark in
    substitute_const ark (mk_const ark % var_to_level game_tree level)

  let substitute_level_to_var game_tree =
    let ark = game_tree.ctx#ark in
    let f sym =
      try mk_const ark (Hashtbl.find game_tree.level_to_var sym)
      with Not_found -> assert false
    in
    substitute_const ark f

  let dimension game_tree = List.length game_tree.xs

  let nb_vertex game_tree = game_tree.max_vertex + 1

  let get_open game_tree =
    let rec find v =
      match v.state with
      | Covered _ -> None
      | Open -> Some v
      | Expanded children ->
        List.fold_left (fun open_vertex child ->
            match open_vertex with
            | Some v -> Some v
            | None -> find child)
          None
          children
    in
    find game_tree.root

  let children vertex =
    match vertex.state with
    | Expanded children -> children
    | _ -> []

  let rec depth vertex =
    match vertex.parent with
    | Some (p, _, _) -> 1 + depth p
    | None -> 0

  let rec height vertex =
    1 + (List.fold_left max 0 (List.map height (children vertex)))

  (* Verify well-labeledness conditions *)
  let well_labeled game_tree =
    let ark = game_tree.ctx#ark in
    let entails = game_tree.ctx#implies in
    let rec well_labeled_vertex v =
      let child_guards =
        children v |> List.map (fun c -> match c.parent with
            | None -> assert false
            | Some (_, guard, _) -> guard)
      in
      let consecution_and_availability =
        match v.parent with
        | None -> true
        | Some (parent, guard, move) ->
          (* Consecution: if u -[psi : m]-> v, then
               Phi(u)(x) /\ psi(x) /\ y = m(x) /\ reach(y,x') |= Phi(v)(x')
           *)
          let move_formula =
            List.map2
              (fun y m ->
                 match refine ark m with
                 | `Term t -> mk_eq ark (mk_const ark y) t
                 | `Formula phi -> mk_iff ark (mk_const ark y) phi)
              game_tree.ys
              move
          in
          let rename_xs =
            let f sym =
              (if List.mem sym game_tree.xs then
                 var_to_level game_tree 0 sym
               else
                 sym)
              |> mk_const ark
            in
            substitute_const ark f
          in
          let reach_move = rename_xs game_tree.reach in
          entails
            (mk_and ark ([parent.annotation; guard; reach_move]@move_formula))
            (rename_xs v.annotation)
          (* Availability: psi(x) /\ y = m(x) |= safe(x,y) *)
          && entails (mk_and ark (guard::move_formula)) game_tree.safe

      in
      consecution_and_availability
      && match v.state with
      | Expanded children ->
        entails v.annotation (mk_or ark child_guards) (* Adequacy *)
        && List.for_all well_labeled_vertex children
      | Covered u ->
        entails v.annotation u.annotation (* Covering *)
      | Open -> true
    in
    well_labeled_vertex game_tree.root

  let delete_children game_tree vertex =
    let rec delete vertex =
      begin match vertex.state with
        | Expanded children ->
          List.iter delete children
        | Covered covering ->
          covering.covers <-
            List.filter (fun v -> v.id != vertex.id) covering.covers
        | Open -> ()
      end;
      List.iter (fun v -> v.state <- Open) vertex.covers
    in
    match vertex.state with
    | Expanded children -> List.iter delete children
    | _ -> assert false

  let pp_prefix ark formatter prefix =
    let pp_elt formatter = function
      | (`Forall, x) -> Format.fprintf formatter "A %a" (pp_symbol ark) x
      | (`Exists, x) -> Format.fprintf formatter "E %a" (pp_symbol ark) x
    in
    ApakEnum.pp_print_enum pp_elt formatter (BatList.enum prefix)

  (* Let v be a vertex and let, let r = u_0 ... u_n = v be the path from the
     root to v.  For each i, let (guard_i,move_i) = M(u_i,u_{i+1}).
     path_to_root_formulas computes the list
       [init(x_0); guard_0(x_0) /\ reach(move_0(x_0),x_1);
                   ...;
                   guard_{n-1}(x_{n-1}) /\ reach(move_{n-1}(x_{n-1}),x_{n-1})]
     representing plays of the game where the safety player conforms to the
     path u_0...u_n and the reachability player is constrained to satisfy the
     guards along the path *)
  let path_to_root_formula game_tree vertex =
    let ark = game_tree.ctx#ark in
    let rec path_to_root_formula vertex depth =
      match vertex.parent with
      | Some (parent, guard, moves) ->
        let move_map =
          List.fold_left2 (fun map y m ->
              Symbol.Map.add
                y
                (substitute_var_to_level
                   game_tree
                   (depth - 1)
                   m)
                map)
            Symbol.Map.empty
            game_tree.ys
            moves
        in
        (* Map x variables to x_depth and y variables to
           move_depth(x_{depth-1}) *)
        let subst sym =
          if List.mem sym game_tree.xs then
            mk_const ark (var_to_level game_tree depth sym)
          else
            (Symbol.Map.find sym move_map)
        in
        let guard_and_reach =
          mk_and ark [substitute_var_to_level game_tree (depth - 1) guard;
                      substitute_const ark subst game_tree.reach]
        in
        guard_and_reach::(path_to_root_formula parent (depth - 1))
      | None ->
        assert (depth == 0); (* vertex is root *)
        [substitute_var_to_level game_tree depth game_tree.start]
    in
    path_to_root_formula vertex (depth vertex)

  (* Unroll the game k so that the safety player makes k moves (and the
     reachability player makes k-1), using variable indices starting at i *)
  let rec unroll game_tree i k =
    let ark = game_tree.ctx#ark in
    if k <= 1 then
      substitute_var_to_level game_tree i game_tree.safe
    else
      (* safe(x_i,y_i) *)
      let safe = substitute_var_to_level game_tree i game_tree.safe in
      (* reach(y_i,x_{i+1}) *)
      let reach =
        let sym_map =
          List.fold_left
            (fun map x ->
               Symbol.Map.add
                 x
                 (mk_const ark (var_to_level game_tree (i + 1) x))
                 map)
            (List.fold_left
               (fun map y ->
                  Symbol.Map.add
                    y
                    (mk_const ark (var_to_level game_tree i y))
                    map)
               Symbol.Map.empty
               game_tree.ys)
            game_tree.xs
        in
        substitute_const ark ((flip Symbol.Map.find) sym_map) game_tree.reach
      in
      let rest = unroll game_tree (i + 1) (k - 1) in
      mk_and ark [safe; mk_implies ark reach rest]

  (* Strengthen the annotation at a vertex with given refinement.  Remove
     coverings that are no longer implied.  The consecution condition is not
     checked. *)
  let strengthen_annotation game_tree vertex refinement =
    let ark = game_tree.ctx#ark in
    let smt_ctx = game_tree.ctx in
    let new_annotation = mk_and ark [refinement; vertex.annotation] in
    vertex.annotation <- new_annotation;
    let (covers, uncovered) =
      List.partition
        (fun v -> (smt_ctx#implies v.annotation new_annotation))
        vertex.covers
    in
    vertex.covers <- covers;
    uncovered |> List.iter (fun v -> v.state <- Open)

  let rec refine_path_to_root game_tree vertex refine =
    let ark = game_tree.ctx#ark in
    let smt_ctx = game_tree.ctx in
    let (phi, refine) = match refine with
      | (x::xs) -> (rewrite ark ~down:(nnf_rewriter ark) x, xs)
      | [] -> assert false
    in
    strengthen_annotation game_tree vertex phi;
    match vertex.parent with
    | Some (parent, _, _) ->
      refine_path_to_root game_tree parent refine
    | None ->
      assert (refine = [])

  let simple_tree_interpolant smt_ctx root children =
    let pattern =
      let interp_pattern =
        List.map
          (Z3.Interpolation.mk_interpolant smt_ctx#z3 % smt_ctx#of_formula)
          children
      in
      Z3.Boolean.mk_and smt_ctx#z3 ((smt_ctx#of_formula root)::interp_pattern)
    in
    let params = Z3.Params.mk_params smt_ctx#z3 in
    match Z3.Interpolation.compute_interpolant smt_ctx#z3 pattern params with
    | (_, Some interp, None) ->
      `Unsat (List.map smt_ctx#formula_of interp)
    | (_, None, Some _) -> `Sat
    | (_, _, _) -> `Unknown

  (* Try to find an ancestor of v to cover it. *)
  let find_cover game_tree v =
    let rec find_cover u =
      if game_tree.ctx#implies v.annotation u.annotation then
        Some u
      else
        match u.parent with
        | Some (u', _, _) -> find_cover u'
        | None -> None
    in
    match v.parent with
    | None -> false
    | Some (parent, _, _) ->
      match find_cover parent with
      | Some cov ->
        logf ~level:`trace "Found cover: %d covers %d" cov.id v.id ;
        let ark = game_tree.ctx#ark in
        v.state <- Covered cov;
        cov.covers <- v::cov.covers;
        true
      | None -> false

  let depth_bounded_safe_region game_tree depth =
    let rec go d vertex =
      if d >= depth then
        []
      else
        match vertex.state with
        | Expanded children ->
          vertex.annotation::(BatList.flatten (List.map (go (d + 1)) children))
        | _ -> [vertex.annotation]
    in
    mk_or (game_tree.ctx#ark) (go 0 game_tree.root)

  (* find a vertex at less than a given depth that satisfies a given
     predicate *)
  let find_depth_bounded game_tree depth p =
    let rec go d vertex =
      if d >= depth then
        None
      else
      if p vertex then
        Some vertex
      else
        match vertex.state with
        | Expanded children ->
          List.fold_left (fun found v ->
              match found with
              | Some _ -> found
              | None -> go (d + 1) v)
            None
            children
        | _ -> None
    in
    go 0 game_tree.root

  let force_cover game_tree v =
    let ark = game_tree.ctx#ark in
    let path_to_root = path_to_root_formula game_tree v in
    let p2r_formula = mk_and ark path_to_root in
    let v_depth = depth v in
    let p u =
      let u_annotation =
        substitute_var_to_level game_tree v_depth u.annotation
      in
      game_tree.ctx#implies p2r_formula u_annotation
    in
    match find_depth_bounded game_tree v_depth p with
    | None -> false
    | Some cov ->
        logf ~level:`trace "Found forced cover: %d may cover %d" cov.id v.id;

        let cov_annotation =
          substitute_var_to_level game_tree v_depth cov.annotation
          |> mk_not ark
        in
        let seq = List.rev (cov_annotation::path_to_root) in
        match game_tree.ctx#interpolate_seq seq with
        | `Sat _ | `Unknown -> assert false
        | `Unsat interpolants ->
          let annotations =
            List.rev_map (substitute_level_to_var game_tree) interpolants
          in
          refine_path_to_root game_tree v annotations;
          if game_tree.ctx#implies v.annotation cov.annotation then begin
            logf ~level:`trace "Force cover successful.";
            v.state <- Covered cov;
            cov.covers <- v::cov.covers;
            true
          end else begin
            logf ~level:`trace "Force cover failed.";
            false
          end

  (* Formula representing the safety player's skeleton losing the unrolled
     game *)
  let rec losing game_tree skeleton x_map =
    let ark = game_tree.ctx#ark in
    match Quantifier.destruct_skeleton_block ark skeleton with
    | `Exists alternatives ->
      List.map (fun (moves, sub_skeleton) ->
          let move_map = (* ys -> moves *)
            let subst v =
              try
                Symbol.Map.find (Hashtbl.find game_tree.level_to_var v) x_map
              with Not_found -> assert false
            in
            List.fold_left2
              (fun map y (_, m) ->
                 Symbol.Map.add y (substitute_const ark subst m) map)
              Symbol.Map.empty
              game_tree.ys
              moves
          in
          (* safe(x_i, moves(x_i)) *)
          let safe =
            let subst v =
              try Symbol.Map.find v move_map
              with Not_found ->
              try Symbol.Map.find v x_map
              with Not_found -> assert false
            in
            substitute_const ark subst game_tree.safe
          in
          match Quantifier.destruct_skeleton_block ark sub_skeleton with
          | `Forall (x_map_list, sub_sub_skeleton) ->
            let x_map =
              List.fold_left2
                (fun map x (_, x') ->
                   Symbol.Map.add x (mk_const ark x') map)
                Symbol.Map.empty
                game_tree.xs
                x_map_list
            in
            (* reach(moves(x_i),x_j) *)
            let reach =
              let subst v =
                try Symbol.Map.find v move_map
                with Not_found ->
                try Symbol.Map.find v x_map
                with Not_found -> assert false
              in
              substitute_const ark subst game_tree.reach
            in
            let losing_subgame = losing game_tree sub_sub_skeleton x_map in
            mk_or ark [mk_not ark safe;
                       mk_and ark (reach::losing_subgame)]
          | `Exists _ -> assert false
          | `Empty -> mk_not ark safe)
        alternatives
    | `Empty -> [mk_false ark]
    | _ -> assert false

  let rec paste game_tree skeleton vertex =
    let ark = game_tree.ctx#ark in
    let x_map =
      List.fold_left
        (fun map x -> Symbol.Map.add x (mk_const ark x) map)
        Symbol.Map.empty
        game_tree.xs
    in
    if not (force_cover game_tree vertex) then
      let losing_branches = losing game_tree skeleton x_map in
      let interp =
        simple_tree_interpolant game_tree.ctx vertex.annotation losing_branches
      in
      match interp with
      | `Sat -> assert false
      | `Unknown -> assert false
      | `Unsat not_guards ->
        let guards =
          BatList.map
            (fun not_guard ->
               rewrite ark ~down:(nnf_rewriter ark) (mk_not ark not_guard))
            not_guards
        in
        let alternatives =
          match Quantifier.destruct_skeleton_block ark skeleton with
          | `Exists alternatives -> alternatives
          | _ -> assert false
        in
        let children =
          List.map2 (fun (moves, sub_skeleton) guard ->
              let moves =
                List.map (substitute_level_to_var game_tree % snd) moves
              in
              let id = game_tree.max_vertex + 1 in
              game_tree.max_vertex <- id;
              { id = id;
                annotation = mk_true ark; (* really should not use this *)
                state = Open;
                covers = [];
                parent = Some (vertex, guard, moves) })
            alternatives
            guards
        in
        vertex.state <- Expanded children;
        List.iter2 (fun (_, sub_skeleton) child ->
            let (guard, move) = match child.parent with
              | Some (_, guard, move) -> (guard, move)
              | None -> assert false
            in
            match Quantifier.destruct_skeleton_block ark sub_skeleton with
            | `Forall (_, sub_sub_skeleton) ->
              (* guard(x_lev) *)
              let level = (-1) in
              let guard =
                substitute_var_to_level game_tree level guard
              in
              (* y -> move(x_lev) *)
              let move_map = 
                List.fold_left2
                  (fun map y m ->
                     Symbol.Map.add
                       y
                       (substitute_var_to_level game_tree level m)
                       map)
                  Symbol.Map.empty
                  game_tree.ys
                  move
              in
              (* reach(move(x_lev),x) *)
              let reach =
                let subst v =
                  try Symbol.Map.find v move_map
                  with Not_found -> mk_const ark v
                in
                substitute_const ark subst game_tree.reach
              in
              let lose =
                mk_and ark (losing game_tree sub_sub_skeleton x_map)
              in
              begin
                match
                  game_tree.ctx#interpolate_seq [mk_and ark [guard; reach];
                                                 lose]
                with
                | `Unsat [annotation] ->
                  strengthen_annotation game_tree child annotation;
                  paste game_tree sub_sub_skeleton child
                | _ -> assert false
              end
            | `Empty -> ()
            | _ -> assert false)
          alternatives
          children

  
  let rec expand_vertex game_tree vertex k =
    logf ~level:`info "Expanding vertex #%d" vertex.id;
    let ark = game_tree.ctx#ark in
    let vertex_depth = depth vertex in
    let rec prefix level =
      if level < vertex_depth then
        let xs =
          List.map
            (fun x -> (`Forall, var_to_level game_tree level x))
            game_tree.xs
        in
        xs@(prefix (level + 1))        
      else if level < vertex_depth + k then
        let xs =
          List.map
            (fun x -> (`Forall, var_to_level game_tree level x))
            game_tree.xs
        in
        let ys =
          List.map
            (fun y -> (`Exists, var_to_level game_tree level y))
            game_tree.ys
        in
        xs@ys@(prefix (level + 1))
      else
        []
    in
    let path_to_root = path_to_root_formula game_tree vertex in
    let unrolled = unroll game_tree vertex_depth k in
    let game_matrix =
      mk_implies ark (mk_and ark path_to_root) unrolled
      |> rewrite ark ~down:(nnf_rewriter ark)
    in
    let game_prefix = prefix 0 in
    match Quantifier.winning_skeleton game_tree.ctx game_prefix game_matrix with
    | `Sat skeleton ->
      let (x_map, skeleton) =
        match Quantifier.destruct_skeleton_block ark skeleton with
        | `Forall (block, sub_skeleton) ->
          let x_map =
            List.fold_left
              (fun map x ->
                 Symbol.Map.add x
                   (mk_const ark (var_to_level game_tree vertex_depth x))
                   map)
              Symbol.Map.empty
              game_tree.xs
          in
          (x_map, sub_skeleton)
        | _ -> assert false
      in
      let lost =
        mk_and ark (losing game_tree skeleton x_map)
        |> rewrite ark ~down:(nnf_rewriter ark)
      in
      begin
        match game_tree.ctx#interpolate_seq (List.rev (lost::path_to_root)) with
        | `Sat _ | `Unknown -> assert false
        | `Unsat interpolants ->
          let annotations =
            List.rev_map (substitute_level_to_var game_tree) interpolants
          in
          refine_path_to_root game_tree vertex annotations;
          paste game_tree skeleton vertex;
          true
      end
    | `Unsat skeleton ->
      begin match vertex.parent with
        | None ->
          logf ~level:`info "Failed to expand.  Reachbility player wins!@\n%a"
            (Quantifier.pp_skeleton ark) skeleton;
          false
        | Some (parent, _, _) ->
          let k' = max (k + 1) (height parent) in
          logf ~level:`trace
            "Failed to expand vertex #%d.  Moving up with game depth %d."
            vertex.id
            k';
          delete_children game_tree parent;
          expand_vertex game_tree parent k'
      end
    | `Unknown -> assert false

  let pp formatter game_tree =
    let open Format in
    let ark = game_tree.ctx#ark in
    let pp_sep formatter () = Format.fprintf formatter "@;" in
    let rec go formatter v =
      let (guard, moves) = match v.parent with
        | Some (_, guard, moves) -> (guard, moves)
        | _ -> assert false
      in
      fprintf formatter "@[<v 0>when@;  %a@;move (%a)@;  @[<v 0>#%d [%a]@;%a@]@]"
        (Formula.pp ark) guard
        (ApakEnum.pp_print_enum (pp_expr ark)) (BatList.enum moves)
        v.id
        (Formula.pp ark) v.annotation
        (ApakEnum.pp_print_enum_nobox ~pp_sep go) (BatList.enum (children v))
    in
    let root = game_tree.root in
    fprintf formatter "#%d [%a]@;@[<v 0>%a@]"
      root.id
      (Formula.pp ark) root.annotation
      (ApakEnum.pp_print_enum_nobox ~pp_sep go) (BatList.enum (children root))
end

let solve smt_ctx (xs, ys) ~start ~safe ~reach =
  let game_tree = GameTree.empty smt_ctx (xs, ys) ~start ~safe ~reach in
  let nb_rounds = ref 0 in
  let rec go v =
    incr nb_rounds;
    logf ~level:`info
      "-- Round %d ---------------------------------------------"
      (!nb_rounds);
    logf ~level:`info "%a" GameTree.pp game_tree;

    assert (GameTree.well_labeled game_tree);
    assert((!nb_rounds) < 100);
    if GameTree.expand_vertex game_tree v 2 then
      match GameTree.get_open game_tree with
      | Some u -> go u
      | None -> Some game_tree
    else
      None
  in
  if GameTree.expand_vertex game_tree (GameTree.root game_tree) 2 then
    match GameTree.get_open game_tree with
    | Some u -> go u
    | None -> Some game_tree
  else
    None

