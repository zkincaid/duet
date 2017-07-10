open Core
open CfgIr
open Ark
open Apak
open BatPervasives

module P = Putil.Set.Make(AP.Set)
module Dom = Dominator.Make(CfgIr.Cfg)

let intersects x y = not (AP.Set.is_empty (AP.Set.inter x y))

let add_equality eq partition =
  let (rest, merge) =
    P.partition (fun x -> AP.Set.is_empty (AP.Set.inter eq x)) partition
  in
  P.add (P.fold AP.Set.union merge AP.Set.empty) rest

let p_map f p = P.fold (fun x p -> P.add (f x) p) p P.empty

let compact set =
  let lt x y = AP.Set.subset x y && not (AP.Set.equal x y) in
  let add x c =
    if (P.exists (lt x) set) then c else P.add x c
  in
  P.fold add set P.empty

module D = struct
  module M = BatSet.Make(struct
      type t = Def.t * AP.Set.t [@@deriving show,ord]
    end)
  include M
  let pp formatter set =
    let pp_elt formatter (def, set) =
      Format.fprintf formatter "@[%a@ -> %a@]"
        Def.pp def
        AP.Set.pp set
    in
    Format.fprintf formatter "[%a]"
      (ArkUtil.pp_print_enum pp_elt)
      (M.enum set)

  let compact set =
    let lt (d,x) (e,y) =
      Def.equal d e && AP.Set.subset x y && not (AP.Set.equal x y)
    in
    let add x c =
      if (exists (lt x) set) then c else add x c
    in
    fold add set empty
  let join x y = compact (union x y)
  let widen = join
end

(** Get the least common ancestor of a list of vertices in a dominator
    tree *)
let get_lca dom_tree = function
  | [] -> failwith "Can't get the LCA of an empty set of vertices!"
  | (x::xs) -> List.fold_left (Dom.get_lca dom_tree) x xs

(** Determine which access paths could possibly be related at each point in
    file.  Returns a pair of functions (pre,post) mapping each definition d to
    a a set of related sets of access paths before and after the execution of
    d.  Currently, this is an intraprocedural analysis that works
    independently on each thread. *)
let relatable file =
  let join_map = Def.HT.create 32 in
  let process_thread thread =
    let func = lookup_function thread file in
    let dom_tree = Dom.compute func.cfg (Cfg.initial_vertex func.cfg) in
    let is_join_vertex v = (Cfg.in_degree func.cfg v) > 1 in
    let set_join_map v =
      if is_join_vertex v then begin
        let preds = Cfg.pred func.cfg v in
        let lca = get_lca dom_tree preds in
        let f a v = AP.Set.union a (Def.get_defs v) in
        let add_branch modified v =
          Dom.fold_to_ancestor f modified dom_tree v lca
        in
        let modified = List.fold_left add_branch AP.Set.empty preds in
        Def.HT.add join_map v modified
      end
    in
    Cfg.iter_vertex set_join_map func.cfg
  in
  let module S = Solve.MakeForwardCfgSolver(
    struct
      type t = P.t [@@deriving show]
      let join x y = compact (P.union x y)
      let widen = join
      let equal = P.equal

      let name = "Infer related"
      let transfer def related =
        let related =
          try add_equality (Def.HT.find join_map def) related
          with Not_found -> related
        in
        let defs = Def.get_defs def in
        let uses = Def.get_uses def in
        let pure_defs = AP.Set.diff defs uses in
        let du = AP.Set.union defs uses in
        let related = p_map (fun x -> AP.Set.diff x pure_defs) related in
        let related =
          p_map
            (fun x -> if intersects x du then AP.Set.union x du else x)
            related
        in
        compact (P.add du (add_equality du related))
      let bottom = P.empty
    end)
  in
  let in_map = Def.HT.create 32 in
  let out_map = Def.HT.create 32 in
  let f result =
    BatEnum.iter (uncurry (Def.HT.add in_map)) (S.enum_input result);
    BatEnum.iter (uncurry (Def.HT.add out_map)) (S.enum_output result);
    S.display result
  in
  List.iter process_thread file.threads;
  S.file_analysis file f P.empty (fun _ init -> init);
  ((fun v ->
      try add_equality (Def.HT.find join_map v) (Def.HT.find in_map v)
      with Not_found -> (Def.HT.find in_map v)),
   Def.HT.find out_map)

(** Construct a dependence graph with the property that any analysis
    run on this dependence graph is as accurate as the corresponding
    CFG analysis.  This graph has less framing than the CFG, but no
    guarantee can be made. *)
(*
let infer_frames file =
  let (relatable_at, relatable_post) = relatable file in
  let split v uses =
    let relatable =
      let ensure_uses = AP.Set.fold (fun x -> P.add (AP.Set.singleton x)) uses
      in
	compact (ensure_uses (relatable_at v))
    in
    let split = p_map (AP.Set.inter uses) relatable in
    let split =
      if P.mem AP.Set.empty split
      then P.remove AP.Set.empty split
      else split
    in
      P.fold (fun u s -> D.add (v, u) s) split D.empty
  in
  let satisfies def set =
    let pos =
      match def.dkind with
	| Assume _ ->
	    P.filter (intersects (Def.get_defs def)) (relatable_post def)
	| _ -> P.empty
    in
      intersects (Def.get_defs def) set
      || D.cardinal (split def set) > 1
      || P.exists (fun x -> AP.Set.subset set x) pos
      || Def.is_blocking def && (AP.Set.for_all AP.is_shared set)
  in
  let module FI = struct
    let name = "Frame inference"
    let transfer def uses =
      let defs = Def.get_defs def in
      let def_uses = Def.get_uses def in
      let pure_defs = AP.Set.diff defs def_uses in
      let (sat, unsat) =
	D.partition (fun (_, set) -> satisfies def set) uses
      in
      let domain =
	AP.Set.diff
	  (D.fold (fun (_, set) frame -> AP.Set.union set frame) sat def_uses)
	  pure_defs
      in
	D.compact (D.union unsat (split def domain))
    let bottom = D.empty
    include D
  end
  in
  let module S = Solve.MakeBackwardCfgSolver(FI) in
  let dg = DG.create () in
  let add_initial (use, set) =
    DG.add_edge_e dg (DG.E.create Def.initial set use)
  in
  let initial_vertices = CfgIr.initial_vertices file in
  let add_edges result def uses =
    let add_edge (use, set) =
      if satisfies def set
      then (DG.add_edge_e dg (DG.E.create def set use))
    in
      D.iter add_edge uses;
      if Def.Set.mem def initial_vertices
      then D.iter add_initial (S.input result def)
  in
  let process_thread thread =
    let func = lookup_function thread file in
      Cfg.iter_vertex (DG.add_vertex dg) func.cfg
  in
  let f result =
    S.iter_input (add_edges result) result;
  in
    List.iter process_thread file.threads;
    ignore (S.backwards_file_analysis file f D.empty (fun _ init -> init));
    DG.display_labelled dg;
    DG.sanity_check dg;
    file
*)

module MemLoc = PointerAnalysis.MemLoc
module DS = Ark.DisjointSet.Make(MemLoc)

let memlocs ap_set =
  let f ap = MemLoc.Set.union (PointerAnalysis.resolve_ap ap) in
  AP.Set.fold f ap_set MemLoc.Set.empty

(** Partition the access paths in a program into related "packs".  The
    function returned by {!infer_partition} maps each access path to
    its equivalence class.  *)
let infer_partition file =
  let partition = DS.create 32 in
  let union_loc_set set =
    let for_all p = MemLoc.Set.for_all p set in
    let nexists p = for_all (fun x -> not (p x)) in
    if (MemLoc.Set.cardinal set == 2)
       && (for_all MemLoc.is_var)
       && (for_all MemLoc.is_shared || nexists MemLoc.is_shared)
    then begin
      let s = DS.find partition (MemLoc.Set.choose set) in
      let merge ap = ignore (DS.union s (DS.find partition ap)) in
      MemLoc.Set.iter merge set
    end
  in
  let rec add_bexpr bexpr =
    let uses = memlocs (Bexpr.get_uses bexpr) in
    if MemLoc.Set.cardinal uses <= 2 then union_loc_set uses
    else begin
      match bexpr with
      | And (l, r) -> (add_bexpr l; add_bexpr r)
      | Or (l, r) -> (add_bexpr l; add_bexpr r)
      | Atom _ -> ()
    end
  in
  let add_vertex v = match v.dkind with
    | Assume p -> add_bexpr p
    | Assert (p, _) -> add_bexpr p
    | _ ->
      union_loc_set (memlocs (AP.Set.union (Def.get_uses v) (Def.get_defs v)))
  in
  let process_thread t =
    let func = lookup_function t file in
    Cfg.iter_vertex add_vertex func.cfg
  in
  List.iter process_thread file.threads;
  (match file.globinit with
   | Some f -> Cfg.iter_vertex add_vertex f.cfg
   | None -> ());
  let map = DS.reverse_map partition MemLoc.Set.empty MemLoc.Set.add in
  let f ap = try map ap with Not_found -> MemLoc.Set.singleton ap in
  f

module VarDS = DisjointSet.Make(Var)
let memlocs ap_set =
  let f ap = MemLoc.Set.union (PointerAnalysis.resolve_ap ap) in
  AP.Set.fold f ap_set MemLoc.Set.empty

let var_locs ap_set =
  let f ap set =
    let g memloc set =
      match memloc with
      | (PointerAnalysis.MAddr vi, offset) -> Var.Set.add (vi, offset) set
      | _ -> set
    in
    MemLoc.Set.fold g (PointerAnalysis.resolve_ap ap) set
  in
  AP.Set.fold f ap_set Var.Set.empty

let infer_var_partition file =
  let partition = VarDS.create 32 in
  let union_loc_set set =
    let for_all p = Var.Set.for_all p set in
    let nexists p = for_all (fun x -> not (p x)) in
    if (Var.Set.cardinal set == 2)
       && (for_all Var.is_shared || nexists Var.is_shared)
    then begin
      let s = VarDS.find partition (Var.Set.choose set) in
      let merge ap = ignore (VarDS.union s (VarDS.find partition ap)) in
      Var.Set.iter merge set
    end
  in
  let rec add_bexpr bexpr =
    let uses = var_locs (Bexpr.get_uses bexpr) in
    if Var.Set.cardinal uses <= 2 then union_loc_set uses
    else begin
      match bexpr with
      | And (l, r) -> (add_bexpr l; add_bexpr r)
      | Or (l, r) -> (add_bexpr l; add_bexpr r)
      | Atom _ -> ()
    end
  in
  let add_vertex v = match v.dkind with
    | Assume p -> add_bexpr p
    | Assert (p, _) -> add_bexpr p
    | _ ->
      union_loc_set (var_locs (AP.Set.union (Def.get_uses v) (Def.get_defs v)))
  in
  let process_thread t =
    let func = lookup_function t file in
    Cfg.iter_vertex add_vertex func.cfg
  in
  List.iter process_thread file.threads;
  (match file.globinit with
   | Some f -> Cfg.iter_vertex add_vertex f.cfg
   | None -> ());
  let map = VarDS.reverse_map partition Var.Set.empty Var.Set.add in
  let f var = try map var with Not_found -> Var.Set.singleton var in
  f
