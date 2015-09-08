(** Simple program slicing *)

open Core
open Apak

module G = Afg.G
module F = Fixpoint.Wto(G)
module WL = Fixpoint.GraphWorklist(G)(Def)

(* "boring" vertices are not included in slices *)
let is_boring v = match v.dkind with
  | Assume bexpr -> Bexpr.equal bexpr Bexpr.ktrue
  | _            -> false

(* Add a vertices to a slice (skipping boring vertices) *)
let add_to_slice v set = if is_boring v then set else Def.Set.add v set

(** Compute, for each vertex v, the set of all vertices backward-reachable
    from v *)
let backward graph =
  let ht = Def.HT.create 1024 in
  let change v reaching =
    try Def.HT.replace ht v reaching
    with Not_found -> Def.HT.add ht v reaching
  in
  let reaching v =
    try Def.HT.find ht v
    with Not_found -> Def.Set.empty
  in
  let add_predecessor u set = add_to_slice u (Def.Set.union (reaching u) set) in
  let update v =
    let new_reaching = G.fold_pred add_predecessor graph v Def.Set.empty in
    let old_reaching = reaching v in
    change v new_reaching;
    not (Def.Set.equal new_reaching old_reaching)
  in
  let wide_update = None in
  F.fix graph update wide_update;
  reaching

let forward graph =
  let ht = Def.HT.create 1024 in
  let change v reaching =
    try Def.HT.replace ht v reaching
    with Not_found -> Def.HT.add ht v reaching
  in
  let reaching v =
    try Def.HT.find ht v
    with Not_found -> Def.Set.empty
  in
  let add_successor u set = add_to_slice u (Def.Set.union (reaching u) set) in
  let update v =
    let new_reaching = G.fold_succ add_successor graph v Def.Set.empty in
    let old_reaching = reaching v in
    change v new_reaching;
    not (Def.Set.equal new_reaching old_reaching)
  in
  WL.fix graph update;
  reaching

let slice_stats graph get_slice =
  let total_slice_size = ref 0 in
  let max_slice_size = ref 0 in
  let total_vertices = ref 0 in
  let f vertex =
    if not (is_boring vertex) then begin
      let slice = get_slice vertex in
      let slice_size = Def.Set.cardinal slice in
      if slice_size > (!max_slice_size) then max_slice_size := slice_size;
      total_slice_size := !total_slice_size + slice_size;
      incr total_vertices
    end
  in
  G.iter_vertex f graph;
  print_endline ("Vertices: " ^ (string_of_int (!total_vertices)));
  print_endline ("Max slice: " ^ (string_of_int (!max_slice_size)));
  let avg_slice =
    (float_of_int !total_slice_size) /. (float_of_int (!total_vertices))
  in
  print_endline ("Avg slice: " ^ (string_of_float avg_slice))
(*
let _ =
  let go file =
    let dg = AliasLogic.construct_dg file in
    let slice = backward dg in
      slice_stats dg slice
  in
  CmdLine.register_pass
    ("-backward-slice", go, " Backward slice")

let _ =
  let go file =
    let dg = AliasLogic.construct_dg file in
    let slice = forward dg in
      slice_stats dg slice
  in
  CmdLine.register_pass
    ("-forward-slice", go, " Forward slice")
*)
