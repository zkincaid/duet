open Core
open CfgIr
open Solve
open Apak

let may_use def =
  let open PointerAnalysis in
  let f ap set =
    match ap with
    | Variable v -> Var.Set.add v set
    | Deref _ ->
      let g memloc set =
        match memloc with
        | (MAddr vi, offset) -> Var.Set.add (vi,offset) set
        | _ -> set
      in
      MemLoc.Set.fold g (ap_points_to ap) set
  in
  AP.Set.fold f (Def.get_uses def) Var.Set.empty

let must_define def =
  match Def.assigned_var def with
  | Some v -> Var.Set.singleton v
  | None -> Var.Set.empty

let live_vars file uses =
  let module LiveInterp = struct
    include Lattice.LiftSubset(Var.Set)
    let transfer def live =
      Var.Set.union (Var.Set.diff live (must_define def)) (uses def)
    let widen = join
    let name = "Liveness analysis"
  end in
  let module Live = Solve.MakeBackwardCfgSolver(LiveInterp) in

  let live_map = Def.HT.create 991 in
  let process_vertex (v, live) = Def.HT.add live_map v live in
  let process_result result =
    BatEnum.iter process_vertex (Live.enum_input result)
  in
  let mk_init _ value = value in
  (Def.HT.find live_map,
   Live.backwards_file_analysis file process_result Var.Set.empty mk_init)
