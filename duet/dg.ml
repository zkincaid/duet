(** Sequential dependence graphs *)

open Core

module Pack = Var.Set
module FS = Lattice.FunctionSpace.Total.Make(Pack)(Lattice.LiftSubset(Def.Set))
module G = Afg.G
module S = Afg.Pack

let construct file pack uses =
  (* Map access paths to their reaching definitions *)

  (** Reaching definitions analysis *)
  let module RDInterp = struct
    include FS

    let transfer def rd =
      begin match Def.assigned_var def with
        | Some v -> FS.update (pack v) (Def.Set.singleton def) rd
        | None -> match def.dkind with
          | Store (lhs, _) ->
            let open PointerAnalysis in
            let f memloc rd =
              match memloc with
              | (MAddr vi, offset) ->
                let p = pack (vi, offset) in
                FS.update p (Def.Set.add def (FS.eval rd p)) rd
              | (_, _) -> rd
            in
            MemLoc.Set.fold f (resolve_ap lhs) rd
          | Assume phi | Assert (phi, _) ->
            let set_rd v rd = FS.update (pack v) (Def.Set.singleton def) rd in
            Var.Set.fold set_rd (Bexpr.free_vars phi) rd
          | _ -> rd
      end
    let widen = join
    let name = "Reaching definitions"
    let bottom = FS.const Def.Set.empty
  end in

  let module RD = Solve.MakeForwardCfgSolver(RDInterp) in
  let dg = G.create () in

  let (_, init_s) = Live.live_vars file uses in

  let add_edge src lbl tgt = G.add_edge_e dg (G.E.create src lbl tgt) in

  (* Add a vertex and its incoming edges to the G, and add v -> rd to
     rd_map *)
  let process_vertex (v, rd) =
    let uses = uses v in
    let go (pack, defs) =
      if not (Var.Set.is_empty (Var.Set.inter uses pack))
      then
        let pack_edge =
          let f var pair_set =
            let v = Variable var in
            S.PairSet.add (S.mk_pair v v) pair_set
          in
          Var.Set.fold f pack S.PairSet.empty
        in
        Def.Set.iter (fun def -> add_edge def pack_edge v) defs

    in
    G.add_vertex dg v;
    BatEnum.iter go (FS.enum rd)
  in
  let init =
    let init_def = Def.Set.singleton Def.initial in
    Var.Set.fold
      (fun s fs -> FS.update (pack s) init_def fs)
      init_s
      (FS.const Def.Set.empty)
  in
  let mk_init _ value = value in
  (* add all the vertices of a cfg to the G *)
  let process_result result =
    BatEnum.iter process_vertex (RD.enum_input result)
  in
  RD.file_analysis file process_result init mk_init;
  dg

(** Simplify a dependence graph *)
let simplify_dg afg =
  let vertices = G.fold_vertex (fun v vs -> v::vs) afg [] in
  let remove_copy v =
    match v.dkind with
    | Assign (_, AccessPath (Variable _)) ->
      let f pe se =
        let def_ap = S.fst (S.PairSet.choose (G.E.label pe)) in
        let use_ap = S.snd (S.PairSet.choose (G.E.label se)) in
        let lbl = S.PairSet.singleton (S.mk_pair def_ap use_ap) in
        G.add_edge_e afg (G.E.create (G.E.src pe) lbl (G.E.dst se))
      in
      G.iter_pred_e (fun pe -> G.iter_succ_e (f pe) afg v) afg v;
      G.remove_vertex afg v
    | _ -> ()
  in
(*
  let split_vertex v = (* don't split asserts! *)
    match v.dkind with
      | Assume _ ->
	  if S.PowerSet.cardinal (G.inputs afg v) = 1 then begin
	    let add_copy e =
	      let new_v = clone_def v in
	      let pred_e = G.E.create (G.E.src e) (G.E.label e) new_v in
	      let add_succ_e se =
		G.add_edge_e afg
		  (G.E.create new_v (G.E.label se) (G.E.dst se))
	      in
		G.remove_edge_e afg e;
		G.add_vertex afg new_v;
		G.add_edge_e afg pred_e;
		G.iter_succ_e add_succ_e afg v
	    in
	      List.iter add_copy (List.tl (G.pred_e afg v))
	  end
      | _ -> ()
  in
*)
  let init_ap =
    Variable (Var.mk (Varinfo.mk_global "init" (Concrete (Int unknown_width))))
  in
  let relabel e =
    let ap = S.snd (S.PairSet.choose (G.E.label e)) in
    let lbl = S.PairSet.singleton (S.mk_pair init_ap ap) in
    G.remove_edge_e afg e;
    G.add_edge_e afg (G.E.create Def.initial lbl (G.E.dst e))
  in
  (* reduce the dimension of initial_def  *)
  if G.mem_vertex afg Def.initial
  then G.iter_succ_e relabel afg Def.initial;
  List.iter remove_copy vertices
(*    List.iter split_vertex (G.fold_vertex (fun v vs -> v::vs) afg [])*)

let compare_dg g h =
  let compare_v d =
    let cmp = compare (G.in_degree g d) (G.in_degree h d) in
    if cmp < 0 then print_endline "<"
    else if cmp > 0 then print_endline ">"
    else print_endline "="
  in
  G.iter_vertex compare_v g
