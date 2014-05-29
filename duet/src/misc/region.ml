(*pp camlp4find deriving.syntax *)

(** Implementation of region graphs.  A region of a CFG is a subgraph with a
    distinguished entry and exit such that every incoming edge to the region
    is ends at the entry and every outgoing edge originates from the exit.  *)

open Core
open CfgIr
open Graph
open Apak

module R = Sese.Make(Cfg)
module G = R.G
module CG = RecGraph.Callgraph(RecGraph.LiftPar(R))

type region_hierarchy = {
  callgraph : CG.t;
  block : Def.t -> R.Block.t option
}

let region_hierarchy g =
  { callgraph = CG.callgraph g (-1);
    block = R.block g }

let rh_parent rh x =
  match CG.pred rh.callgraph x with
  | [x] -> Some x
  | []  -> None
  | _   -> assert false

(** Compute the least common ancestor of two regions in the region hierarchy
    forest (or None, if the regions have no common ancestors). *)
let rh_lca rh x y =
  let p = rh_parent rh in
  let rec to_root r rest =
    match r with
    | Some r -> to_root (p r) (r::rest)
    | None   -> rest
  in
  let rec go cur xpath ypath = match xpath, ypath with
    | (xp::xps, yp::yps) ->
      if R.Block.equal xp yp then go (Some xp) xps yps
      else cur
    | _ -> cur
  in
  go None (to_root (p x) [x]) (to_root (p y) [y])

(** Compute local variables for regions.  A variable v is local to a region r
    if v is not a global variable or a variable whose address is taken, every
    use and definition of v is contained in r, and r is the smallest region
    with this property. *)
let region_vars g =
  let rh = region_hierarchy g in
  let ht = Var.HT.create 32 in
  let join rx ry =
    match rx, ry with
    | (None, _) | (_, None) -> None
    | (Some a, Some b) -> rh_lca rh a b
  in
  let add_use def v =
    if Varinfo.is_global (fst v) || Varinfo.addr_taken (fst v) then ()
    else begin
      try Var.HT.replace ht v (join (Var.HT.find ht v) (rh.block def))
      with Not_found -> Var.HT.add ht v (rh.block def)
    end
  in
  let add_uses (_, v) = match v with
    | `Atom def -> Var.Set.iter (add_use def) (Def.free_vars def)
    | `Block _  -> ()
  in
  let rmap = R.Block.HT.create 32 in
  let add_rmap x = function
    | Some r -> begin
      try R.Block.HT.replace rmap r (Var.Set.add x (R.Block.HT.find rmap r))
      with Not_found -> R.Block.HT.add rmap r (Var.Set.singleton x)
    end
    | None -> ()
  in
  BatEnum.iter add_uses (R.vertices g);
  Var.HT.iter add_rmap ht;
  (fun block ->
    try R.Block.HT.find rmap block
    with Not_found -> Var.Set.empty)

module MakeElim (K : Sig.KA.Ordered.S) :
sig
  val kleene : R.t ->
               G.t ->
               (def -> K.t) ->
               ((var -> bool) -> K.t -> K.t) ->
               def ->
               def ->
               K.t
  val summarize_fun : func ->
                      (def -> K.t) ->
                      ((var -> bool) -> K.t -> K.t) ->
                      K.t
end = struct
  module PE = Pathexp.MakeElim(G)(K)
  open RecGraph
  let kleene rg g def_weight generalize s t =
    let region_vars = region_vars rg in
    let rec weight = function
      | `Atom def -> def_weight def
      | `Block block ->
	let rv = region_vars block in
	let entry = R.block_entry rg block in
	let exit = R.block_exit rg block in
	let body = R.block_body rg block in
	let summary = PE.path_expr_v body weight entry exit in
	let exist v = Varinfo.is_global (fst v) || not (Var.Set.mem v rv) in
	generalize exist summary
    in
    PE.path_expr_v g weight (`Atom s) (`Atom t)

  let summarize_fun func weight generalize =
    let init = Cfg.initial_vertex func.cfg in
    let term = Def.mk (Assume Bexpr.ktrue) in
    let terminal = Cfg.enum_terminal func.cfg in
    Cfg.add_vertex func.cfg term;
    BatEnum.iter (fun t -> Cfg.add_edge func.cfg t term) terminal;
    let rg = R.construct func.cfg ~entry:init ~exit:term in
    Cfg.remove_vertex func.cfg term;
    let body = R.block_body rg 0 in
    let summary = kleene rg body weight generalize init term in
    generalize
      (fun v -> not (is_local func (fst v) || is_formal func (fst v)))
      summary
end
