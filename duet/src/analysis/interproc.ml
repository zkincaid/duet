(*pp camlp4find deriving.syntax *)

open Core
open CfgIr
open Ai
open Apak

module V = struct
  include Def
  type atom = t
  type block = Varinfo.t
  let classify v = match v.dkind with
    | Call (None, AddrOf (Variable (func, OffsetFixed 0)), []) ->
      RecGraph.Block func
    | Call (_, _, _) ->
      Log.errorf "Unrecognized call: %a" format v;
      assert false
    | _ -> RecGraph.Atom v
end
module RG = RecGraph.Make(V)(Varinfo)
module RGD = ExtGraph.Display.MakeSimple(RG.G)(Def)
module MakePathExpr = Pathexp.MakeRG(RG)(Varinfo)
  
let make_recgraph file =
  ignore (Bddpa.initialize file);
  Pa.simplify_calls file;
  let mk_stub rg func =
    let v = Def.mk (Assume Bexpr.ktrue) in
    let graph = RG.G.add_vertex RG.G.empty v in
    RG.add_block rg func graph ~entry:v ~exit:v
  in
  let mk_func rg func =
    let add_edge src tgt graph = RG.G.add_edge graph src tgt in
    let graph = Cfg.fold_edges add_edge func.cfg RG.G.empty in
    let bentry = Cfg.initial_vertex func.cfg in
    let ts = Cfg.enum_terminal func.cfg in
    let bexit = Def.mk (Assume Bexpr.ktrue) in
    let add_edge graph v = RG.G.add_edge graph v bexit in
    let graph = BatEnum.fold add_edge (RG.G.add_vertex graph bexit) ts in
    RG.add_block rg func.fname graph ~entry:bentry ~exit:bexit
  in
  let add_call rg (_, v) =
    match V.classify v with
    | RecGraph.Block func ->
      begin
	try ignore (RG.block_entry rg func); rg
	with Not_found -> mk_stub rg func
      end
    | RecGraph.Atom _ -> rg
  in
  let rg = List.fold_left mk_func RG.empty file.funcs in
  BatEnum.fold add_call rg (RG.vertices rg)
