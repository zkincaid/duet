open Core
open CfgIr
open Srk

module Seq = struct
  module V = struct
    include Def
    type atom = t
    type block = Varinfo.t
    type ('a,'b) typ = ('a,'b) RecGraph.seq_typ
    let classify v = match v.dkind with
      | Call (None, AddrOf (Variable (func, OffsetNone)), []) ->
        `Block func
      | Call (_, _, _) ->
        Log.fatalf "Unrecognized call: %a" pp v
      | _ -> `Atom v
  end
  module RG = RecGraph.Make(V)(Varinfo)
  module RGD = ExtGraph.Display.MakeSimple(RG.G)(Def)
end

module V = struct
  include Def
  type atom = t
  type block = Varinfo.t
  type ('a,'b) typ = ('a,'b) RecGraph.par_typ
  let classify v = match v.dkind with
    | Call (None, AddrOf (Variable (func, OffsetNone)), []) ->
      `Block func
    | Call (_, _, _) ->
      Log.fatalf "Unrecognized call: %a" pp v
    | Builtin (Fork (None, AddrOf (Variable (func, OffsetNone)), [])) ->
      `ParBlock func
    | Builtin (Fork (_, _, _)) ->
      Log.fatalf "Unrecognized fork: %a" pp v;
    | _ -> `Atom v
end
module RG = RecGraph.Make(V)(Varinfo)
module RGD = ExtGraph.Display.MakeSimple(RG.G)(Def)

module SeqRG = struct
  type ('a, 'b) typ = ('a, 'b) RecGraph.seq_typ
  include (RG : RecGraph.S with type ('a, 'b) typ := ('a, 'b) RecGraph.par_typ
                            and module G = RG.G
                            and module Block = RG.Block
                            and type t = RG.t
                            and type atom = RG.atom
                            and type block = RG.block)
  let classify v = match v.dkind with
    | Call (None, AddrOf (Variable (func, OffsetNone)), []) ->
      `Block func
    | Call (_, _, _) ->
      Log.fatalf "Unrecognized call: %a" Def.pp v
    | _ -> `Atom v
end

let local func_name =
  try
    let func =
      List.find (fun f -> Varinfo.equal func_name f.fname) (get_gfile()).funcs
    in
    let vars =
      Varinfo.Set.remove (return_var func_name)
        (Varinfo.Set.of_enum (BatEnum.append
                                (BatList.enum func.formals)
                                (BatList.enum func.locals)))
    in
    fun (x, _) -> (Varinfo.Set.mem x vars)
  with Not_found -> (fun (_, _) -> false)

let make_recgraph file =
  ignore (Bddpa.initialize file);
  PointerAnalysis.simplify_calls file;
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
    | `ParBlock func | `Block func ->
      begin
        try ignore (RG.block_entry rg func); rg
        with Not_found -> mk_stub rg func
      end
    | `Atom _ -> rg
  in
  let rg = List.fold_left mk_func RG.empty file.funcs in
  BatEnum.fold add_call rg (RG.vertices rg)

let remove_skip rg =
  let f block graph =
    let remove v graph =
      if Def.equal v (RG.block_entry rg block) then
        graph
      else match v.dkind with
        | Assume phi when Bexpr.eval phi = Some true ->
          RG.G.fold_succ
            (fun s g ->
               RG.G.fold_pred (fun p g -> RG.G.add_edge g p s) graph v g)
            graph
            v
            (RG.G.remove_vertex graph v)
        | _ -> graph
    in
    RG.G.fold_vertex remove graph graph
  in
  RG.map f rg
