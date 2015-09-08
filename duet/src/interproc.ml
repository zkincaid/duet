open Core
open CfgIr
open Ai
open Apak

module Seq = struct
  module V = struct
    include Def
    type atom = t
    type block = Varinfo.t
    type ('a,'b) typ = ('a,'b) RecGraph.seq_typ
    let classify v = match v.dkind with
      | Call (None, AddrOf (Variable (func, OffsetFixed 0)), []) ->
        `Block func
      | Call (_, _, _) ->
        Log.errorf "Unrecognized call: %a" format v;
        assert false
      | _ -> `Atom v
  end
  module RG = RecGraph.Make(V)(Varinfo)
  module RGD = ExtGraph.Display.MakeSimple(RG.G)(Def)
  module MakePathExpr = Pathexp.MakeSeqRG(RG)(Varinfo)
end

module V = struct
  include Def
  type atom = t
  type block = Varinfo.t
  type ('a,'b) typ = ('a,'b) RecGraph.par_typ
  let classify v = match v.dkind with
    | Call (None, AddrOf (Variable (func, OffsetFixed 0)), []) ->
      `Block func
    | Call (_, _, _) ->
      Log.errorf "Unrecognized call: %a" format v;
      assert false
    | Builtin (Fork (None, AddrOf (Variable (func, OffsetFixed 0)), [])) ->
      `ParBlock func
    | Builtin (Fork (_, _, _)) ->
      Log.errorf "Unrecognized fork: %a" format v;
      assert false
    | _ -> `Atom v
end
module RG = RecGraph.Make(V)(Varinfo)
module RGD = ExtGraph.Display.MakeSimple(RG.G)(Def)
module MakeParPathExpr = Pathexp.MakeParRG(RG)(Varinfo)

module SeqRG = struct
  type ('a, 'b) typ = ('a, 'b) RecGraph.seq_typ
  include (RG : RecGraph.S with type ('a, 'b) typ := ('a, 'b) RecGraph.par_typ
                            and module G = RG.G
                            and module Block = RG.Block
                            and type t = RG.t
                            and type atom = RG.atom
                            and type block = RG.block)
  let classify v = match v.dkind with
    | Call (None, AddrOf (Variable (func, OffsetFixed 0)), []) ->
      `Block func
    | Call (_, _, _) ->
      Log.errorf "Unrecognized call: %a" Def.format v;
      assert false
    | _ -> `Atom v
end
module MakePathExpr = Pathexp.MakeSeqRG(SeqRG)(Varinfo)

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
    | `ParBlock func | `Block func ->
      begin
        try ignore (RG.block_entry rg func); rg
        with Not_found -> mk_stub rg func
      end
    | `Atom _ -> rg
  in
  let rg = List.fold_left mk_func RG.empty file.funcs in
  BatEnum.fold add_call rg (RG.vertices rg)
