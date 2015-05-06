open Core
open CfgIr
open Apak

(** Static callgraph *)
module Callgraph =
struct
  module G = Graph.Imperative.Digraph.Concrete(Varinfo)
  module Top = Graph.Topological.Make(G)
  include G

  let vertex_name v = "\"" ^ (Varinfo.show v) ^ "\""
  let get_subgraph _ = None
  let default_vertex_attributes _ = []
  let default_edge_attributes _ = []
  let graph_attributes _ = []
  let vertex_attributes _ = []
  let edge_attributes _ = []
  let compute_topological_order g =
    let ht = Varinfo.HT.create 32 in
    let max = ref 0 in
    let next_id () =
      let x = !max in
      incr max;
      x
    in
    let get_id x =
      try Varinfo.HT.find ht x
      with Not_found -> failwith "CfgIr.compute_topological_order: id not found"
    in
    Top.iter (fun x -> Varinfo.HT.add ht x (next_id ())) g;
    fun x y -> Pervasives.compare (get_id y) (get_id x)
  let vertex_clone x = x
  let vertex_string x = Varinfo.show x
end

(** Build the static callgraph for a file.  Dynamic calls are not
    supported. *)
let build_callgraph file =
  let cg = Callgraph.create () in
  let add_calls func =
    let add_call_edge v = match v.dkind with
      | Call (_, AddrOf (Variable (tgt, OffsetFixed 0)), _)
      | Call (_, AccessPath (Variable (tgt, OffsetFixed 0)), _) ->
        Callgraph.add_edge cg func.fname tgt
      | Call _ ->
        failwith "Can't resolve non-static call"
      | _ -> ()
    in
    Cfg.iter_vertex add_call_edge func.cfg
  in
  List.iter (fun f -> Callgraph.add_vertex cg f.fname) file.funcs;
  List.iter add_calls file.funcs;
  cg

module DefLabel = struct
  type t = def option deriving (Compare)
  let default = None
  let compare = Compare_t.compare
end

(** Thread creation graph.  Currently intraprocedural. *)
module Tcg = Graph.Imperative.Digraph.ConcreteLabeled(Varinfo)(DefLabel)
let construct_tcg file =
  let tcg = Tcg.create () in
  let lookup_thread thread =
    try List.find (fun f -> Varinfo.equal thread f.fname) file.funcs
    with Not_found -> begin
        Log.errorf "Can't resolve thread identifier `%a'" Varinfo.format thread;
        assert false
      end
  in
  let add_succs thread =
    let func = lookup_thread thread in
    let f def = match def.dkind with
      | Builtin (Fork (_, expr, _)) -> begin
          let add_edge func =
            let edge = Tcg.E.create thread (Some def) func in
            Tcg.add_edge_e tcg edge
          in
          Varinfo.Set.iter add_edge (Pa.resolve_call expr)
        end
      | _ -> ()
    in
    Cfg.iter_vertex f func.cfg
  in
  List.iter (Tcg.add_vertex tcg) file.entry_points;
  List.iter add_succs file.threads;
  tcg

let (iter_tcg_order, iter_reverse_tcg_order) =
  let go pick next dst f file =
    let tcg = construct_tcg file in
    let process_edge edge = f (Tcg.E.label edge) (dst edge) in
    let process t =
      if pick t tcg then begin
        next process_edge tcg t;
        Tcg.remove_vertex tcg t
      end
    in
    let process_initial t = if pick t tcg then f None t in
    Tcg.iter_vertex process_initial tcg;
    while Tcg.nb_vertex tcg != 0 do
      Tcg.iter_vertex process tcg
    done
  in
  (go (fun t tcg -> Tcg.in_degree tcg t = 0) Tcg.iter_succ_e Tcg.E.dst,
   go (fun t tcg -> Tcg.out_degree tcg t = 0) Tcg.iter_pred_e Tcg.E.src)

module CGOutput = Graph.Graphviz.Dot(Callgraph)
let display_callgraph callgraph =
  ExtGraph.display_dot CGOutput.output_graph callgraph
