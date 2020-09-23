open Core
open Srk
open CfgIr

module RG = Interproc.RG
module Callgraph = RecGraph.Callgraph(Interproc.RG)
module CGLoop = Loop.Make(Callgraph)
let categorize file =
  let show_bool x =
    if x then "True"
    else "False"
  in
  match file.entry_points with
  | [main] -> begin
      let rg = Interproc.make_recgraph file in
      let is_recursive =
        Callgraph.callgraph rg main
        |> CGLoop.loop_nest
        |> CGLoop.cutpoints
        |> CGLoop.VertexSet.is_empty
        |> not
      in
      let uses_memory =
        try
          file |> CfgIr.iter_defs (fun def ->
                      match def.dkind with
                      | Store (_, _) -> raise Not_found
                      | _ -> ());
          false
        with Not_found -> true
      in
      let uses_floats =
        let is_float v =
          match resolve_type (Varinfo.get_type v) with
          | Float _ -> true
          | _ -> false
        in
        List.exists is_float file.vars
        || List.exists
             (fun func ->
               List.exists is_float func.formals
               || List.exists is_float func.locals)
             file.funcs
      in
      Format.printf "Recursive: %s\n" (show_bool is_recursive);
      Format.printf "Memory:    %s\n" (show_bool uses_memory);
      Format.printf "Floats:    %s\n" (show_bool uses_floats)
    end
  | _ -> assert false

let _ =
  CmdLine.register_pass
    ("-categorize", categorize, " List features used in the input program")
