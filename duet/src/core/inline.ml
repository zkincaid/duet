(*pp camlp4find deriving.syntax *)

(** Static inliner *)

open Core
open CfgIr
open Apak
open Call

let emit_cfg caller callee ret params pre =
  let cfg = caller.cfg in
  let args =
    try List.combine callee.formals params
    with Invalid_argument _ -> []
  in

  let add_params pre (v, e) =
    let assign = Def.mk (Assign ((v, OffsetFixed 0), e)) in
      Def.Set.iter (fun v -> Cfg.add_edge cfg v assign) pre;
      Def.Set.singleton assign
  in

  let rec add_vertex pre cur =
    let f pre succ exits =
      if Cfg.mem_vertex cfg succ
      then exits
      else Def.Set.union (add_vertex pre succ) exits
    in
    match cur.dkind with
    | Return eo ->
      begin match (ret, eo) with
        | (Some v, Some e) ->
            let vert = Def.mk (Assign (v, e)) in
              Def.Set.iter (fun v -> Cfg.add_edge cfg v vert) pre;
              Def.Set.singleton vert
        | (None, _) -> pre
        | _ -> failwith "Return value empty"
      end
    | _ ->
      Def.Set.iter (fun v -> Cfg.add_edge cfg v cur) pre; 
      if (Cfg.out_degree callee.cfg cur) < 1
      then Def.Set.singleton cur
      else Cfg.fold_succ (f (Def.Set.singleton cur)) callee.cfg cur Def.Set.empty
  in
   
    add_vertex (List.fold_left add_params pre args)
               (Cfg.initial_vertex callee.cfg)

let expand_call func callee def ret params = match callee with
  | Some callee ->
      let pre = Cfg.fold_pred Def.Set.add func.cfg def Def.Set.empty in
      let exits = emit_cfg func callee ret params pre in
        Cfg.iter_succ 
          (fun v ->
             Def.Set.iter
               (fun u -> Cfg.add_edge func.cfg u v)
               exits)
          func.cfg def;
        Cfg.remove_vertex func.cfg def
  | None ->
      Cfg.iter_pred
        (fun u -> Cfg.iter_succ (Cfg.add_edge func.cfg u) func.cfg def)
        func.cfg
        def

let inline_file file =
  let ht = Varinfo.HT.create (List.length file.funcs) in
  let cg = build_callgraph file in
  let top_order = Callgraph.compute_topological_order cg in
  let rec inline name =
    try let func = List.find (fun f -> Varinfo.equal name f.fname) file.funcs in
        let expand_calls def = match def.dkind with
          | Call (vo, AddrOf (Variable (tgt, OffsetFixed 0)), elst) ->
              let callee =
                try Varinfo.HT.find ht tgt
                with Not_found -> if (top_order name tgt) < 0
                                  then failwith "Can't inline recursive program"
                                  else inline tgt; Varinfo.HT.find ht tgt
              in expand_call func callee def vo elst
          | _ -> ()
        in
          Cfg.iter_vertex expand_calls func.cfg;
          Varinfo.HT.add ht name (Some func)
    with Not_found -> Varinfo.HT.add ht name None
  in
    Callgraph.Top.iter inline cg

let _ = CmdLine.register_pass ("-inline", inline_file, " Inline input file")
