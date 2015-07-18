(** Static inliner *)

open Core
open CfgIr
open Apak
open Call

let emit_cfg caller callee ret params preds succs =
  let visited = Def.HT.create 0 in
  let cfg = caller.cfg in
  let args =
    try List.combine callee.formals params
    with Invalid_argument _ -> []
  in

  let add_params preds (v, e) =
    let assign = Def.mk (Assign ((v, OffsetFixed 0), e)) in
    List.iter (fun v -> Cfg.add_edge cfg v assign) preds;
    [assign]
  in

  let rec add_vertex preds def =
    let add_exit preds =
      List.iter (fun u -> List.iter (fun v -> Cfg.add_edge cfg u v) succs) preds
    in
    match def.dkind with
    | Return eo ->
      begin match (ret, eo) with
        | (Some v, Some e) ->
          let vert = Def.mk (Assign (v, e)) in
          List.iter (fun v -> Cfg.add_edge cfg v vert) preds;
          add_exit [vert]
        | (None, _) -> add_exit preds
        | _ -> failwith "Return value empty"
      end
    | _ ->
      List.iter (fun v -> Cfg.add_edge cfg v def) preds;
      if not (Def.HT.mem visited def) then
        begin
          Def.HT.add visited def true;
          List.iter (fun v -> Cfg.add_edge cfg v def) preds;
          if (Cfg.out_degree callee.cfg def) < 1
          then add_exit [def] 
          else Cfg.iter_succ (add_vertex [def]) callee.cfg def
        end
  in
  add_vertex (List.fold_left add_params preds args)
    (Cfg.initial_vertex callee.cfg)

let expand_call func callee def ret params = match callee with
  | Some callee ->
    let preds = Cfg.pred func.cfg def in
    let succs = Cfg.succ func.cfg def in
    Cfg.remove_vertex func.cfg def;
    emit_cfg func callee ret params preds succs
  | None -> remove_inner_vertex def func.cfg

let inline_file file =
  let ht = Varinfo.HT.create (List.length file.funcs) in
  let cg = build_callgraph file in
  let top_order = Callgraph.compute_topological_order cg in
  let rec inline name = if not (Varinfo.HT.mem ht name) then
      try let func = List.find (fun f -> Varinfo.equal name f.fname) file.funcs in
        let expand_calls def = match def.dkind with
          | Call (vo, AddrOf (Variable (tgt, OffsetFixed 0)), elst) ->
            begin
              try expand_call func (Varinfo.HT.find ht tgt) def vo elst
              with Not_found ->
                if (top_order name tgt) <= 0
                then Log.errorf "WARNING: Can't inline recursive call from %a to %a"
                    Varinfo.pp name
                    Varinfo.pp tgt
                else
                  begin inline tgt;
                    expand_call func (Varinfo.HT.find ht tgt) def vo elst
                  end
            end
          | _ -> ()
        in
        Cfg.iter_vertex expand_calls func.cfg;
        if !Log.debug_mode then Cfg.sanity_check func.cfg;
        Varinfo.HT.add ht name (Some func)
      with Not_found -> Varinfo.HT.add ht name None
  in
  Callgraph.Top.iter inline cg

