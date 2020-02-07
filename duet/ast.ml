open Core
open Srk

(** Statement kind *)
type stmt_kind =
  | Branch        of stmt * stmt
  | Instr         of def list
  | Goto          of int (** Statement id *)
  | ForkGoto      of int (** Statement id *)
  | Block         of stmt list
and stmt = {
  sid : int; (** Statement id *)
  mutable skind : stmt_kind;
}

(** Function definition type *)
type funcdec = {
  mutable fname : varinfo;
  mutable formals : varinfo list;
  mutable locals : varinfo list;
  mutable body : stmt list;
  mutable file : file option;
}
and file = {
  mutable filename : string;
  mutable funcs : funcdec list;
  mutable vars : varinfo list;
  mutable globinit : funcdec option;
  mutable max_sid : int;
  mutable types : typ list; (** named types *)
  mutable stmt_map : (int,stmt) Hashtbl.t
}

module StmtHashTyp = struct
  type t = stmt
  let equal a b = (a.sid = b.sid)
  let compare a b = Stdlib.compare (a.sid) (b.sid)
  let hash stmt = stmt.sid
end
module StmtHT = Hashtbl.Make(StmtHashTyp)
module StmtSet = Set.Make(StmtHashTyp)

let mk_file name =
  { filename = name;
    funcs = [];
    vars = [];
    globinit = None;
    max_sid = 0;
    types = [];
    stmt_map = Hashtbl.create 32 }

let mk_stmt file kind =
  let sid = file.max_sid in
  let stmt = { sid = sid;
               skind = kind }
  in
  file.max_sid <- sid + 1;
  Hashtbl.add file.stmt_map sid stmt;
  stmt

let stmt_kind stmt = stmt.skind
let stmt_id stmt = stmt.sid
let lookup_stmt file sid =
  try Hashtbl.find file.stmt_map sid
  with Not_found -> failwith ("Undefined statement id: " ^ (string_of_int sid))

type 'a open_stmt =
  | OBranch        of 'a * 'a
  | OInstr         of def list
  | OGoto          of int (** Statement id *)
  | OForkGoto      of int (** Statement id *)
  | OBlock         of 'a list

let rec fold_stmt f stmt = match stmt_kind stmt with
  | Branch (a, b) -> f (OBranch (fold_stmt f a, fold_stmt f b))
  | Instr defs -> f (OInstr defs)
  | Goto tgt -> f (OGoto tgt)
  | ForkGoto tgt -> f (OForkGoto tgt)
  | Block stmts -> f (OBlock (List.map (fold_stmt f) stmts))

let start_block formatter =
  Format.pp_print_string formatter "{";
  Format.pp_open_box formatter 2;
  Format.pp_force_newline formatter ()

let end_block formatter =
  Format.pp_close_box formatter ();
  Format.pp_force_newline formatter ();
  Format.pp_print_string formatter "}"

let rec pp_stmt formatter stmt = match stmt_kind stmt with
  | Branch (s1, s2) ->
    Format.fprintf formatter "Branch@;%a@\nelse@;%a"
      pp_stmt s1
      pp_stmt s2
  | Instr [] ->
    Format.fprintf formatter "skip %d" stmt.sid
  | Instr [def] -> Def.pp formatter def
  | Instr (d::ds) ->
    let pp def =
      Format.pp_force_newline formatter ();
      Def.pp formatter def;
      Format.pp_print_string formatter ";";
    in
    start_block formatter;
    Def.pp formatter d;
    Format.pp_print_string formatter ";";
    List.iter pp ds;
    end_block formatter
  | Goto i -> Format.fprintf formatter "goto: %d" i
  | ForkGoto i -> Format.fprintf formatter "fork/goto: %d" i
  | Block stmts ->
    let pp stmt =
      pp_stmt formatter stmt;
      Format.pp_force_newline formatter ()
    in
    start_block formatter;
    List.iter pp stmts;
    end_block formatter

let rec iter_defs_stmt f s = match stmt_kind s with
  | Branch (bthen, belse) -> iter_defs_stmt f bthen; iter_defs_stmt f belse
  | Instr defs -> List.iter f defs
  | Goto _ -> ()
  | ForkGoto _ -> ()
  | Block stmts -> List.iter (iter_defs_stmt f) stmts

let iter_defs_fundec f func = List.iter (iter_defs_stmt f) func.body
let iter_defs_file f file = List.iter (iter_defs_fundec f) file.funcs

module StmtCfg = Graph.Imperative.Digraph.Concrete(StmtHashTyp)

module Display = struct
  include StmtCfg;;
  let vertex_name v =
    "\"" ^ (String.escaped (SrkUtil.mk_show pp_stmt v)) ^ "\""
  let get_subgraph _ =  None
  let default_vertex_attributes _ = []
  let default_edge_attributes _ = []
  let graph_attributes _ = []
  let vertex_attributes _ = []
  let edge_attributes _ = []
end
module DotOutput = Graph.Graphviz.Dot(Display)

let construct_cfg file func =
  let cfg = StmtCfg.create () in
  let add_edge = StmtCfg.add_edge cfg in
  let rec process_block incoming = function
    | [] -> incoming
    | (x::xs) -> process_block (process_stmt incoming x) xs
  and process_stmt incoming stmt =
    List.iter (fun x -> add_edge x stmt) incoming;
    match stmt_kind stmt with
    | Goto sid -> add_edge stmt (lookup_stmt file sid); []
    | Block stmts -> process_block [stmt] stmts
    | Branch (bthen, belse) ->
      let bstart = Def.mk (Assume Bexpr.ktrue) in
      let bend = Def.mk (Assume Bexpr.ktrue) in
      let bstart = mk_stmt file (Instr [bstart]) in
      let bend = mk_stmt file (Instr [bend]) in
      let out_then = process_stmt [bstart] bthen in
      let out_else = process_stmt [bstart] belse in
      add_edge stmt bstart;
      List.iter (fun x -> add_edge x bend) (out_then@out_else);
      [bend]
    | ForkGoto _ -> [stmt]
    | Instr _ -> [stmt]
  in
  let rec add_vertices stmt =
    StmtCfg.add_vertex cfg stmt;
    match stmt_kind stmt with
    | Branch (a, b) -> add_vertices a; add_vertices b
    | Block stmts -> List.iter add_vertices stmts
    | _ -> ()
  in
  List.iter add_vertices func.body;
  ignore (process_block [] func.body);
  cfg

