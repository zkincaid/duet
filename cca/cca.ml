open Srk
open KoatParse
open CcaSyntax
open Apak

include Log.Make(struct let name = "cca" end)

let split_loops = ref true
let matrix_rec = ref true
let display_its = ref false
let show_stats = ref false
let forward_inv = ref "box"

module ITSLoop = Loop.SccGraph(ITS)

let enum_loop_headers its = ITSLoop.enum_headers (ITSLoop.construct its)

let parse_file filename =
  let open Lexing in
  let lexbuf = Lexing.from_channel (open_in filename) in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };
  try KoatParse.program KoatLex.koat lexbuf with
  | _ ->
    let open Lexing in
    let pos = lexbuf.lex_curr_p in
    failwith (Printf.sprintf "Parse error: %s:%d:%d"
                filename
                pos.pos_lnum
                (pos.pos_cnum - pos.pos_bol + 1))


module MakeDecorator (M : sig
    type t
    val manager_alloc : unit -> t Apron.Manager.t
  end) = struct
  module D = struct
    include SrkApron
    type t = (Ctx.t, M.t) SrkApron.property
    let man = M.manager_alloc ()
    let top = top man (Env.empty Ctx.context)
    let bottom = bottom man (Env.empty Ctx.context)
  end
  module FP = Apak.Fixpoint.MakeAnalysis(ITS)(D)

  let decorate entry its =
    let edge_transfer tr prop =
      Tr.abstract_post prop (ITS.E.label tr)
    in
    let vertex_transfer v prop =
      if ITS.V.equal v entry then
        D.top
      else
        prop
    in
    let result =
      FP.analyze vertex_transfer ~edge_transfer its
    in
    BatEnum.fold (fun its v ->
        let out = SrkApron.formula_of_property (FP.output result v) in
        logf "Found invariant at %s: %a" v (Srk.Syntax.Formula.pp Ctx.context) out;
        ITS.fold_succ_e (fun e its ->
            let its = ITS.remove_edge_e its e in
            let tr = Tr.mul (Tr.assume out) (ITS.E.label e) in
            ITS.add_edge_e its (ITS.E.create (ITS.E.src e) tr (ITS.E.dst e)))
          its
          v
          its)
      its
      (enum_loop_headers its)
end

module BoxDecorator = MakeDecorator(Box)
module OctDecorator = MakeDecorator(Oct)
module PolyhedronDecorator = MakeDecorator(struct
    type t = Polka.loose Polka.t
    let manager_alloc = Polka.manager_alloc_loose
  end)


module Weight = struct
  include Tr
  module DPoly = struct
    module WV = Iteration.WedgeVector
    module SplitWV = Iteration.Split(WV)
    include Iteration.Sum(WV)(SplitWV)
    let abstract_iter ?(exists=fun x -> true) ark phi symbols =
      if !split_loops then
        right (SplitWV.abstract_iter ~exists ark phi symbols)
      else
        left (WV.abstract_iter ~exists ark phi symbols)
  end
  module DMatrix = struct
    module WM = Iteration.WedgeMatrix
    module SplitWM = Iteration.Split(WM)
    include Iteration.Sum(WM)(SplitWM)
    let abstract_iter ?(exists=fun x -> true) ark phi symbols =
      if !split_loops then
        right (SplitWM.abstract_iter ~exists ark phi symbols)
      else
        left (WM.abstract_iter ~exists ark phi symbols)
  end
  module D = struct
    include Iteration.Sum(DPoly)(DMatrix)
    let abstract_iter ?(exists=fun x -> true) ark phi symbols =
      if !matrix_rec then
        right (DMatrix.abstract_iter ~exists ark phi symbols)
      else
        left (DPoly.abstract_iter ~exists ark phi symbols)
  end
  module I = Iter(D)
  let star x = Log.time "cra:star" I.star x
end

module P = Apak.Pathexp.MakeElim(ITS)(Weight)

let path_expr its start sinks =
  let its = 
    ITS.fold_edges_e (fun e its ->
        if ITS.V.equal (ITS.E.src e) (ITS.E.dst e) then
          let loop = Weight.star (ITS.E.label e) in
          let its = ITS.remove_edge_e its e in
          assert (ITS.in_degree its (ITS.E.src e) > 0);
          ITS.fold_pred_e (fun e its ->
              let its = ITS.remove_edge_e its e in
              let tr = Tr.mul (ITS.E.label e) loop in
              ITS.add_edge_e its (ITS.E.create (ITS.E.src e) tr (ITS.E.dst e)))
            its
            (ITS.E.src e)
            its
        else
          its)
      its
      its
  in
  P.path_expr_multiple_tgt its ITS.E.label start (fun x -> List.mem x sinks)

let filename = ref "<none>"

let usage_msg = "CRA complexity analyzer\nUsage: duet [OPTIONS] file.koat"
  
let spec_list = [
  ("-domain",
   Arg.Set_string forward_inv,
   " Set abstract domain (box,octagon,polyhedron,none)");
  ("-no-split",
   Arg.Clear split_loops,
   " Disable loop splitting");
  ("-no-matrix",
   Arg.Clear matrix_rec,
   " Disable matrix recurrences");
  ("-display-its",
   Arg.Set display_its,
   " Display integer transition system (requires eog)");
  ("-verbosity",
   Arg.String (fun v -> Log.verbosity_level := (Log.level_of_string v)),
   " Set verbosity level (higher = more verbose; defaults to 0)");
  ("-verbose",
   Arg.String (fun v -> Log.set_verbosity_level v `info),
   " Raise verbosity for a particular module");
  ("-verbose-list",
   Arg.Unit (fun () ->
       print_endline "Available modules for setting verbosity:";
       Hashtbl.iter (fun k _ ->
           print_endline (" - " ^ k);
         ) Log.loggers;
       exit 0;
     ),
   " List modules which can be used with -verbose");
  ("-stats", Arg.Set show_stats, " Display statistics");
  ("-color", Arg.Set Log.colorize, " Use ANSI colors")
]


let () =
  Arg.parse (Arg.align spec_list) (fun x -> filename := x) usage_msg;
  assert (!filename != "<none>");
  let ces = parse_file (!filename) in
  let its = its_of_ces ces in
  if !display_its then
    DisplayITS.display its;
  let its =
    match !forward_inv with
    | "box" -> BoxDecorator.decorate ces.start its
    | "octagon" -> OctDecorator.decorate ces.start its
    | "polyhedron" -> PolyhedronDecorator.decorate ces.start its
    | "none" -> its
    | _ -> Log.fatalf "Unrecognized abstract domain `%s'" (!forward_inv)
  in
  let sinks =
    ITS.fold_vertex (fun v sinks ->
        if ITS.out_degree its v = 0 then
          v::sinks
        else
          sinks)
      its
      []
  in
  let sinks =
    BatEnum.fold (fun sinks header -> header::sinks) sinks (enum_loop_headers its)
  in
  let summary = path_expr its ces.start sinks in
  logf ~attributes:[`Bold] ~level:`always "Finished analysis -- extracting bounds.";

  (* replace cost with 0, add constraint cost = rhs *)
  let guard =
    let subst x =
      if x = cost then
        Ctx.mk_real QQ.zero
      else
        Ctx.mk_const x
    in
    let rhs =
      Syntax.substitute_const Ctx.context subst (Tr.get_transform "cost" summary)
    in
    Ctx.mk_and [Syntax.substitute_const Ctx.context subst (Tr.guard summary);
                Ctx.mk_eq (Ctx.mk_const cost) rhs ]
  in
  let exists x =
    match Var.of_symbol x with
    | Some _ -> true
    | None -> false
  in
  begin
    match Wedge.symbolic_bounds_formula Ctx.context ~exists guard cost with
    | `Sat (lower, upper) ->
      begin match lower with
        | Some lower ->
          logf ~level:`always "%a <= cost" (Syntax.Term.pp Ctx.context) lower;
          logf ~level:`always "Runtime is o(%a)"
            BigO.pp (BigO.of_term Ctx.context lower)
        | None -> ()
      end;
      begin match upper with
        | Some upper ->
          logf ~level:`always "cost <= %a" (Syntax.Term.pp Ctx.context) upper;
          logf ~level:`always "Runtime is O(%a)"
            BigO.pp (BigO.of_term Ctx.context upper)
        | None -> ()
      end
    | `Unsat ->
      assert false
  end;
  if !show_stats then
    Log.print_stats ()
